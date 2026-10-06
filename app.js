import { initializeApp } from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js';
import { getAuth, signInWithEmailAndPassword, signOut, onAuthStateChanged } from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js';
import { getFirestore, collection, doc, getDoc, setDoc, onSnapshot, writeBatch } from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js';
import { firebaseConfig, LOGIN_EMAIL_DOMAIN } from './firebase-config.js';

const app = initializeApp(firebaseConfig);
const auth = getAuth(app);
const db = getFirestore(app);

/* ============ 設定 ============ */

const MIN_STAFF = 6;
const MAX_STAFF = 14;
const MAX_RESCHEDULE_PER_DAY = 5;
const WEEKDAYS = ['日', '月', '火', '水', '木', '金', '土'];
const OPEN_DAYS = ['月', '火', '水', '木', '金', '土'];

const defaultMaster = {
  '月': ['スタッフA', 'スタッフB', 'スタッフC', 'スタッフD', 'スタッフE', 'スタッフF'],
  '火': ['スタッフA', 'スタッフB', 'スタッフC', 'スタッフD', 'スタッフE'],
  '水': ['スタッフA', 'スタッフB', 'スタッフC', 'スタッフD', 'スタッフE', 'スタッフF', 'スタッフG'],
  '木': ['スタッフA', 'スタッフB', 'スタッフC', 'スタッフD', 'スタッフE', 'スタッフF'],
  '金': ['スタッフA', 'スタッフB', 'スタッフC', 'スタッフD', 'スタッフE', 'スタッフF', 'スタッフG', 'スタッフH'],
  '土': ['スタッフA', 'スタッフB', 'スタッフC', 'スタッフD', 'スタッフE', 'スタッフF', 'スタッフG']
};

/* ============ ユーティリティ ============ */
// XSS対策：HTMLに埋め込む文字列は必ずこれを通す
function esc(s) {
  return String(s).replace(/[&<>"']/g, c => (
    { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]
  ));
}

// 表記ゆれ対策：全角/半角・前後空白・連続空白を統一
function normName(s) {
  return String(s || '').normalize('NFKC').replace(/\s+/g, ' ').trim();
}

function loadJSON(key, fallback) {
  try {
    const v = JSON.parse(localStorage.getItem(key));
    return v === null || v === undefined ? fallback : v;
  } catch (e) {
    console.error('Load error:', key, e);
    return fallback;
  }
}

function clone(o) { return JSON.parse(JSON.stringify(o)); }

function sanitizeMaster(m) {
  const out = {};
  OPEN_DAYS.forEach(d => {
    const list = Array.isArray(m && m[d]) ? m[d] : [];
    out[d] = [...new Set(list.map(normName).filter(Boolean))];
  });
  return out;
}

/* ============ 状態 ============ */
let masterConfig = clone(defaultMaster);
let userDayRescheduleCounts = {};
let pendingRequests = [];
let currentUserRole = null;

// シフトは「固定メンバーとの差分」だけを保存する（Firestore: shifts/{日付}）
// overrides[日付] = { removed: [固定メンバー名...], added: [{name, originDate, type}...] }
let overrides = {};

// 未保存の変更（saveStorage でまとめて Firestore に書き込む）
const dirty = { dates: new Set(), days: new Set(), reqs: new Set(), master: false };

function migrateLegacy(legacy) {
  const out = {};
  Object.entries(legacy || {}).forEach(([date, list]) => {
    if (!Array.isArray(list)) return;
    const fixedNames = masterConfig[getDayName(date)] || [];
    const kept = list.filter(m => m.type === 'fixed').map(m => normName(m.name));
    out[date] = {
      removed: fixedNames.filter(n => !kept.includes(n)),
      added: list
        .filter(m => m.type !== 'fixed' || !fixedNames.includes(normName(m.name)))
        .map(m => ({ name: normName(m.name), originDate: m.originDate, type: m.type }))
    };
  });
  return out;
}

let currentMonday = getMonday(new Date());
let selectedDateStr = formatDate(currentMonday);

/* ============ 日付ヘルパー ============ */
function getMonday(d) {
  const date = new Date(d);
  date.setHours(0, 0, 0, 0);
  const day = date.getDay();
  date.setDate(date.getDate() - day + (day === 0 ? -6 : 1));
  return date;
}

function formatDate(d) {
  const y = d.getFullYear();
  const m = String(d.getMonth() + 1).padStart(2, '0');
  const dd = String(d.getDate()).padStart(2, '0');
  return `${y}-${m}-${dd}`;
}

function getDayName(dateStr) {
  return WEEKDAYS[new Date(dateStr.replace(/-/g, '/')).getDay()];
}

function getWeekDays(monday) {
  return Array.from({ length: 6 }, (_, i) => {
    const d = new Date(monday);
    d.setDate(monday.getDate() + i);
    return d;
  });
}

/* ============ シフト操作（差分ベース） ============ */
function getOv(date) {
  dirty.dates.add(date);
  if (!overrides[date]) overrides[date] = { removed: [], added: [] };
  return overrides[date];
}

function getFixedNames(date) {
  return masterConfig[getDayName(date)] || [];
}

// 常に新しい配列を返す（保存データを直接いじらない）
function getShiftObjectsForDate(date) {
  const o = overrides[date] || { removed: [], added: [] };
  const fixed = getFixedNames(date)
    .filter(n => !o.removed.includes(n))
    .map(name => ({ name, originDate: date, type: 'fixed' }));
  return fixed.concat(o.added.map(a => ({ ...a })));
}

function hasMember(date, name) {
  return getShiftObjectsForDate(date).some(m => m.name === name);
}

function removeMember(date, item) {
  const o = getOv(date);
  if (item.type === 'fixed' && getFixedNames(date).includes(item.name)) {
    if (!o.removed.includes(item.name)) o.removed.push(item.name);
  } else {
    const i = o.added.findIndex(a =>
      a.name === item.name && a.type === item.type && a.originDate === item.originDate);
    if (i >= 0) o.added.splice(i, 1);
  }
}

function addMember(date, item) {
  const o = getOv(date);
  if (item.type === 'fixed' && getFixedNames(date).includes(item.name)) {
    o.removed = o.removed.filter(n => n !== item.name);
  } else {
    o.added.push({ name: item.name, originDate: item.originDate, type: item.type });
  }
}

/* ============ 振替回数 ============ */
function getRescheduleUsed(name, dayName) {
  return userDayRescheduleCounts[`${dayName}_${name}`] || 0;
}

function updateRescheduleCount(name, dayName, delta) {
  const key = `${dayName}_${name}`;
  dirty.days.add(dayName);
  userDayRescheduleCounts[key] = Math.max(0, (userDayRescheduleCounts[key] || 0) + delta);
}

/* ============ 保存 ============ */
async function saveStorage() {
  try {
    const batch = writeBatch(db);
    dirty.dates.forEach(d => batch.set(doc(db, 'shifts', d), overrides[d] || { removed: [], added: [] }));
    dirty.days.forEach(day => {
      const c = {};
      Object.entries(userDayRescheduleCounts).forEach(([k, v]) => {
        if (k.startsWith(day + '_')) c[k.slice(day.length + 1)] = v;
      });
      batch.set(doc(db, 'counts', day), { c });
    });
    dirty.reqs.forEach(id => batch.delete(doc(db, 'requests', String(id))));
    if (dirty.master) batch.set(doc(db, 'config', 'master'), masterConfig);
    dirty.dates.clear(); dirty.days.clear(); dirty.reqs.clear(); dirty.master = false;
    await batch.commit();
  } catch (e) {
    console.error(e);
    alert('保存に失敗しました。通信状況や権限を確認し、画面を再読み込みしてください。');
  }
  render();
}

/* ============ 認証・メニュー ============ */
function requireAdmin() {
  if (currentUserRole !== 'admin') {
    alert('管理者のみ実行できます。');
    return false;
  }
  return true;
}

function toggleDropdownMenu(e) {
  e.stopPropagation();
  document.getElementById('dropdown-menu').classList.toggle('show');
}

document.addEventListener('click', () => {
  const menu = document.getElementById('dropdown-menu');
  if (menu) menu.classList.remove('show');
});

async function handleLogin(e) {
  e.preventDefault();
  const id = document.getElementById('login-id').value.trim().toLowerCase();
  const pass = document.getElementById('login-pass').value;
  const errorDiv = document.getElementById('login-error');
  try {
    await signInWithEmailAndPassword(auth, `${id}@${LOGIN_EMAIL_DOMAIN}`, pass);
    errorDiv.style.display = 'none';
  } catch (err) {
    errorDiv.style.display = 'block';
  }
}

function handleLogout() {
  if (confirm('ログアウトしますか？')) {
    document.getElementById('dropdown-menu').classList.remove('show');
    signOut(auth);
  }
}

/* ---- Firestore リアルタイム同期 ---- */
let unsubs = [];
function stopListeners() { unsubs.forEach(u => u()); unsubs = []; }

function startListeners(isAdmin) {
  stopListeners();
  const onErr = e => { console.error(e); alert('データの同期に失敗しました。権限設定を確認してください。'); };

  unsubs.push(onSnapshot(collection(db, 'shifts'), snap => {
    overrides = {};
    snap.forEach(d => {
      const v = d.data();
      overrides[d.id] = { removed: v.removed || [], added: v.added || [] };
    });
    render();
  }, onErr));

  unsubs.push(onSnapshot(collection(db, 'counts'), snap => {
    userDayRescheduleCounts = {};
    snap.forEach(d => {
      Object.entries(d.data().c || {}).forEach(([name, n]) => {
        userDayRescheduleCounts[`${d.id}_${name}`] = n;
      });
    });
    render();
  }, onErr));

  unsubs.push(onSnapshot(doc(db, 'config', 'master'), snap => {
    if (snap.exists()) {
      masterConfig = sanitizeMaster(snap.data());
    } else if (isAdmin) {
      setDoc(doc(db, 'config', 'master'), defaultMaster); // 初回だけ初期値を書き込む
    }
    render();
  }, onErr));

  if (isAdmin) { // 申請（理由を含む）は管理者だけが読める
    unsubs.push(onSnapshot(collection(db, 'requests'), snap => {
      pendingRequests = snap.docs.map(d => d.data()).sort((a, b) => a.id - b.id);
      render();
    }, onErr));
  }
}

onAuthStateChanged(auth, async user => {
  if (!user) {
    currentUserRole = null;
    stopListeners();
    pendingRequests = [];
    document.getElementById('login-id').value = '';
    document.getElementById('login-pass').value = '';
    document.getElementById('login-overlay').style.display = 'flex';
    return;
  }
  let isAdmin = false;
  try { isAdmin = (await getDoc(doc(db, 'admins', user.uid))).exists(); } catch (e) { /* 一般ユーザー扱い */ }
  currentUserRole = isAdmin ? 'admin' : 'user';
  document.getElementById('login-overlay').style.display = 'none';
  document.getElementById('login-pass').value = '';
  updateRoleUI();
  startListeners(isAdmin);
  render();
});

function updateRoleUI() {
  const isAdmin = currentUserRole === 'admin';
  document.getElementById('admin-menu-area').style.display = isAdmin ? 'block' : 'none';
  document.getElementById('user-menu-area').style.display = isAdmin ? 'none' : 'block';
}

function closeModal(id) {
  document.getElementById(id).style.display = 'none';
}

/* ============ 描画 ============ */
function renderTabs() {
  const weekDays = getWeekDays(currentMonday);
  const first = weekDays[0];
  document.getElementById('week-title').textContent = `${first.getFullYear()}年 ${first.getMonth() + 1}月`;
  document.getElementById('jump-date').value = selectedDateStr;

  document.getElementById('day-tabs').innerHTML = weekDays.map(d => {
    const dateStr = formatDate(d);
    const count = getShiftObjectsForDate(dateStr).length;
    return `
      <div class="tab-item ${dateStr === selectedDateStr ? 'active' : ''}" data-date="${esc(dateStr)}">
        <div>${esc(WEEKDAYS[d.getDay()])}</div>
        <span class="tab-date">${d.getDate()}</span>
        <span class="badge">${count}人</span>
      </div>`;
  }).join('');
}

function renderContent() {
  const members = getShiftObjectsForDate(selectedDateStr);
  const count = members.length;
  const dayName = getDayName(selectedDateStr);

  const reqCount = pendingRequests.length;
  document.getElementById('menu-badge').textContent = reqCount;
  document.getElementById('dropdown-req-badge').textContent = reqCount;

  const statusBox = document.getElementById('status-container');
  if (count < MIN_STAFF) {
    statusBox.innerHTML = `
      <div class="status-card danger">
        <div class="status-title">⚠️ 人員不足 (${count}/${MIN_STAFF}名)</div>
        <div class="status-desc">${MIN_STAFF}名を下回っているため、代理を立てる必要があります。</div>
      </div>`;
  } else if (count < MAX_STAFF) {
    statusBox.innerHTML = `
      <div class="status-card success">
        <div class="status-title">〇 出勤OK (${count}名)</div>
        <div class="status-desc">最大${MAX_STAFF}名まで「自由練習」として参加可能です。</div>
      </div>`;
  } else {
    statusBox.innerHTML = `
      <div class="status-card warning">
        <div class="status-title">満員 (${MAX_STAFF}/${MAX_STAFF}名)</div>
        <div class="status-desc">これ以上自由練習を追加できません。</div>
      </div>`;
  }

  document.getElementById('member-list').innerHTML = members.map((item, index) => {
    const used = getRescheduleUsed(item.name, dayName);
    const remaining = Math.max(0, MAX_RESCHEDULE_PER_DAY - used);

    let tag = '';
    if (item.type === 'transfer') {
      tag = `<span class="tag-type tag-transfer">振替枠 (${esc(item.originDate)}から)</span>`;
    } else if (item.type === 'free') {
      tag = '<span class="tag-type tag-free">自由練習</span>';
    } else if (item.type === 'special_transfer') {
      tag = '<span class="tag-type tag-special">特別振替枠</span>';
    }

    let actions;
    if (item.type === 'free') {
      actions = `<button class="btn-action btn-cancel" data-action="remove-free" data-index="${index}">削除</button>`;
    } else if (item.type === 'transfer' || item.type === 'special_transfer') {
      actions = `<button class="btn-action btn-cancel" data-action="cancel-transfer" data-index="${index}">振替取消</button>`;
    } else {
      actions = `
        <button class="btn-action" data-action="reschedule" data-index="${index}">振替</button>
        <button class="btn-action" style="border-color:#52796f; color:#52796f;" data-action="special" data-index="${index}">特例申請</button>`;
    }

    return `
      <div class="member-card">
        <div class="member-info">
          <div><span class="member-name">${esc(item.name)}</span>${tag}</div>
          <span class="member-sub">${esc(dayName)}曜枠 振替残: ${remaining} / ${MAX_RESCHEDULE_PER_DAY} 回</span>
        </div>
        <div class="action-group">${actions}</div>
      </div>`;
  }).join('');

  document.getElementById('add-btn').disabled = count >= MAX_STAFF;
}

function render() {
  renderTabs();
  renderContent();
}

function selectDate(dateStr) {
  selectedDateStr = dateStr;
  render();
}

function changeWeek(direction) {
  currentMonday.setDate(currentMonday.getDate() + direction * 7);
  selectedDateStr = formatDate(getWeekDays(currentMonday)[0]);
  render();
}

// タイトルをタップ → カレンダーで選んだ日の週へ移動
function jumpToDate(dateStr) {
  if (!dateStr) return;
  const d = new Date(dateStr.replace(/-/g, '/'));
  if (Number.isNaN(d.getTime())) return;
  currentMonday = getMonday(d);
  // 日曜は活動日ではないので、その週の月曜を選択する
  selectedDateStr = d.getDay() === 0 ? formatDate(currentMonday) : dateStr;
  render();
}

const jumpInput = document.getElementById('jump-date');
jumpInput.addEventListener('change', e => jumpToDate(e.target.value));
jumpInput.addEventListener('click', () => {
  try { jumpInput.showPicker(); } catch (e) { /* 非対応ブラウザは標準動作に任せる */ }
});

/* ============ 共通バリデーション ============ */
// 振替先の日付チェック。問題があればメッセージを返す
function validateTargetDate(targetDate, originDate, name) {
  if (!targetDate || targetDate === originDate) return '別の日付を正しく選択してください。';
  if (Number.isNaN(new Date(targetDate.replace(/-/g, '/')).getTime())) return '日付が正しくありません。';
  if (!OPEN_DAYS.includes(getDayName(targetDate))) return '日曜日は活動日ではないため振替できません。';
  if (targetDate < formatDate(new Date())) return '過去の日付には振替できません。';
  const members = getShiftObjectsForDate(targetDate);
  if (members.length >= MAX_STAFF) return `${targetDate} は最大人数の${MAX_STAFF}名に達しているため振替できません。`;
  if (members.some(m => m.name === name)) return `${name}さんは既に ${targetDate} に登録されています。`;
  return '';
}

function setMinDate(inputId) {
  document.getElementById(inputId).min = formatDate(new Date());
}

/* ============ 自由練習 ============ */
function addFreeShift() {
  const members = getShiftObjectsForDate(selectedDateStr);
  if (members.length >= MAX_STAFF) return;

  const name = normName(prompt(`${selectedDateStr} に追加するお名前を入力してください:`));
  if (!name) return;
  if (name.length > 30) { alert('名前は30文字以内で入力してください。'); return; }
  if (members.some(m => m.name === name)) {
    alert(`${name}さんは既に ${selectedDateStr} に登録されています。`);
    return;
  }
  addMember(selectedDateStr, { name, originDate: selectedDateStr, type: 'free' });
  saveStorage();
}

function removeFreeShift(item) {
  if (confirm(`${item.name}さんの自由練習を削除しますか？`)) {
    removeMember(selectedDateStr, item);
    saveStorage();
  }
}

/* ============ 特例申請 ============ */
function openSpecialRequestModal(name, index) {
  document.getElementById('special-req-title').textContent = `【特例申請】${name}さん (${selectedDateStr})`;
  document.getElementById('req-member-name').value = name;
  document.getElementById('req-member-index').value = index;
  document.getElementById('req-type').value = 'absent';
  document.getElementById('req-reason').value = '';
  document.getElementById('req-target-date').value = selectedDateStr;
  setMinDate('req-target-date');
  toggleReqTypeUI();
  document.getElementById('special-request-modal').style.display = 'flex';
}

function toggleReqTypeUI() {
  const type = document.getElementById('req-type').value;
  document.getElementById('group-target-date').style.display = type === 'special_transfer' ? 'block' : 'none';
}

function submitSpecialRequest() {
  const name = document.getElementById('req-member-name').value;
  const type = document.getElementById('req-type').value;
  const reason = document.getElementById('req-reason').value.trim();
  const targetDate = document.getElementById('req-target-date').value;

  if (!reason) { alert('理由を入力してください。'); return; }
  if (reason.length > 200) { alert('理由は200文字以内で入力してください。'); return; }

  if (type === 'special_transfer') {
    const err = validateTargetDate(targetDate, selectedDateStr, name);
    if (err) { alert(err); return; }
  }

  if (pendingRequests.some(r => r.name === name && r.originalDate === selectedDateStr)) {
    alert('この日の申請は既に送信済みです。管理者の対応をお待ちください。');
    return;
  }

  const reqObj = {
    id: Date.now(),
    name,
    originalDate: selectedDateStr,
    type,
    reason,
    targetDate: type === 'special_transfer' ? targetDate : '',
    createdAt: new Date().toLocaleString('ja-JP')
  };
  setDoc(doc(db, 'requests', String(reqObj.id)), reqObj)
    .catch(() => alert('申請の送信に失敗しました。もう一度お試しください。'));
  closeModal('special-request-modal');
  alert('管理者に申請を送信しました。承認されるまでしばらくお待ちください。');
}

/* ============ 申請管理（管理者） ============ */
function openRequestsModal() {
  document.getElementById('dropdown-menu').classList.remove('show');
  if (!requireAdmin()) return;

  const listDiv = document.getElementById('requests-list');
  if (pendingRequests.length === 0) {
    listDiv.innerHTML = '<p style="font-size:13px; color:var(--text-sub); text-align:center; padding: 20px 0;">届いている特例申請はありません。</p>';
  } else {
    listDiv.innerHTML = pendingRequests.map(req => {
      const isAbsent = req.type === 'absent';
      const badge = isAbsent
        ? '<span class="request-type-badge req-absent">特例欠席</span>'
        : '<span class="request-type-badge req-special">特別振替 (回数なし)</span>';
      const id = Number(req.id);
      return `
        <div class="request-card">
          <div>${badge} <strong style="font-size:14px;">${esc(req.name)}</strong></div>
          <div style="font-size:11px; color:var(--text-sub); margin-top:2px;">
            対象日: ${esc(req.originalDate)}${isAbsent ? '' : ` ➔ 振替希望: ${esc(req.targetDate)}`}
          </div>
          <div class="request-reason">理由: ${esc(req.reason)}</div>
          <div style="font-size:10px; color:#999; margin-bottom:8px;">申請日時: ${esc(req.createdAt)}</div>
          <div style="display:flex; gap:6px; justify-content:flex-end;">
            <button class="btn-action btn-cancel" data-req-action="reject" data-id="${id}">却下</button>
            <button class="btn-main" style="padding: 6px 12px; font-size:12px; flex:initial;" data-req-action="approve" data-id="${id}">承認して実行</button>
          </div>
        </div>`;
    }).join('');
  }
  document.getElementById('requests-modal').style.display = 'flex';
}

function approveRequest(reqId) {
  if (!requireAdmin()) return;
  const reqIndex = pendingRequests.findIndex(r => r.id === reqId);
  if (reqIndex === -1) return;
  const req = pendingRequests[reqIndex];

  const origin = getShiftObjectsForDate(req.originalDate);
  const item = origin.find(m => m.name === req.name);

  if (!item) {
    alert(`${req.name}さんは ${req.originalDate} のシフトに存在しないため、この申請は処理できません。申請を削除します。`);
    dirty.reqs.add(req.id);
    pendingRequests.splice(reqIndex, 1);
    saveStorage();
    openRequestsModal();
    return;
  }

  if (req.type === 'absent') {
    removeMember(req.originalDate, item);
    alert(`${req.name}さんの ${req.originalDate} の特例欠席を承認し、シフトから外しました。`);
  } else if (req.type === 'special_transfer') {
    const err = validateTargetDate(req.targetDate, req.originalDate, req.name);
    if (err) { alert(`特別振替を実行できません：\n${err}`); return; }

    removeMember(req.originalDate, item);
    addMember(req.targetDate, { name: req.name, originDate: req.originalDate, type: 'special_transfer' });
    alert(`${req.name}さんの特別振替（${req.originalDate} ➔ ${req.targetDate}）を承認しました。※振替回数は消費されません。`);
  }

  dirty.reqs.add(req.id);
    pendingRequests.splice(reqIndex, 1);
  saveStorage();
  openRequestsModal();
}

function rejectRequest(reqId) {
  if (!requireAdmin()) return;
  if (confirm('この申請を却下しますか？')) {
    dirty.reqs.add(reqId);
    pendingRequests = pendingRequests.filter(r => r.id !== reqId);
    saveStorage();
    openRequestsModal();
  }
}

/* ============ 通常振替 ============ */
function openRescheduleModal(name, index) {
  const dayName = getDayName(selectedDateStr);
  if (getRescheduleUsed(name, dayName) >= MAX_RESCHEDULE_PER_DAY) {
    alert(`${name}さんの【${dayName}曜日枠】の振替上限（${MAX_RESCHEDULE_PER_DAY}回）に達しています。\n上限を超える場合は「特例申請」ボタンから管理者に申請してください。`);
    return;
  }
  if (getShiftObjectsForDate(selectedDateStr).length - 1 < MIN_STAFF) {
    alert(`振替すると ${selectedDateStr} が${MIN_STAFF}名未満になります。\n代理を立ててください。`);
    return;
  }
  document.getElementById('reschedule-modal-title').textContent = `【通常振替】${name}さん`;
  document.getElementById('reschedule-member-name').value = name;
  document.getElementById('reschedule-member-index').value = index;
  document.getElementById('reschedule-date-input').value = selectedDateStr;
  setMinDate('reschedule-date-input');
  document.getElementById('reschedule-modal').style.display = 'flex';
}

function executeReschedule() {
  const name = document.getElementById('reschedule-member-name').value;
  const index = parseInt(document.getElementById('reschedule-member-index').value, 10);
  const targetDate = document.getElementById('reschedule-date-input').value;

  const members = getShiftObjectsForDate(selectedDateStr);
  const item = members[index];
  if (!item || item.name !== name || item.type !== 'fixed') {
    alert('対象のメンバー情報が変わっています。画面を確認してやり直してください。');
    closeModal('reschedule-modal');
    return;
  }

  const err = validateTargetDate(targetDate, selectedDateStr, name);
  if (err) { alert(err); return; }

  const dayName = getDayName(selectedDateStr);
  const used = getRescheduleUsed(name, dayName);
  if (used >= MAX_RESCHEDULE_PER_DAY) {
    alert(`${dayName}曜日枠の振替上限に達しています。`);
    return;
  }

  if (members.length - 1 < MIN_STAFF) {
    alert(`振替すると ${selectedDateStr} が${MIN_STAFF}名未満になります。\n代理を立ててください。`);
    closeModal('reschedule-modal');
    return;
  }

  removeMember(selectedDateStr, item);
  addMember(targetDate, { name, originDate: selectedDateStr, type: 'transfer' });
  updateRescheduleCount(name, dayName, 1);

  closeModal('reschedule-modal');
  saveStorage();
  alert(`${name}さんを ${targetDate} へ振替しました。\n（${dayName}曜枠 振替残り: ${MAX_RESCHEDULE_PER_DAY - (used + 1)}回）`);
}

function cancelReschedule(item) {
  if (!confirm(`${item.name}さんの振替を取り消し、元に戻しますか？`)) return;

  removeMember(selectedDateStr, item);

  // 元の日に既にいる場合は二重登録しない
  if (!hasMember(item.originDate, item.name)) {
    addMember(item.originDate, { name: item.name, originDate: item.originDate, type: 'fixed' });
  }
  if (item.type !== 'special_transfer') {
    updateRescheduleCount(item.name, getDayName(item.originDate), -1);
  }

  saveStorage();
  alert(`${item.name}さんの振替を取り消し、${item.originDate} の枠に戻しました。`);
}

/* ============ 固定メンバー設定 ============ */
function openMasterConfig() {
  document.getElementById('dropdown-menu').classList.remove('show');
  if (!requireAdmin()) return;

  document.getElementById('master-inputs').innerHTML = OPEN_DAYS.map(d => `
    <div class="form-group">
      <label>${esc(d)}曜日の固定メンバー</label>
      <input type="text" id="master-${esc(d)}" value="${esc((masterConfig[d] || []).join(', '))}">
    </div>`).join('');
  document.getElementById('master-modal').style.display = 'flex';
}

function saveMasterConfig() {
  if (!requireAdmin()) return;
  OPEN_DAYS.forEach(d => {
    const raw = document.getElementById(`master-${d}`).value.split(/[,、，]/);
    masterConfig[d] = [...new Set(raw.map(normName).filter(Boolean))];
  });
  dirty.master = true;
  closeModal('master-modal');
  saveStorage();
  alert('固定パターンを更新しました！\n（振替・欠席などの個別変更は維持されます）');
}

/* ============ データ管理 ============ */
function openDataModal() {
  document.getElementById('dropdown-menu').classList.remove('show');
  if (!requireAdmin()) return;
  document.getElementById('data-modal').style.display = 'flex';
}

function exportData() {
  if (!requireAdmin()) return;
  const backup = {
    version: 2,
    masterConfig,
    shiftOverrides: overrides,
    userDayRescheduleCounts,
    pendingRequests,
    exportedAt: new Date().toISOString()
  };
  const blob = new Blob([JSON.stringify(backup, null, 2)], { type: 'application/json' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = `oakra_shift_backup_${formatDate(new Date())}.json`;
  a.click();
  URL.revokeObjectURL(url);
}

function importData(event) {
  if (!requireAdmin()) return;
  const input = event.target;
  const file = input.files[0];
  if (!file) return;

  const reader = new FileReader();
  reader.onload = e => {
    try {
      const data = JSON.parse(e.target.result);
      if (!data || typeof data.masterConfig !== 'object' || typeof data.userDayRescheduleCounts !== 'object') {
        alert('無効なバックアップファイルフォーマットです。');
        return;
      }
      Object.keys(overrides).forEach(d => dirty.dates.add(d));
      masterConfig = sanitizeMaster(data.masterConfig);
      userDayRescheduleCounts = data.userDayRescheduleCounts || {};
      // 新形式(v2)・旧形式(customShifts)どちらも読み込める
      if (data.shiftOverrides && typeof data.shiftOverrides === 'object') {
        overrides = data.shiftOverrides;
      } else if (data.customShifts && typeof data.customShifts === 'object') {
        overrides = migrateLegacy(data.customShifts);
      } else {
        overrides = {};
      }
      Object.keys(overrides).forEach(d => dirty.dates.add(d));
      WEEKDAYS.forEach(d => dirty.days.add(d));
      dirty.master = true;
      closeModal('data-modal');
      saveStorage();
      alert('データを正常に復元しました。（申請データは復元されません）');
    } catch (err) {
      alert('ファイルの読み込みに失敗しました。');
    } finally {
      input.value = '';
    }
  };
  reader.readAsText(file);
}

function resetRescheduleCounts() {
  if (!requireAdmin()) return;
  if (confirm('すべてのメンバーの「振替回数カウント」を初期化（0回に戻す）しますか？')) {
    userDayRescheduleCounts = {};
    WEEKDAYS.forEach(d => dirty.days.add(d));
    closeModal('data-modal');
    saveStorage();
    alert('振替回数を初期化しました。');
  }
}

function resetAllData() {
  if (!requireAdmin()) return;
  if (confirm('【注意】すべてのデータを削除して初期状態に戻しますか？')) {
    Object.keys(overrides).forEach(d => dirty.dates.add(d));
    pendingRequests.forEach(r => dirty.reqs.add(r.id));
    WEEKDAYS.forEach(d => dirty.days.add(d));
    dirty.master = true;
    masterConfig = clone(defaultMaster);
    overrides = {};
    userDayRescheduleCounts = {};
    pendingRequests = [];
    closeModal('data-modal');
    saveStorage();
    alert('すべてのデータを初期化しました。');
  }
}

/* ============ イベント委譲（inline onclick を廃止してXSS/引用符問題を回避） ============ */
document.getElementById('day-tabs').addEventListener('click', e => {
  const tab = e.target.closest('.tab-item[data-date]');
  if (tab) selectDate(tab.dataset.date);
});

document.getElementById('member-list').addEventListener('click', e => {
  const btn = e.target.closest('button[data-action]');
  if (!btn) return;
  const item = getShiftObjectsForDate(selectedDateStr)[parseInt(btn.dataset.index, 10)];
  if (!item) return;

  switch (btn.dataset.action) {
    case 'remove-free': removeFreeShift(item); break;
    case 'cancel-transfer': cancelReschedule(item); break;
    case 'reschedule': openRescheduleModal(item.name, parseInt(btn.dataset.index, 10)); break;
    case 'special': openSpecialRequestModal(item.name, parseInt(btn.dataset.index, 10)); break;
  }
});

document.getElementById('requests-list').addEventListener('click', e => {
  const btn = e.target.closest('button[data-req-action]');
  if (!btn) return;
  const id = Number(btn.dataset.id);
  if (btn.dataset.reqAction === 'approve') approveRequest(id);
  else if (btn.dataset.reqAction === 'reject') rejectRequest(id);
});

/* ============ 起動 ============ */
if ('serviceWorker' in navigator) {
  navigator.serviceWorker.register('sw.js').catch(err => console.warn('SW registration failed', err));
}

// type="module" ではHTMLのonclickから関数が見えないので、windowに公開する
Object.assign(window, {
  handleLogin, handleLogout, toggleDropdownMenu, openRequestsModal, openMasterConfig,
  openDataModal, changeWeek, addFreeShift, toggleReqTypeUI, closeModal, submitSpecialRequest,
  saveMasterConfig, executeReschedule, exportData, importData, resetRescheduleCounts, resetAllData
});
