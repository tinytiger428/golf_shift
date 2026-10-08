import { initializeApp } from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js';
import { getAuth, signInWithEmailAndPassword, createUserWithEmailAndPassword, deleteUser, sendPasswordResetEmail, signOut, onAuthStateChanged } from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js';
import { getFirestore, collection, doc, getDoc, setDoc, onSnapshot, writeBatch, query, limit, orderBy } from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js';
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
  '火': ['スタッフA', 'スタッフB', 'スタッフC', 'スタッフD', 'スタッフE', 'スタッフF'],
  '水': ['スタッフA', 'スタッフB', 'スタッフC', 'スタッフD', 'スタッフE', 'スタッフF'],
  '木': ['スタッフA', 'スタッフB', 'スタッフC', 'スタッフD', 'スタッフE', 'スタッフF'],
  '金': ['スタッフA', 'スタッフB', 'スタッフC', 'スタッフD', 'スタッフE', 'スタッフF'],
  '土': ['スタッフA', 'スタッフB', 'スタッフC', 'スタッフD', 'スタッフE', 'スタッフF']
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
  if (!dateStr || typeof dateStr !== 'string') return '';
  const d = new Date(dateStr.replace(/-/g, '/'));
  if (isNaN(d.getTime())) return '';
  return WEEKDAYS[d.getDay()] || '';
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
  dirty.dates.add(date);
  const o = getOv(date);
  if (item.type === 'fixed' && getFixedNames(date).includes(item.name)) {
    if (!o.removed.includes(item.name)) o.removed.push(item.name);
  } else {
    const i = o.added.findIndex(a =>
      a.name === item.name && (a.type === item.type || !item.type) && (!item.originDate || a.originDate === item.originDate));
    if (i >= 0) {
      o.added.splice(i, 1);
    } else {
      const idxByName = o.added.findIndex(a => a.name === item.name);
      if (idxByName >= 0) o.added.splice(idxByName, 1);
    }
  }
}

function addMember(date, item) {
  dirty.dates.add(date);
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

/* ============ 確認ダイアログ（ブラウザ標準のconfirmは一瞬で閉じる端末があるため自前で表示） ============ */
function askConfirm(message) {
  return new Promise(resolve => {
    const wrap = document.createElement('div');
    wrap.className = 'modal';
    wrap.style.display = 'flex';
    wrap.style.zIndex = '10000';
    wrap.innerHTML = `
      <div class="modal-content">
        <div class="modal-title" style="white-space:pre-wrap;">${esc(message)}</div>
        <div class="modal-actions">
          <button class="btn-action" data-ans="no">いいえ</button>
          <button class="btn-main" style="padding: 8px 16px; flex: initial;" data-ans="yes">はい</button>
        </div>
      </div>`;
    wrap.addEventListener('click', e => {
      const b = e.target.closest('button[data-ans]');
      if (!b) return;
      wrap.remove();
      resolve(b.dataset.ans === 'yes');
    });
    document.body.appendChild(wrap);
  });
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

async function handleLogout() {
  const menu = document.getElementById('dropdown-menu');
  if (menu) menu.classList.remove('show');
  try {
    await signOut(auth);
    showLogin();
    const overlay = document.getElementById('login-overlay');
    if (overlay) overlay.style.display = 'flex';
  } catch (err) {
    console.error('Logout error:', err);
    alert('ログアウトに失敗しました。通信状況を確認してもう一度お試しください。');
  }
}

/* ---- Firestore リアルタイム同期 ---- */
let unsubs = [];
function stopListeners() { unsubs.forEach(u => u()); unsubs = []; }

function startListeners(isAdmin) {
  stopListeners();
  const onErr = e => { console.error(e); alert('データの同期に失敗しました。権限設定を確認してください。'); };

  // クエリ制限（limit）を付与して過剰なドキュメント読み取り・コストを防止
  unsubs.push(onSnapshot(query(collection(db, 'shifts'), limit(200)), snap => {
    overrides = {};
    snap.forEach(d => {
      const v = d.data();
      overrides[d.id] = { removed: v.removed || [], added: v.added || [] };
    });
    render();
  }, onErr));

  unsubs.push(onSnapshot(query(collection(db, 'counts'), limit(100)), snap => {
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

  if (isAdmin) { // 申請およびユーザー権限一覧は管理者/幹部だけが読める。
    unsubs.push(onSnapshot(query(collection(db, 'requests'), orderBy('id', 'desc'), limit(50)), snap => {
      pendingRequests = snap.docs.map(d => d.data()).sort((a, b) => a.id - b.id);
      render();
    }, onErr));

    unsubs.push(onSnapshot(query(collection(db, 'users'), limit(500)), snap => {
      allUsers = snap.docs.map(d => ({ uid: d.id, ...d.data() }));
      renderRolesList();
    }, onErr));
  }
}

function canOperateOn(memberName) {
  if (currentUserRole === 'admin' || currentUserRole === 'executive') return true;
  if (!currentMemberName) return false;
  return normName(memberName) === normName(currentMemberName);
}

onAuthStateChanged(auth, async user => {
  if (!user) {
    currentUserRole = null;
    currentMemberName = '';
    stopListeners();
    pendingRequests = [];
    const loginId = document.getElementById('login-id');
    const loginPass = document.getElementById('login-pass');
    if (loginId) loginId.value = '';
    if (loginPass) loginPass.value = '';
    showLogin();
    const overlay = document.getElementById('login-overlay');
    if (overlay) overlay.style.display = 'flex';
    return;
  }

  let role = 'user';
  let fullName = '';
  try {
    const userDocSnap = await getDoc(doc(db, 'users', user.uid));
    if (userDocSnap.exists()) {
      const uData = userDocSnap.data();
      role = computeRole(uData);
      fullName = uData.fullName || '';
    } else {
      const legacyAdminSnap = await getDoc(doc(db, 'admins', user.uid));
      if (legacyAdminSnap.exists()) role = 'admin';
    }
  } catch (e) {
    console.warn('Role fetch warning:', e);
  }

  currentUserRole = role;
  currentMemberName = fullName;

  const overlay = document.getElementById('login-overlay');
  if (overlay) overlay.style.display = 'none';
  const loginPass = document.getElementById('login-pass');
  if (loginPass) loginPass.value = '';

  updateRoleUI();
  startListeners(role === 'admin' || role === 'executive');
  render();
});

function updateRoleUI() {
  const isAdmin = currentUserRole === 'admin';
  const isExec = currentUserRole === 'executive';
  const hasMenu = isAdmin || isExec;
  const adminMenuArea = document.getElementById('admin-menu-area');
  const userMenuArea = document.getElementById('user-menu-area');
  if (adminMenuArea) adminMenuArea.style.display = hasMenu ? 'block' : 'none';
  if (userMenuArea) userMenuArea.style.display = hasMenu ? 'none' : 'block';

  const itemRoles = document.getElementById('item-roles');
  const itemMaster = document.getElementById('item-master');
  const itemData = document.getElementById('item-data');
  if (itemRoles) itemRoles.style.display = isAdmin ? 'block' : 'none';
  if (itemMaster) itemMaster.style.display = isAdmin ? 'block' : 'none';
  if (itemData) itemData.style.display = isAdmin ? 'block' : 'none';
}

function closeModal(id) {
  const modal = document.getElementById(id);
  if (modal) modal.style.display = 'none';
}

/* ============ アカウント管理・サインアップ ============ */
const EMAIL_RE = /^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/;
const USERNAME_RE = /^[a-zA-Z0-9_]{3,20}$/;
const RESERVED_USERNAMES = ['admin', 'administrator', 'root', 'system', 'null', 'undefined'];
const ROLE_LABELS = { admin: 'admin', executive: '幹部', user: 'ユーザー' };

let currentMemberName = '';
let allUsers = [];
let signupInProgress = false;

function showSignup() {
  const loginPanel = document.getElementById('login-panel');
  const signupPanel = document.getElementById('signup-panel');
  if (loginPanel) loginPanel.style.display = 'none';
  if (signupPanel) signupPanel.style.display = 'block';
  const subtitle = document.getElementById('login-subtitle');
  if (subtitle) subtitle.textContent = 'アカウントを新規作成します';
  const errDiv = document.getElementById('signup-error');
  if (errDiv) errDiv.style.display = 'none';
}

function showLogin() {
  const loginPanel = document.getElementById('login-panel');
  const signupPanel = document.getElementById('signup-panel');
  if (signupPanel) signupPanel.style.display = 'none';
  if (loginPanel) loginPanel.style.display = 'block';
  const subtitle = document.getElementById('login-subtitle');
  if (subtitle) subtitle.textContent = 'ログインしてシフトシステムを開始します';
}

function signupErrorMessage(err) {
  if (!err) return 'アカウントを作成できませんでした。';
  console.error('Signup error details:', err);
  switch (err.code) {
    case 'auth/email-already-in-use':
      return 'このメールアドレスは既に登録されています。';
    case 'auth/invalid-email':
      return 'メールアドレスの形式が正しくありません。';
    case 'auth/weak-password':
      return 'パスワードは6文字以上で入力してください。';
    case 'auth/admin-restricted-operation':
    case 'auth/operation-not-allowed':
      return 'Firebase Consoleの設定で新規ユーザー登録が制限されています。Firebaseコンソールの[Authentication] → [設定]（またはSign-in method）でメール/パスワード認証および新規登録を許可してください。';
    case 'permission-denied':
      return 'データベースへの書き込み権限がありませんでした。';
    default:
      if (err.message) return `アカウントを作成できませんでした（${err.message}）。`;
      return 'アカウントを作成できませんでした。通信状況を確認してもう一度お試しください。';
  }
}

async function handleSignup(e) {
  e.preventDefault();
  const errorDiv = document.getElementById('signup-error');
  const btn = document.getElementById('signup-submit');
  const showErr = msg => { if (errorDiv) { errorDiv.textContent = msg; errorDiv.style.display = 'block'; } };

  const fullName = normName(document.getElementById('signup-fullname')?.value || '');
  const email = (document.getElementById('signup-email')?.value || '').trim().toLowerCase();
  const username = (document.getElementById('signup-username')?.value || '').trim().toLowerCase();
  const pass = document.getElementById('signup-pass')?.value || '';

  if (!fullName || fullName.length > 30) { showErr('名前は1〜30文字で入力してください。'); return; }
  if (!EMAIL_RE.test(email) || email.length > 254) { showErr('メールアドレスの形式が正しくありません。'); return; }
  if (email.endsWith('@' + LOGIN_EMAIL_DOMAIN)) { showErr('このメールアドレスは使用できません。'); return; }
  if (!USERNAME_RE.test(username)) { showErr('ユーザーネームは半角英数字と_で3〜20文字で入力してください。'); return; }
  if (RESERVED_USERNAMES.includes(username)) { showErr('このユーザーネームは使用できません。'); return; }
  if (pass.length < 6 || pass.length > 64) { showErr('パスワードは6文字以上で入力してください。'); return; }

  if (btn) btn.disabled = true;
  signupInProgress = true;
  let cred = null;
  let created = false;
  try {
    cred = await createUserWithEmailAndPassword(auth, email, pass);

    try {
      const taken = await getDoc(doc(db, 'usernames', username));
      if (taken.exists() && taken.data().uid !== cred.user.uid) {
        await deleteUser(cred.user);
        showErr('このユーザーネームは既に使われています。別のユーザーネームを入力してください。');
        return;
      }
    } catch (checkErr) {
      console.warn('Username check skipped:', checkErr);
    }

    const batch = writeBatch(db);
    batch.set(doc(db, 'users', cred.user.uid), { fullName, email, username, role: 'user', createdAt: Date.now() });
    batch.set(doc(db, 'usernames', username), { uid: cred.user.uid, email });
    await batch.commit();
    created = true;
  } catch (err) {
    console.error('Signup error:', err);
    if (cred && !created) { try { await deleteUser(cred.user); } catch (_) { /* 無視 */ } }
    showErr(signupErrorMessage(err));
  } finally {
    if (btn) btn.disabled = false;
    signupInProgress = false;
  }

  if (created) {
    if (document.getElementById('signup-pass')) document.getElementById('signup-pass').value = '';
    if (document.getElementById('signup-error')) document.getElementById('signup-error').style.display = 'none';
  }
}

function computeRole(userData) {
  if (!userData) return 'user';
  if (userData.role === 'admin' || userData.role === 'executive' || userData.role === 'user') return userData.role;
  return 'user';
}

function openRolesModal() {
  const menu = document.getElementById('dropdown-menu');
  if (menu) menu.classList.remove('show');
  renderRolesList();
  const modal = document.getElementById('roles-modal');
  if (modal) modal.style.display = 'flex';
}

function renderRolesList() {
  const listDiv = document.getElementById('roles-list');
  if (!listDiv) return;

  if (!allUsers || allUsers.length === 0) {
    listDiv.innerHTML = '<p style="font-size:13px; color:var(--ink-sub); text-align:center; padding: 20px 0;">登録されているアカウントはありません。</p>';
    return;
  }

  const sorted = [...allUsers].sort((a, b) => (a.fullName || '').localeCompare(b.fullName || '', 'ja'));

  listDiv.innerHTML = sorted.map(u => {
    const role = computeRole(u);
    const detailId = `role-detail-${u.uid}`;
    return `
      <div class="role-user-card">
        <div class="role-user-row">
          <button class="role-user-name" onclick="toggleUserDetail('${detailId}')">
            ${esc(u.fullName || '（名前未設定）')}
          </button>
          <select class="role-select" onchange="changeUserRole('${esc(u.uid)}', this.value)">
            <option value="admin" ${role === 'admin' ? 'selected' : ''}>admin</option>
            <option value="executive" ${role === 'executive' ? 'selected' : ''}>幹部</option>
            <option value="user" ${role === 'user' ? 'selected' : ''}>ユーザー</option>
          </select>
        </div>
        <div class="role-user-detail" id="${detailId}">
          <dl>
            <dt>フルネーム</dt><dd>${esc(u.fullName || '-')}</dd>
            <dt>メール</dt><dd>${esc(u.email || '-')}</dd>
            <dt>ユーザー名</dt><dd>${esc(u.username || '-')}</dd>
          </dl>
          ${u.email ? `<button class="btn-action" style="font-size:11px;" onclick="sendPasswordResetEmailForUser('${esc(u.email)}')">パスワード再設定メールを送信</button>` : ''}
        </div>
      </div>`;
  }).join('');
}

function toggleUserDetail(id) {
  const el = document.getElementById(id);
  if (el) el.classList.toggle('open');
}

async function changeUserRole(uid, newRole) {
  if (!ROLE_LABELS[newRole]) return;
  try {
    await setDoc(doc(db, 'users', uid), { role: newRole }, { merge: true });
    alert(`権限を「${ROLE_LABELS[newRole]}」に変更しました。`);
    renderRolesList();
  } catch (err) {
    console.error(err);
    alert('権限の変更に失敗しました。');
  }
}

async function sendPasswordResetEmailForUser(email) {
  if (!email) return;
  if (!confirm(`${email} 宛にパスワード再設定メールを送信しますか？`)) return;
  try {
    await sendPasswordResetEmail(auth, email);
    alert(`${email} に再設定用のメールを送信しました。`);
  } catch (err) {
    console.error(err);
    alert('パスワード再設定メールの送信に失敗しました。');
  }
}

let editingMasterConfig = {};

function openMasterConfig() {
  const menu = document.getElementById('dropdown-menu');
  if (menu) menu.classList.remove('show');
  editingMasterConfig = clone(masterConfig);
  renderMasterConfigInputs();
  const modal = document.getElementById('master-modal');
  if (modal) modal.style.display = 'flex';
}

function renderMasterConfigInputs() {
  const container = document.getElementById('master-inputs');
  if (!container) return;

  const suggestions = new Set();
  (allUsers || []).forEach(u => { if (u.fullName) suggestions.add(u.fullName); });
  OPEN_DAYS.forEach(d => {
    (masterConfig[d] || []).forEach(name => suggestions.add(name));
  });

  const datalistHtml = `<datalist id="master-name-suggestions">` +
    Array.from(suggestions).map(n => `<option value="${esc(n)}"></option>`).join('') +
    `</datalist>`;

  const daysHtml = OPEN_DAYS.map(d => {
    const members = editingMasterConfig[d] || [];
    const chipsHtml = members.map((name, idx) => `
      <span class="master-chip">
        ${esc(name)}
        <button type="button" onclick="removeMasterMember('${d}', ${idx})">×</button>
      </span>
    `).join('');

    return `
      <div class="form-group master-day-group">
        <label>${esc(d)}曜日の固定メンバー (${members.length}名)</label>
        <div class="master-chips-container">${chipsHtml}</div>
        <div class="master-add-row">
          <input type="text" id="master-input-${d}" list="master-name-suggestions" placeholder="名前を入力（候補から選択）" onkeydown="if(event.key==='Enter'){event.preventDefault();addMasterMember('${d}');}">
          <button type="button" class="btn-action" onclick="addMasterMember('${d}')">追加</button>
        </div>
      </div>
    `;
  }).join('');

  container.innerHTML = datalistHtml + daysHtml;
}

function addMasterMember(day) {
  const input = document.getElementById(`master-input-${day}`);
  if (!input) return;
  const val = normName(input.value);
  if (!val) return;

  if (!editingMasterConfig[day]) editingMasterConfig[day] = [];
  if (!editingMasterConfig[day].includes(val)) {
    editingMasterConfig[day].push(val);
  }
  renderMasterConfigInputs();
  setTimeout(() => {
    const nextInput = document.getElementById(`master-input-${day}`);
    if (nextInput) nextInput.focus();
  }, 50);
}

function removeMasterMember(day, idx) {
  if (editingMasterConfig[day] && editingMasterConfig[day][idx] !== undefined) {
    editingMasterConfig[day].splice(idx, 1);
    renderMasterConfigInputs();
  }
}

function saveMasterConfig() {
  masterConfig = sanitizeMaster(editingMasterConfig);
  dirty.master = true;
  closeModal('master-modal');
  saveStorage();
  alert('固定パターンを更新しました！\n（個別変更は維持されます）');
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

    let actions = '';
    if (canOperateOn(item.name)) {
      if (item.type === 'free') {
        actions = `<button class="btn-action btn-cancel" data-action="remove-free" data-index="${index}">削除</button>`;
      } else if (item.type === 'transfer' || item.type === 'special_transfer') {
        actions = `<button class="btn-action btn-cancel" data-action="cancel-transfer" data-index="${index}">振替取消</button>`;
      } else {
        actions = `
          <button class="btn-action" data-action="reschedule" data-index="${index}">振替</button>
          <button class="btn-action" style="border-color:#52796f; color:#52796f;" data-action="special" data-index="${index}">特例申請</button>`;
      }
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

/* ============ ダッシュボード・月間カレンダー ============ */
let currentCalendarYear = new Date().getFullYear();
let currentCalendarMonth = new Date().getMonth();

function changeCalendarMonth(delta) {
  currentCalendarMonth += delta;
  if (currentCalendarMonth < 0) {
    currentCalendarMonth = 11;
    currentCalendarYear--;
  } else if (currentCalendarMonth > 11) {
    currentCalendarMonth = 0;
    currentCalendarYear++;
  }
  renderCalendar();
}

function renderCalendar() {
  const titleEl = document.getElementById('calendar-month-title');
  if (titleEl) titleEl.textContent = `${currentCalendarYear}年${currentCalendarMonth + 1}月`;

  const gridEl = document.getElementById('calendar-grid');
  if (!gridEl) return;

  const firstDay = new Date(currentCalendarYear, currentCalendarMonth, 1);
  const lastDay = new Date(currentCalendarYear, currentCalendarMonth + 1, 0);
  const totalDays = lastDay.getDate();
  const startDayOfWeek = firstDay.getDay();

  const todayStr = formatDate(new Date());
  let html = '';

  for (let i = 0; i < startDayOfWeek; i++) {
    html += `<div class="cal-cell other-month"></div>`;
  }

  for (let day = 1; day <= totalDays; day++) {
    const d = new Date(currentCalendarYear, currentCalendarMonth, day);
    const dateStr = formatDate(d);
    const dayOfWeek = d.getDay();
    const isToday = dateStr === todayStr;
    const isSun = dayOfWeek === 0;
    const isSat = dayOfWeek === 6;

    let cellClass = 'cal-cell';
    if (isToday) cellClass += ' is-today';
    if (isSun) cellClass += ' is-sunday';
    if (isSat) cellClass += ' is-saturday';

    if (isSun) {
      html += `
        <div class="cal-cell is-sunday">
          <span class="cal-date-num">${day}</span>
          <span class="cal-badge count-off">休み</span>
        </div>`;
    } else {
      const staffList = getShiftObjectsForDate(dateStr);
      const count = staffList.length;
      let badgeClass = 'count-ok';
      if (count < MIN_STAFF) badgeClass = 'count-low';
      else if (count >= MAX_STAFF) badgeClass = 'count-full';

      html += `
        <div class="${cellClass}" onclick="onCalendarDateClick('${dateStr}')">
          <span class="cal-date-num">${day}</span>
          <span class="cal-badge ${badgeClass}">${count}名</span>
        </div>`;
    }
  }

  gridEl.innerHTML = html;
}

function onCalendarDateClick(dateStr) {
  switchView('shift-detail', dateStr);
}

function switchView(viewName, targetDateStr) {
  const dashEl = document.getElementById('dashboard-view');
  const detailEl = document.getElementById('shift-detail-view');
  if (!dashEl || !detailEl) return;

  if (targetDateStr) {
    jumpToDate(targetDateStr);
  }

  if (viewName === 'dashboard') {
    dashEl.style.display = 'block';
    detailEl.style.display = 'none';
  } else {
    dashEl.style.display = 'none';
    detailEl.style.display = 'block';
  }
}

function renderUpcomingSchedule() {
  const container = document.getElementById('upcoming-schedule-list');
  if (!container) return;

  const today = new Date();
  const list = [];
  let current = new Date(today);

  while (list.length < 3) {
    if (current.getDay() !== 0) {
      list.push(new Date(current));
    }
    current.setDate(current.getDate() + 1);
  }

  container.innerHTML = list.map(d => {
    const dateStr = formatDate(d);
    const dayName = WEEKDAYS[d.getDay()];
    const members = getShiftObjectsForDate(dateStr);
    const count = members.length;

    return `
      <div class="upcoming-card" onclick="onCalendarDateClick('${dateStr}')">
        <div>
          <div class="upcoming-date">${d.getMonth() + 1}月${d.getDate()}日 (${dayName})</div>
          <div class="upcoming-detail">出勤メンバー: ${count}名 (${members.map(m => esc(m.name)).join(', ') || 'なし'})</div>
        </div>
        <span class="upcoming-badge">${count}名出勤</span>
      </div>`;
  }).join('');
}

function renderTransferHistory() {
  const container = document.getElementById('transfer-history-list');
  if (!container) return;

  const transfers = [];
  Object.entries(overrides).forEach(([dateStr, obj]) => {
    (obj.added || []).forEach(item => {
      if (typeof item === 'object' && item.type === 'transfer' && item.originDate) {
        transfers.push({
          name: item.name,
          originDate: item.originDate,
          targetDate: dateStr
        });
      }
    });
  });

  if (transfers.length === 0) {
    container.innerHTML = `<div class="empty-state">現在、振替の履歴はありません</div>`;
    return;
  }

  const recent = transfers.slice(-5).reverse();
  container.innerHTML = recent.map(t => {
    return `
      <div class="transfer-card">
        <div class="transfer-card-header">
          <span class="transfer-member-name">${esc(t.name)}</span>
          ${canOperateOn(t.name) ? `<button class="btn-action btn-cancel" data-hist-cancel data-name="${esc(t.name)}" data-origin="${esc(t.originDate)}" data-target="${esc(t.targetDate)}">取消</button>` : ''}
        </div>
        <div class="transfer-route">
          <span class="date-pill origin">${esc(t.originDate)}</span>
          <span class="route-arrow">➔</span>
          <span class="date-pill target">${esc(t.targetDate)}</span>
        </div>
      </div>`;
  }).join('');
}

function renderDashboard() {
  renderUpcomingSchedule();
  renderTransferHistory();
  renderCalendar();
}

function render() {
  renderDashboard();
  renderTabs();
  renderContent();
}
render();

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
  if (!/^\d{4}-\d{2}-\d{2}$/.test(targetDate)) return '日付の形式が正しくありません。';
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

async function removeFreeShift(item) {
  if (!canOperateOn(item.name)) {
    alert('ご自身のシフトのみ削除できます。');
    return;
  }
  if (await askConfirm(`${item.name}さんの自由練習を削除しますか？`)) {
    removeMember(selectedDateStr, item);
    saveStorage();
  }
}

/* ============ 特例申請 ============ */
function openSpecialRequestModal(name, index) {
  if (!canOperateOn(name)) {
    alert('ご自身のシフトのみ申請できます。');
    return;
  }
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
  if (!canOperateOn(name)) {
    alert('ご自身のシフトのみ振替できます。');
    return;
  }
  const dayName = getDayName(selectedDateStr);
  if (currentUserRole !== 'admin' && getRescheduleUsed(name, dayName) >= MAX_RESCHEDULE_PER_DAY) {
    alert(`${name}さんの【${dayName}曜日枠】の振替上限（${MAX_RESCHEDULE_PER_DAY}回）に達しています。\n上限を超える場合は「特例申請」ボタンから管理者に申請してください。`);
    return;
  }
  if (currentUserRole !== 'admin' && getShiftObjectsForDate(selectedDateStr).length - 1 < MIN_STAFF) {
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

  if (!canOperateOn(name)) {
    alert('ご自身のシフトのみ振替できます。');
    closeModal('reschedule-modal');
    return;
  }

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
  if (currentUserRole !== 'admin' && used >= MAX_RESCHEDULE_PER_DAY) {
    alert(`${dayName}曜日枠の振替上限に達しています。`);
    return;
  }

  if (currentUserRole !== 'admin' && members.length - 1 < MIN_STAFF) {
    alert(`振替すると ${selectedDateStr} が${MIN_STAFF}名未満になります。\n代理を立ててください。`);
    closeModal('reschedule-modal');
    return;
  }

  removeMember(selectedDateStr, item);
  addMember(targetDate, { name, originDate: selectedDateStr, type: 'transfer' });
  updateRescheduleCount(name, dayName, 1);

  closeModal('reschedule-modal');
  saveStorage();
  alert(`${name}さんを ${targetDate} へ振替しました。\n（${dayName}曜枠 振替残り: ${Math.max(0, MAX_RESCHEDULE_PER_DAY - (used + 1))}回）`);
}

async function cancelReschedule(item, targetDate = selectedDateStr) {
  if (!canOperateOn(item.name)) {
    alert('ご自身の振替のみ取り消せます。');
    return;
  }
  if (!(await askConfirm(`${item.name}さんの振替を取り消し、元に戻しますか？`))) return;

  // 旧データ等で元の日付が無い場合は、元の枠に戻せないので振替枠の削除のみ行う
  const originDate = item.originDate;

  removeMember(targetDate, item);

  if (!originDate) {
    saveStorage();
    alert(`${item.name}さんの振替枠を削除しました。\n（元の日付が記録されていないため、元の枠への復元はできません）`);
    return;
  }

  // 元の日に既にいる場合は二重登録しない
  if (!hasMember(originDate, item.name)) {
    addMember(originDate, { name: item.name, originDate, type: 'fixed' });
  }
  if (item.type !== 'special_transfer') {
    updateRescheduleCount(item.name, getDayName(originDate), -1);
  }

  saveStorage();
  alert(`${item.name}さんの振替を取り消し、${originDate} の枠に戻しました。`);
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
const dayTabsEl = document.getElementById('day-tabs');
if (dayTabsEl) {
  dayTabsEl.addEventListener('click', e => {
    const tab = e.target.closest('.tab-item[data-date]');
    if (tab) selectDate(tab.dataset.date);
  });
}

const memberListEl = document.getElementById('member-list');
if (memberListEl) {
  memberListEl.addEventListener('click', e => {
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
}

const historyListEl = document.getElementById('transfer-history-list');
if (historyListEl) {
  historyListEl.addEventListener('click', e => {
    const btn = e.target.closest('button[data-hist-cancel]');
    if (!btn) return;
    const { name, origin, target } = btn.dataset;
    cancelReschedule({ name, originDate: origin, type: 'transfer' }, target);
  });
}

const reqListEl = document.getElementById('requests-list');
if (reqListEl) {
  reqListEl.addEventListener('click', e => {
    const btn = e.target.closest('button[data-req-action]');
    if (!btn) return;
    const id = Number(btn.dataset.id);
    if (btn.dataset.reqAction === 'approve') approveRequest(id);
    else if (btn.dataset.reqAction === 'reject') rejectRequest(id);
  });
}

/* ============ 起動 ============ */
if ('serviceWorker' in navigator) {
  navigator.serviceWorker.register('sw.js').catch(err => console.warn('SW registration failed', err));
}

// type="module" ではHTMLのonclickから関数が見えないので、windowに公開する
Object.assign(window, {
  handleLogin, handleLogout, toggleDropdownMenu, openRequestsModal, openMasterConfig,
  openDataModal, changeWeek, addFreeShift, toggleReqTypeUI, closeModal, submitSpecialRequest,
  saveMasterConfig, executeReschedule, exportData, importData, resetRescheduleCounts, resetAllData,
  switchView, changeCalendarMonth, onCalendarDateClick,
  showSignup, showLogin, handleSignup, openRolesModal, changeUserRole, sendPasswordResetEmailForUser, toggleUserDetail,
  addMasterMember, removeMasterMember
});
