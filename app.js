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
function isStaffRole() {
  return currentUserRole === 'admin' || currentUserRole === 'executive';
}

function requireStaff() {
  if (!isStaffRole()) {
    alert('管理者または幹部のみ実行できます。');
    return false;
  }
  return true;
}

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

// ログインID → Firebaseのメールアドレス。
// 新規登録者は usernames/{ユーザー名} に本物のメールを保存している。無ければ旧方式（仮ドメイン）。
async function resolveLoginEmail(id) {
  if (id.includes('@')) return id; // メールアドレスを直接入力した場合
  try {
    const snap = await getDoc(doc(db, 'usernames', id));
    if (snap.exists() && snap.data().email) return snap.data().email;
  } catch (e) {
    console.warn('Username lookup failed:', e);
  }
  return `${id}@${LOGIN_EMAIL_DOMAIN}`;
}

async function handleLogin(e) {
  e.preventDefault();
  const id = document.getElementById('login-id').value.trim().toLowerCase();
  const pass = document.getElementById('login-pass').value;
  const errorDiv = document.getElementById('login-error');
  try {
    await signInWithEmailAndPassword(auth, await resolveLoginEmail(id), pass);
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
  let profileMissing = false;
  try {
    const userDocSnap = await getDoc(doc(db, 'users', user.uid));
    if (userDocSnap.exists()) {
      const uData = userDocSnap.data();
      role = computeRole(uData);
      fullName = uData.fullName || '';
    } else {
      const legacyAdminSnap = await getDoc(doc(db, 'admins', user.uid));
      if (legacyAdminSnap.exists()) role = 'admin';
      else profileMissing = true;
    }
  } catch (e) {
    console.warn('Role fetch warning:', e);
  }

  // アプリ側で削除されたユーザー（プロフィールが無い）はログインさせない。登録処理中は除く。
  if (profileMissing && !signupInProgress) {
    await signOut(auth);
    const errorDiv = document.getElementById('login-error');
    if (errorDiv) errorDiv.style.display = 'block';
    return;
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

  const headerUserInfo = document.getElementById('header-user-info');
  if (headerUserInfo) {
    if (currentMemberName) {
      const roleStr = ROLE_LABELS[currentUserRole] || 'ユーザー';
      headerUserInfo.innerHTML = `<strong>${esc(currentMemberName)}</strong> さん（${roleStr}）| 曜日ごとに5回まで振替可能`;
    } else {
      headerUserInfo.textContent = '曜日ごとに1人5回まで振替可能';
    }
  }

  const itemRoles = document.getElementById('item-roles');
  const itemMaster = document.getElementById('item-master');
  const itemData = document.getElementById('item-data');
  // 幹部もadminと同じメニューを表示（データ管理の操作・adminへの権限変更は各処理で管理者のみに制限）
  if (itemRoles) itemRoles.style.display = hasMenu ? 'block' : 'none';
  if (itemMaster) itemMaster.style.display = hasMenu ? 'block' : 'none';
  if (itemData) itemData.style.display = hasMenu ? 'block' : 'none';
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
  if (!requireStaff()) return;
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
    const isExecViewer = currentUserRole !== 'admin';
    const lockRole = isExecViewer && role === 'admin';  // 幹部はadminの権限を変更できない
    const adminOpt = isExecViewer && role !== 'admin' ? 'disabled' : ''; // 幹部はadminに昇格できない
    return `
      <div class="role-user-card">
        <div class="role-user-row">
          <button class="role-user-name" onclick="toggleUserDetail('${detailId}')">
            ${esc(u.fullName || '（名前未設定）')}
          </button>
          <select class="role-select" ${lockRole ? 'disabled' : ''} onchange="changeUserRole('${esc(u.uid)}', this.value)">
            <option value="admin" ${role === 'admin' ? 'selected' : ''} ${adminOpt}>admin</option>
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
          ${lockRole ? '' : `<button class="btn-action" style="font-size:11px; color:#c0392b;" onclick="deleteUserAccount('${esc(u.uid)}')">このユーザーを削除</button>`}
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
  if (!requireStaff()) return;
  if (currentUserRole !== 'admin') {
    const target = (allUsers || []).find(x => x.uid === uid);
    if (newRole === 'admin' || (target && computeRole(target) === 'admin')) {
      alert('adminへの権限変更・adminの権限変更は管理者のみ実行できます。');
      renderRolesList();
      return;
    }
  }
  try {
    await setDoc(doc(db, 'users', uid), { role: newRole }, { merge: true });
    alert(`権限を「${ROLE_LABELS[newRole]}」に変更しました。`);
    renderRolesList();
  } catch (err) {
    console.error(err);
    alert('権限の変更に失敗しました。');
  }
}

async function deleteUserAccount(uid) {
  if (!requireStaff()) return;
  const u = (allUsers || []).find(x => x.uid === uid);
  if (!u) return;
  if (currentUserRole !== 'admin' && computeRole(u) === 'admin') {
    alert('adminの削除は管理者のみ実行できます。');
    return;
  }
  if (auth.currentUser && auth.currentUser.uid === uid) {
    alert('自分自身は削除できません。');
    return;
  }
  const ok = await askConfirm(`「${u.fullName || u.username || uid}」を削除しますか？\nこのユーザーはログインできなくなります。\n（Firebase Consoleの Authentication からも削除すると完全に消えます）`);
  if (!ok) return;
  try {
    const batch = writeBatch(db);
    batch.delete(doc(db, 'users', uid));
    if (u.username) batch.delete(doc(db, 'usernames', u.username));
    await batch.commit();
    alert('ユーザーを削除しました。');
  } catch (err) {
    console.error(err);
    alert('ユーザーの削除に失敗しました。');
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
  if (!requireStaff()) return;
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
  if (!requireStaff()) return;
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

// 履歴に出す振替の一覧（一般ユーザーは自分の分のみ。幹部/adminは全員分）
function getVisibleTransfers() {
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
  const mine = n => !!currentMemberName && normName(n) === normName(currentMemberName);
  return isStaffRole() ? transfers : transfers.filter(t => mine(t.name));
}

function transferCardHtml(t) {
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
}

// すべての履歴を月ごとに区切って表示（振替先の日付の月・新しい順）
function renderAllHistory() {
  const container = document.getElementById('all-history-list');
  if (!container) return;
  const list = getVisibleTransfers().sort((a, b) => b.targetDate.localeCompare(a.targetDate));
  if (list.length === 0) {
    container.innerHTML = '<div class="empty-state">現在、振替の履歴はありません</div>';
    return;
  }
  const byMonth = new Map();
  list.forEach(t => {
    const key = t.targetDate.slice(0, 7);
    if (!byMonth.has(key)) byMonth.set(key, []);
    byMonth.get(key).push(t);
  });
  container.innerHTML = [...byMonth.entries()].map(([key, items]) => {
    const [y, m] = key.split('-');
    return `
      <div style="margin-bottom:16px;">
        <div style="font-weight:700; font-size:14px; color:var(--green-deep); padding:6px 0; border-bottom:2px solid var(--line); margin-bottom:8px;">
          ${y}年${Number(m)}月 <span style="font-size:12px; color:var(--ink-sub); font-weight:600;">（${items.length}件）</span>
        </div>
        <div class="transfer-list">${items.map(transferCardHtml).join('')}</div>
      </div>`;
  }).join('');
}

function openAllHistory() {
  renderAllHistory();
  document.getElementById('all-history-modal').style.display = 'flex';
}

function renderTransferHistory() {
  const container = document.getElementById('transfer-history-list');
  if (!container) return;

  const staff = isStaffRole();
  const visible = getVisibleTransfers();

  // 「すべて見る」画面を開いている間は、そちらも最新に更新
  const allModal = document.getElementById('all-history-modal');
  if (allModal && allModal.style.display === 'flex') renderAllHistory();

  const title = document.getElementById('transfer-history-title');
  if (title) title.textContent = staff ? '振替状況・履歴' : '自分の振替状況・履歴';

  const pendingHtml = staff
    ? pendingRequests.filter(r => r.type === 'extension_transfer').map(req => `
      <div class="transfer-card" style="border-color: var(--amber, #d9a441);">
        <div class="transfer-card-header">
          <span class="transfer-member-name">${esc(req.name)}</span>
          <span class="request-type-badge req-special">振替日程延長申請（承認待ち）</span>
        </div>
        <div class="transfer-route">
          <span class="date-pill origin">${esc(req.originalDate)}</span>
          <span class="route-arrow">➔</span>
          <span class="date-pill target">${esc(req.targetDate)}</span>
        </div>
        <div class="request-reason">理由: ${esc(req.reason)}</div>
        <div style="display:flex; gap:6px; justify-content:flex-end; margin-top:8px;">
          <button class="btn-action btn-cancel" data-req-action="reject" data-id="${Number(req.id)}">却下</button>
          <button class="btn-main" style="padding: 6px 12px; font-size:12px; flex:initial;" data-req-action="approve" data-id="${Number(req.id)}">承認</button>
        </div>
      </div>`).join('')
    : '';

  if (visible.length === 0 && !pendingHtml) {
    container.innerHTML = `<div class="empty-state">現在、振替の履歴はありません</div>`;
    return;
  }

  const recent = visible.slice(-5).reverse();
  const moreBtn = visible.length > 5
    ? `<button type="button" class="link-btn" onclick="openAllHistory()">すべて見る（${visible.length}件・月別）</button>`
    : '';
  container.innerHTML = pendingHtml + recent.map(transferCardHtml).join('') + moreBtn;
}

/* ============ マイシフト・自分の振替 ============ */
let quickSelectedOriginDate = '';
let quickSelectedTargetDate = '';

function renderMyShift() {
  const container = document.getElementById('my-shift-container');
  const userBadge = document.getElementById('my-shift-user-badge');
  if (!container) return;

  if (!currentMemberName) {
    if (userBadge) userBadge.textContent = '未ログイン';
    container.innerHTML = `
      <div style="text-align: center; padding: 24px 16px; color: var(--text-sub); font-size: 13px;">
        ログインすると、ここにあなたの出勤予定と振替ボタンが表示されます。
      </div>`;
    return;
  }

  const roleLabel = ROLE_LABELS[currentUserRole] || 'ユーザー';
  if (userBadge) {
    userBadge.textContent = `${esc(currentMemberName)}（${roleLabel}）`;
  }

  // 担当曜日（固定枠）の確認
  const myFixedDays = OPEN_DAYS.filter(d => (masterConfig[d] || []).map(normName).includes(normName(currentMemberName)));

  // 各曜日の振替残数
  const countsHtml = OPEN_DAYS.map(d => {
    const isMyDay = myFixedDays.includes(d);
    const used = getRescheduleUsed(currentMemberName, d);
    const remaining = Math.max(0, MAX_RESCHEDULE_PER_DAY - used);
    if (!isMyDay && used === 0) return '';
    return `<span class="count-pill">${esc(d)}曜枠: <strong>残${remaining}回</strong> (${used}/${MAX_RESCHEDULE_PER_DAY}使用)</span>`;
  }).filter(Boolean).join('');

  // 今後42日（6週間）の予定を走査して自分のシフトを収集
  const today = new Date();
  today.setHours(0, 0, 0, 0);
  const mySchedules = [];

  for (let i = 0; i < 42; i++) {
    const d = new Date(today);
    d.setDate(today.getDate() + i);
    if (d.getDay() === 0) continue; // 日曜日は活動なし

    const dateStr = formatDate(d);
    const dayName = getDayName(dateStr);
    const members = getShiftObjectsForDate(dateStr);
    const myItem = members.find(m => normName(m.name) === normName(currentMemberName));

    if (myItem) {
      mySchedules.push({
        dateStr,
        dayName,
        d,
        item: myItem,
        totalStaff: members.length
      });
    }
  }

  let scheduleListHtml = '';
  if (mySchedules.length === 0) {
    scheduleListHtml = `
      <div style="text-align: center; padding: 24px 16px; background: #fff; border: 1px dashed var(--line); border-radius: 10px;">
        <p style="font-size: 13px; font-weight: bold; color: var(--text);">直近の出勤予定が登録されていません</p>
        <p style="font-size: 11px; color: var(--text-sub); margin-top: 4px; margin-bottom: 12px;">
          担当の曜日（固定枠）を登録すると、毎週の予定が自動表示され振替できるようになります。
        </p>
        <button class="btn-main" style="font-size: 12px; padding: 6px 14px; margin: auto;" onclick="openMyFixedDayModal()">
          ＋ 出勤担当曜日（固定枠）を設定する
        </button>
      </div>`;
  } else {
    scheduleListHtml = `
      <div class="my-schedule-list">
        ${mySchedules.map(({ dateStr, dayName, d, item, totalStaff }) => {
          let typeTag = '';
          const isTransfer = item.type === 'transfer' || item.type === 'special_transfer';
          const isFree = item.type === 'free';
          const isFixed = item.type === 'fixed' || (!isTransfer && !isFree);

          if (isTransfer) {
            typeTag = `<span class="tag-type tag-transfer" style="font-size:10px;">振替枠 (${esc(item.originDate || '')}から)</span>`;
          } else if (isFree) {
            typeTag = `<span class="tag-type tag-free" style="font-size:10px;">自由練習</span>`;
          } else {
            typeTag = `<span class="tag-type" style="background:var(--primary-light); color:var(--primary-dark); font-size:10px;">固定枠</span>`;
          }

          // 人数チェック（回答A2: 6人ジャストなら振替時に代理が必要）
          const staffStatusBadge = totalStaff < MIN_STAFF
            ? `<span style="color:var(--danger); font-size:11px; font-weight:bold;">⚠️ 人員不足 (${totalStaff}名)</span>`
            : totalStaff === MIN_STAFF
              ? `<span style="color:var(--warning); font-size:11px; font-weight:bold;">⚠️ 6名出勤中 (振替は要代理)</span>`
              : `<span style="color:var(--primary); font-size:11px;">〇 出勤 ${totalStaff}名</span>`;

          let actionButtons = '';
          if (isFixed) {
            actionButtons = `
              <button class="btn-reschedule-quick" onclick="openQuickRescheduleModal('${esc(dateStr)}')">
                ⇄ この日を振替する
              </button>
              <button class="btn-action" style="font-size:11px; border-color:var(--line); color:var(--text-sub);" onclick="jumpToShiftDetail('${esc(dateStr)}')">
                詳細・特例申請
              </button>`;
          } else if (isTransfer) {
            actionButtons = `
              <button class="btn-action btn-cancel" style="font-size:12px;" onclick="cancelReschedule({ name: '${esc(currentMemberName)}', originDate: '${esc(item.originDate || '')}', type: '${esc(item.type)}' }, '${esc(dateStr)}')">
                振替取消（${esc(item.originDate || '元の日')}に戻す）
              </button>`;
          } else if (isFree) {
            actionButtons = `
              <button class="btn-action btn-cancel" style="font-size:12px;" onclick="removeFreeShift({ name: '${esc(currentMemberName)}', originDate: '${esc(dateStr)}', type: 'free' })">
                自由練習を削除
              </button>`;
          }

          return `
            <div class="my-schedule-item">
              <div class="my-schedule-header">
                <div class="my-schedule-date">
                  ${d.getMonth() + 1}月${d.getDate()}日 (${esc(dayName)}) ${typeTag}
                </div>
                ${staffStatusBadge}
              </div>
              <div class="my-schedule-actions">
                ${actionButtons}
              </div>
            </div>`;
        }).join('')}
      </div>`;
  }

  container.innerHTML = `
    <div class="my-profile-banner">
      <div class="my-profile-info">
        <div class="my-avatar-icon">👤</div>
        <div>
          <div class="my-name-text">
            ${esc(currentMemberName)}
            <span class="my-role-badge">${roleLabel}</span>
          </div>
          <div style="font-size: 11px; color: var(--text-sub); margin-top: 2px;">
            固定出勤: ${myFixedDays.length > 0 ? myFixedDays.map(d => d + '曜').join('・') : '未設定'}
            <button type="button" style="background:none; border:none; color:var(--primary); font-size:11px; font-weight:bold; cursor:pointer; text-decoration:underline; margin-left:4px;" onclick="openMyFixedDayModal()">
              [変更/登録]
            </button>
          </div>
        </div>
      </div>
      <div class="my-counts-badges">
        ${countsHtml || '<span class="count-pill">振替回数: 未使用</span>'}
      </div>
    </div>
    ${scheduleListHtml}
  `;
}

function openQuickRescheduleModal(originDateStr) {
  quickSelectedOriginDate = originDateStr;
  quickSelectedTargetDate = '';

  const originLabel = document.getElementById('quick-reschedule-origin-label');
  const originD = new Date(originDateStr.replace(/-/g, '/'));
  if (originLabel) {
    originLabel.textContent = `${originD.getFullYear()}年${originD.getMonth() + 1}月${originD.getDate()}日 (${getDayName(originDateStr)})`;
  }

  const warningDiv = document.getElementById('quick-reschedule-warning');
  const submitBtn = document.getElementById('quick-reschedule-submit-btn');
  const members = getShiftObjectsForDate(originDateStr);
  const totalStaff = members.length;
  const dayName = getDayName(originDateStr);
  const used = getRescheduleUsed(currentMemberName, dayName);

  let isBlocked = false;
  let warnMsg = '';

  // 振替上限チェック
  if (currentUserRole !== 'admin' && used >= MAX_RESCHEDULE_PER_DAY) {
    isBlocked = true;
    warnMsg = `【${dayName}曜日枠】の振替上限（${MAX_RESCHEDULE_PER_DAY}回）に達しています。これ以上振替できません。特別振替が必要な場合は「特例申請」を行ってください。`;
  }
  // 回答A2の人数制限チェック（従来通り6名未満になる場合は振替を禁止）
  else if (currentUserRole !== 'admin' && totalStaff - 1 < MIN_STAFF) {
    isBlocked = true;
    warnMsg = `現在 ${originDateStr} は出勤者が ${totalStaff} 名です。振替すると ${totalStaff - 1} 名となり、最低人数（${MIN_STAFF}名）を下回るため振替できません。先に代理メンバーを立ててください。`;
  }

  if (warningDiv) {
    if (isBlocked) {
      warningDiv.innerHTML = `<div class="staff-alert-banner">⚠️ <strong>振替不可:</strong><br>${esc(warnMsg)}</div>`;
    } else {
      warningDiv.innerHTML = '';
    }
  }

  if (submitBtn) {
    submitBtn.disabled = isBlocked;
  }

  // 候補日リスト（今日以降の活動日をピックアップ）
  renderQuickTargetDatesGrid(originDateStr);

  const customDateInput = document.getElementById('quick-reschedule-custom-date');
  if (customDateInput) {
    customDateInput.value = '';
    setMinDate('quick-reschedule-custom-date');
  }

  document.getElementById('quick-reschedule-origin-date').value = originDateStr;
  document.getElementById('quick-selected-target-date').value = '';

  const modal = document.getElementById('quick-reschedule-modal');
  if (modal) modal.style.display = 'flex';
}

function renderQuickTargetDatesGrid(originDateStr) {
  const grid = document.getElementById('quick-target-dates-grid');
  if (!grid) return;

  const today = new Date();
  today.setHours(0, 0, 0, 0);
  const candidates = [];

  for (let i = 1; i <= 35 && candidates.length < 16; i++) {
    const d = new Date(today);
    d.setDate(today.getDate() + i);
    if (d.getDay() === 0) continue; // 日曜休み

    const dateStr = formatDate(d);
    if (dateStr === originDateStr) continue; // 同じ日は除外

    const members = getShiftObjectsForDate(dateStr);
    const count = members.length;
    const isAlreadyIn = members.some(m => normName(m.name) === normName(currentMemberName));
    const isFull = count >= MAX_STAFF;

    candidates.push({
      dateStr,
      d,
      dayName: getDayName(dateStr),
      count,
      isAlreadyIn,
      isFull
    });
  }

  grid.innerHTML = candidates.map(c => {
    const disabled = c.isAlreadyIn || c.isFull;
    let statusText = '';
    let statusColor = 'var(--primary)';

    if (c.isAlreadyIn) {
      statusText = '出勤予定あり';
      statusColor = 'var(--text-sub)';
    } else if (c.isFull) {
      statusText = '満員 (14名)';
      statusColor = 'var(--danger)';
    } else {
      statusText = `〇 空きあり (${c.count}名)`;
    }

    return `
      <div class="target-date-card ${disabled ? 'disabled' : ''}" 
           id="target-card-${c.dateStr}" 
           onclick="${disabled ? '' : `selectQuickTargetDate('${c.dateStr}')`}">
        <div class="d-name">${c.d.getMonth() + 1}/${c.d.getDate()} (${c.dayName})</div>
        <div class="d-status" style="color: ${statusColor}; font-weight: 600;">${statusText}</div>
      </div>`;
  }).join('');
}

function selectQuickTargetDate(dateStr) {
  quickSelectedTargetDate = dateStr;
  document.getElementById('quick-selected-target-date').value = dateStr;

  document.querySelectorAll('.target-date-card').forEach(el => el.classList.remove('selected'));
  const card = document.getElementById(`target-card-${dateStr}`);
  if (card) card.classList.add('selected');

  const customInput = document.getElementById('quick-reschedule-custom-date');
  if (customInput) customInput.value = dateStr;
}

function onQuickCustomDateSelect(val) {
  if (!val) return;
  quickSelectedTargetDate = val;
  document.getElementById('quick-selected-target-date').value = val;

  document.querySelectorAll('.target-date-card').forEach(el => el.classList.remove('selected'));
  const card = document.getElementById(`target-card-${val}`);
  if (card) card.classList.add('selected');
}

async function confirmQuickReschedule() {
  const originDate = document.getElementById('quick-reschedule-origin-date').value;
  const targetDate = document.getElementById('quick-selected-target-date').value;

  if (!originDate) {
    alert('振替元の日付が不正です。');
    return;
  }
  if (!targetDate) {
    alert('振替希望日を選択してください。');
    return;
  }

  const err = validateTargetDate(targetDate, originDate, currentMemberName);
  if (err) {
    alert(err);
    return;
  }

  const dayName = getDayName(originDate);
  const used = getRescheduleUsed(currentMemberName, dayName);

  if (currentUserRole !== 'admin' && used >= MAX_RESCHEDULE_PER_DAY) {
    alert(`${dayName}曜日枠の振替上限（${MAX_RESCHEDULE_PER_DAY}回）に達しています。`);
    return;
  }

  const originMembers = getShiftObjectsForDate(originDate);
  if (currentUserRole !== 'admin' && originMembers.length - 1 < MIN_STAFF) {
    alert(`振替すると ${originDate} の出勤者が ${originMembers.length - 1} 名となり、最低人数（${MIN_STAFF}名）を下回るため振替できません。\n事前に代理メンバーを立ててください。`);
    return;
  }

  const item = originMembers.find(m => normName(m.name) === normName(currentMemberName));
  if (!item) {
    alert(`振替対象のシフトが見つかりませんでした。画面を再読み込みしてください。`);
    return;
  }

  // 振替実行
  removeMember(originDate, item);
  addMember(targetDate, { name: currentMemberName, originDate, type: 'transfer' });
  updateRescheduleCount(currentMemberName, dayName, 1);

  closeModal('quick-reschedule-modal');
  await saveStorage();

  const targetD = new Date(targetDate.replace(/-/g, '/'));
  alert(`${currentMemberName}さんを ${targetD.getMonth() + 1}月${targetD.getDate()}日 (${getDayName(targetDate)}) へ振り替えました！\n（${dayName}曜枠 残り: ${Math.max(0, MAX_RESCHEDULE_PER_DAY - (used + 1))}回）`);
}

function openMyFixedDayModal() {
  if (!currentMemberName) {
    alert('ログインしてください。');
    return;
  }
  const currentDays = OPEN_DAYS.filter(d => (masterConfig[d] || []).map(normName).includes(normName(currentMemberName)));

  const checkboxes = document.querySelectorAll('input[name="my-day"]');
  checkboxes.forEach(cb => {
    cb.checked = currentDays.includes(cb.value);
  });

  const modal = document.getElementById('my-fixed-day-modal');
  if (modal) modal.style.display = 'flex';
}

async function saveMyFixedDays() {
  if (!currentMemberName) return;
  const checkedDays = Array.from(document.querySelectorAll('input[name="my-day"]:checked')).map(cb => cb.value);

  // masterConfig を更新
  OPEN_DAYS.forEach(d => {
    if (!masterConfig[d]) masterConfig[d] = [];

    const normList = masterConfig[d].map(normName);
    const hasMe = normList.includes(normName(currentMemberName));

    if (checkedDays.includes(d)) {
      if (!hasMe) masterConfig[d].push(currentMemberName);
    } else {
      if (hasMe) masterConfig[d] = masterConfig[d].filter(n => normName(n) !== normName(currentMemberName));
    }
  });

  dirty.master = true;
  closeModal('my-fixed-day-modal');
  await saveStorage();
  alert('出勤担当曜日の設定を保存しました！');
}

function jumpToShiftDetail(dateStr) {
  switchView('shift-detail', dateStr);
}

function renderDashboard() {
  renderMyShift();
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

/* ---- 振替可能日程ルール ----
   ・振替元の前後 TRANSFER_WINDOW_DAYS 日以内（例: 10/21 → 10/15〜10/27）
   ・自分の固定曜日以外の日
   上記を満たせば自動確定。期間を超える日は「振替日程延長申請」で幹部/adminの承認が必要。 */
const TRANSFER_WINDOW_DAYS = 6;

function addDays(dateStr, n) {
  const d = new Date(dateStr.replace(/-/g, '/'));
  d.setDate(d.getDate() + n);
  return formatDate(d);
}

function getTransferWindow(originDate) {
  return { min: addDays(originDate, -TRANSFER_WINDOW_DAYS), max: addDays(originDate, TRANSFER_WINDOW_DAYS) };
}

function isWithinTransferWindow(targetDate, originDate) {
  const w = getTransferWindow(originDate);
  return targetDate >= w.min && targetDate <= w.max;
}

function getFixedDays(name) {
  const n = normName(name);
  return OPEN_DAYS.filter(d => (masterConfig[d] || []).some(m => normName(m) === n));
}

// 自分の固定曜日への振替ならメッセージを返す
function checkNotFixedDay(targetDate, name) {
  const days = getFixedDays(name);
  if (days.includes(getDayName(targetDate))) {
    return `振替できません。曜日を確認してください。\n（${name}さんの固定曜日: ${days.join('・')}）`;
  }
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
  if (!requireStaff()) return;

  const listDiv = document.getElementById('requests-list');
  if (pendingRequests.length === 0) {
    listDiv.innerHTML = '<p style="font-size:13px; color:var(--text-sub); text-align:center; padding: 20px 0;">届いている特例申請はありません。</p>';
  } else {
    listDiv.innerHTML = pendingRequests.map(req => {
      const isAbsent = req.type === 'absent';
      const badge = isAbsent
        ? '<span class="request-type-badge req-absent">特例欠席</span>'
        : req.type === 'extension_transfer'
          ? '<span class="request-type-badge req-special">振替日程延長</span>'
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

// 申請一覧モーダルが開いているときだけ再描画（履歴パネルから操作した場合は開かない）
function refreshRequestsView() {
  const m = document.getElementById('requests-modal');
  if (m && m.style.display === 'flex') openRequestsModal();
}

function approveRequest(reqId) {
  if (!requireStaff()) return;
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
    refreshRequestsView();
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
  } else if (req.type === 'extension_transfer') {
    const err = validateTargetDate(req.targetDate, req.originalDate, req.name) || checkNotFixedDay(req.targetDate, req.name);
    if (err) { alert(`振替日程延長を実行できません：\n${err}`); return; }

    // 通常振替として確定（振替回数を消費・履歴から取り消し可能）
    removeMember(req.originalDate, item);
    addMember(req.targetDate, { name: req.name, originDate: req.originalDate, type: 'transfer' });
    updateRescheduleCount(req.name, getDayName(req.originalDate), 1);
    alert(`${req.name}さんの振替日程延長（${req.originalDate} ➔ ${req.targetDate}）を承認し、振替を確定しました。`);
  } else {
    return;
  }

  dirty.reqs.add(req.id);
    pendingRequests.splice(reqIndex, 1);
  saveStorage();
  refreshRequestsView();
}

function rejectRequest(reqId) {
  if (!requireStaff()) return;
  if (confirm('この申請を却下しますか？')) {
    dirty.reqs.add(reqId);
    pendingRequests = pendingRequests.filter(r => r.id !== reqId);
    saveStorage();
    refreshRequestsView();
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
  setExtensionMode(false);
  const w = getTransferWindow(selectedDateStr);
  const hint = document.getElementById('reschedule-range-hint');
  if (hint) hint.textContent = `振替可能期間: ${w.min} 〜 ${w.max}（ご自身の固定曜日を除く）`;
  updateRescheduleDateMessage();
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

  const fixedErr = checkNotFixedDay(targetDate, name);
  if (fixedErr) { alert(fixedErr); return; }
  if (!isWithinTransferWindow(targetDate, selectedDateStr)) {
    alert('振替可能期間外です。期間内の日程を選ぶか、「振替日程延長」から申請してください。');
    return;
  }

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

// 日付を選んだ時点で、ルール違反なら赤文字で理由を表示（OKボタンも押せなくする）
function updateRescheduleDateMessage() {
  const msgEl = document.getElementById('reschedule-date-error');
  if (!msgEl) return;
  const modal = document.getElementById('reschedule-modal');
  const extension = !!(modal && modal.dataset.extension === '1');
  const name = document.getElementById('reschedule-member-name').value;
  const target = document.getElementById('reschedule-date-input').value;

  let msg = '';
  if (target && target !== selectedDateStr) {
    msg = validateTargetDate(target, selectedDateStr, name) || checkNotFixedDay(target, name);
    if (!msg) {
      const inWindow = isWithinTransferWindow(target, selectedDateStr);
      if (!extension && !inWindow) msg = '振替可能期間外です。期間内の日程を選ぶか、「振替日程延長」から申請してください。';
      else if (extension && inWindow) msg = '振替可能期間内の日程です。「通常振替に戻る」から振替してください。';
    }
  }
  msgEl.textContent = msg;
  msgEl.style.display = msg ? 'block' : 'none';
  ['reschedule-confirm', 'reschedule-ext-submit'].forEach(id => {
    const b = document.getElementById(id);
    if (b) b.disabled = !!msg;
  });
}

const rescheduleDateInput = document.getElementById('reschedule-date-input');
if (rescheduleDateInput) {
  rescheduleDateInput.addEventListener('input', updateRescheduleDateMessage);
  rescheduleDateInput.addEventListener('change', updateRescheduleDateMessage);
}

/* ---- 振替日程延長申請（振替可能期間外への振替。幹部/adminの承認で確定） ---- */
function setExtensionMode(on) {
  const show = (id, v) => { const el = document.getElementById(id); if (el) el.style.display = v ? '' : 'none'; };
  show('reschedule-ext-group', on);
  show('reschedule-ext-submit', on);
  show('reschedule-confirm', !on);
  const toggle = document.getElementById('reschedule-ext-toggle');
  if (toggle) toggle.textContent = on ? '通常振替に戻る' : '振替日程延長';
  const reason = document.getElementById('reschedule-ext-reason');
  if (reason && !on) reason.value = '';
  const modal = document.getElementById('reschedule-modal');
  if (modal) modal.dataset.extension = on ? '1' : '';
  updateRescheduleDateMessage();
}

function toggleExtensionMode() {
  const modal = document.getElementById('reschedule-modal');
  setExtensionMode(!(modal && modal.dataset.extension === '1'));
}

function submitExtensionRequest() {
  const name = document.getElementById('reschedule-member-name').value;
  const index = parseInt(document.getElementById('reschedule-member-index').value, 10);
  const targetDate = document.getElementById('reschedule-date-input').value;
  const reason = document.getElementById('reschedule-ext-reason').value.trim();

  if (!canOperateOn(name)) {
    alert('ご自身のシフトのみ申請できます。');
    closeModal('reschedule-modal');
    return;
  }
  const item = getShiftObjectsForDate(selectedDateStr)[index];
  if (!item || item.name !== name || item.type !== 'fixed') {
    alert('対象のメンバー情報が変わっています。画面を確認してやり直してください。');
    closeModal('reschedule-modal');
    return;
  }

  const err = validateTargetDate(targetDate, selectedDateStr, name) || checkNotFixedDay(targetDate, name);
  if (err) { alert(err); return; }
  if (isWithinTransferWindow(targetDate, selectedDateStr)) {
    alert('この日程は振替可能期間内です。「振替を確定する」で振替してください。');
    return;
  }
  if (!reason) { alert('延長が必要な理由を入力してください。'); return; }
  if (reason.length > 200) { alert('理由は200文字以内で入力してください。'); return; }

  const dayName = getDayName(selectedDateStr);
  if (currentUserRole !== 'admin' && getRescheduleUsed(name, dayName) >= MAX_RESCHEDULE_PER_DAY) {
    alert(`${dayName}曜日枠の振替上限に達しています。`);
    return;
  }

  const reqObj = {
    id: Date.now(),
    name,
    originalDate: selectedDateStr,
    type: 'extension_transfer',
    reason,
    targetDate,
    createdAt: new Date().toLocaleString('ja-JP')
  };
  setDoc(doc(db, 'requests', String(reqObj.id)), reqObj)
    .catch(() => alert('申請の送信に失敗しました。もう一度お試しください。'));
  closeModal('reschedule-modal');
  alert('振替日程延長を申請しました。幹部・管理者の承認後に振替が確定します。');
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

const allHistoryEl = document.getElementById('all-history-list');
if (allHistoryEl) {
  allHistoryEl.addEventListener('click', e => {
    const btn = e.target.closest('button[data-hist-cancel]');
    if (!btn) return;
    const { name, origin, target } = btn.dataset;
    cancelReschedule({ name, originDate: origin, type: 'transfer' }, target);
  });
}

const historyListEl = document.getElementById('transfer-history-list');
if (historyListEl) {
  historyListEl.addEventListener('click', e => {
    const reqBtn = e.target.closest('button[data-req-action]');
    if (reqBtn) {
      const id = Number(reqBtn.dataset.id);
      if (reqBtn.dataset.reqAction === 'approve') approveRequest(id);
      else if (reqBtn.dataset.reqAction === 'reject') rejectRequest(id);
      return;
    }
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
  toggleExtensionMode, submitExtensionRequest, openAllHistory, showSignup, showLogin, handleSignup, openRolesModal, changeUserRole, sendPasswordResetEmailForUser, deleteUserAccount, toggleUserDetail,
  addMasterMember, removeMasterMember,
  renderMyShift, openQuickRescheduleModal, selectQuickTargetDate, onQuickCustomDateSelect, confirmQuickReschedule,
  openMyFixedDayModal, saveMyFixedDays, jumpToShiftDetail, cancelReschedule, removeFreeShift
});
