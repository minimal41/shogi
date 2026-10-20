/* 千里眼将棋 — 画面と対局の進行
   将棋のルールと AI は engine.js（window.ShogiEngine）。AI の思考は Web Worker で動かす。 */
(function () {
'use strict';
const E = window.ShogiEngine;
if (!E) { document.getElementById('statusText').textContent = '将棋エンジンを読み込めませんでした。ページを再読み込みしてください。'; return; }
const { Position, BLACK, WHITE, FILE, RANK, sqOf, moveToUSI, mFrom, mTo, mPiece, mIsPromo, OWNER } = E;
const MATE_IN_MAX = E.MATE_IN_MAX;

const LEVELS = [
  { name: '入門', desc: '駒の動きを覚えたての人向け。ときどき駒をただで取らせてくれます。', req: { weak: { depth: 1, noise: 260 }, book: true } },
  { name: '初級', desc: '目先の駒得を狙ってきます。王手や詰みの筋はあまり読みません。', req: { weak: { depth: 2, noise: 110 }, book: true } },
  { name: '中級', desc: '3手先まで読み、詰みも見逃しません。手加減は少しだけ。', req: { weak: { depth: 3, noise: 35, seeMates: true }, book: true } },
  { name: '上級', desc: '1手3秒の本気の読み。定跡と詰み探索を使います。', req: { timeMs: 3000, mateNodes: 60000, book: true, ttBits: 20 } },
  { name: '最強', desc: '1手10秒。αβ探索と詰み探索を全力で回す、千里眼の本気です。', req: { timeMs: 10000, mateNodes: 400000, book: true, ttBits: 21 }, explainMs: 6000 },
  { name: '長考', desc: '1手最大30秒。最強の3倍の時間と大きな置換表で、さらに深く読みます。待ち時間は長めです。', req: { timeMs: 30000, mateNodes: 1500000, book: true, ttBits: 22, softRatio: 0.7, easyRatio: 0.5, easyStable: 8, mateTimeCap: 4000 }, explainMs: 10000 },
];
// explainMs: 指したあと（あなたの手番のあいだ）に、理由を言葉にするための読み比べに使う時間
const STORE_KEY = 'senrigan-shogi-v1';
const KANJI = E.KANJI_NUM, ZEN = E.ZEN_NUM;
const HAND_ORDER = [E.HI, E.KA, E.KI, E.GI, E.KE, E.KY, E.FU];
const SIZE_CLASS = [0, 6, 5, 4, 3, 2, 2, 3, 1, 6, 5, 4, 3, 2, 2];
const $ = (id) => document.getElementById(id);

// ---------------------------------------------------------------- state
let G = null;                 // persisted game
const pos = new Position();
let H = null;                 // derived history
let legal = [];
let sel = null;               // { type: 'board', sq } | { type: 'hand', pt }
let promoPending = null;
let thinking = false;
let live = null;              // live search info while thinking
let reading = null;           // last finished reading
let hint = null;              // { from, to, text } | { loading: true }
let resultHidden = false;
let justTo = 0;
let resignArmed = 0;
let view = null;              // ply shown while reviewing the record (null = live position)
let why = null;               // explanation still being worked out: { id, ply, base, lastTo, prev, main, started, ms }
const EXP = window.SenriganExplain;
const whyMemo = EXP ? new EXP.Memo() : null;   // remembers recent wording so explanations don't repeat themselves
const posView = new Position();
function dispPos() { return view === null ? pos : posView; }
function setView(v) {
  if (v === null || v >= G.moves.length) { view = null; }
  else {
    view = Math.max(0, v);
    posView.setSFEN(E.START_SFEN);
    for (const u of G.moves.slice(0, view)) { const m = posView.parseUSI(u); if (!m) break; posView.doMove(m); }
  }
  sel = null;
  render();
}

function newGame(userSide, level) {
  return { v: 1, userSide, level, moves: [], evals: [], result: null, flipped: userSide === WHITE, sound: G ? G.sound : true,
    explain: G ? !!G.explain : false, notes: {}, started: Date.now(), furigoma: false };
}

function rebuild() {
  pos.setSFEN(E.START_SFEN);
  H = { keys: [pos.key()], checks: [pos.inCheck()], kif: [], kifLines: [], lastTo: 0, froms: [], tos: [], caps: [] };
  const ok = [];
  for (const u of G.moves) {
    const m = pos.parseUSI(u);
    if (!m) break;
    applyInternal(m);
    ok.push(u);
  }
  G.moves = ok;
  legal = pos.legalMoves();
}
function applyInternal(m) {
  const disp = E.moveToKIF(pos, m, H.lastTo);
  H.kif.push(disp.replace('同　', '同'));
  let body = disp.slice(1);
  if (mFrom(m) === 0) { if (!body.endsWith('打')) body += '打'; }
  else body += '(' + FILE[mFrom(m)] + RANK[mFrom(m)] + ')';
  H.kifLines.push(body);
  pos.doMove(m);
  H.lastTo = mTo(m);
  H.froms.push(mFrom(m)); H.tos.push(mTo(m)); H.caps.push(E.mCap(m) & 15);
  H.keys.push(pos.key());
  H.checks.push(pos.inCheck());
}
function save() { try { localStorage.setItem(STORE_KEY, JSON.stringify(G)); } catch (e) { /* storage unavailable */ } }
function load() { try { const s = localStorage.getItem(STORE_KEY); if (s) { const g = JSON.parse(s); if (g && g.v === 1 && Array.isArray(g.moves)) return g; } } catch (e) { /* ignore */ } return null; }

// ---------------------------------------------------------------- engine
let worker = null, mode = 'worker', seq = 0, pending = null, localSearcher = null;
let workerKind = 'file';      // 'file' = engine.js を直接 Worker に / 'blob' = 読み込み済みソースから生成
function makeWorker(kind) {
  if (kind === 'file') return new Worker('engine.js');
  // index.html をファイルとして直接開いた場合（file://）は engine.js を Worker にできないため、
  // ページに読み込んだエンジン自身のソースから Blob Worker を作る
  if (!E.workerSource) throw new Error('engine source unavailable');
  const url = URL.createObjectURL(new Blob([E.workerSource], { type: 'text/javascript' }));
  return new Worker(url);
}
function startWorker() {
  worker = null;
  for (const kind of workerKind === 'file' ? ['file', 'blob'] : ['blob']) {
    try { worker = makeWorker(kind); workerKind = kind; break; } catch (err) { worker = null; }
  }
  if (!worker) { mode = 'local'; return; }
  mode = 'worker';
  worker.onmessage = (e) => onEngine(e.data);
  worker.onerror = (e) => {
    if (e && e.preventDefault) e.preventDefault();
    const p = pending;
    pending = null;
    worker = null;
    if (workerKind === 'file') {
      // engine.js を Worker として読めなかった → Blob Worker で再試行
      workerKind = 'blob';
      startWorker();
      if (worker) { if (p) { pending = p; worker.postMessage(p.msg); } return; }
    }
    mode = 'local';
    if (p) runLocal(p.msg, p.purpose);
  };
}
function stopEngine() {
  if (!pending) return;
  pending = null;
  if (worker) { worker.terminate(); worker = null; startWorker(); }
}
function runLocal(msg, purpose) {
  pending = { id: msg.id, purpose, msg };
  const m2 = Object.assign({}, msg);
  if (m2.timeMs) m2.timeMs = Math.min(m2.timeMs, 2500);
  if (m2.mateNodes) m2.mateNodes = Math.min(m2.mateNodes, 40000);
  if (m2.explain) m2.explain = { timeMs: Math.min(m2.explain.timeMs, 1200) };   // this runs on the page itself
  setTimeout(() => {
    if (!pending || pending.id !== msg.id) return;
    localSearcher = localSearcher || new E.Searcher(19);
    E.handleGo(localSearcher, m2, onEngine);
  }, 50);
}
function ask(purpose, extra) {
  const id = ++seq;
  const msg = Object.assign({ type: 'go', id, sfen: E.START_SFEN, moves: G.moves.slice() }, extra);
  if (mode === 'worker' && worker) { pending = { id, purpose, msg }; worker.postMessage(msg); }
  else runLocal(msg, purpose);
}
function onEngine(d) {
  if (d.type === 'explain') { onExplain(d); return; }   // arrives after the move, while you think
  if (!pending || d.id !== pending.id) return;
  if (d.type === 'info') {
    if (pending.purpose === 'ai') { live = d; renderReading(); renderStatus(); }
    return;
  }
  if (d.type !== 'bestmove') return;
  const { purpose, msg } = pending;
  pending = null;
  if (purpose === 'ai') onAIMove(d, msg); else onHint(d);
}
function cancelWhy() {
  why = null;
  if (mode === 'worker' && worker) worker.postMessage({ type: 'cancel-explain' });
  else if (E.cancelExplain) E.cancelExplain(false);
}

function requestAI() {
  if (G.result || pos.stm === G.userSide) return;
  thinking = true; live = null;
  render();
  const L = LEVELS[G.level];
  const req = Object.assign({}, L.req);
  if (G.explain && L.explainMs && EXP) req.explain = { timeMs: L.explainMs };
  startThinkBar(req.timeMs ? (mode === 'local' ? Math.min(req.timeMs, 2500) : req.timeMs) : 0);
  ask('ai', req);
}
function startThinkBar(ms) {
  const bar = $('thinkBar'), fill = $('thinkBarFill');
  if (!ms) { bar.hidden = true; return; }
  fill.style.animation = 'none';
  void fill.offsetWidth;
  fill.style.animation = '';
  fill.style.animationDuration = ms + 'ms';
  bar.hidden = false;
}

function scoreForBlack(score, side) { return side === BLACK ? score : -score; }

function onAIMove(d, msg) {
  thinking = false;
  const aiSide = G.userSide ^ 1;
  const ply = G.moves.length;
  if (!d.book && (d.depth > 0 || d.dfpn || d.mate)) {
    const b = Math.max(-30000, Math.min(30000, scoreForBlack(d.score, aiSide)));
    G.evals = G.evals.filter(e => e.ply < ply);
    G.evals.push({ ply, b, mate: d.mate ? (d.mate > 0 ? (aiSide === BLACK ? d.mate : -d.mate) : (aiSide === BLACK ? d.mate : -d.mate)) : 0 });
  }
  reading = { depth: d.depth, nodes: d.nodes, time: d.time, scoreB: scoreForBlack(d.score, aiSide), mate: d.mate, side: aiSide, pv: d.pv, book: d.book, dfpn: d.dfpn, base: pos.clone(), lastTo: H.lastTo };
  live = null;
  if (d.move === 'resign' || (d.mate < 0 && G.level >= 2)) {
    finish({ winner: G.userSide, reason: '投了', by: aiSide });
    return;
  }
  const m = pos.parseUSI(d.move);
  if (!m) { finish({ winner: G.userSide, reason: '投了', by: aiSide }); return; }
  const prev = ply > 0 ? { from: H.froms[ply - 1], to: H.tos[ply - 1], cap: H.caps[ply - 1], k: H.kif[ply - 1], chain: capChain(ply) } : null;
  const base = reading.base, lastTo = H.lastTo;
  G.moves.push(d.move);
  applyInternal(m);
  justTo = mTo(m);
  if (msg && msg.explain) startWhy(d, ply, base, lastTo, prev, msg.explain.timeMs);
  clack();
  afterMove();
}

// ---------------------------------------------------------------- why this move (explanations)
// pieces taken in the captures played one after another just before ply (most recent first)
function capChain(ply) {
  const out = [];
  for (let i = ply - 1; i >= 0 && H.caps[i] && out.length < 8; i--) out.push(H.caps[i]);
  return out;
}
function startWhy(d, ply, base, lastTo, prev, ms) {
  const main = { move: d.move, score: d.score, depth: d.depth, pv: d.pv, book: d.book, dfpn: d.dfpn, mate: d.mate };
  why = null;
  const hist = G.moves.slice(0, ply);   // the moves before this one (for tempo: who started an exchange)
  if (d.book) { storeWhy({ ply, base, lastTo, prev, main, hist }, null); return; }   // no reading to compare for a book move
  why = { id: d.id, ply, base, lastTo, prev, main, hist, started: Date.now(), ms };
}
function onExplain(d) {
  if (!why || d.id !== why.id) return;
  const w = why;
  why = null;
  storeWhy(w, d.data);
  renderWhy(); renderMoves();
}
function storeWhy(w, data) {
  if (G.moves[w.ply] !== w.main.move) return;   // taken back in the meantime
  let note = null;
  try { note = EXP.build({ base: w.base, lastTo: w.lastTo, prev: w.prev, ply: w.ply, hist: w.hist, data, main: w.main }, whyMemo); } catch (e) { note = null; }
  G.notes[w.ply] = note ? { head: note.head, paras: note.paras, rows: note.rows, foot: note.foot }
    : { head: '', paras: ['この手の理由はうまく言葉にできませんでした。'], rows: [], foot: '' };
  save();
}
function isAIPly(i) { return (i % 2 === 0 ? BLACK : WHITE) !== G.userSide; }

function onHint(d) {
  if (!hint || !hint.loading) return;
  const m = d.move && d.move !== 'resign' ? pos.parseUSI(d.move) : 0;
  if (!m) { hint = { text: '指せる手が見つかりませんでした。' }; renderHint(); return; }
  const side = pos.stm;
  const kif = E.moveToKIF(pos, m, H.lastTo).replace('同　', '同');
  let ev;
  if (d.mate > 0) ev = `${d.mate}手以内の詰みがあります`;
  else ev = '評価値 ' + fmtScore(scoreForBlack(d.score, side));
  hint = { from: mFrom(m), to: mTo(m), pt: mFrom(m) === 0 ? (mPiece(m) & 15) : 0, text: kif, ev };
  render();
}

// ---------------------------------------------------------------- game flow
function canAct() { return view === null && !G.result && !thinking && !promoPending && pos.stm === G.userSide; }

function afterMove() {
  legal = pos.legalMoves();
  sel = null;
  const end = detectEnd();
  if (end) { finish(end); return; }
  save();
  render();
  if (pos.stm !== G.userSide) requestAI();
}

function detectEnd() {
  if (legal.length === 0) return { winner: pos.stm ^ 1, reason: pos.inCheck() ? '詰み' : '手詰まり' };
  if (G.moves.length >= 512) return { winner: -1, reason: '持将棋' };
  const k = H.keys[H.keys.length - 1];
  const idx = [];
  for (let i = 0; i < H.keys.length; i++) if (H.keys[i] === k) idx.push(i);
  if (idx.length >= 4) {
    const first = idx[0], last = idx[idx.length - 1];
    let bAll = true, wAll = true;
    for (let i = first + 1; i <= last; i++) {
      if (i % 2 === 1) { if (!H.checks[i]) bAll = false; } else { if (!H.checks[i]) wAll = false; }
    }
    if (bAll) return { winner: WHITE, reason: '連続王手の千日手' };
    if (wAll) return { winner: BLACK, reason: '連続王手の千日手' };
    return { winner: -1, reason: '千日手' };
  }
  return null;
}

function finish(res) {
  stopEngine();
  thinking = false;
  res.plies = G.moves.length;
  G.result = res;
  resultHidden = false;
  save();
  render();
}

function userMove(m) {
  hint = null;
  sel = null;
  stopEngine();
  G.moves.push(moveToUSI(m));
  applyInternal(m);
  justTo = mTo(m);
  clack();
  afterMove();
}

function startNew() {
  stopEngine();
  const sv = document.querySelector('input[name="side"]:checked').value;
  let side = sv === '1' ? WHITE : BLACK, furi = false;
  if (sv === 'r') { side = Math.random() < 0.5 ? BLACK : WHITE; furi = true; }
  const level = Number(document.querySelector('input[name="level"]:checked').value);
  G = newGame(side, level);
  G.furigoma = furi;
  G.sound = $('optSound').checked;
  G.explain = $('optExplain').checked;
  cancelWhy();
  thinking = false; live = null; reading = null; hint = null; sel = null; promoPending = null; view = null;
  rebuild();
  save();
  render();
  if (furi) toast(side === BLACK ? '振り駒の結果、あなたが先手です' : '振り駒の結果、あなたが後手です');
  if (pos.stm !== G.userSide) requestAI();
}

function undo() {
  closePromo();
  hint = null;
  view = null;
  if (thinking) {
    stopEngine(); thinking = false; live = null;
    G.moves.pop();
  } else {
    if (G.result && G.result.by === G.userSide) { G.result = null; save(); rebuild(); render(); return; }
    const userMoves = G.moves.filter((_, i) => (i % 2 === 0 ? BLACK : WHITE) === G.userSide).length;
    if (userMoves === 0) { toast('戻せる手がありません'); return; }
    G.result = null;
    while (G.moves.length) {
      const mover = (G.moves.length - 1) % 2 === 0 ? BLACK : WHITE;
      G.moves.pop();
      if (mover === G.userSide) break;
    }
  }
  G.evals = G.evals.filter(e => e.ply < G.moves.length);
  for (const k of Object.keys(G.notes)) if (Number(k) >= G.moves.length) delete G.notes[k];
  if (why && why.ply >= G.moves.length) cancelWhy();
  rebuild();
  sel = null;
  save();
  render();
  if (pos.stm !== G.userSide && !G.result) requestAI();
}

function resign() {
  if (G.result) return;
  const now = Date.now();
  if (now - resignArmed > 3000) {
    resignArmed = now;
    $('btnResign').classList.add('armed');
    $('btnResign').textContent = 'もう一度押すと投了';
    setTimeout(() => { if (Date.now() - resignArmed >= 2900) { $('btnResign').classList.remove('armed'); $('btnResign').textContent = '投了する'; } }, 3000);
    return;
  }
  resignArmed = 0;
  $('btnResign').classList.remove('armed');
  $('btnResign').textContent = '投了する';
  finish({ winner: G.userSide ^ 1, reason: '投了', by: G.userSide });
}

function askHint() {
  if (!canAct()) return;
  hint = { loading: true };
  renderHint();
  ask('hint', { timeMs: 2500, mateNodes: 40000, ttBits: 20 });
}

// ---------------------------------------------------------------- input
function onSquare(sq) {
  if (!canAct()) return;
  const p = pos.board[sq];
  if (sel) {
    const cands = legal.filter(m => mTo(m) === sq && (sel.type === 'board' ? mFrom(m) === sel.sq : (mFrom(m) === 0 && (mPiece(m) & 15) === sel.pt)));
    if (cands.length === 1) { userMove(cands[0]); return; }
    if (cands.length > 1) { openPromo(cands); return; }
    if (p && OWNER[p] === G.userSide && !(sel.type === 'board' && sel.sq === sq)) { sel = { type: 'board', sq }; render(); return; }
    sel = null; render(); return;
  }
  if (p && OWNER[p] === G.userSide) { sel = { type: 'board', sq }; render(); }
}
function onHand(pt) {
  if (!canAct()) return;
  sel = (sel && sel.type === 'hand' && sel.pt === pt) ? null : { type: 'hand', pt };
  render();
}
function openPromo(cands) {
  const yes = cands.find(m => mIsPromo(m)), no = cands.find(m => !mIsPromo(m));
  promoPending = { yes, no };
  const t = mPiece(yes) & 15;
  $('promoYes').innerHTML = pieceHTML(t + 8, G.userSide, false) + '<span>成る</span>';
  $('promoNo').innerHTML = pieceHTML(t, G.userSide, false) + '<span>成らない</span>';
  $('promo').hidden = false;
  $('promoYes').focus();
}
function closePromo() { promoPending = null; $('promo').hidden = true; }

// ---------------------------------------------------------------- rendering
const boardEl = $('board');
const squares = [];   // index by visual cell
let focusCell = 40;
function cellToSq(vc, vr) {
  return G.flipped ? sqOf(vc + 1, 9 - vr) : sqOf(9 - vc, vr + 1);
}
function buildBoard() {
  boardEl.textContent = '';
  for (let vr = 0; vr < 9; vr++) for (let vc = 0; vc < 9; vc++) {
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'sq';
    b.tabIndex = (vr * 9 + vc) === focusCell ? 0 : -1;
    b.dataset.cell = String(vr * 9 + vc);
    boardEl.appendChild(b);
    squares.push(b);
  }
  for (const [x, y] of [[1 / 3, 1 / 3], [2 / 3, 1 / 3], [1 / 3, 2 / 3], [2 / 3, 2 / 3]]) {
    const s = document.createElement('span');
    s.className = 'star';
    s.style.left = (x * 100) + '%'; s.style.top = (y * 100) + '%';
    boardEl.appendChild(s);
  }
  boardEl.addEventListener('click', (e) => {
    const b = e.target.closest('.sq');
    if (!b) return;
    const cell = Number(b.dataset.cell);
    setFocusCell(cell, false);
    onSquare(cellToSq(cell % 9, (cell / 9) | 0));
  });
  boardEl.addEventListener('keydown', (e) => {
    const b = e.target.closest('.sq');
    if (!b) return;
    let cell = Number(b.dataset.cell), r = (cell / 9) | 0, c = cell % 9;
    if (e.key === 'ArrowUp') r = Math.max(0, r - 1);
    else if (e.key === 'ArrowDown') r = Math.min(8, r + 1);
    else if (e.key === 'ArrowLeft') c = Math.max(0, c - 1);
    else if (e.key === 'ArrowRight') c = Math.min(8, c + 1);
    else if (e.key === 'Escape') { sel = null; render(); return; }
    else return;
    e.preventDefault();
    setFocusCell(r * 9 + c, true);
  });
}
function setFocusCell(cell, move) {
  squares[focusCell].tabIndex = -1;
  focusCell = cell;
  squares[cell].tabIndex = 0;
  if (move) squares[cell].focus();
}

function glyph(t, c) {
  if (t === E.OU) return c === G.userSide ? '玉' : '王';
  return E.PIECE_CHAR[t];
}
function pieceHTML(t, c, op) {
  return `<span class="pc z${SIZE_CLASS[t]}${t >= E.TO ? ' pro' : ''}${op ? ' op' : ''}"><span class="g">${glyph(t, c)}</span></span>`;
}
function sideMark(c) {
  const fill = c === BLACK ? 'var(--ink)' : 'none';
  return `<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M10 2 L17 7 L17 18 L3 18 L3 7 Z" fill="${fill}" stroke="var(--ink)" stroke-width="1.6" stroke-linejoin="round"/></svg>`;
}
function sqName(sq) { return ZEN[FILE[sq]] + KANJI[RANK[sq]]; }

function render() {
  if (!G) return;
  const bottom = G.flipped ? WHITE : BLACK;
  // coordinates
  const files = $('files'), ranks = $('ranks');
  files.innerHTML = ''; ranks.innerHTML = '';
  for (let vc = 0; vc < 9; vc++) { const s = document.createElement('span'); s.textContent = ZEN[G.flipped ? vc + 1 : 9 - vc]; files.appendChild(s); }
  for (let vr = 0; vr < 9; vr++) { const s = document.createElement('span'); s.textContent = KANJI[G.flipped ? 9 - vr : vr + 1]; ranks.appendChild(s); }

  const P = dispPos();
  const shownPly = view === null ? H.froms.length : view;
  const lastFrom = shownPly > 0 ? H.froms[shownPly - 1] : 0;
  const lastTo = shownPly > 0 ? H.tos[shownPly - 1] : 0;
  const targets = new Map();
  if (sel && canAct()) {
    for (const m of legal) {
      if (sel.type === 'board' ? mFrom(m) === sel.sq : (mFrom(m) === 0 && (mPiece(m) & 15) === sel.pt)) targets.set(mTo(m), true);
    }
  }
  const inChk = (view !== null || !G.result) && P.inCheck();
  const kingInCheck = inChk ? P.kingSq[P.stm] : 0;
  for (let cell = 0; cell < 81; cell++) {
    const vc = cell % 9, vr = (cell / 9) | 0;
    const sq = cellToSq(vc, vr);
    const b = squares[cell];
    const p = P.board[sq];
    let cls = 'sq';
    if (sq === lastTo || sq === lastFrom) cls += ' last';
    if (sel && sel.type === 'board' && sel.sq === sq) cls += ' sel';
    if (targets.has(sq)) cls += ' target' + (p ? ' cap' : '');
    if (sq === kingInCheck) cls += ' check';
    if (view === null && hint && !hint.loading && (sq === hint.to || (hint.from && sq === hint.from))) cls += ' hint';
    if (sq === justTo) cls += ' just';
    b.className = cls;
    if (p) {
      const t = p & 15, c = p >> 4;
      b.innerHTML = pieceHTML(t, c, c !== bottom);
      b.setAttribute('aria-label', `${sqName(sq)} ${c === BLACK ? '先手' : '後手'}の${E.PIECE_KANJI[t]}`);
    } else {
      b.innerHTML = '';
      b.setAttribute('aria-label', `${sqName(sq)} 空き`);
    }
  }
  justTo = 0;
  renderStand($('standTop'), bottom ^ 1);
  renderStand($('standBottom'), bottom);
  renderStatus();
  renderHint();
  renderButtons();
  renderEval();
  renderReading();
  renderWhy();
  renderMoves();
  renderResult();
  syncSetup();
}

function renderStand(el, c) {
  const isUser = c === G.userSide;
  const who = isUser ? 'あなた' : '千里眼';
  let html = `<div class="stand-label">${sideMark(c)}${c === BLACK ? '先手' : '後手'}・${who}</div>`;
  let any = false;
  for (const t of HAND_ORDER) {
    const n = dispPos().hand[c * 8 + t];
    if (!n) continue;
    any = true;
    const active = isUser && canAct();
    const selected = sel && sel.type === 'hand' && sel.pt === t && isUser;
    html += `<button type="button" class="hp${selected ? ' sel' : ''}" data-pt="${t}" ${active ? '' : 'disabled'} aria-label="持ち駒の${E.PIECE_KANJI[t]} ${n}枚">${pieceHTML(t, c, false)}${n > 1 ? `<span class="cnt">${n}</span>` : ''}</button>`;
  }
  if (!any) html += '<span class="stand-empty">持ち駒なし</span>';
  el.innerHTML = html;
}

function renderStatus() {
  const mark = $('turnMark'), text = $('statusText'), sub = $('statusSub');
  $('pulse').hidden = !thinking;
  if (!thinking) $('thinkBar').hidden = true;
  $('chipCheck').hidden = !(view === null && !G.result && pos.inCheck());
  $('chipReview').hidden = view === null;
  mark.innerHTML = sideMark(dispPos().stm);
  const n = G.moves.length;
  if (view !== null) {
    text.textContent = view === 0 ? '開始局面' : `${view}手目の局面`;
    sub.textContent = thinking ? '千里眼が考えています（最新の局面）' : G.result ? resultDetail(G.result) : (pos.stm === G.userSide ? 'あなたの番です（最新の局面）' : '');
  } else if (G.result) {
    text.textContent = resultTitle(G.result);
    sub.textContent = resultDetail(G.result);
  } else if (thinking) {
    text.textContent = '千里眼が考えています';
    if (live) sub.textContent = live.mate > 0 ? `${live.mate}手詰めを発見` : `深さ ${live.depth} ・ ${fmtNodes(live.nodes)}局面`;
    else sub.textContent = `${n + 1}手目`;
  } else {
    text.textContent = 'あなたの番です';
    sub.textContent = `${n + 1}手目・${G.userSide === BLACK ? '先手' : '後手'}`;
  }
}

function renderHint() {
  const el = $('hintText');
  if (!hint) { el.textContent = ''; return; }
  if (hint.loading) { el.textContent = '千里眼に聞いています…'; return; }
  if (!hint.to) { el.textContent = hint.text; return; }
  el.innerHTML = '';
  el.append('ヒント：');
  const b = document.createElement('b'); b.textContent = hint.text; el.append(b);
  el.append(`（${hint.ev}）`);
}

function renderButtons() {
  const userMoves = G.moves.filter((_, i) => (i % 2 === 0 ? BLACK : WHITE) === G.userSide).length;
  $('btnUndo').disabled = !(thinking || userMoves > 0 || (G.result && G.result.by === G.userSide));
  $('btnHint').disabled = !canAct() || (hint && hint.loading);
  $('btnResign').disabled = !!G.result;
}

function winRate(b) { return 1 / (1 + Math.exp(-b / 600)); }
function fmtScore(b) {
  if (Math.abs(b) >= MATE_IN_MAX) return b > 0 ? '先手勝ち' : '後手勝ち';
  const r = Math.round(b);
  return (r > 0 ? '+' : r < 0 ? '−' : '±') + Math.abs(r);
}
function verdict(b) {
  const a = Math.abs(b);
  if (a < 300) return '互角';
  const who = b > 0 ? '先手' : '後手';
  if (a >= MATE_IN_MAX) return who + '勝ち';
  if (a < 800) return who + 'やや有利';
  if (a < 1600) return who + '有利';
  if (a < 3000) return who + '優勢';
  return who + '勝勢';
}
function fmtNodes(n) {
  if (n >= 1e8) return (n / 1e8).toFixed(1) + '億';
  if (n >= 1e4) return (n / 1e4).toFixed(n >= 1e6 ? 0 : 1) + '万';
  return String(n);
}

function renderEval() {
  const last = G.evals.length ? G.evals[G.evals.length - 1] : null;
  let b = last ? last.b : 0;
  const wr = last ? (Math.abs(b) >= MATE_IN_MAX ? (b > 0 ? 1 : 0) : winRate(b)) : 0.5;
  const pb = Math.round(wr * 100);
  $('wrB').textContent = pb + '%';
  $('wrW').textContent = (100 - pb) + '%';
  $('wrBarS').style.flexBasis = pb + '%';
  $('wrBarG').style.flexBasis = (100 - pb) + '%';
  $('wrVerdict').textContent = last ? verdict(b) : '互角';
  if (!last) $('evalNum').textContent = '評価値 ±0（対局開始）';
  else if (last.mate) $('evalNum').textContent = `${last.mate > 0 ? '先手' : '後手'}の勝ち筋（${Math.abs(last.mate)}手で詰み）`;
  else $('evalNum').textContent = '評価値 ' + fmtScore(b) + '（先手から見て）';
  drawGraph();
}

const GW = 320, GH = 132, GL = 26, GR = 8, GT = 8, GB = 20;
function graphPoints() {
  const pts = [{ ply: 0, wr: 0.5, b: 0 }];
  for (const e of G.evals) pts.push({ ply: e.ply + 1, wr: Math.abs(e.b) >= MATE_IN_MAX ? (e.b > 0 ? 1 : 0) : winRate(e.b), b: e.b, mate: e.mate });
  return pts;
}
function drawGraph() {
  const svg = $('graph');
  const pts = graphPoints();
  const maxPly = Math.max(40, Math.ceil((G.moves.length + 2) / 20) * 20);
  const X = (p) => GL + (GW - GL - GR) * p / maxPly;
  const Y = (wr) => GT + (GH - GT - GB) * (1 - wr);
  const midY = Y(0.5);
  let grid = '';
  for (const w of [0, 0.25, 0.5, 0.75, 1]) {
    grid += `<line x1="${GL}" x2="${GW - GR}" y1="${Y(w)}" y2="${Y(w)}" stroke="var(--line)" stroke-width="1"/>`;
  }
  const lab = `<text x="${GL - 4}" y="${Y(1) + 3}" text-anchor="end">100</text><text x="${GL - 4}" y="${midY + 3}" text-anchor="end">50</text><text x="${GL - 4}" y="${Y(0) + 3}" text-anchor="end">0</text>`;
  let xt = '';
  const step = maxPly <= 60 ? 20 : maxPly <= 160 ? 40 : 80;
  for (let p = 0; p <= maxPly; p += step) xt += `<text x="${X(p)}" y="${GH - 6}" text-anchor="middle">${p}</text>`;
  let line = '', area = '';
  if (pts.length > 1) {
    line = pts.map((p, i) => (i ? 'L' : 'M') + X(p.ply).toFixed(1) + ' ' + Y(p.wr).toFixed(1)).join(' ');
    area = `M${X(pts[0].ply)} ${midY} ` + pts.map(p => 'L' + X(p.ply).toFixed(1) + ' ' + Y(p.wr).toFixed(1)).join(' ') + ` L${X(pts[pts.length - 1].ply).toFixed(1)} ${midY} Z`;
  }
  const lastP = pts[pts.length - 1];
  svg.innerHTML = `
    <defs>
      <clipPath id="cpTop"><rect x="0" y="0" width="${GW}" height="${midY}"/></clipPath>
      <clipPath id="cpBot"><rect x="0" y="${midY}" width="${GW}" height="${GH - midY}"/></clipPath>
    </defs>
    ${grid}${lab}${xt}
    <text x="${GW - GR}" y="${Y(1) + 10}" text-anchor="end">先手有利</text>
    <text x="${GW - GR}" y="${Y(0) - 4}" text-anchor="end">後手有利</text>
    ${area ? `<path d="${area}" fill="var(--sente)" fill-opacity=".14" clip-path="url(#cpTop)"/><path d="${area}" fill="var(--gote)" fill-opacity=".14" clip-path="url(#cpBot)"/>` : ''}
    <line x1="${GL}" x2="${GW - GR}" y1="${midY}" y2="${midY}" stroke="var(--mid)" stroke-width="1"/>
    ${line ? `<path d="${line}" fill="none" stroke="var(--ink)" stroke-width="2" stroke-linejoin="round" stroke-linecap="round"/>` : ''}
    ${pts.length > 1 ? `<circle cx="${X(lastP.ply)}" cy="${Y(lastP.wr)}" r="4" fill="${lastP.wr >= 0.5 ? 'var(--sente)' : 'var(--gote)'}" stroke="var(--surface)" stroke-width="2"/>` : ''}
    <line id="cross" x1="0" x2="0" y1="${GT}" y2="${GH - GB}" stroke="var(--muted)" stroke-width="1" visibility="hidden"/>
    <rect x="${GL}" y="0" width="${GW - GL - GR}" height="${GH - GB}" fill="transparent" id="hit"/>`;
  const hit = svg.querySelector('#hit'), cross = svg.querySelector('#cross'), tip = $('tip');
  const showAt = (clientX) => {
    if (pts.length < 2) return;
    const r = svg.getBoundingClientRect();
    const x = (clientX - r.left) / r.width * GW;
    let best = pts[0], bd = 1e9;
    for (const p of pts) { const d = Math.abs(X(p.ply) - x); if (d < bd) { bd = d; best = p; } }
    cross.setAttribute('x1', X(best.ply)); cross.setAttribute('x2', X(best.ply)); cross.setAttribute('visibility', 'visible');
    const pct = Math.round(best.wr * 100);
    const mv = best.ply > 0 ? (H.kif[best.ply - 1] || '') : '開始局面';
    tip.innerHTML = '';
    const b1 = document.createElement('b'); b1.textContent = `先手 ${pct}%`;
    tip.append(b1, document.createElement('br'), `${best.ply}手目 ${mv}`, document.createElement('br'), best.mate ? `${Math.abs(best.mate)}手詰め` : '評価値 ' + fmtScore(best.b));
    tip.hidden = false;
    const px = X(best.ply) / GW * r.width;
    const tw = tip.offsetWidth;
    tip.style.left = Math.max(0, Math.min(r.width - tw, px - tw / 2)) + 'px';
    tip.style.top = (-tip.offsetHeight - 6) + 'px';
  };
  hit.addEventListener('pointermove', (e) => showAt(e.clientX));
  hit.addEventListener('pointerdown', (e) => showAt(e.clientX));
  hit.addEventListener('pointerleave', () => { cross.setAttribute('visibility', 'hidden'); tip.hidden = true; });
}

function pvKif(base, lastTo, pvUsi, max) {
  const p = base.clone();
  const out = [];
  let prev = lastTo;
  for (const u of pvUsi.slice(0, max)) {
    const m = p.parseUSI(u);
    if (!m) break;
    out.push(E.moveToKIF(p, m, prev).replace('同　', '同'));
    prev = mTo(m);
    p.doMove(m);
  }
  return out;
}

function renderReading() {
  const src = thinking && live ? { depth: live.depth, nodes: live.nodes, time: live.time, scoreB: scoreForBlack(live.score, pos.stm), mate: live.mate, pv: live.pv, base: pos, lastTo: H.lastTo, side: pos.stm } : reading;
  if (!src) {
    $('stDepth').textContent = '—'; $('stScore').textContent = '—'; $('stNodes').textContent = '—'; $('stTime').textContent = '—';
    $('pv').textContent = thinking ? '読み始めています…' : 'まだ読んでいません。千里眼の手番になると考え始めます。';
    return;
  }
  if (src.book) {
    $('stDepth').textContent = '定跡'; $('stScore').textContent = '—'; $('stNodes').textContent = '—'; $('stTime').textContent = '—';
    $('pv').textContent = '定跡（序盤の決まった指し方）から指しました。';
    return;
  }
  $('stDepth').textContent = src.dfpn ? '詰み探索' : String(src.depth);
  $('stScore').textContent = src.mate ? (src.mate > 0 ? `${src.mate}手詰` : `${-src.mate}手で詰まされる`) : fmtScore(src.scoreB);
  $('stNodes').textContent = fmtNodes(src.nodes || 0);
  $('stTime').textContent = ((src.time || 0) / 1000).toFixed(1) + '秒';
  const ks = pvKif(src.base, src.lastTo, src.pv || [], 12);
  const pvEl = $('pv');
  pvEl.innerHTML = '';
  if (src.mate > 0) { const s = document.createElement('span'); s.className = 'mate'; s.textContent = src.dfpn ? '詰みを読み切りました　' : `${src.mate}手詰めを読み切りました　`; pvEl.append(s); }
  pvEl.append(ks.length ? '読み筋：' + ks.join(' ') : '—');
}

// 千里眼の考え：見ている局面までで最後の千里眼の手について、選んだ理由を出す
function renderWhy() {
  const sec = $('whySec'), box = $('why');
  const shown = view === null ? G.moves.length : view;
  let ply = -1;
  for (let i = shown - 1; i >= 0; i--) if (isAIPly(i)) { ply = i; break; }
  const note = ply >= 0 ? G.notes[ply] : null;
  const waiting = !!(why && why.ply === ply);
  const on = !!(EXP && G.explain && LEVELS[G.level].explainMs);
  sec.hidden = !(on || note || waiting);
  if (sec.hidden) return;
  $('whyPly').textContent = (note || waiting) ? `${ply + 1}手目` : '';
  box.textContent = '';
  if (waiting) {
    const p = document.createElement('p'); p.className = 'why-wait';
    p.append(`${H.kif[ply]}を選んだ理由を、ほかの候補と読み比べながら整理しています…`);
    const bar = document.createElement('div'); bar.className = 'why-bar';
    const fill = document.createElement('span');
    fill.style.animationDuration = why.ms + 'ms';
    fill.style.animationDelay = -(Date.now() - why.started) + 'ms';
    bar.append(fill);
    box.append(p, bar);
    return;
  }
  if (!note) {
    const p = document.createElement('p'); p.className = 'why-wait';
    p.textContent = thinking ? '千里眼が指したら、その手を選んだ理由をここに書きます。' : '千里眼が指すと、その手を選んだ理由と、ほかの候補手との比較をここに書きます。';
    box.append(p);
    return;
  }
  for (const t of note.paras) { const p = document.createElement('p'); p.textContent = t; box.append(p); }
  if (note.rows && note.rows.length) {
    const tb = document.createElement('table'); tb.className = 'cands';
    const cap = document.createElement('caption'); cap.textContent = '読み比べた候補手';
    const head = document.createElement('tr');
    for (const h of ['候補手', '評価値', '読み筋']) { const th = document.createElement('th'); th.scope = 'col'; th.textContent = h; head.append(th); }
    tb.append(cap, head);
    for (const r of note.rows) {
      const tr = document.createElement('tr'); if (r.chosen) tr.className = 'chosen';
      const a = document.createElement('td'); a.className = 'mv'; a.textContent = r.k;
      if (r.chosen) { const b = document.createElement('span'); b.className = 'tag'; b.textContent = '採用'; a.append(b); }
      const ev = document.createElement('td'); ev.className = 'ev'; ev.textContent = r.ev;
      const ln = document.createElement('td'); ln.className = 'line'; ln.textContent = r.line || '—';
      tr.append(a, ev, ln); tb.append(tr);
    }
    box.append(tb);
  }
  if (note.foot) { const f = document.createElement('p'); f.className = 'why-foot'; f.textContent = note.foot; box.append(f); }
}

function renderMoves() {
  const ol = $('moves');
  ol.innerHTML = '';
  if (!H.kif.length) {
    const li = document.createElement('li'); li.className = 'moves-empty'; li.style.gridColumn = '1 / -1'; li.style.border = '0';
    li.textContent = 'まだ指し手はありません。';
    ol.appendChild(li);
    $('navLabel').textContent = '開始局面';
    for (const id of ['navFirst', 'navPrev', 'navNext', 'navLast']) $(id).disabled = true;
    return;
  }
  const evByPly = new Map(G.evals.map(e => [e.ply, e]));
  const shown = view === null ? H.kif.length : view;
  let curEl = null;
  H.kif.forEach((k, i) => {
    const li = document.createElement('li');
    const btn = document.createElement('button');
    btn.type = 'button'; btn.dataset.ply = String(i + 1);
    if (i === shown - 1) { li.className = 'cur'; curEl = li; btn.setAttribute('aria-current', 'true'); }
    if (G.notes[i]) { li.classList.add('noted'); btn.title = '千里眼の考えあり'; }
    const n = document.createElement('span'); n.className = 'n'; n.textContent = String(i + 1);
    const mv = document.createElement('span'); mv.className = 'mv'; mv.textContent = k;
    btn.append(n, mv);
    const e = evByPly.get(i);
    if (e) { const ev = document.createElement('span'); ev.className = 'ev'; ev.textContent = e.mate ? '詰' : fmtScore(e.b); btn.append(ev); }
    li.appendChild(btn);
    ol.appendChild(li);
  });
  if (view === null || !curEl) ol.scrollTop = ol.scrollHeight;
  else { const top = curEl.offsetTop - ol.offsetTop; if (top < ol.scrollTop || top > ol.scrollTop + ol.clientHeight - 30) ol.scrollTop = Math.max(0, top - ol.clientHeight / 2); }
  $('navLabel').textContent = view === null ? '最新の局面' : (view === 0 ? '開始局面' : `${view}手目 / ${H.kif.length}手`);
  $('navFirst').disabled = shown === 0; $('navPrev').disabled = shown === 0;
  $('navNext').disabled = view === null; $('navLast').disabled = view === null;
}

function resultTitle(r) {
  if (r.winner === -1) return '引き分け';
  return r.winner === G.userSide ? 'あなたの勝ち' : '千里眼の勝ち';
}
function resultDetail(r) {
  const n = r.plies != null ? r.plies : G.moves.length;
  if (r.winner === -1) return r.reason === '持将棋' ? `まで${n}手で持将棋` : `まで${n}手で千日手`;
  const w = r.winner === BLACK ? '先手' : '後手';
  let why = r.reason;
  if (r.reason === '投了') why = (r.by === G.userSide ? 'あなた' : '千里眼') + 'が投了';
  return `まで${n}手で${w}の勝ち（${why}）`;
}
function renderResult() {
  const box = $('resultBox');
  if (!G.result || resultHidden || view !== null) { box.hidden = true; return; }
  $('resultTitle').textContent = resultTitle(G.result);
  $('resultSub').textContent = resultDetail(G.result);
  box.hidden = false;
}

function syncSetup() {
  $('optSound').checked = G.sound !== false;
  const lv = document.querySelector(`input[name="level"][value="${G.level}"]`);
  if (lv && !lv.checked) lv.checked = true;
  const L = LEVELS[Number(document.querySelector('input[name="level"]:checked').value)];
  $('levelDesc').textContent = L.desc;
  $('optExplain').checked = !!G.explain;
  $('optExplain').disabled = !L.explainMs;
  $('explainNote').textContent = L.explainMs ? '（最強・長考）' : '（最強・長考で使えます）';
}

// ---------------------------------------------------------------- KIF export
function buildKif() {
  const d = new Date(G.started || Date.now());
  const pad = (x) => String(x).padStart(2, '0');
  const lv = LEVELS[G.level].name;
  const lines = [
    '# KIF形式棋譜ファイル',
    `開始日時：${d.getFullYear()}/${pad(d.getMonth() + 1)}/${pad(d.getDate())} ${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`,
    '手合割：平手',
    `先手：${G.userSide === BLACK ? 'あなた' : '千里眼（' + lv + '）'}`,
    `後手：${G.userSide === WHITE ? 'あなた' : '千里眼（' + lv + '）'}`,
    '手数----指手---------消費時間--',
  ];
  H.kifLines.forEach((k, i) => {
    lines.push(`${String(i + 1).padStart(4)} ${k}   ( 0:00/00:00:00)`);
    const n = G.notes[i];   // 千里眼の考えは KIF のコメント行（*）として残す
    if (n && n.paras) for (const p of n.paras) lines.push('*' + p);
  });
  if (G.result) {
    const n = G.moves.length + 1;
    const r = G.result;
    const word = r.reason === '投了' ? '投了' : r.reason === '詰み' ? '詰み' : r.reason.includes('千日手') ? (r.reason === '千日手' ? '千日手' : '反則負け') : '投了';
    lines.push(`${String(n).padStart(4)} ${word}`);
    lines.push(resultDetail(r).replace(/（.*）/, ''));
  }
  return lines.join('\n') + '\n';
}
async function copyKif() {
  const text = buildKif();
  try {
    await navigator.clipboard.writeText(text);
    toast('棋譜をコピーしました');
  } catch (e) {
    const ta = $('kifText');
    ta.value = text; ta.hidden = false; ta.focus(); ta.select();
    toast('棋譜を選択しました。コピーして使ってください');
  }
}

// ---------------------------------------------------------------- sound & toast
let actx = null;
function clack() {
  if (G.sound === false) return;
  try {
    actx = actx || new (window.AudioContext || window.webkitAudioContext)();
    if (actx.state === 'suspended') actx.resume();
    const t = actx.currentTime + 0.005;
    const len = Math.floor(actx.sampleRate * 0.07);
    const buf = actx.createBuffer(1, len, actx.sampleRate);
    const dt = buf.getChannelData(0);
    for (let i = 0; i < len; i++) dt[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / len, 7);
    const src = actx.createBufferSource(); src.buffer = buf;
    const bp = actx.createBiquadFilter(); bp.type = 'bandpass'; bp.frequency.value = 2100; bp.Q.value = 1.3;
    const g = actx.createGain(); g.gain.setValueAtTime(0.85, t); g.gain.exponentialRampToValueAtTime(0.001, t + 0.09);
    src.connect(bp); bp.connect(g); g.connect(actx.destination);
    const o = actx.createOscillator(); o.type = 'sine';
    o.frequency.setValueAtTime(240, t); o.frequency.exponentialRampToValueAtTime(95, t + 0.07);
    const g2 = actx.createGain(); g2.gain.setValueAtTime(0.3, t); g2.gain.exponentialRampToValueAtTime(0.001, t + 0.1);
    o.connect(g2); g2.connect(actx.destination);
    src.start(t); o.start(t); o.stop(t + 0.12);
  } catch (e) { /* audio unavailable */ }
}
let toastTimer = 0;
function toast(msg) {
  const el = $('toast');
  el.textContent = msg; el.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => { el.hidden = true; }, 2600);
}

// ---------------------------------------------------------------- wiring
function buildLevelSeg() {
  const seg = $('levelSeg');
  LEVELS.forEach((L, i) => {
    const lab = document.createElement('label');
    lab.innerHTML = `<input type="radio" name="level" id="level${i}" value="${i}"><span>${L.name}</span>`;
    seg.appendChild(lab);
  });
  seg.addEventListener('change', (e) => {
    const v = Number(e.target.value);
    $('levelDesc').textContent = LEVELS[v].desc;
    if (G && !G.result) { G.level = v; save(); toast(`次の手から「${LEVELS[v].name}」で指します`); }
    if (G) { syncSetup(); renderWhy(); }
  });
}
function sizeVars() {
  const w = boardEl.clientWidth;
  if (w > 0) document.documentElement.style.setProperty('--sq', (w / 9).toFixed(2) + 'px');
}

function boot(data) {
  buildLevelSeg();
  const restored = data && data.G && data.G.v === 1 ? data.G : load();
  G = restored || newGame(BLACK, 4);
  if (typeof G.level !== 'number' || !LEVELS[G.level]) G.level = 4;
  if (!G.notes || typeof G.notes !== 'object') G.notes = {};
  if (!EXP) $('explainToggle').hidden = true;
  document.querySelector(`input[name="side"][value="${G.userSide === WHITE ? '1' : '0'}"]`).checked = true;
  document.querySelector(`input[name="level"][value="${G.level}"]`).checked = true;
  buildBoard();
  rebuild();
  startWorker();
  sizeVars();
  if (window.ResizeObserver) new ResizeObserver(sizeVars).observe(boardEl);
  else window.addEventListener('resize', sizeVars);

  document.querySelector('.table').addEventListener('click', (e) => {
    const hp = e.target.closest('.hp');
    if (hp && !hp.disabled) onHand(Number(hp.dataset.pt));
  });
  $('promoYes').addEventListener('click', () => { const m = promoPending && promoPending.yes; closePromo(); if (m) userMove(m); });
  $('promoNo').addEventListener('click', () => { const m = promoPending && promoPending.no; closePromo(); if (m) userMove(m); });
  document.addEventListener('keydown', (e) => { if (e.key === 'Escape' && promoPending) { closePromo(); sel = null; render(); } });
  $('btnUndo').addEventListener('click', undo);
  $('btnHint').addEventListener('click', askHint);
  $('btnFlip').addEventListener('click', () => { G.flipped = !G.flipped; save(); render(); });
  $('btnResign').addEventListener('click', resign);
  $('btnNew').addEventListener('click', startNew);
  $('btnAgain').addEventListener('click', startNew);
  $('btnCloseResult').addEventListener('click', () => { resultHidden = true; renderResult(); });
  $('btnCopy').addEventListener('click', copyKif);
  $('btnCopy2').addEventListener('click', copyKif);
  $('optSound').addEventListener('change', (e) => { G.sound = e.target.checked; save(); });
  $('optExplain').addEventListener('change', (e) => {
    G.explain = e.target.checked;
    if (!G.explain) cancelWhy();
    save(); render();
    if (G.explain && LEVELS[G.level].explainMs) toast(thinking ? '次に千里眼が指す手から、理由を表示します' : '千里眼が指すと、その手を選んだ理由を表示します');
  });
  $('moves').addEventListener('click', (e) => { const b = e.target.closest('button[data-ply]'); if (b) setView(Number(b.dataset.ply)); });
  $('navFirst').addEventListener('click', () => setView(0));
  $('navPrev').addEventListener('click', () => setView((view === null ? G.moves.length : view) - 1));
  $('navNext').addEventListener('click', () => { if (view !== null) setView(view + 1); });
  $('navLast').addEventListener('click', () => setView(null));

  render();
  if (!G.result && pos.stm !== G.userSide) requestAI();
}

boot({});
})();
