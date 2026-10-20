/* 千里眼将棋 — 指し手の理由を言葉にする
   千里眼が指したあとに engine.js が行う「解説用の読み」（有力な候補手を同じ深さで読み比べた評価と
   読み筋、相手の狙い、この手の狙い）と、局面そのものの観察（駒の当たり・両取り・囲い・読み筋での
   駒の損得・評価の内訳）から、その局面だけの文章を組み立てる。
   同じ種類の事実にも言い回しを何通りも用意し、最近使ったものを避けて選ぶ。「迷った」「途中で
   考えを変えた」といった話題も、一つの解説で繰り返さず、続けて使いすぎないようにしている。 */
(function (root) {
'use strict';
const E = root.ShogiEngine || (typeof require === 'function' ? require('./engine.js') : null);
if (!E) return;
const { BLACK, FU, KY, KE, GI, KA, HI, KI, OU, TO, NY, NK, NG, UM, RY, FILE, RANK, OWNER, DEMOTE, SQ81, HV, EXV,
        mFrom, mTo, mPiece, mCap, mIsPromo, MATE_IN_MAX } = E;

const NAME = ['', '歩', '香車', '桂馬', '銀', '角', '飛車', '金', '玉', 'と金', '成香', '成桂', '成銀', '馬', '龍'];
const SHORT = ['', '歩', '香', '桂', '銀', '角', '飛車', '金', '玉', 'と', '成香', '成桂', '成銀', '馬', '龍'];
const KAN = ['', '一', '二', '三', '四', '五', '六', '七', '八', '九'];
const ZEN = E.ZEN_NUM;
const sqName = (s) => ZEN[FILE[s]] + KAN[RANK[s]];
const kifOf = (pos, m, prevTo) => E.moveToKIF(pos, m, prevTo).replace('同　', '同');
const cheb = (a, b) => Math.max(Math.abs(FILE[a] - FILE[b]), Math.abs(RANK[a] - RANK[b]));
const ahead = (c, from, to) => (c === BLACK ? RANK[from] - RANK[to] : RANK[to] - RANK[from]);
const isMate = (v) => v != null && Math.abs(v) >= MATE_IN_MAX;
const matOf = (p, c) => (c === BLACK ? p.material : -p.material);
const SLIDER = new Set([KY, KA, HI, UM, RY]);
const GOLDISH = new Set([KI, GI, TO, NY, NK, NG]);

// ---------------------------------------------------------------- 言い回しの記憶
// 同じ種類の文では、最近使った言い回しを外して（直近の半分は候補にしない）残りから選ぶ。
// 話題（「迷った」「方針を変えた」など）は、何回前の解説で使ったかも覚えておく。
class Memo {
  constructor() { this.n = 0; this.last = new Map(); this.builds = 0; this.topics = new Map(); }
  pick(key, list, rnd) {
    const ok = [];
    for (let i = 0; i < list.length; i++) if (list[i] != null && list[i] !== false && list[i] !== '') ok.push(i);
    if (!ok.length) return '';
    ok.sort((a, b) => (this.last.get(key + '#' + a) || 0) - (this.last.get(key + '#' + b) || 0));
    const fresh = ok.slice(0, Math.max(1, Math.ceil(ok.length / 2)));
    const i = fresh[Math.floor(rnd() * fresh.length)];
    this.last.set(key + '#' + i, ++this.n);
    const v = list[i];
    return typeof v === 'function' ? v() : v;
  }
  ago(topic) { const b = this.topics.get(topic); return b == null ? Infinity : this.builds - b; }
  mark(topic) { this.topics.set(topic, this.builds); }
}
function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = Math.imul(a ^ (a >>> 15), a | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// ---------------------------------------------------------------- 局面の観察
const BUF = new Int32Array(1024);
// victim 側の駒のうち、相手が取りにいけば得をするもの：マス → 得になる量（SEE）
function enPrise(pos, victim) {
  const flip = pos.stm === victim;
  if (flip) pos.doNull();
  const n = pos.gen(BUF, 0, 9), out = new Map();
  for (let i = 0; i < n; i++) {
    const m = BUF[i], c = mCap(m) & 15;
    if (!c || c === OU || !pos.isLegalPseudo(m)) continue;
    const g = E.seeMove(pos, m), to = mTo(m);
    if (g > (out.get(to) || 0)) out.set(to, g);
  }
  if (flip) pos.undoNull();
  return out;
}

// 囲い（先手の配置で書き、後手は盤を180度回して当てはめる）
const CASTLES = [
  ['穴熊', 99, [[KY, 98]]], ['穴熊', 19, [[KY, 18]]],
  ['銀冠', 28, [[GI, 27], [KI, 38]]],
  ['高美濃囲い', 28, [[GI, 38], [KI, 49], [KI, 47]]],
  ['美濃囲い', 28, [[GI, 38], [KI, 49]]],
  ['矢倉囲い', 88, [[GI, 77], [KI, 78], [KI, 67]]],
  ['舟囲い', 78, [[KI, 69], [KI, 58]]],
];
function castleOf(pos, c) {
  const at = (fr) => { const f = (fr / 10) | 0, r = fr % 10; return c === BLACK ? E.sqOf(f, r) : E.sqOf(10 - f, 10 - r); };
  for (const [name, k, need] of CASTLES) {
    if (pos.kingSq[c] !== at(k)) continue;
    if (need.every(([t, s]) => pos.board[at(s)] === (t | (c << 4)))) return name;
  }
  return '';
}
// 香・角・飛車（成り駒も）の利きの数。歩を突いて角道が通った／止まった、などを見つける
function reach(pos, c) {
  const out = new Map();
  for (const s of SQ81) {
    const p = pos.board[s];
    if (p && (p >> 4) === c && SLIDER.has(p & 15)) out.set(s, E.attacksFrom(pos, s).length);
  }
  return out;
}
function defenders(pos, c) {   // 玉のすぐそばにいる金銀の数
  const k = pos.kingSq[c];
  let n = 0;
  for (const s of SQ81) { const p = pos.board[s]; if (p && (p >> 4) === c && GOLDISH.has(p & 15) && cheb(s, k) <= 1) n++; }
  return n;
}

// ---------------------------------------------------------------- 手数（手得・手損）
// 駒ごとに「初めの位置から今の位置まで、最少で何手かかるか」を足したものを、その側の役に立った手数とみる。
// 実際に指した手数と比べて二人の差を見れば、どちらが手得・手損かがわかる（序盤だけで使う）
const ORIGIN = [0, 1].map(c => {
  const at = (f, r) => (c === BLACK ? E.sqOf(f, r) : E.sqOf(10 - f, 10 - r));
  return { [FU]: [1, 2, 3, 4, 5, 6, 7, 8, 9].map(f => at(f, 7)), [KY]: [at(1, 9), at(9, 9)], [KE]: [at(2, 9), at(8, 9)],
    [GI]: [at(3, 9), at(7, 9)], [KI]: [at(4, 9), at(6, 9)], [OU]: [at(5, 9)], [KA]: [at(8, 8)], [HI]: [at(2, 8)] };
});
// 駒の動き（先手から見た [筋, 段] の向き。後手は段を逆に）。slide は何マスでも進める向き
const GOLD = [[0, -1], [-1, -1], [1, -1], [-1, 0], [1, 0], [0, 1]], KING8 = [[0, -1], [-1, -1], [1, -1], [-1, 0], [1, 0], [0, 1], [-1, 1], [1, 1]];
const DIAG = [[-1, -1], [1, -1], [-1, 1], [1, 1]], ORTHO = [[0, -1], [-1, 0], [1, 0], [0, 1]];
const MOVES = { [FU]: { step: [[0, -1]] }, [KY]: { slide: [[0, -1]] }, [KE]: { step: [[-1, -2], [1, -2]] },
  [GI]: { step: [[0, -1], [-1, -1], [1, -1], [-1, 1], [1, 1]] }, [KI]: { step: GOLD }, [OU]: { step: KING8 },
  [KA]: { slide: DIAG }, [HI]: { slide: ORTHO }, [UM]: { slide: DIAG, step: ORTHO }, [RY]: { slide: ORTHO, step: DIAG } };
for (const t of [TO, NY, NK, NG]) MOVES[t] = MOVES[KI];
const DIST = new Map();
function distFrom(t, c, o) {   // 何もない盤で、c 側の t の駒が o から各マスへ行く最少手数（行けないマスは 99）
  const key = (t * 2 + c) * 256 + o;
  if (DIST.has(key)) return DIST.get(key);
  const d = new Int8Array(FILE.length).fill(99), mv = MOVES[t], q = [o], sg = c === BLACK ? 1 : -1;
  const to = (s, df, dr) => E.sqOf(FILE[s] + df, RANK[s] + dr * sg);
  const ok = (f, r) => f >= 1 && f <= 9 && r >= 1 && r <= 9;
  d[o] = 0;
  for (let i = 0; i < q.length; i++) {
    const s = q[i], n = d[s] + 1, go = (x) => { if (d[x] > n) { d[x] = n; q.push(x); } };
    for (const [df, dr] of mv.step || []) if (ok(FILE[s] + df, RANK[s] + dr * sg)) go(to(s, df, dr));
    for (const [df, dr] of mv.slide || []) for (let k = 1; ok(FILE[s] + df * k, RANK[s] + dr * k * sg); k++) go(to(s, df * k, dr * k));
  }
  DIST.set(key, d);
  return d;
}
function devMoves(p, c) {
  const by = new Map();
  for (const s of SQ81) { const x = p.board[s]; if (x && (x >> 4) === c) { const b = DEMOTE[x & 15]; if (!by.has(b)) by.set(b, []); by.get(b).push({ s, t: x & 15 }); } }
  let sum = 0;
  for (const [b, list] of by) {
    const os = ORIGIN[c][b] || [], cost = (x, o) => { const v = distFrom(x.t > OU ? x.t : b, c, o)[x.s]; return v >= 99 ? 1 : v; };
    if (b === FU) { for (const x of list) { const o = os.find(q => FILE[q] === FILE[x.s]); sum += o ? cost(x, o) : 1; } continue; }
    // 同じ種類の駒どうしは、合計がいちばん少なくなる組み合わせで初めの位置に対応させる（持ち駒から打った駒は 1 手）
    let best = Infinity;
    const rec = (i, used, acc) => {
      if (acc >= best) return;
      if (i === list.length) { best = acc; return; }
      rec(i + 1, used, acc + 1);
      os.forEach((o, j) => { if (!(used & (1 << j))) rec(i + 1, used | (1 << j), acc + cost(list[i], o)); });
    };
    rec(0, 0, 0);
    sum += best;
  }
  return sum;
}
// moves を指したあと、us 側がどれだけ手得したか（負なら手損）
function tempoGain(P, moves, us) {
  const p = P.clone(), e0 = devMoves(p, us) - devMoves(p, us ^ 1);
  let n = 0;
  for (const m of moves) { n += p.stm === us ? 1 : -1; p.doMove(m); }
  return devMoves(p, us) - devMoves(p, us ^ 1) - e0 - n;
}
// 手得・手損を言うのは、駒組みの段階（成り駒がなく、持ち駒も角交換くらいまで）。
// skip のマスの成り駒（いま取り合っている角成など）は数えない
function isOpening(P, ply, skip) {
  if (ply > 40) return false;
  let big = 0, pawns = 0;
  for (let c = 0; c < 2; c++) { for (let t = KY; t <= KI; t++) big += P.hand[c * 8 + t]; pawns += P.hand[c * 8 + FU]; }
  for (const s of SQ81) if (P.board[s] && (P.board[s] & 15) > OU && !(skip && skip.includes(s))) return false;
  return big <= 2 && pawns <= 4;
}
const tempoWord = (n, gain) => (n === 1 ? '一手' : n === 2 ? '二手' : '') + (gain ? '得' : '損');
// 読み筋の中で、自分の同じ駒を二度動かして手数を無駄にする手（取る手は除く）
function wasted(P, L, lim) {
  const p = P.clone(), us = p.stm, at = new Map();   // 動かした駒の今のマス → { start, n, t, first }
  for (let i = 0; i < Math.min(L.moves.length, lim + 1); i++) {
    const m = L.moves[i], fr = mFrom(m), to = mTo(m);
    if (p.stm === us && fr && !mCap(m)) {
      const r = at.get(fr) || { start: fr, n: 0, t: mPiece(m) & 15, first: i };
      at.delete(fr);
      if (++r.n >= 2 && distFrom(r.t, us, r.start)[to] < r.n) return { ply: i, back: to === r.start, t: r.t, first: r.first };
      at.set(to, r);
    } else { at.delete(to); if (fr) at.delete(fr); }
    p.doMove(m);
  }
  return null;
}
// 読み筋がないとき：取った駒は、いちばん安い駒で取り返されるとみる
function cheapRecapture(P, M) {
  const p = after(P, [M], 1), to = mTo(M);
  let best = 0;
  for (const m of p.legalMoves()) if (mTo(m) === to && mCap(m) && (!best || E.PV[mPiece(m) & 15] < E.PV[mPiece(best) & 15])) best = m;
  return best;
}
// この手についての手得・手損：自分から始める交換、相手が始めた交換の取り返し、当てた駒を引かせる手
function tempoNote(X, hist) {
  if (!X.opening) return null;
  const P = X.P, M = X.M, I = X.Mi, side = X.side, pvR = X.L && X.L.moves.length >= 2 ? X.L.moves[1] : 0;
  if (I.cap && !I.recapture) {
    const R = pvR || cheapRecapture(P, M);
    if (R && mTo(R) === I.to && mCap(R) && DEMOTE[mCap(R) & 15] === DEMOTE[I.cap]) {
      const g = tempoGain(P, [M, R], side);
      if (g <= -1) return { kind: 'give', n: -g, t: DEMOTE[I.cap] };
    }
  }
  if (I.recapture && hist && hist.length && X.prev && (X.prev.chain || [X.prev.cap]).length === 1) {
    const p0 = new E.Position(), key = (q) => q.toSFEN().split(' ').slice(0, 3).join(' ');
    p0.setSFEN(E.START_SFEN);
    for (let i = 0; i < hist.length - 1; i++) { const m = p0.parseUSI(hist[i]); if (!m) return null; p0.doMove(m); }
    const pm = p0.parseUSI(hist[hist.length - 1]);
    if (pm && mCap(pm) && DEMOTE[mCap(pm) & 15] === DEMOTE[I.cap] && key(after(p0, [pm], 1)) === key(P)) {
      const g = tempoGain(p0, [pm, M], side ^ 1);
      if (g <= -1) return { kind: 'get', n: -g, t: DEMOTE[I.cap] };
    }
  }
  const R = X.R;
  if (R && !R.cap && !R.drop && ahead(side ^ 1, R.from, R.to) < 0 && (I.hits.some(h => h.s === R.from) || I.threats.some(th => th.s === R.from))
    && tempoGain(P, [M, pvR], side) >= 1) return { kind: 'chase', R };
  return null;
}

// 指し手そのものの観察（pos はその手を指す前の局面）。light なら駒の当たりなどは調べない。
// prevCap は直前の手が駒を取ったか（取られた駒を取り返す手と、ぶつけられた歩を取る手を区別する）
function moveInfo(pos, m, prevTo, light, prevCap) {
  const us = pos.stm, them = us ^ 1, from = mFrom(m), to = mTo(m), t = mPiece(m) & 15, cap = mCap(m) & 15;
  const I = { m, us, from, to, t, nt: mIsPromo(m) ? t + 8 : t, cap, promo: mIsPromo(m), drop: from === 0,
    check: pos.givesCheck(m), see: E.seeMove(pos, m), onPrev: cap !== 0 && to === prevTo, recapture: cap !== 0 && to === prevTo && !!prevCap, k: kifOf(pos, m, prevTo),
    threats: [], saved: [], exposed: [], fled: 0, hits: [], opened: [], closed: [], blocks: [], castle: '',
    ownK: cheb(to, pos.kingSq[us]), enemyK: cheb(to, pos.kingSq[them]), defB: 0, defA: 0 };
  if (light) return I;
  const ownB = enPrise(pos, us), oppB = enPrise(pos, them), reachB = reach(pos, us), castleB = castleOf(pos, us);
  const eReachB = reach(pos, them);
  I.defB = defenders(pos, us);
  pos.doMove(m);
  const ownA = enPrise(pos, us), oppA = enPrise(pos, them), reachA = reach(pos, us);
  for (const [s, n] of reach(pos, them)) if (eReachB.has(s) && n <= eReachB.get(s) - 2) I.blocks.push({ s, t: pos.board[s] & 15 });
  I.defA = defenders(pos, us);
  for (const [s, g] of oppA) if (g >= 150 && (oppB.get(s) || 0) < g - 60) I.threats.push({ s, t: pos.board[s] & 15, g });
  I.threats.sort((a, b) => b.g - a.g);
  for (const [s, g] of ownB) if (g >= 150 && s !== from && (ownA.get(s) || 0) < 150 && OWNER[pos.board[s]] === us) I.saved.push({ s, t: pos.board[s] & 15, g });
  for (const [s, g] of ownA) {
    const before = s === to ? (from ? ownB.get(from) || 0 : 0) : ownB.get(s) || 0;
    if (g >= 150 && before < g - 60) I.exposed.push({ s, t: pos.board[s] & 15, g });
  }
  if (!I.drop && (ownB.get(from) || 0) >= 150 && (ownA.get(to) || 0) < 150) I.fled = ownB.get(from);
  I.hits = E.attacksFrom(pos, to).filter(s => OWNER[pos.board[s]] === them).map(s => ({ s, t: pos.board[s] & 15 }));
  for (const [s, n] of reachA) {
    if (s === to) continue;
    const b = reachB.has(s) ? reachB.get(s) : n;
    if (n >= b + 2) I.opened.push({ s, t: pos.board[s] & 15 });
    else if (n <= b - 2) I.closed.push({ s, t: pos.board[s] & 15 });
  }
  const c = castleOf(pos, us);
  if (c && c !== castleB) I.castle = c;
  pos.undoMove(m);
  return I;
}

// 評価の内訳を千里眼側から見た値に
function partsOf(p, side) {
  const r = E.evalParts(p), s = side === BLACK ? 1 : -1;
  return { mat: s * r.mat, act: s * (r.place + r.mob), threat: s * r.threat, nn: s * r.nn,
    myKing: side === BLACK ? r.kingB : -r.kingW, theirKing: side === BLACK ? r.kingW : -r.kingB };
}
// b − a を「駒の損得・自玉・攻め・駒の働き・駒の当たり」に（玉まわりの補正ネットは差の大きい側の玉へ）
function aspectDiff(a, b) {
  const d = { mat: b.mat - a.mat, myKing: b.myKing - a.myKing, theirKing: b.theirKing - a.theirKing, act: b.act - a.act, threat: b.threat - a.threat };
  if (Math.abs(d.myKing) >= Math.abs(d.theirKing)) d.myKing += b.nn - a.nn; else d.theirKing += b.nn - a.nn;
  return d;
}

// 読み筋をたどる：駒の取り合い（side から見た得失）、成り、王手、詰み
function walk(P, usis, side, prevTo) {
  const p = P.clone(), mat0 = matOf(p, side);
  // kabs は「同」を使わない書き方（手順を「…」で略したあとに置く手のため）
  const L = { moves: [], kifs: [], kabs: [], got: [], lost: [], promos: [], checks: [], mated: -1, build: 0 };
  let prev = prevTo;
  for (const u of usis) {
    const m = p.parseUSI(u);
    if (!m) break;
    const mover = p.stm, c = mCap(m) & 15, ply = L.moves.length, t = mPiece(m) & 15;
    L.kifs.push(kifOf(p, m, prev));
    L.kabs.push(kifOf(p, m, 0));
    if (c) (mover === side ? L.got : L.lost).push({ t: DEMOTE[c], board: c, ply, s: mTo(m) });
    if (mIsPromo(m)) L.promos.push({ mine: mover === side, t: t + 8, s: mTo(m), ply });
    if (p.givesCheck(m)) L.checks.push({ mine: mover === side, ply });
    if (ply < 6 && !c && (t === OU || (GOLDISH.has(t) && cheb(mTo(m), p.kingSq[mover]) <= 2))) L.build++;
    L.moves.push(m); prev = mTo(m);
    p.doMove(m);
  }
  if (p.inCheck() && p.legalMoves().length === 0) L.mated = p.stm;
  L.end = p; L.mat = matOf(p, side) - mat0; L.parts = partsOf(p, side);
  L.fight = L.got.concat(L.lost).filter(x => x.ply <= 5).length;
  // 成った駒がすぐ取られたものは「作れた」と言わない
  for (const pr of L.promos) pr.kept = !(pr.ply + 1 < L.moves.length && mTo(L.moves[pr.ply + 1]) === pr.s && mCap(L.moves[pr.ply + 1]));
  // 駒の損得は先の長い読みまでは数えない（取り合いの途中では切らない）
  let h = Math.min(L.moves.length - 1, 7);
  while (h + 1 < L.moves.length && h < 11 && mCap(L.moves[h + 1])) h++;
  L.horizon = h;
  // 読み筋の一文で見せる範囲（5手まで。ただし駒の取り合いの途中では切らない）
  let e = Math.min(L.moves.length - 1, 5);
  while (e < 8 && e + 1 < L.moves.length && mCap(L.moves[e]) && mCap(L.moves[e + 1]) && mTo(L.moves[e + 1]) === mTo(L.moves[e])) e++;
  L.shown = e;
  return L;
}

// 対局開始からの駒の損得（成り駒は元の駒として、盤上と持ち駒を合わせて数える。歩一枚の得が 100）
function balance(p, side) {
  let v = 0;
  for (const s of SQ81) { const x = p.board[s]; if (x && (x & 15) !== OU) v += ((x >> 4) === side ? 1 : -1) * HV[DEMOTE[x & 15]]; }
  for (let t = FU; t <= KI; t++) v += (p.hand[side * 8 + t] - p.hand[(side ^ 1) * 8 + t]) * HV[t];
  return v / 2;
}
// 駒の得失：同じ種類どうしは交換として相殺し、残りを得た駒・渡した駒に
function matWords(L, upto, from) {
  const lim = upto == null ? L.horizon : upto, lo = from == null ? -99 : from;
  const g = L.got.filter(x => x.ply <= lim && x.ply >= lo).map(x => x.t), l = L.lost.filter(x => x.ply <= lim && x.ply >= lo).map(x => x.t), traded = [];
  for (let i = g.length - 1; i >= 0; i--) { const j = l.indexOf(g[i]); if (j >= 0) { traded.push(g[i]); g.splice(i, 1); l.splice(j, 1); } }
  const vg = g.reduce((a, t) => a + HV[t], 0), vl = l.reduce((a, t) => a + HV[t], 0);
  return { g, l, traded, net: vg - vl };
}
// 取られた駒のうち、同じ種類の駒を取り返して交換になっていないもの（いちばん近い手どうしを組にする）
function unpairedLost(L, t, lim) {
  const left = L.lost.filter(x => x.t === t && x.ply <= lim);
  for (const g of L.got) {
    if (g.t !== t || g.ply > lim) continue;
    let bi = -1, bd = Infinity;
    left.forEach((x, i) => { const d = Math.abs(x.ply - g.ply); if (d < bd) { bd = d; bi = i; } });
    if (bi >= 0) left.splice(bi, 1);
  }
  return left;
}
function pieceList(ts) {
  const cnt = new Map();
  for (const t of ts) cnt.set(t, (cnt.get(t) || 0) + 1);
  const out = [];
  for (const t of [HI, KA, KI, GI, KE, KY, FU]) {
    if (!cnt.has(t)) continue;
    if (t === KI && cnt.get(KI) === 1 && cnt.get(GI) === 1) { out.push('金銀'); cnt.delete(GI); continue; }
    const n = cnt.get(t);
    out.push(SHORT[t] + (n > 1 ? KAN[n] + '枚' : ''));
  }
  return out.join('と');
}
// 「銀得」「二歩得」「角と金銀の交換で駒得」など
function gainNoun(w) {
  if (!w.l.length && w.g.length) {
    if (w.g.every(t => t === FU)) return `${KAN[Math.min(9, w.g.length)]}歩得`;
    return w.g.length === 1 ? `${SHORT[w.g[0]]}得` : w.g.length <= 3 ? `${pieceList(w.g)}の駒得` : '大きな駒得';
  }
  if (!w.g.length && w.l.length) {
    if (w.l.every(t => t === FU)) return `${KAN[Math.min(9, w.l.length)]}歩損`;
    return w.l.length === 1 ? `${SHORT[w.l[0]]}損` : w.l.length <= 3 ? `${pieceList(w.l)}の駒損` : '大きな駒損';
  }
  if (w.g.length && w.l.length) {
    if (w.g.length + w.l.length > 3) return w.net > 0 ? '駒得' : '駒損';
    const grp = (ts) => pieceList(ts).replace(/と/g, '・');
    return `${grp(w.l)}と${grp(w.g)}の交換で${w.net > 0 ? '駒得' : '駒損'}`;
  }
  return '';
}
const TRADE = ['', '歩交換', '香の交換', '桂の交換', '銀交換', '角交換', '飛車交換', '金の交換'];

// 相手（または自分）の「パスしたら指される手」：狙いの中身（moves はルートからの手順）
function threatInfo(P, moves, t, by) {
  const p = P.clone();
  for (const m of moves) p.doMove(m);
  p.doNull();
  const T = p.parseUSI(t.pv[0]);
  if (!T) return null;
  const L = walk(p, t.pv, by, 0), I = moveInfo(p, T, 0);
  const early = L.got.filter(x => x.ply <= Math.min(L.horizon, 4));
  const cap = early.filter(x => x.t !== FU).sort((a, b) => HV[b.t] - HV[a.t])[0] || early[0] || null;
  const w = matWords(L, Math.min(L.horizon, 4));
  const real = t.mate > 0 || (t.v - t.st >= 250 && (w.net >= 300 || (cap && cap.t !== FU && w.net >= 150) || L.promos.some(x => x.mine && x.kept && x.ply <= 2) || I.threats.filter(x => x.g >= 300).length >= 2));
  return { T, k: kifOf(p, T, 0), L, I, gain: t.v - t.st, mate: t.mate, cap, real };
}

// ---------------------------------------------------------------- 動詞
// [言い切り, て形, 相手にされたときのて形]
const V = {
  tsuku: ['突く', '突いて', '突かれて'], utsu: ['打つ', '打って', '打たれて'], toru: ['取る', '取って', '取られて'],
  kaesu: ['取り返す', '取り返して', '取り返されて'], naru: ['成る', '成って', '成られて'], komu: ['成り込む', '成り込んで', '成り込まれて'],
  haneru: ['跳ねる', '跳ねて', '跳ねられて'], deru: ['出る', '出て', '出られて'], agaru: ['上がる', '上がって', '上がられて'],
  hiku: ['引く', '引いて', '引かれて'], yoru: ['寄る', '寄って', '寄られて'], mawaru: ['回る', '回って', '回られて'],
};
function verbOf(I) {
  if (I.drop) return V.utsu;
  if (I.cap) return I.recapture ? V.kaesu : V.toru;
  if (I.promo) return I.t === HI || I.t === KA ? V.komu : V.naru;
  if (I.t === FU) return V.tsuku;
  if (I.t === KE) return V.haneru;
  const f = ahead(I.us, I.from, I.to), far = cheb(I.from, I.to) >= 2 && SLIDER.has(I.t);
  if (f > 0) return far ? V.deru : V.agaru;
  if (f < 0) return V.hiku;
  return far && (I.t === HI || I.t === RY) ? V.mawaru : V.yoru;
}

// 静かな手の性格。np は「〜手です」の前に、goal は「〜と突いて、」の後に置く形。
// asp はその手が主に効く評価の項目（評価の内訳に触れるときに食い違わないように）
function natureOf(P, I, imm, say) {
  const side = I.us, t = I.t, f = FILE[I.to], ownK = P.kingSq[side], enK = P.kingSq[side ^ 1];
  const near = (k) => (f <= 3 && FILE[k] <= 4) || (f >= 7 && FILE[k] >= 6);
  // 言い方が複数あるものは、指した手なら記憶を使って選ぶ（候補手の説明では最初の言い方）
  const N = (np, goal, asp, key) => (Array.isArray(np) ? (say ? say('nat.' + key, np.map((x, i) => () => ({ np: x, goal: goal[i], asp: asp || '' }))) : { np: np[0], goal: goal[0], asp: asp || '' }) : { np, goal, asp: asp || '' });
  // 決まった言い方がない手は、指した直後に評価のどこが良くなったかで言い分ける
  // 歩は玉のそばでなければ「守り」とは言わない
  const top = imm ? ['myKing', 'theirKing', 'act'].filter(k => k !== 'myKing' || t !== FU || cheb(I.to, ownK) <= 3).sort((a, b) => imm[b] - imm[a])[0] : '';
  const by = (n) => {
    if (!imm || imm[top] < 50) return n;
    if (t === FU) return top === 'myKing' ? N('歩を突いて玉のまわりの形を整える', '玉のまわりの形を整えます。', top)
      : top === 'theirKing' ? N('歩を伸ばして攻めの形を一歩進める', '攻めの形を一歩進めます。', top) : N('歩を突いて駒の通り道を作る', '駒の通り道を作ります。', top);
    if (top === 'myKing') return t === OU ? N(['玉を安全な位置に移す', '玉を戦いの起きにくい所へ移す'], ['玉を安全な位置に移します。', '玉を戦いの起きにくい所へ移します。'], top, 'kSafe')
      : N([`${NAME[t]}で守りを固める`, `${NAME[t]}を使って玉のまわりを厚くする`, `${NAME[t]}を守りの位置に据える`], ['守りを固めます。', '玉のまわりを厚くします。', '守りの形を整えます。'], top, 'gSafe');
    if (top === 'theirKing') return !I.drop && ahead(side, I.from, I.to) > 0
      ? N(['攻めの形を一歩進める', '攻めの準備を整える', '攻めに使う駒を前に出す'], ['攻めの形を一歩進めます。', '攻めの準備を整えます。', '攻めの態勢を整えます。'], top, 'atk')
      : N(['攻めの準備を整える', '攻めに備えて駒の配置を変える'], ['攻めの準備を整えます。', '攻めに備えて配置を変えます。'], top, 'atk2');
    return N([`${NAME[t]}の働きを良くする`, `${NAME[t]}を働きやすい場所へ移す`], [`${NAME[t]}の働きを良くします。`, `${NAME[t]}を働きやすい場所へ移します。`], top, 'act');
  };
  const ownHalf = side === BLACK ? RANK[I.to] >= 6 : RANK[I.to] <= 4;
  const blk = I.blocks.find(b => b.t !== KY) || I.blocks[0];
  if (blk && ownHalf) return N(`${NAME[t]}で${NAME[blk.t]}の利きを止める`, `${NAME[blk.t]}の利きを止めます。`, 'myKing');
  if (I.drop) {
    if (t === FU) {
      const safe = !after(P, [I.m], 1).attacked(I.to, side ^ 1), hit = I.hits.filter(h => h.t !== OU).sort((a, b) => E.PV[b.t] - E.PV[a.t])[0];
      if (side === BLACK ? RANK[I.to] >= 7 : RANK[I.to] <= 3) return N('歩を打って守りの隙を埋める', '守りの隙を埋めます。', 'myKing');
      if (hit && !safe) return hit.t === FU ? N('合わせの歩を打つ', '歩を合わせます。', 'act') : N(`歩を打って${NAME[hit.t]}の頭をたたく`, `${NAME[hit.t]}の頭をたたきます。`, 'theirKing');
      if (safe && (side === BLACK ? RANK[I.to] === 4 : RANK[I.to] === 6)) return N('歩を打って次に成る含みを残す', '次に成る含みを残します。', 'theirKing');
      return N(`歩を打って${sqName(I.to)}を押さえる`, `${sqName(I.to)}を押さえます。`, 'act');
    }
    if (cheb(I.to, ownK) <= 2) return N(`${NAME[t]}を打って守りを固める`, '守りを固めます。', 'myKing');
    if (cheb(I.to, enK) <= 3) return N(`${NAME[t]}を打ち込んで攻めの拠点を作る`, '攻めの拠点を作ります。', 'theirKing');
    return by(N(`持ち駒の${NAME[t]}を${sqName(I.to)}に据える`, `${NAME[t]}の利きを盤上に加えます。`, 'act'));
  }
  // 駒得にはならない取り（取り返される、またはぶつけられた駒を取るだけ）
  if (I.cap) {
    const nm = NAME[I.cap], came = I.prevDrop ? '打ってきた' : I.cap === FU ? '突いてきた' : '出てきた';
    if (I.recapture) return N(`${NAME[t]}で取り返す`, '駒の損得を元に戻します。', 'mat');
    if (I.see >= 150) return N(`${nm}を取って駒得を図る`, '駒得を図ります。', 'mat');
    if (I.onPrev) return N(`${came}${nm}を取る`, '相手の仕掛けに応じます。', 'mat');
    return N(`${nm}を取って駒の交換に持ち込む`, '駒の交換に持ち込みます。', 'mat');
  }
  if (t === FU) {
    if (I.closed.some(x => x.t === KA || x.t === UM)) return N('角道を止めてじっくり構える', '角道を止めて、じっくり構えます。');
    if (I.opened.some(x => x.t === KA || x.t === UM)) return N('角道を開けて角を働かせる', '角道を開けます。', 'act');
    const rook = SQ81.find(s => P.board[s] === (HI | (side << 4)) && FILE[s] === f && ahead(side, s, I.to) > 0);
    if (after(P, [I.m], 1).attacked(I.to, side ^ 1)) {   // 取られる場所へ突く（歩をぶつける・突き捨てる）
      if (f === 1 || f === 9) return N('端歩をぶつけて端から仕掛ける', '端から仕掛けます。', 'theirKing');
      if (rook) return N('飛車先の歩を突いて歩交換を挑む', '飛車先の歩交換を挑みます。', 'act');
      return I.exposed.some(e => e.s === I.to) ? N(`${ZEN[f]}筋の歩を突き捨てる`, `${ZEN[f]}筋の歩を突き捨てます。`, 'theirKing')
        : N(`${ZEN[f]}筋で歩をぶつける`, `${ZEN[f]}筋で歩をぶつけます。`, 'act');
    }
    if (f === 1 || f === 9) {
      if (near(ownK) && cheb(I.to, ownK) <= 4) return N('端歩を突いて玉の逃げ道を広げる', '玉の逃げ道を広げておきます。', 'myKing');
      if (near(enK)) return N('端歩を伸ばして端攻めの含みを作る', '端攻めの含みを残します。', 'theirKing');
      return N('端歩を突いて相手の出方をうかがう', '相手の出方をうかがいます。');
    }
    if (rook) return N('飛車先の歩を伸ばす', '飛車先を伸ばしていきます。', 'act');
    if (RANK[I.to] === 5) return N(`${ZEN[f]}筋の位を取る`, `${ZEN[f]}筋の位を取ります。`, 'act');
    if (f === 5) return N('中央の歩を突いて駒の通り道を作る', '銀や角の通り道を作ります。', 'act');
    if (cheb(I.to, ownK) <= 2) return N('玉のそばの歩を突いて囲いの形を整える', '囲いの形を整えます。', 'myKing');
    return by(N(`${ZEN[f]}筋の歩を伸ばして戦いに備える`, '戦いに備えます。'));
  }
  if (GOLDISH.has(t)) {
    if (cheb(I.to, ownK) < cheb(I.from, ownK) && cheb(I.to, ownK) <= 2) return N([`${NAME[t]}を玉に寄せて守りを固める`, `${NAME[t]}を玉に近づけて囲いを厚くする`], ['守りを固めます。', '囲いを厚くします。'], 'myKing', 'guard');
    if (ahead(side, I.from, I.to) > 0 && cheb(I.to, ownK) > 2 && (side === BLACK ? RANK[I.to] <= 6 : RANK[I.to] >= 4)) return N(`${NAME[t]}を前線に繰り出す`, `${NAME[t]}を攻めに参加させます。`, 'theirKing');
    return by(N(`${NAME[t]}の位置を整える`, '形を整えます。'));
  }
  if (t === KE) return N('桂馬を跳ねて攻めに加える', '攻めに加えます。', 'theirKing');
  if (t === KY) return N(`香車を進めて${ZEN[f]}筋を押さえる`, `${ZEN[f]}筋を押さえます。`);
  if (t === KA || t === UM) {
    if (ahead(side, I.from, I.to) < 0) return by(N(`${NAME[t]}を${sqName(I.to)}に引いて働く場所を変える`, '働く場所を変えます。'));
    return N(`${NAME[t]}を${sqName(I.to)}に出て利きを広げる`, '利きを広げます。', 'act');
  }
  if (t === HI || t === RY) {
    if (FILE[I.from] !== f) return N(`${NAME[t]}を${ZEN[f]}筋に回してそこに戦力を集める`, `${ZEN[f]}筋に戦力を集めます。`, 'act');
    if (t === HI && RANK[I.to] === (side === BLACK ? 6 : 4)) return N('飛車を浮いて横にも利かせる', '横にも利きを通します。', 'act');
    return by(N(`${NAME[t]}の位置を${sqName(I.to)}に変える`, `${NAME[t]}の働きを変えます。`));
  }
  if (t === OU) {
    if (I.defA > I.defB) return N('玉を守りの金銀に近づける', '玉を守りの金銀に近づけます。', 'myKing');
    if (cheb(I.to, enK) > cheb(I.from, enK)) return N('玉を戦いの場所から遠ざける', '玉を戦いから遠ざけます。', 'myKing');
    return by(N('玉の居場所を整える', '玉の居場所を整えます。'));
  }
  return by(N(`${NAME[t]}を動かして形を整える`, '形を整えます。'));
}

// ---------------------------------------------------------------- 文脈をまとめる
const MEMO = new Memo();

function context(inp, memo) {
  const P = inp.base.clone(), side = P.stm, d = inp.data || null, main = inp.main;
  const M = P.parseUSI(main.move);
  if (!M) return null;
  const rnd = rng((P.hashLo ^ Math.imul(P.hashHi, 31) ^ Math.imul((inp.ply || 0) + 1, 2654435761)) >>> 0);
  const X = { P, side, d, main, M, memo, lastTo: inp.lastTo || 0, prev: inp.prev || null, score: main.score, used: new Set() };
  X.say = (key, list) => memo.pick(key, list, rnd);
  X.prevCap = !!(X.prev && X.prev.cap);
  X.bal0 = balance(P, side);
  X.Mi = moveInfo(P, M, X.lastTo, false, X.prevCap);
  X.Mi.prevDrop = !!(X.prev && X.prev.from === 0);
  X.Mk = X.Mi.k;
  X.v = verbOf(X.Mi);
  X.imm = aspectDiff(partsOf(P, side), partsOf(after(P, [M], 1), side));   // 指した直後の評価の変化
  X.nat = natureOf(P, X.Mi, X.imm, X.say);
  X.inCheck = P.inCheck();
  X.legal = d && d.legal ? d.legal : P.legalMoves().length;
  X.handPieces = 0;   // 歩以外の持ち駒の数（多い、または盤上の駒が減っていれば、もう駒組みの段階ではない）
  for (let c = 0; c < 2; c++) for (let t = KY; t <= KI; t++) X.handPieces += P.hand[c * 8 + t];
  if (SQ81.filter(q => P.board[q]).length < 30) X.handPieces = 9;
  X.opening = isOpening(P, inp.ply || 0, [X.lastTo, X.Mi.to]);
  if (main.book) { X.tempo = tempoNote(X, inp.hist); return X; }
  // 直前まで続いていた駒の取り合いも含めて損得を数える（取り返しただけで「駒得」と言わない）。
  // chain は直前の手から順に、続けて取られた（取った）駒
  const chain = X.prev ? X.prev.chain || (X.prev.cap ? [X.prev.cap] : []) : [];
  const walkFrom = (usis) => {
    const L = walk(P, usis, side, X.lastTo);
    chain.forEach((c, i) => {
      const e = { t: DEMOTE[c], board: c, ply: -1 - i, s: 0 };
      if (i % 2 === 0) { L.lost.unshift(e); L.mat -= EXV[c]; } else { L.got.unshift(e); L.mat += EXV[c]; }
    });
    return L;
  };
  // 指した手の読み筋は、本番の深い読み（「千里眼の読み」と同じもの）を使う
  const c0 = d && d.cands && d.cands[0] && d.cands[0].m === main.move ? d.cands[0] : null;
  const pv = main.pv && main.pv.length >= 2 ? main.pv : c0 && c0.pv.length ? c0.pv : [main.move];
  X.L = walkFrom(pv);
  X.mateLen = main.score >= MATE_IN_MAX ? (main.mate || X.L.moves.length) : 0;
  X.La = c0 && c0.pv.length ? walkFrom(c0.pv) : X.L;   // 候補どうしを比べる時は同じ深さの読み
  if (X.L.moves.length >= 2) X.R = moveInfo(after(P, X.L.moves, 1), X.L.moves[1], mTo(M), false, !!mCap(M));
  // 歩交換・駒の交換
  const L = X.L, Lm = L.moves;
  X.pawnTrade = X.Mi.t === FU && !X.Mi.drop && !X.Mi.cap && Lm.length >= 3 && mTo(Lm[1]) === X.Mi.to && mCap(Lm[1]) && mTo(Lm[2]) === X.Mi.to && mCap(Lm[2]);
  X.rookPawn = X.pawnTrade && (mPiece(Lm[2]) & 15) === HI;
  const w4 = matWords(L, 3, 0);
  X.trade = !X.pawnTrade && w4.traded.length && !w4.g.length && !w4.l.length && ((L.got.length && L.got[0].ply <= 1) || (L.lost.length && L.lost[0].ply <= 1)) ? TRADE[w4.traded[0]] || '' : '';
  // 相手の狙い・この手の狙い
  if (d && d.rootThreat) X.rt = threatInfo(P, [], d.rootThreat, side ^ 1);
  if (d && d.moveThreat) X.mt = threatInfo(P, [M], d.moveThreat, side);
  // 動かした駒を相手がすぐに取る（読み筋の応手。読み筋がなければ、ただで取られる形）なら、その駒の次の狙いは言わない
  X.takenNow = X.R ? !!(X.R.cap && X.R.to === X.Mi.to) : X.Mi.exposed.some(e => e.s === X.Mi.to);
  if (X.mt && ((X.R && X.R.cap && mFrom(X.mt.T) && X.R.to === mFrom(X.mt.T)) || (X.takenNow && mFrom(X.mt.T) === X.Mi.to))) X.mt.real = false;
  // この手そのものが攻めの手か（王手・成り・次の狙い・駒への当たり）。攻めながら駒をかわす手を「受け」とは言わない
  X.attacking = X.Mi.check || (X.Mi.promo && !X.takenNow) || !!(X.mt && X.mt.real) || X.Mi.threats.some(t => t.g >= 300 && X.Mi.hits.some(h => h.s === t.s));
  if (X.rt && X.rt.real) X.rtHandled = handled(X);
  X.tempo = tempoNote(X, inp.hist);
  // 候補手
  X.alts = [];
  X.twin = (a) => mFrom(a.A) === mFrom(M) && mTo(a.A) === mTo(M) && (mPiece(a.A) & 15) === (mPiece(M) & 15);   // 同じ手の成・不成違い
  if (d && c0 && c0.s != null) {
    const shM = c0.sh;
    for (let i = 1; i < d.cands.length; i++) {
      const c = d.cands[i], A = P.parseUSI(c.m);
      if (!A || c.s == null) continue;
      const a = { c, A, k: kifOf(P, A, X.lastTo), I: moveInfo(P, A, X.lastTo, false, X.prevCap), dv: c0.s - c.s, L: c.pv.length ? walkFrom(c.pv) : null };
      a.I.prevDrop = X.Mi.prevDrop;
      a.v = verbOf(a.I);
      a.nat = natureOf(P, a.I);
      a.ev = isMate(c.s) || isMate(X.score) ? c.s : X.score - Math.max(0, a.dv);
      a.tempting = shM != null && c.sh != null && c.sh - shM >= 80 && a.dv >= 80;
      if (c.om) a.omK = kifLine(after(P, [A], 1), c.om, mTo(A));                                   // すぐに詰まされる手順
      if (c.tr && a.L && a.L.moves.length >= 2) a.tr = threatInfo(P, [A, a.L.moves[1]], c.tr, side ^ 1);  // 相手の応手の狙い
      X.alts.push(a);
    }
    X.alts.sort((x, y) => x.dv - y.dv);
  }
  // 読みの途中で本命が入れ替わったか
  const it = d && d.iters ? d.iters : [];
  let lastOther = -1;
  for (let i = 0; i < it.length; i++) if (it[i][1] !== main.move) lastOther = i;
  if (lastOther >= 0 && it[lastOther][0] >= 5) {
    let i0 = lastOther;
    while (i0 > 0 && it[i0 - 1][1] === it[lastOther][1]) i0--;
    const A = P.parseUSI(it[lastOther][1]);
    if (A) X.mind = { m: it[lastOther][1], k: kifOf(P, A, X.lastTo), d1: it[i0][0], d2: it[lastOther][0], ds: lastOther + 1 < it.length ? it[lastOther + 1][0] : (main.depth || it[lastOther][0]) + 1 };
  } else if (it.length >= 6) {
    let i0 = it.length - 1;
    while (i0 > 0 && it[i0 - 1][1] === main.move) i0--;
    X.stable = it[i0][0];
  }
  return X;
}
function after(P, moves, n) { const p = P.clone(); for (let i = 0; i < n; i++) p.doMove(moves[i]); return p; }
function kifLine(pos, usis, prevTo) {
  const p = pos.clone(), out = [];
  for (const u of usis) { const m = p.parseUSI(u); if (!m) break; out.push(kifOf(p, m, prevTo)); prevTo = mTo(m); p.doMove(m); }
  return out;
}

// この手が相手の狙いを消しているか、どうやって消しているか（詰めろなら、深い読みで詰まされていないこと）。
// took：狙いの駒を取った、moved：狙われていた駒を動かした、blocked：利きを止めた、guarded：紐をつけた
function handled(X) {
  const T = X.rt, I = X.Mi;
  if (T.mate) return !isMate(X.score) || X.score > 0 ? 'mate' : false;
  if ([1, 3, 5].some(i => X.L.moves[i] === T.T)) return false;
  if (mFrom(T.T) && I.to === mFrom(T.T)) return 'took';
  const target = T.cap ? T.cap.s : T.I.threats.length ? T.I.threats[0].s : 0;
  if (I.from && target && I.from === target) return 'moved';
  if (!T.cap) return X.L.moves.length < 2 || X.L.moves[1] !== T.T ? 'other' : false;
  const s = T.cap.s;
  if (mFrom(T.T) && I.blocks.some(b => b.s === mFrom(T.T))) return 'blocked';
  if (I.saved.some(x => x.s === s)) return 'guarded';
  return X.L.moves.length >= 2 && X.L.moves[1] !== T.T && !(mTo(X.L.moves[1]) === s && mCap(X.L.moves[1])) ? 'other' : false;
}

// ---------------------------------------------------------------- 言葉の部品
function standWords(X, v) {
  if (v >= 3000) return X.say('st+4', ['勝勢です', '勝ちが見えてきました']);
  if (v >= 1500) return X.say('st+3', ['はっきり優勢です', '優勢を保てています']);
  if (v >= 600) return X.say('st+2', ['有利です', 'リードを広げつつあります']);
  if (v >= 200) return X.say('st+1', ['少し指しやすい局面です', 'わずかにリードしています']);
  if (v > -200) return X.say('st0', ['互角の形勢です', 'まだ形勢は五分です', 'どちらとも言えない形勢です']);
  if (v > -600) return X.say('st-1', ['少し苦しい局面です', 'わずかに押されています']);
  if (v > -1500) return X.say('st-2', ['苦しい形勢です', '形勢は思わしくありません']);
  return X.say('st-3', ['かなり苦しい形勢です', '大差をつけられています']);
}
// 相手の応手の性格（「△同歩と取り返して」の「と取り返して」の部分）。prev はその前の手
function replyTe(R, prev) {
  if (!R) return 'と応じて';
  if (R.cap && R.to === mTo(prev)) return mCap(prev) ? 'と取り返して' : 'と取って';
  if (R.cap) return `と${NAME[R.cap]}を取って`;
  if (R.check) return 'と王手をかけて';
  if (R.fled) return 'と逃げて';
  if (R.saved.length) return 'と受けて';
  if (R.threats.length) return 'と反撃して';
  return 'と応じて';
}
// 取られる駒の名前。読み筋の途中で成った駒は、いま盤上にある姿（成る前の名前）で呼ぶ
const capName = (L, x) => (x.board !== x.t && L.promos.some(p => !p.mine && p.s === x.s && p.ply < x.ply) ? NAME[x.t] : NAME[x.board]);
// 狙いの中身を動詞句で（「△５五角で４四の金を取る」「▲１四歩△同歩のあと、▲同香で香車を取る」など）と、
// その名詞句（「〜手」「〜筋」）。あとで駒を取る筋は、取るところまでの手順を見せる（どう狙っているかがわかるように）
function threatVerb(T) {
  const L = T.L, I = T.I, cap = T.cap, big = I.threats.filter(x => x.g >= 300), k = L.kifs;
  const pr = L.promos.find(x => x.mine && x.kept && x.ply <= 2);
  const upTo = (j) => (j <= 0 ? T.k : `${k.slice(0, j).join('')}のあと、${k[j]}`);   // j 手目がその狙いの決め手
  const pair = (a, b) => (a.t === b.t ? `二枚の${NAME[a.t]}` : `${NAME[a.t]}と${NAME[b.t]}`);
  if (I.cap && I.cap !== FU) return [`${T.k}で${NAME[I.cap]}を取る`, '手'];
  if (!I.cap && big.length >= 2) return [`${T.k}で${pair(big[0], big[1])}の両取りをかける`, '手'];
  if (pr && pr.ply === 0) return [`${T.k}と成って${NAME[pr.t]}を作る`, '手'];
  if (!I.cap && big.length) return [`${T.k}で${sqName(big[0].s)}の${NAME[big[0].t]}に当てる`, '手'];
  if (pr) return [`${upTo(pr.ply)}で${NAME[pr.t]}を作る`, '筋'];
  if (cap && cap.t !== FU && cap.ply <= 4) return [`${upTo(cap.ply)}で${capName(L, cap)}を取る`, '筋'];
  const lim = Math.min(L.horizon, 4), w = matWords(L, lim), top = w.g.filter(t => t !== FU).sort((a, b) => HV[b] - HV[a])[0];
  const lastGot = (t) => L.got.filter(x => x.ply <= lim && (t == null || x.t === t)).reduce((m, x) => Math.max(m, x.ply), 0);
  if (w.net >= 150 && top) return [`${upTo(lastGot(top))}で${NAME[top]}を取る`, '筋'];
  if (w.net >= 150) return [`${k.slice(0, lastGot() + 1).join('')}と進めて${gainNoun(w)}にする`, '筋'];
  if (I.check) return [`${T.k}と王手をかける`, '手'];
  return [`${T.k}から攻めを続ける`, '筋'];
}
function threatNoun(T) {
  const [v, n] = threatVerb(T);
  return v + n;
}
// ---------------------------------------------------------------- この手の主な理由
function purposeOf(X) {
  const I = X.Mi, fork = I.threats.filter(th => th.t !== FU && I.hits.some(h => h.s === th.s));
  if (X.main.book) return 'book';
  if (X.mateLen) return 'mate';
  if (X.legal <= 1) return 'forced';
  if (X.inCheck) return 'evasion';
  if (X.rt && X.rt.real && X.rt.mate && X.rtHandled) return 'defendMate';
  if (I.recapture && X.prev && X.prev.cap) return 'recapture';
  if (I.check && fork.length && fork[0].g >= 400 && !X.takenNow) return 'fork';
  if (fork.length >= 2 && fork[1].g >= 300 && !X.takenNow) return 'fork';
  if (I.cap && I.see >= 150) return 'capture';
  if (X.mt && X.mt.real && X.mt.mate) return 'mateThreat';
  // 突いてきた歩などをそのまま取るのは「受け」とは言わない（取らないと何をされるかは、ほかの手の説明で）
  // 攻めの手が結果として狙いを消している（駒をかわしている、相手に暇を与えない）なら、攻めの方を主に言う
  const attackFirst = X.attacking && (X.rtHandled === 'moved' || X.rtHandled === 'other');
  if (X.rt && X.rt.real && X.rtHandled && !(X.rtHandled === 'took' && I.onPrev) && !attackFirst) return 'defend';
  if (I.fled >= 300 && !X.attacking) return 'escape';
  if (I.t === FU && I.threats.some(th => th.g >= 300 && I.hits.some(h => h.s === th.s))) return 'pawnStrike';
  if (I.see <= -150 && X.score > -MATE_IN_MAX) return 'sacrifice';
  if (X.pawnTrade) return 'pawnTrade';
  if (X.trade && I.cap) return 'trade';
  if (I.cap && I.onPrev && !I.recapture) return 'accept';
  if (I.promo && X.L.promos.length && X.L.promos[0].ply === 0 && X.L.promos[0].kept) return 'promote';
  if (X.mt && X.mt.real) return 'threat';
  if (!X.takenNow && I.t !== FU && I.threats.some(t => t.t !== FU && t.g >= 300 && I.hits.some(h => h.s === t.s))) return 'hit';
  if (I.castle) return 'castle';
  if (I.t === FU && I.hits.some(h => h.t !== OU)) return 'pawnStrike';
  if (I.check) return 'check';
  return 'plan';
}

const LEAD = {
  book(X) {
    const n = X.nat, I = X.Mi;
    if (I.cap && I.onPrev && !I.recapture && X.prev) return X.say('book.take', [
      `定跡どおり、${X.prev.k}には${X.Mk}と取ります。`,
      `${X.prev.k}には${X.Mk}と取るのが定跡です。`,
    ]);
    return X.say('book', [
      `${X.Mk}は序盤の定跡にある手で、${n.np}狙いです。`,
      `ここはまだ定跡の範囲なので、${X.Mk}と${X.v[1]}${n.goal}`,
      `定跡どおりの${X.Mk}です。${n.np}のが狙いです。`,
    ]);
  },
  mate(X) {
    const L = X.L, n = X.mateLen, Mk = X.Mk;
    if (n <= 1) return X.say('mate1', [`${Mk}で詰みです。`, `ここは${Mk}の一手で詰んでいます。`, `${Mk}と指せば、あなたの玉にはもう逃げ道がありません。`]);
    const out = [X.say('mate', [
      `${n}手詰めを読み切りました。${Mk}からあなたの玉を追い詰めます。`,
      `この局面には詰みがあります。${Mk}から${n}手で、あなたの玉が詰む手順を確かめました。`,
      `${Mk}が詰みへの入口です。ここから${n}手で寄せ切れます。`,
      `${Mk}以下、${n}手であなたの玉を詰ませられる局面になりました。`,
    ])];
    const k = L.kifs;
    if (k.length >= 3) {
      const seq = k.length <= 7 ? k.join('') : k.slice(0, 5).join('') + '…' + L.kabs[k.length - 1];
      out.push(X.say('mate.seq', [`手順は${seq}です。`, `${seq}と進めば詰みます。`, `読み筋は${seq}。`]));
      const sac = L.moves.findIndex((m, i) => i % 2 === 0 && i + 1 < L.moves.length && mTo(L.moves[i + 1]) === mTo(m) && mCap(L.moves[i + 1]));
      const quiet = L.moves.findIndex((m, i) => i % 2 === 0 && !L.checks.some(c => c.ply === i));
      if (sac >= 0 && sac + 1 < k.length) {
        const byKing = (mPiece(L.moves[sac + 1]) & 15) === OU;
        out.push(X.say('mate.sac', [
          `途中の${k[sac]}は捨て駒で、${byKing ? '玉で取らせて引っ張り出すのが' : '取らせて形を崩すのが'}ポイントです。`,
          `${k[sac]}と駒を捨てるところが急所で、${k[sac + 1]}と取らせてから一気に迫ります。`,
        ]));
      } else if (quiet >= 0) {
        out.push(`途中の${k[quiet]}は王手ではありませんが、詰みを防ぐ受けがありません。`);
      } else if (n >= 5) {
        out.push(X.say('mate.chk', ['王手を続けて、逃げ道を一つずつ消していく順です。', '最後まで王手の連続で迫ります。']));
      }
    }
    return out.join('');
  },
  forced(X) {
    return X.say('forced', [
      `指せる手は${X.Mk}しかありませんでした。`,
      X.inCheck && X.prev ? `${X.prev.k}の王手をかわす手は、${X.Mk}の一通りだけです。` : null,
      `この局面で指せるのは${X.Mk}だけです。`,
    ]);
  },
  evasion(X) {
    const I = X.Mi, pk = X.prev ? X.prev.k + 'の' : 'この';
    const te = I.t === OU ? (I.cap ? `玉で${NAME[I.cap]}を取って` : '玉をかわして')
      : I.cap ? `王手をかけてきた${NAME[I.cap]}を取って` : I.drop ? `${NAME[I.t]}を合駒して` : `${NAME[I.t]}を間に入れて`;
    const plain = I.t === OU ? (I.cap ? `玉で${NAME[I.cap]}を取る` : '玉をかわす')
      : I.cap ? `王手をかけてきた${NAME[I.cap]}を取る` : I.drop ? `${NAME[I.t]}を合駒する` : `${NAME[I.t]}を間に入れる`;
    return X.say('evasion', [
      `${pk}王手には、${te}受けました（${X.Mk}）。`,
      `王手の受け方は${X.legal}通りありましたが、${X.Mk}と${plain}のが最善です。`,
      `${X.Mk}で王手を受けます。${plain}形がいちばん安全と見ました。`,
    ]);
  },
  defendMate(X) {
    const T = X.rt, n = T.mate, tail = n <= 1 ? 'の一手詰め' : `以下の${n}手詰め`;
    return X.say('defMate', [
      `あなたは${T.k}${tail}を狙っていました。${X.Mk}はその詰み筋を消す受けです。`,
      `ここは受けが必要な局面でした。放っておくと${T.k}${n <= 1 ? 'で' : `以下${n}手で`}詰まされるため、${X.Mk}と${X.v[1]}受けています。`,
      `まず${T.k}からの詰みを防ぐのが先決で、${X.Mk}がその受けです。`,
      `${T.k}${tail}が残っていたので、${X.Mk}で先に受けました。`,
    ]);
  },
  recapture(X) {
    const p = X.prev, lost = NAME[p.cap];
    X.used.add('evenTold');
    return X.say('recap', [
      `${p.k}で${lost}を取られたので、${X.Mk}と取り返しました。`,
      `まずは${X.Mk}と取り返します。${lost}を取られたままでは駒損になるからです。`,
      `${p.k}には${X.Mk}。取られた${lost}の分を、すぐに取り戻します。`,
      `${X.Mk}と取り返して、駒の損得を元に戻しました。`,
    ]);
  },
  fork(X) {
    const I = X.Mi, th = I.threats.filter(x => x.t !== FU && I.hits.some(h => h.s === x.s)), a = th[0];
    if (I.check) {
      const nm = a.t === HI || a.t === RY ? '王手飛車取り' : a.t === KA || a.t === UM ? '王手角取り' : '';
      return X.say('forkChk', [
        nm ? `${X.Mk}は${nm}です。王手を受けている間に${NAME[a.t]}を取れます。` : `${X.Mk}は王手をかけながら、${sqName(a.s)}の${NAME[a.t]}にも当てた手です。`,
        `${X.Mk}と${X.v[1]}王手をかけ、同時に${sqName(a.s)}の${NAME[a.t]}も狙いました。`,
        `王手と${NAME[a.t]}取りを同時にかける${X.Mk}です。王手を受ければ${NAME[a.t]}が取れます。`,
      ]);
    }
    const b = th[1];
    const pair = a.t === b.t ? `${sqName(a.s)}と${sqName(b.s)}の${NAME[a.t]}` : `${NAME[a.t]}と${NAME[b.t]}`;
    return X.say('fork', [
      `${X.Mk}と${X.v[1]}、${sqName(a.s)}の${NAME[a.t]}と${sqName(b.s)}の${NAME[b.t]}を同時に狙いました。`,
      `${X.Mk}は${pair}の両取りです。どちらかは助かりません。`,
      `${pair}に同時に当たりをかける${X.Mk}を選びました。片方を逃げても、もう片方が取れます。`,
    ]);
  },
  capture(X) {
    const I = X.Mi, nm = NAME[I.cap], at = sqName(I.to), Lm = X.L.moves, p = X.prev;
    // 直前に取られた駒の分を、別の場所で取り返す手
    const ex = p && p.cap && (p.chain || [p.cap]).length === 1 && EXV[I.cap] >= EXV[p.cap] * 0.75 && EXV[I.cap] <= EXV[p.cap] * 1.25;
    const after = X.bal0 + HV[DEMOTE[I.cap]];   // 取ったあとの、対局開始からの駒の損得
    if (!I.recapture && (ex || (X.bal0 <= -100 && Math.abs(after) < 100))) X.used.add('evenTold');
    if (!I.recapture && !ex && X.bal0 <= -100 && Math.abs(after) < 100) return X.say('capture.even0', [
      `${X.Mk}で${nm}を取り、駒の損得を五分に戻します。`,
      `${X.Mk}と${nm}を取って、先に取られていた分を取り返しました。`,
    ]);
    if (!I.recapture && ex) return X.say('capture.back', [
      `${p.k}で${NAME[p.cap]}を取られた分を、${X.Mk}と${nm}を取って取り戻します。`,
      `${X.Mk}で${nm}を取り、直前に取られた${NAME[p.cap]}の分を取り返しました。`,
    ]);
    // 読み筋の中で取り返されて得が残らないなら、「得」とは言わない
    if (matWords(X.L, X.L.shown, 0).net < 100) return X.say('capture.even', [`${X.Mk}で${at}の${nm}を取ります。`, `ここは${X.Mk}と${nm}を取っておきます。`]);
    const free = I.see >= EXV[I.cap] && !(Lm.length >= 2 && mTo(Lm[1]) === I.to && mCap(Lm[1]));
    return X.say('capture', [
      free ? `${at}の${nm}に守りがなかったので、${X.Mk}と取りました。` : `${X.Mk}で${nm}を取ります。取り返されても、差し引きでこちらの得です。`,
      free ? `${nm}がただで取れる形だったので、${X.Mk}と取っています。` : `${at}の${nm}を${X.Mk}と取りました。取り合いになっても駒得が残ります。`,
      after >= 100 ? `${X.Mk}と${nm}を取って、駒得をはっきりさせました。` : null,
      free ? `あなたの${nm}がただで取れるので、${X.Mk}を選びました。` : null,
    ]);
  },
  mateThreat(X) {
    const T = X.mt, n = T.mate;
    return X.say('tsume', [
      n <= 1 ? `${X.Mk}は詰めろです。放っておくと次の${T.k}で詰みます。` : `${X.Mk}は詰めろです。放っておくと${T.k}から${n}手で詰みます。`,
      `${X.Mk}で、あなたの玉に詰めろをかけました（次に${T.k}${n > 1 ? `以下${n}手` : ''}で詰み）。`,
      `この手で、受けなければ${T.k}${n > 1 ? `からの${n}手詰め` : 'の一手詰め'}が生じます。`,
      `${X.Mk}と${X.v[1]}玉に迫り、${T.k}からの詰みを見せました。`,
    ]);
  },
  defend(X) {
    const T = X.rt, I = X.Mi, how = X.rtHandled, d = threatNoun(T);
    if (how === 'took') return X.say('defend.took', [
      `${X.Mk}と取って、あなたの${d}を未然に防ぎました。`,
      `${d}を許さないよう、${X.Mk}と狙いの駒を取り払います。`,
    ]);
    if (how === 'moved') return X.say('defend.moved', [
      `${d}を避けるため、${X.Mk}と${NAME[I.t]}を逃がしました。`,
      `${X.Mk}と${X.v[1]}、${d}をかわしています。`,
      `狙われていた${NAME[I.t]}を${X.Mk}と${X.v[1]}、${d}をかわします。`,
    ]);
    const blk = how === 'blocked' && I.blocks.find(b => b.s === mFrom(T.T));
    const te = how === 'guarded' && T.cap ? `${sqName(T.cap.s)}の${NAME[T.cap.board]}に紐をつけて` : blk ? `${NAME[blk.t]}の利きを止めて` : X.v[1];
    return X.say('defend', [
      `あなたは次に${d}を狙っていました。${X.Mk}と${te}、それを防ぎます。`,
      `${d}が気になる局面でした。${X.Mk}と${te}、その狙いを消しています。`,
      `何もしないと${d}が厳しいので、${X.Mk}と${te}先に受けておきます。`,
    ]);
  },
  accept(X) {
    const p = X.prev;
    return X.say('accept', [
      p ? `${p.k}には、${X.Mk}と素直に取ります。` : null,
      `ここは${X.Mk}と取るのが自然です。`,
      p ? `${X.Mk}と取って、${p.k}に応じます。` : null,
    ]);
  },
  escape(X) {
    const I = X.Mi, nm = NAME[I.t];
    return X.say('escape', [
      `${sqName(I.from)}の${nm}に当たりがかかっていたので、${X.Mk}と逃げました。`,
      `取られそうだった${nm}を、${X.Mk}でかわしました。`,
      `${nm}を安全な${sqName(I.to)}へ移す${X.Mk}です。`,
    ]);
  },
  sacrifice(X) {
    const I = X.Mi, nm = NAME[I.nt], comp = compensation(X);
    const takes = X.R && X.R.cap && X.R.to === I.to, R = takes ? X.L.kifs[1] : '';
    X.used.add('comp');
    const told = (t) => { if (R && t.includes(R)) X.used.add('reply'); return t; };
    if (I.t === FU && !I.drop && !I.cap) return told(X.say('sac.fu', [
      `${X.Mk}は歩の突き捨てです。${takes ? `${R}と取らせて、` : ''}${comp[1]}。`,
      `${X.Mk}と突き捨てて、相手の形を乱しにいきます。${comp[1]}。`,
    ]));
    if (I.cap) return told(X.say('sac.cap', [
      `${X.Mk}は${NAME[I.cap]}を取って${nm}を差し出す手です。${R ? `${R}と取られても、` : ''}${comp[1]}。`,
      `${X.Mk}と${NAME[I.cap]}を取り、${nm}は渡します。${comp[0]}と読んでいます。`,
    ]));
    return told(X.say('sac', [
      `${X.Mk}は${nm}を捨てる手です。${R ? `${R}と取られても、` : ''}${comp[1]}。`,
      `あえて${nm}を渡す${X.Mk}を選びました。${comp[0]}と読んでいます。`,
      `駒損を承知の${X.Mk}です。${comp[1]}。`,
    ]));
  },
  pawnTrade(X) {
    const seq = X.L.kifs.slice(1, 3).join(''), pre = X.rookPawn ? '飛車先の' : '';
    return X.say('ptrade', [
      `${X.Mk}は${pre}歩を交換しにいく手です。${seq}と進めば、歩を一枚持ち駒にできます。`,
      `${X.Mk}と突き捨てて、${seq}で${pre}歩交換を果たします。`,
      `${pre}歩交換を狙う${X.Mk}です。手にした歩は、あとで攻めにも受けにも使えます。`,
    ]);
  },
  promote(X) {
    const I = X.Mi, nt = NAME[I.nt];
    const aim = X.mt && X.mt.real ? `次は${threatNoun(X.mt)}も見えています。` : I.enemyK <= 3 ? 'あなたの玉に近い場所で働きます。' : '';
    return X.say('promo', [
      `${X.Mk}で${nt}を作りました。${aim}`,
      `${NAME[I.t]}が成って${nt}になる${X.Mk}です。${aim}`,
      `${X.Mk}と${X.v[1]}、${nt}の力を生かします。${aim}`,
    ]);
  },
  threat(X) {
    const d = threatNoun(X.mt);
    return X.say('threat', [
      `${X.Mk}の狙いは、次の${d}です。`,
      `${X.Mk}と${X.v[1]}、次に${d}を見せました。`,
      `次に${d}があるので、あなたは受けに回る必要があります。${X.Mk}はその含みを持った手です。`,
      `${X.Mk}は${d}を狙った一手です。`,
    ]);
  },
  hit(X) {
    const I = X.Mi, t = I.threats.filter(x => x.t !== FU && I.hits.some(h => h.s === x.s)).sort((a, b) => b.g - a.g)[0];
    return X.say('hit', [
      `${X.Mk}と${X.v[1]}、${sqName(t.s)}の${NAME[t.t]}に当てました。`,
      `${X.Mk}で${sqName(t.s)}の${NAME[t.t]}に当たりをかけます。`,
    ]);
  },
  castle(X) {
    const c = X.Mi.castle;
    return X.say('castle', [
      `${X.Mk}で${c}が完成しました。`,
      `${c}に組む${X.Mk}です。玉の守りがぐっと固くなります。`,
      X.Mi.t === OU ? `${X.Mk}と${X.v[1]}、玉を${c}に収めました。` : `${X.Mk}と${X.v[1]}、${c}の形を整えました。`,
    ]);
  },
  trade(X) {
    X.used.add('tradeTold');
    if (X.Mi.onPrev && !X.Mi.recapture) return X.say('trade.accept', [`${X.Mk}と取って、${X.trade}に応じます。`, `${X.trade}を受けて立つ${X.Mk}です。`]);
    return X.say('trade', [`${X.Mk}は${X.trade}を挑む手です。`, `${X.trade}を狙った${X.Mk}です。`, `${X.Mk}から${X.trade}に持ち込みます。`]);
  },
  pawnStrike(X) {
    const I = X.Mi, h = I.hits.filter(x => x.t !== OU).sort((a, b) => E.PV[b.t] - E.PV[a.t])[0], nm = NAME[h.t];
    const promoNext = X.side === BLACK ? RANK[I.to] <= 4 : RANK[I.to] >= 6;
    const canTake = E.attacksFrom(after(X.P, [X.M], 1), h.s).indexOf(I.to) >= 0;
    // 相手がその歩をすぐに取る読み筋なら、「取らなければ成れる」のような仮定の話はしない
    const takes = X.R && X.R.cap && X.R.to === I.to, Rk = takes ? X.L.kifs[1] : '';
    if (I.drop && takes) { X.used.add('reply'); return X.say('tataki.take', [
      `${X.Mk}と${nm}の頭に歩を打ち、${Rk}と取らせます。`,
      `${X.Mk}は${nm}の頭をたたく歩です。${Rk}と取らせて、${nm}の位置をずらします。`,
    ]); }
    if (I.drop) return X.say('tataki', [
      canTake ? `${X.Mk}と打って、${nm}の頭をたたきました。` : `${X.Mk}と打って${nm}に当て、${promoNext ? '次は成り込みを狙います' : 'その動きを縛ります'}。`,
      canTake && promoNext ? `${X.Mk}は${nm}に当てる歩打ちです。取れば形が崩れ、取らなければ歩が成り込めます。`
        : canTake ? `${X.Mk}は${nm}に当てる歩打ちです。取らせて${nm}の位置をずらす狙いがあります。` : null,
      h.t === FU ? `${X.Mk}と合わせの歩を打ち、どう応じるかを問います。` : `${nm}の正面に${X.Mk}と歩を打ち、どう応じるかを問います。`,
    ]);
    const big = I.hits.filter(x => x.t !== OU && x.t !== FU).sort((a, b) => E.PV[b.t] - E.PV[a.t])[0];
    if (!big) return X.say('clash', [
      `${X.Mk}と歩をぶつけて、${ZEN[FILE[I.to]]}筋で戦いを起こします。`,
      `${X.Mk}は${ZEN[FILE[I.to]]}筋の歩をぶつける仕掛けです。`,
      `ここで${X.Mk}と突き、歩をぶつけて動きます。`,
    ]);
    if (takes) { X.used.add('reply'); return X.say('tsuki.take', [
      `${X.Mk}と突いて${NAME[big.t]}に当て、${Rk}と取らせます。`,
      `${X.Mk}と歩をぶつけて、${Rk}と取らせます。`,
    ]); }
    return X.say('tsuki', [
      `${X.Mk}と${X.v[1]}、${sqName(big.s)}の${NAME[big.t]}に当てました。`,
      `${X.Mk}は${NAME[big.t]}をどかしにいく歩です。`,
      `${NAME[big.t]}の前に歩を突き出す${X.Mk}です。${NAME[big.t]}はどこかへ逃げる必要があります。`,
    ]);
  },
  check(X) {
    const L = X.L, R = X.R, pr = L.promos.find(p => p.mine && p.kept && p.ply <= L.shown), w = matWords(L, L.shown);
    const gain = !pr && L.mat >= 150 && w.net >= 150 && X.bal0 + matWords(L, L.shown, 0).net >= 100 && gainNoun(w);
    if (gain) X.used.add('gainTold');
    const aim = pr ? `その間に${NAME[pr.t]}を作れます` : gain ? `${gain}に持ち込みます`
      : R && R.t === OU ? `玉を${sqName(R.to)}へ動かして、守りから引き離します` : R && R.drop ? `持ち駒を一枚使わせます` : '攻めのきっかけを作ります';
    const out = X.say('check', [
      `${X.Mk}と王手をかけました。${R ? `${R.k}と応じさせてから、` : ''}${R ? aim.replace(/^その間に/, '') : aim}。`,
      `${X.Mk}は王手で先手を取る手です。${aim}。`,
      `まずは${X.Mk}の王手から入ります。${aim}。`,
    ]);
    if (R && out.includes(R.k)) X.used.add('reply');
    return out;
  },
  plan(X) {
    const n = X.nat;
    return X.say('plan', [
      `${X.Mk}は、${n.np}手です。`,
      `${X.Mk}と${X.v[1]}、${n.goal}`,
      `ここは${n.np}${X.Mk}を選びました。`,
    ]);
  },
};

// 駒を捨てる手の見返り：[普通体, 丁寧体]
function compensation(X) {
  const L = X.L;
  if (L.mated === (X.side ^ 1)) return ['そのまま寄せ切れる', 'そのまま寄せ切れます'];
  if (L.mat >= 0 && L.got.length) return ['あとで駒を取り返せる', 'あとで駒は取り返せます'];
  const pr = L.promos.find(p => p.mine && p.kept && p.ply <= L.shown);
  if (pr) { X.used.add('promoTold'); return [`その間に${NAME[pr.t]}を作れる`, `その間に${NAME[pr.t]}を作れます`]; }
  const d = aspectDiff(partsOf(X.P, X.side), L.parts);
  if (d.theirKing >= d.myKing && d.theirKing > 60) return ['その分あなたの玉に迫れる', 'その分、あなたの玉に迫れます'];
  if (d.myKing > 60) return ['自玉の安全が手に入る', '代わりに自玉の安全が手に入ります'];
  if (X.score >= -150) return ['形勢は損ねない', '形勢は損ねません'];
  return ['ほかの手よりはまし', 'それでもほかの手よりはましです'];
}

// ---------------------------------------------------------------- 読み筋の一文
function lineSentence(X) {
  const L = X.L, k = L.kifs;
  if (k.length < 2) return '';
  const seq = k.slice(1, L.shown + 1).join(''), rest = k.slice(2, L.shown + 1).join('');
  if (L.fight === 0 && L.build >= 2 && L.mated < 0 && X.handPieces <= 1 && X.memo.ago('build') >= 3) {
    X.memo.mark('build');
    return X.say('line.build', [
      `読み筋は${seq}で、しばらくは互いに陣形を整える展開が続くと見ています。`,
      `このあとは${seq}と、双方が駒組みを進める穏やかな進行を予想しています。`,
      `${seq}と、まだ駒がぶつかる前の準備が続く見込みです。`,
    ]);
  }
  const out = outcome(X), te = replyTe(X.R, X.M);
  const best = rest && !/最善/.test(X.leadText || '');   // 「最善」を一つの段落で二度言わない
  // 相手の応手はもう書いたので、その先だけ
  if (X.used.has('reply') && rest) return X.say('line.rest', [`以下${rest}と進むと読んでいます。`, `そのあとは${rest}と続く見込みです。`]) + out;
  if (!out) return X.say('line.plain', [
    `読み筋は${seq}です。`,
    best ? `あなたの最善の応手は${k[1]}で、以下${rest}と進むと読んでいます。` : null,
    best ? `${k[1]}${te}くるのが最善と見ていて、以下${rest}と続きます。` : null,
    `予想される進行は${seq}です。`,
  ]);
  return X.say('line', [
    `読み筋は${seq}で、${out}`,
    best ? `あなたの最善の応手は${k[1]}で、以下${rest}と進むと読んでいます。${out}` : null,
    `このあと${seq}と進めば、${out}`,
    `予想される進行は${seq}。${out}`,
    best ? `${k[1]}${te}くるのが最善で、${rest}と続きます。${out}` : null,
    L.fight >= 2 ? `${seq}と、すぐに駒がぶつかる展開です。${out}` : null,
  ]);
}
// 駒の損得や成りは、読み筋の一文で見せた範囲で起きることだけを言う
// （「得」「損」は、対局開始からの損得 b1 で見てもそうなるときだけ言う）
function outcome(X) {
  const L = X.L, w = matWords(L, L.shown), pr = L.promos.find(p => p.mine && p.kept && p.ply <= Math.min(4, L.shown));
  if (L.mated === (X.side ^ 1)) return 'あなたの玉が詰みます。';
  const g = gainNoun(w), b1 = X.bal0 + matWords(L, L.shown, 0).net, even = Math.abs(b1) < 100 && !X.used.has('evenTold');
  if (w.net >= 150 && g && !X.used.has('gainTold')) {
    if (b1 >= 100) return X.say('out.gain', [`${g}になります。`, g.includes('交換') ? null : `差し引き${g}です。`, `${g}が見込めます。`]);
    if (even) return X.say('out.even', ['これで駒の損得は五分に戻ります。', '駒の損得は、これで互角に戻ります。']);
  }
  if (pr && !X.used.has('promoTold')) return X.say('out.promo', [`${NAME[pr.t]}ができます。`, `${NAME[pr.t]}を作れます。`]);
  if (w.net <= -150 && g && L.mat < -100) {
    if (b1 <= -100) return X.used.has('comp') ? `${g}になります。` : `${g}になりますが、${compensation(X)[1]}。`;
    if (even) return X.used.has('comp') ? '駒の損得は五分に戻ります。' : `駒の損得は五分に戻りますが、${compensation(X)[1]}。`;
  }
  // 駒の交換（最初に取った駒をこの手の種類として言い、ほかにも交換があればまとめて）
  const tw = matWords(L, L.shown, 0), kinds = [...new Set(tw.traded)].sort((a, b) => HV[b] - HV[a]);
  if (X.trade && !X.used.has('tradeTold')) return kinds.length >= 2 ? `${kinds.map(t => SHORT[t]).join('と')}をそれぞれ交換する形になります。` : `${X.trade}になります。`;
  const st = standNow(X);
  return st ? `千里眼から見て${st}。` : '';
}
// 形勢のひとことは、前と同じ評価が続くあいだは言い直さない
function standBucket(v) { return v >= 3000 ? 4 : v >= 1500 ? 3 : v >= 600 ? 2 : v >= 200 ? 1 : v > -200 ? 0 : v > -600 ? -1 : v > -1500 ? -2 : -3; }
function standNow(X) {
  if (X.used.has('stand')) return '';
  const b = standBucket(X.score), m = X.memo;
  if (m.lastStand === b && m.ago('stand') < 3) return '';
  m.lastStand = b; m.mark('stand'); X.used.add('stand');
  return standWords(X, X.score);
}

// ---------------------------------------------------------------- 選ばなかった手の「なぜ」
// その手を指すと相手にどんな手があり、何が起きるのか。候補の読み筋をたどって、決め手になる相手の手を探す
function refutation(X, a) {
  const L = a.L, side = X.side;
  if (!L || L.moves.length < 2) return null;
  const k = L.kifs, ka = L.kabs, pos = X.P.clone(), steps = [];
  for (let i = 0; i < Math.min(L.moves.length, 8); i++) {   // 先の方は推測が混じるので 8 手まで
    const m = L.moves[i], I = pos.stm !== side ? moveInfo(pos, m, mTo(L.moves[i - 1]), false, !!mCap(L.moves[i - 1])) : null;
    steps.push({ i, I });
    pos.doMove(m);
  }
  const r = {};
  // 長い手順は、初めの二手と終わりの二手を残して「…」で略す（略したすぐあとの手は「同」を使わずに書く）
  const span = (from, to) => (to - from <= 6 ? k.slice(from, to).join('') : k.slice(from, from + 2).join('') + '…' + ka[to - 2] + k[to - 1]);
  // K は決め手になる相手の手、Ks はそれを手順なしで単独に書くとき用、R1 と rest は相手の最初の応手とそれ以降
  const at = (j, kind, more) => Object.assign(r, { kind, key: j, K: k[j], Ks: j <= 1 ? k[j] : ka[j], pre: span(1, j), seq: span(1, j + 1),
    R1: k[1], rest: span(2, j + 1), pv: steps[j] && steps[j].I ? verbOf(steps[j].I)[2] : '指されて', asp: dAsp, w: weak() }, more);
  // 選んだ手の変化と比べて、いちばん見劣りする評価の項目（目立たなければ ''）
  const weak = () => { const w = ['myKing', 'theirKing', 'act'].sort((p, q) => dAsp[p] - dAsp[q])[0]; return dAsp[w] > -40 ? '' : w; };
  const wA = matWords(L), loss = wA.net - matWords(X.La).net, dAsp = aspectDiff(X.La.parts, L.parts);
  const s1 = steps[1] && steps[1].I;
  // すぐに詰まされる
  if ((isMate(a.c.s) && a.c.s < 0) || L.mated === side) return at(1, 'mate', { line: k.slice(1, 6).join(''), cnt: Math.min(5, k.length - 1), more: k.length > 6 });
  if (a.omK && a.omK.length) return at(1, 'mate', { line: a.omK.slice(0, 5).join(''), cnt: Math.min(5, a.omK.length), more: a.omK.length > 5, n: a.omK.length, K: a.omK[0] });
  // ほとんど差がない手には「問題」は言わない
  if (a.dv < 30) return at(Math.min(3, L.moves.length - 1), 'close', { asp: dAsp });
  // 選んだ手で取る駒（相手の狙いを持った駒や、取り返すべき駒）を、取らないまま残してしまう
  const Mc = X.Mi.cap, takesThreat = !!(X.rt && X.rt.real && mFrom(X.rt.T) === X.Mi.to);
  if (Mc && (takesThreat || (EXV[Mc] >= 300 && (X.Mi.see >= 0 || X.Mi.recapture))) && a.dv >= (takesThreat ? 80 : 150)
    && !(a.I.cap && EXV[a.I.cap] * 2 >= EXV[Mc]) && !L.got.some(x => x.s === X.Mi.to && x.ply <= 2)) return at(1, 'noTake');
  // もともとあった相手の狙いが、そのまま決まる
  if (X.rt && X.rt.real && L.moves[1] === X.rt.T && a.dv >= 80) return at(1, 'threatLeft');
  // 両取り（王手〇取り）をかけられて、駒を取られる
  for (const st of steps) {
    if (!st.I || st.i > 5) continue;
    const big = st.I.threats.filter(t => t.t !== FU && t.g >= 300 && st.I.hits.some(h => h.s === t.s));
    const won = L.lost.find(x => x.ply > st.i && big.some(t => t.s === x.s));
    if (won && (big.length >= 2 || st.I.check)) return at(st.i, 'fork', { big, check: st.I.check && big.length < 2 });
  }
  // 動かした駒がただで取られる／その駒が守っていた駒を取られる
  if (loss <= -150) for (const e of a.I.exposed) {
    if (e.s === a.I.to && a.I.cap) continue;   // 取る手は、下の「割に合わない交換」で見る
    const cap = L.lost.find(x => x.s === e.s && x.ply >= 1 && x.ply <= 3);
    if (cap) return at(cap.ply, e.s === a.I.to ? 'loose' : 'exposed', { piece: e });
  }
  // 取っても割に合わない交換
  if (a.I.cap && a.I.see <= -150 && mTo(L.moves[1]) === a.I.to && mCap(L.moves[1])) return at(1, 'badTrade');
  // 読み筋の先で駒を損する（歩一枚だけの損は、成り駒を作られる方を先に言う）
  let mc = null;
  if (loss <= -150 && wA.l.length) {
    // 歩一枚の損は、すぐに取られるか、その手で動かした（打った）歩が取られるときだけ理由にする
    // 選んだ手の読み筋でも同じように渡す駒は、理由にならない
    const extra = wA.l.slice();
    for (const t of matWords(X.La).l) { const j = extra.indexOf(t); if (j >= 0) extra.splice(j, 1); }
    const t = extra.sort((p, q) => HV[q] - HV[p])[0];
    mc = t && unpairedLost(L, t, L.horizon).find(x => x.ply >= 1 && x.ply <= (t !== FU || x.s === a.I.to ? 7 : 3));
    if (mc && t !== FU) return at(mc.ply, 'material', { piece: mc });
  }
  // 成り駒を作られる
  const pr = L.promos.find(p => !p.mine && p.kept && p.ply <= 6 && (p.t === RY || p.t === UM || cheb(p.s, X.P.kingSq[side]) <= 3));
  if (pr && a.dv >= 60 && !X.La.promos.some(q => !q.mine && q.kept && q.t === pr.t)) return at(pr.ply, 'promo', { promo: pr });
  if (mc) return at(mc.ply, 'material', { piece: mc });
  // 相手の応手に厳しい狙いがある（選んだ手でも同じ応手が来るなら、理由にはならない）
  const sameReply = [X.L, X.La].some(l => l.moves[1] && E.moveToUSI(l.moves[1]) === E.moveToUSI(L.moves[1]));
  // （その狙いの駒を次にこちらが取れるなら、狙いとは言わない：▲同歩と取るだけの歩など）
  const takesIt = a.tr && L.moves[2] && mCap(L.moves[2]) && mTo(L.moves[2]) === (mFrom(a.tr.T) || mTo(L.moves[1]));
  if (a.tr && a.tr.real && a.dv >= 60 && !sameReply && !takesIt) return at(1, 'replyThreat', { tr: a.tr });
  // 出た駒を追い返される（手損）
  if (s1 && a.dv >= 30 && s1.threats.some(t => t.s === a.I.to) && L.moves[2] && mFrom(L.moves[2]) === a.I.to) return at(1, 'pushedBack', { back: k[2] });
  // 序盤の手損：自分から交換して相手に取り返される、同じ駒を二度動かす
  if (X.opening && a.dv >= 30) {
    const R1 = L.moves[1];
    if (a.I.cap && !a.I.recapture && mTo(R1) === a.I.to && mCap(R1) && DEMOTE[mCap(R1) & 15] === DEMOTE[a.I.cap] && !(X.tempo && X.tempo.kind === 'give')) {
      const g = tempoGain(X.P, [a.A, R1], side);
      if (g <= -1) return at(1, 'tempoTrade', { n: -g, t: DEMOTE[a.I.cap] });
    }
    const wa = wasted(X.P, L, 4);   // その手で動かした駒を、すぐにまた動かすことになる
    if (wa && wa.first === 0 && !wasted(X.P, X.La, 4) && !L.moves.slice(0, wa.ply + 1).some(m => mCap(m))) return at(wa.ply, 'tempo', { piece: wa });
  }
  // 王手で追われる／玉が薄くなる
  const checks = L.checks.filter(c => !c.mine && c.ply <= 6);
  if (a.dv >= 60 && (checks.length >= 2 || (checks.length && dAsp.myKing <= -150))) return at(checks[0].ply, 'kingRun');
  if (a.dv >= 60 && dAsp.myKing <= -Math.max(120, a.dv * 0.5)) return at(Math.min(3, L.moves.length - 1), 'kingThin');
  // 受けられて攻めが続かない
  if (a.dv >= 60 && s1 && dAsp.theirKing <= -Math.max(100, a.dv * 0.5) && (s1.saved.length || s1.fled || s1.blocks.length)) return at(1, 'stall');
  // 反撃される
  const ct = s1 && s1.threats.find(t => t.t !== FU && t.g >= 300);
  if (ct && a.dv >= 60 && !sameReply) return at(1, 'counter', { target: ct });
  return at(Math.min(3, L.moves.length - 1), 'generic');
}
const SHARP = new Set(['mate', 'threatLeft', 'fork', 'noTake', 'tempoTrade', 'loose', 'exposed', 'badTrade', 'material', 'promo', 'replyThreat', 'pushedBack', 'kingRun', 'counter']);

// 理由を名詞句で（「△５五角の両取り」「△同銀と取り返されて損をする筋」など）。ほかの文に埋め込むとき用
function problemNoun(X, r) {
  const pre = r.pre ? `${r.pre}からの` : '';
  switch (r.kind) {
    case 'mate': return `${r.K}からの詰み筋`;
    case 'threatLeft': return `${X.rt.k}を防げない弱点`;
    case 'fork': return r.check ? `${pre}${r.K}の王手${NAME[r.big[0].t]}取り` : `${pre}${r.K}の両取り`;
    case 'noTake': return `${sqName(X.Mi.to)}の${NAME[X.Mi.cap]}を${X.Mi.recapture ? '取り返せない' : '取れない'}`;
    case 'loose': return `${r.key === 1 ? r.K : r.seq}でただ取られてしまう筋`;
    case 'exposed': return `${r.seq}で${NAME[r.piece.t]}を取られる筋`;
    case 'badTrade': return `${r.K}と取り返されて損をする筋`;
    case 'material': return `${r.seq}で${NAME[r.piece.board]}を取られる筋`;
    case 'promo': return `${r.seq}で${NAME[r.promo.t]}を作られる筋`;
    case 'replyThreat': return r.tr.mate ? `${r.K}が詰めろになる筋` : `${r.K}のあと、${threatVerb(r.tr)[0]}狙い`;
    case 'pushedBack': return `${r.K}で追い返される筋`;
    case 'kingRun': return `${r.Ks}からの王手攻め`;
    case 'counter': return `${r.K}の反撃`;
    default: return '';
  }
}
// 選んだ手の方が良い点（ほとんど差がないときに言えること）
function meritOf(X, a) {
  if (!a.L) return '';
  const d = aspectDiff(a.L.parts, X.La.parts), k = ['myKing', 'theirKing', 'act'].sort((p, q) => d[q] - d[p])[0];
  if (d[k] < 60 || a.nat.asp === k) return '';
  return { myKing: '玉の守りを崩さずに済む', theirKing: '攻めを続けやすい', act: '駒がよく働く' }[k];
}

// 「▲Aと指すと△Bがあって、〜になるので避けた」という形で、選ばなかった理由を書く
function whyNot(X, a, nth) {
  let r = a.ref;
  if (!r) return '';
  // 手損の話は一つの解説で一度まで（二つ目からはふつうの言い方で）
  if (['tempo', 'tempoTrade', 'pushedBack'].includes(r.kind)) { if (X.used.has('tempoWhy')) r = Object.assign({}, r, { kind: 'generic' }); else X.used.add('tempoWhy'); }
  const A = a.k, M = X.Mk, K = r.K;
  const lead = nth === 0 ? '' : X.say('alt.conj', ['また、', '一方、', 'ほかに、', 'それから、', '']);
  const cond = X.say('why.if', [`${A}と指すと`, `${A}だと`, `もし${A}なら`]);
  const noun = problemNoun(X, r);
  // 一見よさそうな手
  if (a.tempting && noun && !X.used.has('tempt')) {
    X.used.add('tempt');
    const lure = a.I.cap ? `で${NAME[a.I.cap]}が取れそう` : a.I.check ? 'の王手が厳しそう' : a.I.promo ? 'と成るのが自然' : 'が良さそう';
    return X.say('why.tempt', [
      `${lead === '一方、' ? '' : lead}一見${A}${lure}ですが、${noun}があるので指せません。`,
      `${lead}${A}${lure}に見えますが、${noun}があって、うまくいきません。`,
    ]);
  }
  // 途中まで本命だった手
  if (X.mind && X.mind.m === a.c.m && !X.used.has('mind') && mindWorth(X, a)) {
    X.used.add('mind'); X.memo.mark('mind');
    const since = sinceWhen(X), when = switchWhen(X);
    if (noun) return lead + X.say('why.was', [
      `${since}${A}を本命と見ていましたが、${when}${noun}が見つかったので、${M}に切り替えました。`,
      `途中までは${A}が最善に見えていましたが、さらに読んで${noun}に気づき、取りやめました。`,
    ]);
    if (r.kind === 'close') return lead + X.say('why.was0', [
      `${since}${A}が最善でしたが、${when}${M}とほぼ並び、最後は${M}の方をわずかに上と見ました。`,
      `${A}は途中まで本命でしたが、${when}${M}が追いつき、最後に逆転しました。`,
    ]);
  }
  const nm = (t) => NAME[t];
  switch (r.kind) {
    case 'mate': return lead + X.say('why.mate', [
      `${cond}、${r.line}${r.more ? '…' : ''}と迫られて、こちらの玉が詰んでしまうので、${A}は指せません。`,
      `${A}には${K}からの詰み筋があります${r.cnt >= 3 ? `（${r.line}${r.more ? '…' : ''}）` : ''}。これがあるので${A}は選べません。`,
      `${A}だと${K}以下${r.n ? r.n + '手で' : ''}玉が詰まされてしまうので、避けました。`,
    ]);
    case 'threatLeft': {
      const T = X.rt, th = T.I.threats.find(x => x.t !== FU), tp = T.L.promos.find(x => x.mine && x.kept && x.ply === 0);
      const hurt = tp ? `${NAME[tp.t]}を作られて` : T.I.cap && T.I.cap !== FU ? `${nm(T.I.cap)}を取られて` : th ? `${nm(th.t)}を狙われて` : T.cap && T.cap.t !== FU ? `${capName(T.L, T.cap)}を取られて` : '攻め込まれて';
      return lead + X.say('why.left', [
        `${A}では、あなたが狙っていた${T.k}を止められず、${hurt}しまいます。`,
        `${A}は${T.k}の狙いを放っておく手なので、${hurt}しまいます。だから選べません。`,
      ]);
    }
    case 'fork': {
      const pre = r.pre ? `${r.pre}のあと、` : '', b = r.big;
      if (r.check) return lead + X.say('why.forkChk', [
        `${cond}、${pre}${K}と${r.pv}王手${nm(b[0].t)}取りがかかります。王手を受けている間に${nm(b[0].t)}を取られるので、${A}は避けました。`,
        `${A}だと、${pre}${K}の王手で${sqName(b[0].s)}の${nm(b[0].t)}まで狙われてしまいます。これを嫌って${A}は見送りました。`,
      ]);
      const pair = b[0].t === b[1].t ? `二枚の${nm(b[0].t)}` : `${nm(b[0].t)}と${nm(b[1].t)}`;
      return lead + X.say('why.fork', [
        `${cond}、${pre}${K}と${r.pv}${pair}の両取りになります。どちらかは助からないので、${A}は避けました。`,
        `${A}だと、${pre}${K}が${pair}の両取りになってしまいます。これを嫌って${A}は見送りました。`,
      ]);
    }
    case 'exposed': {
      const e = r.piece;
      return lead + X.say('why.exposed', [
        `${A}と${a.v[0]}と${sqName(e.s)}の${nm(e.t)}の守りがいなくなり、${r.seq}と取られてしまうので、${A}は避けました。`,
        `${A}では${nm(e.t)}に紐がつかない形になって、${r.Ks}で取られてしまいます。だから${A}は選びませんでした。`,
      ]);
    }
    case 'noTake': {
      const sq = sqName(X.Mi.to), c = nm(X.Mi.cap), back = X.Mi.recapture ? '取り返せず' : '取れず';
      return lead + X.say('why.notake', [
        `${A}では${sq}の${c}を${back}、${K}と${r.pv}しまいます。`,
        `${A}だと${sq}の${c}が残ったままになり、${K}と攻めを続けられてしまうので、${A}は選びませんでした。`,
      ]);
    }
    case 'loose': return lead + X.say('why.loose', [
      `${A}と${a.v[1]}も、${r.key === 1 ? K : r.seq}と取られるだけで、${nm(a.I.nt)}をただで渡すことになります。`,
      r.key === 1 ? `${A}は${K}で取られてしまう手なので、指せません。` : `${A}は${r.seq}と進むと${nm(a.I.nt)}を取られてしまう手なので、指せません。`,
    ]);
    case 'badTrade': return lead + X.say('why.trade', [
      `${A}で${nm(a.I.cap)}を取っても、${K}と取り返されて${nm(a.I.nt)}を損するので、割に合いません。`,
      `${A}と${nm(a.I.cap)}を取るのは、${K}と取り返されると${nm(a.I.nt)}を渡すだけの交換になります。`,
    ]);
    case 'material': {
      const p = nm(r.piece.board);
      return lead + X.say('why.mat', [
        r.key === 1 ? `${cond}、${K}で${p}を取られてしまうので、${A}は避けました。` : `${cond}、${r.seq}と進んで${p}を取られてしまうので、${A}は避けました。`,
        `${A}には${r.key === 1 ? K + 'があり' : r.seq + 'という手順があり'}、${p}を取られて駒損になります。`,
      ]);
    }
    case 'promo': return lead + X.say('why.promo', [
      `${A}だと${r.seq}と${r.promo.t === RY || r.promo.t === UM ? '成り込まれて' : '成られて'}、${nm(r.promo.t)}ができてしまいます。`,
      `${cond}、${r.seq}で${nm(r.promo.t)}を作られてしまうので、見送りました。`,
    ]);
    case 'replyThreat': {
      const T = r.tr;
      if (T.mate) return lead + X.say('why.replyMate', [
        `${A}だと${K}と${r.pv}、次に${T.k}${T.mate > 1 ? `からの${T.mate}手詰め` : 'の一手詰め'}を狙われます。受けに手を取られるので、${A}は避けました。`,
        `${A}だと${K}が詰めろになっていて、次に${T.k}以下で詰まされてしまいます。だから${A}は選べません。`,
      ]);
      return lead + X.say('why.reply', [
        `${A}だと${K}と${r.pv}、次に${threatNoun(T)}を狙われます。その受けに手を取られるので、${A}は見送りました。`,
        `${A}には${K}という手があり、${threatNoun(T)}が見えています。これを防ぐのに手番を使わされるので、${A}は避けました。`,
      ]);
    }
    case 'tempoTrade': return lead + X.say('why.tempoTrade', [
      `${A}と自分から${nm(r.t)}を交換すると、${K}と取り返されて${tempoWord(r.n, false)}になります。`,
      `${cond}、${K}と取り返されたところで、手数の上で${tempoWord(r.n, false)}になるので、${A}は見送りました。`,
    ]);
    case 'tempo': {
      const pc = r.piece;
      return lead + X.say(pc.back ? 'why.tempoBack' : 'why.tempo2', pc.back ? [
        `${A}だと${r.seq}と進んで、${nm(pc.t)}が元の位置に戻ることになります。その分の手損になるので、${A}は見送りました。`,
        `${A}は、${r.seq}で${nm(pc.t)}が元に戻る手順になるので、手損です。`,
      ] : [
        `${A}は${r.seq}と、${nm(pc.t)}を二度動かすことになるので、手損になります。`,
        `${cond}、${r.seq}と${nm(pc.t)}をもう一度動かすことになり、その分の手損が気になりました。`,
      ]);
    }
    case 'pushedBack': return lead + X.say('why.back', [
      `${A}と${a.v[1]}も、${K}と${nm(a.I.nt)}に当てられて、${r.back}と引くしかありません。結局手損になるので、${A}は見送りました。`,
      `${A}は${K}で追い返されてしまうので、手損になるだけです。`,
    ]);
    case 'kingRun': return lead + X.say('why.king', [
      `${cond}、${r.key === 1 ? K : r.seq}から王手が続いて、こちらの玉が追い回されてしまうので、${A}は避けました。`,
      `${A}だと${r.seq}と王手で迫られて、玉の守りが崩れてしまいます。`,
    ]);
    case 'kingThin': return lead + X.say('why.thin', [
      `${A}だと${r.seq}と進んで、こちらの玉の守りが薄くなってしまうので、見送りました。`,
      `${A}は${r.seq}と進んだあと、玉の囲いが手薄になるのが気になりました。`,
    ]);
    case 'stall': return lead + X.say('why.stall', [
      `${A}と攻めても、${K}と受けられると次の攻めが続きません。`,
      `${A}には${K}という受けがあって、攻めが空振りに終わるので見送りました。`,
    ]);
    case 'counter': {
      const t = r.target;
      return lead + X.say('why.counter', [
        `${A}には${K}と反撃する手があり、${sqName(t.s)}の${nm(t.t)}に当たりがかかってしまいます。`,
        `${cond}、${K}と${r.pv}${nm(t.t)}を狙われるので、${A}は避けました。`,
      ]);
    }
    case 'close': {
      const merit = meritOf(X, a);
      X.used.add('close');
      return lead + X.say('why.close', [
        merit ? `${A}も有力で、${r.seq}と進んでも大きな差はありません。それでも${M}の方が${merit}と見て、こちらを選びました。` : null,
        merit ? `${A}（${a.nat.np}手）でも悪くありませんが、${M}の方が${merit}ので選びました。` : null,
        `${A}も十分に考えられる手で、ほとんど好みの差でした。`,
        `${A}（${a.nat.np}手）も同じくらい有力で、方針の違いと言える比較でした。`,
      ]);
    }
    default: {
      const w = r.w, then = r.rest ? `以下${r.rest}と進むと、` : '';
      if (!w) return lead + X.say('why.gen0', [
        `${A}には${r.R1}という応手があり、${then}${M}の変化より指しにくくなるので、選びませんでした。`,
        `${A}だと${r.seq}と進んで、${M}ほど良い形にはなりません。`,
      ]);
      return lead + X.say('why.gen.' + w, {
        myKing: [`${A}には${r.R1}という応手があり、${then}こちらの玉の囲いが薄くなります。`, `${A}だと${r.seq}と進んで、玉の守りが手薄になってしまいます。`],
        theirKing: [`${A}だと${r.R1}と応じられて、あなたの玉に迫る手がかりが少なくなります。`, `${A}は${r.seq}と進むと、攻めの形が作りにくくなります。`],
        act: [`${A}は${r.seq}と進んだあと、駒がうまく働かない形になってしまいます。`, `${A}だと${r.R1}と応じられて、駒の働きが悪い形になります。`],
      }[w]);
    }
  }
}
// 選んだ手なら、その決め手が成立しない（いちばん近い候補についてだけ確かめる）
function avoids(X, a) {
  const r = a.ref;
  if (!r || r.key !== 1 || !a.L || !['fork', 'counter', 'replyThreat'].includes(r.kind)) return '';
  if (mTo(a.L.moves[1]) === a.I.to) return '';   // その手で動かした駒を取る応手は、選んだ手のあとでは比べようがない
  const pM = after(X.P, [X.M], 1), u = E.moveToUSI(a.L.moves[1]), K2 = pM.parseUSI(u), Kx = a.L.kabs[1];   // 選んだ手のあとなので「同」は使わない
  if (!K2) return X.say('avoid.none', [`${X.Mk}と指しておけば、${Kx}はそもそも指せません。`, `${X.Mk}なら、${Kx}の余地がありません。`]);
  const I2 = moveInfo(pM, K2, X.Mi.to, false, !!X.Mi.cap), big = I2.threats.filter(t => t.t !== FU && t.g >= 300);
  if (r.kind === 'fork' && !r.check && big.length < 2) return X.say('avoid.fork', [`${X.Mk}なら、${Kx}と${r.pv}も両取りになりません。`, `${X.Mk}と指しておけば、${Kx}の両取りは成立しません。`]);
  if (r.kind === 'counter' && !big.length) return X.say('avoid.counter', [`${X.Mk}なら、${Kx}と来られても怖くありません。`]);
  return '';
}

// 本命が入れ替わったのが読みのどのあたりか（深さの数字は出さず、時間の感覚で言う）
function switchWhen(X) {
  const D = X.main.depth || 0, ds = X.mind.ds;
  if (D && ds > D) return '思考を終える直前に';
  if (D && ds === D) return '思考を終える少し前に';
  if (D && ds === D - 1) return '読みの後半で';
  if (ds <= Math.max(5, D / 2)) return '読み始めてまもなく';
  return '読み進めるうちに';
}
const sinceWhen = (X) => (X.mind.d1 <= 3 ? '最初は' : '途中までは');
function mindWorth(X, a) { return X.mind.d2 >= 6 && (X.memo.ago('mind') >= 3 || X.mind.ds >= 12 || (a && a.dv >= 100)); }

function pickAlts(X) {
  // 直前の解説で、同じ手を同じ理由で説明したばかりなら、ほかの手を優先する（毎回同じ話にならないように）
  const recent = (a) => X.memo.ago('why:' + a.ref.kind + ':' + a.c.m) < 4;
  let alts = X.alts.filter(a => a.ref && !(X.twin(a) && a.dv < 100)), out = [];
  if (alts.some(a => !recent(a))) alts = alts.filter(a => !recent(a));
  const same = (a, b) => mFrom(a.A) === mFrom(b.A) && mTo(a.A) === mTo(b.A) && (mPiece(a.A) & 15) === (mPiece(b.A) & 15);
  const add = (a) => { if (a && out.length < 3 && !out.some(b => b === a || same(a, b))) out.push(a); };
  add(alts[0]);                                          // いちばん近かった手
  add(alts.find(a => a.tempting));                       // 一見よさそうな手
  add(X.mind && alts.find(a => a.c.m === X.mind.m && mindWorth(X, a)));     // 途中まで本命だった手
  for (const a of alts) if (SHARP.has(a.ref.kind)) add(a);   // 選ばなかった理由がはっきりしている手
  if (out.length < 2) add(alts[1]);
  return out;
}

// ---------------------------------------------------------------- 読みの経過・形勢のひとこと
function metaSentence(X, top) {
  if (X.mind && !X.used.has('mind') && X.mind.ds > 5 && mindWorth(X, X.alts.find(a => a.c.m === X.mind.m))) {
    X.used.add('mind'); X.memo.mark('mind');
    const since = sinceWhen(X), when = switchWhen(X);
    return X.say('meta.mind', [
      `${since}${X.mind.k}を本命と見ていましたが、${when}${X.Mk}が上回りました。`,
      since === '最初は' ? `読み始めは${X.mind.k}が最善に見えていました。読み進めるうちに順番が入れ替わり、最後は${X.Mk}を選んでいます。` : null,
      `一度は${X.mind.k}に傾きましたが、${when}考えを改めました。`,
    ]);
  }
  if (top && top.dv >= 300 && !isMate(top.c.s)) return X.say('meta.clear', [
    `有力に見えたほかの手には、どれもはっきりした問題がありました。ここは${X.Mk}の一手です。`,
    `ほかの候補ではどれもうまくいかないので、迷う余地の少ない局面でした。`,
  ]);
  if (X.stable && X.stable <= 4 && top && top.dv >= 50) return X.say('meta.stable', [
    `読み始めから最後まで、${X.Mk}が最善のまま変わりませんでした。`,
    `読みの初めから終わりまで、本命は一貫して${X.Mk}でした。`,
  ]);
  const st = standNow(X);
  if (st) return X.say('meta.stand', [`指したあとの形勢は、千里眼から見て${st}。`, `この手で、千里眼から見て${st}。`]);
  return '';
}

// 「▲６二とと取る」「△同銀とと金を取る」のような、と が重なる言い方を直す
function polish(t) {
  return t.replace(/([▲△][^、。▲△（）]*?と)と(?=[取指寄上引逃打成突跳出回応受反攻迫追])/g, '$1で').replace(/([▲△][^、。▲△（）]*?[^と])とと金/g, '$1でと金')
    .replace(/([▲△][^、。▲△（）]*?と)(?=という|と[進続])/g, '$1、');
}

// 手得・手損のひとこと（序盤の駒の交換、相手の駒を引かせる手）
function tempoSentence(X, book) {
  const T = X.tempo;
  if (!T) return '';
  if (T.kind === 'give') return book
    ? X.say('tempo.giveBook', [`自分から${NAME[T.t]}を交換する分、手数の上では${tempoWord(T.n, false)}になりますが、定跡でも指される形です。`])
    : X.say('tempo.give', [
      `自分から${NAME[T.t]}を交換するので、手数の上では${tempoWord(T.n, false)}になりますが、それでも${SHORT[T.t]}を持ち合う形の方が良いと見ました。`,
      `先に取る側なので${tempoWord(T.n, false)}になりますが、ここは交換して局面を動かす方を選びました。`,
    ]);
  if (T.kind === 'get') return X.say('tempo.get', [
    `あなたから${NAME[T.t]}を交換してきたので、手数の上ではこちらが${tempoWord(T.n, true)}です。`,
    `交換を先に仕掛けたのはあなたなので、ここでこちらが${tempoWord(T.n, true)}になります。`,
  ]);
  return X.say('tempo.chase', [`${NAME[T.R.t]}を引かせる分、こちらの手得になります。`, `相手の${NAME[T.R.t]}が下がる分だけ、手得を稼げます。`]);
}

// 主な理由とは別に、この手が相手の狙いをどうやって消しているか（「銀が４五から動いたので、〜もなくなりました」など）。
// どう消しているのかをはっきり言えないときは何も言わない
function alsoStops(X) {
  const T = X.rt, I = X.Mi, how = X.rtHandled, d = threatNoun(T), nm = NAME[I.t];
  if (how === 'moved') return X.say('also.moved', [
    `${nm}が${sqName(I.from)}から動いたので、あなたの${d}もなくなりました。`,
    `あなたの${d}も、${nm}を動かしたことでかわしています。`,
  ]);
  const blk = how === 'blocked' && I.blocks.find(b => b.s === mFrom(T.T));
  if (blk) return X.say('also.blocked', [
    `${X.Mk}で${NAME[blk.t]}の利きが止まったので、あなたの${d}もなくなりました。`,
    `あなたの${d}も、${NAME[blk.t]}の利きを止めたことで防いでいます。`,
  ]);
  if (how === 'guarded' && T.cap) return X.say('also.guarded', [
    `${sqName(T.cap.s)}の${NAME[T.cap.board]}に紐がついたので、あなたの${d}も怖くなくなりました。`,
    `あなたの${d}も、${NAME[T.cap.board]}に紐をつけたことで防いでいます。`,
  ]);
  if (how === 'other' && X.attacking) return X.mt && X.mt.real
    ? X.say('also.faster', [`あなたの${d}より、こちらの${X.used.has('mtTold') || ['threat', 'mateThreat', 'promote'].includes(X.purpose) ? '狙い' : threatNoun(X.mt)}の方が先です。`, `先にこちらが攻めるので、あなたに${d}を指す暇はありません。`])
    : I.check ? `王手で先に攻めるので、あなたに${d}を指す暇はありません。` : '';
  return '';
}

// ---------------------------------------------------------------- 組み立て
function build(inp, memo) {
  memo = memo || MEMO;
  memo.builds++;
  const X = context(inp, memo);
  if (!X) return null;
  const purpose = purposeOf(X);
  X.purpose = purpose;
  const lead = LEAD[purpose](X);
  X.leadText = lead;
  if (purpose === 'book') return { head: X.Mk, kind: purpose, paras: [polish(lead + tempoSentence(X, true))], rows: [], foot: '' };
  if (purpose === 'mate') return { head: X.Mk, kind: purpose, paras: [polish(lead)], rows: [], foot: X.main.dfpn ? '詰み探索（df-pn）で読み切った手順です。' : '' };
  const p1 = [lead];
  // 主な理由とは別に、この手の狙いや受けにも触れる
  if (!['threat', 'mateThreat', 'promote', 'fork'].includes(purpose) && X.mt && X.mt.real && !X.mt.mate && X.mt.gain >= 300 && !(purpose === 'pawnStrike' && mFrom(X.mt.T) === X.Mi.to))
    { p1.push(X.say('also.threat', [`さらに次は${threatNoun(X.mt)}も狙えます。`, `次に${threatNoun(X.mt)}が控えています。`])); X.used.add('mtTold'); }
  if (!['defend', 'defendMate'].includes(purpose) && X.rt && X.rt.real && X.rtHandled && X.rtHandled !== 'took' && !X.rt.mate && X.rt.gain >= 300)
    p1.push(alsoStops(X));
  else if (X.attacking && X.Mi.fled >= 300 && purpose !== 'escape')   // 当たりの駒を、攻めながらかわす
    p1.push(X.say('also.dodge', [`当たりのかかっていた${NAME[X.Mi.t]}を、攻めに使いながらかわしています。`, `取られそうだった${NAME[X.Mi.t]}をかわす意味もあります。`]));
  if (X.rt && X.rt.real && !X.rtHandled && !X.rt.mate && X.mt && X.mt.real && X.score >= -100 && !['defend', 'defendMate'].includes(purpose))
    p1.push(X.say('race', [`あなたの${threatNoun(X.rt)}も残っていますが、こちらの攻めの方が一手早いと見ています。`, `あなたの${threatNoun(X.rt)}は承知の上で、先に攻める方を選びました。`]));
  if (X.tempo && X.tempo.kind !== 'chase') p1.push(tempoSentence(X));
  if (purpose !== 'forced' && purpose !== 'pawnTrade') p1.push(lineSentence(X));
  if (X.tempo && X.tempo.kind === 'chase') p1.push(tempoSentence(X));
  const top = X.alts.find(a => !X.twin(a)), paras = [];
  for (const a of X.alts) a.ref = refutation(X, a);
  // 有力な手が並んでいる局面
  const even = X.alts.filter(a => a.dv < 20 && !isMate(a.c.s) && !X.twin(a));
  let alts = pickAlts(X);
  if (even.length >= 2 && memo.ago('many') >= 3) {
    memo.mark('many'); X.used.add('close');
    p1.unshift(X.say('many', [
      `有力な手は${even.slice(0, 2).map(a => a.k).join('や')}など複数あり、どれも甲乙つけがたいところでした。`,
      `${X.Mk}のほか、${even.slice(0, 2).map(a => a.k).join('・')}もほぼ同点で、どれを選んでもおかしくありません。`,
      `${even.slice(0, 2).map(a => a.k).join('・')}も同じくらい有力で、選択肢の多い場面でした。`,
    ]));
    alts = alts.filter(a => even.indexOf(a) < 0);
  } else if (top && top.dv < 15 && memo.ago('closeOpen') >= 3 && purpose === 'plan') {
    memo.mark('closeOpen'); X.used.add('close');
    p1.unshift(X.say('close.open', [
      `${X.Mk}と${top.k}で最後まで迷いました。`,
      `候補は${X.Mk}と${top.k}の二つに絞られ、その差はごくわずかでした。`,
    ]));
    alts = alts.filter(a => a !== top);
  }
  paras.push(p1.join(''));
  // 同じ理由で選ばなかった手は一文にまとめる（ほぼ互角の手は、選んだ手の良い点が同じものどうし）
  const groups = [];
  for (const a of alts) {
    const r = a.ref, special = (a.tempting && problemNoun(X, r)) || (X.mind && X.mind.m === a.c.m && mindWorth(X, a));
    const n = r && (special ? problemNoun(X, r) : r.kind === 'close' ? 'close:' + meritOf(X, a) : r.kind === 'generic' ? 'gen:' + r.w
      : r.kind === 'badTrade' ? `bad:${a.I.cap}:${a.I.nt}` : problemNoun(X, r));
    const g = n && groups.find(x => x.noun === n);
    if (g) g.alts.push(a); else groups.push({ noun: n, alts: [a] });
  }
  for (const g of groups) for (const a of g.alts) memo.mark('why:' + a.ref.kind + ':' + a.c.m);
  const p2 = groups.map((g, i) => {
    if (g.alts.length === 1) return whyNot(X, g.alts[0], i) + (i === 0 ? avoids(X, g.alts[0]) : '');
    const names = g.alts.map(a => a.k).join(g.alts.length <= 2 ? 'や' : '・');
    const conj = i ? X.say('alt.conj', ['また、', '一方、', 'ほかに、', 'それから、', '']) : '';
    if (g.noun.startsWith('gen:')) return conj + X.say('why.groupGen.' + g.noun.slice(4), {
      myKing: [`${names}は、どれも${X.Mk}と比べて玉の守りが手薄になる展開でした。`, `${names}では、いずれも玉の囲いが薄くなる変化になるので選びませんでした。`],
      theirKing: [`${names}は、どれも${X.Mk}と比べて攻めの手がかりをつかみにくい展開でした。`, `${names}では、いずれも攻めの形が作りにくくなります。`],
      act: [`${names}は、どれも${X.Mk}と比べて駒の働きが悪くなる展開でした。`, `${names}では、いずれも駒がうまく働かない形になります。`],
      '': [`${names}は、どれも${X.Mk}の変化ほど良い形になりませんでした。`, `${names}では、いずれも${X.Mk}より指しにくくなります。`],
    }[g.noun.slice(4)]);
    if (g.noun.startsWith('bad:')) {
      const a0 = g.alts[0];
      return conj + X.say('why.groupBad', [
        `${names}で${NAME[a0.I.cap]}を取っても、取り返されて${NAME[a0.I.nt]}を損するので、どれも割に合いません。`,
        `${names}と${NAME[a0.I.cap]}を取るのは、どれも取り返されると${NAME[a0.I.nt]}を渡すだけの交換になります。`,
      ]);
    }
    if (g.alts[0].ref.kind === 'threatLeft') return conj + X.say('why.groupLeft', [
      `${names}では、あなたの${threatNoun(X.rt)}を防げないので、選べませんでした。`,
      `${names}は、どれもあなたの${threatNoun(X.rt)}を受けていない手なので見送りました。`,
    ]);
    if (g.alts[0].ref.kind === 'noTake') {
      const sq = sqName(X.Mi.to), c = NAME[X.Mi.cap], v = X.Mi.recapture ? '取り返せない' : '取れない';
      return conj + X.say('why.groupNoTake', [`${names}では${sq}の${c}を${v}ので、選べませんでした。`, `${names}は、どれも${sq}の${c}を${v}手なので見送りました。`]);
    }
    if (g.noun.startsWith('close:')) {
      const merit = g.noun.slice(6);
      X.used.add('close');
      return conj + X.say(merit ? 'why.groupClose' : 'why.groupEven', merit ? [
        `${names}も有力でしたが、${X.Mk}の方が${merit}と見て、こちらを選びました。`,
        `${names}でも悪くありませんが、${X.Mk}の方が${merit}ので選びました。`,
      ] : [
        `${names}も同じくらい有力で、ほとんど好みの差でした。`,
        `${names}も十分に考えられる手で、方針の違いと言える比較でした。`,
      ]);
    }
    return conj + X.say('why.group', [
      `${names}では、どれも${g.noun}があるので避けました。`,
      `${names}は、いずれも${g.noun}が残ってしまいます。`,
    ]);
  }).join('');
  if (p2) paras.push(p2);
  else if (X.d && X.d.partial && !X.d.depth) paras.push('ほかの候補との読み比べは、次の読みが始まったため途中で切り上げました。');
  if (purpose !== 'forced') { const m = metaSentence(X, top); if (m) paras.push(m); }
  return { head: X.Mk, kind: purpose, paras: paras.filter(Boolean).map(polish), rows: tableRows(X), foot: footNote(X) };
}

function fmtEv(v) {
  if (v >= MATE_IN_MAX) return '詰み';
  if (v <= -MATE_IN_MAX) return '詰まされる';
  const r = Math.round(v);
  return (r > 0 ? '+' : r < 0 ? '−' : '±') + Math.abs(r);
}
function tableRows(X) {
  if (!X.alts.length) return [];
  const rows = [{ k: X.Mk, ev: fmtEv(X.score), line: X.L.kifs.slice(1, 4).join(''), chosen: true }];
  for (const a of X.alts.slice(0, 4)) rows.push({ k: a.k, ev: fmtEv(a.ev), line: a.L ? a.L.kifs.slice(1, 4).join('') : '', chosen: false });
  return rows;
}
function footNote(X) {
  const d = X.d;
  if (!d || !d.depth) return '';
  return `候補${d.cands.length}手を、それぞれ${d.depth}手先まで読み比べた結果です。評価値は千里眼から見た値です。`;
}

const api = { build, Memo };
if (typeof module !== 'undefined' && module.exports) module.exports = api;
else root.SenriganExplain = api;
})(typeof self !== 'undefined' ? self : this);
