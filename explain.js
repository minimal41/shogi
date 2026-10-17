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
const pts = (v) => (v >= 1000 ? `${Math.floor(v / 100) * 100}点以上` : `${Math.max(10, Math.round(v / 10) * 10)}点ほど`);
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

// 指し手そのものの観察（pos はその手を指す前の局面）。light なら駒の当たりなどは調べない
function moveInfo(pos, m, prevTo, light) {
  const us = pos.stm, them = us ^ 1, from = mFrom(m), to = mTo(m), t = mPiece(m) & 15, cap = mCap(m) & 15;
  const I = { m, us, from, to, t, nt: mIsPromo(m) ? t + 8 : t, cap, promo: mIsPromo(m), drop: from === 0,
    check: pos.givesCheck(m), see: E.seeMove(pos, m), recapture: cap !== 0 && to === prevTo, k: kifOf(pos, m, prevTo),
    threats: [], saved: [], fled: 0, hits: [], opened: [], closed: [], blocks: [], castle: '',
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
const ASPECT = { myKing: '玉の守り', theirKing: '攻め', act: '駒の働き', threat: '駒の当たり', mat: '駒の損得' };

// 読み筋をたどる：駒の取り合い（side から見た得失）、成り、王手、詰み
function walk(P, usis, side, prevTo) {
  const p = P.clone(), mat0 = matOf(p, side);
  const L = { moves: [], kifs: [], got: [], lost: [], promos: [], checks: [], mated: -1, build: 0 };
  let prev = prevTo;
  for (const u of usis) {
    const m = p.parseUSI(u);
    if (!m) break;
    const mover = p.stm, c = mCap(m) & 15, ply = L.moves.length, t = mPiece(m) & 15;
    L.kifs.push(kifOf(p, m, prev));
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
  return L;
}

// 駒の得失：同じ種類どうしは交換として相殺し、残りを得た駒・渡した駒に
function matWords(L, upto) {
  const lim = upto == null ? L.horizon : upto;
  const g = L.got.filter(x => x.ply <= lim).map(x => x.t), l = L.lost.filter(x => x.ply <= lim).map(x => x.t), traded = [];
  for (let i = g.length - 1; i >= 0; i--) { const j = l.indexOf(g[i]); if (j >= 0) { traded.push(g[i]); g.splice(i, 1); l.splice(j, 1); } }
  const vg = g.reduce((a, t) => a + HV[t], 0), vl = l.reduce((a, t) => a + HV[t], 0);
  return { g, l, traded, net: vg - vl };
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

// 相手（または自分）の「パスしたら指される手」：狙いの中身
function threatInfo(P, M, t, by) {
  const p = P.clone();
  if (M) p.doMove(M);
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
const V = {
  tsuku: ['突く', '突いて'], utsu: ['打つ', '打って'], toru: ['取る', '取って'], kaesu: ['取り返す', '取り返して'],
  naru: ['成る', '成って'], komu: ['成り込む', '成り込んで'], haneru: ['跳ねる', '跳ねて'], deru: ['出る', '出て'],
  agaru: ['上がる', '上がって'], hiku: ['引く', '引いて'], yoru: ['寄る', '寄って'], mawaru: ['回る', '回って'],
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
function natureOf(P, I, imm) {
  const side = I.us, t = I.t, f = FILE[I.to], ownK = P.kingSq[side], enK = P.kingSq[side ^ 1];
  const near = (k) => (f <= 3 && FILE[k] <= 4) || (f >= 7 && FILE[k] >= 6);
  const N = (np, goal, asp) => ({ np, goal, asp: asp || '' });
  // 決まった言い方がない手は、指した直後に評価のどこが良くなったかで言い分ける
  const top = imm ? ['myKing', 'theirKing', 'act'].sort((a, b) => imm[b] - imm[a])[0] : '';
  const by = (n) => {
    if (!imm || imm[top] < 50) return n;
    if (top === 'myKing') return t === OU ? N('玉を安全な位置に移す', '玉を安全な位置に移します。', top) : N(`${NAME[t]}で守りを固める`, '守りを固めます。', top);
    if (top === 'theirKing') return N('攻めの形を一歩進める', '攻めの形を一歩進めます。', top);
    return N(`${NAME[t]}の働きを良くする`, `${NAME[t]}の働きを良くします。`, top);
  };
  const ownHalf = side === BLACK ? RANK[I.to] >= 6 : RANK[I.to] <= 4;
  const blk = I.blocks.find(b => b.t !== KY) || I.blocks[0];
  if (blk && ownHalf) return N(`${NAME[t]}で${NAME[blk.t]}の利きを止める`, `${NAME[blk.t]}の利きを止めます。`, 'myKing');
  if (I.drop) {
    if (t === FU) {
      if (side === BLACK ? RANK[I.to] >= 7 : RANK[I.to] <= 3) return N('歩を打って守りの隙を埋める', '守りの隙を埋めます。', 'myKing');
      if (side === BLACK ? RANK[I.to] === 4 : RANK[I.to] === 6) return N('歩を打って次に成る含みを残す', '次に成る含みを残します。', 'theirKing');
      return N(`歩を打って${sqName(I.to)}を押さえる`, `${sqName(I.to)}を押さえます。`, 'act');
    }
    if (cheb(I.to, ownK) <= 2) return N(`${NAME[t]}を打って守りを固める`, '守りを固めます。', 'myKing');
    if (cheb(I.to, enK) <= 3) return N(`${NAME[t]}を打ち込んで攻めの拠点を作る`, '攻めの拠点を作ります。', 'theirKing');
    return by(N(`持ち駒の${NAME[t]}を${sqName(I.to)}に据える`, `${NAME[t]}の利きを盤上に加えます。`, 'act'));
  }
  if (t === FU) {
    if (I.closed.some(x => x.t === KA || x.t === UM)) return N('角道を止めてじっくり構える', '角道を止めて、じっくり構えます。');
    if (I.opened.some(x => x.t === KA || x.t === UM)) return N('角道を開けて角を働かせる', '角道を開けます。', 'act');
    if (f === 1 || f === 9) {
      if (near(ownK) && cheb(I.to, ownK) <= 4) return N('端歩を突いて玉の逃げ道を広げる', '玉の逃げ道を広げておきます。', 'myKing');
      if (near(enK)) return N('端歩を伸ばして端攻めの含みを作る', '端攻めの含みを残します。', 'theirKing');
      return N('端歩を突いて相手の出方をうかがう', '相手の出方をうかがいます。');
    }
    const rook = SQ81.find(s => P.board[s] === (HI | (side << 4)) && FILE[s] === f && ahead(side, s, I.to) > 0);
    if (rook) return N('飛車先の歩を伸ばす', '飛車先を伸ばしていきます。', 'act');
    if (RANK[I.to] === 5) return N(`${ZEN[f]}筋の位を取る`, `${ZEN[f]}筋の位を取ります。`, 'act');
    if (f === 5) return N('中央の歩を突いて駒の通り道を作る', '銀や角の通り道を作ります。', 'act');
    if (cheb(I.to, ownK) <= 2) return N('玉のそばの歩を突いて囲いの形を整える', '囲いの形を整えます。', 'myKing');
    return by(N(`${ZEN[f]}筋の歩を伸ばして戦いに備える`, '戦いに備えます。'));
  }
  if (GOLDISH.has(t)) {
    if (cheb(I.to, ownK) < cheb(I.from, ownK) && cheb(I.to, ownK) <= 2) return N(`${NAME[t]}を玉に寄せて守りを固める`, '守りを固めます。', 'myKing');
    if (ahead(side, I.from, I.to) > 0 && cheb(I.to, ownK) > 2) return N(`${NAME[t]}を前線に繰り出す`, `${NAME[t]}を攻めに参加させます。`, 'theirKing');
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
  X.Mi = moveInfo(P, M, X.lastTo);
  X.Mk = X.Mi.k;
  X.v = verbOf(X.Mi);
  X.imm = aspectDiff(partsOf(P, side), partsOf(after(P, [M], 1), side));   // 指した直後の評価の変化
  X.nat = natureOf(P, X.Mi, X.imm);
  X.inCheck = P.inCheck();
  X.legal = d && d.legal ? d.legal : P.legalMoves().length;
  X.handPieces = 0;   // 歩以外の持ち駒の数（多い、または盤上の駒が減っていれば、もう駒組みの段階ではない）
  for (let c = 0; c < 2; c++) for (let t = KY; t <= KI; t++) X.handPieces += P.hand[c * 8 + t];
  if (SQ81.filter(q => P.board[q]).length < 30) X.handPieces = 9;
  if (main.book) return X;
  // 直前に駒を取られていれば、その分も含めて損得を数える（取り返しただけで「駒得」と言わない）
  const debt = X.Mi.recapture && X.prev && X.prev.cap ? X.prev.cap : 0;
  const walkFrom = (usis) => {
    const L = walk(P, usis, side, X.lastTo);
    if (debt) { L.lost.unshift({ t: DEMOTE[debt], board: debt, ply: -1, s: X.prev.to }); L.mat -= EXV[debt]; }
    return L;
  };
  // 指した手の読み筋は、本番の深い読み（「千里眼の読み」と同じもの）を使う
  const c0 = d && d.cands && d.cands[0] && d.cands[0].m === main.move ? d.cands[0] : null;
  const pv = main.pv && main.pv.length >= 2 ? main.pv : c0 && c0.pv.length ? c0.pv : [main.move];
  X.L = walkFrom(pv);
  X.mateLen = main.score >= MATE_IN_MAX ? (main.mate || X.L.moves.length) : 0;
  X.La = c0 && c0.pv.length ? walkFrom(c0.pv) : X.L;   // 候補どうしを比べる時は同じ深さの読み
  if (X.L.moves.length >= 2) X.R = moveInfo(after(P, X.L.moves, 1), X.L.moves[1], mTo(M));
  // 歩交換・駒の交換
  const L = X.L, Lm = L.moves;
  X.pawnTrade = X.Mi.t === FU && !X.Mi.drop && !X.Mi.cap && Lm.length >= 3 && mTo(Lm[1]) === X.Mi.to && mCap(Lm[1]) && mTo(Lm[2]) === X.Mi.to && mCap(Lm[2]);
  X.rookPawn = X.pawnTrade && (mPiece(Lm[2]) & 15) === HI;
  const w4 = matWords(L, 3);
  X.trade = !X.pawnTrade && w4.traded.length && !w4.g.length && !w4.l.length && ((L.got.length && L.got[0].ply <= 1) || (L.lost.length && L.lost[0].ply <= 1)) ? TRADE[w4.traded[0]] || '' : '';
  // 相手の狙い・この手の狙い
  if (d && d.rootThreat) X.rt = threatInfo(P, 0, d.rootThreat, side ^ 1);
  if (d && d.moveThreat) X.mt = threatInfo(P, M, d.moveThreat, side);
  if (X.mt && X.R && X.R.cap && mFrom(X.mt.T) && X.R.to === mFrom(X.mt.T)) X.mt.real = false;
  if (X.rt && X.rt.real) X.rtHandled = handled(X);
  // 候補手
  X.alts = [];
  if (d && c0 && c0.s != null) {
    const shM = c0.sh;
    for (let i = 1; i < d.cands.length; i++) {
      const c = d.cands[i], A = P.parseUSI(c.m);
      if (!A || c.s == null) continue;
      const a = { c, A, k: kifOf(P, A, X.lastTo), I: moveInfo(P, A, X.lastTo, true), dv: c0.s - c.s, L: c.pv.length ? walkFrom(c.pv) : null };
      a.nat = natureOf(P, a.I);
      a.ev = isMate(c.s) || isMate(X.score) ? c.s : X.score - Math.max(0, a.dv);
      a.tempting = shM != null && c.sh != null && c.sh - shM >= 80 && a.dv >= 80;
      if (a.L && a.L.moves.length >= 2) {
        a.R = moveInfo(after(P, a.L.moves, 1), a.L.moves[1], mTo(A));
        a.sharp = a.R.check || a.R.promo || a.R.threats.some(x => x.t !== FU) || (a.R.cap && a.R.to !== mTo(A)) || a.dv >= 300;
      }
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

// この手が相手の狙いを消しているか（詰めろなら、深い読みで詰まされていないこと）
function handled(X) {
  const T = X.rt, I = X.Mi;
  if (T.mate) return !isMate(X.score) || X.score > 0 ? 'mate' : false;
  if ([1, 3, 5].some(i => X.L.moves[i] === T.T)) return false;
  if (!T.cap) return X.L.moves.length < 2 || X.L.moves[1] !== T.T ? 'other' : false;
  const s = T.cap.s;
  if (I.from === s && I.fled) return 'fled';
  if (mFrom(T.T) && I.to === mFrom(T.T)) return 'took';
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
function gapAdv(dv) {
  if (dv < 30) return 'わずかに';
  if (dv < 100) return '少し';
  if (dv < 250) return pts(dv);
  if (dv < 700) return 'はっきり';
  return '大きく';
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
// 狙いの中身を名詞句で（「△５五角で金を取る手」「▲４五歩で角に当てる手」など）
function threatNoun(T) {
  const L = T.L, I = T.I, cap = T.cap, big = I.threats.filter(x => x.g >= 300);
  const pr = L.promos.find(x => x.mine && x.kept && x.ply <= 2);
  if (I.cap && I.cap !== FU) return `${T.k}で${NAME[I.cap]}を取る手`;
  if (!I.cap && big.length >= 2) return `${T.k}の両取り`;
  if (pr && pr.ply === 0) return `${T.k}で${NAME[pr.t]}を作る手`;
  if (!I.cap && big.length) return `${T.k}で${NAME[big[0].t]}に当てる手`;
  if (pr) return `${T.k}から${NAME[pr.t]}を作る筋`;
  if (cap && cap.t !== FU) return `${T.k}から${NAME[cap.board]}を取る筋`;
  const w = matWords(L, Math.min(L.horizon, 4)), top = w.g.filter(t => t !== FU).sort((a, b) => HV[b] - HV[a])[0];
  if (w.net >= 150 && top) return `${T.k}から${NAME[top]}を取る筋`;
  if (w.net >= 150) return `${T.k}からの駒得`;
  return `${T.k}からの攻め`;
}
// 評価関数の内訳で見た、指した直後の変化（目立つものがあるときだけ）
function internals(X) {
  if (X.memo.ago('imm') < 3) return '';
  const d = X.imm, k = ['myKing', 'theirKing', 'act'].sort((a, b) => d[b] - d[a])[0];
  if (d[k] < 50 || (X.nat.asp && X.nat.asp !== k)) return '';
  X.memo.mark('imm');
  return X.say('imm', [
    `評価の内訳でも、この手で「${ASPECT[k]}」の点数が${pts(d[k])}上がっています。`,
    `千里眼の評価関数で見ると、効いているのは「${ASPECT[k]}」の項目で、${pts(d[k])}のプラスです。`,
  ]);
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
  if (I.check && fork.length && fork[0].g >= 400) return 'fork';
  if (fork.length >= 2 && fork[1].g >= 300) return 'fork';
  if (I.cap && I.see >= 150) return 'capture';
  if (X.mt && X.mt.real && X.mt.mate) return 'mateThreat';
  if (X.rt && X.rt.real && X.rtHandled) return 'defend';
  if (I.fled >= 300) return 'escape';
  if (I.t === FU && I.threats.some(th => th.g >= 300 && I.hits.some(h => h.s === th.s))) return 'pawnStrike';
  if (I.see <= -150 && X.score > -MATE_IN_MAX) return 'sacrifice';
  if (X.pawnTrade) return 'pawnTrade';
  if (X.trade && I.cap) return 'trade';
  if (I.promo && X.L.promos.length && X.L.promos[0].ply === 0 && X.L.promos[0].kept) return 'promote';
  if (X.mt && X.mt.real) return 'threat';
  if (I.castle) return 'castle';
  if (X.trade) return 'trade';
  if (I.t === FU && I.hits.some(h => h.t !== OU)) return 'pawnStrike';
  if (I.check) return 'check';
  return 'plan';
}

const LEAD = {
  book(X) {
    const n = X.nat;
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
      const seq = k.length <= 7 ? k.join('') : k.slice(0, 5).join('') + '…' + k[k.length - 1];
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
    const I = X.Mi, pk = X.prev ? X.prev.k : 'この';
    const te = I.t === OU ? (I.cap ? `玉で${NAME[I.cap]}を取って` : '玉をかわして')
      : I.cap ? `王手をかけてきた${NAME[I.cap]}を取って` : I.drop ? `${NAME[I.t]}を合駒して` : `${NAME[I.t]}を間に入れて`;
    const plain = I.t === OU ? (I.cap ? `玉で${NAME[I.cap]}を取る` : '玉をかわす')
      : I.cap ? `王手をかけてきた${NAME[I.cap]}を取る` : I.drop ? `${NAME[I.t]}を合駒する` : `${NAME[I.t]}を間に入れる`;
    return X.say('evasion', [
      `${pk}の王手には、${te}受けました（${X.Mk}）。`,
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
    const I = X.Mi, nm = NAME[I.cap], at = sqName(I.to), free = I.see >= EXV[I.cap];
    return X.say('capture', [
      free ? `${at}の${nm}に守りがなかったので、${X.Mk}と取りました。` : `${X.Mk}で${nm}を取ります。取り返されても、差し引きでこちらの得です。`,
      free ? `${nm}がただで取れる形だったので、${X.Mk}と取っています。` : `${at}の${nm}を${X.Mk}と取りました。取り合いになっても駒得が残ります。`,
      `${X.Mk}と${nm}を取って、駒得をはっきりさせました。`,
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
    if (how === 'fled') return X.say('defend.fled', [
      `${d}を避けるため、${X.Mk}と${NAME[I.t]}を逃がしました。`,
      `${X.Mk}と${X.v[1]}、${d}をかわしています。`,
    ]);
    const te = how === 'guarded' && T.cap ? `${NAME[T.cap.board]}に紐をつけて` : how === 'blocked' ? '利きを止めて' : X.v[1];
    return X.say('defend', [
      `あなたは次に${d}を狙っていました。${X.Mk}はそれを防ぐ手です。`,
      `${d}が気になる局面でした。${X.Mk}と${te}、その狙いを消しています。`,
      `何もしないと${T.k}が厳しいので、${X.Mk}で先に手を打ちました。`,
      `${X.Mk}は受けの手です。${d}を未然に防ぎました。`,
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
    if (I.t === FU && !I.drop) return X.say('sac.fu', [
      `${X.Mk}は歩の突き捨てです。${takes ? `${R}と取らせて、` : ''}${comp[1]}。`,
      `${X.Mk}と突き捨てて、相手の形を乱しにいきます。${comp[1]}。`,
    ]);
    return X.say('sac', [
      `${X.Mk}は${nm}を捨てる手です。${R ? `${R}と取られても、` : ''}${comp[1]}。`,
      `あえて${nm}を渡す${X.Mk}を選びました。${comp[0]}と読んでいます。`,
      `駒損を承知の${X.Mk}です。${comp[1]}。`,
    ]);
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
  castle(X) {
    const c = X.Mi.castle;
    return X.say('castle', [
      `${X.Mk}で${c}が完成しました。`,
      `${c}に組む${X.Mk}です。玉の守りがぐっと固くなります。`,
      X.Mi.t === OU ? `${X.Mk}と${X.v[1]}、玉を${c}に収めました。` : `${X.Mk}と${X.v[1]}、${c}の形を整えました。`,
    ]);
  },
  trade(X) {
    return X.say('trade', [`${X.Mk}は${X.trade}を挑む手です。`, `${X.trade}を狙った${X.Mk}です。`, `${X.Mk}から${X.trade}に持ち込みます。`]);
  },
  pawnStrike(X) {
    const I = X.Mi, h = I.hits.filter(x => x.t !== OU).sort((a, b) => E.PV[b.t] - E.PV[a.t])[0], nm = NAME[h.t];
    const promoNext = X.side === BLACK ? RANK[I.to] <= 4 : RANK[I.to] >= 6;
    const canTake = E.attacksFrom(after(X.P, [X.M], 1), h.s).indexOf(I.to) >= 0;
    if (I.drop) return X.say('tataki', [
      canTake ? `${X.Mk}と打って、${nm}の頭をたたきました。` : `${X.Mk}と打って${nm}に当て、${promoNext ? '次は成り込みを狙います' : `${nm}の動きを縛ります`}。`,
      canTake && promoNext ? `${X.Mk}は${nm}に当てる歩打ちです。取れば形が崩れ、取らなければ歩が成り込めます。`
        : canTake ? `${X.Mk}は${nm}に当てる歩打ちです。取らせて${nm}の位置をずらす狙いがあります。` : null,
      `${nm}の正面に${X.Mk}と歩を打ち、どう応じるかを問います。`,
    ]);
    const big = I.hits.filter(x => x.t !== OU && x.t !== FU).sort((a, b) => E.PV[b.t] - E.PV[a.t])[0];
    if (!big) return X.say('clash', [
      `${X.Mk}と歩をぶつけて、${ZEN[FILE[I.to]]}筋で戦いを起こします。`,
      `${X.Mk}は${ZEN[FILE[I.to]]}筋の歩をぶつける仕掛けです。`,
      `ここで${X.Mk}と突き、歩をぶつけて動きます。`,
    ]);
    return X.say('tsuki', [
      `${X.Mk}と${X.v[1]}、${sqName(big.s)}の${NAME[big.t]}に当てました。`,
      `${X.Mk}は${NAME[big.t]}をどかしにいく歩です。`,
      `${NAME[big.t]}の前に歩を突き出す${X.Mk}です。${NAME[big.t]}はどこかへ逃げる必要があります。`,
    ]);
  },
  check(X) {
    const L = X.L, R = X.R, pr = L.promos.find(p => p.mine && p.kept);
    const aim = pr ? `その間に${NAME[pr.t]}を作れます` : L.mat >= 150 && gainNoun(matWords(L)) ? `その流れで${gainNoun(matWords(L))}になります`
      : R && R.t === OU ? `玉を${sqName(R.to)}へ動かして、守りから引き離します` : R && R.drop ? `持ち駒を一枚使わせます` : '攻めのきっかけを作ります';
    return X.say('check', [
      `${X.Mk}と王手をかけました。${R ? `${R.k}と応じさせてから、` : ''}${aim}。`,
      `${X.Mk}は王手で先手を取る手です。${aim}。`,
      `まずは${X.Mk}の王手から入ります。${aim}。`,
    ]);
  },
  plan(X) {
    const n = X.nat;
    return X.say('plan', [
      `${X.Mk}は、${n.np}手です。`,
      `${X.Mk}と${X.v[1]}、${n.goal}`,
      `ここは${n.np}${X.Mk}を選びました。`,
    ]) + internals(X);
  },
};

// 駒を捨てる手の見返り：[普通体, 丁寧体]
function compensation(X) {
  const L = X.L;
  if (L.mated === (X.side ^ 1)) return ['そのまま寄せ切れる', 'そのまま寄せ切れます'];
  if (L.mat >= 0 && L.got.length) return ['あとで駒を取り返せる', 'あとで駒は取り返せます'];
  const pr = L.promos.find(p => p.mine && p.kept);
  if (pr) return [`その間に${NAME[pr.t]}を作れる`, `その間に${NAME[pr.t]}を作れます`];
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
  const seq = k.slice(1, Math.min(k.length, 6)).join(''), rest = k.slice(2, 6).join('');
  if (L.fight === 0 && L.build >= 2 && L.mated < 0 && X.handPieces <= 1 && X.memo.ago('build') >= 3) {
    X.memo.mark('build');
    return X.say('line.build', [
      `読み筋は${seq}で、しばらくは互いに陣形を整える展開が続くと見ています。`,
      `このあとは${seq}と、双方が駒組みを進める穏やかな進行を予想しています。`,
      `${seq}と、まだ駒がぶつかる前の準備が続く見込みです。`,
    ]);
  }
  const out = outcome(X), te = replyTe(X.R, X.M);
  if (!out) return X.say('line.plain', [
    `読み筋は${seq}です。`,
    rest ? `あなたの最善の応手は${k[1]}で、以下${rest}と進むと読んでいます。` : null,
    rest ? `${k[1]}${te}くるのが最善と見ていて、以下${rest}と続きます。` : null,
    `予想される進行は${seq}です。`,
  ]);
  return X.say('line', [
    `読み筋は${seq}で、${out}`,
    rest ? `あなたの最善の応手は${k[1]}で、以下${rest}と進むと読んでいます。${out}` : null,
    `このあと${seq}と進めば、${out}`,
    `予想される進行は${seq}。${out}`,
    rest ? `${k[1]}${te}くるのが最善で、${rest}と続きます。${out}` : null,
    L.fight >= 2 ? `${seq}と、すぐに駒がぶつかる展開です。${out}` : null,
  ]);
}
function outcome(X) {
  const L = X.L, w = matWords(L), pr = L.promos.find(p => p.mine && p.kept && p.ply <= 4);
  if (L.mated === (X.side ^ 1)) return 'あなたの玉が詰みます。';
  if (w.net >= 150 && gainNoun(w)) return X.say('out.gain', [`${gainNoun(w)}になります。`, `差し引き${gainNoun(w)}です。`, `${gainNoun(w)}が見込めます。`]);
  if (pr) return X.say('out.promo', [`${NAME[pr.t]}ができる展開です。`, `${NAME[pr.t]}を作れます。`]);
  if (w.net <= -150 && gainNoun(w)) return `${gainNoun(w)}になりますが、${compensation(X)[1]}。`;
  if (X.trade) return `${X.trade}になります。`;
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

// ---------------------------------------------------------------- 他の候補との比較
function altSentence(X, a, nth) {
  const L = a.L, k = L ? L.kifs : [], Rk = k[1] || '', cont = k.slice(1, 4).join('');
  const lead = nth === 0 ? '' : X.say('alt.conj', ['また、', '一方、', 'ほかに、', 'なお、', '']);
  const wA = L ? matWords(L) : null, wM = matWords(X.La);
  const dAsp = L ? aspectDiff(X.La.parts, L.parts) : null;
  const te = replyTe(a.R, a.A);
  // 詰まされる
  if (isMate(a.c.s) && a.c.s < 0) return lead + X.say('alt.mated', [
    `${a.k}は${Rk}以下の詰みがあって指せません。`,
    `${a.k}だと${cont}…と迫られて、こちらの玉が詰まされます。`,
    `${a.k}では${Rk}から詰まされてしまいます。`,
  ]);
  // 相手の狙いがそのまま残る
  if (X.rt && X.rt.real && L && L.moves[1] === X.rt.T && a.dv >= 120) return lead + X.say('alt.threat', [
    `${a.k}では、${X.rt.k}の狙いがそのまま残ってしまいます。`,
    `${a.k}は${X.rt.k}を許すので、受けとして不十分です。`,
    `${a.k}だと${cont}と進んで、狙われていた${X.rt.I.threats.length ? NAME[X.rt.I.threats[0].t] : X.rt.cap ? NAME[X.rt.cap.t] : '駒'}を守れません。`,
  ]);
  // 一見よさそうな手
  if (a.tempting && Rk && !X.used.has('tempt')) {
    X.used.add('tempt');
    const lure = a.I.cap ? `で${NAME[a.I.cap]}が取れそう` : a.I.check ? 'の王手が厳しそう' : a.I.promo ? 'と成るのが自然' : 'が良さそう';
    const res = wA && wA.net - wM.net <= -150 && gainNoun(wA) && wA.net < 0 ? `${gainNoun(wA)}になります`
      : X.say('tempt.res', [`${gapAdv(a.dv)}評価が下がります`, a.dv >= 300 ? '形勢を損ねます' : `${gapAdv(a.dv)}損をします`, `${X.Mk}より${pts(a.dv)}見劣りします`]);
    return lead + X.say('alt.tempt', [
      `一見${a.k}${lure}ですが、${Rk}${te}こられると${res}。`,
      `${a.k}${lure}に見えますが、${cont}と進むと${res}。`,
    ]);
  }
  // 途中まで本命だった
  if (X.mind && X.mind.m === a.c.m && !X.used.has('mind') && mindWorth(X, a)) {
    X.used.add('mind'); X.memo.mark('mind');
    if (a.dv < 30) return lead + X.say('alt.was0', [
      `深さ${X.mind.d2}までは${a.k}が最善でしたが、深く読むと${X.Mk}とほぼ並び、最後はわずかな差で${X.Mk}が上回りました。`,
      `${a.k}は途中まで本命でした。最後の深さで${X.Mk}が${a.dv <= 5 ? '並び、わずかに' : 'わずかに'}上回ったので、こちらを選んでいます。`,
    ]);
    if (a.sharp && Rk) return lead + X.say('alt.was', [
      `深さ${X.mind.d2}までは${a.k}を本命と見ていましたが、深く読むと${Rk}という返し技があり、評価を下げました。`,
      `途中まで最善と考えていた${a.k}は、深さ${X.mind.ds}で${Rk}${te}こられる筋が見えて、${X.Mk}に席を譲りました。`,
    ]);
    return lead + X.say('alt.was2', [
      `読み始めの本命は${a.k}でしたが、${cont}と進めた先で${gapAdv(a.dv)}見劣りすることが分かりました。`,
      `${a.k}は深さ${X.mind.d2}まで最善でしたが、さらに読むと${gapAdv(a.dv)}評価が落ちました。`,
    ]);
  }
  // ほぼ同じ評価
  if (a.dv < 30) {
    X.used.add('close');
    if (a.dv <= 5) return lead + X.say('alt.even', [
      `${a.k}も評価は同じで、${a.nat.np}手です。どちらを選んでも大差はありません。`,
      `数字の上では${a.k}も並んでいました。こちらは${a.nat.np}手です。`,
      `${a.k}とは評価が並び、方針の違いと言える比較でした。`,
    ]);
    return lead + X.say('alt.close', [
      `${a.k}（${a.nat.np}手）もほぼ同じ評価で、好みの範囲の差です。`,
      a.c.ef >= 0.2 ? `${a.k}にも読みの${Math.round(a.c.ef * 10)}割近くを費やしましたが、評価の差は${Math.round(a.dv)}点しかありませんでした。` : null,
      `${a.k}とはほとんど差がなく、紙一重の比較でした。`,
      `${a.k}も有力で、評価の差は${Math.round(a.dv)}点しかありません。`,
    ]);
  }
  // 駒損になる
  if (wA && wA.net - wM.net <= -150 && Rk) {
    const loss = gainNoun(wA) && wA.net < 0 ? gainNoun(wA) : '駒損';
    return lead + X.say('alt.mat', [
      `${a.k}には${Rk}があり、${loss}になります。`,
      `${a.k}だと${cont}と進んで、${loss}です。`,
      `${a.k}は${Rk}${te}こられて、${loss}になってしまいます。`,
    ]);
  }
  // 評価の内訳で一番悪くなるところ（差の大部分を占めるときだけ）
  if (dAsp && Rk && a.dv >= 40) {
    const worst = ['myKing', 'theirKing', 'act', 'threat'].sort((x, y) => dAsp[x] - dAsp[y])[0];
    if (dAsp[worst] <= -Math.max(60, a.dv * 0.5)) {
      const txt = {
        myKing: [`${a.k}は玉の守りが薄くなるのが難点で、${Rk}から攻め込まれます。`, `${a.k}だと${cont}と進み、こちらの玉が危なくなります。`],
        theirKing: [`${a.k}は攻めが一手遅れ、${Rk}と先に手を回されます。`, `${a.k}では${cont}と進んで、あなたの玉への迫り方が弱くなります。`],
        act: [`${a.k}は${Rk}${te}こられたあと、駒の働きが悪くなります。`, `${a.k}だと${cont}と進んで、駒がうまく働かない形になります。`],
        threat: [`${a.k}は${Rk}のあと、取られそうな駒が残ります。`, `${a.k}では${cont}と進んで、駒に当たりが残ったままになります。`],
      }[worst];
      return lead + X.say('alt.asp.' + worst, txt);
    }
  }
  return lead + X.say('alt.gen', [
    cont ? `${a.k}は${cont}と進んで、${gapAdv(a.dv)}評価が下がります。` : null,
    cont && a.c.ef >= 0.2 ? `${a.k}は読みの${Math.round(a.c.ef * 10)}割ほどを使って検討しましたが、${cont}と進むと${gapAdv(a.dv)}評価が下がりました。` : null,
    Rk && a.sharp ? `${a.k}には${Rk}が好手で、${X.Mk}より${pts(a.dv)}劣ります。` : null,
    `${a.k}は、${X.Mk}と比べて${gapAdv(a.dv)}見劣りします。`,
  ]);
}

function mindWorth(X, a) { return X.mind.d2 >= 6 && (X.memo.ago('mind') >= 3 || X.mind.ds >= 12 || (a && a.dv >= 100)); }

function pickAlts(X) {
  const alts = X.alts, out = [];
  const add = (a) => { if (a && out.indexOf(a) < 0 && out.length < 3) out.push(a); };
  add(alts[0]);
  add(alts.find(a => a.tempting));
  add(X.mind && alts.find(a => a.c.m === X.mind.m));
  add(alts.find(a => isMate(a.c.s) && a.c.s < 0));
  if (out.length < 2) add(alts.find(a => a.dv >= 30));
  return out;
}

// ---------------------------------------------------------------- 読みの経過・形勢のひとこと
function metaSentence(X, top) {
  if (X.mind && !X.used.has('mind') && X.mind.ds > 5 && mindWorth(X, X.alts.find(a => a.c.m === X.mind.m))) {
    X.used.add('mind'); X.memo.mark('mind');
    return X.say('meta.mind', [
      `深さ${X.mind.d2}までは${X.mind.k}を本命と見ていましたが、深さ${X.mind.ds}からは${X.Mk}が上回りました。`,
      `読み始めは${X.mind.k}が最善に見えていました。深く読むにつれて評価が入れ替わり、最後は${X.Mk}を選んでいます。`,
      `一度は${X.mind.k}に傾きましたが、深さ${X.mind.ds}で考えを改めました。`,
    ]);
  }
  if (top && top.dv >= 300 && !isMate(top.c.s)) return X.say('meta.clear', [
    `次善の${top.k}とも${pts(top.dv)}の差があり、迷う余地の少ない局面でした。`,
    `ほかの手とは${pts(top.dv)}の開きがあって、ここは${X.Mk}の一手と言えます。`,
  ]);
  if (X.stable && X.stable <= 4 && top && top.dv >= 50) return X.say('meta.stable', [
    `深さ${X.stable}の時点から最後まで、${X.Mk}が最善のまま変わりませんでした。`,
    `読みの初めから終わりまで、本命は一貫して${X.Mk}でした。`,
  ]);
  const st = standNow(X);
  if (st) return X.say('meta.stand', [`指したあとの形勢は、千里眼から見て${st}。`, `この手で、千里眼から見て${st}。`]);
  return '';
}

// 「▲６二とと取る」「△同銀とと金を取る」のような、と が重なる言い方を直す
function polish(t) {
  return t.replace(/([▲△][^、。▲△（）]*?と)と(?!金)/g, '$1で').replace(/([▲△][^、。▲△（）]*?[^と])とと金/g, '$1でと金');
}

// ---------------------------------------------------------------- 組み立て
function build(inp, memo) {
  memo = memo || MEMO;
  memo.builds++;
  const X = context(inp, memo);
  if (!X) return null;
  const purpose = purposeOf(X);
  const lead = LEAD[purpose](X);
  if (purpose === 'book') return { head: X.Mk, kind: purpose, paras: [polish(lead)], rows: [], foot: '' };
  if (purpose === 'mate') return { head: X.Mk, kind: purpose, paras: [polish(lead)], rows: [], foot: X.main.dfpn ? '詰み探索（df-pn）で読み切った手順です。' : '' };
  const p1 = [lead];
  // 主な理由とは別に、この手の狙いや受けにも触れる
  if (!['threat', 'mateThreat', 'promote', 'fork'].includes(purpose) && X.mt && X.mt.real && !X.mt.mate && X.mt.gain >= 300)
    p1.push(X.say('also.threat', [`さらに次は${threatNoun(X.mt)}も狙えます。`, `次に${threatNoun(X.mt)}が控えています。`]));
  if (!['defend', 'defendMate'].includes(purpose) && X.rt && X.rt.real && X.rtHandled && !X.rt.mate && X.rt.gain >= 300)
    p1.push(X.say('also.def', [`あなたの${threatNoun(X.rt)}も、この手で防いでいます。`, `同時に、${X.rt.k}の狙いも消えています。`]));
  if (X.rt && X.rt.real && !X.rtHandled && !X.rt.mate && X.mt && X.mt.real && X.score >= -100 && !['defend', 'defendMate'].includes(purpose))
    p1.push(X.say('race', [`あなたの${X.rt.k}も残っていますが、こちらの攻めの方が一手早いと見ています。`, `${X.rt.k}の狙いは承知の上で、先に攻める方を選びました。`]));
  if (purpose !== 'forced' && purpose !== 'pawnTrade') p1.push(lineSentence(X));
  const top = X.alts[0], paras = [];
  // 有力な手が並んでいる局面
  const even = X.alts.filter(a => a.dv < 20 && !isMate(a.c.s));
  let alts = pickAlts(X);
  if (even.length >= 2 && memo.ago('many') >= 3) {
    memo.mark('many'); X.used.add('close');
    p1.unshift(X.say('many', [
      `有力な手は${even.slice(0, 2).map(a => a.k).join('や')}など複数あり、評価はほぼ横並びでした。`,
      `${X.Mk}のほか、${even.slice(0, 2).map(a => a.k).join('・')}もほぼ同点で、どれを選んでもおかしくありません。`,
      `ここは${even.slice(0, 2).map(a => a.k).join('・')}も同じくらいの評価で、選択肢の多い場面です。`,
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
  const p2 = alts.map((a, i) => altSentence(X, a, i)).join('');
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
  return `候補${d.cands.length}手を同じ深さ（${d.depth}手）まで読み比べた結果です。評価値は千里眼から見た値です。`;
}

const api = { build, Memo };
if (typeof module !== 'undefined' && module.exports) module.exports = api;
else root.SenriganExplain = api;
})(typeof self !== 'undefined' ? self : this);
