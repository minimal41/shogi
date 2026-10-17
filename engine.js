/* Shogi engine: rules, move generation, evaluation, search, mate solver, book.
   Runs as a normal script (defines ShogiEngine) or as a Web Worker. */
(function shogiEngineFactory(root) {
'use strict';

// ---------------------------------------------------------------------------
// Pieces and board geometry
// ---------------------------------------------------------------------------
const FU = 1, KY = 2, KE = 3, GI = 4, KA = 5, HI = 6, KI = 7, OU = 8,
      TO = 9, NY = 10, NK = 11, NG = 12, UM = 13, RY = 14;
const BLACK = 0, WHITE = 1;
const WALL = 32;
const NSQ = 143;               // 13 rows x 11 cols, 2-row / 1-col sentinel border
const PROMO = 1 << 16;
const MAX_PLY = 2048;          // game + search history depth

const N = -11, S = 11, E = 1, Wd = -1, NE = -10, NW = -12, SE = 12, SW = 10;
const DIR8 = [N, NE, E, SE, S, SW, Wd, NW];
const DIR_INDEX = new Int8Array(25).fill(-1);
DIR8.forEach((d, i) => { DIR_INDEX[d + 12] = i; });

const SQ81 = new Int32Array(81);
const FILE = new Int8Array(NSQ), RANK = new Int8Array(NSQ);
{
  let i = 0;
  for (let r = 1; r <= 9; r++) for (let f = 9; f >= 1; f--) {
    const s = (r + 1) * 11 + (10 - f);
    SQ81[i++] = s; FILE[s] = f; RANK[s] = r;
  }
}
function sqOf(file, rank) { return (rank + 1) * 11 + (10 - file); }

const OWNER = new Uint8Array(33).fill(2);   // 0 black, 1 white, 2 empty, 3 wall
for (let t = 1; t <= 14; t++) { OWNER[t] = 0; OWNER[t | 16] = 1; }
OWNER[WALL] = 3;

const DEMOTE = new Int8Array(16);
for (let t = 0; t < 16; t++) DEMOTE[t] = t;
DEMOTE[TO] = FU; DEMOTE[NY] = KY; DEMOTE[NK] = KE; DEMOTE[NG] = GI; DEMOTE[UM] = KA; DEMOTE[RY] = HI;
const CAN_PROMOTE = new Uint8Array(16);
for (let t = FU; t <= HI; t++) CAN_PROMOTE[t] = 1;

// Movement (black orientation)
const GOLD_STEPS = [N, NE, NW, E, Wd, S];
const STEPS_B = [];
const SLIDES_B = [];
for (let t = 0; t < 16; t++) { STEPS_B[t] = []; SLIDES_B[t] = []; }
STEPS_B[FU] = [N];
STEPS_B[KE] = [-21, -23];
STEPS_B[GI] = [N, NE, NW, SE, SW];
STEPS_B[KI] = GOLD_STEPS;
STEPS_B[OU] = DIR8.slice();
STEPS_B[TO] = STEPS_B[NY] = STEPS_B[NK] = STEPS_B[NG] = GOLD_STEPS;
STEPS_B[UM] = [N, E, S, Wd];
STEPS_B[RY] = [NE, SE, SW, NW];
SLIDES_B[KY] = [N];
SLIDES_B[KA] = [NE, SE, SW, NW];
SLIDES_B[HI] = [N, E, S, Wd];
SLIDES_B[UM] = SLIDES_B[KA];
SLIDES_B[RY] = SLIDES_B[HI];

// STEP_LIST[c*16+t], SLIDE_LIST[c*16+t]
const STEP_LIST = [], SLIDE_LIST = [];
for (let c = 0; c < 2; c++) for (let t = 0; t < 16; t++) {
  const sg = c === 0 ? 1 : -1;
  STEP_LIST[c * 16 + t] = Int32Array.from(STEPS_B[t].map(d => d * sg));
  SLIDE_LIST[c * 16 + t] = Int32Array.from(SLIDES_B[t].map(d => d * sg));
}

// Attack masks: [by*8+k] -> bitmask of piece types of colour `by` that attack a target
// from the adjacent square in direction DIR8[k] (STEP_ATK) or from further along it (SLIDE_ATK).
const STEP_ATK = new Int32Array(16), SLIDE_ATK = new Int32Array(16);
// Movement masks: [c*16+t] -> bitmask over k of movement directions.
const STEP_MOVE_MASK = new Int32Array(32), SLIDE_MOVE_MASK = new Int32Array(32);
for (let c = 0; c < 2; c++) for (let t = 1; t <= 14; t++) {
  for (const d of STEP_LIST[c * 16 + t]) {
    if (d < -12 || d > 12) continue;           // knight jumps handled separately
    const k = DIR_INDEX[d + 12];
    STEP_MOVE_MASK[c * 16 + t] |= 1 << k;
    STEP_ATK[c * 8 + DIR_INDEX[-d + 12]] |= 1 << t;
  }
  for (const d of SLIDE_LIST[c * 16 + t]) {
    const k = DIR_INDEX[d + 12];
    STEP_MOVE_MASK[c * 16 + t] |= 1 << k;
    SLIDE_MOVE_MASK[c * 16 + t] |= 1 << k;
    STEP_ATK[c * 8 + DIR_INDEX[-d + 12]] |= 1 << t;
    SLIDE_ATK[c * 8 + DIR_INDEX[-d + 12]] |= 1 << t;
  }
}

// Line direction table: LINE_DIR[a*NSQ+b] = unit step from a toward b if aligned, else 0
const LINE_DIR = new Int8Array(NSQ * NSQ);
for (let i = 0; i < 81; i++) for (let j = 0; j < 81; j++) {
  const a = SQ81[i], b = SQ81[j];
  if (a === b) continue;
  const ra = (a / 11) | 0, ca = a % 11, rb = (b / 11) | 0, cb = b % 11;
  const dr = rb - ra, dc = cb - ca;
  let d = 0;
  if (dc === 0) d = Math.sign(dr) * 11;
  else if (dr === 0) d = Math.sign(dc);
  else if (Math.abs(dr) === Math.abs(dc)) d = Math.sign(dr) * 11 + Math.sign(dc);
  LINE_DIR[a * NSQ + b] = d;
}

// Zones
const ZONE = [new Uint8Array(NSQ), new Uint8Array(NSQ)];
const LAST1 = [new Uint8Array(NSQ), new Uint8Array(NSQ)];   // FU/KY may not stay / be dropped
const LAST2 = [new Uint8Array(NSQ), new Uint8Array(NSQ)];   // KE may not stay / be dropped
for (let i = 0; i < 81; i++) {
  const s = SQ81[i], r = RANK[s];
  ZONE[0][s] = r <= 3 ? 1 : 0; ZONE[1][s] = r >= 7 ? 1 : 0;
  LAST1[0][s] = r === 1 ? 1 : 0; LAST1[1][s] = r === 9 ? 1 : 0;
  LAST2[0][s] = r <= 2 ? 1 : 0; LAST2[1][s] = r >= 8 ? 1 : 0;
}

// ---------------------------------------------------------------------------
// Zobrist hashing (two 32-bit halves)
// ---------------------------------------------------------------------------
let rngState = 0x2545F491;
function rnd32() {
  let x = rngState;
  x ^= x << 13; x ^= x >>> 17; x ^= x << 5;
  rngState = x;
  return x | 0;
}
const Z_PIECE_LO = new Int32Array(32 * NSQ), Z_PIECE_HI = new Int32Array(32 * NSQ);
for (let i = 0; i < 32 * NSQ; i++) { Z_PIECE_LO[i] = rnd32(); Z_PIECE_HI[i] = rnd32(); }
const Z_HAND_LO = new Int32Array(16 * 20), Z_HAND_HI = new Int32Array(16 * 20);
for (let i = 0; i < 16 * 20; i++) {
  if (i % 20 === 0) continue;   // count 0 -> key 0
  Z_HAND_LO[i] = rnd32(); Z_HAND_HI[i] = rnd32();
}
const Z_SIDE_LO = rnd32() | 1, Z_SIDE_HI = rnd32();

// ---------------------------------------------------------------------------
// Material values
// ---------------------------------------------------------------------------
//                       -  FU   KY   KE   GI   KA   HI   KI    OU   TO   NY   NK   NG   UM    RY
const PV = new Int32Array([0, 90, 315, 405, 495, 855, 990, 540, 0, 540, 540, 540, 540, 945, 1395, 0]);
// Value of a piece held in hand (index FU..KI)
const HV = new Int32Array([0, 100, 320, 420, 520, 900, 1050, 560, 0]);
// Exchange value: what capturing a piece of type t swings (its board value + the hand value gained)
const EXV = new Int32Array(16);
for (let t = 1; t <= 14; t++) EXV[t] = t === OU ? 30000 : PV[t] + HV[DEMOTE[t]];
// Value used to order attackers (least valuable first)
const SEE_V = new Int32Array([0, 90, 315, 405, 495, 855, 990, 540, 30000, 540, 540, 540, 540, 945, 1395, 0]);

// ---------------------------------------------------------------------------
// Move helpers
// m = from | to<<8 | promo<<16 | piece<<17 | captured<<22 ; drops have from = 0
// ---------------------------------------------------------------------------
function mFrom(m) { return m & 255; }
function mTo(m) { return (m >> 8) & 255; }
function mPiece(m) { return (m >> 17) & 31; }
function mCap(m) { return (m >> 22) & 31; }
function mIsPromo(m) { return (m & PROMO) !== 0; }

const PIECE_USI = ['', 'P', 'L', 'N', 'S', 'B', 'R', 'G', 'K'];
const USI_PIECE = { P: FU, L: KY, N: KE, S: GI, B: KA, R: HI, G: KI, K: OU };

function sqToUSI(s) { return String(FILE[s]) + String.fromCharCode(96 + RANK[s]); }
function usiToSq(str) {
  const f = str.charCodeAt(0) - 48, r = str.charCodeAt(1) - 96;
  if (f < 1 || f > 9 || r < 1 || r > 9) return -1;
  return sqOf(f, r);
}
function moveToUSI(m) {
  if (m === 0) return 'resign';
  const from = mFrom(m), to = mTo(m);
  if (from === 0) return PIECE_USI[mPiece(m) & 15] + '*' + sqToUSI(to);
  return sqToUSI(from) + sqToUSI(to) + (mIsPromo(m) ? '+' : '');
}

// ---------------------------------------------------------------------------
// Position
// ---------------------------------------------------------------------------
const START_SFEN = 'lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1';

class Position {
  constructor() {
    this.board = new Int8Array(NSQ);
    this.hand = new Int8Array(16);
    this.kingSq = new Int32Array(2);
    this.pawnMask = new Int32Array(2);
    this.stm = BLACK;
    this.hashLo = 0; this.hashHi = 0;
    this.material = 0;
    this.ply = 0;
    this.histLo = new Int32Array(MAX_PLY);
    this.histHi = new Int32Array(MAX_PLY);
    this.histMat = new Int32Array(MAX_PLY);
    this.histMove = new Int32Array(MAX_PLY);
    this.histCheck = new Uint8Array(MAX_PLY);   // side to move at that index was in check
    this.tmpTarget = new Uint8Array(NSQ);
    // evaluation scratch
    this.atk = [new Uint8Array(NSQ), new Uint8Array(NSQ)];
    this.chkBuf = new Int32Array(16);
    this.betweenBuf = new Int32Array(8);
    this.evBuf = new Int32Array(700);
    this.hlmBuf = new Int32Array(700);
    this.chkGenBuf = new Int32Array(700);
    this.heChk = new Int32Array(16);
    this.heAtt = new Int32Array(16);
    this.setSFEN(START_SFEN);
  }

  clone() {
    const p = new Position();
    p.setSFEN(this.toSFEN());
    return p;
  }

  // Exact copy including the move history (repetition detection needs it)
  copyFrom(o) {
    this.board.set(o.board); this.hand.set(o.hand); this.kingSq.set(o.kingSq); this.pawnMask.set(o.pawnMask);
    this.stm = o.stm; this.hashLo = o.hashLo; this.hashHi = o.hashHi; this.material = o.material; this.ply = o.ply;
    this.histLo.set(o.histLo); this.histHi.set(o.histHi); this.histMat.set(o.histMat);
    this.histMove.set(o.histMove); this.histCheck.set(o.histCheck);
    return this;
  }

  setSFEN(sfen) {
    const parts = sfen.trim().split(/\s+/);
    const b = this.board;
    b.fill(WALL);
    for (let i = 0; i < 81; i++) b[SQ81[i]] = 0;
    this.hand.fill(0);
    this.kingSq[0] = this.kingSq[1] = 0;
    const rows = parts[0].split('/');
    if (rows.length !== 9) throw new Error('bad sfen');
    for (let r = 1; r <= 9; r++) {
      let f = 9, promo = false;
      for (const ch of rows[r - 1]) {
        if (ch === '+') { promo = true; continue; }
        if (ch >= '1' && ch <= '9') { f -= ch.charCodeAt(0) - 48; continue; }
        const up = ch.toUpperCase();
        let t = USI_PIECE[up];
        if (!t) throw new Error('bad sfen piece');
        if (promo) t += 8;
        promo = false;
        const c = ch === up ? BLACK : WHITE;
        const s = sqOf(f, r);
        b[s] = t | (c << 4);
        if (t === OU) this.kingSq[c] = s;
        f--;
      }
    }
    this.stm = parts[1] === 'w' ? WHITE : BLACK;
    const hs = parts[2] || '-';
    if (hs !== '-') {
      let num = 0;
      for (const ch of hs) {
        if (ch >= '0' && ch <= '9') { num = num * 10 + (ch.charCodeAt(0) - 48); continue; }
        const up = ch.toUpperCase();
        const t = USI_PIECE[up];
        const c = ch === up ? BLACK : WHITE;
        this.hand[c * 8 + t] += num || 1;
        num = 0;
      }
    }
    this.ply = 0;
    this.recompute();
  }

  recompute() {
    const b = this.board;
    let lo = 0, hi = 0, mat = 0;
    this.pawnMask[0] = this.pawnMask[1] = 0;
    for (let i = 0; i < 81; i++) {
      const s = SQ81[i], p = b[s];
      if (p === 0) continue;
      lo ^= Z_PIECE_LO[p * NSQ + s]; hi ^= Z_PIECE_HI[p * NSQ + s];
      const c = p >> 4, t = p & 15;
      mat += c === 0 ? PV[t] : -PV[t];
      if (t === FU) this.pawnMask[c] |= 1 << FILE[s];
      if (t === OU) this.kingSq[c] = s;
    }
    for (let c = 0; c < 2; c++) for (let t = FU; t <= KI; t++) {
      const n = this.hand[c * 8 + t];
      lo ^= Z_HAND_LO[(c * 8 + t) * 20 + n]; hi ^= Z_HAND_HI[(c * 8 + t) * 20 + n];
      mat += (c === 0 ? 1 : -1) * n * HV[t];
    }
    if (this.stm === WHITE) { lo ^= Z_SIDE_LO; hi ^= Z_SIDE_HI; }
    this.hashLo = lo; this.hashHi = hi; this.material = mat;
    this.histCheck[this.ply] = this.inCheck() ? 1 : 0;
  }

  toSFEN(moveNumber) {
    const b = this.board;
    const rows = [];
    for (let r = 1; r <= 9; r++) {
      let row = '', empty = 0;
      for (let f = 9; f >= 1; f--) {
        const p = b[sqOf(f, r)];
        if (p === 0) { empty++; continue; }
        if (empty) { row += empty; empty = 0; }
        const t = p & 15, c = p >> 4;
        let ch = PIECE_USI[DEMOTE[t]];
        if (c === WHITE) ch = ch.toLowerCase();
        row += (t >= TO ? '+' : '') + ch;
      }
      if (empty) row += empty;
      rows.push(row);
    }
    let hs = '';
    const order = [HI, KA, KI, GI, KE, KY, FU];
    for (let c = 0; c < 2; c++) for (const t of order) {
      const n = this.hand[c * 8 + t];
      if (!n) continue;
      let ch = PIECE_USI[t];
      if (c === WHITE) ch = ch.toLowerCase();
      hs += (n > 1 ? n : '') + ch;
    }
    return rows.join('/') + ' ' + (this.stm === BLACK ? 'b' : 'w') + ' ' + (hs || '-') + ' ' + (moveNumber || 1);
  }

  // Key identifying board + hands + side (for repetition in the UI)
  key() { return (this.hashHi >>> 0).toString(16) + ':' + (this.hashLo >>> 0).toString(16); }

  // -------------------------------------------------------------------------
  doMove(m) {
    const b = this.board, us = this.stm, them = us ^ 1, ply = this.ply;
    this.histLo[ply] = this.hashLo; this.histHi[ply] = this.hashHi;
    this.histMat[ply] = this.material; this.histMove[ply] = m;
    const from = m & 255, to = (m >> 8) & 255, pc = (m >> 17) & 31;
    let lo = this.hashLo ^ Z_SIDE_LO, hi = this.hashHi ^ Z_SIDE_HI, mat = this.material;
    const sg = us === BLACK ? 1 : -1;
    if (from === 0) {
      const t = pc & 15, hidx = us * 8 + t, n = this.hand[hidx], z = hidx * 20 + n;
      lo ^= Z_HAND_LO[z] ^ Z_HAND_LO[z - 1]; hi ^= Z_HAND_HI[z] ^ Z_HAND_HI[z - 1];
      this.hand[hidx] = n - 1;
      b[to] = pc;
      lo ^= Z_PIECE_LO[pc * NSQ + to]; hi ^= Z_PIECE_HI[pc * NSQ + to];
      mat += sg * (PV[t] - HV[t]);
      if (t === FU) this.pawnMask[us] |= 1 << FILE[to];
    } else {
      const cap = (m >> 22) & 31;
      b[from] = 0;
      lo ^= Z_PIECE_LO[pc * NSQ + from]; hi ^= Z_PIECE_HI[pc * NSQ + from];
      if (cap !== 0) {
        const ct = cap & 15, bt = DEMOTE[ct], hidx = us * 8 + bt, n = this.hand[hidx], z = hidx * 20 + n;
        lo ^= Z_PIECE_LO[cap * NSQ + to] ^ Z_HAND_LO[z] ^ Z_HAND_LO[z + 1];
        hi ^= Z_PIECE_HI[cap * NSQ + to] ^ Z_HAND_HI[z] ^ Z_HAND_HI[z + 1];
        this.hand[hidx] = n + 1;
        if (ct === FU) this.pawnMask[them] &= ~(1 << FILE[to]);
        mat += sg * (PV[ct] + HV[bt]);
      }
      let np = pc;
      if (m & PROMO) {
        np = pc + 8;
        const t = pc & 15;
        mat += sg * (PV[t + 8] - PV[t]);
        if (t === FU) this.pawnMask[us] &= ~(1 << FILE[from]);
      }
      b[to] = np;
      lo ^= Z_PIECE_LO[np * NSQ + to]; hi ^= Z_PIECE_HI[np * NSQ + to];
      if ((pc & 15) === OU) this.kingSq[us] = to;
    }
    this.hashLo = lo; this.hashHi = hi; this.material = mat;
    this.stm = them;
    this.ply = ply + 1;
  }

  undoMove(m) {
    const ply = --this.ply, b = this.board;
    const us = this.stm ^ 1, them = this.stm;
    this.stm = us;
    this.hashLo = this.histLo[ply]; this.hashHi = this.histHi[ply]; this.material = this.histMat[ply];
    const from = m & 255, to = (m >> 8) & 255, pc = (m >> 17) & 31;
    if (from === 0) {
      const t = pc & 15;
      this.hand[us * 8 + t]++;
      b[to] = 0;
      if (t === FU) this.pawnMask[us] &= ~(1 << FILE[to]);
    } else {
      const cap = (m >> 22) & 31;
      b[from] = pc;
      b[to] = cap;
      if (cap !== 0) {
        const ct = cap & 15;
        this.hand[us * 8 + DEMOTE[ct]]--;
        if (ct === FU) this.pawnMask[them] |= 1 << FILE[to];
      }
      if ((m & PROMO) && (pc & 15) === FU) this.pawnMask[us] |= 1 << FILE[from];
      if ((pc & 15) === OU) this.kingSq[us] = from;
    }
  }

  doNull() {
    const ply = this.ply;
    this.histLo[ply] = this.hashLo; this.histHi[ply] = this.hashHi;
    this.histMat[ply] = this.material; this.histMove[ply] = 0;
    this.hashLo ^= Z_SIDE_LO; this.hashHi ^= Z_SIDE_HI;
    this.stm ^= 1;
    this.ply = ply + 1;
  }
  undoNull() {
    const ply = --this.ply;
    this.hashLo = this.histLo[ply]; this.hashHi = this.histHi[ply];
    this.stm ^= 1;
  }

  // Hash after a move, without making it
  keyAfter(m, out) {
    const us = this.stm;
    const from = m & 255, to = (m >> 8) & 255, pc = (m >> 17) & 31;
    let lo = this.hashLo ^ Z_SIDE_LO, hi = this.hashHi ^ Z_SIDE_HI;
    if (from === 0) {
      const t = pc & 15, hidx = us * 8 + t, n = this.hand[hidx], z = hidx * 20 + n;
      lo ^= Z_HAND_LO[z] ^ Z_HAND_LO[z - 1] ^ Z_PIECE_LO[pc * NSQ + to];
      hi ^= Z_HAND_HI[z] ^ Z_HAND_HI[z - 1] ^ Z_PIECE_HI[pc * NSQ + to];
    } else {
      const cap = (m >> 22) & 31;
      lo ^= Z_PIECE_LO[pc * NSQ + from]; hi ^= Z_PIECE_HI[pc * NSQ + from];
      if (cap !== 0) {
        const bt = DEMOTE[cap & 15], hidx = us * 8 + bt, n = this.hand[hidx], z = hidx * 20 + n;
        lo ^= Z_PIECE_LO[cap * NSQ + to] ^ Z_HAND_LO[z] ^ Z_HAND_LO[z + 1];
        hi ^= Z_PIECE_HI[cap * NSQ + to] ^ Z_HAND_HI[z] ^ Z_HAND_HI[z + 1];
      }
      const np = (m & PROMO) ? pc + 8 : pc;
      lo ^= Z_PIECE_LO[np * NSQ + to]; hi ^= Z_PIECE_HI[np * NSQ + to];
    }
    out[0] = lo; out[1] = hi;
  }

  // -------------------------------------------------------------------------
  // Is square `sq` attacked by colour `by`?
  attacked(sq, by) {
    const b = this.board, o = by * 8;
    for (let k = 0; k < 8; k++) {
      const d = DIR8[k];
      let s = sq + d, p = b[s];
      if (p !== 0) {
        if (OWNER[p] === by && ((STEP_ATK[o + k] >> (p & 15)) & 1)) return true;
        continue;
      }
      s += d;
      while ((p = b[s]) === 0) s += d;
      if (OWNER[p] === by && ((SLIDE_ATK[o + k] >> (p & 15)) & 1)) return true;
    }
    if (by === BLACK) return b[sq + 21] === KE || b[sq + 23] === KE;
    return b[sq - 21] === (KE | 16) || b[sq - 23] === (KE | 16);
  }

  inCheck() { return this.attacked(this.kingSq[this.stm], this.stm ^ 1); }

  // Fill `out` with squares of pieces of colour `by` attacking `sq`; returns count
  attackers(sq, by, out) {
    const b = this.board, o = by * 8;
    let n = 0;
    for (let k = 0; k < 8; k++) {
      const d = DIR8[k];
      let s = sq + d, p = b[s];
      if (p !== 0) {
        if (OWNER[p] === by && ((STEP_ATK[o + k] >> (p & 15)) & 1)) out[n++] = s;
        continue;
      }
      s += d;
      while ((p = b[s]) === 0) s += d;
      if (OWNER[p] === by && ((SLIDE_ATK[o + k] >> (p & 15)) & 1)) out[n++] = s;
    }
    const kn = by === BLACK ? KE : (KE | 16), off = by === BLACK ? 1 : -1;
    if (b[sq + 21 * off] === kn) out[n++] = sq + 21 * off;
    if (b[sq + 23 * off] === kn) out[n++] = sq + 23 * off;
    return n;
  }

  // -------------------------------------------------------------------------
  // Move generation. mode bits: 1 = captures, 2 = non-captures (board), 4 = drops,
  // 8 = include every legal non-promotion (UI / exact legality)
  // Pseudo-legal: own-king safety and pawn-drop mate are checked separately.
  gen(list, n, mode) {
    const b = this.board, us = this.stm, them = us ^ 1;
    const wantCap = (mode & 1) !== 0, wantQuiet = (mode & 2) !== 0, all = (mode & 8) !== 0;
    if (mode & 3) {
      for (let i = 0; i < 81; i++) {
        const from = SQ81[i], p = b[from];
        if (OWNER[p] !== us) continue;
        const t = p & 15;
        const steps = STEP_LIST[us * 16 + t];
        for (let j = 0; j < steps.length; j++) {
          const to = from + steps[j], q = b[to], o = OWNER[q];
          if (o === us || o === 3) continue;
          if (q === 0 ? !wantQuiet : !wantCap) continue;
          n = this.addMove(list, n, from, to, p, q, t, us, all);
        }
        const slides = SLIDE_LIST[us * 16 + t];
        for (let j = 0; j < slides.length; j++) {
          const d = slides[j];
          let to = from + d, q;
          while ((q = b[to]) === 0) {
            if (wantQuiet) n = this.addMove(list, n, from, to, p, 0, t, us, all);
            to += d;
          }
          if (wantCap && OWNER[q] === them) n = this.addMove(list, n, from, to, p, q, t, us, all);
        }
      }
    }
    if (mode & 4) n = this.genDrops(list, n);
    return n;
  }

  addMove(list, n, from, to, p, q, t, us, all) {
    const base = from | (to << 8) | (p << 17) | (q << 22);
    if (CAN_PROMOTE[t] && (ZONE[us][from] || ZONE[us][to])) {
      list[n++] = base | PROMO;
      if (t === FU) { if (all && !LAST1[us][to]) list[n++] = base; return n; }
      if (t === KY) {
        if (LAST1[us][to]) return n;
        if (all || !LAST2[us][to]) list[n++] = base;
        return n;
      }
      if (t === KE) { if (!LAST2[us][to]) list[n++] = base; return n; }
      if (t === GI) { list[n++] = base; return n; }
      if (all) list[n++] = base;      // KA / HI non-promotion
      return n;
    }
    list[n++] = base;
    return n;
  }

  genDrops(list, n) {
    const b = this.board, us = this.stm, h = this.hand, o = us * 8;
    const types = [];
    for (let t = FU; t <= KI; t++) if (h[o + t] > 0) types.push(t);
    if (types.length === 0) return n;
    const pm = this.pawnMask[us], L1 = LAST1[us], L2 = LAST2[us], cbit = us << 4;
    for (let i = 0; i < 81; i++) {
      const to = SQ81[i];
      if (b[to] !== 0) continue;
      for (let j = 0; j < types.length; j++) {
        const t = types[j];
        if (t === FU) { if (L1[to] || ((pm >> FILE[to]) & 1)) continue; }
        else if (t === KY) { if (L1[to]) continue; }
        else if (t === KE) { if (L2[to]) continue; }
        list[n++] = (to << 8) | ((t | cbit) << 17);
      }
    }
    return n;
  }

  // Drops onto the squares marked in `target` (used for interpositions)
  genDropsTo(list, n, targets, nt) {
    const us = this.stm, h = this.hand, o = us * 8;
    const pm = this.pawnMask[us], L1 = LAST1[us], L2 = LAST2[us], cbit = us << 4;
    for (let t = FU; t <= KI; t++) {
      if (h[o + t] === 0) continue;
      for (let i = 0; i < nt; i++) {
        const to = targets[i];
        if (t === FU) { if (L1[to] || ((pm >> FILE[to]) & 1)) continue; }
        else if (t === KY) { if (L1[to]) continue; }
        else if (t === KE) { if (L2[to]) continue; }
        list[n++] = (to << 8) | ((t | cbit) << 17);
      }
    }
    return n;
  }

  // Pseudo-legal evasions when the side to move is in check
  genEvasions(list, n, all) {
    const b = this.board, us = this.stm, them = us ^ 1, ksq = this.kingSq[us];
    const kp = b[ksq];
    // king moves
    for (let k = 0; k < 8; k++) {
      const to = ksq + DIR8[k], q = b[to], o = OWNER[q];
      if (o === us || o === 3) continue;
      list[n++] = ksq | (to << 8) | (kp << 17) | (q << 22);
    }
    const chk = this.chkBuf;
    const nc = this.attackers(ksq, them, chk);
    if (nc !== 1) return n;
    const c = chk[0];
    // target squares: checker + squares between
    const tg = this.tmpTarget;
    const between = this.betweenBuf;
    let nb = 0;
    tg[c] = 1;
    const d = LINE_DIR[c * NSQ + ksq];
    if (d !== 0 && c + d !== ksq) {
      for (let s = c + d; s !== ksq; s += d) { tg[s] = 1; between[nb++] = s; }
    }
    // non-king board moves onto target squares
    const start = n;
    const mode = 3 | (all ? 8 : 0);
    const tmp = this.evBuf;
    const cnt = this.gen(tmp, 0, mode);
    for (let i = 0; i < cnt; i++) {
      const m = tmp[i];
      if ((m & 255) === ksq) continue;
      if (tg[(m >> 8) & 255]) list[n++] = m;
    }
    tg[c] = 0;
    for (let i = 0; i < nb; i++) tg[between[i]] = 0;
    if (nb > 0) n = this.genDropsTo(list, n, between, nb);
    return n;
  }

  // Does pseudo-legal move m leave own king safe? (does not check pawn-drop mate)
  isLegalPseudo(m) {
    const us = this.stm;
    this.doMove(m);
    const ok = !this.attacked(this.kingSq[us], us ^ 1);
    this.undoMove(m);
    return ok;
  }

  // Full legality including uchifuzume (pawn drop mate) for a pseudo-legal move
  isLegal(m) {
    const us = this.stm;
    this.doMove(m);
    let ok = !this.attacked(this.kingSq[us], us ^ 1);
    if (ok && (m & 255) === 0 && (((m >> 17) & 15) === FU)) {
      const to = (m >> 8) & 255;
      const ek = this.kingSq[us ^ 1];
      if (ek === to + (us === BLACK ? N : S)) {
        if (!this.hasLegalMove()) ok = false;   // pawn drop mate is illegal
      }
    }
    this.undoMove(m);
    return ok;
  }

  // Is a pawn drop at `to` giving check a mate? (assumes drop is otherwise legal)
  hasLegalMove() {
    const buf = this.hlmBuf;
    const inChk = this.inCheck();
    const n = inChk ? this.genEvasions(buf, 0, false) : this.gen(buf, 0, 7);
    for (let i = 0; i < n; i++) if (this.isLegalPseudo(buf[i])) return true;
    return false;
  }

  // All legal moves (every promotion choice) — for UI and tests
  legalMoves() {
    const buf = new Int32Array(1024);
    const n = this.inCheck() ? this.genEvasions(buf, 0, true) : this.gen(buf, 0, 15);
    const out = [];
    for (let i = 0; i < n; i++) if (this.isLegal(buf[i])) out.push(buf[i]);
    return out;
  }

  // Does move m (pseudo-legal) give check?
  givesCheck(m) {
    const b = this.board, us = this.stm, ek = this.kingSq[us ^ 1];
    const from = m & 255, to = (m >> 8) & 255, pc = (m >> 17) & 31;
    const t = (m & PROMO) ? (pc & 15) + 8 : (pc & 15);
    // direct
    const d = LINE_DIR[to * NSQ + ek];
    if (d !== 0) {
      const k = DIR_INDEX[d + 12];
      if (to + d === ek) { if ((STEP_MOVE_MASK[us * 16 + t] >> k) & 1) return true; }
      else if ((SLIDE_MOVE_MASK[us * 16 + t] >> k) & 1) {
        let s = to + d;
        while (s !== ek && (b[s] === 0 || s === from)) s += d;
        if (s === ek) return true;
      }
    } else if (t === KE) {
      const diff = ek - to;
      if (us === BLACK ? (diff === -21 || diff === -23) : (diff === 21 || diff === 23)) return true;
    }
    // discovered
    if (from !== 0) {
      const dd = LINE_DIR[ek * NSQ + from];
      if (dd !== 0 && LINE_DIR[ek * NSQ + to] !== dd) {
        let s = ek + dd;
        while (s !== from && b[s] === 0) s += dd;
        if (s === from) {
          s += dd;
          let p;
          while ((p = b[s]) === 0) s += dd;
          if (OWNER[p] === us && ((SLIDE_MOVE_MASK[us * 16 + (p & 15)] >> DIR_INDEX[-dd + 12]) & 1)) return true;
        }
      }
    }
    return false;
  }

  // Pseudo-legal check: can m be played in this position? (validates TT / killer moves)
  isPseudoLegal(m) {
    if (m === 0) return false;
    const b = this.board, us = this.stm;
    const from = m & 255, to = (m >> 8) & 255, pc = (m >> 17) & 31, cap = (m >> 22) & 31;
    if (to < 23 || to > 119 || OWNER[b[to]] > 2) return false;
    if (OWNER[pc] !== us) return false;
    const t = pc & 15;
    if (from === 0) {
      if (b[to] !== 0 || cap !== 0 || (m & PROMO)) return false;
      if (t < FU || t > KI || this.hand[us * 8 + t] === 0) return false;
      if (t === FU && (LAST1[us][to] || ((this.pawnMask[us] >> FILE[to]) & 1))) return false;
      if (t === KY && LAST1[us][to]) return false;
      if (t === KE && LAST2[us][to]) return false;
      return true;
    }
    if (from < 23 || from > 119 || b[from] !== pc || b[to] !== cap) return false;
    if (cap !== 0 && OWNER[cap] === us) return false;
    if ((cap & 15) === OU) return false;
    // reachable?
    const d = LINE_DIR[from * NSQ + to];
    let ok = false;
    if (d !== 0) {
      const k = DIR_INDEX[d + 12];
      if (from + d === to) ok = ((STEP_MOVE_MASK[us * 16 + t] >> k) & 1) === 1;
      else if ((SLIDE_MOVE_MASK[us * 16 + t] >> k) & 1) {
        let s = from + d;
        while (s !== to && b[s] === 0) s += d;
        ok = s === to;
      }
    } else if (t === KE) {
      const diff = to - from;
      ok = us === BLACK ? (diff === -21 || diff === -23) : (diff === 21 || diff === 23);
    }
    if (!ok) return false;
    if (m & PROMO) {
      if (!CAN_PROMOTE[t]) return false;
      if (!ZONE[us][from] && !ZONE[us][to]) return false;
    } else {
      if ((t === FU || t === KY) && LAST1[us][to]) return false;
      if (t === KE && LAST2[us][to]) return false;
    }
    return true;
  }

  // Parse a USI move string in this position (returns 0 if not legal)
  parseUSI(str) {
    const moves = this.legalMoves();
    for (const m of moves) if (moveToUSI(m) === str) return m;
    return 0;
  }

  // ------------------------------------------------------------------------
  // Repetition: 0 none, 1 draw, 2 side to move wins (opponent perpetual check),
  // 3 side to move loses (own perpetual check). Scans `limit` plies back.
  repetition(limit) {
    const ply = this.ply, lo = this.hashLo, hi = this.hashHi;
    const end = Math.max(0, ply - limit);
    for (let i = ply - 4; i >= end; i -= 2) {
      if (this.histLo[i] === lo && this.histHi[i] === hi) {
        // positions i..ply. Side to move at i equals current side.
        let oppAllChecks = true, ownAllChecks = true;
        for (let j = i + 2; j <= ply; j += 2) if (!this.histCheck[j]) { oppAllChecks = false; break; }
        for (let j = i + 1; j < ply; j += 2) if (!this.histCheck[j]) { ownAllChecks = false; break; }
        if (oppAllChecks) return 2;
        if (ownAllChecks) return 3;
        return 1;
      }
    }
    return 0;
  }
}

// ---------------------------------------------------------------------------
// Japanese notation (KIF style)
// ---------------------------------------------------------------------------
const KANJI_NUM = ['', '一', '二', '三', '四', '五', '六', '七', '八', '九'];
const ZEN_NUM = ['', '１', '２', '３', '４', '５', '６', '７', '８', '９'];
const PIECE_KANJI = ['', '歩', '香', '桂', '銀', '角', '飛', '金', '玉', 'と', '成香', '成桂', '成銀', '馬', '龍'];
const PIECE_CHAR = ['', '歩', '香', '桂', '銀', '角', '飛', '金', '玉', 'と', '杏', '圭', '全', '馬', '龍'];

function moveToKIF(pos, m, prevTo) {
  const us = pos.stm;
  const from = mFrom(m), to = mTo(m), pc = mPiece(m), t = pc & 15;
  const mark = us === BLACK ? '▲' : '△';
  const dest = (prevTo === to) ? '同　' : ZEN_NUM[FILE[to]] + KANJI_NUM[RANK[to]];
  let name = PIECE_KANJI[t];
  if (from === 0) {
    // "打" only when a board piece of the same type could also move there
    let need = false;
    const moves = pos.legalMoves();
    for (const x of moves) if (mFrom(x) !== 0 && mTo(x) === to && (mPiece(x) & 15) === t && !mIsPromo(x)) { need = true; break; }
    return mark + dest + name + (need ? '打' : '');
  }
  let rel = '';
  const moves = pos.legalMoves();
  const others = [];
  for (const x of moves) {
    if (mFrom(x) !== 0 && mFrom(x) !== from && mTo(x) === to && mPiece(x) === pc) {
      if (others.indexOf(mFrom(x)) < 0) others.push(mFrom(x));
    }
  }
  if (others.length > 0) rel = disambiguate(us, t, from, to, others);
  let suffix = '';
  if (mIsPromo(m)) suffix = '成';
  else if (CAN_PROMOTE[t] && (ZONE[us][from] || ZONE[us][to])) suffix = '不成';
  return mark + dest + name + rel + suffix;
}

function disambiguate(us, t, from, to, others) {
  // 上 / 引 / 寄 first, then 左 / 右 / 直, then both combined
  const motion = (src) => {
    const dr = us === BLACK ? RANK[src] - RANK[to] : RANK[to] - RANK[src];
    if (dr > 0) return '上';
    if (dr < 0) return '引';
    return '寄';
  };
  const mine = motion(from);
  const sameMotion = others.filter(o => motion(o) === mine);
  if (sameMotion.length === 0) return mine;
  if (t !== UM && t !== RY && FILE[from] === FILE[to] && mine === '上') return '直';
  const xOf = (s) => us === BLACK ? -FILE[s] : FILE[s];   // larger = further right for the mover
  const x = xOf(from);
  if (others.every(o => xOf(o) < x)) return '右';
  if (others.every(o => xOf(o) > x)) return '左';
  if (sameMotion.every(o => xOf(o) < x)) return '右' + mine;
  if (sameMotion.every(o => xOf(o) > x)) return '左' + mine;
  return mine;
}

// ---------------------------------------------------------------------------
// Exports (filled in further below)
// ---------------------------------------------------------------------------
const api = {
  FU, KY, KE, GI, KA, HI, KI, OU, TO, NY, NK, NG, UM, RY, BLACK, WHITE, WALL, PROMO,
  NSQ, SQ81, FILE, RANK, sqOf, OWNER, DEMOTE, CAN_PROMOTE, ZONE, LAST1, LAST2,
  Position, START_SFEN, moveToUSI, sqToUSI, usiToSq, moveToKIF,
  mFrom, mTo, mPiece, mCap, mIsPromo, PIECE_CHAR, PIECE_KANJI, KANJI_NUM, ZEN_NUM, PV, HV, EXV
};

// ---------------------------------------------------------------------------
// Extra move generation for mate search
// ---------------------------------------------------------------------------
Position.prototype.genChecks = function (list, n) {
  const b = this.board, us = this.stm, them = us ^ 1, ek = this.kingSq[them];
  const h = this.hand, o = us * 8, cbit = us << 4;
  const pm = this.pawnMask[us], L1 = LAST1[us], L2 = LAST2[us];
  for (let t = FU; t <= KI; t++) {
    if (h[o + t] === 0) continue;
    const steps = STEP_LIST[us * 16 + t];
    for (let j = 0; j < steps.length; j++) {
      const s = ek - steps[j];
      if (b[s] !== 0) continue;
      if (t === FU) { if (L1[s] || ((pm >> FILE[s]) & 1)) continue; }
      else if (t === KE) { if (L2[s]) continue; }
      list[n++] = (s << 8) | ((t | cbit) << 17);
    }
    const slides = SLIDE_LIST[us * 16 + t];
    for (let j = 0; j < slides.length; j++) {
      const d = slides[j];
      let s = ek - d;
      while (b[s] === 0) {
        if (!(t === KY && L1[s])) list[n++] = (s << 8) | ((t | cbit) << 17);
        s -= d;
      }
    }
  }
  const tmp = this.chkGenBuf;
  const cnt = this.gen(tmp, 0, 3);
  for (let i = 0; i < cnt; i++) if (this.givesCheck(tmp[i])) list[n++] = tmp[i];
  return n;
};

// Side to move is in check: does any legal evasion exist? (fast, early exit)
Position.prototype.hasEvasion = function () {
  const b = this.board, us = this.stm, them = us ^ 1, ksq = this.kingSq[us], kp = b[ksq];
  b[ksq] = 0;
  for (let k = 0; k < 8; k++) {
    const to = ksq + DIR8[k], o = OWNER[b[to]];
    if (o === us || o === 3) continue;
    if (!this.attacked(to, them)) { b[ksq] = kp; return true; }
  }
  b[ksq] = kp;
  const chk = this.heChk;
  const att = this.heAtt;
  const nc = this.attackers(ksq, them, chk);
  if (nc !== 1) return nc === 0;
  const c = chk[0];
  let na = this.attackers(c, us, att);
  for (let i = 0; i < na; i++) {
    const s = att[i];
    if (s === ksq) continue;
    const p = b[s], t = p & 15;
    let m = s | (c << 8) | (p << 17) | (b[c] << 22);
    if (((t === FU || t === KY) && LAST1[us][c]) || (t === KE && LAST2[us][c])) m |= PROMO;
    if (this.isLegalPseudo(m)) return true;
  }
  const d = LINE_DIR[c * NSQ + ksq];
  if (d !== 0 && c + d !== ksq) {
    const h = this.hand, o = us * 8;
    const anyDrop = h[o + GI] || h[o + KI] || h[o + KA] || h[o + HI];
    for (let s = c + d; s !== ksq; s += d) {
      if (anyDrop) return true;
      if (h[o + FU] && !LAST1[us][s] && !((this.pawnMask[us] >> FILE[s]) & 1)) return true;
      if (h[o + KY] && !LAST1[us][s]) return true;
      if (h[o + KE] && !LAST2[us][s]) return true;
      na = this.attackers(s, us, att);
      for (let i = 0; i < na; i++) {
        const f = att[i];
        if (f === ksq) continue;
        const p = b[f], t = p & 15;
        let m = f | (s << 8) | (p << 17);
        if (((t === FU || t === KY) && LAST1[us][s]) || (t === KE && LAST2[us][s])) m |= PROMO;
        if (this.isLegalPseudo(m)) return true;
      }
    }
  }
  return false;
};

// Mate in one: returns a mating move or 0 (side to move must not be in check)
Position.prototype.mate1 = function (buf) {
  const n = this.genChecks(buf, 0);
  const us = this.stm;
  for (let i = 0; i < n; i++) {
    const m = buf[i];
    if ((m & 255) === 0 && ((m >> 17) & 15) === FU) continue;   // pawn-drop mate is illegal
    this.doMove(m);
    if (this.attacked(this.kingSq[us], us ^ 1)) { this.undoMove(m); continue; }
    const esc = this.hasEvasion();
    this.undoMove(m);
    if (!esc) return m;
  }
  return 0;
};

// ---------------------------------------------------------------------------
// Evaluation
// ---------------------------------------------------------------------------
const REL = [new Uint8Array(NSQ * NSQ), new Uint8Array(NSQ * NSQ)];
for (let i = 0; i < 81; i++) for (let j = 0; j < 81; j++) {
  const a = SQ81[i], k = SQ81[j];
  const dx = Math.abs(FILE[a] - FILE[k]);
  REL[0][a * NSQ + k] = (RANK[k] - RANK[a] + 8) * 9 + dx;
  REL[1][a * NSQ + k] = (RANK[a] - RANK[k] + 8) * 9 + dx;
}
const OWNK = new Int16Array(16 * 153), ENEK = new Int16Array(16 * 153);
function fillRel(table, t, top, rows, scale) {
  for (let r = 0; r < rows.length; r++) {
    const dy = top - r;
    for (let dx = 0; dx < rows[r].length; dx++) table[t * 153 + (dy + 8) * 9 + dx] = Math.round(rows[r][dx] * (scale || 1));
  }
}
function fillDist(table, t, vals) {   // by Chebyshev distance
  for (let dy = -8; dy <= 8; dy++) for (let dx = 0; dx <= 8; dx++) {
    const dist = Math.max(dx, Math.abs(dy));
    if (dist > 0 && dist < vals.length) table[t * 153 + (dy + 8) * 9 + dx] = vals[dist];
  }
}
const GOLD_DEF = [[4, 6, 4, 0], [16, 20, 12, 4], [36, 42, 24, 6], [0, 44, 24, 6], [28, 32, 16, 4], [6, 8, 4, 0]];
const SILVER_DEF = [[6, 8, 6, 2], [18, 24, 16, 6], [32, 38, 24, 6], [0, 30, 20, 4], [20, 28, 12, 2], [4, 6, 2, 0]];
const GOLD_ATK = [[8, 8, 6, 2], [24, 24, 16, 6], [48, 46, 26, 8], [0, 44, 24, 6], [36, 36, 20, 6], [16, 16, 10, 4]];
const SILVER_ATK = [[8, 10, 8, 2], [24, 28, 18, 6], [44, 44, 26, 8], [0, 36, 22, 6], [36, 40, 20, 6], [14, 16, 10, 4]];
fillRel(OWNK, KI, 3, GOLD_DEF);
fillRel(OWNK, GI, 3, SILVER_DEF);
for (const t of [TO, NY, NK, NG]) fillRel(OWNK, t, 3, GOLD_DEF, 0.5);
fillRel(OWNK, KE, 0, [[0, 6, 4], [8, 10, 4], [4, 6, 2]]);
fillRel(OWNK, KY, -1, [[4, 4, 2], [4, 4, 2]]);
fillRel(OWNK, FU, 3, [[4, 4, 2], [10, 12, 6], [14, 14, 8]]);
fillDist(OWNK, HI, [0, -30, -15]);
fillDist(OWNK, UM, [0, 30, 30, 15]);
fillDist(OWNK, RY, [0, 15, 15, 5]);
fillRel(ENEK, KI, 3, GOLD_ATK);
for (const t of [TO, NY, NK, NG]) fillRel(ENEK, t, 3, GOLD_ATK);
fillRel(ENEK, GI, 3, SILVER_ATK);
fillRel(ENEK, KE, 4, [[10, 12, 10], [16, 20, 16, 6], [14, 20, 14, 6]]);
fillRel(ENEK, FU, 3, [[8, 6], [20, 12], [24, 10]]);
for (let dy = 1; dy <= 8; dy++) ENEK[KY * 153 + (dy + 8) * 9] = 16;
fillDist(ENEK, HI, [0, 40, 30, 15]);
fillDist(ENEK, RY, [0, 80, 60, 30, 10]);
fillDist(ENEK, UM, [0, 70, 50, 25, 8]);

// Absolute piece-square by relative rank (1 = own back rank)
const PST_RANK = [];
for (let t = 0; t < 16; t++) PST_RANK[t] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
PST_RANK[FU] = [0, 0, 0, 0, 3, 6, 10, 14, 0, 0];
PST_RANK[KY] = [0, 6, 2, 0, 0, 0, 0, 0, 0, 0];
PST_RANK[KE] = [0, 0, 2, 8, 10, 12, 4, -10, 0, 0];
PST_RANK[GI] = [0, -6, 4, 8, 10, 10, 6, 4, 0, -4];
PST_RANK[KI] = [0, 0, 2, 2, 0, -4, -6, -6, -6, -6];
PST_RANK[HI] = [0, 0, 0, 0, 0, 0, 4, 10, 10, 10];
PST_RANK[OU] = [0, 0, -6, -24, -60, -90, -110, -110, -90, -70];
PST_RANK[UM] = [0, 8, 8, 4, 0, 0, 0, 4, 8, 8];
PST_RANK[RY] = [0, 0, 0, 0, 0, 0, 10, 24, 30, 24];
const KING_FILE = [-25, -12, 0, 6, 4];
const PST = [new Int16Array(16 * NSQ), new Int16Array(16 * NSQ)];
for (let t = 1; t <= 14; t++) for (let i = 0; i < 81; i++) {
  const s = SQ81[i];
  const rrB = 10 - RANK[s], rrW = RANK[s];
  let vb = PST_RANK[t][rrB], vw = PST_RANK[t][rrW];
  if (t === OU) { vb += KING_FILE[Math.abs(FILE[s] - 5)]; vw += KING_FILE[Math.abs(FILE[s] - 5)]; }
  PST[0][t * NSQ + s] = vb;
  PST[1][t * NSQ + s] = vw;
}
const MOB = new Int16Array(16);
MOB[KA] = 3; MOB[HI] = 3; MOB[UM] = 2; MOB[RY] = 2; MOB[KY] = 1;
const HAND_POWER = new Int16Array([0, 1, 2, 2, 3, 3, 4, 5, 0]);
// King zone: 8 neighbours then 3 squares two ranks ahead
const KZONE = [Int32Array.from(DIR8.concat([-23, -22, -21])), Int32Array.from(DIR8.concat([23, 22, 21]))];
const TEMPO = 20;

const EVAL_PARAMS = { kingScale: 4, kingCap: 2500 };

function kingDanger(pos, c) {
  const b = pos.board, k = pos.kingSq[c], them = c ^ 1;
  const atkT = pos.atk[them], atkO = pos.atk[c];
  const zone = KZONE[c];
  let units = 0, escapes = 0, pressure = 0;
  for (let i = 0; i < 11; i++) {
    const s = k + zone[i], p = b[s];
    if (p === WALL) continue;
    const a = atkT[s];
    if (i < 8) {
      if (a === 0) { if (OWNER[p] !== c) escapes++; continue; }
      pressure += a;
      units += a * 4 + (a > atkO[s] ? 6 : 0);
      if (OWNER[p] !== c && a > atkO[s]) units += 2;
    } else if (a > 0) {
      units += a * 2;
    }
  }
  const h = pos.hand, o = them * 8;
  let hp = 0;
  for (let t = FU; t <= KI; t++) if (h[o + t]) hp += HAND_POWER[t] * (t === FU ? Math.min(h[o + t], 2) : h[o + t]);
  units += pressure > 0 ? hp * 2 : hp;
  if (pressure > 0) units += escapes === 0 ? 8 : escapes === 1 ? 4 : 0;
  const pen = (units * units) >> 2;
  return pen > EVAL_PARAMS.kingCap ? EVAL_PARAMS.kingCap : pen;
}

function evaluateHand(pos) {
  const b = pos.board, kB = pos.kingSq[0], kW = pos.kingSq[1];
  const atkB = pos.atk[0], atkW = pos.atk[1];
  atkB.fill(0); atkW.fill(0);
  const relB = REL[0], relW = REL[1], pstB = PST[0], pstW = PST[1];
  let sc = pos.material;
  for (let i = 0; i < 81; i++) {
    const s = SQ81[i], p = b[s];
    if (p === 0) continue;
    const t = p & 15;
    if (p < 16) {
      sc += pstB[t * NSQ + s] + OWNK[t * 153 + relB[s * NSQ + kB]] + ENEK[t * 153 + relW[s * NSQ + kW]];
      if (t === OU) continue;
      const st = STEP_LIST[t];
      for (let j = 0; j < st.length; j++) atkB[s + st[j]]++;
      const sl = SLIDE_LIST[t];
      if (sl.length) {
        let mob = 0;
        for (let j = 0; j < sl.length; j++) {
          const d = sl[j];
          let q = s + d;
          for (;;) {
            atkB[q]++;
            const pq = b[q];
            if (pq === 0) { mob++; q += d; continue; }
            if (OWNER[pq] === 1) mob++;
            break;
          }
        }
        sc += MOB[t] * mob;
      }
    } else {
      sc -= pstW[t * NSQ + s] + OWNK[t * 153 + relW[s * NSQ + kW]] + ENEK[t * 153 + relB[s * NSQ + kB]];
      if (t === OU) continue;
      const st = STEP_LIST[16 + t];
      for (let j = 0; j < st.length; j++) atkW[s + st[j]]++;
      const sl = SLIDE_LIST[16 + t];
      if (sl.length) {
        let mob = 0;
        for (let j = 0; j < sl.length; j++) {
          const d = sl[j];
          let q = s + d;
          for (;;) {
            atkW[q]++;
            const pq = b[q];
            if (pq === 0) { mob++; q += d; continue; }
            if (OWNER[pq] === 0) mob++;
            break;
          }
        }
        sc -= MOB[t] * mob;
      }
    }
  }
  sc += kingDanger(pos, WHITE) - kingDanger(pos, BLACK);
  return (pos.stm === BLACK ? sc : -sc) + TEMPO;
}

// ---------------------------------------------------------------------------
// Learnable evaluation: a sum of weights over sparse features (black's view)
// ---------------------------------------------------------------------------
const HAND_MAX = [0, 18, 4, 4, 4, 2, 2, 4];
const FEAT = {};
{
  let o = 0;
  const add = (name, size) => { FEAT[name] = o; o += size; };
  add('MAT', 16);
  add('HAND', 38);
  add('PST', 16 * 45);
  add('OWNK', 6 * 16 * 153);
  add('ENEK', 6 * 16 * 153);
  add('MOB', 16 * 17);
  add('KS_A', 16);
  add('KS_U', 9 * 8);
  add('KS_X', 9 * 2);
  add('KS_F', 8);
  add('KS_D', 9 * 2);
  add('HANG_S', 16);
  add('HANG_N', 16);
  add('TEMPO', 1);
  add('THR_S', 16);
  add('THR_N', 16);
  FEAT.N = o;
}
const NPARAMS = FEAT.N;
const F_MAT = FEAT.MAT, F_PST = FEAT.PST, F_OWNK = FEAT.OWNK, F_ENEK = FEAT.ENEK, F_MOB = FEAT.MOB;
const F_KS_A = FEAT.KS_A, F_KS_U = FEAT.KS_U, F_KS_X = FEAT.KS_X, F_KS_F = FEAT.KS_F, F_KS_D = FEAT.KS_D;
const F_HANG_S = FEAT.HANG_S, F_HANG_N = FEAT.HANG_N, F_TEMPO = FEAT.TEMPO, F_THR_S = FEAT.THR_S, F_THR_N = FEAT.THR_N;
const HAND_BASE = new Int32Array(8);
{ let o = FEAT.HAND; for (let t = 1; t <= 7; t++) { HAND_BASE[t] = o; o += HAND_MAX[t]; } }
const MIRROR = [new Uint8Array(NSQ), new Uint8Array(NSQ)];
for (let i = 0; i < 81; i++) {
  const s = SQ81[i];
  const fb = FILE[s], rb = RANK[s];
  MIRROR[0][s] = (rb - 1) * 5 + (Math.min(fb, 10 - fb) - 1);
  const fw = 10 - FILE[s], rw = 10 - RANK[s];
  MIRROR[1][s] = (rw - 1) * 5 + (Math.min(fw, 10 - fw) - 1);
}
const FRONT2 = [Int32Array.from([-23, -22, -21]), Int32Array.from([23, 22, 21])];
// King context: file class (edge / side / centre) x (inside own camp / advanced), from the king owner's view
const KCLASS = [new Uint8Array(NSQ), new Uint8Array(NSQ)];
for (let i = 0; i < 81; i++) {
  const s = SQ81[i], f = Math.min(FILE[s], 10 - FILE[s]);
  const fc = f <= 2 ? 0 : f <= 4 ? 1 : 2;
  KCLASS[0][s] = (RANK[s] >= 7 ? 0 : 3) + fc;
  KCLASS[1][s] = (RANK[s] <= 3 ? 0 : 3) + fc;
}
const WT = new Int16Array(NPARAMS);
//              -  FU KY KE GI KA HI KI OU TO NY NK NG UM RY
const VRANK = new Int8Array([0, 1, 2, 3, 4, 6, 7, 5, 15, 5, 5, 5, 5, 8, 9, 0]);
const ATK_MIN = [new Int8Array(NSQ), new Int8Array(NSQ)];
const EVAL_BUF = new Int32Array(1024);
const PIECE_LIST = new Int32Array(64);

function defaultWeights() {
  WT.fill(0);
  for (let t = 1; t <= 14; t++) if (t !== OU) WT[FEAT.MAT + t] = PV[t];
  for (let t = 1; t <= 7; t++) for (let k = 0; k < HAND_MAX[t]; k++) WT[HAND_BASE[t] + k] = HV[t];
  for (let t = 1; t <= 14; t++) for (let i = 0; i < 81; i++) {
    const s = SQ81[i];
    WT[FEAT.PST + t * 45 + MIRROR[0][s]] = PST[0][t * NSQ + s];
  }
  for (let k = 0; k < 6; k++) for (let i = 0; i < 16 * 153; i++) { WT[FEAT.OWNK + k * 2448 + i] = OWNK[i]; WT[FEAT.ENEK + k * 2448 + i] = ENEK[i]; }
  for (const t of [KY, KA, HI, UM, RY]) for (let c = 0; c <= 16; c++) WT[FEAT.MOB + t * 17 + c] = MOB[t] * c;
  for (let a = 0; a < 16; a++) WT[FEAT.KS_A + a] = -a * 12;
  for (let u = 0; u <= 8; u++) for (let h = 0; h < 8; h++) WT[FEAT.KS_U + u * 8 + h] = -(u * u * 10 + u * h * 8 + (u > 0 ? h * 6 : h * 2));
  for (let x = 0; x <= 8; x++) { WT[FEAT.KS_X + x * 2 + 1] = x === 0 ? -60 : x === 1 ? -30 : 0; }
  for (let f = 0; f < 8; f++) WT[FEAT.KS_F + f] = -f * 6;
  for (let d = 0; d <= 8; d++) { WT[FEAT.KS_D + d * 2 + 1] = -d * 10; }
  for (let t = 1; t <= 14; t++) if (t !== OU) { WT[FEAT.HANG_S + t] = -Math.round(PV[t] * 0.08); WT[FEAT.HANG_N + t] = -Math.round(PV[t] * 0.5); }
  WT[FEAT.TEMPO] = 20;
  for (let t = 1; t <= 14; t++) if (t !== OU) { WT[FEAT.THR_S + t] = -Math.round(PV[t] * 0.05); WT[FEAT.THR_N + t] = -Math.round(PV[t] * 0.25); }
}

// ---------------------------------------------------------------------------
// Dense king-safety / balance features for the small correction network.
// extractFeatures fills KST / DENSE_MAT as a side effect; denseFeatures assembles them.
// out[0..ND-1]: black's view, out[ND..2ND-1]: white's view
// ---------------------------------------------------------------------------
const ND = 56;
const CHEB = new Uint8Array(NSQ * NSQ);
for (let i = 0; i < 81; i++) for (let j = 0; j < 81; j++) {
  const a = SQ81[i], b2 = SQ81[j];
  CHEB[a * NSQ + b2] = Math.max(Math.abs(FILE[a] - FILE[b2]), Math.abs(RANK[a] - RANK[b2]));
}
//                          -  FU KY KE GI KA HI KI OU TO NY NK NG UM RY
const NEAR_W = new Int8Array([0, 1, 1, 1, 2, 2, 2, 2, 0, 2, 2, 2, 2, 3, 3, 0]);
const IS_DEF = new Uint8Array([0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0]);
const ZONE5A = (() => { const z = []; for (let dr = -2; dr <= 2; dr++) for (let dc = -2; dc <= 2; dc++) if (Math.max(Math.abs(dr), Math.abs(dc)) === 2) z.push(dr * 11 + dc); return Int32Array.from(z); })();
const KST = new Float64Array(2 * 10);
// Attack / defence counts around a king, pooled left-right: front, front-diagonals, sides, back-diagonals, back
function kingGroups(pos, c, out, o) {
  const k = pos.kingSq[c], b = pos.board, atkT = pos.atk[c ^ 1], atkO = pos.atk[c];
  const f = c === BLACK ? -11 : 11;
  const sq = [k + f, k + f - 1, k + f + 1, k - 1, k + 1, k - f - 1, k - f + 1, k - f];
  const grp = [0, 1, 1, 2, 2, 3, 3, 4];
  for (let i = 0; i < 10; i++) out[o + i] = 0;
  for (let i = 0; i < 8; i++) {
    const s2 = sq[i];
    if (b[s2] === WALL) continue;
    out[o + grp[i]] += atkT[s2];
    out[o + 5 + grp[i]] += atkO[s2];
  }
}
const DENSE_MAT = new Float64Array(1);
function denseFeatures(pos, out) {
  const b = pos.board;
  for (let c = 0; c < 2; c++) {
    const k = pos.kingSq[c], atkT = pos.atk[c ^ 1];
    let Z = 0;
    for (let i = 0; i < 16; i++) { const sq = k + ZONE5A[i]; if (sq >= 0 && sq < NSQ && b[sq] !== WALL) Z += atkT[sq]; }
    KST[c * 10 + 5] = Z;
  }
  const h = pos.hand;
  let matB = DENSE_MAT[0];
  for (let t = FU; t <= KI; t++) matB += (h[t] - h[8 + t]) * HV[t];
  for (let v = 0; v < 2; v++) {
    const base = v * ND, us = v, op = v ^ 1;
    for (let i = 0; i < 10; i++) { out[base + i] = KST[us * 10 + i]; out[base + 10 + i] = KST[op * 10 + i]; }
    for (let t = 1; t <= 7; t++) { out[base + 19 + t] = h[us * 8 + t]; out[base + 26 + t] = h[op * 8 + t]; }
    out[base + 34] = (v === 0 ? matB : -matB) / 1000;
    out[base + 35] = pos.stm === us ? 1 : 0;
    kingGroups(pos, us, out, base + 36);
    kingGroups(pos, op, out, base + 46);
  }
  return 2 * ND;
}

function kingFeatures(pos, c, F, n) {
  const b = pos.board, k = pos.kingSq[c], atkT = pos.atk[c ^ 1], atkO = pos.atk[c];
  let A = 0, U = 0, X = 0, D = 0, Fr = 0;
  for (let i = 0; i < 8; i++) {
    const s = k + DIR8[i], p = b[s];
    if (p === WALL) continue;
    const a = atkT[s], d = atkO[s];
    A += a;
    if (a > d) U++;
    if (OWNER[p] !== c && a === 0) X++;
    if (p === 0 && d === 0) D++;
  }
  const fz = FRONT2[c];
  for (let i = 0; i < 3; i++) { const s = k + fz[i]; if (b[s] !== WALL) Fr += atkT[s]; }
  const h = pos.hand, o = (c ^ 1) * 8;
  const hp = Math.min(h[o + FU], 2) + h[o + KY] + h[o + KE] + 2 * (h[o + GI] + h[o + KI] + h[o + KA]) + 3 * h[o + HI];
  const hb = hp > 7 ? 7 : hp;
  const goldish = (h[o + KI] + h[o + GI] + h[o + KA] + h[o + HI]) > 0 ? 1 : 0;
  const ko = c * 10;
  KST[ko] = A; KST[ko + 1] = U; KST[ko + 2] = X; KST[ko + 3] = D; KST[ko + 4] = Fr;
  const i1 = F_KS_A + (A > 15 ? 15 : A);
  const i2 = F_KS_U + U * 8 + hb;
  const i3 = F_KS_X + X * 2 + (A > 0 ? 1 : 0);
  const i4 = F_KS_F + (Fr > 7 ? 7 : Fr);
  const i5 = F_KS_D + D * 2 + goldish;
  if (c === BLACK) { F[n++] = i1; F[n++] = i2; F[n++] = i3; F[n++] = i4; F[n++] = i5; }
  else { F[n++] = ~i1; F[n++] = ~i2; F[n++] = ~i3; F[n++] = ~i4; F[n++] = ~i5; }
  return n;
}

// Writes signed feature indices (x >= 0 means +1 on W[x], x < 0 means -1 on W[~x]); returns count
function extractFeatures(pos, F) {
  const b = pos.board, kB = pos.kingSq[0], kW = pos.kingSq[1];
  const atkB = pos.atk[0], atkW = pos.atk[1];
  atkB.fill(0); atkW.fill(0);
  const mnB = ATK_MIN[0], mnW = ATK_MIN[1];
  mnB.fill(15); mnW.fill(15);
  const relB = REL[0], relW = REL[1], mirB = MIRROR[0], mirW = MIRROR[1];
  const PL = PIECE_LIST;
  const ownB = F_OWNK + KCLASS[0][kB] * 2448, ownW = F_OWNK + KCLASS[1][kW] * 2448;
  let d1B = 0, d2B = 0, d1W = 0, d2W = 0, nr2B = 0, nr3B = 0, nr2W = 0, nr3W = 0, matB = 0;
  const eneB = F_ENEK + KCLASS[1][kW] * 2448, eneW = F_ENEK + KCLASS[0][kB] * 2448;
  let n = 0, np = 0;
  for (let i = 0; i < 81; i++) {
    const s = SQ81[i], p = b[s];
    if (p === 0) continue;
    const t = p & 15;
    if (p < 16) {
      F[n++] = F_PST + t * 45 + mirB[s];
      if (t === OU) continue;
      PL[np++] = s;
      F[n++] = F_MAT + t;
      matB += PV[t];
      if (IS_DEF[t]) { const dk = CHEB[s * NSQ + kB]; if (dk <= 1) d1B++; else if (dk === 2) d2B++; }
      { const de = CHEB[s * NSQ + kW]; if (de <= 2) nr2W += NEAR_W[t]; else if (de === 3) nr3W += NEAR_W[t]; }
      F[n++] = ownB + t * 153 + relB[s * NSQ + kB];
      F[n++] = eneB + t * 153 + relW[s * NSQ + kW];
      const vr = VRANK[t];
      const st = STEP_LIST[t];
      for (let j = 0; j < st.length; j++) { const q = s + st[j]; atkB[q]++; if (vr < mnB[q]) mnB[q] = vr; }
      const sl = SLIDE_LIST[t];
      if (sl.length) {
        let mob = 0;
        for (let j = 0; j < sl.length; j++) {
          const d = sl[j];
          let q = s + d;
          for (;;) {
            atkB[q]++;
            if (vr < mnB[q]) mnB[q] = vr;
            const pq = b[q];
            if (pq === 0) { mob++; q += d; continue; }
            if (OWNER[pq] === 1) mob++;
            break;
          }
        }
        F[n++] = F_MOB + t * 17 + (mob > 16 ? 16 : mob);
      }
    } else {
      F[n++] = ~(F_PST + t * 45 + mirW[s]);
      if (t === OU) continue;
      PL[np++] = s;
      F[n++] = ~(F_MAT + t);
      matB -= PV[t];
      if (IS_DEF[t]) { const dk = CHEB[s * NSQ + kW]; if (dk <= 1) d1W++; else if (dk === 2) d2W++; }
      { const de = CHEB[s * NSQ + kB]; if (de <= 2) nr2B += NEAR_W[t]; else if (de === 3) nr3B += NEAR_W[t]; }
      F[n++] = ~(ownW + t * 153 + relW[s * NSQ + kW]);
      F[n++] = ~(eneW + t * 153 + relB[s * NSQ + kB]);
      const vr = VRANK[t];
      const st = STEP_LIST[16 + t];
      for (let j = 0; j < st.length; j++) { const q = s + st[j]; atkW[q]++; if (vr < mnW[q]) mnW[q] = vr; }
      const sl = SLIDE_LIST[16 + t];
      if (sl.length) {
        let mob = 0;
        for (let j = 0; j < sl.length; j++) {
          const d = sl[j];
          let q = s + d;
          for (;;) {
            atkW[q]++;
            if (vr < mnW[q]) mnW[q] = vr;
            const pq = b[q];
            if (pq === 0) { mob++; q += d; continue; }
            if (OWNER[pq] === 0) mob++;
            break;
          }
        }
        F[n++] = ~(F_MOB + t * 17 + (mob > 16 ? 16 : mob));
      }
    }
  }
  const h = pos.hand;
  for (let t = FU; t <= KI; t++) {
    const base = HAND_BASE[t], mx = HAND_MAX[t];
    let cb = h[t]; if (cb > mx) cb = mx;
    for (let k = 0; k < cb; k++) F[n++] = base + k;
    let cw = h[8 + t]; if (cw > mx) cw = mx;
    for (let k = 0; k < cw; k++) F[n++] = ~(base + k);
  }
  n = kingFeatures(pos, BLACK, F, n);
  n = kingFeatures(pos, WHITE, F, n);
  KST[6] = d1B; KST[7] = d2B; KST[8] = nr2B; KST[9] = nr3B;
  KST[16] = d1W; KST[17] = d2W; KST[18] = nr2W; KST[19] = nr3W;
  DENSE_MAT[0] = matB;
  const stm = pos.stm;
  for (let i = 0; i < np; i++) {
    const s = PL[i], p = b[s], c = p >> 4;
    const atkT = c === 0 ? atkW : atkB, atkO = c === 0 ? atkB : atkW;
    if (atkT[s] > 0 && atkO[s] === 0) {
      const idx = (c === stm ? F_HANG_S : F_HANG_N) + (p & 15);
      F[n++] = c === 0 ? idx : ~idx;
    } else if ((c === 0 ? mnW[s] : mnB[s]) < VRANK[p & 15]) {
      const idx = (c === stm ? F_THR_S : F_THR_N) + (p & 15);
      F[n++] = c === 0 ? idx : ~idx;
    }
  }
  F[n++] = stm === BLACK ? F_TEMPO : ~F_TEMPO;
  return n;
}

const DENSE_BUF = new Float64Array(2 * ND);
// Correction network: ND -> NH -> 1, antisymmetric combination h(black) - h(white)
const NH = 24;
const NN_W1T = new Float64Array(NH * ND), NN_B1 = new Float64Array(NH), NN_W2 = new Float64Array(NH), NN_Z = new Float64Array(NH);
let NN_ON = false;
function nnHalf(x, off) {
  const z = NN_Z;
  for (let j = 0; j < NH; j++) z[j] = NN_B1[j];
  for (let i = 0; i < ND; i++) {
    const v = x[off + i];
    if (v === 0) continue;
    const r = i * NH;
    for (let j = 0; j < NH; j++) z[j] += NN_W1T[r + j] * v;
  }
  let out = 0;
  for (let j = 0; j < NH; j++) if (z[j] > 0) out += NN_W2[j] * z[j];
  return out;
}
function setNN(o) {
  if (!o) { NN_ON = false; return; }
  for (let j = 0; j < NH; j++) for (let i = 0; i < ND; i++) NN_W1T[i * NH + j] = o.W1[j * ND + i];
  NN_B1.set(o.B1); NN_W2.set(o.W2); NN_ON = true;
}

function evaluate(pos) {
  const F = EVAL_BUF;
  const n = extractFeatures(pos, F);
  let s = 0;
  for (let i = 0; i < n; i++) { const x = F[i]; s += x >= 0 ? WT[x] : -WT[~x]; }
  if (NN_ON) {
    denseFeatures(pos, DENSE_BUF);
    s += Math.round(nnHalf(DENSE_BUF, 0) - nnHalf(DENSE_BUF, ND));
  }
  return pos.stm === BLACK ? s : -s;
}
function setWeights(arr) { for (let i = 0; i < NPARAMS && i < arr.length; i++) WT[i] = arr[i]; }

// The evaluation split into parts that can be put into words (black's view; the parts sum to
// evaluate() for black). kingB: black king's safety, kingW: danger to white's king.
function evalParts(pos) {
  const F = EVAL_BUF, n = extractFeatures(pos, F);
  let mat = 0, place = 0, kingB = 0, kingW = 0, mob = 0, threat = 0, tempo = 0;
  for (let i = 0; i < n; i++) {
    const x = F[i], black = x >= 0, idx = black ? x : ~x, w = black ? WT[idx] : -WT[idx];
    if (idx < F_PST) mat += w;
    else if (idx < F_OWNK) { if (((idx - F_PST) / 45 | 0) === OU) { if (black) kingB += w; else kingW += w; } else place += w; }
    else if (idx < F_ENEK) { if (black) kingB += w; else kingW += w; }     // defenders around their own king
    else if (idx < F_MOB) { if (black) kingW += w; else kingB += w; }      // attackers near the enemy king
    else if (idx < F_KS_A) mob += w;
    else if (idx < F_HANG_S) { if (black) kingB += w; else kingW += w; }   // king-safety counts
    else if (idx === F_TEMPO) tempo += w;
    else threat += w;                                                      // hanging / threatened pieces
  }
  let nn = 0;
  if (NN_ON) { denseFeatures(pos, DENSE_BUF); nn = Math.round(nnHalf(DENSE_BUF, 0) - nnHalf(DENSE_BUF, ND)); }
  return { mat, place, kingB, kingW, mob, threat, tempo, nn };
}

// ---------------------------------------------------------------------------
// Transposition table
// ---------------------------------------------------------------------------
const INF = 32000, MATE = 31000, MATE_IN_MAX = 30000, SUPERIOR = 29000;
const MAX_SPLY = 128;
const NO_EVAL = -32768;
const B_UPPER = 1, B_LOWER = 2, B_EXACT = 3;
const now = (typeof performance !== 'undefined' && performance.now) ? () => performance.now() : () => Date.now();

class TTable {
  constructor(bits) {
    this.size = 1 << bits; this.mask = this.size - 1;
    this.key = new Int32Array(this.size);
    this.move = new Int32Array(this.size);
    this.score = new Int16Array(this.size);
    this.ev = new Int16Array(this.size);
    this.depth = new Int8Array(this.size);
    this.flag = new Uint8Array(this.size);
    this.age = 0;
  }
  clear() { this.key.fill(0); this.move.fill(0); this.flag.fill(0); this.depth.fill(0); }
  probe(lo, hi) {
    const i = (lo & this.mask) & ~1;
    if (this.key[i] === hi && this.flag[i] !== 0) return i;
    if (this.key[i + 1] === hi && this.flag[i + 1] !== 0) return i + 1;
    return -1;
  }
  store(lo, hi, move, score, ev, depth, bound) {
    const i0 = (lo & this.mask) & ~1;
    let i;
    if (this.key[i0] === hi && this.flag[i0] !== 0) i = i0;
    else if (this.key[i0 + 1] === hi && this.flag[i0 + 1] !== 0) i = i0 + 1;
    else {
      const v0 = this.flag[i0] === 0 ? -1000 : this.depth[i0] - ((this.flag[i0] >> 2) === this.age ? 0 : 64);
      const v1 = this.flag[i0 + 1] === 0 ? -1000 : this.depth[i0 + 1] - ((this.flag[i0 + 1] >> 2) === this.age ? 0 : 64);
      i = v0 <= v1 ? i0 : i0 + 1;
      this.move[i] = 0;
    }
    if (this.key[i] === hi && this.flag[i] !== 0 && bound !== B_EXACT && depth < this.depth[i] - 2 && (this.flag[i] >> 2) === this.age) {
      if (move !== 0 && this.move[i] === 0) this.move[i] = move;
      return;
    }
    if (move !== 0) this.move[i] = move;
    this.key[i] = hi; this.score[i] = score; this.ev[i] = ev; this.depth[i] = depth;
    this.flag[i] = bound | (this.age << 2);
  }
}
// Reads through to `base` but writes only to its own entries: lets the explanation search reuse what
// the main search learned without changing a single entry of the main table.
class OverlayTT extends TTable {
  constructor(base, bits) { super(bits); this.base = base; }
  probe(lo, hi) {
    const i = super.probe(lo, hi);
    if (i >= 0 || !this.base) return i;
    const b = this.base, j = b.probe(lo, hi);
    if (j < 0) return -1;
    const i0 = (lo & this.mask) & ~1;
    const k = this.flag[i0] === 0 ? i0 : this.flag[i0 + 1] === 0 ? i0 + 1 : (this.depth[i0] <= this.depth[i0 + 1] ? i0 : i0 + 1);
    this.key[k] = hi; this.move[k] = b.move[j]; this.score[k] = b.score[j]; this.ev[k] = b.ev[j]; this.depth[k] = b.depth[j];
    this.flag[k] = (b.flag[j] & 3) | (this.age << 2);
    return k;
  }
}
function valueToTT(v, ply) { return v >= MATE_IN_MAX ? v + ply : v <= -MATE_IN_MAX ? v - ply : v; }
function valueFromTT(v, ply) { return v >= MATE_IN_MAX ? v - ply : v <= -MATE_IN_MAX ? v + ply : v; }

const LMR = new Int8Array(64 * 64);
for (let d = 1; d < 64; d++) for (let m = 1; m < 64; m++) LMR[d * 64 + m] = Math.floor(0.6 + Math.log(d) * Math.log(m) / 2.2);

// ---------------------------------------------------------------------------
// df-pn mate solver
// ---------------------------------------------------------------------------
const DF_INF = 100000000;
const DF_MAX_DEPTH = 64;
class DfPn {
  constructor(bits) {
    this.size = 1 << bits; this.mask = this.size - 1;
    this.kLo = new Int32Array(this.size); this.kHi = new Int32Array(this.size);
    this.pn = new Int32Array(this.size); this.dn = new Int32Array(this.size);
    this.used = new Uint8Array(this.size);
    this.bufs = []; this.cLo = []; this.cHi = []; this.cRep = [];
    for (let i = 0; i < DF_MAX_DEPTH + 2; i++) {
      this.bufs.push(new Int32Array(700)); this.cLo.push(new Int32Array(700));
      this.cHi.push(new Int32Array(700)); this.cRep.push(new Uint8Array(700));
    }
    this.pathLo = new Int32Array(DF_MAX_DEPTH + 2); this.pathHi = new Int32Array(DF_MAX_DEPTH + 2);
    this.key = new Int32Array(2);
    this.nodes = 0; this.aborted = false;
  }
  clear() { this.used.fill(0); }
  find(lo, hi) {
    let i = lo & this.mask;
    for (let j = 0; j < 4; j++) {
      if (!this.used[i]) return -1;
      if (this.kLo[i] === lo && this.kHi[i] === hi) return i;
      i = (i + 1) & this.mask;
    }
    return -1;
  }
  put(lo, hi, pn, dn) {
    let i = lo & this.mask, v = -1;
    for (let j = 0; j < 4; j++) {
      if (!this.used[i] || (this.kLo[i] === lo && this.kHi[i] === hi)) { v = i; break; }
      i = (i + 1) & this.mask;
    }
    if (v < 0) {
      // replace the least informative of the 4 (unsolved with smallest pn+dn)
      let best = 1e18; i = lo & this.mask;
      for (let j = 0; j < 4; j++) {
        const solved = this.pn[i] === 0 || this.dn[i] === 0;
        const w = solved ? 1e17 : this.pn[i] + this.dn[i];
        if (w < best) { best = w; v = i; }
        i = (i + 1) & this.mask;
      }
    }
    this.used[v] = 1; this.kLo[v] = lo; this.kHi[v] = hi; this.pn[v] = pn; this.dn[v] = dn;
  }
  // Returns a mating move for the side to move, or 0
  solve(pos, maxNodes, timeMs, maxDepth) {
    this.nodes = 0; this.aborted = false;
    this.maxNodes = maxNodes; this.deadline = now() + timeMs;
    this.maxDepth = Math.min(maxDepth || 48, DF_MAX_DEPTH);
    this.pos = pos;
    if (pos.inCheck()) return 0;
    this.rootPly = pos.ply;
    this.mid(DF_INF - 1, DF_INF - 1, 0, true);
    if (this.aborted) return 0;
    const e = this.find(pos.hashLo, pos.hashHi);
    if (e < 0 || this.pn[e] !== 0) return 0;
    return this.provenChild(true);
  }
  provenChild(isOr) {
    const pos = this.pos, buf = new Int32Array(700);
    let n;
    if (isOr) n = pos.genChecks(buf, 0); else n = pos.genEvasions(buf, 0, false);
    let best = 0, bestScore = -1;
    for (let i = 0; i < n; i++) {
      const m = buf[i];
      if (isOr ? !pos.isLegal(m) : !pos.isLegalPseudo(m)) continue;
      pos.keyAfter(m, this.key);
      const e = this.find(this.key[0], this.key[1]);
      if (isOr) {
        if (e >= 0 && this.pn[e] === 0) return m;
      } else {
        // defender: prefer an unproven move, else any
        const sc = e < 0 ? 2 : (this.pn[e] === 0 ? 1 : 3);
        if (sc > bestScore) { bestScore = sc; best = m; }
      }
    }
    return best;
  }
  pv(maxLen) {
    const pos = this.pos, out = [];
    let isOr = true;
    for (let i = 0; i < maxLen; i++) {
      const m = this.provenChild(isOr);
      if (!m) break;
      out.push(m);
      pos.doMove(m);
      isOr = !isOr;
    }
    for (let i = out.length - 1; i >= 0; i--) pos.undoMove(out[i]);
    return out;
  }
  mid(thpn, thdn, depth, isOr) {
    const pos = this.pos;
    if ((++this.nodes & 1023) === 0 && now() > this.deadline) this.aborted = true;
    if (this.nodes >= this.maxNodes) this.aborted = true;
    if (this.aborted) return;
    const lo0 = pos.hashLo, hi0 = pos.hashHi;
    const moves = this.bufs[depth];
    let n = 0;
    if (isOr) {
      const raw = pos.genChecks(moves, 0);
      for (let i = 0; i < raw; i++) { const m = moves[i]; if (pos.isLegal(m)) moves[n++] = m; }
    } else {
      const raw = pos.genEvasions(moves, 0, false);
      for (let i = 0; i < raw; i++) { const m = moves[i]; if (pos.isLegalPseudo(m)) moves[n++] = m; }
    }
    if (n === 0) {
      if (isOr) this.put(lo0, hi0, DF_INF, 0);
      else this.put(lo0, hi0, 0, DF_INF);
      return;
    }
    if (depth >= this.maxDepth) { this.put(lo0, hi0, DF_INF, 0); return; }
    this.pathLo[depth] = lo0; this.pathHi[depth] = hi0;
    const cLo = this.cLo[depth], cHi = this.cHi[depth], rep = this.cRep[depth], key = this.key;
    for (let i = 0; i < n; i++) {
      pos.keyAfter(moves[i], key);
      cLo[i] = key[0]; cHi[i] = key[1];
      let r = 0;
      for (let j = depth; j >= 0; j--) if (this.pathLo[j] === key[0] && this.pathHi[j] === key[1]) { r = 1; break; }
      // also positions earlier in the game (repetition is never a win for the attacker)
      if (!r) for (let j = this.rootPly - 1, lim = Math.max(0, this.rootPly - 16); j >= lim; j--) {
        if (pos.histLo[j] === key[0] && pos.histHi[j] === key[1]) { r = 1; break; }
      }
      rep[i] = r;
    }
    for (;;) {
      let best = 0, bPn = DF_INF, bDn = DF_INF, second = DF_INF, sum = 0;
      if (isOr) {
        for (let i = 0; i < n; i++) {
          let cpn = 1, cdn = 1;
          if (rep[i]) { cpn = DF_INF; cdn = 0; }
          else { const e = this.find(cLo[i], cHi[i]); if (e >= 0) { cpn = this.pn[e]; cdn = this.dn[e]; } }
          sum += cdn; if (sum > DF_INF) sum = DF_INF;
          if (cpn < bPn) { second = bPn; bPn = cpn; bDn = cdn; best = i; }
          else if (cpn < second) second = cpn;
        }
        const pn = bPn, dn = sum;
        if (pn >= thpn || dn >= thdn) { this.put(lo0, hi0, pn, dn); return; }
        const cthpn = Math.min(thpn, second + 1);
        const cthdn = Math.min(DF_INF - 1, thdn - dn + bDn);
        const m = moves[best];
        pos.doMove(m);
        this.mid(cthpn, cthdn, depth + 1, false);
        pos.undoMove(m);
      } else {
        for (let i = 0; i < n; i++) {
          let cpn = 1, cdn = 1;
          if (rep[i]) { cpn = DF_INF; cdn = 0; }
          else { const e = this.find(cLo[i], cHi[i]); if (e >= 0) { cpn = this.pn[e]; cdn = this.dn[e]; } }
          sum += cpn; if (sum > DF_INF) sum = DF_INF;
          if (cdn < bDn) { second = bDn; bDn = cdn; bPn = cpn; best = i; }
          else if (cdn < second) second = cdn;
        }
        const pn = sum, dn = bDn;
        if (pn >= thpn || dn >= thdn) { this.put(lo0, hi0, pn, dn); return; }
        const cthdn = Math.min(thdn, second + 1);
        const cthpn = Math.min(DF_INF - 1, thpn - pn + bPn);
        const m = moves[best];
        pos.doMove(m);
        this.mid(cthpn, cthdn, depth + 1, true);
        pos.undoMove(m);
      }
      if (this.aborted) return;
    }
  }
}

// ---------------------------------------------------------------------------
// Searcher
// ---------------------------------------------------------------------------
const ATK_ORDER = new Int32Array([0, 1, 2, 3, 4, 7, 8, 5, 15, 6, 6, 6, 6, 9, 10, 0]);

class Searcher {
  constructor(ttBits) {
    this.pos = new Position();
    this.tt = new TTable(ttBits || 20);
    this.dfpn = null;
    this.hist = new Int32Array(64 * NSQ);
    this.killers = new Int32Array(MAX_SPLY * 2 + 8);
    this.counter = new Int32Array(32 * NSQ);
    this.moveBuf = []; this.scoreBuf = []; this.quietBuf = []; this.badBuf = [];
    for (let i = 0; i < MAX_SPLY + 4; i++) {
      this.moveBuf.push(new Int32Array(700)); this.scoreBuf.push(new Int32Array(700));
      this.quietBuf.push(new Int32Array(64));
      this.badBuf.push(new Int32Array(64));
    }
    this.pvTable = new Int32Array(MAX_SPLY * MAX_SPLY);
    this.pvLen = new Int32Array(MAX_SPLY + 2);
    this.evalStack = new Int32Array(MAX_SPLY + 4);
    this.curMove = new Int32Array(MAX_SPLY + 4);
    this.seeGain = new Int32Array(64); this.seeSq = new Int32Array(64); this.seePc = new Int32Array(64);
    this.mateBuf = new Int32Array(700);
    this.ecLo = new Int32Array(1 << 16); this.ecHi = new Int32Array(1 << 16); this.ecVal = new Int16Array(1 << 16);
    this.nodes = 0; this.stopped = false; this.deadline = Infinity; this.nodeLimit = Infinity;
    this.rootEffort = new Map();   // nodes spent on each root move (for explanations)
    this.contempt = 40; this.rootSide = 0; this.repLimit = 32;
    this.useMate1 = false;
    this.mate1Depth = 2;
    this.qsChecks = false;
    this.lmpImpBase = 4; this.lmpImpMul = 2; this.lmpBase = 2; this.lmpMul = 1;
    this.futBase = 120; this.futMul = 110;
    this.rfpMul = 100;
    this.lmr = new Int8Array(64 * 64);
    this.setLmrDiv(2.2);
  }

  setLmrDiv(div) {
    this.lmrDiv = div;
    for (let d = 1; d < 64; d++) for (let m = 1; m < 64; m++) this.lmr[d * 64 + m] = Math.floor(0.6 + Math.log(d) * Math.log(m) / div);
  }

  evaluate() {
    const pos = this.pos, i = pos.hashLo & 0xffff;
    if (this.ecLo[i] === pos.hashLo && this.ecHi[i] === pos.hashHi) return this.ecVal[i];
    let v = evaluate(pos);
    if (v > 20000) v = 20000; else if (v < -20000) v = -20000;
    this.ecLo[i] = pos.hashLo; this.ecHi[i] = pos.hashHi; this.ecVal[i] = v;
    return v;
  }

  checkTime() {
    if (this.nodes >= this.nodeLimit || now() >= this.deadline) this.stopped = true;
  }

  drawValue() { return this.pos.stm === this.rootSide ? -this.contempt : this.contempt; }

  histIndex(m) { return ((((m & 255) === 0) ? 32 : 0) + ((m >> 17) & 31)) * NSQ + ((m >> 8) & 255); }

  leastAttacker(sq, by) {
    const b = this.pos.board, o = by * 8;
    let bestSq = 0, bestV = 1e9;
    for (let k = 0; k < 8; k++) {
      const d = DIR8[k];
      let s = sq + d, p = b[s];
      if (p !== 0) {
        if (OWNER[p] === by && ((STEP_ATK[o + k] >> (p & 15)) & 1)) { const v = SEE_V[p & 15]; if (v < bestV) { bestV = v; bestSq = s; } }
        continue;
      }
      s += d;
      while ((p = b[s]) === 0) s += d;
      if (OWNER[p] === by && ((SLIDE_ATK[o + k] >> (p & 15)) & 1)) { const v = SEE_V[p & 15]; if (v < bestV) { bestV = v; bestSq = s; } }
    }
    if (bestV > SEE_V[KE]) {
      const kn = by === BLACK ? KE : (KE | 16), off = by === BLACK ? 1 : -1;
      if (b[sq + 21 * off] === kn) return sq + 21 * off;
      if (b[sq + 23 * off] === kn) return sq + 23 * off;
    }
    return bestSq;
  }

  see(m) {
    const b = this.pos.board;
    const from = m & 255, to = (m >> 8) & 255, pc = (m >> 17) & 31, cap = (m >> 22) & 31;
    const gain = this.seeGain, rsq = this.seeSq, rpc = this.seePc;
    let nr = 0;
    let onSq = (m & PROMO) ? (pc & 15) + 8 : (pc & 15);
    gain[0] = (cap ? EXV[cap & 15] : 0) + ((m & PROMO) ? PV[onSq] - PV[pc & 15] : 0);
    if (from !== 0) { rsq[nr] = from; rpc[nr++] = b[from]; b[from] = 0; }
    let side = this.pos.stm ^ 1, d = 0;
    for (;;) {
      const s = this.leastAttacker(to, side);
      if (s === 0) break;
      d++;
      gain[d] = EXV[onSq] - gain[d - 1];
      if (Math.max(-gain[d - 1], gain[d]) < 0) break;
      onSq = b[s] & 15;
      rsq[nr] = s; rpc[nr++] = b[s]; b[s] = 0;
      side ^= 1;
      if (d >= 60) break;
    }
    for (let i = nr - 1; i >= 0; i--) b[rsq[i]] = rpc[i];
    while (d > 0) { gain[d - 1] = -Math.max(-gain[d - 1], gain[d]); d--; }
    return gain[0];
  }

  updatePV(ply, m) {
    const base = ply * MAX_SPLY, nb = (ply + 1) * MAX_SPLY;
    this.pvTable[base + ply] = m;
    const len = this.pvLen[ply + 1];
    for (let j = ply + 1; j < len; j++) this.pvTable[base + j] = this.pvTable[nb + j];
    this.pvLen[ply] = len > ply + 1 ? len : ply + 1;
  }

  // ------------------------------------------------------------------------
  qsearch(alpha, beta, ply, qd) {
    const pos = this.pos;
    if ((++this.nodes & 1023) === 0) this.checkTime();
    if (this.stopped) return 0;
    const pvNode = beta - alpha > 1;
    if (pvNode) this.pvLen[ply] = ply;
    const us = pos.stm, them = us ^ 1;
    const inCheck = pos.attacked(pos.kingSq[us], them);
    pos.histCheck[pos.ply] = inCheck ? 1 : 0;
    if (ply >= MAX_SPLY - 2) return inCheck ? 0 : this.evaluate();
    const tt = this.tt, ti = tt.probe(pos.hashLo, pos.hashHi);
    let ttMove = 0, ttEv = NO_EVAL;
    if (ti >= 0) {
      const ts = valueFromTT(tt.score[ti], ply), tb = tt.flag[ti] & 3;
      if (!pvNode && (tb === B_EXACT || (tb === B_LOWER && ts >= beta) || (tb === B_UPPER && ts <= alpha))) return ts;
      ttMove = tt.move[ti]; ttEv = tt.ev[ti];
      if (ttMove && !pos.isPseudoLegal(ttMove)) ttMove = 0;
    }
    let best, standPat = 0;
    if (inCheck) best = -INF;
    else {
      standPat = ttEv !== NO_EVAL ? ttEv : this.evaluate();
      if (standPat >= beta) {
        if (ti < 0) tt.store(pos.hashLo, pos.hashHi, 0, valueToTT(standPat, ply), standPat, -1, B_LOWER);
        return standPat;
      }
      if (standPat > alpha) alpha = standPat;
      best = standPat;
    }
    const moves = this.moveBuf[ply], scores = this.scoreBuf[ply];
    let n;
    if (inCheck) n = pos.genEvasions(moves, 0, false);
    else {
      n = pos.gen(moves, 0, 1);
      // quiet promotions of rook / bishop / pawn near the top of qsearch
      if (qd === 0) {
        const tmp = this.moveBuf[MAX_SPLY + 1];
        const c2 = pos.gen(tmp, 0, 2);
        for (let i = 0; i < c2; i++) { const m = tmp[i]; if (m & PROMO) { const t = (m >> 17) & 15; if (t === HI || t === KA || t === FU) moves[n++] = m; } }
        if (this.qsChecks) {
          const tmp2 = this.moveBuf[MAX_SPLY + 2];
          const c3 = pos.genChecks(tmp2, 0);
          for (let i = 0; i < c3; i++) { const m = tmp2[i]; if (((m >> 22) & 31) === 0 && !(m & PROMO)) moves[n++] = m; }
        }
      }
    }
    for (let i = 0; i < n; i++) {
      const m = moves[i];
      if (m === ttMove) { scores[i] = 1 << 30; continue; }
      const cap = (m >> 22) & 31;
      let s = cap ? EXV[cap & 15] * 32 - ATK_ORDER[(m >> 17) & 15] : 0;
      if (m & PROMO) s += PV[((m >> 17) & 15) + 8] - PV[(m >> 17) & 15];
      if (!cap && inCheck) s = -100000 + (this.hist[this.histIndex(m)] >> 2);
      scores[i] = s;
    }
    let legal = 0, bestMove = 0;
    for (let i = 0; i < n; i++) {
      let bi = i, bs = scores[i];
      for (let j = i + 1; j < n; j++) if (scores[j] > bs) { bs = scores[j]; bi = j; }
      const m = moves[bi];
      if (bi !== i) { moves[bi] = moves[i]; scores[bi] = scores[i]; moves[i] = m; scores[i] = bs; }
      if (!inCheck) {
        const cap = (m >> 22) & 31;
        if ((cap || (m & PROMO)) && standPat + EXV[cap & 15] + ((m & PROMO) ? 600 : 0) + 120 <= alpha) continue;
        if (this.see(m) < 0) continue;
      }
      pos.doMove(m);
      if (pos.attacked(pos.kingSq[us], them)) { pos.undoMove(m); continue; }
      if ((m & 255) === 0 && ((m >> 17) & 15) === FU && pos.kingSq[them] === ((m >> 8) & 255) + (us === BLACK ? N : S)) {
        if (!pos.hasLegalMove()) { pos.undoMove(m); continue; }
      }
      legal++;
      this.curMove[ply] = m;
      const v = -this.qsearch(-beta, -alpha, ply + 1, qd + 1);
      pos.undoMove(m);
      if (this.stopped) return 0;
      if (v > best) {
        best = v;
        if (v > alpha) {
          bestMove = m;
          if (pvNode) this.updatePV(ply, m);
          if (v >= beta) break;
          alpha = v;
        }
      }
    }
    if (inCheck && legal === 0) return -MATE + ply;
    tt.store(pos.hashLo, pos.hashHi, bestMove, valueToTT(best, ply), inCheck ? NO_EVAL : standPat, -1,
      best >= beta ? B_LOWER : (pvNode && bestMove ? B_EXACT : B_UPPER));
    return best;
  }

  // ------------------------------------------------------------------------
  search(alpha, beta, depth, ply, cutNode) {
    const pos = this.pos;
    const pvNode = beta - alpha > 1;
    if (pvNode) this.pvLen[ply] = ply;
    if (depth <= 0) return this.qsearch(alpha, beta, ply, 0);
    if ((++this.nodes & 1023) === 0) this.checkTime();
    if (this.stopped) return 0;
    const us = pos.stm, them = us ^ 1;
    const inCheck = pos.attacked(pos.kingSq[us], them);
    pos.histCheck[pos.ply] = inCheck ? 1 : 0;
    const rootNode = ply === 0;
    if (!rootNode) {
      const rep = pos.repetition(this.repLimit);
      if (rep !== 0) return rep === 1 ? this.drawValue() : rep === 2 ? SUPERIOR : -SUPERIOR;
      if (ply >= MAX_SPLY - 4) return inCheck ? 0 : this.evaluate();
      if (-MATE + ply > alpha) { alpha = -MATE + ply; if (alpha >= beta) return alpha; }
      if (MATE - ply - 1 < beta) { beta = MATE - ply - 1; if (alpha >= beta) return alpha; }
    }
    const tt = this.tt, ti = tt.probe(pos.hashLo, pos.hashHi);
    let ttMove = 0, ttScore = 0, ttDepth = -100, ttBound = 0, ttEv = NO_EVAL;
    if (ti >= 0) {
      ttMove = tt.move[ti]; ttScore = valueFromTT(tt.score[ti], ply); ttDepth = tt.depth[ti];
      ttBound = tt.flag[ti] & 3; ttEv = tt.ev[ti];
      if (ttMove && !pos.isPseudoLegal(ttMove)) ttMove = 0;
      if (!pvNode && ttDepth >= depth &&
          (ttBound === B_EXACT || (ttBound === B_LOWER && ttScore >= beta) || (ttBound === B_UPPER && ttScore <= alpha))) {
        if (ttMove && ttScore >= beta && !((ttMove >> 22) & 31) && !(ttMove & PROMO)) this.updateKiller(ttMove, ply);
        return ttScore;
      }
    }

    // static evaluation
    let staticEval = NO_EVAL, ev = NO_EVAL;
    if (!inCheck) {
      staticEval = ttEv !== NO_EVAL ? ttEv : this.evaluate();
      ev = staticEval;
      if (ti >= 0 && ((ttBound === B_LOWER && ttScore > ev) || (ttBound === B_UPPER && ttScore < ev) || ttBound === B_EXACT) && Math.abs(ttScore) < MATE_IN_MAX) ev = ttScore;
      this.evalStack[ply] = staticEval;
    } else {
      this.evalStack[ply] = ply >= 2 ? this.evalStack[ply - 2] : 0;
    }
    const improving = !inCheck && ply >= 2 && staticEval > this.evalStack[ply - 2];

    // mate in one
    if (!rootNode && !inCheck && this.useMate1 && depth >= this.mate1Depth) {
      const mm = pos.mate1(this.mateBuf);
      if (mm) {
        const v = MATE - ply - 1;
        tt.store(pos.hashLo, pos.hashHi, mm, valueToTT(v, ply), staticEval, Math.min(depth + 6, 120), B_EXACT);
        if (pvNode) { this.pvLen[ply + 1] = ply + 1; this.updatePV(ply, mm); }
        return v;
      }
    }

    if (!pvNode && !inCheck) {
      // reverse futility pruning
      if (depth <= 6 && ev - (this.rfpMul * depth - (improving ? 50 : 0)) >= beta && ev < MATE_IN_MAX) return ev;
      // null move pruning
      if (depth >= 2 && ev >= beta && staticEval >= beta - 30 * depth + 150 && this.curMove[ply - 1] !== 0 && beta > -MATE_IN_MAX) {
        const R = 3 + (depth >> 2) + Math.min(3, ((ev - beta) / 200) | 0);
        pos.doNull();
        this.curMove[ply] = 0;
        let v = -this.search(-beta, -beta + 1, depth - R, ply + 1, !cutNode);
        pos.undoNull();
        if (this.stopped) return 0;
        if (v >= beta) {
          if (v >= MATE_IN_MAX) v = beta;
          if (depth < 10) return v;
          // verification at high depth
          const v2 = this.search(beta - 1, beta, depth - R, ply, false);
          if (v2 >= beta) return v;
        }
      }
      // razoring
      if (depth <= 2 && ev + 280 * depth <= alpha) {
        const v = this.qsearch(alpha, alpha + 1, ply, 0);
        if (v <= alpha) return v;
      }
    }

    // internal iterative reduction
    if (!ttMove && depth >= 6 && (pvNode || cutNode)) depth--;

    const moves = this.moveBuf[ply], scores = this.scoreBuf[ply];
    const k0 = this.killers[ply * 2], k1 = this.killers[ply * 2 + 1];
    const prev = ply > 0 ? this.curMove[ply - 1] : 0;
    const cm = prev ? this.counter[((prev >> 17) & 31) * NSQ + ((prev >> 8) & 255)] : 0;
    const hist = this.hist;
    const quiets = this.quietBuf[ply];
    let nq = 0, legal = 0, bestScore = -INF, bestMove = 0;
    const origAlpha = alpha;
    const lmpLimit = improving ? this.lmpImpBase + depth * depth * this.lmpImpMul : this.lmpBase + depth * depth * this.lmpMul;
    // staged move picker: TT move, good captures, killers, quiets+drops, bad captures (or evasions)
    const bad = this.badBuf[ply];
    let n = 0, idx = 0, nBad = 0, badIdx = 0, stage = ttMove ? 0 : (inCheck ? 10 : 1), kIdx = 0;
    let kt0 = 0, kt1 = 0, kt2 = 0;
    for (;;) {
      let m = 0;
      if (stage === 0) { m = ttMove; stage = inCheck ? 10 : 1; }
      else if (stage === 1 || stage === 2) {
        if (stage === 1) {
          n = pos.gen(moves, 0, 1);
          for (let j = 0; j < n; j++) {
            const mv = moves[j];
            scores[j] = EXV[(mv >> 22) & 15] * 32 - ATK_ORDER[(mv >> 17) & 15] + ((mv & PROMO) ? 400 : 0);
          }
          idx = 0; stage = 2;
        }
        while (idx < n) {
          let bi = idx, bs = scores[idx];
          for (let j = idx + 1; j < n; j++) if (scores[j] > bs) { bs = scores[j]; bi = j; }
          const mv = moves[bi];
          if (bi !== idx) { moves[bi] = moves[idx]; scores[bi] = scores[idx]; moves[idx] = mv; scores[idx] = bs; }
          idx++;
          if (mv === ttMove) continue;
          if (this.see(mv) < 0) { if (nBad < 64) bad[nBad++] = mv; continue; }
          m = mv; break;
        }
        if (m === 0) { stage = 3; continue; }
      } else if (stage === 3) {
        while (kIdx < 3 && m === 0) {
          const km = kIdx === 0 ? k0 : kIdx === 1 ? k1 : cm;
          kIdx++;
          if (km === 0 || km === ttMove || km === kt0 || km === kt1) continue;
          if (((km >> 22) & 31) !== 0 || !pos.isPseudoLegal(km)) continue;
          m = km;
          if (kIdx === 1) kt0 = km; else if (kIdx === 2) kt1 = km; else kt2 = km;
        }
        if (m === 0) { stage = 4; continue; }
      } else if (stage === 4 || stage === 5) {
        if (stage === 4) {
          const q0 = n;
          n = pos.gen(moves, n, 6);
          for (let j = q0; j < n; j++) {
            const mv = moves[j];
            scores[j] = (mv & PROMO) ? (1 << 27) + PV[((mv >> 17) & 15) + 8] : hist[this.histIndex(mv)];
          }
          idx = q0; stage = 5;
        }
        while (idx < n) {
          let bi = idx, bs = scores[idx];
          for (let j = idx + 1; j < n; j++) if (scores[j] > bs) { bs = scores[j]; bi = j; }
          const mv = moves[bi];
          if (bi !== idx) { moves[bi] = moves[idx]; scores[bi] = scores[idx]; moves[idx] = mv; scores[idx] = bs; }
          idx++;
          if (mv === ttMove || mv === kt0 || mv === kt1 || mv === kt2) continue;
          m = mv; break;
        }
        if (m === 0) { stage = 6; continue; }
      } else if (stage === 6) {
        if (badIdx >= nBad) break;
        m = bad[badIdx++];
      } else {
        if (stage === 10) {
          n = pos.genEvasions(moves, 0, false);
          for (let j = 0; j < n; j++) {
            const mv = moves[j], cp = (mv >> 22) & 31;
            scores[j] = cp ? (1 << 28) + EXV[cp & 15] * 32 - ATK_ORDER[(mv >> 17) & 15] : hist[this.histIndex(mv)];
          }
          idx = 0; stage = 11;
        }
        while (idx < n) {
          let bi = idx, bs = scores[idx];
          for (let j = idx + 1; j < n; j++) if (scores[j] > bs) { bs = scores[j]; bi = j; }
          const mv = moves[bi];
          if (bi !== idx) { moves[bi] = moves[idx]; scores[bi] = scores[idx]; moves[idx] = mv; scores[idx] = bs; }
          idx++;
          if (mv === ttMove) continue;
          m = mv; break;
        }
        if (m === 0) break;
      }
      const cap = (m >> 22) & 31;
      const quiet = !cap && !(m & PROMO);
      const gives = pos.givesCheck(m);
      if (!rootNode && bestScore > -MATE_IN_MAX && legal > 0 && !inCheck) {
        if (quiet && !gives) {
          if (depth <= 8 && legal >= lmpLimit) continue;
          const lmrDepth = depth - 1 - this.lmr[Math.min(depth, 63) * 64 + Math.min(legal, 63)];
          if (lmrDepth <= 6 && staticEval + this.futBase + this.futMul * lmrDepth <= alpha) continue;
          if (lmrDepth <= 5 && this.see(m) < -50 * lmrDepth * lmrDepth) continue;
        } else if (depth <= 6 && !gives && this.see(m) < -120 * depth) continue;
      }
      pos.doMove(m);
      if (pos.attacked(pos.kingSq[us], them)) { pos.undoMove(m); continue; }
      if (gives && (m & 255) === 0 && ((m >> 17) & 15) === FU) {
        if (!pos.hasLegalMove()) { pos.undoMove(m); continue; }
      }
      legal++;
      this.curMove[ply] = m;
      const n0 = this.nodes;
      let ext = 0;
      if (gives && ply < 2 * this.rootDepth && (depth <= 3 || this.seeAfterOk(m))) ext = 1;
      const newDepth = depth - 1 + ext;
      let v;
      if (legal === 1) {
        v = -this.search(-beta, -alpha, newDepth, ply + 1, pvNode ? false : !cutNode);
      } else {
        let r = 0;
        if (depth >= 3 && legal > (pvNode ? 2 : 1) && (quiet || cutNode)) {
          r = this.lmr[Math.min(depth, 63) * 64 + Math.min(legal, 63)];
          if (pvNode) r--;
          if (cutNode) r++;
          if (!improving) r++;
          if (m === k0 || m === k1 || m === cm) r--;
          if (quiet) r -= (hist[this.histIndex(m)] / 6000) | 0;
          if (gives) r--;
          if (inCheck) r--;
          if (r < 0) r = 0;
          if (r > newDepth - 1) r = newDepth - 1 > 0 ? newDepth - 1 : 0;
        }
        v = -this.search(-alpha - 1, -alpha, newDepth - r, ply + 1, true);
        if (v > alpha && r > 0) v = -this.search(-alpha - 1, -alpha, newDepth, ply + 1, !cutNode);
        if (v > alpha && v < beta && pvNode) v = -this.search(-beta, -alpha, newDepth, ply + 1, false);
      }
      pos.undoMove(m);
      if (this.stopped) return 0;
      if (rootNode) { this.rootScores.set(m, v); this.rootEffort.set(m, (this.rootEffort.get(m) || 0) + this.nodes - n0); }
      if (v > bestScore) {
        bestScore = v;
        if (v > alpha) {
          bestMove = m;
          if (rootNode) { this.iterBest = m; this.iterBestScore = v; }
          if (pvNode) this.updatePV(ply, m);
          if (v >= beta) {
            if (quiet) this.updateQuiet(m, ply, depth, quiets, nq, prev);
            break;
          }
          alpha = v;
        }
      }
      if (quiet && nq < 64) quiets[nq++] = m;
    }
    if (legal === 0) return -MATE + ply;
    tt.store(pos.hashLo, pos.hashHi, bestMove, valueToTT(bestScore, ply), staticEval, depth,
      bestScore >= beta ? B_LOWER : (pvNode && bestScore > origAlpha ? B_EXACT : B_UPPER));
    return bestScore;
  }

  // the move was just made: was it a safe check (not hanging the checking piece cheaply)?
  seeAfterOk(m) {
    const pos = this.pos;
    const to = (m >> 8) & 255;
    const us = pos.stm;            // opponent of mover
    // if the checking piece can be captured by a cheaper piece, don't extend
    const s = this.leastAttacker(to, us);
    if (s === 0) return true;
    const mover = pos.board[to] & 15;
    if ((pos.board[s] & 15) === OU) {
      // king can capture unless defended
      return pos.attacked(to, us ^ 1);
    }
    return SEE_V[pos.board[s] & 15] >= SEE_V[mover] && pos.attacked(to, us ^ 1);
  }

  updateKiller(m, ply) {
    if (this.killers[ply * 2] !== m) { this.killers[ply * 2 + 1] = this.killers[ply * 2]; this.killers[ply * 2] = m; }
  }

  updateQuiet(m, ply, depth, quiets, nq, prev) {
    this.updateKiller(m, ply);
    if (prev) this.counter[((prev >> 17) & 31) * NSQ + ((prev >> 8) & 255)] = m;
    const bonus = Math.min(depth * depth * 8 + 16, 2000);
    const h = this.hist;
    let idx = this.histIndex(m);
    h[idx] += bonus - ((h[idx] * bonus) / 16384 | 0);
    for (let i = 0; i < nq; i++) {
      idx = this.histIndex(quiets[i]);
      h[idx] -= bonus + ((h[idx] * bonus) / 16384 | 0);
    }
  }

  extractPV() {
    const out = [];
    for (let j = 0; j < this.pvLen[0]; j++) out.push(this.pvTable[j]);
    return out;
  }

  // ------------------------------------------------------------------------
  // Main entry: think on this.pos. opts: { timeMs, maxDepth, nodes, onInfo, mateNodes, noise }
  think(opts) {
    const pos = this.pos;
    const t0 = now();
    const timeMs = opts.timeMs || 1000;
    const maxDepth = Math.min(opts.maxDepth || 64, MAX_SPLY - 10);
    this.tt.age = (this.tt.age + 1) & 63;
    this.nodes = 0; this.stopped = false;
    this.deadline = t0 + timeMs;
    this.nodeLimit = opts.nodes || Infinity;
    this.rootSide = pos.stm;
    this.rootEffort = new Map();
    this.killers.fill(0);
    for (let i = 0; i < this.hist.length; i++) this.hist[i] = this.hist[i] >> 1;
    const inCheck = pos.inCheck();
    pos.histCheck[pos.ply] = inCheck ? 1 : 0;
    const buf = new Int32Array(700);
    const nm = inCheck ? pos.genEvasions(buf, 0, false) : pos.gen(buf, 0, 7);
    const rootMoves = [];
    for (let i = 0; i < nm; i++) if (pos.isLegal(buf[i])) rootMoves.push(buf[i]);
    const result = { move: 0, score: -MATE, depth: 0, nodes: 0, pv: [], mate: 0, time: 0 };
    if (rootMoves.length === 0) return result;
    result.move = rootMoves[0];
    if (rootMoves.length === 1 && !opts.analyze) {
      result.score = 0; result.pv = [rootMoves[0]];
      // quick estimate of the score
      this.rootDepth = 1;
      this.deadline = now() + Math.min(timeMs, 200);
      for (let d = 1; d <= 6 && !this.stopped; d++) {
        this.rootScores = new Map();
        const v = this.search(-INF, INF, d, 0, false);
        if (!this.stopped) result.score = v;
      }
      return result;
    }

    // mate search first
    if (opts.mateNodes && !inCheck) {
      if (!this.dfpn) this.dfpn = new DfPn(19);
      const mateTime = Math.min(timeMs * 0.15, opts.mateTimeCap || 1500);
      const mm = this.dfpn.solve(pos, opts.mateNodes, mateTime, 48);
      if (mm) {
        const pv = this.dfpn.pv(40);
        result.move = mm; result.score = MATE - pv.length; result.pv = pv.length ? pv : [mm];
        result.mate = pv.length; result.dfpn = true;
        result.nodes = this.dfpn.nodes; result.time = now() - t0;
        if (opts.onInfo) opts.onInfo({ depth: 0, score: result.score, mate: result.mate, nodes: result.nodes, pv: result.pv, time: result.time });
        return result;
      }
    }

    let bestMove = rootMoves[0], bestScore = 0, prevScore = 0;
    const soft = opts.analyze ? timeMs : timeMs * (opts.softRatio || 0.55);
    let stableCount = 0;
    const iters = [];                 // best move and score after each finished depth (for explanations)
    result.iters = iters; result.effort = this.rootEffort;
    for (let depth = 1; depth <= maxDepth; depth++) {
      this.rootDepth = depth;
      this.rootScores = new Map();
      this.iterBest = 0; this.iterBestScore = -INF;
      let delta = 30, alpha = -INF, beta = INF;
      if (depth >= 4 && Math.abs(prevScore) < MATE_IN_MAX) { alpha = prevScore - delta; beta = prevScore + delta; }
      let score;
      for (;;) {
        score = this.search(alpha, beta, depth, 0, false);
        if (this.stopped) break;
        if (score <= alpha) { beta = (alpha + beta) >> 1; alpha = Math.max(-INF, score - delta); }
        else if (score >= beta) { beta = Math.min(INF, score + delta); if (this.iterBest) bestMove = this.iterBest; }
        else break;
        delta += (delta >> 1) + 10;
        if (delta > 1200) { alpha = -INF; beta = INF; }
      }
      if (this.stopped) {
        if (this.iterBest && this.iterBestScore > -MATE_IN_MAX && (this.iterBestScore >= prevScore - 50 || this.iterBest === bestMove)) bestMove = this.iterBest;
        break;
      }
      const pv = this.extractPV();
      const newBest = pv.length ? pv[0] : (this.iterBest || bestMove);
      stableCount = newBest === bestMove ? stableCount + 1 : 0;
      bestMove = newBest; bestScore = score; prevScore = score;
      result.depth = depth; result.pv = pv.length ? pv : [bestMove];
      iters.push({ depth, move: newBest, score });
      const el = now() - t0;
      if (opts.onInfo) opts.onInfo({ depth, score, nodes: this.nodes, pv: result.pv, time: el, mate: score >= MATE_IN_MAX ? MATE - score : score <= -MATE_IN_MAX ? -(MATE + score) : 0 });
      if (Math.abs(score) >= MATE_IN_MAX && depth > (MATE - Math.abs(score)) + 4) break;
      if (el > soft) break;
      if (!opts.analyze && el > soft * (opts.easyRatio || 0.4) && stableCount >= (opts.easyStable || 6) && depth >= 10) break;
    }
    result.move = bestMove; result.score = bestScore; result.nodes = this.nodes; result.time = now() - t0;
    if (bestScore >= MATE_IN_MAX) result.mate = MATE - bestScore;
    else if (bestScore <= -MATE_IN_MAX) result.mate = -(MATE + bestScore);
    if (result.pv.length === 0 || result.pv[0] !== bestMove) result.pv = [bestMove];
    return result;
  }

  // Weak play: score every root move with a shallow search and pick with noise
  thinkWeak(opts) {
    const pos = this.pos;
    this.nodes = 0; this.stopped = false; this.deadline = now() + 5000; this.nodeLimit = Infinity;
    this.rootSide = pos.stm;
    this.useMate1 = false;
    const inCheck = pos.inCheck();
    pos.histCheck[pos.ply] = inCheck ? 1 : 0;
    const buf = new Int32Array(700);
    const nm = inCheck ? pos.genEvasions(buf, 0, false) : pos.gen(buf, 0, 7);
    let best = 0, bestV = -Infinity, bestRaw = 0;
    const depth = opts.depth || 1;
    this.rootDepth = depth;
    for (let i = 0; i < nm; i++) {
      const m = buf[i];
      if (!pos.isLegal(m)) continue;
      pos.doMove(m);
      this.curMove[0] = m;
      const v = depth <= 1 ? -this.qsearch(-INF, INF, 1, 0) : -this.search(-INF, INF, depth - 1, 1, false);
      pos.undoMove(m);
      // Box-Muller noise
      const u = Math.random() || 1e-9, w = Math.random();
      const noise = Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * w) * (opts.noise || 0);
      const mateV = Math.abs(v) >= MATE_IN_MAX;
      const vv = v + (mateV && opts.seeMates ? 0 : noise);
      if (vv > bestV) { bestV = vv; best = m; bestRaw = v; }
    }
    this.useMate1 = true;
    return { move: best, score: bestRaw, depth, nodes: this.nodes, pv: best ? [best] : [], mate: 0, time: 0 };
  }
}

// ---------------------------------------------------------------------------
// Opening book (USI lines; validated at load time)
// ---------------------------------------------------------------------------
const BOOK_LINES = [
  // Kakugawari
  '7g7f 8c8d 2g2f 4a3b 6i7h 8d8e 8h7g 3c3d 7i8h 2b7g+ 8h7g 3a2b 3i4h 2b3c 3g3f 7a6b 4h3g 6c6d',
  '2g2f 8c8d 7g7f 4a3b 6i7h 8d8e 8h7g 3c3d 7i8h 2b7g+ 8h7g 3a2b 3i3h 7a7b 4g4f 6c6d',
  // Yagura
  '7g7f 8c8d 7i6h 3c3d 6g6f 7a6b 5g5f 5c5d 3i4h 3a4b 4i5h 4a3b 6i7h 5a4a 5i6i 6a5b 5h6g 4b3c 6h7g 7c7d',
  '7g7f 8c8d 7i6h 3c3d 6h7g 7a6b 2g2f 6c6d 5g5f 6b6c 3i4h 3a4b 4i5h 4a3b 6i7h',
  // Aigakari
  '2g2f 8c8d 2f2e 8d8e 6i7h 4a3b 2e2d 2c2d 2h2d P*2c 2d2f 7a7b 7g7f',
  // Static rook vs. Shikenbisha (white ranging rook)
  '7g7f 3c3d 2g2f 4c4d 2f2e 2b3c 3i4h 8b4b 5i6h 5a6b 6h7h 6b7b 4i5h 7b8b 5g5f 7a7b',
  '2g2f 3c3d 7g7f 4c4d 3i4h 8b4b 5i6h 5a6b 6h7h 6b7b 2f2e 2b3c 4i5h 7b8b',
  // Black Shikenbisha
  '7g7f 3c3d 6g6f 8c8d 2h6h 8d8e 8h7g 7a6b 5i4h 5a4b 4h3h 4b3b 3h2h 3a4b 3i3h',
  // Black central rook
  '5g5f 8c8d 2h5h 8d8e 7g7f 3c3d 8h7g 7a6b 5i4h 5a4b 4h3h 4b3b 3h2h',
  // White replies to 2g2f / 7g7f with static rook
  '7g7f 8c8d 6i7h 8d8e 8h7g 3c3d 7i8h 2b7g+ 8h7g 3a2b 2g2f 7a7b',
  '2g2f 3c3d 7g7f 8c8d 2f2e 8d8e 6i7h 4a3b 2e2d 2c2d 2h2d 8e8f 8g8f 8b8f 2d3d 2b3c',
];
let BOOK = null;
function buildBook() {
  BOOK = new Map();
  const pos = new Position();
  for (const line of BOOK_LINES) {
    pos.setSFEN(START_SFEN);
    for (const u of line.split(/\s+/)) {
      const m = pos.parseUSI(u);
      if (!m) break;
      const k = pos.key();
      let e = BOOK.get(k);
      if (!e) { e = []; BOOK.set(k, e); }
      const f = e.find(x => x.u === u);
      if (f) f.w++; else e.push({ u, w: 1 });
      pos.doMove(m);
    }
  }
}
function bookMove(pos) {
  if (!BOOK) buildBook();
  const e = BOOK.get(pos.key());
  if (!e || !e.length) return 0;
  let total = 0;
  for (const x of e) total += x.w;
  let r = Math.random() * total;
  for (const x of e) { r -= x.w; if (r <= 0) return pos.parseUSI(x.u); }
  return pos.parseUSI(e[0].u);
}

defaultWeights();

// ---- trained parameters (fitted to YaneuraOu+SuishoPetite analysis of ~370k positions) ----
function b64Int16(b) { const s = atob(b); const n = s.length >> 1; const o = new Int16Array(n); for (let i = 0; i < n; i++) o[i] = ((s.charCodeAt(2 * i) | (s.charCodeAt(2 * i + 1) << 8)) << 16) >> 16; return o; }
function b64Float32(b) { const s = atob(b); const u = new Uint8Array(s.length); for (let i = 0; i < s.length; i++) u[i] = s.charCodeAt(i); return new Float32Array(u.buffer); }
setWeights(b64Int16('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'));
const NN_W1_DATA = b64Float32('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');
const NN_B1_DATA = b64Float32('oXYAQF/+xroLdGI/q6IswM7J8T8Tij+/A+r6u5IhK0CgUoI/SuyePtVjAEDrjgM+xRDpv7TZXL+dWCvAsyi6vyabBsAdzPo/jCGfPofgCz+kmBk/lLyIv/tnuT4Lw7A6');
const NN_W2_DATA = b64Float32('t3uuwnaDRkIkgSbCs2Qrwjv4zEFjkA/CtDMswgH4DUJKiQhCmJUMwnqtOkJexAnCZD4HQgY9IUIIbmFC/DELQsccQsLENF5Ca10dwojaNkKTJiRCErg9wngIMcLAQefB');
setNN({ W1: NN_W1_DATA, B1: NN_B1_DATA, W2: NN_W2_DATA });
Object.assign(api, { denseFeatures, setNN, ND, NH, evaluate, evaluateHand, extractFeatures, setWeights, defaultWeights, WT, FEAT, NPARAMS, Searcher, DfPn, TTable, bookMove, buildBook, BOOK_LINES, MATE, MATE_IN_MAX, INF, EVAL_PARAMS });

// ---------------------------------------------------------------------------
// Explanation analysis: why the chosen move beat the other candidates.
// It starts only after the move has been sent and runs in short slices, on a searcher of its own
// that reads the main search's table through an overlay and never writes to the main searcher's
// state — so the move, its strength and its thinking time are exactly what they would be without it.
// ---------------------------------------------------------------------------
const EX_SLICE_MS = 120, EX_CANDS = 5;
const EX_COPY = ['contempt', 'repLimit', 'useMate1', 'mate1Depth', 'qsChecks', 'lmpImpBase', 'lmpImpMul', 'lmpBase', 'lmpMul', 'futBase', 'futMul', 'rfpMul'];
const SEE_CTX = { pos: null, seeGain: new Int32Array(64), seeSq: new Int32Array(64), seePc: new Int32Array(64), leastAttacker: Searcher.prototype.leastAttacker };
function seeMove(pos, m) { SEE_CTX.pos = pos; return Searcher.prototype.see.call(SEE_CTX, m); }

// Squares the piece on `s` attacks
function attacksFrom(pos, s) {
  const b = pos.board, p = b[s], out = [];
  if (p === 0 || p === WALL) return out;
  const st = STEP_LIST[(p >> 4) * 16 + (p & 15)], sl = SLIDE_LIST[(p >> 4) * 16 + (p & 15)];
  for (let j = 0; j < st.length; j++) { const q = s + st[j]; if (q >= 0 && q < NSQ && b[q] !== WALL) out.push(q); }
  for (let j = 0; j < sl.length; j++) { let q = s + sl[j]; while (b[q] !== WALL) { out.push(q); if (b[q] !== 0) break; q += sl[j]; } }
  return out;
}

function legalRoot(pos) {
  const buf = new Int32Array(700);
  const n = pos.inCheck() ? pos.genEvasions(buf, 0, false) : pos.gen(buf, 0, 7);
  const out = [];
  for (let i = 0; i < n; i++) if (pos.isLegal(buf[i])) out.push(buf[i]);
  return out;
}
function pvAt(s, ply) { const out = []; for (let j = ply; j < s.pvLen[ply]; j++) out.push(s.pvTable[ply * MAX_SPLY + j]); return out; }

let exJob = null;
function cancelExplain(flush) {
  const j = exJob;
  if (!j) return;
  exJob = null; j.cancelled = true;
  if (flush) exPublish(j, true);
}

function startExplain(main, res, msg, post) {
  cancelExplain(false);
  let ex = main.explainer;
  if (!ex) { ex = main.explainer = new Searcher(1); ex.tt = new OverlayTT(main.tt, 19); ex.dfpn = new DfPn(16); }
  ex.tt.base = main.tt; ex.tt.age = (ex.tt.age + 1) & 63;
  for (const k of EX_COPY) ex[k] = main[k];
  if (ex.lmrDiv !== main.lmrDiv) ex.setLmrDiv(main.lmrDiv);
  ex.hist.set(main.hist); ex.counter.set(main.counter); ex.killers.set(main.killers);
  ex.pos.copyFrom(main.pos);
  ex.rootSide = ex.pos.stm; ex.nodes = 0; ex.nodeLimit = Infinity;
  ex.dfpn.clear();
  const t0 = now(), budget = Math.max(300, msg.explain.timeMs || 3000);
  const job = { ex, res, id: msg.id, post, t0, budget, end: t0 + budget, sliceEnd: 0, cancelled: false,
    depth: 0, rootMoves: [], inCheck: ex.pos.inCheck(), cands: [{ m: res.move }], rootThreat: null, moveThreat: null };
  job.gen = explainSteps(job);
  exJob = job;
  setTimeout(() => exSlice(job), 0);
}

function exSlice(job) {
  if (job.cancelled) return;
  job.sliceEnd = now() + EX_SLICE_MS;
  for (;;) {
    if (job.gen.next().done) { if (exJob === job) exJob = null; exPublish(job, false); return; }
    if (now() >= job.sliceEnd) break;
  }
  setTimeout(() => exSlice(job), 0);
}

// Runs one search of the job. If the time slice ends first, it is retried in the next slice
// (the table keeps the work already done). Gives null once the phase's own time is up.
function* exRun(job, phaseEnd, fn) {
  const ex = job.ex, end = Math.min(phaseEnd, job.end);
  for (;;) {
    ex.stopped = false;
    ex.deadline = Math.min(end, job.sliceEnd);
    const v = fn();
    if (!ex.stopped) return v;
    if (now() >= end) return null;
    yield;
  }
}

function exChild(ex, m, d, a, b) {
  const pos = ex.pos;
  pos.doMove(m);
  ex.curMove[0] = m; ex.rootDepth = d;
  const v = d <= 1 ? -ex.qsearch(-b, -a, 1, 0) : -ex.search(-b, -a, d - 1, 1, false);
  pos.undoMove(m);
  return v;
}

// Exact score and line of one candidate at depth d (aspiration around its previous score)
function* exAspire(job, c, d) {
  let delta = 40, a = -INF, b = INF;
  if (d >= 3 && c.last !== undefined && Math.abs(c.last) < MATE_IN_MAX) { a = c.last - delta; b = c.last + delta; }
  for (;;) {
    const v = yield* exRun(job, job.end, () => exChild(job.ex, c.m, d, a, b));
    if (v === null) return null;
    if (v <= a) a = Math.max(-INF, v - delta);
    else if (v >= b) b = Math.min(INF, v + delta);
    else { c.cur = { v, pv: [c.m].concat(pvAt(job.ex, 1)) }; return v; }
    delta += delta;
    if (delta > 1000) { a = -INF; b = INF; }
  }
}

// What the side to move could do if the other side passed: after `m` (our move) it is our threat,
// with m = 0 at the root it is the opponent's threat against us.
function* exThreat(job, m, phaseEnd) {
  const ex = job.ex, pos = ex.pos;
  if (m) pos.doMove(m);
  pos.doNull();
  ex.curMove[0] = 0;
  const st = ex.evaluate();
  let best = null;
  for (let d = 1; d <= 8; d++) {
    ex.rootDepth = d;
    const v = yield* exRun(job, phaseEnd, () => ex.search(-INF, INF, d, 1, false));
    if (v === null) break;
    best = { pv: pvAt(ex, 1), v };
    if (Math.abs(v) >= MATE_IN_MAX) break;
  }
  let mate = 0;
  if (best && !pos.inCheck() && ex.dfpn.solve(pos, 20000, Math.max(20, Math.min(150, phaseEnd - now())), 31)) mate = ex.dfpn.pv(31).length || 1;
  pos.undoNull();
  if (m) pos.undoMove(m);
  return best && { pv: best.pv, v: best.v, st, mate };
}

function* explainSteps(job) {
  const ex = job.ex, pos = ex.pos, res = job.res, M = res.move, iters = res.iters || [];
  const roots = job.rootMoves = legalRoot(pos);
  if (roots.length <= 1 || res.dfpn || Math.abs(res.score) >= MATE_IN_MAX || roots.indexOf(M) < 0) return;
  // 1. every legal move at a glance (captures resolved): shows which moves look tempting
  const sh = new Map();
  yield* exRun(job, job.end, () => {
    for (const m of roots) {
      if (sh.has(m)) continue;
      pos.doMove(m); ex.curMove[0] = m;
      const v = -ex.qsearch(-INF, INF, 1, 0);
      pos.undoMove(m);
      if (ex.stopped) break;
      sh.set(m, v);
    }
    return 0;
  });
  // 2. candidates: the chosen move, the moves the main search worked hardest to refute,
  //    its earlier favourites and the moves that look best at a glance
  const eff = res.effort || new Map();
  let total = 0;
  for (const v of eff.values()) total += v;
  const pick = [M];
  const add = (m) => { if (m && pick.length < EX_CANDS && pick.indexOf(m) < 0 && roots.indexOf(m) >= 0) pick.push(m); };
  const byEffort = roots.filter(m => m !== M).sort((a, b) => (eff.get(b) || 0) - (eff.get(a) || 0) || (sh.get(b) || 0) - (sh.get(a) || 0));
  add(byEffort[0]); add(byEffort[1]);
  for (let i = iters.length - 1, k = 0; i >= 0 && k < 2; i--) if (iters[i].depth >= 4 && iters[i].move !== M && pick.indexOf(iters[i].move) < 0) { add(iters[i].move); k++; }
  const byGlance = roots.filter(m => m !== M).sort((a, b) => (sh.get(b) || -INF) - (sh.get(a) || -INF));
  for (let i = 0, k = 0; i < byGlance.length && k < 2; i++) {
    const m = byGlance[i];
    if (pick.indexOf(m) < 0 && sh.has(m) && sh.get(m) >= (sh.get(M) || 0) - 80) { add(m); k++; }
  }
  for (const m of byEffort) add(m);
  job.cands = pick.map(m => ({ m, sh: sh.has(m) ? sh.get(m) : null, ef: total ? (eff.get(m) || 0) / total : 0 }));
  yield;
  // 3. the opponent's threat against us, and what our move threatens
  if (!job.inCheck) job.rootThreat = yield* exThreat(job, 0, now() + job.budget * 0.08);
  if (!pos.givesCheck(M)) job.moveThreat = yield* exThreat(job, M, now() + job.budget * 0.08);
  // 4. every candidate read to the same depth (exact score and line), deeper until the time is up
  const maxD = Math.max(2, Math.min(res.depth || 64, MAX_SPLY - 12));
  for (let d = 1; d <= maxD; d++) {
    for (const c of job.cands) {
      if ((yield* exAspire(job, c, d)) === null) return;
      yield;
    }
    for (const c of job.cands) { c.done = c.cur; c.last = c.cur.v; }
    job.depth = d;
    if (now() >= job.end) return;
  }
}

function exPublish(job, partial) {
  const u = moveToUSI, res = job.res;
  const thr = (t) => t && { pv: t.pv.map(u), v: t.v, st: t.st, mate: t.mate };
  job.post({ type: 'explain', id: job.id, partial, data: {
    depth: job.depth, mainDepth: res.depth, mainScore: res.score, mate: res.mate, dfpn: !!res.dfpn,
    legal: job.rootMoves.length, inCheck: job.inCheck, chosen: u(res.move), mainPv: res.pv.map(u),
    iters: (res.iters || []).map(it => [it.depth, u(it.move), it.score]),
    cands: job.cands.map(c => ({ m: u(c.m), s: c.done ? c.done.v : null, pv: c.done ? c.done.pv.map(u) : [], sh: c.sh, ef: c.ef })),
    rootThreat: thr(job.rootThreat), moveThreat: thr(job.moveThreat), nodes: job.ex.nodes, time: Math.round(now() - job.t0) } });
}

// ---------------------------------------------------------------------------
// Request handling (shared by the Web Worker and the main-thread fallback)
// ---------------------------------------------------------------------------
function handleGo(searcher, msg, post) {
  cancelExplain(true);   // a new request ends an explanation still in progress (sending what it has)
  const pos = searcher.pos;
  pos.setSFEN(msg.sfen || START_SFEN);
  for (const u of (msg.moves || [])) {
    const m = pos.parseUSI(u);
    if (!m) break;
    pos.doMove(m);
    pos.histCheck[pos.ply] = pos.inCheck() ? 1 : 0;
  }
  let res = null;
  if (msg.book) {
    const bm = bookMove(pos);
    if (bm) res = { move: bm, score: 0, depth: 0, nodes: 0, pv: [bm], book: true, mate: 0, time: 0 };
  }
  if (!res) {
    if (msg.weak) res = searcher.thinkWeak({ depth: msg.weak.depth, noise: msg.weak.noise, seeMates: msg.weak.seeMates });
    else res = searcher.think({
      timeMs: msg.timeMs || 1000, maxDepth: msg.maxDepth || 64, mateNodes: msg.mateNodes || 0, nodes: msg.nodes,
      softRatio: msg.softRatio, easyRatio: msg.easyRatio, easyStable: msg.easyStable, mateTimeCap: msg.mateTimeCap,
      onInfo: (info) => post({ type: 'info', id: msg.id, depth: info.depth, score: info.score, mate: info.mate, nodes: info.nodes, time: info.time, pv: info.pv.map(moveToUSI) })
    });
  }
  post({ type: 'bestmove', id: msg.id, move: res.move ? moveToUSI(res.move) : 'resign', score: res.score, mate: res.mate, depth: res.depth, nodes: res.nodes, time: res.time, pv: res.pv.map(moveToUSI), book: !!res.book, dfpn: !!res.dfpn });
  // only now, with the move already sent, work out why it was chosen
  if (msg.explain && res.move && !res.book && !msg.weak) startExplain(searcher, res, msg, post);
}
Object.assign(api, { handleGo, cancelExplain, evalParts, seeMove, attacksFrom, OverlayTT });

if (typeof importScripts === 'function' && typeof document === 'undefined' && typeof self !== 'undefined') {
  let searcher = null;
  self.onmessage = function (ev) {
    const msg = ev.data;
    if (msg.type === 'go') {
      if (!searcher || (msg.ttBits && searcher.tt.size !== (1 << msg.ttBits))) searcher = new Searcher(msg.ttBits || 20);
      handleGo(searcher, msg, (x) => self.postMessage(x));
    } else if (msg.type === 'cancel-explain') {
      cancelExplain(false);
    } else if (msg.type === 'ping') {
      self.postMessage({ type: 'pong' });
    }
  };
}

if (typeof module !== 'undefined' && module.exports) module.exports = api;
else root.ShogiEngine = api;
// On a page, keep this file's own source so the page can start it as a Blob worker
// (needed when index.html is opened directly from disk, where file workers are blocked).
if (typeof document !== 'undefined') api.workerSource = '(' + shogiEngineFactory.toString() + ')(self);';
})(typeof self !== 'undefined' ? self : this);
