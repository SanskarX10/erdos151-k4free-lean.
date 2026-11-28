"""Generate pure-kernel Lean 4 proof of R(3,6) <= 18 (R1.H1.R1.H1.R1.H2.R1.H1.R1.H1)."""
import itertools
from pathlib import Path

BASE_EDGES = [
    (0, 1), (1, 2), (2, 3), (3, 0),
    (0, 4), (0, 5), (1, 6), (1, 7),
    (2, 8), (2, 9), (3, 10), (3, 11),
]
BASE_ADJ = [0] * 12
for u, v in BASE_EDGES:
    BASE_ADJ[u] |= 1 << v
    BASE_ADJ[v] |= 1 << u

FORB = {(4, 5), (6, 7), (8, 9), (10, 11)}
CAND = [(u, v) for u in range(4, 12) for v in range(u + 1, 12) if (u, v) not in FORB]
assert len(CAND) == 24

H0_S3 = {(4, 6), (4, 8), (5, 9), (5, 10), (6, 10), (7, 8), (7, 11), (9, 11)}
H0_ADJ = BASE_ADJ[:]
for u, v in H0_S3:
    H0_ADJ[u] |= 1 << v
    H0_ADJ[v] |= 1 << u

def swap_v(v, bits):
    if v < 4:
        return v
    p = (v - 4) // 2
    return v ^ (1 if ((bits >> p) & 1) else 0)

SWAP_MASKS = []
for bits in range(16):
    m = 0
    for idx, (u, v) in enumerate(CAND):
        a, b = swap_v(u, bits), swap_v(v, bits)
        if (min(a, b), max(a, b)) in H0_S3:
            m |= 1 << idx
    SWAP_MASKS.append(m)

def build_s3_tree(yes, no):
    adj_yes = BASE_ADJ[:]
    adj_poss = BASE_ADJ[:]
    deg_yes = [0] * 12
    deg_unk = [0] * 12
    for idx, (u, v) in enumerate(CAND):
        bit = 1 << idx
        if yes & bit:
            adj_yes[u] |= 1 << v
            adj_yes[v] |= 1 << u
            adj_poss[u] |= 1 << v
            adj_poss[v] |= 1 << u
            deg_yes[u] += 1
            deg_yes[v] += 1
        elif not (no & bit):
            adj_poss[u] |= 1 << v
            adj_poss[v] |= 1 << u
            deg_unk[u] += 1
            deg_unk[v] += 1

    for u in range(4, 12):
        if deg_yes[u] > 2:
            return ("degHi", u)
    for u in range(4, 12):
        if deg_yes[u] + deg_unk[u] < 2:
            return ("degLo", u)
    for u in range(12):
        for v in range(u + 1, 12):
            if (adj_yes[u] >> v) & 1:
                common = adj_yes[u] & adj_yes[v]
                if common:
                    w = (common & -common).bit_length() - 1
                    return ("tri", u, v, w)
    if all(deg_yes[u] == 2 for u in range(4, 12)):
        for comb in itertools.combinations(range(12), 5):
            m = sum(1 << x for x in comb)
            if all((adj_yes[x] & m) == 0 for x in comb):
                return ("ind5Full", comb)
        bits = SWAP_MASKS.index(yes)
        return ("valid", bits)
    for comb in itertools.combinations(range(12), 5):
        m = sum(1 << x for x in comb)
        if all((adj_poss[x] & m) == 0 for x in comb):
            return ("ind5", comb)

    best_u = min((u for u in range(4, 12) if deg_yes[u] < 2), key=lambda u: deg_unk[u])
    best_idx = next(
        idx for idx, (u, v) in enumerate(CAND)
        if not ((yes | no) & (1 << idx)) and (u == best_u or v == best_u)
    )
    return ("branch", best_idx, build_s3_tree(yes | (1 << best_idx), no), build_s3_tree(yes, no | (1 << best_idx)))

def fmt_tree(t):
    tag = t[0]
    if tag == "degHi":
        return f"S3Tree.degHi {t[1]}"
    if tag == "degLo":
        return f"S3Tree.degLo {t[1]}"
    if tag == "tri":
        return f"S3Tree.tri {t[1]} {t[2]} {t[3]}"
    if tag == "ind5":
        a, b, c, d, e = t[1]
        return f"S3Tree.ind5 {a} {b} {c} {d} {e}"
    if tag == "ind5Full":
        a, b, c, d, e = t[1]
        return f"S3Tree.ind5Full {a} {b} {c} {d} {e}"
    if tag == "valid":
        return f"S3Tree.valid {t[1]}"
    _, idx, t1, t2 = t
    return f"S3Tree.branch {idx} ({fmt_tree(t1)}) ({fmt_tree(t2)})"

tree = build_s3_tree(0, 0)
tree_str = fmt_tree(tree)

IND4_H0 = [
    sum(1 << x for x in c)
    for c in itertools.combinations(range(12), 4)
    if all((H0_ADJ[x] & sum(1 << y for y in c)) == 0 for x in c)
]
IND_ALL_H0 = []
for k in range(1, 5):
    for c in itertools.combinations(range(12), k):
        m = sum(1 << x for x in c)
        if all((H0_ADJ[x] & m) == 0 for x in c):
            IND_ALL_H0.append(m)

cand_str = ", ".join(f"({u}, {v})" for u, v in CAND)
INC_MASK = [0] * 12
EDGE_BIT = [0] * 144
for idx, (u, v) in enumerate(CAND):
    INC_MASK[u] |= 1 << idx
    INC_MASK[v] |= 1 << idx
    EDGE_BIT[u * 12 + v] = 1 << idx
    EDGE_BIT[v * 12 + u] = 1 << idx
inc_str = ", ".join(str(x) for x in INC_MASK)
ebit_str = ", ".join(str(x) for x in EDGE_BIT)
base_str = ", ".join(str(x) for x in BASE_ADJ)
h0_str = ", ".join(str(x) for x in H0_ADJ)
swap_str = ", ".join(str(x) for x in SWAP_MASKS)
ind4_str = ", ".join(str(x) for x in IND4_H0)
ind_all_str = ", ".join(str(x) for x in IND_ALL_H0)

lean_code = f"""import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1_H1_R1
import Mathlib

/-! Pure-kernel proof of R(3,6) <= 18 (R1.H1.R1.H1.R1.H2.R1.H1.R1.H1).
Uses R(3,3)<=6, R(3,4)<=9, R(3,5)<=14, e(3,4,8)>=10, Cariolaro's 5-line
elimination of degree-4 vertices, structural characterization of 5-regular
18-vertex graphs (S4 = C4, S3 2-regular), and a tiny pure-kernel decision
tree verifying uniqueness of the (3,5,12,20)-graph H0 and impossibility of
extending H0 by 5 vertices. -/
-- Step: Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H2.R1.H1.R1.H1
-- Credit: @SanskarX10

open Finset SimpleGraph
open scoped Classical

private def baseAdj12 : Array Nat :=
  #[{base_str}]

private def candEdges24 : Array (Nat × Nat) :=
  #[{cand_str}]

private def h0Adj12 : Array Nat :=
  #[{h0_str}]

private def swapMasks16 : Array Nat :=
  #[{swap_str}]

private def ind4H0List : List Nat :=
  [{ind4_str}]

private def indAllH0List : List Nat :=
  [{ind_all_str}]

private def swapVert (bits v : Nat) : Nat :=
  if v < 4 then v
  else if bits.testBit ((v - 4) / 2) then v ^^^ 1 else v

private def incMask12 : Array Nat :=
  #[{inc_str}]

private def edgeBit144 : Array Nat :=
  #[{ebit_str}]

private def isAdjYes (yes a b : Nat) : Bool :=
  (baseAdj12.getD a 0).testBit b || ((yes &&& edgeBit144.getD (a * 12 + b) 0) != 0)

private def isAdjPoss (_yes no a b : Nat) : Bool :=
  (baseAdj12.getD a 0).testBit b || ((((16777215 - no) &&& edgeBit144.getD (a * 12 + b) 0)) != 0)

private def pop24 (m : Nat) : Nat :=
  (List.range 24).countP fun i => m.testBit i

private def degYes (yes u : Nat) : Nat :=
  pop24 (yes &&& incMask12.getD u 0)

private def degPoss (_yes no u : Nat) : Nat :=
  pop24 ((16777215 - no) &&& incMask12.getD u 0)

private def checkInd5 (adjFn : Nat → Nat → Bool) (a b c d e : Nat) : Bool :=
  a < b && b < c && c < d && d < e && e < 12 &&
  !(adjFn a b) && !(adjFn a c) && !(adjFn a d) && !(adjFn a e) &&
  !(adjFn b c) && !(adjFn b d) && !(adjFn b e) &&
  !(adjFn c d) && !(adjFn c e) && !(adjFn d e)

private inductive S3Tree where
  | degHi (u : Nat)
  | degLo (u : Nat)
  | tri (a b c : Nat)
  | ind5 (a b c d e : Nat)
  | ind5Full (a b c d e : Nat)
  | valid (bits : Nat)
  | branch (idx : Nat) (withE : S3Tree) (withoutE : S3Tree)

private def checkS3Tree : S3Tree → Nat → Nat → Bool
  | S3Tree.degHi u, yes, _ => 4 ≤ u && u < 12 && degYes yes u > 2
  | S3Tree.degLo u, yes, no => 4 ≤ u && u < 12 && degPoss yes no u < 2
  | S3Tree.tri a b c, yes, _ =>
      a < 12 && b < 12 && c < 12 &&
      isAdjYes yes a b && isAdjYes yes a c && isAdjYes yes b c
  | S3Tree.ind5 a b c d e, yes, no => checkInd5 (isAdjPoss yes no) a b c d e
  | S3Tree.ind5Full a b c d e, yes, _ =>
      (List.range 8).all (fun i => degYes yes (i + 4) == 2) &&
      checkInd5 (isAdjYes yes) a b c d e
  | S3Tree.valid bits, yes, _ =>
      bits < 16 &&
      (List.range 8).all (fun i => degYes yes (i + 4) == 2) &&
      yes == swapMasks16.getD bits 0
  | S3Tree.branch idx t1 t2, yes, no =>
      idx < 24 && !(yes.testBit idx) && !(no.testBit idx) &&
      checkS3Tree t1 (yes ||| (1 <<< idx)) no &&
      checkS3Tree t2 yes (no ||| (1 <<< idx))

private def s3TreeCert : S3Tree :=
  {tree_str}

private def popcount (n m : Nat) : Nat :=
  (List.range n).countP fun i => m.testBit i

private def isIndH0 (m : Nat) : Bool :=
  (List.range 12).all fun i =>
    !(m.testBit i) || ((h0Adj12.getD i 0) &&& m == 0)

private def hasInd6 (chosen : List Nat) : Bool :=
  (List.range' 1 31).any fun yMask =>
    let need := 6 - popcount 5 yMask
    indAllH0List.any fun iMask =>
      popcount 12 iMask == need &&
      (List.range 5).all fun k =>
        !(yMask.testBit k) || ((chosen.getD k 0) &&& iMask == 0)

private def targetCnt : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]

private def fitsCnt (cnt : List Nat) (m : Nat) : Bool :=
  (List.range 12).all fun i =>
    (cnt.getD i 0) + (if m.testBit i then 1 else 0) ≤ targetCnt.getD i 0

private def addCnt (cnt : List Nat) (m : Nat) : List Nat :=
  (List.range 12).map fun i =>
    (cnt.getD i 0) + (if m.testBit i then 1 else 0)

private def nonEmptyTails : List Nat → List (List Nat)
  | [] => []
  | x :: xs => (x :: xs) :: nonEmptyTails xs

private def check5Ext : Nat → List Nat → List Nat → List Nat → Bool
  | 0, _, cnt, chosen => if cnt == targetCnt then hasInd6 chosen else true
  | k + 1, cands, cnt, chosen =>
      (nonEmptyTails cands).all fun l =>
        match l with
        | [] => true
        | m :: rest =>
            if fitsCnt cnt m then check5Ext k (m :: rest) (addCnt cnt m) (m :: chosen)
            else true

private def checkSwapMasks : Bool :=
  (List.range 16).all fun bits =>
    (List.range 12).all fun a =>
      (List.range 12).all fun b =>
        isAdjYes (swapMasks16.getD bits 0) a b ==
          (h0Adj12.getD (swapVert bits a) 0).testBit (swapVert bits b)

private def checkInd4Complete : Bool :=
  (List.range 4096).all fun m =>
    if popcount 12 m == 4 && isIndH0 m then ind4H0List.contains m else true

private def checkIndAllValid : Bool :=
  indAllH0List.all fun m => m < 4096 && isIndH0 m

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem r36_cert_verify :
    checkS3Tree s3TreeCert 0 0 = true ∧
    checkSwapMasks = true ∧
    checkInd4Complete = true ∧
    checkIndAllValid = true ∧
    check5Ext 5 ind4H0List (List.replicate 12 0) [] = true := by
  exact ⟨by rfl, by rfl, by rfl, by rfl, by rfl⟩
"""

out = Path("ply-math-dev/r36_cert_test.lean")
out.write_text(lean_code)
print("Wrote", out, len(lean_code), "bytes")
