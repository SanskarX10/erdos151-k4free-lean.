"""Generate pure-kernel Lean 4 proof of R1.H1.R1.H1.R1.H3 (R(3,9)>=36 and R(3,10)>=40)."""
from pathlib import Path

ADJ39 = [
    8665465938, 17330931845, 138782314762, 2686722580, 347926446121,
    17718973008, 69831237793, 2223522114, 279323903620, 146298439976,
    71408568577, 4336948738, 283551803428, 154754240584, 1344545936,
    17450993921, 70334452226, 2189762596, 279257432136, 8725496976,
    279259390468, 77448921128, 429775717440, 70351194241, 139629695234,
    9210824784, 154787909761, 35771654402, 71542292996, 38965150760,
    294347948100, 5654054024, 148714555664, 55870755329, 78454497314,
    490297360384, 51818595408, 38742794756, 35438989584,
]

ADJ35 = [0] * 35
for i in range(35):
    for d in [1, 7, 11, 16, 19, 24, 28, 34]:
        ADJ35[i] |= 1 << ((i + d) % 35)


def greedy_matching_cover(adj, mask):
    rem = mask
    pairs = []
    while rem:
        best_v = -1
        best_d = 999
        m = rem
        while m:
            lsb = m & -m
            v = lsb.bit_length() - 1
            m ^= lsb
            d = (adj[v] & rem).bit_count()
            if 0 < d < best_d:
                best_d = d
                best_v = v
        if best_v == -1:
            break
        nbrs = adj[best_v] & rem
        best_u = -1
        best_du = 999
        m = nbrs
        while m:
            lsb = m & -m
            u = lsb.bit_length() - 1
            m ^= lsb
            d = (adj[u] & rem).bit_count()
            if d < best_du:
                best_du = d
                best_u = u
        pairs.append((best_v, best_u))
        rem &= ~(1 << best_v) & ~(1 << best_u)
    return len(pairs) + rem.bit_count(), pairs


def build_cert(adj, mask, need):
    if need == 0:
        raise RuntimeError("Found independent set!")
    if mask.bit_count() < need:
        return ("leaf", [])
    ub, pairs = greedy_matching_cover(adj, mask)
    if ub < need:
        return ("leaf", pairs)
    best_v = -1
    best_d = -1
    m = mask
    while m:
        lsb = m & -m
        v = lsb.bit_length() - 1
        m ^= lsb
        d = (adj[v] & mask).bit_count()
        if d > best_d:
            best_d = d
            best_v = v
    c_in = build_cert(adj, mask & ~(1 << best_v) & ~adj[best_v], need - 1)
    c_out = build_cert(adj, mask & ~(1 << best_v), need)
    return ("branch", best_v, c_in, c_out)


def fmt_cert(cert):
    if cert[0] == "leaf":
        ps = ", ".join(f"({u}, {v})" for u, v in cert[1])
        return f"H3Cert.leaf [{ps}]"
    _, v, c1, c2 = cert
    return f"H3Cert.branch {v} ({fmt_cert(c1)}) ({fmt_cert(c2)})"


# Build full trees (no symmetry trick needed for soundness — both are tiny!)
cert35 = build_cert(ADJ35, (1 << 35) - 1, 9)
cert39 = build_cert(ADJ39, (1 << 39) - 1, 10)

def count_tree(c):
    return 1 if c[0] == "leaf" else 1 + count_tree(c[2]) + count_tree(c[3])

print("cert35 nodes (full):", count_tree(cert35))
print("cert39 nodes (full):", count_tree(cert39))

lean = f"""import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1

/-! Pure-kernel proof of R(3,9) >= 36 and R(3,10) >= 40 (R1.H1.R1.H1.R1.H3)
via Kalbfleisch's 35-vertex triangle-free circulant and Exoo's 39-vertex
triangle-free graph, verified with matching-cover branch-and-bound trees. -/
-- Step: Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H3
-- Credit: @SanskarX10

private def h3Rows35 : Array Nat :=
  #[{", ".join(str(x) for x in ADJ35)}]

private def h3Rows39 : Array Nat :=
  #[{", ".join(str(x) for x in ADJ39)}]

private def h3Edge (rows : Array Nat) (i j : Nat) : Bool :=
  (rows.getD i 0).testBit j

private def h3Symm (rows : Array Nat) (n : Nat) : Bool :=
  (List.range n).all fun i =>
    !(h3Edge rows i i) &&
    (List.range n).all fun j => h3Edge rows i j == h3Edge rows j i

private def h3TF (rows : Array Nat) (n : Nat) : Bool :=
  (List.range n).all fun i =>
    (List.range n).all fun j =>
      !(h3Edge rows i j) || ((rows.getD i 0) &&& (rows.getD j 0) == 0)

private inductive H3Cert where
  | leaf (pairs : List (Nat × Nat))
  | branch (v : Nat) (withV : H3Cert) (withoutV : H3Cert)

private def h3CheckPairs (rows : Array Nat) : List Nat → List (Nat × Nat) → Nat → Bool
  | rem, [], need => rem.length < need
  | rem, (u, v) :: ps, need =>
      rem.contains u && rem.contains v && h3Edge rows u v &&
      (need > 0) &&
      h3CheckPairs rows ((rem.erase u).erase v) ps (need - 1)

private def h3CheckCert (rows : Array Nat) : H3Cert → List Nat → Nat → Bool
  | H3Cert.leaf ps, rem, need => h3CheckPairs rows rem ps need
  | H3Cert.branch v cIn cOut, rem, need =>
      rem.contains v && (need > 0) &&
      h3CheckCert rows cIn ((rem.erase v).filter fun x => !(h3Edge rows v x)) (need - 1) &&
      h3CheckCert rows cOut (rem.erase v) need

private def h3Cert35 : H3Cert :=
  {fmt_cert(cert35)}

private def h3Cert39 : H3Cert :=
  {fmt_cert(cert39)}

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem h3_verify_35 :
    h3Symm h3Rows35 35 = true ∧
    h3TF h3Rows35 35 = true ∧
    h3CheckCert h3Rows35 h3Cert35 (List.range 35) 9 = true := by
  exact ⟨by rfl, by rfl, by rfl⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem h3_verify_39 :
    h3Symm h3Rows39 39 = true ∧
    h3TF h3Rows39 39 = true ∧
    h3CheckCert h3Rows39 h3Cert39 (List.range 39) 10 = true := by
  exact ⟨by rfl, by rfl, by rfl⟩

private theorem h3_checkPairs_sound (rows : Array Nat) (I : Finset Nat)
    (hind : ∀ x ∈ I, ∀ y ∈ I, h3Edge rows x y = false) :
    ∀ (ps : List (Nat × Nat)) (rem : List Nat) (need : Nat),
      (∀ x ∈ I, x ∈ rem) →
      h3CheckPairs rows rem ps need = true →
      I.card < need := by
  intro ps
  induction ps with
  | nil =>
      intro rem need hsub hchk
      simp only [h3CheckPairs, decide_eq_true_eq] at hchk
      have h1 : I.card ≤ rem.toFinset.card := Finset.card_le_card (fun x hx => List.mem_toFinset.mpr (hsub x hx))
      have h2 : rem.toFinset.card ≤ rem.length := List.toFinset_card_le rem
      omega
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      intro rem need hsub hchk
      simp only [h3CheckPairs, Bool.and_eq_true, decide_eq_true_eq] at hchk
      rcases hchk with ⟨⟨⟨⟨_, _⟩, huv⟩, hpos⟩, hrest⟩
      let I' := (I.erase u).erase v
      have hsub' : ∀ x ∈ I', x ∈ (rem.erase u).erase v := by
        intro x hx
        have hxv : x ≠ v := Finset.ne_of_mem_erase hx
        have hx1 : x ∈ I.erase u := Finset.mem_of_mem_erase hx
        have hxu : x ≠ u := Finset.ne_of_mem_erase hx1
        have hxI : x ∈ I := Finset.mem_of_mem_erase hx1
        exact List.mem_erase_of_ne hxv |>.mpr (List.mem_erase_of_ne hxu |>.mpr (hsub x hxI))
      have hind' : ∀ x ∈ I', ∀ y ∈ I', h3Edge rows x y = false := by
        intro x hx y hy
        exact hind x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
          y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
      have hlt : I'.card < need - 1 := ih ((rem.erase u).erase v) (need - 1) hsub' hrest
      have hnotboth : ¬ (u ∈ I ∧ v ∈ I) := by
        rintro ⟨hu, hv⟩
        have hfalse := hind u hu v hv
        rw [huv] at hfalse
        cases hfalse
      have hcard : I.card ≤ I'.card + 1 := by
        by_cases hu : u ∈ I
        · have hv : v ∉ I := fun hv => hnotboth ⟨hu, hv⟩
          have hv' : v ∉ I.erase u := fun h => hv (Finset.mem_of_mem_erase h)
          dsimp [I']
          rw [Finset.erase_eq_of_notMem hv', Finset.card_erase_of_mem hu]
          have : 1 ≤ I.card := Finset.one_le_card.mpr ⟨u, hu⟩
          omega
        · dsimp [I']
          rw [Finset.erase_eq_of_notMem hu]
          by_cases hv : v ∈ I
          · rw [Finset.card_erase_of_mem hv]
            have : 1 ≤ I.card := Finset.one_le_card.mpr ⟨v, hv⟩
            omega
          · rw [Finset.erase_eq_of_notMem hv]
            omega
      omega

private theorem h3_checkCert_sound (rows : Array Nat) :
    ∀ (cert : H3Cert) (rem : List Nat) (need : Nat) (I : Finset Nat),
      (∀ x ∈ I, ∀ y ∈ I, h3Edge rows x y = false) →
      (∀ x ∈ I, x ∈ rem) →
      h3CheckCert rows cert rem need = true →
      I.card < need := by
  intro cert
  induction cert with
  | leaf ps =>
      intro rem need I hind hsub hchk
      exact h3_checkPairs_sound rows I hind ps rem need hsub hchk
  | branch v cIn cOut ihIn ihOut =>
      intro rem need I hind hsub hchk
      simp only [h3CheckCert, Bool.and_eq_true, decide_eq_true_eq] at hchk
      rcases hchk with ⟨⟨⟨_, hpos⟩, hIn⟩, hOut⟩
      by_cases hv : v ∈ I
      · let I' := I.erase v
        have hsub' : ∀ x ∈ I', x ∈ (rem.erase v).filter fun x => !(h3Edge rows v x) := by
          intro x hx
          have hxv : x ≠ v := Finset.ne_of_mem_erase hx
          have hxI : x ∈ I := Finset.mem_of_mem_erase hx
          rw [List.mem_filter]
          refine ⟨(List.mem_erase_of_ne hxv).mpr (hsub x hxI), ?_⟩
          simp [hind v hv x hxI]
        have hind' : ∀ x ∈ I', ∀ y ∈ I', h3Edge rows x y = false :=
          fun x hx y hy => hind x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
        have hlt := ihIn _ (need - 1) I' hind' hsub' hIn
        have hcard : I'.card = I.card - 1 := Finset.card_erase_of_mem hv
        have h1 : 1 ≤ I.card := Finset.one_le_card.mpr ⟨v, hv⟩
        omega
      · have hsub' : ∀ x ∈ I, x ∈ rem.erase v := by
          intro x hx
          have hxv : x ≠ v := fun h => hv (h ▸ hx)
          exact (List.mem_erase_of_ne hxv).mpr (hsub x hx)
        exact ihOut _ need I hind hsub' hOut

private theorem h3_lower_bound (rows : Array Nat) (N K : Nat) (cert : H3Cert)
    (hsym : h3Symm rows N = true)
    (htf : h3TF rows N = true)
    (hcert : h3CheckCert rows cert (List.range N) K = true) :
    ∀ n : Nat, K ≤ Erdos151.H n → N + 1 ≤ n := by
  intro n hH
  by_contra hlt
  have hnN : n ≤ N := by omega
  let G : SimpleGraph (Fin n) :=
    {{ Adj := fun x y => h3Edge rows x.val y.val = true
      symm := ⟨fun x y h => by
        simp only [h3Symm, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hsym
        have hxy := (hsym x.val (List.mem_range.mpr (lt_of_lt_of_le x.isLt hnN))).2
          y.val (List.mem_range.mpr (lt_of_lt_of_le y.isLt hnN))
        exact hxy.symm.trans h⟩
      loopless := ⟨fun x h => by
        simp only [h3Symm, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hsym
        have hxx := (hsym x.val (List.mem_range.mpr (lt_of_lt_of_le x.isLt hnN))).1
        rw [h] at hxx
        cases hxx⟩ }}
  have hGtf : G.CliqueFree 3 := by
    intro t ht
    obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := SimpleGraph.is3Clique_iff.mp ht
    simp only [h3TF, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at htf
    have hx := htf x.val (List.mem_range.mpr (lt_of_lt_of_le x.isLt hnN))
      y.val (List.mem_range.mpr (lt_of_lt_of_le y.isLt hnN))
    have hand : (rows.getD x.val 0 &&& rows.getD y.val 0) = 0 := by
      rcases hx with hfalse | hzero
      · rw [hxy] at hfalse
        cases hfalse
      · exact hzero
    have hbit : ((rows.getD x.val 0 &&& rows.getD y.val 0)).testBit z.val = true := by
      rw [Nat.testBit_and]
      have h1 : (rows.getD x.val 0).testBit z.val = true := hxz
      have h2 : (rows.getD y.val 0).testBit z.val = true := hyz
      simp [h1, h2]
    rw [hand] at hbit
    simp at hbit
  have hAtt : ∃ s, G.IsNIndepSet (Erdos151.H n) s := by
    let sizes : Set ℕ :=
      {{k | ∀ Q : SimpleGraph (Fin n), Q.CliqueFree 3 → ∃ s, Q.IsNIndepSet k s}}
    have hne : sizes.Nonempty := ⟨0, fun _ _ => ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩⟩
    have hfin : sizes.Finite := (Set.finite_Iic n).subset fun k hk => by
      obtain ⟨s, hs⟩ := hk G hGtf
      simpa [hs.card_eq] using Finset.card_le_univ s
    exact hne.csSup_mem hfin G hGtf
  obtain ⟨s, hs⟩ := hAtt
  let I : Finset Nat := s.image Fin.val
  have hIcard : I.card = s.card := Finset.card_image_of_injective s Fin.val_injective
  have hIsub : ∀ x ∈ I, x ∈ List.range N := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
    exact List.mem_range.mpr (lt_of_lt_of_le a.isLt hnN)
  have hIind : ∀ x ∈ I, ∀ y ∈ I, h3Edge rows x y = false := by
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    cases h : h3Edge rows a.val b.val
    · rfl
    · have hab : a ≠ b := by
        intro he
        subst b
        exact G.irrefl h
      exact (hs.isIndepSet ha hb hab h).elim
  have hltK : I.card < K := h3_checkCert_sound rows cert (List.range N) K I hIind hIsub hcert
  have hsc : s.card = Erdos151.H n := hs.card_eq
  omega

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1.H3 := by
  exact ⟨h3_lower_bound h3Rows35 35 9 h3Cert35 h3_verify_35.1 h3_verify_35.2.1 h3_verify_35.2.2,
         h3_lower_bound h3Rows39 39 10 h3Cert39 h3_verify_39.1 h3_verify_39.2.1 h3_verify_39.2.2⟩
"""

out = Path("ply-math-dev/Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H3.lean")
out.write_text(lean)
print("Wrote", out, "size:", len(lean), "bytes,", len(lean.splitlines()), "lines")
