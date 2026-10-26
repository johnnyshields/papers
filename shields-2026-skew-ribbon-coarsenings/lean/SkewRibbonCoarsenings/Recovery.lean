/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Coordinates

/-!
# Recovery at prescribed factor weights

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:recovery` (`thm:recovery`,
`eq:outer-recovery`, `eq:inner-derivative`, `eq:inner-recovery`, `eq:two-factor-cancel`).

`block_formula` is the displayed identity before `thm:recovery`:
`∂_{h_k} G_F = ∑ P_F(x) Q_F(x + k)` over the retained cuts `x` and `x + k` (prefix and suffix
coarsening inventories).  `outer_recovery` is `eq:outer-recovery`, `inner_derivative` is
`eq:inner-derivative`, `inner_recovery_int` and `inner_recovery` are `eq:inner-recovery`
(integrally as `n · G_β` and over `ℚ`), and `two_factor_cancel_forward` and
`two_factor_cancel_iff` are `eq:two-factor-cancel`; the reverse direction of the latter takes
`eq:congruence` as an explicit hypothesis.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset MvPolynomial

/-- The partial derivative `∂_{h_k}` on `Λ_ℤ` (`k = 0` is the zero derivation). -/
noncomputable def dh (k : ℕ) : Derivation ℤ Lam Lam :=
  if hk : 0 < k then MvPolynomial.pderiv (Nat.toPNat' k) else 0

lemma dh_of_pos {k : ℕ} (hk : 0 < k) : dh k = MvPolynomial.pderiv (Nat.toPNat' k) := by
  simp [dh, hk]

lemma dh_hgen {k : ℕ} (hk : 0 < k) (N : ℕ) : dh k (hgen N) = if k = N then 1 else 0 := by
  rw [dh_of_pos hk]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hgen, hk.ne']
  · rw [hgen_eq_X hN, MvPolynomial.pderiv_X, Pi.single_apply]
    by_cases h : k = N
    · subst h; simp
    · have : Nat.toPNat' N ≠ Nat.toPNat' k := fun h' => h (by
        have := congrArg PNat.val h'
        rwa [PNat.toPNat'_coe hN, PNat.toPNat'_coe hk, eq_comm] at this)
      simp [this, h]

lemma G_zero_empty : G 0 ∅ = 1 := by
  rw [G_empty]; simp [hgen]

/-- Splitting off the largest retained cut. -/
lemma G_insert_max {N a : ℕ} {s : Finset ℕ} (ha : a < N) (hs : ∀ z ∈ s, z < a) :
    G N (insert a s) = G N s + hgen (N - a) * G a s := by
  have han : a ∉ s := fun h => lt_irrefl _ (hs a h)
  unfold G
  rw [Finset.sum_powerset_insert han, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT' : ∀ z ∈ T, z < a := fun z hz => hs z (Finset.mem_powerset.mp hT hz)
  rw [gaps_insert_max ha hT', Multiset.map_cons, Multiset.prod_cons]

/-- Prefix inventory `P(x)`: the coarsening polynomial of the part of `S` below `x`. -/
noncomputable def prefG (S : Finset ℕ) (x : ℕ) : Lam := G x (S.filter (· < x))

/-- Suffix inventory `Q(y)`: the coarsening polynomial of the part of `S` above `y`, of weight
`N - y`. -/
noncomputable def sufG (N : ℕ) (S : Finset ℕ) (y : ℕ) : Lam :=
  G (N - y) ((S.filter (y < ·)).image (· - y))

lemma sufG_top {N : ℕ} {S : Finset ℕ} (hS : ∀ z ∈ S, z < N) : sufG N S N = 1 := by
  unfold sufG
  have : S.filter (N < ·) = ∅ := Finset.filter_eq_empty_iff.mpr fun z hz => not_lt.mpr (hS z hz).le
  rw [this]
  simpa using G_zero_empty

lemma sufG_insert {N a y : ℕ} {s : Finset ℕ} (ha : a < N) (hs : ∀ z ∈ s, z < a) (hy : y < a) :
    sufG N (insert a s) y = sufG N s y + hgen (N - a) * sufG a s y := by
  unfold sufG
  have e : (insert a s).filter (y < ·) = insert a (s.filter (y < ·)) := by
    rw [Finset.filter_insert, if_pos hy]
  rw [e, Finset.image_insert]
  have h1 : a - y < N - y := by omega
  have h2 : ∀ z ∈ (s.filter (y < ·)).image (· - y), z < a - y := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have := Finset.mem_filter.mp hw
    have := hs w this.1
    omega
  rw [G_insert_max h1 h2]
  congr 3
  omega

lemma sufG_at {N a : ℕ} {s : Finset ℕ} (hs : ∀ z ∈ s, z < a) (ha : a < N) :
    sufG N (insert a s) a = hgen (N - a) := by
  unfold sufG
  have : (insert a s).filter (a < ·) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun z hz => ?_
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact lt_irrefl _
    · exact not_lt.mpr (hs z h).le
  rw [this]; simpa using G_empty (N - a)

lemma sufG_at_sub {a : ℕ} {s : Finset ℕ} (hs : ∀ z ∈ s, z < a) : sufG a s a = 1 :=
  sufG_top hs

lemma prefG_insert {a x : ℕ} {s : Finset ℕ} (hx : x < a) :
    prefG (insert a s) x = prefG s x := by
  unfold prefG
  rw [Finset.filter_insert, if_neg (by omega)]

lemma prefG_top {a : ℕ} {s : Finset ℕ} (hs : ∀ z ∈ s, z < a) :
    prefG (insert a s) a = G a s := by
  unfold prefG
  rw [Finset.filter_insert, if_neg (lt_irrefl a), Finset.filter_true_of_mem (fun z hz => hs z hz)]


/-- The right-hand side of the marked-block formula: over the left endpoints `x ∈ {0} ∪ S` of a
block of length `k`, the prefix inventory times the suffix inventory, when `x + k` is a retained
cut or the endpoint `N`. -/
noncomputable def blockF (N : ℕ) (S : Finset ℕ) (k : ℕ) : Lam :=
  ∑ x ∈ insert 0 S, if x + k ∈ insert N S then prefG S x * sufG N S (x + k) else 0

lemma blockF_step {N a : ℕ} {s : Finset ℕ} (ha : a < N) (hs : ∀ z ∈ s, z < a) (ha0 : 0 < a)
    {x k : ℕ} (hx : x ∈ insert 0 s) :
    (if x + k ∈ insert N (insert a s) then prefG (insert a s) x * sufG N (insert a s) (x + k)
      else 0)
      = (if x + k ∈ insert N s then prefG s x * sufG N s (x + k) else 0)
        + hgen (N - a) * (if x + k ∈ insert a s then prefG s x * sufG a s (x + k) else 0) := by
  have hxa : x < a := by
    rcases Finset.mem_insert.mp hx with rfl | h
    · exact ha0
    · exact hs x h
  have hsN : ∀ z ∈ s, z < N := fun z hz => lt_trans (hs z hz) ha
  have hS'N : ∀ z ∈ insert a s, z < N := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact ha
    · exact hsN z h
  have has : a ∉ s := fun h => lt_irrefl _ (hs a h)
  rw [prefG_insert hxa]
  rcases lt_trichotomy (x + k) a with hy | hy | hy
  · have hyN : x + k ≠ N := by omega
    have hya : x + k ≠ a := by omega
    simp only [Finset.mem_insert, hyN, hya, false_or]
    by_cases hm : x + k ∈ s
    · simp only [hm, if_true]
      rw [sufG_insert ha hs hy]; ring
    · simp [hm]
  · have hyN : x + k ≠ N := by omega
    have hyas : x + k ∉ s := by rw [hy]; exact has
    have hNa : a ≠ N := ha.ne
    simp only [Finset.mem_insert, hyN, hy, true_or, or_true, if_true, hyas, false_or, if_false,
      hNa, has]
    rw [sufG_at hs ha, sufG_top hs]; ring
  · have hya : x + k ≠ a := by omega
    have hys : x + k ∉ s := fun h => by have := hs _ h; omega
    by_cases hyN : x + k = N
    · have hNa : N ≠ a := ha.ne'
      have hNs : N ∉ s := fun h => by have := hsN N h; omega
      simp only [Finset.mem_insert, hyN, hys, true_or, or_true, if_true, hya, false_or,
        if_false, mul_zero, add_zero, hNa, hNs]
      rw [sufG_top hS'N, sufG_top hsN]
    · simp [Finset.mem_insert, hyN, hya, hys]

/-- The marked-block formula displayed before `thm:recovery`:
`∂_{h_k} G_F = ∑ P_F(x) Q_F(x + k)` over a block of length `k` from the retained cut (or the
start) `x` to the retained cut (or the end) `x + k`, where `P_F(x)` and `Q_F(x + k)` are the
coarsening polynomials of the prefix before `x` and of the suffix after `x + k`. -/
theorem block_formula : ∀ (S : Finset ℕ) {N : ℕ}, IsCutSet N S → ∀ {k : ℕ}, 0 < k →
    dh k (G N S) = blockF N S k := by
  intro S
  induction S using Finset.induction_on_max with
  | empty =>
    intro N _ k hk
    rw [G_empty, dh_hgen hk]
    unfold blockF
    simp only [Finset.insert_empty, Finset.sum_singleton, zero_add, prefG, Finset.filter_empty]
    by_cases h : k = N
    · subst h
      rw [if_pos rfl, if_pos (Finset.mem_singleton_self _), sufG_top (by simp), G_zero_empty,
        mul_one]
    · rw [if_neg h, if_neg (by simpa using h)]
  | insert a s hs ih =>
    intro N hN k hk
    have ha : a < N := (Finset.mem_Ioo.mp (hN (Finset.mem_insert_self a s))).2
    have ha0 : 0 < a := (Finset.mem_Ioo.mp (hN (Finset.mem_insert_self a s))).1
    have hsa : IsCutSet a s := fun z hz =>
      Finset.mem_Ioo.mpr ⟨(Finset.mem_Ioo.mp (hN (Finset.mem_insert_of_mem hz))).1, hs z hz⟩
    have hsN : IsCutSet N s := fun z hz => Finset.mem_Ioo.mpr
      ⟨(Finset.mem_Ioo.mp (hN (Finset.mem_insert_of_mem hz))).1, lt_trans (hs z hz) ha⟩
    have has : a ∉ s := fun h => lt_irrefl _ (hs a h)
    have ha0s : a ∉ insert 0 s := by
      simp only [Finset.mem_insert, not_or]; exact ⟨ha0.ne', has⟩
    rw [G_insert_max ha hs, map_add, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ih hsN hk,
      ih hsa hk, dh_hgen hk]
    unfold blockF
    rw [Finset.insert_comm, Finset.sum_insert ha0s]
    have hxs : ∀ x ∈ insert 0 s, (if x + k ∈ insert N (insert a s)
          then prefG (insert a s) x * sufG N (insert a s) (x + k) else 0)
        = (if x + k ∈ insert N s then prefG s x * sufG N s (x + k) else 0)
          + hgen (N - a) * (if x + k ∈ insert a s then prefG s x * sufG a s (x + k) else 0) :=
      fun x hx => blockF_step ha hs ha0 hx
    rw [Finset.sum_congr rfl hxs, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hlast : (if a + k ∈ insert N (insert a s)
          then prefG (insert a s) a * sufG N (insert a s) (a + k) else 0)
        = if k = N - a then G a s else 0 := by
      by_cases hk' : k = N - a
      · have : a + k = N := by omega
        rw [if_pos hk', this, if_pos (Finset.mem_insert_self _ _), prefG_top hs,
          sufG_top (fun z hz => by
            rcases Finset.mem_insert.mp hz with rfl | h
            · exact ha
            · exact lt_trans (hs z h) ha), mul_one]
      · rw [if_neg hk', if_neg]
        simp only [Finset.mem_insert, not_or]
        refine ⟨by omega, by omega, fun h => ?_⟩
        have := hs _ h; omega
    rw [hlast]
    by_cases hk' : k = N - a
    · simp only [hk', if_true]; ring
    · simp only [hk', if_false]; ring


/-! ### The derivative identity -/

section Inner

variable {m n : ℕ} {A E : Finset ℕ}

lemma comp_mem_iff (hA : IsCutSet m A) (hE : IsCutSet n E) {z : ℕ} :
    z ∈ compCuts m A n E ↔ (∃ y ∈ A, n * y = z) ∨ ∃ j < m, ∃ e ∈ E, j * n + e = z :=
  mem_compCuts

/-- Cuts of `α ∘ β` below `n` are the cuts of `β`. -/
lemma comp_mem_low (hm : 0 < m) (hA : IsCutSet m A) (hE : IsCutSet n E) {z : ℕ} (hz : z < n) :
    z ∈ compCuts m A n E ↔ z ∈ E := by
  rw [comp_mem_iff hA hE]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨j, hj, e, he, rfl⟩)
    · have := (Finset.mem_Ioo.mp (hA hy)).1
      have : n ≤ n * y := Nat.le_mul_of_pos_right _ this
      omega
    · have he' := (Finset.mem_Ioo.mp (hE he)).1
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simpa using he
      · have : n ≤ j * n := Nat.le_mul_of_pos_left _ hj0
        omega
  · intro he
    exact Or.inr ⟨0, hm, z, he, by simp⟩

/-- Cuts of `α ∘ β` above `(m-1) n` are the cuts of the last copy of `β`, translated. -/
lemma comp_mem_high (hm : 0 < m) (hA : IsCutSet m A) (hE : IsCutSet n E) {z : ℕ} (hz : (m - 1) * n < z) :
    z ∈ compCuts m A n E ↔ ∃ e ∈ E, (m - 1) * n + e = z := by
  rw [comp_mem_iff hA hE]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨j, hj, e, he, rfl⟩)
    · have := (Finset.mem_Ioo.mp (hA hy)).2
      have : n * y ≤ n * (m - 1) := Nat.mul_le_mul_left _ (by omega)
      rw [mul_comm n (m - 1)] at this
      omega
    · have he' := (Finset.mem_Ioo.mp (hE he)).2
      have hjm : j = m - 1 := by
        by_contra hne
        have : j + 1 ≤ m - 1 := by omega
        have : (j + 1) * n ≤ (m - 1) * n := Nat.mul_le_mul_right _ this
        nlinarith
      subst hjm
      exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact Or.inr ⟨m - 1, by omega, e, he, rfl⟩

lemma compCuts_lt (hn : 0 < n) (hA : IsCutSet m A) (hE : IsCutSet n E) :
    ∀ z ∈ compCuts m A n E, z < m * n := fun z hz => by
  have := compCuts_isCutSet hn hA hE
  have h := Finset.mem_Ioo.mp (this hz)
  rw [mul_comm] at h
  rw [mul_comm]
  exact h.2

lemma comp_sufG (hn : 0 < n) (hm : 0 < m) (hA : IsCutSet m A) (hE : IsCutSet n E) {x j : ℕ}
    (hj : 0 < j) (hxj : x + j ≤ n) :
    sufG (m * n) (compCuts m A n E) ((m - 1) * n + (x + j)) = sufG n E (x + j) := by
  unfold sufG
  have hN : m * n - ((m - 1) * n + (x + j)) = n - (x + j) := by
    have : m * n = (m - 1) * n + n := by
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
      simp; ring
    omega
  rw [hN]
  congr 1
  ext w
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨z, ⟨hz, hlt⟩, rfl⟩
    have hz' : (m - 1) * n < z := by omega
    obtain ⟨e, he, rfl⟩ := (comp_mem_high hm hA hE hz').mp hz
    exact ⟨e, ⟨he, by omega⟩, by omega⟩
  · rintro ⟨e, ⟨he, hlt⟩, rfl⟩
    have hz' : (m - 1) * n < (m - 1) * n + e := by
      have := (Finset.mem_Ioo.mp (hE he)).1; omega
    exact ⟨(m - 1) * n + e, ⟨(comp_mem_high hm hA hE hz').mpr ⟨e, he, rfl⟩, by omega⟩, by omega⟩

end Inner


section InnerDerivative

variable {m n : ℕ} {A E : Finset ℕ}

lemma E_subset_comp (hm : 0 < m) : E ⊆ compCuts m A n E := fun e he =>
  mem_compCuts.mpr (Or.inr ⟨0, hm, e, he, by simp⟩)

lemma prefG_comp (hm : 0 < m) (hA : IsCutSet m A) (hE : IsCutSet n E) {x : ℕ} (hx : x < n) :
    prefG (compCuts m A n E) x = prefG E x := by
  unfold prefG
  congr 1
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(comp_mem_low hm hA hE (by omega)).mp h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(comp_mem_low hm hA hE (by omega)).mpr h1, h2⟩

lemma comp_mem_shift (hm : 0 < m) (hn : 0 < n) (hA : IsCutSet m A) (hE : IsCutSet n E)
    {x j : ℕ} (hj : 0 < j) (hx : x < n) :
    ((m - 1) * n + j + x ∈ insert (m * n) (compCuts m A n E)) ↔ (x + j ∈ insert n E) := by
  have hmn : m * n = (m - 1) * n + n := by
    obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
    simp; ring
  have hE' : ∀ e ∈ E, e < n := fun e he => (Finset.mem_Ioo.mp (hE he)).2
  rw [Finset.mem_insert, Finset.mem_insert]
  by_cases hle : x + j ≤ n
  · by_cases heq : x + j = n
    · simp only [heq, true_or, iff_true]; left; omega
    · have hlt : x + j < n := by omega
      have : (m - 1) * n < (m - 1) * n + j + x := by omega
      rw [comp_mem_high hm hA hE this]
      constructor
      · rintro (h | ⟨e, he, h⟩)
        · omega
        · right; have : e = x + j := by omega
          rw [← this]; exact he
      · rintro (h | h)
        · omega
        · right; exact ⟨x + j, h, by omega⟩
  · have hgt : n < x + j := by omega
    have h1 : ¬ (m * n = (m - 1) * n + j + x) := by omega
    have h2 : (m - 1) * n + j + x ∉ compCuts m A n E := fun h => by
      have := compCuts_lt hn hA hE _ h; omega
    have h3 : ¬ (x + j = n) := by omega
    have h4 : x + j ∉ E := fun h => by have := hE' _ h; omega
    have h1' : ¬ ((m - 1) * n + j + x = m * n) := by omega
    simp [h1, h1', h2, h3, h4]

/-- `eq:inner-derivative`, for the cut-set representation: the derivative of `G_{α ∘ β}` by the
generator of index `(m-1) n + j` is the derivative of `G_β` by `h_j`, `1 ≤ j ≤ n`.  The case
`m = 1` (outer composition `(1)`) is included.

**Differs from the paper's route.**  Instead of a marked-block bijection of coarsenings, both
sides are expanded by the marked-block formula `block_formula` (prefix and suffix inventories at
the block ends), and the formula for `α ∘ β` is matched term by term with that of `β`: the
prefix inventory below `n` and the suffix inventory above `(m-1) n` of `α ∘ β` are those of `β`
(`prefG_comp`, `comp_sufG`), and no block of length `(m-1) n + j` starts at or beyond `n`. -/
theorem inner_derivative (hm : 0 < m) (hn : 0 < n) (hA : IsCutSet m A) (hE : IsCutSet n E)
    {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) :
    dh ((m - 1) * n + j) (G (m * n) (compCuts m A n E)) = dh j (G n E) := by
  have hcut := compCuts_isCutSet hn hA hE
  have hcut' : IsCutSet (m * n) (compCuts m A n E) := hcut
  have hk : 0 < (m - 1) * n + j := by omega
  rw [block_formula _ hcut' hk, block_formula _ hE hj]
  unfold blockF
  set S := compCuts m A n E with hS
  have hsub : insert 0 E ⊆ insert 0 S := Finset.insert_subset_insert 0 (E_subset_comp hm)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hxn : x < n := by
      rcases Finset.mem_insert.mp hx with rfl | h
      · exact hn
      · exact (Finset.mem_Ioo.mp (hE h)).2
    have hshift := comp_mem_shift hm hn hA hE hj hxn
    have e1 : (m - 1) * n + j + x = x + ((m - 1) * n + j) := by ring
    rw [e1] at hshift
    by_cases hmem : x + j ∈ insert n E
    · rw [if_pos (hshift.mpr hmem), if_pos hmem, prefG_comp hm hA hE hxn]
      congr 1
      have hxj : x + j ≤ n := by
        rcases Finset.mem_insert.mp hmem with h | h
        · omega
        · exact (Finset.mem_Ioo.mp (hE h)).2.le
      have := comp_sufG hn hm hA hE hj hxj
      have e2 : (m - 1) * n + (x + j) = x + ((m - 1) * n + j) := by ring
      rwa [e2] at this
    · rw [if_neg (fun h => hmem (hshift.mp h)), if_neg hmem]
  · intro x hxS hxE
    have hxS' : x ∈ S := by
      rcases Finset.mem_insert.mp hxS with rfl | h
      · exact absurd (Finset.mem_insert_self _ _) hxE
      · exact h
    have hxn : n ≤ x := by
      by_contra hlt
      push_neg at hlt
      exact hxE (Finset.mem_insert_of_mem ((comp_mem_low hm hA hE hlt).mp hxS'))
    rw [if_neg]
    intro hmem
    have hxm : x < m * n := compCuts_lt hn hA hE x hxS'
    have hle : x + ((m - 1) * n + j) ≤ m * n := by
      rcases Finset.mem_insert.mp hmem with h | h
      · omega
      · have := compCuts_lt hn hA hE _ h; omega
    have : m * n = (m - 1) * n + n := by
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
      simp; ring
    omega

end InnerDerivative


/-! ### Outer recovery and the inner operator -/

/-- `eq:outer-recovery`: `π_n(G_{α ∘ β}) = G_α`, for `α` of weight `m` with cut set `A` and `β`
of weight `n > 0` with cut set `E`.  This is the split substitution identity `proj_Psi` applied to
`eq:substitution`. -/
theorem outer_recovery {m n : ℕ} {A E : Finset ℕ} (hn : 0 < n) (hA : IsCutSet m A)
    (hE : IsCutSet n E) : proj n (G (m * n) (compCuts m A n E)) = G m A := by
  rw [← Psi_G n E hn hE m A hA]
  exact congrArg (fun f : Lam →+* Lam => f (G m A)) (proj_Psi hn hE)

/-- The weighted Euler identity for a weight-`n` polynomial in the generators `h_1, …, h_n`
(indexed by naturals): `∑_{j=1}^n j h_j ∂_{h_j} F = n F`. -/
theorem euler_dh {n : ℕ} {F : Lam} (hF : IsWeightedHomogeneous hgenWeight F n) :
    ∑ j ∈ Finset.Icc 1 n, j • (hgen j * dh j F) = n • F := by
  conv_lhs => rw [MvPolynomial.as_sum F]
  conv_rhs => rw [MvPolynomial.as_sum F]
  simp only [map_sum, Finset.mul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight hgenWeight d = n := hF (MvPolynomial.mem_support_iff.mp hd)
  have hdle : ∀ i ∈ d.support, (i : ℕ) ≤ n := by
    intro i hi
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    have : (i : ℕ) * 1 ≤ ∑ x ∈ d.support, d x • hgenWeight x := by
      calc (i : ℕ) * 1 ≤ d i * (i : ℕ) := by
            have := Finsupp.mem_support_iff.mp hi
            nlinarith [Nat.pos_of_ne_zero this]
        _ = d i • hgenWeight i := by simp [hgenWeight]
        _ ≤ _ := Finset.single_le_sum (f := fun x => d x • hgenWeight x) (fun _ _ => Nat.zero_le _) hi
    omega
  have key : ∀ j ∈ Finset.Icc 1 n, j • (hgen j * dh j (monomial d (F.coeff d)))
      = (j * d (Nat.toPNat' j)) • monomial d (F.coeff d) := by
    intro j hj
    have hj0 : 0 < j := (Finset.mem_Icc.mp hj).1
    rw [dh_of_pos hj0, hgen_eq_X hj0, MvPolynomial.X_mul_pderiv_monomial, smul_smul]
  rw [Finset.sum_congr rfl key, ← Finset.sum_smul]
  congr 1
  have e1 : ∑ x ∈ d.support, d x • hgenWeight x
      = ∑ j ∈ d.support.image (fun i : ℕ+ => (i : ℕ)), j * d (Nat.toPNat' j) := by
    rw [Finset.sum_image (fun a _ b _ h => PNat.coe_injective h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hgenWeight, PNat.toPNat'_coe i.pos, mul_comm]
  have e0 : ∑ x ∈ d.support, d x • hgenWeight x = n := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  refine Eq.trans ?_ e0
  rw [e1]
  symm
  apply Finset.sum_subset
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_Icc.mpr ⟨i.pos, hdle i hi⟩
  · intro j hj hjn
    have hj0 : 0 < j := (Finset.mem_Icc.mp hj).1
    have : d (Nat.toPNat' j) = 0 := by
      by_contra hne
      apply hjn
      refine Finset.mem_image.mpr ⟨Nat.toPNat' j, Finsupp.mem_support_iff.mpr hne, ?_⟩
      exact PNat.toPNat'_coe hj0
    simp [this]

/-- `eq:inner-recovery`, integral form: `n · G_β = ∑_{j=1}^n j h_j ∂_{h_{(m-1)n+j}} G_{α ∘ β}`,
for `α` of weight `m > 0` and `β` of weight `n > 0`.  The division by `n` is not asserted
over `ℤ`. -/
theorem inner_recovery_int {m n : ℕ} {A E : Finset ℕ} (hm : 0 < m) (hn : 0 < n)
    (hA : IsCutSet m A) (hE : IsCutSet n E) :
    ∑ j ∈ Finset.Icc 1 n, j • (hgen j * dh ((m - 1) * n + j) (G (m * n) (compCuts m A n E)))
      = n • G n E := by
  rw [← euler_dh (G_isWeightedHomogeneous hE)]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hj0, hjn⟩ := Finset.mem_Icc.mp hj
  rw [inner_derivative hm hn hA hE hj0 hjn]

/-- The rational-linear operator `𝓛_{m,n} = (1/n) ∑_{j=1}^n j h_j ∂_{h_{(m-1)n+j}}` on
`ℚ[h₁, h₂, …]`. -/
noncomputable def innerOp (m n : ℕ) (F : MvPolynomial ℕ+ ℚ) : MvPolynomial ℕ+ ℚ :=
  ((n : ℚ)⁻¹) • ∑ j ∈ Finset.Icc 1 n,
    (j : ℚ) • (MvPolynomial.X (Nat.toPNat' j) * MvPolynomial.pderiv (Nat.toPNat' ((m - 1) * n + j)) F)

/-- `eq:inner-recovery`: `𝓛_{m,n}(G_{α ∘ β}) = G_β` over `ℚ`, for `α` of weight `m > 0` and `β`
of weight `n > 0`. -/
theorem inner_recovery {m n : ℕ} {A E : Finset ℕ} (hm : 0 < m) (hn : 0 < n)
    (hA : IsCutSet m A) (hE : IsCutSet n E) :
    innerOp m n (MvPolynomial.map (Int.castRingHom ℚ) (G (m * n) (compCuts m A n E)))
      = MvPolynomial.map (Int.castRingHom ℚ) (G n E) := by
  have h := congrArg (MvPolynomial.map (Int.castRingHom ℚ)) (inner_recovery_int hm hn hA hE)
  simp only [map_sum, map_nsmul, map_mul, nsmul_eq_mul, map_natCast] at h
  unfold innerOp
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hterm : ∀ j ∈ Finset.Icc 1 n,
      (j : ℚ) • (MvPolynomial.X (Nat.toPNat' j) * MvPolynomial.pderiv (Nat.toPNat' ((m - 1) * n + j))
        (MvPolynomial.map (Int.castRingHom ℚ) (G (m * n) (compCuts m A n E))))
      = (j : MvPolynomial ℕ+ ℚ) * (MvPolynomial.map (Int.castRingHom ℚ) (hgen j) *
          MvPolynomial.map (Int.castRingHom ℚ) (dh ((m - 1) * n + j) (G (m * n) (compCuts m A n E)))) := by
    intro j hj
    have hj0 : 0 < j := (Finset.mem_Icc.mp hj).1
    have hk : 0 < (m - 1) * n + j := by omega
    rw [dh_of_pos hk, hgen_eq_X hj0, ← MvPolynomial.pderiv_map, MvPolynomial.map_X]
    rw [Algebra.smul_def]
    simp [mul_assoc]
  rw [Finset.sum_congr rfl hterm, h, Algebra.smul_def]
  have : (algebraMap ℚ (MvPolynomial ℕ+ ℚ)) ((n : ℚ)⁻¹) * (n : MvPolynomial ℕ+ ℚ) = 1 := by
    rw [← map_natCast (algebraMap ℚ (MvPolynomial ℕ+ ℚ)), ← map_mul, inv_mul_cancel₀ hn', map_one]
  rw [← mul_assoc, this, one_mul]


/-- `eq:two-factor-cancel`, forward implication: for outer factors of weight `m > 0` (cut sets
`A`, `A'`) and inner factors of weight `n > 0` (cut sets `E`, `E'`),
`α ∘ β ∼ α' ∘ β'` implies `α ∼ α'` and `β ∼ β'`.  The outer factors are recovered by
`eq:outer-recovery`, the inner ones by `eq:inner-recovery` (in its integral form, using that
`Λ_ℤ` is torsion free). -/
theorem two_factor_cancel_forward {m n : ℕ} {A A' E E' : Finset ℕ} (hm : 0 < m) (hn : 0 < n)
    (hA : IsCutSet m A) (hA' : IsCutSet m A') (hE : IsCutSet n E) (hE' : IsCutSet n E')
    (h : Equivalent (m * n) (compCuts m A n E) (compCuts m A' n E')) :
    Equivalent m A A' ∧ Equivalent n E E' := by
  unfold Equivalent at h ⊢
  constructor
  · rw [← outer_recovery hn hA hE, ← outer_recovery hn hA' hE', h]
  · have h1 := inner_recovery_int hm hn hA hE
    have h2 := inner_recovery_int hm hn hA' hE'
    have hG : G (m * n) (compCuts m A n E) = G (m * n) (compCuts m A' n E') := h
    rw [hG, h2] at h1
    exact (smul_right_injective Lam hn.ne' h1).symm

/-- `eq:two-factor-cancel`, forward implication through the operators: the recovery operators
`proj n` and `innerOp m n` (over `ℚ`) applied to `G_{α ∘ β}` return `G_α` and `G_β`. -/
theorem two_factor_recovery {m n : ℕ} {A E : Finset ℕ} (hm : 0 < m) (hn : 0 < n)
    (hA : IsCutSet m A) (hE : IsCutSet n E) :
    proj n (G (m * n) (compCuts m A n E)) = G m A ∧
      innerOp m n (MvPolynomial.map (Int.castRingHom ℚ) (G (m * n) (compCuts m A n E)))
        = MvPolynomial.map (Int.castRingHom ℚ) (G n E) :=
  ⟨outer_recovery hn hA hE, inner_recovery hm hn hA hE⟩

/-- `eq:two-factor-cancel`: for displayed products with the same two factor weights `m > 0` and
`n > 0`, `α ∘ β ∼ α' ∘ β'` if and only if `α ∼ α'` and `β ∼ β'`.

**The reverse direction is the paper's `eq:congruence` (in the proof of `thm:main-structure`),
which belongs to recognition and is not proved in this module: it is taken as the explicit
hypothesis `hcong` so that the final assembly can discharge it.**  The forward direction is proved
here (`two_factor_cancel_forward`) and does not use `hcong`. -/
theorem two_factor_cancel_iff {m n : ℕ} {A A' E E' : Finset ℕ} (hm : 0 < m) (hn : 0 < n)
    (hA : IsCutSet m A) (hA' : IsCutSet m A') (hE : IsCutSet n E) (hE' : IsCutSet n E')
    (hcong : Equivalent m A A' → Equivalent n E E' →
      Equivalent (m * n) (compCuts m A n E) (compCuts m A' n E')) :
    Equivalent (m * n) (compCuts m A n E) (compCuts m A' n E') ↔
      Equivalent m A A' ∧ Equivalent n E E' :=
  ⟨two_factor_cancel_forward hm hn hA hA' hE hE', fun ⟨h1, h2⟩ => hcong h1 h2⟩

end SkewRibbonCoarsenings
