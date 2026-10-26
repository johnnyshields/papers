/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/TriangleIdentity.lean
import SkewRibbonCoarsenings.Labels
import SkewRibbonCoarsenings.Setting

/-!
# The triangle identity

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:balance`, subsection "The triangle
identity" (`eq:uv`, the midpoint remark, `eq:three-difference`).

For two compositions of weight `n` with cut sets `S, S'` and equal two-block inventories
(`TwoBlockEq`), the functions `τ`, `u`, `v` of `eq:uv` satisfy: `u, v` are odd, ternary, with
disjoint supports.  The three-block labeled difference `K_b(a) - K_c(a)` is
`-∑_{i<j} (u(a_i) v(a_j) + v(a_i) u(a_j))` (`eq:three-difference`).
Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

/-- The two-block inventories of the compositions with cut sets `S, S'` agree: the ordinary
coefficients of `h_p h_q` (`p + q = n`) in `G_β` and `G_γ` coincide. -/
def TwoBlockEq (n : ℕ) (S S' : Finset ℕ) : Prop :=
  ∀ p q : ℕ, 0 < p → 0 < q → p + q = n → mult n S {p, q} = mult n S' {p, q}

/-- The symmetrization `τ(x) = b(x) + b(-x)` of `eq:uv`. -/
def tauFun (n : ℕ) (S : Finset ℕ) (x : ZMod n) : ℤ := cutInd n S x + cutInd n S (-x)

/-- The odd part `x(t) = b(t) - b(-t)` of the cut indicator (`sec:balance`). -/
def oddPart (n : ℕ) (S : Finset ℕ) (x : ZMod n) : ℤ := cutInd n S x - cutInd n S (-x)

/-- The three-term cross sum `∑_{i<j} (u(a_i) v(a_j) + v(a_i) u(a_j))` of `eq:three-difference`. -/
def triangleSum {n : ℕ} (u v : ZMod n → ℤ) (x y z : ZMod n) : ℤ :=
  (u x * v y + v x * u y) + (u x * v z + v x * u z) + (u y * v z + v y * u z)

section Basic

variable {n : ℕ} {S : Finset ℕ}

theorem cutInd_zero (hS : IsCutSet n S) : cutInd n S 0 = 0 := by
  unfold cutInd
  have : (0 : ℕ) ∉ S := fun h => by have := Finset.mem_Ioo.mp (hS h); omega
  simp [this]

theorem cutInd_eq_zero_or_one (x : ZMod n) : cutInd n S x = 0 ∨ cutInd n S x = 1 := by
  unfold cutInd; split_ifs <;> simp

theorem cutInd_natCast {t : ℕ} (ht : t < n) :
    cutInd n S (t : ZMod n) = if t ∈ S then 1 else 0 := by
  unfold cutInd
  rw [ZMod.val_natCast_of_lt ht]

theorem neg_natCast_eq {t : ℕ} (ht : t ≤ n) : -(t : ZMod n) = ((n - t : ℕ) : ZMod n) := by
  rw [Nat.cast_sub ht, ZMod.natCast_self]; ring

theorem cutInd_neg_natCast (hS : IsCutSet n S) {t : ℕ} (ht : t < n) :
    cutInd n S (-(t : ZMod n)) = if n - t ∈ S then 1 else 0 := by
  by_cases h : t = 0
  · subst h
    have hn : n ∉ S := fun h => by have := Finset.mem_Ioo.mp (hS h); omega
    simp [cutInd_zero hS, hn]
  · rw [neg_natCast_eq ht.le]
    exact cutInd_natCast (by omega)

end Basic

section Gaps

theorem gaps_singleton {n t : ℕ} (ht : t < n) (h0 : 0 < t) : gaps n {t} = {t, n - t} := by
  unfold gaps
  have h : n ∉ ({t} : Finset ℕ) := by simp; omega
  rw [Finset.insert_val_of_notMem h]
  simp only [Finset.singleton_val, Multiset.map_cons, Multiset.map_singleton]
  have e1 : ((({t} : Finset ℕ).filter (· < n)).sup id) = t := by
    simp [Finset.filter_singleton, ht]
  have e2 : ((({t} : Finset ℕ).filter (· < t)).sup id) = 0 := by
    simp [Finset.filter_singleton]
  rw [e1, e2, Nat.sub_zero, Multiset.pair_comm]
  rfl

theorem card_gaps {n : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.Ioo 0 n) :
    (gaps n T).card = T.card + 1 := by
  unfold gaps
  rw [Multiset.card_map]
  show (insert n T).card = _
  rw [Finset.card_insert_of_notMem]
  intro h; have := Finset.mem_Ioo.mp (hT h); omega

theorem multiset_pair_eq_pair {a b c d : ℕ} :
    ({a, b} : Multiset ℕ) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a ∈ ({c, d} : Multiset ℕ) := h ▸ (by simp)
    have hb : b ∈ ({c, d} : Multiset ℕ) := h ▸ (by simp)
    have hc : c ∈ ({a, b} : Multiset ℕ) := h.symm ▸ (by simp)
    have hd : d ∈ ({a, b} : Multiset ℕ) := h.symm ▸ (by simp)
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha hb hc hd
    have := congrArg (Multiset.count a) h
    have := congrArg (Multiset.count b) h
    simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at *
    omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Multiset.pair_comm _ _

/-- The ordinary two-block coefficient: for `p + q = n`, `m_β(p, q)` is the number of retained
single cuts `t ∈ S` with block lengths `{p, q}`. -/
theorem mult_two {n : ℕ} {S : Finset ℕ} (hS : IsCutSet n S) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q = n) :
    mult n S {p, q} =
      if p = q then (if p ∈ S then 1 else 0)
      else (if p ∈ S then 1 else 0) + (if q ∈ S then 1 else 0) := by
  classical
  have hS' : S ⊆ Finset.Ioo 0 n := hS
  have key : S.powerset.filter (fun T => gaps n T = {p, q}) =
      (S.filter fun t => t = p ∨ t = q).image (fun t => ({t} : Finset ℕ)) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hTS, hg⟩
      have hcard := card_gaps (hTS.trans hS')
      rw [hg] at hcard
      have h2 : T.card = 1 := by
        have : ({p, q} : Multiset ℕ).card = 2 := by simp
        omega
      obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp h2
      have ht : t ∈ S := hTS (Finset.mem_singleton_self t)
      have ht' := Finset.mem_Ioo.mp (hS' ht)
      rw [gaps_singleton ht'.2 ht'.1, multiset_pair_eq_pair] at hg
      refine ⟨t, ⟨ht, ?_⟩, rfl⟩
      omega
    · rintro ⟨t, ⟨ht, hpt⟩, rfl⟩
      have ht' := Finset.mem_Ioo.mp (hS' ht)
      refine ⟨Finset.singleton_subset_iff.mpr ht, ?_⟩
      rw [gaps_singleton ht'.2 ht'.1, multiset_pair_eq_pair]
      omega
  unfold mult
  rw [key, Finset.card_image_of_injective _ Finset.singleton_injective]
  by_cases hpq' : p = q
  · subst hpq'
    simp only [or_self, if_true]
    rw [Finset.filter_eq' S p]
    split_ifs <;> simp
  · rw [if_neg hpq', Finset.filter_or, Finset.filter_eq' S p, Finset.filter_eq' S q,
      Finset.card_union_of_disjoint]
    · split_ifs <;> simp
    · rw [Finset.disjoint_left]
      intro x hx hx'
      split_ifs at hx hx' <;> simp_all

end Gaps

section Odd

variable {n : ℕ} {S S' : Finset ℕ}

/-- `tau_eq` of `eq:uv`: equal two-block inventories give `τ_b = τ_c`.  For `x = t` with
`0 < t < n` the two-block coefficient of `h_t h_{n-t}` is `b(t)` at a midpoint and
`b(t) + b(n-t)` otherwise. -/
theorem tau_eq_of_twoBlockEq (hn : 0 < n) (hS : IsCutSet n S) (hS' : IsCutSet n S')
    (h : TwoBlockEq n S S') (x : ZMod n) : tauFun n S x = tauFun n S' x := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hx : x = ((x.val : ℕ) : ZMod n) := (ZMod.natCast_zmod_val x).symm
  have hlt : x.val < n := ZMod.val_lt x
  unfold tauFun
  rw [hx]
  by_cases h0 : x.val = 0
  · rw [h0]
    simp [cutInd_zero hS, cutInd_zero hS']
  · have hq : x.val < n := hlt
    have hmem := h x.val (n - x.val) (by omega) (by omega) (by omega)
    rw [mult_two hS (by omega) (by omega) (by omega),
      mult_two hS' (by omega) (by omega) (by omega)] at hmem
    rw [cutInd_natCast hlt, cutInd_neg_natCast hS hlt, cutInd_natCast hlt,
      cutInd_neg_natCast hS' hlt]
    by_cases heq : x.val = n - x.val
    · rw [if_pos heq, if_pos heq] at hmem
      rw [← heq]
      split_ifs at hmem ⊢ <;> omega
    · rw [if_neg heq, if_neg heq] at hmem
      split_ifs at hmem ⊢ <;> omega

variable (htau : ∀ x : ZMod n, cutInd n S x + cutInd n S (-x) = cutInd n S' x + cutInd n S' (-x))
include htau

/-- `eq:uv`: `u` is odd. -/
theorem uFun_odd : IsOdd (uFun n S S') := by
  intro x
  have := htau x
  unfold uFun
  rw [neg_neg]
  linarith

/-- `eq:uv`: `v` is odd. -/
theorem vFun_odd : IsOdd (vFun n S S') := by
  intro x
  have := htau x
  unfold vFun
  linarith

/-- `eq:uv`: `u` and `v` have disjoint supports, `u(x) v(x) = 0`. -/
theorem uFun_mul_vFun (x : ZMod n) : uFun n S S' x * vFun n S S' x = 0 := by
  have := htau x
  unfold uFun vFun
  rcases cutInd_eq_zero_or_one (S := S) x with h1 | h1 <;>
  rcases cutInd_eq_zero_or_one (S := S) (-x) with h2 | h2 <;>
  rcases cutInd_eq_zero_or_one (S := S') x with h3 | h3 <;>
  rcases cutInd_eq_zero_or_one (S := S') (-x) with h4 | h4 <;>
  simp_all

end Odd

theorem uFun_ternary {n : ℕ} (S S' : Finset ℕ) (x : ZMod n) :
    uFun n S S' x ∈ ({-1, 0, 1} : Set ℤ) := by
  unfold uFun
  rcases cutInd_eq_zero_or_one (S := S) x with h1 | h1 <;>
  rcases cutInd_eq_zero_or_one (S := S') (-x) with h2 | h2 <;>
  simp [h1, h2]

theorem vFun_ternary {n : ℕ} (S S' : Finset ℕ) (x : ZMod n) :
    vFun n S S' x ∈ ({-1, 0, 1} : Set ℤ) := by
  unfold vFun
  rcases cutInd_eq_zero_or_one (S := S) x with h1 | h1 <;>
  rcases cutInd_eq_zero_or_one (S := S') x with h2 | h2 <;>
  simp [h1, h2]

section Three

theorem sum_perm_fin3 (F : Fin 3 → Fin 3 → Fin 3 → ℤ) :
    ∑ π : Equiv.Perm (Fin 3), F (π 0) (π 1) (π 2) =
      F 0 1 2 + F 0 2 1 + F 1 0 2 + F 1 2 0 + F 2 0 1 + F 2 1 0 := by
  have : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 1 2, Equiv.swap 0 1, finRotate 3, (finRotate 3)⁻¹, Equiv.swap 0 2} := by
    decide
  rw [this]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have e1 : ((1 : Equiv.Perm (Fin 3)) 0, (1 : Equiv.Perm (Fin 3)) 1,
      (1 : Equiv.Perm (Fin 3)) 2) = (0, 1, 2) := by decide
  have e2 : ((Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 0, (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 1,
      (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 2) = (0, 2, 1) := by decide
  have e3 : ((Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 0, (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 1,
      (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 2) = (1, 0, 2) := by decide
  have e4 : ((finRotate 3 : Equiv.Perm (Fin 3)) 0, (finRotate 3 : Equiv.Perm (Fin 3)) 1,
      (finRotate 3 : Equiv.Perm (Fin 3)) 2) = (1, 2, 0) := by decide
  have e5 : (((finRotate 3)⁻¹ : Equiv.Perm (Fin 3)) 0, ((finRotate 3)⁻¹ : Equiv.Perm (Fin 3)) 1,
      ((finRotate 3)⁻¹ : Equiv.Perm (Fin 3)) 2) = (2, 0, 1) := by decide
  have e6 : ((Equiv.swap 0 2 : Equiv.Perm (Fin 3)) 0, (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) 1,
      (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) 2) = (2, 1, 0) := by decide
  simp only [Prod.mk.injEq] at e1 e2 e3 e4 e5 e6
  rw [e1.1, e1.2.1, e1.2.2, e2.1, e2.2.1, e2.2.2, e3.1, e3.2.1, e3.2.2, e4.1, e4.2.1, e4.2.2,
    e5.1, e5.2.1, e5.2.2, e6.1, e6.2.1, e6.2.2]
  ring

theorem K_three (S : Finset ℕ) (a : Fin 3 → ℕ) :
    K S a = ∑ π : Equiv.Perm (Fin 3),
      if (a (π 0) ∈ S ∧ a (π 0) + a (π 1) ∈ S) then 1 else 0 := by
  unfold K
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro π _
  have e1 : partialSum a π 1 = a (π 0) := by
    simp [partialSum, Finset.sum_filter]
  have e2 : partialSum a π 2 = a (π 0) + a (π 1) := by
    simp only [partialSum, Finset.sum_filter, Fin.sum_univ_three]
    simp
  have : (∀ j < 3, 0 < j → partialSum a π j ∈ S) ↔ (a (π 0) ∈ S ∧ a (π 0) + a (π 1) ∈ S) := by
    constructor
    · intro h; exact ⟨e1 ▸ h 1 (by omega) (by omega), e2 ▸ h 2 (by omega) (by omega)⟩
    · rintro ⟨h1, h2⟩ j hj hj0
      interval_cases j
      · rw [e1]; exact h1
      · rw [e2]; exact h2
  simp only [this]

variable {n m : ℕ} {S S' : Finset ℕ}

/-- The label `a_i` as an element of `ℤ/n`. -/
def lab (n : ℕ) (a : Fin 3 → ℕ) (i : Fin 3) : ZMod n := ((a i : ℕ) : ZMod n)

/-- Pairing opposite orders of the three labeled parts (the displayed formula before
`eq:three-difference`, without the factor `1/2`): `K_b(a) = ∑_{i<j} (b(a_i) b(-a_j) +
b(-a_i) b(a_j))`. -/
theorem K_three_eq (hS : IsCutSet n S) {a : Fin 3 → ℕ} (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = n) :
    (K S a : ℤ) = (cutInd n S (lab n a 0) * cutInd n S (-lab n a 1) +
        cutInd n S (-lab n a 0) * cutInd n S (lab n a 1)) +
      (cutInd n S (lab n a 0) * cutInd n S (-lab n a 2) +
        cutInd n S (-lab n a 0) * cutInd n S (lab n a 2)) +
      (cutInd n S (lab n a 1) * cutInd n S (-lab n a 2) +
        cutInd n S (-lab n a 1) * cutInd n S (lab n a 2)) := by
  have hlt : ∀ i, a i < n := by
    intro i
    have h3 : ∑ j, a j = a 0 + a 1 + a 2 := Fin.sum_univ_three a
    have h0 := ha 0; have h1 := ha 1; have h2 := ha 2
    fin_cases i <;> simp <;> omega
  have hK : (K S a : ℤ) = ∑ π : Equiv.Perm (Fin 3),
      cutInd n S (lab n a (π 0)) * cutInd n S (-lab n a (π 2)) := by
    rw [K_three, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro π _
    have hs : a (π 0) + a (π 1) + a (π 2) = n := by
      have := Equiv.sum_comp π a
      rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
      rw [Fin.sum_univ_three] at hsum
      omega
    unfold lab
    rw [cutInd_natCast (hlt _), cutInd_neg_natCast hS (hlt _)]
    have : n - a (π 2) = a (π 0) + a (π 1) := by omega
    rw [this]
    by_cases h1 : a (π 0) ∈ S <;> by_cases h2 : a (π 0) + a (π 1) ∈ S <;> simp [h1, h2]
  rw [hK, sum_perm_fin3 (fun i j k => cutInd n S (lab n a i) * cutInd n S (-lab n a k))]
  ring

theorem pair_identity (B B' C C' B2 B2' C2 C2' : ℤ) (h1 : B + B' = C + C')
    (h2 : B2 + B2' = C2 + C2') :
    (B * B2' + B' * B2) - (C * C2' + C' * C2) =
      -((B - C') * (B2 - C2) + (B - C) * (B2 - C2')) := by
  have e1 : B' = C + C' - B := by linarith
  have e2 : B2' = C2 + C2' - B2 := by linarith
  subst e1 e2
  ring

/-- `eq:three-difference`: for positive `a, b', c'` summing to `n` (the labels `a 0, a 1, a 2`) and
two compositions with equal two-block inventories,
`K_b(a) - K_c(a) = -∑_{i<j} (u(a_i) v(a_j) + v(a_i) u(a_j))`.  The hypothesis is the equality
`τ_b = τ_c` of `eq:uv`, which `tau_eq_of_twoBlockEq` derives from the two-block inventories. -/
theorem three_difference (hS : IsCutSet n S) (hS' : IsCutSet n S')
    (htau : ∀ x : ZMod n, cutInd n S x + cutInd n S (-x) = cutInd n S' x + cutInd n S' (-x))
    {a : Fin 3 → ℕ} (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) :
    (K S a : ℤ) - K S' a =
      -triangleSum (uFun n S S') (vFun n S S') (lab n a 0) (lab n a 1) (lab n a 2) := by
  rw [K_three_eq hS ha hsum, K_three_eq hS' ha hsum]
  unfold triangleSum uFun vFun
  have p01 := pair_identity _ _ _ _ _ _ _ _ (htau (lab n a 0)) (htau (lab n a 1))
  have p02 := pair_identity _ _ _ _ _ _ _ _ (htau (lab n a 0)) (htau (lab n a 2))
  have p12 := pair_identity _ _ _ _ _ _ _ _ (htau (lab n a 1)) (htau (lab n a 2))
  linarith

/-- The midpoint remark (`sec:balance`): for `n = 2m`, `τ(m) = 2 b(m)`, while the ordinary
two-block coefficient `m_β(m, m)` is `b(m)`. -/
theorem midpoint_remark (hS : IsCutSet (2 * m) S) (hm : 0 < m) :
    tauFun (2 * m) S (m : ZMod (2 * m)) = 2 * cutInd (2 * m) S (m : ZMod (2 * m)) ∧
      (mult (2 * m) S {m, m} : ℤ) = cutInd (2 * m) S (m : ZMod (2 * m)) := by
  have hneg : -((m : ℕ) : ZMod (2 * m)) = (m : ZMod (2 * m)) := by
    rw [neg_natCast_eq (by omega)]
    congr 1; omega
  refine ⟨?_, ?_⟩
  · unfold tauFun; rw [hneg]; ring
  · rw [mult_two hS hm hm (by omega), if_pos rfl, cutInd_natCast (by omega)]
    split_ifs <;> simp

/-- The ordinary two-block coefficient away from a midpoint is `τ(t) = b(t) + b(-t)`: for
`0 < t < n`, `2 t ≠ n`, `m_β(t, n - t) = τ(t)`. -/
theorem twoBlock_coeff_eq_tau (hS : IsCutSet n S) {t : ℕ} (ht0 : 0 < t) (htn : t < n)
    (hmid : t ≠ n - t) :
    (mult n S {t, n - t} : ℤ) = tauFun n S (t : ZMod n) := by
  unfold tauFun
  rw [mult_two hS ht0 (by omega) (by omega), if_neg hmid, cutInd_natCast htn,
    cutInd_neg_natCast hS htn]
  split_ifs <;> simp

end Three

end SkewRibbonCoarsenings
