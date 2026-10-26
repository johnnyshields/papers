/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationGapReadings
import SkewClassInflation.CellProfiles
import SkewClassInflation.ProfileRowWeights

/-!
# Weight and span of general repeated-inner sources

The full ordered-profile readings in `eq:saturation-readings` of
`shields-2026-skew-class-inflation.tex`.  Periodic internal rows are summed
with their actual multiplicities, including coincident merger values.
Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative
open scoped BigOperators

variable (A : SaturationInner)

private theorem sum_replace_zero {N : ℕ} (hN : 0 < N) (f : Fin N → ℤ) (v : ℤ) :
    (∑ i : Fin N, if i.val = 0 then v else f i) =
      (∑ i : Fin N, f i) + v - f ⟨0, hN⟩ := by
  classical
  let z : Fin N := ⟨0, hN⟩
  have he : (fun i : Fin N => if i.val = 0 then v else f i) =
      fun i => f i + if i = z then v - f z else 0 := by
    funext i
    by_cases hi : i = z
    · subst i
      simp [z]
    · have hv : i.val ≠ 0 := by
        intro hh
        exact hi (Fin.ext hh)
      simp only [hv, hi, ite_false, add_zero]
  rw [he, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  dsimp [z]
  ring

private def cyclicRow (i : Fin A.k) : ℤ :=
  if i.val = 0 then A.merger else A.r i.castSucc

private theorem cyclic_row_sum :
    (∑ i : Fin A.k, A.cyclicRow i) = (∑ i : Fin (A.k + 1), (A.r i : ℤ)) - A.d := by
  have he := sum_replace_zero A.k_pos (fun i : Fin A.k => (A.r i.castSucc : ℤ)) A.merger
  have hz : (⟨0, A.k_pos⟩ : Fin A.k).castSucc = 0 := rfl
  rw [hz] at he
  have hmerger : (A.merger : ℤ) = (A.r 0 : ℤ) + A.r (Fin.last A.k) - A.d := by
    have := A.first_bound
    dsimp [merger]
    omega
  rw [Fin.sum_univ_castSucc]
  change (∑ i : Fin A.k, A.cyclicRow i) = _
  change (∑ i : Fin A.k, if i.val = 0 then (A.merger : ℤ) else A.r i.castSucc) = _
  rw [he, hmerger]
  ring

private theorem cyclic_power_sum (m : ℕ) :
    (∑ i : Fin (m * A.k), A.cyclicRow ⟨i.val % A.k, Nat.mod_lt _ A.k_pos⟩) =
      (m : ℤ) * ∑ i : Fin A.k, A.cyclicRow i := by
  let f : Fin (m * A.k) → ℤ :=
    fun i => A.cyclicRow ⟨i.val % A.k, Nat.mod_lt _ A.k_pos⟩
  rw [← (finProdFinEquiv : Fin m × Fin A.k ≃ Fin (m * A.k)).sum_comp f,
    Fintype.sum_prod_type]
  have he : ∀ i : Fin m, ∀ j : Fin A.k, f (finProdFinEquiv (i, j)) = A.cyclicRow j := by
    intro i j
    change A.cyclicRow ⟨(j.val + A.k * i.val) % A.k, _⟩ = A.cyclicRow j
    congr 1
    apply Fin.ext
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A positive power counts every copy and subtracts only the merged strips. -/
theorem power_row_weight (m : ℕ) (hm : 0 < m) :
    (∑ i : Fin (m * A.k + 1), ((A.power m hm).r i : ℤ)) =
      (m : ℤ) * (∑ i : Fin (A.k + 1), (A.r i : ℤ)) - (m - 1 : ℕ) * (A.d : ℤ) := by
  have hmk : 0 < m * A.k := Nat.mul_pos hm A.k_pos
  have he := sum_replace_zero hmk
    (fun i : Fin (m * A.k) => A.cyclicRow ⟨i.val % A.k, Nat.mod_lt _ A.k_pos⟩) (A.r 0)
  have hrows : ∀ i : Fin (m * A.k),
      ((A.power m hm).r i.castSucc : ℤ) =
        if i.val = 0 then (A.r 0 : ℤ) else A.cyclicRow ⟨i.val % A.k, Nat.mod_lt _ A.k_pos⟩ := by
    intro i
    change (A.powerRows m i.castSucc : ℤ) = _
    unfold powerRows cyclicRow
    simp only [Fin.val_castSucc]
    split_ifs <;> first | rfl | omega
  rw [Fin.sum_univ_castSucc, A.power_last]
  simp_rw [hrows]
  rw [he, A.cyclic_power_sum, A.cyclic_row_sum]
  have hc : A.cyclicRow ⟨0 % A.k, Nat.mod_lt _ A.k_pos⟩ = A.merger := by
    simp [cyclicRow]
  change (m : ℤ) * ((∑ i : Fin (A.k + 1), (A.r i : ℤ)) - A.d) + A.r 0 -
    A.cyclicRow ⟨0 % A.k, Nat.mod_lt _ A.k_pos⟩ + A.r (Fin.last A.k) = _
  rw [hc]
  have hmerger : (A.merger : ℤ) = (A.r 0 : ℤ) + A.r (Fin.last A.k) - A.d := by
    have := A.first_bound
    dsimp [merger]
    omega
  have hsub : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  rw [hmerger, hsub]
  ring

/-- All row cells of the actual source are counted, including coincident numerical row lengths. -/
theorem chain_row_weight (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    (∑ i : Fin ((A.chain a ha l hl).1 + 1), ((A.chain a ha l hl).2.r i : ℤ)) =
      ((a + l.sum : ℕ) : ℤ) * (∑ i : Fin (A.k + 1), (A.r i : ℤ)) -
        (((a + l.sum : ℕ) : ℤ) - (l.length + 1 : ℕ)) * A.d := by
  induction l generalizing a with
  | nil =>
    have he := A.power_row_weight a ha
    have hs : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
    change (∑ i : Fin (a * A.k + 1), ((A.power a ha).r i : ℤ)) = _
    simpa only [List.sum_nil, Nat.add_zero, List.length_nil, Nat.zero_add,
      Nat.cast_one, hs] using he
  | cons b l ih =>
    let P := A.power a ha
    let Q := A.chain b (hl b List.mem_cons_self) l
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    have hp : A.d < P.r (Fin.last (a * A.k)) := A.power_rows_above_seam a ha _
    have hq : A.d < Q.2.r 0 := by
      rw [A.chain_first]
      have := A.first_bound
      omega
    change (∑ i, ((Profile.join P Q.2 A.d hp hq).r i : ℤ)) = _
    rw [Profile.join_row_weight]
    have hleft := A.power_row_weight a ha
    have hright := ih b (hl b List.mem_cons_self)
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    change (∑ i, (P.r i : ℤ)) = _ at hleft
    change (∑ i, (Q.2.r i : ℤ)) = _ at hright
    rw [hleft, hright]
    have hs : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
    simp only [hs, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- The full general source weight is exactly the displayed copy-minus-merger formula. -/
theorem diagram_row_weight {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (∑ i : Fin ((A.diagram α hM).1 + 1), ((A.diagram α hM).2.r i : ℤ)) =
      (M : ℤ) * (∑ i : Fin (A.k + 1), (A.r i : ℤ)) -
        ((M : ℤ) - α.length) * A.d := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    have hs : a + l.sum = M := by simpa only [he, List.sum_cons] using α.blocks_sum
    rw [A.chain_row_weight, hs]
    simp only [Composition.length, he, List.length_cons]

/-- The manuscript's span increment is measured from the actual original inner row weight. -/
def spanIncrement : ℤ := (∑ i : Fin (A.k + 1), (A.r i : ℤ)) - A.k * A.c - A.d

/-- The strict endpoint bounds make the actual span increment positive. -/
theorem spanIncrement_pos : 0 < A.spanIncrement := by
  have hs := profile_span_sum A.profile
  have hz := A.profile.zeta_nonneg 0
  have hr := A.profile.xi_sub_zeta 0
  have hb : (A.c : ℤ) + A.d < A.r 0 := by exact_mod_cast A.first_bound
  have hg : (∑ j : Fin A.k, (A.profile.g j : ℤ)) = (A.k : ℤ) * A.c := by
    simp [profile]
  rw [hg] at hs
  change A.profile.xi 0 = (∑ i : Fin (A.k + 1), (A.r i : ℤ)) -
    (A.k : ℤ) * A.c at hs
  change A.profile.xi 0 - A.profile.zeta 0 = (A.r 0 : ℤ) at hr
  unfold spanIncrement
  linarith only [hs, hz, hr, hb]

/-- The full span of an individual repeated power is its copy multiple plus one end mark. -/
theorem power_span (m : ℕ) (hm : 0 < m) :
    (A.power m hm).xi 0 = (m : ℤ) * A.spanIncrement + A.d := by
  rw [profile_span_sum, A.power_row_weight]
  have hg : (∑ j : Fin (m * A.k), ((A.power m hm).g j : ℤ)) =
      (m * A.k : ℕ) * (A.c : ℤ) := by
    simp [power]
  rw [hg]
  have hs : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  rw [hs, spanIncrement]
  push_cast
  ring

/-- The private largest index of each actual repeated power has its exact affine copy value. -/
theorem power_largest_label (m : ℕ) (hm : 0 < m) :
    (A.power m hm).toBetaDiagram.largestLabel = (m : ℤ) * A.spanIncrement + A.d := by
  change (A.power m hm).xi 0 - (A.power m hm).zeta (Fin.last (m * A.k)) = _
  rw [Gluing.Profile.zeta_last, sub_zero, A.power_span]

/-- The full normalized source span is the copy multiple of the increment plus one end mark. -/
theorem diagram_span {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (A.diagram α hM).2.xi 0 = (M : ℤ) * A.spanIncrement + A.d := by
  rw [profile_span_sum, A.diagram_row_weight]
  have hg := A.diagram_gap_sum (fun j => (j : ℤ)) α hM
  simp only [nsmul_eq_mul, Nat.cast_mul] at hg
  rw [hg]
  have hlen : 0 < α.length := by
    have hn := A.diagram_row_count α hM
    unfold diagram at hn
    split at hn
    · rename_i he
      have hs := α.blocks_sum
      rw [he] at hs
      simp only [List.sum_nil] at hs
      omega
    · rename_i a l he
      simp only [Composition.length, he, List.length_cons]
      omega
  have hs : ((α.length - 1 : ℕ) : ℤ) = (α.length : ℤ) - 1 := by omega
  rw [hs, spanIncrement]
  ring

/-- The largest actual Jacobi--Trudi label has the exact general source span. -/
theorem diagram_largest_label {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (A.diagram α hM).2.toBetaDiagram.largestLabel = (M : ℤ) * A.spanIncrement + A.d := by
  change (A.diagram α hM).2.xi 0 -
    (A.diagram α hM).2.zeta (Fin.last (A.diagram α hM).1) = _
  rw [Gluing.Profile.zeta_last, sub_zero, A.diagram_span]

/-- Differentiation extracts the displayed maximal-generator coefficient with its full sign. -/
theorem diagram_maximal_derivative {M : ℕ} (α : Composition M) (hM : 0 < M) :
    let D := (A.diagram α hM).2.toBetaDiagram
    let j : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    (-1 : CompleteRing) ^ (A.diagram α hM).1 *
      (MvPolynomial.pderiv j D.schur : CompleteRing) =
        complete A.c ^ (M * A.k) * complete A.d ^ (α.length - 1) := by
  intro D j
  have he : (MvPolynomial.pderiv j D.schur : CompleteRing) = D.cornerCoefficient :=
    D.pderiv_schur_largest
  rw [he]
  exact A.diagram_corner_coefficient α hM

end SkewClassInflation.SaturationInner
