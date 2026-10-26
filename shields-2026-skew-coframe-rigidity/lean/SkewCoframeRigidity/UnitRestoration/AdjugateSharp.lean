/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.AdjugateOrderMain

/-!
# Sharpness of the adjugate orders

Complements `adjugate_difference_order` and `contraction_order_ge` in
`shields-2026-skew-coframe-rigidity.tex`, `sc:splice-nonzero`, with the cases in which the order
bounds are attained.  Throughout, `k` is the number of core rows of `V`, `L` its largest label,
and `adjDifference V s` compares the array of `V` with the array of its half-turn translated by `s`.

* A unit value `b` of `V` gives the entry of the array at column label `b` and row label `b`
  exactly order `k`, with leading coefficient `σ s_{core}` (`adjArray_unit_coeff`).  An entry
  with no column or no row of that label is `0`.  So if exactly one of `b` and `L - s - b` is a
  unit value of `V`, the difference has order exactly `k` at `(b, b)`
  (`adjDifference_unit_exact`); for a self-rotating core about `M` this is the alignment
  `s = L - M`, and the unit values `b` with exactly one of `b`, `M - b` a unit value are the
  positions where the weights `ρ_b` of the paper are nonzero.
* If the core is not its own half-turn, then for every translation `s` some entry of the
  difference has order exactly `k - 1` (`adjDifference_core_exact`).
* Contractions: the family consisting of the single entry, with coefficient one, has order
  exactly `λ`, so the bound `λ` of `contraction_order_ge` is attained
  (`contraction_unit_exact`, `contraction_core_exact`).  Exactness for a general family of
  coefficients is not asserted.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Matrix Polynomial

local notation "CR" => SkewCofactorIndependence.CompleteRing

section Unit

theorem adjArray_unit_FF {m : ℕ} (D : BetaDiagram m) {b : ℤ} (hb : b ∈ unitVals D) :
    ∃ (σ : ℤˣ) (q : FF[X]), adjArrayOf letterSeqF D b b =
      Polynomial.X ^ coreCount D * (Polynomial.C (((σ : ℤ) : FF) *
        algebraMap CR FF (coreDiagram D).schur) + Polynomial.X * q) := by
  classical
  obtain ⟨i, j, hi, hj⟩ := mem_unitVals.mp hb
  have hK : (coreMatrix letterSeqF D.row D.col (corePairing D)).det ≠ 0 := by
    rw [det_coreMatrix_eq]
    exact (map_ne_zero_iff _ algebraMap_injective_FF).mpr (BetaDiagram.schur_ne_zero _)
  obtain ⟨σ, hσ⟩ := adjugate_scaledMatrix_expansion letterSeqF D.row D.col
    D.row_strictAnti.injective D.col_strictAnti.injective (unitPairing D) (unitPairing_spec D)
    (corePairing D) hK
  have hiU : i ∈ unitRows D.row D.col := ⟨j, by rw [hi, hj]⟩
  have hjU : j ∈ unitCols D.row D.col := ⟨i, by rw [hi, hj]⟩
  have hji : j = (unitPairing D ⟨i, hiU⟩).1 := by
    apply D.col_strictAnti.injective
    rw [← unitPairing_spec D ⟨i, hiU⟩]
    exact (hj.trans hi.symm)
  obtain ⟨q, hq⟩ := (hσ i j).2.2 hiU hjU hji
  have hcard : (Finset.univ.filter fun l => l ∉ unitRows D.row D.col).card = coreCount D :=
    card_coreRows_eq_count D
  refine ⟨σ, q, ?_⟩
  have e : adjArrayOf letterSeqF D b b = adjArrayOf letterSeqF D (D.col j) (D.row i) := by
    rw [hi, hj]
  rw [e, adjArrayOf_apply, hq, hcard, det_coreMatrix_eq]

theorem adjArray_unit_coeff {m : ℕ} (D : BetaDiagram m) {b : ℤ} (hb : b ∈ unitVals D) :
    (Polynomial.X : CR[X]) ^ coreCount D ∣ adjArray D b b ∧
      (adjArray D b b).coeff (coreCount D) ≠ 0 := by
  obtain ⟨σ, h1, -⟩ := adjArray_order D
  obtain ⟨σ', q, hq⟩ := adjArray_unit_FF D hb
  have hnc : ¬ (IsCoreColLabel D b ∧ IsCoreRowLabel D b) := by
    rintro ⟨⟨j, hj, hjb⟩, -⟩
    obtain ⟨i, -, hi, -⟩ := mem_unitVals.mp hb
    exact hj ⟨i, by rw [hi, hjb]⟩
  refine ⟨h1 b b hnc, fun h0 => ?_⟩
  have hc := congrArg (fun p => p.coeff (coreCount D)) (map_adjArray D b b)
  simp only [Polynomial.coeff_map, h0, map_zero, hq] at hc
  rw [Polynomial.coeff_X_pow_mul'] at hc
  simp only [le_refl, if_true, Nat.sub_self] at hc
  rw [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero,
    add_zero] at hc
  have hne : (((σ' : ℤ) : FF) * algebraMap CR FF (coreDiagram D).schur) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Units.ne_zero σ')
      ((map_ne_zero_iff _ algebraMap_injective_FF).mpr (BetaDiagram.schur_ne_zero _))
  exact hne hc.symm

theorem adjArray_diag_eq_zero {m : ℕ} (D : BetaDiagram m) {b : ℤ} (hb : b ∉ unitVals D) :
    adjArray D b b = 0 := by
  rcases adjArrayOf_eq_zero_or letterSeq D b b with h | ⟨j, i, hj, hi⟩
  · exact h
  · exact absurd (mem_unitVals.mpr ⟨i, j, hi, hj⟩) hb

/-- **Exact order at a unit value.**  If exactly one of `b` and `L - s - b` is a unit value of
`V`, the entry of `adjDifference V s` at column label `b` and row label `b` has order exactly
`k`. -/
theorem adjDifference_unit_exact {n : ℕ} (V : BetaDiagram (n + 1)) (s b : ℤ)
    (h : ¬ (b ∈ unitVals V ↔ V.largestLabel - s - b ∈ unitVals V)) :
    (Polynomial.X : CR[X]) ^ coreCount V ∣ adjDifference V s b b ∧
      ¬ (Polynomial.X : CR[X]) ^ (coreCount V + 1) ∣ adjDifference V s b b := by
  have hrot : adjArray V.rotation (b + s) (b + s) = adjArray V (V.largestLabel - s - b)
      (V.largestLabel - s - b) := by
    unfold adjArray
    rw [adjArrayOf_rotation]
    congr 1 <;> ring
  unfold adjDifference
  rw [hrot]
  have key : ∀ p : CR[X], (Polynomial.X : CR[X]) ^ coreCount V ∣ p → p.coeff (coreCount V) ≠ 0 →
      (Polynomial.X : CR[X]) ^ coreCount V ∣ p ∧ ¬ (Polynomial.X : CR[X]) ^ (coreCount V + 1) ∣ p := by
    intro p h1 h2
    refine ⟨h1, fun h3 => h2 ?_⟩
    exact (Polynomial.X_pow_dvd_iff.mp h3) _ (Nat.lt_succ_self _)
  by_cases hb : b ∈ unitVals V
  · have hb' : V.largestLabel - s - b ∉ unitVals V := fun h' => h ⟨fun _ => h', fun _ => hb⟩
    rw [adjArray_diag_eq_zero V hb', sub_zero]
    exact key _ (adjArray_unit_coeff V hb).1 (adjArray_unit_coeff V hb).2
  · have hb' : V.largestLabel - s - b ∈ unitVals V := by
      by_contra h'
      exact h ⟨fun x => absurd x hb, fun x => absurd x h'⟩
    rw [adjArray_diag_eq_zero V hb, zero_sub]
    obtain ⟨d1, d2⟩ := adjArray_unit_coeff V hb'
    exact key _ ((dvd_neg).mpr d1) (by rw [Polynomial.coeff_neg]; exact neg_ne_zero.mpr d2)

end Unit

section CoreExact

theorem fullMatrixOf_letterSeq {b : ℕ} (B : BetaDiagram b) :
    fullMatrixOf letterSeq B = B.matrix := by
  ext i j
  simp [fullMatrixOf, BetaDiagram.matrix, letterOf_letterSeq]

theorem det_adjCore_ne_zero {m : ℕ} (D : BetaDiagram m) :
    (adjugate (fullMatrixOf letterSeq (coreDiagram D))).det ≠ 0 := by
  rw [Matrix.det_adjugate, fullMatrixOf_letterSeq]
  exact pow_ne_zero _ (BetaDiagram.schur_ne_zero _)

theorem adjArray_coeff_core {n : ℕ} (V : BetaDiagram (n + 1)) :
    ∃ σ : ℤˣ,
      (∀ c r, ¬ (IsCoreColLabel V c ∧ IsCoreRowLabel V r) →
        (adjArray V c r).coeff (coreCount V - 1) = 0) ∧
      (∀ j i : Fin (coreCount V),
        (adjArray V (V.col (coreColEmb V j)) (V.row (coreRowEmb V i))).coeff (coreCount V - 1) =
          ((σ : ℤ) : CR) * adjugate (fullMatrixOf letterSeq (coreDiagram V)) j i) := by
  obtain ⟨σ, h1, h2⟩ := adjArray_order V
  have hk : 0 < coreCount V := coreCount_pos_of_pos V (Nat.succ_pos n)
  refine ⟨σ, fun c r hcr => ?_, fun j i => ?_⟩
  · exact (Polynomial.X_pow_dvd_iff.mp (h1 c r hcr)) _ (by omega)
  · have := (Polynomial.X_pow_dvd_iff.mp (h2 j i)) (coreCount V - 1) (by omega)
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      Polynomial.coeff_C_zero] at this
    exact sub_eq_zero.mp this

theorem adjDifference_eq {n : ℕ} (V : BetaDiagram (n + 1)) (s c r : ℤ) :
    adjDifference V s c r = adjArray V c r -
      adjArray V (V.largestLabel - s - r) (V.largestLabel - s - c) := by
  unfold adjDifference adjArray
  rw [adjArrayOf_rotation]
  congr 2 <;> ring

/-- **Exact order for a core that is not its own half-turn.**  For every translation `s` some
entry of the difference of the adjugate arrays has order exactly `k - 1`. -/
theorem adjDifference_core_exact {n : ℕ} (V : BetaDiagram (n + 1))
    (hns : ¬ (coreDiagram V).Symmetric) (s : ℤ) :
    ∃ c r : ℤ, (Polynomial.X : CR[X]) ^ (coreCount V - 1) ∣ adjDifference V s c r ∧
      ¬ (Polynomial.X : CR[X]) ^ coreCount V ∣ adjDifference V s c r := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ c r, (Polynomial.X : CR[X]) ^ coreCount V ∣ adjDifference V s c r :=
    fun c r => hcon c r ((adjugate_difference_order V).1 s c r)
  set t := V.largestLabel - s with ht
  obtain ⟨σ, hz, hc⟩ := adjArray_coeff_core V
  have hk : 0 < coreCount V := coreCount_pos_of_pos V (Nat.succ_pos n)
  have hcoef : ∀ c r, (adjArray V c r).coeff (coreCount V - 1) =
      (adjArray V (t - r) (t - c)).coeff (coreCount V - 1) := by
    intro c r
    have := (Polynomial.X_pow_dvd_iff.mp (hall c r)) (coreCount V - 1) (by omega)
    rw [adjDifference_eq, Polynomial.coeff_sub] at this
    exact sub_eq_zero.mp this
  have hP : ∀ c r, (adjArray V c r).coeff (coreCount V - 1) ≠ 0 →
      IsCoreColLabel V c ∧ IsCoreRowLabel V r := by
    intro c r h
    by_contra hn
    exact h (hz c r hn)
  set B := coreDiagram V with hB
  have hσ : ((σ : ℤ) : CR) ≠ 0 := by exact_mod_cast Units.ne_zero σ
  have hdet := det_adjCore_ne_zero V
  have hI : ∀ j, ∃ i, adjugate (fullMatrixOf letterSeq B) j i ≠ 0 := by
    intro j
    by_contra hn
    push Not at hn
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero j hn)
  have hII : ∀ i, ∃ j, adjugate (fullMatrixOf letterSeq B) j i ≠ 0 := by
    intro i
    by_contra hn
    push Not at hn
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero i hn)
  have star : ∀ j i, adjugate (fullMatrixOf letterSeq B) j i ≠ 0 →
      (∃ j'', B.col j'' = t - B.row i) ∧ (∃ i'', B.row i'' = t - B.col j) := by
    intro j i hji
    have h1 := hc j i
    have h2 : (adjArray V (V.col (coreColEmb V j)) (V.row (coreRowEmb V i))).coeff
        (coreCount V - 1) ≠ 0 := by rw [h1]; exact mul_ne_zero hσ hji
    have h3 := hcoef _ _ ▸ h2
    obtain ⟨⟨j1, hj1, hj1b⟩, ⟨i1, hi1, hi1b⟩⟩ := hP _ _ h3
    obtain ⟨j2, rfl⟩ := exists_coreColEmb V hj1
    obtain ⟨i2, rfl⟩ := exists_coreRowEmb V hi1
    exact ⟨⟨j2, hj1b⟩, ⟨i2, hi1b⟩⟩
  have hrowEq : B.row = fun i => t - B.col i.rev := by
    refine strictAnti_eq_of_image_eq B.row_strictAnti ?_ ?_
    · intro i j hij
      have := B.col_strictAnti (Fin.rev_lt_rev.mpr hij)
      show t - B.col j.rev < t - B.col i.rev
      omega
    · ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i0, rfl⟩
        obtain ⟨j', hj'⟩ := hII i0
        obtain ⟨⟨j'', hj''⟩, -⟩ := star _ _ hj'
        exact ⟨j''.rev, by rw [Fin.rev_rev, hj'']; ring⟩
      · rintro ⟨i, rfl⟩
        obtain ⟨i', hi'⟩ := hI i.rev
        obtain ⟨-, ⟨i'', hi''⟩⟩ := star _ _ hi'
        exact ⟨i'', hi''⟩
  have hcolEq : B.col = fun i => t - B.row i.rev := by
    refine strictAnti_eq_of_image_eq B.col_strictAnti ?_ ?_
    · intro i j hij
      have := B.row_strictAnti (Fin.rev_lt_rev.mpr hij)
      show t - B.row j.rev < t - B.row i.rev
      omega
    · ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j0, rfl⟩
        obtain ⟨i', hi'⟩ := hI j0
        obtain ⟨-, ⟨i'', hi''⟩⟩ := star _ _ hi'
        exact ⟨i''.rev, by rw [Fin.rev_rev, hi'']; ring⟩
      · rintro ⟨i, rfl⟩
        obtain ⟨j', hj'⟩ := hII i.rev
        obtain ⟨⟨j'', hj''⟩, -⟩ := star _ _ hj'
        exact ⟨j'', hj''⟩
  exact hns ⟨t, fun i => congrFun hrowEq i, fun i => congrFun hcolEq i⟩

end CoreExact

section Contraction

theorem X_pow_succ_dvd_X_mul (p : CR[X]) (g : ℕ) :
    (Polynomial.X : CR[X]) ^ (g + 1) ∣ Polynomial.X * p ↔ (Polynomial.X : CR[X]) ^ g ∣ p := by
  rw [pow_succ', mul_dvd_mul_iff_left Polynomial.X_ne_zero]

/-- **The contraction bound is attained at a unit value.**  Under the hypothesis of
`adjDifference_unit_exact`, the contraction of the difference array against the single
coefficient one at `(b, b)` has order exactly `k + 1`, which is `λ` for a self-rotating
core. -/
theorem contraction_unit_exact {n : ℕ} (V : BetaDiagram (n + 1)) (s b : ℤ)
    (h : ¬ (b ∈ unitVals V ↔ V.largestLabel - s - b ∈ unitVals V)) :
    (Polynomial.X : CR[X]) ^ (coreCount V + 1) ∣
        ∑ x ∈ ({(b, b)} : Finset (ℤ × ℤ)), Polynomial.X * (1 : CR[X]) * adjDifference V s x.1 x.2 ∧
      ¬ (Polynomial.X : CR[X]) ^ (coreCount V + 2) ∣
        ∑ x ∈ ({(b, b)} : Finset (ℤ × ℤ)), Polynomial.X * (1 : CR[X]) * adjDifference V s x.1 x.2 := by
  obtain ⟨h1, h2⟩ := adjDifference_unit_exact V s b h
  simp only [Finset.sum_singleton, mul_one]
  exact ⟨(X_pow_succ_dvd_X_mul _ _).mpr h1, fun h3 => h2 ((X_pow_succ_dvd_X_mul _ _).mp h3)⟩

/-- **The contraction bound is attained for a core that is not its own half-turn**: for every
translation some single-entry contraction has order exactly `k = λ`. -/
theorem contraction_core_exact {n : ℕ} (V : BetaDiagram (n + 1))
    (hns : ¬ (coreDiagram V).Symmetric) (s : ℤ) :
    ∃ c r : ℤ, (Polynomial.X : CR[X]) ^ coreCount V ∣
        ∑ x ∈ ({(c, r)} : Finset (ℤ × ℤ)), Polynomial.X * (1 : CR[X]) * adjDifference V s x.1 x.2 ∧
      ¬ (Polynomial.X : CR[X]) ^ (coreCount V + 1) ∣
        ∑ x ∈ ({(c, r)} : Finset (ℤ × ℤ)), Polynomial.X * (1 : CR[X]) * adjDifference V s x.1 x.2 := by
  obtain ⟨c, r, h1, h2⟩ := adjDifference_core_exact V hns s
  have hk : coreCount V = (coreCount V - 1) + 1 := by
    have := coreCount_pos_of_pos V (Nat.succ_pos n); omega
  refine ⟨c, r, ?_⟩
  simp only [Finset.sum_singleton, mul_one]
  rw [hk]
  refine ⟨(X_pow_succ_dvd_X_mul _ _).mpr h1, fun h3 => h2 ?_⟩
  have := (X_pow_succ_dvd_X_mul _ _).mp h3
  rwa [← hk] at this

end Contraction

section SelfCore

/-- The half-turn constant of a symmetric core of a normalized diagram is its largest label. -/
theorem core_const_eq_largestLabel {n : ℕ} (V : BetaDiagram (n + 1)) (hV : IsNorm V) (M : ℤ)
    (hrow : ∀ i, (coreDiagram V).row i = M - (coreDiagram V).col i.rev) :
    M = V.largestLabel := by
  have hk : 0 < coreCount V := coreCount_pos_of_pos V (Nat.succ_pos n)
  set k0 : Fin (coreCount V) := ⟨0, hk⟩
  set kl : Fin (coreCount V) := ⟨coreCount V - 1, by omega⟩
  have e0 : coreRowEmb V k0 = 0 := Fin.ext ((coreRowEmb_zero_iff V k0).mpr rfl)
  have el : coreColEmb V kl = Fin.last n :=
    Fin.ext (by have := (coreColEmb_last_iff V kl).mpr (by simp [kl]; omega); simp; omega)
  have hrev : k0.rev = kl := Fin.ext (by simp [k0, kl, Fin.val_rev])
  have h := hrow k0
  rw [coreDiagram_row, coreDiagram_col, hrev, e0, el] at h
  have hl : V.col (Fin.last n) = 0 := hV
  rw [hl] at h
  rw [largestLabel_of_norm V hV]
  omega

/-- A normalized diagram with a self-rotating core that is not its own half-turn has a unit value
`b` such that exactly one of `b` and `L - b` is a unit value. -/
theorem exists_unit_asymmetry {n : ℕ} (V : BetaDiagram (n + 1)) (hV : IsNorm V)
    (hsym : (coreDiagram V).Symmetric) (hne : V.rotation ≠ V) :
    ∃ b : ℤ, ¬ (b ∈ unitVals V ↔ V.largestLabel - b ∈ unitVals V) := by
  by_contra hcon
  push Not at hcon
  have hU : unitVals V.rotation = unitVals V := by
    ext x
    rw [mem_unitVals_rotation]
    exact (hcon x).symm
  obtain ⟨b, hb⟩ : ∃ b, coreCount V = b + 1 :=
    ⟨coreCount V - 1, by have := coreCount_pos_of_pos V (Nat.succ_pos n); omega⟩
  set B := castDiagram (coreDiagram V) hb with hBdef
  have hBV : SameLists (coreDiagram V) B := sameLists_castDiagram _ hb
  have hBV' : SameLists (coreDiagram V.rotation) B.rotation :=
    sameLists_coreDiagram_rotation V B hBV
  have hBn : IsNorm B := by
    obtain ⟨hcc, hr, hc⟩ := hBV
    have e : Fin.cast hcc (Fin.cast hcc.symm (Fin.last b)) = Fin.last b := Fin.ext rfl
    have h1 := hc (Fin.cast hcc.symm (Fin.last b))
    rw [e, coreDiagram_col] at h1
    have h2 : coreColEmb V (Fin.cast hcc.symm (Fin.last b)) = Fin.last n := by
      have := (coreColEmb_last_iff V (Fin.cast hcc.symm (Fin.last b))).mpr (by simp [hcc])
      exact Fin.ext (by simp; omega)
    rw [h2] at h1
    exact h1.symm.trans hV
  have hBsym : B.rotation = B := (symmetric_iff_rotation hBV hBn).mp hsym
  have hBV'' : SameLists (coreDiagram V.rotation) B := by
    have := hBV'; rwa [hBsym] at this
  exact hne (eq_of_core_unit (hBV''.trans hBV.symm) hU)

/-- **Sharpness for a self-rotating core.**  Let `V` be normalized with a self-rotating core about
`M` and `V` not its own half-turn.  Then `M` is the largest label, and some entry of the
aligned adjugate difference has order exactly `k`, and the contraction of the difference at that
entry with coefficient one has order exactly `k + 1`. -/
theorem adjDifference_self_exact {n : ℕ} (V : BetaDiagram (n + 1)) (hV : IsNorm V)
    (hne : V.rotation ≠ V) (M : ℤ) (hrow : ∀ i, (coreDiagram V).row i = M - (coreDiagram V).col i.rev)
    (hcol : ∀ i, (coreDiagram V).col i = M - (coreDiagram V).row i.rev) :
    M = V.largestLabel ∧ ∃ b : ℤ,
      ((Polynomial.X : CR[X]) ^ coreCount V ∣ adjDifference V (V.largestLabel - M) b b ∧
        ¬ (Polynomial.X : CR[X]) ^ (coreCount V + 1) ∣ adjDifference V (V.largestLabel - M) b b) ∧
      ((Polynomial.X : CR[X]) ^ (coreCount V + 1) ∣
        ∑ x ∈ ({(b, b)} : Finset (ℤ × ℤ)),
          Polynomial.X * (1 : CR[X]) * adjDifference V (V.largestLabel - M) x.1 x.2 ∧
        ¬ (Polynomial.X : CR[X]) ^ (coreCount V + 2) ∣
          ∑ x ∈ ({(b, b)} : Finset (ℤ × ℤ)),
            Polynomial.X * (1 : CR[X]) * adjDifference V (V.largestLabel - M) x.1 x.2) := by
  have hM := core_const_eq_largestLabel V hV M hrow
  obtain ⟨b, hb⟩ := exists_unit_asymmetry V hV ⟨M, hrow, hcol⟩ hne
  have e : V.largestLabel - (V.largestLabel - M) - b = V.largestLabel - b := by rw [hM]; ring
  have hb' : ¬ (b ∈ unitVals V ↔ V.largestLabel - (V.largestLabel - M) - b ∈ unitVals V) := by
    rw [e]; exact hb
  exact ⟨hM, b, adjDifference_unit_exact V _ b hb', contraction_unit_exact V _ b hb'⟩

end SelfCore

end SkewCoframeRigidity.UnitRestoration
