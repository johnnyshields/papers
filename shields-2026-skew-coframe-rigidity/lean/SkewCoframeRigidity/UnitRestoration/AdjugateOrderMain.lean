/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.AdjugateOrder

/-!
# The whole adjugate array of a diagram and its half-turn

Formalizes the closing assertions of `sc:splice-nonzero` in
`shields-2026-skew-coframe-rigidity.tex`: the whole absolute adjugate difference between `V` and
its half-turn has no grade below `μ = λ - 1`, and every contraction of that array with one
positive raw letter has order at least `λ`.

**Reading.**  The positive letters carry a factor `ε`; the unit entries carry none.  The array of
`D` is `adjArray D`, the adjugate of the scaled Jacobi–Trudi matrix with its entry at column label
`c` and row label `r` in position `(c, r)`, and zero where `D` has no such column or row.  The
absolute difference is `adjDifference V s`, the array of `V` minus the array of its half-turn
translated by `s` in both coordinates.  The grade of an entry is its `ε`-adic order.

* Every entry of `adjArray D` has order at least `k - 1`, with `k` the number of core rows; the
  entries at a core column and a core row are the only ones of order `k - 1`, and there the
  leading coefficient is `σ adj(JT(core))` with one sorting sign `σ` for the array
  (`adjArray_order`).  Hence the difference has order at least `k - 1` (`μ = k - 1` for a core
  that is not its own half-turn).
* If the core is its own half-turn about `M`, the two leading arrays agree after translating the
  half-turn by `L - M` (for a normalized `V` the largest label `L` is a core row and `0` a core
  column, so `M = L` and no translation is needed), and the difference has order at least `k`,
  that is `μ = λ - 1` with `λ = k + 1` (`adjugate_difference_order`).
* A single positive raw letter multiplies a coefficient by `ε`, so every contraction of the
  difference array against finitely many coefficients has order at least `λ`
  (`contraction_order_ge`).

The statements are lower bounds on the order, as in the paper's lemma; they assert no
nonvanishing.  Unconditional.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Matrix Polynomial

local notation "CR" => SkewCofactorIndependence.CompleteRing

section Array

variable {R : Type*} [CommRing R]

open scoped Classical in
/-- The adjugate array of the scaled Jacobi–Trudi matrix of `D`, indexed by the actual labels:
the entry at column label `c` and row label `r` is the adjugate entry of the column and row
carrying those labels, and zero when `D` has no such column or no such row. -/
noncomputable def adjArrayOf (h : ℕ → R) {m : ℕ} (D : BetaDiagram m) (c r : ℤ) : R[X] :=
  ∑ j, ∑ i, if D.col j = c ∧ D.row i = r then
    adjugate (scaledMatrix h D.row D.col) j i else 0

theorem adjArrayOf_apply (h : ℕ → R) {m : ℕ} (D : BetaDiagram m) (j i : Fin m) :
    adjArrayOf h D (D.col j) (D.row i) = adjugate (scaledMatrix h D.row D.col) j i := by
  classical
  unfold adjArrayOf
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [if_neg]
      exact fun h' => hb (D.row_strictAnti.injective h'.2)
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg]
    exact fun h' => hb (D.col_strictAnti.injective h'.1)
  · simp

theorem adjArrayOf_eq_zero_or (h : ℕ → R) {m : ℕ} (D : BetaDiagram m) (c r : ℤ) :
    adjArrayOf h D c r = 0 ∨ ∃ j i, D.col j = c ∧ D.row i = r := by
  classical
  by_cases hx : ∃ j i, D.col j = c ∧ D.row i = r
  · exact Or.inr hx
  · left
    unfold adjArrayOf
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    exact fun h' => hx ⟨j, i, h'⟩

theorem scaledMatrix_rotation (h : ℕ → R) {n : ℕ} (D : BetaDiagram (n + 1)) :
    scaledMatrix h D.rotation.row D.rotation.col =
      ((scaledMatrix h D.row D.col)ᵀ).submatrix Fin.rev Fin.rev := by
  ext i j
  simp only [scaledMatrix, Matrix.of_apply, BetaDiagram.rotation_row, BetaDiagram.rotation_col,
    Matrix.submatrix_apply, Matrix.transpose_apply]
  congr 1
  ring

theorem adjugate_scaledMatrix_rotation (h : ℕ → R) {n : ℕ} (D : BetaDiagram (n + 1))
    (j i : Fin (n + 1)) :
    adjugate (scaledMatrix h D.rotation.row D.rotation.col) j i =
      adjugate (scaledMatrix h D.row D.col) i.rev j.rev := by
  rw [scaledMatrix_rotation]
  have := congrFun (congrFun (adjugate_submatrix_equiv_self (Fin.revPerm (n := n + 1))
    ((scaledMatrix h D.row D.col)ᵀ)) j) i
  simp only [Matrix.submatrix_apply, Fin.revPerm_apply] at this
  have e : ((scaledMatrix h D.row D.col)ᵀ).submatrix Fin.rev Fin.rev =
      ((scaledMatrix h D.row D.col)ᵀ).submatrix (Fin.revPerm (n := n + 1))
        (Fin.revPerm (n := n + 1)) := rfl
  rw [e, this, ← adjugate_transpose]
  rfl

open scoped Classical in
/-- The adjugate array of the half-turn is the original array reflected through the largest label
and transposed. -/
theorem adjArrayOf_rotation (h : ℕ → R) {n : ℕ} (D : BetaDiagram (n + 1)) (c r : ℤ) :
    adjArrayOf h D.rotation c r =
      adjArrayOf h D (D.largestLabel - r) (D.largestLabel - c) := by
  unfold adjArrayOf
  simp only [adjugate_scaledMatrix_rotation, BetaDiagram.rotation_row, BetaDiagram.rotation_col]
  rw [Finset.sum_comm]
  refine Fintype.sum_equiv (Fin.revPerm (n := n + 1)) _ _ (fun i => ?_)
  refine Fintype.sum_equiv (Fin.revPerm (n := n + 1)) _ _ (fun j => ?_)
  simp only [Fin.revPerm_apply]
  congr 1
  apply propext
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

end Array

section Core

/-- The adjugate array of the scaled Jacobi–Trudi matrix over the complete ring. -/
noncomputable def adjArray {m : ℕ} (D : BetaDiagram m) (c r : ℤ) : CR[X] :=
  adjArrayOf letterSeq D c r

/-- `c` is the label of a core column of `D`. -/
def IsCoreColLabel {m : ℕ} (D : BetaDiagram m) (c : ℤ) : Prop :=
  ∃ j, j ∉ unitCols D.row D.col ∧ D.col j = c

/-- `r` is the label of a core row of `D`. -/
def IsCoreRowLabel {m : ℕ} (D : BetaDiagram m) (r : ℤ) : Prop :=
  ∃ i, i ∉ unitRows D.row D.col ∧ D.row i = r

theorem fullMatrixOf_core {R : Type*} [CommRing R] (h : ℕ → R) {m : ℕ} (D : BetaDiagram m) :
    fullMatrixOf h (coreDiagram D) = (coreMatrix h D.row D.col (corePairing D)).submatrix
      (coreRowEquiv D) (coreRowEquiv D) := by
  ext a b
  have hb := congrArg Subtype.val (corePairing_coreRowEquiv D b)
  simp only [coreMatrix, fullMatrixOf, Matrix.of_apply, Matrix.submatrix_apply, coreDiagram_row,
    coreDiagram_col]
  have : ((coreRowEquiv D) b : Fin m) = coreRowEmb D b := rfl
  rw [this] at *
  simp only [coreRowEquiv, Equiv.coe_fn_mk] at hb ⊢
  rw [hb]
  rfl

theorem map_adjArray {m : ℕ} (D : BetaDiagram m) (c r : ℤ) :
    (adjArray D c r).map (algebraMap CR FF) = adjArrayOf letterSeqF D c r := by
  classical
  unfold adjArray adjArrayOf
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hji : D.col j = c ∧ D.row i = r
  · rw [if_pos hji, if_pos hji]
    have := congrFun (congrFun (RingHom.map_adjugate (Polynomial.mapRingHom (algebraMap CR FF))
      (scaledMatrix letterSeq D.row D.col)) j) i
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at this
    have hS : (scaledMatrix letterSeq D.row D.col).map (Polynomial.mapRingHom (algebraMap CR FF)) =
        scaledMatrix letterSeqF D.row D.col := by
      ext a b
      simp [scaledMatrix, scaledLetter_map]
    rw [hS] at this
    simpa using this
  · rw [if_neg hji, if_neg hji, Polynomial.map_zero]

open scoped Classical in
/-- **Orders of the adjugate array over the field of fractions.**  Let `k` be the number of core
rows.  Entries not at a core column and a core row are divisible by `ε^k`, and the entry at the
`j`-th core column and `i`-th core row is `ε^{k-1}(σ adj(JT(core))_{ji} + ε q)`. -/
theorem adjArray_order_FF {m : ℕ} (D : BetaDiagram m) :
    ∃ σ : ℤˣ,
      (∀ c r, ¬ (IsCoreColLabel D c ∧ IsCoreRowLabel D r) →
        (Polynomial.X : FF[X]) ^ coreCount D ∣ adjArrayOf letterSeqF D c r) ∧
      (∀ j i : Fin (coreCount D), ∃ q : FF[X],
        adjArrayOf letterSeqF D (D.col (coreColEmb D j)) (D.row (coreRowEmb D i)) =
          Polynomial.X ^ (coreCount D - 1) * (Polynomial.C (((σ : ℤ) : FF) *
            adjugate (fullMatrixOf letterSeqF (coreDiagram D)) j i) + Polynomial.X * q)) := by
  have hK : (coreMatrix letterSeqF D.row D.col (corePairing D)).det ≠ 0 := by
    rw [det_coreMatrix_eq]
    exact (map_ne_zero_iff _ algebraMap_injective_FF).mpr (BetaDiagram.schur_ne_zero _)
  obtain ⟨σ, hσ⟩ := adjugate_scaledMatrix_expansion letterSeqF D.row D.col
    D.row_strictAnti.injective D.col_strictAnti.injective (unitPairing D) (unitPairing_spec D)
    (corePairing D) hK
  have hcard : (Finset.univ.filter fun l => l ∉ unitRows D.row D.col).card = coreCount D :=
    card_coreRows_eq_count D
  refine ⟨σ, fun c r hcr => ?_, fun j i => ?_⟩
  · rcases adjArrayOf_eq_zero_or letterSeqF D c r with h0 | ⟨j, i, rfl, rfl⟩
    · rw [h0]; exact dvd_zero _
    · rw [adjArrayOf_apply]
      obtain ⟨q, hq⟩ := (hσ i j).1 (by
        by_contra hn
        push Not at hn
        exact hcr ⟨⟨j, hn.2, rfl⟩, ⟨i, hn.1, rfl⟩⟩)
      rw [hq, hcard]
      exact dvd_mul_right _ _
  · rw [adjArrayOf_apply]
    obtain ⟨q, hq⟩ := (hσ (coreRowEmb D i) (coreColEmb D j)).2.1 (coreRowEmb_mem D i)
      (coreColEmb_mem D j)
    refine ⟨q, ?_⟩
    rw [hq, hcard]
    have h1 : (corePairing D).symm ⟨coreColEmb D j, coreColEmb_mem D j⟩ = coreRowEquiv D j := by
      rw [Equiv.symm_apply_eq, corePairing_coreRowEquiv]
      rfl
    have h2 : (⟨coreRowEmb D i, coreRowEmb_mem D i⟩ :
        {i // i ∉ unitRows D.row D.col}) = coreRowEquiv D i := rfl
    rw [h1, h2, fullMatrixOf_core, adjugate_submatrix_equiv_self]
    rfl

theorem X_pow_dvd_of_map {p : CR[X]} {g : ℕ} (hp : (Polynomial.X : FF[X]) ^ g ∣ p.map (algebraMap CR FF)) :
    (Polynomial.X : CR[X]) ^ g ∣ p := by
  rw [Polynomial.X_pow_dvd_iff] at hp ⊢
  intro d hd
  apply algebraMap_injective_FF
  have := hp d hd
  rw [Polynomial.coeff_map] at this
  rw [map_zero]
  exact this

theorem map_fullMatrixOf {m : ℕ} (D : BetaDiagram m) :
    (fullMatrixOf letterSeqF D) = (fullMatrixOf letterSeq D).map (algebraMap CR FF) := by
  ext a b
  simp [fullMatrixOf, letterOf_letterSeqF]

/-- **Orders of the adjugate array.**  Let `k` be the number of core rows of `D`.  Every entry
of the scaled adjugate array whose column label and row label are not both core labels is
divisible by `ε^k`, and the entry at the `j`-th core column and `i`-th core row agrees with
`ε^{k-1} σ adj(JT(core))_{ji}` modulo `ε^k`, with one sorting sign `σ` for the whole array. -/
theorem adjArray_order {m : ℕ} (D : BetaDiagram m) :
    ∃ σ : ℤˣ,
      (∀ c r, ¬ (IsCoreColLabel D c ∧ IsCoreRowLabel D r) →
        (Polynomial.X : CR[X]) ^ coreCount D ∣ adjArray D c r) ∧
      (∀ j i : Fin (coreCount D),
        (Polynomial.X : CR[X]) ^ coreCount D ∣
          adjArray D (D.col (coreColEmb D j)) (D.row (coreRowEmb D i)) -
            Polynomial.X ^ (coreCount D - 1) * Polynomial.C (((σ : ℤ) : CR) *
              adjugate (fullMatrixOf letterSeq (coreDiagram D)) j i)) := by
  obtain ⟨σ, h1, h2⟩ := adjArray_order_FF D
  refine ⟨σ, fun c r hcr => X_pow_dvd_of_map (by rw [map_adjArray]; exact h1 c r hcr),
    fun j i => X_pow_dvd_of_map ?_⟩
  obtain ⟨q, hq⟩ := h2 j i
  have hk : coreCount D = (coreCount D - 1) + 1 := by have := j.pos; omega
  refine ⟨q, ?_⟩
  have hadj : algebraMap CR FF (adjugate (fullMatrixOf letterSeq (coreDiagram D)) j i) =
      adjugate (fullMatrixOf letterSeqF (coreDiagram D)) j i := by
    rw [map_fullMatrixOf]
    have := congrFun (congrFun (RingHom.map_adjugate (algebraMap CR FF)
      (fullMatrixOf letterSeq (coreDiagram D))) j) i
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at this
    simpa using this
  rw [Polynomial.map_sub, map_adjArray, hq, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  simp only [map_mul, map_intCast, hadj, Polynomial.C_mul]
  have e : (Polynomial.X : FF[X]) ^ coreCount D =
      Polynomial.X ^ (coreCount D - 1) * Polynomial.X := by
    rw [← pow_succ, ← hk]
  rw [e]
  ring

theorem adjArray_dvd_pred {m : ℕ} (D : BetaDiagram m) (c r : ℤ) :
    (Polynomial.X : CR[X]) ^ (coreCount D - 1) ∣ adjArray D c r := by
  obtain ⟨σ, h1, h2⟩ := adjArray_order D
  by_cases hcr : IsCoreColLabel D c ∧ IsCoreRowLabel D r
  · obtain ⟨⟨j, hj, rfl⟩, ⟨i, hi, rfl⟩⟩ := hcr
    obtain ⟨j', rfl⟩ := exists_coreColEmb D hj
    obtain ⟨i', rfl⟩ := exists_coreRowEmb D hi
    have := dvd_add ((pow_dvd_pow _ (Nat.sub_le (coreCount D) 1)).trans (h2 j' i'))
      (dvd_mul_right ((Polynomial.X : CR[X]) ^ (coreCount D - 1)) (Polynomial.C (((σ : ℤ) : CR) *
        adjugate (fullMatrixOf letterSeq (coreDiagram D)) j' i')))
    simpa using this
  · exact (pow_dvd_pow _ (Nat.sub_le (coreCount D) 1)).trans (h1 c r hcr)

/-- The entries of the Jacobi–Trudi adjugate of a half-turn-symmetric diagram. -/
theorem adjugate_fullMatrixOf_symm {R : Type*} [CommRing R] (h : ℕ → R) {b : ℕ}
    (B : BetaDiagram b) (M : ℤ) (hrow : ∀ i, B.row i = M - B.col i.rev)
    (hcol : ∀ i, B.col i = M - B.row i.rev) (j i : Fin b) :
    adjugate (fullMatrixOf h B) j i = adjugate (fullMatrixOf h B) i.rev j.rev := by
  have hM : fullMatrixOf h B = ((fullMatrixOf h B)ᵀ).submatrix (Fin.revPerm (n := b))
      (Fin.revPerm (n := b)) := by
    ext x y
    simp only [fullMatrixOf, Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
      Fin.revPerm_apply]
    congr 1
    rw [hrow y.rev, hcol x.rev]
    simp only [Fin.rev_rev]
    ring
  conv_lhs => rw [hM]
  rw [adjugate_submatrix_equiv_self]
  simp only [Matrix.submatrix_apply, Fin.revPerm_apply]
  rw [← adjugate_transpose]
  rfl

/-- The difference between the adjugate array of `V` and that of its half-turn, with the
half-turn translated by `s` in both coordinates. -/
noncomputable def adjDifference {n : ℕ} (V : BetaDiagram (n + 1)) (s c r : ℤ) : CR[X] :=
  adjArray V c r - adjArray V.rotation (c + s) (r + s)

/-- **The adjugate difference between a diagram and its half-turn** (`sc:splice-nonzero`).  Let
`k` be the number of core rows of `V`.  For every translation `s` of the half-turn, the entries of
the two scaled adjugate arrays differ at order at least `k - 1`.  If the core is its own
half-turn about `M`, then translating the half-turn by `L - M`, where `L` is the largest label of
`V`, aligns the two cores, and the difference of the arrays is divisible by `ε^k`: no grade
below `λ - 1 = k` appears. -/
theorem adjugate_difference_order {n : ℕ} (V : BetaDiagram (n + 1)) :
    (∀ s c r : ℤ, (Polynomial.X : CR[X]) ^ (coreCount V - 1) ∣ adjDifference V s c r) ∧
    (∀ M : ℤ, (∀ i, (coreDiagram V).row i = M - (coreDiagram V).col i.rev) →
      (∀ i, (coreDiagram V).col i = M - (coreDiagram V).row i.rev) →
      ∀ c r : ℤ, (Polynomial.X : CR[X]) ^ coreCount V ∣
        adjDifference V (V.largestLabel - M) c r) := by
  refine ⟨fun s c r => ?_, fun M hrow hcol c r => ?_⟩
  · unfold adjDifference
    refine dvd_sub (adjArray_dvd_pred V c r) ?_
    have := adjArray_dvd_pred V.rotation (c + s) (r + s)
    rwa [coreCount_rotation] at this
  have hrot : adjArray V.rotation (c + (V.largestLabel - M)) (r + (V.largestLabel - M)) =
      adjArray V (M - r) (M - c) := by
    unfold adjArray
    rw [adjArrayOf_rotation]
    congr 1 <;> ring
  unfold adjDifference
  rw [hrot]
  obtain ⟨σ, h1, h2⟩ := adjArray_order V
  have hrowL : ∀ r, IsCoreRowLabel V r → IsCoreColLabel V (M - r) := by
    rintro r ⟨i, hi, rfl⟩
    obtain ⟨i', rfl⟩ := exists_coreRowEmb V hi
    refine ⟨coreColEmb V i'.rev, coreColEmb_mem V _, ?_⟩
    have := hcol i'.rev
    rw [Fin.rev_rev] at this
    exact this
  have hcolL : ∀ c, IsCoreColLabel V c → IsCoreRowLabel V (M - c) := by
    rintro c ⟨j, hj, rfl⟩
    obtain ⟨j', rfl⟩ := exists_coreColEmb V hj
    refine ⟨coreRowEmb V j'.rev, coreRowEmb_mem V _, ?_⟩
    have := hrow j'.rev
    rw [Fin.rev_rev] at this
    exact this
  by_cases hcr : IsCoreColLabel V c ∧ IsCoreRowLabel V r
  · obtain ⟨⟨j, hj, rfl⟩, ⟨i, hi, rfl⟩⟩ := hcr
    obtain ⟨j', rfl⟩ := exists_coreColEmb V hj
    obtain ⟨i', rfl⟩ := exists_coreRowEmb V hi
    have e1 : M - V.row (coreRowEmb V i') = V.col (coreColEmb V i'.rev) := by
      have := hcol i'.rev
      rw [Fin.rev_rev] at this
      exact this.symm
    have e2 : M - V.col (coreColEmb V j') = V.row (coreRowEmb V j'.rev) := by
      have := hrow j'.rev
      rw [Fin.rev_rev] at this
      exact this.symm
    rw [e1, e2]
    have hsy := adjugate_fullMatrixOf_symm letterSeq (coreDiagram V) M hrow hcol j' i'
    have d1 := h2 j' i'
    have d2 := h2 i'.rev j'.rev
    rw [← hsy] at d2
    have := dvd_sub d1 d2
    convert this using 1
    ring
  · refine dvd_sub (h1 c r hcr) (h1 _ _ ?_)
    rintro ⟨hc, hr⟩
    apply hcr
    refine ⟨?_, ?_⟩
    · simpa using hrowL _ hr
    · simpa using hcolL _ hc

/-- **Contraction of the whole adjugate array** (`sc:splice-nonzero`).  Contract the array
difference against any finite family of coefficients, each carrying one positive raw letter
(a factor `ε`).  The result has order at least `λ`: at least `k` when the core is not its own
half-turn, and at least `k + 1` when it is, after the alignment of `adjugate_difference_order`. -/
theorem contraction_order_ge {n : ℕ} (V : BetaDiagram (n + 1)) (S : Finset (ℤ × ℤ))
    (w : ℤ × ℤ → CR[X]) :
    (0 < coreCount V → ∀ s : ℤ, (Polynomial.X : CR[X]) ^ coreCount V ∣
      ∑ x ∈ S, Polynomial.X * w x * adjDifference V s x.1 x.2) ∧
    (∀ M : ℤ, (∀ i, (coreDiagram V).row i = M - (coreDiagram V).col i.rev) →
      (∀ i, (coreDiagram V).col i = M - (coreDiagram V).row i.rev) →
      (Polynomial.X : CR[X]) ^ (coreCount V + 1) ∣
        ∑ x ∈ S, Polynomial.X * w x * adjDifference V (V.largestLabel - M) x.1 x.2) := by
  obtain ⟨h1, h2⟩ := adjugate_difference_order V
  refine ⟨fun hk s => Finset.dvd_sum fun x _ => ?_, fun M hr hc => Finset.dvd_sum fun x _ => ?_⟩
  · have hk' : coreCount V = (coreCount V - 1) + 1 := by omega
    have := mul_dvd_mul (dvd_refl (Polynomial.X : CR[X])) (h1 s x.1 x.2)
    rw [← pow_succ', ← hk'] at this
    exact this.trans ⟨w x, by ring⟩
  · have := mul_dvd_mul (dvd_refl (Polynomial.X : CR[X])) (h2 M hr hc x.1 x.2)
    rw [← pow_succ'] at this
    exact this.trans ⟨w x, by ring⟩

end Core

end SkewCoframeRigidity.UnitRestoration
