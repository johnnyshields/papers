/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Model
import SkewCoframeRigidity.Unshifted.YExpansion

/-!
# The endpoint inverse columns of the unshifted exclusion

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`sec:unshifted`, `ph:unshifted-exclusion`).  For a diagram `D` of span `M` with proper inverse
`Π = T⁻¹`, the vector `a = -∑_c Π_{c,m} z^c`, `m = M - 1`, is the column of `Π` at the port
`m` (the zero vector when `m` is not a proper row position).  It depends only on the letters
below `m`, and the coframe is affine in the top letter `y = H_m`: `G = G₀ + y a`.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The indicator vector of the top port: the proper row at position `m = M - 1`, if any. -/
def portIndicator (D : BetaDiagram (n + 1)) : Fin n → K :=
  fun i => if rowPos D i + 1 = span D then 1 else 0

/-- The coefficients of `a = -∑_c Π_{c,m} z^c`, indexed by the columns; zero when no proper row
sits at position `m`. -/
noncomputable def endpointAVec (h : ℕ → K) (D : BetaDiagram (n + 1)) : Fin n → K :=
  -((properMatrixOf h D)⁻¹ *ᵥ portIndicator D)

/-- The endpoint column `a = -∑_c Π_{c,m} z^c`. -/
noncomputable def endpointA (h : ℕ → K) (D : BetaDiagram (n + 1)) : K[X] :=
  ∑ j, C (endpointAVec h D j) * X ^ colPos D j

/-- The labels of the proper matrix stay below `m = M - 1`. -/
theorem properLabel_lt (D : BetaDiagram (n + 1)) (i j : Fin n) :
    (D.row i.succ - D.col j.castSucc) + 1 < (span D : ℤ) := by
  have h1 := rowPos_sub_colPos D i j
  have h2 := rowPos_lt_span D i
  have h3 := colPos_pos D j
  omega

/-- The proper matrix depends only on the letters below `m`. -/
theorem properMatrixOf_congr {h h' : ℕ → K} (D : BetaDiagram (n + 1))
    (hh : ∀ k, k + 1 < span D → h k = h' k) : properMatrixOf h D = properMatrixOf h' D := by
  ext i j
  simp only [properMatrixOf, Matrix.of_apply]
  have := properLabel_lt D i j
  unfold letterOf
  split_ifs with hneg
  · rfl
  · apply hh
    omega

/-- The top vector splits as its value with the top letter removed plus `H_m` at the port. -/
theorem topVecOf_update (h : ℕ → K) (D : BetaDiagram (n + 1)) :
    topVecOf h D = topVecOf (Function.update h (span D - 1) 0) D +
      h (span D - 1) • portIndicator D := by
  funext i
  have hpos := rowPos_pos D i
  have hlt := rowPos_lt_span D i
  have e : D.row i.succ - D.col (Fin.last n) = (rowPos D i : ℤ) := (rowPos_cast D i).symm
  simp only [topVecOf, Pi.add_apply, Pi.smul_apply, portIndicator, e, letterOf_natCast,
    smul_eq_mul]
  by_cases hi : rowPos D i + 1 = span D
  · have : rowPos D i = span D - 1 := by omega
    simp [this, show span D - 1 + 1 = span D by omega]
  · have : rowPos D i ≠ span D - 1 := by omega
    simp [hi, Function.update_of_ne this]

/-- The endpoint column does not depend on the top letter. -/
theorem endpointAVec_update (h : ℕ → K) (D : BetaDiagram (n + 1)) (y : K) :
    endpointAVec (Function.update h (span D - 1) y) D = endpointAVec h D := by
  unfold endpointAVec
  rw [properMatrixOf_congr D (h' := h)]
  intro k hk
  rw [Function.update_of_ne (by omega)]

/-- The endpoint column depends only on the letters below `m`. -/
theorem endpointAVec_congr {h h' : ℕ → K} (D : BetaDiagram (n + 1))
    (hh : ∀ k, k + 1 < span D → h k = h' k) : endpointAVec h D = endpointAVec h' D := by
  unfold endpointAVec
  rw [properMatrixOf_congr D hh]

theorem endpointA_congr {h h' : ℕ → K} (D : BetaDiagram (n + 1))
    (hh : ∀ k, k + 1 < span D → h k = h' k) : endpointA h D = endpointA h' D := by
  unfold endpointA
  rw [endpointAVec_congr D hh]

/-- The coefficients of the coframe are affine in the top letter: `G = G₀ + y a`. -/
theorem coframeVecOf_eq (h : ℕ → K) (D : BetaDiagram (n + 1)) :
    coframeVecOf h D = coframeVecOf (Function.update h (span D - 1) 0) D +
      h (span D - 1) • endpointAVec h D := by
  have hT : properMatrixOf (Function.update h (span D - 1) 0) D = properMatrixOf h D :=
    properMatrixOf_congr D fun k hk => by rw [Function.update_of_ne (by omega)]
  unfold coframeVecOf endpointAVec
  rw [hT, topVecOf_update h D, Matrix.mulVec_add, Matrix.mulVec_smul]
  simp only [smul_neg, neg_add_rev]
  abel

/-- `G = G₀ + y a`: the coframe is affine in the top letter `y = H_m`, with the slope the
endpoint column `a`, and `G₀` the coframe with the top letter set to zero. -/
theorem coframeOf_eq (h : ℕ → K) (D : BetaDiagram (n + 1)) :
    coframeOf h D = coframeOf (Function.update h (span D - 1) 0) D +
      C (h (span D - 1)) * endpointA h D := by
  unfold coframeOf endpointA
  rw [coframeVecOf_eq h D, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

/-! ### The opposite endpoint

For the rotation `W` of `V` the coframe `C` is affine in the same letter, with slope
`b = -∑_i Π_{1,i} z^{M-i}` read off the row of `Π` at the column position one. -/

/-- The indicator vector of the columns at position one. -/
def colIndicator (D : BetaDiagram (n + 1)) : Fin n → K :=
  fun j => if colPos D j = 1 then 1 else 0

/-- The endpoint column `b = -∑_i Π_{1,i} z^{M-i}`; zero when no proper column sits at one. -/
noncomputable def endpointB (h : ℕ → K) (D : BetaDiagram (n + 1)) : K[X] :=
  ∑ i, C (-(((properMatrixOf h D)⁻¹)ᵀ *ᵥ colIndicator D) i) * X ^ (span D - rowPos D i)

/-- Rotation transposes the proper matrix and reverses both indices. -/
theorem properMatrixOf_rot (h : ℕ → K) {V W : BetaDiagram (n + 1)} {c : ℤ}
    (hr : ∀ i, W.row i = c - V.col i.rev) (hc : ∀ i, W.col i = c - V.row i.rev) (i j : Fin n) :
    properMatrixOf h W i j = properMatrixOf h V j.rev i.rev := by
  simp only [properMatrixOf, Matrix.of_apply, hr, hc, Fin.rev_succ, Fin.rev_castSucc]
  congr 1
  ring

theorem properMatrixOf_rot_eq (h : ℕ → K) {V W : BetaDiagram (n + 1)} {c : ℤ}
    (hr : ∀ i, W.row i = c - V.col i.rev) (hc : ∀ i, W.col i = c - V.row i.rev) :
    properMatrixOf h W = ((properMatrixOf h V)ᵀ).submatrix Fin.rev Fin.rev := by
  ext i j
  exact properMatrixOf_rot h hr hc i j

theorem inv_properMatrixOf_rot (h : ℕ → K) {V W : BetaDiagram (n + 1)} {c : ℤ}
    (hr : ∀ i, W.row i = c - V.col i.rev) (hc : ∀ i, W.col i = c - V.row i.rev) (i j : Fin n) :
    (properMatrixOf h W)⁻¹ i j = (properMatrixOf h V)⁻¹ j.rev i.rev := by
  rw [properMatrixOf_rot_eq h hr hc]
  have := Matrix.inv_submatrix_equiv ((properMatrixOf h V)ᵀ) Fin.revPerm Fin.revPerm
  have e : ((properMatrixOf h V)ᵀ).submatrix Fin.rev Fin.rev =
      ((properMatrixOf h V)ᵀ).submatrix Fin.revPerm Fin.revPerm := rfl
  rw [e, this, ← Matrix.transpose_nonsing_inv]
  simp [Fin.revPerm]

section Rotation

variable (h : ℕ → K) {V W : BetaDiagram (n + 1)} {c : ℤ}
  (hr : ∀ i, W.row i = c - V.col i.rev) (hc : ∀ i, W.col i = c - V.row i.rev)
  (hW : W.col (Fin.last n) = 0)

include hc hW in
theorem rot_const : c = V.row 0 := by
  have := hc (Fin.last n)
  rw [Fin.rev_last] at this
  omega

include hr hc hW in
theorem span_rot : span W = span V := by
  have h0 := rot_const hc hW
  have e : (span W : ℤ) = span V := by
    rw [span_cast, span_cast]
    unfold BetaDiagram.largestLabel
    rw [hr 0, hW, Fin.rev_zero, h0]
    ring
  exact_mod_cast e

include hr hc hW in
theorem rowPos_rot (i : Fin n) : rowPos W i = span V - colPos V i.rev := by
  have h0 := rot_const hc hW
  have hlt := colPos_lt_span V i.rev
  have e := rowPos_cast W i
  have e2 := colPos_cast V i.rev
  have e3 := span_cast V
  unfold BetaDiagram.largestLabel at e3
  rw [hW, hr, Fin.rev_succ, h0] at e
  omega

include hc hW in
theorem colPos_rot (j : Fin n) : colPos W j = span V - rowPos V j.rev := by
  have h0 := rot_const hc hW
  have hlt := rowPos_lt_span V j.rev
  have e := colPos_cast W j
  have e2 := rowPos_cast V j.rev
  have e3 := span_cast V
  unfold BetaDiagram.largestLabel at e3
  rw [hW, hc, Fin.rev_castSucc, h0] at e
  omega

include hr hc hW in
theorem endpointAVec_rot (i : Fin n) :
    endpointAVec h W i = -(((properMatrixOf h V)⁻¹)ᵀ *ᵥ colIndicator V) i.rev := by
  unfold endpointAVec
  simp only [Pi.neg_apply, neg_inj, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inv_properMatrixOf_rot h hr hc]
  have hk := colPos_lt_span V k
  have hk1 := colPos_pos V k
  simp only [Fin.revPerm_apply, Fin.rev_rev, portIndicator, colIndicator,
    rowPos_rot hr hc hW, span_rot hr hc hW]
  congr 1
  by_cases h1 : colPos V k = 1
  · simp [h1]
    omega
  · simp [h1]
    omega

include hr hc hW in
/-- The endpoint column of the rotated board is the column `b` read from the row of `Π` at the
column position one. -/
theorem endpointA_rot : endpointA h W = endpointB h V := by
  unfold endpointA endpointB
  conv_rhs => rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.revPerm_apply, endpointAVec_rot h hr hc hW, colPos_rot hc hW]

include hr hc hW in
/-- `C = C₀ + y b` for the rotation `W` of `V`: the coframe of `W` is affine in the same top
letter, with slope `endpointB h V` and the same value of `y = H_m`. -/
theorem coframeOf_rot_eq : coframeOf h W =
    coframeOf (Function.update h (span V - 1) 0) W + C (h (span V - 1)) * endpointB h V := by
  rw [← endpointA_rot h hr hc hW, ← span_rot hr hc hW]
  exact coframeOf_eq h W

end Rotation

/-- A missing native port gives the zero vector. -/
theorem endpointA_eq_zero_of_no_port (h : ℕ → K) (D : BetaDiagram (n + 1))
    (hno : ∀ i, rowPos D i + 1 ≠ span D) : endpointA h D = 0 := by
  have : portIndicator (K := K) D = 0 := by
    funext i; simp [portIndicator, hno i]
  unfold endpointA endpointAVec
  simp [this]

/-! ### The disconnected case: an endpoint component

A component of the proper corner whose rows and columns form a block with zero below it carries
the whole port column: the column of `Π` at its head row is the column of the inverse of the
component's own matrix, extended by zero. -/

/-- The column of the inverse at the head row of a block with a zero block below it. -/
theorem inv_mulVec_single_block {T : Matrix (Fin n) (Fin n) K} (hT : T.det ≠ 0) {k : ℕ}
    (r cc : Fin k → Fin n) (hr : Function.Injective r) (F : Matrix (Fin k) (Fin k) K)
    (hF : ∀ p q, F p q = T (r p) (cc q)) (hdet : F.det ≠ 0)
    (hz : ∀ i, i ∉ Set.range r → ∀ q, T i (cc q) = 0) (p0 : Fin k) :
    T⁻¹ *ᵥ Pi.single (r p0) 1 = fun j => ∑ q, if cc q = j then F⁻¹ q p0 else 0 := by
  classical
  set v : Fin n → K := fun j => ∑ q, if cc q = j then F⁻¹ q p0 else 0 with hv
  have hTv : T *ᵥ v = Pi.single (r p0) 1 := by
    funext i
    have e : (T *ᵥ v) i = ∑ q, T i (cc q) * F⁻¹ q p0 := by
      simp only [Matrix.mulVec, dotProduct, hv, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp [mul_ite]
    rw [e]
    by_cases hi : i ∈ Set.range r
    · obtain ⟨p, rfl⟩ := hi
      have : ∑ q, T (r p) (cc q) * F⁻¹ q p0 = (F * F⁻¹) p p0 := by
        simp only [Matrix.mul_apply, hF]
      rw [this, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)]
      simp [Matrix.one_apply, Pi.single_apply, hr.eq_iff]
    · rw [Finset.sum_eq_zero fun q _ => by rw [hz i hi q, zero_mul]]
      have : i ≠ r p0 := fun h => hi ⟨p0, h.symm⟩
      simp [Pi.single_apply, this]
  rw [← hTv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hT),
    Matrix.one_mulVec]

section Block

variable {k : ℕ}

theorem portIndicator_eq_single (D : BetaDiagram (n + 1)) (i0 : Fin n)
    (hi0 : rowPos D i0 + 1 = span D) : portIndicator D = (Pi.single i0 1 : Fin n → K) := by
  funext i
  by_cases hi : i = i0
  · subst hi; simp [portIndicator, hi0]
  · have : rowPos D i + 1 ≠ span D := fun h' => hi (rowPos_injective D (by omega))
    simp [portIndicator, this, hi]

/-- The vector `(G_s, 1)` of the own coframe is annihilated by every row but the top one of the
full matrix, and the top row returns the top quotient. -/
theorem fullMatrixOf_mulVec_coframe (h : ℕ → K) (E : BetaDiagram (k + 1))
    (hT : (properMatrixOf h E).det ≠ 0) :
    fullMatrixOf h E *ᵥ (Fin.snoc (α := fun _ => K) (coframeVecOf h E) 1) =
      Pi.single 0 (topQuotientOf h E) := by
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · have h1 := coeff_span h E (coframeVecOf h E)
    have h2 : topQuotientOf h E = PowerSeries.coeff (span E) (PowerSeries.mk h *
        (uniPoly (coframeVecOf h E) (colPos E) : PowerSeries K)) := rfl
    rw [h2, h1]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, fullMatrixOf, Matrix.of_apply, mul_one, Pi.single_eq_same]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => mul_comm _ _
  · have h1 := congrFun (properMatrix_mulVec_coframeVecOf h E hT) i'
    simp only [Matrix.mulVec, dotProduct, properMatrixOf, Pi.neg_apply, topVecOf,
      Matrix.of_apply] at h1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, fullMatrixOf, Matrix.of_apply, mul_one]
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i')]
    linear_combination h1

/-- The endpoint column is the head column of the inverse of a block with a zero block below
it, placed at the positions of the block's columns. -/
theorem endpointA_eq_sum (h : ℕ → K) (D : BetaDiagram (n + 1))
    (hT : (properMatrixOf h D).det ≠ 0) {k : ℕ} (r cc : Fin k → Fin n)
    (hr : Function.Injective r) (F : Matrix (Fin k) (Fin k) K)
    (hFeq : ∀ p q, F p q = properMatrixOf h D (r p) (cc q)) (hdet : F.det ≠ 0)
    (hz : ∀ i, i ∉ Set.range r → ∀ q, properMatrixOf h D i (cc q) = 0) (p0 : Fin k)
    (hhead : rowPos D (r p0) + 1 = span D) :
    endpointA h D = -∑ q, C (F⁻¹ q p0) * X ^ colPos D (cc q) := by
  classical
  have hcolumn := inv_mulVec_single_block hT r cc hr F hFeq hdet hz p0
  unfold endpointA endpointAVec
  rw [portIndicator_eq_single D (r p0) hhead, hcolumn]
  simp only [Pi.neg_apply, map_neg, map_sum, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [apply_ite C]

/-- The endpoint column of a block with a zero block below it:
`a = -z^A g / k_E`, in the form `a k_E = -z^A g`, where `g` is the own coframe of the block
read as a diagram `E` with rows and columns translated by `A`. -/
theorem endpointA_block (h : ℕ → K) (D : BetaDiagram (n + 1))
    (hT : (properMatrixOf h D).det ≠ 0) (E : BetaDiagram (k + 1)) (A : ℕ)
    (r cc : Fin (k + 1) → Fin n) (hr : Function.Injective r)
    (hrow : ∀ p, (rowPos D (r p) : ℤ) = E.row p + A)
    (hcol : ∀ q, (colPos D (cc q) : ℤ) = E.col q + A) (hEn : E.col (Fin.last k) = 0)
    (hz : ∀ i, i ∉ Set.range r → ∀ q, properMatrixOf h D i (cc q) = 0)
    (hhead : rowPos D (r 0) + 1 = span D) (hTE : (properMatrixOf h E).det ≠ 0)
    (hF : (fullMatrixOf h E).det ≠ 0) :
    topQuotientOf h E ≠ 0 ∧
      endpointA h D * C (topQuotientOf h E) = -(X ^ A * coframeOf h E) := by
  classical
  have hFeq : ∀ p q, fullMatrixOf h E p q = properMatrixOf h D (r p) (cc q) := by
    intro p q
    simp only [fullMatrixOf, properMatrixOf, Matrix.of_apply]
    congr 1
    have := rowPos_sub_colPos D (r p) (cc q)
    have := hrow p
    have := hcol q
    omega
  have hq : topQuotientOf h E ≠ 0 := by
    intro h0
    have := schurOf_eq_cornerOf_mul_topQuotientOf h E hTE
    rw [h0, mul_zero] at this
    exact hF this
  refine ⟨hq, ?_⟩
  have hvec : ∀ q, (fullMatrixOf h E)⁻¹ q 0 * topQuotientOf h E =
      (Fin.snoc (α := fun _ => K) (coframeVecOf h E) 1 : Fin (k + 1) → K) q := by
    intro q
    have h1 := fullMatrixOf_mulVec_coframe h E hTE
    have h2 : (Fin.snoc (α := fun _ => K) (coframeVecOf h E) 1 : Fin (k + 1) → K) =
        (fullMatrixOf h E)⁻¹ *ᵥ (topQuotientOf h E • (Pi.single 0 1 : Fin (k + 1) → K)) := by
      rw [← Pi.single_smul' 0 (topQuotientOf h E) (1 : K), smul_eq_mul, mul_one, ← h1,
        Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hF),
        Matrix.one_mulVec]
    rw [h2, Matrix.mulVec_smul, Matrix.mulVec_single_one]
    simp [mul_comm]
  have hcp : ∀ q, colPos D (cc q) = (E.col q).toNat + A := by
    intro q
    have := hcol q
    have := col_last_le E q
    omega
  have hEc : ∀ j : Fin k, colPos E j = (E.col j.castSucc).toNat := by
    intro j
    have := colPos_cast E j
    omega
  have hsum : endpointA h D * C (topQuotientOf h E) =
      -∑ q, C ((fullMatrixOf h E)⁻¹ q 0 * topQuotientOf h E) * X ^ colPos D (cc q) := by
    rw [endpointA_eq_sum h D hT r cc hr _ hFeq hF hz 0 hhead, neg_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul]
    ring
  rw [hsum, neg_inj]
  simp_rw [hvec]
  rw [Fin.sum_univ_castSucc, coframeOf, mul_add, mul_one, Finset.mul_sum]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hcp, hEn]
  simp [hEc, pow_add, add_comm]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- A unit component (a single row and column at the same position) carries the port:
`a = -z^c / ϑ`, in the form `a H₀ = -z^c`. -/
theorem endpointA_unit (h : ℕ → K) (D : BetaDiagram (n + 1))
    (hT : (properMatrixOf h D).det ≠ 0) (i0 j0 : Fin n) (hpos : rowPos D i0 = colPos D j0)
    (hz : ∀ i, i ≠ i0 → properMatrixOf h D i j0 = 0) (hhead : rowPos D i0 + 1 = span D)
    (h0 : h 0 ≠ 0) : endpointA h D * C (h 0) = -X ^ colPos D j0 := by
  have hF : ∀ p q : Fin 1, (!![h 0] : Matrix (Fin 1) (Fin 1) K) p q =
      properMatrixOf h D ((fun _ => i0) p) ((fun _ => j0) q) := by
    intro p q
    have := rowPos_sub_colPos D i0 j0
    rw [hpos, sub_self] at this
    simp only [properMatrixOf, Matrix.of_apply, ← this, Subsingleton.elim p 0,
      Subsingleton.elim q 0]
    simp [letterOf]
  rw [endpointA_eq_sum h D hT (fun _ => i0) (fun _ => j0) (fun _ _ _ => Subsingleton.elim _ _)
    (!![h 0]) hF (by simpa using h0)
    (fun i hi q => hz i fun h' => hi ⟨0, h'.symm⟩) 0 hhead]
  have hinv : (!![h 0] : Matrix (Fin 1) (Fin 1) K)⁻¹ = !![(h 0)⁻¹] :=
    Matrix.inv_eq_right_inv (by ext i j; fin_cases i; fin_cases j; simp [h0])
  rw [hinv]
  simp
  rw [← map_mul, inv_mul_cancel₀ h0, map_one]

end Block

/-! ### The coordinate `α_{E,p}`

`α_{E,p} = [(H^p - p ϑ^{p-1} H) g]_{L+1} - p(p-1) ϑ^{p-2} H_1 k_E`, with `g` the own coframe of
`E`, `L` its span and `k_E = [H g]_L` its top quotient. -/

section Alpha

open PowerSeries in
/-- The coordinate `α_{E,p}` for an arbitrary letter sequence, coframe polynomial and span. -/
noncomputable def alphaOf {R : Type*} [CommRing R] (h : ℕ → R) (G : R[X]) (p L : ℕ) : R :=
  coeff (L + 1) ((seriesOf h ^ p - PowerSeries.C ((p : R) * h 0 ^ (p - 1)) * seriesOf h) *
      (G : PowerSeries R)) -
    (p : R) * ((p - 1 : ℕ) : R) * h 0 ^ (p - 2) * h 1 *
      coeff L (seriesOf h * (G : PowerSeries R))

theorem map_seriesOf {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (h : ℕ → R) :
    PowerSeries.map f (seriesOf h) = seriesOf (fun k => f (h k)) := by
  ext k
  simp [seriesOf]

theorem alphaOf_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (h : ℕ → R)
    (G : R[X]) (p L : ℕ) :
    f (alphaOf h G p L) = alphaOf (fun k => f (h k)) (G.map f) p L := by
  have key : ∀ (n : ℕ) (F : PowerSeries R), f (PowerSeries.coeff n F) =
      PowerSeries.coeff n (PowerSeries.map f F) := fun n F => (PowerSeries.coeff_map f n F).symm
  unfold alphaOf
  rw [map_sub]
  congr 1
  · rw [key]
    simp only [map_mul, map_sub, map_pow, map_natCast, PowerSeries.map_C, map_seriesOf,
      ← Polynomial.polynomial_map_coe]
  · rw [map_mul, key]
    simp only [map_mul, map_sub, map_pow, map_natCast, PowerSeries.map_C, map_seriesOf,
      ← Polynomial.polynomial_map_coe]

/-- The coordinate `α_{E,p}` of a diagram over the raw field. -/
noncomputable def alphaE (p : ℕ) {k : ℕ} (E : BetaDiagram (k + 1)) : CohField :=
  alphaOf cohLetters (coframe E) p (span E)

section AlphaReduction

open PowerSeries

variable {K : Type*} [Field K]

theorem coeff_one_mul (A B : K⟦X⟧) :
    coeff 1 (A * B) = constantCoeff A * coeff 1 B + coeff 1 A * constantCoeff B := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp [add_comm]

theorem coeff_one_pow (A : K⟦X⟧) (m : ℕ) :
    coeff 1 (A ^ m) = m * constantCoeff A ^ (m - 1) * coeff 1 A := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, coeff_one_mul, ih, map_pow]
    rcases m with _ | m
    · simp
    · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring_nf

/-- Series congruent modulo `X²` have congruent powers: the coefficients at `0` and `1` agree. -/
theorem coeff_pow_congr {A B : K⟦X⟧} (hA : coeff 0 A = coeff 0 B) (hB : coeff 1 A = coeff 1 B)
    (m : ℕ) {i : ℕ} (hi : i ≤ 1) : coeff i (A ^ m) = coeff i (B ^ m) := by
  have hd : (PowerSeries.X ^ 2 : K⟦X⟧) ∣ A - B := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    interval_cases j
    · rw [map_sub, hA, sub_self]
    · rw [map_sub, hB, sub_self]
  have := (hd.trans (sub_dvd_pow_sub_pow A B m))
  rw [PowerSeries.X_pow_dvd_iff] at this
  have h := this i (by omega)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

/-- For `L ≥ 2` the coordinate `α` is the coefficient `[z^{L+1}] P^p G^{1-p}` of the numerator
and the inverse coframe: the two cap terms cancel against the top two coefficients of `HG`. -/
theorem alphaOf_eq (h : ℕ → K) (G : K[X]) (hG : G.coeff 0 = 1) {p L : ℕ} (hp : 2 ≤ p)
    (hL : 2 ≤ L) :
    alphaOf h G p L = coeff (L + 1) (((trunc L (seriesOf h * (G : K⟦X⟧)) : K[X]) : K⟦X⟧) ^ p *
      ((G : K⟦X⟧)⁻¹) ^ (p - 1)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have e1 : q + 2 - 1 = q + 1 := by omega
  have e2 : q + 2 - 2 = q := by omega
  rw [e1]
  set Gs : K⟦X⟧ := (G : K⟦X⟧) with hGs
  set Hs : K⟦X⟧ := seriesOf h with hHs
  have hc : constantCoeff Gs ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hGs, Polynomial.coeff_coe, hG]
    exact one_ne_zero
  have hu : Gs * Gs⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hc
  set N : K⟦X⟧ := Hs * Gs with hN
  set P : K⟦X⟧ := ((trunc L N : K[X]) : K⟦X⟧) with hP
  set T : K⟦X⟧ := PowerSeries.mk (fun j => coeff (L + j) N) with hT
  have hNT : N = P + PowerSeries.X ^ L * T := by
    ext n
    rw [map_add, hP, Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_X_pow_mul',
      hT]
    by_cases hn : n < L
    · simp [hn, not_le.mpr hn]
    · rw [if_neg hn, if_pos (not_lt.mp hn), PowerSeries.coeff_mk]
      simp [Nat.add_sub_cancel' (not_lt.mp hn)]
  have hH : Hs = N * Gs⁻¹ := by
    rw [hN, mul_assoc, hu, mul_one]
  have hPu : P * Gs⁻¹ = Hs - PowerSeries.X ^ L * (T * Gs⁻¹) := by
    rw [hH, hNT]; ring
  -- `H^p G = N^p G^{1-p}`
  have h1 : Hs ^ (q + 2) * Gs = N ^ (q + 2) * Gs⁻¹ ^ (q + 1) := by
    rw [hH, mul_pow]
    have : Gs⁻¹ ^ (q + 2) * Gs = Gs⁻¹ ^ (q + 1) := by
      rw [pow_succ, mul_assoc, mul_comm Gs⁻¹ Gs, hu, mul_one]
    rw [mul_assoc, this]
  obtain ⟨w, hw⟩ := pow_add_expand P (PowerSeries.X ^ L * T) q
  have h2 : Hs ^ (q + 2) * Gs = P ^ (q + 2) * Gs⁻¹ ^ (q + 1) +
      (q + 2 : K⟦X⟧) * PowerSeries.X ^ L * (T * (P * Gs⁻¹) ^ (q + 1)) +
      PowerSeries.X ^ (2 * L) * (T ^ 2 * w * Gs⁻¹ ^ (q + 1)) := by
    rw [h1, hNT, hw]
    rw [show 2 * L = L + L by ring, pow_add PowerSeries.X L L]
    ring
  have hX : ∀ i, i ≤ 1 → coeff i (P * Gs⁻¹) = coeff i Hs := by
    intro i hi
    rw [hPu, map_sub, PowerSeries.coeff_X_pow_mul', if_neg (by omega), sub_zero]
  have hc0 : coeff 0 ((P * Gs⁻¹) ^ (q + 1)) = h 0 ^ (q + 1) := by
    rw [coeff_pow_congr (hX 0 (by omega)) (hX 1 le_rfl) (q + 1) (Nat.zero_le 1),
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
    simp [hHs, seriesOf]
  have hc1 : coeff 1 ((P * Gs⁻¹) ^ (q + 1)) = (q + 1 : K) * h 0 ^ q * h 1 := by
    rw [coeff_pow_congr (hX 0 (by omega)) (hX 1 le_rfl) (q + 1) le_rfl, coeff_one_pow]
    simp [hHs, seriesOf]
  have hB : PowerSeries.coeff (L + 1) (PowerSeries.X ^ L * (T * (P * Gs⁻¹) ^ (q + 1))) =
      PowerSeries.coeff L N * ((q + 1 : K) * h 0 ^ q * h 1) +
        PowerSeries.coeff (L + 1) N * h 0 ^ (q + 1) := by
    rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), show L + 1 - L = 1 by omega,
      PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
    simp only [Finset.Nat.antidiagonal_zero, Finset.map_singleton, Finset.sum_cons,
      Finset.sum_singleton]
    simp [hT, hc0, hc1, add_comm]
  have hC : PowerSeries.coeff (L + 1) (PowerSeries.X ^ (2 * L) * (T ^ 2 * w * Gs⁻¹ ^ (q + 1))) = 0 := by
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hmain := congrArg (PowerSeries.coeff (L + 1)) h2
  have hq2 : ((q : K⟦X⟧) + 2) = PowerSeries.C ((q : K) + 2) := by
    rw [map_add, map_natCast, map_ofNat]
  rw [map_add, map_add, hC, add_zero, hq2, mul_assoc, PowerSeries.coeff_C_mul, hB] at hmain
  unfold alphaOf
  rw [sub_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, ← hN, hmain]
  simp only [e1, e2, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- A unit component (own coframe `1`, span zero): `α_{E,p} = -p(p-1) ϑ^{p-1} H_1`. -/
theorem alphaOf_unit (h : ℕ → K) (p : ℕ) :
    alphaOf h 1 p 0 = -((p : K) * ((p - 1 : ℕ) : K) * h 0 ^ (p - 2) * h 1 * h 0) := by
  unfold alphaOf
  rw [Polynomial.coe_one, mul_one, mul_one, map_sub, coeff_one_pow, PowerSeries.coeff_C_mul,
    zero_add]
  have e : PowerSeries.coeff 0 (seriesOf h) = h 0 := by simp [seriesOf]
  have e1 : PowerSeries.coeff 1 (seriesOf h) = h 1 := by simp [seriesOf]
  have e0 : PowerSeries.constantCoeff (seriesOf h) = h 0 := by simp [seriesOf]
  rw [e, e1, e0]
  rcases p with _ | _ | p
  · simp
  · simp
  · have : p + 1 + 1 - 1 = p + 1 := by omega
    have h2 : p + 1 + 1 - 2 = p := by omega
    rw [this, h2]
    push_cast
    ring

end AlphaReduction

section AlphaCoordinates

variable {k : ℕ} (E : BetaDiagram (k + 1))

/-- For span at least two, `α_{E,p}` is the coefficient `[z^{L+1}] P^p G^{1-p}` of the own
atlas: the image under the coordinate map of a polynomial in the atlas coordinates, free of the
letter `H_L` and of every letter above the span. -/
theorem alphaE_eq_toField (hE : E.Connected) {p : ℕ} (hp : 2 ≤ p) (hL : 2 ≤ span E) :
    alphaE p E = toField E (PowerSeries.coeff (span E + 1)
      (((mP E : (ModelRing E)[X]) : PowerSeries (ModelRing E)) ^ p * mGinv E ^ (p - 1))) := by
  have hT := properDet_cohLetters_ne_zero hE
  have hcoe : (coframe E).coeff 0 = 1 := by
    have := constantCoeff_coframeOf cohLetters E
    rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe] at this
  unfold alphaE
  rw [alphaOf_eq cohLetters (coframe E) hcoe hp hL]
  have e := (PowerSeries.coeff_map (toField E : ModelRing E →+* CohField) (span E + 1)
    (((mP E : (ModelRing E)[X]) : PowerSeries (ModelRing E)) ^ p * mGinv E ^ (p - 1)))
  rw [toField_ringHom_apply] at e
  have hm : PowerSeries.map (toField E : ModelRing E →+* CohField)
      (((mP E : (ModelRing E)[X]) : PowerSeries (ModelRing E)) ^ p * mGinv E ^ (p - 1)) =
        (numerator E : PowerSeries CohField) ^ p * (coframe E : PowerSeries CohField)⁻¹ ^ (p - 1) := by
    rw [map_mul, map_pow, map_pow, ← Polynomial.polynomial_map_coe, toField_mP E hT,
      toField_mGinv E]
  rw [← e, hm]
  rfl

end AlphaCoordinates

section Positivity

/-- A rational power series with nonnegative coefficients. -/
def NonnegSeries (F : PowerSeries ℚ) : Prop := ∀ n, 0 ≤ PowerSeries.coeff n F

theorem NonnegSeries.mul {F G : PowerSeries ℚ} (hF : NonnegSeries F) (hG : NonnegSeries G) :
    NonnegSeries (F * G) := fun n => by
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hF _) (hG _)

theorem NonnegSeries.pow {F : PowerSeries ℚ} (hF : NonnegSeries F) (m : ℕ) :
    NonnegSeries (F ^ m) := by
  induction m with
  | zero => intro n; rw [pow_zero, PowerSeries.coeff_one]; split_ifs <;> norm_num
  | succ m ih => rw [pow_succ]; exact ih.mul hF

/-- A single term of the convolution is bounded by the coefficient of the product. -/
theorem coeff_mul_ge {F G : PowerSeries ℚ} (hF : NonnegSeries F) (hG : NonnegSeries G) {i n : ℕ}
    (hi : i ≤ n) : PowerSeries.coeff i F * PowerSeries.coeff (n - i) G ≤
      PowerSeries.coeff n (F * G) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.single_le_sum (f := fun x : ℕ × ℕ => PowerSeries.coeff x.1 F *
    PowerSeries.coeff x.2 G) (fun x _ => mul_nonneg (hF _) (hG _))
    (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp; omega) : (i, n - i) ∈
      Finset.HasAntidiagonal.antidiagonal n)

/-- Powers of a series with nonnegative coefficients and constant term one grow
coefficientwise. -/
theorem coeff_pow_mono {F : PowerSeries ℚ} (hF : NonnegSeries F)
    (h0 : PowerSeries.constantCoeff F = 1) {j m : ℕ} (hjm : j ≤ m) (n : ℕ) :
    PowerSeries.coeff n (F ^ j) ≤ PowerSeries.coeff n (F ^ m) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjm
  have := coeff_mul_ge (hF.pow j) (hF.pow t) (Nat.le_refl n)
  rw [pow_add]
  have h00 : PowerSeries.coeff 0 (F ^ t) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, h0, one_pow]
  simpa [h00] using this

end Positivity

section Specialization

variable {n : ℕ} (D : BetaDiagram (n + 1)) (J : Fin n → ℚ) (Sv : ℕ → ℚ)

/-- A rational point of the model ring: `ϑ = 1`, the native coefficients `J`, the available
numerator coefficients `Sv`, and every letter above the span zero. -/
def specVar : VarIdx D → ℚ
  | Sum.inl none => 1
  | Sum.inl (some (Sum.inl j)) => J j
  | Sum.inl (some (Sum.inr i)) => Sv i.1
  | Sum.inr _ => 0

/-- Evaluation of the model ring at the point `specVar`. -/
noncomputable def specHom : ModelRing D →+* ℚ :=
  (MvPolynomial.aeval (specVar D J Sv) : ModelRing D →ₐ[ℚ] ℚ)

theorem specHom_X (v : VarIdx D) : specHom D J Sv (MvPolynomial.X v) = specVar D J Sv v :=
  MvPolynomial.aeval_X _ _

theorem specHom_mNum (i : ℕ) : specHom D J Sv (mNum D i) =
    if i = 0 then 1 else if 0 < i ∧ i < span D ∧ i ∉ rowSet D then Sv i else 0 := by
  unfold mNum
  by_cases h0 : i = 0
  · simp [h0, specHom_X, specVar]
  · by_cases hc : 0 < i ∧ i < span D ∧ i ∉ rowSet D
    · simp [h0, hc, specHom_X, specVar]
    · simp [h0, hc]

theorem map_mG : (mG D).map (specHom D J Sv) = uniPoly J (colPos D) := by
  unfold mG
  rw [uniPoly_map]
  congr 1
  funext j
  rw [specHom_X]
  rfl

theorem map_mGinv : PowerSeries.map (specHom D J Sv) (mGinv D) =
    ((uniPoly J (colPos D) : ℚ[X]) : PowerSeries ℚ)⁻¹ := by
  have hc : PowerSeries.constantCoeff ((uniPoly J (colPos D) : ℚ[X]) : PowerSeries ℚ) ≠ 0 := by
    rw [constantCoeff_uniPoly _ _ (colPos_pos D)]; exact one_ne_zero
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc]
  have := congrArg (PowerSeries.map (specHom D J Sv)) (mG_mul_mGinv D)
  rw [map_mul, map_one, ← Polynomial.polynomial_map_coe, map_mG] at this
  rw [mul_comm]
  exact this

theorem coeff_map_mP (i : ℕ) : ((mP D).map (specHom D J Sv)).coeff i =
    if i < span D then (if i = 0 then 1 else if 0 < i ∧ i < span D ∧ i ∉ rowSet D then Sv i
      else 0) else 0 := by
  rw [Polynomial.coeff_map, mP_coeff]
  by_cases h : i < span D
  · rw [if_pos h, if_pos h, specHom_mNum]
  · rw [if_neg h, if_neg h, map_zero]

/-- The model coefficient of `α` at a rational point. -/
theorem specHom_coeff (p : ℕ) (i : ℕ) :
    specHom D J Sv (PowerSeries.coeff i
      (((mP D : (ModelRing D)[X]) : PowerSeries (ModelRing D)) ^ p * mGinv D ^ (p - 1))) =
    PowerSeries.coeff i ((((mP D).map (specHom D J Sv) : ℚ[X]) : PowerSeries ℚ) ^ p *
      (((uniPoly J (colPos D) : ℚ[X]) : PowerSeries ℚ)⁻¹) ^ (p - 1)) := by
  have e := PowerSeries.coeff_map (specHom D J Sv) i
    (((mP D : (ModelRing D)[X]) : PowerSeries (ModelRing D)) ^ p * mGinv D ^ (p - 1))
  rw [← e, map_mul, map_pow, map_pow, ← Polynomial.polynomial_map_coe, map_mGinv]

/-- The geometric series `∑ z^{dk}`. -/
noncomputable def geomSeries (d : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => if d ∣ m then 1 else 0

theorem one_sub_X_pow_mul_geomSeries {d : ℕ} (hd : 0 < d) :
    (1 - (PowerSeries.X : PowerSeries ℚ) ^ d) * geomSeries d = 1 := by
  ext m
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', geomSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_one]
  by_cases hm : d ≤ m
  · rw [if_pos hm, PowerSeries.coeff_mk]
    have : m ≠ 0 := by omega
    have e : d ∣ m ↔ d ∣ m - d := by
      constructor
      · intro h; exact Nat.dvd_sub h dvd_rfl
      · intro h
        have := Nat.dvd_add h (dvd_refl d)
        rwa [Nat.sub_add_cancel hm] at this
    by_cases h : d ∣ m
    · rw [if_pos h, if_pos (e.mp h), if_neg this]; norm_num
    · rw [if_neg h, if_neg (fun h' => h (e.mpr h')), if_neg this]; norm_num
  · rw [if_neg hm]
    by_cases h0 : m = 0
    · simp [h0]
    · have : ¬ d ∣ m := fun h => hm (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h)
      simp [this, h0]

theorem nonneg_geomSeries (d : ℕ) : NonnegSeries (geomSeries d) := fun m => by
  rw [geomSeries, PowerSeries.coeff_mk]; split_ifs <;> norm_num

theorem uniPoly_single (d : ℕ) {n : ℕ} (j0 : Fin n) (J : Fin n → ℚ) (s : Fin n → ℕ)
    (hJ : ∀ j, j ≠ j0 → J j = 0) (hs : s j0 = d) (c : ℚ) (hc : J j0 = c) :
    uniPoly J s = 1 + Polynomial.C c * Polynomial.X ^ d := by
  unfold uniPoly
  rw [Finset.sum_eq_single j0 (fun j _ hj => by rw [hJ j hj]; simp) (by simp), hs, hc]

section Nonvanishing

variable {n : ℕ} (D : BetaDiagram (n + 1)) (J : Fin n → ℚ) (Sv : ℕ → ℚ)

/-- The specialized numerator, as a series. -/
noncomputable abbrev specP : PowerSeries ℚ := (((mP D).map (specHom D J Sv) : ℚ[X]) : PowerSeries ℚ)

theorem nonneg_specP (hSv : ∀ i, 0 ≤ Sv i) : NonnegSeries (specP D J Sv) := fun i => by
  rw [Polynomial.coeff_coe, coeff_map_mP]
  split_ifs <;> first | exact zero_le_one | exact hSv i | exact le_rfl

theorem constantCoeff_specP : PowerSeries.constantCoeff (specP D J Sv) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, coeff_map_mP,
    if_pos (span_pos D), if_pos rfl]

theorem coeff_specP {i : ℕ} (hi : i < span D) (h0 : 0 < i) (hr : i ∉ rowSet D) :
    PowerSeries.coeff i (specP D J Sv) = Sv i := by
  rw [Polynomial.coeff_coe, coeff_map_mP, if_pos hi, if_neg h0.ne', if_pos ⟨h0, hi, hr⟩]

theorem modelCoeff_ne_zero_of_spec (p : ℕ)
    (hne : PowerSeries.coeff (span D + 1) (specP D J Sv ^ p *
      (((uniPoly J (colPos D) : ℚ[X]) : PowerSeries ℚ)⁻¹) ^ (p - 1)) ≠ 0) :
    PowerSeries.coeff (span D + 1)
      (((mP D : (ModelRing D)[X]) : PowerSeries (ModelRing D)) ^ p * mGinv D ^ (p - 1)) ≠ 0 :=
  fun h => hne (by rw [← specHom_coeff D J Sv p, h, map_zero])

/-- A row (no native columns): the coefficient `[z^{L+1}] P^p` has a positive specialization
once the span is at least three, from the product `P_2 P_{L-1}`. -/
theorem row_coeff_ne_zero (D : BetaDiagram (0 + 1)) {p : ℕ} (hp : 2 ≤ p) (hL : 3 ≤ span D) :
    PowerSeries.coeff (span D + 1)
      (((mP D : (ModelRing D)[X]) : PowerSeries (ModelRing D)) ^ p * mGinv D ^ (p - 1)) ≠ 0 := by
  let J : Fin 0 → ℚ := fun _ => 0
  let Sv : ℕ → ℚ := fun i => if i = 2 ∨ i + 1 = span D then 1 else 0
  apply modelCoeff_ne_zero_of_spec D J Sv p
  have hG : (uniPoly J (colPos D) : ℚ[X]) = 1 := by simp [uniPoly]
  rw [hG, Polynomial.coe_one, inv_one, one_pow, mul_one]
  have hnn : ∀ i, 0 ≤ Sv i := fun i => by simp only [Sv]; split_ifs <;> norm_num
  have hrow : rowSet D = ∅ := by simp [rowSet]
  have hF := nonneg_specP D J Sv hnn
  have h0 := constantCoeff_specP D J Sv
  have c2 : PowerSeries.coeff 2 (specP D J Sv) = 1 := by
    rw [coeff_specP D J Sv (by omega) (by omega) (by simp [hrow])]; simp [Sv]
  have c1 : PowerSeries.coeff (span D - 1) (specP D J Sv) = 1 := by
    rw [coeff_specP D J Sv (by omega) (by omega) (by simp [hrow])]
    simp [Sv]; omega
  have h1 := coeff_mul_ge hF hF (i := 2) (n := span D + 1) (by omega)
  rw [show span D + 1 - 2 = span D - 1 by omega, c2, c1] at h1
  have h2 := coeff_pow_mono hF h0 hp (span D + 1)
  rw [pow_two] at h2
  intro h
  rw [h] at h2
  linarith

/-- The row of span two with `p ≥ 3`: the coefficient `[z^3] P^p` uses `P_1^3`. -/
theorem row_two_coeff_ne_zero (D : BetaDiagram (0 + 1)) {p : ℕ} (hp : 3 ≤ p) (hL : span D = 2) :
    PowerSeries.coeff (span D + 1)
      (((mP D : (ModelRing D)[X]) : PowerSeries (ModelRing D)) ^ p * mGinv D ^ (p - 1)) ≠ 0 := by
  let J : Fin 0 → ℚ := fun _ => 0
  let Sv : ℕ → ℚ := fun i => if i = 1 then 1 else 0
  apply modelCoeff_ne_zero_of_spec D J Sv p
  have hG : (uniPoly J (colPos D) : ℚ[X]) = 1 := by simp [uniPoly]
  rw [hG, Polynomial.coe_one, inv_one, one_pow, mul_one]
  have hnn : ∀ i, 0 ≤ Sv i := fun i => by simp only [Sv]; split_ifs <;> norm_num
  have hrow : rowSet D = ∅ := by simp [rowSet]
  have hF := nonneg_specP D J Sv hnn
  have h0 := constantCoeff_specP D J Sv
  have c1 : PowerSeries.coeff 1 (specP D J Sv) = 1 := by
    rw [coeff_specP D J Sv (by omega) (by omega) (by simp [hrow])]; simp [Sv]
  have h1 := coeff_mul_ge hF hF (i := 1) (n := 2) (by omega)
  simp only [c1, Nat.reduceSub, one_mul, ← pow_two] at h1
  have h3 := coeff_mul_ge hF (hF.pow 2) (i := 1) (n := 3) (by omega)
  simp only [c1, Nat.reduceSub, one_mul, ← pow_succ'] at h3
  have h2 := coeff_pow_mono hF h0 hp (span D + 1)
  rw [hL] at h2 ⊢
  intro h
  rw [h] at h2
  linarith

/-- Native columns: with `d` the least native column and `L + 1 = a d + b`, `0 ≤ b < d`, the
coefficient `[z^{L+1}] P^p G^{1-p}` is positive at the point `G = 1 - z^d`, `P = 1 + z^b`. -/
theorem native_coeff_ne_zero {n : ℕ} (D : BetaDiagram (n + 1 + 1)) (hD : D.Connected) {p : ℕ}
    (hp : 2 ≤ p) :
    PowerSeries.coeff (span D + 1)
      (((mP D : (ModelRing D)[X]) : PowerSeries (ModelRing D)) ^ p * mGinv D ^ (p - 1)) ≠ 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  set j0 : Fin (n + 1) := Fin.last n with hj0
  set d := colPos D j0 with hd
  have hdpos : 0 < d := colPos_pos D j0
  have hdlt : d < span D := colPos_lt_span D j0
  have hdmin : ∀ j, d ≤ colPos D j := fun j => by
    have := colPos_cast D j
    have := colPos_cast D j0
    have h3 : D.col j0.castSucc ≤ D.col j.castSucc :=
      D.col_strictAnti.antitone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last j))
    omega
  have hrowd : ∀ i, d ≤ rowPos D i := fun i => by
    have h1 := hD.2 i.castSucc (by have := i.isLt; simp; omega)
    have := colPos_cast D i
    have := rowPos_cast D i
    have := hdmin i
    have h4 : D.row ⟨(i.castSucc : Fin (n + 1 + 1)).val + 1, by have := i.isLt; simp; omega⟩ =
        D.row i.succ := rfl
    omega
  set b := (span D + 1) % d with hb
  set a := (span D + 1) / d with ha
  have hbd : b < d := Nat.mod_lt _ hdpos
  have hab : d * a + b = span D + 1 := Nat.div_add_mod _ _
  let J : Fin (n + 1) → ℚ := fun j => if j = j0 then -1 else 0
  let Sv : ℕ → ℚ := fun i => if i = b then 1 else 0
  apply modelCoeff_ne_zero_of_spec D J Sv (q + 2)
  have hG : (uniPoly J (colPos D) : ℚ[X]) = 1 + Polynomial.C (-1) * Polynomial.X ^ d :=
    uniPoly_single d j0 J (colPos D) (fun j hj => by simp [J, hj]) rfl (-1) (by simp [J])
  have hc : PowerSeries.constantCoeff ((uniPoly J (colPos D) : ℚ[X]) : PowerSeries ℚ) ≠ 0 := by
    rw [constantCoeff_uniPoly _ _ (colPos_pos D)]; exact one_ne_zero
  have hGs : ((uniPoly J (colPos D) : ℚ[X]) : PowerSeries ℚ)⁻¹ = geomSeries d := by
    refine ((PowerSeries.eq_inv_iff_mul_eq_one hc).mpr ?_).symm
    have e : ((uniPoly J (colPos D) : ℚ[X]) : PowerSeries ℚ) = 1 - PowerSeries.X ^ d := by
      rw [hG]; simp [sub_eq_add_neg]
    rw [e, mul_comm]
    exact one_sub_X_pow_mul_geomSeries hdpos
  rw [hGs]
  have hnn : ∀ i, 0 ≤ Sv i := fun i => by simp only [Sv]; split_ifs <;> norm_num
  have hP := nonneg_specP D J Sv hnn
  have hP0 := constantCoeff_specP D J Sv
  have hu := nonneg_geomSeries d
  have hPb : 1 ≤ PowerSeries.coeff b (specP D J Sv) := by
    by_cases hb0 : b = 0
    · rw [hb0, PowerSeries.coeff_zero_eq_constantCoeff_apply, hP0]
    · rw [coeff_specP D J Sv (by omega) (Nat.pos_of_ne_zero hb0) (fun hmem => by
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
        have := hrowd i
        omega)]
      simp [Sv]
  have hpow : 1 ≤ PowerSeries.coeff b (specP D J Sv ^ (q + 2)) := by
    have := coeff_pow_mono hP hP0 (show 1 ≤ q + 2 by omega) b
    rw [pow_one] at this
    linarith
  have hgeo : 1 ≤ PowerSeries.coeff (d * a) (geomSeries d ^ (q + 2 - 1)) := by
    rw [show q + 2 - 1 = q + 1 by omega, pow_succ]
    have := coeff_mul_ge (hu.pow q) hu (i := 0) (n := d * a) (Nat.zero_le _)
    have h00 : PowerSeries.coeff 0 (geomSeries d ^ q) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
      simp [geomSeries]
    rw [h00, Nat.sub_zero] at this
    have h1 : PowerSeries.coeff (d * a) (geomSeries d) = 1 := by
      simp [geomSeries]
    rw [h1] at this
    linarith
  have hmul := coeff_mul_ge (hP.pow (q + 2)) (hu.pow (q + 2 - 1)) (i := b) (n := span D + 1)
    (by omega)
  rw [show span D + 1 - b = d * a by omega] at hmul
  intro h
  rw [h] at hmul
  nlinarith [hmul, hpow, hgeo]

end Nonvanishing

end Specialization

section AlphaNonzero

variable {k : ℕ}

theorem cohLetters_ne_zero (j : ℕ) : cohLetters j ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2 (MvPolynomial.X_ne_zero j)

/-- `α_{E,p} ≠ 0` for a connected component of span at least two, unless `p = 2` and `E` is the
literal two-cell row.  The coefficient `[z^{L+1}] P^p G^{1-p}` of the own atlas is nonzero because
the coordinate map is injective and the polynomial has a positive value at a rational point. -/
theorem alphaE_ne_zero {E : BetaDiagram (k + 1)} (hE : E.Connected) {p : ℕ} (hp : 2 ≤ p)
    (hL : 2 ≤ span E) (hexc : ¬ (p = 2 ∧ k = 0 ∧ span E = 2)) : alphaE p E ≠ 0 := by
  have hT := properDet_cohLetters_ne_zero hE
  rw [alphaE_eq_toField E hE hp hL]
  intro h
  have hq := toField_injective E hT (h.trans (map_zero _).symm)
  clear h
  cases k with
  | zero =>
    by_cases h3 : 3 ≤ span E
    · exact row_coeff_ne_zero E hp h3 hq
    · have h2 : span E = 2 := by omega
      have hp3 : 3 ≤ p := by
        by_contra hlt
        exact hexc ⟨by omega, rfl, h2⟩
      exact row_two_coeff_ne_zero E hp3 h2 hq
  | succ k => exact native_coeff_ne_zero E hE hp hq

end AlphaNonzero

end Alpha

end SkewCoframeRigidity.Unshifted
