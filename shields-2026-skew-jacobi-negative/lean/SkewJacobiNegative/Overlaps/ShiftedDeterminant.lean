/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Shields.LinearAlgebra.Matrix.CauchyBinet

/-!
# The Jacobi–Trudi determinant after the shift `h_a ↦ ∑_m X^m h_{a-m}`

Formalizes `shields-2026-skew-base-computational.tex`, `lem:invariants`: the step of
Reiner–Shaw–van Willigenburg, Thm. 8.10, that the skew Schur function determines the skew
Schur function of the diagram with the top cell of every column removed.

Over any commutative ring `R` with a function `h : ℤ → R` that is `0` on negative integers and `1`
at `0`, this file computes the leading term of the shifted Jacobi–Trudi determinant
`det (∑_m X^m h_{ξ_i - ζ_j - m})` for strictly decreasing `ξ`, `ζ` with `ζ ≤ ξ`.  By
Cauchy–Binet over the integers in `[ζ_last, ξ_0]` it is
`∑_k det (h_{ξ_i - k_j}) · det (X^{k_i - ζ_j})`, the sum over decreasing integer tuples `k`.  The
second determinant is `X^{∑(k_i - ζ_i)}` when `ζ_i ≤ k_i` and `k_j < ζ_i` for `i < j` and `0`
otherwise (`det_powMatrix`), and the first vanishes unless `k_i ≤ ξ_i`
(`betaDetOf_eq_zero`).  So the shifted determinant has degree at most `c` in `X`, with
`c = ∑ (k_i - ζ_i)` for `k_0 = ξ_0` and `k_{i+1} = min (ξ_{i+1}, ζ_i - 1)`, and its coefficient
at `X^c` is `det (h_{ξ_{i+1} - k_{j+1}})` (`shifted_coeff`).  The argument uses no
Littlewood–Richardson expansion.

Sorry-free.
-/

namespace SkewJacobiNegative.Overlaps

open Polynomial
open scoped Matrix

section Vanishing

variable {R : Type*} [CommRing R]

/-- A square matrix with a zero block whose rows and columns together outnumber the size has
determinant zero. -/
theorem det_eq_zero_of_zero_block {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (P Q : Finset (Fin n))
    (hcard : n < P.card + Q.card) (h0 : ∀ i ∈ P, ∀ j ∈ Q, M i j = 0) : M.det = 0 := by
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have hex : ∃ j ∈ Q, σ j ∈ P := by
    by_contra hcon
    push Not at hcon
    have hmaps : ∀ j ∈ Q, σ j ∈ Pᶜ := fun j hj => Finset.mem_compl.mpr (hcon j hj)
    have := Finset.card_le_card_of_injOn σ hmaps σ.injective.injOn
    rw [Finset.card_compl, Fintype.card_fin] at this
    have hP := Finset.card_le_univ P
    rw [Fintype.card_fin] at hP
    omega
  obtain ⟨j, hj, hjP⟩ := hex
  have hprod : ∏ i, M (σ i) i = 0 :=
    Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ j) (h0 (σ j) hjP j hj)
  rw [hprod, smul_zero]

/-- The Jacobi–Trudi determinant `det (h_{a_i - b_j})` of two sequences. -/
def betaDetOf (h : ℤ → R) {ℓ : ℕ} (a b : Fin ℓ → ℤ) : R :=
  (Matrix.of fun i j : Fin ℓ => h (a i - b j)).det

/-- If some `a_i` is smaller than `b_i` for antitone `a`, `b`, the Jacobi–Trudi determinant of
`a` and `b` vanishes. -/
theorem betaDetOf_eq_zero (h : ℤ → R) (hneg : ∀ a, a < 0 → h a = 0) {ℓ : ℕ}
    {a b : Fin ℓ → ℤ} (ha : Antitone a) (hb : Antitone b) {i₀ : Fin ℓ} (hlt : a i₀ < b i₀) :
    betaDetOf h a b = 0 := by
  apply det_eq_zero_of_zero_block _ (Finset.Ici i₀) (Finset.Iic i₀)
  · rw [Fin.card_Ici, Fin.card_Iic]
    have := i₀.2
    omega
  · intro i hi j hj
    rw [Finset.mem_Ici] at hi
    rw [Finset.mem_Iic] at hj
    apply hneg
    have h1 := ha hi
    have h2 := hb hj
    omega

end Vanishing

section Interlacing

variable {R : Type*} [CommRing R] {ℓ : ℕ}

/-- The matrix `(X^{k_i - ζ_j})` with entry `0` where `k_i < ζ_j`. -/
noncomputable def powMatrix (k ζ : Fin ℓ → ℤ) : Matrix (Fin ℓ) (Fin ℓ) R[X] :=
  Matrix.of fun i j => if ζ j ≤ k i then X ^ (k i - ζ j).toNat else 0

/-- `k` interlaces `ζ`: `ζ_i ≤ k_i` for every `i`, and `k_j < ζ_i` for `i < j`. -/
def Interlaces (k ζ : Fin ℓ → ℤ) : Prop := (∀ i, ζ i ≤ k i) ∧ ∀ i j, i < j → k j < ζ i

/-- The unit upper bidiagonal matrix of the column operations that turn `powMatrix` into a matrix
with at most one nonzero entry in each row. -/
noncomputable def subDiag (ζ : Fin ℓ → ℤ) : Matrix (Fin ℓ) (Fin ℓ) R[X] :=
  Matrix.of fun c j =>
    if c = j then 1 else if c.val + 1 = j.val then -X ^ (ζ c - ζ j).toNat else 0

theorem det_subDiag (ζ : Fin ℓ → ℤ) : (subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [subDiag]
  · intro i j hij
    have h1 : i ≠ j := ne_of_gt hij
    have h2 : i.val + 1 ≠ j.val := by
      have : j.val < i.val := hij
      omega
    simp [subDiag, h1, h2]

/-- The entry of `powMatrix k ζ * subDiag ζ`: nonzero only where `ζ_j ≤ k_i < ζ_{j-1}`. -/
def PowCond (k ζ : Fin ℓ → ℤ) (i j : Fin ℓ) : Prop :=
  ζ j ≤ k i ∧ ∀ j' : Fin ℓ, j'.val + 1 = j.val → k i < ζ j'

open Classical in
theorem powMatrix_mul_subDiag {ζ : Fin ℓ → ℤ} (hζ : StrictAnti ζ) (k : Fin ℓ → ℤ) (i j : Fin ℓ) :
    (powMatrix k ζ * subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]) i j =
      if PowCond k ζ i j then X ^ (k i - ζ j).toNat else 0 := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hjj : (subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]) j j = 1 := by simp [subDiag]
  rw [hjj, mul_one]
  by_cases hj : j.val = 0
  · have hz : ∑ c ∈ Finset.univ.erase j,
        powMatrix k ζ i c * (subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]) c j = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      have hcj : c ≠ j := Finset.ne_of_mem_erase hc
      have : ¬ c.val + 1 = j.val := by omega
      simp [subDiag, hcj, this]
    rw [hz, add_zero]
    have hP : PowCond k ζ i j ↔ ζ j ≤ k i := by
      unfold PowCond
      refine ⟨fun h => h.1, fun h => ⟨h, fun j' hj' => by omega⟩⟩
    simp only [powMatrix, Matrix.of_apply, hP]
  · obtain ⟨j', hj'⟩ : ∃ j' : Fin ℓ, j'.val + 1 = j.val :=
      ⟨⟨j.val - 1, by have := j.2; omega⟩, by simp; omega⟩
    have hj'j : j' ≠ j := by intro h; rw [h] at hj'; omega
    have hlt : ζ j < ζ j' := hζ (show j' < j by rw [Fin.lt_def]; omega)
    have hz : ∑ c ∈ Finset.univ.erase j,
        powMatrix k ζ i c * (subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]) c j =
        powMatrix k ζ i j' * (subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]) j' j := by
      refine Finset.sum_eq_single_of_mem j' (Finset.mem_erase.mpr ⟨hj'j, Finset.mem_univ _⟩) ?_
      intro c hc hcj
      have hcj' : c ≠ j := Finset.ne_of_mem_erase hc
      have : ¬ c.val + 1 = j.val := by
        intro h
        apply hcj
        exact Fin.ext (by omega)
      simp [subDiag, hcj', this]
    rw [hz]
    have hsub : (subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]) j' j = -X ^ (ζ j' - ζ j).toNat := by
      simp [subDiag, hj'j, hj']
    rw [hsub]
    have hP : PowCond k ζ i j ↔ ζ j ≤ k i ∧ k i < ζ j' := by
      unfold PowCond
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2 j' hj'⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun j'' hj'' => ?_⟩
        have : j'' = j' := Fin.ext (by omega)
        rw [this]; exact h2
    simp only [powMatrix, Matrix.of_apply, hP]
    by_cases h1 : k i < ζ j
    · have h2 : ¬ ζ j ≤ k i := by omega
      have h3 : ¬ ζ j' ≤ k i := by omega
      simp [h2, h3]
    · by_cases h2 : k i < ζ j'
      · have h3 : ¬ ζ j' ≤ k i := by omega
        have h4 : ζ j ≤ k i := by omega
        simp [h3, h4, h2]
      · have h3 : ζ j' ≤ k i := by omega
        have h4 : ζ j ≤ k i := by omega
        simp only [h3, h4, h2, ite_true, and_false, ite_false, mul_neg]
        rw [← pow_add]
        have : (k i - ζ j').toNat + (ζ j' - ζ j).toNat = (k i - ζ j).toNat := by omega
        rw [this]
        simp

theorem eq_one_of_powCond {k ζ : Fin ℓ → ℤ} (hk : StrictAnti k) (hζ : StrictAnti ζ)
    (σ : Equiv.Perm (Fin ℓ))
    (hσ : ∀ j, PowCond k ζ (σ j) j) : σ = 1 := by
  have hsm : StrictMono σ := by
    intro a b hab
    have hb : 1 ≤ b.val := by have : a.val < b.val := hab; omega
    obtain ⟨b', hb'⟩ : ∃ b' : Fin ℓ, b'.val + 1 = b.val :=
      ⟨⟨b.val - 1, by have := b.2; omega⟩, by simp; omega⟩
    have h1 := (hσ b).2 b' hb'
    have h2 := (hσ a).1
    have h3 : ζ b' ≤ ζ a :=
      hζ.antitone (show a ≤ b' by rw [Fin.le_def]; have : a.val < b.val := hab; omega)
    by_contra hcon
    have : σ b ≤ σ a := not_lt.mp hcon
    have := hk.antitone this
    omega
  exact Equiv.ext fun i => congrFun hsm.eq_id i

open Classical in
/-- **The determinant of `(X^{k_i - ζ_j})`**: `X^{∑ (k_i - ζ_i)}` when `k` interlaces `ζ`, and `0`
otherwise. -/
theorem det_powMatrix {k ζ : Fin ℓ → ℤ} (hk : StrictAnti k) (hζ : StrictAnti ζ) :
    (powMatrix k ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]).det =
      if Interlaces k ζ then X ^ (∑ i, (k i - ζ i).toNat) else 0 := by
  classical
  have hdet : (powMatrix k ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]).det =
      (powMatrix k ζ * subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]).det := by
    rw [Matrix.det_mul, det_subDiag, mul_one]
  rw [hdet, Matrix.det_apply]
  have hterm : ∀ σ : Equiv.Perm (Fin ℓ), σ ≠ 1 →
      ∏ i, (powMatrix k ζ * subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]) (σ i) i = 0 := by
    intro σ hσ
    by_cases hall : ∀ j, PowCond k ζ (σ j) j
    · exact absurd (eq_one_of_powCond hk hζ σ hall) hσ
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      refine Finset.prod_eq_zero (f := fun i =>
        (powMatrix k ζ * subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]) (σ i) i) (Finset.mem_univ j) ?_
      rw [powMatrix_mul_subDiag hζ, ite_eq_right hj]
  by_cases hG : Interlaces k ζ
  · rw [ite_eq_left hG, Finset.sum_eq_single 1]
    · simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, id_eq]
      have : ∀ i, (powMatrix k ζ * subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]) i i =
          X ^ (k i - ζ i).toNat := by
        intro i
        rw [powMatrix_mul_subDiag hζ, ite_eq_left]
        refine ⟨hG.1 i, fun j' hj' => ?_⟩
        exact hG.2 j' i (by rw [Fin.lt_def]; omega)
      simp only [this]
      exact Finset.prod_pow_eq_pow_sum _ _ _
    · intro σ _ hσ
      rw [hterm σ hσ, smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right hG]
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_cases hσ : σ = 1
    · subst hσ
      by_cases hall : ∀ j, PowCond k ζ j j
      · exfalso
        apply hG
        refine ⟨fun i => (hall i).1, fun i j hij => ?_⟩
        obtain ⟨j', hj'⟩ : ∃ j' : Fin ℓ, j'.val + 1 = j.val :=
          ⟨⟨j.val - 1, by have := j.2; omega⟩, by have : i.val < j.val := hij; simp; omega⟩
        have h1 := (hall j).2 j' hj'
        have h2 : ζ j' ≤ ζ i :=
          hζ.antitone (show i ≤ j' by rw [Fin.le_def]; have : i.val < j.val := hij; omega)
        omega
      · push Not at hall
        obtain ⟨j, hj⟩ := hall
        have : ∏ i, (powMatrix k ζ * subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]) i i = 0 := by
          refine Finset.prod_eq_zero (f := fun i =>
            (powMatrix k ζ * subDiag ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]) i i) (Finset.mem_univ j) ?_
          rw [powMatrix_mul_subDiag hζ, ite_eq_right hj]
        simp [this]
    · rw [hterm σ hσ, smul_zero]

end Interlacing

section CauchyBinetExpansion

variable {R : Type*} [CommRing R] (h : ℤ → R)

/-- The shifted Jacobi–Trudi entry `∑_{m ≤ a} X^m h_{a-m}`. -/
noncomputable def shiftEntry (a : ℤ) : R[X] :=
  ∑ m ∈ Finset.range (a.toNat + 1), C (h (a - m)) * X ^ m

/-- The left Cauchy–Binet factor: `h_{ξ_i - k}` for the integer `k = hi - n`. -/
noncomputable def cbLeft {ℓ : ℕ} (ξ : Fin ℓ → ℤ) (hi : ℤ) (N : ℕ) :
    Matrix (Fin ℓ) (Fin N) R[X] :=
  Matrix.of fun i n => C (h (ξ i - (hi - (n : ℕ))))

/-- The right Cauchy–Binet factor: `X^{k - ζ_j}` for `ζ_j ≤ k = hi - n`, and `0` otherwise. -/
noncomputable def cbRight {ℓ : ℕ} (ζ : Fin ℓ → ℤ) (hi : ℤ) (N : ℕ) :
    Matrix (Fin N) (Fin ℓ) R[X] :=
  Matrix.of fun n j => if ζ j ≤ hi - (n : ℕ) then X ^ (hi - (n : ℕ) - ζ j).toNat else 0

theorem cbLeft_mul_cbRight (hneg : ∀ a, a < 0 → h a = 0) {ℓ : ℕ} (ξ ζ : Fin ℓ → ℤ) (hi lo : ℤ)
    (N : ℕ) (hN : N = (hi - lo + 1).toNat)
    (hξ : ∀ i, ξ i ≤ hi) (hζ : ∀ j, lo ≤ ζ j) (i j : Fin ℓ) :
    (cbLeft h ξ hi N * cbRight ζ hi N : Matrix (Fin ℓ) (Fin ℓ) R[X]) i j =
      shiftEntry h (ξ i - ζ j) := by
  rw [show (cbLeft h ξ hi N * cbRight ζ hi N : Matrix (Fin ℓ) (Fin ℓ) R[X]) i j =
    ∑ n, cbLeft h ξ hi N i n * cbRight ζ hi N n j from rfl]
  simp only [cbLeft, cbRight, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun n => C (h (ξ i - (hi - (n : ℤ)))) *
    (if ζ j ≤ hi - (n : ℤ) then (X : R[X]) ^ (hi - (n : ℤ) - ζ j).toNat else 0)) N]
  by_cases ha : ξ i - ζ j < 0
  · have hs : shiftEntry h (ξ i - ζ j) = 0 := by
      have : (ξ i - ζ j).toNat = 0 := by omega
      simp [shiftEntry, this, hneg _ ha]
    rw [hs]
    refine Finset.sum_eq_zero fun n _ => ?_
    change C (h (ξ i - (hi - (n : ℤ)))) *
      (if ζ j ≤ hi - (n : ℤ) then (X : R[X]) ^ (hi - (n : ℤ) - ζ j).toNat else 0) = 0
    by_cases hc : ζ j ≤ hi - (n : ℤ)
    · rw [hneg (ξ i - (hi - n)) (by omega)]
      simp
    · rw [ite_eq_right hc, mul_zero]
  · push Not at ha
    unfold shiftEntry
    symm
    refine Finset.sum_of_injOn (fun m => (hi - ζ j - m).toNat) ?_ ?_ ?_ ?_
    · intro m₁ hm₁ m₂ hm₂ e
      simp only [Finset.coe_range, Set.mem_Iio] at hm₁ hm₂
      simp only at e
      have := hξ i
      omega
    · intro m hm
      simp only [Finset.coe_range, Set.mem_Iio] at hm ⊢
      have := hζ j
      have := hξ i
      omega
    · intro n hn hnot
      simp only [Finset.mem_range] at hn
      by_cases hc : ζ j ≤ hi - (n : ℤ)
      · have : ξ i - (hi - (n : ℤ)) < 0 := by
          by_contra hcon
          apply hnot
          refine ⟨(hi - ζ j - n).toNat, ?_, ?_⟩
          · simp only [Finset.coe_range, Set.mem_Iio]
            omega
          · simp only
            omega
        rw [hneg _ this]
        simp
      · rw [ite_eq_right hc, mul_zero]
    · intro m hm
      simp only [Finset.mem_range] at hm
      have e1 : hi - ((hi - ζ j - m).toNat : ℤ) = ζ j + m := by
        have := hζ j
        have := hξ i
        omega
      have e2 : ((hi - ζ j - m).toNat : ℕ) = ((hi - ζ j - m).toNat : ℕ) := rfl
      simp only [e1]
      have e3 : ξ i - (ζ j + m) = ξ i - ζ j - m := by ring
      have e4 : ζ j ≤ ζ j + (m : ℤ) := by omega
      have e5 : (ζ j + (m : ℤ) - ζ j).toNat = m := by omega
      rw [ite_eq_left e4, e3, e5]

/-- The integers `hi - f i` of an increasing selection `f`. -/
def selValues {ℓ N : ℕ} (hi : ℤ) (f : Fin ℓ → Fin N) : Fin ℓ → ℤ := fun i => hi - ((f i : ℕ) : ℤ)

theorem selValues_strictAnti {ℓ N : ℕ} (hi : ℤ) {f : Fin ℓ → Fin N} (hf : StrictMono f) :
    StrictAnti (selValues hi f) := by
  intro a b hab
  have : (f a : ℕ) < f b := hf hab
  simp only [selValues]
  omega

/-- **Cauchy–Binet expansion of the shifted Jacobi–Trudi determinant**:
`det (∑_m X^m h_{ξ_i - ζ_j - m}) = ∑_f det (h_{ξ_i - k_j}) det (X^{k_i - ζ_j})`, over the
decreasing integer tuples `k = hi - f` in `[lo, hi]`. -/
theorem det_shiftEntry (hneg : ∀ a, a < 0 → h a = 0) {ℓ : ℕ} (ξ ζ : Fin ℓ → ℤ) (hi lo : ℤ)
    (N : ℕ) (hN : N = (hi - lo + 1).toNat) (hξ : ∀ i, ξ i ≤ hi) (hζ : ∀ j, lo ≤ ζ j) :
    (Matrix.of fun i j : Fin ℓ => shiftEntry h (ξ i - ζ j)).det =
      ∑ f ∈ Shields.increasingSelections ℓ N,
        C (betaDetOf h ξ (selValues hi f)) *
          (powMatrix (selValues hi f) ζ : Matrix (Fin ℓ) (Fin ℓ) R[X]).det := by
  have hM : (Matrix.of fun i j : Fin ℓ => shiftEntry h (ξ i - ζ j) : Matrix (Fin ℓ) (Fin ℓ) R[X]) =
      (cbLeft h ξ hi N * cbRight ζ hi N : Matrix (Fin ℓ) (Fin ℓ) R[X]) :=
    Matrix.ext fun i j => (cbLeft_mul_cbRight h hneg ξ ζ hi lo N hN hξ hζ i j).symm
  have hCB := Shields.det_mul_eq_sum_increasing (cbLeft h ξ hi N) (cbRight ζ hi N)
  rw [hM]
  refine hCB.trans (Finset.sum_congr rfl fun f _ => ?_)
  congr 1
  have : (cbLeft h ξ hi N).submatrix id f =
      (Polynomial.C : R →+* R[X]).mapMatrix
        (Matrix.of fun i j : Fin ℓ => h (ξ i - selValues hi f j)) := by
    ext i j
    simp [cbLeft, selValues]
  rw [this, ← RingHom.map_det]
  rfl

end CauchyBinetExpansion

section LeadingCoefficient

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The least subscripts `κ_j = min (ξ_{j+1}, ζ_j - 1)` of the diagram with the top cell of every
column removed. -/
def hatLower (ξ ζ : Fin (n + 1) → ℤ) : Fin n → ℤ :=
  fun j => min (ξ j.succ) (ζ j.castSucc - 1)

/-- The largest decreasing tuple `k` with `ζ_i ≤ k_i ≤ ξ_i` interlacing `ζ`:
`k₀ = ξ₀`, `k_{j+1} = κ_j`. -/
def maxSel (ξ ζ : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  Fin.cons (ξ 0) (hatLower ξ ζ)

/-- The degree `∑ (k_i - ζ_i)` of the top coefficient. -/
def shiftDegree (ξ ζ : Fin (n + 1) → ℤ) : ℕ := ∑ i, (maxSel ξ ζ i - ζ i).toNat

variable {ξ ζ : Fin (n + 1) → ℤ}

theorem maxSel_zero : maxSel ξ ζ 0 = ξ 0 := by simp [maxSel]

theorem maxSel_succ (j : Fin n) : maxSel ξ ζ j.succ = min (ξ j.succ) (ζ j.castSucc - 1) := by
  simp [maxSel, hatLower]

theorem hatLower_lt (hξ : StrictAnti ξ) (hζ : StrictAnti ζ) {i j : Fin n} (hij : i < j) :
    hatLower ξ ζ j < hatLower ξ ζ i := by
  have h1 : ξ j.succ < ξ i.succ := hξ (Fin.succ_lt_succ_iff.mpr hij)
  have h2 : ζ j.castSucc < ζ i.castSucc := hζ (Fin.castSucc_lt_castSucc_iff.mpr hij)
  unfold hatLower
  omega

theorem maxSel_strictAnti (hξ : StrictAnti ξ) (hζ : StrictAnti ζ) : StrictAnti (maxSel ξ ζ) := by
  intro a b hab
  induction b using Fin.cases with
  | zero => exact absurd hab (Fin.not_lt_zero _)
  | succ j =>
    induction a using Fin.cases with
    | zero =>
      rw [maxSel_zero, maxSel_succ]
      have : ξ j.succ < ξ 0 := hξ (Fin.succ_pos j)
      omega
    | succ i =>
      have hij : i < j := Fin.succ_lt_succ_iff.mp hab
      have := hatLower_lt hξ hζ hij
      simpa [maxSel] using this

theorem maxSel_le (hζ : StrictAnti ζ) (hle : ∀ i, ζ i ≤ ξ i) (i : Fin (n + 1)) :
    ζ i ≤ maxSel ξ ζ i ∧ maxSel ξ ζ i ≤ ξ i := by
  induction i using Fin.cases with
  | zero => rw [maxSel_zero]; exact ⟨hle 0, le_rfl⟩
  | succ j =>
    rw [maxSel_succ]
    have h1 : ζ j.succ < ζ j.castSucc := hζ (Fin.castSucc_lt_succ)
    have := hle j.succ
    refine ⟨?_, min_le_left _ _⟩
    omega

theorem betaDetOf_maxSel (h : ℤ → R) (hneg : ∀ a, a < 0 → h a = 0) (h0 : h 0 = 1)
    (hξ : StrictAnti ξ) :
    betaDetOf h ξ (maxSel ξ ζ) =
      betaDetOf h (fun i : Fin n => ξ i.succ) (hatLower ξ ζ) := by
  unfold betaDetOf
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · simp only [Matrix.of_apply, maxSel_zero, sub_self, h0, Fin.val_zero, pow_zero, one_mul,
      Fin.succAbove_zero]
    congr 1
  · intro i _ hi
    have : ξ i < ξ 0 := hξ (Fin.pos_iff_ne_zero.mpr hi)
    simp [maxSel_zero, hneg (ξ i - ξ 0) (by omega)]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The degree and leading coefficient of the shifted determinant.**  For strictly decreasing
`ξ`, `ζ` with `ζ ≤ ξ`, the determinant `det (∑_m X^m h_{ξ_i - ζ_j - m})` has degree at most
`shiftDegree ξ ζ`, and its coefficient there is `det (h_{ξ_{i+1} - κ_j})`. -/
theorem shifted_coeff (h : ℤ → R) (hneg : ∀ a, a < 0 → h a = 0) (h0 : h 0 = 1)
    (hξ : StrictAnti ξ) (hζ : StrictAnti ζ) (hle : ∀ i, ζ i ≤ ξ i) :
    (∀ m, shiftDegree ξ ζ < m →
      (Matrix.of fun i j : Fin (n + 1) => shiftEntry h (ξ i - ζ j)).det.coeff m = 0) ∧
    (Matrix.of fun i j : Fin (n + 1) => shiftEntry h (ξ i - ζ j)).det.coeff (shiftDegree ξ ζ) =
      betaDetOf h (fun i : Fin n => ξ i.succ) (hatLower ξ ζ) := by
  classical
  set hi := ξ 0 with hhi
  set lo := ζ (Fin.last n) with hlo
  set N := (hi - lo + 1).toNat with hN
  have hξhi : ∀ i, ξ i ≤ hi := fun i => hξ.antitone (Fin.zero_le i)
  have hζlo : ∀ j, lo ≤ ζ j := fun j => hζ.antitone (Fin.le_last j)
  rw [det_shiftEntry h hneg ξ ζ hi lo N hN hξhi hζlo]
  -- coefficient of one term
  have hterm : ∀ f ∈ Shields.increasingSelections (n + 1) N, ∀ m,
      (C (betaDetOf h ξ (selValues hi f)) *
        (powMatrix (selValues hi f) ζ : Matrix (Fin (n + 1)) (Fin (n + 1)) R[X]).det).coeff m =
      if Interlaces (selValues hi f) ζ ∧ m = ∑ i, ((selValues hi f) i - ζ i).toNat
        then betaDetOf h ξ (selValues hi f) else 0 := by
    intro f hf m
    have hk : StrictAnti (selValues hi f) :=
      selValues_strictAnti hi (Shields.mem_increasingSelections.mp hf)
    rw [det_powMatrix hk hζ]
    by_cases hI : Interlaces (selValues hi f) ζ
    · rw [ite_eq_left hI, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hm : m = ∑ i, ((selValues hi f) i - ζ i).toNat
      · simp [hI, hm]
      · simp [hI, hm]
    · rw [ite_eq_right hI]
      simp [hI]
  -- a term that can be nonzero lies below the maximal selection
  have hbelow : ∀ f ∈ Shields.increasingSelections (n + 1) N,
      Interlaces (selValues hi f) ζ → betaDetOf h ξ (selValues hi f) ≠ 0 →
      ∀ i, selValues hi f i ≤ maxSel ξ ζ i := by
    intro f hf hI hne i
    have hk : StrictAnti (selValues hi f) :=
      selValues_strictAnti hi (Shields.mem_increasingSelections.mp hf)
    have hkξ : ∀ i, selValues hi f i ≤ ξ i := by
      intro i
      by_contra hcon
      exact hne (betaDetOf_eq_zero h hneg hξ.antitone hk.antitone (i₀ := i) (not_le.mp hcon))
    induction i using Fin.cases with
    | zero => rw [maxSel_zero]; exact hkξ 0
    | succ j =>
      rw [maxSel_succ]
      refine le_min (hkξ _) ?_
      have := hI.2 j.castSucc j.succ (Fin.castSucc_lt_succ)
      omega
  have hdeg : ∀ f ∈ Shields.increasingSelections (n + 1) N,
      Interlaces (selValues hi f) ζ → betaDetOf h ξ (selValues hi f) ≠ 0 →
      ∑ i, ((selValues hi f) i - ζ i).toNat ≤ shiftDegree ξ ζ := by
    intro f hf hI hne
    refine Finset.sum_le_sum fun i _ => ?_
    exact Int.toNat_le_toNat (by have := hbelow f hf hI hne i; omega)
  have hdeg_eq : ∀ f ∈ Shields.increasingSelections (n + 1) N,
      Interlaces (selValues hi f) ζ → betaDetOf h ξ (selValues hi f) ≠ 0 →
      ∑ i, ((selValues hi f) i - ζ i).toNat = shiftDegree ξ ζ → selValues hi f = maxSel ξ ζ := by
    intro f hf hI hne heq
    have hle' : ∀ i ∈ Finset.univ, ((selValues hi f) i - ζ i).toNat ≤ (maxSel ξ ζ i - ζ i).toNat :=
      fun i _ => Int.toNat_le_toNat (by have := hbelow f hf hI hne i; omega)
    have := (Finset.sum_eq_sum_iff_of_le hle').mp heq
    funext i
    have h1 := this i (Finset.mem_univ i)
    have h2 := hI.1 i
    have h3 := hbelow f hf hI hne i
    omega
  refine ⟨fun m hm => ?_, ?_⟩
  · rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun f hf => ?_
    rw [hterm f hf m]
    by_cases hc : Interlaces (selValues hi f) ζ ∧ m = ∑ i, ((selValues hi f) i - ζ i).toNat
    · rw [ite_eq_left hc]
      by_contra hne
      have := hdeg f hf hc.1 hne
      omega
    · rw [ite_eq_right hc]
  · -- the maximal selection
    have hmaxle := maxSel_le hζ hle
    have hf0mem : ∀ i, (hi - maxSel ξ ζ i).toNat < N := by
      intro i
      have h1 := (hmaxle i).1
      have h2 := hζlo i
      have h3 := (hmaxle i).2
      have h4 := hξhi i
      omega
    let f₀ : Fin (n + 1) → Fin N := fun i => ⟨(hi - maxSel ξ ζ i).toNat, hf0mem i⟩
    have hsel : selValues hi f₀ = maxSel ξ ζ := by
      funext i
      have h3 := (hmaxle i).2
      have h4 := hξhi i
      simp only [selValues, f₀]
      omega
    have hmono : StrictMono f₀ := by
      intro a b hab
      have := maxSel_strictAnti hξ hζ hab
      change (hi - maxSel ξ ζ a).toNat < (hi - maxSel ξ ζ b).toNat
      have h3 := (hmaxle a).2
      have h4 := hξhi a
      omega
    have hf0 : f₀ ∈ Shields.increasingSelections (n + 1) N :=
      Shields.mem_increasingSelections.mpr hmono
    have hI0 : Interlaces (maxSel ξ ζ) ζ := by
      refine ⟨fun i => (hmaxle i).1, fun i j hij => ?_⟩
      induction j using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ j =>
        rw [maxSel_succ]
        have : ζ j.castSucc ≤ ζ i := hζ.antitone (by
          rw [Fin.le_def]; have := Fin.lt_def.mp hij; simp at this ⊢; omega)
        have := min_le_right (ξ j.succ) (ζ j.castSucc - 1)
        omega
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single f₀]
    · rw [hterm f₀ hf0, hsel, ite_eq_left ⟨hI0, rfl⟩, betaDetOf_maxSel h hneg h0 hξ]
    · intro f hf hne
      rw [hterm f hf]
      by_cases hc : Interlaces (selValues hi f) ζ ∧
          shiftDegree ξ ζ = ∑ i, ((selValues hi f) i - ζ i).toNat
      · rw [ite_eq_left hc]
        by_contra hne0
        apply hne
        have := hdeg_eq f hf hc.1 hne0 hc.2.symm
        funext i
        have h5 : ((f i : ℕ) : ℤ) = hi - maxSel ξ ζ i := by
          have := congrFun this i
          simp only [selValues] at this
          omega
        apply Fin.ext
        change (f i : ℕ) = (hi - maxSel ξ ζ i).toNat
        omega
      · rw [ite_eq_right hc]
    · intro h; exact absurd hf0 h

end LeadingCoefficient

end SkewJacobiNegative.Overlaps
