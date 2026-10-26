/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.EndpointLeaders
import SkewJacobiNegative.RepresentationBridges
import SkewJacobiNegative.Gluing.DualEvaluation
import SkewJacobiNegative.Base.TableauBridge
import SkewJacobiNegative.BetaBridge
import Vendor.AlgebraicCombinatorics.SymmetricFunctions.SchurBasics

/-!
# Actual finite-alphabet endpoint specialization

The rational complete-generator ring is specialized to independent alphabet
variables.  The determinant-to-tableau identification retains the full beta
lists and their genuine signed-index convention.
-/

namespace SkewJacobiNegative

open scoped BigOperators

/-- The three-row power determinant, with exponents in decreasing row order. -/
noncomputable def threePowerDet (r : Fin 3 → ℕ) : MvPolynomial (Fin 3) ℚ :=
  (Matrix.of fun i j : Fin 3 => MvPolynomial.X j ^ r i).det

/-- The alternant for the partition `(a + b, b, 0)`. -/
noncomputable def threeAlternant (a b : ℕ) : MvPolynomial (Fin 3) ℚ :=
  threePowerDet ![a + b + 2, b + 1, 0]

/-- The descending-exponent Vandermonde. -/
noncomputable def threeVandermonde : MvPolynomial (Fin 3) ℚ :=
  threePowerDet ![2, 1, 0]

/-- The signed cofactors of the first row of the three-variable Vandermonde. -/
noncomputable def threeVandermondeWeights : Fin 3 → MvPolynomial (Fin 3) ℚ :=
  ![MvPolynomial.X 1 - MvPolynomial.X 2,
    MvPolynomial.X 2 - MvPolynomial.X 0,
    MvPolynomial.X 0 - MvPolynomial.X 1]

/-- The one-row alternant identity gives the complete function without division. -/
theorem hsymm_three_mul_vandermonde (k : ℕ) :
    MvPolynomial.hsymm (Fin 3) ℚ k * threeVandermonde =
      threePowerDet ![k + 2, 1, 0] := by
  classical
  let P : NPartition 3 :=
    ⟨![k, 0, 0], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  have hp : schurPoly P = MvPolynomial.hsymm (Fin 3) ℤ k :=
    schurPoly_row_eq_h (N := 3) k P ⟨rfl, by
      intro i hi
      fin_cases i <;> simp_all [P]⟩
  have hh := alternant_eq_rho_mul_schur P
  have harg : (fun i => P.parts i + rhoVector 3 i) = ![k + 2, 1, 0] := by
    ext i
    fin_cases i <;> simp [P, rhoVector, AlgebraicCombinatorics.rho]
  have hrho : rhoVector 3 = ![2, 1, 0] := by
    ext i
    fin_cases i <;> simp [rhoVector, AlgebraicCombinatorics.rho]
  rw [hp, harg, hrho] at hh
  simp only [AlgebraicCombinatorics.alternant_eq_det,
    AlgebraicCombinatorics.alternantMatrix] at hh
  let f : MvPolynomial (Fin 3) ℤ →+* MvPolynomial (Fin 3) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hm (r : Fin 3 → ℕ) :
      f ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X j : MvPolynomial (Fin 3) ℤ)
        ^ r i).det) = threePowerDet r := by
    rw [f.map_det]
    apply congrArg Matrix.det
    ext i j
    simp [f, threePowerDet]
  have he := congrArg f hh
  rw [map_mul, hm, hm] at he
  have hf : f (MvPolynomial.hsymm (Fin 3) ℤ k) =
      MvPolynomial.hsymm (Fin 3) ℚ k :=
    MvPolynomial.map_hsymm (σ := Fin 3) (R := ℤ) (S := ℚ) k (Int.castRingHom ℚ)
  rw [hf] at he
  simpa only [threeVandermonde, mul_comm] using he.symm

/-- The divided-difference expression is an identity after multiplying by the Vandermonde. -/
theorem hsymm_three_vandermonde_sum (k : ℕ) :
    MvPolynomial.hsymm (Fin 3) ℚ k * threeVandermonde =
      ∑ a : Fin 3, MvPolynomial.X a ^ (k + 2) * threeVandermondeWeights a := by
  rw [hsymm_three_mul_vandermonde]
  simp [threePowerDet, Matrix.det_fin_three, Fin.sum_univ_succ,
    threeVandermondeWeights]
  ring

/-- The product of the three signed cofactors is the negative Vandermonde. -/
theorem prod_threeVandermondeWeights :
    (∏ a : Fin 3, threeVandermondeWeights a) = -threeVandermonde := by
  simp [threeVandermondeWeights, threeVandermonde, threePowerDet,
    Matrix.det_fin_three, Fin.prod_univ_succ]
  ring

/-- The independent-variable Vandermonde is nonzero. -/
theorem threeVandermonde_ne_zero : threeVandermonde ≠ 0 := by
  intro hz
  have h := congrArg (MvPolynomial.eval (fun i : Fin 3 => (![2, 1, 0] i : ℚ))) hz
  norm_num [threeVandermonde, threePowerDet, Matrix.det_fin_three] at h

/-- A common exponent shift factors the full alphabet product from an alternant. -/
theorem threePowerDet_shift (r : Fin 3 → ℕ) (e : ℕ) :
    threePowerDet (fun i => r i + e) =
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) ^ e *
        threePowerDet r := by
  unfold threePowerDet
  have hm : (Matrix.of fun i j : Fin 3 =>
      (MvPolynomial.X j : MvPolynomial (Fin 3) ℚ) ^ (r i + e)) =
      Matrix.of (fun i j => MvPolynomial.X j ^ e * MvPolynomial.X j ^ r i) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.of_apply, pow_add]
    ring
  rw [hm]
  change (Matrix.of (fun i j : Fin 3 => MvPolynomial.X j ^ e *
    (Matrix.of (fun i j : Fin 3 =>
      (MvPolynomial.X j : MvPolynomial (Fin 3) ℚ) ^ r i)) i j)).det = _
  rw [Matrix.det_mul_row]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  rw [← mul_pow, ← mul_pow]
  simp only [Fin.succ_zero_eq_one', Fin.succ_one_eq_two', mul_assoc]

/-- Factor the positive-index three-row complete matrix through the power matrices.
No rational-function denominator is introduced. -/
theorem hsymm_three_determinant_factorization (A B : Fin 3 → ℕ)
    (hB : ∀ j, B j ≤ B 0) (hA : ∀ i, B 0 ≤ A i) :
    (Matrix.of fun i j : Fin 3 => MvPolynomial.hsymm (Fin 3) ℚ (A i - B j)).det *
        threeVandermonde ^ 2 =
      threePowerDet (fun i => A i - B 0 + 2) *
        threePowerDet (fun i => B 0 - B i.rev) := by
  classical
  let H := Matrix.of fun i j : Fin 3 =>
    MvPolynomial.hsymm (Fin 3) ℚ (A i - B j)
  let U := Matrix.of fun i a : Fin 3 =>
    (MvPolynomial.X a : MvPolynomial (Fin 3) ℚ) ^ (A i - B 0 + 2)
  let T := Matrix.of fun a j : Fin 3 =>
    (MvPolynomial.X a : MvPolynomial (Fin 3) ℚ) ^ (B 0 - B j)
  let W := Matrix.of fun a j : Fin 3 => threeVandermondeWeights a * T a j
  have hm : threeVandermonde • H = U * W := by
    apply Matrix.ext
    intro i j
    change threeVandermonde * MvPolynomial.hsymm (Fin 3) ℚ (A i - B j) =
      ∑ a : Fin 3, U i a * W a j
    rw [mul_comm, hsymm_three_vandermonde_sum]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [U, W, T]
    have he : A i - B 0 + 2 + (B 0 - B j) = A i - B j + 2 := by
      have := hA i
      have := hB j
      omega
    rw [← he, pow_add]
    ring
  have hW : W.det = -threeVandermonde * T.det := by
    rw [show W = Matrix.of (fun a j => threeVandermondeWeights a * T a j) from rfl,
      Matrix.det_mul_column, prod_threeVandermondeWeights]
  have hT : T.det = -threePowerDet (fun i => B 0 - B i.rev) := by
    simp only [T, threePowerDet, Matrix.det_fin_three, Matrix.of_apply]
    simp only [Fin.rev]
    norm_num
    ring
  have hd : threeVandermonde *
      (H.det * threeVandermonde ^ 2) =
      threeVandermonde *
        (threePowerDet (fun i => A i - B 0 + 2) *
          threePowerDet (fun i => B 0 - B i.rev)) := by
    calc
      threeVandermonde * (H.det * threeVandermonde ^ 2) =
          (threeVandermonde • H).det := by
            rw [Matrix.det_smul]
            simp only [Fintype.card_fin]
            ring
      _ = U.det * W.det := by rw [hm, Matrix.det_mul]
      _ = _ := by rw [hW, hT]; change _ = _; dsimp [U, threePowerDet]; ring
  exact mul_left_cancel₀ threeVandermonde_ne_zero hd

/-- Specialization of the rational complete generators to a finite alphabet. -/
noncomputable def finiteSpecialization (b : ℕ) :
    CompleteRing →ₐ[ℚ] MvPolynomial (Fin b) ℚ :=
  Gluing.evalComplete b (Gluing.varAlphabet b)

/-- The three-variable specialization used in `lem:three-variable-endpoint`. -/
noncomputable abbrev threeVariableSpecialization := finiteSpecialization 3

@[simp]
theorem finiteSpecialization_complete_nat (b k : ℕ) :
    finiteSpecialization b (complete (k : ℤ)) =
      MvPolynomial.hsymm (Fin b) ℚ k := by
  rw [complete_eq_hh]
  change Gluing.evalComplete b (Gluing.varAlphabet b) (Gluing.hh (k : ℤ)) = _
  rw [Gluing.evalComplete_hh, if_neg (by omega)]
  simpa using Gluing.completeHom_varAlphabet b k

@[simp]
theorem finiteSpecialization_complete_neg (b : ℕ) {k : ℤ} (hk : k < 0) :
    finiteSpecialization b (complete k) = 0 := by
  rw [complete_of_neg hk, map_zero]

/-- Rational scalar extension commutes with the actual tableau specialization. -/
theorem evalComplete_integerLift {R : Type*} [CommRing R] [Algebra ℚ R]
    (b : ℕ) (β : ℕ → R) (p : Base.CompleteRing) :
    Gluing.evalComplete b β (integerLift p) = Base.tableauSpecialization b β p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simp [integerLift, Gluing.evalComplete, Base.tableauSpecialization, Base.specialize]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
      simp only [map_mul, hp]
      congr 1
      simp [integerLift, Gluing.evalComplete, Base.tableauSpecialization, Base.specialize]

/-- The actual three-variable Jacobi--Trudi Schur polynomial for `(a + b, b, 0)`. -/
noncomputable def threeSchur (a b : ℕ) : MvPolynomial (Fin 3) ℚ :=
  threeVariableSpecialization
    (complete ((a + b : ℕ) : ℤ) * complete (b : ℤ) -
      complete ((a + b + 1 : ℕ) : ℤ) * complete ((b : ℤ) - 1))

/-- The two-by-two formula retains exactly the three-row partition determinant. -/
theorem threeSchur_eq_jacobiTrudi (a b : ℕ) :
    threeSchur a b = threeVariableSpecialization
      (Matrix.of (fun i j : Fin 3 =>
        complete ((![a + b, b, 0] i : ℕ) - (i.val : ℤ) + (j.val : ℤ)))).det := by
  have hm : Matrix.of (fun i j : Fin 3 =>
      complete ((![a + b, b, 0] i : ℕ) - (i.val : ℤ) + (j.val : ℤ))) =
      !![complete ((a + b : ℕ) : ℤ), complete ((a + b + 1 : ℕ) : ℤ),
          complete ((a + b + 2 : ℕ) : ℤ);
        complete ((b : ℤ) - 1), complete (b : ℤ), complete ((b + 1 : ℕ) : ℤ);
        0, 0, 1] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.of_apply, complete_of_neg, complete_zero]
    all_goals congr 1 <;> omega
  rw [hm, Matrix.det_fin_three]
  simp [threeSchur]

/-- A three-row Plücker identity for the power determinants. -/
theorem threePowerDet_plucker (p q : ℕ) :
    threePowerDet ![p, 1, 0] * threePowerDet ![q + 1, 1, 0] -
      threePowerDet ![p + 1, 1, 0] * threePowerDet ![q, 1, 0] =
      threeVandermonde * threePowerDet ![p, q, 0] := by
  simp [threePowerDet, threeVandermonde, Matrix.det_fin_three, pow_succ]
  ring

/-- The actual Schur specialization and its alternant are related without division. -/
theorem threeSchur_mul_vandermonde (a b : ℕ) :
    threeSchur a b * threeVandermonde = threeAlternant a b := by
  cases b with
  | zero =>
    have hs : threeSchur a 0 = MvPolynomial.hsymm (Fin 3) ℚ a := by
      simp [threeSchur, complete_of_neg, finiteSpecialization_complete_nat]
    rw [hs, hsymm_three_mul_vandermonde]
    rfl
  | succ b =>
    have hs : threeSchur a (b + 1) =
        MvPolynomial.hsymm (Fin 3) ℚ (a + b + 1) *
          MvPolynomial.hsymm (Fin 3) ℚ (b + 1) -
        MvPolynomial.hsymm (Fin 3) ℚ (a + b + 2) *
          MvPolynomial.hsymm (Fin 3) ℚ b := by
      unfold threeSchur
      rw [show ((b + 1 : ℕ) : ℤ) - 1 = (b : ℤ) by omega,
        map_sub, map_mul, map_mul, finiteSpecialization_complete_nat,
        finiteSpecialization_complete_nat, finiteSpecialization_complete_nat,
        finiteSpecialization_complete_nat]
      congr 2 <;> omega
    have he : (threeSchur a (b + 1) * threeVandermonde) * threeVandermonde =
        threeAlternant a (b + 1) * threeVandermonde := by
      calc
        (threeSchur a (b + 1) * threeVandermonde) * threeVandermonde =
            (MvPolynomial.hsymm (Fin 3) ℚ (a + b + 1) * threeVandermonde) *
              (MvPolynomial.hsymm (Fin 3) ℚ (b + 1) * threeVandermonde) -
            (MvPolynomial.hsymm (Fin 3) ℚ (a + b + 2) * threeVandermonde) *
              (MvPolynomial.hsymm (Fin 3) ℚ b * threeVandermonde) := by rw [hs]; ring
        _ = threePowerDet ![a + b + 3, 1, 0] * threePowerDet ![b + 3, 1, 0] -
            threePowerDet ![a + b + 4, 1, 0] * threePowerDet ![b + 2, 1, 0] := by
              simp only [hsymm_three_mul_vandermonde]
        _ = threeAlternant a (b + 1) * threeVandermonde := by
          have hp := threePowerDet_plucker (a + b + 3) (b + 2)
          simpa only [threeAlternant, show a + (b + 1) + 2 = a + b + 3 by omega,
            show b + 1 + 1 = b + 2 by omega, show b + 2 + 1 = b + 3 by omega,
            show a + b + 3 + 1 = a + b + 4 by omega, mul_comm] using hp
    exact mul_right_cancel₀ threeVandermonde_ne_zero he

namespace BetaDiagram

variable {n : ℕ}

/-- The specialization is the bounded-tableau Schur function of the actual beta shape. -/
theorem evalComplete_schur {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : BetaDiagram n) (hn : 0 < n) (b : ℕ) (β : ℕ → R) :
    Gluing.evalComplete b β D.schur =
      Shields.skewSchur (D.toDiagram hn).outerShape (D.toDiagram hn).innerShape b β := by
  rw [← D.toDiagram_schur hn, evalComplete_integerLift,
    Base.Diagram.tableauSpecialization_schurFunction]

/-- Independent-variable specialization is the actual tableau polynomial, not a certificate. -/
theorem finiteSpecialization_schur (D : BetaDiagram n) (hn : 0 < n) (b : ℕ) :
    finiteSpecialization b D.schur =
      Shields.skewSchur (D.toDiagram hn).outerShape (D.toDiagram hn).innerShape b
        (Gluing.varAlphabet b) :=
  D.evalComplete_schur hn b (Gluing.varAlphabet b)

/-- A finite beta shape has at most the stated number of rows in every column. -/
theorem toDiagram_skewColLen_le (D : BetaDiagram n) (hn : 0 < n) (j : ℕ) :
    Shields.skewColLen (D.toDiagram hn).outerShape (D.toDiagram hn).innerShape j ≤ n := by
  have hc : (D.toDiagram hn).outerShape.colLen j ≤ n := by
    by_contra h
    have hm : (n, j) ∈ (D.toDiagram hn).outerShape :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hr := YoungDiagram.mem_iff_lt_rowLen.mp hm
    have hz := Base.boundaryShape_rowLen_outside (D.toDiagram hn).outer
      (D.toDiagram hn).outer_antitone n le_rfl
    change j < (Base.boundaryShape (D.toDiagram hn).outer
      (D.toDiagram hn).outer_antitone).rowLen n at hr
    rw [hz] at hr
    omega
  unfold Shields.skewColLen
  omega

/-- Specialization in at least the row count cannot kill an actual Schur determinant. -/
theorem finiteSpecialization_schur_ne_zero (D : BetaDiagram n) (hn : 0 < n)
    (b : ℕ) (hb : n ≤ b) : finiteSpecialization b D.schur ≠ 0 := by
  classical
  rw [D.finiteSpecialization_schur hn b]
  let ev : MvPolynomial (Fin b) ℚ →ₐ[ℚ] ℝ := MvPolynomial.aeval (fun _ => (1 : ℝ))
  have he : ev (Shields.skewSchur (D.toDiagram hn).outerShape
      (D.toDiagram hn).innerShape b (Gluing.varAlphabet b)) =
      Shields.skewSchur (D.toDiagram hn).outerShape
        (D.toDiagram hn).innerShape b (fun _ => (1 : ℝ)) := by
    unfold Shields.skewSchur
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro c hc
    have hT : T c.1 c.2 < b := T.2 c.1 c.2 hc
    simp [ev, Gluing.varAlphabet, hT]
  have hp : 0 < Shields.skewSchur (D.toDiagram hn).outerShape
      (D.toDiagram hn).innerShape b (fun _ => (1 : ℝ)) :=
    Shields.skewSchur_pos (fun _ _ => zero_lt_one)
      (fun j => (D.toDiagram_skewColLen_le hn j).trans hb)
  intro hz
  have := congrArg ev hz
  rw [he, map_zero] at this
  exact (ne_of_gt hp) this

/-- In a dense board the first inner-boundary column is present in every skew row. -/
theorem dense_common_column (D : BetaDiagram n) (hn : 0 < n) (hD : D.Dense)
    (i : Fin n) :
    (i.val, (D.toDiagram hn).inner ⟨0, hn⟩) ∈
      Shields.skewCells (D.toDiagram hn).outerShape (D.toDiagram hn).innerShape := by
  apply Shields.mem_skewCells.mpr
  constructor
  · apply YoungDiagram.mem_iff_lt_rowLen.mpr
    rw [Base.Diagram.outerShape_rowLen]
    have h := hD i ⟨0, hn⟩
    have h0 := D.translated_col_nonneg hn ⟨0, hn⟩
    have hz : (((⟨0, hn⟩ : Fin n).val : ℕ) : ℤ) = 0 := rfl
    rw [hz, add_zero] at h0
    change (D.col ⟨0, hn⟩ - D.bottomCol hn +
      (((⟨0, hn⟩ : Fin n).val : ℕ) : ℤ)).toNat <
        (D.row i - D.bottomCol hn + i.val).toNat
    rw [hz, add_zero]
    omega
  · intro hm
    have h := YoungDiagram.mem_iff_lt_rowLen.mp hm
    rw [Base.Diagram.innerShape_rowLen] at h
    have hi := (D.toDiagram hn).inner_antitone
      (show (⟨0, hn⟩ : Fin n) ≤ i from Nat.zero_le i.val)
    omega

/-- A dense board vanishes on every alphabet smaller than its row count.
This is the tableau form of the manuscript's rank bound. -/
theorem finiteSpecialization_schur_eq_zero_dense (D : BetaDiagram n)
    (hn : 0 < n) (hD : D.Dense) (b : ℕ) (hb : b < n) :
    finiteSpecialization b D.schur = 0 := by
  classical
  rw [D.finiteSpecialization_schur hn b]
  let j := (D.toDiagram hn).inner ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have h0 := D.dense_common_column hn hD ⟨0, hn⟩
  have hl := D.dense_common_column hn hD last
  letI : IsEmpty (Shields.BoundedSkewSSYT (D.toDiagram hn).outerShape
      (D.toDiagram hn).innerShape b) := ⟨fun T => by
    have hgap := T.1.entry_add_sub_le 0 j (Shields.mem_skewCells.mp h0).2
      last.val (by omega) (Shields.mem_skewCells.mp hl).1
    have hbound := T.2 last.val j hl
    dsimp [last] at hgap hbound
    omega⟩
  simp [Shields.skewSchur]

/-- Dense three-row cofactors remain nonzero in the true three-variable alphabet. -/
theorem threeVariable_schur_ne_zero (D : BetaDiagram 3) :
    threeVariableSpecialization D.schur ≠ 0 :=
  D.finiteSpecialization_schur_ne_zero (by omega) 3 le_rfl

/-- The successive row-beta gaps minus one give the first two-part partition. -/
def threeUpperA (D : BetaDiagram 3) : ℕ := (D.row 0 - D.row 1 - 1).toNat

def threeUpperB (D : BetaDiagram 3) : ℕ := (D.row 1 - D.row 2 - 1).toNat

/-- The reversed column-beta gaps minus one give the second two-part partition. -/
def threeLowerA (D : BetaDiagram 3) : ℕ := (D.col 1 - D.col 2 - 1).toNat

def threeLowerB (D : BetaDiagram 3) : ℕ := (D.col 0 - D.col 1 - 1).toNat

/-- The common full-column power in the dense three-row factorization. -/
def threeCommonPower (D : BetaDiagram 3) : ℕ := (D.row 2 - D.col 0 + 2).toNat

/-- Dense three-row factorization in a division-free alternant presentation. -/
theorem dense_three_alternant_factorization (D : BetaDiagram 3) (hD : D.Dense) :
    threeVariableSpecialization D.schur * threeVandermonde ^ 2 =
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) ^
          D.threeCommonPower *
        threeAlternant D.threeUpperA D.threeUpperB *
        threeAlternant D.threeLowerA D.threeLowerB := by
  classical
  let A : Fin 3 → ℕ := fun i => (D.row i - D.col 2).toNat
  let B : Fin 3 → ℕ := fun j => (D.col j - D.col 2).toNat
  have hc (j : Fin 3) : D.col 2 ≤ D.col j :=
    D.col_strictAnti.antitone (Fin.le_last j)
  have h0 (j : Fin 3) : D.col j ≤ D.col 0 :=
    D.col_strictAnti.antitone (Fin.zero_le j)
  have hB (j : Fin 3) : B j ≤ B 0 := by
    dsimp [B]
    have := hc j
    have := hc 0
    have := h0 j
    omega
  have hA (i : Fin 3) : B 0 ≤ A i := by
    dsimp [A, B]
    have := hc 0
    have := hD i 0
    omega
  have hmatrix :
      (threeVariableSpecialization : CompleteRing →ₐ[ℚ] _).mapMatrix D.matrix =
        Matrix.of (fun i j : Fin 3 => MvPolynomial.hsymm (Fin 3) ℚ (A i - B j)) := by
    apply Matrix.ext
    intro i j
    change threeVariableSpecialization (complete (D.row i - D.col j)) = _
    have he : (((A i - B j : ℕ) : ℤ)) = D.row i - D.col j := by
      dsimp [A, B]
      have := hc j
      have := hD i j
      omega
    rw [← he, finiteSpecialization_complete_nat]
    rfl
  have hs : threeVariableSpecialization D.schur =
      (Matrix.of fun i j : Fin 3 =>
        MvPolynomial.hsymm (Fin 3) ℚ (A i - B j)).det := by
    rw [schur, AlgHom.map_det, hmatrix]
  rw [hs, hsymm_three_determinant_factorization A B hB hA]
  have hr01 := D.row_strictAnti (show (0 : Fin 3) < 1 by decide)
  have hr12 := D.row_strictAnti (show (1 : Fin 3) < 2 by decide)
  have hc01 := D.col_strictAnti (show (0 : Fin 3) < 1 by decide)
  have hc12 := D.col_strictAnti (show (1 : Fin 3) < 2 by decide)
  have hd := hD 2 0
  have hU : (fun i => A i - B 0 + 2) =
      fun i => (![D.threeUpperA + D.threeUpperB + 2, D.threeUpperB + 1, 0] i) +
        D.threeCommonPower := by
    ext i
    fin_cases i <;>
      norm_num [A, B, threeUpperA, threeUpperB, threeCommonPower]
    all_goals
      have := hc 0
      have := hD 0 0
      have := hD 1 0
      omega
  have hL : (fun i => B 0 - B i.rev) =
      ![D.threeLowerA + D.threeLowerB + 2, D.threeLowerB + 1, 0] := by
    ext i
    fin_cases i <;>
      norm_num [B, threeLowerA, threeLowerB, Fin.rev]
    all_goals
      have := hc 0
      have := hc 1
      omega
  rw [hU, hL, threePowerDet_shift]
  rfl

/-- Equality of the two partition parameters is precisely beta reflection. -/
theorem symmetric_of_three_parameters_eq (D : BetaDiagram 3)
    (ha : D.threeUpperA = D.threeLowerA)
    (hb : D.threeUpperB = D.threeLowerB) : D.Symmetric := by
  have hr01 := D.row_strictAnti (show (0 : Fin 3) < 1 by decide)
  have hr12 := D.row_strictAnti (show (1 : Fin 3) < 2 by decide)
  have hc01 := D.col_strictAnti (show (0 : Fin 3) < 1 by decide)
  have hc12 := D.col_strictAnti (show (1 : Fin 3) < 2 by decide)
  change (D.row 0 - D.row 1 - 1).toNat = (D.col 1 - D.col 2 - 1).toNat at ha
  change (D.row 1 - D.row 2 - 1).toNat = (D.col 0 - D.col 1 - 1).toNat at hb
  refine ⟨D.row 0 + D.col 2, ?_, ?_⟩ <;> intro i <;>
    fin_cases i <;> simp only [Fin.rev] <;> norm_num <;> omega

/-- Positive endpoint extension retains positivity of every actual matrix index. -/
theorem extendTop_dense (D : BetaDiagram (n + 1)) (hD : D.Dense)
    (t : ℤ) (ht : 0 < t) : (D.extendTop t ht).Dense := by
  intro i j
  have h := hD i j
  change D.col j < if i = 0 then D.row i + t else D.row i
  split_ifs <;> omega

theorem extendBottom_dense (D : BetaDiagram (n + 1)) (hD : D.Dense)
    (t : ℤ) (ht : 0 < t) : (D.extendBottom t ht).Dense := by
  intro i j
  have h := hD i j
  change (if j = Fin.last n then D.col j - t else D.col j) < D.row i
  split_ifs <;> omega

/-- The row partition acquires the top shift; every other factor stays fixed. -/
theorem dense_three_top_factorization (D : BetaDiagram 3) (hD : D.Dense)
    (t : ℤ) (ht : 0 < t) :
    threeVariableSpecialization (D.extendTop t ht).schur * threeVandermonde ^ 2 =
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) ^
          D.threeCommonPower *
        threeAlternant (D.threeUpperA + t.toNat) D.threeUpperB *
        threeAlternant D.threeLowerA D.threeLowerB := by
  have h := (D.extendTop t ht).dense_three_alternant_factorization
    (D.extendTop_dense hD t ht)
  have hr := D.row_strictAnti (show (0 : Fin 3) < 1 by decide)
  simpa [threeUpperA, threeUpperB, threeLowerA, threeLowerB, threeCommonPower,
    extendTop, show (D.row 0 + t - D.row 1 - 1).toNat =
      (D.row 0 - D.row 1 - 1).toNat + t.toNat by omega] using h

/-- The reversed column partition acquires the bottom shift with the same common power. -/
theorem dense_three_bottom_factorization (D : BetaDiagram 3) (hD : D.Dense)
    (t : ℤ) (ht : 0 < t) :
    threeVariableSpecialization (D.extendBottom t ht).schur * threeVandermonde ^ 2 =
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) ^
          D.threeCommonPower *
        threeAlternant D.threeUpperA D.threeUpperB *
        threeAlternant (D.threeLowerA + t.toNat) D.threeLowerB := by
  have h := (D.extendBottom t ht).dense_three_alternant_factorization
    (D.extendBottom_dense hD t ht)
  have hc := D.col_strictAnti (show (1 : Fin 3) < 2 by decide)
  simpa [threeUpperA, threeUpperB, threeLowerA, threeLowerB, threeCommonPower,
    extendBottom, show (D.col 1 - (D.col 2 - t) - 1).toNat =
      (D.col 1 - D.col 2 - 1).toNat + t.toNat by omega] using h

/-- `eq:three-variable-factorization`, on the actual beta determinant and actual Schur factors. -/
theorem dense_three_schur_factorization (D : BetaDiagram 3) (hD : D.Dense) :
    threeVariableSpecialization D.schur =
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) ^
          D.threeCommonPower *
        threeSchur D.threeUpperA D.threeUpperB *
        threeSchur D.threeLowerA D.threeLowerB := by
  apply mul_right_cancel₀ (pow_ne_zero 2 threeVandermonde_ne_zero)
  calc
    threeVariableSpecialization D.schur * threeVandermonde ^ 2 =
        (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) ^
            D.threeCommonPower *
          threeAlternant D.threeUpperA D.threeUpperB *
          threeAlternant D.threeLowerA D.threeLowerB :=
      D.dense_three_alternant_factorization hD
    _ = _ := by
      rw [← threeSchur_mul_vandermonde, ← threeSchur_mul_vandermonde]
      ring

end BetaDiagram
end SkewJacobiNegative
