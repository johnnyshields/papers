/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.WeakBoardMonomials
import SkewJacobiNegative.GeneralHessenberg

/-!
# Recognition of full Hessenberg boards from the maximal cofactor

Formalizes `lem:hessenberg-membership` and `eq:hessenberg-membership` in
`shields-2026-skew-class-inflation.tex`.  The maximal cofactor retains every
zero-gap unit.  No Hessenberg condition is assumed of an unknown mate.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- The full board is upper Hessenberg before any beta cancellation. -/
def IsHessenberg {n : ℕ} (D : BetaDiagram n) : Prop :=
  ∀ i j, j.val + 1 < i.val → D.row i - D.col j < 0

/-- Monomiality of the actual unsigned maximal cofactor recognizes the full board. -/
theorem cofactor_monomial_iff_hessenberg {n : ℕ} (D : BetaDiagram (n + 1))
    (hD : D.Connected) : IsMonomial D.cornerPolynomial ↔ IsHessenberg D := by
  have hh := weak_board_monomial_iff n (fun i => D.row i.succ)
    (fun j => D.col j.castSucc)
    (D.row_strictAnti.comp_strictMono Fin.strictMono_succ)
    (D.col_strictAnti.comp_strictMono Fin.strictMono_castSucc)
    (fun i => hD.2 i.castSucc (by simp only [Fin.val_castSucc]; omega))
  change IsMonomial D.cornerPolynomial ↔ _ at hh
  rw [hh]
  constructor
  · intro h i j hij
    have hj : j.val < n := by have := i.isLt; omega
    let k : Fin n := ⟨j.val, hj⟩
    have hk : k.val + 1 < n := by dsimp [k]; have := i.isLt; omega
    have hl := h k hk
    have he : k.castSucc = j := Fin.ext rfl
    rw [he] at hl
    have hle : (⟨k.val + 1, hk⟩ : Fin n).succ ≤ i := by
      change k.val + 1 + 1 ≤ i.val
      dsimp [k]
      omega
    have hr := D.row_strictAnti.antitone hle
    omega
  · intro h i hi
    have hh := h (⟨i.val + 1, hi⟩ : Fin n).succ i.castSucc
      (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
    omega

/-- The arithmetic internal-row inequalities are exactly the same recognition condition. -/
theorem profile_cofactor_monomial_iff_thick {n : ℕ} (P : Profile n) :
    IsMonomial P.toBetaDiagram.cornerPolynomial ↔ Staircase.Thick P := by
  rw [cofactor_monomial_iff_hessenberg _ P.toBetaDiagram_connected]
  constructor
  · intro h
    exact GeneralHessenberg.hessenberg_thick P h
  · intro h
    exact h.hessenberg

/-- Recognition is transported through full polynomial equality, not imposed on the mate. -/
theorem hessenberg_of_equal_schur {n : ℕ} (D E : BetaDiagram (n + 1))
    (hD : D.Connected) (hE : E.Connected) (he : D.schur = E.schur)
    (hh : IsHessenberg D) : IsHessenberg E := by
  apply (cofactor_monomial_iff_hessenberg E hE).mp
  rw [← D.cornerPolynomial_eq_of_schur_eq E hD hE he]
  exact (cofactor_monomial_iff_hessenberg D hD).mpr hh

end SkewClassInflation
