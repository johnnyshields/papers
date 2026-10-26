/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalOneActiveCapPower
import SkewCornerDescent.Matrix.OriginalOrdinaryClosureQuotient

/-!
# Exact ordinary monomial normalization of the one-active residue

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
The actual identified closing response and both complete ordinary quotient
factorizations turn the single active class into an exact source/window
residue power.  Its integer orientation scalar is produced, not imposed.
The actual rational numerator and denominator remain the supplied ones.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
noncomputable local instance oneActiveOrdinaryPowerRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Given the actual identified ordinary closing response, the single active
class supplies the exact ordinary source/window residue power.  Its scalar
orientation is produced from both original quotient factorizations, not an
assumed monomial normalization. -/
theorem originalOneActive_ordinary_residue_power {n m s t on : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (H : Profile t) (O : Profile on)
    (q : ℤ) (v u z w zO : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (hO : originalHorizontalClosure P = translate zO O.cells ∨
      originalVerticalClosure P = translate zO O.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a : ℕ) (hab : a < b)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₁)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : c.OriginalResponseClass P)
    (hother : ∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0)
    (hactive : let center : Fin (originalSelectedCount (hD := hD) O - 1) :=
        ⟨originalSelectedCount (hD := hD) P - 1, by
          rw [originalOrdinaryClosure_selected_count P O zO hO]
          have := NeZero.pos (originalSelectedCount (hD := hD) P)
          omega⟩
      c.originalInternalResidue O center = active.val) :
    ∃ κ : ℤ, (κ = 1 ∨ κ = -1) ∧
      c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
        (κ : OtherField c.top) * (c.residueMap O.schur / c.residueMap P.schur^2)^(b-a) := by
  obtain ⟨κ0, hκ0, hpower⟩ := c.originalOneActive_cap_normalized_power P W A H q v u z w hv
    hwindow hW hA hH hcutq hcutLq hC hmax Λ b a hab hKU hKW p₀ p₁ hpq hdep active hother
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  obtain ⟨ε, hε, hquot⟩ := c.originalOrdinaryClosure_residue_quotient P O zO hO hB hmax
  let F := c.originalTrueCapProduct P
  let γ := c.residueMap O.schur / c.residueMap P.schur^2
  change γ = (ε : OtherField c.top) * _ / F at hquot
  rw [hactive] at hquot
  have horiented : active.val / F = (ε : OtherField c.top) * γ := by
    rcases hε with h | h
    · rw [h] at hquot ⊢
      simpa only [Int.cast_one, one_mul] using hquot.symm
    · rw [h] at hquot ⊢
      simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_div] at hquot ⊢
      linear_combination hquot
  have hκ02 : κ0^2 = 1 := by rcases hκ0 with h | h <;> simp [h]
  have hε2 : ε^2 = 1 := by rcases hε with h | h <;> simp [h]
  have hκ2 : (κ0*ε^(b-a))^2 = 1 := by
    rw [mul_pow, hκ02, one_mul, ← pow_mul, Nat.mul_comm (b-a) 2, pow_mul, hε2, one_pow]
  refine ⟨κ0*ε^(b-a), sq_eq_one_iff.mp hκ2, ?_⟩
  change c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
    (κ0 : OtherField c.top) * (active.val / F)^(b-a) at hpower
  rw [horiented, mul_pow] at hpower
  simpa only [Int.cast_mul, Int.cast_pow, mul_assoc] using hpower

end SkewCornerDescent.Matrix.SelectedCoordinate
