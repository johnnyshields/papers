/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SingleActivePacket
import SkewCornerDescent.Matrix.OriginalRationalClassSums

/-!
# Exact cap-normalized power of the single active original class

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
The actual rational support packet is collapsed by faithful class sums and
indicator functions.  The full source/window residue ratio is consequently
the active cap-normalized response to its produced exponent, with a produced
integer orientation sign.  No singleton support or rational prefactor match
is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
noncomputable local instance oneActiveCapPowerRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A single active actual class gives the exact source/window residue ratio
as its cap-normalized power with a produced orientation sign.  The rational
packet is collapsed using its faithful sums, not declared a singleton. -/
theorem originalOneActive_cap_normalized_power {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (H : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
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
    (active : c.OriginalResponseClass P)
    (hother : ∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0) :
    ∃ κ : ℤ, (κ = 1 ∨ κ = -1) ∧
      c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
        (κ : OtherField c.top) * (active.val / c.originalTrueCapProduct P)^(b-a) := by
  classical
  obtain ⟨ε, _, support, e, hε, _, hsupp, hdegree, hfactor, _, _, hsums, _⟩ :=
    c.originalWindow_rational_class_sums P W A H q v u z w hv hwindow hW hA hH
      hcutq hcutLq hC hmax Λ b a hab hKU hKW p₀ p₁ hpq hdep
  have hB : 0 < originalSelectedCount (hD := hD) P :=
    (c.originalWindow_true_cap_product P W q v z hwindow hW
      (fun _ hx => privateDiagonal_avoids_interior hcutq hx)
      (fun _ hx => privateDiagonal_avoids_interior hcutLq hx) hC).1
  let middle : Fin (originalSelectedCount (hD := hD) H + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by
      rw [originalHorizontalClosure_profile_selected_count P H w hH]
      omega⟩
  let S := c.regularResidue (c.originalHessenbergResponse H middle middle)
  let F := c.originalTrueCapProduct P
  let γ := c.residueMap H.schur / c.residueMap P.schur^2
  have hF : F ≠ 0 := c.originalTrueCapProduct_ne_zero P hB hmax
  obtain ⟨τ, hτ, hquot⟩ := c.originalHorizontalClosure_residue_quotient P H w hH hB hmax
  have hcoord : S / F = (τ : OtherField c.top) * γ := by
    change γ = (τ : OtherField c.top) * S / F at hquot
    rcases hτ with h | h
    · rw [h] at hquot ⊢
      simpa only [Int.cast_one, one_mul] using hquot.symm
    · rw [h] at hquot ⊢
      simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_div] at hquot ⊢
      linear_combination hquot
  have hshift := c.originalVirtualCentralResponse_eq_oriented_cap P H w hH hB hmax τ hcoord
  let response := c.originalVirtualCentralResponse P H middle
  have hτF : (τ : OtherField c.top) ≠ 0 := by
    rcases hτ with h | h <;> simp [h]
  have hinj : Function.Injective response := by
    intro α β he
    change c.originalVirtualCentralResponse P H middle α =
      c.originalVirtualCentralResponse P H middle β at he
    rw [hshift α, hshift β] at he
    have hm : ((((τ : ℚ)*α : ℚ) : OtherField c.top) * F) =
        ((((τ : ℚ)*β : ℚ) : OtherField c.top) * F) := by
      change S - ((((τ : ℚ)*α : ℚ) : OtherField c.top) * F) =
        S - ((((τ : ℚ)*β : ℚ) : OtherField c.top) * F) at he
      linear_combination -he
    have hh := mul_right_cancel₀ hF hm
    have hc : (α : OtherField c.top) = (β : OtherField c.top) :=
      mul_left_cancel₀ hτF (by simpa only [Rat.cast_mul, Rat.cast_intCast] using hh)
    exact_mod_cast hc
  obtain ⟨α, hsupport, hα, hvalue⟩ := single_active_packet_support support
    (Subtype.val : c.OriginalResponseClass P → OtherField c.top)
    (c.originalResponseClassExponent P W a b) active response hinj e hother
    (fun α hα => (hsupp α).mp hα) ((b-a : ℕ) : ℤ) (by exact_mod_cast (by omega : b-a ≠ 0))
    hdegree hsums
  rw [hsupport, Finset.prod_singleton, hα, zpow_natCast] at hfactor
  change c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
    (ε : OtherField c.top) * (γ - (α : OtherField c.top))^(b-a) at hfactor
  have hresponse : S - (τ : OtherField c.top) * (α : OtherField c.top) * F = active.val := by
    have hh := hvalue
    change c.originalVirtualCentralResponse P H middle α = active.val at hh
    rw [hshift α, Rat.cast_mul, Rat.cast_intCast] at hh
    exact hh
  have hγ : γ - (α : OtherField c.top) =
      (τ : OtherField c.top) * (active.val / F) := by
    rcases hτ with h | h
    · rw [h] at hcoord hresponse ⊢
      simp only [Int.cast_one, one_mul] at hcoord hresponse ⊢
      field_simp [hF] at hcoord ⊢
      linear_combination hresponse - hcoord
    · rw [h] at hcoord hresponse ⊢
      simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at hcoord hresponse ⊢
      field_simp [hF] at hcoord ⊢
      linear_combination hcoord - hresponse
  have hε2 : ε^2 = 1 := by rcases hε with h | h <;> simp [h]
  have hτ2 : τ^2 = 1 := by rcases hτ with h | h <;> simp [h]
  have hκ2 : (ε*τ^(b-a))^2 = 1 := by
    rw [mul_pow, hε2, one_mul, ← pow_mul, Nat.mul_comm (b-a) 2, pow_mul, hτ2, one_pow]
  refine ⟨ε*τ^(b-a), sq_eq_one_iff.mp hκ2, ?_⟩
  change c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
    (((ε*τ^(b-a) : ℤ) : OtherField c.top)) * (active.val / F)^(b-a)
  rw [hγ, mul_pow] at hfactor
  simpa only [Int.cast_mul, Int.cast_pow, mul_assoc] using hfactor

end SkewCornerDescent.Matrix.SelectedCoordinate
