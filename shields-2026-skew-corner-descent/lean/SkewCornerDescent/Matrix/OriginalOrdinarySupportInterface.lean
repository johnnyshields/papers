/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPinnedSupportAlternative
import SkewCornerDescent.Matrix.OriginalOrdinaryCenterResponse
import SkewCornerDescent.Matrix.OriginalResponseCycleProjection
import SkewCornerDescent.Matrix.OriginalOrdinaryClosureScalars

/-!
# Actual ordinary support alternative at the complete normal interface

Supports `shields-2026-skew-corner-descent.tex` (`thm:intrinsic-order`).
The full support alternative supplies detection or one active class and
its periodic words. Literal source projection transfers the completed
response period at the exact produced cardinality. Canonical ordinary
center bridges then supply the actual horizontal or vertical center,
not an assumed unit-corrected representation. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
noncomputable local instance ordinarySupportInterfaceRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

private theorem closure_word_periodic_modulus_congr {F : Type*} {n B C : ℕ}
    [NeZero B] [NeZero C] (f : ZMod n → F) (S : F) (k : ℕ) (h : B = C)
    (hp : Function.Periodic (closureWord f S C) (k : ZMod C)) :
    Function.Periodic (closureWord f S B) (k : ZMod B) := by
  subst C
  exact hp

set_option maxHeartbeats 1000000 in
-- The support result and source projection use distinct dependent cyclic index types.
/-- The actual ordinary full-window domain supplies every hypothesis needed
by the normal interface, unless a positive earlier original coefficient is detected. -/
theorem originalOrdinary_support_interface {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (H : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevq : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (hprevLq : diagLo P.cells (P.xi 0 - q - 1) = diagHi P.cells (P.xi 0 - q - 1))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hr : 0 < r)
    (hcop : Nat.Coprime b a) (hprime : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det = Λ^b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ) (fun j => W.zeta j.castSucc)).det = Λ^a)
    (δ : ℤ) (hspan : P.xi 0 = (b : ℤ) * δ)
    (hqspan : q = ((b-a : ℕ) : ℤ) * δ)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₁)
    (lo prevlo hi prevhi : ℤ × ℤ)
    (hlo : lo ∈ P.cells) (hprevlo : prevlo ∈ P.cells)
    (hhi : hi ∈ P.cells) (hprevhi : prevhi ∈ P.cells)
    (hclo : content lo = P.xi 0 - q) (hcprevlo : content prevlo = P.xi 0 - q - 1)
    (hchi : content hi = q) (hcprevhi : content prevhi = q - 1)
    (hdir : lo.2 = prevlo.2 ↔ hi.2 = prevhi.2) :
    (∃ j : ℕ, 0 < j ∧ j ≤ r*(b-a)-1 ∧
      PowerSeries.coeff j (c.originalDeterminantDefect P A H a b p₀ p₁) ≠ 0) ∨
    ∃ active : c.OriginalResponseClass P,
      c.originalResponseClassExponent P W a b active = ((b-a : ℕ) : ℤ) ∧
      (∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0) ∧
      Function.Periodic (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
        (r : ZMod (originalSelectedCount (hD := hD) P)) ∧
      Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active.val)
        (r : ZMod (originalSelectedCount (hD := hD) P)) ∧
      ∃ on : ℕ, ∃ O : Profile on, ∃ zO : ℤ × ℤ,
        ∃ hO : originalHorizontalClosure P = translate zO O.cells ∨
          originalVerticalClosure P = translate zO O.cells,
        c.originalInternalResidue O ⟨originalSelectedCount (hD := hD) P - 1, by
          rw [originalOrdinaryClosure_selected_count P O zO hO]
          have := NeZero.pos (originalSelectedCount (hD := hD) P)
          omega⟩ = active.val := by
  classical
  let : NeZero (r*b) := ⟨ne_of_gt (Nat.mul_pos hr (show 0 < b by omega))⟩
  let : NeZero (r*(b-a)) := ⟨by have := Nat.mul_pos hr (show 0 < b-a by omega); omega⟩
  have hspan' : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ)*δ := by rw [P.zeta_last]; simpa using hspan
  rcases c.originalPinnedSupport_alternative P W A H q v u z w hq hv hwindow hW hA hH
      hcutq hcutLq hprevq hprevLq hmax Λ b a r ha hab hr hcop hprime hKU hKW δ hspan'
      hqspan p₀ p₁ hpq hdep lo prevlo hi prevhi hlo hprevlo hhi hprevhi
      hclo hcprevlo hchi hcprevhi hdir with hdet | hdata
  · exact Or.inl hdet
  · obtain ⟨active, he, hother, hgap, hperiod, hresponse, _, hremaining⟩ := hdata
    dsimp only at hremaining
    obtain ⟨hpin, on, V, vV, hV, _⟩ := hremaining
    have hcountP : originalSelectedCount (hD := hD) P = r*b := by
      rw [originalSelectedCount_eq_primeOrder, hKU,
        primeOrder_pow (irreducible_cellSchur hD).prime, hprime, Nat.mul_comm]
    have hcountW : originalSelectedCount (hD := hD) W = r*a := by
      rw [originalSelectedCount_eq_primeOrder, hKW,
        primeOrder_pow (irreducible_cellSchur hD).prime, hprime, Nat.mul_comm]
    have hC : 0 < originalSelectedCount (hD := hD) W := by
      rw [hcountW]
      exact Nat.mul_pos hr ha
    obtain ⟨_, hprojection⟩ := c.originalWindow_complete_cycle_projection P W q z v hv hW.symm
      hwindow hcutq hcutLq hC (r*(b-a)) (by rw [hcountP, hcountW, Nat.mul_sub_left_distrib])
    have hresponseActual : Function.Periodic
        (completeResponseCycle (c.originalInternalResidue P) active.val)
        (r : ZMod (originalSelectedCount (hD := hD) P)) := by
      rw [hprojection active.val]
      exact closure_word_periodic_modulus_congr
        (finiteWordCycle (c.originalInternalResidue P) hperiod) active.val r hcountP hresponse
    refine Or.inr ⟨active, he, hother, hgap, hresponseActual, ?_⟩
    have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
    by_cases hvdir : lo.2 = prevlo.2
    · refine ⟨on, V, vV, Or.inr hV, ?_⟩
      have hc := c.originalVerticalClosure_internal_center_response P V H vV w hV hH hB
      dsimp only at hc hpin ⊢
      simp only [hvdir, ↓reduceIte, one_mul] at hpin
      exact hc.trans hpin.symm
    · refine ⟨t, H, w, Or.inl hH, ?_⟩
      have hc := c.originalHorizontalClosure_internal_center_response P H w hH hB
      dsimp only at hc hpin ⊢
      simp only [hvdir, ↓reduceIte, zero_mul, sub_zero] at hpin
      exact hc.trans hpin.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
