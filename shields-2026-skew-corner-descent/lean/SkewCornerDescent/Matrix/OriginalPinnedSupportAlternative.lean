/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSupportAlternative
import SkewCornerDescent.Matrix.OriginalOneActiveClosurePin
import SkewCornerDescent.Matrix.OriginalVerticalResponse

/-!
# Actual determinant detection or a pinned periodic support branch

Supports `shields-2026-skew-corner-descent.tex`
(`thm:intrinsic-order`, `prop:closure-pin`).
The support alternative supplies every phase and gap premise consumed by the
private closure-plane pin. No proper-core phase jet, response period, active
class, or class-count balance is assumed at the assembly boundary. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
attribute [local instance] Classical.propDecidable

noncomputable local instance pinnedSupportRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete ordinary windows either detect the actual full determinant
before the period order or produce its actual omitted phase with label zero
or one. The support and mixed-jet suppliers compose inside this declaration. -/
theorem originalPinnedSupport_alternative {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevq : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (hprevLq : diagLo P.cells (P.xi 0 - q - 1) = diagHi P.cells (P.xi 0 - q - 1))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hr : 0 < r)
    (hcoprime : b.Coprime a) (hprime : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (Δ : ℤ) (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * Δ)
    [NeZero (originalSelectedCount (hD := hD) P)] [NeZero (r * b)]
    [NeZero (r * (b - a))] (hqspan : q = ((b - a : ℕ) : ℤ) * Δ)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁)
    (lo prevlo hi prevhi : ℤ × ℤ)
    (hlo : lo ∈ P.cells) (hprevlo : prevlo ∈ P.cells)
    (hhi : hi ∈ P.cells) (hprevhi : prevhi ∈ P.cells)
    (hclo : content lo = P.xi 0 - q) (hcprevlo : content prevlo = P.xi 0 - q - 1)
    (hchi : content hi = q) (hcprevhi : content prevhi = q - 1)
    (hdir : lo.2 = prevlo.2 ↔ hi.2 = prevhi.2) :
    (∃ h : ℕ, 0 < h ∧ h ≤ r * (b - a) - 1 ∧
      PowerSeries.coeff h (c.originalDeterminantDefect P A Q a b p₀ p₁) ≠ 0) ∨
    (∃ active : c.OriginalResponseClass P,
      c.originalResponseClassExponent P W a b active = ((b - a : ℕ) : ℤ) ∧
      (∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0) ∧
      Function.Periodic (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
        (r : ZMod (originalSelectedCount (hD := hD) P)) ∧
      ∃ hperiod : r * (b - a) ≤ originalSelectedCount (hD := hD) P - 1,
        Function.Periodic (closureWord (finiteWordCycle (n := r * (b - a))
          (c.originalInternalResidue P) hperiod) active.val (r * b)) (r : ZMod (r * b)) ∧
        (∀ i j : Fin (originalSelectedCount (hD := hD) P), j.val = i.val + r →
          ∀ k, k < (c.top : ℕ) →
            (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
            (c.originalSelectedCoreRight P j).coeff k =
              (c.originalSelectedCoreRight P i).coeff k) ∧
        (let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
          ⟨originalSelectedCount (hD := hD) P, by
            rw [originalHorizontalClosure_profile_selected_count P Q w hQ]
            omega⟩;
          let hB := NeZero.pos (originalSelectedCount (hD := hD) P);
          let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, hB⟩;
          let last : Fin (originalSelectedCount (hD := hD) P) :=
            ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩;
          (active.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
            (if lo.2 = prevlo.2 then 1 else 0) * c.originalTrueCapProduct P) ∧
          ∃ k : ℕ, ∃ V : Profile k, ∃ vV : ℤ × ℤ,
            ∃ hV : originalVerticalClosure P = translate vV V.cells,
              active.val = if lo.2 = prevlo.2 then
                c.regularResidue (c.originalLocalResponse V
                  (some (originalVerticalClosureSelectedCopy P V vV hV true
                    (originalSelectedEnumeration (hD := hD) P last)))
                  (some (originalVerticalClosureSelectedCopy P V vV hV false
                    (originalSelectedEnumeration (hD := hD) P first))))
              else c.regularResidue (c.originalHessenbergResponse Q middle middle))) := by
  rcases c.originalSupport_alternative P W A Q q v u z w hq hv hwindow hW hA hQ
      hcutq hcutLq hmax Λ b a r ha hab hr hcoprime hprime hKU hKW Δ hspan hqspan
      p₀ p₁ hpq hdep with hdetect | ⟨active, he, hother, hgap, hperiod, hresponse, hstep⟩
  · exact Or.inl hdetect
  · have hactive : c.originalResponseClassExponent P W a b active ≠ 0 := by
      rw [he]
      omega
    have hpin := c.originalOneActive_closure_plane_pin P W A Q q v u z w hv hwindow
      hW hA hQ hcutq hcutLq hprevq hprevLq hmax Λ b a r ha hab hr hprime hKU hKW
      p₀ p₁ hpq hdep active hactive hgap hperiod hresponse hstep
      lo prevlo hi prevhi hlo hprevlo hhi hprevhi hclo hcprevlo hchi hcprevhi hdir
    have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
    obtain ⟨k, V, vV, hV, hactual⟩ :=
      c.originalClosure_plane_actual_response P Q w hQ hB (decide (lo.2 = prevlo.2))
    refine Or.inr ⟨active, he, hother, hgap, hperiod, hresponse, hstep, hpin,
      k, V, vV, hV, ?_⟩
    dsimp only at hpin hactual ⊢
    by_cases hdir : lo.2 = prevlo.2
    · simp only [hdir, decide_true, ↓reduceIte, one_mul] at hpin hactual ⊢
      exact hpin.trans hactual
    · simp only [hdir, decide_false, Bool.false_eq_true, ↓reduceIte, zero_mul, sub_zero]
        at hpin hactual ⊢
      exact hpin

end SkewCornerDescent.Matrix.SelectedCoordinate
