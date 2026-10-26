/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalOneActiveAlternative
import SkewCornerDescent.Matrix.OriginalResponseClassSum
import SkewCornerDescent.Matrix.OriginalCompletedCorePhase

/-!
# Complete actual support detection or one-active periodic nullspace

Formalizes `shields-2026-skew-corner-descent.tex` (`lem:positive-support`).
The full actual class inventory either detects by the period order minus one,
or has exactly one active class and both complete response and gap words are
periodic with the selected multiplicity. The statement does not require positivity
of the active exponents: the many-active producer also covers signed support.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

noncomputable local instance supportAlternativeRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- On the actual complete matched-chart domain, failure to detect through the
period order minus one leaves exactly one actual active class and both literal
completed response and gap words periodic. All numerical and class-inventory
inputs to the branch suppliers are produced internally. -/
theorem originalSupport_alternative {n m s t : ℕ}
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
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hrpos : 0 < r)
    (hcoprime : b.Coprime a) (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (Δ : ℤ) (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * Δ)
    [NeZero (originalSelectedCount (hD := hD) P)] [NeZero (r * b)]
    [NeZero (r * (b - a))]
    (hqspan : q = ((b - a : ℕ) : ℤ) * Δ)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
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
        ∀ i j : Fin (originalSelectedCount (hD := hD) P), j.val = i.val + r →
          ∀ k, k < (c.top : ℕ) →
            (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
            (c.originalSelectedCoreRight P j).coeff k =
              (c.originalSelectedCoreRight P i).coeff k) := by
  classical
  by_cases htwo : ∃ X Y : c.OriginalResponseClass P, X ≠ Y ∧
      c.originalResponseClassExponent P W a b X ≠ 0 ∧
      c.originalResponseClassExponent P W a b Y ≠ 0
  · exact Or.inl (c.originalManyActive_general P W A Q q v u z w hq hv hwindow hW hA hQ
      hcutq hcutLq hmax Λ b a r ha hab hrpos hcoprime hr hKU hKW Δ hspan hqspan
      p₀ p₁ hpq hdep htwo)
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hsum := c.originalWindow_responseClassExponent_sum P W q z v hv hW.symm
    hwindow hcutq hcutLq r b a hrpos ha (by omega) hcountP hcountW
  have hexists : ∃ X : c.OriginalResponseClass P,
      c.originalResponseClassExponent P W a b X ≠ 0 := by
    by_contra hnone
    have hz (X) : c.originalResponseClassExponent P W a b X = 0 := by
      by_contra hX
      exact hnone ⟨X, hX⟩
    simp_rw [hz] at hsum
    simp only [Finset.sum_const_zero] at hsum
    omega
  obtain ⟨active, hactive⟩ := hexists
  have hunique (X) (hne : X ≠ active) :
      c.originalResponseClassExponent P W a b X = 0 := by
    by_contra hX
    exact htwo ⟨X, active, hne, hX, hactive⟩
  have he : c.originalResponseClassExponent P W a b active = ((b - a : ℕ) : ℤ) := by
    rw [Finset.sum_eq_single active] at hsum
    · exact hsum
    · intro X _ hX
      exact hunique X hX
    · intro h
      exact (h (Finset.mem_univ active)).elim
  have hn : 2 ≤ r * (b - a) := by
    simpa only [one_mul] using
      Nat.mul_le_mul (show 1 ≤ r by omega) (show 2 ≤ b - a by omega)
  let : NeZero (r * (b - a)) := ⟨by omega⟩
  let : NeZero (r * b) := ⟨Nat.ne_of_gt (Nat.mul_pos hrpos (by omega))⟩
  let : NeZero (originalSelectedCount (hD := hD) P) := ⟨by rw [hcountP]; exact NeZero.ne _⟩
  rcases c.originalOneActive_alternative P W A Q q v u z w hq hv hwindow hW hA hQ
      hcutq hcutLq hmax Λ b a r ha hab hrpos hcoprime hr hKU hKW Δ hspan hqspan
      p₀ p₁ hpq hdep active hunique with hdetect | ⟨hgap, hresponse⟩
  · exact Or.inl ⟨r * (b - a) - 1, by omega, le_rfl, hdetect⟩
  · obtain ⟨capacity, hp⟩ := hresponse
    have hC : 0 < originalSelectedCount (hD := hD) W := by
      rw [hcountW]
      exact Nat.mul_pos hrpos ha
    have hdiff : r * (b - a) = originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W := by
      rw [hcountP, hcountW, Nat.mul_sub_left_distrib]
    obtain ⟨_, hproj⟩ := c.originalWindow_complete_cycle_projection P W q z v hv hW.symm
      hwindow hcutq hcutLq hC (r * (b - a)) hdiff
    have hactual := completeResponseCycle_periodic_of_projection hcountP
      (c.originalInternalResidue P) capacity active.val r (hproj active.val) hp
    have hcores := c.originalCompleted_selected_core_phase P W q z v hv hW.symm hwindow
      hcutq hcutLq Λ b a r ha (by omega) hrpos hr hKU hKW active.val hactual hgap
    exact Or.inr ⟨active, he, hunique, hgap, capacity, hp, hcores⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
