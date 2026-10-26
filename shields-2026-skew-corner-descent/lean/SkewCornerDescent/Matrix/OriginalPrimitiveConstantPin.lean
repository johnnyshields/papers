/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrimitiveCoreProfiles
import SkewCornerDescent.Matrix.OriginalConstantWindowClass
import SkewCornerDescent.Matrix.OriginalOneActiveClosurePin
import SkewCornerDescent.Matrix.OriginalOrdinaryCenterResponse
import SkewCornerDescent.Matrix.OriginalOrdinaryClosureScalars

/-!
# Direct ordinary closure pin for a constant primitive original word

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The original corner powers produce both counts. A constant response word
supplies its one active class; the primitive classifier supplies the full
gap period and literal-window core jets. The actual ordinary cut then pins
the real horizontal or vertical internal center without a detector branch.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
noncomputable local instance primitiveConstantPinRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

set_option maxHeartbeats 800000 in
-- The direct assembly retains the full dependent source and ordinary closure inventories.
/-- A constant primitive response word directly produces its actual ordinary
closure, active class, full core profiles and complete gap period. -/
theorem originalPrimitive_constant_ordinary_pin {n m s t : ℕ}
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
    (hprevq : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (hprevLq : diagLo P.cells (P.xi 0 - q - 1) = diagHi P.cells (P.xi 0 - q - 1))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b)
    (hcop : Nat.Coprime b a) (hr : primeOrder (cellSchur D hD.1) Λ = 1)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det = Λ^b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ) (fun j => W.zeta j.castSucc)).det = Λ^a)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₁)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hconstant : ∀ i j, c.originalInternalResidue P i = c.originalInternalResidue P j)
    (lo prevlo hi prevhi : ℤ × ℤ)
    (hlo : lo ∈ P.cells) (hprevlo : prevlo ∈ P.cells)
    (hhi : hi ∈ P.cells) (hprevhi : prevhi ∈ P.cells)
    (hclo : content lo = P.xi 0 - q) (hcprevlo : content prevlo = P.xi 0 - q - 1)
    (hchi : content hi = q) (hcprevhi : content prevhi = q - 1)
    (hdir : lo.2 = prevlo.2 ↔ hi.2 = prevhi.2) :
    ∃ active : c.OriginalResponseClass P,
      c.originalResponseClassExponent P W a b active = ((b-a : ℕ) : ℤ) ∧
      (∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0) ∧
      Function.Periodic (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
        (1 : ZMod (originalSelectedCount (hD := hD) P)) ∧
      (∀ i : Fin (originalSelectedCount (hD := hD) P),
        c.originalSelectedCoreLeft P i = c.originalSelectedCoreLeft P 0 ∧
          c.originalSelectedCoreRight P i = c.originalSelectedCoreRight P 0) ∧
      ∃ on : ℕ, ∃ O : Profile on, ∃ zO : ℤ × ℤ,
        ∃ hO : originalHorizontalClosure P = translate zO O.cells ∨
          originalVerticalClosure P = translate zO O.cells,
        c.originalInternalResidue O ⟨originalSelectedCount (hD := hD) P - 1, by
          rw [originalOrdinaryClosure_selected_count P O zO hO]
          have := NeZero.pos (originalSelectedCount (hD := hD) P)
          omega⟩ = active.val := by
  classical
  have hcountP : originalSelectedCount (hD := hD) P = b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, mul_one]
  have hcountW : originalSelectedCount (hD := hD) W = a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, mul_one]
  let : NeZero b := ⟨by omega⟩
  let : NeZero (1*b) := ⟨by omega⟩
  let : NeZero (1*(b-a)) := ⟨by omega⟩
  let i₀ : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨0, by omega⟩
  let active := c.originalResponseClassOf P (originalInternalStateIndex P i₀)
  have haval : active.val = c.originalInternalResidue P i₀ := rfl
  obtain ⟨_, he, hother⟩ := c.originalWindow_constant_internal_class P W q z v hv hW.symm
    hwindow hcutq hcutLq a b ha (by omega) hcountP hcountW i₀ (fun i => hconstant i i₀)
  change c.originalResponseClassExponent P W a b active = ((b-a : ℕ) : ℤ) at he
  change ∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0 at hother
  obtain ⟨_, _, hgap⟩ := c.originalPrimitive_closure_heights P W A H q v u z w hv hwindow hW
    hA hH hcutq hcutLq hmax Λ a b ha (by omega) hcop hcountP hcountW hKU hKW p₀ p₁ hpq hdep
  have hcore := c.originalPrimitive_constant_core_profiles P W A H q v u z w hv hwindow hW
    hA hH hcutq hcutLq hmax Λ a b ha (by omega) hcop hcountP hcountW hKU hKW p₀ p₁ hpq hdep
    i₀ (fun i => hconstant i i₀)
  have hperiod : 1*(b-a) ≤ originalSelectedCount (hD := hD) P - 1 := by omega
  have hword (x : ZMod (1*b)) : closureWord
      (finiteWordCycle (c.originalInternalResidue P) hperiod) active.val (1*b) x =
        active.val := by
    unfold closureWord
    split_ifs
    · rfl
    · exact (hconstant _ i₀).trans haval.symm
  have hresponse : Function.Periodic (closureWord
      (finiteWordCycle (c.originalInternalResidue P) hperiod) active.val (1*b))
      (1 : ZMod (1*b)) :=
    fun x => (hword _).trans (hword _).symm
  have hstep (i j : Fin (originalSelectedCount (hD := hD) P)) (_ : j.val = i.val+1)
      (k : ℕ) (_ : k < (c.top : ℕ)) :
      (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
      (c.originalSelectedCoreRight P j).coeff k = (c.originalSelectedCoreRight P i).coeff k :=
    ⟨congrArg (fun p : Polynomial (OtherField c.top) => p.coeff k)
        ((hcore j).1.trans (hcore i).1.symm),
      congrArg (fun p : Polynomial (OtherField c.top) => p.coeff k)
        ((hcore j).2.trans (hcore i).2.symm)⟩
  have hpin := c.originalOneActive_closure_plane_pin P W A H q v u z w hv hwindow hW hA hH
    hcutq hcutLq hprevq hprevLq hmax Λ b a 1 ha hab (by omega) hr hKU hKW
    p₀ p₁ hpq hdep active (by rw [he]; omega)
    (by simpa only [Nat.cast_one] using hgap) hperiod
    (by simpa only [Nat.cast_one] using hresponse) hstep
    lo prevlo hi prevhi hlo hprevlo hhi hprevhi hclo hcprevlo hchi hcprevhi hdir
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  refine ⟨active, he, hother, hgap, hcore, ?_⟩
  by_cases hvdir : lo.2 = prevlo.2
  · obtain ⟨on, O, zO, hO⟩ := (originalVerticalClosure_connected P).exists_profile_cells
    refine ⟨on, O, zO, Or.inr hO, ?_⟩
    have hc := c.originalVerticalClosure_internal_center_response P O H zO w hO hH hB
    dsimp only at hc hpin ⊢
    simp only [hvdir, ↓reduceIte, one_mul] at hpin
    exact hc.trans hpin.symm
  · refine ⟨t, H, w, Or.inl hH, ?_⟩
    have hc := c.originalHorizontalClosure_internal_center_response P H w hH hB
    dsimp only at hc hpin ⊢
    simp only [hvdir, ↓reduceIte, zero_mul, sub_zero] at hpin
    exact hc.trans hpin.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
