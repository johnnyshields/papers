/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalCoreWords
import SkewCornerDescent.Matrix.OriginalCompletedCorePhase
import SkewCornerDescent.FiniteRepeatedWordPeriod

/-!
# Actual proper-core phases across the literal closure splice

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full copied core words transport source phases across the actual closure
boundary. The selected-count divisibility is supplied by the original corner power.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A proved source core phase persists through every period multiple in the literal
closure, including endpoints on opposite sides of its true splice. -/
theorem originalVerticalClosure_core_phase {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    (r : ℕ) (hr : 0 < r) (hdiv : r ∣ originalSelectedCount (hD := hD) P)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hphase : ∀ i j : Fin (originalSelectedCount (hD := hD) P), j.val = i.val + r →
      ∀ k < (c.top : ℕ),
        (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
        (c.originalSelectedCoreRight P j).coeff k = (c.originalSelectedCoreRight P i).coeff k)
    (d : ℕ) (i t : Fin (originalSelectedCount (hD := hD) Q))
    (ht : t.val = i.val + d * r) (k : ℕ) (hk : k < (c.top : ℕ)) :
    (c.originalSelectedCoreLeft Q t).coeff k = (c.originalSelectedCoreLeft Q i).coeff k ∧
    (c.originalSelectedCoreRight Q t).coeff k = (c.originalSelectedCoreRight Q i).coeff k := by
  let f := fun j : Fin (originalSelectedCount (hD := hD) P) =>
    ((c.originalSelectedCoreLeft P j).coeff k, (c.originalSelectedCoreRight P j).coeff k)
  let g := fun j : Fin (originalSelectedCount (hD := hD) Q) =>
    ((c.originalSelectedCoreLeft Q j).coeff k, (c.originalSelectedCoreRight Q j).coeff k)
  have hrep (j) : g j = f ⟨j.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ := by
    have h := c.originalVerticalClosure_core_words_mod P Q v hQ hB j
    exact Prod.ext (congrArg (fun p => p.coeff k) h.1)
      (congrArg (fun p => p.coeff k) h.2)
  have hp (j l : Fin (originalSelectedCount (hD := hD) P)) (hl : l.val = j.val + r) :
      f j = f l := by
    have h := hphase j l hl k hk
    exact Prod.ext h.1.symm h.2.symm
  have he := finite_repeated_word_phase hB hr hdiv f g hrep hp d i t ht
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- The original one-active completed nullspace supplies the entire actual closure
core phase from literal windows and original corner powers. No phase or closure
selected-count equality is left as an assembly premise. -/
theorem originalCompleted_vertical_core_phase {n m qn : ℕ}
    (P : Profile n) (W : Profile m) (Q : Profile qn)
    (z : ℤ × ℤ) (hQ : originalVerticalClosure P = translate z Q.cells)
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a < b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (d : ℕ) (i t : Fin (originalSelectedCount (hD := hD) Q))
    (ht : t.val = i.val + d * r) (k : ℕ) (hk : k < (c.top : ℕ)) :
    (c.originalSelectedCoreLeft Q t).coeff k = (c.originalSelectedCoreLeft Q i).coeff k ∧
    (c.originalSelectedCoreRight Q t).coeff k = (c.originalSelectedCoreRight Q i).coeff k := by
  have hcount : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hdiv : r ∣ originalSelectedCount (hD := hD) P := ⟨b, hcount⟩
  have hphase := c.originalCompleted_selected_core_phase P W q u v hv hW hwindow hq hLq
    Λ b a r ha hab hrpos hr hKU hKW active hresponse hgap
  exact c.originalVerticalClosure_core_phase P Q z hQ r hrpos hdiv (NeZero.pos _)
    hphase d i t ht k hk

end SkewCornerDescent.Matrix.SelectedCoordinate
