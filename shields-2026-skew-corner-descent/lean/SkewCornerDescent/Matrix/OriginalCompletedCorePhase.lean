/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedCorePhase
import SkewCornerDescent.Matrix.OriginalResponseCycleProjection

/-!
# Completed actual nullspace periods give literal selected-core phases

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The completed actual response and gap periods restrict to their full internal
source ranges. Cofactor powers and complete windows supply the finite phase
anchor. Proper cores repeat as actual normalized literal components, without
identifying the active closure plane in advance. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

/-- A period of a complete actual response cycle restricts to the full original
internal word, retaining each indexed occurrence. -/
theorem completeResponseCycle_internal_period {B : ℕ} [NeZero B] {F : Type*}
    (l : Fin (B - 1) → F) (S : F) (r : ℕ)
    (hp : Function.Periodic (completeResponseCycle l S) (r : ZMod B))
    (i j : Fin (B - 1)) (hji : j.val = i.val + r) : l i = l j := by
  have h := hp (i.val : ZMod B)
  rw [← Nat.cast_add, ← hji, completeResponseCycle_prefix,
    completeResponseCycle_prefix] at h
  exact h.symm

/-- The cyclic coordinate of a valid original index reindexes to that same
literal finite index. -/
theorem finEquiv_symm_index {B : ℕ} [NeZero B] (i : Fin B) :
    (ZMod.finEquiv B).symm (i.val : ZMod B) = i := by
  cases B with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ B =>
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt

/-- A produced full source projection transports a closure-word period to the
complete actual finite word, including an equality of the two length spellings. -/
theorem completeResponseCycle_periodic_of_projection {n B C : ℕ}
    [NeZero n] [NeZero B] [NeZero C] {F : Type*} (hBC : B = C)
    (l : Fin (B - 1) → F) (capacity : n ≤ B - 1) (S : F) (r : ℕ)
    (hproj : completeResponseCycle l S =
      closureWord (finiteWordCycle (n := n) l capacity) S B)
    (hp : Function.Periodic (closureWord (finiteWordCycle (n := n) l capacity) S C)
      (r : ZMod C)) :
    Function.Periodic (completeResponseCycle l S) (r : ZMod B) := by
  subst C
  rw [hproj]
  exact hp

end SkewCornerDescent.CyclicWindows

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- On the actual one-active completed-period nullspace, the original selected
proper cores repeat at the selected multiplicity. This produces the core-phase
input before the closure plane is pinned. -/
theorem originalCompleted_selected_core_phase {n m : ℕ} (P : Profile n) (W : Profile m)
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
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    ∀ i j : Fin (originalSelectedCount (hD := hD) P), j.val = i.val + r →
      ∀ k, k < (c.top : ℕ) →
        (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
        (c.originalSelectedCoreRight P j).coeff k = (c.originalSelectedCoreRight P i).coeff k := by
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hrpos ha
  apply c.originalSelectedCore_phase_jets P W q u v hv hW hwindow hq hLq hC r (b - a)
    hrpos (by omega) (by rw [hcountP, hcountW, Nat.mul_sub_left_distrib])
  · intro i j hji
    exact completeResponseCycle_internal_period (c.originalInternalResidue P) active r
      hresponse i j hji
  · intro i j hji _
    have h := hgap (i.val : ZMod (originalSelectedCount (hD := hD) P))
    rw [← Nat.cast_add, ← hji] at h
    dsimp only at h
    rw [finEquiv_symm_index, finEquiv_symm_index] at h
    exact h.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
