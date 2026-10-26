/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedCorePhase

/-!
# Actual proper-core phase equality at every open-chain period multiple

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The complete source window produces one-step core phase rigidity. Finite-chain
composition supplies every period multiple inside the original source, without
assuming any phase equality or closing an unidentified cyclic edge. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual open-source multiple of the period has identical low proper-core jets.
All phase steps are produced from the original response/gap nullspace and complete window. -/
theorem originalSelectedCore_multiple_phase_jets {n m : ℕ} (P : Profile n) (W : Profile m)
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hdiff : originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W = r * d)
    (hresponse : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
      j.val = i.val + r → c.originalInternalResidue P i = c.originalInternalResidue P j)
    (hgap : ∀ i j : Fin (originalSelectedCount (hD := hD) P),
      j.val = i.val + r → j.val + 1 < originalSelectedCount (hD := hD) P →
        c.originalCompletedGap P i = c.originalCompletedGap P j) :
    ∀ s : ℕ, ∀ i j : Fin (originalSelectedCount (hD := hD) P),
      j.val = i.val + s * r → ∀ k, k < (c.top : ℕ) →
        (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
        (c.originalSelectedCoreRight P j).coeff k = (c.originalSelectedCoreRight P i).coeff k := by
  have hphase := c.originalSelectedCore_phase_jets P W q u v hv hW hwindow hq hLq hC
    r d hr hd hdiff hresponse hgap
  intro s
  induction s with
  | zero =>
    intro i j hij k hk
    have he : j = i := Fin.ext (by simpa only [Nat.zero_mul, Nat.add_zero] using hij)
    subst j
    exact ⟨rfl, rfl⟩
  | succ s ih =>
    intro i j hij k hk
    rw [Nat.succ_mul] at hij
    let mid : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨i.val + s * r, by have := j.isLt; omega⟩
    have hj : j.val = mid.val + r := by change j.val = i.val + s * r + r; omega
    have hs := hphase mid j hj k hk
    have hi := ih i mid rfl k hk
    exact ⟨hs.1.trans hi.1, hs.2.trans hi.2⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
