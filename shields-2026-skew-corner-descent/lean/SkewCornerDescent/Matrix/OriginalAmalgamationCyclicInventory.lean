/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalAmalgamationWord
import SkewCornerDescent.Matrix.OriginalWindowResponsePeriod
import SkewCornerDescent.Matrix.OriginalCapNormalization
import SkewCornerDescent.FinitePeriodicWords
import SkewCornerDescent.FiniteClosureWindows

/-!
# The actual amalgamation's complete extra cyclic inventory

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`, `lem:original-transfer`).
The literal equal end windows produce the overlap period and the amalgamation word.
Its extra linear starts form exactly one complete cyclic inverse inventory, including
repeated wraps and the zero-start full-source boundary. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete literal windows supply the actual finite cycle and every extra start in the
amalgamation. Neither a word correspondence nor a response-period equation is an input. -/
theorem originalAmalgamation_linear_inventory {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hproper : originalSelectedCount (hD := hD) W < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)]
    (j : ℕ) (hj : j ≤ originalSelectedCount (hD := hD) P) :
    let cycle := finiteWordCycle (n := originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W) (c.originalInternalResidue P) (by omega)
    linearInverseWindowSum (c.originalInternalResidue A) j =
      linearInverseWindowSum (c.originalInternalResidue P) j + inverseWindowSum cycle j := by
  classical
  let B := originalSelectedCount (hD := hD) P
  let C := originalSelectedCount (hD := hD) W
  let N := B - C
  have hN : 0 < N := by dsimp only [N, B, C]; omega
  have hNL : N ≤ B - 1 := by dsimp only [N, B, C]; omega
  let cycle := finiteWordCycle (n := N) (c.originalInternalResidue P) hNL
  have hp (i j : Fin (B - 1)) (hji : j.val = i.val + N) :
      c.originalInternalResidue P i = c.originalInternalResidue P j := by
    have he := c.originalWindow_response_period_from_profile P W q z v hv hW.symm
      hwindow hcutq hcutLq i j hji
    exact congrArg c.regularResidue he
  have hP (i : Fin (B - 1)) :
      c.originalInternalResidue P i = cycle (i.val : ZMod N) :=
    finiteWordCycle_eq _ hNL hp i
  obtain ⟨hcount, hinv, hw⟩ := c.originalAmalgamation_internal_word P W A q v u z
    hq hv hwindow hW hA
    (fun _ hx => privateDiagonal_avoids_interior hcutq hx)
    (fun _ hx => privateDiagonal_avoids_interior hcutLq hx) hC
  have hlen : originalSelectedCount (hD := hD) A - 1 = (B - 1) + N := by
    dsimp only [N, B, C]
    omega
  have hAcycle (i : Fin (originalSelectedCount (hD := hD) A - 1)) :
      c.originalInternalResidue A i = cycle (i.val : ZMod N) := by
    have he := congrArg c.regularResidue (hw i)
    by_cases hi : i.val < N
    · simp only [show i.val < originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W from hi, dite_true] at he
      exact he.trans (hP _)
    · simp only [show ¬ i.val < originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W from hi, dite_false] at he
      have hm : ((i.val - N : ℕ) : ZMod N) = (i.val : ZMod N) := by
        rw [Nat.cast_sub (by omega : N ≤ i.val), ZMod.natCast_self, sub_zero]
      exact he.trans ((hP _).trans (congrArg cycle hm))
  dsimp only
  rw [linearInverseWindowSum_fin_congr hlen _
    (fun i : Fin ((B - 1) + N) => cycle (i.val : ZMod N))
    (fun i => by simpa only [finCongr_apply, Fin.val_cast] using hAcycle i) j,
    linearInverseWindowSum_add_period cycle j (by dsimp only [B]; omega)]
  have he : (fun i : Fin (B - 1) => cycle (i.val : ZMod N)) =
      c.originalInternalResidue P := funext (fun i => (hP i).symm)
  rw [he]

end SkewCornerDescent.Matrix.SelectedCoordinate
