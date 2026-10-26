/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationCoreWord
import SkewCornerDescent.Matrix.OriginalCompletedCorePhase
import SkewCornerDescent.FiniteSplicedWordPeriod

/-!
# Actual proper-core phases through the complete amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual prefix and full source word transport every core phase. Original
corner powers supply the required prefix divisibility and finite count relations.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original completed nullspace supplies all actual amalgamation core phases,
including intervals crossing the prefix-to-source splice. -/
theorem originalCompleted_amalgamation_core_phase {n m an : ℕ}
    (P : Profile n) (W : Profile m) (A : Profile an)
    (q : ℤ) (u v w : ℤ × ℤ) (hq0 : 0 ≤ q) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate w A.cells)
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
    (d : ℕ) (i t : Fin (originalSelectedCount (hD := hD) A))
    (ht : t.val = i.val + d * r) (k : ℕ) (hk : k < (c.top : ℕ)) :
    (c.originalSelectedCoreLeft A t).coeff k = (c.originalSelectedCoreLeft A i).coeff k ∧
    (c.originalSelectedCoreRight A t).coeff k = (c.originalSelectedCoreRight A i).coeff k := by
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hdivP : r ∣ originalSelectedCount (hD := hD) P := ⟨b, hcountP⟩
  have hdivW : r ∣ originalSelectedCount (hD := hD) W := ⟨a, hcountW⟩
  obtain ⟨hcount, hinv, hword⟩ := c.originalAmalgamation_core_word P W A q v w u hq0 hv
    hwindow hW.symm hA (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx)
  let T := originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W
  have hlenA : originalSelectedCount (hD := hD) A =
      originalSelectedCount (hD := hD) P + T := by dsimp only [T]; omega
  have hT : T ≤ originalSelectedCount (hD := hD) P := Nat.sub_le _ _
  have hlenr : r ≤ originalSelectedCount (hD := hD) P := Nat.le_of_dvd (NeZero.pos _) hdivP
  have hdivT : r ∣ T := Nat.dvd_sub hdivP hdivW
  let f := fun j : Fin (originalSelectedCount (hD := hD) P) =>
    ((c.originalSelectedCoreLeft P j).coeff k, (c.originalSelectedCoreRight P j).coeff k)
  let g := fun j : Fin (originalSelectedCount (hD := hD) A) =>
    ((c.originalSelectedCoreLeft A j).coeff k, (c.originalSelectedCoreRight A j).coeff k)
  have hrep (j : Fin (originalSelectedCount (hD := hD) A)) :
      g j = if hj : j.val < T then f ⟨j.val, hj.trans_le hT⟩
        else f ⟨j.val - T, by have := j.isLt; omega⟩ := by
    have h := hword j
    by_cases hj : j.val < T
    · change j.val < originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W at hj
      simp only [T, hj, ↓reduceDIte] at h ⊢
      exact Prod.ext (congrArg (fun p => p.coeff k) h.1)
        (congrArg (fun p => p.coeff k) h.2)
    · change ¬ j.val < originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W at hj
      simp only [T, hj, ↓reduceDIte] at h ⊢
      exact Prod.ext (congrArg (fun p => p.coeff k) h.1)
        (congrArg (fun p => p.coeff k) h.2)
  have hphase := c.originalCompleted_selected_core_phase P W q u v hv hW hwindow hq hLq
    Λ b a r ha hab hrpos hr hKU hKW active hresponse hgap
  have hp (j l : Fin (originalSelectedCount (hD := hD) P)) (hl : l.val = j.val + r) :
      f j = f l := by
    have h := hphase j l hl k hk
    exact Prod.ext h.1.symm h.2.symm
  have he := finite_spliced_word_phase hlenA hT hrpos hlenr hdivT f g hrep hp d i t ht
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
