/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPositiveNullPeriod
import SkewCornerDescent.Matrix.OriginalResponseClassDefects
import SkewCornerDescent.Matrix.OriginalPrimitiveClasses

/-!
# One-active nullity on a complete literal matched window

Supports `shields-2026-skew-corner-descent.tex` (`lem:positive-support`).
Selected cofactor powers produce the complete occurrence counts. Literal matching
produces the period capacity and reduced class defects; the actual class family
then produces positive separating assignments. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory

private theorem windowDefect_length_congr {F ι : Type*} [Field F] [Fintype ι]
    {n B C : ℕ} [NeZero n] [NeZero B] [NeZero C] (h : B = C)
    (f : ZMod n → F) (S : ι → F) (e : ι → ℤ) (b j : ℕ) :
    windowDefect f S e b B j = windowDefect f S e b C j := by
  subst C
  rfl

private theorem closureWord_period_length_congr {F : Type*}
    {n B C : ℕ} [NeZero n] [NeZero B] [NeZero C] (h : B = C)
    (f : ZMod n → F) (S : F) (r : ℕ) :
    Function.Periodic (closureWord f S B) (r : ZMod B) ↔
      Function.Periodic (closureWord f S C) (r : ZMod C) := by
  subst C
  rfl

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A zero full-period detector with a unique active actual response class
forces the completed source response word to have the selected multiplicity
as period. Every count and capacity used by the cyclic theorem is produced
from the complete literal window and the original cofactor powers. -/
theorem originalWindow_one_active_null_primitive {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hrpos : 0 < r)
    (hcoprime : Nat.Coprime a b)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (r * (b - a))] [NeZero (r * b)]
    (active : c.OriginalResponseClass P)
    (hunique : ∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0)
    (hzero : ∀ hperiod : r * (b - a) ≤ originalSelectedCount (hD := hD) P - 1,
      windowDefect (finiteWordCycle (n := r * (b - a))
        (c.originalInternalResidue P) hperiod) Subtype.val
        (c.originalResponseClassExponent P W a b) b (r * b) (r * (b - a)) = 0) :
    ∃ hperiod : r * (b - a) ≤ originalSelectedCount (hD := hD) P - 1,
      Function.Periodic (closureWord (finiteWordCycle (n := r * (b - a))
        (c.originalInternalResidue P) hperiod) active.val (r * b)) (r : ZMod (r * b)) := by
  classical
  let d := b - a
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hB : 0 < originalSelectedCount (hD := hD) P := by
    rw [hcountP]
    exact Nat.mul_pos hrpos (by omega)
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hrpos ha
  obtain ⟨k, s, hk, hs, _, hbshape, _⟩ :=
    positive_remainder_exists (show 0 < d by dsimp [d]; omega)
      (show d < b by dsimp [d]; omega)
  obtain ⟨hperiod, hcounts, _⟩ := c.originalWindow_responseClass_defects P W q u v hv
    hW hwindow hcutq hcutLq hC r d s k b a hrpos hs hk hbshape
    (by dsimp [d]; omega) hcountP hcountW
  let word := c.originalResponseClassWord P (r * d) hperiod
  let cycle := finiteWordCycle (n := r * d) (c.originalInternalResidue P) hperiod
  have hcycle : Subtype.val ∘ word = cycle :=
    c.originalResponseClassWord_val P (r * d) hperiod
  have heq : c.originalResponseClassExponent P W a b =
      classDefect word 1 d s (r * s - 1) 0 := by
    funext X
    exact hcounts X
  have hlen : k * (r * d) + r * s = r * b := by rw [hbshape]; ring
  let : NeZero (k * (r * d) + r * s) := ⟨by rw [hlen]; exact NeZero.ne _⟩
  have hcop : Nat.Coprime (k * d + s) d := by
    rw [← hbshape]
    exact (Nat.coprime_self_sub_right (by omega)).mpr hcoprime.symm
  have hsingle : ∀ X, X ≠ active → classDefect word 1 d s (r * s - 1) 0 X = 0 := by
    intro X hX
    rw [← heq]
    exact hunique X hX
  have hz := hzero hperiod
  change windowDefect cycle Subtype.val _ b (r * b) (r * d) = 0 at hz
  rw [heq, ← hcycle,
    ← windowDefect_length_congr hlen (Subtype.val ∘ word) Subtype.val
      (classDefect word 1 d s (r * s - 1) 0) b (r * d)] at hz
  conv_lhs at hz => arg 4; rw [hbshape]
  have hp := c.original_one_active_null_of_unique P hB hmax hrpos hs hcop
    word active hsingle hz
  rw [hcycle] at hp
  exact ⟨hperiod, (closureWord_period_length_congr hlen cycle active.val r).mp hp⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
