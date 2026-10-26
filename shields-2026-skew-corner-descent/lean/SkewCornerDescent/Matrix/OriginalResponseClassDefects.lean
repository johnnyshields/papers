/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassWords
import SkewCornerDescent.CyclicInventoryDefects

/-!
# Exact reduced signed counts of actual response classes

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`, `lem:peeling`).
The complete original source and window counts reduce to the full-period mask
minus the literal short prefix. Natural subtraction is used only after the positive
remainder and multiplicity supply its boundary conditions. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory
open scoped BigOperators

private theorem reduced_signed_mask_counts {r d s k b a : ℕ} [NeZero (r * d)]
    (hr : 0 < r) (hs : 0 < s) (hk : 0 < k)
    (hb : b = k * d + s) (ha : a + d = b) (f : ZMod (r * d) → ℕ) :
    (a : ℤ) * windowSum f 1 (r * b - 1) 0 -
        (b : ℤ) * windowSum f 1 (r * a - 1) 0 =
      (s : ℤ) * (∑ i, f i) - (d : ℤ) * windowSum f 1 (r * s - 1) 0 := by
  have hrs : 0 < r * s := Nat.mul_pos hr hs
  have ha' : a = (k - 1) * d + s := by
    have hkk : k = (k - 1) + 1 := by omega
    rw [hkk, Nat.add_mul, one_mul] at hb
    omega
  have hP : r * b - 1 = k * (r * d) + (r * s - 1) := by
    rw [hb, Nat.mul_add, ← Nat.mul_assoc]
    have hm : r * k * d = k * (r * d) := by ring
    rw [hm]
    omega
  have hW : r * a - 1 = (k - 1) * (r * d) + (r * s - 1) := by
    rw [ha', Nat.mul_add, ← Nat.mul_assoc]
    have hm : r * (k - 1) * d = (k - 1) * (r * d) := by ring
    rw [hm]
    omega
  rw [hP, hW, zmod_windowSum_mul_add, zmod_windowSum_mul_add]
  simp only [nsmul_eq_mul, Nat.cast_id, Nat.cast_add, Nat.cast_mul]
  have hbZ : (b : ℤ) = (k : ℤ) * (d : ℤ) + (s : ℤ) := by exact_mod_cast hb
  have haZ : (a : ℤ) + (d : ℤ) = (b : ℤ) := by exact_mod_cast ha
  have hkZ : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hkZ, hbZ]
  have haZ' : (a : ℤ) = (k : ℤ) * (d : ℤ) + (s : ℤ) - (d : ℤ) := by omega
  rw [haZ']
  ring

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The signed multiplicity of a given value in the complete original source
and window inventories, including values absent from either inventory. -/
noncomputable def originalResponseValueExponent {n m : ℕ} (P : Profile n) (W : Profile m)
    (a b : ℕ) (x : OtherField c.top) : ℤ := by
  classical
  exact (a : ℤ) * (Finset.univ.filter fun i => c.originalInternalResidue P i = x).card -
    (b : ℤ) * (Finset.univ.filter fun i => c.originalInternalResidue W i = x).card

/-- The signed multiplicity of one literal actual response class. -/
noncomputable def originalResponseClassExponent {n m : ℕ} (P : Profile n) (W : Profile m)
    (a b : ℕ) (X : c.OriginalResponseClass P) : ℤ :=
  c.originalResponseValueExponent P W a b X.val

/-- The actual signed source/window occurrence counts are the exact cyclic
class defects on the paper's positive-remainder convention. No class balance,
mask count, or word projection is assumed. -/
theorem originalWindow_responseClass_defects {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (r d s k b a : ℕ) [NeZero (r * d)] (hr : 0 < r) (hs : 0 < s) (hk : 0 < k)
    (hb : b = k * d + s) (ha : a + d = b)
    (hcountP : originalSelectedCount (hD := hD) P = r * b)
    (hcountW : originalSelectedCount (hD := hD) W = r * a) :
    ∃ hperiod : r * d ≤ originalSelectedCount (hD := hD) P - 1,
      (∀ X : c.OriginalResponseClass P,
        (a : ℤ) * (Finset.univ.filter fun i => c.originalInternalResidue P i = X.val).card -
            (b : ℤ) * (Finset.univ.filter fun i => c.originalInternalResidue W i = X.val).card =
          classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s (r * s - 1) 0 X) ∧
      (∑ X : c.OriginalResponseClass P,
        classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s (r * s - 1) 0 X) =
          (d : ℤ) := by
  classical
  have hdiff : b - a = d := by omega
  have hjlen : r * d = originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W := by
    rw [hcountP, hcountW, ← Nat.mul_sub_left_distrib, hdiff]
  obtain ⟨hperiod, hcounts⟩ := c.originalWindow_responseClass_counts P W q u v hv hW
    hwindow hcutq hcutLq hC (r * d) hjlen
  refine ⟨hperiod, ?_, sum_reduced_classDefect hr hs _⟩
  intro X
  rw [(hcounts X).1, (hcounts X).2, hcountP, hcountW]
  exact reduced_signed_mask_counts hr hs hk hb ha
    (classMask (c.originalResponseClassWord P (r * d) hperiod) X)

end SkewCornerDescent.Matrix.SelectedCoordinate
