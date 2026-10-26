/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPositiveClassWitness
import SkewCornerDescent.Matrix.OriginalManyActive
import SkewCornerDescent.CyclicSignedSpecialization

/-!
# One-positive actual short and last inventories

Formalizes the inventory assertions of `shields-2026-skew-corner-descent.tex`
(`lem:two-support`, `cor:one-positive-short`). The literal class counts and a
produced common positive assignment force the original-field short and last
inventories nonzero. No independent response variables, analytic balance premise,
or assumed positive specialization appears in the theorem. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- One positive and at least one negative actual exponent force both the short
and last inventories nonzero. The common positive assignment separates a chosen
negative class from the positive one. No residue factorization is needed for this
inventory assertion; it is consumed only by the original coefficient transfer. -/
theorem originalOnePositive_inventories {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r k s : ℕ) (ha : 0 < a) (hab : a < b) (hrpos : 0 < r)
    (hk : 0 < k) (hs : 0 < s) (hsd : s ≤ b - a) (hbshape : b = k * (b - a) + s)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (r * (b - a))] [NeZero (r * b)]
    (p : c.OriginalResponseClass P)
    (hp : 0 < c.originalResponseClassExponent P W a b p)
    (hothers : ∀ X, X ≠ p → c.originalResponseClassExponent P W a b X ≤ 0)
    (hnegative : ∃ X, c.originalResponseClassExponent P W a b X < 0) :
    ∃ hperiod : r * (b - a) ≤ originalSelectedCount (hD := hD) P - 1,
      let f := finiteWordCycle (n := r * (b - a)) (c.originalInternalResidue P) hperiod
      let e := c.originalResponseClassExponent P W a b
      windowDefect f Subtype.val e b (r * b) (r * s) ≠ 0 ∧
        lastWindowDefect f Subtype.val e b (r * b) ≠ 0 := by
  classical
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hB : 0 < originalSelectedCount (hD := hD) P := by
    rw [hcountP]; exact Nat.mul_pos hrpos (by omega)
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]; exact Nat.mul_pos hrpos ha
  obtain ⟨hperiod, hcounts, hsum⟩ := c.originalWindow_responseClass_defects P W q u v hv
    hW hwindow hcutq hcutLq hC r (b - a) s k b a hrpos hs hk hbshape (by omega)
    hcountP hcountW
  let word := c.originalResponseClassWord P (r * (b - a)) hperiod
  have heq : c.originalResponseClassExponent P W a b =
      classDefect word 1 (b - a) s (r * s - 1) 0 := funext fun X => hcounts X
  obtain ⟨X, hX⟩ := hnegative
  have hXp : X ≠ p := by intro h; rw [h] at hX; omega
  obtain ⟨num, den, x, hrep, hnF, hdF, hnR, hdR, hpos, hsep⟩ :=
    c.originalResponseClasses_positive_separated P hB hmax X p hXp
  let ι := algebraMap (OtherPolynomial c.top) (OtherField c.top)
  let φ := (MvPolynomial.eval x).comp (realResiduePolynomial c.top)
  have hlen : k * (r * (b - a)) + r * s = r * b := by
    calc
      _ = r * (k * (b - a) + s) := by ring
      _ = r * b := congrArg (r * ·) hbshape.symm
  let : NeZero (k * (r * (b - a)) + r * s) := ⟨by rw [hlen]; exact NeZero.ne _⟩
  have hshort := specialized_one_positive_short_ne_zero hrpos hs hsd hk ι φ
    (IsFractionRing.injective _ _) num den word hnF hdF hnR hdR hpos p
    (fun Y hY => by rw [← heq]; exact hothers Y hY)
    ⟨X, by rw [← heq]; exact hX, hsep⟩
  have hresponse : (fun Y => ι (num Y) / ι (den Y)) =
      (Subtype.val : c.OriginalResponseClass P → OtherField c.top) := funext fun Y => (hrep Y).symm
  dsimp only at hshort
  rw [hresponse] at hshort
  let : NeZero (r * s) := ⟨Nat.ne_of_gt (Nat.mul_pos hrpos hs)⟩
  have hfull := windowDefect_full_eq_short (r := r) (d := b - a) (s := s)
    (Subtype.val ∘ word) Subtype.val (classDefect word 1 (b - a) s (r * s - 1) 0)
    (Nat.mul_le_mul_left r hsd) hk rfl rfl rfl
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)) hsum
  rw [windowDefect_eq_last] at hfull
  have hunit : ((k * (b - a) + s : ℕ) : OtherField c.top) / (s : OtherField c.top) *
      (∏ i, (Subtype.val ∘ word) i)⁻¹ ^ k ≠ 0 := by
    apply mul_ne_zero (div_ne_zero (Nat.cast_ne_zero.mpr (by omega))
      (Nat.cast_ne_zero.mpr hs.ne'))
    exact pow_ne_zero _ (inv_ne_zero (Finset.prod_ne_zero_iff.mpr
      (fun i _ => c.originalResponseClass_ne_zero P hB hmax (word i))))
  have hlast := hfull ▸ mul_ne_zero hunit hshort
  have hcycle : (Subtype.val ∘ word) =
      finiteWordCycle (n := r * (b - a)) (c.originalInternalResidue P) hperiod :=
    c.originalResponseClassWord_val P (r * (b - a)) hperiod
  rw [hcycle, ← heq] at hshort hlast
  have hbword : k * (b - a) + s = b := hbshape.symm
  rw [hbword] at hshort hlast
  dsimp only
  refine ⟨hperiod, ?_, ?_⟩
  · rw [← finiteWord_windowDefect_congr (c.originalInternalResidue P) Subtype.val
      (c.originalResponseClassExponent P W a b) b (r * s) rfl hlen hperiod hperiod]
    exact hshort
  · have hlastEq : lastWindowDefect (finiteWordCycle (c.originalInternalResidue P) hperiod)
        Subtype.val (c.originalResponseClassExponent P W a b) b (k * (r * (b - a)) + r * s) =
      lastWindowDefect (finiteWordCycle (c.originalInternalResidue P) hperiod)
        Subtype.val (c.originalResponseClassExponent P W a b) b (r * b) := by
      unfold lastWindowDefect
      rw [hlen]
    rw [← hlastEq]
    exact hlast

end SkewCornerDescent.Matrix.SelectedCoordinate
