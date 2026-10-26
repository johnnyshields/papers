/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadIdentity
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadBridge
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadExtend

/-!
# The leading block over a generic letter family

`leadMatOf h`, `wOf h`, `vOf h`, `topRowOf h` and `surviveOf h` are the objects of
`HeadIdentity.lean` over an arbitrary commutative ring with letters `h`; `survive` is
`surviveOf` at the physical letters, and ring maps commute with `surviveOf`.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Matrix

variable {n p e : ℕ} {L : Type*} [CommRing L]

section Gen

variable (B : BetaDiagram (n + 1)) (hpe : p + e + 1 ≤ n) (h : ℕ → L)

/-- The leading block over the letters `h`. -/
def leadMatOf : Matrix (Fin p ⊕ Fin (e + 1)) (Fin p ⊕ Fin (e + 1)) L :=
  Matrix.of fun a b => letterOf h (leadRow B hpe a - leadCol B hpe b)

/-- The row `w_x`. -/
def wOf (x : ℤ) : Fin p ⊕ Fin (e + 1) → L := fun a => letterOf h (x - leadCol B hpe a)

/-- The column `v_x`. -/
def vOf (x : ℤ) : Fin p ⊕ Fin (e + 1) → L := fun a => letterOf h (leadRow B hpe a - x)

/-- The top row `τ`. -/
def topRowOf : Fin p ⊕ Fin (e + 1) → L := fun a => letterOf h (B.row 0 - leadCol B hpe a)

/-- `survive` over the letters `h`. -/
def surviveOf (x : ℤ) : L :=
  (wOf B hpe h x ⬝ᵥ ((leadMatOf B hpe h).adjugate *ᵥ Pi.single pivot 1)) *
    (letterOf h (B.row 0 - x) * (leadMatOf B hpe h).det -
      topRowOf B hpe h ⬝ᵥ ((leadMatOf B hpe h).adjugate *ᵥ vOf B hpe h x))

theorem letterOf_complete (z : ℤ) :
    letterOf (fun k : ℕ => (complete (k : ℤ) : CompleteRing)) z = complete z := by
  unfold letterOf
  split_ifs with hz
  · exact (complete_of_neg hz).symm
  · show complete ((z.toNat : ℕ) : ℤ) = complete z
    rw [Int.toNat_of_nonneg (by omega)]

theorem survive_eq_surviveOf (x : ℤ) :
    survive B hpe x = surviveOf B hpe (fun k : ℕ => (complete (k : ℤ) : CompleteRing)) x := by
  have hM : leadMatOf B hpe (fun k : ℕ => (complete (k : ℤ) : CompleteRing)) = leadMat B hpe := by
    refine Matrix.ext fun a b => ?_
    simp only [leadMatOf, leadMat, Matrix.of_apply, letterOf_complete]
  have hw : wVec B hpe x = wOf B hpe (fun k : ℕ => (complete (k : ℤ) : CompleteRing)) x :=
    funext fun a => (letterOf_complete _).symm
  have hv : (fun a => complete (leadRow B hpe a - x)) =
      vOf B hpe (fun k : ℕ => (complete (k : ℤ) : CompleteRing)) x :=
    funext fun a => (letterOf_complete _).symm
  have ht : topRowVec B hpe =
      topRowOf B hpe (fun k : ℕ => (complete (k : ℤ) : CompleteRing)) :=
    funext fun a => (letterOf_complete _).symm
  unfold survive surviveOf uVec
  rw [hM, ← hw, ← hv, ← ht, letterOf_complete]

theorem map_surviveOf {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (h : ℕ → R)
    (x : ℤ) :
    f (surviveOf B hpe h x) = surviveOf B hpe (fun k => f (h k)) x := by
  have hl : ∀ z : ℤ, f (letterOf h z) = letterOf (fun k => f (h k)) z := by
    intro z; unfold letterOf; split_ifs <;> simp
  have hM : (leadMatOf B hpe h).map f = leadMatOf B hpe (fun k => f (h k)) := by
    refine Matrix.ext fun a b => ?_
    simp [leadMatOf, hl]
  have hadj : (leadMatOf B hpe h).adjugate.map f = (leadMatOf B hpe (fun k => f (h k))).adjugate := by
    rw [← hM]
    have := RingHom.map_adjugate f (leadMatOf B hpe h)
    simpa [RingHom.mapMatrix_apply] using this
  have hdet : f (leadMatOf B hpe h).det = (leadMatOf B hpe (fun k => f (h k))).det := by
    rw [← hM, RingHom.map_det]; rfl
  have hw : f ∘ wOf B hpe h x = wOf B hpe (fun k => f (h k)) x := funext fun a => hl _
  have hv : f ∘ vOf B hpe h x = vOf B hpe (fun k => f (h k)) x := funext fun a => hl _
  have ht : f ∘ topRowOf B hpe h = topRowOf B hpe (fun k => f (h k)) := funext fun a => hl _
  have he : f ∘ (Pi.single pivot 1 : Fin p ⊕ Fin (e + 1) → R) =
      Pi.single pivot 1 := by
    funext a; by_cases ha : a = pivot <;> simp [Pi.single_apply, ha]
  have hmv : ∀ y : Fin p ⊕ Fin (e + 1) → R, f ∘ ((leadMatOf B hpe h).adjugate *ᵥ y) =
      (leadMatOf B hpe (fun k => f (h k))).adjugate *ᵥ (f ∘ y) := fun y => by
    rw [← hadj]; exact funext fun i => RingHom.map_mulVec f _ _ i
  unfold surviveOf
  rw [map_mul, map_sub, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct, hw, ht, hmv,
    hmv, hv, he, hdet, hl]

end Gen

end SkewCoframeRigidity.UnitRestoration
