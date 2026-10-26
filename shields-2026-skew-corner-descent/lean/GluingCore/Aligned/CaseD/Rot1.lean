/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Rot1.lean`. -/
import GluingCore.Aligned.CaseD.Rot0

/-!
# Aligned marks, case (d): rotation of the lower mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, case (c) "by rotation").

The rotation of the lower mark of `V` is the lower mark of `rotate V`:
`(alD_lowerMark V a θ).rotate = alD_lowerMark (rotate V) a θ` (`alD_lowerMark_rotate`).

Sorry-free.
-/

namespace GluingCore

section Rot1

variable {V : Diagram} {a θ : ℤ}

theorem alD_Z_rotate_W : rotate (translate (alD_z a θ) (alD_Z V a θ)) = alD_Z (rotate V) a θ := by
  ext x
  simp only [mem_rotate, mem_translate, alD_Z, Finset.mem_filter]
  have e1 : -x - alD_z a θ + alD_z a θ = -x := by abel
  have e2 : -(x + alD_z a θ) = -x - alD_z a θ := by abel
  rw [e1, e2]
  tauto

theorem alD_mark_rotate (cs : AttachCase) :
    (alD_mark V a θ cs).rotate = alD_mark (rotate V) a θ cs.rotate := by
  unfold MarkedInner.rotate alD_mark
  simp only [MarkedInner.upper]
  congr 1
  exact alD_Z_rotate_W

theorem alD_case_rotate :
    alD_case (rotate V) a θ = (alD_case V a θ).rotate := by
  have h := alD_mark_rotate (V := V) (a := a) (θ := θ) .a
  have eLH : (alD_mark (rotate V) a θ .a).LowerH ↔ (alD_mark V a θ .a).UpperH := by
    have : alD_mark (rotate V) a θ .a = (alD_mark V a θ .a).rotate := by
      rw [h]; rfl
    rw [this, MarkedInner.lowerH_rotate]
  have eUH : (alD_mark (rotate V) a θ .a).UpperH ↔ (alD_mark V a θ .a).LowerH := by
    have : alD_mark (rotate V) a θ .a = (alD_mark V a θ .a).rotate := by
      rw [h]; rfl
    rw [this, MarkedInner.upperH_rotate]
  unfold alD_case
  by_cases h1 : (alD_mark V a θ .a).LowerH <;> by_cases h2 : (alD_mark V a θ .a).UpperH <;>
    simp [eLH, eUH, h1, h2, AttachCase.rotate]

theorem alD_lowerMark_rotate :
    (alD_lowerMark V a θ).rotate = alD_lowerMark (rotate V) a θ := by
  unfold alD_lowerMark
  rw [alD_mark_rotate, alD_case_rotate]

end Rot1

end GluingCore
