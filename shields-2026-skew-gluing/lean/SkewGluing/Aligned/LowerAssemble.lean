import SkewGluing.Aligned.LowerLegal
import SkewGluing.Invariance
import SkewGluing.Aligned.LowerCase

/-!
# The legal lower mark of an ordinary chart: assembly

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, ordinary case, `b > 0`).

The rotation of a `LowerChart`, the upper attachment of the lower mark (from the lower one by
rotation), the attachments, maximality, and legality of `muOf V (zOf ω η a) (lowerCase ω η)`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram} {a : ℤ}

theorem isMixed_rotate_iff (ω : MarkedInner) : ω.rotate.case.IsMixed ↔ ω.case.IsMixed := by
  unfold AttachCase.IsMixed
  change ω.case.rotate = AttachCase.c ∨ ω.case.rotate = AttachCase.d ↔ _
  cases ω.case <;> simp [AttachCase.rotate]

theorem ordSign_rotate (hω : ¬ ω.case.IsMixed) : ω.rotate.ordSign = ω.ordSign := by
  unfold AttachCase.IsMixed at hω
  unfold ordSign
  change (if ω.case.rotate = AttachCase.b then (-1 : ℤ) else 1) = _
  cases hh : ω.case <;> simp_all [AttachCase.rotate]

theorem zOf_rotate (hω : ¬ ω.case.IsMixed) :
    zOf ω.rotate η.rotate a = zOf ω η a := by
  have h1 := ordSign_rotate hω
  unfold zOf
  rw [h1]
  rfl

/-- Rotating a chart gives a chart with the same displacement `z`. -/
theorem LowerChart.rotate (C : LowerChart ω η V a) :
    LowerChart ω.rotate η.rotate (SkewGluing.rotate V) a where
  hω := isLegal_rotate C.hω
  hord := fun h => C.hord ((isMixed_rotate_iff ω).mp h)
  hV := isConnectedSkew_rotate C.hV
  hη := isLegal_rotate C.hη
  hηord := fun h => C.hηord ((isMixed_rotate_iff η).mp h)
  hU := by
    have := rotate_compose C.hV.2.1 ω
    change SkewGluing.rotate η.E = _
    rw [C.hU, this]
  ha := C.ha
  hpos := by rw [span_rotate]; exact C.hpos

theorem lowerCase_rotate (hω : ¬ ω.case.IsMixed) (hη : ¬ η.case.IsMixed) :
    lowerCase ω.rotate η.rotate = lowerCase ω η := by
  unfold lowerCase
  rw [ordSign_rotate hω, ordSign_rotate hη]

theorem lowerCase_rotate_case (ω η : MarkedInner) :
    (lowerCase ω η).rotate = lowerCase ω η := by
  unfold lowerCase
  split_ifs <;> rfl

namespace LowerChart

variable (C : LowerChart ω η V a)
include C

theorem upperAttach :
    (η.ordSign = ω.ordSign → (muOf V (zOf ω η a) (lowerCase ω η)).UpperH) ∧
      (η.ordSign ≠ ω.ordSign → (muOf V (zOf ω η a) (lowerCase ω η)).UpperV) := by
  have h := C.rotate.lowerAttach
  have e1 : (muOf V (zOf ω η a) (lowerCase ω η)).rotate =
      muOf (SkewGluing.rotate V) (zOf ω.rotate η.rotate a) (lowerCase ω.rotate η.rotate) := by
    rw [muOf_rotate, lowerCase_rotate C.hord C.hηord, lowerCase_rotate_case,
      zOf_rotate C.hord]
  rw [ordSign_rotate C.hord, ordSign_rotate C.hηord] at h
  rw [← e1] at h
  rw [← lowerH_rotate, ← lowerV_rotate]
  exact h

theorem attachmentMatches :
    (muOf V (zOf ω η a) (lowerCase ω η)).AttachmentMatches := by
  have hl := C.lowerAttach
  have hu := C.upperAttach
  unfold AttachmentMatches
  have hcs : lowerCase ω η = .a ∨ lowerCase ω η = .b := by
    unfold lowerCase; split_ifs <;> simp
  have hcase : (muOf V (zOf ω η a) (lowerCase ω η)).case = lowerCase ω η := rfl
  rw [hcase]
  rcases hcs with h | h
  · have hs : η.ordSign = ω.ordSign := by
      by_contra hne
      unfold lowerCase at h
      rw [ite_cases_ne hne] at h
      exact absurd h (by simp)
    exact ⟨fun _ => ⟨hl.1 hs, hu.1 hs⟩, fun h' => absurd (h.symm.trans h') (by simp),
      fun h' => absurd (h.symm.trans h') (by simp), fun h' => absurd (h.symm.trans h') (by simp)⟩
  · have hs : η.ordSign ≠ ω.ordSign := by
      intro heq
      unfold lowerCase at h
      rw [ite_cases_eq heq] at h
      exact absurd h (by simp)
    exact ⟨fun h' => absurd (h.symm.trans h') (by simp), fun _ => ⟨hl.2 hs, hu.2 hs⟩,
      fun h' => absurd (h.symm.trans h') (by simp), fun h' => absurd (h.symm.trans h') (by simp)⟩

theorem isMaximal : (muOf V (zOf ω η a) (lowerCase ω η)).IsMaximal := by
  have G := C.glueData
  have hwf := G.isWellFormed_muOf (lowerCase ω η) C.attachmentMatches
  have hnon : (muOf V (zOf ω η a) (lowerCase ω η)).IsNonemptyMark := by
    rcases hwf.2 with h | h
    · exfalso
      have := h.1
      have hne := G.isConnectedSkew_lowerCopy.2.1
      exact hne.ne_empty this
    · exact h
  refine IsMaximalAtDisplacement.isMaximal hwf.1 hnon ?_
  intro W' hW' hlt hsk hc hsub
  have hW'V : W' ⊆ V := Finset.mem_powerset.mp hW'
  have hZ : W' ⊆ lowerCopy V (zOf ω η a) := by
    intro x hx
    rw [mem_lowerCopy]
    refine ⟨hW'V hx, ?_⟩
    have hm : x + zOf ω η a ∈ SkewGluing.translate (zOf ω η a) W' :=
      mem_translate.mpr (by simpa using hx)
    exact hsub hm
  exact hlt.2 hZ

theorem isLegal_lowerMark :
    (muOf V (zOf ω η a) (lowerCase ω η)).IsLegal := by
  have hz := zOf_rotate (η := η) (a := a) C.hord
  have G := C.glueData
  have G' := C.rotate.glueData
  rw [hz] at G'
  exact GlueData.isLegal_muOf G G' _ C.attachmentMatches C.isMaximal

end LowerChart

end MarkedInner

end SkewGluing
