/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/Local/ComposeRotate.lean
import SkewMarkedFactor.Gluing.Local.ComposeD

/-!
# Rotation of a composite

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (2),
case (c) "by rotation").

For a case-(c) mark `ω`, the rotation of `D ∘_ω E` is `D* ∘_{ω*} E*`, where `ω*` has case (d).
This transfers the case-(d) analysis to case (c).

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem rotate_case_d (hc : ω.case = .c) : ω.rotate.case = .d := by
  change ω.case.rotate = _
  rw [hc]; rfl

theorem origin_rotate_c (hc : ω.case = .c) (D : Diagram) (d : ℤ × ℤ) :
    ω.rotate.origin (SkewMarkedFactor.Gluing.rotate D) (-d) = -(ω.origin D d) := by
  have hc' := rotate_case_d hc
  unfold origin
  rw [hc', hc]
  have hv : ω.rotate.v = ω.v := rfl
  simp only [hv]
  have e1 : content (-d) = -content d := by simp [content]; ring
  rw [e1, diagHi_rotate]
  ext
  · simp [content, eCell]; ring
  · simp [content, eCell]; ring


theorem sameRibbon_rotate_c (hc : ω.case = .c) (D : Diagram) (d : ℤ × ℤ) :
    (d ∈ D ∧ ω.SameRibbon D d) ↔
      (-(d.1 - 1, d.2) ∈ SkewMarkedFactor.Gluing.rotate D ∧
        ω.rotate.SameRibbon (SkewMarkedFactor.Gluing.rotate D) (-(d.1 - 1, d.2))) := by
  have hc' := rotate_case_d hc
  obtain ⟨i, c⟩ := d
  simp only [SameRibbon, hc, hc', mem_rotate]
  have e1 : content (-(i - 1, c)) = -(c - i) - 1 := by simp [content]; ring
  have e2 : -(c - i) - 1 + 1 = -(c - i) := by ring
  have e3 : -(-(c - i) - 1) = c - i + 1 := by ring
  have e4 : content (i, c) = c - i := rfl
  simp only [e1, e2, e4, diagHi_rotate, neg_neg, e3, Prod.fst_neg, Prod.snd_neg]
  constructor
  · rintro ⟨hd, hn, hr⟩
    refine ⟨hn, ?_, ?_⟩
    · convert hd using 1
      simp
    · omega
  · rintro ⟨hn, hd, hr⟩
    refine ⟨?_, hn, ?_⟩
    · convert hd using 1
      simp
    · omega


theorem origin_north_c (hc : ω.case = .c) (D : Diagram) (d : ℤ × ℤ) (hr : ω.SameRibbon D d) :
    ω.origin D (d.1 - 1, d.2) = ω.origin D d + ω.v := by
  obtain ⟨i, c⟩ := d
  have hr2 := hr.2
  simp only [hc, content] at hr2
  have hdl : diagLo D (c - i + 1) = diagLo D (c - i) - 1 := by omega
  unfold origin
  rw [hc]
  have e1 : content (i - 1, c) = c - i + 1 := by simp [content]; ring
  have e2 : content (i, c) = c - i := rfl
  simp only [e1, e2, hdl]
  ext
  · simp [eCell]; ring
  · simp [eCell]; ring

theorem compose_rotate_c (hc : ω.case = .c) (hD : D.Nonempty) :
    ω.compose D = SkewMarkedFactor.Gluing.rotate (ω.rotate.compose
      (SkewMarkedFactor.Gluing.rotate D)) := by
  have hc' := rotate_case_d hc
  have hD' : (SkewMarkedFactor.Gluing.rotate D).Nonempty := hD.image _
  have hsh : ω.rotate.supplementalShift = -eCell := supplementalShift_d hc'
  have hsh' : ω.supplementalShift = eCell := by simp [supplementalShift, hc]
  ext x
  rw [mem_rotate, mem_compose hD, mem_compose hD']
  constructor
  · rintro (⟨d, hd, hx⟩ | ⟨d, hd, hr, hx⟩)
    · left
      refine ⟨-d, mem_rotate.mpr (by simpa using hd), ?_⟩
      rw [origin_rotate_c hc]
      rw [mem_translate] at hx ⊢
      change -x - -(ω.origin D d) ∈ SkewMarkedFactor.Gluing.rotate ω.E
      rw [mem_rotate]
      have : -(-x - -(ω.origin D d)) = x - ω.origin D d := by abel
      rwa [this]
    · right
      have hs := (sameRibbon_rotate_c hc D d).mp ⟨hd, hr⟩
      refine ⟨-(d.1 - 1, d.2), hs.1, hs.2, ?_⟩
      rw [origin_rotate_c hc, origin_north_c hc D d hr, hsh]
      rw [hsh'] at hx
      rw [mem_translate] at hx ⊢
      change -x - (-(ω.origin D d + ω.v) + -eCell) ∈ translate ω.v
        (SkewMarkedFactor.Gluing.rotate ω.upper)
      rw [mem_translate, mem_rotate]
      have : -(-x - (-(ω.origin D d + ω.v) + -eCell) - ω.v) = x - (ω.origin D d + eCell) := by
        abel
      rwa [this]
  · rintro (⟨d', hd', hx⟩ | ⟨d', hd', hr, hx⟩)
    · left
      refine ⟨-d', mem_rotate.mp hd', ?_⟩
      have ho := origin_rotate_c hc D (-d')
      rw [neg_neg] at ho
      rw [ho, mem_translate] at hx
      rw [mem_translate]
      change -x - -(ω.origin D (-d')) ∈ SkewMarkedFactor.Gluing.rotate ω.E at hx
      rw [mem_rotate] at hx
      have : -(-x - -(ω.origin D (-d'))) = x - ω.origin D (-d') := by abel
      rwa [this] at hx
    · right
      obtain ⟨d, hdd⟩ : ∃ d : ℤ × ℤ, -(d.1 - 1, d.2) = d' :=
        ⟨(1 - d'.1, -d'.2), by ext <;> simp⟩
      subst hdd
      have hs := (sameRibbon_rotate_c hc D d).mpr ⟨hd', hr⟩
      refine ⟨d, hs.1, hs.2, ?_⟩
      have ho := origin_rotate_c hc D (d.1 - 1, d.2)
      rw [origin_north_c hc D d hs.2] at ho
      rw [ho, hsh] at hx
      rw [hsh']
      rw [mem_translate] at hx ⊢
      change -x - (-(ω.origin D d + ω.v) + -eCell) ∈ translate ω.v
        (SkewMarkedFactor.Gluing.rotate ω.upper)
        at hx
      rw [mem_translate, mem_rotate] at hx
      have : -(-x - (-(ω.origin D d + ω.v) + -eCell) - ω.v) = x - (ω.origin D d + eCell) := by
        abel
      rwa [this] at hx


/-- **`lem:gluing-local` (3), connectedness, case (c)**, by rotation to case (d). -/
theorem IsLegalNonempty.isConnectedSkew_compose_c (h : ω.IsLegalNonempty)
    (hD : IsConnectedSkew D) (hc : ω.case = .c) : IsConnectedSkew (ω.compose D) := by
  rw [compose_rotate_c hc hD.2.1]
  exact isConnectedSkew_rotate
    (h.rotate.isConnectedSkew_compose_d (isConnectedSkew_rotate hD) (rotate_case_d hc))

/-- **`lem:gluing-local` (3), connectedness, nonempty marks.**  For a legal mark with a nonempty
copy and a connected outer, `D ∘_ω E` is a connected skew diagram. -/
theorem IsLegalNonempty.isConnectedSkew_compose (h : ω.IsLegalNonempty)
    (hD : IsConnectedSkew D) : IsConnectedSkew (ω.compose D) := by
  by_cases hmix : ω.case.IsMixed
  · rcases hmix with hc | hc
    · exact h.isConnectedSkew_compose_c hD hc
    · exact h.isConnectedSkew_compose_d hD hc
  · exact h.isConnectedSkew_compose_ord hD hmix

end MarkedInner

end SkewMarkedFactor.Gluing
