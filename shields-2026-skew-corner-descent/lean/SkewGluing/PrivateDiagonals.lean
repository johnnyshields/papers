/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.MarkLocality

/-!
# Private diagonals of a legal mark

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`sec:marks`, `eq:local-properties`).

The first and last private diagonals are singletons. The removal's diagonal criterion and
condition IV exclude the first possible thick private diagonal.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- The first private diagonal of a legal nonempty mark has at most one cell. -/
theorem IsLegal.private_lower_subsingleton (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {a b : ℤ × ℤ} (ha : a ∈ ω.E) (hb : b ∈ ω.E)
    (hca : content a = minContent ω.E + ω.width)
    (hcb : content b = content a) : a = b := by
  let k : ℤ := minContent ω.E + ω.width
  have hn := h.isNonemptyMark hW
  have hwq := h.2.2.1.2
  have hR := isConnectedSkew_iff_diagonal.mp h.2.2.2.1.1
  have hnotW : ∀ x, content x = k → x ∉ ω.W := by
    intro x hx hxW
    have := (hn.content_W h.1.1 hxW).2
    omega
  have hnotU : ∀ x, content x ≤ k → x ∉ ω.upper := by
    intro x hx hxU
    have := (hn.content_upper h.1.1 hxU).1
    omega
  have haR : a ∈ ω.E \ ω.W := Finset.mem_sdiff.mpr ⟨ha, hnotW a hca⟩
  have hbR : b ∈ ω.E \ ω.W := Finset.mem_sdiff.mpr ⟨hb, hnotW b (hcb.trans hca)⟩
  have hk : k ∈ contents (ω.E \ ω.W) := by
    simpa only [hca] using content_mem_contents haR
  by_cases hprev : k - 1 ∈ contents (ω.E \ ω.W)
  · obtain ⟨y, hyR, hcy⟩ := exists_cell_of_mem_contents hprev
    obtain ⟨hyE, hyW⟩ := Finset.mem_sdiff.mp hyR
    have hyO : y ∈ ω.middle := mem_middle.mpr ⟨hyE, hyW, hnotU y (by omega)⟩
    have hsingle : ∀ z ∈ ω.E \ ω.W, content z = k - 1 → z = y := by
      intro z hz hcz
      obtain ⟨hzE, hzW⟩ := Finset.mem_sdiff.mp hz
      exact h.middle_subsingleton hW
        (mem_middle.mpr ⟨hzE, hzW, hnotU z (by omega)⟩) hyO (by omega)
        (Or.inl (by omega))
    have hlo : diagLo (ω.E \ ω.W) (k - 1) = y.1 := by
      apply diagLo_eq_of
      · rw [← cell_eq_of_content hcy]
        exact hyR
      · intro i hi
        have := congrArg Prod.fst (hsingle (i, i + (k - 1)) hi (by simp [content]))
        omega
    have hhi : diagHi (ω.E \ ω.W) (k - 1) = y.1 := by
      apply diagHi_eq_of
      · rw [← cell_eq_of_content hcy]
        exact hyR
      · intro i hi
        have := congrArg Prod.fst (hsingle (i, i + (k - 1)) hi (by simp [content]))
        omega
    have hstep := hR.2.2.2.1 k hk hprev
    simp only [bitA, bitB, hlo, hhi, Finset.mem_insert, Finset.mem_singleton] at hstep
    have ha1 := diagLo_le haR hca
    have ha2 := le_diagHi haR hca
    have hb1 := diagLo_le hbR (hcb.trans hca)
    have hb2 := le_diagHi hbR (hcb.trans hca)
    change diagLo (ω.E \ ω.W) k ≤ a.1 at ha1
    change a.1 ≤ diagHi (ω.E \ ω.W) k at ha2
    change diagLo (ω.E \ ω.W) k ≤ b.1 at hb1
    change b.1 ≤ diagHi (ω.E \ ω.W) k at hb2
    by_contra hab
    have hrows : a.1 ≠ b.1 := by
      intro heq
      apply hab
      apply Prod.ext heq
      simp only [content] at hcb
      omega
    have hends : diagLo (ω.E \ ω.W) k = y.1 - 1 ∧
        diagHi (ω.E \ ω.W) k = y.1 := by omega
    let x : ℤ × ℤ := (y.1 - 1, y.1 - 1 + k)
    have hxR : x ∈ ω.E \ ω.W := hR.mem_iff.mpr ⟨hk, by omega, by omega⟩
    have hxeR : x + eCell ∈ ω.E \ ω.W := by
      have hyNext : (y.1, y.1 + k) ∈ ω.E \ ω.W :=
        hR.mem_iff.mpr ⟨hk, by omega, by omega⟩
      convert hyNext using 1
      simp [x, eCell]
      ring
    have hxO : x ∈ ω.middle := mem_middle.mpr
      ⟨(Finset.mem_sdiff.mp hxR).1, (Finset.mem_sdiff.mp hxR).2,
        hnotU x (by simp [x, content])⟩
    have hxeO : x + eCell ∈ ω.middle := mem_middle.mpr
      ⟨(Finset.mem_sdiff.mp hxeR).1, (Finset.mem_sdiff.mp hxeR).2,
        hnotU _ (by simp [x, content, eCell]; omega)⟩
    obtain ⟨z, hzW, hcz⟩ := hn.exists_cell_W h.1.1 (d := k - 1)
      (by
        have hs := span_eq_of_isConnectedSkew hn.2.1
        have hm := minContent_le (maxContent_mem hW)
        change (ω.width : ℤ) = _ at hs
        omega) (by omega)
    have hzE := hn.2.2.1 hzW
    have hyz : y ≠ z := fun heq => hyW (heq ▸ hzW)
    have hne : y.1 ≠ z.1 := by
      intro heq
      apply hyz
      apply Prod.ext heq
      simp only [content] at hcy hcz
      omega
    have hgap : z.1 = y.1 - 1 ∨ z.1 = y.1 + 1 := by
      by_contra hgap
      have hsk := h.1.1.1
      have hi : (min y.1 z.1 + 1, min y.1 z.1 + 1 + (k - 1)) ∈ ω.E := by
        rcases le_total y.1 z.1 with hle | hle
        · rw [min_eq_left hle]
          exact hsk.mem hyE hzE (by simp only [content] at hcy hcz; omega)
            (by simp only [content] at hcy hcz; omega) (by omega) (by omega)
            (by simp only [content] at hcy hcz; omega)
            (by simp only [content] at hcy hcz; omega)
        · rw [min_eq_right hle]
          exact hsk.mem hzE hyE (by simp only [content] at hcy hcz; omega)
            (by simp only [content] at hcy hcz; omega) (by omega) (by omega)
            (by simp only [content] at hcy hcz; omega)
            (by simp only [content] at hcy hcz; omega)
      have hWshape := isConnectedSkew_iff_diagonal.mp hn.2.1
      have hlast := hWshape.2.2.2.2 (k - 1)
        (hcz ▸ content_mem_contents hzW) (Or.inr (by
          intro hh
          have := le_maxContent hh
          have := (hn.W_range h.1.1).2
          omega))
      have hiW : (min y.1 z.1 + 1, min y.1 z.1 + 1 + (k - 1)) ∉ ω.W := by
        intro hiW
        have h1 := diagLo_le (k := k - 1) hiW (by omega)
        have h2 := le_diagHi (k := k - 1) hiW (by omega)
        have hz1 := diagLo_le hzW hcz
        have hz2 := le_diagHi hzW hcz
        omega
      have heq := hsingle _ (Finset.mem_sdiff.mpr ⟨hi, hiW⟩) (by simp [content])
      have := congrArg Prod.fst heq
      omega
    rcases hgap with hgap | hgap
    · apply h.no_hat_adjacent hxO hxeO (y := z)
      · rw [cellAdj_iff]
        simp only [x, content] at hcy hcz ⊢
        omega
      · exact Or.inl ⟨hzW, by
          convert hyE using 1
          ext <;> simp only [eCell, content, Prod.fst_add, Prod.snd_add] at hcy hcz ⊢ <;>
            omega⟩
    · apply h.no_hat_adjacent hxO hxeO (y := y)
      · rw [cellAdj_iff]
        simp only [x, content] at hcy hcz ⊢
        omega
      · exact Or.inr ⟨by
          convert hzW using 1
          ext <;> simp only [eCell, content, Prod.fst_add, Prod.snd_add] at hcy hcz ⊢ <;>
            omega, hyE⟩
  · have heq := hR.2.2.2.2 k hk (Or.inl hprev)
    have ha1 := diagLo_le haR hca
    have ha2 := le_diagHi haR hca
    have hb1 := diagLo_le hbR (hcb.trans hca)
    have hb2 := le_diagHi hbR (hcb.trans hca)
    change diagLo (ω.E \ ω.W) k ≤ a.1 at ha1
    change a.1 ≤ diagHi (ω.E \ ω.W) k at ha2
    change diagLo (ω.E \ ω.W) k ≤ b.1 at hb1
    change b.1 ≤ diagHi (ω.E \ ω.W) k at hb2
    apply Prod.ext
    · omega
    · simp only [content] at hca hcb
      omega

/-- The last private diagonal is the rotation of the first private diagonal. -/
theorem IsLegal.private_upper_subsingleton (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {a b : ℤ × ℤ} (ha : a ∈ ω.E) (hb : b ∈ ω.E)
    (hca : content a = minContent ω.E + ω.period - 1)
    (hcb : content b = content a) : a = b := by
  have hn := h.isNonemptyMark hW
  have hmax := hn.maxContent_E h.1.1
  have hmin := minContent_rotate h.1.1.2.1
  have ha' : -a ∈ ω.rotate.E := by
    rw [show ω.rotate.E = SkewGluing.rotate ω.E from rfl, mem_rotate, neg_neg]
    exact ha
  have hb' : -b ∈ ω.rotate.E := by
    rw [show ω.rotate.E = SkewGluing.rotate ω.E from rfl, mem_rotate, neg_neg]
    exact hb
  apply neg_injective
  apply (isLegal_rotate h).private_lower_subsingleton (rotate_W_nonempty hW) ha' hb'
  · rw [show ω.rotate.E = SkewGluing.rotate ω.E from rfl, hmin, width_rotate]
    simp only [content, Prod.fst_neg, Prod.snd_neg] at hca ⊢
    omega
  · simp only [content, Prod.fst_neg, Prod.snd_neg] at hcb ⊢
    omega

/-- The first private diagonal exists and is a singleton, not merely a subsingleton. -/
theorem IsLegal.private_lower_eq_singleton (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ∃ z, ω.E.filter (fun x => content x = minContent ω.E + ω.width) = {z} := by
  have hn := h.isNonemptyMark hW
  have hm := hn.maxContent_E h.1.1
  have hwq := h.2.2.1.2
  obtain ⟨z, hz, hcz⟩ := exists_cell_of_connectedSkew h.1.1
    (d := minContent ω.E + ω.width) (by omega) (by omega)
  refine ⟨z, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hc⟩
    exact h.private_lower_subsingleton hW hx hz hc (by omega)
  · rintro rfl
    exact ⟨hz, hcz⟩

/-- The last private diagonal exists and is a singleton. -/
theorem IsLegal.private_upper_eq_singleton (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ∃ z, ω.E.filter (fun x => content x = minContent ω.E + ω.period - 1) = {z} := by
  have hn := h.isNonemptyMark hW
  have hm := hn.maxContent_E h.1.1
  have hwq := h.2.2.1.2
  obtain ⟨z, hz, hcz⟩ := exists_cell_of_connectedSkew h.1.1
    (d := minContent ω.E + ω.period - 1) (by omega) (by omega)
  refine ⟨z, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hc⟩
    exact h.private_upper_subsingleton hW hx hz hc (by omega)
  · rintro rfl
    exact ⟨hz, hcz⟩

end SkewGluing.MarkedInner
