-- [TODO-COPIED] from skew-factor-gluing/lean/SkewGluing/Invariance.lean
import SkewBase.Copied.Composition

/-!
# Composition with a translated outer

The translation behavior of the composite `ω.compose D` under translation of the outer `D`
(`MarkedInner.outerShift`, `MarkedInner.origin_translate_outer`,
`MarkedInner.sameRibbon_translate_outer`, `MarkedInner.compose_translate_outer`), as in
`eq:gluing-offsets`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

/-- The vector by which `ω.compose D` moves when the outer `D` is translated by `u`, read off
`eq:gluing-offsets`: `c(u) v + u₁ e`, `c(u) v - u₁ e`, `c(u) v`, `c(u) v` in cases (a)–(d)
(the offsets of the mixed cases involve `ℓ_k` and `h_k`, which move with the outer). -/
def outerShift (ω : MarkedInner) (u : ℤ × ℤ) : ℤ × ℤ :=
  match ω.case with
  | .a => content u • ω.v + u.1 • eCell
  | .b => content u • ω.v - u.1 • eCell
  | .c => content u • ω.v
  | .d => content u • ω.v

theorem origin_translate_outer {D : Diagram} {d : ℤ × ℤ} (hd : d ∈ D) (u : ℤ × ℤ)
    (ω : MarkedInner) :
    ω.origin (SkewGluing.translate u D) (d + u) = ω.origin D d + ω.outerShift u := by
  have hk : content d ∈ contents D := content_mem_contents hd
  have hc : content (d + u) = content d + content u := content_add d u
  unfold origin outerShift
  cases ω.case
  · simp only [hc, add_smul, Prod.fst_add]; abel
  · simp only [hc, add_smul, Prod.fst_add]; abel
  · simp only [hc, diagLo_translate u _ hk, add_smul, Prod.fst_add]
    have e : (d.1 + u.1 - (diagLo D (content d) + u.1)) = d.1 - diagLo D (content d) := by ring
    rw [e]; abel
  · simp only [hc, diagHi_translate u _ hk, add_smul, Prod.fst_add]
    have e : (diagHi D (content d) + u.1 - (d.1 + u.1)) = diagHi D (content d) - d.1 := by ring
    rw [e]; abel

theorem sameRibbon_translate_outer {D : Diagram} {d : ℤ × ℤ} (hd : d ∈ D) (u : ℤ × ℤ)
    (ω : MarkedInner) :
    ω.SameRibbon (SkewGluing.translate u D) (d + u) ↔ ω.SameRibbon D d := by
  have hk : content d ∈ contents D := content_mem_contents hd
  have hc : content (d + u) = content d + content u := content_add d u
  have hmem : ((d + u).1 - 1, (d + u).2) ∈ SkewGluing.translate u D ↔ (d.1 - 1, d.2) ∈ D := by
    rw [mem_translate]
    have e : ((d + u).1 - 1, (d + u).2) - u = (d.1 - 1, d.2) := by
      ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
    rw [e]
  have hk1 : (d.1 - 1, d.2) ∈ D → content d + 1 ∈ contents D := fun h => by
    have := content_mem_contents h
    have e : content (d.1 - 1, d.2) = content d + 1 := by simp only [content]; ring
    rwa [e] at this
  have e1 : content d + content u + 1 = (content d + 1) + content u := by ring
  unfold SameRibbon
  rw [hc]
  cases hcs : ω.case
  · simp only [hmem, and_false]
  · simp only [hmem, and_false]
  · dsimp only
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := hmem.mp h1
      refine ⟨h1', ?_⟩
      rw [diagLo_translate u _ hk, e1, diagLo_translate u _ (hk1 h1')] at h2
      simp only [Prod.fst_add] at h2
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨hmem.mpr h1, ?_⟩
      rw [diagLo_translate u _ hk, e1, diagLo_translate u _ (hk1 h1)]
      simp only [Prod.fst_add]
      omega
  · dsimp only
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := hmem.mp h1
      refine ⟨h1', ?_⟩
      rw [diagHi_translate u _ hk, e1, diagHi_translate u _ (hk1 h1')] at h2
      simp only [Prod.fst_add] at h2
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨hmem.mpr h1, ?_⟩
      rw [diagHi_translate u _ hk, e1, diagHi_translate u _ (hk1 h1)]
      simp only [Prod.fst_add]
      omega

/-- **Composition with a translated outer.**  For a nonempty outer `D`, `ω.compose (translate u D)`
is the translate of `ω.compose D` by `ω.outerShift u`. -/
theorem compose_translate_outer (u : ℤ × ℤ) {D : Diagram} (hD : D.Nonempty) (ω : MarkedInner) :
    ω.compose (SkewGluing.translate u D) =
      SkewGluing.translate (ω.outerShift u) (ω.compose D) := by
  have hD' : (SkewGluing.translate u D).Nonempty := hD.image _
  have reindex : ∀ P : ℤ × ℤ → Prop,
      (∃ d ∈ SkewGluing.translate u D, P d) ↔ ∃ d ∈ D, P (d + u) := by
    intro P
    constructor
    · rintro ⟨d', hd', hP⟩
      exact ⟨d' - u, mem_translate.mp hd', by simpa using hP⟩
    · rintro ⟨d, hd, hP⟩
      exact ⟨d + u, mem_translate.mpr (by simpa using hd), hP⟩
  ext x
  rw [mem_translate, mem_compose hD', mem_compose hD, reindex, reindex]
  apply or_congr
  · refine exists_congr fun d => and_congr_right fun hd => ?_
    rw [origin_translate_outer hd, mem_translate, mem_translate]
    have e : x - (ω.origin D d + ω.outerShift u) = x - ω.outerShift u - ω.origin D d := by abel
    rw [e]
  · refine exists_congr fun d => and_congr_right fun hd => ?_
    rw [sameRibbon_translate_outer hd, origin_translate_outer hd, mem_translate, mem_translate]
    have e : x - (ω.origin D d + ω.outerShift u + ω.supplementalShift) =
        x - ω.outerShift u - (ω.origin D d + ω.supplementalShift) := by abel
    rw [e]

end MarkedInner

end SkewGluing
