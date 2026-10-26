/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/InnerFactor/Locality.lean`. -/
import GluingCore.Local

/-!
# Locality of composition

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`), via `eq:gluing-offsets` and the two windows of `lem:gluing-local` (3).

The cells of `D ∘_ω E` on the contents up to `c₀ + (K + 1) q - 1` depend only on the cells of
`D` on the contents up to `K` (`mem_compose_iff_of_prefix`); the cells on the contents from
`c₀ + J q + w` on depend only on the cells of `D` on the contents from `J` on, and move with
the outer when that part of the outer moves (`mem_compose_iff_of_shift`).

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω : MarkedInner}

theorem diagRows_congr {D D' : Diagram} {K : ℤ} (h : ∀ x, content x ≤ K → (x ∈ D ↔ x ∈ D'))
    {k : ℤ} (hk : k ≤ K) : diagRows D k = diagRows D' k := by
  ext i
  rw [mem_diagRows, mem_diagRows]
  exact h (i, i + k) (by simp only [content]; omega)

theorem diagLo_congr {D D' : Diagram} {K : ℤ} (h : ∀ x, content x ≤ K → (x ∈ D ↔ x ∈ D'))
    {k : ℤ} (hk : k ≤ K) : diagLo D k = diagLo D' k := by
  unfold diagLo
  rw [diagRows_congr h hk]

theorem diagHi_congr {D D' : Diagram} {K : ℤ} (h : ∀ x, content x ≤ K → (x ∈ D ↔ x ∈ D'))
    {k : ℤ} (hk : k ≤ K) : diagHi D k = diagHi D' k := by
  unfold diagHi
  rw [diagRows_congr h hk]

theorem origin_congr {D D' : Diagram} {d : ℤ × ℤ}
    (hlo : diagLo D (content d) = diagLo D' (content d))
    (hhi : diagHi D (content d) = diagHi D' (content d)) :
    ω.origin D d = ω.origin D' d := by
  unfold origin
  cases ω.case <;> simp [hlo, hhi]

theorem sameRibbon_congr {D D' : Diagram} {d : ℤ × ℤ}
    (hmem : (d.1 - 1, d.2) ∈ D ↔ (d.1 - 1, d.2) ∈ D')
    (hlo : diagLo D (content d) = diagLo D' (content d))
    (hhi : diagHi D (content d) = diagHi D' (content d))
    (hlo1 : diagLo D (content d + 1) = diagLo D' (content d + 1))
    (hhi1 : diagHi D (content d + 1) = diagHi D' (content d + 1)) :
    ω.SameRibbon D d ↔ ω.SameRibbon D' d := by
  unfold SameRibbon
  cases ω.case <;> simp [hmem, hlo, hhi, hlo1, hhi1]

theorem mem_compose_of_prefix_aux (hω : ω.IsLegal) {D D' : Diagram} (hD : D.Nonempty)
    (hD' : D'.Nonempty) {K : ℤ} (h : ∀ x, content x ≤ K → (x ∈ D ↔ x ∈ D')) {x : ℤ × ℤ}
    (hx : content x ≤ minContent ω.E + (K + 1) * ω.period - 1) (hxD : x ∈ ω.compose D) :
    x ∈ ω.compose D' := by
  have hq := hω.period_pos
  rw [mem_compose hD] at hxD
  rw [mem_compose hD']
  rcases hxD with ⟨d, hd, hxd⟩ | ⟨d, hd, hr, hxd⟩
  · have h1 := hω.copy_content (mem_translate.mp hxd)
    rw [content_sub, content_origin] at h1
    have hdK : content d ≤ K := by
      by_contra hn
      have := mul_le_mul_of_nonneg_right (show K + 1 ≤ content d by omega) hq.le
      nlinarith
    have hd' : d ∈ D' := (h d hdK).mp hd
    left
    refine ⟨d, hd', ?_⟩
    rw [← origin_congr (diagLo_congr h hdK) (diagHi_congr h hdK)]
    exact hxd
  · have h1 := hω.upper_content (mem_translate.mp hxd)
    rw [content_sub, content_add, content_origin, content_supplementalShift] at h1
    have hdK : content d + 1 ≤ K := by
      by_contra hn
      have := mul_le_mul_of_nonneg_right (show K ≤ content d by omega) hq.le
      nlinarith
    have hd' : d ∈ D' := (h d (by omega)).mp hd
    right
    have hn : content (d.1 - 1, d.2) = content d + 1 := by simp only [content]; ring
    have hmem : (d.1 - 1, d.2) ∈ D ↔ (d.1 - 1, d.2) ∈ D' := by
      have := h (d.1 - 1, d.2) (by omega)
      exact this
    have hrib := sameRibbon_congr (ω := ω) hmem (diagLo_congr h (by omega))
      (diagHi_congr h (by omega)) (diagLo_congr h hdK) (diagHi_congr h hdK)
    have ho := origin_congr (ω := ω) (diagLo_congr h (show content d ≤ K by omega))
      (diagHi_congr h (show content d ≤ K by omega))
    refine ⟨d, hd', hrib.mp hr, ?_⟩
    rw [← ho]
    exact hxd

/-- **Prefix locality.**  The cells of `D ∘_ω E` on the contents `≤ c₀ + (K + 1) q - 1` depend
only on the cells of `D` on the contents `≤ K`. -/
theorem mem_compose_iff_of_prefix (hω : ω.IsLegal) {D D' : Diagram} (hD : D.Nonempty)
    (hD' : D'.Nonempty) {K : ℤ} (h : ∀ x, content x ≤ K → (x ∈ D ↔ x ∈ D')) {x : ℤ × ℤ}
    (hx : content x ≤ minContent ω.E + (K + 1) * ω.period - 1) :
    x ∈ ω.compose D ↔ x ∈ ω.compose D' :=
  ⟨mem_compose_of_prefix_aux hω hD hD' h hx,
    mem_compose_of_prefix_aux hω hD' hD (fun x hx => (h x hx).symm) hx⟩

theorem mem_compose_of_shift_aux (hω : ω.IsLegal) {D' D : Diagram} (hD' : D'.Nonempty)
    (hD : D.Nonempty) {J : ℤ} {z T : ℤ × ℤ} (_hT : content T = content z * ω.period)
    (hmem : ∀ x, J ≤ content x → (x ∈ D' ↔ x + z ∈ D))
    (horig : ∀ d ∈ D', J ≤ content d → ω.origin D' d + T = ω.origin D (d + z))
    (hrib : ∀ d ∈ D', J ≤ content d → (ω.SameRibbon D' d ↔ ω.SameRibbon D (d + z)))
    {x : ℤ × ℤ} (hx : minContent ω.E + J * ω.period + ω.width ≤ content x)
    (hxD : x ∈ ω.compose D') : x + T ∈ ω.compose D := by
  have hq := hω.period_pos
  rw [mem_compose hD'] at hxD
  rw [mem_compose hD]
  rcases hxD with ⟨d, hd, hxd⟩ | ⟨d, hd, hr, hxd⟩
  · have h1 := hω.copy_content (mem_translate.mp hxd)
    rw [content_sub, content_origin] at h1
    have hdJ : J ≤ content d := by
      by_contra hn
      have := mul_le_mul_of_nonneg_right (show content d + 1 ≤ J by omega) hq.le
      nlinarith
    left
    refine ⟨d + z, (hmem d hdJ).mp hd, ?_⟩
    rw [mem_translate, ← horig d hd hdJ]
    have e : x + T - (ω.origin D' d + T) = x - ω.origin D' d := by abel
    rw [e]
    exact mem_translate.mp hxd
  · have h1 := hω.upper_content (mem_translate.mp hxd)
    rw [content_sub, content_add, content_origin, content_supplementalShift] at h1
    have hdJ : J ≤ content d := by
      by_contra hn
      have := mul_le_mul_of_nonneg_right (show content d + 1 ≤ J by omega) hq.le
      nlinarith
    right
    refine ⟨d + z, (hmem d hdJ).mp hd, (hrib d hd hdJ).mp hr, ?_⟩
    rw [mem_translate, ← horig d hd hdJ]
    have e : x + T - (ω.origin D' d + T + ω.supplementalShift) =
        x - (ω.origin D' d + ω.supplementalShift) := by abel
    rw [e]
    exact mem_translate.mp hxd

theorem mem_compose_of_shift_aux' (hω : ω.IsLegal) {D' D : Diagram} (hD' : D'.Nonempty)
    (hD : D.Nonempty) {J : ℤ} {z T : ℤ × ℤ} (hT : content T = content z * ω.period)
    (hmem : ∀ x, J ≤ content x → (x ∈ D' ↔ x + z ∈ D))
    (horig : ∀ d ∈ D', J ≤ content d → ω.origin D' d + T = ω.origin D (d + z))
    (hrib : ∀ d ∈ D', J ≤ content d → (ω.SameRibbon D' d ↔ ω.SameRibbon D (d + z)))
    {x : ℤ × ℤ} (hx : minContent ω.E + J * ω.period + ω.width ≤ content x)
    (hxD : x + T ∈ ω.compose D) : x ∈ ω.compose D' := by
  have hq := hω.period_pos
  rw [mem_compose hD] at hxD
  rw [mem_compose hD']
  have hcT : content (x + T) = content x + content z * ω.period := by
    rw [content_add, hT]
  rcases hxD with ⟨d₂, hd₂, hxd⟩ | ⟨d₂, hd₂, hr, hxd⟩
  · have h1 := hω.copy_content (mem_translate.mp hxd)
    rw [content_sub, content_origin, hcT] at h1
    have hdJ : J + content z ≤ content d₂ := by
      by_contra hn
      have := mul_le_mul_of_nonneg_right (show content d₂ + 1 ≤ J + content z by omega) hq.le
      nlinarith
    obtain ⟨d, rfl⟩ : ∃ d, d₂ = d + z := ⟨d₂ - z, by abel⟩
    have hcd : content (d + z) = content d + content z := content_add d z
    have hdJ' : J ≤ content d := by omega
    have hd : d ∈ D' := (hmem d hdJ').mpr hd₂
    left
    refine ⟨d, hd, ?_⟩
    rw [mem_translate]
    have := mem_translate.mp hxd
    rw [← horig d hd hdJ'] at this
    have e : x + T - (ω.origin D' d + T) = x - ω.origin D' d := by abel
    rwa [e] at this
  · have h1 := hω.upper_content (mem_translate.mp hxd)
    rw [content_sub, content_add (ω.origin D d₂), content_origin, content_supplementalShift,
      hcT] at h1
    have hdJ : J + content z ≤ content d₂ := by
      by_contra hn
      have := mul_le_mul_of_nonneg_right (show content d₂ + 1 ≤ J + content z by omega) hq.le
      nlinarith
    obtain ⟨d, rfl⟩ : ∃ d, d₂ = d + z := ⟨d₂ - z, by abel⟩
    have hcd : content (d + z) = content d + content z := content_add d z
    have hdJ' : J ≤ content d := by omega
    have hd : d ∈ D' := (hmem d hdJ').mpr hd₂
    right
    refine ⟨d, hd, (hrib d hd hdJ').mpr hr, ?_⟩
    rw [mem_translate]
    have := mem_translate.mp hxd
    rw [← horig d hd hdJ'] at this
    have e : x + T - (ω.origin D' d + T + ω.supplementalShift) =
        x - (ω.origin D' d + ω.supplementalShift) := by abel
    rwa [e] at this

/-- **Suffix locality.**  Suppose the cells of `D'` on the contents `≥ J` are those of `D`
translated by `-z`, with the origins of the copies moving by `T`, `c(T) = c(z) q`.  Then the
cells of `D' ∘_ω E` on the contents `≥ c₀ + J q + w` are those of `D ∘_ω E` translated by `-T`. -/
theorem mem_compose_iff_of_shift (hω : ω.IsLegal) {D' D : Diagram} (hD' : D'.Nonempty)
    (hD : D.Nonempty) {J : ℤ} {z T : ℤ × ℤ} (hT : content T = content z * ω.period)
    (hmem : ∀ x, J ≤ content x → (x ∈ D' ↔ x + z ∈ D))
    (horig : ∀ d ∈ D', J ≤ content d → ω.origin D' d + T = ω.origin D (d + z))
    (hrib : ∀ d ∈ D', J ≤ content d → (ω.SameRibbon D' d ↔ ω.SameRibbon D (d + z)))
    {x : ℤ × ℤ} (hx : minContent ω.E + J * ω.period + ω.width ≤ content x) :
    x ∈ ω.compose D' ↔ x + T ∈ ω.compose D :=
  ⟨mem_compose_of_shift_aux hω hD' hD hT hmem horig hrib hx,
    mem_compose_of_shift_aux' hω hD' hD hT hmem horig hrib hx⟩

end MarkedInner

end GluingCore
