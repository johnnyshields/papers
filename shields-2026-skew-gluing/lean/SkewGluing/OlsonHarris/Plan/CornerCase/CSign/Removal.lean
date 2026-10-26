import SkewGluing.OlsonHarris.Plan.CornerCase.CSign.Counts

/-!
# The northbound count after removing a ribbon

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the identity `ξ(D) - ξ(D \ A)` = number of northbound boxes of
the ribbon `A` in the proof of thesis Lemma 5.5.11 (`OlsonHarris2024HopfApplications`), for a
legal mark of case (c).

* For `A` removable on the right (an upset), removing `A` does not change whether the remaining
  cells have a northern neighbor on the same northwest ribbon, so
  `ξ(D) - ξ(D \ A)` is the number of cells of `A` with that property (`xi_diff_right`).
* For `A` removable on the left (a downset), the northwest ribbons change, but the southeast
  ribbons of the remaining cells do not; by thesis Lemma 5.5.10 (`card_nwNorth_eq_card_seNorth`)
  the count `ξ` is also the southeast count, and `ξ(D) - ξ(D \ A)` is the number of cells of `D`
  whose northern neighbor lies in `A` on the same southeast ribbon (`xi_diff_left`).

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

namespace CSign

variable {D A X : Diagram}

theorem diagLo_sdiff_upset (hA : IsUpsetIn X A) {d : ℤ × ℤ} (hd : d ∈ X \ A) :
    diagLo (X \ A) (content d) = diagLo X (content d) := by
  obtain ⟨hdX, hdA⟩ := Finset.mem_sdiff.mp hd
  have hmem := diagLo_mem (content_mem_contents hdX)
  have hzA : (diagLo X (content d), diagLo X (content d) + content d) ∉ A := fun hz => by
    apply hdA
    refine hA.2 d hdX _ hz ?_ ?_
    · exact diagLo_le hdX (by simp [content])
    · have := diagLo_le hdX (k := content d) (by simp [content])
      simp only [content] at this ⊢; omega
  refine diagLo_eq_of (Finset.mem_sdiff.mpr ⟨hmem, hzA⟩) fun i hi => ?_
  exact diagLo_le (Finset.mem_sdiff.mp hi).1 (by ring)

theorem diagHi_sdiff_downset (hA : IsDownsetIn X A) {d : ℤ × ℤ} (hd : d ∈ X \ A) :
    diagHi (X \ A) (content d) = diagHi X (content d) := by
  obtain ⟨hdX, hdA⟩ := Finset.mem_sdiff.mp hd
  have hmem := diagHi_mem (content_mem_contents hdX)
  have hzA : (diagHi X (content d), diagHi X (content d) + content d) ∉ A := fun hz => by
    apply hdA
    refine hA.2 d hdX _ hz ?_ ?_
    · exact le_diagHi hdX (by simp [content])
    · have := le_diagHi hdX (k := content d) (by simp [content])
      simp only [content] at this ⊢; omega
  refine diagHi_eq_of (Finset.mem_sdiff.mpr ⟨hmem, hzA⟩) fun i hi => ?_
  exact le_diagHi (Finset.mem_sdiff.mp hi).1 (by ring)

theorem north_not_mem_of_upset (hA : IsUpsetIn X A) {d : ℤ × ℤ} (hd : d ∈ X \ A) :
    (d.1 - 1, d.2) ∉ A := fun h => (Finset.mem_sdiff.mp hd).2 (hA.2 d (Finset.mem_sdiff.mp hd).1 _ h
  (by simp) (by simp))

theorem nwNorth_sdiff_iff (hA : IsUpsetIn X A) {d : ℤ × ℤ} (hd : d ∈ X \ A) :
    nwNorth (X \ A) d ↔ nwNorth X d := by
  unfold nwNorth
  constructor
  · rintro ⟨hn, hr⟩
    have hn' := Finset.mem_sdiff.mp hn
    have h1 := diagLo_sdiff_upset hA hd
    have h2 := diagLo_sdiff_upset hA hn
    rw [content_north] at h2
    exact ⟨hn'.1, by rw [← h1, ← h2]; exact hr⟩
  · rintro ⟨hn, hr⟩
    have hn' : (d.1 - 1, d.2) ∈ X \ A := Finset.mem_sdiff.mpr ⟨hn, north_not_mem_of_upset hA hd⟩
    have h1 := diagLo_sdiff_upset hA hd
    have h2 := diagLo_sdiff_upset hA hn'
    rw [content_north] at h2
    exact ⟨hn', by rw [h1, h2]; exact hr⟩

theorem seNorth_sdiff_iff (hA : IsDownsetIn X A) {d : ℤ × ℤ} (hd : d ∈ X \ A) :
    seNorth (X \ A) d ↔ seNorth X d ∧ (d.1 - 1, d.2) ∉ A := by
  unfold seNorth
  constructor
  · rintro ⟨hn, hr⟩
    have hn' := Finset.mem_sdiff.mp hn
    have h1 := diagHi_sdiff_downset hA hd
    have h2 := diagHi_sdiff_downset hA hn
    rw [content_north] at h2
    exact ⟨⟨hn'.1, by rw [← h1, ← h2]; exact hr⟩, hn'.2⟩
  · rintro ⟨⟨hn, hr⟩, hnA⟩
    have hn' : (d.1 - 1, d.2) ∈ X \ A := Finset.mem_sdiff.mpr ⟨hn, hnA⟩
    have h1 := diagHi_sdiff_downset hA hd
    have h2 := diagHi_sdiff_downset hA hn'
    rw [content_north] at h2
    exact ⟨hn', by rw [h1, h2]; exact hr⟩

/-- **Removal of a ribbon on the right.**  `ξ(D) - ξ(D \ A)` is the number of cells of `A` with a
cell to the north on the same northwest ribbon of `D`. -/
theorem xi_diff_right {ω : MarkedInner} (hc : ω.case = .c) (hD : IsConnectedSkew D)
    (hA : IsUpsetIn D A) :
    (northboundSum ω D : ℤ) - northboundSum ω (D \ A) = ((A.filter (nwNorth D)).card : ℤ) := by
  have hX := isSkew_sdiff_of_isUpsetIn hD.1 hA
  rw [northboundSum_eq_card hc hD.1, northboundSum_eq_card hc hX]
  have hfil : (D \ A).filter (nwNorth (D \ A)) = (D.filter (nwNorth D)).filter (· ∉ A) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hd, hdA⟩, hp⟩
      exact ⟨⟨hd, (nwNorth_sdiff_iff hA (Finset.mem_sdiff.mpr ⟨hd, hdA⟩)).mp hp⟩, hdA⟩
    · rintro ⟨⟨hd, hp⟩, hdA⟩
      exact ⟨⟨hd, hdA⟩, (nwNorth_sdiff_iff hA (Finset.mem_sdiff.mpr ⟨hd, hdA⟩)).mpr hp⟩
  have hA' : A.filter (nwNorth D) = (D.filter (nwNorth D)).filter (· ∈ A) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hdA, hp⟩
      exact ⟨⟨hA.1 hdA, hp⟩, hdA⟩
    · rintro ⟨⟨-, hp⟩, hdA⟩
      exact ⟨hdA, hp⟩
  rw [hfil, hA']
  have := Finset.card_filter_add_card_filter_not (s := D.filter (nwNorth D)) (· ∈ A)
  omega

/-- **Removal of a ribbon on the left.**  `ξ(D) - ξ(D \ A)` is the number of cells of `D` with a
cell to the north on the same southeast ribbon of `D` that lies in `A`. -/
theorem xi_diff_left {ω : MarkedInner} (hc : ω.case = .c) (hD : IsConnectedSkew D)
    (hA : IsDownsetIn D A) :
    (northboundSum ω D : ℤ) - northboundSum ω (D \ A) =
      (((D.filter (seNorth D)).filter (fun d => (d.1 - 1, d.2) ∈ A)).card : ℤ) := by
  have hX := isSkew_sdiff_of_isDownsetIn hD.1 hA
  have hse : ∀ Y : Diagram, IsSkew Y → northboundSum ω Y = (Y.filter (seNorth Y)).card := by
    intro Y hY
    unfold northboundSum
    simp only [northbound_eq_card hc]
    rw [← sum_components_card_filter (P := seNorth)
      fun C hC d hd => seNorth_component_iff hY hC hd]
    refine Finset.sum_congr rfl fun C hC => ?_
    exact card_nwNorth_eq_card_seNorth (isConnectedSkew_component hY hC)
  rw [hse D hD.1, hse (D \ A) hX]
  have hfil : (D \ A).filter (seNorth (D \ A)) =
      (D.filter (seNorth D)).filter (fun d => (d.1 - 1, d.2) ∉ A) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hd, hdA⟩, hp⟩
      obtain ⟨h1, h2⟩ := (seNorth_sdiff_iff hA (Finset.mem_sdiff.mpr ⟨hd, hdA⟩)).mp hp
      exact ⟨⟨hd, h1⟩, h2⟩
    · rintro ⟨⟨hd, hp⟩, hnA⟩
      have hdA : d ∉ A := fun h => hnA (hA.2 _ hp.1 d h (by simp) (by simp))
      exact ⟨⟨hd, hdA⟩, (seNorth_sdiff_iff hA (Finset.mem_sdiff.mpr ⟨hd, hdA⟩)).mpr ⟨hp, hnA⟩⟩
  rw [hfil]
  have := Finset.card_filter_add_card_filter_not (s := D.filter (seNorth D))
    (fun d : ℤ × ℤ => (d.1 - 1, d.2) ∈ A)
  omega

end CSign

end Corner

end Plan

end SkewGluing
