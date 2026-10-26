import SkewGluing.Decoder.Defs

/-!
# Bookkeeping for the decoder

Formalizes `shields-2026-skew-gluing.tex`, «Reconstructing a chart from its two words»
(`ge:decoder`).

Differences of the height `hwd`, sums of a word difference over one block of `f` positions
(`window`), the area of a connected diagram as a sum of heights, the reference outer (a row of `m`
cells) and the elementary properties of the port residues.

Sorry-free.
-/

namespace SkewGluing

/-- The height at `k₂` minus the height at `k₁` is the sum of the word steps in between. -/
theorem hwd_sub (P : Diagram) {k₁ k₂ : ℤ} (h1 : 0 ≤ k₁) (h2 : k₁ ≤ k₂) :
    hwd P k₂ - hwd P k₁ = ∑ i ∈ Finset.Icc (k₁ + 1) k₂, (Yw P i - Xw P i) := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k₂ - k₁ by omega)
  have e : k₂ = k₁ + n := by omega
  rw [e]
  clear e hn h2
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : k₁ + ((n + 1 : ℕ) : ℤ) = (k₁ + n) + 1 := by push_cast; ring
    rw [e1, hwd_succ P (by omega)]
    have e2 : Finset.Icc (k₁ + 1) (k₁ + n + 1) =
        insert (k₁ + n + 1) (Finset.Icc (k₁ + 1) (k₁ + n)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [e2, Finset.sum_insert (by simp)]
    have := ih
    linarith

/-- A function supported on the positions with residue in `S ⊆ [0, a]`, `a < f`, sums over the
interval `[lo, j f + a]`, where `j f - (f - a - 1) ≤ lo ≤ j f`, to its values at `j f + r`,
`r ∈ S`. -/
theorem sum_block {g : ℤ → ℤ} {f a j : ℤ} {S : Finset ℤ} (hS : ∀ r ∈ S, 0 ≤ r ∧ r ≤ a)
    (haf : a < f) {lo : ℤ} (hlo : j * f - (f - a - 1) ≤ lo) (hlo' : lo ≤ j * f)
    (hg : ∀ i, lo ≤ i → i ≤ j * f + a → i % f ∉ S → g i = 0) (hf : 0 < f) :
    ∑ i ∈ Finset.Icc lo (j * f + a), g i = ∑ r ∈ S, g (j * f + r) := by
  have hsub : S.image (fun r => j * f + r) ⊆ Finset.Icc lo (j * f + a) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    have := hS r hr
    rw [Finset.mem_Icc]
    omega
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · intro x _ y _ hxy
    simpa using hxy
  · intro x hx hnot
    apply hg x (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2
    intro hmem
    apply hnot
    rw [Finset.mem_image]
    refine ⟨x % f, hmem, ?_⟩
    have hx2 := Finset.mem_Icc.mp hx
    have h3 := Int.mul_ediv_add_emod x f
    have hs := hS (x % f) hmem
    have hr := Int.emod_nonneg x hf.ne'
    have h4 : x / f = j := by
      have hq1 : j * f ≤ x := by
        by_contra hcon
        have h5 : x / f ≤ j - 1 := by
          have : x / f < j := by
            by_contra h6
            have : j * f ≤ f * (x / f) := by nlinarith
            omega
          omega
        have : f * (x / f) ≤ f * (j - 1) := by nlinarith
        nlinarith
      have h5 : j ≤ x / f := by
        rw [Int.le_ediv_iff_mul_le hf]; exact hq1
      have h6 : x / f < j + 1 := by
        rw [Int.ediv_lt_iff_lt_mul hf]; nlinarith
      omega
    rw [h4] at h3
    linarith

/-- The area of a connected diagram is the sum of the heights of its diagonals. -/
theorem card_eq_sum_height {D : Diagram} (hD : IsConnectedSkew D) :
    ((D.card : ℕ) : ℤ) = ∑ k ∈ Finset.range (span D), height D (minContent D + k) := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hsp := span_eq_of_isConnectedSkew hD
  set t : Finset ℤ := (Finset.range (span D)).image (fun k : ℕ => minContent D + (k : ℤ)) with ht
  have hmaps : ∀ x ∈ D, content x ∈ t := by
    intro x hx
    have hc := content_mem_contents hx
    rw [hs.mem_contents_iff] at hc
    rw [ht, Finset.mem_image]
    refine ⟨(content x - minContent D).toNat, Finset.mem_range.mpr (by omega), by omega⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  rw [ht, Finset.sum_image (by intro x _ y _ h; simpa using h)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hk0 : minContent D + (k : ℤ) ∈ contents D := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
  have hfib : D.filter (fun x => content x = minContent D + (k : ℤ)) =
      (Finset.Icc (diagLo D (minContent D + k)) (diagHi D (minContent D + k))).image
        (fun i => (i, i + (minContent D + (k : ℤ)))) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨hx, hc⟩
      have hj : j = i + (minContent D + (k : ℤ)) := by simp only [content] at hc; omega
      subst hj
      have := hs.mem_iff.mp hx
      exact ⟨i, ⟨this.2.1, this.2.2⟩, rfl, rfl⟩
    · rintro ⟨i', ⟨h1, h2⟩, rfl, rfl⟩
      refine ⟨hs.mem_iff.mpr ⟨hk0, h1, h2⟩, ?_⟩
      simp only [content]; ring
  rw [hfib, Finset.card_image_of_injective _ (by intro x y h; simpa using congrArg Prod.fst h),
    Int.card_Icc]
  have := diagLo_le_diagHi hk0
  unfold height
  omega

theorem hwd_pos {P : Diagram} (hP : IsConnectedSkew P) {k : ℤ} (h1 : 0 ≤ k)
    (h2 : k < (span P : ℤ)) : 0 < hwd P k := by
  rw [hwd_eq_height hP h1 h2]
  have hs := isConnectedSkew_iff_diagonal.mp hP
  have hsp := span_eq_of_isConnectedSkew hP
  have hk0 : minContent P + k ∈ contents P := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
  have := diagLo_le_diagHi hk0
  unfold height
  omega

/-- A row of `m ≥ 1` cells, as the reference outer of span `m`. -/
theorem exists_outer_span {m : ℕ} (hm : 1 ≤ m) :
    ∃ A : Diagram, IsConnectedSkew A ∧ span A = m := by
  have hbd : IsBitData m (fun _ => (0 : ℤ)) (fun _ => (0 : ℤ)) :=
    ⟨hm, fun _ _ _ => ⟨Or.inl rfl, Or.inl rfl⟩, fun k _ => by simp [heightWord],
      by simp [heightWord]⟩
  exact ⟨fromBits m _ _, isConnectedSkew_fromBits hbd, span_fromBits hbd⟩

end SkewGluing
