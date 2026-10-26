import SkewGluing.MixedFold.Identity

/-!
# Words of composites at the two ends

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (3)),
at the level of the bit words: if two connected skew diagrams agree, after southwest
normalization, on all cells of content at most `c` (at least `c`, up to a translation `u`), their
words agree on the positions at most `c` (after the shift by the content of `u`).

Sorry-free.
-/

namespace SkewGluing

theorem mixFold_diagRows_agree {D₁ D₂ : Diagram} {c : ℤ}
    (h : ∀ x : ℤ × ℤ, content x ≤ c → (x ∈ D₁ ↔ x ∈ D₂)) {j : ℤ} (hj : j ≤ c) :
    diagRows D₁ j = diagRows D₂ j := by
  ext i
  rw [mem_diagRows, mem_diagRows]
  exact h (i, i + j) (by simp [content]; omega)

theorem mixFold_diagLo_agree {D₁ D₂ : Diagram} {c : ℤ}
    (h : ∀ x : ℤ × ℤ, content x ≤ c → (x ∈ D₁ ↔ x ∈ D₂)) {j : ℤ} (hj : j ≤ c) :
    diagLo D₁ j = diagLo D₂ j ∧ diagHi D₁ j = diagHi D₂ j := by
  have := mixFold_diagRows_agree h hj
  unfold diagLo diagHi
  rw [this]
  exact ⟨rfl, rfl⟩

theorem mixFold_minContent_normalize {D : Diagram} (hD : IsConnectedSkew D) :
    minContent (normalize D) = 0 := by
  have hne := hD.2.1
  unfold normalize
  rw [minContent_translate hne, content_neg_sw' hne]
  ring
where
  content_neg_sw' {D : Diagram} (hne : D.Nonempty) : content (-(sw D)) = -minContent D := by
    have := content_sw hne
    simp only [content, Prod.fst_neg, Prod.snd_neg] at this ⊢
    omega

theorem mixFold_word_normalize {D : Diagram} (hD : IsConnectedSkew D) {k : ℤ} (h1 : 1 ≤ k)
    (h2 : k ≤ (span D : ℤ) - 1) :
    wordA D k = bitA (normalize D) k ∧ wordB D k = bitB (normalize D) k := by
  have e := wordA_translate hD (-(sw D)) h1 (by omega)
  have e2 := wordB_translate hD (-(sw D)) h1 (by omega)
  have hm := mixFold_minContent_normalize hD
  constructor
  · rw [← e]; unfold wordA normalize; unfold normalize at hm; rw [hm]; simp
  · rw [← e2]; unfold wordB normalize; unfold normalize at hm; rw [hm]; simp

/-- The first window: the words agree up to the position `c`. -/
theorem mixFold_word_first {D₁ D₂ : Diagram} (h₁ : IsConnectedSkew D₁) (h₂ : IsConnectedSkew D₂)
    {c : ℤ} (h : ∀ x : ℤ × ℤ, content x ≤ c → (x ∈ normalize D₁ ↔ x ∈ normalize D₂)) {k : ℤ}
    (hk1 : 1 ≤ k) (hkc : k ≤ c) (hk₁ : k ≤ (span D₁ : ℤ) - 1) (hk₂ : k ≤ (span D₂ : ℤ) - 1) :
    wordA D₁ k = wordA D₂ k ∧ wordB D₁ k = wordB D₂ k := by
  obtain ⟨a1, b1⟩ := mixFold_word_normalize h₁ hk1 hk₁
  obtain ⟨a2, b2⟩ := mixFold_word_normalize h₂ hk1 hk₂
  rw [a1, a2, b1, b2]
  unfold bitA bitB
  obtain ⟨l1, u1⟩ := mixFold_diagLo_agree h (j := k - 1) (by omega)
  obtain ⟨l2, u2⟩ := mixFold_diagLo_agree h (j := k) hkc
  rw [l1, l2, u1, u2]
  exact ⟨rfl, rfl⟩

/-- The last window: the words agree from the position `c + 1` on, after the shift by the content
of `u`. -/
theorem mixFold_word_last {D₁ D₂ : Diagram} (h₁ : IsConnectedSkew D₁) (h₂ : IsConnectedSkew D₂)
    {c : ℤ} {u : ℤ × ℤ}
    (h : ∀ x : ℤ × ℤ, c ≤ content x → (x ∈ normalize D₁ ↔ x ∈ translate u (normalize D₂)))
    {k : ℤ} (hk1 : 1 ≤ k) (hkc : c + 1 ≤ k) (hk₁ : k ≤ (span D₁ : ℤ) - 1)
    (hk2 : 1 ≤ k - content u) (hk₂ : k - content u ≤ (span D₂ : ℤ) - 1) :
    wordA D₁ k = wordA D₂ (k - content u) := by
  obtain ⟨a1, b1⟩ := mixFold_word_normalize h₁ hk1 hk₁
  obtain ⟨a2, b2⟩ := mixFold_word_normalize h₂ hk2 hk₂
  rw [a1, a2]
  unfold bitA
  have hn2 := h₂.2.1
  have hshape := isConnectedSkew_iff_diagonal.mp (isConnectedSkew_normalize h₂)
  have hm := mixFold_minContent_normalize h₂
  have hsp := span_eq_of_isConnectedSkew (isConnectedSkew_normalize h₂)
  have hspn : span (normalize D₂) = span D₂ := by unfold normalize; exact span_translate _
  have hmax : maxContent (normalize D₂) = (span D₂ : ℤ) - 1 := by
    rw [hspn, hm] at hsp; omega
  have hc1 : k - content u - 1 ∈ contents (normalize D₂) := by
    rw [hshape.mem_contents_iff, hm]; omega
  have hc2 : k - content u ∈ contents (normalize D₂) := by
    rw [hshape.mem_contents_iff, hm]; omega
  have t1 := diagLo_translate u _ hc1
  have t2 := diagLo_translate u _ hc2
  rw [show k - content u - 1 + content u = k - 1 by ring] at t1
  rw [show k - content u + content u = k by ring] at t2
  have hlo : ∀ j, c ≤ j → diagLo (normalize D₁) j = diagLo (translate u (normalize D₂)) j := by
    intro j hj
    have hrows : diagRows (normalize D₁) j = diagRows (translate u (normalize D₂)) j := by
      ext i
      rw [mem_diagRows, mem_diagRows]
      exact h (i, i + j) (by simp [content]; omega)
    unfold diagLo; rw [hrows]
  rw [hlo (k - 1) (by omega), hlo k (by omega), t1, t2]
  ring

end SkewGluing
