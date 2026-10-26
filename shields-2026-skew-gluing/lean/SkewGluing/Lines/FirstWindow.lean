import SkewGluing.Lines.WordFacts
import SkewGluing.Local

/-!
# The first window of a composite, read on its boundary words

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (3):
"its first `q` diagonals are those of `E`").

For a legal mark `ω` and a connected outer `D`, the first `q` diagonals of `D ∘_ω E` are those of
`E`, shifted by the origin of the southwest cell of `D`.  Consequently the first `q - 1` bits of the
two boundary words of the composite are those of `E` (`wordA_compose_first`,
`wordB_compose_first`).

Sorry-free.
-/

namespace SkewGluing

namespace Lines

/-- A window: if `Y` and `X` agree up to the translation `o` on the contents `≤ c`, then their
diagonals agree there. -/
theorem diag_of_window {X Y : Diagram} {o : ℤ × ℤ} {c : ℤ}
    (h : ∀ y : ℤ × ℤ, content y ≤ c → (y ∈ Y ↔ y - o ∈ X)) {k : ℤ} (hk : k ≤ c)
    (hkX : k - content o ∈ contents X) :
    diagLo Y k = diagLo X (k - content o) + o.1 ∧ diagHi Y k = diagHi X (k - content o) + o.1 := by
  have hc : content o = o.2 - o.1 := rfl
  have key : ∀ i : ℤ, (i, i + k) ∈ Y ↔ (i - o.1, (i - o.1) + (k - content o)) ∈ X := by
    intro i
    have e : ((i, i + k) : ℤ × ℤ) - o = (i - o.1, (i - o.1) + (k - content o)) := by
      ext
      · simp
      · simp only [Prod.snd_sub]; omega
    rw [← e]
    exact h _ (by simp only [content]; omega)
  constructor
  · apply diagLo_eq_of
    · rw [key]
      have := diagLo_mem hkX
      convert this using 2 <;> ring
    · intro i hi
      have := diagLo_le (D := X) (k := k - content o) ((key i).mp hi) (by ring)
      omega
  · apply diagHi_eq_of
    · rw [key]
      have := diagHi_mem hkX
      convert this using 2 <;> ring
    · intro i hi
      have := le_diagHi (D := X) (k := k - content o) ((key i).mp hi) (by ring)
      omega

end Lines

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem IsLegal.content_origin_sw (_hω : ω.IsLegal) (hD : IsConnectedSkew D) :
    content (ω.origin D (sw D)) = minContent D * ω.period := by
  rw [content_origin, content_sw hD.2.1]

/-- The first window of the composite as an equivalence of cells. -/
theorem IsLegal.first_window_mem (hω : ω.IsLegal) (hD : IsConnectedSkew D) {y : ℤ × ℤ}
    (hy : content y ≤ minContent (ω.compose D) + ω.period - 1) :
    y ∈ ω.compose D ↔ y - ω.origin D (sw D) ∈ ω.E := by
  have hmin := hω.minContent_compose hD
  have hwin := hω.compose_first_window hD
  have hco := hω.content_origin_sw hD
  have h1 : content y ≤ minContent ω.E + minContent D * ω.period + ω.period - 1 := by
    rw [← hmin]; omega
  have := Finset.ext_iff.mp hwin y
  simp only [Finset.mem_filter, mem_translate] at this
  constructor
  · intro hy'
    exact (this.mp ⟨hy', h1⟩).1
  · intro hy'
    refine (this.mpr ⟨hy', ?_⟩).1
    rw [content_sub] at ⊢
    omega

/-- **The first `q` diagonals of the composite are those of `E`**, shifted by the origin of the
southwest cell of `D`. -/
theorem IsLegal.diag_compose_first (hω : ω.IsLegal) (hD : IsConnectedSkew D) {j : ℤ} (hj0 : 0 ≤ j)
    (hj : j ≤ ω.period - 1) :
    diagLo (ω.compose D) (minContent (ω.compose D) + j) =
        diagLo ω.E (minContent ω.E + j) + (ω.origin D (sw D)).1 ∧
      diagHi (ω.compose D) (minContent (ω.compose D) + j) =
        diagHi ω.E (minContent ω.E + j) + (ω.origin D (sw D)).1 := by
  have hmin := hω.minContent_compose hD
  have hco := hω.content_origin_sw hD
  have hE := hω.1.1
  have hcE := hω.1.contents_eq
  have hkX : minContent ω.E + j ∈ contents ω.E := by
    rw [hcE, Finset.mem_Icc]
    have : (0 : ℤ) ≤ ω.width := by positivity
    omega
  have := Lines.diag_of_window (X := ω.E) (Y := ω.compose D) (o := ω.origin D (sw D))
    (c := minContent (ω.compose D) + ω.period - 1)
    (fun y hy => hω.first_window_mem hD hy) (k := minContent (ω.compose D) + j) (by omega)
    (by rw [hco, hmin]; convert hkX using 1; ring)
  have e : minContent (ω.compose D) + j - content (ω.origin D (sw D)) = minContent ω.E + j := by
    rw [hco, hmin]; ring
  rwa [e] at this

/-- **The first `q - 1` bits of the composite are those of `E`.** -/
theorem IsLegal.wordA_compose_first (hω : ω.IsLegal) (hD : IsConnectedSkew D) {k : ℤ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ ω.period - 1) :
    wordA (ω.compose D) k = wordA ω.E k := by
  have h1 := (hω.diag_compose_first hD (j := k - 1) (by omega) (by omega)).1
  have h2 := (hω.diag_compose_first hD (j := k) (by omega) (by omega)).1
  unfold wordA bitA
  have e1 : minContent (ω.compose D) + k - 1 = minContent (ω.compose D) + (k - 1) := by ring
  have e2 : minContent ω.E + k - 1 = minContent ω.E + (k - 1) := by ring
  rw [e1, e2, h1, h2]
  ring

theorem IsLegal.wordB_compose_first (hω : ω.IsLegal) (hD : IsConnectedSkew D) {k : ℤ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ ω.period - 1) :
    wordB (ω.compose D) k = wordB ω.E k := by
  have h1 := (hω.diag_compose_first hD (j := k - 1) (by omega) (by omega)).2
  have h2 := (hω.diag_compose_first hD (j := k) (by omega) (by omega)).2
  unfold wordB bitB
  have e1 : minContent (ω.compose D) + k - 1 = minContent (ω.compose D) + (k - 1) := by ring
  have e2 : minContent ω.E + k - 1 = minContent ω.E + (k - 1) := by ring
  rw [e1, e2, h1, h2]
  ring

end MarkedInner

end SkewGluing
