/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/InnerFactor/Agree.lean`. -/
import GluingCore.Aligned.InnerFactor.Windows

/-!
# Repetition of the outer from the repetition of the composite

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`), via `eq:gluing-offsets` and `eq:gluing-mixed-profile`.

Let `F = D ∘_ω E` for a legal mark `ω` of period `q` and width `w`, and suppose that on the
contents `[c₀ + (m₀ + b) q + w, c₀ + (m₀ + a) q - 1]` the cells of `F` repeat under a translation
`τ` of content `Δ q` (`PerData`).  Then the diagonals `[m₀ + b, m₀ + a - 1]` of `D` repeat
`Δ` diagonals later under one common row shift (`FactorData`): for an ordinary mark by sampling
the private residue `w`, and in case (d) by the heights on the private residue `w` and the
overlaps `S_j` on a marked residue meeting neither middle tail.

Sorry-free.
-/

namespace GluingCore

open MarkedInner

/-- The repetition of the composite `D ∘_ω E`: on the contents `[c₀ + (m₀ + b) q + w,
c₀ + (m₀ + a) q - 1]` its cells repeat under the translation `τ`, of content `Δ q`. -/
structure PerData (ω : MarkedInner) (D : Diagram) (a b Δ : ℤ) (τ : ℤ × ℤ) : Prop where
  legal : ω.IsLegal
  conn : IsConnectedSkew D
  ha : 1 ≤ a
  hb : 0 ≤ b
  hba : b < a
  hΔ : 0 ≤ Δ
  hM : maxContent D = minContent D + a + b - 1 + Δ
  hτ : content τ = Δ * ω.period
  per : ∀ x : ℤ × ℤ,
    minContent ω.E + (minContent D + b) * ω.period + ω.widthZ ≤ content x →
    content x ≤ minContent ω.E + (minContent D + a) * ω.period - 1 →
    (x ∈ ω.compose D ↔ x + τ ∈ ω.compose D)

/-- Cell-level repetition gives repetition of the first and last row of each diagonal. -/
theorem diag_shift_of_per {F : Diagram} {τ : ℤ × ℤ} {k₀ k₁ : ℤ}
    (hper : ∀ x : ℤ × ℤ, k₀ ≤ content x → content x ≤ k₁ → (x ∈ F ↔ x + τ ∈ F)) {k : ℤ}
    (hk : k ∈ contents F) (h0 : k₀ ≤ k) (h1 : k ≤ k₁) :
    diagLo F (k + content τ) = diagLo F k + τ.1 ∧ diagHi F (k + content τ) = diagHi F k + τ.1 := by
  have hcτ : ∀ i : ℤ, content ((i, i + k) + τ) = k + content τ := by
    intro i; rw [content_add]; simp [content]
  have c1 : ∀ i : ℤ, content (i, i + k) = k := by intro i; simp [content]
  have e1 : ∀ i : ℤ, (i, i + k) + τ = (i + τ.1, (i + τ.1) + (k + content τ)) := by
    intro i; ext <;> (simp [content]; try ring)
  have fwd : ∀ i : ℤ, (i, i + k) ∈ F → (i + τ.1, (i + τ.1) + (k + content τ)) ∈ F := by
    intro i hi
    have := (hper (i, i + k) (by rw [c1]; exact h0) (by rw [c1]; exact h1)).mp hi
    rwa [e1] at this
  have bwd : ∀ i : ℤ, (i, i + (k + content τ)) ∈ F → (i - τ.1, (i - τ.1) + k) ∈ F := by
    intro i hi
    have hx : (i - τ.1, (i - τ.1) + k) + τ = (i, i + (k + content τ)) := by
      ext <;> (simp [content]; try ring)
    have := (hper (i - τ.1, (i - τ.1) + k) (by rw [c1]; exact h0) (by rw [c1]; exact h1)).mpr
      (by rw [hx]; exact hi)
    exact this
  have hk' : k + content τ ∈ contents F := by
    have := fwd _ (diagLo_mem hk)
    exact mem_contents_iff.mpr ⟨_, this⟩
  constructor
  · have a1 := diagLo_le (D := F) (k := k + content τ) (fwd _ (diagLo_mem hk)) (by ring)
    have a2 := diagLo_le (D := F) (k := k) (bwd _ (diagLo_mem hk')) (by ring)
    omega
  · have a1 := le_diagHi (D := F) (k := k + content τ) (fwd _ (diagHi_mem hk)) (by ring)
    have a2 := le_diagHi (D := F) (k := k) (bwd _ (diagHi_mem hk')) (by ring)
    omega

namespace PerData

variable {ω : MarkedInner} {D : Diagram} {a b Δ : ℤ} {τ : ℤ × ℤ}

theorem diag_shift (h : PerData ω D a b Δ τ) {k : ℤ} (hk : k ∈ contents (ω.compose D))
    (h0 : minContent ω.E + (minContent D + b) * ω.period + ω.widthZ ≤ k)
    (h1 : k ≤ minContent ω.E + (minContent D + a) * ω.period - 1) :
    diagLo (ω.compose D) (k + Δ * ω.period) = diagLo (ω.compose D) k + τ.1 ∧
      diagHi (ω.compose D) (k + Δ * ω.period) = diagHi (ω.compose D) k + τ.1 := by
  have := diag_shift_of_per (F := ω.compose D) (τ := τ) h.per hk h0 h1
  rwa [h.hτ] at this

theorem mem_contents_compose (h : PerData ω D a b Δ τ) {k : ℤ} :
    k ∈ contents (ω.compose D) ↔
      minContent ω.E + minContent D * ω.period ≤ k ∧
        k ≤ minContent ω.E + maxContent D * ω.period + ω.period + ω.width - 1 := by
  have hs := isConnectedSkew_iff_diagonal.mp (h.legal.isConnectedSkew_compose h.conn)
  rw [hs.mem_contents_iff, h.legal.minContent_compose h.conn, h.legal.maxContent_compose h.conn]

end PerData

end GluingCore
