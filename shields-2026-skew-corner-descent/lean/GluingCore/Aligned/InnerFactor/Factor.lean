/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/InnerFactor/Factor.lean`. -/
import GluingCore.Aligned.InnerFactor.Rows
import GluingCore.Aligned.InnerFactor.Locality

/-!
# The inner factor of a divisible chart

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`).

Let `D` be a connected outer with contents `[m₀, m₀ + r - 1]`, let `0 ≤ b < a` and `m = a + b`,
`Δ = r - m`.  If the diagonals `[m₀ + b, m₀ + a - 1]` of `D` are translates, by one common row
shift `z₁`, of the diagonals `Δ` further along (`FactorData`), the union `V` of the diagonals
`[m₀, m₀ + a - 1]` of `D` and the diagonals `[m₀ + r - a, m₀ + r - 1]` of `D` translated by
`-(z₁, z₁ + Δ)` is a connected skew diagram of span `m` (`innerFactor`).  By locality of
composition the window of `V ∘_ω E` on the first `a q` diagonals is that of `D ∘_ω E`, and its
window from the diagonal `b q + w` on is the translate of that of `D ∘_ω E` by `-T`.

Sorry-free.
-/

namespace GluingCore

/-- The data of the inner factor: a connected outer `D`, with `0 ≤ b < a`, `Δ ≥ 0`,
`N_D = a + b + Δ`, and the diagonals `[m₀ + b, m₀ + a - 1]` repeated `Δ` diagonals later with the
row shift `z₁`. -/
structure FactorData (D : Diagram) (a b Δ z₁ : ℤ) : Prop where
  conn : IsConnectedSkew D
  ha : 1 ≤ a
  hb : 0 ≤ b
  hba : b < a
  hΔ : 0 ≤ Δ
  hM : maxContent D = minContent D + a + b - 1 + Δ
  agree : ∀ k, minContent D + b ≤ k → k ≤ minContent D + a - 1 →
    diagLo D (k + Δ) = diagLo D k + z₁ ∧ diagHi D (k + Δ) = diagHi D k + z₁

/-- The first row of the diagonal `k` of the inner factor. -/
def factorLo (D : Diagram) (a Δ z₁ k : ℤ) : ℤ :=
  if k ≤ minContent D + a - 1 then diagLo D k else diagLo D (k + Δ) - z₁

/-- The last row of the diagonal `k` of the inner factor. -/
def factorHi (D : Diagram) (a Δ z₁ k : ℤ) : ℤ :=
  if k ≤ minContent D + a - 1 then diagHi D k else diagHi D (k + Δ) - z₁

/-- The inner factor `V`: the diagonals `[m₀, m₀ + a - 1]` of `D`, followed by the diagonals
`[m₀ + a + Δ, m₀ + a + b + Δ - 1]` of `D` moved back by `Δ` diagonals. -/
def innerFactor (D : Diagram) (a b Δ z₁ : ℤ) : Diagram :=
  rowsDiagram (minContent D) (minContent D + a + b - 1) (factorLo D a Δ z₁) (factorHi D a Δ z₁)

namespace FactorData

variable {D : Diagram} {a b Δ z₁ : ℤ}

theorem hs (h : FactorData D a b Δ z₁) : HasDiagonalShape D :=
  isConnectedSkew_iff_diagonal.mp h.conn

theorem mem_contents (h : FactorData D a b Δ z₁) {k : ℤ} :
    k ∈ contents D ↔ minContent D ≤ k ∧ k ≤ maxContent D :=
  h.hs.mem_contents_iff

theorem factorLo_of_le {k : ℤ} (hk : k ≤ minContent D + a - 1) :
    factorLo D a Δ z₁ k = diagLo D k := by
  simp [factorLo, hk]

theorem factorHi_of_le {k : ℤ} (hk : k ≤ minContent D + a - 1) :
    factorHi D a Δ z₁ k = diagHi D k := by
  simp [factorHi, hk]

theorem factorLo_shift (h : FactorData D a b Δ z₁) {k : ℤ} (hk : minContent D + b ≤ k) :
    factorLo D a Δ z₁ k = diagLo D (k + Δ) - z₁ := by
  by_cases hc : k ≤ minContent D + a - 1
  · rw [factorLo_of_le hc]
    have := (h.agree k hk hc).1
    omega
  · simp [factorLo, hc]

theorem factorHi_shift (h : FactorData D a b Δ z₁) {k : ℤ} (hk : minContent D + b ≤ k) :
    factorHi D a Δ z₁ k = diagHi D (k + Δ) - z₁ := by
  by_cases hc : k ≤ minContent D + a - 1
  · rw [factorHi_of_le hc]
    have := (h.agree k hk hc).2
    omega
  · simp [factorHi, hc]

theorem rowsData (h : FactorData D a b Δ z₁) :
    RowsData (minContent D) (minContent D + a + b - 1) (factorLo D a Δ z₁)
      (factorHi D a Δ z₁) := by
  have hs := h.hs
  have hM := h.hM
  have ha := h.ha
  have hb := h.hb
  have hba := h.hba
  have hΔ := h.hΔ
  have hends := MarkedInner.D_ends h.conn
  have hmem : ∀ k, minContent D ≤ k → k ≤ maxContent D → k ∈ contents D := fun k h1 h2 =>
    h.mem_contents.mpr ⟨h1, h2⟩
  refine ⟨by have := h.ha; omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro k h1 h2
    by_cases hc : k ≤ minContent D + a - 1
    · rw [factorLo_of_le hc, factorHi_of_le hc]
      exact diagLo_le_diagHi (hmem k h1 (by omega))
    · have e1 := h.factorLo_shift (k := k) (by omega)
      have e2 := h.factorHi_shift (k := k) (by omega)
      have := diagLo_le_diagHi (hmem (k + Δ) (by omega) (by omega))
      omega
  · intro k h1 h2
    have hb := MarkedInner.D_bits h.conn (J := k + Δ) (by omega) (by omega)
    have hb1 := MarkedInner.D_bits h.conn (J := k) (by omega) (by omega)
    by_cases hk : k ≤ minContent D + a - 1
    · rw [factorLo_of_le hk, factorLo_of_le (by omega)]
      exact hb1.1
    · have e1 := h.factorLo_shift (k := k) (by omega)
      have e2 := h.factorLo_shift (k := k - 1) (by omega)
      have e3 : k - 1 + Δ = k + Δ - 1 := by ring
      rw [e3] at e2
      rw [e1, e2]
      rcases hb.1 with h3 | h3
      · left; omega
      · right; omega
  · intro k h1 h2
    have hb := MarkedInner.D_bits h.conn (J := k + Δ) (by omega) (by omega)
    have hb1 := MarkedInner.D_bits h.conn (J := k) (by omega) (by omega)
    by_cases hk : k ≤ minContent D + a - 1
    · rw [factorHi_of_le hk, factorHi_of_le (by omega)]
      exact hb1.2
    · have e1 := h.factorHi_shift (k := k) (by omega)
      have e2 := h.factorHi_shift (k := k - 1) (by omega)
      have e3 : k - 1 + Δ = k + Δ - 1 := by ring
      rw [e3] at e2
      rw [e1, e2]
      rcases hb.2 with h3 | h3
      · left; omega
      · right; omega
  · rw [factorLo_of_le (by omega), factorHi_of_le (by omega)]
    exact hends.1
  · have e1 := h.factorLo_shift (k := minContent D + a + b - 1) (by have := h.ha; omega)
    have e2 := h.factorHi_shift (k := minContent D + a + b - 1) (by have := h.ha; omega)
    rw [e1, e2]
    have : minContent D + a + b - 1 + Δ = maxContent D := by omega
    rw [this]
    have := hends.2
    omega

theorem isConnectedSkew_innerFactor (h : FactorData D a b Δ z₁) :
    IsConnectedSkew (innerFactor D a b Δ z₁) :=
  RowsDiagram.isConnectedSkew h.rowsData

theorem minContent_innerFactor (h : FactorData D a b Δ z₁) :
    minContent (innerFactor D a b Δ z₁) = minContent D :=
  RowsDiagram.minContent_eq h.rowsData

theorem maxContent_innerFactor (h : FactorData D a b Δ z₁) :
    maxContent (innerFactor D a b Δ z₁) = minContent D + a + b - 1 :=
  RowsDiagram.maxContent_eq h.rowsData

theorem span_innerFactor (h : FactorData D a b Δ z₁) :
    (span (innerFactor D a b Δ z₁) : ℤ) = a + b := by
  have := RowsDiagram.span_eq h.rowsData
  unfold innerFactor
  omega

theorem nonempty_innerFactor (h : FactorData D a b Δ z₁) : (innerFactor D a b Δ z₁).Nonempty :=
  h.isConnectedSkew_innerFactor.2.1

/-- The inner factor has the cells of `D` on the contents `≤ m₀ + a - 1`. -/
theorem mem_innerFactor_iff_prefix (h : FactorData D a b Δ z₁) {x : ℤ × ℤ}
    (hx : content x ≤ minContent D + a - 1) : x ∈ innerFactor D a b Δ z₁ ↔ x ∈ D := by
  rw [innerFactor, RowsDiagram.mem_iff', h.hs.mem_iff', h.mem_contents]
  have hM := h.hM
  have ha := h.ha
  have hb := h.hb
  have hΔ := h.hΔ
  rw [factorLo_of_le hx, factorHi_of_le hx]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, by omega⟩, h3, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, by omega⟩, h3, h4⟩

/-- The inner factor on the contents `≥ m₀ + b` is `D` on the contents `≥ m₀ + b + Δ`, moved by
`-(z₁, z₁ + Δ)`. -/
theorem mem_innerFactor_iff_suffix (h : FactorData D a b Δ z₁) {x : ℤ × ℤ}
    (hx : minContent D + b ≤ content x) :
    x ∈ innerFactor D a b Δ z₁ ↔ x + (z₁, z₁ + Δ) ∈ D := by
  have hc : content (x + (z₁, z₁ + Δ)) = content x + Δ := by
    rw [content_add]; simp [content]
  rw [innerFactor, RowsDiagram.mem_iff', h.hs.mem_iff', h.mem_contents, hc]
  have hM := h.hM
  have hΔ := h.hΔ
  have hb := h.hb
  have hlo := h.factorLo_shift (k := content x) hx
  have hhi := h.factorHi_shift (k := content x) hx
  have h1 : (x + (z₁, z₁ + Δ)).1 = x.1 + z₁ := rfl
  rw [hlo, hhi, h1]
  have hmD : minContent D ≤ content x + Δ := by omega
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨hmD, by omega⟩, by omega, by omega⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

end FactorData

/-! ## Checked examples -/

/-- `(12) = (6) ∘ (2) = (3) ∘ (4)`: the inner factor of the row `(6)` with `a = 2`, `b = 0`,
`Δ = 4` is the row `(2)`. -/
example : innerFactor (skewOf [6] []) 2 0 4 0 = skewOf [2] [] := by decide +kernel

/-- The same for the column of six cells, where the repetition moves the rows by `-4`. -/
example : normalize (innerFactor (skewOf [1, 1, 1, 1, 1, 1] []) 2 0 4 (-4)) =
    normalize (skewOf [1, 1] []) := by decide +kernel

end GluingCore
