/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/InnerFactor/Windows.lean`. -/
import GluingCore.Aligned.InnerFactor.Factor
import GluingCore.Aligned.InnerFactor.Locality

/-!
# Windows of the composite with the inner factor

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`), via `eq:gluing-offsets` and locality of composition.

For `V = innerFactor D a b Δ z₁` and a legal mark `ω` of period `q` and width `w`, the cells of
`V ∘_ω E` on the contents `< c₀ + (m₀ + a) q` are those of `D ∘_ω E`
(`FactorData.mem_compose_iff_prefix`); the cells on the contents `≥ c₀ + (m₀ + b) q + w` are
those of `D ∘_ω E`, moved back by the vector `factorShift ω Δ z₁` of content `Δ q`
(`FactorData.mem_compose_iff_suffix`).  The vector is `Δ v ± z₁ e` for an ordinary mark and
`Δ v` for a mixed one.

Sorry-free.
-/

namespace GluingCore

open MarkedInner

/-- The vector by which the origins of the copies move when the outer moves `Δ` diagonals along
and `z₁` rows: `Δ v + z₁ e` in case (a), `Δ v - z₁ e` in case (b), `Δ v` in the mixed
cases. -/
def factorShift (ω : MarkedInner) (Δ z₁ : ℤ) : ℤ × ℤ :=
  match ω.case with
  | .a => Δ • ω.v + z₁ • eCell
  | .b => Δ • ω.v - z₁ • eCell
  | .c => Δ • ω.v
  | .d => Δ • ω.v

theorem content_factorShift (ω : MarkedInner) (Δ z₁ : ℤ) :
    content (factorShift ω Δ z₁) = Δ * ω.period := by
  have h : ∀ n : ℤ, content (n • eCell) = 0 := by intro n; simp [content, eCell]
  have hv : content ω.v = ω.period := rfl
  unfold factorShift
  cases ω.case <;> simp [content_add, content_sub, content_smul, h, hv]

namespace FactorData

variable {D : Diagram} {a b Δ z₁ : ℤ}

theorem diagLo_innerFactor (h : FactorData D a b Δ z₁) {k : ℤ} (h1 : minContent D + b ≤ k)
    (h2 : k ≤ minContent D + a + b - 1) :
    diagLo (innerFactor D a b Δ z₁) k = diagLo D (k + Δ) - z₁ := by
  have := h.ha
  have := h.hb
  rw [innerFactor, RowsDiagram.diagLo_eq h.rowsData (by omega) h2, h.factorLo_shift h1]

theorem diagHi_innerFactor (h : FactorData D a b Δ z₁) {k : ℤ} (h1 : minContent D + b ≤ k)
    (h2 : k ≤ minContent D + a + b - 1) :
    diagHi (innerFactor D a b Δ z₁) k = diagHi D (k + Δ) - z₁ := by
  have := h.ha
  have := h.hb
  rw [innerFactor, RowsDiagram.diagHi_eq h.rowsData (by omega) h2, h.factorHi_shift h1]

theorem origin_innerFactor (h : FactorData D a b Δ z₁) (ω : MarkedInner) {d : ℤ × ℤ}
    (hd : d ∈ innerFactor D a b Δ z₁) (hdb : minContent D + b ≤ content d) :
    ω.origin (innerFactor D a b Δ z₁) d + factorShift ω Δ z₁ =
      ω.origin D (d + (z₁, z₁ + Δ)) := by
  have hdM : content d ≤ minContent D + a + b - 1 := by
    have := (RowsDiagram.mem_iff'.mp hd).1.2
    exact this
  have hc : content (d + (z₁, z₁ + Δ)) = content d + Δ := by
    rw [content_add]; simp [content]
  have hlo := h.diagLo_innerFactor hdb hdM
  have hhi := h.diagHi_innerFactor hdb hdM
  unfold origin factorShift
  rw [hc]
  cases ω.case
  · ext <;> simp [content, eCell] <;> ring
  · ext <;> simp [content, eCell] <;> ring
  · simp only [hlo]
    ext <;> simp [content, eCell] <;> ring
  · simp only [hhi]
    ext <;> simp [content, eCell] <;> ring

theorem sameRibbon_innerFactor (h : FactorData D a b Δ z₁) (ω : MarkedInner) {d : ℤ × ℤ}
    (hdb : minContent D + b ≤ content d) :
    ω.SameRibbon (innerFactor D a b Δ z₁) d ↔ ω.SameRibbon D (d + (z₁, z₁ + Δ)) := by
  have hc : content (d + (z₁, z₁ + Δ)) = content d + Δ := by
    rw [content_add]; simp [content]
  have hcn : content (d.1 - 1, d.2) = content d + 1 := by simp only [content]; ring
  have hcell : ((d + (z₁, z₁ + Δ)).1 - 1, (d + (z₁, z₁ + Δ)).2) =
      (d.1 - 1, d.2) + (z₁, z₁ + Δ) := by
    ext <;> (simp; try ring)
  have hf : (d + (z₁, z₁ + Δ)).1 = d.1 + z₁ := rfl
  have hmem : (d.1 - 1, d.2) ∈ innerFactor D a b Δ z₁ ↔
      ((d + (z₁, z₁ + Δ)).1 - 1, (d + (z₁, z₁ + Δ)).2) ∈ D := by
    rw [hcell]
    exact h.mem_innerFactor_iff_suffix (x := (d.1 - 1, d.2)) (by omega)
  unfold SameRibbon
  rw [hc]
  by_cases hn : (d.1 - 1, d.2) ∈ innerFactor D a b Δ z₁
  · have hn' := hmem.mp hn
    have hdM : content d + 1 ≤ minContent D + a + b - 1 := by
      have := (RowsDiagram.mem_iff'.mp hn).1.2
      rw [hcn] at this
      exact this
    have hlo := h.diagLo_innerFactor hdb (by omega)
    have hhi := h.diagHi_innerFactor hdb (by omega)
    have hlo1 := h.diagLo_innerFactor (k := content d + 1) (by omega) hdM
    have hhi1 := h.diagHi_innerFactor (k := content d + 1) (by omega) hdM
    cases hcs : ω.case
    · simp only [hn, hn', true_and]
    · simp only [hn, hn', true_and]
    · have e : content d + Δ + 1 = content d + 1 + Δ := by ring
      simp only [hn, hn', true_and, hlo, hlo1, e]
      rw [hf]
      omega
    · have e : content d + Δ + 1 = content d + 1 + Δ := by ring
      simp only [hn, hn', true_and, hhi, hhi1, e]
      rw [hf]
      omega
  · have hn' : ¬ ((d + (z₁, z₁ + Δ)).1 - 1, (d + (z₁, z₁ + Δ)).2) ∈ D := fun hh => hn (hmem.mpr hh)
    simp only [hn, hn', false_and]

/-- Prefix window: the cells of `V ∘_ω E` on the contents `< c₀ + (m₀ + a) q` are those of
`D ∘_ω E`. -/
theorem mem_compose_iff_prefix (h : FactorData D a b Δ z₁) {ω : MarkedInner} (hω : ω.IsLegal)
    {x : ℤ × ℤ} (hx : content x ≤ minContent ω.E + (minContent D + a) * ω.period - 1) :
    x ∈ ω.compose (innerFactor D a b Δ z₁) ↔ x ∈ ω.compose D := by
  refine mem_compose_iff_of_prefix hω h.nonempty_innerFactor h.conn.2.1
    (K := minContent D + a - 1) (fun y hy => h.mem_innerFactor_iff_prefix hy) ?_
  have : minContent D + a - 1 + 1 = minContent D + a := by ring
  rw [this]
  exact hx

/-- Suffix window: the cells of `V ∘_ω E` on the contents `≥ c₀ + (m₀ + b) q + w` are those of
`D ∘_ω E` moved back by `factorShift ω Δ z₁`. -/
theorem mem_compose_iff_suffix (h : FactorData D a b Δ z₁) {ω : MarkedInner} (hω : ω.IsLegal)
    {x : ℤ × ℤ}
    (hx : minContent ω.E + (minContent D + b) * ω.period + ω.width ≤ content x) :
    x ∈ ω.compose (innerFactor D a b Δ z₁) ↔ x + factorShift ω Δ z₁ ∈ ω.compose D := by
  refine mem_compose_iff_of_shift hω h.nonempty_innerFactor h.conn.2.1
    (z := (z₁, z₁ + Δ)) (J := minContent D + b) ?_ (fun y hy => h.mem_innerFactor_iff_suffix hy)
    (fun d hd hdb => h.origin_innerFactor ω hd hdb)
    (fun d _ hdb => h.sameRibbon_innerFactor ω hdb) hx
  rw [content_factorShift]
  simp [content]

end FactorData

end GluingCore
