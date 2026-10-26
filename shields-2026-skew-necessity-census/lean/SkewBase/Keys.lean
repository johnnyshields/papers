import Mathlib.Data.Prod.Lex
import SkewBase.ChartSize
import SkewBase.Copied.OuterTranslate
import SkewBase.Copied.Presentation

/-!
# Keys of minimal charts

Formalizes `shields-2026-skew-base-computational.tex`, «Keys and necessity» (`sec:keys`):
`def:key`.

The cost of a proper chart `F = D ∘_ω E` is the pair `(N_W, N_E)` of numbers of diagonals occupied
by `W` and `E`, ordered lexicographically; for a proper legal chart it equals
`(N_F mod q, q + N_F mod q)` (`Chart.cost_eq`, from `lem:copies` (iii)).  A chart is minimal for
`F` when it is a proper legal chart of `F` of least cost.  The key of a chart is its marked
inner up to translation and rotation together with the value `s D` of the outer function.
`keySet s F` is `K(F)`, the set of keys of the minimal charts of `F`.

The marked inner is taken up to translation and rotation, and no ordinary-gauge identification is
made: two minimal charts related by the gauge of `eq:gluing-gauge` have different keys here, as in
the paper.

Sorry-free.
-/

namespace SkewGluing

open SkewBase

variable {R : Type*}

/-! ### Marked inners up to translation and rotation -/

theorem rotate_translate (t : ℤ × ℤ) (D : Diagram) :
    rotate (translate t D) = translate (-t) (rotate D) := by
  ext y
  simp only [mem_rotate, mem_translate]
  have : -y - t = -(y - -t) := by abel
  rw [this]

namespace MarkedInner

theorem translateBy_zero (ω : MarkedInner) : ω.translateBy 0 = ω := by
  cases ω
  simp [translateBy, translate_zero]

theorem translateBy_translateBy (s t : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translateBy t).translateBy s = ω.translateBy (s + t) := by
  simp [translateBy, translate_translate]

theorem rotate_translateBy (t : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translateBy t).rotate = ω.rotate.translateBy (-t) := by
  have hE : (ω.translateBy t).rotate.E = (ω.rotate.translateBy (-t)).E := by
    simp [rotate, translateBy, rotate_translate]
  have hW : (ω.translateBy t).rotate.W = (ω.rotate.translateBy (-t)).W := by
    ext y
    simp only [rotate, translateBy, upper, mem_rotate, mem_translate]
    rw [show -y - ω.v - t = -y - t - ω.v by abel, show -(y - -t) - ω.v = -y - t - ω.v by abel]
  have hv : (ω.translateBy t).rotate.v = (ω.rotate.translateBy (-t)).v := rfl
  have hc : (ω.translateBy t).rotate.case = (ω.rotate.translateBy (-t)).case := rfl
  cases h1 : (ω.translateBy t).rotate
  cases h2 : (ω.rotate.translateBy (-t))
  rw [h1, h2] at hE hW hv hc
  simp_all

/-- The marked inners equal to `ω` up to translation and rotation. -/
def orbit (ω : MarkedInner) : Set MarkedInner :=
  {ω' | ω.EquivTranslate ω' ∨ ω.rotate.EquivTranslate ω'}

theorem mem_orbit_self (ω : MarkedInner) : ω ∈ ω.orbit :=
  Or.inl ⟨0, (translateBy_zero ω).symm⟩

/-- Equality up to translation and rotation is symmetric. -/
theorem orbit_symm {ω₁ ω₂ : MarkedInner} (h : ω₂ ∈ ω₁.orbit) : ω₁ ∈ ω₂.orbit := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · refine Or.inl ⟨-t, ?_⟩
    rw [translateBy_translateBy]; simp [translateBy_zero]
  · refine Or.inr ⟨t, ?_⟩
    rw [rotate_translateBy, rotate_rotate, translateBy_translateBy]
    simp [translateBy_zero]

/-- Equality up to translation and rotation is transitive. -/
theorem orbit_trans {ω₁ ω₂ ω₃ : MarkedInner} (h₁₂ : ω₂ ∈ ω₁.orbit) (h₂₃ : ω₃ ∈ ω₂.orbit) :
    ω₃ ∈ ω₁.orbit := by
  rcases h₁₂ with ⟨s, rfl⟩ | ⟨s, rfl⟩ <;> rcases h₂₃ with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact Or.inl ⟨t + s, by rw [translateBy_translateBy]⟩
  · refine Or.inr ⟨t - s, ?_⟩
    rw [rotate_translateBy, translateBy_translateBy]
    congr 1
  · exact Or.inr ⟨t + s, by rw [translateBy_translateBy]⟩
  · refine Or.inl ⟨t - s, ?_⟩
    rw [rotate_translateBy, rotate_rotate, translateBy_translateBy]
    congr 1

/-- Two marked inners have the same orbit exactly when they are equal up to translation and
rotation. -/
theorem orbit_eq_iff {ω₁ ω₂ : MarkedInner} : ω₁.orbit = ω₂.orbit ↔ ω₂ ∈ ω₁.orbit := by
  constructor
  · intro h
    rw [h]
    exact mem_orbit_self ω₂
  · intro h
    ext x
    exact ⟨fun hx => orbit_trans (orbit_symm h) hx, fun hx => orbit_trans h hx⟩

end MarkedInner

/-! ### Cost, minimal charts and keys -/

namespace Chart

/-- The cost `(N_W, N_E)` of a chart, the numbers of diagonals occupied by `W` and by `E`, ordered
lexicographically. -/
def cost (χ : Chart) : Lex (ℕ × ℕ) := toLex (χ.ω.width, span χ.ω.E)

/-- **`sec:keys`, the cost of a proper legal chart.**  For a chart of `F` of period `q`, the cost
is `(N_F mod q, q + N_F mod q)`. -/
theorem cost_eq {χ : Chart} {F : Diagram} (hχ : χ.IsProperLegal) (hF : χ.IsChartOf F) :
    ((ofLex χ.cost).1 : ℤ) = (span F : ℤ) % χ.ω.period ∧
      ((ofLex χ.cost).2 : ℤ) = χ.ω.period + (span F : ℤ) % χ.ω.period := by
  obtain ⟨t, rfl⟩ := hF
  have hspan : span (translate t χ.parent) = span (χ.ω.compose χ.D) := by
    rw [span_translate]; rfl
  have h1 := (width_eq_span_mod hχ.2.2.2 hχ.1).1
  have h2 := span_inner_eq hχ.2.2.2
  simp only [cost, ofLex_toLex]
  rw [hspan]
  exact ⟨h1, by rw [h2, h1]⟩

/-- `χ` is a minimal chart of `F`: a proper legal chart of `F` whose cost is least among the
proper legal charts of `F`. -/
def IsMinimalOf (χ : Chart) (F : Diagram) : Prop :=
  χ.IsProperLegal ∧ χ.IsChartOf F ∧
    ∀ χ' : Chart, χ'.IsProperLegal → χ'.IsChartOf F → χ.cost ≤ χ'.cost

end Chart

/-- The key of a proper chart `F = D ∘_ω E`: `ω` up to translation and rotation, and the outer
value `s D`. -/
def Key (R : Type*) : Type _ := Set MarkedInner × R

/-- The key of a chart, for the outer function `s`. -/
def Chart.key (s : Diagram → R) (χ : Chart) : Key R := (χ.ω.orbit, s χ.D)

/-- `K(F)`: the keys of the minimal charts of `F`. -/
def keySet (s : Diagram → R) (F : Diagram) : Set (Key R) :=
  {k | ∃ χ : Chart, χ.IsMinimalOf F ∧ χ.key s = k}

/-- A common key gives proper legal charts of the two diagrams whose marked inners agree up to
translation and rotation and whose outers have the same value of `s`. -/
theorem exists_charts_of_mem_keySet_inter {s : Diagram → R} {F G : Diagram} {k : Key R}
    (hF : k ∈ keySet s F) (hG : k ∈ keySet s G) :
    ∃ χ₁ χ₂ : Chart, χ₁.IsProperLegal ∧ χ₂.IsProperLegal ∧ χ₁.IsChartOf F ∧ χ₂.IsChartOf G ∧
      (χ₁.ω.EquivTranslate χ₂.ω ∨ χ₁.ω.rotate.EquivTranslate χ₂.ω) ∧ s χ₁.D = s χ₂.D := by
  obtain ⟨χ₁, ⟨h₁, c₁, -⟩, rfl⟩ := hF
  obtain ⟨χ₂, ⟨h₂, c₂, -⟩, hk⟩ := hG
  have hω : χ₁.ω.orbit = χ₂.ω.orbit := congrArg Prod.fst hk.symm
  exact ⟨χ₁, χ₂, h₁, h₂, c₁, c₂, MarkedInner.orbit_eq_iff.mp hω, congrArg Prod.snd hk.symm⟩

end SkewGluing
