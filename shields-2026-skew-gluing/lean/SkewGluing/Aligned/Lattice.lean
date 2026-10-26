import SkewGluing.Local

/-!
# The lattice map of an ordinary mark and reassociation of ordinary compositions

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-reassociation`, `eq:gluing-offsets`, `eq:gluing-gauge`).

For an ordinary mark `ω` (case (a) or (b)) the copy origin of `eq:gluing-offsets` is the value at
`d` of the additive map `L_ω(t) = c(t) v + (±t₁) e` (the lattice map of the paper, `L(i, i+j) =
j v + i e` in case (a)).  Because `L_ω` is additive, composing an ordinary composition with an
ordinary mark is again an ordinary composition: `MarkedInner.compose_reassoc_ordinary` is the
cell identity `eq:gluing-reassociation` for ordinary marks, with `γ` any cell map `g` and the
displacement relation read off the origins.  The two instances used by the lemma are `γ = id`
and `γ = AT` (the latter being the gauge `eq:gluing-gauge` for a vertical edge reading).

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω μ η : MarkedInner}

/-- The sign `+1` in case (a) and `-1` in case (b), the coefficient of the row coordinate in the
origin `L_ω` of an ordinary mark. -/
def ordSign (ω : MarkedInner) : ℤ := if ω.case = .b then -1 else 1

/-- The lattice map `L_ω(t) = c(t) v + (±t₁) e` of an ordinary mark: `L(i, i + j) = j v + i e` in
case (a), `j v - i e` in case (b). -/
def lat (ω : MarkedInner) (t : ℤ × ℤ) : ℤ × ℤ := content t • ω.v + (ω.ordSign * t.1) • eCell

theorem origin_eq_lat (h : ¬ ω.case.IsMixed) (D : Diagram) (d : ℤ × ℤ) :
    ω.origin D d = ω.lat d := by
  unfold origin lat ordSign
  unfold AttachCase.IsMixed at h
  cases hc : ω.case <;> simp_all [sub_eq_add_neg, neg_smul]

theorem lat_add (ω : MarkedInner) (t u : ℤ × ℤ) : ω.lat (t + u) = ω.lat t + ω.lat u := by
  unfold lat
  ext <;> simp [content, eCell] <;> ring

theorem lat_smul_eCell (ω : MarkedInner) (n : ℤ) : ω.lat (n • eCell) = (ω.ordSign * n) • eCell := by
  unfold lat
  ext <;> simp [content, eCell]

theorem lat_eCell (ω : MarkedInner) : ω.lat eCell = ω.ordSign • eCell := by
  have := ω.lat_smul_eCell 1
  simpa using this

theorem lat_lat (ω μ : MarkedInner) (t : ℤ × ℤ) :
    ω.lat (μ.lat t) =
      content t • ω.lat μ.v + (ω.ordSign * (μ.ordSign * t.1)) • eCell := by
  unfold lat
  ext <;> simp [content, eCell] <;> ring

/-- **`eq:gluing-reassociation` for ordinary marks, cell form.**  Let `ω`, `μ`, `η` be ordinary
marks, `μ` on `V`, `η` on `U = V ∘_ω E`, and let `g` be a cell map.  If the origin of `η` at
each cell `d` of `C` is `L_ω (L_μ (g d))`, then
`C ∘_η U = (C' ∘_μ V) ∘_ω E` with `C' = g(C)`, as sets of cells. -/
theorem compose_reassoc_ordinary (hω : ¬ ω.case.IsMixed) (hμ : ¬ μ.case.IsMixed)
    (hη : ¬ η.case.IsMixed) {V C : Diagram} (hV : V.Nonempty) (hC : C.Nonempty)
    (g : ℤ × ℤ → ℤ × ℤ) (hU : η.E = ω.compose V) (hVμ : μ.E = V)
    (hg : ∀ d, η.lat d = ω.lat (μ.lat (g d))) :
    η.compose C = ω.compose (μ.compose (C.image g)) := by
  have hC' : (C.image g).Nonempty := hC.image g
  have hμC : (μ.compose (C.image g)).Nonempty := by
    obtain ⟨d, hd⟩ := hC'
    obtain ⟨y, hy⟩ := hV
    refine ⟨y + μ.origin (C.image g) d, ?_⟩
    rw [compose_of_ordinary ⟨d, hd⟩ hμ]
    exact ⟨d, hd, by rw [mem_translate, hVμ]; simpa using hy⟩
  ext x
  rw [compose_of_ordinary hC hη, compose_of_ordinary hμC hω]
  constructor
  · rintro ⟨d, hd, hx⟩
    rw [mem_translate, hU, compose_of_ordinary hV hω] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [mem_translate] at hxy
    refine ⟨y + μ.lat (g d), ?_, ?_⟩
    · rw [compose_of_ordinary hC' hμ]
      refine ⟨g d, Finset.mem_image_of_mem g hd, ?_⟩
      rw [mem_translate, hVμ, origin_eq_lat hμ]
      simpa using hy
    · rw [mem_translate, origin_eq_lat hω, lat_add]
      rw [origin_eq_lat hη, hg, origin_eq_lat hω] at hxy
      have e : x - (ω.lat y + ω.lat (μ.lat (g d))) = x - ω.lat (μ.lat (g d)) - ω.lat y := by
        abel
      rw [e]; exact hxy
  · rintro ⟨d', hd', hx⟩
    rw [compose_of_ordinary hC' hμ] at hd'
    obtain ⟨d'', hd'', hd'⟩ := hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd''
    rw [mem_translate, hVμ, origin_eq_lat hμ] at hd'
    rw [mem_translate, origin_eq_lat hω] at hx
    refine ⟨d, hd, ?_⟩
    rw [mem_translate, hU, compose_of_ordinary hV hω]
    refine ⟨d' - μ.lat (g d), hd', ?_⟩
    rw [mem_translate, origin_eq_lat hη, hg]
    have : d' = (d' - μ.lat (g d)) + μ.lat (g d) := by abel
    rw [this, lat_add] at hx
    have e : x - ω.lat (μ.lat (g d)) - ω.lat (d' - μ.lat (g d)) =
        x - (ω.lat (d' - μ.lat (g d)) + ω.lat (μ.lat (g d))) := by abel
    rw [origin_eq_lat hω, e]; exact hx

end MarkedInner

end SkewGluing
