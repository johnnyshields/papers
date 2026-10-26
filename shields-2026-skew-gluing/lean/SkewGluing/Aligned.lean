import SkewGluing.Aligned.Statement
import SkewGluing.Invariance
import SkewGluing.Aligned.CaseD
import SkewGluing.Aligned.OrdinaryLower
import SkewGluing.Aligned.MixedEta

/-!
# Aligned marks: reassociation through a chart

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-reassociation`, `eq:gluing-walk-signs`,
`eq:gluing-nested-count`, `eq:gluing-gauge`).

`MarkedInner.IsLegal.aligned` is `lem:gluing-aligned`: for `U = V ∘_ω E` and a legal mark `η` on
`U` whose displacement has content `a q`, there are a legal mark `μ` on `V` and
`γ ∈ {id, AT}` (with `γ = AT` only for the empty `μ`) such that `C ∘_η U = (γ(C) ∘_μ V) ∘_ω E`
for every connected `C` (`IsReassociation`).

The proof is organized by the case of `ω`:

* the cell identity for ordinary `ω` and ordinary `η`, from the additive lattice map of
  `Aligned/Lattice.lean` (`compose_reassoc_ordinary`), is proved;
* case (c) is deduced from case (d) by rotation (`rotate_compose`);
* the width-zero lower mark `μ` is the empty mark, legal on every connected `V`
  (`emptyMarkH_isLegal`).

The remaining cases are proved in their own modules: ordinary lower marks and the `b = 0` edge
case in `SkewGluing.Aligned.OrdinaryLower`, an ordinary `ω` with a mixed `η` in
`SkewGluing.Aligned.MixedEta`, and case (d) of `ω` (the walk `eq:gluing-walk-signs` and the nested
count `eq:gluing-nested-count`) in `SkewGluing.Aligned.CaseD`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

/-- **`lem:gluing-aligned`, ordinary lower marks (legality).**  For an ordinary `ω`, an ordinary
`η` on `U = V ∘_ω E` of displacement content `a q` and `a < N_V` (that is, `b > 0`), there is a
legal ordinary mark `μ` on `V`, namely `Z = V ∩ (V - z)` with `L_ω(z) = v_η`, with
`v_η = L_ω(v_μ)` and the case of `η` the product of those of `ω` and `μ`.  The proof is in
`SkewGluing.Aligned.OrdinaryLower`. -/
theorem exists_lowerMark_ordinary (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed)
    (hV : IsConnectedSkew V) (hη : η.IsLegal) (hηord : ¬ η.case.IsMixed)
    (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hpos : a < (span V : ℤ)) :
    ∃ μ : MarkedInner, μ.IsLegal ∧ μ.E = V ∧ ¬ μ.case.IsMixed ∧ η.v = ω.lat μ.v ∧
      η.ordSign = ω.ordSign * μ.ordSign :=
  exists_lowerMark_ordinary_proof hω hord hV hη hηord hU ha hpos

/-- **`lem:gluing-aligned`, ordinary case, `b = 0`.**  For an ordinary `ω` and an ordinary `η` on
`U = V ∘_ω E` with displacement content `N_V q`, the displacement of `η` is the image under
`L_ω` of one of the two edge readings `v_H`, `v_V = v_H - e` of `V`, and the case of `η` is
that of the product with the empty mark (horizontal reading) or the opposite one (vertical
reading, the gauge of `eq:gluing-gauge`).  The proof is in
`SkewGluing.Aligned.OrdinaryLower`. -/
theorem ordinary_edge_displacement (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed)
    (hV : IsConnectedSkew V) (hη : η.IsLegal) (hηord : ¬ η.case.IsMixed)
    (hU : η.E = ω.compose V) (ha : content η.v = (span V : ℤ) * ω.period) :
    (η.v = ω.lat (vH V) ∧ η.ordSign = ω.ordSign) ∨
      (η.v = ω.lat (vH V) - ω.ordSign • eCell ∧ η.ordSign = -ω.ordSign) :=
  ordinary_edge_displacement_proof hω hord hV hη hηord hU ha

/-- **`lem:gluing-aligned`, ordinary `ω` and mixed `η`.**

The proof is in `SkewGluing.Aligned.MixedEta`. -/
theorem aligned_ordinary_mixed_eta (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed)
    (hV : IsConnectedSkew V) (hη : η.IsLegal) (hηmix : η.case.IsMixed)
    (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    ∃ (μ : MarkedInner) (γ : Diagram → Diagram), IsReassociation ω η V μ γ :=
  aligned_ordinary_mixed_eta_proof hω hord hV hη hηmix hU ha

/-- **`lem:gluing-aligned`, case (d) of `ω`**: the southeast boundary is periodic, the walk
`eq:gluing-walk-signs` fixes the displacement `a v` and the lower mark `Z = V ∩ (V - z)` with
`z = (θ, θ + a)`, and the nested count `eq:gluing-nested-count` gives the identity.  The
proof is in `SkewGluing.Aligned.CaseD`. -/
theorem aligned_mixed_d (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    ∃ (μ : MarkedInner) (γ : Diagram → Diagram), IsReassociation ω η V μ γ :=
  aligned_mixed_d_proof hω hd hV hη hU ha

/-! ### Assembly for ordinary `ω` and `η` -/

theorem lat_eq_of_relation {ω μ η : MarkedInner} (hv : η.v = ω.lat μ.v)
    (hs : η.ordSign = ω.ordSign * μ.ordSign) (d : ℤ × ℤ) : η.lat d = ω.lat (μ.lat d) := by
  rw [lat_lat]
  unfold lat
  rw [hv, hs]
  ext <;> simp [lat, content, eCell] <;> ring

theorem aligned_ordinary (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hηord : ¬ η.case.IsMixed) (hU : η.E = ω.compose V) {a : ℤ}
    (ha : content η.v = a * ω.period) :
    ∃ (μ : MarkedInner) (γ : Diagram → Diagram), IsReassociation ω η V μ γ := by
  have hle := eta_le_span hω hV hη hU ha
  rcases lt_or_eq_of_le hle with hlt | heq
  · obtain ⟨μ, hμ, hμV, hμord, hv, hs⟩ :=
      exists_lowerMark_ordinary hω hord hV hη hηord hU ha hlt
    refine ⟨μ, id, ⟨hμ, hμV, Or.inl rfl, ?_⟩⟩
    intro C hC
    have := compose_reassoc_ordinary hord hμord hηord hV.2.1 hC.2.1 id hU hμV
      (lat_eq_of_relation hv hs)
    simpa using this
  · have hμ := emptyMarkH_isLegal hV
    have hμord : ¬ (emptyMarkH V).case.IsMixed := by
      simp [emptyMarkH, AttachCase.IsMixed]
    have hsμ : (emptyMarkH V).ordSign = 1 := by simp [ordSign, emptyMarkH]
    have hμv : (emptyMarkH V).v = vH V := rfl
    have hsω : ω.ordSign = 1 ∨ ω.ordSign = -1 := by unfold ordSign; split_ifs <;> simp
    have hedge := ordinary_edge_displacement hω hord hV hη hηord hU (by rw [ha, heq])
    rcases hedge with ⟨hv, hs⟩ | ⟨hv, hs⟩
    · refine ⟨emptyMarkH V, id, ⟨hμ, rfl, Or.inl rfl, ?_⟩⟩
      intro C hC
      have := compose_reassoc_ordinary hord hμord hηord hV.2.1 hC.2.1 id hU rfl
        (lat_eq_of_relation (by rw [hμv]; exact hv) (by rw [hs, hsμ]; ring))
      simpa using this
    · refine ⟨emptyMarkH V, antitranspose, ⟨hμ, rfl, Or.inr ⟨rfl, rfl⟩, ?_⟩⟩
      intro C hC
      refine compose_reassoc_ordinary hord hμord hηord hV.2.1 hC.2.1
        (fun x => (-x.2, -x.1)) hU rfl ?_
      intro d
      rw [lat_lat]
      unfold lat
      rw [hv, hsμ, hμv]
      ext <;> simp [lat, content, eCell, hs] <;> ring

/-! ### Case (c) by rotation, and the lemma -/

theorem IsReassociation.rotate {ω η : MarkedInner} {V : Diagram} {μ : MarkedInner}
    {γ : Diagram → Diagram} (hV : V.Nonempty)
    (h : IsReassociation ω.rotate η.rotate (SkewGluing.rotate V) μ γ) :
    IsReassociation ω η V μ.rotate γ := by
  refine ⟨isLegal_rotate h.legal, ?_, ?_, ?_⟩
  · change SkewGluing.rotate μ.E = V
    rw [h.inner, SkewGluing.rotate_rotate]
  · rcases h.gamma with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h1, ?_⟩
      change SkewGluing.rotate μ.upper = ∅
      simp [upper, h2, SkewGluing.translate, SkewGluing.rotate]
  · intro C hC
    have hrC : IsConnectedSkew (SkewGluing.rotate C) := isConnectedSkew_rotate hC
    have h1 := h.compose_eq _ hrC
    have hCne := hC.2.1
    have hγne : ∀ X : Diagram, X.Nonempty → (γ X).Nonempty := by
      intro X hX
      rcases h.gamma with h3 | ⟨h3, -⟩
      · rw [h3]; exact hX
      · rw [h3]; exact hX.image _
    have hY : (γ (SkewGluing.rotate C)).Nonempty := hγne _ (hCne.image _)
    have hμne : μ.E.Nonempty := by
      rw [h.inner]; exact hV.image _
    have hX : (μ.compose (γ (SkewGluing.rotate C))).Nonempty := by
      obtain ⟨d, hd⟩ := hY
      obtain ⟨y, hy⟩ := hμne
      refine ⟨y + μ.origin (γ (SkewGluing.rotate C)) d, ?_⟩
      rw [mem_compose ⟨d, hd⟩]
      exact Or.inl ⟨d, hd, by rw [mem_translate]; simpa using hy⟩
    have e1 : η.compose C =
        SkewGluing.rotate (η.rotate.compose (SkewGluing.rotate C)) := by
      have := rotate_compose (D := SkewGluing.rotate C) (hCne.image _) η.rotate
      rw [rotate_rotate, SkewGluing.rotate_rotate] at this
      exact this
    have e2 : SkewGluing.rotate (ω.rotate.compose (μ.compose (γ (SkewGluing.rotate C)))) =
        ω.compose (SkewGluing.rotate (μ.compose (γ (SkewGluing.rotate C)))) := by
      have := rotate_compose (D := μ.compose (γ (SkewGluing.rotate C))) hX ω.rotate
      rw [rotate_rotate] at this
      exact this.symm
    have e3 : SkewGluing.rotate (μ.compose (γ (SkewGluing.rotate C))) =
        μ.rotate.compose (γ C) := by
      have := rotate_compose (D := γ (SkewGluing.rotate C)) hY μ
      have e4 : SkewGluing.rotate (γ (SkewGluing.rotate C)) = γ C := by
        rcases h.gamma with h3 | ⟨h3, -⟩
        · rw [h3]; exact SkewGluing.rotate_rotate
        · rw [h3]; exact rotate_antitranspose_rotate C
      rw [e4] at this
      exact this.symm
    rw [e1, h1, e2, e3]

/-- **`lem:gluing-aligned`.**  Let `U = V ∘_ω E` for a legal mark `ω` and a connected `V`, and
let `η` be a legal mark on `U` whose displacement has content `a q`, `q` the period of `ω`.
There are a legal mark `μ` on `V` and `γ ∈ {id, AT}` (with `γ = AT` only for an empty `μ`), fixed
before `C` is chosen, such that `C ∘_η U = (γ(C) ∘_μ V) ∘_ω E` for every connected `C`
(`eq:gluing-reassociation`).  The identity is an equality of cell sets.

Case (c) is proved from case (d) by rotation; the cases of ordinary `ω` and `η` are proved from
the lattice map except for the sorries listed in the module docstring. -/
theorem IsLegal.aligned (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hη : η.IsLegal)
    (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    ∃ (μ : MarkedInner) (γ : Diagram → Diagram), IsReassociation ω η V μ γ := by
  have hVne := hV.2.1
  cases hc : ω.case with
  | a | b =>
    have hord : ¬ ω.case.IsMixed := by simp [hc, AttachCase.IsMixed]
    by_cases hm : η.case.IsMixed
    · exact aligned_ordinary_mixed_eta hω hord hV hη hm hU ha
    · exact aligned_ordinary hω hord hV hη hm hU ha
  | d => exact aligned_mixed_d hω hc hV hη hU ha
  | c =>
    have hd : ω.rotate.case = .d := by simp [rotate, hc, AttachCase.rotate]
    have hU' : η.rotate.E = ω.rotate.compose (SkewGluing.rotate V) := by
      rw [rotate_compose hVne]
      change SkewGluing.rotate η.E = _
      rw [hU]
    have ha' : content η.rotate.v = a * ω.rotate.period := ha
    obtain ⟨μ, γ, h⟩ := aligned_mixed_d (isLegal_rotate hω) hd (isConnectedSkew_rotate hV)
      (isLegal_rotate hη) hU' ha'
    exact ⟨μ.rotate, γ, h.rotate hVne⟩

end MarkedInner

/-! ### Checked examples -/

section Examples

open MarkedInner

/-- The mark `η` of period four and width three on the row `(7) = (3) ∘_ω (3)`, `ω` the
case-(a) mark on `(3)` of period two. -/
def rowSevenMark : MarkedInner where
  E := skewOf [7] []
  W := {(0, 0), (0, 1), (0, 2)}
  v := (0, 4)
  case := .a

example : compose (skewOf [3] []) rowInnerThree = skewOf [7] [] := by decide +kernel
example : rowSevenMark.IsLegal := by decide +kernel

/-- `lem:gluing-aligned` for the ordinary chart `(7) = (3) ∘_ω (3)`: the lower mark is `ω`
itself on `(3)`, and `C ∘_η (7) = (C ∘_ω (3)) ∘_ω (3)` for the sample outers `C`. -/
example : ∀ C ∈ [skewOf [2] [], skewOf [1, 1] [], skewOf [2, 1] [], skewOf [2, 2] []],
    rowSevenMark.compose C = rowInnerThree.compose (rowInnerThree.compose C) := by
  decide +kernel

/-- `lem:gluing-aligned` for the mixed chart `U = (3) ∘_ω (2, 1)`, `ω` the case-(d) hook mark of
period two: the mark `η` of period four and width three on `U` is reassociated through the row
mark on `(3)`. -/
def hookRowMark : MarkedInner where
  E := compose (skewOf [3] []) hookInner
  W := (compose (skewOf [3] []) hookInner).filter fun x =>
    x + (-2, 2) ∈ compose (skewOf [3] []) hookInner
  v := (-2, 2)
  case := .d

example : hookRowMark.IsLegal := by decide +kernel

example : ∀ C ∈ [skewOf [2] [], skewOf [1, 1] [], skewOf [2, 1] [], skewOf [2, 2] [],
      skewOf [3, 2] [1]],
    hookRowMark.compose C = hookInner.compose (rowInnerThree.compose C) := by
  decide +kernel

/-- The gauge case `γ = AT` with the empty lower mark: the chart `(2) = (2) ∘_ω (1)`-type edge
reading, on the row `(3)` with the empty lower mark on a single cell. -/
example : (emptyMarkH (skewOf [1] [])).IsLegal := emptyMarkH_isLegal (by decide)

end Examples

end SkewGluing
