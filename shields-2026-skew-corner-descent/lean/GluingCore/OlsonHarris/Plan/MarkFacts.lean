-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/MarkFacts.lean
import GluingCore.OlsonHarris.Plan.Defs
import GluingCore.Mark
import GluingCore.Local.Final
import GluingCore.OlsonHarris.Plan.MarkFacts.Translate
import GluingCore.OlsonHarris.Plan.MarkFacts.Positivity
import GluingCore.OlsonHarris.Plan.MarkFacts.HatMark
import GluingCore.OlsonHarris.Plan.MurnaghanNakayama

/-!
# Facts about the modified composition that concern only the mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `lem:gluing-local`): statements about the hat shapes and the
placement formula that the assembly of the Olson-Harris composition theorem needs.

* `isConnectedSkew_compose`: the composite of a connected outer with a legal mark is connected
  skew (`lem:gluing-local` (3), from `GluingCore.Local.Final`).
* `cellSchur_add_ne_zero`: two skew Schur functions never cancel (positivity at the all-ones
  alphabet, `GluingCore.OlsonHarris.Plan.MarkFacts.Positivity`).
* `hatFactor_ne_zero`, `pDeriv_hatFactor`: the three factors of the hat factor are skew
  diagrams (`GluingCore.OlsonHarris.Plan.MarkFacts.HatMark`: the hatted mark is the cut of the
  amalgam `E ∪ (E - v)` to the marked diagonals, and condition IV keeps the cut skew) of span
  below the period.
* `modComp_translate`, `modCompC_translate`: translating the outer translates the composite
  (`GluingCore.OlsonHarris.Plan.MarkFacts.Translate`).

`pDeriv_hatFactor` uses `pDeriv_cellSchur_left` of
`GluingCore.OlsonHarris.Plan.MurnaghanNakayama`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

open MarkFacts

/-- **The composite of a connected outer with a legal mark is connected skew**
(`lem:gluing-local` (3)): `MarkedInner.IsLegal.isConnectedSkew_compose` of
`GluingCore.Local.Final`. -/
theorem isConnectedSkew_compose {ω : MarkedInner} (hω : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) : IsConnectedSkew (ω.compose D) :=
  hω.isConnectedSkew_compose hD

/-- **Positivity of skew Schur functions: two never cancel.**  For skew diagrams `X`, `X'`,
`s_X + s_{X'} ≠ 0`.  Both are nonnegative combinations of monomials in the variables
(`aeval_cellSchur_skewDiagram_all`, `s_X` the generating function of semistandard tableaux), and
`s_X` is positive at the all-ones alphabet in enough variables.  Used to fix a sign `(-1)^ξ` in
the corner case. -/
theorem cellSchur_add_ne_zero {X X' : Diagram} (hX : IsSkew X) (hX' : IsSkew X') :
    cellSchur X + cellSchur X' ≠ 0 :=
  cellSchur_add_cellSchur_ne_zero hX hX'

/-- **The hat factor is nonzero**: `s_W`, `s_{\overline W}` and `s_{\overline O}` are skew
Schur functions of skew diagrams (`IsLegal.isSkew_W`, `IsLegal.isSkew_hatMarkFin`,
`IsLegal.isSkew_hatMiddleFin`), hence nonzero (`cellSchur_ne_zero`). -/
theorem hatFactor_ne_zero {ω : MarkedInner} (hω : ω.IsLegal) : hatFactor ω ≠ 0 := by
  unfold hatFactor
  exact mul_ne_zero (mul_ne_zero (cellSchur_ne_zero hω.isSkew_W)
    (cellSchur_ne_zero hω.isSkew_hatMarkFin)) (cellSchur_ne_zero hω.isSkew_hatMiddleFin)

/-- **The modified composition is translation invariant**: `D ↦ D ∘_ω E` commutes with
translating `D` (`MarkedInner.compose_translate`: `L_ω(d + t) = L_ω(d) + c(t) v + t₁ e`, the
same for the ribbon-rank offsets, and the counts of rows, columns and diagonals are unchanged).
True for every mark, so no legality is assumed. -/
theorem modComp_translate (ω : MarkedInner) (t : ℤ × ℤ) (X : Diagram) :
    modComp ω (translate t X) = modComp ω X := by
  unfold modComp
  rw [edgeComponents_translate, Finset.prod_image fun A _ B _ h => translate_injective' t h]
  exact Finset.prod_congr rfl fun C hC =>
    MarkedInner.componentT_translate ω (component_nonempty hC) t

/-- The corner variant of `modComp_translate` (the northbound counts are translation
invariant). -/
theorem modCompC_translate (ω : MarkedInner) (t : ℤ × ℤ) (X : Diagram) :
    modCompC ω (translate t X) = modCompC ω X := by
  unfold modCompC
  rw [edgeComponents_translate, Finset.prod_image fun A _ B _ h => translate_injective' t h]
  refine Finset.prod_congr rfl fun C hC => ?_
  unfold componentTc
  rw [MarkedInner.northbound_translate, MarkedInner.componentT_translate ω
    (component_nonempty hC) t]

/-- **`p_{mq}^⊥` kills the hat factor.**  Each factor is a skew diagram whose span is below the
period `q` (`W` has span `w < q`; `\overline W` lies on the `w` marked diagonals; `\overline O`
avoids the marked diagonals, where the middle is thin), so it has no ribbon of size `mq`; by
`pDeriv_cellSchur_left` the derivation `p_{mq}^⊥` kills each factor, hence their product.
The hypothesis on the case is not used: the statement holds for every legal mark.

The thesis argues with ribbons removable on the left (Lemma 5.4.4); here the span count suffices
and needs no property of the key ribbons. -/
theorem pDeriv_hatFactor {ω : MarkedInner} (hω : ω.IsLegal)
    (hc : ω.case = .a ∨ ω.case = .b) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * ω.period.toNat) (hatFactor ω) = 0 := by
  have _ := hc
  have hq : ω.period.toNat ≤ m * ω.period.toNat := Nat.le_mul_of_pos_left _ hm
  have h1 := pDeriv_cellSchur_eq_zero_of_span_lt (Z := ω.W) (n := m * ω.period.toNat)
    (by have := hω.span_W_lt; omega)
  have h2 := pDeriv_cellSchur_eq_zero_of_span_lt (Z := hatMarkFin ω) (n := m * ω.period.toNat)
    (by have := hω.span_hatMarkFin_lt; omega)
  have h3 := pDeriv_cellSchur_eq_zero_of_span_lt (Z := hatMiddleFin ω) (n := m * ω.period.toNat)
    (by have := hω.span_hatMiddleFin_lt; omega)
  unfold hatFactor
  rw [Derivation.leibniz, Derivation.leibniz, h1, h2, h3]
  simp

end Plan

end GluingCore
