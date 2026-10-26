/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.OrdinaryGaugeCensusCertificate

/-!
# Actual ordinary gauge classification through eight cells

Formalizes `shields-2026-skew-corner-descent.tex` (`rem:ordinary-gauge`).
The kernel-certified census and its literal completeness identify all
positive ordinary reading pairs through eight actual cells. Their six
marks are precisely the ordinary Hypothesis V failures in that range.
The actual southeast-step displacement gives the full antitransposed-outer
composition identity. No equivalence outside the bounded range is claimed.
Sorry-free.
-/

namespace SkewCornerDescent
open SkewGluing

private theorem failure_census_not_hypothesisV {A : ℕ} {ω : MarkedInner}
    (h : ω ∈ ordinaryVFailureCensus A) : ¬ ordinaryHypothesisV ω := by
  obtain ⟨_, _, hm⟩ := (mem_diagramCensusUnion A _ ω).mp h
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2

-- Use the certified census as a finite object without recomputing it during elaboration.
attribute [local irreducible] ordinaryGaugeCensus ordinaryVFailureCensus

/-- Every actual positive horizontal/vertical equal-period reading pair
through eight cells fails V at both readings and has the exact gauge displacement. -/
theorem ordinaryGauge_through_eight {ωa ωb : MarkedInner}
    (ha : ωa.IsLegal) (hb : ωb.IsLegal) (hWa : ωa.W.Nonempty)
    (hca : ωa.case = .a) (hcb : ωb.case = .b) (hE : ωb.E = ωa.E)
    (hperiod : ωa.period = ωb.period) (harea : ωa.E.card ≤ 8) :
    ¬ ordinaryHypothesisV ωa ∧ ¬ ordinaryHypothesisV ωb ∧ ωa.v = ωb.v + eCell := by
  have hWb := ordinaryGauge_nonempty_other ha hb hWa hE hperiod
  have hm := ordinaryGaugeCensus_complete ha hb hWa hWb hca hcb hE hperiod 8 harea
  have himages := ordinary_gauge_census_eight.2.2.1
  have hma : normalizeMarkedInner ωa ∈ ordinaryVFailureCensus 8 := by
    rw [← himages]
    exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_image.mpr ⟨(normalizeMarkedInner ωa, normalizeMarkedInner ωb), hm, rfl⟩))
  have hmb : normalizeMarkedInner ωb ∈ ordinaryVFailureCensus 8 := by
    rw [← himages]
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_image.mpr ⟨(normalizeMarkedInner ωa, normalizeMarkedInner ωb), hm, rfl⟩))
  refine ⟨?_, ?_, ordinary_gauge_census_eight.2.2.2 _ hm⟩
  · intro hV
    exact failure_census_not_hypothesisV hma
      ((ordinaryHypothesisV_translateBy ωa (-sw ωa.E)).mpr hV)
  · intro hV
    exact failure_census_not_hypothesisV hmb
      ((ordinaryHypothesisV_translateBy ωb (-sw ωb.E)).mpr hV)

/-- In the exhaustive range, the positive ordinary V failures are exactly
the marks occurring in the three complete normalized ordinary gauge pairs. -/
theorem ordinaryVFailure_through_eight_iff {ω : MarkedInner} (h : ω.IsLegal)
    (hW : ω.W.Nonempty) (hcase : ω.case = .a ∨ ω.case = .b) (harea : ω.E.card ≤ 8) :
    ¬ ordinaryHypothesisV ω ↔
      normalizeMarkedInner ω ∈ (ordinaryGaugeCensus 8).image Prod.fst ∪
        (ordinaryGaugeCensus 8).image Prod.snd := by
  constructor
  · intro hnot
    rw [ordinary_gauge_census_eight.2.2.1]
    exact ordinaryVFailureCensus_complete h hW hcase hnot 8 harea
  · intro hm hV
    rw [ordinary_gauge_census_eight.2.2.1] at hm
    exact failure_census_not_hypothesisV hm
      ((ordinaryHypothesisV_translateBy ω (-sw ω.E)).mpr hV)

/-- Every bounded positive ordinary reading pair gives the actual whole
composition gauge for every nonempty outer, not just an equality of functions. -/
theorem ordinaryGauge_through_eight_compose {ωa ωb : MarkedInner}
    (ha : ωa.IsLegal) (hb : ωb.IsLegal) (hWa : ωa.W.Nonempty)
    (hca : ωa.case = .a) (hcb : ωb.case = .b) (hE : ωb.E = ωa.E)
    (hperiod : ωa.period = ωb.period) (harea : ωa.E.card ≤ 8)
    (D : Diagram) (hD : D.Nonempty) :
    ωa.compose D = ωb.compose (antitranspose D) := by
  have hclassification := ordinaryGauge_through_eight ha hb hWa hca hcb hE hperiod harea
  exact MarkedInner.compose_antitranspose_gauge hD hE.symm hca hcb hclassification.2.2

end SkewCornerDescent
