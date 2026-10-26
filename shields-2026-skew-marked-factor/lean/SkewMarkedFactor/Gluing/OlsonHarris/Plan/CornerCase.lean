/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Connected

/-!
# The corner case: ribbons removable from a composite (mixed marks)

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis §5.5
(`OlsonHarris2024HopfApplications`), Lemmas 5.5.2–5.5.13, in the form that the assembly needs:
`CornerCompat ω` for a legal mark of case (c) (`W → O ↑ W`).  Case (d) follows by rotation.

For a corner mark there is no ribbon of size `q` removable on the left from `E` (Lemma 5.5.2),
and the ribbons of size divisible by `q` removable from `C ∘_ω E` are all removable on the right,
indexed by the ribbons of `C` removable on the left or on the right (Lemma 5.5.11); consequently
the corner modified composition is killed by `p_{mq}^⊥` (which is `(modComp ↼ p_{mq}) = 0` of
Lemma 5.5.12), and `p_{mq} ⇀ (modComp) = ± (p_m ⇀ - ↼ p_m) modComp`, whence the two ribbon
sums agree.  An alternative route for this half is the Hamel–Goulden identity of
McNamara–van Willigenburg, Thm. 3.28 and Thm. 3.31 (corner shapes satisfy Hypothesis V).

`cornerCompat_c` is derived from `corner_ribbon_core` in `Plan/CornerCase/Combinatorics.lean`, which
combines the bijection of ribbons `corner_ribbon_bijection` (`Plan/CornerCase/Lift.lean`, read off
the boundary words of the composite) with `corner_lift_height_sign` (thesis Lemmas 5.5.10, 5.5.11;
`Plan/CornerCase/CSign.lean`) and `corner_lift_remainder` (thesis Lemma 5.5.8;
`Plan/CornerCase/Crem.lean`).  The derivation (Leibniz rule over the components of the outer, the
exponent bookkeeping, the Murnaghan–Nakayama rule in derivation form on both sides, and the
cancellation of the nonzero hat factor) is in `Plan/CornerCase/Disconnected.lean`,
`Bookkeeping.lean`, `Combinatorics.lean` and `Connected.lean`.  It uses `pDeriv_cellSchur_left`,
`pDeriv_cellSchur_right` and `hatFactor_ne_zero`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

/-- **Thesis Lemmas 5.5.12 and 5.5.13 (via `schur`), case (c).**  For a legal mark of case (c)
and a skew diagram `X`: `p_{mq}^⊥` kills the corner modified composition
`(-1)^{ξ(X)} s_W^{|X| - row X} s_{\overline W}^{|X| - col X} s_{\overline O}^{|X| - dia X}
s_{X ∘_ω E}`, and the signed ribbon sums over the ribbons of size `m` removable on the right
and on the left agree on it.

Proof: `cornerEq_of_connected` reduces to connected `X` (Leibniz rule); for connected `X`,
`cornerEq_connected` combines `pDeriv_cellSchur_left`, `pDeriv_cellSchur_right`, the absence of
ribbons of size `m q` removable on the left (`corner_no_leftRibbons`) and the lifting of the
ribbons removable on the right (`corner_ribbon_lift`) with the nonvanishing of `hatFactor`.
The absence of ribbons removable on the left (thesis Lemmas 5.5.2, 5.5.7 (iii), 5.5.11 (iii)) is
`corner_no_leftRibbons`; the heights and the remainders of the lifts are
`corner_lift_height_sign` and `corner_lift_remainder`. -/
theorem cornerCompat_c {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    CornerCompat ω := fun X hX m hm =>
  Corner.cornerEq_of_connected (fun _ hC _ hm => Corner.cornerEq_connected hω hc hC hm) X.card X
    rfl hX m hm

end Plan

end SkewMarkedFactor.Gluing
