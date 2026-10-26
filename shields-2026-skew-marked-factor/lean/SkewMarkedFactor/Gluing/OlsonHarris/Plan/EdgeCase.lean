/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.Defs
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.Core
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.Rotate
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.AntiEdge

/-!
# The edge case: ribbons removable from a composite (ordinary marks)

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis §5.3.3 and §5.4
(`OlsonHarris2024HopfApplications`), Thm. 5.4.1 (a mark satisfies IV exactly when `E` has no loose
end ribbons) and Lemmas 5.4.2–5.4.7, Thm. 5.4.8 and Thm. 5.4.9, in the form that the assembly
needs: `EdgeCompat ω`.

For a legal mark `ω` of case (a) (`W → O → W`, `p_{mq}` acts as a derivation on both sides) or (b)
(`W ↑ O ↑ W`, transposed twist `ω(p_m) = (-1)^{m-1} p_m`), the modified composition `modComp ω`
intertwines `p_{mq}^⊥` with signed ribbon removal of ribbons of size `m` on the left and on the
right.  By `pDeriv_cellSchur_left` and `pDeriv_cellSchur_right` (Murnaghan–Nakayama, one power
sum) the statement is equivalent to a purely combinatorial identity between Schur functions of
cell diagrams:

* the ribbons of size `m q` removable on the left (right) from `C ∘_ω E` are exactly the lifts
  `A ∘ K` of the ribbons `A` of size `m` removable on the left (right) from `C`, built from the
  top (bottom) key ribbons of the copies of `E` (Lemma 5.4.5), of height `m h(E) + ht A`
  (Lemma 5.2.9);
* removing the key ribbon of a removable box `b` of `C` from `C ∘_ω E` leaves
  `(C \\ b) ∘_ω E`, together with a copy of `\overline O` if `b` has no box to its southeast, of
  `\overline W` if `b` has no box to its south and of `W` if `b` has no box to its east
  (Lemma 5.4.3, using IV);
* `W`, `\overline W`, `\overline O` have no removable ribbon of size divisible by `q`
  (Lemma 5.4.4), so by Murnaghan–Nakayama they are killed by `p_{mq}^⊥`.

`edgeCompat_a` is proved from the left equation for a connected outer (`EdgeCase.Core`), the
reduction from skew to connected outers (`EdgeCase.Reduction`) and the right equation by rotation
(`EdgeCase.Rotate`); `edgeCompat_b` follows from it through the antitransposed mark
(`EdgeCase.AntiEdge`).

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

/-- **Thesis Lemma 5.4.7 (via `schur`), case (a).**  For a legal mark of case (a), connected or
not skew `X`, and `m > 0`: `p_{mq}^⊥ (s_{[X] □ E}) = (-1)^{m h(E)} (s_W s_{\overline W}
s_{\overline O})^m Σ_{A} (-1)^{ht A} s_{[X \ A] □ E}`, the sum over the ribbons of size `m`
removable on the left, and the same with the right.

The sign is `edgeSign`, with `h(E) = |v₁|` the height of the key ribbons.  The statement for a
connected `C` is the substantive one (`edgeEqL_connected_a`); the passage to a disconnected `X`
is by the Leibniz rule (a ribbon is connected, so lies in one component, and the ribbons
removable from `X` are the ribbons removable from its components). -/
theorem edgeCompat_a {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .a) : EdgeCompat ω := by
  have hL : ∀ ω' : MarkedInner, ω'.IsLegal → ω'.case = .a → ∀ X : Diagram, IsSkew X →
      ∀ m : ℕ, 0 < m → EdgeEqL ω' X m := fun ω' hω' hc' X hX m hm =>
    edgeEqL_of_connected (fun C hC m hm => edgeEqL_connected_a hω' hc' hC hm) _ X rfl hX m hm
  intro X hX m hm
  refine ⟨hL ω hω hc X hX m hm, ?_⟩
  have hωr : ω.rotate.IsLegal := MarkedInner.isLegal_rotate hω
  have hcr : ω.rotate.case = .a := by simp [MarkedInner.rotate, hc, AttachCase.rotate]
  exact edgeEqR_of_edgeEqL_rotate hω.1 hω.2.2.1
    (hL ω.rotate hωr hcr (SkewMarkedFactor.Gluing.rotate X) (isSkew_rotate hX) m hm)

/-- **Thesis Thm. 5.4.9 (via `schur`), case (b)**, from case (a) by transposition: `E^t` is a
`W → O → W` shape with the same `k`, `h(E^t) = k - h(E) - 1`, `(D ∘_ω E)^t = D^* ∘_{ω^t} E^t`, and
`ω(p_m) = (-1)^{m-1} p_m`.  The sign is `edgeSign`: `-(-1)^{m |v₁|}`.

The transposition of marked inners (legality of the transposed mark, the composition identity,
`schurInvolution` intertwining `p_m^⊥` up to `(-1)^{m-1}`) is in `EdgeCase.AntiEdge`; then
`edgeCompat_a` applies. -/
theorem edgeCompat_b {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .b) : EdgeCompat ω := by
  have hW := MarkedInner.W_nonempty_of_case_b hω hc
  have hca : ω.anti.case = .a := by
    rw [MarkedInner.anti_case, hc]; rfl
  exact MarkedInner.edgeCompat_of_anti hω hc
    (edgeCompat_a (MarkedInner.isLegal_anti hω hW) hca)

end Plan

end SkewMarkedFactor.Gluing
