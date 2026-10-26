-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/CSign.lean
import GluingCore.OlsonHarris.Plan.CornerCase.CSign.Parity
import GluingCore.OlsonHarris.Plan.CornerCase.CSign.LiftHeight
import GluingCore.OlsonHarris.Plan.CornerCase.CSign.WindowCount

/-!
# The heights of the lifted strips and the sign `σ`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemmas 5.5.10 and 5.5.11
(`OlsonHarris2024HopfApplications`), the heights of the lifts of the ribbons of the outer to the
corner composite `D ∘_ω E` of a legal mark of case (c) (`W → O ↑ W`).

`corner_lift_height_sign_proof` proves `corner_lift_height_sign`: with `σ = (-1)^{v₁}`, where `v₁`
is the row displacement of the mark (the thesis writes the sign as `(-1)^{h(E)}`), the lift `Ã` of a
ribbon `A` of size `m` removable from the connected outer `D` has
`(-1)^{ht Ã} = ± σ^m (-1)^{ht A} (-1)^{ξ(D) + ξ(D \ A)}`, with `+` for `A` removable on the right
and `-` for `A` removable on the left.

**Differs from the paper's route.**  The thesis reads the height of `Ã` off the border strip as a
sum over the boxes of `A` of the heights of the key ribbons, and proves `ξ(D) = ξ(D*)` by induction
on the ribbons.  Here the height of the lift is the difference of the last rows of its end
diagonals, computed from the mixed profile of the rotated composite (`corner_hi_diff`), the
northbound count is a count of cells read diagonal by diagonal (`card_nwNorth`, `card_seNorth`), and
`ξ(D) = ξ(D*)` is a telescoping identity (`card_nwNorth_eq_card_seNorth`); the sign `σ` is the
parity of `v₁`, with no use of the key ribbons `K_W`, `K_O`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

open MarkedInner CSign

/-- **Thesis Lemmas 5.5.10 and 5.5.11: the heights of the lifts.**  There is a sign `σ`,
namely `(-1)^{v₁}` for the row displacement `v₁ = ω.rowShift`, depending only on `ω`, such that for
a ribbon `A` of size `m` removable from the connected outer `D`, the lift
`Ã = cornerLift ω D m s A` (on the right, offset `s`) or
`cornerLift ω D m t A` (on the left, offset `t`) has height sign
`(-1)^{ht Ã} = ± σ^m (-1)^{ht A} (-1)^{ξ(D) + ξ(D \ A)}`, with `+` for `A` removable on the right
and `-` on the left (thesis: `ht Ã = m h(E) + ht A - ξ(D) + ξ(D \ A)`, respectively
`m h(E) - ht A + ξ(D) - ξ(D \ A) - 1`). -/
theorem corner_lift_height_sign_proof {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ D : Diagram, IsConnectedSkew D → ∀ m : ℕ, 0 < m →
      ∀ s t : ℤ, ω.IsPhases s t →
        (∀ A ∈ rightRibbons D m,
          ribbonSign (cornerLift ω D m s A) =
            σ ^ m * ribbonSign A * (-1) ^ (northboundSum ω D + northboundSum ω (D \ A))) ∧
        (∀ A ∈ leftRibbons D m,
          ribbonSign (cornerLift ω D m t A) =
            -(σ ^ m * ribbonSign A * (-1) ^ (northboundSum ω D + northboundSum ω (D \ A)))) := by
  have hW : ω.W.Nonempty := by
    rcases hω.1.2 with h | h
    · have := h.2.2
      rw [hc] at this
      cases this
    · exact h.1
  have hl : ω.IsLegalNonempty := ⟨hω, hW⟩
  refine ⟨(-1) ^ ω.rowShift.natAbs, sigma_cases _, fun D hD m hm s t hph => ⟨?_, ?_⟩⟩
  · -- ribbons removable on the right
    intro A hA
    obtain ⟨j, hj0, hjm, hB, hBm, hAw⟩ := right_window_D_exists hD hm hA
    have hup := (mem_rightRibbons.mp hA).2.2.2
    have hs := isConnectedSkew_iff_diagonal.mp hD
    have hsp := span_eq_of_isConnectedSkew hD
    have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have hmc : minContent A = minContent D + j := by rw [hAw, minContent_windowRibbon hm]
    have h0 : minContent D + j ∈ contents D :=
      hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
    have h1 : minContent D + j + m - 1 ∈ contents D :=
      hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
    have ha := ribbonHeight_cornerLift_right hl hD hc hph hm hj0 hjm hB hmc
    have hb : (ribbonHeight A : ℤ) = diagHi D (minContent D + j) -
        diagHi D (minContent D + j + m - 1) := by
      rw [hAw]; exact ribbonHeight_windowRibbon hD hm h0 h1
    have hxi := xi_diff_right hc hD hup
    have hcard : ((A.filter (nwNorth D)).card : ℤ) = diagLo D (minContent D + j) -
        diagLo D (min (minContent D + j + m) (maxContent D)) := by
      rw [hAw]; exact card_window_nwNorth hD h0 h1
    rw [hcard] at hxi
    have e1 : minContent D + j + m = minContent D + (j + m) := by ring
    rw [e1] at hb hxi
    have hpar := right_parity (diagHi D) (diagLo D) (minContent D) (maxContent D)
      (minContent D + j) (minContent D + (j + m)) m ω.rowShift
      (profS D (minContent D + j)) (profS D (minContent D + (j + m))) (by ring) hm1
      (by omega) (by omega) (MarkedInner.D_ends hD)
      (by
        by_cases hj : j = 0
        · left; omega
        · right
          have := Bext_of_mem (D := D) (j := j) (by omega) (by omega)
          rw [this] at hB
          unfold wordB bitB at hB
          omega)
      (by
        by_cases hj : j + m = (span D : ℤ)
        · left; omega
        · right
          have := Bext_of_mem (D := D) (j := j + m) (by omega) (by omega)
          rw [this] at hBm
          unfold wordB bitB at hBm
          omega)
      rfl rfl
    unfold ribbonSign
    rw [neg_mul] at ha
    exact neg_one_pow_eq_parity _ _ _ m ω.rowShift (by omega)
  · -- ribbons removable on the left
    intro A hA
    obtain ⟨j, hj0, hjm, hA1, hA0, hmc⟩ := left_window_D_mem hD hm hA
    have hdown := (mem_leftRibbons.mp hA).2.2.2
    have hs := isConnectedSkew_iff_diagonal.mp hD
    have hsp := span_eq_of_isConnectedSkew hD
    have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have ha := ribbonHeight_cornerLift_left hl hD hc hph hm hj0 hjm hA0 hmc
    have hb := ribbonHeight_of_mem_leftRibbons hD hm hA hmc
    have hxi := xi_diff_left hc hD hdown
    rw [card_left_seNorth hD hm hA hj0 hjm hmc] at hxi
    have e1 : minContent D + j + m = minContent D + (j + m) := by ring
    rw [e1] at hb hxi
    have hpar := left_parity (diagHi D) (diagLo D) (minContent D) (maxContent D)
      (minContent D + j) (minContent D + (j + m)) m ω.rowShift
      (profS D (minContent D + j)) (profS D (minContent D + (j + m))) (by ring) hm1
      (by omega) (by omega) (MarkedInner.D_ends hD)
      (by
        by_cases hj : j = 0
        · left; omega
        · right
          have := Aext_of_mem (D := D) (j := j) (by omega) (by omega)
          rw [this] at hA1
          unfold wordA bitA at hA1
          omega)
      (by
        by_cases hj : j + m = (span D : ℤ)
        · left; omega
        · right
          have := Aext_of_mem (D := D) (j := j + m) (by omega) (by omega)
          rw [this] at hA0
          unfold wordA bitA at hA0
          omega)
      rfl rfl
    unfold ribbonSign
    rw [neg_mul] at ha
    have := neg_one_pow_eq_parity (ribbonHeight (cornerLift ω D m t A)) (ribbonHeight A)
      (northboundSum ω D + northboundSum ω (D \ A) + 1) m ω.rowShift (by push_cast; omega)
    rw [this, pow_succ]
    ring

/-! ### Checked examples -/

section Examples

/-- The outer `(4, 3, 3) / (2, 1)`, which has right and left ribbons of sizes `1, 2, 3`. -/
def CSign.signOuter : Diagram := skewOf [4, 3, 3] [2, 1]

/-- The sign formula of `corner_lift_height_sign_proof` on the rotated hook mark, which has the
phases `s = 1`, `t = 0`, `v₁ = -1`, for the ribbons of sizes `1, 2, 3` of `signOuter`: the
northbound counts are the cell counts of `northboundSum_eq_card`. -/
example : ∀ m ∈ ({1, 2, 3} : Finset ℕ), (∀ A ∈ rightRibbons signOuter m,
    ribbonSign (cornerLift hookInner.rotate signOuter m 1 A) =
      ((-1 : ℤ) ^ hookInner.rotate.rowShift.natAbs) ^ m * ribbonSign A *
        (-1) ^ ((signOuter.filter (nwNorth signOuter)).card +
          ((signOuter \ A).filter (nwNorth (signOuter \ A))).card)) ∧
    (∀ A ∈ leftRibbons signOuter m,
    ribbonSign (cornerLift hookInner.rotate signOuter m 0 A) =
      -(((-1 : ℤ) ^ hookInner.rotate.rowShift.natAbs) ^ m * ribbonSign A *
        (-1) ^ ((signOuter.filter (nwNorth signOuter)).card +
          ((signOuter \ A).filter (nwNorth (signOuter \ A))).card))) := by
  decide +kernel

end Examples

end Corner

end Plan

end GluingCore
