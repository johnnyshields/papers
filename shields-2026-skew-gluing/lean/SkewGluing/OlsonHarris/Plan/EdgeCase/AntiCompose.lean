import SkewGluing.Antitranspose
import SkewGluing.OlsonHarris.Plan.EdgeCase.Rotate
import SkewGluing.OlsonHarris.Plan.EdgeCase.TFun

/-!
# Antitransposition of the composite

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `eq:gluing-gauge`): thesis Lemma 5.3.4 (iii) and Thm. 5.4.9
(`OlsonHarris2024HopfApplications`).

For an ordinary mark, antitransposing the union of copies `copies ω D` gives the union of copies of
the antitransposed mark with the same outer diagram: the copy at `d` is placed at
`atVec (origin ω D d) = origin ω^{AT} D d`.  The functions of the pieces are exchanged by `ι`.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewGluing

open Plan

open scoped Classical

namespace MarkedInner

theorem origin_of_a {ω : MarkedInner} (h : ω.case = .a) (D : Diagram) (d : ℤ × ℤ) :
    ω.origin D d = content d • ω.v + d.1 • eCell := by
  unfold SkewGluing.MarkedInner.origin; rw [h]

theorem origin_of_b {ω : MarkedInner} (h : ω.case = .b) (D : Diagram) (d : ℤ × ℤ) :
    ω.origin D d = content d • ω.v - d.1 • eCell := by
  unfold SkewGluing.MarkedInner.origin; rw [h]

theorem antitranspose_copies {ω : MarkedInner} (hord : ¬ ω.case.IsMixed) (D : Diagram) :
    antitranspose (Plan.MarkedInner.copies ω D) = Plan.MarkedInner.copies ω.anti D := by
  ext y
  rw [mem_antitranspose', Plan.MarkedInner.mem_copies, Plan.MarkedInner.mem_copies]
  refine exists_congr fun d => and_congr_right fun _ => ?_
  rw [mem_translate, mem_translate, anti_E, mem_antitranspose', origin_anti hord,
    atVec_sub, atVec_atVec]

theorem cellSchur_copies_anti {ω : MarkedInner} (hord : ¬ ω.case.IsMixed) (D : Diagram) :
    cellSchur (Plan.MarkedInner.copies ω.anti D) =
      schurInvolution (cellSchur (Plan.MarkedInner.copies ω D)) := by
  rw [← antitranspose_copies hord, cellSchur_antitranspose]

end MarkedInner

end SkewGluing
