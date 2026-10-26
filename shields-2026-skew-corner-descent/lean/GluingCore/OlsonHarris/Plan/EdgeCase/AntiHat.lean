-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/AntiHat.lean
import GluingCore.OlsonHarris.Plan.EdgeCase.AntiCompose

/-!
# The modified composition under antitransposition

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `eq:gluing-gauge`): thesis Thm. 5.4.9
(`OlsonHarris2024HopfApplications`).

The hat shapes of the antitransposed mark are the antitranspositions of translates of the hat
shapes of the mark, so `hatFactor` and `modComp` of `ω^{AT}` are the images under `ι` of those of
`ω`, with the same outer diagram: `modComp ω^{AT} X = ι (modComp ω X)`.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace GluingCore

open Plan

open scoped Classical

namespace MarkedInner

theorem hatMiddleFin_anti (ω : MarkedInner) :
    hatMiddleFin ω.anti = antitranspose (GluingCore.translate eCell (hatMiddleFin ω)) := by
  ext x
  rw [mem_antitranspose', mem_translate, Plan.MarkedInner.mem_hatMiddleFin,
    Plan.MarkedInner.mem_hatMiddleFin, mem_middle_anti, mem_middle_anti]
  have e1 : atVec (x + eCell) = atVec x - eCell := by
    rw [atVec_add, atVec_eCell]; abel
  rw [e1, sub_add_cancel]
  tauto

theorem hatMarkWindow_anti (ω : MarkedInner) :
    hatMarkWindow ω.anti = antitranspose (GluingCore.translate eCell (hatMarkWindow ω)) := by
  ext x
  rw [mem_antitranspose', mem_translate, Plan.MarkedInner.mem_hatMarkWindow,
    Plan.MarkedInner.mem_hatMarkWindow, Plan.MarkedInner.mem_windowCells,
    Plan.MarkedInner.mem_windowCells, Plan.MarkedInner.mem_windowCells,
    Plan.MarkedInner.mem_windowCells]
  have e1 : ∀ u : ℤ × ℤ, atVec (u + eCell) = atVec u - eCell := by
    intro u; rw [atVec_add, atVec_eCell]; abel
  have e2 : atVec (x + ω.anti.v) = atVec x + ω.v := by
    rw [atVec_add, anti_v, atVec_atVec]
  have e3 : atVec x - eCell + eCell = atVec x := by abel
  have e4 : atVec x - eCell + ω.v = atVec x + ω.v - eCell := by abel
  have e5 : atVec (x + eCell + ω.anti.v) = atVec x + ω.v - eCell := by
    rw [atVec_add, atVec_add, anti_v, atVec_atVec, atVec_eCell]; abel
  simp only [anti_W, anti_E, mem_antitranspose', e1, e2, e3, e4, e5]
  tauto

theorem cellSchur_hatMiddleFin_anti (ω : MarkedInner) :
    cellSchur (hatMiddleFin ω.anti) = schurInvolution (cellSchur (hatMiddleFin ω)) := by
  rw [hatMiddleFin_anti, cellSchur_antitranspose, cellSchur_translate]

theorem cellSchur_hatMarkFin_anti {ω : MarkedInner} (hwf : ω.IsWellFormed)
    (hII : ω.IsNarrow) (hW : ω.W.Nonempty) :
    cellSchur (hatMarkFin ω.anti) = schurInvolution (cellSchur (hatMarkFin ω)) := by
  rw [Plan.MarkedInner.hatMarkFin_eq_hatMarkWindow (isWellFormed_anti hwf hW)
      (isNarrow_anti hII),
    Plan.MarkedInner.hatMarkFin_eq_hatMarkWindow hwf hII, hatMarkWindow_anti,
    cellSchur_antitranspose, cellSchur_translate]

theorem cellSchur_W_anti (ω : MarkedInner) :
    cellSchur ω.anti.W = schurInvolution (cellSchur ω.W) := by
  rw [anti_W, cellSchur_antitranspose]

theorem hatFactor_anti {ω : MarkedInner} (hwf : ω.IsWellFormed) (hII : ω.IsNarrow)
    (hW : ω.W.Nonempty) : hatFactor ω.anti = schurInvolution (hatFactor ω) := by
  unfold hatFactor
  rw [map_mul, map_mul, cellSchur_W_anti, cellSchur_hatMarkFin_anti hwf hII hW,
    cellSchur_hatMiddleFin_anti]

theorem componentT_anti {ω : MarkedInner} (hwf : ω.IsWellFormed) (hII : ω.IsNarrow)
    (hW : ω.W.Nonempty) (hord : ¬ ω.case.IsMixed) {C : Diagram} (hC : C.Nonempty) :
    componentT ω.anti C = schurInvolution (componentT ω C) := by
  unfold componentT
  have hord' : ¬ ω.anti.case.IsMixed := by
    unfold AttachCase.IsMixed at *
    rw [anti_case]
    cases hh : ω.case <;> simp_all [AttachCase.anti]
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, cellSchur_W_anti,
    cellSchur_hatMarkFin_anti hwf hII hW, cellSchur_hatMiddleFin_anti,
    Plan.MarkedInner.compose_eq_copies hord hC, Plan.MarkedInner.compose_eq_copies hord' hC,
    cellSchur_copies_anti hord]

theorem modComp_anti {ω : MarkedInner} (hwf : ω.IsWellFormed) (hII : ω.IsNarrow)
    (hW : ω.W.Nonempty) (hord : ¬ ω.case.IsMixed) (X : Diagram) :
    modComp ω.anti X = schurInvolution (modComp ω X) := by
  unfold modComp
  rw [map_prod]
  exact Finset.prod_congr rfl fun C hC =>
    componentT_anti hwf hII hW hord (component_nonempty hC)

end MarkedInner

end GluingCore
