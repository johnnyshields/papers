-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/Rotate.lean
import GluingCore.OlsonHarris.Plan.EdgeCase.HatShapes
import GluingCore.OlsonHarris.Plan.EdgeCase.Reduction
import GluingCore.OlsonHarris.Rotation

/-!
# Rotation of the modified composition

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`): thesis Lemma 5.3.4 (ii) and the proof of Lemma 5.4.3 for
boxes removable on the right (`OlsonHarris2024HopfApplications`).

The hat shapes of the rotated mark are translates of the rotations of the hat shapes
(the northwest variants are translates of the southeast variants), so `modComp` and `hatFactor`
are invariant under `ω ↦ ω*`, `X ↦ X*`, and the right equation for `ω` at `X` is the left equation
for `ω*` at `X*` (`edgeEqR_of_edgeEqL_rotate`).

Sorry-free.
-/

set_option linter.style.openClassical false

namespace GluingCore

namespace Plan

open scoped Classical

namespace MarkedInner

open GluingCore.MarkedInner

theorem hatMarkWindow_rotate (ω : MarkedInner) :
    hatMarkWindow ω.rotate =
      GluingCore.rotate (translate (ω.v + eCell) (hatMarkWindow ω)) := by
  ext x
  rw [mem_rotate, mem_translate, mem_hatMarkWindow, mem_hatMarkWindow, mem_windowCells,
    mem_windowCells, mem_windowCells, mem_windowCells]
  simp only [GluingCore.MarkedInner.rotate, mem_rotate, GluingCore.MarkedInner.upper,
    mem_translate]
  have e1 : -(x + eCell) = -x - eCell := by abel
  have e2 : -x - (ω.v + eCell) - ω.v = -x - ω.v - ω.v - eCell := by abel
  have e3 : -(x + eCell + ω.v) = -x - eCell - ω.v := by abel
  have e4 : -(x + ω.v) = -x - ω.v := by abel
  have e5 : -x - (ω.v + eCell) + eCell = -x - ω.v := by abel
  have e6 : -x - (ω.v + eCell) + ω.v = -x - eCell := by abel
  have e7 : -(x + eCell) - ω.v = -x - eCell - ω.v := by abel
  have e8 : -x - (ω.v + eCell) = -x - ω.v - eCell := by abel
  have e9 : -(x + eCell) = -x - eCell := by abel
  have e10 : -x - ω.v - eCell + ω.v = -x - eCell := by abel
  have e11 : -x - ω.v - eCell + eCell = -x - ω.v := by abel
  have e12 : -x - ω.v - eCell + eCell + ω.v = -x := by abel
  have e13 : -x - eCell - ω.v = -x - ω.v - eCell := by abel
  have e14 : -x - ω.v + ω.v = -x := by abel
  simp only [e1, e3, e4, e8, e10, e11, e13, e14]
  tauto

theorem hatMiddleFin_rotate (ω : MarkedInner) :
    hatMiddleFin ω.rotate = GluingCore.rotate (translate eCell (hatMiddleFin ω)) := by
  ext x
  rw [mem_rotate, mem_translate, mem_hatMiddleFin, mem_hatMiddleFin, middle_rotate, mem_rotate,
    mem_rotate]
  have e1 : -(x + eCell) = -x - eCell := by abel
  have e2 : -x - eCell + eCell = -x := by abel
  rw [e1, e2]
  tauto

theorem cellSchur_hatMiddleFin_rotate (ω : MarkedInner) :
    cellSchur (hatMiddleFin ω.rotate) = cellSchur (hatMiddleFin ω) := by
  rw [hatMiddleFin_rotate, cellSchur_rotate, cellSchur_translate]

theorem cellSchur_hatMarkFin_rotate {ω : MarkedInner} (hwf : ω.IsWellFormed) (hII : ω.IsNarrow) :
    cellSchur (hatMarkFin ω.rotate) = cellSchur (hatMarkFin ω) := by
  rw [hatMarkFin_eq_hatMarkWindow (isWellFormed_rotate hwf) (isNarrow_rotate hII),
    hatMarkFin_eq_hatMarkWindow hwf hII, hatMarkWindow_rotate, cellSchur_rotate,
    cellSchur_translate]

theorem cellSchur_W_rotate (ω : MarkedInner) :
    cellSchur ω.rotate.W = cellSchur ω.W := by
  change cellSchur (GluingCore.rotate ω.upper) = _
  rw [cellSchur_rotate]
  exact cellSchur_translate _ _

theorem hatFactor_rotate {ω : MarkedInner} (hwf : ω.IsWellFormed) (hII : ω.IsNarrow) :
    hatFactor ω.rotate = hatFactor ω := by
  unfold hatFactor
  rw [cellSchur_W_rotate, cellSchur_hatMarkFin_rotate hwf hII, cellSchur_hatMiddleFin_rotate]

theorem numRows_rotate (D : Diagram) : numRows (GluingCore.rotate D) = numRows D := by
  unfold numRows rowSet GluingCore.rotate
  rw [Finset.image_image]
  have : ((Prod.fst : ℤ × ℤ → ℤ) ∘ fun x => -x) = (fun a : ℤ => -a) ∘ Prod.fst := by
    funext x; simp
  rw [this, ← Finset.image_image]
  exact Finset.card_image_of_injective _ neg_injective

theorem numCols_rotate (D : Diagram) : numCols (GluingCore.rotate D) = numCols D := by
  rw [numCols_eq_card_image_snd, numCols_eq_card_image_snd]
  unfold GluingCore.rotate
  rw [Finset.image_image]
  have : ((Prod.snd : ℤ × ℤ → ℤ) ∘ fun x => -x) = (fun a : ℤ => -a) ∘ Prod.snd := by
    funext x; simp
  rw [this, ← Finset.image_image]
  exact Finset.card_image_of_injective _ neg_injective

theorem card_rotate' (D : Diagram) : (GluingCore.rotate D).card = D.card :=
  Finset.card_image_of_injective _ neg_injective

theorem componentT_rotate {ω : MarkedInner} (hwf : ω.IsWellFormed) (hII : ω.IsNarrow)
    {C : Diagram} (hC : C.Nonempty) :
    componentT ω.rotate (GluingCore.rotate C) = componentT ω C := by
  unfold componentT
  rw [card_rotate', numRows_rotate, numCols_rotate, span_rotate, cellSchur_W_rotate,
    cellSchur_hatMarkFin_rotate hwf hII, cellSchur_hatMiddleFin_rotate,
    ← MarkedInner.cellSchur_compose_rotate_outer hC]

theorem modComp_rotate {ω : MarkedInner} (hwf : ω.IsWellFormed) (hII : ω.IsNarrow)
    (X : Diagram) : modComp ω.rotate (GluingCore.rotate X) = modComp ω X := by
  unfold modComp
  rw [edgeComponents_rotate, Finset.prod_image fun A _ B _ h => rotate_injective h]
  refine Finset.prod_congr rfl fun C hC => ?_
  exact componentT_rotate hwf hII (component_nonempty hC)

end MarkedInner

/-! ### Ribbons removable on the right are the rotations of ribbons removable on the left -/

theorem isRibbon_rotate {Y : Diagram} (h : IsRibbon Y) : IsRibbon (GluingCore.rotate Y) :=
  ⟨isConnectedSkew_rotate h.1, by rw [MarkedInner.card_rotate', span_rotate]; exact h.2⟩

theorem isUpsetIn_iff_rotate {X Y : Diagram} :
    IsUpsetIn X Y ↔ IsDownsetIn (GluingCore.rotate X) (GluingCore.rotate Y) := by
  unfold IsUpsetIn IsDownsetIn
  constructor
  · rintro ⟨hsub, h⟩
    refine ⟨rotate_subset hsub, fun x hx y hy h1 h2 => ?_⟩
    rw [mem_rotate] at hx hy ⊢
    exact h (-x) hx (-y) hy (by simp only [Prod.fst_neg]; omega)
      (by simp only [Prod.snd_neg]; omega)
  · rintro ⟨hsub, h⟩
    refine ⟨?_, fun x hx y hy h1 h2 => ?_⟩
    · intro z hz
      have := hsub (mem_rotate.mpr (by simpa using hz) : -z ∈ GluingCore.rotate Y)
      simpa using mem_rotate.mp this
    · have := h (-x) (mem_rotate.mpr (by simpa using hx)) (-y)
        (mem_rotate.mpr (by simpa using hy)) (by simp only [Prod.fst_neg]; omega)
        (by simp only [Prod.snd_neg]; omega)
      simpa using mem_rotate.mp this

theorem leftRibbons_rotate (X : Diagram) (m : ℕ) :
    leftRibbons (GluingCore.rotate X) m = (rightRibbons X m).image GluingCore.rotate := by
  ext Y'
  rw [Finset.mem_image, mem_leftRibbons]
  constructor
  · rintro ⟨hsub, hcard, hrib, hdown⟩
    refine ⟨GluingCore.rotate Y', ?_, GluingCore.rotate_rotate⟩
    rw [mem_rightRibbons]
    refine ⟨?_, ?_, isRibbon_rotate hrib, ?_⟩
    · have := rotate_subset hsub
      rwa [GluingCore.rotate_rotate] at this
    · rw [MarkedInner.card_rotate']; exact hcard
    · rw [isUpsetIn_iff_rotate, GluingCore.rotate_rotate]; exact hdown
  · rintro ⟨Y, hY, rfl⟩
    rw [mem_rightRibbons] at hY
    obtain ⟨hsub, hcard, hrib, hup⟩ := hY
    refine ⟨rotate_subset hsub, ?_, isRibbon_rotate hrib, ?_⟩
    · rw [MarkedInner.card_rotate']; exact hcard
    · exact isUpsetIn_iff_rotate.mp hup

theorem ribbonSign_rotate (Y : Diagram) : ribbonSign (GluingCore.rotate Y) = ribbonSign Y := by
  unfold ribbonSign ribbonHeight
  rw [MarkedInner.numRows_rotate]

theorem ribbonSumRight_rotate (F F' : Diagram → Lambda) (hF : ∀ Z, F' (GluingCore.rotate Z) = F Z)
    (X : Diagram) (m : ℕ) :
    ribbonSumRight F X m = ribbonSumLeft F' (GluingCore.rotate X) m := by
  unfold ribbonSumRight ribbonSumLeft
  rw [leftRibbons_rotate, Finset.sum_image fun A _ B _ h => rotate_injective h]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [ribbonSign_rotate, ← rotate_sdiff, hF]

theorem edgeEqR_of_edgeEqL_rotate {ω : MarkedInner} (hwf : ω.IsWellFormed) (hII : ω.IsNarrow)
    {X : Diagram} {m : ℕ} (h : EdgeEqL ω.rotate (GluingCore.rotate X) m) : EdgeEqR ω X m := by
  unfold EdgeEqL at h
  unfold EdgeEqR
  rw [MarkedInner.modComp_rotate hwf hII, MarkedInner.hatFactor_rotate hwf hII,
    ← ribbonSumRight_rotate (modComp ω) (modComp ω.rotate)
      (fun Z => MarkedInner.modComp_rotate hwf hII Z)] at h
  have e : edgeSign ω.rotate m = edgeSign ω m := by
    unfold edgeSign
    cases hc : ω.case <;> simp [MarkedInner.rotate, hc, AttachCase.rotate]
  rw [e] at h
  exact h

end Plan

end GluingCore
