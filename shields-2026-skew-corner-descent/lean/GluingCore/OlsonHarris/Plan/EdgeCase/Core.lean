-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/Core.lean
import GluingCore.OlsonHarris.Plan.EdgeCase.Geometry
import GluingCore.OlsonHarris.Plan.EdgeCase.Kill
import GluingCore.OlsonHarris.Plan.MurnaghanNakayama

/-!
# The left edge equation for a connected outer diagram, case (a)

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.4.6 and Lemma 5.4.7
(`OlsonHarris2024HopfApplications`), for a connected outer diagram and a legal mark of case (a).

The derivation `p_{mq}^⊥` kills `s_W`, `s_{\overline W}`, `s_{\overline O}`
(`pDeriv_cellSchur_hat_aux`), so it acts on the modified composition `tFun ω C` through the union of
copies; Murnaghan–Nakayama (`pDeriv_cellSchur_left`) expresses it as a sum over the ribbons of
size `m q` removable on the left, which are the lifts of the ribbons of size `m` removable on the
left from `C` (`leftRibbons_copies`); removing a lift leaves the composite of the rest and copies
of `W`, `\overline W`, `\overline O` (`cellSchur_copies_sdiff_liftRibbon`), and the exponents are
the cell counts.

Uses `pDeriv_cellSchur_left`.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace GluingCore

namespace Plan

open scoped Classical

theorem isSkew_sdiff_downset {X A : Diagram} (hX : IsSkew X) (hA : IsDownsetIn X A) :
    IsSkew (X \ A) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨hxX, hxA⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyX, hyA⟩ := Finset.mem_sdiff.mp hy
  simp only [Finset.mem_Icc] at hi hj
  have hz : (i, j) ∈ X := hX.mem (a := x.1) (b := x.2) (c := y.1) (d := y.2) hxX hyX h1 h2
    hi.1 hi.2 hj.1 hj.2
  refine Finset.mem_sdiff.mpr ⟨hz, fun hzA => hxA ?_⟩
  exact hA.2 x hxX (i, j) hzA hi.1 hj.1

theorem card_filter_split {X A : Diagram} (hA : IsDownsetIn X A) (u : ℤ × ℤ)
    (hu : 0 ≤ u.1 ∧ 0 ≤ u.2) :
    (X.filter fun x => x + u ∈ X).card =
      ((X \ A).filter fun x => x + u ∈ X \ A).card + (A.filter fun x => x + u ∈ X).card := by
  have e : X.filter (fun x => x + u ∈ X) =
      (X \ A).filter (fun x => x + u ∈ X \ A) ∪ A.filter (fun x => x + u ∈ X) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hx, hxu⟩
      by_cases hxA : x ∈ A
      · exact Or.inr ⟨hxA, hxu⟩
      · refine Or.inl ⟨⟨hx, hxA⟩, hxu, fun hA' => hxA ?_⟩
        exact hA.2 x hx (x + u) hA' (by simp; omega) (by simp; omega)
    · rintro (⟨⟨hx, -⟩, hxu, -⟩ | ⟨hxA, hxu⟩)
      · exact ⟨hx, hxu⟩
      · exact ⟨hA.1 hxA, hxu⟩
  rw [e, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_filter, Finset.mem_sdiff] at hx1 hx2
  exact hx1.1.2 hx2.1

theorem derivation_eq_zero_mul {D : Derivation ℚ Lambda Lambda} {a b : Lambda} (ha : D a = 0)
    (hb : D b = 0) : D (a * b) = 0 := by
  rw [Derivation.leibniz, ha, hb]; simp

theorem derivation_eq_zero_pow {D : Derivation ℚ Lambda Lambda} {a : Lambda} (ha : D a = 0)
    (k : ℕ) : D (a ^ k) = 0 := by
  rw [Derivation.leibniz_pow, ha]; simp

/-- **The left equation for a connected outer diagram** (thesis Lemma 5.4.7), case (a). -/
theorem edgeEqL_connected_a {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .a)
    {C : Diagram} (hC : IsConnectedSkew C) {m : ℕ} (hm : 0 < m) : EdgeEqL ω C m := by
  have hord : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hc]
  have hq : 0 < ω.period := hω.period_pos
  obtain ⟨hW0, hH0, hO0⟩ := pDeriv_cellSchur_hat_aux hω hm
  have hn0 : 0 < m * ω.period.toNat := Nat.mul_pos hm (by omega)
  have hF : IsSkew (MarkedInner.copies ω C) := by
    have := (hω.isConnectedSkew_compose hC).1
    rwa [MarkedInner.compose_eq_copies hord hC.2.1] at this
  obtain ⟨himg, hinj, hsign⟩ := leftRibbons_copies hω hc hC hm
  have hmain : pDeriv (m * ω.period.toNat) (cellSchur (MarkedInner.copies ω C)) =
      ∑ A ∈ leftRibbons C m, ((-1) ^ (m * ω.v.1.natAbs) * ribbonSign A : ℤ) *
        cellSchur (MarkedInner.copies ω C \ liftRibbon ω C A) := by
    rw [pDeriv_cellSchur_left hF hn0]
    unfold ribbonSumLeft
    rw [himg, Finset.sum_image fun A hA B hB h => hinj hA hB h]
    refine Finset.sum_congr rfl fun A hA => ?_
    rw [hsign A hA]
  have hkill : pDeriv (m * ω.period.toNat) (cellSchur ω.W ^ countE C *
      cellSchur (hatMarkFin ω) ^ countS C * cellSchur (hatMiddleFin ω) ^ countSE C) = 0 :=
    derivation_eq_zero_mul (derivation_eq_zero_mul (derivation_eq_zero_pow hW0 _)
      (derivation_eq_zero_pow hH0 _)) (derivation_eq_zero_pow hO0 _)
  unfold EdgeEqL
  rw [modComp_connected_eq_tFun hord hC]
  unfold tFun
  rw [Derivation.leibniz, hkill, hmain]
  simp only [smul_eq_mul, mul_zero, add_zero]
  unfold ribbonSumLeft
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [mem_leftRibbons] at hA
  obtain ⟨hAC, hAcard, hArib, hAdown⟩ := hA
  have hskew : IsSkew (C \ A) := isSkew_sdiff_downset hC.1 hAdown
  rw [modComp_eq_tFun hω hord _ _ rfl hskew]
  rw [cellSchur_copies_sdiff_liftRibbon hω hc hC.1 hAdown]
  have eE := card_filter_split hAdown (0, 1) (by simp)
  have eS := card_filter_split hAdown (1, 0) (by simp)
  have eSE := card_filter_split hAdown eCell (by simp [eCell])
  have cE := Finset.card_filter_add_card_filter_not (s := A) (fun x => x + (0, 1) ∈ C)
  have cS := Finset.card_filter_add_card_filter_not (s := A) (fun x => x + (1, 0) ∈ C)
  have cSE := Finset.card_filter_add_card_filter_not (s := A) (fun x => x + eCell ∈ C)
  unfold tFun countE countS countSE at *
  set aW := (A.filter fun x => x + (0, 1) ∉ C).card
  set aS := (A.filter fun x => x + (1, 0) ∉ C).card
  set aO := (A.filter fun x => x + eCell ∉ C).card
  set sW := cellSchur ω.W
  set sH := cellSchur (hatMarkFin ω)
  set sO := cellSchur (hatMiddleFin ω)
  have hW' : sW ^ (C.filter fun x => x + (0, 1) ∈ C).card * sW ^ aW =
      sW ^ ((C \ A).filter fun x => x + (0, 1) ∈ C \ A).card * sW ^ m := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hH' : sH ^ (C.filter fun x => x + (1, 0) ∈ C).card * sH ^ aS =
      sH ^ ((C \ A).filter fun x => x + (1, 0) ∈ C \ A).card * sH ^ m := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hO' : sO ^ (C.filter fun x => x + eCell ∈ C).card * sO ^ aO =
      sO ^ ((C \ A).filter fun x => x + eCell ∈ C \ A).card * sO ^ m := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hε : edgeSign ω m = (-1) ^ (m * ω.v.1.natAbs) := by simp [edgeSign, hc]
  unfold hatFactor
  rw [hε, mul_pow, mul_pow]
  push_cast
  calc _ = ((-1) ^ (m * ω.v.1.natAbs) * (ribbonSign A : Lambda)) *
        cellSchur (MarkedInner.copies ω (C \ A)) *
        ((sW ^ (C.filter fun x => x + (0, 1) ∈ C).card * sW ^ aW) *
          (sH ^ (C.filter fun x => x + (1, 0) ∈ C).card * sH ^ aS) *
          (sO ^ (C.filter fun x => x + eCell ∈ C).card * sO ^ aO)) := by ring
    _ = _ := by rw [hW', hH', hO']; ring

end Plan

end GluingCore
