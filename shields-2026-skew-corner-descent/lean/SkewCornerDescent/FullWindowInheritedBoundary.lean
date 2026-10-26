/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.FullWindowProper

/-!
# The actual ordinary boundary is forced by a complete literal period

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`,
`lem:boundary-full-window`). Complete literal windows transport every
terminal first-band diagonal point to the source’s singleton extreme
diagonal. The first band therefore has a genuine singleton terminal
diagonal, and connected-skew boundary steps give its actual empty joining
edge. No private diagonal or joining edge is assumed. Sorry-free.
-/

namespace SkewCornerDescent
open SkewGluing

private theorem thin_diagonal_points_eq {D : Diagram} {k : ℤ} {x y : ℤ × ℤ}
    (hthin : diagLo D k = diagHi D k) (hx : x ∈ D) (hy : y ∈ D)
    (hcx : content x = k) (hcy : content y = k) : x = y := by
  have hlx := diagLo_le hx hcx
  have hux := le_diagHi hx hcx
  have hly := diagLo_le hy hcy
  have huy := le_diagHi hy hcy
  apply Prod.ext
  · omega
  · dsimp only [content] at hcx hcy
    omega

/-- A complete literal multiple-span period produces its singleton
terminal diagonal and actual empty joining edge.

**Differs from the paper's route.** The source’s singleton extreme
diagonals and complete literal period supply the private boundary,
rather than transporting a separately supplied ordinary source cut. -/
theorem fullWindow_period_ordinary_boundary {D : Diagram} (hD : IsConnectedSkew D)
    (b : ℕ) (hb : 2 ≤ b) (δ : ℤ) (hδ : 0 < δ) (v : ℤ × ℤ)
    (hv : content v = δ) (hmin : minContent D = 0)
    (hmax : maxContent D = (b : ℤ) * δ - 1)
    (hwindow : upperFullWindow D b δ = translate v (lowerFullWindow D b δ)) :
    (diagLo D (δ-1) = diagHi D (δ-1)) ∧
      CellAdj (ne (firstContentBand D δ)) (sw (firstContentBand D δ) + v) := by
  have shape := hasDiagonalShape_of_isConnectedSkew hD
  have hbcast : (2 : ℤ) ≤ b := by exact_mod_cast hb
  have hsmall : ∀ k, 0 ≤ k → k < δ → k ∈ contents D := by
    intro k hk0 hkδ
    apply shape.mem_contents_iff.mpr
    rw [hmin, hmax]
    constructor <;> nlinarith
  have hk : δ-1 ∈ contents D := hsmall _ (by omega) (by omega)
  have hzero : (0 : ℤ) ∈ contents D := hsmall _ (by omega) hδ
  have hmaxthin : diagLo D (maxContent D) = diagHi D (maxContent D) := by
    apply shape.2.2.2.2 _ (maxContent_mem shape.1)
    right
    intro hn
    have hh := le_maxContent hn
    omega
  let k := b-1
  have hkb : k < b := by dsimp only [k]; omega
  have hkcast : (k : ℤ) = (b : ℤ)-1 := by dsimp only [k]; omega
  let pLo := (diagLo D (δ-1), diagLo D (δ-1) + (δ-1))
  let pHi := (diagHi D (δ-1), diagHi D (δ-1) + (δ-1))
  have hpLo : pLo ∈ D := diagLo_mem hk
  have hpHi : pHi ∈ D := diagHi_mem hk
  have hcLo : content pLo = δ-1 := by dsimp only [pLo,content]; ring
  have hcHi : content pHi = δ-1 := by dsimp only [pHi,content]; ring
  have hcShift (x : ℤ × ℤ) (hc : content x = δ-1) :
      content (x+(k : ℤ)•v) = maxContent D := by
    rw [content_add, MarkedInner.content_smul, hc, hv, hkcast, hmax]
    ring
  have hLo := (fullWindow_iterate hδ hv hwindow pLo
    (by rw [hcLo]; constructor <;> omega) k hkb).mpr hpLo
  have hHi := (fullWindow_iterate hδ hv hwindow pHi
    (by rw [hcHi]; constructor <;> omega) k hkb).mpr hpHi
  have he := thin_diagonal_points_eq hmaxthin hLo hHi (hcShift pLo hcLo) (hcShift pHi hcHi)
  have hcancel : pLo = pHi := add_right_cancel he
  have hcut : diagLo D (δ-1) = diagHi D (δ-1) := congrArg Prod.fst hcancel
  have hE := firstContentBand_isConnectedSkew hD δ hδ hsmall hmin hcut
  have hend := firstContentBand_extreme_contents δ hδ hsmall
  let E := firstContentBand D δ
  have hneD : ne E ∈ D := (Finset.mem_filter.mp (ne_mem hE.2.1)).1
  have hswD : sw E ∈ D := (Finset.mem_filter.mp (sw_mem hE.2.1)).1
  have hneC : content (ne E) = δ-1 := (content_ne hE.2.1).trans hend.2
  have hswC : content (sw E) = 0 := (content_sw hE.2.1).trans hend.1
  have hne : ne E = pLo := thin_diagonal_points_eq hcut hneD hpLo hneC hcLo
  have hδcontent : δ ∈ contents D := by
    apply shape.mem_contents_iff.mpr
    rw [hmin, hmax]
    constructor <;> nlinarith
  let q := (diagLo D δ, diagLo D δ + δ)
  have hqD : q ∈ D := diagLo_mem hδcontent
  have hqC : content q = δ := by dsimp only [q,content]; ring
  have hqMinusC : content (q-v) = 0 := by rw [MarkedInner.content_sub, hqC, hv]; ring
  have hqMinusD : q-v ∈ D := by
    apply (fullWindow_step hv hwindow (x := q-v) (by
      rw [hqMinusC]
      constructor <;> nlinarith)).mp
    simpa only [sub_add_cancel] using hqD
  have hminthin : diagLo D 0 = diagHi D 0 := by
    apply shape.2.2.2.2 _ hzero
    left
    intro hn
    have hh := minContent_le hn
    rw [hmin] at hh
    omega
  have hback : q-v = sw E := thin_diagonal_points_eq hminthin hqMinusD hswD hqMinusC hswC
  have hq : q = sw E+v := by
    calc
      q = (q-v)+v := by abel
      _ = sw E+v := by rw [hback]
  have hrow := shape.diagLo_anti hk hδcontent (by omega : δ-1 ≤ δ)
  have hadj : CellAdj pLo q := by
    rw [cellAdj_iff]
    dsimp only [pLo,q,Prod.fst,Prod.snd]
    omega
  refine ⟨hcut, ?_⟩
  change CellAdj (ne E) (sw E+v)
  rw [hne, ← hq]
  exact hadj

end SkewCornerDescent
