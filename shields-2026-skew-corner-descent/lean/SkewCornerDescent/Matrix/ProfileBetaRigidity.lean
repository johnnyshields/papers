/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalProfileAtoms
import SkewCornerDescent.Matrix.OriginalSelectedCoreCoordinates
import SkewGluing.ProfileInvariant

/-!
# Literal normalized components preserve full original beta endpoints

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Canonical cell equality supplies dependent row-count casts for both beta
lists. Actual unit components and selected proper strips then produce their
whole paired original endpoint equivalences in the translated source frame.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open SkewGluing

private theorem beta_cast_of_sigma {n m : ℕ} (P : Profile n) (Q : Profile m)
    (he : (⟨n, P⟩ : Σ r, Profile r) = ⟨m, Q⟩) :
    ∃ hn : n = m, ∀ k : Fin (n + 1),
      Q.xi (Fin.cast (congrArg (fun r : ℕ => r + 1) hn) k) = P.xi k ∧
      Q.zeta (Fin.cast (congrArg (fun r : ℕ => r + 1) hn) k) = P.zeta k := by
  cases he
  exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- Equal normalized cell diagrams identify both complete beta lists under the
canonical dependent row-count cast, rather than only their Schur functions. -/
theorem profile_beta_cast_of_cells_eq {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hcells : P.cells = Q.cells) :
    ∃ hn : n = m, ∀ k : Fin (n + 1),
      Q.xi (Fin.cast (congrArg (fun r : ℕ => r + 1) hn) k) = P.xi k ∧
      Q.zeta (Fin.cast (congrArg (fun r : ℕ => r + 1) hn) k) = P.zeta k := by
  apply beta_cast_of_sigma
  exact Profile.presentation_sigma_unique (v := (0 : ℤ × ℤ)) (w := (0 : ℤ × ℤ))
    (by simpa only [SkewGluing.translate_zero] using hcells)

namespace SelectedCoordinate
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Literal normalized unit components and their actual placement produce the
whole original paired endpoint equivalence, including every full inverse index. -/
theorem original_unit_endpoint_equiv_of_core_cells {n m : ℕ} (P : Profile n) (Q : Profile m)
    (u : OriginalBlocks P) (v : OriginalBlocks Q)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) Q v)
    (hune : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hvne : Q.zeta v.val.castSucc < Q.xi v.val.succ)
    (hcells : (interiorBlockProfile P u.val hune).cells =
      (interiorBlockProfile Q v.val hvne).cells)
    (shift : ℤ) (hτ : originalComponentTau Q v = originalComponentTau P u + shift) :
    ∃ e : Fin (originalRemovedSize (hD := hD) P u) ≃
        Fin (originalRemovedSize (hD := hD) Q v),
      ∀ k, originalRemainingRowBeta Q ⟨v, e k⟩ = originalRemainingRowBeta P ⟨u, k⟩ + shift ∧
        originalRemainingColBeta Q ⟨v, e k⟩ = originalRemainingColBeta P ⟨u, k⟩ + shift := by
  classical
  let U := interiorBlockProfile P u.val hune
  let V := interiorBlockProfile Q v.val hvne
  obtain ⟨hlen, hβ⟩ := profile_beta_cast_of_cells_eq U V hcells
  have hsP : originalRemovedSize (hD := hD) P u = interiorBlockLength P u.val + 1 := by
    simp only [originalRemovedSize, ite_eq_right hu]
  have hsQ : originalRemovedSize (hD := hD) Q v = interiorBlockLength Q v.val + 1 := by
    simp only [originalRemovedSize, ite_eq_right hv]
  let eP := finCongr hsP
  let eQ := finCongr hsQ
  let eLen := finCongr (congrArg (fun r : ℕ => r + 1) hlen)
  let e := eP.trans (eLen.trans eQ.symm)
  refine ⟨e, ?_⟩
  intro k
  let i := eP k
  have hiP : originalUnitIndex P u hu i = k := by apply Fin.ext; rfl
  have hiQ : originalUnitIndex Q v hv (eLen i) = e k := by apply Fin.ext; rfl
  have hbP := original_unit_component_beta P u hu hune i
  have hbQ := original_unit_component_beta Q v hv hvne (eLen i)
  rw [hiP] at hbP
  rw [hiQ] at hbQ
  have hn := hβ i
  change V.xi (eLen i) = U.xi i ∧ V.zeta (eLen i) = U.zeta i at hn
  constructor
  · change Q.xi (originalRemovedRow Q v (e k)).succ =
      P.xi (originalRemovedRow P u k).succ + shift
    rw [hbQ.1, hbP.1, hn.1, hτ]
    exact (add_assoc (U.xi i) (originalComponentTau P u) shift).symm
  · change Q.zeta (originalRemovedCol Q v (e k)).castSucc =
      P.zeta (originalRemovedCol P u k).castSucc + shift
    rw [hbQ.2, hbP.2, hn.2, hτ]
    exact (add_assoc (U.zeta i) (originalComponentTau P u) shift).symm

/-- Literal selected starting components produce the entire proper-strip
endpoint equivalence, even when that strip has size zero. -/
theorem original_selected_endpoint_equiv_of_core_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : OriginalSelectedBlocks (hD := hD) Q)
    (hcells : (interiorBlockProfile P b.val.val
        (originalBlockSelected_nonempty P b.val b.property)).cells =
      (interiorBlockProfile Q d.val.val
        (originalBlockSelected_nonempty Q d.val d.property)).cells)
    (shift : ℤ)
    (hx : Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some d))) =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) + shift) :
    ∃ e : Fin (originalRemovedSize (hD := hD) P b.val) ≃
        Fin (originalRemovedSize (hD := hD) Q d.val),
      ∀ k, originalRemainingRowBeta Q ⟨d.val, e k⟩ =
          originalRemainingRowBeta P ⟨b.val, k⟩ + shift ∧
        originalRemainingColBeta Q ⟨d.val, e k⟩ =
          originalRemainingColBeta P ⟨b.val, k⟩ + shift := by
  classical
  let U := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  let V := interiorBlockProfile Q d.val.val (originalBlockSelected_nonempty Q d.val d.property)
  obtain ⟨hlen, hβ⟩ := profile_beta_cast_of_cells_eq U V hcells
  let eP := finCongr (originalRemovedSize_selected P b)
  let eQ := finCongr (originalRemovedSize_selected Q d)
  let eLen := finCongr hlen
  let e := eP.trans (eLen.trans eQ.symm)
  have hzero := (hβ 0).1
  change V.xi 0 = U.xi 0 at hzero
  have hxP := original_selected_core_retained_row P b
  have hxQ := original_selected_core_retained_row Q d
  change _ = U.xi 0 + originalComponentTau P b.val at hxP
  change _ = V.xi 0 + originalComponentTau Q d.val at hxQ
  have hτ : originalComponentTau Q d.val = originalComponentTau P b.val + shift := by
    apply add_left_cancel (a := U.xi 0)
    calc
      U.xi 0 + originalComponentTau Q d.val =
          V.xi 0 + originalComponentTau Q d.val :=
        congrArg (fun r : ℤ => r + originalComponentTau Q d.val) hzero.symm
      _ = Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some d))) := hxQ.symm
      _ = P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) + shift := hx
      _ = (U.xi 0 + originalComponentTau P b.val) + shift :=
        congrArg (fun r : ℤ => r + shift) hxP
      _ = U.xi 0 + (originalComponentTau P b.val + shift) := add_assoc _ _ _
  refine ⟨e, ?_⟩
  intro k
  let i := eP k
  have hiP : Fin.cast (originalRemovedSize_selected P b).symm i = k := by apply Fin.ext; rfl
  have hiQ : Fin.cast (originalRemovedSize_selected Q d).symm (eLen i) = e k := by
    apply Fin.ext
    rfl
  have hrP := original_selected_core_row_coordinate P b i
  have hcP := original_selected_core_col_coordinate P b i
  have hrQ := original_selected_core_row_coordinate Q d (eLen i)
  have hcQ := original_selected_core_col_coordinate Q d (eLen i)
  rw [hiP] at hrP hcP
  rw [hiQ] at hrQ hcQ
  change originalResponseRows P ⟨b.val, k⟩ =
    U.xi i.succ + originalComponentTau P b.val at hrP
  change originalResponseCols P ⟨b.val, k⟩ =
    U.zeta i.castSucc + originalComponentTau P b.val at hcP
  change originalResponseRows Q ⟨d.val, e k⟩ =
    V.xi (eLen i).succ + originalComponentTau Q d.val at hrQ
  change originalResponseCols Q ⟨d.val, e k⟩ =
    V.zeta (eLen i).castSucc + originalComponentTau Q d.val at hcQ
  have hsucc : Fin.cast (congrArg (fun r : ℕ => r + 1) hlen) i.succ = (eLen i).succ := by
    apply Fin.ext
    rfl
  have hcast : Fin.cast (congrArg (fun r : ℕ => r + 1) hlen) i.castSucc =
      (eLen i).castSucc := by
    apply Fin.ext
    rfl
  have hr := (hβ i.succ).1
  have hc := (hβ i.castSucc).2
  rw [hsucc] at hr
  rw [hcast] at hc
  constructor
  · change originalResponseRows Q ⟨d.val, e k⟩ = originalResponseRows P ⟨b.val, k⟩ + shift
    rw [hrQ, hrP, hr, hτ]
    exact (add_assoc (U.xi i.succ) (originalComponentTau P b.val) shift).symm
  · change originalResponseCols Q ⟨d.val, e k⟩ = originalResponseCols P ⟨b.val, k⟩ + shift
    rw [hcQ, hcP, hc, hτ]
    exact (add_assoc (U.zeta i.castSucc) (originalComponentTau P b.val) shift).symm

/-- Literal selected ending components give the complete proper-strip copy
in the outgoing endpoint frame, including an empty proper strip. -/
theorem original_selected_endpoint_equiv_of_end_core_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : OriginalSelectedBlocks (hD := hD) Q)
    (hcells : (interiorBlockProfile P b.val.val
        (originalBlockSelected_nonempty P b.val b.property)).cells =
      (interiorBlockProfile Q d.val.val
        (originalBlockSelected_nonempty Q d.val d.property)).cells)
    (shift : ℤ)
    (hy : Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some d))) =
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) + shift) :
    ∃ e : Fin (originalRemovedSize (hD := hD) P b.val) ≃
        Fin (originalRemovedSize (hD := hD) Q d.val),
      ∀ k, originalRemainingRowBeta Q ⟨d.val, e k⟩ =
          originalRemainingRowBeta P ⟨b.val, k⟩ + shift ∧
        originalRemainingColBeta Q ⟨d.val, e k⟩ =
          originalRemainingColBeta P ⟨b.val, k⟩ + shift := by
  let U := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  let V := interiorBlockProfile Q d.val.val (originalBlockSelected_nonempty Q d.val d.property)
  obtain ⟨hlen, hβ⟩ := profile_beta_cast_of_cells_eq U V hcells
  have hxi := (hβ 0).1
  change V.xi 0 = U.xi 0 at hxi
  have hτ : originalComponentTau Q d.val = originalComponentTau P b.val + shift := by
    simpa only [originalColSplitEquiv_selected, originalComponentTau] using hy
  have hrP := original_selected_core_retained_row P b
  have hrQ := original_selected_core_retained_row Q d
  change _ = U.xi 0 + originalComponentTau P b.val at hrP
  change _ = V.xi 0 + originalComponentTau Q d.val at hrQ
  apply original_selected_endpoint_equiv_of_core_cells P Q b d hcells shift
  rw [hrP, hrQ, hxi, hτ]
  exact (add_assoc _ _ _).symm

end SelectedCoordinate
end SkewCornerDescent.Matrix
