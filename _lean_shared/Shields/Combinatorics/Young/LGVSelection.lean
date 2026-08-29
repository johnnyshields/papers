/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic

/-!
# Selecting the first crossing of a family of paths

A sign-reversing involution on families of lattice paths splices the two paths of one
crossing, and it is an involution only because that crossing is chosen canonically:
least height, then least path index meeting a later path there, then least abscissa
shared on that path, then least such later path.  This file makes the choice once, for
an abstract occupancy relation `Occ q i x` -- the abscissae the path `q` holds at height
`i` -- and a crossing set `Meet q r` of the heights at which two paths meet.

Two geometries instantiate it.  In `Shields.LGVInvolution` a path sweeps the whole
interval `[q i, q (i+1)]` at every height below `b`; in `Shields.LGVMixed` it sweeps that
interval below `b` and holds the single point `q i` from `b` on.  The selection sees no
difference between them: it reads occupancy through `Occ` and crossing heights through
`Meet`, and the only thing it asks of the pair is that two monotone paths meeting at a
height share an abscissa there.

## Main definitions

* `Shields.FamMeets` — two paths of the family meet.
* `Shields.selHeight`, `Shields.selIndex`, `Shields.selAbscissa`, `Shields.selPartner` —
  the canonical crossing, each an `sInf` over the corresponding set.

## Main results

* `Shields.selSpec` — the four selectors do name an actual crossing.
* `Shields.select_eq` — **the selection is its own fixed point.**  A second family
  agreeing with the first off the two selected paths, whose selected pair still holds the
  selected abscissa at the selected height, gains no crossing below that height, and
  reaches no abscissa below the selected one that the original did not, has the same four
  selectors.  This is what makes the splice an involution.

## Implementation notes

`select_eq` takes the spliced family as an opaque `G` constrained by five facts, rather
than as a splice.  The two geometries splice differently — one at the selected height,
one above it — and the invariance argument reads only those five facts, so stating it
this way is what lets both geometries share it.

## Papers depending on this file

* `edrei-spectral-classification` — both alphabets of the Jacobi--Trudi cancellation.
-/

namespace Shields

section Selection

variable {m : ℕ} (Occ : (ℕ → ℕ) → ℕ → ℕ → Prop) (Meet : (ℕ → ℕ) → (ℕ → ℕ) → Finset ℕ)

/-- Two paths of the family meet. -/
def FamMeets (F : Fin m → ℕ → ℕ) : Prop :=
  ∃ u v : Fin m, u < v ∧ (Meet (F u) (F v)).Nonempty

/-! ### The selection

Four nested infima.  Each is taken over a set of naturals that is nonempty as soon as the
family meets itself, and each names the data the next one is cut out by. -/

/-- The heights at which some pair of the family meets. -/
def selHeights (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {i | ∃ u v : Fin m, u < v ∧ i ∈ Meet (F u) (F v)}

/-- The least height at which two paths of the family meet. -/
noncomputable def selHeight (F : Fin m → ℕ → ℕ) : ℕ := sInf (selHeights Meet F)

/-- The paths that meet a later path at the least crossing height. -/
def selIndices (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {n | ∃ u : Fin m, (u : ℕ) = n ∧ ∃ v : Fin m, u < v ∧
    ∃ x, Occ (F u) (selHeight Meet F) x ∧ Occ (F v) (selHeight Meet F) x}

/-- The least path index meeting a later path at the least crossing height. -/
noncomputable def selIndex (F : Fin m → ℕ → ℕ) : ℕ := sInf (selIndices Occ Meet F)

/-- The abscissae the selected path shares with a later one at the selected height. -/
def selAbscissae (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {x | ∃ u : Fin m, (u : ℕ) = selIndex Occ Meet F ∧ Occ (F u) (selHeight Meet F) x ∧
    ∃ v : Fin m, u < v ∧ Occ (F v) (selHeight Meet F) x}

/-- The least such abscissa. -/
noncomputable def selAbscissa (F : Fin m → ℕ → ℕ) : ℕ := sInf (selAbscissae Occ Meet F)

/-- The later paths through the selected lattice point. -/
def selPartners (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {n | ∃ v : Fin m, (v : ℕ) = n ∧ selIndex Occ Meet F < n ∧
    Occ (F v) (selHeight Meet F) (selAbscissa Occ Meet F)}

/-- The least such later path. -/
noncomputable def selPartner (F : Fin m → ℕ → ℕ) : ℕ := sInf (selPartners Occ Meet F)

/-- The one demand the selection makes of the geometry: two monotone paths meeting at a
height share an abscissa there. -/
def SharesAbscissa : Prop :=
  ∀ q r : ℕ → ℕ, Monotone q → Monotone r → ∀ i ∈ Meet q r, ∃ x, Occ q i x ∧ Occ r i x

variable {Occ Meet} {F : Fin m → ℕ → ℕ}

theorem selHeights_nonempty (h : FamMeets Meet F) : (selHeights Meet F).Nonempty := by
  obtain ⟨u, v, huv, i, hi⟩ := h
  exact ⟨i, u, v, huv, hi⟩

theorem selHeight_mem (h : FamMeets Meet F) : selHeight Meet F ∈ selHeights Meet F :=
  Nat.sInf_mem (selHeights_nonempty h)

theorem selHeight_le {i : ℕ} (hi : i ∈ selHeights Meet F) : selHeight Meet F ≤ i :=
  Nat.sInf_le hi

theorem selIndex_le {n : ℕ} (hn : n ∈ selIndices Occ Meet F) : selIndex Occ Meet F ≤ n :=
  Nat.sInf_le hn

theorem selAbscissa_le {x : ℕ} (hx : x ∈ selAbscissae Occ Meet F) :
    selAbscissa Occ Meet F ≤ x := Nat.sInf_le hx

theorem selPartner_le {n : ℕ} (hn : n ∈ selPartners Occ Meet F) : selPartner Occ Meet F ≤ n :=
  Nat.sInf_le hn

theorem selIndices_nonempty (hshare : SharesAbscissa Occ Meet) (hF : ∀ w, Monotone (F w))
    (h : FamMeets Meet F) : (selIndices Occ Meet F).Nonempty := by
  obtain ⟨u, v, huv, hmem⟩ := selHeight_mem h
  obtain ⟨x, h1, h2⟩ := hshare _ _ (hF u) (hF v) _ hmem
  exact ⟨u, u, rfl, v, huv, x, h1, h2⟩

theorem selIndex_mem (hshare : SharesAbscissa Occ Meet) (hF : ∀ w, Monotone (F w))
    (h : FamMeets Meet F) : selIndex Occ Meet F ∈ selIndices Occ Meet F :=
  Nat.sInf_mem (selIndices_nonempty hshare hF h)

theorem selAbscissae_nonempty (hshare : SharesAbscissa Occ Meet) (hF : ∀ w, Monotone (F w))
    (h : FamMeets Meet F) : (selAbscissae Occ Meet F).Nonempty := by
  obtain ⟨u, hu, v, huv, x, h1, h2⟩ := selIndex_mem hshare hF h
  exact ⟨x, u, hu, h1, v, huv, h2⟩

theorem selAbscissa_mem (hshare : SharesAbscissa Occ Meet) (hF : ∀ w, Monotone (F w))
    (h : FamMeets Meet F) : selAbscissa Occ Meet F ∈ selAbscissae Occ Meet F :=
  Nat.sInf_mem (selAbscissae_nonempty hshare hF h)

theorem selPartners_nonempty (hshare : SharesAbscissa Occ Meet) (hF : ∀ w, Monotone (F w))
    (h : FamMeets Meet F) : (selPartners Occ Meet F).Nonempty := by
  obtain ⟨u, hu, h1, v, huv, h2⟩ := selAbscissa_mem hshare hF h
  refine ⟨v, v, rfl, ?_, h2⟩
  rw [← hu]
  exact huv

theorem selPartner_mem (hshare : SharesAbscissa Occ Meet) (hF : ∀ w, Monotone (F w))
    (h : FamMeets Meet F) : selPartner Occ Meet F ∈ selPartners Occ Meet F :=
  Nat.sInf_mem (selPartners_nonempty hshare hF h)

/-- **The selected lattice point.**  The two selected paths, the selected height and the
selected abscissa, packaged as the swap consumes them. -/
theorem selSpec (hshare : SharesAbscissa Occ Meet) (hF : ∀ w, Monotone (F w))
    (h : FamMeets Meet F) : ∃ u v : Fin m, (u : ℕ) = selIndex Occ Meet F ∧
      (v : ℕ) = selPartner Occ Meet F ∧ u < v ∧
      Occ (F u) (selHeight Meet F) (selAbscissa Occ Meet F) ∧
      Occ (F v) (selHeight Meet F) (selAbscissa Occ Meet F) := by
  obtain ⟨u, hu, hsu, -⟩ := selAbscissa_mem hshare hF h
  obtain ⟨v, hv, hlt, hsv⟩ := selPartner_mem hshare hF h
  refine ⟨u, v, hu, hv, ?_, hsu, hsv⟩
  rw [Fin.lt_def, hu, hv]
  exact hlt

/-- **The selection is its own fixed point.**  Each of the four selectors is forced by the
one before it: below the selected height nothing moved, at that height the two selected
paths hold the same abscissae between them, and neither reaches below the selected
abscissa anywhere the original did not. -/
theorem select_eq {G : Fin m → ℕ → ℕ} {u v : Fin m} (hshare : SharesAbscissa Occ Meet)
    (hu : (u : ℕ) = selIndex Occ Meet F) (hv : (v : ℕ) = selPartner Occ Meet F) (huv : u < v)
    (hGmono : ∀ w, Monotone (G w)) (hGother : ∀ w : Fin m, w ≠ u → w ≠ v → G w = F w)
    (hGlow : ∀ (w w' : Fin m) (k : ℕ), k < selHeight Meet F →
      (k ∈ Meet (G w) (G w') ↔ k ∈ Meet (F w) (F w')))
    (hGor : ∀ (w : Fin m) (y : ℕ), (w = u ∨ w = v) → Occ (G w) (selHeight Meet F) y →
      Occ (F u) (selHeight Meet F) y ∨ Occ (F v) (selHeight Meet F) y)
    (hGdown : ∀ (w : Fin m) (y : ℕ), (w = u ∨ w = v) → y < selAbscissa Occ Meet F →
      Occ (G w) (selHeight Meet F) y → Occ (F w) (selHeight Meet F) y)
    (hGu : Occ (G u) (selHeight Meet F) (selAbscissa Occ Meet F))
    (hGv : Occ (G v) (selHeight Meet F) (selAbscissa Occ Meet F))
    (hGmeet : selHeight Meet F ∈ Meet (G u) (G v)) :
    FamMeets Meet G ∧ selHeight Meet G = selHeight Meet F ∧
      selIndex Occ Meet G = selIndex Occ Meet F ∧
      selAbscissa Occ Meet G = selAbscissa Occ Meet F ∧
      selPartner Occ Meet G = selPartner Occ Meet F := by
  have hGint : FamMeets Meet G := ⟨u, v, huv, _, hGmeet⟩
  -- (1) the height
  have h1 : selHeight Meet G = selHeight Meet F := by
    refine le_antisymm (selHeight_le ⟨u, v, huv, hGmeet⟩) ?_
    by_contra hcon
    obtain ⟨w, w', hww', hmem⟩ := selHeight_mem hGint
    rw [hGlow w w' _ (by omega)] at hmem
    have := selHeight_le (Meet := Meet) (F := F) ⟨w, w', hww', hmem⟩
    omega
  -- (2) the path index
  have h2 : selIndex Occ Meet G = (u : ℕ) := by
    refine le_antisymm (selIndex_le ⟨u, rfl, v, huv, selAbscissa Occ Meet F,
      by rw [h1]; exact hGu, by rw [h1]; exact hGv⟩) ?_
    obtain ⟨w, hw, w', hww', y, hy1, hy2⟩ := selIndex_mem hshare hGmono hGint
    rw [h1] at hy1 hy2
    by_contra hcon
    have hwu : w < u := by rw [Fin.lt_def, hw]; omega
    have hFw : Occ (F w) (selHeight Meet F) y := by
      rwa [hGother w (ne_of_lt hwu) (ne_of_lt (lt_trans hwu huv))] at hy1
    have hpair : ∃ w'' : Fin m, w < w'' ∧ Occ (F w'') (selHeight Meet F) y := by
      by_cases hc : w' = u ∨ w' = v
      · rcases hGor w' y hc hy2 with hs | hs
        · exact ⟨u, hwu, hs⟩
        · exact ⟨v, lt_trans hwu huv, hs⟩
      · rw [not_or] at hc
        exact ⟨w', hww', by rwa [hGother w' hc.1 hc.2] at hy2⟩
    obtain ⟨w'', hlt, hs⟩ := hpair
    have hle := selIndex_le (Occ := Occ) (Meet := Meet) (F := F) ⟨w, rfl, w'', hlt, y, hFw, hs⟩
    rw [← hu] at hle
    rw [Fin.lt_def] at hwu
    omega
  -- (3) the abscissa
  have h3 : selAbscissa Occ Meet G = selAbscissa Occ Meet F := by
    refine le_antisymm (selAbscissa_le ⟨u, by rw [h2], by rw [h1]; exact hGu, v, huv,
      by rw [h1]; exact hGv⟩) ?_
    obtain ⟨w, hw, hy1, w', hww', hy2⟩ := selAbscissa_mem hshare hGmono hGint
    rw [h2] at hw
    rw [(Fin.val_eq_val w u).mp hw] at hy1 hww'
    rw [h1] at hy1 hy2
    by_contra hcon
    have hlt : selAbscissa Occ Meet G < selAbscissa Occ Meet F := by omega
    have hFu : Occ (F u) (selHeight Meet F) (selAbscissa Occ Meet G) :=
      hGdown u _ (Or.inl rfl) hlt hy1
    have hpair : ∃ w'' : Fin m, u < w'' ∧
        Occ (F w'') (selHeight Meet F) (selAbscissa Occ Meet G) := by
      by_cases hc : w' = v
      · refine ⟨v, huv, ?_⟩
        rw [hc] at hy2
        exact hGdown v _ (Or.inr rfl) hlt hy2
      · exact ⟨w', hww', by rwa [hGother w' (ne_of_gt hww') hc] at hy2⟩
    obtain ⟨w'', hlt2, hs⟩ := hpair
    exact absurd (selAbscissa_le (Occ := Occ) (Meet := Meet) (F := F)
      ⟨u, hu, hFu, w'', hlt2, hs⟩) hcon
  -- (4) the partner
  have h4 : selPartner Occ Meet G = (v : ℕ) := by
    refine le_antisymm (selPartner_le ⟨v, rfl, by rw [h2, ← Fin.lt_def]; exact huv,
      by rw [h1, h3]; exact hGv⟩) ?_
    obtain ⟨w, hw, hlt, hs⟩ := selPartner_mem hshare hGmono hGint
    rw [h1, h3] at hs
    rw [h2] at hlt
    by_contra hcon
    have hwv : w ≠ v := by intro hc; rw [hc] at hw; omega
    have hwu : w ≠ u := by intro hc; rw [hc] at hw; omega
    rw [hGother w hwu hwv] at hs
    have hlt' : selIndex Occ Meet F < (w : ℕ) := by rw [← hu, hw]; exact hlt
    have hle := selPartner_le (Occ := Occ) (Meet := Meet) (F := F) ⟨w, rfl, hlt', hs⟩
    rw [← hv] at hle
    omega
  exact ⟨hGint, h1, by rw [h2, hu], h3, by rw [h4, hv]⟩

end Selection


/-! ### Axiom footprint -/

/-- info: 'Shields.FamMeets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FamMeets

/-- info: 'Shields.selPartner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selPartner

end Shields
