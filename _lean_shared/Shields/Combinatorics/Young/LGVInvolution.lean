/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.LGVPaths
import Shields.LinearAlgebra.Matrix.TotallyNonneg.Basic

/-!
# The Lindström--Gessel--Viennot involution at every number of rows

The signed sum over families of lattice paths collapses onto the non-intersecting ones,
and this file builds the sign-reversing weight-preserving involution that does it.  A
family is a permutation `σ` of `Fin m` together with a path from each source to the sink
`σ` assigns it; the involution splices the two paths of the first crossing and composes
`σ` with that transposition, so it changes the sign and not the weight, and the surviving
terms are the families with no shared lattice point.

The crossing is selected canonically -- least height, then least index, then least
abscissa, then least partner -- because the involution has to be an involution: a choice
that depended on the family in any other way would not be undone by applying the splice
twice.

## Main definitions

* `Shields.Intersects` — two paths of the family share a lattice point below height `b`.
* `Shields.famHeight`, `Shields.famIndex`, `Shields.famAbscissa`, `Shields.famPartner` —
  the canonical crossing, each an `sInf` over the corresponding cross set.
* `Shields.famSplice` — the involution on families: exchange the tails of the two selected
  paths above the selected height.

## Main results

* `Shields.select_spec` — the four selectors do name an actual crossing.
* `Shields.perm_eq_one_of_not_intersects` — with sources and sinks strictly decreasing, a
  non-intersecting family has `σ = 1`, so the surviving terms carry sign `+1`.
* `Shields.jacobiTrudiDet_eq_sum_nonIntersecting` — **skew Jacobi--Trudi in the path model
  at every `m`**: the `m × m` determinant `det [h_{λ_u - μ_v - u + v}]` over the even
  alphabet is the total weight of the non-intersecting families from the sources of `μ` to
  the sinks of `λ`.

## Implementation notes

The splice is defined on the whole family rather than on a pair of paths so that
`famSplice i u v` is total: outside the two selected indices it is the identity, and at
an out-of-range index `natSwap` is the identity permutation.  Totality is what lets the
involution be summed over without a subtype.

## Papers depending on this file

* `edrei-spectral-classification` — the Jacobi--Trudi side of the Toeplitz minor identity.
-/

namespace Shields

open Finset

section Sweeps

/-- The abscissae the path `q` sweeps at height `i`: it arrives at `q i` and
leaves at `q (i+1)`. -/
def Sweeps (q : ℕ → ℕ) (i x : ℕ) : Prop := q i ≤ x ∧ x ≤ q (i + 1)

/-- Two paths sharing an abscissa at a height below `b` cross there. -/
theorem mem_crossSet_of_sweeps {b i x : ℕ} {q r : ℕ → ℕ} (hi : i < b)
    (hq : Sweeps q i x) (hr : Sweeps r i x) : i ∈ crossSet b q r :=
  mem_crossSet.mpr ⟨hi, le_trans hq.1 hr.2, le_trans hr.1 hq.2⟩

/-- Two crossing paths share an abscissa: the later of the two arrivals. -/
theorem sweeps_of_mem_crossSet {b i : ℕ} {q r : ℕ → ℕ} (hq : Monotone q) (hr : Monotone r)
    (h : i ∈ crossSet b q r) :
    Sweeps q i (max (q i) (r i)) ∧ Sweeps r i (max (q i) (r i)) := by
  obtain ⟨-, h1, h2⟩ := mem_crossSet.mp h
  have hq' := hq (show i ≤ i + 1 by omega)
  have hr' := hr (show i ≤ i + 1 by omega)
  exact ⟨⟨le_max_left _ _, by omega⟩, ⟨le_max_right _ _, by omega⟩⟩

/-- A splice at a crossing height is monotone: the one place the two profiles are
joined is the one place the crossing condition speaks about. -/
theorem monotone_spliceAt {i : ℕ} {q r : ℕ → ℕ} (hq : Monotone q) (hr : Monotone r)
    (hc : q i ≤ r (i + 1)) : Monotone (spliceAt i q r) := by
  intro k₁ k₂ h
  rcases le_or_gt k₂ i with h₂ | h₂
  · rw [spliceAt_of_le _ _ (by omega), spliceAt_of_le _ _ h₂]
    exact hq h
  · rcases le_or_gt k₁ i with h₁ | h₁
    · rw [spliceAt_of_le _ _ h₁, spliceAt_of_gt _ _ h₂]
      exact le_trans (le_trans (hq h₁) hc) (hr (by omega))
    · rw [spliceAt_of_gt _ _ h₁, spliceAt_of_gt _ _ h₂]
      exact hr h

end Sweeps

section Family

variable {m : ℕ}

/-- A path of the family read at a natural-number index; out of range it is the
zero path, which nothing looks at. -/
def famPath (F : Fin m → ℕ → ℕ) (n : ℕ) : ℕ → ℕ :=
  if h : n < m then F ⟨n, h⟩ else fun _ => 0

@[simp]
theorem famPath_val (F : Fin m → ℕ → ℕ) (w : Fin m) : famPath F (w : ℕ) = F w := by
  rw [famPath, dif_pos w.isLt]

/-- Two paths of the family share a lattice point. -/
def Intersects (b : ℕ) (F : Fin m → ℕ → ℕ) : Prop :=
  ∃ u v : Fin m, u < v ∧ Crosses b (F u) (F v)

instance (b : ℕ) (F : Fin m → ℕ → ℕ) : Decidable (Intersects b F) := by
  unfold Intersects; infer_instance

/-! ### The selection

Four nested infima.  Each is taken over a set of naturals that is nonempty as
soon as the family intersects, and each names the data the next one is cut out
by. -/

/-- The heights at which some pair of the family shares a lattice point. -/
def crossHeights (b : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {i | ∃ u v : Fin m, u < v ∧ i ∈ crossSet b (F u) (F v)}

/-- The least height at which two paths of the family meet. -/
noncomputable def famHeight (b : ℕ) (F : Fin m → ℕ → ℕ) : ℕ := sInf (crossHeights b F)

/-- The paths that meet a later path at the least crossing height. -/
def crossIndices (b : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {n | ∃ u : Fin m, (u : ℕ) = n ∧ ∃ v : Fin m, u < v ∧
    ∃ x, Sweeps (F u) (famHeight b F) x ∧ Sweeps (F v) (famHeight b F) x}

/-- The least path index meeting a later path at the least crossing height. -/
noncomputable def famIndex (b : ℕ) (F : Fin m → ℕ → ℕ) : ℕ := sInf (crossIndices b F)

/-- The abscissae the selected path shares with a later one at the selected
height. -/
def crossAbscissae (b : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {x | ∃ u : Fin m, (u : ℕ) = famIndex b F ∧ Sweeps (F u) (famHeight b F) x ∧
    ∃ v : Fin m, u < v ∧ Sweeps (F v) (famHeight b F) x}

/-- The least such abscissa. -/
noncomputable def famAbscissa (b : ℕ) (F : Fin m → ℕ → ℕ) : ℕ := sInf (crossAbscissae b F)

/-- The later paths through the selected lattice point. -/
def crossPartners (b : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {n | ∃ v : Fin m, (v : ℕ) = n ∧ famIndex b F < n ∧
    Sweeps (F v) (famHeight b F) (famAbscissa b F)}

/-- The least such later path. -/
noncomputable def famPartner (b : ℕ) (F : Fin m → ℕ → ℕ) : ℕ := sInf (crossPartners b F)

variable {b : ℕ} {F : Fin m → ℕ → ℕ}

theorem crossHeights_nonempty (h : Intersects b F) : (crossHeights b F).Nonempty := by
  obtain ⟨u, v, huv, i, hi⟩ := h
  exact ⟨i, u, v, huv, hi⟩

theorem famHeight_mem (h : Intersects b F) : famHeight b F ∈ crossHeights b F :=
  Nat.sInf_mem (crossHeights_nonempty h)

theorem famHeight_le {i : ℕ} (hi : i ∈ crossHeights b F) : famHeight b F ≤ i := Nat.sInf_le hi

theorem famHeight_lt (h : Intersects b F) : famHeight b F < b := by
  obtain ⟨u, v, -, hmem⟩ := famHeight_mem h
  exact (mem_crossSet.mp hmem).1

theorem crossIndices_nonempty (hF : ∀ w, Monotone (F w)) (h : Intersects b F) :
    (crossIndices b F).Nonempty := by
  obtain ⟨u, v, huv, hmem⟩ := famHeight_mem h
  obtain ⟨h1, h2⟩ := sweeps_of_mem_crossSet (hF u) (hF v) hmem
  exact ⟨u, u, rfl, v, huv, _, h1, h2⟩

theorem famIndex_mem (hF : ∀ w, Monotone (F w)) (h : Intersects b F) :
    famIndex b F ∈ crossIndices b F :=
  Nat.sInf_mem (crossIndices_nonempty hF h)

theorem famIndex_le {n : ℕ} (hn : n ∈ crossIndices b F) : famIndex b F ≤ n := Nat.sInf_le hn

theorem crossAbscissae_nonempty (hF : ∀ w, Monotone (F w)) (h : Intersects b F) :
    (crossAbscissae b F).Nonempty := by
  obtain ⟨u, hu, v, huv, x, h1, h2⟩ := famIndex_mem hF h
  exact ⟨x, u, hu, h1, v, huv, h2⟩

theorem famAbscissa_mem (hF : ∀ w, Monotone (F w)) (h : Intersects b F) :
    famAbscissa b F ∈ crossAbscissae b F :=
  Nat.sInf_mem (crossAbscissae_nonempty hF h)

theorem famAbscissa_le {x : ℕ} (hx : x ∈ crossAbscissae b F) : famAbscissa b F ≤ x :=
  Nat.sInf_le hx

theorem crossPartners_nonempty (hF : ∀ w, Monotone (F w)) (h : Intersects b F) :
    (crossPartners b F).Nonempty := by
  obtain ⟨u, hu, h1, v, huv, h2⟩ := famAbscissa_mem hF h
  refine ⟨v, v, rfl, ?_, h2⟩
  rw [← hu]
  exact huv

theorem famPartner_mem (hF : ∀ w, Monotone (F w)) (h : Intersects b F) :
    famPartner b F ∈ crossPartners b F :=
  Nat.sInf_mem (crossPartners_nonempty hF h)

theorem famPartner_le {n : ℕ} (hn : n ∈ crossPartners b F) : famPartner b F ≤ n := Nat.sInf_le hn

/-- **The selected lattice point.**  The two selected paths, the selected height
and the selected abscissa, packaged as the swap consumes them. -/
theorem select_spec (hF : ∀ w, Monotone (F w)) (h : Intersects b F) :
    ∃ u v : Fin m, (u : ℕ) = famIndex b F ∧ (v : ℕ) = famPartner b F ∧ u < v ∧
      Sweeps (F u) (famHeight b F) (famAbscissa b F) ∧
      Sweeps (F v) (famHeight b F) (famAbscissa b F) := by
  obtain ⟨u, hu, hsu, -⟩ := famAbscissa_mem hF h
  obtain ⟨v, hv, hlt, hsv⟩ := famPartner_mem hF h
  refine ⟨u, v, hu, hv, ?_, hsu, hsv⟩
  rw [Fin.lt_def, hu, hv]
  exact hlt

end Family

section Splice

variable {m : ℕ}

/-- The family with the tails of the paths at indices `u` and `v` exchanged above
height `i`. -/
def famSplice (i u v : ℕ) (F : Fin m → ℕ → ℕ) : Fin m → ℕ → ℕ := fun w =>
  if (w : ℕ) = u then spliceAt i (F w) (famPath F v)
  else if (w : ℕ) = v then spliceAt i (F w) (famPath F u)
  else F w

theorem famSplice_apply (i u v : ℕ) (F : Fin m → ℕ → ℕ) (w : Fin m) :
    famSplice i u v F w =
      if (w : ℕ) = u then spliceAt i (F w) (famPath F v)
      else if (w : ℕ) = v then spliceAt i (F w) (famPath F u)
      else F w := rfl

variable {i : ℕ} {F : Fin m → ℕ → ℕ} {u v : Fin m}

theorem famSplice_left : famSplice i (u : ℕ) (v : ℕ) F u = spliceAt i (F u) (F v) := by
  rw [famSplice_apply, if_pos rfl, famPath_val]

theorem famSplice_right (huv : u ≠ v) :
    famSplice i (u : ℕ) (v : ℕ) F v = spliceAt i (F v) (F u) := by
  rw [famSplice_apply, if_neg fun hc => huv ((Fin.val_eq_val v u).mp hc).symm, if_pos rfl,
    famPath_val]

theorem famSplice_other {w : Fin m} (h1 : w ≠ u) (h2 : w ≠ v) :
    famSplice i (u : ℕ) (v : ℕ) F w = F w := by
  rw [famSplice_apply, if_neg fun hc => h1 ((Fin.val_eq_val w u).mp hc),
    if_neg fun hc => h2 ((Fin.val_eq_val w v).mp hc)]

/-- Below the splice height nothing moves. -/
theorem famSplice_apply_of_le {w : Fin m} {k : ℕ} (hk : k ≤ i) :
    famSplice i (u : ℕ) (v : ℕ) F w k = F w k := by
  rw [famSplice_apply]
  split_ifs
  · rw [spliceAt_of_le _ _ hk]
  · rw [spliceAt_of_le _ _ hk]
  · rfl

/-- The selected path's sweep at the selected height runs to the partner's exit. -/
theorem sweeps_famSplice_left {y : ℕ} :
    Sweeps (famSplice i (u : ℕ) (v : ℕ) F u) i y ↔ F u i ≤ y ∧ y ≤ F v (i + 1) := by
  rw [Sweeps, famSplice_left, spliceAt_of_le _ _ le_rfl, spliceAt_of_gt _ _ (by omega : i < i + 1)]

theorem sweeps_famSplice_right {y : ℕ} (huv : u ≠ v) :
    Sweeps (famSplice i (u : ℕ) (v : ℕ) F v) i y ↔ F v i ≤ y ∧ y ≤ F u (i + 1) := by
  rw [Sweeps, famSplice_right huv, spliceAt_of_le _ _ le_rfl,
    spliceAt_of_gt _ _ (by omega : i < i + 1)]

theorem mem_crossSet_famSplice_of_lt {b : ℕ} {w w' : Fin m} {k : ℕ} (hk : k < i) :
    k ∈ crossSet b (famSplice i (u : ℕ) (v : ℕ) F w) (famSplice i (u : ℕ) (v : ℕ) F w')
      ↔ k ∈ crossSet b (F w) (F w') := by
  rw [mem_crossSet, mem_crossSet, famSplice_apply_of_le (by omega : k ≤ i),
    famSplice_apply_of_le (by omega : k ≤ i), famSplice_apply_of_le (by omega : k + 1 ≤ i),
    famSplice_apply_of_le (by omega : k + 1 ≤ i)]

/-- **The swap does not leave the two sweeps it joined.**  At the splice height the
union of the two sweeps is unchanged, so an abscissa the spliced path reaches was
reached by one of the originals. -/
theorem sweeps_or_of_sweeps_famSplice {x y : ℕ} (huv : u ≠ v)
    (hu : Sweeps (F u) i x) (hv : Sweeps (F v) i x) {w : Fin m} (hw : w = u ∨ w = v)
    (h : Sweeps (famSplice i (u : ℕ) (v : ℕ) F w) i y) :
    Sweeps (F u) i y ∨ Sweeps (F v) i y := by
  rcases hw with rfl | rfl
  · rw [sweeps_famSplice_left] at h
    simp only [Sweeps] at hu hv ⊢
    omega
  · rw [sweeps_famSplice_right huv] at h
    simp only [Sweeps] at hu hv ⊢
    omega

theorem monotone_famSplice (hF : ∀ w, Monotone (F w)) (h1 : F u i ≤ F v (i + 1))
    (h2 : F v i ≤ F u (i + 1)) (w : Fin m) : Monotone (famSplice i (u : ℕ) (v : ℕ) F w) := by
  rw [famSplice_apply]
  split_ifs with hwu hwv
  · rw [(Fin.val_eq_val w u).mp hwu, famPath_val]
    exact monotone_spliceAt (hF u) (hF v) h1
  · rw [(Fin.val_eq_val w v).mp hwv, famPath_val]
    exact monotone_spliceAt (hF v) (hF u) h2
  · exact hF w

/-- Splicing the same pair at the same height twice is the identity. -/
theorem famSplice_famSplice (huv : u ≠ v) :
    famSplice i (u : ℕ) (v : ℕ) (famSplice i (u : ℕ) (v : ℕ) F) = F := by
  funext w
  by_cases hwu : w = u
  · subst hwu
    rw [famSplice_left, famSplice_left, famSplice_right huv, spliceAt_spliceAt]
  · by_cases hwv : w = v
    · subst hwv
      rw [famSplice_right huv, famSplice_right huv, famSplice_left, spliceAt_spliceAt]
    · rw [famSplice_other hwu hwv, famSplice_other hwu hwv]

end Splice

section Invariance

variable {m : ℕ} {b : ℕ} {F : Fin m → ℕ → ℕ}

/-- The family with the tails of the two selected paths exchanged above the
selected height. -/
noncomputable def lgvFam (b : ℕ) (F : Fin m → ℕ → ℕ) : Fin m → ℕ → ℕ :=
  famSplice (famHeight b F) (famIndex b F) (famPartner b F) F

/-- **The selection is its own fixed point.**  The four selectors read the same
values off the spliced family as off the original, which is what makes the swap
an involution.  Each is forced by the one before it: below the selected height
nothing moved, at that height the two sweeps have the same union, and an abscissa
below the selected one on the selected path was already swept by it. -/
theorem select_lgvFam (hF : ∀ w, Monotone (F w)) (h : Intersects b F) :
    Intersects b (lgvFam b F) ∧ famHeight b (lgvFam b F) = famHeight b F ∧
      famIndex b (lgvFam b F) = famIndex b F ∧
      famAbscissa b (lgvFam b F) = famAbscissa b F ∧
      famPartner b (lgvFam b F) = famPartner b F := by
  obtain ⟨u, v, hu, hv, huv, hsu, hsv⟩ := select_spec hF h
  have hne : u ≠ v := ne_of_lt huv
  have hib : famHeight b F < b := famHeight_lt h
  have hGdef : lgvFam b F = famSplice (famHeight b F) (u : ℕ) (v : ℕ) F := by
    rw [lgvFam, hu, hv]
  rw [hGdef]
  set G := famSplice (famHeight b F) (u : ℕ) (v : ℕ) F with hG
  -- the spliced family, through the six facts the argument uses
  have hGleft : ∀ y : ℕ, Sweeps (G u) (famHeight b F) y ↔
      (F u (famHeight b F) ≤ y ∧ y ≤ F v (famHeight b F + 1)) := by
    intro y; rw [hG, sweeps_famSplice_left]
  have hGright : ∀ y : ℕ, Sweeps (G v) (famHeight b F) y ↔
      (F v (famHeight b F) ≤ y ∧ y ≤ F u (famHeight b F + 1)) := by
    intro y; rw [hG, sweeps_famSplice_right hne]
  have hGother : ∀ w : Fin m, w ≠ u → w ≠ v → G w = F w := by
    intro w h1 h2; rw [hG, famSplice_other h1 h2]
  have hGlow : ∀ (w w' : Fin m) (k : ℕ), k < famHeight b F →
      (k ∈ crossSet b (G w) (G w') ↔ k ∈ crossSet b (F w) (F w')) := by
    intro w w' k hk; rw [hG, mem_crossSet_famSplice_of_lt hk]
  have hGor : ∀ (w : Fin m) (y : ℕ), (w = u ∨ w = v) → Sweeps (G w) (famHeight b F) y →
      (Sweeps (F u) (famHeight b F) y ∨ Sweeps (F v) (famHeight b F) y) := by
    intro w y hw hs
    rw [hG] at hs
    exact sweeps_or_of_sweeps_famSplice hne hsu hsv hw hs
  have hGmono : ∀ w, Monotone (G w) := by
    rw [hG]
    refine monotone_famSplice hF ?_ ?_ <;> · simp only [Sweeps] at hsu hsv; omega
  -- the two selected paths still meet at the selected point
  have hGu : Sweeps (G u) (famHeight b F) (famAbscissa b F) := by
    rw [hGleft]; simp only [Sweeps] at hsu hsv; omega
  have hGv : Sweeps (G v) (famHeight b F) (famAbscissa b F) := by
    rw [hGright]; simp only [Sweeps] at hsu hsv; omega
  clear_value G
  clear hG hGdef
  have hGint : Intersects b G :=
    ⟨u, v, huv, famHeight b F, mem_crossSet_of_sweeps hib hGu hGv⟩
  -- (1) the height
  have h1 : famHeight b G = famHeight b F := by
    refine le_antisymm (famHeight_le ⟨u, v, huv, mem_crossSet_of_sweeps hib hGu hGv⟩) ?_
    by_contra hcon
    obtain ⟨w, w', hww', hmem⟩ := famHeight_mem hGint
    rw [hGlow w w' _ (by omega)] at hmem
    have := famHeight_le (b := b) (F := F) ⟨w, w', hww', hmem⟩
    omega
  -- (2) the path index
  have h2 : famIndex b G = (u : ℕ) := by
    refine le_antisymm (famIndex_le ⟨u, rfl, v, huv, famAbscissa b F, by rw [h1]; exact hGu,
      by rw [h1]; exact hGv⟩) ?_
    obtain ⟨w, hw, w', hww', y, hy1, hy2⟩ := famIndex_mem hGmono hGint
    rw [h1] at hy1 hy2
    by_contra hcon
    have hwu : w < u := by rw [Fin.lt_def, hw]; omega
    have hFw : Sweeps (F w) (famHeight b F) y := by
      rwa [hGother w (ne_of_lt hwu) (ne_of_lt (lt_trans hwu huv))] at hy1
    have hpair : ∃ w'' : Fin m, w < w'' ∧ Sweeps (F w'') (famHeight b F) y := by
      by_cases hc : w' = u ∨ w' = v
      · rcases hGor w' y hc hy2 with hs | hs
        · exact ⟨u, hwu, hs⟩
        · exact ⟨v, lt_trans hwu huv, hs⟩
      · rw [not_or] at hc
        exact ⟨w', hww', by rwa [hGother w' hc.1 hc.2] at hy2⟩
    obtain ⟨w'', hlt, hs⟩ := hpair
    have hle := famIndex_le (b := b) (F := F) ⟨w, rfl, w'', hlt, y, hFw, hs⟩
    rw [← hu] at hle
    rw [Fin.lt_def] at hwu
    omega
  -- (3) the abscissa
  have h3 : famAbscissa b G = famAbscissa b F := by
    refine le_antisymm (famAbscissa_le ⟨u, by rw [h2], by rw [h1]; exact hGu, v, huv,
      by rw [h1]; exact hGv⟩) ?_
    obtain ⟨w, hw, hy1, w', hww', hy2⟩ := famAbscissa_mem hGmono hGint
    rw [h2] at hw
    rw [(Fin.val_eq_val w u).mp hw] at hy1 hww'
    rw [h1] at hy1 hy2
    by_contra hcon
    have hFu : Sweeps (F u) (famHeight b F) (famAbscissa b G) := by
      rw [hGleft] at hy1
      simp only [Sweeps] at hsu hsv ⊢
      omega
    have hpair : ∃ w'' : Fin m, u < w'' ∧ Sweeps (F w'') (famHeight b F) (famAbscissa b G) := by
      by_cases hc : w' = v
      · rw [hc] at hy2
        refine ⟨v, huv, ?_⟩
        rw [hGright] at hy2
        simp only [Sweeps] at hsu hsv ⊢
        omega
      · exact ⟨w', hww', by rwa [hGother w' (ne_of_gt hww') hc] at hy2⟩
    obtain ⟨w'', hlt, hs⟩ := hpair
    exact absurd (famAbscissa_le (b := b) (F := F) ⟨u, hu, hFu, w'', hlt, hs⟩) hcon
  -- (4) the partner
  have h4 : famPartner b G = (v : ℕ) := by
    refine le_antisymm (famPartner_le ⟨v, rfl, by rw [h2, ← Fin.lt_def]; exact huv,
      by rw [h1, h3]; exact hGv⟩) ?_
    obtain ⟨w, hw, hlt, hs⟩ := famPartner_mem hGmono hGint
    rw [h1, h3] at hs
    rw [h2] at hlt
    by_contra hcon
    have hwv : w ≠ v := by intro hc; rw [hc] at hw; omega
    have hwu : w ≠ u := by intro hc; rw [hc] at hw; omega
    rw [hGother w hwu hwv] at hs
    have hlt' : famIndex b F < (w : ℕ) := by rw [← hu, hw]; exact hlt
    have hle := famPartner_le (b := b) (F := F) ⟨w, rfl, hlt', hs⟩
    rw [← hv] at hle
    omega
  exact ⟨hGint, h1, by rw [h2, hu], h3, by rw [h4, hv]⟩

/-- **The swap is an involution on the intersecting families.** -/
theorem lgvFam_lgvFam (hF : ∀ w, Monotone (F w)) (h : Intersects b F) :
    lgvFam b (lgvFam b F) = F := by
  obtain ⟨-, h1, h2, -, h4⟩ := select_lgvFam hF h
  obtain ⟨u, v, hu, hv, huv, -, -⟩ := select_spec hF h
  rw [lgvFam, h1, h2, h4, lgvFam, ← hu, ← hv]
  exact famSplice_famSplice (ne_of_lt huv)

end Invariance

/-! ## The signed sum over families

A family is a permutation `σ` together with a path from each source `S w` to the
sink `C (σ w)`, and it carries the weight of its paths with the sign of `σ`.  The
swap is `lgvFam` on the paths and composition with the transposition of the two
selected indices on `σ`; it is sign-reversing and weight-preserving, so the sum
collapses to the families with no shared lattice point.
-/

section Signed

variable {m : ℕ}

/-- A transposition of two natural-number indices, as a permutation of `Fin m`;
the identity when either index is out of range. -/
noncomputable def natSwap (m u v : ℕ) : Equiv.Perm (Fin m) :=
  if h : u < m ∧ v < m then Equiv.swap ⟨u, h.1⟩ ⟨v, h.2⟩ else 1

theorem natSwap_val (u v : Fin m) : natSwap m (u : ℕ) (v : ℕ) = Equiv.swap u v := by
  rw [natSwap, dif_pos ⟨u.isLt, v.isLt⟩]

theorem natSwap_mul_self (m u v : ℕ) : natSwap m u v * natSwap m u v = 1 := by
  rw [natSwap]
  split_ifs
  · exact Equiv.swap_mul_self _ _
  · exact one_mul 1

/-- The families of paths from the sources `S` to the sinks `C`, one path per
source, together with the assignment of sinks to sources. -/
noncomputable def famFinset (b : ℕ) {m : ℕ} (S C : Fin m → ℕ) :
    Finset ((_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)) :=
  Finset.univ.sigma fun σ => Fintype.piFinset fun w => hPaths b (S w) (C (σ w))

theorem mem_famFinset {b : ℕ} {S C : Fin m → ℕ}
    {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)} :
    x ∈ famFinset b S C ↔ ∀ w, x.2 w ∈ hPaths b (S w) (C (x.1 w)) := by
  rw [famFinset, Finset.mem_sigma, Fintype.mem_piFinset]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem monotone_of_mem_famFinset {b : ℕ} {S C : Fin m → ℕ}
    {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)} (hx : x ∈ famFinset b S C) (w : Fin m) :
    Monotone (x.2 w) :=
  hPaths_mono (mem_famFinset.mp hx w)

variable {R : Type*} [CommRing R]

/-- The signed weight of a family: the product of its path weights, signed by the
assignment of sinks to sources. -/
noncomputable def famWeight (b : ℕ) {m : ℕ} (β : ℕ → R)
    (x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)) : R :=
  ((Equiv.Perm.sign x.1 : ℤ) : R) * ∏ w, pathWeight b β (x.2 w)

/-- **The swap.**  Exchange the tails of the two selected paths and compose the
sink assignment with the transposition of their indices. -/
noncomputable def lgvSwap (b : ℕ) {m : ℕ} (x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)) :
    (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ) :=
  ⟨x.1 * natSwap m (famIndex b x.2) (famPartner b x.2), lgvFam b x.2⟩

variable {b : ℕ} {S C : Fin m → ℕ}

/-- The swap of a family is a family: the two spliced paths keep their sources and
exchange their sinks, which is what composing with the transposition records. -/
theorem lgvSwap_mem {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)}
    (hx : x ∈ famFinset b S C) (h : Intersects b x.2) : lgvSwap b x ∈ famFinset b S C := by
  obtain ⟨u, v, hu, hv, huv, hsu, hsv⟩ := select_spec (monotone_of_mem_famFinset hx) h
  have hmem := mem_famFinset.mp hx
  have hne : u ≠ v := ne_of_lt huv
  have hib : famHeight b x.2 < b := famHeight_lt h
  have hfam : lgvFam b x.2 = famSplice (famHeight b x.2) (u : ℕ) (v : ℕ) x.2 := by
    rw [lgvFam, hu, hv]
  have hns : natSwap m (famIndex b x.2) (famPartner b x.2) = Equiv.swap u v := by
    rw [← hu, ← hv, natSwap_val]
  simp only [Sweeps] at hsu hsv
  refine mem_famFinset.mpr fun w => ?_
  change lgvFam b x.2 w ∈ hPaths b (S w) (C ((x.1 * natSwap m _ _) w))
  rw [hns, hfam, Equiv.Perm.mul_apply]
  by_cases hwu : w = u
  · subst hwu
    rw [famSplice_left, Equiv.swap_apply_left]
    exact spliceAt_mem (hmem w) (hmem v) hib (by omega)
  · by_cases hwv : w = v
    · subst hwv
      rw [famSplice_right hne, Equiv.swap_apply_right]
      exact spliceAt_mem (hmem w) (hmem u) hib (by omega)
    · rw [famSplice_other hwu hwv, Equiv.swap_apply_of_ne_of_ne hwu hwv]
      exact hmem w

/-- The swap moves every intersecting family. -/
theorem lgvSwap_ne {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)}
    (hF : ∀ w, Monotone (x.2 w)) (h : Intersects b x.2) : lgvSwap b x ≠ x := by
  obtain ⟨u, v, hu, hv, huv, -, -⟩ := select_spec hF h
  intro hc
  have h1 : x.1 * natSwap m (famIndex b x.2) (famPartner b x.2) = x.1 := congrArg Sigma.fst hc
  rw [← hu, ← hv, natSwap_val, mul_eq_left] at h1
  have h2 : Equiv.swap u v u = (1 : Equiv.Perm (Fin m)) u := by rw [h1]
  rw [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h2
  exact (ne_of_lt huv) h2.symm

theorem lgvSwap_lgvSwap {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)}
    (hF : ∀ w, Monotone (x.2 w)) (h : Intersects b x.2) : lgvSwap b (lgvSwap b x) = x := by
  obtain ⟨-, -, h2, -, h4⟩ := select_lgvFam hF h
  refine Sigma.ext ?_ ?_
  · change x.1 * natSwap m (famIndex b x.2) (famPartner b x.2) *
      natSwap m (famIndex b (lgvFam b x.2)) (famPartner b (lgvFam b x.2)) = x.1
    rw [h2, h4, mul_assoc, natSwap_mul_self, mul_one]
  · exact heq_of_eq (lgvFam_lgvFam hF h)

/-- **The swap preserves the total weight.**  Away from the two selected paths
nothing moved, and their two weights have the same product. -/
theorem prod_pathWeight_lgvFam (β : ℕ → R)
    {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)} (hx : x ∈ famFinset b S C)
    (h : Intersects b x.2) :
    ∏ w, pathWeight b β (lgvFam b x.2 w) = ∏ w, pathWeight b β (x.2 w) := by
  obtain ⟨u, v, hu, hv, huv, hsu, hsv⟩ := select_spec (monotone_of_mem_famFinset hx) h
  have hmem := mem_famFinset.mp hx
  have hne : u ≠ v := ne_of_lt huv
  have hfam : lgvFam b x.2 = famSplice (famHeight b x.2) (u : ℕ) (v : ℕ) x.2 := by
    rw [lgvFam, hu, hv]
  have hsplit : ∀ g : Fin m → R,
      ∏ w, g w = (∏ w ∈ Finset.univ \ {u, v}, g w) * (g u * g v) := by
    intro g
    rw [← Finset.prod_pair hne, Finset.prod_sdiff (Finset.subset_univ _)]
  rw [hsplit (fun w => pathWeight b β (lgvFam b x.2 w)),
    hsplit (fun w => pathWeight b β (x.2 w)), hfam]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w hw => ?_) ?_
  · rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    rw [famSplice_other hw.2.1 hw.2.2]
  · rw [famSplice_left, famSplice_right hne]
    simp only [Sweeps] at hsu hsv
    exact pathWeight_spliceAt_mul (hmem u) (hmem v) ⟨by omega, by omega⟩ β

/-- **The cancellation.**  The signed sum over all families is the signed sum over
the families whose paths share no lattice point — for any endpoints and any number
of paths.  This is `LGV.sum_crossing_eq_sum_transposed` at every `m`. -/
theorem sum_famWeight_eq_sum_nonIntersecting (b : ℕ) {m : ℕ} (β : ℕ → R) (S C : Fin m → ℕ) :
    ∑ x ∈ famFinset b S C, famWeight b β x
      = ∑ x ∈ (famFinset b S C).filter fun x => ¬ Intersects b x.2, famWeight b β x := by
  refine sum_eq_sum_filter_of_signReversing _ _ _ (lgvSwap b) (fun x hx hP => ?_)
    (fun x hx hP => ?_) (fun x hx hP => ?_) (fun x hx hP => ?_) (fun x hx hP => ?_)
  · exact lgvSwap_mem hx (not_not.mp hP)
  · exact fun hc => hc (select_lgvFam (monotone_of_mem_famFinset hx) (not_not.mp hP)).1
  · exact lgvSwap_ne (monotone_of_mem_famFinset hx) (not_not.mp hP)
  · exact lgvSwap_lgvSwap (monotone_of_mem_famFinset hx) (not_not.mp hP)
  · have h := not_not.mp hP
    obtain ⟨u, v, hu, hv, huv, -, -⟩ := select_spec (monotone_of_mem_famFinset hx) h
    have hns : natSwap m (famIndex b x.2) (famPartner b x.2) = Equiv.swap u v := by
      rw [← hu, ← hv, natSwap_val]
    change ((Equiv.Perm.sign x.1 : ℤ) : R) * _ +
      ((Equiv.Perm.sign (x.1 * natSwap m _ _) : ℤ) : R) * _ = 0
    rw [hns, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (ne_of_lt huv)]
    change ((Equiv.Perm.sign x.1 : ℤ) : R) * ∏ w, pathWeight b β (x.2 w) +
      (((Equiv.Perm.sign x.1 * -1 : ℤˣ) : ℤ) : R) * ∏ w, pathWeight b β (lgvFam b x.2 w) = 0
    rw [prod_pathWeight_lgvFam β hx h]
    push_cast
    ring

end Signed

/-! ## The determinant

With the endpoints prescribes — sources from `μ` and sinks
from `λ`, both shifted by `m-1-u` so that weakly decreasing row lengths become
strictly decreasing endpoints — an intersecting family is forced whenever the
sink assignment is not the identity, so the determinant is the total weight of
the non-intersecting families.
-/

section Determinant

variable {R : Type*} [CommRing R] {b m : ℕ}

/-- Shifting both indices of a Jacobi--Trudi entry leaves it unchanged. -/
theorem jtCoeff_add_right (d : ℕ → R) (p q k : ℕ) : jtCoeff d (p + k) (q + k) = jtCoeff d p q := by
  unfold jtCoeff
  split_ifs with h1 h2 h2
  · congr 1
    omega
  · omega
  · omega
  · rfl

/-- The sources of: the row lengths of `μ`, shifted so that
they strictly decrease. -/
def jtSource (mu : YoungDiagram) (m : ℕ) (v : Fin m) : ℕ := mu.rowLen v + (m - 1 - v)

/-- The sinks of: the row lengths of `λ`, shifted likewise. -/
def jtSink (lam : YoungDiagram) (m : ℕ) (u : Fin m) : ℕ := lam.rowLen u + (m - 1 - u)

theorem strictAnti_jtSource (mu : YoungDiagram) (m : ℕ) : StrictAnti (jtSource mu m) := by
  intro u v huv
  rw [Fin.lt_def] at huv
  have h1 := mu.rowLen_anti u v (le_of_lt huv)
  have h2 := v.isLt
  rw [jtSource, jtSource]
  omega

theorem strictAnti_jtSink (lam : YoungDiagram) (m : ℕ) : StrictAnti (jtSink lam m) := by
  intro u v huv
  rw [Fin.lt_def] at huv
  have h1 := lam.rowLen_anti u v (le_of_lt huv)
  have h2 := v.isLt
  rw [jtSink, jtSink]
  omega

/-- **The determinant as a signed sum over families.**  The Leibniz expansion of
the `m × m` Jacobi--Trudi matrix over the even alphabet is the signed weight of
the families of paths, indexed by source. -/
theorem jacobiTrudiDet_eq_sum_famFinset (β : ℕ → R) (lam mu : YoungDiagram) :
    jacobiTrudiDet (fun k => completeHom b k β) lam mu m
      = ∑ x ∈ famFinset b (jtSource mu m) (jtSink lam m), famWeight b β x := by
  rw [jacobiTrudiDet, Matrix.det_apply', famFinset, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  change _ = ∑ F ∈ Fintype.piFinset _, ((Equiv.Perm.sign σ : ℤ) : R) * ∏ w, pathWeight b β (F w)
  rw [← Finset.mul_sum, ← Finset.prod_univ_sum]
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun w _ => ?_)
  have h1 : lam.rowLen (σ w) + (w : ℕ) + (m - 1)
      = jtSink lam m (σ w) + ((σ w : ℕ) + (w : ℕ)) := by
    have := (σ w).isLt
    have := w.isLt
    rw [jtSink]
    omega
  have h2 : mu.rowLen (w : ℕ) + (σ w : ℕ) + (m - 1)
      = jtSource mu m w + ((σ w : ℕ) + (w : ℕ)) := by
    have := (σ w).isLt
    have := w.isLt
    rw [jtSource]
    omega
  rw [Matrix.of_apply, ← jtCoeff_add_right _ _ _ (m - 1), h1, h2, jtCoeff_add_right,
    ← edgeSum_eq_jtCoeff, edgeSum]

/-- **Non-intersecting forces the identity assignment.**  With strictly decreasing
sources and sinks, a family whose sink assignment inverts two indices has a path
that starts to the right of another and finishes to its left, and two such paths
share a lattice point. -/
theorem perm_eq_one_of_not_intersects {S C : Fin m → ℕ} {σ : Equiv.Perm (Fin m)}
    {F : Fin m → ℕ → ℕ} (hS : StrictAnti S) (hC : StrictAnti C)
    (hmem : ∀ w, F w ∈ hPaths b (S w) (C (σ w))) (h : ¬ Intersects b F) : σ = 1 := by
  by_contra hne
  obtain ⟨u, v, huv, hσ⟩ : ∃ u v : Fin m, u < v ∧ σ v < σ u := by
    by_contra hcon
    refine hne (perm_eq_one_of_strictMono fun a c hac => ?_)
    rcases lt_trichotomy (σ a) (σ c) with hlt | heq | hgt
    · exact hlt
    · exact absurd (σ.injective heq) (ne_of_lt hac)
    · exact absurd ⟨a, c, hac, hgt⟩ hcon
  exact h ⟨u, v, huv, crosses_of_lt (hmem u) (hmem v) (hS huv) (hC hσ)⟩

/-- **Skew Jacobi--Trudi in the path model at `m` rows.**  The `m × m` determinant
`det [h_{λ_u - μ_v - u + v}]` over the even alphabet is the total weight of the
families of `m` paths, from the sources of `μ` to the sinks of `λ` in order, no
two of which share a lattice point.

This is `LGV.jacobiTrudiDet_two_eq_sum_nonCrossing` at every `m`.  Identifying the
non-intersecting families with the tableaux of `λ/μ` is the other half, and it is
proved: at two rows in `LGVTableau` (`nonCrossingIsSkewSchur`) and at every `m`
in `LGVTableauM` (`sum_nonIntersecting_eq_skewSchur`).  Composing the two gives
`JacobiTrudi.SkewJacobiTrudi` for the even alphabet,
`LGVTableauM.skewJacobiTrudi_even`. -/
theorem jacobiTrudiDet_eq_sum_nonIntersecting (β : ℕ → R) (lam mu : YoungDiagram) :
    jacobiTrudiDet (fun k => completeHom b k β) lam mu m
      = ∑ F ∈ (Fintype.piFinset fun w : Fin m =>
            hPaths b (jtSource mu m w) (jtSink lam m w)).filter fun F => ¬ Intersects b F,
          ∏ w, pathWeight b β (F w) := by
  rw [jacobiTrudiDet_eq_sum_famFinset, sum_famWeight_eq_sum_nonIntersecting]
  refine Finset.sum_nbij' (fun x => x.2) (fun F => ⟨1, F⟩) (fun x hx => ?_) (fun F hF => ?_)
    (fun x hx => ?_) (fun F hF => ?_) (fun x hx => ?_)
  · rw [Finset.mem_filter, mem_famFinset] at hx
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun w => ?_, hx.2⟩
    have h1 : x.1 = 1 := perm_eq_one_of_not_intersects (strictAnti_jtSource mu m)
      (strictAnti_jtSink lam m) hx.1 hx.2
    have := hx.1 w
    rwa [h1, Equiv.Perm.one_apply] at this
  · rw [Finset.mem_filter, Fintype.mem_piFinset] at hF
    rw [Finset.mem_filter, mem_famFinset]
    exact ⟨fun w => hF.1 w, hF.2⟩
  · rw [Finset.mem_filter, mem_famFinset] at hx
    have h1 : x.1 = 1 := perm_eq_one_of_not_intersects (strictAnti_jtSource mu m)
      (strictAnti_jtSink lam m) hx.1 hx.2
    exact Sigma.ext h1.symm (heq_of_eq rfl)
  · rfl
  · rw [Finset.mem_filter, mem_famFinset] at hx
    have h1 : x.1 = 1 := perm_eq_one_of_not_intersects (strictAnti_jtSource mu m)
      (strictAnti_jtSink lam m) hx.1 hx.2
    rw [famWeight, h1]
    simp

/-- At two paths the endpoints are those of `LGV.jacobiTrudiDet_two_eq_sum_nonCrossing`:
the first row is shifted by one and the second is not. -/
theorem jtSource_two (mu : YoungDiagram) :
    jtSource mu 2 0 = mu.rowLen 0 + 1 ∧ jtSource mu 2 1 = mu.rowLen 1 := ⟨rfl, rfl⟩

theorem jtSink_two (lam : YoungDiagram) :
    jtSink lam 2 0 = lam.rowLen 0 + 1 ∧ jtSink lam 2 1 = lam.rowLen 1 := ⟨rfl, rfl⟩

/-- The two-path cancellation of `Shields.LGV` is this one at `m = 2`. -/
theorem sum_nonIntersecting_two (β : ℕ → R) (lam mu : YoungDiagram) :
    ∑ F ∈ (Fintype.piFinset fun w : Fin 2 =>
          hPaths b (jtSource mu 2 w) (jtSink lam 2 w)).filter fun F => ¬ Intersects b F,
        ∏ w, pathWeight b β (F w)
      = ∑ x ∈ (hPaths b (mu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ
                hPaths b (mu.rowLen 1) (lam.rowLen 1)).filter
                  fun x => ¬ Crosses b x.1 x.2,
          pathWeight b β x.1 * pathWeight b β x.2 :=
  (jacobiTrudiDet_eq_sum_nonIntersecting β lam mu).symm.trans
    (jacobiTrudiDet_two_eq_sum_nonCrossing β lam mu)

end Determinant

end Shields
