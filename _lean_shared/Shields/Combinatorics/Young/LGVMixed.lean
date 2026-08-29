/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.LGVInvolution
import Shields.Combinatorics.Young.LGVOddResidue

/-!
# The cancellation for the mixed crossing predicate

`Shields.Combinatorics.Young.LGVInvolution` cancels the signed sum over families of **even**
paths, where non-intersection is interval disjointness at every height, and
`Shields.Combinatorics.Young.LGVOddPaths` cancels a pair of **odd** paths, where it is point
disjointness.  A mixed path carries both geometries at once -- `Shields.MixedMeets` tests
intervals on the heights `0, …, b-1` and points on the heights `b, …, b+a` -- and this module runs
one involution across the two.

* **One occupancy.**  `Shields.MOcc` is the set of abscissae a mixed path occupies at a height:
  the interval `[q i, q (i+1)]` below `b`, the single point `q i` from `b` on.  `Shields.MMeetsAt`
  is a shared point at one height and `Shields.MMeets` a shared point at some height `≤ b + a`;
  `Shields.mMeets_iff_mixedMeets` identifies the latter with `Shields.MixedMeets`, so the two
  readings of the predicate agree.  Height `b` belongs to the odd half in both.  These sit in
  `Shields.Combinatorics.Young.LGVOddResidue`, which the fibering there needs them for; what this
  module adds is `Shields.mMeets_of_lt`, that a pair with transposed endpoints has to meet.
* **One splice.**  `Shields.spliceAt` serves both geometries.  The odd cut is at the meeting index
  and the even cut one above it, but at an odd meeting height the two profiles already agree
  there, so the two cuts are the *same function*
  (`Shields.spliceAt_eq_eSpliceAt_of_meet`).  `Shields.mSplice_mem` is the one new fact: the
  spliced profile is again a mixed path, the unit steps above height `b` included.
* **One selection.**  `Shields.mFamHeight`, `Shields.mFamIndex`, `Shields.mFamAbscissa` and
  `Shields.mFamPartner` read the least shared point of the family across both geometries at once
  -- least height, then least path index meeting a later path there, then least abscissa on that
  path, then least such later path -- and `Shields.select_mLgvFam` shows the four are unchanged by
  the splice.  Below and *at* the selected height nothing moves, which is what makes them stable.

## Main results

* `Shields.sum_mFamWeight_eq_sum_nonIntersecting` -- the signed sum over all mixed families
  collapses to the families with no shared lattice point, at arbitrary endpoints and every `m`,
  with no hypotheses.  `Shields.mixedJacobiTrudiDet_eq_sum_nonIntersecting` is the determinant
  form.

## Implementation notes

Indexing is by **source**: re-indexing by sink breaks involutivity, and the abscissa selector is
what makes the argument close at arbitrary endpoints.

Beyond two rows the residue is no longer the cancellation but the tableau side,
`Shields.NonIntersectingIsSuperSkewSchur` -- that the non-intersecting mixed families of `m` paths
carry the branching sum.  It is proved here at `m ≤ 2` and carried as a hypothesis of
`Shields.skewJacobiTrudi_of_nonIntersecting` beyond that;
`Shields.Combinatorics.Young.LGVOddTableau` discharges it at every `m` and
`Shields.Combinatorics.Young.LGVOddTableauTwo` at two.

## Tags

Lindström-Gessel-Viennot, sign-reversing involution, non-intersecting paths, Jacobi-Trudi, super
Schur function
-/

namespace Shields

open Finset

/-! ## When a pair of mixed paths has no choice but to meet

`LGVOddResidue.MMeets` reads a shared lattice point one height at a time: an interval at an even
height, a point at an odd one.  What the involution needs on top of it is that a pair whose
sources and sinks are oppositely ordered always shares one.
-/

section Geometry

/-- **The transposed term is entirely meeting.**  Two mixed paths whose sources
and sinks are oppositely ordered share a lattice point.  The difference of the
profiles starts positive and ends negative; where it changes sign, an even
height gives meeting intervals outright, and an odd height cannot change it
without an equality, because both steps are units. -/
theorem mMeets_of_lt {b a s₁ e₁ s₂ e₂ : ℕ} {q r : ℕ → ℕ} (hq : q ∈ mixedPaths b a s₁ e₁)
    (hr : r ∈ mixedPaths b a s₂ e₂) (hs : s₂ < s₁) (he : e₁ < e₂) : MMeets b a q r := by
  obtain ⟨hq', hqs⟩ := mem_mixedPaths.mp hq
  obtain ⟨hr', hrs⟩ := mem_mixedPaths.mp hr
  obtain ⟨j, hmin, hle⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
    (p := fun k => q k ≤ r k)
    (by rw [hPaths_zero hq', hPaths_zero hr']; omega)
    ⟨b + a, by rw [hPaths_top hq' le_rfl, hPaths_top hr' le_rfl]; omega⟩
  have hjt : j < b + a := by
    by_contra hc
    rw [hPaths_top hq' (by omega), hPaths_top hr' (by omega)] at hmin
    omega
  rcases lt_or_ge j b with hjb | hjb
  · refine ⟨j, mem_mMeetSet.mpr ⟨by omega, Or.inl ⟨hjb, ?_, ?_⟩⟩⟩
    · exact le_trans (hPaths_mono hq' (by omega : j ≤ j + 1)) hle
    · exact le_trans (by omega) (hPaths_mono hq' (by omega : j ≤ j + 1))
  · have hstep := hrs j hjb (by omega)
    have hmono := hPaths_mono hq' (by omega : j ≤ j + 1)
    exact ⟨j + 1, mem_mMeetSet.mpr ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩⟩

end Geometry

/-! ## The splice, in both geometries at once

`spliceAt` cuts above the index and `eSpliceAt` at it; at a meeting
point of the odd geometry the two profiles agree there, so the two cuts are the
same function and one splice serves both halves.  What has to be reproved is
membership: the spliced profile is a mixed path, unit steps included.
-/

section Splice

variable {b a i : ℕ} {q r : ℕ → ℕ}

theorem mixedPaths_mem {s e : ℕ} (hq : q ∈ mixedPaths b a s e) : q ∈ hPaths (b + a) s e :=
  (mem_mixedPaths.mp hq).1

theorem mixedPaths_step {s e : ℕ} (hq : q ∈ mixedPaths b a s e) {k : ℕ} (h1 : b ≤ k)
    (h2 : k < b + a) : q (k + 1) ≤ q k + 1 :=
  (mem_mixedPaths.mp hq).2 k h1 h2

/-- **The two cuts are one.**  At an odd meeting height the profiles agree, so
cutting above the index and cutting at it give the same profile: the even splice
of `Shields.LGV` already is the odd splice of `Shields.LGVOdd`. -/
theorem spliceAt_eq_eSpliceAt_of_meet (hmeet : q i = r i) : spliceAt i q r = eSpliceAt i q r := by
  funext k
  rcases lt_or_ge k i with hk | hk
  · rw [spliceAt_of_le _ _ (by omega), eSpliceAt_of_lt _ _ hk]
  · rcases eq_or_lt_of_le hk with rfl | hk'
    · rw [spliceAt_of_le _ _ le_rfl, eSpliceAt_of_ge _ _ le_rfl, hmeet]
    · rw [spliceAt_of_gt _ _ hk', eSpliceAt_of_ge _ _ (by omega)]

/-- A splice at a meeting height is again a mixed path, from `q`'s source to
`r`'s sink.  Above height `b` the step at the join is one of the two originals'
steps, so it is still a unit. -/
theorem mSplice_mem {s₁ e₁ s₂ e₂ : ℕ} (hq : q ∈ mixedPaths b a s₁ e₁)
    (hr : r ∈ mixedPaths b a s₂ e₂) (hi : i ≤ b + a) (hm : MMeetsAt b q r i) :
    spliceAt i q r ∈ mixedPaths b a s₁ e₂ := by
  have hq' := mixedPaths_mem hq
  have hr' := mixedPaths_mem hr
  have hjoin : q i ≤ r (i + 1) := mMeetsAt_cross (hPaths_mono hr') hm
  refine mem_mixedPaths.mpr ⟨mem_hPaths.mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [spliceAt_of_le _ _ (Nat.zero_le i)]
    exact hPaths_zero hq'
  · exact monotone_spliceAt (hPaths_mono hq') (hPaths_mono hr') hjoin
  · intro k hk
    rcases lt_or_ge i k with hik | hik
    · rw [spliceAt_of_gt _ _ hik]
      exact hPaths_top hr' hk
    · have hki : k = i := by omega
      rw [hki, spliceAt_of_le _ _ le_rfl, eq_of_mMeetsAt (by omega) hm]
      exact hPaths_top hr' (by omega)
  · intro k hkb hka
    rcases le_or_gt (k + 1) i with h₁ | h₁
    · rw [spliceAt_of_le _ _ h₁, spliceAt_of_le _ _ (by omega : k ≤ i)]
      exact mixedPaths_step hq hkb hka
    · rcases lt_or_ge i k with h₂ | h₂
      · rw [spliceAt_of_gt _ _ (by omega : i < k + 1), spliceAt_of_gt _ _ h₂]
        exact mixedPaths_step hr hkb hka
      · have hki : k = i := by omega
        rw [spliceAt_of_gt _ _ (by omega : i < k + 1), spliceAt_of_le _ _ (by omega : k ≤ i),
          hki, eq_of_mMeetsAt (by omega) hm]
        exact mixedPaths_step hr (by omega) (by omega)

end Splice

/-! ## The mixed weight as one alphabet

The `b` even and the `a` odd variables read as a single sequence of `b + a`
letters, so a mixed path's weight is an ordinary `pathWeight` across `b + a`
heights.  Everything the even model proves about weights then applies verbatim,
the splice's weight invariance included.
-/

section Weight

variable {R : Type*} [CommRing R]

/-- The two alphabets as one sequence: `β` on the even heights, `α` on the odd
ones. -/
def mixedVar (b : ℕ) (β α : ℕ → R) (j : ℕ) : R := if j < b then β j else α (j - b)

theorem mixedWeight_eq_pathWeight (b a : ℕ) (β α : ℕ → R) (q : ℕ → ℕ) :
    mixedWeight b a β α q = pathWeight (b + a) (mixedVar b β α) q := by
  rw [mixedWeight, pathWeight, pathWeight, pathWeight, Finset.prod_range_add]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun i hi => ?_)
    (Finset.prod_congr rfl fun i _ => ?_)
  · rw [mixedVar, if_pos (Finset.mem_range.mp hi)]
  · have h1 : shiftAt b q (i + 1) = q (b + i + 1) := rfl
    rw [mixedVar, if_neg (by omega), Nat.add_sub_cancel_left, h1]
    rfl

end Weight

/-! ## The selection

Four nested infima, exactly those of `Shields.LGVInvolution` with the even
sweep replaced by the mixed occupancy: the least height carrying a shared point,
the least path index meeting a later path there, the least abscissa on that path
shared with a later one, and the least such later path.
-/

section Family

variable {m : ℕ}

/-- The heights at which some pair of the family shares a lattice point. -/
def mCrossHeights (b a : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ := selHeights (mMeetSet b a) F

/-- The least height at which two paths of the family meet. -/
noncomputable def mFamHeight (b a : ℕ) (F : Fin m → ℕ → ℕ) : ℕ := selHeight (mMeetSet b a) F

/-- The paths that meet a later path at the least crossing height. -/
def mCrossIndices (b a : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ :=
  selIndices (MOcc b) (mMeetSet b a) F

/-- The least path index meeting a later path at the least crossing height. -/
noncomputable def mFamIndex (b a : ℕ) (F : Fin m → ℕ → ℕ) : ℕ :=
  selIndex (MOcc b) (mMeetSet b a) F

/-- The abscissae the selected path shares with a later one at the selected
height. -/
def mCrossAbscissae (b a : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ :=
  selAbscissae (MOcc b) (mMeetSet b a) F

/-- The least such abscissa. -/
noncomputable def mFamAbscissa (b a : ℕ) (F : Fin m → ℕ → ℕ) : ℕ :=
  selAbscissa (MOcc b) (mMeetSet b a) F

/-- The later paths through the selected lattice point. -/
def mCrossPartners (b a : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ :=
  selPartners (MOcc b) (mMeetSet b a) F

/-- The least such later path. -/
noncomputable def mFamPartner (b a : ℕ) (F : Fin m → ℕ → ℕ) : ℕ :=
  selPartner (MOcc b) (mMeetSet b a) F

variable {b a : ℕ} {F : Fin m → ℕ → ℕ}

/-- Two paths meeting at a height share the later of their two arrivals, which is all the
selection asks of the mixed geometry. -/
theorem sharesAbscissa_mMeetSet (b a : ℕ) : SharesAbscissa (MOcc b) (mMeetSet b a) :=
  fun _ _ hq hr _ hmem => ⟨_, mOcc_of_mMeetsAt hq hr (mem_mMeetSet.mp hmem).2⟩

theorem mCrossHeights_nonempty (h : MIntersects b a F) : (mCrossHeights b a F).Nonempty :=
  selHeights_nonempty h

theorem mFamHeight_mem (h : MIntersects b a F) : mFamHeight b a F ∈ mCrossHeights b a F :=
  selHeight_mem h

theorem mFamHeight_le {i : ℕ} (hi : i ∈ mCrossHeights b a F) : mFamHeight b a F ≤ i :=
  selHeight_le hi

theorem mFamHeight_le_top (h : MIntersects b a F) : mFamHeight b a F ≤ b + a := by
  obtain ⟨u, v, -, hmem⟩ := mFamHeight_mem h
  exact (mem_mMeetSet.mp hmem).1

theorem mCrossIndices_nonempty (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    (mCrossIndices b a F).Nonempty :=
  selIndices_nonempty (sharesAbscissa_mMeetSet b a) hF h

theorem mFamIndex_mem (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    mFamIndex b a F ∈ mCrossIndices b a F :=
  selIndex_mem (sharesAbscissa_mMeetSet b a) hF h

theorem mFamIndex_le {n : ℕ} (hn : n ∈ mCrossIndices b a F) : mFamIndex b a F ≤ n := selIndex_le hn

theorem mCrossAbscissae_nonempty (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    (mCrossAbscissae b a F).Nonempty :=
  selAbscissae_nonempty (sharesAbscissa_mMeetSet b a) hF h

theorem mFamAbscissa_mem (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    mFamAbscissa b a F ∈ mCrossAbscissae b a F :=
  selAbscissa_mem (sharesAbscissa_mMeetSet b a) hF h

theorem mFamAbscissa_le {x : ℕ} (hx : x ∈ mCrossAbscissae b a F) : mFamAbscissa b a F ≤ x :=
  selAbscissa_le hx

theorem mCrossPartners_nonempty (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    (mCrossPartners b a F).Nonempty :=
  selPartners_nonempty (sharesAbscissa_mMeetSet b a) hF h

theorem mFamPartner_mem (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    mFamPartner b a F ∈ mCrossPartners b a F :=
  selPartner_mem (sharesAbscissa_mMeetSet b a) hF h

theorem mFamPartner_le {n : ℕ} (hn : n ∈ mCrossPartners b a F) : mFamPartner b a F ≤ n :=
  selPartner_le hn

/-- **The selected lattice point.**  The two selected paths, the selected height
and the selected abscissa, packaged as the swap consumes them. -/
theorem select_mSpec (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    ∃ u v : Fin m, (u : ℕ) = mFamIndex b a F ∧ (v : ℕ) = mFamPartner b a F ∧ u < v ∧
      MOcc b (F u) (mFamHeight b a F) (mFamAbscissa b a F) ∧
      MOcc b (F v) (mFamHeight b a F) (mFamAbscissa b a F) :=
  selSpec (sharesAbscissa_mMeetSet b a) hF h

end Family

/-! ## The swap, and the invariance of the selection

The splice of `Shields.LGVInvolution` is reused unchanged: it cuts above the
selected height, which at an odd height is the same profile as cutting at it.
Three facts carry the invariance argument across both geometries — at and below
the selected height nothing moves, the union of the two occupancies at that
height is unchanged, and an abscissa below the selected one on a selected path
was already occupied by it.  At an odd height all three are immediate, since the
occupancies there are untouched.
-/

section Invariance

variable {m : ℕ} {b a : ℕ} {F : Fin m → ℕ → ℕ} {i : ℕ} {u v : Fin m}

/-- The two selected paths still occupy the selected point after the splice. -/
theorem mOcc_famSplice_self (huv : u ≠ v) {x : ℕ} (hsu : MOcc b (F u) i x)
    (hsv : MOcc b (F v) i x) :
    MOcc b (famSplice i (u : ℕ) (v : ℕ) F u) i x ∧
      MOcc b (famSplice i (u : ℕ) (v : ℕ) F v) i x := by
  rcases lt_or_ge i b with hib | hib
  · rw [MOcc] at hsu hsv
    constructor
    · refine Or.inl ⟨hib, ?_, ?_⟩
      · rw [famSplice_left, spliceAt_of_le _ _ le_rfl]
        omega
      · rw [famSplice_left, spliceAt_of_gt _ _ (by omega : i < i + 1)]
        omega
    · refine Or.inl ⟨hib, ?_, ?_⟩
      · rw [famSplice_right huv, spliceAt_of_le _ _ le_rfl]
        omega
      · rw [famSplice_right huv, spliceAt_of_gt _ _ (by omega : i < i + 1)]
        omega
  · rw [MOcc] at hsu hsv
    exact ⟨Or.inr ⟨hib, by rw [famSplice_apply_of_le (le_refl i)]; omega⟩,
      Or.inr ⟨hib, by rw [famSplice_apply_of_le (le_refl i)]; omega⟩⟩

/-- **The swap does not leave the two occupancies it joined.**  At the selected
height the union of the two occupancies is unchanged, so an abscissa a spliced
path reaches was reached by one of the originals. -/
theorem mOcc_or_of_mOcc_famSplice (huv : u ≠ v) {x y : ℕ} (hsu : MOcc b (F u) i x)
    (hsv : MOcc b (F v) i x) {w : Fin m} (hw : w = u ∨ w = v)
    (h : MOcc b (famSplice i (u : ℕ) (v : ℕ) F w) i y) :
    MOcc b (F u) i y ∨ MOcc b (F v) i y := by
  rcases lt_or_ge i b with hib | hib
  · rw [MOcc] at hsu hsv
    rcases hw with rfl | rfl
    · rw [famSplice_left, MOcc, spliceAt_of_le _ _ le_rfl,
        spliceAt_of_gt _ _ (by omega : i < i + 1)] at h
      rw [MOcc, MOcc]
      omega
    · rw [famSplice_right huv, MOcc, spliceAt_of_le _ _ le_rfl,
        spliceAt_of_gt _ _ (by omega : i < i + 1)] at h
      rw [MOcc, MOcc]
      omega
  · rcases h with ⟨hc, -, -⟩ | ⟨-, hy'⟩
    · omega
    · rw [famSplice_apply_of_le (le_refl i)] at hy'
      rcases hw with rfl | rfl
      · exact Or.inl (Or.inr ⟨hib, hy'⟩)
      · exact Or.inr (Or.inr ⟨hib, hy'⟩)

/-- An abscissa below the selected one, occupied by a selected path after the
splice, was already occupied by it: this is what the abscissa selector buys. -/
theorem mOcc_of_mOcc_famSplice_lt (huv : u ≠ v) {x y : ℕ} (hsu : MOcc b (F u) i x)
    (hsv : MOcc b (F v) i x) (hy : y < x) {w : Fin m} (hw : w = u ∨ w = v)
    (h : MOcc b (famSplice i (u : ℕ) (v : ℕ) F w) i y) : MOcc b (F w) i y := by
  rcases lt_or_ge i b with hib | hib
  · rw [MOcc] at hsu hsv
    rcases hw with rfl | rfl
    · rw [famSplice_left, MOcc, spliceAt_of_le _ _ le_rfl,
        spliceAt_of_gt _ _ (by omega : i < i + 1)] at h
      rw [MOcc]
      omega
    · rw [famSplice_right huv, MOcc, spliceAt_of_le _ _ le_rfl,
        spliceAt_of_gt _ _ (by omega : i < i + 1)] at h
      rw [MOcc]
      omega
  · rcases h with ⟨hc, -, -⟩ | ⟨-, hy'⟩
    · omega
    · rw [famSplice_apply_of_le (le_refl i)] at hy'
      exact Or.inr ⟨hib, hy'⟩

/-- Below the selected height nothing moved, so the pairs meeting there are the
same before and after the splice. -/
theorem mem_mMeetSet_famSplice_of_lt {w w' : Fin m} {k : ℕ} (hk : k < i) :
    k ∈ mMeetSet b a (famSplice i (u : ℕ) (v : ℕ) F w) (famSplice i (u : ℕ) (v : ℕ) F w')
      ↔ k ∈ mMeetSet b a (F w) (F w') := by
  rw [mem_mMeetSet, mem_mMeetSet,
    mMeetsAt_congr (famSplice_apply_of_le (u := u) (v := v) (F := F) (w := w) (by omega : k ≤ i))
      (famSplice_apply_of_le (u := u) (v := v) (F := F) (w := w) (by omega : k + 1 ≤ i))
      (famSplice_apply_of_le (u := u) (v := v) (F := F) (w := w') (by omega : k ≤ i))
      (famSplice_apply_of_le (u := u) (v := v) (F := F) (w := w') (by omega : k + 1 ≤ i))]

/-- The family with the tails of the two selected paths exchanged above the
selected height. -/
noncomputable def mLgvFam (b a : ℕ) (F : Fin m → ℕ → ℕ) : Fin m → ℕ → ℕ :=
  famSplice (mFamHeight b a F) (mFamIndex b a F) (mFamPartner b a F) F

/-- **The selection is its own fixed point.**  The four selectors read the same
values off the spliced family as off the original, across both geometries, which
is what makes the swap an involution. -/
theorem select_mLgvFam (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    MIntersects b a (mLgvFam b a F) ∧ mFamHeight b a (mLgvFam b a F) = mFamHeight b a F ∧
      mFamIndex b a (mLgvFam b a F) = mFamIndex b a F ∧
      mFamAbscissa b a (mLgvFam b a F) = mFamAbscissa b a F ∧
      mFamPartner b a (mLgvFam b a F) = mFamPartner b a F := by
  obtain ⟨u, v, hu, hv, huv, hsu, hsv⟩ := select_mSpec hF h
  have hne : u ≠ v := ne_of_lt huv
  have hmeet : MMeetsAt b (F u) (F v) (mFamHeight b a F) := mMeetsAt_of_mOcc hsu hsv
  obtain ⟨hGu, hGv⟩ := mOcc_famSplice_self hne hsu hsv
  have hGdef : mLgvFam b a F = famSplice (mFamHeight b a F) (u : ℕ) (v : ℕ) F := by
    rw [mLgvFam, hu, hv]
  rw [hGdef]
  exact select_eq (sharesAbscissa_mMeetSet b a) hu hv huv
    (monotone_famSplice hF (mMeetsAt_cross (hF v) hmeet)
      (mMeetsAt_cross (hF u) (mMeetsAt_comm hmeet)))
    (fun _ h1 h2 => famSplice_other h1 h2) (fun _ _ _ hk => mem_mMeetSet_famSplice_of_lt hk)
    (fun _ _ hw hs => mOcc_or_of_mOcc_famSplice hne hsu hsv hw hs)
    (fun _ _ hw hy hs => mOcc_of_mOcc_famSplice_lt hne hsu hsv hy hw hs) hGu hGv
    (mem_mMeetSet.mpr ⟨mFamHeight_le_top h, mMeetsAt_of_mOcc hGu hGv⟩)

theorem mLgvFam_mLgvFam (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    mLgvFam b a (mLgvFam b a F) = F := by
  obtain ⟨-, h1, h2, -, h4⟩ := select_mLgvFam hF h
  obtain ⟨u, v, hu, hv, huv, -, -⟩ := select_mSpec hF h
  rw [mLgvFam, h1, h2, h4, mLgvFam, ← hu, ← hv]
  exact famSplice_famSplice (ne_of_lt huv)

end Invariance

/-! ## The signed sum over mixed families

A family is a permutation `σ` together with a mixed path from each source `S w`
to the sink `C (σ w)`, carrying the product of its weights with the sign of `σ`.
The swap is `mLgvFam` on the paths and composition with the transposition of the
two selected indices on `σ`; it is sign-reversing and weight-preserving, so the
sum collapses to the families with no shared lattice point.
-/

section Signed

variable {m : ℕ}

/-- The families of mixed paths from the sources `S` to the sinks `C`, one path
per source, together with the assignment of sinks to sources. -/
noncomputable def mFamFinset (b a : ℕ) {m : ℕ} (S C : Fin m → ℕ) :
    Finset ((_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)) :=
  Finset.univ.sigma fun σ => Fintype.piFinset fun w => mixedPaths b a (S w) (C (σ w))

theorem mem_mFamFinset {b a : ℕ} {S C : Fin m → ℕ}
    {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)} :
    x ∈ mFamFinset b a S C ↔ ∀ w, x.2 w ∈ mixedPaths b a (S w) (C (x.1 w)) := by
  rw [mFamFinset, Finset.mem_sigma, Fintype.mem_piFinset]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem monotone_of_mem_mFamFinset {b a : ℕ} {S C : Fin m → ℕ}
    {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)} (hx : x ∈ mFamFinset b a S C) (w : Fin m) :
    Monotone (x.2 w) :=
  hPaths_mono (mixedPaths_mem (mem_mFamFinset.mp hx w))

variable {R : Type*} [CommRing R]

/-- The signed weight of a mixed family. -/
noncomputable def mFamWeight (b a : ℕ) {m : ℕ} (β α : ℕ → R)
    (x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)) : R :=
  ((Equiv.Perm.sign x.1 : ℤ) : R) * ∏ w, mixedWeight b a β α (x.2 w)

/-- **The swap.**  Exchange the tails of the two selected paths and compose the
sink assignment with the transposition of their indices. -/
noncomputable def mLgvSwap (b a : ℕ) {m : ℕ}
    (x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)) :
    (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ) :=
  ⟨x.1 * natSwap m (mFamIndex b a x.2) (mFamPartner b a x.2), mLgvFam b a x.2⟩

variable {b a : ℕ} {S C : Fin m → ℕ}

/-- The swap of a family is a family: the two spliced paths keep their sources
and exchange their sinks. -/
theorem mLgvSwap_mem {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)}
    (hx : x ∈ mFamFinset b a S C) (h : MIntersects b a x.2) :
    mLgvSwap b a x ∈ mFamFinset b a S C := by
  obtain ⟨u, v, hu, hv, huv, hsu, hsv⟩ := select_mSpec (monotone_of_mem_mFamFinset hx) h
  have hmem := mem_mFamFinset.mp hx
  have hne : u ≠ v := ne_of_lt huv
  have hib : mFamHeight b a x.2 ≤ b + a := mFamHeight_le_top h
  have hmeet : MMeetsAt b (x.2 u) (x.2 v) (mFamHeight b a x.2) := mMeetsAt_of_mOcc hsu hsv
  have hfam : mLgvFam b a x.2 = famSplice (mFamHeight b a x.2) (u : ℕ) (v : ℕ) x.2 := by
    rw [mLgvFam, hu, hv]
  have hns : natSwap m (mFamIndex b a x.2) (mFamPartner b a x.2) = Equiv.swap u v := by
    rw [← hu, ← hv, natSwap_val]
  refine mem_mFamFinset.mpr fun w => ?_
  change mLgvFam b a x.2 w ∈ mixedPaths b a (S w) (C ((x.1 * natSwap m _ _) w))
  rw [hns, hfam, Equiv.Perm.mul_apply]
  by_cases hwu : w = u
  · subst hwu
    rw [famSplice_left, Equiv.swap_apply_left]
    exact mSplice_mem (hmem w) (hmem v) hib hmeet
  · by_cases hwv : w = v
    · subst hwv
      rw [famSplice_right hne, Equiv.swap_apply_right]
      exact mSplice_mem (hmem w) (hmem u) hib (mMeetsAt_comm hmeet)
    · rw [famSplice_other hwu hwv, Equiv.swap_apply_of_ne_of_ne hwu hwv]
      exact hmem w

/-- The swap moves every intersecting family. -/
theorem mLgvSwap_ne {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)}
    (hF : ∀ w, Monotone (x.2 w)) (h : MIntersects b a x.2) : mLgvSwap b a x ≠ x := by
  obtain ⟨u, v, hu, hv, huv, -, -⟩ := select_mSpec hF h
  intro hc
  have h1 : x.1 * natSwap m (mFamIndex b a x.2) (mFamPartner b a x.2) = x.1 :=
    congrArg Sigma.fst hc
  rw [← hu, ← hv, natSwap_val, mul_eq_left] at h1
  have h2 : Equiv.swap u v u = (1 : Equiv.Perm (Fin m)) u := by rw [h1]
  rw [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h2
  exact (ne_of_lt huv) h2.symm

theorem mLgvSwap_mLgvSwap {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)}
    (hF : ∀ w, Monotone (x.2 w)) (h : MIntersects b a x.2) :
    mLgvSwap b a (mLgvSwap b a x) = x := by
  obtain ⟨-, -, h2, -, h4⟩ := select_mLgvFam hF h
  refine Sigma.ext ?_ ?_
  · change x.1 * natSwap m (mFamIndex b a x.2) (mFamPartner b a x.2) *
      natSwap m (mFamIndex b a (mLgvFam b a x.2)) (mFamPartner b a (mLgvFam b a x.2)) = x.1
    rw [h2, h4, mul_assoc, natSwap_mul_self, mul_one]
  · exact heq_of_eq (mLgvFam_mLgvFam hF h)

/-- **The swap preserves the total weight.**  Read as a single alphabet of
`b + a` letters the mixed weight is an ordinary path weight, and at the splice
the two step counts are exchanged. -/
theorem prod_mixedWeight_mLgvFam (β α : ℕ → R)
    {x : (_ : Equiv.Perm (Fin m)) × (Fin m → ℕ → ℕ)} (hx : x ∈ mFamFinset b a S C)
    (h : MIntersects b a x.2) :
    ∏ w, mixedWeight b a β α (mLgvFam b a x.2 w) = ∏ w, mixedWeight b a β α (x.2 w) := by
  obtain ⟨u, v, hu, hv, huv, hsu, hsv⟩ := select_mSpec (monotone_of_mem_mFamFinset hx) h
  have hmem := mem_mFamFinset.mp hx
  have hne : u ≠ v := ne_of_lt huv
  have hmeet : MMeetsAt b (x.2 u) (x.2 v) (mFamHeight b a x.2) := mMeetsAt_of_mOcc hsu hsv
  have hfam : mLgvFam b a x.2 = famSplice (mFamHeight b a x.2) (u : ℕ) (v : ℕ) x.2 := by
    rw [mLgvFam, hu, hv]
  have hsplit : ∀ g : Fin m → R,
      ∏ w, g w = (∏ w ∈ Finset.univ \ {u, v}, g w) * (g u * g v) := by
    intro g
    rw [← Finset.prod_pair hne, Finset.prod_sdiff (Finset.subset_univ _)]
  simp only [mixedWeight_eq_pathWeight]
  rw [hsplit (fun w => pathWeight (b + a) (mixedVar b β α) (mLgvFam b a x.2 w)),
    hsplit (fun w => pathWeight (b + a) (mixedVar b β α) (x.2 w)), hfam]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w hw => ?_) ?_
  · rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    rw [famSplice_other hw.2.1 hw.2.2]
  · rw [famSplice_left, famSplice_right hne]
    exact pathWeight_spliceAt_mul (mixedPaths_mem (hmem u)) (mixedPaths_mem (hmem v))
      ⟨mMeetsAt_cross (monotone_of_mem_mFamFinset hx v) hmeet,
       mMeetsAt_cross (monotone_of_mem_mFamFinset hx u) (mMeetsAt_comm hmeet)⟩ _

/-- **The cancellation for the mixed crossing predicate.**  The signed sum over
all mixed families is the signed sum over the families whose paths share no
lattice point — for any endpoints and any number of paths, with the even and the
odd geometry both present.  This is `sum_famWeight_eq_sum_nonIntersecting`
across the two. -/
theorem sum_mFamWeight_eq_sum_nonIntersecting (b a : ℕ) {m : ℕ} (β α : ℕ → R)
    (S C : Fin m → ℕ) :
    ∑ x ∈ mFamFinset b a S C, mFamWeight b a β α x
      = ∑ x ∈ (mFamFinset b a S C).filter fun x => ¬ MIntersects b a x.2,
          mFamWeight b a β α x := by
  refine sum_eq_sum_filter_of_signReversing _ _ _ (mLgvSwap b a) (fun x hx hP => ?_)
    (fun x hx hP => ?_) (fun x hx hP => ?_) (fun x hx hP => ?_) (fun x hx hP => ?_)
  · exact mLgvSwap_mem hx (not_not.mp hP)
  · exact fun hc => hc (select_mLgvFam (monotone_of_mem_mFamFinset hx) (not_not.mp hP)).1
  · exact mLgvSwap_ne (monotone_of_mem_mFamFinset hx) (not_not.mp hP)
  · exact mLgvSwap_mLgvSwap (monotone_of_mem_mFamFinset hx) (not_not.mp hP)
  · have h := not_not.mp hP
    obtain ⟨u, v, hu, hv, huv, -, -⟩ := select_mSpec (monotone_of_mem_mFamFinset hx) h
    have hns : natSwap m (mFamIndex b a x.2) (mFamPartner b a x.2) = Equiv.swap u v := by
      rw [← hu, ← hv, natSwap_val]
    change ((Equiv.Perm.sign x.1 : ℤ) : R) * _ +
      ((Equiv.Perm.sign (x.1 * natSwap m _ _) : ℤ) : R) * _ = 0
    rw [hns, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (ne_of_lt huv)]
    change ((Equiv.Perm.sign x.1 : ℤ) : R) * ∏ w, mixedWeight b a β α (x.2 w) +
      (((Equiv.Perm.sign x.1 * -1 : ℤˣ) : ℤ) : R) *
        ∏ w, mixedWeight b a β α (mLgvFam b a x.2 w) = 0
    rw [prod_mixedWeight_mLgvFam β α hx h]
    push_cast
    ring

end Signed

/-! ## The determinant

With the endpoints the skew Jacobi--Trudi identity prescribes, an intersecting family is
forced whenever the sink assignment is not the identity, so the `m × m`
determinant over the mixed alphabet `ρ_D` is the total weight of the
non-intersecting families.
-/

section Determinant

variable {R : Type*} [CommRing R] {b a m : ℕ}

theorem mixedPaths_eq_empty_of_lt {s e : ℕ} (h : e < s) : mixedPaths b a s e = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun q hq => ?_
  exact absurd (hPaths_eq_empty_of_lt (b := b + a) h ▸ mixedPaths_mem hq)
    (Finset.notMem_empty q)

/-- The total weight of the mixed paths from `s` to `e`: the entry of the
Jacobi--Trudi matrix over the alphabet `ρ_D`. -/
noncomputable def mEdgeSum (b a : ℕ) (β α : ℕ → R) (s e : ℕ) : R :=
  ∑ q ∈ mixedPaths b a s e, mixedWeight b a β α q

theorem mEdgeSum_eq_jtCoeff (b a : ℕ) (β α : ℕ → R) (s e : ℕ) :
    mEdgeSum b a β α s e = jtCoeff (fun k => superHom b a k β α) e s := by
  rw [jtCoeff]
  rcases le_or_gt s e with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, e = s + k := ⟨e - s, by omega⟩
    rw [if_pos h, mEdgeSum, mixedPaths_sum_eq_superHom, Nat.add_sub_cancel_left]
  · rw [if_neg (by omega), mEdgeSum, mixedPaths_eq_empty_of_lt h, Finset.sum_empty]

/-- **The determinant as a signed sum over mixed families.**  The Leibniz
expansion of the `m × m` Jacobi--Trudi matrix over `ρ_D` is the signed weight of
the families of mixed paths, indexed by source. -/
theorem mixedJacobiTrudiDet_eq_sum_mFamFinset (β α : ℕ → R) (lam mu : YoungDiagram) :
    jacobiTrudiDet (fun k => superHom b a k β α) lam mu m
      = ∑ x ∈ mFamFinset b a (jtSource mu m) (jtSink lam m), mFamWeight b a β α x := by
  rw [jacobiTrudiDet, Matrix.det_apply', mFamFinset, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  change _ = ∑ F ∈ Fintype.piFinset _,
    ((Equiv.Perm.sign σ : ℤ) : R) * ∏ w, mixedWeight b a β α (F w)
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
    ← mEdgeSum_eq_jtCoeff, mEdgeSum]

/-- **Non-intersecting forces the identity assignment.**  With strictly
decreasing sources and sinks, a family whose sink assignment inverts two indices
has a path that starts to the right of another and finishes to its left, and two
such mixed paths share a lattice point. -/
theorem perm_eq_one_of_not_mIntersects {S C : Fin m → ℕ} {σ : Equiv.Perm (Fin m)}
    {F : Fin m → ℕ → ℕ} (hS : StrictAnti S) (hC : StrictAnti C)
    (hmem : ∀ w, F w ∈ mixedPaths b a (S w) (C (σ w))) (h : ¬ MIntersects b a F) : σ = 1 := by
  by_contra hne
  obtain ⟨u, v, huv, hσ⟩ : ∃ u v : Fin m, u < v ∧ σ v < σ u := by
    by_contra hcon
    refine hne (perm_eq_one_of_strictMono fun c d hcd => ?_)
    rcases lt_trichotomy (σ c) (σ d) with hlt | heq | hgt
    · exact hlt
    · exact absurd (σ.injective heq) (ne_of_lt hcd)
    · exact absurd ⟨c, d, hcd, hgt⟩ hcon
  exact h ⟨u, v, huv, mMeets_of_lt (hmem u) (hmem v) (hS huv) (hC hσ)⟩

/-- **Skew Jacobi--Trudi in the mixed path model at `m` rows.**  The `m × m`
determinant `det [d_{λ_u - μ_v - u + v}]` over the alphabet `ρ_D` is the total
weight of the families of `m` mixed paths, from the sources of `μ` to the sinks
of `λ` in order, no two of which share a lattice point. -/
theorem mixedJacobiTrudiDet_eq_sum_nonIntersecting (β α : ℕ → R) (lam mu : YoungDiagram) :
    jacobiTrudiDet (fun k => superHom b a k β α) lam mu m
      = ∑ F ∈ (Fintype.piFinset fun w : Fin m =>
            mixedPaths b a (jtSource mu m w) (jtSink lam m w)).filter
              fun F => ¬ MIntersects b a F,
          ∏ w, mixedWeight b a β α (F w) := by
  rw [mixedJacobiTrudiDet_eq_sum_mFamFinset, sum_mFamWeight_eq_sum_nonIntersecting]
  refine Finset.sum_nbij' (fun x => x.2) (fun F => ⟨1, F⟩) (fun x hx => ?_) (fun F hF => ?_)
    (fun x hx => ?_) (fun F hF => ?_) (fun x hx => ?_)
  · rw [Finset.mem_filter, mem_mFamFinset] at hx
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun w => ?_, hx.2⟩
    have h1 : x.1 = 1 := perm_eq_one_of_not_mIntersects (strictAnti_jtSource mu m)
      (strictAnti_jtSink lam m) hx.1 hx.2
    have := hx.1 w
    rwa [h1, Equiv.Perm.one_apply] at this
  · rw [Finset.mem_filter, Fintype.mem_piFinset] at hF
    rw [Finset.mem_filter, mem_mFamFinset]
    exact ⟨fun w => hF.1 w, hF.2⟩
  · rw [Finset.mem_filter, mem_mFamFinset] at hx
    have h1 : x.1 = 1 := perm_eq_one_of_not_mIntersects (strictAnti_jtSource mu m)
      (strictAnti_jtSink lam m) hx.1 hx.2
    exact Sigma.ext h1.symm (heq_of_eq rfl)
  · rfl
  · rw [Finset.mem_filter, mem_mFamFinset] at hx
    have h1 : x.1 = 1 := perm_eq_one_of_not_mIntersects (strictAnti_jtSource mu m)
      (strictAnti_jtSink lam m) hx.1 hx.2
    rw [mFamWeight, h1]
    simp

end Determinant

/-! ## What `SkewJacobiTrudi` still needs

The cancellation holds at every `m`; the residue is the tableau side.  It is
stated here as a predicate so that it sits in the type of anything that consumes
it, proved here at `m ≤ 1`, and carried as a hypothesis beyond.  At two rows it is a
theorem as well, in `Shields.Combinatorics.Young.LGVOddTableauTwo`, which is where the
two-column bijection it consumes is proved.
-/

section Residue

variable {R : Type*} [CommRing R]

/-- **The residue at `m` rows.**  That the non-intersecting families of `m`
mixed paths carry the branching sum of the super branching rule.

At `a = 0` this is `sum_nonIntersecting_eq_skewSchur`, and at two
rows it is `sum_nonMeeting_mixed_eq_superSkewSchur_uncond`.
`sum_nonIntersecting_mixed_eq_superSkewSchur` fibers the families over their
abscissae at height `b` -- the splice at `m` paths and the dictionary carrying those abscissae
to the intermediate shapes `μ ⊆ ν ⊆ λ` are there -- and asks in return for the two tableau
bijections at `m`; the odd one, `sum_nonEIntersecting_eq_skewSchurTranspose`, is
what stands between them. -/
def NonIntersectingIsSuperSkewSchur (b a m : ℕ) (β α : ℕ → R) : Prop :=
  ∀ lam mu : YoungDiagram, mu ≤ lam → (∀ i, m ≤ i → lam.rowLen i = 0) →
    ∑ F ∈ (Fintype.piFinset fun w : Fin m =>
          mixedPaths b a (jtSource mu m w) (jtSink lam m w)).filter
            fun F => ¬ MIntersects b a F,
        ∏ w, mixedWeight b a β α (F w)
      = superSkewSchur lam mu b a β α

/-- The residue at one row or none is a theorem: the determinant is already
the super branching rule there. -/
theorem nonIntersectingIsSuperSkewSchur_of_le_one {b a m : ℕ} (β α : ℕ → R) (hm : m ≤ 1) :
    NonIntersectingIsSuperSkewSchur b a m β α := by
  intro lam mu hmu hrow
  rw [← mixedJacobiTrudiDet_eq_sum_nonIntersecting]
  exact jacobiTrudiDet_eq_superSkewSchur_of_le_one (fun _ => rfl) hm hmu hrow

/-- **`JacobiTrudi.SkewJacobiTrudi` from the residue.**  The cancellation is
supplied; what the identity still asks for is the tableau side at every `m`. -/
theorem skewJacobiTrudi_of_nonIntersecting {b a : ℕ} {β α : ℕ → R}
    (h : ∀ m, NonIntersectingIsSuperSkewSchur b a m β α) :
    SkewJacobiTrudi (fun k => superHom b a k β α) b a β α := by
  intro lam mu m hmu hrow
  rw [mixedJacobiTrudiDet_eq_sum_nonIntersecting]
  exact h m lam mu hmu hrow

end Residue

/-! ## Non-vacuity

The odd half of the predicate decides configurations the even half does not see,
so the selection genuinely has to range over both geometries.
-/

section Instance

/-- The mixed path from `0` to `1` that waits at the even height and steps at
the odd one. -/
def lowPath : ℕ → ℕ := fun k => if k ≤ 1 then 0 else 1

theorem lowPath_mem : lowPath ∈ mixedPaths 1 1 0 1 := by
  have hval : ∀ k, lowPath k = if k ≤ 1 then 0 else 1 := fun _ => rfl
  refine mem_mixedPaths.mpr ⟨mem_hPaths.mpr ⟨rfl, fun k₁ k₂ h => ?_, fun k hk => ?_⟩,
    fun i h1 h2 => ?_⟩
  · rw [hval, hval]
    split_ifs <;> omega
  · rw [hval, if_neg (by omega)]
  · have hi : i = 1 := by omega
    subst hi
    change lowPath 2 ≤ lowPath 1 + 1
    decide

theorem constPath_mem : (fun _ => 1) ∈ mixedPaths 1 1 1 1 :=
  mem_mixedPaths.mpr ⟨mem_hPaths.mpr ⟨rfl, fun _ _ _ => le_rfl, fun _ _ => rfl⟩,
    fun _ _ _ => by omega⟩

/-- **The point condition decides.**  These two mixed paths sweep disjoint
intervals at the one even height, so the even predicate calls them
non-intersecting; they occupy the same point at the top odd height, so the mixed
predicate does not.  This is the configuration the selection has to reach past
the even geometry to see. -/
theorem mMeets_lowPath : ¬ Crosses 1 lowPath (fun _ => 1) ∧ MMeets 1 1 lowPath fun _ => 1 := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨h1, h2, h3⟩ := mem_crossSet.mp hi
    have hi0 : i = 0 := by omega
    rw [hi0, lowPath] at h3
    norm_num at h3
  · exact ⟨2, mem_mMeetSet.mpr ⟨by omega, Or.inr ⟨by omega, by rw [lowPath]; norm_num⟩⟩⟩

end Instance

/-! ## Axiom-footprint guards -/

section AxiomGuards

end AxiomGuards


/-! ### Axiom footprint -/

/-- info: 'Shields.mixedJacobiTrudiDet_eq_sum_nonIntersecting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixedJacobiTrudiDet_eq_sum_nonIntersecting

end Shields
