/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.LGVInvolution
import Shields.Combinatorics.Young.LGVOddTableauTwo

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
  readings of the predicate agree.  Height `b` belongs to the odd half in both.
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
* `Shields.skewJacobiTrudi_two_rows` -- at two rows everything else is a theorem, so for `λ`
  inside two rows, `det [d_{λ_u - μ_v - u + v}]_{2 × 2} = s_{λ/μ}(β | α)` over any commutative
  ring, every `b`, `a`, `β`, `α` and every `μ ⊆ λ`, with nothing assumed.

## Implementation notes

Indexing is by **source**: re-indexing by sink breaks involutivity, and the abscissa selector is
what makes the argument close at arbitrary endpoints.

Beyond two rows the residue is no longer the cancellation but the tableau side,
`Shields.NonIntersectingIsSuperSkewSchur` -- that the non-intersecting mixed families of `m` paths
carry the branching sum.  It is proved here at `m ≤ 2` and carried as a hypothesis of
`Shields.skewJacobiTrudi_of_nonIntersecting` beyond that;
`Shields.Combinatorics.Young.LGVOddTableau` discharges it at every `m`.

## Tags

Lindström-Gessel-Viennot, sign-reversing involution, non-intersecting paths, Jacobi-Trudi, super
Schur function
-/

namespace Shields

open Finset

/-! ## One occupancy for the two geometries

A mixed path occupies an interval at an even height and a point at an odd one.
`MOcc` is that set of abscissae and `MMeetsAt` is two paths sharing one of them;
the two disjuncts are cut apart by the height alone, so no configuration is
counted twice and height `b` is odd.
-/

section Geometry

/-- The abscissae the mixed path `q` occupies at height `i`: the interval it
sweeps, `[q i, q (i+1)]`, below height `b`, and the single point `q i` from
height `b` on. -/
def MOcc (b : ℕ) (q : ℕ → ℕ) (i x : ℕ) : Prop :=
  (i < b ∧ q i ≤ x ∧ x ≤ q (i + 1)) ∨ (b ≤ i ∧ x = q i)

/-- Two mixed paths share a lattice point at height `i`: their swept intervals
meet below height `b`, their points coincide from height `b` on. -/
def MMeetsAt (b : ℕ) (q r : ℕ → ℕ) (i : ℕ) : Prop :=
  (i < b ∧ q i ≤ r (i + 1) ∧ r i ≤ q (i + 1)) ∨ (b ≤ i ∧ q i = r i)

instance (b : ℕ) (q r : ℕ → ℕ) (i : ℕ) : Decidable (MMeetsAt b q r i) := by
  unfold MMeetsAt; infer_instance

variable {b : ℕ} {q r : ℕ → ℕ} {i x : ℕ}

theorem mMeetsAt_comm (h : MMeetsAt b q r i) : MMeetsAt b r q i := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h3, h2⟩
  · exact Or.inr ⟨h1, h2.symm⟩

/-- A meeting joins the two profiles: the splice at a meeting height is
monotone because of this. -/
theorem mMeetsAt_cross (hr : Monotone r) (h : MMeetsAt b q r i) : q i ≤ r (i + 1) := by
  rcases h with ⟨-, h2, -⟩ | ⟨-, h2⟩
  · exact h2
  · rw [h2]; exact hr (by omega)

/-- Two paths meeting at a height share an abscissa there. -/
theorem mOcc_of_mMeetsAt (hq : Monotone q) (hr : Monotone r) (h : MMeetsAt b q r i) :
    MOcc b q i (max (q i) (r i)) ∧ MOcc b r i (max (q i) (r i)) := by
  have hq' := hq (show i ≤ i + 1 by omega)
  have hr' := hr (show i ≤ i + 1 by omega)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact ⟨Or.inl ⟨h1, le_max_left _ _, by omega⟩, Or.inl ⟨h1, le_max_right _ _, by omega⟩⟩
  · exact ⟨Or.inr ⟨h1, by omega⟩, Or.inr ⟨h1, by omega⟩⟩

/-- Two paths sharing an abscissa at a height meet there. -/
theorem mMeetsAt_of_mOcc (h1 : MOcc b q i x) (h2 : MOcc b r i x) : MMeetsAt b q r i := by
  rcases h1 with ⟨ha, hb1, hb2⟩ | ⟨ha, hb1⟩ <;> rcases h2 with ⟨hc, hd1, hd2⟩ | ⟨hc, hd1⟩
  · exact Or.inl ⟨ha, by omega, by omega⟩
  · omega
  · omega
  · exact Or.inr ⟨ha, by omega⟩

/-- The meeting condition reads only the two profiles at the height and the one
above it. -/
theorem mMeetsAt_congr {q' r' : ℕ → ℕ} (h1 : q i = q' i) (h2 : q (i + 1) = q' (i + 1))
    (h3 : r i = r' i) (h4 : r (i + 1) = r' (i + 1)) :
    MMeetsAt b q r i ↔ MMeetsAt b q' r' i := by
  rw [MMeetsAt, MMeetsAt, h1, h2, h3, h4]

/-- The heights at which the two mixed paths share a lattice point. -/
def mMeetSet (b a : ℕ) (q r : ℕ → ℕ) : Finset ℕ :=
  (Finset.range (b + a + 1)).filter fun i => MMeetsAt b q r i

/-- Two mixed paths intersect: they share a lattice point at some height. -/
def MMeets (b a : ℕ) (q r : ℕ → ℕ) : Prop := (mMeetSet b a q r).Nonempty

instance (b a : ℕ) (q r : ℕ → ℕ) : Decidable (MMeets b a q r) :=
  inferInstanceAs (Decidable (mMeetSet b a q r).Nonempty)

variable {a : ℕ}

theorem mem_mMeetSet : i ∈ mMeetSet b a q r ↔ i ≤ b + a ∧ MMeetsAt b q r i := by
  rw [mMeetSet, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- **The two readings of the predicate agree.**  Sharing a point at some height
`≤ b + a` is `LGVOdd.MixedMeets`: interval disjointness below height `b`, point
disjointness from height `b` on. -/
theorem mMeets_iff_mixedMeets (b a : ℕ) (q r : ℕ → ℕ) :
    MMeets b a q r ↔ MixedMeets b a q r := by
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_mMeetSet] at hi
    obtain ⟨hib, hmeet⟩ := hi
    rcases hmeet with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨i, mem_crossSet.mpr ⟨h1, h2, h3⟩⟩
    · refine Or.inr ⟨i - b, mem_eMeetSet.mpr ⟨by omega, ?_⟩⟩
      change q (b + (i - b)) = r (b + (i - b))
      rw [show b + (i - b) = i by omega]
      exact h2
  · rintro (⟨i, hi⟩ | ⟨k, hk⟩)
    · obtain ⟨h1, h2, h3⟩ := mem_crossSet.mp hi
      exact ⟨i, mem_mMeetSet.mpr ⟨by omega, Or.inl ⟨h1, h2, h3⟩⟩⟩
    · obtain ⟨h1, h2⟩ := mem_eMeetSet.mp hk
      exact ⟨b + k, mem_mMeetSet.mpr ⟨by omega, Or.inr ⟨by omega, h2⟩⟩⟩

/-- **The transposed term is entirely meeting.**  Two mixed paths whose sources
and sinks are oppositely ordered share a lattice point.  The difference of the
profiles starts positive and ends negative; where it changes sign, an even
height gives meeting intervals outright, and an odd height cannot change it
without an equality, because both steps are units. -/
theorem mMeets_of_lt {b a s₁ e₁ s₂ e₂ : ℕ} {q r : ℕ → ℕ} (hq : q ∈ mixedPaths b a s₁ e₁)
    (hr : r ∈ mixedPaths b a s₂ e₂) (hs : s₂ < s₁) (he : e₁ < e₂) : MMeets b a q r := by
  obtain ⟨hq', hqs⟩ := mem_mixedPaths.mp hq
  obtain ⟨hr', hrs⟩ := mem_mixedPaths.mp hr
  have hex : ∃ k, q k ≤ r k := by
    refine ⟨b + a, ?_⟩
    rw [hPaths_top hq' le_rfl, hPaths_top hr' le_rfl]
    omega
  have hspec : q (Nat.find hex) ≤ r (Nat.find hex) := Nat.find_spec hex
  have hktop : Nat.find hex ≤ b + a := by
    refine Nat.find_le ?_
    rw [hPaths_top hq' le_rfl, hPaths_top hr' le_rfl]
    omega
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, hPaths_zero hq', hPaths_zero hr'] at hspec
    omega
  set j := Nat.find hex - 1 with hj
  have hsucc : j + 1 = Nat.find hex := by omega
  have hmin : ¬ q j ≤ r j := Nat.find_min hex (by omega)
  have hle : q (j + 1) ≤ r (j + 1) := by rw [hsucc]; exact hspec
  rcases lt_or_ge j b with hjb | hjb
  · refine ⟨j, mem_mMeetSet.mpr ⟨by omega, Or.inl ⟨hjb, ?_, ?_⟩⟩⟩
    · exact le_trans (hPaths_mono hq' (by omega : j ≤ j + 1)) hle
    · exact le_trans (by omega) (hPaths_mono hq' (by omega : j ≤ j + 1))
  · have hstep := hrs j hjb (by omega)
    have hmono := hPaths_mono hq' (by omega : j ≤ j + 1)
    exact ⟨j + 1, mem_mMeetSet.mpr ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩⟩

end Geometry

/-! ## The splice, in both geometries at once

`LGV.spliceAt` cuts above the index and `LGVOdd.eSpliceAt` at it; at a meeting
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
  · intro k₁ k₂ h
    rcases le_or_gt k₂ i with h₂ | h₂
    · rw [spliceAt_of_le _ _ (by omega), spliceAt_of_le _ _ h₂]
      exact hPaths_mono hq' h
    · rcases le_or_gt k₁ i with h₁ | h₁
      · rw [spliceAt_of_le _ _ h₁, spliceAt_of_gt _ _ h₂]
        exact le_trans (le_trans (hPaths_mono hq' h₁) hjoin) (hPaths_mono hr' (by omega))
      · rw [spliceAt_of_gt _ _ h₁, spliceAt_of_gt _ _ h₂]
        exact hPaths_mono hr' h
  · intro k hk
    rcases lt_or_ge i k with hik | hik
    · rw [spliceAt_of_gt _ _ hik]
      exact hPaths_top hr' hk
    · have hki : k = i := by omega
      have hib : b ≤ i := by omega
      have heq : q i = r i := by
        rcases hm with ⟨h1, -, -⟩ | ⟨-, h2⟩
        · omega
        · exact h2
      rw [hki, spliceAt_of_le _ _ le_rfl, heq]
      exact hPaths_top hr' (by omega)
  · intro k hkb hka
    rcases le_or_gt (k + 1) i with h₁ | h₁
    · rw [spliceAt_of_le _ _ h₁, spliceAt_of_le _ _ (by omega : k ≤ i)]
      exact mixedPaths_step hq hkb hka
    · rcases lt_or_ge i k with h₂ | h₂
      · rw [spliceAt_of_gt _ _ (by omega : i < k + 1), spliceAt_of_gt _ _ h₂]
        exact mixedPaths_step hr hkb hka
      · have hki : k = i := by omega
        have heq : q i = r i := by
          rcases hm with ⟨h3, -, -⟩ | ⟨-, h4⟩
          · omega
          · exact h4
        rw [spliceAt_of_gt _ _ (by omega : i < k + 1), spliceAt_of_le _ _ (by omega : k ≤ i),
          hki, heq]
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

/-- Two paths of the family share a lattice point. -/
def MIntersects (b a : ℕ) (F : Fin m → ℕ → ℕ) : Prop :=
  ∃ u v : Fin m, u < v ∧ MMeets b a (F u) (F v)

instance (b a : ℕ) (F : Fin m → ℕ → ℕ) : Decidable (MIntersects b a F) := by
  unfold MIntersects; infer_instance

/-- The heights at which some pair of the family shares a lattice point. -/
def mCrossHeights (b a : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {i | ∃ u v : Fin m, u < v ∧ i ∈ mMeetSet b a (F u) (F v)}

/-- The least height at which two paths of the family meet. -/
noncomputable def mFamHeight (b a : ℕ) (F : Fin m → ℕ → ℕ) : ℕ := sInf (mCrossHeights b a F)

/-- The paths that meet a later path at the least crossing height. -/
def mCrossIndices (b a : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {n | ∃ u : Fin m, (u : ℕ) = n ∧ ∃ v : Fin m, u < v ∧
    ∃ x, MOcc b (F u) (mFamHeight b a F) x ∧ MOcc b (F v) (mFamHeight b a F) x}

/-- The least path index meeting a later path at the least crossing height. -/
noncomputable def mFamIndex (b a : ℕ) (F : Fin m → ℕ → ℕ) : ℕ := sInf (mCrossIndices b a F)

/-- The abscissae the selected path shares with a later one at the selected
height. -/
def mCrossAbscissae (b a : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {x | ∃ u : Fin m, (u : ℕ) = mFamIndex b a F ∧ MOcc b (F u) (mFamHeight b a F) x ∧
    ∃ v : Fin m, u < v ∧ MOcc b (F v) (mFamHeight b a F) x}

/-- The least such abscissa. -/
noncomputable def mFamAbscissa (b a : ℕ) (F : Fin m → ℕ → ℕ) : ℕ := sInf (mCrossAbscissae b a F)

/-- The later paths through the selected lattice point. -/
def mCrossPartners (b a : ℕ) (F : Fin m → ℕ → ℕ) : Set ℕ :=
  {n | ∃ v : Fin m, (v : ℕ) = n ∧ mFamIndex b a F < n ∧
    MOcc b (F v) (mFamHeight b a F) (mFamAbscissa b a F)}

/-- The least such later path. -/
noncomputable def mFamPartner (b a : ℕ) (F : Fin m → ℕ → ℕ) : ℕ := sInf (mCrossPartners b a F)

variable {b a : ℕ} {F : Fin m → ℕ → ℕ}

theorem mCrossHeights_nonempty (h : MIntersects b a F) : (mCrossHeights b a F).Nonempty := by
  obtain ⟨u, v, huv, i, hi⟩ := h
  exact ⟨i, u, v, huv, hi⟩

theorem mFamHeight_mem (h : MIntersects b a F) : mFamHeight b a F ∈ mCrossHeights b a F :=
  Nat.sInf_mem (mCrossHeights_nonempty h)

theorem mFamHeight_le {i : ℕ} (hi : i ∈ mCrossHeights b a F) : mFamHeight b a F ≤ i :=
  Nat.sInf_le hi

theorem mFamHeight_le_top (h : MIntersects b a F) : mFamHeight b a F ≤ b + a := by
  obtain ⟨u, v, -, hmem⟩ := mFamHeight_mem h
  exact (mem_mMeetSet.mp hmem).1

theorem mCrossIndices_nonempty (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    (mCrossIndices b a F).Nonempty := by
  obtain ⟨u, v, huv, hmem⟩ := mFamHeight_mem h
  obtain ⟨h1, h2⟩ := mOcc_of_mMeetsAt (hF u) (hF v) (mem_mMeetSet.mp hmem).2
  exact ⟨u, u, rfl, v, huv, _, h1, h2⟩

theorem mFamIndex_mem (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    mFamIndex b a F ∈ mCrossIndices b a F :=
  Nat.sInf_mem (mCrossIndices_nonempty hF h)

theorem mFamIndex_le {n : ℕ} (hn : n ∈ mCrossIndices b a F) : mFamIndex b a F ≤ n := Nat.sInf_le hn

theorem mCrossAbscissae_nonempty (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    (mCrossAbscissae b a F).Nonempty := by
  obtain ⟨u, hu, v, huv, x, h1, h2⟩ := mFamIndex_mem hF h
  exact ⟨x, u, hu, h1, v, huv, h2⟩

theorem mFamAbscissa_mem (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    mFamAbscissa b a F ∈ mCrossAbscissae b a F :=
  Nat.sInf_mem (mCrossAbscissae_nonempty hF h)

theorem mFamAbscissa_le {x : ℕ} (hx : x ∈ mCrossAbscissae b a F) : mFamAbscissa b a F ≤ x :=
  Nat.sInf_le hx

theorem mCrossPartners_nonempty (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    (mCrossPartners b a F).Nonempty := by
  obtain ⟨u, hu, h1, v, huv, h2⟩ := mFamAbscissa_mem hF h
  refine ⟨v, v, rfl, ?_, h2⟩
  rw [← hu]
  exact huv

theorem mFamPartner_mem (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    mFamPartner b a F ∈ mCrossPartners b a F :=
  Nat.sInf_mem (mCrossPartners_nonempty hF h)

theorem mFamPartner_le {n : ℕ} (hn : n ∈ mCrossPartners b a F) : mFamPartner b a F ≤ n :=
  Nat.sInf_le hn

/-- **The selected lattice point.**  The two selected paths, the selected height
and the selected abscissa, packaged as the swap consumes them. -/
theorem select_mSpec (hF : ∀ w, Monotone (F w)) (h : MIntersects b a F) :
    ∃ u v : Fin m, (u : ℕ) = mFamIndex b a F ∧ (v : ℕ) = mFamPartner b a F ∧ u < v ∧
      MOcc b (F u) (mFamHeight b a F) (mFamAbscissa b a F) ∧
      MOcc b (F v) (mFamHeight b a F) (mFamAbscissa b a F) := by
  obtain ⟨u, hu, hsu, -⟩ := mFamAbscissa_mem hF h
  obtain ⟨v, hv, hlt, hsv⟩ := mFamPartner_mem hF h
  refine ⟨u, v, hu, hv, ?_, hsu, hsv⟩
  rw [Fin.lt_def, hu, hv]
  exact hlt

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
  have hib : mFamHeight b a F ≤ b + a := mFamHeight_le_top h
  have hmeet : MMeetsAt b (F u) (F v) (mFamHeight b a F) := mMeetsAt_of_mOcc hsu hsv
  have hGdef : mLgvFam b a F = famSplice (mFamHeight b a F) (u : ℕ) (v : ℕ) F := by
    rw [mLgvFam, hu, hv]
  rw [hGdef]
  set G := famSplice (mFamHeight b a F) (u : ℕ) (v : ℕ) F with hG
  have hGother : ∀ w : Fin m, w ≠ u → w ≠ v → G w = F w := by
    intro w h1 h2; rw [hG, famSplice_other h1 h2]
  have hGlow : ∀ (w w' : Fin m) (k : ℕ), k < mFamHeight b a F →
      (k ∈ mMeetSet b a (G w) (G w') ↔ k ∈ mMeetSet b a (F w) (F w')) := by
    intro w w' k hk; rw [hG, mem_mMeetSet_famSplice_of_lt hk]
  have hGor : ∀ (w : Fin m) (y : ℕ), (w = u ∨ w = v) →
      MOcc b (G w) (mFamHeight b a F) y →
      (MOcc b (F u) (mFamHeight b a F) y ∨ MOcc b (F v) (mFamHeight b a F) y) := by
    intro w y hw hs
    rw [hG] at hs
    exact mOcc_or_of_mOcc_famSplice hne hsu hsv hw hs
  have hGdown : ∀ (w : Fin m) (y : ℕ), (w = u ∨ w = v) → y < mFamAbscissa b a F →
      MOcc b (G w) (mFamHeight b a F) y → MOcc b (F w) (mFamHeight b a F) y := by
    intro w y hw hy hs
    rw [hG] at hs
    exact mOcc_of_mOcc_famSplice_lt hne hsu hsv hy hw hs
  have hGmono : ∀ w, Monotone (G w) := by
    rw [hG]
    exact monotone_famSplice hF (mMeetsAt_cross (hF v) hmeet)
      (mMeetsAt_cross (hF u) (mMeetsAt_comm hmeet))
  have hGu : MOcc b (G u) (mFamHeight b a F) (mFamAbscissa b a F) := by
    rw [hG]; exact (mOcc_famSplice_self hne hsu hsv).1
  have hGv : MOcc b (G v) (mFamHeight b a F) (mFamAbscissa b a F) := by
    rw [hG]; exact (mOcc_famSplice_self hne hsu hsv).2
  clear_value G
  clear hG hGdef
  have hGmeet : mFamHeight b a F ∈ mMeetSet b a (G u) (G v) :=
    mem_mMeetSet.mpr ⟨hib, mMeetsAt_of_mOcc hGu hGv⟩
  have hGint : MIntersects b a G := ⟨u, v, huv, _, hGmeet⟩
  -- (1) the height
  have h1 : mFamHeight b a G = mFamHeight b a F := by
    refine le_antisymm (mFamHeight_le ⟨u, v, huv, hGmeet⟩) ?_
    by_contra hcon
    obtain ⟨w, w', hww', hmem⟩ := mFamHeight_mem hGint
    rw [hGlow w w' _ (by omega)] at hmem
    have := mFamHeight_le (b := b) (a := a) (F := F) ⟨w, w', hww', hmem⟩
    omega
  -- (2) the path index
  have h2 : mFamIndex b a G = (u : ℕ) := by
    refine le_antisymm (mFamIndex_le ⟨u, rfl, v, huv, mFamAbscissa b a F, by rw [h1]; exact hGu,
      by rw [h1]; exact hGv⟩) ?_
    obtain ⟨w, hw, w', hww', y, hy1, hy2⟩ := mFamIndex_mem hGmono hGint
    rw [h1] at hy1 hy2
    by_contra hcon
    have hwu : w < u := by rw [Fin.lt_def, hw]; omega
    have hFw : MOcc b (F w) (mFamHeight b a F) y := by
      rwa [hGother w (ne_of_lt hwu) (ne_of_lt (lt_trans hwu huv))] at hy1
    have hpair : ∃ w'' : Fin m, w < w'' ∧ MOcc b (F w'') (mFamHeight b a F) y := by
      by_cases hc : w' = u ∨ w' = v
      · rcases hGor w' y hc hy2 with hs | hs
        · exact ⟨u, hwu, hs⟩
        · exact ⟨v, lt_trans hwu huv, hs⟩
      · rw [not_or] at hc
        exact ⟨w', hww', by rwa [hGother w' hc.1 hc.2] at hy2⟩
    obtain ⟨w'', hlt, hs⟩ := hpair
    have hle := mFamIndex_le (b := b) (a := a) (F := F) ⟨w, rfl, w'', hlt, y, hFw, hs⟩
    rw [← hu] at hle
    rw [Fin.lt_def] at hwu
    omega
  -- (3) the abscissa
  have h3 : mFamAbscissa b a G = mFamAbscissa b a F := by
    refine le_antisymm (mFamAbscissa_le ⟨u, by rw [h2], by rw [h1]; exact hGu, v, huv,
      by rw [h1]; exact hGv⟩) ?_
    obtain ⟨w, hw, hy1, w', hww', hy2⟩ := mFamAbscissa_mem hGmono hGint
    rw [h2] at hw
    rw [(Fin.val_eq_val w u).mp hw] at hy1 hww'
    rw [h1] at hy1 hy2
    by_contra hcon
    have hlt : mFamAbscissa b a G < mFamAbscissa b a F := by omega
    have hFu : MOcc b (F u) (mFamHeight b a F) (mFamAbscissa b a G) :=
      hGdown u _ (Or.inl rfl) hlt hy1
    have hpair : ∃ w'' : Fin m, u < w'' ∧
        MOcc b (F w'') (mFamHeight b a F) (mFamAbscissa b a G) := by
      by_cases hc : w' = v
      · refine ⟨v, huv, ?_⟩
        rw [hc] at hy2
        exact hGdown v _ (Or.inr rfl) hlt hy2
      · exact ⟨w', hww', by rwa [hGother w' (ne_of_gt hww') hc] at hy2⟩
    obtain ⟨w'', hlt2, hs⟩ := hpair
    exact absurd (mFamAbscissa_le (b := b) (a := a) (F := F) ⟨u, hu, hFu, w'', hlt2, hs⟩) hcon
  -- (4) the partner
  have h4 : mFamPartner b a G = (v : ℕ) := by
    refine le_antisymm (mFamPartner_le ⟨v, rfl, by rw [h2, ← Fin.lt_def]; exact huv,
      by rw [h1, h3]; exact hGv⟩) ?_
    obtain ⟨w, hw, hlt, hs⟩ := mFamPartner_mem hGmono hGint
    rw [h1, h3] at hs
    rw [h2] at hlt
    by_contra hcon
    have hwv : w ≠ v := by intro hc; rw [hc] at hw; omega
    have hwu : w ≠ u := by intro hc; rw [hc] at hw; omega
    rw [hGother w hwu hwv] at hs
    have hlt' : mFamIndex b a F < (w : ℕ) := by rw [← hu, hw]; exact hlt
    have hle := mFamPartner_le (b := b) (a := a) (F := F) ⟨w, rfl, hlt', hs⟩
    rw [← hv] at hle
    omega
  exact ⟨hGint, h1, by rw [h2, hu], h3, by rw [h4, hv]⟩

/-- **The swap is an involution on the intersecting families.** -/
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
odd geometry both present.  This is `LGVInvolution.sum_famWeight_eq_sum_nonIntersecting`
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

/-! ## Two rows

At two paths there is one pair to test, so a non-intersecting family is a pair
of mixed paths that do not meet, and `LGVOddTableau.sum_nonMeeting_mixed_eq_superSkewSchur_uncond`
identifies their total weight with the branching sum the super branching rule.
-/

section TwoRows

variable {R : Type*} [CommRing R] {b a : ℕ}

/-- At two paths the family intersects exactly when its two paths meet. -/
theorem mIntersects_two {F : Fin 2 → ℕ → ℕ} :
    MIntersects b a F ↔ MMeets b a (F 0) (F 1) := by
  constructor
  · rintro ⟨u, v, huv, h⟩
    have h1 := u.isLt
    have h2 := v.isLt
    rw [Fin.lt_def] at huv
    have hu : u = 0 := by
      rw [Fin.ext_iff]
      change (u : ℕ) = 0
      omega
    have hv : v = 1 := by
      rw [Fin.ext_iff]
      change (v : ℕ) = 1
      omega
    rwa [hu, hv] at h
  · exact fun h => ⟨0, 1, by decide, h⟩

/-- The two-path families, read as pairs. -/
theorem sum_nonMIntersecting_two (β α : ℕ → R) (lam mu : YoungDiagram) :
    ∑ F ∈ (Fintype.piFinset fun w : Fin 2 =>
          mixedPaths b a (jtSource mu 2 w) (jtSink lam 2 w)).filter
            fun F => ¬ MIntersects b a F,
        ∏ w, mixedWeight b a β α (F w)
      = ∑ x ∈ (mixedPaths b a (mu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ
              mixedPaths b a (mu.rowLen 1) (lam.rowLen 1)).filter
                fun x => ¬ MixedMeets b a x.1 x.2,
          mixedWeight b a β α x.1 * mixedWeight b a β α x.2 := by
  refine Finset.sum_nbij' (fun F => (F 0, F 1)) (fun x => ![x.1, x.2]) (fun F hF => ?_)
    (fun x hx => ?_) (fun F hF => ?_) (fun x hx => ?_) (fun F hF => ?_)
  · rw [Finset.mem_filter, Fintype.mem_piFinset] at hF
    obtain ⟨hmem, hint⟩ := hF
    rw [mIntersects_two, mMeets_iff_mixedMeets] at hint
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hmem 0, hmem 1⟩, hint⟩
  · rw [Finset.mem_filter, Finset.mem_product] at hx
    obtain ⟨⟨h1, h2⟩, hint⟩ := hx
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun w => ?_, ?_⟩
    · match w with
      | 0 => exact h1
      | 1 => exact h2
    · rw [mIntersects_two, mMeets_iff_mixedMeets]
      exact hint
  · funext w
    match w with
    | 0 => rfl
    | 1 => rfl
  · exact Prod.ext rfl rfl
  · rw [Fin.prod_univ_two]

/-- **the skew Jacobi--Trudi identity at two rows, with the odd alphabet, unconditionally.**
For `λ` inside two rows,

`det [d_{λ_u - μ_v - u + v}]_{2 × 2} = s_{λ/μ}(β | α)`,

over any commutative ring, every `b`, `a`, `β`, `α` and every `μ ⊆ λ`.  The
cancellation is `mixedJacobiTrudiDet_eq_sum_nonIntersecting` and the tableau
side is `LGVOddTableau.sum_nonMeeting_mixed_eq_superSkewSchur_uncond`. -/
theorem skewJacobiTrudi_two_rows (β α : ℕ → R) (lam mu : YoungDiagram) (hmu : mu ≤ lam)
    (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) :
    jacobiTrudiDet (fun k => superHom b a k β α) lam mu 2 = superSkewSchur lam mu b a β α := by
  rw [mixedJacobiTrudiDet_eq_sum_nonIntersecting, sum_nonMIntersecting_two,
    sum_nonMeeting_mixed_eq_superSkewSchur_uncond lam mu hmu hrow]

end TwoRows

/-! ## What `SkewJacobiTrudi` still needs

The cancellation holds at every `m`; the residue is the tableau side.  It is
stated here as a predicate so that it sits in the type of anything that consumes
it, proved at `m ≤ 2`, and carried as a hypothesis beyond.
-/

section Residue

variable {R : Type*} [CommRing R]

/-- **The residue at `m` rows.**  That the non-intersecting families of `m`
mixed paths carry the branching sum of the super branching rule.

At `a = 0` this is `LGVTableauM.sum_nonIntersecting_eq_skewSchur`, and at two
rows it is `LGVOddTableau.sum_nonMeeting_mixed_eq_superSkewSchur_uncond`.  In
general it needs three things, each of which is proved at two rows only: the
height-`b` splice of a family at `m` paths, `LGVOdd.sum_nonMeeting_mixed_split`;
the odd tableau bijection at `m` columns,
`LGVOddTableau.nonMeetingIsSkewSchurTranspose`; and the dictionary carrying the
`m` abscissae at height `b` to the intermediate shapes `μ ⊆ ν ⊆ λ`, which
`LGVOdd.twoRow` and `LGVOdd.eq_twoRow` supply for two. -/
def NonIntersectingIsSuperSkewSchur (b a m : ℕ) (β α : ℕ → R) : Prop :=
  ∀ lam mu : YoungDiagram, mu ≤ lam → (∀ i, m ≤ i → lam.rowLen i = 0) →
    ∑ F ∈ (Fintype.piFinset fun w : Fin m =>
          mixedPaths b a (jtSource mu m w) (jtSink lam m w)).filter
            fun F => ¬ MIntersects b a F,
        ∏ w, mixedWeight b a β α (F w)
      = superSkewSchur lam mu b a β α

/-- The residue at two rows is a theorem. -/
theorem nonIntersectingIsSuperSkewSchur_two (b a : ℕ) (β α : ℕ → R) :
    NonIntersectingIsSuperSkewSchur b a 2 β α := by
  intro lam mu hmu hrow
  rw [sum_nonMIntersecting_two, sum_nonMeeting_mixed_eq_superSkewSchur_uncond lam mu hmu hrow]

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

end Shields
