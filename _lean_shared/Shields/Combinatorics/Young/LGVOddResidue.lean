/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.LGVInvolution
import Shields.Combinatorics.Young.LGVOddPaths

/-!
# The branching sum at `m` mixed paths

`Shields.Combinatorics.Young.LGVOddPaths` splices a *pair* of mixed paths at height `b`: below
that height the even geometry decides, from it on the odd one.  This module runs the same
separation at `m` paths and turns it into the branching sum of the super branching rule, given
the two tableau bijections.

The argument is one fibering.  A non-intersecting family of `m` mixed paths is sorted by the
`m` abscissae it occupies at height `b`.  Each fiber factors into a non-crossing even family
below the height and a non-meeting odd family above it, weight for weight
(`Shields.sum_nonIntersecting_mixed_split`).  A fiber whose abscissae are not strictly decreasing
has an empty odd half (`Shields.eFilter_eq_empty_of_not_drop`).  And the fibers that survive are
exactly the intermediate shapes `μ ⊆ ν ⊆ λ`: `Shields.shapeOfAbscissae` subtracts the
Jacobi--Trudi offsets from the abscissae and `Shields.jtSource` puts them back.

## Main results

* `Shields.sum_nonIntersecting_mixed_eq_superSkewSchur` -- the branching sum at `m` paths, from
  the even tableau bijection at `m` rows and the odd one at `m` columns.
* `Shields.sum_nonMeeting_mixed_eq_superSkewSchur` -- the same at two rows, read as pairs, which
  is what `Shields.Combinatorics.Young.LGVOddBranching` discharges the even half of.

## Implementation notes

The two tableau bijections enter as hypotheses rather than as imports.  Both are proved
elsewhere -- the even one at two rows in `Shields.Combinatorics.Young.LGVTableauTwo` and at every
`m` in `Shields.Combinatorics.Young.LGVTableau`, the odd one at two columns in
`Shields.Combinatorics.Young.LGVOddTableauTwo` and at every `m` in
`Shields.Combinatorics.Young.LGVOddTableau` -- and each of those modules sits downstream of this
one.  Carrying them in the type is what lets the fibering be written once and consumed at both
generalities.

The two-row statement reads its paths as an ordered pair rather than as a family over `Fin 2`,
because that is the shape the two-row cancellation delivers them in.
`Shields.sum_nonMIntersecting_two` and `Shields.sum_nonEIntersecting_two` are the translations,
and the offsets match on the nose: `jtSource ν 2` is `(ν₀ + 1, ν₁)`.

## Tags

Lindström-Gessel-Viennot, Jacobi-Trudi, skew Schur function, super Schur function, branching rule
-/

namespace Shields

open Finset

/-! ## Meeting, in both geometries at once

A mixed path sweeps an interval at each even height and stands at a point at each odd one, so two
mixed paths share a lattice point when their intervals overlap below height `b` or their points
coincide from height `b` on.  That is `LGVOdd.MixedMeets` read one height at a time, and
`mMeets_iff_mixedMeets` is the identification.
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

/-- From height `b` on a meeting is a coincidence of points. -/
theorem eq_of_mMeetsAt (hb : b ≤ i) (h : MMeetsAt b q r i) : q i = r i := by
  rcases h with ⟨h1, -, -⟩ | ⟨-, h2⟩
  · omega
  · exact h2

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

end Geometry

/-! ## Point disjointness for a family

`MMeets` on every pair, and `EMeets` on every pair, exactly as `LGVInvolution.Intersects` is
`Crosses` on every pair.
-/

section Family

variable {m : ℕ}

/-- Two paths of the family share a lattice point. -/
def MIntersects (b a : ℕ) (F : Fin m → ℕ → ℕ) : Prop :=
  ∃ u v : Fin m, u < v ∧ MMeets b a (F u) (F v)

instance (b a : ℕ) (F : Fin m → ℕ → ℕ) : Decidable (MIntersects b a F) := by
  unfold MIntersects; infer_instance

/-- Two odd paths of the family share a point. -/
def EIntersects (a : ℕ) (G : Fin m → ℕ → ℕ) : Prop :=
  ∃ u v : Fin m, u < v ∧ EMeets a (G u) (G v)

instance (a : ℕ) (G : Fin m → ℕ → ℕ) : Decidable (EIntersects a G) := by
  unfold EIntersects; infer_instance

end Family

/-! ## The splice at height `b`, at `m` paths

`sum_nonMeeting_mixed_split` separates a *pair* of mixed paths at height
`b`.  The same separation runs at `m` paths: the mixed predicate on a family is
the even predicate on the truncations or the odd predicate on the shifts, and the
weights factor the same way.
-/

section Split

variable {m : ℕ}

/-- **The mixed predicate on a family separates.**  A family shares a lattice
point exactly when its truncations cross below height `b` or its shifts meet
from height `b` on. -/
theorem mIntersects_iff (b a : ℕ) (F : Fin m → ℕ → ℕ) :
    MIntersects b a F ↔ Intersects b F ∨ EIntersects a fun w => shiftAt b (F w) := by
  constructor
  · rintro ⟨u, v, huv, h⟩
    rcases (mMeets_iff_mixedMeets b a _ _).mp h with hc | he
    · exact Or.inl ⟨u, v, huv, hc⟩
    · exact Or.inr ⟨u, v, huv, he⟩
  · rintro (⟨u, v, huv, h⟩ | ⟨u, v, huv, h⟩)
    · exact ⟨u, v, huv, (mMeets_iff_mixedMeets b a _ _).mpr (Or.inl h)⟩
    · exact ⟨u, v, huv, (mMeets_iff_mixedMeets b a _ _).mpr (Or.inr h)⟩

theorem intersects_truncAt (b : ℕ) (F : Fin m → ℕ → ℕ) :
    Intersects b (fun w => truncAt b (F w)) ↔ Intersects b F := by
  unfold Intersects Crosses
  simp only [crossSet_truncAt]

theorem intersects_glueAt (b : ℕ) (Y Z : Fin m → ℕ → ℕ) :
    Intersects b (fun w => glueAt b (Y w) (Z w)) ↔ Intersects b Y := by
  unfold Intersects Crosses
  simp only [crossSet_glueAt]

variable {R : Type*} [CommRing R]

/-- **The splice of a family.**  Both the weights and the non-intersection
condition separate at height `b`: a non-intersecting family of mixed paths
through the abscissae `c` is a non-crossing family of even paths below height `b`
together with a non-meeting family of odd paths above it, and the fiber sum is
the product of the two.

This is `sum_nonMeeting_mixed_split` at every `m`. -/
theorem sum_nonIntersecting_mixed_split (b a : ℕ) (S C c : Fin m → ℕ) (β α : ℕ → R) :
    ∑ F ∈ (Fintype.piFinset fun w => mixedPaths b a (S w) (C w)).filter
            (fun F => (∀ w, F w b = c w) ∧ ¬ MIntersects b a F),
        ∏ w, mixedWeight b a β α (F w)
      = (∑ Y ∈ (Fintype.piFinset fun w => hPaths b (S w) (c w)).filter
            fun Y => ¬ Intersects b Y, ∏ w, pathWeight b β (Y w))
        * ∑ Z ∈ (Fintype.piFinset fun w => ePaths a (c w) (C w)).filter
            fun Z => ¬ EIntersects a Z, ∏ w, pathWeight a α (Z w) := by
  rw [sum_mul_sum_prod]
  refine Finset.sum_nbij'
    (fun F => ((fun w => truncAt b (F w)), fun w => shiftAt b (F w)))
    (fun x => fun w => glueAt b (x.1 w) (x.2 w))
    (fun F hF => ?_) (fun x hx => ?_) (fun F hF => ?_) (fun x hx => ?_) (fun F hF => ?_)
  · rw [Finset.mem_filter, Fintype.mem_piFinset] at hF
    obtain ⟨hmem, hc, hnI⟩ := hF
    rw [mIntersects_iff, not_or] at hnI
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun w => ?_, ?_⟩,
      Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun w => ?_, hnI.2⟩⟩
    · rw [← hc w]; exact truncAt_mem (hmem w)
    · rw [intersects_truncAt]; exact hnI.1
    · rw [← hc w]; exact shiftAt_mem (hmem w)
  · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Fintype.mem_piFinset,
      Fintype.mem_piFinset] at hx
    obtain ⟨⟨hY, hYc⟩, hZ, hZm⟩ := hx
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun w => glueAt_mem (hY w) (hZ w),
      fun w => ?_, ?_⟩
    · change glueAt b (x.1 w) (x.2 w) b = c w
      rw [glueAt_of_le _ _ le_rfl]
      exact hPaths_top (hY w) le_rfl
    · rw [mIntersects_iff, not_or, intersects_glueAt]
      refine ⟨hYc, ?_⟩
      have hshift : (fun w => shiftAt b (glueAt b (x.1 w) (x.2 w))) = x.2 :=
        funext fun w => shiftAt_glueAt (hY w) (hZ w)
      rw [hshift]
      exact hZm
  · exact funext fun w => glueAt_truncAt_shiftAt b (F w)
  · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Fintype.mem_piFinset,
      Fintype.mem_piFinset] at hx
    obtain ⟨⟨hY, -⟩, hZ, -⟩ := hx
    exact Prod.ext (funext fun w => truncAt_glueAt (hY w))
      (funext fun w => shiftAt_glueAt (hY w) (hZ w))
  · change ∏ w, mixedWeight b a β α (F w)
      = (∏ w, pathWeight b β (truncAt b (F w))) * ∏ w, pathWeight a α (shiftAt b (F w))
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => by rw [mixedWeight, pathWeight_truncAt]

end Split

/-! ## The dictionary: `m` abscissae are an intermediate shape

The intermediate shape `ν` of the super branching rule is the vector of abscissae
the family occupies at height `b`, once the Jacobi--Trudi offsets are subtracted.
`mRows` builds a diagram from prescribed row lengths, and `shapeOfAbscissae` is
the passage; `jtSource ν m` is its inverse.
-/

section Dictionary

/-- The Young diagram with rows `r 0, …, r (m-1)` and no others.  Weakly
decreasing `r` is what makes those row lengths come back out. -/
def mRows : ℕ → (ℕ → ℕ) → YoungDiagram
  | 0, _ => ⊥
  | (n + 1), r => mRows n r ⊔ rect (n + 1) (r n)

theorem mem_mRows {m : ℕ} {r : ℕ → ℕ} {i j : ℕ} :
    (i, j) ∈ mRows m r ↔ ∃ k, k < m ∧ i ≤ k ∧ j < r k := by
  induction m with
  | zero =>
    constructor
    · intro h; exact absurd h (YoungDiagram.notMem_bot _)
    · rintro ⟨k, hk, -, -⟩; omega
  | succ n ih =>
    change (i, j) ∈ mRows n r ⊔ rect (n + 1) (r n) ↔ _
    rw [YoungDiagram.mem_sup, ih, mem_rect]
    constructor
    · rintro (⟨k, h1, h2, h3⟩ | ⟨h1, h2⟩)
      · exact ⟨k, by omega, h2, h3⟩
      · exact ⟨n, by omega, by omega, h2⟩
    · rintro ⟨k, h1, h2, h3⟩
      rcases Nat.lt_or_ge k n with h | h
      · exact Or.inl ⟨k, h, h2, h3⟩
      · obtain rfl : k = n := by omega
        exact Or.inr ⟨by omega, h3⟩

theorem rowLen_mRows {m : ℕ} {r : ℕ → ℕ}
    (hanti : ∀ k₁ k₂, k₁ ≤ k₂ → k₂ < m → r k₂ ≤ r k₁) (i : ℕ) :
    (mRows m r).rowLen i = if i < m then r i else 0 := by
  have key : ∀ j : ℕ, (i, j) ∈ mRows m r ↔ j < if i < m then r i else 0 := by
    intro j
    rw [mem_mRows]
    split_ifs with hi
    · constructor
      · rintro ⟨k, h1, h2, h3⟩
        exact lt_of_lt_of_le h3 (hanti i k h2 h1)
      · intro h
        exact ⟨i, hi, le_rfl, h⟩
    · constructor
      · rintro ⟨k, h1, h2, -⟩
        omega
      · intro h
        omega
  have h1 := key ((mRows m r).rowLen i)
  have h2 := key (if i < m then r i else 0)
  rw [YoungDiagram.mem_iff_lt_rowLen] at h1 h2
  omega

/-- The row lengths a vector of abscissae names: the abscissa less the
Jacobi--Trudi offset. -/
def abscissaRowLen (m : ℕ) (c : Fin m → ℕ) (i : ℕ) : ℕ :=
  if h : i < m then c ⟨i, h⟩ - (m - 1 - i) else 0

/-- The intermediate shape a vector of abscissae names. -/
def shapeOfAbscissae (m : ℕ) (c : Fin m → ℕ) : YoungDiagram := mRows m (abscissaRowLen m c)

/-- The abscissae of a fiber that survives: strictly decreasing, which after the
offsets is exactly the partition condition. -/
def AbscissaDrop {m : ℕ} (c : Fin m → ℕ) : Prop := ∀ u v : Fin m, u < v → c v < c u

instance {m : ℕ} (c : Fin m → ℕ) : Decidable (AbscissaDrop c) := by
  unfold AbscissaDrop; infer_instance

/-- A strictly decreasing vector of naturals drops by at least the index gap. -/
theorem add_sub_le_of_abscissaDrop {m : ℕ} {c : Fin m → ℕ} (h : AbscissaDrop c) :
    ∀ (v u : ℕ) (hu : u ≤ v) (hv : v < m),
      c ⟨v, hv⟩ + (v - u) ≤ c ⟨u, lt_of_le_of_lt hu hv⟩ := by
  intro v
  induction v with
  | zero =>
    intro u hu hv
    obtain rfl : u = 0 := by omega
    omega
  | succ v ih =>
    intro u hu hv
    rcases Nat.lt_or_ge u (v + 1) with hlt | hge
    · have hstep : c ⟨v + 1, hv⟩ < c ⟨v, by omega⟩ :=
        h ⟨v, by omega⟩ ⟨v + 1, hv⟩ (Fin.mk_lt_mk.mpr (by omega))
      have := ih u (by omega) (show v < m by omega)
      omega
    · obtain rfl : u = v + 1 := by omega
      omega

theorem abscissaRowLen_anti {m : ℕ} {c : Fin m → ℕ} (h : AbscissaDrop c) :
    ∀ k₁ k₂, k₁ ≤ k₂ → k₂ < m → abscissaRowLen m c k₂ ≤ abscissaRowLen m c k₁ := by
  intro k₁ k₂ h12 h2
  have hgap := add_sub_le_of_abscissaDrop h k₂ k₁ h12 h2
  rw [abscissaRowLen, abscissaRowLen, dif_pos h2, dif_pos (show k₁ < m by omega)]
  omega

theorem rowLen_shapeOfAbscissae {m : ℕ} {c : Fin m → ℕ} (h : AbscissaDrop c) (i : ℕ) :
    (shapeOfAbscissae m c).rowLen i = abscissaRowLen m c i := by
  rw [shapeOfAbscissae, rowLen_mRows (abscissaRowLen_anti h)]
  split_ifs with hi
  · rfl
  · rw [abscissaRowLen, dif_neg hi]

/-- **The abscissae are the shape.**  `jtSource` of the shape a vector names is
the vector itself, provided every abscissa clears its own offset. -/
theorem jtSource_shapeOfAbscissae {m : ℕ} {c : Fin m → ℕ} (h : AbscissaDrop c)
    (hoff : ∀ w : Fin m, m - 1 - (w : ℕ) ≤ c w) (w : Fin m) :
    jtSource (shapeOfAbscissae m c) m w = c w := by
  have hw := w.isLt
  have hc := hoff w
  rw [jtSource, rowLen_shapeOfAbscissae h, abscissaRowLen, dif_pos hw]
  have : (⟨(w : ℕ), hw⟩ : Fin m) = w := rfl
  rw [this]
  omega

/-- **The shape is the abscissae.**  A shape inside `m` rows is recovered from
its own Jacobi--Trudi sources. -/
theorem shapeOfAbscissae_jtSource {m : ℕ} {nu : YoungDiagram}
    (hnu : ∀ i, m ≤ i → nu.rowLen i = 0) :
    shapeOfAbscissae m (jtSource nu m) = nu := by
  have hanti : ∀ k₁ k₂, k₁ ≤ k₂ → k₂ < m →
      abscissaRowLen m (jtSource nu m) k₂ ≤ abscissaRowLen m (jtSource nu m) k₁ := by
    intro k₁ k₂ h12 h2
    have h1 : k₁ < m := by omega
    have hle : nu.rowLen k₂ ≤ nu.rowLen k₁ := nu.rowLen_anti k₁ k₂ h12
    rw [abscissaRowLen, abscissaRowLen, dif_pos h2, dif_pos h1]
    change nu.rowLen k₂ + (m - 1 - k₂) - (m - 1 - k₂) ≤ nu.rowLen k₁ + (m - 1 - k₁) - (m - 1 - k₁)
    omega
  refine eq_of_rowLen fun i => ?_
  rw [shapeOfAbscissae, rowLen_mRows hanti]
  split_ifs with hi
  · rw [abscissaRowLen, dif_pos hi]
    change nu.rowLen i + (m - 1 - i) - (m - 1 - i) = nu.rowLen i
    omega
  · exact (hnu i (by omega)).symm

end Dictionary

/-! ## The residue: the abscissae at height `b` are the intermediate shape

The non-intersecting mixed families are fibered over their abscissae at height `b`; each fiber
factors into an even and an odd half; a fiber whose abscissae are not strictly decreasing has an
empty odd half; and the surviving fibers are the intermediate shapes.
-/

section Residue

/-- **A surviving fiber names an intermediate shape.**  When the abscissae drop strictly and
each sits inside its own Jacobi--Trudi box, the shape they name lies between `μ` and `λ`.  The
two halves are the same case split on whether the row is one of the `m` the abscissae describe:
inside, the box condition is the inequality after the offset cancels; outside, both shapes have
an empty row. -/
theorem shapeOfAbscissae_mem_youngIcc {m : ℕ} {c : Fin m → ℕ} {lam mu : YoungDiagram}
    (hdrop : AbscissaDrop c) (hmu : mu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0)
    (hbox : ∀ (i : ℕ) (hi : i < m),
      mu.rowLen i + (m - 1 - i) ≤ c ⟨i, hi⟩ ∧ c ⟨i, hi⟩ ≤ lam.rowLen i + (m - 1 - i)) :
    mu ≤ shapeOfAbscissae m c ∧ shapeOfAbscissae m c ≤ lam := by
  have hrl : ∀ i, (shapeOfAbscissae m c).rowLen i = abscissaRowLen m c i :=
    rowLen_shapeOfAbscissae hdrop
  refine ⟨le_iff_rowLen.mpr fun i => ?_, le_iff_rowLen.mpr fun i => ?_⟩ <;>
    rw [hrl i, abscissaRowLen]
  · by_cases hi : i < m
    · rw [dif_pos hi]
      have := hbox i hi
      omega
    · rw [dif_neg hi]
      have : lam.rowLen i = 0 := hrow i (by omega)
      have := rowLen_mono hmu i
      omega
  · by_cases hi : i < m
    · rw [dif_pos hi]
      have := hbox i hi
      omega
    · rw [dif_neg hi]
      omega

variable {R : Type*} [CommRing R]

/-- What a surviving fiber hands the bijection: its abscissae drop strictly, each sits inside its
own Jacobi--Trudi box, and each clears its own offset. -/
theorem abscissaBox_of_mem {m : ℕ} {lam mu : YoungDiagram} {c : Fin m → ℕ}
    (hc : c ∈ (Fintype.piFinset fun w : Fin m =>
      Finset.Icc (jtSource mu m w) (jtSink lam m w)).filter (fun c => AbscissaDrop c)) :
    AbscissaDrop c ∧ (∀ (i : ℕ) (hi : i < m),
        mu.rowLen i + (m - 1 - i) ≤ c ⟨i, hi⟩ ∧ c ⟨i, hi⟩ ≤ lam.rowLen i + (m - 1 - i)) ∧
      ∀ w : Fin m, m - 1 - (w : ℕ) ≤ c w := by
  rw [Finset.mem_filter, Fintype.mem_piFinset] at hc
  have hbox : ∀ (i : ℕ) (hi : i < m), mu.rowLen i + (m - 1 - i) ≤ c ⟨i, hi⟩ ∧
      c ⟨i, hi⟩ ≤ lam.rowLen i + (m - 1 - i) := fun i hi => Finset.mem_Icc.mp (hc.1 ⟨i, hi⟩)
  refine ⟨hc.2, hbox, fun w => ?_⟩
  have : mu.rowLen (w : ℕ) + (m - 1 - (w : ℕ)) ≤ c w := (hbox (w : ℕ) w.isLt).1
  omega

/-- **The surviving fibers are the intermediate shapes.**  `shapeOfAbscissae` and `jtSource` are
inverse between the abscissa tuples that drop strictly inside the Jacobi--Trudi box and the
diagrams `μ ⊆ ν ⊆ λ`, so a sum over one is a sum over the other. -/
theorem sum_shapeOfAbscissae {M : Type*} [AddCommMonoid M] {m : ℕ} {lam mu : YoungDiagram}
    (hmu : mu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) (f : YoungDiagram → M) :
    ∑ c ∈ (Fintype.piFinset fun w : Fin m =>
        Finset.Icc (jtSource mu m w) (jtSink lam m w)).filter (fun c => AbscissaDrop c),
        f (shapeOfAbscissae m c)
      = ∑ nu ∈ youngIcc mu lam, f nu := by
  refine Finset.sum_nbij' (fun c => shapeOfAbscissae m c) (fun nu => jtSource nu m)
    (fun c hc => ?_) (fun nu hnu => ?_) (fun c hc => ?_) (fun nu hnu => ?_) (fun _ _ => rfl)
  · -- the shape of a surviving fiber lies between `mu` and `lam`
    obtain ⟨hdrop, hbox, -⟩ := abscissaBox_of_mem hc
    exact mem_youngIcc.mpr (shapeOfAbscissae_mem_youngIcc hdrop hmu hrow hbox)
  · -- an intermediate shape names a surviving fiber
    obtain ⟨h1, h2⟩ := mem_youngIcc.mp hnu
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun w => Finset.mem_Icc.mpr ?_,
      fun u v huv => strictAnti_jtSource nu m huv⟩
    exact ⟨by rw [jtSource, jtSource]; have := rowLen_mono h1 (w : ℕ); omega,
      by rw [jtSource, jtSink]; have := rowLen_mono h2 (w : ℕ); omega⟩
  · -- fiber to shape and back
    obtain ⟨hdrop, -, hoff⟩ := abscissaBox_of_mem hc
    exact funext fun w => jtSource_shapeOfAbscissae hdrop hoff w
  · -- shape to fiber and back
    obtain ⟨-, h2⟩ := mem_youngIcc.mp hnu
    exact shapeOfAbscissae_jtSource fun i hi =>
      Nat.le_zero.mp (hrow i hi ▸ rowLen_mono h2 i)

/-- A family of odd paths whose sources are not strictly decreasing while its
sinks are either meets or is impossible: this is what empties the fibers of the
splice that no intermediate shape indexes. -/
theorem eFilter_eq_empty_of_not_drop {a m : ℕ} {c C : Fin m → ℕ} (hC : StrictAnti C)
    (h : ¬ AbscissaDrop c) :
    ((Fintype.piFinset fun w => ePaths a (c w) (C w)).filter
      fun Z => ¬ EIntersects a Z) = ∅ := by
  obtain ⟨u, v, huv, hle⟩ : ∃ u v : Fin m, u < v ∧ c u ≤ c v := by
    rw [AbscissaDrop, not_forall] at h
    obtain ⟨u, hu⟩ := h
    rw [not_forall] at hu
    obtain ⟨v, hv⟩ := hu
    rw [not_forall] at hv
    obtain ⟨huv, hlt⟩ := hv
    exact ⟨u, v, huv, by omega⟩
  refine Finset.eq_empty_of_forall_notMem fun Z hZ => ?_
  rw [Finset.mem_filter, Fintype.mem_piFinset] at hZ
  obtain ⟨hmem, hnI⟩ := hZ
  have hnm : ¬ EMeets a (Z u) (Z v) := fun hc => hnI ⟨u, v, huv, hc⟩
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact hnm ⟨0, mem_eMeetSet.mpr ⟨Nat.zero_le a, by
      rw [hPaths_zero (ePaths_mem (hmem u)), hPaths_zero (ePaths_mem (hmem v))]; exact heq⟩⟩
  · have hsym : ¬ EMeets a (Z v) (Z u) := fun hc => hnm (by rwa [EMeets, eMeetSet_comm])
    have hsep := lt_of_not_eMeets (hmem v) (hmem u) hlt hsym a le_rfl
    rw [hPaths_top (ePaths_mem (hmem u)) le_rfl, hPaths_top (ePaths_mem (hmem v)) le_rfl] at hsep
    exact absurd (hC huv) (by omega)

/-- **The branching sum at `m` mixed paths.**  The non-intersecting families of `m` mixed paths
from the sources of `μ` to the sinks of `λ` carry the branching sum of the super branching rule,
given the even tableau bijection at `m` rows and the odd one at `m` columns.

The proof is the fibering over the abscissae at height `b` and nothing else: each fiber factors
into its even and its odd half (`sum_nonIntersecting_mixed_split`), a fiber whose abscissae are
not strictly decreasing has an empty odd half (`eFilter_eq_empty_of_not_drop`), and the survivors
are indexed by the intermediate shapes `μ ⊆ ν ⊆ λ` (`shapeOfAbscissae`).  No Cauchy--Binet, no
minor pairing.

Both hypotheses are theorems, proved downstream: `sum_nonIntersecting_eq_skewSchur`
and `sum_nonEIntersecting_eq_skewSchurTranspose`. -/
theorem sum_nonIntersecting_mixed_eq_superSkewSchur {b a m : ℕ} {β α : ℕ → R}
    (hH : ∀ nu mu : YoungDiagram, mu ≤ nu → (∀ i, m ≤ i → nu.rowLen i = 0) →
      ∑ Y ∈ (Fintype.piFinset fun w : Fin m =>
            hPaths b (jtSource mu m w) (jtSink nu m w)).filter fun Y => ¬ Intersects b Y,
          ∏ w, pathWeight b β (Y w)
        = skewSchur nu mu b β)
    (hE : ∀ lam nu : YoungDiagram, nu ≤ lam → (∀ i, m ≤ i → lam.rowLen i = 0) →
      ∑ Z ∈ (Fintype.piFinset fun w : Fin m =>
            ePaths a (jtSource nu m w) (jtSink lam m w)).filter fun Z => ¬ EIntersects a Z,
          ∏ w, pathWeight a α (Z w)
        = skewSchur lam.transpose nu.transpose a α)
    (lam mu : YoungDiagram) (hmu : mu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    ∑ F ∈ (Fintype.piFinset fun w : Fin m =>
          mixedPaths b a (jtSource mu m w) (jtSink lam m w)).filter
            fun F => ¬ MIntersects b a F,
        ∏ w, mixedWeight b a β α (F w)
      = superSkewSchur lam mu b a β α := by
  set T : Finset (Fin m → ℕ) :=
    Fintype.piFinset fun w => Finset.Icc (jtSource mu m w) (jtSink lam m w) with hT
  have hmaps : ∀ F ∈ (Fintype.piFinset fun w : Fin m =>
      mixedPaths b a (jtSource mu m w) (jtSink lam m w)).filter
        (fun F => ¬ MIntersects b a F), (fun w => F w b) ∈ T := by
    intro F hF
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hF
    refine Fintype.mem_piFinset.mpr fun w => Finset.mem_Icc.mpr ?_
    exact hPaths_le (mem_mixedPaths.mp (hF.1 w)).1 b
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- every fiber factors into its even and its odd half
  simp only [Finset.filter_filter, funext_iff]
  rw [Finset.sum_congr rfl fun c _ => Eq.trans
    (Finset.sum_congr (Finset.filter_congr fun _ _ => and_comm) fun _ _ => rfl)
    (sum_nonIntersecting_mixed_split b a (jtSource mu m) (jtSink lam m) c β α)]
  rw [superSkewSchur_eq_branching _ _ _ _ _ _ hmu]
  -- a fiber whose abscissae are not strictly decreasing has an empty odd half
  refine Eq.trans (Finset.sum_subset (Finset.filter_subset (fun c => AbscissaDrop c) T) ?_).symm ?_
  · intro c hc hnot
    rw [Finset.mem_filter] at hnot
    rw [eFilter_eq_empty_of_not_drop (strictAnti_jtSink lam m) (fun hd => hnot ⟨hc, hd⟩),
      Finset.sum_empty, mul_zero]
  -- the surviving fibers are the intermediate shapes, and the summand is the branching term
  refine Eq.trans (Finset.sum_congr rfl fun c hc => ?_) (sum_shapeOfAbscissae hmu hrow _)
  obtain ⟨hdrop, hbox, hoff⟩ := abscissaBox_of_mem hc
  have hsrc : ∀ w : Fin m, jtSource (shapeOfAbscissae m c) m w = c w :=
    jtSource_shapeOfAbscissae hdrop hoff
  have hsink : ∀ w : Fin m, jtSink (shapeOfAbscissae m c) m w = c w := fun w => hsrc w
  have hnurow : ∀ i, m ≤ i → (shapeOfAbscissae m c).rowLen i = 0 := fun i hi => by
    rw [rowLen_shapeOfAbscissae hdrop i, abscissaRowLen, dif_neg (by omega)]
  obtain ⟨hmunu, hnulam⟩ := shapeOfAbscissae_mem_youngIcc hdrop hmu hrow hbox
  have heven := hH (shapeOfAbscissae m c) mu hmunu hnurow
  have hodd := hE lam (shapeOfAbscissae m c) hnulam hrow
  simp only [hsink] at heven
  simp only [hsrc] at hodd
  rw [← heven, ← hodd]

end Residue

/-! ## Two rows, read as pairs

At two paths there is one pair to test, so a non-intersecting family is a pair of paths that do
not meet.  `sum_nonIntersecting_two` is the even translation; the mixed and the odd
ones are here.
-/

section TwoRows

variable {R : Type*} [CommRing R] {b a : ℕ}

/-- **A family of two paths is a pair.**  When the family predicate `Q` is the pair
predicate `q` read on the two members, summing a product weight over the families avoiding
`Q` is summing the pair weight over the pairs avoiding `q`. -/
theorem sum_piFinset_two {M : Type*} [CommSemiring M] {P : Fin 2 → Finset (ℕ → ℕ)}
    {Q : (Fin 2 → ℕ → ℕ) → Prop} [DecidablePred Q]
    {q : (ℕ → ℕ) → (ℕ → ℕ) → Prop} [DecidableRel q]
    (hQ : ∀ F : Fin 2 → ℕ → ℕ, Q F ↔ q (F 0) (F 1)) (f : (ℕ → ℕ) → M) :
    ∑ F ∈ (Fintype.piFinset P).filter (fun F => ¬ Q F), ∏ w, f (F w)
      = ∑ x ∈ (P 0 ×ˢ P 1).filter (fun x => ¬ q x.1 x.2), f x.1 * f x.2 := by
  refine Finset.sum_nbij' (fun F => (F 0, F 1)) (fun x => ![x.1, x.2]) (fun F hF => ?_)
    (fun x hx => ?_) (fun F hF => ?_) (fun x hx => ?_) (fun F hF => ?_)
  · rw [Finset.mem_filter, Fintype.mem_piFinset] at hF
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hF.1 0, hF.1 1⟩,
      fun hc => hF.2 ((hQ F).mpr hc)⟩
  · rw [Finset.mem_filter, Finset.mem_product] at hx
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun w => ?_,
      fun hc => hx.2 ((hQ _).mp hc)⟩
    match w with
    | 0 => exact hx.1.1
    | 1 => exact hx.1.2
  · funext w
    match w with
    | 0 => rfl
    | 1 => rfl
  · exact Prod.ext rfl rfl
  · rw [Fin.prod_univ_two]

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
          mixedWeight b a β α x.1 * mixedWeight b a β α x.2 :=
  sum_piFinset_two (fun _ => mIntersects_two.trans (mMeets_iff_mixedMeets b a _ _)) _

/-- At two paths the odd family shares a point exactly when its two paths meet. -/
theorem eIntersects_two {G : Fin 2 → ℕ → ℕ} :
    EIntersects a G ↔ EMeets a (G 0) (G 1) := by
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

/-- The two-path odd families, read as pairs. -/
theorem sum_nonEIntersecting_two (α : ℕ → R) (lam nu : YoungDiagram) :
    ∑ G ∈ (Fintype.piFinset fun w : Fin 2 =>
          ePaths a (jtSource nu 2 w) (jtSink lam 2 w)).filter fun G => ¬ EIntersects a G,
        ∏ w, pathWeight a α (G w)
      = ∑ x ∈ (ePaths a (nu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ
              ePaths a (nu.rowLen 1) (lam.rowLen 1)).filter
                fun x => ¬ EMeets a x.1 x.2,
          pathWeight a α x.1 * pathWeight a α x.2 :=
  sum_piFinset_two (fun _ => eIntersects_two) _

end TwoRows

/-! ## The branching sum at two rows

The two-row statement the odd path model leaves behind, in the pair reading.  Its two tableau
bijections are hypotheses here and are discharged downstream: the even one in
`Shields.Combinatorics.Young.LGVOddBranching`, the odd one in
`Shields.Combinatorics.Young.LGVOddTableauTwo`.
-/

section TwoRowBranching

variable {R : Type*} [CommRing R]

/-- **the super branching rule at two rows.**  Given the two tableau bijections -- the even one
of `Shields.LGV` and the odd one of `Shields.LGVOdd` -- the non-intersecting pairs of mixed paths
carry the branching sum of the super branching rule.

This is `sum_nonIntersecting_mixed_eq_superSkewSchur` at `m = 2`, with the pairs read as families
over `Fin 2`.  The offsets `jtSource ν 2` are `(ν₀ + 1, ν₁)` on the nose, so the three
translations -- `sum_nonMIntersecting_two` for the conclusion, `sum_nonIntersecting_two` and
`sum_nonEIntersecting_two` for the two hypotheses -- are all the passage needs. -/
theorem sum_nonMeeting_mixed_eq_superSkewSchur {b a : ℕ} {β α : ℕ → R}
    (hH : NonCrossingIsSkewSchur b β) (hE : NonMeetingIsSkewSchurTranspose a α)
    (lam mu : YoungDiagram) (hmu : mu ≤ lam) (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) :
    ∑ x ∈ (mixedPaths b a (mu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ
            mixedPaths b a (mu.rowLen 1) (lam.rowLen 1)).filter
              fun x => ¬ MixedMeets b a x.1 x.2,
        mixedWeight b a β α x.1 * mixedWeight b a β α x.2
      = superSkewSchur lam mu b a β α := by
  rw [← sum_nonMIntersecting_two β α lam mu]
  refine sum_nonIntersecting_mixed_eq_superSkewSchur ?_ ?_ lam mu hmu hrow
  · intro nu mu' hmu' hnurow
    rw [sum_nonIntersecting_two β nu mu']
    exact hH nu mu' hmu' hnurow
  · intro lam' nu hnu hlamrow
    rw [sum_nonEIntersecting_two α lam' nu]
    exact hE lam' nu hnu hlamrow

end TwoRowBranching


/-! ### Axiom footprint -/

/-- info: 'Shields.sum_nonMeeting_mixed_eq_superSkewSchur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_nonMeeting_mixed_eq_superSkewSchur

end Shields
