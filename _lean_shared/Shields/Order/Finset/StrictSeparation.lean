/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Order.Interval.Finset.Basic

/-!
# Strict separation pins a finite set

A finite set `S` **separates strictly** under `f : ι → α` when every member takes a smaller value
than every non-member.  Two facts follow, and neither uses anything about `α` beyond its order.

Such a set is determined by its cardinality: two sets of the same size that both separate strictly
are equal.  And a strict separator cannot split a tie — if two indices carry the same value, no
separator contains one and omits the other.

The two are complementary, and read together they say where the hypothesis has to go.  Uniqueness
is unconditional; *existence* at a prescribed cardinality is not, because a value shared by several
indices makes every candidate set of the wrong size split the tie.  A consumer therefore needs a
gap at the rank it selects, and the second theorem is what makes that necessary rather than
merely convenient.

## Main results

* `Shields.eq_of_forall_lt_of_card_eq` — equal cardinality and strict separation force equality.
* `Shields.not_forall_lt_of_eq` — a strict separator cannot split a tie.

## Tags

strict separation, finset, linear order, uniqueness
-/

namespace Shields

variable {ι α : Type*} [LinearOrder α] {f : ι → α}

/--
**Strict separation determines the set.**  If `S` and `T` have the same cardinality and each
separates strictly under `f`, then `S = T`.

The proof is antisymmetry: if the two differ, equal cardinality forces an `i` in the first but not
the second and a `j` in the second but not the first, and the two separation hypotheses then give
`f i < f j` and `f j < f i`.

Note what it does *not* say.  Existence at a prescribed cardinality is a separate matter and can
fail: when several indices share the boundary value, no set of that size separates strictly at
all — which is exactly the tie `not_forall_lt_of_eq` rules out.
-/
theorem eq_of_forall_lt_of_card_eq {S T : Finset ι} (hcard : S.card = T.card)
    (hS : ∀ i ∈ S, ∀ j ∉ S, f i < f j) (hT : ∀ i ∈ T, ∀ j ∉ T, f i < f j) :
    S = T := by
  by_contra hne
  -- Equal cardinality makes each set meet the other's complement.
  have hST : ∃ i, i ∈ S ∧ i ∉ T := by
    by_contra h
    push Not at h
    exact hne (Finset.eq_of_subset_of_card_le h hcard.ge)
  have hTS : ∃ j, j ∈ T ∧ j ∉ S := by
    by_contra h
    push Not at h
    exact hne (Finset.eq_of_subset_of_card_le h hcard.le).symm
  obtain ⟨i, hiS, hiT⟩ := hST
  obtain ⟨j, hjT, hjS⟩ := hTS
  exact absurd (hS i hiS j hjS) (not_lt.mpr (hT j hjT i hiT).le)

/--
**Strict separation cannot split a tie.**  If two indices carry the same value, no set with the
separation property contains one and omits the other.
-/
theorem not_forall_lt_of_eq {S : Finset ι} {i j : ι}
    (hij : f i = f j) (hiS : i ∈ S) (hjS : j ∉ S) :
    ¬ ∀ x ∈ S, ∀ y ∉ S, f x < f y :=
  fun h => absurd (h i hiS j hjS) (by rw [hij]; exact lt_irrefl _)

/-- info: 'Shields.eq_of_forall_lt_of_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_of_forall_lt_of_card_eq

/-- info: 'Shields.not_forall_lt_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_forall_lt_of_eq

end Shields
