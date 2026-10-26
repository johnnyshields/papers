import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod

/-!
# The census returns exactly the Schur classes

Formalizes `shields-2026-skew-base-computational.tex`, «The census» (`sec:census`), `def:census`
and `thm:census`, abstractly.

The census of a finite set `U` of diagrams, closed under rotation, groups representatives of the
rotation orbits by the row multiset (the shard), then by the pair (invariant, value at the first
point), then by the value at the second point, then by equality of the polynomial `s`, and
reports each final part together with the rotations of its members.  `census_eq` proves the
reported parts are exactly the classes `{y ∈ U | s y = s x}`.

The argument takes three inputs as hypotheses:

* rotation invariance `s (rot x) = s x` (`hs_rot`);
* equal polynomials have equal shard and equal invariant (`hinv`), the content of the
  row-overlap invariants of Schur-equal diagrams (`lem:invariants`);
* the two evaluations `ev₁`, `ev₂` are functions, so equal polynomials have equal values.

The evaluations are *not* assumed to commute with anything here: the census only needs that a
function of `s` is constant on Schur classes.  That evaluation of a Jacobi–Trudi determinant is
the determinant of the evaluated entries is `SkewBase.evalAt_jtDet`.

Sorry-free.
-/

namespace SkewBase

section Grouping

variable {X : Type*} [DecidableEq X]

/-- The classes of the finite set `S` under equality of the key `k`, as a set of parts. -/
def classesBy {κ : Type*} [DecidableEq κ] (k : X → κ) (S : Finset X) : Finset (Finset X) :=
  S.image fun x => S.filter fun y => k y = k x

/-- Regroup every part of `Ps` by the key `k`. -/
def refineBy {κ : Type*} [DecidableEq κ] (k : X → κ) (Ps : Finset (Finset X)) :
    Finset (Finset X) :=
  Ps.biUnion (classesBy k)

/-- Regrouping the classes of one key by a second key gives the classes of the pair. -/
theorem refineBy_classesBy {κ ι : Type*} [DecidableEq κ] [DecidableEq ι] (k : X → κ)
    (f : X → ι) (S : Finset X) :
    refineBy f (classesBy k S) = classesBy (fun x => (k x, f x)) S := by
  ext P
  simp only [refineBy, classesBy, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, z, hz, rfl⟩
    have hz' := Finset.mem_filter.mp hz
    refine ⟨z, hz'.1, ?_⟩
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2.trans hz'.2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2.trans hz'.2.symm, h3⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨S.filter fun y => k y = k z, ⟨z, hz, rfl⟩, z, Finset.mem_filter.mpr ⟨hz, rfl⟩, ?_⟩
    ext y
    simp only [Finset.mem_filter]
    tauto

/-- Classes under two keys that agree are the same. -/
theorem classesBy_congr {κ ι : Type*} [DecidableEq κ] [DecidableEq ι] (k : X → κ) (f : X → ι)
    (S : Finset X) (h : ∀ x y, k y = k x ↔ f y = f x) : classesBy k S = classesBy f S := by
  unfold classesBy
  refine Finset.image_congr fun x _ => ?_
  exact Finset.filter_congr fun y _ => h x y

end Grouping

section Census

variable {X σ ι A R₁ R₂ : Type*} [DecidableEq X] [DecidableEq σ] [DecidableEq ι]
  [DecidableEq A] [DecidableEq R₁] [DecidableEq R₂]

/-- **`def:census`**, on the finite set `reps` of orbit representatives: `shard` is the row
multiset, `inv` the invariant `I`, `s` the skew Schur function and `ev₁`, `ev₂` the two
evaluations.  Per shard: group the representatives by `(inv, ev₁ ∘ s)`, regroup by `ev₂ ∘ s`,
regroup by `s`, and adjoin the rotations to each final part.

(A group of one representative is its own regrouping, so the paper's "in each group of two or
more" is the same computation.) -/
def censusOf (rot : X → X) (shard : X → σ) (inv : X → ι) (s : X → A) (ev₁ : A → R₁)
    (ev₂ : A → R₂) (reps : Finset X) : Finset (Finset X) :=
  (reps.image shard).biUnion fun ρ =>
    (refineBy s (refineBy (fun x => ev₂ (s x))
      (classesBy (fun x => (inv x, ev₁ (s x))) (reps.filter fun x => shard x = ρ)))).image
        fun P => P ∪ P.image rot

/-- The census of `U`, run on the representatives `canon x ∈ {x, rot x}` of its rotation
orbits. -/
def census (rot canon : X → X) (shard : X → σ) (inv : X → ι) (s : X → A) (ev₁ : A → R₁)
    (ev₂ : A → R₂) (U : Finset X) : Finset (Finset X) :=
  censusOf rot shard inv s ev₁ ev₂ (U.image canon)

/-- **`thm:census`, soundness and completeness.**  The parts reported by the census are exactly
the Schur classes `{y ∈ U | s y = s x}`, for a rotation-closed finite set `U`, given that
rotation preserves `s` and that equal `s` forces equal shard and equal invariant. -/
theorem census_eq (rot canon : X → X) (shard : X → σ) (inv : X → ι) (s : X → A)
    (ev₁ : A → R₁) (ev₂ : A → R₂) (U : Finset X)
    (hrot : ∀ x, rot (rot x) = x) (hs_rot : ∀ x, s (rot x) = s x)
    (hcanon : ∀ x, canon x = x ∨ canon x = rot x)
    (hinv : ∀ x y, s x = s y → shard x = shard y ∧ inv x = inv y)
    (hU : ∀ x ∈ U, rot x ∈ U) :
    census rot canon shard inv s ev₁ ev₂ U = U.image fun x => U.filter fun y => s y = s x := by
  unfold census
  set reps := U.image canon with hreps
  have hrepsU : ∀ z ∈ reps, z ∈ U := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    rcases hcanon y with h | h <;> rw [h]
    · exact hy
    · exact hU y hy
  have hs_canon : ∀ z, s (canon z) = s z := by
    intro z
    rcases hcanon z with h | h <;> rw [h]
    exact hs_rot z
  -- the parts of one shard, after the three regroupings
  have hparts : ∀ S : Finset X, refineBy s (refineBy (fun x => ev₂ (s x))
      (classesBy (fun x => (inv x, ev₁ (s x))) S)) = classesBy s S := by
    intro S
    rw [refineBy_classesBy, refineBy_classesBy]
    apply classesBy_congr
    intro x y
    constructor
    · intro h
      exact (Prod.mk.inj h).2
    · intro h
      obtain ⟨-, h2⟩ := hinv y x h
      simp only [Prod.mk.injEq]
      exact ⟨⟨⟨h2, by rw [h]⟩, by rw [h]⟩, h⟩
  -- adjoining rotations to the class of a representative gives the full Schur class
  have hadj : ∀ r ∈ reps,
      ((reps.filter fun x => shard x = shard r).filter fun y => s y = s r) ∪
        ((reps.filter fun x => shard x = shard r).filter fun y => s y = s r).image rot =
      U.filter fun y => s y = s r := by
    intro r hr
    ext z
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro (⟨⟨hz, -⟩, hs⟩ | ⟨y, ⟨⟨hy, -⟩, hs⟩, rfl⟩)
      · exact ⟨hrepsU z hz, hs⟩
      · exact ⟨hU y (hrepsU y hy), by rw [hs_rot, hs]⟩
    · rintro ⟨hz, hs⟩
      have hc : canon z ∈ reps := Finset.mem_image_of_mem canon hz
      have hsc : s (canon z) = s r := by rw [hs_canon, hs]
      have hshard := (hinv _ _ hsc).1
      have hmem : canon z ∈ (reps.filter fun x => shard x = shard r).filter
          fun y => s y = s r := by
        simp only [Finset.mem_filter]
        exact ⟨⟨hc, hshard⟩, hsc⟩
      rcases hcanon z with h | h
      · left
        rw [h] at hmem
        simpa only [Finset.mem_filter] using hmem
      · right
        refine ⟨canon z, ?_, ?_⟩
        · simpa only [Finset.mem_filter] using hmem
        · rw [h, hrot]
  ext Q
  simp only [censusOf, hparts, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨ρ, ⟨r0, hr0, rfl⟩, P, hP, rfl⟩
    unfold classesBy at hP
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
    have hxreps : x ∈ reps := (Finset.mem_filter.mp hx).1
    have hρ : shard x = shard r0 := (Finset.mem_filter.mp hx).2
    refine ⟨x, hrepsU x hxreps, ?_⟩
    have hS : (reps.filter fun y => shard y = shard r0) =
        reps.filter fun y => shard y = shard x := by
      rw [hρ]
    rw [hS]
    exact (hadj x hxreps).symm
  · rintro ⟨x, hx, rfl⟩
    have hc : canon x ∈ reps := Finset.mem_image_of_mem canon hx
    refine ⟨shard (canon x), ⟨canon x, hc, rfl⟩,
      {y ∈ {x_1 ∈ reps | shard x_1 = shard (canon x)} | s y = s (canon x)}, ?_, ?_⟩
    · unfold classesBy
      refine Finset.mem_image.mpr ⟨canon x, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hc, rfl⟩
    · rw [hadj _ hc, hs_canon]

end Census

section Canonical

variable {X : Type*}

/-- The lexicographically smaller of a diagram and its rotation, for a linear order on diagrams,
is a representative of the rotation orbit of the kind `census_eq` requires. -/
theorem canonMin_cases [LinearOrder X] (rot : X → X) (x : X) :
    min x (rot x) = x ∨ min x (rot x) = rot x := by
  rcases le_total x (rot x) with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

/-- With that choice, the representative of a rotation orbit does not depend on the member. -/
theorem canonMin_rot [LinearOrder X] (rot : X → X) (hrot : ∀ x, rot (rot x) = x) (x : X) :
    min (rot x) (rot (rot x)) = min x (rot x) := by
  rw [hrot, min_comm]

end Canonical

end SkewBase
