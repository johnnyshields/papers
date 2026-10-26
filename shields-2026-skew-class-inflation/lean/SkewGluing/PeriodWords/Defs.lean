-- TODO-COPIED: skew-factor-gluing/lean/SkewGluing/PeriodWords/Defs.lean
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Common
import SkewGluing.Tactics

/-!
# Period constraints on words and their period graph

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-periods`).

A word of length `L` is a function `ℤ → α`, read on the positions `1, …, L`.  It has period `p`
except at a set `S` of residues when positions `x` and `x + p`, both in range, carry equal values
whenever `x % p ∉ S`.  The period graph joins the positions constrained to be equal; `PeriodJoined`
is the equivalence relation it generates.  Words satisfying the constraints are constant on the
classes of the period graph, and the period graph is the universal such quotient.

Sorry-free.
-/

namespace SkewGluing
namespace PeriodWords

/-- A word `f` of length `L` has period `p` except at the residues `S`: positions `x` and `x + p`
of `1, …, L` carry equal values unless `x` has residue in `S` modulo `p`.  A *full* period is the
case `S = ∅`. -/
def PeriodExcept {α : Type*} (L p : ℕ) (S : Finset ℤ) (f : ℤ → α) : Prop :=
  ∀ x ∈ Finset.Icc (1 : ℤ) ((L : ℤ) - p), x % (p : ℤ) ∉ S → f x = f (x + p)

instance {α : Type*} [DecidableEq α] {L p : ℕ} {S : Finset ℤ} {f : ℤ → α} :
    Decidable (PeriodExcept L p S f) := by
  unfold PeriodExcept
  infer_instance

/-- The edge of the period graph from `x` to `x + p`, present on `1, …, L` unless the residue of
`x` modulo `p` is exceptional. -/
def periodEdge (L p : ℕ) (S : Finset ℤ) (x y : ℤ) : Prop :=
  x ∈ Finset.Icc (1 : ℤ) ((L : ℤ) - p) ∧ x % (p : ℤ) ∉ S ∧ y = x + p

/-- Two positions are joined in the period graph of the constraints "period `p` except at the
residues `S`" and "period `Q` except at the residues `T`" on a word of length `L`. -/
def PeriodJoined (L p : ℕ) (S : Finset ℤ) (Q : ℕ) (T : Finset ℤ) : ℤ → ℤ → Prop :=
  Relation.EqvGen fun x y => periodEdge L p S x y ∨ periodEdge L Q T x y

theorem periodExcept_iff_edges {α : Type*} {L p : ℕ} {S : Finset ℤ} {f : ℤ → α} :
    PeriodExcept L p S f ↔ ∀ x y, periodEdge L p S x y → f x = f y := by
  constructor
  · rintro h x y ⟨hx, hS, rfl⟩
    exact h x hx hS
  · intro h x hx hS
    exact h x _ ⟨hx, hS, rfl⟩

theorem PeriodJoined.symm {L p : ℕ} {S : Finset ℤ} {Q : ℕ} {T : Finset ℤ} {x y : ℤ}
    (h : PeriodJoined L p S Q T x y) : PeriodJoined L p S Q T y x :=
  Relation.EqvGen.symm _ _ h

theorem PeriodJoined.trans {L p : ℕ} {S : Finset ℤ} {Q : ℕ} {T : Finset ℤ} {x y z : ℤ}
    (h : PeriodJoined L p S Q T x y) (h' : PeriodJoined L p S Q T y z) :
    PeriodJoined L p S Q T x z :=
  Relation.EqvGen.trans _ _ _ h h'

theorem periodJoined_equivalence (L p : ℕ) (S : Finset ℤ) (Q : ℕ) (T : Finset ℤ) :
    Equivalence (PeriodJoined L p S Q T) :=
  Relation.EqvGen.is_equivalence _

theorem periodJoined_comm {L p : ℕ} {S : Finset ℤ} {Q : ℕ} {T : Finset ℤ} {x y : ℤ} :
    PeriodJoined L p S Q T x y ↔ PeriodJoined L Q T p S x y := by
  have key : ∀ {p Q : ℕ} {S T : Finset ℤ} {x y : ℤ},
      PeriodJoined L p S Q T x y → PeriodJoined L Q T p S x y := by
    intro p Q S T x y h
    induction h with
    | rel x y h => exact Relation.EqvGen.rel _ _ h.symm
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  exact ⟨key, key⟩

/-- A word satisfying both period constraints is constant on the classes of the period graph. -/
theorem PeriodJoined.eq_of_periodExcept {α : Type*} {L p : ℕ} {S : Finset ℤ} {Q : ℕ}
    {T : Finset ℤ} {f : ℤ → α} (hp : PeriodExcept L p S f) (hQ : PeriodExcept L Q T f)
    {x y : ℤ} (h : PeriodJoined L p S Q T x y) : f x = f y := by
  induction h with
  | rel x y h =>
    rcases h with h | h
    · exact periodExcept_iff_edges.1 hp x y h
    · exact periodExcept_iff_edges.1 hQ x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Universality of the period graph: two positions are joined exactly when every word satisfying
both constraints takes equal values there. -/
theorem periodJoined_iff_forall_word {L p : ℕ} {S : Finset ℤ} {Q : ℕ} {T : Finset ℤ}
    {x y : ℤ} :
    PeriodJoined L p S Q T x y ↔
      ∀ (α : Type) (f : ℤ → α), PeriodExcept L p S f → PeriodExcept L Q T f → f x = f y := by
  constructor
  · intro h α f hp hQ
    exact h.eq_of_periodExcept hp hQ
  · intro h
    have key := h (Quot fun a b => periodEdge L p S a b ∨ periodEdge L Q T a b)
      (fun z => Quot.mk _ z)
      (periodExcept_iff_edges.2 fun a b hab => Quot.sound (Or.inl hab))
      (periodExcept_iff_edges.2 fun a b hab => Quot.sound (Or.inr hab))
    exact Quot.eqvGen_exact key

/-- Edges of the period graph preserve the residue modulo the gcd of the two periods. -/
theorem PeriodJoined.gcd_dvd_sub {L p : ℕ} {S : Finset ℤ} {Q : ℕ} {T : Finset ℤ} {x y : ℤ}
    (h : PeriodJoined L p S Q T x y) : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x := by
  induction h with
  | rel x y h =>
    rcases h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · simpa using Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)
    · simpa using Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right p Q)
  | refl x => simp
  | symm x y _ ih => simpa using dvd_neg.2 ih
  | trans x y z _ _ ih1 ih2 => simpa using dvd_add ih2 ih1

end PeriodWords
end SkewGluing
