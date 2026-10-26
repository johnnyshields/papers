/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.NoOpening

/-!
# Connected classes across arbitrary row counts

Formalizes `eq:no-escape` and the permanence clause of
`cor:inflation-no-escape` in `shields-2026-skew-class-inflation.tex`.
A class ranges over all valid connected profiles of every row count;
row count is recovered from polynomial equality.  Sorry-free.
-/

namespace SkewClassInflation

/-- Connected diagrams up to literal translation, with arbitrary positive row count. -/
abbrev ConnectedProfile := (n : ℕ) × Profile n

namespace ConnectedProfile

/-- The actual Schur determinant of a connected translation class. -/
noncomputable def schur (D : ConnectedProfile) : SkewJacobiNegative.CompleteRing :=
  profileSchur D.2

/-- Inflation on the disjoint union of all row counts. -/
def inflate (t : ℕ) (D : ConnectedProfile) : ConnectedProfile :=
  ⟨D.1, Profile.inflate t D.2⟩

/-- Global rotation reverses both complete profile words. -/
def rotate (D : ConnectedProfile) : ConnectedProfile := ⟨D.1, D.2.rotate⟩

/-- The full class contains every connected mate, not merely profiles of a fixed order. -/
noncomputable def schurClass (D : ConnectedProfile) : Set ConnectedProfile :=
  {H | H.schur = D.schur}

/-- Inflation is injective even when row count has not been fixed in advance. -/
theorem inflate_injective (t : ℕ) : Function.Injective (inflate t) := by
  rintro ⟨n, P⟩ ⟨m, Q⟩ h
  have hn := congrArg Sigma.fst h
  change n = m at hn
  subst m
  have hp : Profile.inflate t P = Profile.inflate t Q := eq_of_heq (Sigma.mk.inj h).2
  have he := Profile.inflate_injective t hp
  cases he
  rfl

/-- Inflation and global rotation commute on actual connected translation classes. -/
theorem inflate_rotate (t : ℕ) (D : ConnectedProfile) :
    (inflate t D).rotate = inflate t D.rotate := by
  rcases D with ⟨n, P⟩
  rfl

/-- Whole-profile reversal preserves the actual Schur function. -/
theorem schur_rotate (D : ConnectedProfile) : D.rotate.schur = D.schur := by
  rcases D with ⟨n, P⟩
  exact (profileSchur_eq_inherited P.rotate).trans
    (P.schur_rotate.trans (profileSchur_eq_inherited P).symm)

/-- Global rotation is an involution on complete connected translation classes. -/
theorem rotate_rotate (D : ConnectedProfile) : D.rotate.rotate = D := by
  rcases D with ⟨n, P⟩
  change (⟨n, P.rotate.rotate⟩ : ConnectedProfile) = ⟨n, P⟩
  rw [SkewJacobiNegative.Gluing.Profile.rotate_rotate]

/-- A rotated source has the identical unrestricted connected Schur class. -/
theorem schurClass_rotate (D : ConnectedProfile) : D.rotate.schurClass = D.schurClass := by
  ext H
  change (H.schur = D.rotate.schur) ↔ H.schur = D.schur
  rw [schur_rotate]

/-- Every arbitrary connected inflated mate is the inflation of an original connected mate. -/
theorem inflation_no_escape (D : ConnectedProfile) (t : ℕ) :
    (inflate t D).schurClass ⊆ inflate t '' D.schurClass := by
  rcases D with ⟨n, P⟩
  rintro ⟨m, Q⟩ h
  obtain ⟨R, he, hr⟩ := mate_deflation P Q t h
  refine ⟨⟨m, R⟩, hr, ?_⟩
  change (⟨m, Profile.inflate t R⟩ : ConnectedProfile) = ⟨m, Q⟩
  rw [he]

/-- Lost equality cannot return, with no same-row-count premise on the two diagrams. -/
theorem equality_at_earlier (D E : ConnectedProfile) {s t : ℕ} (hst : s ≤ t)
    (h : (inflate t D).schur = (inflate t E).schur) :
    (inflate s D).schur = (inflate s E).schur := by
  rcases D with ⟨n, P⟩
  rcases E with ⟨m, Q⟩
  have hn := (profile_invariants (Profile.inflate t P) (Profile.inflate t Q) h).1
  subst m
  exact equality_at_earlier_inflation P Q hst h

/-- All original mates survive exactly when none of their negative entries opens. -/
theorem class_transport_of_noOpening (D : ConnectedProfile) (t : ℕ)
    (h : ∀ E ∈ D.schurClass, NoOpening t E.2) :
    (inflate t D).schurClass = inflate t '' D.schurClass := by
  apply Set.Subset.antisymm (inflation_no_escape D t)
  rintro _ ⟨E, he, rfl⟩
  rcases D with ⟨n, P⟩
  rcases E with ⟨m, Q⟩
  have hn := (profile_invariants Q P he).1
  subst m
  exact inflate_eq_of_noOpening Q P t (h ⟨n, Q⟩ he) (h ⟨n, P⟩ rfl) he

end ConnectedProfile
end SkewClassInflation
