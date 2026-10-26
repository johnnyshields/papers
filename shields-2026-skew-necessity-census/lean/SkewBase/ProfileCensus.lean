import SkewBase.Census
import SkewBase.JacobiTrudiEval
import SkewBase.Copied.RowInvariants
import SkewBase.RowOverlaps

/-!
# The census over connected diagrams given by profiles

Formalizes `shields-2026-skew-base-computational.tex`, «The census» (`sec:census`), `thm:census`,
for connected diagrams presented by their profiles (`lem:profiles`).

`SkewBase.census_eq` is instantiated at `AnyProfile`, the connected diagrams of any number of
rows: the shard is the row multiset, the invariant `I` is the sequence of all row overlap
partitions `ρ^{(k)}`, `k ≥ 1`, the polynomial is `schurZ` over `ℤ`, rotation is the reversal of
the profile, and the two evaluations are `evalAt η₁`, `evalAt η₂` at arbitrary points of
arbitrary commutative rings (in the paper, `𝔽_p` and `𝔽_{p'}`).

The invariance hypothesis of `census_eq` is discharged by `SkewGluing.Profile.rows_eq_of_schur_eq`
(the row multiset) and `SkewGluing.Profile.rowOverlapPartition_eq_of_schur_eq` (every
`ρ^{(k)}`, `Reiner–Shaw–van Willigenburg, Cor. 8.11`), and rotation invariance by
`Profile.schur_rotate`.  The theorem is unconditional.

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-- A connected diagram, by its profile, with any number of rows. -/
abbrev AnyProfile : Type := Σ n : ℕ, Profile n

namespace AnyProfile

/-- Rotation through `180` degrees: reverse the profile. -/
def rotate (G : AnyProfile) : AnyProfile := ⟨G.1, G.2.rotate⟩

/-- The skew Schur function `s_F ∈ ℤ[h₁, h₂, …]`. -/
noncomputable def schur (G : AnyProfile) : LambdaZ := schurZ G.2

/-- The shard of a profile: its multiset of row lengths. -/
def shard (G : AnyProfile) : Multiset ℕ := G.2.rowMultiset

/-- The invariant `I` of a profile: the sequence of its row overlap partitions `ρ^{(k)}`,
`k ≥ 1`, the numbers of columns shared by `k` consecutive rows (with zeros).  The first is the
row multiset and the second is the multiset of gaps plus one. -/
def invariant (G : AnyProfile) : ℕ+ → Multiset ℕ := fun k => G.2.rowOverlapPartition k

theorem rotate_rotate (G : AnyProfile) : G.rotate.rotate = G := by
  obtain ⟨n, P⟩ := G
  simp [rotate]

theorem schur_rotate (G : AnyProfile) : G.rotate.schur = G.schur := schurZ_rotate G.2

/-- Schur-equal connected diagrams have the same row multiset and the same row overlap
partitions `ρ^{(k)}` for every `k ≥ 1`. -/
theorem shard_invariant_eq {G H : AnyProfile} (h : G.schur = H.schur) :
    G.shard = H.shard ∧ G.invariant = H.invariant := by
  have h' := (schurZ_eq_iff G.2 H.2).mp h
  exact ⟨(Profile.rows_eq_of_schur_eq h').2,
    funext fun k => Profile.rowOverlapPartition_eq_of_schur_eq h' k⟩

end AnyProfile

open scoped Classical in
/-- **`thm:census`, for profiles.**  For every finite rotation-closed set `U` of connected
diagrams, the parts reported by the census, with the evaluations at any two points `η₁`, `η₂` of
any two commutative rings, are exactly the Schur classes `{H ∈ U | s_H = s_G}`.  The
representatives are any choice `canon x ∈ {x, x*}`, for instance the lexicographically smaller. -/
theorem census_eq_schurClasses {S₁ S₂ : Type*} [CommRing S₁] [CommRing S₂] (η₁ : ℕ → S₁)
    (η₂ : ℕ → S₂) (canon : AnyProfile → AnyProfile)
    (hcanon : ∀ x, canon x = x ∨ canon x = x.rotate) (U : Finset AnyProfile)
    (hU : ∀ x ∈ U, x.rotate ∈ U) :
    census AnyProfile.rotate canon AnyProfile.shard AnyProfile.invariant AnyProfile.schur
      (evalAt η₁) (evalAt η₂) U = U.image fun x => U.filter fun y => y.schur = x.schur :=
  census_eq _ _ _ _ _ _ _ U AnyProfile.rotate_rotate AnyProfile.schur_rotate hcanon
    (fun _ _ h => AnyProfile.shard_invariant_eq h) hU

end SkewBase
