/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.Lowering
import SkewJacobiNegative.RepresentationBridges

/-!
# No escape and permanent loss under inflation

Formalizes `cor:inflation-no-escape` in
`shields-2026-skew-class-inflation.tex`.  Row count and the row and gap
multisets are produced from actual Schur equality before the full-board
lowering theorem is used.  No hypothesis requires a mate to arrive with a
deflation or with a prescribed row count.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Entrywise identification with the copied profile Schur representation. -/
theorem profileSchur_eq_inherited {n : ℕ} (P : Profile n) : profileSchur P = P.schur := by
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  exact complete_eq_hh _

/-- Row count and both padded multisets are read from the actual polynomial. -/
theorem profile_invariants {n m : ℕ} (P : Profile n) (Q : Profile m)
    (h : profileSchur P = profileSchur Q) :
    n = m ∧ P.rowMultiset = Q.rowMultiset := by
  exact Gluing.Profile.rows_eq_of_schur_eq
    (by simpa only [profileSchur_eq_inherited] using h)

/-- An arbitrary connected mate of an inflated profile has an actual connected deflation. -/
theorem mate_deflation {n m : ℕ} (P : Profile n) (Q : Profile m) (t : ℕ)
    (h : profileSchur Q = profileSchur (Profile.inflate t P)) :
    ∃ R : Profile m, Profile.inflate t R = Q ∧ profileSchur R = profileSchur P := by
  have hi := profile_invariants Q (Profile.inflate t P) h
  obtain rfl := hi.1
  have hg : Q.gapMultiset = (Profile.inflate t P).gapMultiset :=
    Gluing.Profile.gaps_eq_of_schur_eq
      (by simpa only [profileSchur_eq_inherited] using h)
  have hd : Profile.CanDeflate t Q := by
    constructor
    · intro i
      have hm : Q.r i ∈ (Profile.inflate t P).rowMultiset := by
        rw [← hi.2]
        exact Gluing.Profile.mem_rowMultiset.mpr ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := Gluing.Profile.mem_rowMultiset.mp hm
      have := P.r_pos j
      simp only [Profile.inflate_r] at hj
      omega
    · intro i
      have hm : Q.g i ∈ (Profile.inflate t P).gapMultiset := by
        rw [← hg]
        exact Gluing.Profile.mem_gapMultiset.mpr ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := Gluing.Profile.mem_gapMultiset.mp hm
      simp only [Profile.inflate_g] at hj
      omega
  refine ⟨Profile.deflate t Q hd, Profile.inflate_deflate t Q hd, ?_⟩
  apply profileSchur_eq_of_inflate_eq _ _ t
  simpa only [Profile.inflate_deflate] using h

/-- No equality lost at an earlier parameter can return at a later integer parameter. -/
theorem equality_at_earlier_inflation {n : ℕ} (P Q : Profile n) {s t : ℕ}
    (hst : s ≤ t)
    (h : profileSchur (Profile.inflate t P) = profileSchur (Profile.inflate t Q)) :
    profileSchur (Profile.inflate s P) = profileSchur (Profile.inflate s Q) := by
  apply profileSchur_eq_of_inflate_eq _ _ (t - s)
  simpa only [Profile.inflate_add, Nat.sub_add_cancel hst] using h

/-- Once unequal, two inflated functions stay unequal for all larger parameters. -/
theorem inequality_persists {n : ℕ} (P Q : Profile n) {s t : ℕ} (hst : s ≤ t)
    (h : profileSchur (Profile.inflate s P) ≠ profileSchur (Profile.inflate s Q)) :
    profileSchur (Profile.inflate t P) ≠ profileSchur (Profile.inflate t Q) :=
  fun he => h (equality_at_earlier_inflation P Q hst he)

end SkewClassInflation
