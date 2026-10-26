/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.Gluing.RowInvariants
import SkewMarkedFactor.Gluing.CellSchur

/-!
# Connected two-row Schur classes

The rigidity input in `cor:two-row` of
`shields-2026-skew-marked-factor.tex`.
The mate is an arbitrary connected skew diagram.  Row invariance first forces
its number of rows; gap invariance includes a zero overlap-minus-one.
-/

namespace SkewMarkedFactor
open Gluing

namespace Gluing.Profile

/-- A Schur-equal two-row profile has the same ordered rows or their reversal. -/
theorem eq_or_rotate_of_two_row_schur_eq {P Q : Profile 1}
    (h : Q.schur = P.schur) : Q = P ∨ Q = P.rotate := by
  classical
  have hr := (rows_eq_of_schur_eq h).2
  have hg := gaps_eq_of_schur_eq h
  have hg0 : Q.g 0 = P.g 0 := by
    change ({Q.g 0} : Multiset ℕ) = {P.g 0} at hg
    simpa using hg
  have hsum : Q.r 0 + Q.r 1 = P.r 0 + P.r 1 := by
    have hs := congrArg Multiset.sum hr
    change Q.r 0 + Q.r 1 + 0 = P.r 0 + P.r 1 + 0 at hs
    omega
  have hm : Q.r 0 ∈ P.rowMultiset := by
    rw [← hr]
    exact mem_rowMultiset.mpr ⟨0, rfl⟩
  have hm' : Q.r 0 = P.r 0 ∨ Q.r 0 = P.r 1 := by
    change Q.r 0 ∈ ({P.r 0, P.r 1} : Multiset ℕ) at hm
    simpa using hm
  rcases hm' with h0 | h0
  · left
    apply Profile.ext
    · funext i
      fin_cases i
      · exact h0
      · change Q.r 1 = P.r 1
        omega
    · funext i
      fin_cases i
      exact hg0
  · right
    apply Profile.ext
    · funext i
      fin_cases i
      · simpa [Profile.rotate] using h0
      · have h1 : Q.r 1 = P.r 0 := by omega
        simpa [Profile.rotate] using h1
    · funext i
      fin_cases i
      simpa [Profile.rotate] using hg0

/-- The mate may initially have any positive number of rows. -/
theorem two_row_classification {n : ℕ} {Q : Profile n} {P : Profile 1}
    (h : Q.schur = P.schur) :
    (⟨n, Q⟩ : AnyProfile) = ⟨1, P⟩ ∨
      (⟨n, Q⟩ : AnyProfile) = ⟨1, P.rotate⟩ := by
  have hn : n = 1 := (rows_eq_of_schur_eq h).1
  subst n
  rcases eq_or_rotate_of_two_row_schur_eq h with hQ | hQ
  · exact Or.inl (by rw [hQ])
  · exact Or.inr (by rw [hQ])

end Gluing.Profile

/-- Every connected Schur mate of a two-row inner is a translate or a transported rotation. -/
theorem two_row_inner_rigidity {E U : Diagram} (hE : IsConnectedSkew E)
    (hrows : numRows E = 2) (hU : IsConnectedSkew U)
    (hs : cellSchur U = cellSchur E) :
    (∃ t, U = translate t E) ∨ ∃ t, U = translate t (rotate E) := by
  have hn : (cellProfile E).1 = 1 := by
    have h := (cellProfile_spec hE).1
    omega
  rcases he : cellProfile E with ⟨n, P⟩
  simp only [he] at hn
  change n = 1 at hn
  subst n
  have hsp : (cellProfile U).2.schur = P.schur := by
    rw [cellSchur_of_isConnectedSkew hU, cellSchur_of_isConnectedSkew hE] at hs
    have hv : (cellProfile E).2.schur = P.schur :=
      congrArg (fun A : AnyProfile => A.2.schur) he
    exact hs.trans hv
  rcases Profile.two_row_classification hsp with hP | hP
  · left
    exact exists_translate_of_cellProfile_eq hE hU (by rw [he]; exact hP.symm)
  · right
    apply exists_translate_of_cellProfile_eq (isConnectedSkew_rotate hE) hU
    rw [cellProfile_rotate hE, he]
    exact hP.symm

end SkewMarkedFactor
