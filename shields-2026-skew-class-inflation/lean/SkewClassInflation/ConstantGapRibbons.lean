/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonDeterminants
import SkewClassInflation.NoOpening

/-!
# Faithful comparison with constant-gap ribbons

The equality comparison supplied by `eq:constant-gap-substitution`
in `shields-2026-skew-class-inflation.tex`.  Actual connected deflation
subtracts the common gap from every row; the resulting zero-gap ribbon
is identified with its full Jacobi--Trudi polynomial.  The original
Hessenberg condition prevents every opening under reinflation, including
at zero inner gap.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Inflating a zero-gap ribbon opens no negative entry if the inflated board is Hessenberg. -/
theorem zero_gap_noOpening_of_inflate_thick {n : ℕ} (R : Profile n) (t : ℕ)
    (hg : ∀ j, R.g j = 0) (hP : Staircase.Thick (Profile.inflate t R)) : NoOpening t R := by
  intro i j hij
  have hfar : j.val + 1 < i.val := by
    by_contra hn
    by_cases hle : i ≤ j
    · have ha := R.zeta_strictAnti.antitone hle
      have hb := R.xi_sub_zeta i
      have hp := R.r_pos i
      omega
    · have hji : j.val < i.val := lt_of_not_ge hle
      have hv : i.val = j.val + 1 := by omega
      let s : Fin n := ⟨j.val, by have := i.isLt; omega⟩
      have hi : s.succ = i := Fin.ext hv.symm
      have hj : s.castSucc = j := Fin.ext rfl
      have he := R.xi_succ_sub_zeta_castSucc s
      rw [hi, hj, hg s, Nat.cast_zero] at he
      omega
  have he := hP.hessenberg i j hfar
  rw [Profile.index_inflate] at he
  exact he

/-- Equal constant-gap Hessenberg functions are exactly equal ribbons after subtracting that gap.

The row-count correspondence is produced from the full determinant in each direction.

**Differs from the paper's route.** Lowering and no-opening reinflation prove
faithfulness without passing to the localization at the gap generator. -/
theorem constant_gap_equality_iff {n m : ℕ} (P : Profile n) (Q : Profile m) (c : ℕ)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (hrP : ∀ i, c < P.r i) (hrQ : ∀ i, c < Q.r i)
    (hgP : ∀ j, P.g j = c) (hgQ : ∀ j, Q.g j = c) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur ↔
      ribbonWord (List.ofFn (fun i => P.r i - c)) =
        ribbonWord (List.ofFn (fun i => Q.r i - c)) := by
  let canP : Profile.CanDeflate c P := ⟨hrP, fun j => by rw [hgP j]⟩
  let canQ : Profile.CanDeflate c Q := ⟨hrQ, fun j => by rw [hgQ j]⟩
  let R := Profile.deflate c P canP
  let S := Profile.deflate c Q canQ
  have hgR : ∀ j, R.g j = 0 := by intro j; change P.g j - c = 0; rw [hgP j, Nat.sub_self]
  have hgS : ∀ j, S.g j = 0 := by intro j; change Q.g j - c = 0; rw [hgQ j, Nat.sub_self]
  have hRP : Profile.inflate c R = P := Profile.inflate_deflate c P canP
  have hSQ : Profile.inflate c S = Q := Profile.inflate_deflate c Q canQ
  have hnoR : NoOpening c R := zero_gap_noOpening_of_inflate_thick R c hgR (by rw [hRP]; exact hP)
  have hnoS : NoOpening c S := zero_gap_noOpening_of_inflate_thick S c hgS (by rw [hSQ]; exact hQ)
  have hR : R.toBetaDiagram.schur = ribbonWord (List.ofFn (fun i => P.r i - c)) :=
    zero_gaps_ribbon_polynomial R hgR
  have hS : S.toBetaDiagram.schur = ribbonWord (List.ofFn (fun i => Q.r i - c)) :=
    zero_gaps_ribbon_polynomial S hgS
  constructor
  · intro he
    have hn := Nat.succ.inj (P.toBetaDiagram.row_count_of_schur_eq Q.toBetaDiagram he)
    subst m
    have hi : profileSchur (Profile.inflate c R) = profileSchur (Profile.inflate c S) := by
      rw [hRP, hSQ]
      simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using he
    have hh := profileSchur_eq_of_inflate_eq R S c hi
    have heR : R.toBetaDiagram.schur = S.toBetaDiagram.schur := by
      simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hh
    exact hR.symm.trans (heR.trans hS)
  · intro he
    have heR : R.toBetaDiagram.schur = S.toBetaDiagram.schur := hR.trans (he.trans hS.symm)
    have hn := Nat.succ.inj (R.toBetaDiagram.row_count_of_schur_eq S.toBetaDiagram heR)
    subst m
    have hi := inflate_eq_of_noOpening R S c hnoR hnoS
      (by simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using heR)
    rw [hRP, hSQ] at hi
    simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hi

end SkewClassInflation
