/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinPowers
import SkewClassInflation.PrivateShortestRow
import SkewClassInflation.InflationClasses

/-!
# Complete rigidity of the thin powers

Formalizes `lem:two-row-power-rigidity` and `eq:short-row-coefficient`
in `shields-2026-skew-class-inflation.tex`.  An arbitrary connected mate
is recognized from the actual polynomial.  Its unique shortest row must
lie at an endpoint, and the two-observation boundary inverse recovers the
entire ordered profile after one global rotation.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Normalized profile beta lists turn common translation into literal profile equality. -/
theorem profile_eq_of_beta_translation {n : ℕ} (P Q : Profile n)
    (h : P.toBetaDiagram.TranslationEquivalent Q.toBetaDiagram) : P = Q := by
  obtain ⟨c, hr, hc⟩ := h
  have hc0 := hc (Fin.last n)
  change P.zeta (Fin.last n) = Q.zeta (Fin.last n) + c at hc0
  rw [P.zeta_last, Q.zeta_last] at hc0
  have hz : c = 0 := by omega
  apply Gluing.Profile.eq_of_beta_eq
  · funext i
    have h := hr i
    change P.xi i = Q.xi i + c at h
    simpa only [hz, add_zero] using h
  · funext i
    have h := hc i
    change P.zeta i = Q.zeta i + c at h
    simpa only [hz, add_zero] using h

namespace ThinParameters

variable (B : ThinParameters)

/-- The positive complete-generator index of the private shortest row. -/
def shortestGenerator : ℕ+ := ⟨B.a, by have := B.c_pos; have := B.c_lt_a; omega⟩

/-- The shortest-row derivative of the source is exactly its connected first-row deletion. -/
theorem innerPower_shortest_coefficient (m : ℕ) (hm : 0 < m) :
    MvPolynomial.pderiv B.shortestGenerator (B.innerPower m hm).toBetaDiagram.schur =
      (firstRowTail (B.innerPower m hm).toBetaDiagram).schur := by
  apply shortest_first_row_coefficient _ (B.innerPower_thick m hm)
  · rfl
  · intro i; exact (B.innerPower_shortest m hm i).1
  · intro i hi; exact (B.innerPower_shortest m hm i).2.mp hi
  · intro j
    change B.c ≠ B.a
    have := B.c_lt_a
    omega

/-- Recognition supplies every geometric fact needed at an arbitrary equal profile. -/
theorem innerPower_mate_data (m : ℕ) (hm : 0 < m) (Q : Profile m)
    (he : Q.toBetaDiagram.schur = (B.innerPower m hm).toBetaDiagram.schur) :
    Staircase.Thick Q ∧ (∀ i, B.a ≤ Q.r i) ∧
      (∃! r, Q.r r = B.a) ∧ (∀ j, Q.g j = B.c) := by
  let P := B.innerPower m hm
  have hp : P.toBetaDiagram.schur = Q.toBetaDiagram.schur := he.symm
  have hQ : Staircase.Thick Q := by
    apply GeneralHessenberg.hessenberg_thick
    exact hessenberg_of_equal_schur P.toBetaDiagram Q.toBetaDiagram
      P.toBetaDiagram_connected Q.toBetaDiagram_connected hp (B.innerPower_thick m hm).hessenberg
  have he' : Q.schur = P.schur := by
    simpa only [Gluing.Profile.toBetaDiagram_schur] using he
  have hrows := (Gluing.Profile.rows_eq_of_schur_eq he').2
  have hgaps := Gluing.Profile.gaps_eq_of_schur_eq he'
  have hmin : ∀ i, B.a ≤ Q.r i := by
    intro i
    have hx : Q.r i ∈ P.rowMultiset := by
      rw [← hrows]
      exact Gluing.Profile.mem_rowMultiset.mpr ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := Gluing.Profile.mem_rowMultiset.mp hx
    rw [← hj]
    exact (B.innerPower_shortest m hm j).1
  have hcount : P.rowMultiset.count B.a = 1 := by
    rw [Gluing.Profile.rowMultiset, Multiset.count_map]
    change (Finset.univ.filter (fun i : Fin (m + 1) => B.a = P.r i)).card = 1
    have hf : Finset.univ.filter (fun i : Fin (m + 1) => B.a = P.r i) = {0} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact eq_comm.trans (B.innerPower_shortest m hm i).2
    rw [hf]
    exact Finset.card_singleton _
  have hcard : (Finset.univ.filter (fun i : Fin (m + 1) => B.a = Q.r i)).card = 1 := by
    have hh := congrArg (Multiset.count B.a) hrows
    rw [hcount] at hh
    simpa only [Gluing.Profile.rowMultiset, Multiset.count_map,
      ← Finset.filter_val, Finset.card_val] using hh
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard
  have hrr : Q.r r = B.a := by
    have hx : r ∈ Finset.univ.filter (fun i : Fin (m + 1) => B.a = Q.r i) := by
      rw [hr]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hx).2.symm
  refine ⟨hQ, hmin, ⟨r, hrr, ?_⟩, ?_⟩
  · intro i hi
    have hx : i ∈ Finset.univ.filter (fun i : Fin (m + 1) => B.a = Q.r i) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.symm⟩
    rw [hr] at hx
    exact Finset.mem_singleton.mp hx
  · intro j
    have hx : Q.g j ∈ P.gapMultiset := by
      rw [← hgaps]
      exact Gluing.Profile.mem_gapMultiset.mpr ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := Gluing.Profile.mem_gapMultiset.mp hx
    exact hk.symm

/-- A mate with the shortest row first is the literal original block. -/
theorem innerPower_first_mate_eq (m : ℕ) (hm : 0 < m) (Q : Profile m)
    (he : Q.toBetaDiagram.schur = (B.innerPower m hm).toBetaDiagram.schur)
    (hfirst : Q.r 0 = B.a) : Q = B.innerPower m hm := by
  obtain ⟨hQ, hmin, hunique, hgaps⟩ := B.innerPower_mate_data m hm Q he
  have hun : ∀ i, Q.r i = B.a → i = 0 := by
    obtain ⟨r, hr, hu⟩ := hunique
    intro i hi
    exact (hu i hi).trans (hu 0 hfirst).symm
  have hgap : ∀ j, Q.g j ≠ B.a := by
    intro j; rw [hgaps j]; have := B.c_lt_a; omega
  have hcoef := shortest_first_row_coefficient Q hQ B.shortestGenerator hfirst hmin hun hgap
  have htail : (firstRowTail Q.toBetaDiagram).schur =
      (firstRowTail (B.innerPower m hm).toBetaDiagram).schur := by
    rw [← hcoef, he, B.innerPower_shortest_coefficient]
  exact profile_eq_of_beta_translation Q _
    (boundary_reconstruction Q.toBetaDiagram (B.innerPower m hm).toBetaDiagram
      Q.toBetaDiagram_connected (B.innerPower m hm).toBetaDiagram_connected he htail)

/-- Every connected mate of a thin power is the original literal profile or its rotation. -/
theorem innerPower_rigidity (m : ℕ) (hm : 0 < m) (Q : Profile m)
    (he : Q.toBetaDiagram.schur = (B.innerPower m hm).toBetaDiagram.schur) :
    Q = B.innerPower m hm ∨ Q = (B.innerPower m hm).rotate := by
  obtain ⟨hQ, hmin, ⟨r, hr, hu⟩, hgaps⟩ := B.innerPower_mate_data m hm Q he
  have hgap : ∀ j, Q.g j ≠ B.a := by
    intro j; rw [hgaps j]; have := B.c_lt_a; omega
  have huniq : ∀ i, Q.r i = B.a → i = r := hu
  obtain ⟨heq, hprivate⟩ := shortest_row_private Q hQ B.shortestGenerator r hr hmin huniq hgap
  have hcoef : Irreducible (MvPolynomial.pderiv B.shortestGenerator Q.toBetaDiagram.schur) := by
    rw [he, B.innerPower_shortest_coefficient]
    exact (firstRowTail (B.innerPower m hm).toBetaDiagram).schur_irreducible
      (B.innerPower_tail_connected m hm)
  have hb := private_irreducible_row_boundary Q.toBetaDiagram hQ.hessenberg
    B.shortestGenerator r heq hprivate hcoef
  rcases hb with hb | hb
  · left
    apply B.innerPower_first_mate_eq m hm Q he
    simpa only [hb] using hr
  · right
    have heR : Q.rotate.toBetaDiagram.schur = (B.innerPower m hm).toBetaDiagram.schur := by
      rw [Gluing.Profile.toBetaDiagram_schur, Gluing.Profile.schur_rotate,
        ← Gluing.Profile.toBetaDiagram_schur Q, he]
    have hf : Q.rotate.r 0 = B.a := by
      change Q.r (0 : Fin (m + 1)).rev = B.a
      simpa only [Fin.rev_zero, hb] using hr
    have hh := B.innerPower_first_mate_eq m hm Q.rotate heR hf
    have hh' := congrArg Gluing.Profile.rotate hh
    simpa only [Gluing.Profile.rotate_rotate] using hh'

/-- Across every positive row count, the full class consists of the two global orientations. -/
theorem innerPower_full_class (m : ℕ) (hm : 0 < m) :
    let D : ConnectedProfile := ⟨m, B.innerPower m hm⟩
    D.schurClass = {D, D.rotate} := by
  dsimp only
  apply Set.ext
  rintro ⟨k, Q⟩
  constructor
  · intro he
    change profileSchur Q = profileSchur (B.innerPower m hm) at he
    have hn := (profile_invariants Q (B.innerPower m hm) he).1
    subst k
    have hs : Q.toBetaDiagram.schur = (B.innerPower m hm).toBetaDiagram.schur := by
      simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using he
    rcases B.innerPower_rigidity m hm Q hs with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl (congrArg (Sigma.mk m) h))
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (congrArg (Sigma.mk m) h))
  · intro he
    rcases Set.mem_insert_iff.mp he with he | he
    · rw [he]
      rfl
    · rw [Set.mem_singleton_iff.mp he]
      exact ConnectedProfile.schur_rotate _

end ThinParameters
end SkewClassInflation
