/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.ProfileStatistics
import Mathlib.Data.List.FinRange

/-!
# Complete finite enumeration of connected row profiles by area

Supports `shields-2026-skew-corner-descent.tex` (`rem:ordinary-gauge`).
Positive row lengths and their actual adjacent overlap bounds give a finite
recursive enumeration at each area. The data are genuine profiles, not
unchecked row codes or independently chosen cell sets. Sorry-free.
-/

namespace SkewCornerDescent
open SkewGluing
open scoped BigOperators

/-- The area from the complete positive row list of a profile. -/
def profileArea {n : ℕ} (P : Profile n) : ℕ := ∑ i, P.r i

/-- A genuine single-row profile of positive length. -/
def singleRowProfile (r : ℕ+) : Profile 0 where
  r := fun _ => r
  g := Fin.elim0
  r_pos := fun _ => r.pos
  g_lt_castSucc := fun i => Fin.elim0 i
  g_lt_succ := fun i => Fin.elim0 i

/-- Prepend one actual row, with its bounded adjacent overlap. -/
def prependRowProfile {n : ℕ} (r : ℕ+) (P : Profile n)
    (g : Fin (min (r : ℕ) (P.r 0))) : Profile (n+1) where
  r := Fin.cons r P.r
  g := Fin.cons g.val P.g
  r_pos := Fin.cases r.pos P.r_pos
  g_lt_castSucc := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change g.val < (r : ℕ)
      exact lt_of_lt_of_le g.isLt (Nat.min_le_left _ _)
    · change P.g i < P.r i.castSucc
      exact P.g_lt_castSucc i
  g_lt_succ := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change g.val < P.r 0
      exact lt_of_lt_of_le g.isLt (Nat.min_le_right _ _)
    · change P.g i < P.r i.succ
      exact P.g_lt_succ i

/-- Delete the first row and its adjacent overlap. -/
def tailRowProfile {n : ℕ} (P : Profile (n + 1)) : Profile n where
  r := fun i => P.r i.succ
  g := fun i => P.g i.succ
  r_pos := fun i => P.r_pos i.succ
  g_lt_castSucc := fun i => P.g_lt_castSucc i.succ
  g_lt_succ := fun i => P.g_lt_succ i.succ

/-- Every actual row profile has positive area. -/
theorem profileArea_pos {n : ℕ} (P : Profile n) : 0 < profileArea P := by
  have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => Nat.zero_le (P.r i))
    (Finset.mem_univ (0 : Fin (n+1)))
  exact (P.r_pos 0).trans_le hle

/-- The first-row decomposition retains exactly every cell of the row list. -/
theorem profileArea_tail {n : ℕ} (P : Profile (n + 1)) :
    profileArea P = P.r 0 + profileArea (tailRowProfile P) := by
  exact Fin.sum_univ_succ P.r

/-- A single row has exactly its stated area. -/
theorem profileArea_single (r : ℕ+) : profileArea (singleRowProfile r) = r := by
  simp [profileArea, singleRowProfile]

/-- Prepending adds exactly the complete new row length. -/
theorem profileArea_prepend {n : ℕ} (r : ℕ+) (P : Profile n)
    (g : Fin (min (r : ℕ) (P.r 0))) :
    profileArea (prependRowProfile r P g) = r + profileArea P := by
  simp only [profileArea, prependRowProfile, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- The original first row and overlap reconstruct the whole actual profile. -/
theorem prepend_tailRowProfile {n : ℕ} (P : Profile (n + 1)) :
    prependRowProfile ⟨P.r 0, P.r_pos 0⟩ (tailRowProfile P)
      ⟨P.g 0, lt_min (P.g_lt_castSucc 0) (P.g_lt_succ 0)⟩ = P := by
  apply Profile.ext
  · funext i
    exact Fin.cases rfl (fun _ => rfl) i
  · funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- Structurally recursive row fuel bounds the number of rows. Area is
tracked separately, so kernel reduction traverses no well-founded proofs. -/
def profilesWithFuel : ℕ → ℕ → List (Σ n, Profile n)
  | 0, _ => []
  | _+1, 0 => []
  | fuel+1, A+1 =>
    [⟨0, singleRowProfile ⟨A+1, by omega⟩⟩] ++
      (List.range A).flatMap (fun r =>
        (profilesWithFuel fuel (A-r)).flatMap (fun p =>
          (List.finRange (min (r+1) (p.2.r 0))).map (fun g =>
            ⟨p.1+1, prependRowProfile ⟨r+1, by omega⟩ p.2 g⟩)))

/-- All actual connected row profiles of one prescribed positive area. -/
def profilesOfArea (A : ℕ) : List (Σ n, Profile n) := profilesWithFuel A A

/-- Positive actual row lengths bound the number of rows by the area. -/
theorem profileRows_le_area {n : ℕ} (P : Profile n) : n+1 ≤ profileArea P := by
  have h : (∑ _ : Fin (n+1), (1 : ℕ)) ≤ ∑ i, P.r i :=
    Finset.sum_le_sum (fun i _ => P.r_pos i)
  simpa only [profileArea, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, mul_one] using h

/-- Row fuel above the actual row count retains every genuine profile. -/
theorem profile_mem_profilesWithFuel {n : ℕ} (P : Profile n) (fuel : ℕ) (hf : n ≤ fuel) :
    (⟨n, P⟩ : Σ n, Profile n) ∈ profilesWithFuel (fuel+1) (profileArea P) := by
  induction n generalizing fuel with
  | zero =>
    let A := profileArea P - 1
    have harea : profileArea P = A+1 := by have := profileArea_pos P; omega
    have hrow : profileArea P = P.r 0 := by simp [profileArea]
    have he : singleRowProfile ⟨A+1, by omega⟩ = P := by
      apply Profile.ext
      · funext i
        have hi : i = 0 := Fin.fin_one_eq_zero i
        subst i
        change A+1 = P.r 0
        omega
      · funext i
        exact Fin.elim0 i
    rw [harea, profilesWithFuel]
    apply List.mem_append.mpr
    apply Or.inl
    simpa only [List.mem_singleton] using congrArg (Sigma.mk 0) he.symm
  | succ n ih =>
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
    let Q := tailRowProfile P
    let A := profileArea P - 1
    let R := P.r 0 - 1
    have harea : profileArea P = A+1 := by have := profileArea_pos P; omega
    have htail : 0 < profileArea Q := profileArea_pos Q
    have hdecomp := profileArea_tail P
    change profileArea P = P.r 0 + profileArea Q at hdecomp
    have hhead : P.r 0 = R+1 := by have := P.r_pos 0; omega
    have hR : R < A := by omega
    have htailArea : A-R = profileArea Q := by omega
    have hgap : P.g 0 < min (R+1) (Q.r 0) := by
      have h := lt_min (P.g_lt_castSucc 0) (P.g_lt_succ 0)
      change P.g 0 < min (P.r 0) (Q.r 0) at h
      rwa [hhead] at h
    let g : Fin (min (R+1) (Q.r 0)) := ⟨P.g 0, hgap⟩
    have he : prependRowProfile ⟨R+1, by omega⟩ Q g = P := by
      apply Profile.ext
      · funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        change R+1 = P.r 0
        omega
      · funext i
        exact Fin.cases rfl (fun _ => rfl) i
    rw [harea, profilesWithFuel]
    apply List.mem_append.mpr
    apply Or.inr
    apply List.mem_flatMap.mpr
    refine ⟨R, List.mem_range.mpr hR, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨⟨n, Q⟩, ?_, ?_⟩
    · rw [htailArea]
      exact ih Q fuel (by omega)
    · apply List.mem_map.mpr
      exact ⟨g, by simp, congrArg (Sigma.mk (n+1)) he⟩

/-- Every actual row profile occurs in its exact-area enumeration. -/
theorem profile_mem_profilesOfArea {n : ℕ} (P : Profile n) :
    (⟨n, P⟩ : Σ n, Profile n) ∈ profilesOfArea (profileArea P) := by
  have hrows := profileRows_le_area P
  have hm := profile_mem_profilesWithFuel P (profileArea P-1) (by omega)
  have he : profileArea P-1+1 = profileArea P := by have := profileArea_pos P; omega
  rw [he] at hm
  exact hm

/-- Every structurally enumerated profile has exactly its advertised area. -/
theorem mem_profilesWithFuel_area (fuel A : ℕ) (p : Σ n, Profile n)
    (hp : p ∈ profilesWithFuel fuel A) : profileArea p.2 = A := by
  induction fuel generalizing A p with
  | zero => simp only [profilesWithFuel, List.not_mem_nil] at hp
  | succ fuel ih =>
    cases A with
    | zero => simp only [profilesWithFuel, List.not_mem_nil] at hp
    | succ A =>
      rw [profilesWithFuel] at hp
      rcases List.mem_append.mp hp with hs | hs
      · have he := List.mem_singleton.mp hs
        subst p
        exact profileArea_single _
      · obtain ⟨r, hr, hs⟩ := List.mem_flatMap.mp hs
        obtain ⟨q, hq, hs⟩ := List.mem_flatMap.mp hs
        obtain ⟨g, _, rfl⟩ := List.mem_map.mp hs
        have hqArea := ih (A-r) q hq
        have hrA := List.mem_range.mp hr
        change profileArea (prependRowProfile (⟨r+1, by omega⟩ : ℕ+) q.2 g) = A+1
        exact (profileArea_prepend (⟨r+1, by omega⟩ : ℕ+) q.2 g).trans (by
          change r+1 + profileArea q.2 = A+1
          omega)

/-- No profile of a different area enters the exact-area enumeration. -/
theorem mem_profilesOfArea_area {A : ℕ} (p : Σ n, Profile n)
    (hp : p ∈ profilesOfArea A) : profileArea p.2 = A :=
  mem_profilesWithFuel_area A A p hp

/-- Complete actual profiles through a prescribed area bound. -/
def profilesAtMost (A : ℕ) : List (Σ n, Profile n) :=
  (List.range (A+1)).flatMap profilesOfArea

/-- An area bound on an actual profile places it in the bounded census. -/
theorem profile_mem_profilesAtMost {n A : ℕ} (P : Profile n) (hA : profileArea P ≤ A) :
    (⟨n, P⟩ : Σ n, Profile n) ∈ profilesAtMost A := by
  apply List.mem_flatMap.mpr
  exact ⟨profileArea P, List.mem_range.mpr (by omega), profile_mem_profilesOfArea P⟩

/-- Every profile in the bounded census satisfies the bound it advertises. -/
theorem mem_profilesAtMost_area {A : ℕ} (p : Σ n, Profile n)
    (hp : p ∈ profilesAtMost A) : profileArea p.2 ≤ A := by
  obtain ⟨k, hk, hp⟩ := List.mem_flatMap.mp hp
  have he := mem_profilesOfArea_area p hp
  have hkA := List.mem_range.mp hk
  omega

/-- The enumerated row area is the actual number of cells, with disjoint
rows and every cell of each interval retained. -/
theorem profileArea_eq_card {n : ℕ} (P : Profile n) : profileArea P = P.cells.card := by
  symm
  unfold Profile.cells
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_image_of_injective _ (fun a b he => (Prod.mk.inj he).2), Int.card_Ico]
    have he : P.xi i + (i : ℤ) - (P.zeta i + (i : ℤ)) = (P.r i : ℤ) := by
      have h := P.xi_sub_zeta i
      omega
    rw [he, Int.toNat_natCast]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hzi
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hzj
    apply hij
    apply Fin.ext
    have he := congrArg Prod.fst (ha.trans hb.symm)
    change (i : ℤ) = (j : ℤ) at he
    exact_mod_cast he

/-- Every connected skew diagram of bounded actual area is a literal
translate of an enumerated profile, not merely Schur-equivalent to one. -/
theorem diagram_mem_profile_census {D : Diagram} (hD : IsConnectedSkew D)
    (A : ℕ) (harea : D.card ≤ A) :
    ∃ p ∈ profilesAtMost A, ∃ v : ℤ × ℤ, D = translate v p.2.cells := by
  obtain ⟨n, P, v, he⟩ := hD.exists_profile_cells
  have hcard : D.card = P.cells.card := by
    rw [he, translate, Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)]
  have hbound : profileArea P ≤ A := by
    rw [profileArea_eq_card, ← hcard]
    exact harea
  exact ⟨⟨n, P⟩, profile_mem_profilesAtMost P hbound, v, he⟩

end SkewCornerDescent
