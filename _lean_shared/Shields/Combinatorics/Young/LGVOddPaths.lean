/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.LGVPaths

/-!
# Lindström--Gessel--Viennot paths over an odd alphabet

The even path model of `Shields.Combinatorics.Young.LGVPaths` reads a complete homogeneous
symmetric function: at height `i` a path runs east from `q i` to `q (i+1)` and then north, so it
occupies the whole interval `[q i, q (i+1)]` there.  The **odd** alphabet is a different geometry,
not the same model with at most one east step per height:

* an elementary level is a **north/north-east** level -- the step from height `i` to height `i+1`
  moves the abscissa by `0` or `1`;
* a path occupies the **single point** `q i` at height `i`, so non-intersection is point
  disjointness rather than interval disjointness.

Running the elementary symmetric functions through the interval reading returns the wrong
polynomial already at the shape `(2)`.

## Main definitions

* `Shields.ePaths` -- the odd paths: even profiles with unit steps.
* `Shields.mixedPaths`, `Shields.mixedWeight` -- `b` even levels below `a` odd ones, and the
  weight of such a path.
* `Shields.eSpliceAt`, `Shields.eSwapPair` -- the tail swap of a pair of odd paths at a height.
* `Shields.MixedMeets` -- the mixed non-intersection predicate: intervals below height `b`,
  points from `b` on.

## Main results

* `Shields.ePaths_sum_eq_elemHom` -- the odd paths from `s` to `s + m` across `a` levels carry
  total weight `e_m (α_0, …, α_{a-1})`.  The word of an odd path is a *column*: unit steps make
  the letters strictly increase (`Shields.pathLetter_strictMono`), which is where the two
  geometries part company, the even letters increasing only weakly.
* `Shields.mixedPaths_sum_eq_superHom` -- `h_m` of the super alphabet,
  `∑_{p+q=m} h_p(β) e_q(α)`, read off the mixed paths.
* `Shields.mixedPaths_fiber_eq_split` -- **the splice at height `b`**: a mixed path is an even
  path from `s` to `q b` followed by an odd path from `q b` to `e`, and the two halves are
  independent.  On a one-row skew shape the fibers are the terms of the super branching rule
  (`Shields.mixedPaths_fiber_eq_branching_term`), the intermediate shape being the abscissa
  `q b`.
* `Shields.sum_nonMeeting_mixed_split` -- the two non-intersection conditions separate as well as
  the weights do, so the filtered pair sum factors over the intermediate abscissae.
* `Shields.eMeets_of_lt` -- two odd paths with transposed endpoints must meet, a discrete
  intermediate value theorem that uses the unit steps; with `Shields.eSwapPair_eSwapPair` and
  `Shields.pathWeight_eSpliceAt_mul` this gives `Shields.elemDet_two_eq_sum_nonMeeting`.
* `Shields.NonMeetingIsSkewSchurTranspose` -- the residue this module leaves: that the
  non-meeting pairs of odd paths carry the tableaux of the conjugate skew shape.  It is a
  theorem, `nonMeetingIsSkewSchurTranspose`.

## Implementation notes

The odd splice cuts at the meeting index `i` rather than at `i+1`: at an odd height the two
profiles already agree at the meeting point, so cutting one higher would move nothing.

The branching sum the splice buys is assembled one module on, in
`Shields.Combinatorics.Young.LGVOddResidue`, where the fibering runs at every `m` at once and the
two-row statement is its `m = 2` case.  This module stays about the geometry.

No Cauchy--Binet is used, and none is available: Mathlib has none at the pinned revision.

## References

* [I. Gessel and G. Viennot, *Binomial determinants, paths, and hook length formulae*][gessel1985]
* [A. Berele and A. Regev, *Hook Young diagrams with applications to combinatorics and to
  representations of Lie superalgebras*][berele1987]

## Tags

Lindström-Gessel-Viennot, non-intersecting paths, elementary symmetric function, super Schur
function, skew Schur function, branching rule
-/

namespace Shields

open Finset

/-! ## The odd path model

An odd path is an even profile whose steps are `0` or `1`.  Everything the even
model proves about profiles — monotonicity, the letters, the weight as a product
of letters — therefore applies verbatim; the unit steps are an extra condition,
and their whole effect is that the letters strictly increase.
-/

section OddPaths

/-- The profiles of odd paths from `s` to `e` across `a` heights: the even
profiles of `hPaths` whose step at each height is `0` or `1`. -/
noncomputable def ePaths (a s e : ℕ) : Finset (ℕ → ℕ) := by
  exact (hPaths a s e).filter fun q => ∀ i ∈ Finset.range a, q (i + 1) ≤ q i + 1

theorem mem_ePaths {a s e : ℕ} {q : ℕ → ℕ} :
    q ∈ ePaths a s e ↔ q ∈ hPaths a s e ∧ ∀ i, i < a → q (i + 1) ≤ q i + 1 := by
  rw [ePaths, Finset.mem_filter]
  simp only [Finset.mem_range]

theorem ePaths_mem {a s e : ℕ} {q : ℕ → ℕ} (hq : q ∈ ePaths a s e) : q ∈ hPaths a s e :=
  (mem_ePaths.mp hq).1

theorem ePaths_step {a s e : ℕ} {q : ℕ → ℕ} (hq : q ∈ ePaths a s e) {i : ℕ} (hi : i < a) :
    q (i + 1) ≤ q i + 1 :=
  (mem_ePaths.mp hq).2 i hi

/-- **One abscissa per step.**  The unit step at the height where the path
crosses `s + j` lands exactly on `s + j + 1`: below the step the profile has not
yet passed `s + j`, above it it has, and it moved by at most one. -/
theorem ePaths_crossing_eq {a s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ ePaths a s (s + m)) {j : ℕ}
    (hj : j < m) : q (pathLetter a s q j + 1) = s + j + 1 := by
  have hq' := ePaths_mem hq
  have hLa : pathLetter a s q j < a := pathLetter_lt_height hq' (by omega)
  have h1 : ¬ (s + j < q (pathLetter a s q j)) := by
    rw [← pathLetter_lt_iff hq' (le_of_lt hLa)]
    omega
  have h2 : s + j < q (pathLetter a s q j + 1) := by
    rw [← pathLetter_lt_iff hq' (by omega : pathLetter a s q j + 1 ≤ a)]
    omega
  have h3 := ePaths_step hq hLa
  omega

/-- Consecutive letters of an odd path are distinct: the step that carries the
path across `s + j` lands on `s + j + 1`, so it does not carry it across
`s + j + 1` as well. -/
theorem pathLetter_lt_succ {a s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ ePaths a s (s + m)) {j : ℕ}
    (hj : j + 1 < m) : pathLetter a s q j < pathLetter a s q (j + 1) := by
  have hq' := ePaths_mem hq
  have hLa : pathLetter a s q j < a := pathLetter_lt_height hq' (by omega)
  have hcross := ePaths_crossing_eq hq (show j < m by omega)
  have h : ¬ (pathLetter a s q (j + 1) < pathLetter a s q j + 1) := by
    rw [pathLetter_lt_iff hq' (by omega : pathLetter a s q j + 1 ≤ a)]
    omega
  omega

/-- **The word of an odd path is a column.**  This is where the two geometries
part company: the even model's letters increase weakly, so its word is a row,
while unit steps make the odd model's letters increase strictly. -/
theorem pathLetter_strictMono {a s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ ePaths a s (s + m))
    {j₁ j₂ : ℕ} (h : j₁ < j₂) (hj₂ : j₂ < m) :
    pathLetter a s q j₁ < pathLetter a s q j₂ := by
  induction j₂ with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · exact lt_trans (ih h' (by omega)) (pathLetter_lt_succ hq hj₂)
    · exact pathLetter_lt_succ hq hj₂

end OddPaths

/-! ## The odd path sum is `elemHom`

The word of an odd path is a one-column bounded tableau, and the two
descriptions are inverse.  The proofs mirror `wordOfPath` / `pathOfWord` of
`Shields.LGV` with the roles of the row and the column exchanged; what
changes is that the column condition is now the substantive one and the row
condition is vacuous.
-/

section OddPathSum

variable {R : Type*} [CommRing R]

/-- The word of an odd path, as a one-column tableau.  Columns increase strictly
because the letters do; the row condition is vacuous on a shape of one
column. -/
noncomputable def eWordOfPath (a s m : ℕ) (q : ℕ → ℕ) (hq : q ∈ ePaths a s (s + m)) :
    BoundedSSYT (rect m 1) a :=
  ⟨{ entry := fun i j => if j = 0 ∧ i < m then pathLetter a s q i else 0
     row_weak' := by
       intro i j₁ j₂ hj hcell
       exact absurd (mem_rect.mp hcell).2 (by omega)
     col_strict' := by
       intro i₁ i₂ j hi hcell
       obtain ⟨hi₂, hj⟩ := mem_rect.mp hcell
       rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, hi₂⟩]
       exact pathLetter_strictMono hq hi hi₂
     zeros' := by
       intro i j hcell
       exact if_neg fun hc => hcell (mem_rect.mpr ⟨hc.2, by omega⟩)
   },
   by
     intro i j hcell
     obtain ⟨hi, hj⟩ := mem_rect.mp hcell
     change (if j = 0 ∧ i < m then pathLetter a s q i else 0) < a
     rw [if_pos ⟨by omega, hi⟩]
     exact pathLetter_lt_height (ePaths_mem hq) (by omega)⟩

theorem eWordOfPath_apply {a s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ ePaths a s (s + m)) (i j : ℕ) :
    eWordOfPath a s m q hq i j = if j = 0 ∧ i < m then pathLetter a s q i else 0 :=
  rfl

/-- The profile of a column word: the abscissa reached at height `i` is `s` plus
the number of letters below `i`.  This is `wordProfile` on the column of `T`, and
the facts proved there apply to it. -/
noncomputable def ePathOfWord (a s m : ℕ) (T : BoundedSSYT (rect m 1) a) (i : ℕ) : ℕ :=
  s + ((Finset.range m).filter fun j => T j 0 < i).card

/-- The column of a bounded one-column tableau, read as a word: weakly increasing. -/
theorem oneCol_mono {a m : ℕ} (T : BoundedSSYT (rect m 1) a) :
    ∀ j₁ j₂, j₁ ≤ j₂ → j₂ < m → T j₁ 0 ≤ T j₂ 0 :=
  fun _ _ h hj₂ => boundedSSYT_col_mono T h hj₂

theorem oneCol_lt {a m : ℕ} (T : BoundedSSYT (rect m 1) a) : ∀ j, j < m → T j 0 < a :=
  fun _ hj => T.lt (mem_rect.mpr ⟨hj, Nat.zero_lt_one⟩)

/-- A letter below `i` puts its abscissa behind the profile at height `i`. -/
theorem lt_ePathOfWord {a s len : ℕ} (T : BoundedSSYT (rect len 1) a) {i j : ℕ}
    (hj : j < len) (h : T j 0 < i) : s + j < ePathOfWord a s len T i :=
  lt_wordProfile (oneCol_mono T) hj h

/-- A letter at or above `i` stops the profile at its abscissa. -/
theorem ePathOfWord_le {a s len : ℕ} (T : BoundedSSYT (rect len 1) a) {i j : ℕ}
    (h : i ≤ T j 0) : ePathOfWord a s len T i ≤ s + j :=
  wordProfile_le (oneCol_mono T) h

/-- A column word has at most one letter at each height: that is the unit step
of the odd model, read on the tableau side. -/
theorem card_filter_eq_le_one {m a : ℕ} (T : BoundedSSYT (rect m 1) a) (i : ℕ) :
    ((Finset.range m).filter fun j => T j 0 = i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j₁ hj₁ j₂ hj₂
  rw [Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (T.1.col_strict hlt (mem_rect.mpr ⟨hj₂.1, Nat.zero_lt_one⟩)) (by omega)
  · exact absurd (T.1.col_strict hlt (mem_rect.mpr ⟨hj₁.1, Nat.zero_lt_one⟩)) (by omega)

theorem ePathOfWord_mem (a s m : ℕ) (T : BoundedSSYT (rect m 1) a) :
    ePathOfWord a s m T ∈ ePaths a s (s + m) := by
  refine mem_ePaths.mpr ⟨wordProfile_mem_hPaths a (oneCol_lt T), fun i hi => ?_⟩
  have hsub : ((Finset.range m).filter fun j => T j 0 < i)
      ⊆ (Finset.range m).filter fun j => T j 0 < i + 1 := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, by omega⟩
  have hsplit := Finset.card_sdiff_add_card_eq_card hsub
  have hdiff : (((Finset.range m).filter fun j => T j 0 < i + 1) \
      ((Finset.range m).filter fun j => T j 0 < i))
      = (Finset.range m).filter fun j => T j 0 = i := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
    omega
  rw [hdiff] at hsplit
  have hone := card_filter_eq_le_one T i
  rw [ePathOfWord, ePathOfWord]
  omega

/-- The profile of a word writes the word's own letters. -/
theorem pathLetter_ePathOfWord {a s m : ℕ} (T : BoundedSSYT (rect m 1) a) {j : ℕ}
    (hj : j < m) : pathLetter a s (ePathOfWord a s m T) j = T j 0 :=
  pathLetter_wordProfile (oneCol_mono T) (oneCol_lt T) hj

theorem ePathOfWord_eWordOfPath {a s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ ePaths a s (s + m)) :
    ePathOfWord a s m (eWordOfPath a s m q hq) = q :=
  wordProfile_of_pathLetter (ePaths_mem hq) fun j hj => by
    rw [eWordOfPath_apply, if_pos ⟨rfl, hj⟩]

theorem eWordOfPath_ePathOfWord {a s m : ℕ} (T : BoundedSSYT (rect m 1) a) :
    eWordOfPath a s m (ePathOfWord a s m T) (ePathOfWord_mem a s m T) = T := by
  refine BoundedSSYT.ext fun i j => ?_
  rw [eWordOfPath_apply]
  by_cases hc : j = 0 ∧ i < m
  · obtain ⟨rfl, hi⟩ := hc
    rw [if_pos ⟨rfl, hi⟩, pathLetter_ePathOfWord T hi]
  · rw [if_neg hc]
    exact (T.zeros fun h => hc ⟨by have := (mem_rect.mp h).2; omega,
      (mem_rect.mp h).1⟩).symm

/-- Two one-column words agreeing on their cells trace the same odd path. -/
theorem ePathOfWord_congr {a m s : ℕ} (T T' : BoundedSSYT (rect m 1) a)
    (h : ∀ j, j < m → T j 0 = T' j 0) : ePathOfWord a s m T = ePathOfWord a s m T' := by
  funext i
  have hset : ((Finset.range m).filter fun j => T j 0 < i)
      = (Finset.range m).filter fun j => T' j 0 < i := by
    ext j
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hj, hlt⟩
      exact ⟨hj, by rwa [← h j (Finset.mem_range.mp hj)]⟩
    · rintro ⟨hj, hlt⟩
      exact ⟨hj, by rwa [h j (Finset.mem_range.mp hj)]⟩
  change s + ((Finset.range m).filter fun j => T j 0 < i).card
      = s + ((Finset.range m).filter fun j => T' j 0 < i).card
  rw [hset]

/-- A one-column word whose letters are those of an odd path traces that path
back. -/
theorem ePathOfWord_eq_of_entry {a s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ ePaths a s (s + m))
    (T : BoundedSSYT (rect m 1) a) (h : ∀ j, j < m → T j 0 = pathLetter a s q j) :
    ePathOfWord a s m T = q := by
  rw [← ePathOfWord_eWordOfPath hq]
  exact ePathOfWord_congr T _ fun j hj => by
    rw [h j hj, eWordOfPath_apply, if_pos ⟨rfl, hj⟩]

/-- **The odd alphabet.**  The odd paths from `s` to `s + m` across `a` heights
carry total weight `e_m(α_0, …, α_{a-1})`, the `elemHom` of
`Shields.JacobiTrudi`.  This is the odd factor of the alphabet `ρ_D` that
the skew Jacobi--Trudi identity is an identity over, and it is the point-disjoint
north/north-east geometry that produces it: the interval reading of the same
levels returns a different polynomial, exhibited at `λ = (2)` by check (3) of
a separate numerical check. -/
theorem ePaths_sum_eq_elemHom (a s m : ℕ) (α : ℕ → R) :
    ∑ q ∈ ePaths a s (s + m), pathWeight a α q = elemHom a m α := by
  rw [elemHom, skewSchur_bot, schur]
  refine Finset.sum_bij' (fun q hq => eWordOfPath a s m q hq) (fun T _ => ePathOfWord a s m T)
    (fun q _ => Finset.mem_univ _) (fun T _ => ePathOfWord_mem a s m T)
    (fun q hq => ePathOfWord_eWordOfPath hq) (fun T _ => eWordOfPath_ePathOfWord T)
    (fun q hq => ?_)
  rw [pathWeight_eq_prod_letters (ePaths_mem hq), cells_rect, Finset.prod_product]
  simp only [Finset.prod_range_one]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [eWordOfPath_apply, if_pos ⟨rfl, Finset.mem_range.mp hj⟩]

end OddPathSum

/-! ## The mixed model, and the splice at height `b`

`b` even heights carry the path first, then `a` odd ones.  A mixed profile is
therefore an even profile whose steps above height `b` are units, and it splits
at height `b` into an even path from `s` to `q b` and an odd path from `q b` to
`e`.  The splice is a bijection, weight for weight, so nothing bilinear happens
across the join.
-/

section Mixed

/-- The profiles of mixed paths from `s` to `e`: `b` even heights, on which the
step is unrestricted, followed by `a` odd heights, on which it is `0` or `1`. -/
noncomputable def mixedPaths (b a s e : ℕ) : Finset (ℕ → ℕ) := by
  exact (hPaths (b + a) s e).filter fun q => ∀ i ∈ Finset.Ico b (b + a), q (i + 1) ≤ q i + 1

theorem mem_mixedPaths {b a s e : ℕ} {q : ℕ → ℕ} :
    q ∈ mixedPaths b a s e ↔
      q ∈ hPaths (b + a) s e ∧ ∀ i, b ≤ i → i < b + a → q (i + 1) ≤ q i + 1 := by
  rw [mixedPaths, Finset.mem_filter]
  simp only [Finset.mem_Ico, and_imp]

/-- The even half of a mixed profile: it stops at height `b`. -/
def truncAt (b : ℕ) (q : ℕ → ℕ) (k : ℕ) : ℕ := q (min k b)

/-- The odd half of a mixed profile: it starts at height `b`. -/
def shiftAt (b : ℕ) (q : ℕ → ℕ) (k : ℕ) : ℕ := q (b + k)

/-- The mixed profile that runs `q₁` up to height `b` and `q₂` after it. -/
def glueAt (b : ℕ) (q₁ q₂ : ℕ → ℕ) (k : ℕ) : ℕ := if k ≤ b then q₁ k else q₂ (k - b)

@[simp]
theorem glueAt_of_le {b : ℕ} (q₁ q₂ : ℕ → ℕ) {k : ℕ} (hk : k ≤ b) :
    glueAt b q₁ q₂ k = q₁ k :=
  if_pos hk

@[simp]
theorem glueAt_of_gt {b : ℕ} (q₁ q₂ : ℕ → ℕ) {k : ℕ} (hk : b < k) :
    glueAt b q₁ q₂ k = q₂ (k - b) :=
  if_neg (by omega)

theorem truncAt_mem {b a s e : ℕ} {q : ℕ → ℕ} (hq : q ∈ mixedPaths b a s e) :
    truncAt b q ∈ hPaths b s (q b) := by
  have hq' := (mem_mixedPaths.mp hq).1
  refine mem_hPaths.mpr ⟨by simp [truncAt, hPaths_zero hq'], fun k₁ k₂ h => ?_,
    fun k hk => by simp [truncAt, min_eq_right hk]⟩
  exact hPaths_mono hq' (by omega : min k₁ b ≤ min k₂ b)

theorem shiftAt_mem {b a s e : ℕ} {q : ℕ → ℕ} (hq : q ∈ mixedPaths b a s e) :
    shiftAt b q ∈ ePaths a (q b) e := by
  obtain ⟨hq', hstep⟩ := mem_mixedPaths.mp hq
  refine mem_ePaths.mpr ⟨mem_hPaths.mpr ⟨by simp [shiftAt], fun k₁ k₂ h => ?_,
    fun k hk => ?_⟩, fun i hi => ?_⟩
  · exact hPaths_mono hq' (by omega : b + k₁ ≤ b + k₂)
  · exact hPaths_top hq' (by omega : b + a ≤ b + k)
  · exact hstep (b + i) (by omega) (by omega)

/-- The two halves recover the mixed profile. -/
theorem glueAt_truncAt_shiftAt (b : ℕ) (q : ℕ → ℕ) :
    glueAt b (truncAt b q) (shiftAt b q) = q := by
  funext k
  rcases le_or_gt k b with hk | hk
  · rw [glueAt_of_le _ _ hk, truncAt, min_eq_left hk]
  · rw [glueAt_of_gt _ _ hk, shiftAt]
    congr 1
    omega

theorem truncAt_glueAt {b s c : ℕ} {q₁ q₂ : ℕ → ℕ} (h₁ : q₁ ∈ hPaths b s c) :
    truncAt b (glueAt b q₁ q₂) = q₁ := by
  funext k
  rw [truncAt, glueAt_of_le _ _ (min_le_right k b)]
  rcases le_or_gt k b with hk | hk
  · rw [min_eq_left hk]
  · rw [min_eq_right hk.le, hPaths_top h₁ le_rfl, hPaths_top h₁ hk.le]

theorem shiftAt_glueAt {b a s c e : ℕ} {q₁ q₂ : ℕ → ℕ} (h₁ : q₁ ∈ hPaths b s c)
    (h₂ : q₂ ∈ ePaths a c e) : shiftAt b (glueAt b q₁ q₂) = q₂ := by
  funext k
  rw [shiftAt]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.add_zero, glueAt_of_le _ _ le_rfl, hPaths_top h₁ le_rfl,
      hPaths_zero (ePaths_mem h₂)]
  · rw [glueAt_of_gt _ _ (by omega : b < b + k)]
    congr 1
    omega

theorem glueAt_mem {b a s c e : ℕ} {q₁ q₂ : ℕ → ℕ} (h₁ : q₁ ∈ hPaths b s c)
    (h₂ : q₂ ∈ ePaths a c e) : glueAt b q₁ q₂ ∈ mixedPaths b a s e := by
  have h₂' := ePaths_mem h₂
  have hc : q₂ 0 = c := hPaths_zero h₂'
  have hb : q₁ b = c := hPaths_top h₁ le_rfl
  refine mem_mixedPaths.mpr ⟨mem_hPaths.mpr ⟨?_, fun k₁ k₂ h => ?_, fun k hk => ?_⟩,
    fun i hi hia => ?_⟩
  · rw [glueAt_of_le _ _ (Nat.zero_le b)]
    exact hPaths_zero h₁
  · rcases le_or_gt k₂ b with h₂b | h₂b
    · rw [glueAt_of_le _ _ (by omega), glueAt_of_le _ _ h₂b]
      exact hPaths_mono h₁ h
    · rcases le_or_gt k₁ b with h₁b | h₁b
      · rw [glueAt_of_le _ _ h₁b, glueAt_of_gt _ _ h₂b]
        refine le_trans (le_trans (hPaths_mono h₁ h₁b) ?_) (hPaths_mono h₂' (Nat.zero_le _))
        rw [hb, hc]
      · rw [glueAt_of_gt _ _ h₁b, glueAt_of_gt _ _ h₂b]
        exact hPaths_mono h₂' (by omega)
  · rcases le_or_gt k b with hkb | hkb
    · have ha : a = 0 := by omega
      have hk0 : k = b := by omega
      subst ha
      rw [hk0, glueAt_of_le _ _ le_rfl, hb, ← hc]
      exact hPaths_top h₂' (Nat.zero_le 0)
    · rw [glueAt_of_gt _ _ hkb]
      exact hPaths_top h₂' (by omega)
  · rcases Nat.eq_or_lt_of_le hi with rfl | hib
    · rw [glueAt_of_gt _ _ (by omega : b < b + 1), glueAt_of_le _ _ le_rfl, hb, ← hc,
        show b + 1 - b = 0 + 1 by omega]
      exact ePaths_step h₂ (by omega)
    · rw [glueAt_of_gt _ _ (by omega : b < i + 1), glueAt_of_gt _ _ (by omega : b < i),
        show i + 1 - b = (i - b) + 1 by omega]
      exact ePaths_step h₂ (by omega : i - b < a)

variable {R : Type*} [CommRing R]

/-- The weight of a mixed path: `β i` per east step at even height `i`, and
`α i` per north-east step at odd height `b + i`. -/
noncomputable def mixedWeight (b a : ℕ) (β α : ℕ → R) (q : ℕ → ℕ) : R :=
  pathWeight b β q * pathWeight a α (shiftAt b q)

theorem pathWeight_glueAt (b : ℕ) (β : ℕ → R) (q₁ q₂ : ℕ → ℕ) :
    pathWeight b β (glueAt b q₁ q₂) = pathWeight b β q₁ := by
  refine Finset.prod_congr rfl fun i hi => ?_
  have hib := Finset.mem_range.mp hi
  rw [glueAt_of_le _ _ (by omega : i ≤ b), glueAt_of_le _ _ (by omega : i + 1 ≤ b)]

theorem pathWeight_truncAt (b : ℕ) (β : ℕ → R) (q : ℕ → ℕ) :
    pathWeight b β (truncAt b q) = pathWeight b β q := by
  refine Finset.prod_congr rfl fun i hi => ?_
  have hib := Finset.mem_range.mp hi
  have h1 : min i b = i := min_eq_left (by omega)
  have h2 : min (i + 1) b = i + 1 := min_eq_left (by omega)
  simp only [truncAt, h1, h2]

theorem mixedWeight_glueAt {b a s c e : ℕ} (β α : ℕ → R) {q₁ q₂ : ℕ → ℕ}
    (h₁ : q₁ ∈ hPaths b s c) (h₂ : q₂ ∈ ePaths a c e) :
    mixedWeight b a β α (glueAt b q₁ q₂) = pathWeight b β q₁ * pathWeight a α q₂ := by
  rw [mixedWeight, pathWeight_glueAt, shiftAt_glueAt h₁ h₂]

/-- **The splice at height `b`.**  The mixed paths through a fixed abscissa `c`
at height `b` are the pairs consisting of an even path from `s` to `c` and an
odd path from `c` to `e`, and the weight is the product of the two.  The two
halves are independent, so the fiber sum is a product of sums — no bilinear
pairing of the two alphabets is involved. -/
theorem mixedPaths_fiber_eq_split (b a s e c : ℕ) (β α : ℕ → R) :
    ∑ q ∈ (mixedPaths b a s e).filter (fun q => q b = c), mixedWeight b a β α q
      = (∑ q₁ ∈ hPaths b s c, pathWeight b β q₁) * ∑ q₂ ∈ ePaths a c e, pathWeight a α q₂ := by
  rw [sum_mul_sum_prod]
  refine Finset.sum_nbij' (fun q => (truncAt b q, shiftAt b q))
    (fun x => glueAt b x.1 x.2) (fun q hq => ?_) (fun x hx => ?_) (fun q hq => ?_)
    (fun x hx => ?_) (fun q hq => ?_)
  · rw [Finset.mem_filter] at hq
    obtain ⟨hq, hc⟩ := hq
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [← hc]; exact truncAt_mem hq
    · rw [← hc]; exact shiftAt_mem hq
  · rw [Finset.mem_product] at hx
    refine Finset.mem_filter.mpr ⟨glueAt_mem hx.1 hx.2, ?_⟩
    rw [glueAt_of_le _ _ le_rfl]
    exact hPaths_top hx.1 le_rfl
  · exact glueAt_truncAt_shiftAt b q
  · rw [Finset.mem_product] at hx
    exact Prod.ext (truncAt_glueAt hx.1) (shiftAt_glueAt hx.1 hx.2)
  · rw [mixedWeight, pathWeight_truncAt]

/-- **The mixed alphabet.**  The mixed paths from `s` to `s + m` carry total
weight `∑_{p+q=m} h_p(β) e_q(α)`, the coefficient `d_m` of the specialization
`ρ_D` in `b` even and `a` odd variables.  This is the `superHom` that
`jacobiTrudiDet_eq_superSkewSchur_of_le_one` takes as its hypothesis `hd`, so
the path model is a model of exactly the alphabet the skew Jacobi--Trudi identity runs
over. -/
theorem mixedPaths_sum_eq_superHom (b a s m : ℕ) (β α : ℕ → R) :
    ∑ q ∈ mixedPaths b a s (s + m), mixedWeight b a β α q = superHom b a m β α := by
  have hmap : ∀ q ∈ mixedPaths b a s (s + m), q b - s ∈ Finset.range (m + 1) := by
    intro q hq
    have h := hPaths_le (mem_mixedPaths.mp hq).1 b
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmap, superHom]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Finset.mem_range.mp hp
  have hfilter : ((mixedPaths b a s (s + m)).filter fun q => q b - s = p)
      = (mixedPaths b a s (s + m)).filter fun q => q b = s + p := by
    refine Finset.filter_congr fun q hq => ?_
    have h := hPaths_le (mem_mixedPaths.mp hq).1 b
    constructor <;> intro h' <;> omega
  rw [hfilter, mixedPaths_fiber_eq_split, show s + m = (s + p) + (m - p) by omega,
    hPaths_sum_eq_completeHom, ePaths_sum_eq_elemHom]

/-- **The splice reproduces the super branching rule, fiber by summand.**  On a
one-row skew shape `(l) / (t)` the mixed paths through `t + p` at height `b`
carry the weight of the `ν = (t+p)` term of the branching sum: the even half is
`s_{ν/μ}(β)` and the odd half is `s_{λ'/ν'}(α)`.  The intermediate shape of
the super branching rule is the abscissa at height `b`. -/
theorem mixedPaths_fiber_eq_branching_term (b a t l p : ℕ) (hp : t + p ≤ l) (β α : ℕ → R) :
    ∑ q ∈ (mixedPaths b a t l).filter (fun q => q b = t + p), mixedWeight b a β α q
      = skewSchur (rect 1 (t + p)) (rect 1 t) b β
        * skewSchur (rect 1 l).transpose (rect 1 (t + p)).transpose a α := by
  rw [mixedPaths_fiber_eq_split, transpose_rect, transpose_rect,
    skewSchur_rect_row (by omega : t ≤ t + p), skewSchur_rect_col hp,
    show t + p = t + p from rfl, Nat.add_sub_cancel_left,
    show l = (t + p) + (l - (t + p)) by omega, hPaths_sum_eq_completeHom,
    ePaths_sum_eq_elemHom]
  congr 2
  omega

/-- **The splice reproduces the super branching rule on a one-row skew shape.**
Summing the fibers over the intermediate abscissa is summing the branching
formula over the intermediate shape.  Nothing beyond the splice is used: no
Cauchy--Binet, and none is available at the pinned Mathlib revision. -/
theorem mixedPaths_sum_eq_superSkewSchur_rect_row (b a t l : ℕ) (htl : t ≤ l) (β α : ℕ → R) :
    ∑ q ∈ mixedPaths b a t l, mixedWeight b a β α q
      = superSkewSchur (rect 1 l) (rect 1 t) b a β α := by
  have h := mixedPaths_sum_eq_superHom b a t (l - t) β α
  rw [show t + (l - t) = l by omega] at h
  rw [h, superSkewSchur_rect_row htl]

end Mixed

/-! ## Point disjointness, and the splice of a pair

Occupancy at an odd height is the single abscissa `q i`, so two odd paths
intersect exactly when they share a value.  A pair of mixed paths therefore
carries two conditions of different kinds — interval disjointness on the even
heights `0, …, b-1`, point disjointness on the odd heights `b, …, b+a` — and
they separate along the splice, height `b` belonging to the odd half.
-/

section Meeting

/-- The odd heights at which two odd paths occupy the same point. -/
def eMeetSet (a : ℕ) (q r : ℕ → ℕ) : Finset ℕ :=
  (Finset.range (a + 1)).filter fun i => q i = r i

/-- Two odd paths meet when they occupy a common point.  This is the odd
model's non-intersection condition: point disjointness, not the interval
disjointness of `Crosses`. -/
def EMeets (a : ℕ) (q r : ℕ → ℕ) : Prop := (eMeetSet a q r).Nonempty

instance (a : ℕ) (q r : ℕ → ℕ) : Decidable (EMeets a q r) :=
  inferInstanceAs (Decidable (eMeetSet a q r).Nonempty)

theorem mem_eMeetSet {a : ℕ} {q r : ℕ → ℕ} {i : ℕ} :
    i ∈ eMeetSet a q r ↔ i ≤ a ∧ q i = r i := by
  rw [eMeetSet, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

theorem eMeetSet_comm (a : ℕ) (q r : ℕ → ℕ) : eMeetSet a q r = eMeetSet a r q := by
  ext i
  rw [mem_eMeetSet, mem_eMeetSet]
  exact and_congr_right fun _ => eq_comm

/-- **Point disjointness is separation.**  Two odd paths whose sources are
ordered and which never share an abscissa stay strictly ordered throughout: the
unit step cannot carry the lower path past the higher one without landing on
it.  This is the odd counterpart of `lt_of_not_crosses`, and it is the strict
inequality an odd tableau bijection consumes. -/
theorem lt_of_not_eMeets {a s₁ e₁ s₂ e₂ : ℕ} {q r : ℕ → ℕ} (hq : q ∈ ePaths a s₁ e₁)
    (hr : r ∈ ePaths a s₂ e₂) (hs : s₂ < s₁) (h : ¬ EMeets a q r) :
    ∀ i, i ≤ a → r i < q i := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hPaths_zero (ePaths_mem hq), hPaths_zero (ePaths_mem hr)]
    exact hs
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hstep := ePaths_step hr (show i < a by omega)
    have hmono := hPaths_mono (ePaths_mem hq) (show i ≤ i + 1 by omega)
    have hne : q (i + 1) ≠ r (i + 1) := fun hc =>
      h ⟨i + 1, mem_eMeetSet.mpr ⟨hi, hc⟩⟩
    omega

/-- The mixed model's non-intersection condition, both kinds at once: interval
disjointness below height `b`, point disjointness from height `b` on. -/
def MixedMeets (b a : ℕ) (q r : ℕ → ℕ) : Prop :=
  Crosses b q r ∨ EMeets a (shiftAt b q) (shiftAt b r)

instance (b a : ℕ) (q r : ℕ → ℕ) : Decidable (MixedMeets b a q r) :=
  inferInstanceAs (Decidable (Crosses b q r ∨ EMeets a (shiftAt b q) (shiftAt b r)))

/-- The even crossing set reads the profiles only up to height `b`. -/
theorem crossSet_congr {b : ℕ} {q r q' r' : ℕ → ℕ} (hq : ∀ k, k ≤ b → q k = q' k)
    (hr : ∀ k, k ≤ b → r k = r' k) : crossSet b q r = crossSet b q' r' := by
  ext i
  rw [mem_crossSet, mem_crossSet]
  constructor
  · rintro ⟨hib, h1, h2⟩
    rw [← hq i (by omega), ← hq (i + 1) (by omega), ← hr i (by omega), ← hr (i + 1) (by omega)]
    exact ⟨hib, h1, h2⟩
  · rintro ⟨hib, h1, h2⟩
    rw [hq i (by omega), hq (i + 1) (by omega), hr i (by omega), hr (i + 1) (by omega)]
    exact ⟨hib, h1, h2⟩

theorem crossSet_truncAt (b : ℕ) (q r : ℕ → ℕ) :
    crossSet b (truncAt b q) (truncAt b r) = crossSet b q r :=
  crossSet_congr (fun k hk => by rw [truncAt, min_eq_left hk])
    (fun k hk => by rw [truncAt, min_eq_left hk])

theorem crossSet_glueAt (b : ℕ) (q₁ q₂ r₁ r₂ : ℕ → ℕ) :
    crossSet b (glueAt b q₁ q₂) (glueAt b r₁ r₂) = crossSet b q₁ r₁ :=
  crossSet_congr (fun _ hk => glueAt_of_le _ _ hk) (fun _ hk => glueAt_of_le _ _ hk)

variable {R : Type*} [CommRing R]

/-- **The splice of a pair.**  Both the weights and the two non-intersection
conditions separate at height `b`: a non-intersecting pair of mixed paths
through the abscissae `c₁, c₂` is a non-crossing pair of even paths below
height `b` together with a non-meeting pair of odd paths above it, and the
fiber sum is the product of the two.

This is what makes the mixed model need no Cauchy--Binet: the two halves are
joined by a bijection of families, not by a pairing of minors. -/
theorem sum_nonMeeting_mixed_split (b a s₁ e₁ s₂ e₂ c₁ c₂ : ℕ) (β α : ℕ → R) :
    ∑ x ∈ (mixedPaths b a s₁ e₁ ×ˢ mixedPaths b a s₂ e₂).filter
            (fun x => x.1 b = c₁ ∧ x.2 b = c₂ ∧ ¬ MixedMeets b a x.1 x.2),
        mixedWeight b a β α x.1 * mixedWeight b a β α x.2
      = (∑ y ∈ (hPaths b s₁ c₁ ×ˢ hPaths b s₂ c₂).filter fun y => ¬ Crosses b y.1 y.2,
            pathWeight b β y.1 * pathWeight b β y.2)
        * ∑ z ∈ (ePaths a c₁ e₁ ×ˢ ePaths a c₂ e₂).filter fun z => ¬ EMeets a z.1 z.2,
            pathWeight a α z.1 * pathWeight a α z.2 := by
  rw [sum_mul_sum_prod]
  refine Finset.sum_nbij'
    (fun x => ((truncAt b x.1, truncAt b x.2), (shiftAt b x.1, shiftAt b x.2)))
    (fun w => (glueAt b w.1.1 w.2.1, glueAt b w.1.2 w.2.2))
    (fun x hx => ?_) (fun w hw => ?_) (fun x hx => ?_) (fun w hw => ?_) (fun x hx => ?_)
  · rw [Finset.mem_filter, Finset.mem_product] at hx
    obtain ⟨⟨h1, h2⟩, hc1, hc2, hcross⟩ := hx
    rw [MixedMeets, not_or] at hcross
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩⟩
    · rw [← hc1]; exact truncAt_mem h1
    · rw [← hc2]; exact truncAt_mem h2
    · rw [Crosses, crossSet_truncAt]; exact hcross.1
    · rw [← hc1]; exact shiftAt_mem h1
    · rw [← hc2]; exact shiftAt_mem h2
    · exact hcross.2
  · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at hw
    obtain ⟨⟨⟨hy1, hy2⟩, hycross⟩, ⟨hz1, hz2⟩, hzmeet⟩ := hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨glueAt_mem hy1 hz1,
      glueAt_mem hy2 hz2⟩, ?_, ?_, ?_⟩
    · change glueAt b w.1.1 w.2.1 b = c₁
      rw [glueAt_of_le _ _ le_rfl]
      exact hPaths_top hy1 le_rfl
    · change glueAt b w.1.2 w.2.2 b = c₂
      rw [glueAt_of_le _ _ le_rfl]
      exact hPaths_top hy2 le_rfl
    · rw [MixedMeets, not_or, Crosses, crossSet_glueAt, shiftAt_glueAt hy1 hz1,
        shiftAt_glueAt hy2 hz2]
      exact ⟨hycross, hzmeet⟩
  · exact Prod.ext (glueAt_truncAt_shiftAt b x.1) (glueAt_truncAt_shiftAt b x.2)
  · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at hw
    obtain ⟨⟨⟨hy1, hy2⟩, -⟩, ⟨hz1, hz2⟩, -⟩ := hw
    exact Prod.ext (Prod.ext (truncAt_glueAt hy1) (truncAt_glueAt hy2))
      (Prod.ext (shiftAt_glueAt hy1 hz1) (shiftAt_glueAt hy2 hz2))
  · rw [mixedWeight, mixedWeight, pathWeight_truncAt, pathWeight_truncAt]
    ring

end Meeting

/-! ## The cancellation at two odd paths

The Lindström--Gessel--Viennot argument runs in the odd geometry as well, and
the swap is simpler there: the two profiles already agree at a meeting point, so
the tails are exchanged from that index rather than from the one above it.  Two
odd paths with transposed endpoints must meet — the unit steps make the
difference of the profiles change by at most one per height, which is a discrete
intermediate value theorem — so the transposed term of the `2 × 2` determinant
cancels entirely against the meeting pairs of the leading term.
-/

section OddCancellation

/-- The least odd height at which the two paths share a point; `0` when they do
not meet. -/
noncomputable def eMeetHeight (a : ℕ) (q r : ℕ → ℕ) : ℕ :=
  if h : EMeets a q r then (eMeetSet a q r).min' h else 0

theorem eMeetHeight_mem {a : ℕ} {q r : ℕ → ℕ} (h : EMeets a q r) :
    eMeetHeight a q r ∈ eMeetSet a q r := by
  rw [eMeetHeight, dif_pos h]
  exact Finset.min'_mem _ h

theorem eMeetHeight_le_height {a : ℕ} {q r : ℕ → ℕ} (h : EMeets a q r) : eMeetHeight a q r ≤ a :=
  (mem_eMeetSet.mp (eMeetHeight_mem h)).1

theorem eMeetHeight_spec {a : ℕ} {q r : ℕ → ℕ} (h : EMeets a q r) :
    q (eMeetHeight a q r) = r (eMeetHeight a q r) :=
  (mem_eMeetSet.mp (eMeetHeight_mem h)).2

theorem eMeetHeight_le {a : ℕ} {q r : ℕ → ℕ} (h : EMeets a q r) {k : ℕ}
    (hk : k ∈ eMeetSet a q r) : eMeetHeight a q r ≤ k := by
  rw [eMeetHeight, dif_pos h]
  exact Finset.min'_le _ _ hk

/-- The profile that follows `q` below height `i` and `r` from height `i` on.
The cut is at `i`, not at `i+1`: at an odd height the two profiles occupy the
same point when they meet, so the tails can be exchanged there. -/
def eSpliceAt (i : ℕ) (q r : ℕ → ℕ) (k : ℕ) : ℕ := if k < i then q k else r k

@[simp]
theorem eSpliceAt_of_lt {i : ℕ} (q r : ℕ → ℕ) {k : ℕ} (hk : k < i) : eSpliceAt i q r k = q k :=
  if_pos hk

@[simp]
theorem eSpliceAt_of_ge {i : ℕ} (q r : ℕ → ℕ) {k : ℕ} (hk : i ≤ k) : eSpliceAt i q r k = r k :=
  if_neg (by omega)

theorem eSpliceAt_eSpliceAt (i : ℕ) (q r : ℕ → ℕ) :
    eSpliceAt i (eSpliceAt i q r) (eSpliceAt i r q) = q := by
  funext k
  rcases lt_or_ge k i with hk | hk
  · rw [eSpliceAt_of_lt _ _ hk, eSpliceAt_of_lt _ _ hk]
  · rw [eSpliceAt_of_ge _ _ hk, eSpliceAt_of_ge _ _ hk]

/-- A splice at a meeting height is again an odd path, from `q`'s source to
`r`'s sink. -/
theorem eSpliceAt_mem {a s₁ e₁ s₂ e₂ i : ℕ} {q r : ℕ → ℕ} (hq : q ∈ ePaths a s₁ e₁)
    (hr : r ∈ ePaths a s₂ e₂) (hi : i ≤ a) (hmeet : q i = r i) :
    eSpliceAt i q r ∈ ePaths a s₁ e₂ := by
  have hq' := ePaths_mem hq
  have hr' := ePaths_mem hr
  refine mem_ePaths.mpr ⟨mem_hPaths.mpr ⟨?_, fun k₁ k₂ h => ?_, fun k hk => ?_⟩, fun k hk => ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [eSpliceAt_of_ge _ _ (Nat.zero_le 0), ← hmeet]
      exact hPaths_zero hq'
    · rw [eSpliceAt_of_lt _ _ hipos]
      exact hPaths_zero hq'
  · rcases lt_or_ge k₂ i with h₂ | h₂
    · rw [eSpliceAt_of_lt _ _ (by omega), eSpliceAt_of_lt _ _ h₂]
      exact hPaths_mono hq' h
    · rcases lt_or_ge k₁ i with h₁ | h₁
      · rw [eSpliceAt_of_lt _ _ h₁, eSpliceAt_of_ge _ _ h₂]
        exact le_trans (le_trans (hPaths_mono hq' h₁.le) (le_of_eq hmeet)) (hPaths_mono hr' h₂)
      · rw [eSpliceAt_of_ge _ _ h₁, eSpliceAt_of_ge _ _ h₂]
        exact hPaths_mono hr' h
  · rw [eSpliceAt_of_ge _ _ (by omega : i ≤ k)]
    exact hPaths_top hr' hk
  · rcases lt_or_ge (k + 1) i with h₁ | h₁
    · rw [eSpliceAt_of_lt _ _ h₁, eSpliceAt_of_lt _ _ (by omega : k < i)]
      exact ePaths_step hq hk
    · rcases lt_or_ge k i with h₂ | h₂
      · have hik : i = k + 1 := by omega
        rw [eSpliceAt_of_ge _ _ h₁, eSpliceAt_of_lt _ _ h₂, ← hik, ← hmeet, hik]
        exact ePaths_step hq hk
      · rw [eSpliceAt_of_ge _ _ h₁, eSpliceAt_of_ge _ _ h₂]
        exact ePaths_step hr hk

/-- The spliced pair meets at the splice height. -/
theorem meets_eSpliceAt {a i : ℕ} {q r : ℕ → ℕ} (hi : i ≤ a) (hmeet : q i = r i) :
    i ∈ eMeetSet a (eSpliceAt i q r) (eSpliceAt i r q) := by
  refine mem_eMeetSet.mpr ⟨hi, ?_⟩
  rw [eSpliceAt_of_ge _ _ le_rfl, eSpliceAt_of_ge _ _ le_rfl]
  exact hmeet.symm

/-- Below the splice height the spliced profiles are the originals, so they meet
exactly where the originals do. -/
theorem mem_eMeetSet_eSpliceAt_of_lt {a i k : ℕ} (q r : ℕ → ℕ) (hk : k < i) :
    k ∈ eMeetSet a (eSpliceAt i q r) (eSpliceAt i r q) ↔ k ∈ eMeetSet a q r := by
  rw [mem_eMeetSet, mem_eMeetSet, eSpliceAt_of_lt _ _ hk, eSpliceAt_of_lt _ _ hk]

/-- **The splice height is preserved.**  Splicing at the least meeting height
leaves that height least, which is what makes the swap an involution. -/
theorem eMeetHeight_eSpliceAt {a : ℕ} {q r : ℕ → ℕ} (h : EMeets a q r) :
    eMeetHeight a (eSpliceAt (eMeetHeight a q r) q r) (eSpliceAt (eMeetHeight a q r) r q)
      = eMeetHeight a q r := by
  set i := eMeetHeight a q r with hi
  have hia : i ≤ a := eMeetHeight_le_height h
  have hmem := meets_eSpliceAt hia (eMeetHeight_spec h)
  have hmeets : EMeets a (eSpliceAt i q r) (eSpliceAt i r q) := ⟨i, hmem⟩
  refine le_antisymm (eMeetHeight_le hmeets hmem) ?_
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hk := eMeetHeight_mem hmeets
  rw [mem_eMeetSet_eSpliceAt_of_lt q r hcon] at hk
  exact absurd (eMeetHeight_le h hk) (by omega)

variable {R : Type*} [CommRing R]

/-- **The swap preserves weight.**  At every height away from the splice the two
step counts are exchanged; at the splice the two profiles pass through a common
point, so the two increments there are exchanged as well. -/
theorem pathWeight_eSpliceAt_mul {a s₁ e₁ s₂ e₂ i : ℕ} {q r : ℕ → ℕ}
    (hq : q ∈ ePaths a s₁ e₁) (hr : r ∈ ePaths a s₂ e₂) (hmeet : q i = r i) (α : ℕ → R) :
    pathWeight a α (eSpliceAt i q r) * pathWeight a α (eSpliceAt i r q)
      = pathWeight a α q * pathWeight a α r := by
  rw [pathWeight, pathWeight, pathWeight, pathWeight, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← pow_add, ← pow_add]
  congr 1
  have hqm := hPaths_mono (ePaths_mem hq) (show k ≤ k + 1 by omega)
  have hrm := hPaths_mono (ePaths_mem hr) (show k ≤ k + 1 by omega)
  rcases lt_trichotomy (k + 1) i with h | h | h
  · rw [eSpliceAt_of_lt _ _ h, eSpliceAt_of_lt _ _ h, eSpliceAt_of_lt _ _ (by omega : k < i),
      eSpliceAt_of_lt _ _ (by omega : k < i)]
  · rw [eSpliceAt_of_ge _ _ (by omega : i ≤ k + 1), eSpliceAt_of_ge _ _ (by omega : i ≤ k + 1),
      eSpliceAt_of_lt _ _ (by omega : k < i), eSpliceAt_of_lt _ _ (by omega : k < i)]
    have hkk : q (k + 1) = r (k + 1) := by rw [← h] at hmeet; exact hmeet
    omega
  · rw [eSpliceAt_of_ge _ _ (by omega : i ≤ k + 1), eSpliceAt_of_ge _ _ (by omega : i ≤ k + 1),
      eSpliceAt_of_ge _ _ (by omega : i ≤ k), eSpliceAt_of_ge _ _ (by omega : i ≤ k)]
    omega

/-- **The transposed term is entirely meeting.**  Two odd paths whose sources
and sinks are oppositely ordered must share a point: the difference of the
profiles starts positive, ends negative, and changes by at most one at each
height, because both steps are units.  This is where the odd geometry needs its
own argument — the even model's proof runs on intervals meeting, which is a
weaker conclusion than a shared point. -/
theorem eMeets_of_lt {a s₁ e₁ s₂ e₂ : ℕ} {q r : ℕ → ℕ} (hq : q ∈ ePaths a s₁ e₁)
    (hr : r ∈ ePaths a s₂ e₂) (hs : s₂ < s₁) (he : e₁ < e₂) : EMeets a q r := by
  by_contra h
  have hsep := lt_of_not_eMeets hq hr hs h a le_rfl
  rw [hPaths_top (ePaths_mem hq) le_rfl, hPaths_top (ePaths_mem hr) le_rfl] at hsep
  omega

/-- The splice of a meeting pair, at the least height where they meet. -/
noncomputable def eSwapPair (a : ℕ) (x : (ℕ → ℕ) × (ℕ → ℕ)) : (ℕ → ℕ) × (ℕ → ℕ) :=
  (eSpliceAt (eMeetHeight a x.1 x.2) x.1 x.2, eSpliceAt (eMeetHeight a x.1 x.2) x.2 x.1)

theorem eSwapPair_eSwapPair {a : ℕ} {x : (ℕ → ℕ) × (ℕ → ℕ)} (hc : EMeets a x.1 x.2) :
    eSwapPair a (eSwapPair a x) = x := by
  have hh := eMeetHeight_eSpliceAt hc
  refine Prod.ext ?_ ?_ <;>
    · change eSpliceAt (eMeetHeight a _ _) _ _ = _
      rw [eSwapPair, hh]
      simp only []
      rw [eSpliceAt_eSpliceAt]

/-- **The odd cancellation.**  Splicing at the least meeting height is a
weight-preserving bijection from the meeting pairs of the leading term onto all
the pairs of the transposed term. -/
theorem sum_meeting_eq_sum_transposed {a s₁ e₁ s₂ e₂ : ℕ} (α : ℕ → R)
    (hs : s₂ < s₁) (he : e₂ < e₁) :
    ∑ x ∈ (ePaths a s₁ e₁ ×ˢ ePaths a s₂ e₂).filter fun x => EMeets a x.1 x.2,
        pathWeight a α x.1 * pathWeight a α x.2
      = ∑ x ∈ ePaths a s₁ e₂ ×ˢ ePaths a s₂ e₁,
        pathWeight a α x.1 * pathWeight a α x.2 := by
  refine Finset.sum_nbij' (eSwapPair a) (eSwapPair a) (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · rw [Finset.mem_filter, Finset.mem_product] at hx
    obtain ⟨⟨h1, h2⟩, hc⟩ := hx
    exact Finset.mem_product.mpr
      ⟨eSpliceAt_mem h1 h2 (eMeetHeight_le_height hc) (eMeetHeight_spec hc),
       eSpliceAt_mem h2 h1 (eMeetHeight_le_height hc) (eMeetHeight_spec hc).symm⟩
  · rw [Finset.mem_product] at hx
    obtain ⟨h1, h2⟩ := hx
    have hc : EMeets a x.1 x.2 := eMeets_of_lt h1 h2 hs (by omega)
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨eSpliceAt_mem h1 h2 (eMeetHeight_le_height hc) (eMeetHeight_spec hc),
       eSpliceAt_mem h2 h1 (eMeetHeight_le_height hc) (eMeetHeight_spec hc).symm⟩, ?_⟩
    exact ⟨eMeetHeight a x.1 x.2,
      meets_eSpliceAt (eMeetHeight_le_height hc) (eMeetHeight_spec hc)⟩
  · rw [Finset.mem_filter] at hx
    exact eSwapPair_eSwapPair hx.2
  · rw [Finset.mem_product] at hx
    exact eSwapPair_eSwapPair (eMeets_of_lt hx.1 hx.2 hs (by omega))
  · rw [Finset.mem_filter, Finset.mem_product] at hx
    obtain ⟨⟨h1, h2⟩, hc⟩ := hx
    exact (pathWeight_eSpliceAt_mul h1 h2 (eMeetHeight_spec hc) α).symm

/-- The total weight of the odd paths from `s` to `e`: the entry of the
determinant over the odd alphabet. -/
noncomputable def eEdgeSum (a : ℕ) (α : ℕ → R) (s e : ℕ) : R :=
  ∑ q ∈ ePaths a s e, pathWeight a α q

theorem ePaths_eq_empty_of_lt {a s e : ℕ} (h : e < s) : ePaths a s e = ∅ :=
  Finset.eq_empty_of_forall_notMem fun q hq =>
    absurd (hPaths_eq_empty_of_lt (b := a) h ▸ ePaths_mem hq) (Finset.notMem_empty q)

theorem eEdgeSum_eq_jtCoeff (a : ℕ) (α : ℕ → R) (s e : ℕ) :
    eEdgeSum a α s e = jtCoeff (fun m => elemHom a m α) e s := by
  rw [jtCoeff]
  rcases le_or_gt s e with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, e = s + m := ⟨e - s, by omega⟩
    rw [if_pos h, eEdgeSum, ePaths_sum_eq_elemHom, Nat.add_sub_cancel_left]
  · rw [if_neg (by omega), eEdgeSum, ePaths_eq_empty_of_lt h, Finset.sum_empty]

/-- The `2 × 2` determinant over the odd alphabet as path sums. -/
theorem elemDet_two_eq_eEdgeSum {a : ℕ} (α : ℕ → R) (lam mu : YoungDiagram) :
    jacobiTrudiDet (fun m => elemHom a m α) lam mu 2
      = eEdgeSum a α (mu.rowLen 0 + 1) (lam.rowLen 0 + 1)
          * eEdgeSum a α (mu.rowLen 1) (lam.rowLen 1)
        - eEdgeSum a α (mu.rowLen 0 + 1) (lam.rowLen 1)
          * eEdgeSum a α (mu.rowLen 1) (lam.rowLen 0 + 1) := by
  have h1 : jtCoeff (fun m => elemHom a m α) (lam.rowLen 0) (mu.rowLen 0)
      = jtCoeff (fun m => elemHom a m α) (lam.rowLen 0 + 1) (mu.rowLen 0 + 1) :=
    (jtCoeff_succ_succ _ _ _).symm
  have h2 : jtCoeff (fun m => elemHom a m α) (lam.rowLen 1 + 1) (mu.rowLen 1 + 1)
      = jtCoeff (fun m => elemHom a m α) (lam.rowLen 1) (mu.rowLen 1) :=
    jtCoeff_succ_succ _ _ _
  rw [jacobiTrudiDet, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Fin.val_zero, Fin.val_one, Nat.add_zero, eEdgeSum_eq_jtCoeff]
  rw [h1, h2]
  ring

/-- **The odd model at two paths.**  The `2 × 2` determinant
`det [e_{λ_u - μ_v - u + v}]` over the odd alphabet is the total weight of the
pairs of odd paths that share no point.  Point disjointness is the whole of the
non-intersection condition here; the interval condition of the even model would
select a different set of pairs, and check (3) of
a separate numerical check exhibits the resulting polynomial as
wrong. -/
theorem elemDet_two_eq_sum_nonMeeting {a : ℕ} (α : ℕ → R) (lam mu : YoungDiagram) :
    jacobiTrudiDet (fun m => elemHom a m α) lam mu 2
      = ∑ x ∈ (ePaths a (mu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ
                ePaths a (mu.rowLen 1) (lam.rowLen 1)).filter
                  fun x => ¬ EMeets a x.1 x.2,
          pathWeight a α x.1 * pathWeight a α x.2 := by
  have hmu : mu.rowLen 1 ≤ mu.rowLen 0 := mu.rowLen_anti 0 1 (by omega)
  have hlam : lam.rowLen 1 ≤ lam.rowLen 0 := lam.rowLen_anti 0 1 (by omega)
  rw [elemDet_two_eq_eEdgeSum, eEdgeSum, eEdgeSum, eEdgeSum, eEdgeSum, sum_mul_sum_prod,
    sum_mul_sum_prod,
    ← sum_meeting_eq_sum_transposed (a := a) (s₁ := mu.rowLen 0 + 1)
      (e₁ := lam.rowLen 0 + 1) (s₂ := mu.rowLen 1) (e₂ := lam.rowLen 1) α (by omega) (by omega),
    ← Finset.sum_filter_add_sum_filter_not
      (ePaths a (mu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ ePaths a (mu.rowLen 1) (lam.rowLen 1))
      (fun x => EMeets a x.1 x.2)]
  ring

end OddCancellation

/-! ## Two-row shapes, and the super branching rule at two rows

The intermediate shape `ν` of the super branching rule is the pair of abscissae
the two paths occupy at height `b`, so the branching sum and the splice are
indexed by the same data once a shape inside two rows is identified with its two
row lengths.
-/

section TwoRow

/-- The Young diagram with rows `l₀ ≥ l₁` and no others. -/
def twoRow (l₀ l₁ : ℕ) : YoungDiagram := rect 1 l₀ ⊔ rect 2 l₁

theorem mem_twoRow {l₀ l₁ i j : ℕ} :
    (i, j) ∈ twoRow l₀ l₁ ↔ (i < 1 ∧ j < l₀) ∨ (i < 2 ∧ j < l₁) := by
  rw [twoRow, YoungDiagram.mem_sup, mem_rect, mem_rect]

theorem rowLen_twoRow_zero {l₀ l₁ : ℕ} (h : l₁ ≤ l₀) : (twoRow l₀ l₁).rowLen 0 = l₀ := by
  have key : ∀ j : ℕ, (0, j) ∈ twoRow l₀ l₁ ↔ j < l₀ := by
    intro j
    rw [mem_twoRow]
    omega
  have h1 := key ((twoRow l₀ l₁).rowLen 0)
  have h2 := key l₀
  rw [YoungDiagram.mem_iff_lt_rowLen] at h1 h2
  omega

theorem rowLen_twoRow_one (l₀ l₁ : ℕ) : (twoRow l₀ l₁).rowLen 1 = l₁ := by
  have key : ∀ j : ℕ, (1, j) ∈ twoRow l₀ l₁ ↔ j < l₁ := by
    intro j
    rw [mem_twoRow]
    omega
  have h1 := key ((twoRow l₀ l₁).rowLen 1)
  have h2 := key l₁
  rw [YoungDiagram.mem_iff_lt_rowLen] at h1 h2
  omega

theorem rowLen_twoRow_of_le (l₀ l₁ : ℕ) {i : ℕ} (hi : 2 ≤ i) : (twoRow l₀ l₁).rowLen i = 0 := by
  by_contra hc
  have hmem : (i, 0) ∈ twoRow l₀ l₁ :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hc)
  rw [mem_twoRow] at hmem
  omega

/-- A Young diagram is determined by its row lengths. -/
theorem eq_of_rowLen {mu lam : YoungDiagram} (h : ∀ i, mu.rowLen i = lam.rowLen i) : mu = lam := by
  refine YoungDiagram.ext (Finset.ext fun c => ?_)
  obtain ⟨i, j⟩ := c
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen, h i]

/-- Containment of Young diagrams is containment of row lengths. -/
theorem le_iff_rowLen {mu lam : YoungDiagram} : mu ≤ lam ↔ ∀ i, mu.rowLen i ≤ lam.rowLen i := by
  refine ⟨fun h i => rowLen_mono h i, fun h c hc => ?_⟩
  obtain ⟨i, j⟩ := c
  rw [YoungDiagram.mem_iff_lt_rowLen] at hc ⊢
  exact lt_of_lt_of_le hc (h i)

/-- A diagram inside two rows is the `twoRow` of its two row lengths. -/
theorem eq_twoRow {nu : YoungDiagram} (h : ∀ i, 2 ≤ i → nu.rowLen i = 0) :
    nu = twoRow (nu.rowLen 0) (nu.rowLen 1) := by
  have hle : nu.rowLen 1 ≤ nu.rowLen 0 := nu.rowLen_anti 0 1 (by omega)
  refine eq_of_rowLen fun i => ?_
  match i with
  | 0 => rw [rowLen_twoRow_zero hle]
  | 1 => rw [rowLen_twoRow_one]
  | (n + 2) => rw [rowLen_twoRow_of_le _ _ (by omega), h _ (by omega)]

variable {R : Type*} [CommRing R]

/-- **Residue: the odd tableau bijection.**  The non-meeting pairs of odd paths
for a pair of two-row shapes carry the total weight of the tableaux of the
conjugate shape `λ' / ν'`, the second factor of the super branching rule.

This is the odd counterpart of `NonCrossingIsSkewSchur`, and like it it is a
theorem: `nonMeetingIsSkewSchurTranspose`, at every `a` and `α`.
The geometry it consumes is here — `lt_of_not_eMeets` supplies the separation and
`pathLetter` the letters, the latter strictly increasing
(`pathLetter_strictMono`), which is what makes the tableau a column of
`λ' / ν'` rather than a row of `λ / ν`.

Checked over the same search box as the even statement by
a separate numerical check, checks (1) and (7). -/
def NonMeetingIsSkewSchurTranspose (a : ℕ) (α : ℕ → R) : Prop :=
  ∀ lam nu : YoungDiagram, nu ≤ lam → (∀ i, 2 ≤ i → lam.rowLen i = 0) →
    ∑ x ∈ (ePaths a (nu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ
            ePaths a (nu.rowLen 1) (lam.rowLen 1)).filter fun x => ¬ EMeets a x.1 x.2,
        pathWeight a α x.1 * pathWeight a α x.2
      = skewSchur lam.transpose nu.transpose a α

/-- A pair of odd paths whose sources are not strictly ordered downward either
meets or has its sinks in the wrong order.  This is what empties the fibers of
the splice that no intermediate shape indexes. -/
theorem eSum_filter_eq_empty {a c₁ c₂ e₁ e₂ : ℕ} (hc : c₁ ≤ c₂) (he : e₂ ≤ e₁) :
    ((ePaths a c₁ e₁ ×ˢ ePaths a c₂ e₂).filter fun z => ¬ EMeets a z.1 z.2) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
  rw [Finset.mem_filter, Finset.mem_product] at hz
  obtain ⟨⟨h1, h2⟩, hmeet⟩ := hz
  rcases eq_or_lt_of_le hc with rfl | hlt
  · exact hmeet ⟨0, mem_eMeetSet.mpr ⟨Nat.zero_le a, by
      rw [hPaths_zero (ePaths_mem h1), hPaths_zero (ePaths_mem h2)]⟩⟩
  · have hsym : ¬ EMeets a z.2 z.1 := fun hc' => hmeet (by rwa [EMeets, eMeetSet_comm])
    have := lt_of_not_eMeets h2 h1 hlt hsym a le_rfl
    rw [hPaths_top (ePaths_mem h1) le_rfl, hPaths_top (ePaths_mem h2) le_rfl] at this
    omega

end TwoRow

/-! ## Axiom-footprint guards

The same regression test `Shields.AxiomCheck` runs on the rest of the
development: a `sorry` anywhere in a dependency chain makes `#print axioms`
report `sorryAx` and the build fails.
-/

section AxiomGuards

end AxiomGuards


/-! ### Axiom footprint -/

/-- info: 'Shields.ePaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ePaths

/-- info: 'Shields.mixedPaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixedPaths

/-- info: 'Shields.mixedWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixedWeight

/-- info: 'Shields.eSwapPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eSwapPair

/-- info: 'Shields.MixedMeets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MixedMeets

/-- info: 'Shields.ePathOfWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ePathOfWord

end Shields
