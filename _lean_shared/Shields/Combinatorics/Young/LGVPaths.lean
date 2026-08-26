/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.JacobiTrudi

namespace Shields

open Finset

/-! ## The sign-reversing involution

Mathlib has `Finset.sum_involution`: an involution `g` on a `Finset` with
`f a + f (g a) = 0` throughout forces the sum to vanish.  Lindström--Gessel--Viennot
needs it in the form where the involution is only defined — only fixed-point-free
— off a distinguished subpredicate, the sum collapsing to that subpredicate
rather than to zero.
-/

section Involution

variable {ι M : Type*} [AddCommGroup M]

/-- **The engine.**  If `g` maps the part of `s` where `P` fails into itself
without fixed points, is involutive there, and reverses the sign of `f`, then
only the part where `P` holds survives.

The four hypotheses are exactly the four obligations of `Finset.sum_involution`,
relativized to `¬ P`; `gP` is the extra one, that the involution does not escape
the part it is defined on. -/
theorem sum_eq_sum_filter_of_signReversing (s : Finset ι) (f : ι → M) (P : ι → Prop)
    [DecidablePred P] (g : ι → ι) (gmem : ∀ a ∈ s, ¬ P a → g a ∈ s)
    (gP : ∀ a ∈ s, ¬ P a → ¬ P (g a)) (gne : ∀ a ∈ s, ¬ P a → g a ≠ a)
    (ginv : ∀ a ∈ s, ¬ P a → g (g a) = a) (gsign : ∀ a ∈ s, ¬ P a → f a + f (g a) = 0) :
    ∑ a ∈ s, f a = ∑ a ∈ s.filter P, f a := by
  have hzero : ∑ a ∈ s.filter (fun a => ¬ P a), f a = 0 := by
    have hmem : ∀ a ∈ s.filter (fun a => ¬ P a), g a ∈ s.filter (fun a => ¬ P a) := by
      intro a ha
      rw [mem_filter] at ha ⊢
      exact ⟨gmem a ha.1 ha.2, gP a ha.1 ha.2⟩
    refine Finset.sum_involution (fun a _ => g a) (fun a ha => gsign a ?_ ?_)
      (fun a ha _ => gne a ?_ ?_) (fun a ha => hmem a ha) (fun a ha => ginv a ?_ ?_) <;>
      first
        | exact (mem_filter.mp ha).1
        | exact (mem_filter.mp ha).2
  rw [← Finset.sum_filter_add_sum_filter_not s P f, hzero, add_zero]

end Involution

/-! ## Paths

A path across `b` heights is recorded by its **profile**: `p i` is the abscissa
at which the path arrives at height `i`, so between heights `i` and `i+1` it
sweeps the abscissae `p i, …, p (i+1)` and then steps north.  Profiles are
carried as functions `ℕ → ℕ`, constant from `b` on, which keeps every index
computation free of `Fin` coercions; the `Finset` of them is cut out of a product
of intervals.
-/

section Paths

/-- The profiles of paths from `s` to `e` across `b` heights: monotone, starting
at `s`, and constant at `e` from height `b` on. -/
noncomputable def hPaths (b s e : ℕ) : Finset (ℕ → ℕ) := by
  classical
  exact ((Fintype.piFinset fun _ : Fin (b + 1) => Finset.Icc s e).image
      fun p i => p ⟨min i b, Nat.lt_succ_of_le (min_le_right i b)⟩).filter
    fun q => q 0 = s ∧ Monotone q ∧ ∀ i, b ≤ i → q i = e

theorem mem_hPaths {b s e : ℕ} {q : ℕ → ℕ} :
    q ∈ hPaths b s e ↔ q 0 = s ∧ Monotone q ∧ ∀ i, b ≤ i → q i = e := by
  classical
  rw [hPaths, mem_filter, and_iff_right_iff_imp]
  rintro ⟨h0, hmono, htop⟩
  refine mem_image.mpr ⟨fun i : Fin (b + 1) => q i, ?_, ?_⟩
  · refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · rw [← h0]; exact hmono (Nat.zero_le _)
    · rw [← htop b le_rfl]; exact hmono (Nat.lt_succ_iff.mp i.isLt)
  · funext i
    rcases le_or_gt b i with hi | hi
    · simp only [min_eq_right hi]
      rw [htop b le_rfl, htop i hi]
    · simp [min_eq_left hi.le]

theorem hPaths_zero {b s e : ℕ} {q : ℕ → ℕ} (hq : q ∈ hPaths b s e) : q 0 = s :=
  (mem_hPaths.mp hq).1

theorem hPaths_mono {b s e : ℕ} {q : ℕ → ℕ} (hq : q ∈ hPaths b s e) : Monotone q :=
  (mem_hPaths.mp hq).2.1

theorem hPaths_top {b s e : ℕ} {q : ℕ → ℕ} (hq : q ∈ hPaths b s e) {i : ℕ} (hi : b ≤ i) :
    q i = e :=
  (mem_hPaths.mp hq).2.2 i hi

theorem hPaths_le {b s e : ℕ} {q : ℕ → ℕ} (hq : q ∈ hPaths b s e) (i : ℕ) : s ≤ q i ∧ q i ≤ e := by
  refine ⟨?_, ?_⟩
  · rw [← hPaths_zero hq]; exact hPaths_mono hq (Nat.zero_le i)
  · rw [← hPaths_top hq (le_max_right i b)]
    exact hPaths_mono hq (le_max_left i b)

variable {R : Type*} [CommSemiring R]

/-- The weight of a path: the step at height `i` contributes `β i` once per east
move. -/
noncomputable def pathWeight (b : ℕ) (β : ℕ → R) (q : ℕ → ℕ) : R :=
  ∏ i ∈ Finset.range b, β i ^ (q (i + 1) - q i)

end Paths

/-! ## A path is a word, and the path sum is `completeHom`

A path from `s` to `e` writes a letter at each abscissa it crosses: the letter at
`s + j` is the height at which the crossing happens.  The letters weakly increase,
so the word is a one-row semistandard tableau of length `e - s`, and the two
descriptions are inverse.  This is `rung 2`: it identifies the alphabet the path
model is about as `completeHom`, the even factor of `superHom`.
-/

section PathWord

/-- The letter a path writes at abscissa `s + j`: the number of heights already
left behind, which is the height at which the path crosses. -/
noncomputable def pathLetter (b s : ℕ) (q : ℕ → ℕ) (j : ℕ) : ℕ :=
  ((Finset.range b).filter fun i => q (i + 1) ≤ s + j).card

theorem pathLetter_mono (b s : ℕ) (q : ℕ → ℕ) {j₁ j₂ : ℕ} (h : j₁ ≤ j₂) :
    pathLetter b s q j₁ ≤ pathLetter b s q j₂ :=
  Finset.card_le_card fun i hi => by
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, le_trans hi.2 (by omega)⟩

theorem pathLetter_le (b s : ℕ) (q : ℕ → ℕ) (j : ℕ) : pathLetter b s q j ≤ b := by
  rw [pathLetter]
  exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range b))

/-- **The crossing height is where the profile passes the abscissa.**  For a path
from `s` to `e` and a height `i ≤ b`, the letter at `s + j` is below `i` exactly
when the profile has already passed `s + j` at height `i`. -/
theorem pathLetter_lt_iff {b s e : ℕ} {q : ℕ → ℕ} (hq : q ∈ hPaths b s e) {j i : ℕ}
    (hi : i ≤ b) : pathLetter b s q j < i ↔ s + j < q i := by
  constructor
  · intro h
    by_contra hcon
    have hle : q i ≤ s + j := by omega
    have hsub : Finset.range i ⊆ (Finset.range b).filter fun i' => q (i' + 1) ≤ s + j := by
      intro i' hi'
      rw [Finset.mem_range] at hi'
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        le_trans (hPaths_mono hq (by omega : i' + 1 ≤ i)) hle⟩
    have hge : i ≤ pathLetter b s q j := by
      rw [pathLetter]
      exact le_trans (le_of_eq (Finset.card_range i).symm) (Finset.card_le_card hsub)
    omega
  · intro h
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hPaths_zero hq] at h; omega
    have hsub : ((Finset.range b).filter fun i' => q (i' + 1) ≤ s + j)
        ⊆ Finset.range (i - 1) := by
      intro i' hi'
      rw [Finset.mem_filter, Finset.mem_range] at hi'
      rw [Finset.mem_range]
      by_contra hcon
      exact absurd (hPaths_mono hq (by omega : i ≤ i' + 1)) (by omega)
    have hle : pathLetter b s q j ≤ i - 1 := by
      rw [pathLetter]
      exact le_trans (Finset.card_le_card hsub) (le_of_eq (Finset.card_range _))
    omega

/-- The letters of a path from `s` to `e` are heights, so they are below `b`
wherever the path still has ground to cover. -/
theorem pathLetter_lt_height {b s e : ℕ} {q : ℕ → ℕ} (hq : q ∈ hPaths b s e) {j : ℕ}
    (hj : s + j < e) : pathLetter b s q j < b := by
  rw [pathLetter_lt_iff hq le_rfl, hPaths_top hq le_rfl]
  exact hj

/-- **The letters below a height count the abscissae already passed.**  This is
the inverse dictionary: the profile is recovered from the word. -/
theorem card_pathLetter_lt {b s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ hPaths b s (s + m)) {i : ℕ}
    (hi : i ≤ b) :
    ((Finset.range m).filter fun j => pathLetter b s q j < i).card = q i - s := by
  have hval : ((Finset.range m).filter fun j => pathLetter b s q j < i)
      = Finset.range (q i - s) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, pathLetter_lt_iff hq hi]
    have h1 := (hPaths_le hq i).2
    constructor
    · rintro ⟨-, h⟩; omega
    · intro h; exact ⟨by omega, by omega⟩
  rw [hval, Finset.card_range]

/-- Rows of a one-row bounded tableau are weakly increasing. -/
theorem boundedSSYT_row_mono {m b : ℕ} (T : BoundedSSYT (rect 1 m) b) {j₁ j₂ : ℕ}
    (h : j₁ ≤ j₂) (hj₂ : j₂ < m) : T 0 j₁ ≤ T 0 j₂ := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  · exact T.1.row_weak hlt (mem_rect.mpr ⟨Nat.zero_lt_one, hj₂⟩)

end PathWord

section PathSum

variable {R : Type*} [CommRing R]

/-- The word of a path, as a one-row tableau.  Rows weakly increase because the
letter count is monotone in the abscissa; the column condition is vacuous on a
shape of one row. -/
noncomputable def wordOfPath (b s m : ℕ) (q : ℕ → ℕ) (hq : q ∈ hPaths b s (s + m)) :
    BoundedSSYT (rect 1 m) b :=
  ⟨{ entry := fun i j => if i = 0 ∧ j < m then pathLetter b s q j else 0
     row_weak' := by
       intro i j₁ j₂ hj hcell
       obtain ⟨hi, hj₂⟩ := mem_rect.mp hcell
       rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, hj₂⟩]
       exact pathLetter_mono b s q hj.le
     col_strict' := by
       intro i₁ i₂ j hi hcell
       exact absurd (mem_rect.mp hcell).1 (by omega)
     zeros' := by
       intro i j hcell
       refine if_neg fun hc => hcell (mem_rect.mpr ⟨by omega, hc.2⟩)
   },
   by
     intro i j hcell
     obtain ⟨hi, hj⟩ := mem_rect.mp hcell
     change (if i = 0 ∧ j < m then pathLetter b s q j else 0) < b
     rw [if_pos ⟨by omega, hj⟩]
     exact pathLetter_lt_height hq (by omega)⟩

theorem wordOfPath_apply {b s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ hPaths b s (s + m)) (i j : ℕ) :
    wordOfPath b s m q hq i j = if i = 0 ∧ j < m then pathLetter b s q j else 0 :=
  rfl

/-- The profile of a word: the abscissa reached at height `i` is `s` plus the
number of letters below `i`. -/
noncomputable def pathOfWord (b s m : ℕ) (T : BoundedSSYT (rect 1 m) b) (i : ℕ) : ℕ :=
  s + ((Finset.range m).filter fun j => T 0 j < i).card

theorem pathOfWord_mem (b s m : ℕ) (T : BoundedSSYT (rect 1 m) b) :
    pathOfWord b s m T ∈ hPaths b s (s + m) := by
  refine mem_hPaths.mpr ⟨by simp [pathOfWord], fun i₁ i₂ h => ?_, fun i hi => ?_⟩
  · refine Nat.add_le_add_left (Finset.card_le_card fun j hj => ?_) s
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, by omega⟩
  · have hfull : ((Finset.range m).filter fun j => T 0 j < i) = Finset.range m :=
      Finset.filter_true_of_mem fun j hj =>
        lt_of_lt_of_le (T.lt (mem_rect.mpr ⟨Nat.zero_lt_one, Finset.mem_range.mp hj⟩)) hi
    rw [pathOfWord, hfull, Finset.card_range]

theorem pathOfWord_wordOfPath {b s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ hPaths b s (s + m)) :
    pathOfWord b s m (wordOfPath b s m q hq) = q := by
  funext i
  have hset : ∀ k : ℕ, ((Finset.range m).filter fun j => wordOfPath b s m q hq 0 j < k)
      = (Finset.range m).filter fun j => pathLetter b s q j < k := by
    intro k
    ext j
    rw [Finset.mem_filter, Finset.mem_filter, wordOfPath_apply]
    constructor
    · rintro ⟨hj, h⟩
      rw [if_pos ⟨rfl, Finset.mem_range.mp hj⟩] at h
      exact ⟨hj, h⟩
    · rintro ⟨hj, h⟩
      exact ⟨hj, by rw [if_pos ⟨rfl, Finset.mem_range.mp hj⟩]; exact h⟩
  rcases le_or_gt i b with hi | hi
  · rw [pathOfWord, hset, card_pathLetter_lt hq hi]
    have := (hPaths_le hq i).1
    omega
  · rw [pathOfWord, hset, hPaths_top hq hi.le]
    have hfull : ((Finset.range m).filter fun j => pathLetter b s q j < i)
        = Finset.range m :=
      Finset.filter_true_of_mem fun j _ => lt_of_le_of_lt (pathLetter_le b s q j) hi
    rw [hfull, Finset.card_range]

/-- The letter the profile of a word writes at abscissa `s + j` is the word's own
letter there: below a height `i'`, the profile has passed `s + j` exactly when
`T 0 j` exceeds `i'`. -/
theorem pathLetter_pathOfWord {b s m : ℕ} (T : BoundedSSYT (rect 1 m) b) {j : ℕ}
    (hj : j < m) : pathLetter b s (pathOfWord b s m T) j = T 0 j := by
  have hcell : (0, j) ∈ rect 1 m := mem_rect.mpr ⟨Nat.zero_lt_one, hj⟩
  have hset : ((Finset.range b).filter
      fun i' => pathOfWord b s m T (i' + 1) ≤ s + j) = Finset.range (T 0 j) := by
    ext i'
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, pathOfWord,
      Nat.add_le_add_iff_left]
    constructor
    · rintro ⟨-, h⟩
      by_contra hcon
      have hsub : Finset.range (j + 1)
          ⊆ (Finset.range m).filter fun j' => T 0 j' < i' + 1 := by
        intro j' hj'
        rw [Finset.mem_range] at hj'
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
          lt_of_le_of_lt (boundedSSYT_row_mono T (by omega) hj) (by omega)⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      omega
    · intro h
      refine ⟨lt_trans h (T.lt hcell), ?_⟩
      have hsub : ((Finset.range m).filter fun j' => T 0 j' < i' + 1) ⊆ Finset.range j := by
        intro j' hj'
        rw [Finset.mem_filter, Finset.mem_range] at hj'
        rw [Finset.mem_range]
        by_contra hcon
        exact absurd (boundedSSYT_row_mono T (by omega : j ≤ j') hj'.1) (by omega)
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      omega
  rw [pathLetter, hset, Finset.card_range]

theorem wordOfPath_pathOfWord {b s m : ℕ} (T : BoundedSSYT (rect 1 m) b) :
    wordOfPath b s m (pathOfWord b s m T) (pathOfWord_mem b s m T) = T := by
  refine BoundedSSYT.ext fun i j => ?_
  rw [wordOfPath_apply]
  by_cases hc : i = 0 ∧ j < m
  · obtain ⟨rfl, hj⟩ := hc
    rw [if_pos ⟨rfl, hj⟩, pathLetter_pathOfWord T hj]
  · rw [if_neg hc]
    exact (T.zeros fun h => hc ⟨by have := (mem_rect.mp h).1; omega,
      (mem_rect.mp h).2⟩).symm

/-- The weight of a path is the product of its letters.  Both sides are grouped
by height: the letters equal to `i` are exactly the abscissae the path passes at
height `i`, and there are `q (i+1) - q i` of them. -/
theorem pathWeight_eq_prod_letters {b s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ hPaths b s (s + m))
    (β : ℕ → R) :
    pathWeight b β q = ∏ j ∈ Finset.range m, β (pathLetter b s q j) := by
  rw [← Finset.prod_fiberwise_of_maps_to (g := pathLetter b s q) (t := Finset.range b)
    (fun j hj => Finset.mem_range.mpr
      (pathLetter_lt_height hq (by have := Finset.mem_range.mp hj; omega)))
    (fun j => β (pathLetter b s q j))]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hib := Finset.mem_range.mp hi
  rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
    Finset.prod_const]
  congr 1
  have h1 := card_pathLetter_lt hq (le_of_lt hib)
  have h2 := card_pathLetter_lt hq (show i + 1 ≤ b by omega)
  have hsplit : ((Finset.range m).filter fun j => pathLetter b s q j < i + 1)
      = ((Finset.range m).filter fun j => pathLetter b s q j < i)
        ∪ ((Finset.range m).filter fun j => pathLetter b s q j = i) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    omega
  have hdisj : Disjoint ((Finset.range m).filter fun j => pathLetter b s q j < i)
      ((Finset.range m).filter fun j => pathLetter b s q j = i) := by
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    simp only [Finset.mem_filter] at hj₁ hj₂
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj] at h2
  have h3 := hPaths_mono hq (show i ≤ i + 1 by omega)
  have h4 := (hPaths_le hq i).1
  omega

/-- **Rung 2.**  The paths from `s` to `s + m` across `b` heights carry total
weight `h_m(β_0, …, β_{b-1})`, the `completeHom` of `Shields.JacobiTrudi`.
This is what the path model is a model *of*: the even factor of the alphabet
`ρ_D` that is an identity over. -/
theorem hPaths_sum_eq_completeHom (b s m : ℕ) (β : ℕ → R) :
    ∑ q ∈ hPaths b s (s + m), pathWeight b β q = completeHom b m β := by
  rw [completeHom, skewSchur_bot, schur]
  refine Finset.sum_bij' (fun q hq => wordOfPath b s m q hq) (fun T _ => pathOfWord b s m T)
    (fun q _ => Finset.mem_univ _) (fun T _ => pathOfWord_mem b s m T)
    (fun q hq => pathOfWord_wordOfPath hq) (fun T _ => wordOfPath_pathOfWord T)
    (fun q hq => ?_)
  rw [pathWeight_eq_prod_letters hq, cells_rect, Finset.prod_product, Finset.prod_range_one]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [wordOfPath_apply, if_pos ⟨rfl, Finset.mem_range.mp hj⟩]

end PathSum


/-! ## Crossing, and the tail swap

Two paths cross at height `i` when the abscissa intervals `[q i, q (i+1)]` and
`[r i, r (i+1)]` they sweep there meet.  Splicing at the least such height
exchanges their sinks, keeps both profiles monotone, preserves the product of
their weights, and is an involution.  That is the whole Lindström--Gessel--Viennot
cancellation; only the bookkeeping that selects the crossing grows with the
number of paths.
-/

section Crossing

/-- The heights below `b` at which the two paths share a lattice point. -/
def crossSet (b : ℕ) (q r : ℕ → ℕ) : Finset ℕ :=
  (Finset.range b).filter fun i => q i ≤ r (i + 1) ∧ r i ≤ q (i + 1)

/-- Two paths cross when they share a lattice point. -/
def Crosses (b : ℕ) (q r : ℕ → ℕ) : Prop := (crossSet b q r).Nonempty

instance (b : ℕ) (q r : ℕ → ℕ) : Decidable (Crosses b q r) :=
  inferInstanceAs (Decidable (crossSet b q r).Nonempty)

theorem mem_crossSet {b : ℕ} {q r : ℕ → ℕ} {i : ℕ} :
    i ∈ crossSet b q r ↔ i < b ∧ q i ≤ r (i + 1) ∧ r i ≤ q (i + 1) := by
  rw [crossSet, Finset.mem_filter, Finset.mem_range]

theorem crossSet_comm (b : ℕ) (q r : ℕ → ℕ) : crossSet b q r = crossSet b r q := by
  ext i
  rw [mem_crossSet, mem_crossSet]
  tauto

/-- The least height at which the two paths cross; `0` when they do not. -/
noncomputable def crossHeight (b : ℕ) (q r : ℕ → ℕ) : ℕ :=
  if h : Crosses b q r then (crossSet b q r).min' h else 0

theorem crossHeight_mem {b : ℕ} {q r : ℕ → ℕ} (h : Crosses b q r) :
    crossHeight b q r ∈ crossSet b q r := by
  rw [crossHeight, dif_pos h]
  exact Finset.min'_mem _ h

theorem crossHeight_lt {b : ℕ} {q r : ℕ → ℕ} (h : Crosses b q r) : crossHeight b q r < b :=
  (mem_crossSet.mp (crossHeight_mem h)).1

theorem crossHeight_le {b : ℕ} {q r : ℕ → ℕ} (h : Crosses b q r) {k : ℕ}
    (hk : k ∈ crossSet b q r) : crossHeight b q r ≤ k := by
  rw [crossHeight, dif_pos h]
  exact Finset.min'_le _ _ hk

/-- The profile that follows `q` up to height `i` and `r` from height `i+1` on. -/
def spliceAt (i : ℕ) (q r : ℕ → ℕ) (k : ℕ) : ℕ := if k ≤ i then q k else r k

@[simp]
theorem spliceAt_of_le {i : ℕ} (q r : ℕ → ℕ) {k : ℕ} (hk : k ≤ i) : spliceAt i q r k = q k :=
  if_pos hk

@[simp]
theorem spliceAt_of_gt {i : ℕ} (q r : ℕ → ℕ) {k : ℕ} (hk : i < k) : spliceAt i q r k = r k :=
  if_neg (by omega)

/-- Splicing twice at the same height gives back the first path: the two spliced
profiles agree with `q` below `i` and above it respectively. -/
theorem spliceAt_spliceAt (i : ℕ) (q r : ℕ → ℕ) :
    spliceAt i (spliceAt i q r) (spliceAt i r q) = q := by
  funext k
  rcases le_or_gt k i with hk | hk
  · rw [spliceAt_of_le _ _ hk, spliceAt_of_le _ _ hk]
  · rw [spliceAt_of_gt _ _ hk, spliceAt_of_gt _ _ hk]

/-- A splice at a crossing height is again a path, from `q`'s source to `r`'s
sink.  Monotonicity across the splice is exactly one half of the crossing
condition. -/
theorem spliceAt_mem {b s₁ e₁ s₂ e₂ i : ℕ} {q r : ℕ → ℕ} (hq : q ∈ hPaths b s₁ e₁)
    (hr : r ∈ hPaths b s₂ e₂) (hi : i < b) (hc : q i ≤ r (i + 1)) :
    spliceAt i q r ∈ hPaths b s₁ e₂ := by
  refine mem_hPaths.mpr ⟨by rw [spliceAt_of_le _ _ (Nat.zero_le i)]; exact hPaths_zero hq,
    ?_, fun k hk => by rw [spliceAt_of_gt _ _ (by omega)]; exact hPaths_top hr hk⟩
  intro k₁ k₂ h
  rcases le_or_gt k₂ i with h₂ | h₂
  · rw [spliceAt_of_le _ _ (by omega), spliceAt_of_le _ _ h₂]
    exact hPaths_mono hq h
  · rcases le_or_gt k₁ i with h₁ | h₁
    · rw [spliceAt_of_le _ _ h₁, spliceAt_of_gt _ _ h₂]
      exact le_trans (le_trans (hPaths_mono hq h₁) hc) (hPaths_mono hr (by omega))
    · rw [spliceAt_of_gt _ _ h₁, spliceAt_of_gt _ _ h₂]
      exact hPaths_mono hr h

/-- The spliced pair crosses at the splice height: there both profiles are
monotone across the step, which is the crossing condition read for the swapped
pair. -/
theorem crossesAt_spliceAt {b s₁ e₁ s₂ e₂ i : ℕ} {q r : ℕ → ℕ} (hq : q ∈ hPaths b s₁ e₁)
    (hr : r ∈ hPaths b s₂ e₂) (hi : i < b) :
    i ∈ crossSet b (spliceAt i q r) (spliceAt i r q) := by
  refine mem_crossSet.mpr ⟨hi, ?_, ?_⟩
  · rw [spliceAt_of_le _ _ le_rfl, spliceAt_of_gt _ _ (by omega : i < i + 1)]
    exact hPaths_mono hq (by omega : i ≤ i + 1)
  · rw [spliceAt_of_le _ _ le_rfl, spliceAt_of_gt _ _ (by omega : i < i + 1)]
    exact hPaths_mono hr (by omega : i ≤ i + 1)

/-- Below the splice height the two spliced profiles are the originals, so they
cross exactly where the originals do. -/
theorem mem_crossSet_spliceAt_of_lt {b i k : ℕ} (q r : ℕ → ℕ) (hk : k < i) (_hkb : k < b) :
    k ∈ crossSet b (spliceAt i q r) (spliceAt i r q) ↔ k ∈ crossSet b q r := by
  rw [mem_crossSet, mem_crossSet, spliceAt_of_le _ _ (by omega : k ≤ i),
    spliceAt_of_le _ _ (by omega : k ≤ i), spliceAt_of_le _ _ (by omega : k + 1 ≤ i),
    spliceAt_of_le _ _ (by omega : k + 1 ≤ i)]

/-- **The splice height is preserved.**  Splicing at the least crossing height
leaves that height least, which is what makes the swap an involution. -/
theorem crossHeight_spliceAt {b s₁ e₁ s₂ e₂ : ℕ} {q r : ℕ → ℕ} (hq : q ∈ hPaths b s₁ e₁)
    (hr : r ∈ hPaths b s₂ e₂) (h : Crosses b q r) :
    crossHeight b (spliceAt (crossHeight b q r) q r) (spliceAt (crossHeight b q r) r q)
      = crossHeight b q r := by
  set i := crossHeight b q r with hi
  have hib : i < b := crossHeight_lt h
  have hmem := crossesAt_spliceAt hq hr hib
  have hcross : Crosses b (spliceAt i q r) (spliceAt i r q) := ⟨i, hmem⟩
  refine le_antisymm (crossHeight_le hcross hmem) ?_
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hk := crossHeight_mem hcross
  have hkb' : crossHeight b (spliceAt i q r) (spliceAt i r q) < b := crossHeight_lt hcross
  rw [mem_crossSet_spliceAt_of_lt q r hcon hkb'] at hk
  exact absurd (crossHeight_le h hk) (by omega)

variable {R : Type*} [CommRing R]

/-- **The swap preserves weight.**  At every height other than the splice the two
step counts are merely exchanged; at the splice their sum is unchanged, because
the two intervals overlap. -/
theorem pathWeight_spliceAt_mul {b s₁ e₁ s₂ e₂ i : ℕ} {q r : ℕ → ℕ}
    (hq : q ∈ hPaths b s₁ e₁) (hr : r ∈ hPaths b s₂ e₂)
    (hc : q i ≤ r (i + 1) ∧ r i ≤ q (i + 1)) (β : ℕ → R) :
    pathWeight b β (spliceAt i q r) * pathWeight b β (spliceAt i r q)
      = pathWeight b β q * pathWeight b β r := by
  rw [pathWeight, pathWeight, pathWeight, pathWeight, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  obtain ⟨hc1, hc2⟩ := hc
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← pow_add, ← pow_add]
  congr 1
  have hqm := hPaths_mono hq (show k ≤ k + 1 by omega)
  have hrm := hPaths_mono hr (show k ≤ k + 1 by omega)
  rcases lt_trichotomy k i with hk | rfl | hk
  · rw [spliceAt_of_le _ _ (by omega : k ≤ i), spliceAt_of_le _ _ (by omega : k ≤ i),
      spliceAt_of_le _ _ (by omega : k + 1 ≤ i), spliceAt_of_le _ _ (by omega : k + 1 ≤ i)]
  · rw [spliceAt_of_le _ _ le_rfl, spliceAt_of_le _ _ le_rfl,
      spliceAt_of_gt _ _ (by omega : k < k + 1), spliceAt_of_gt _ _ (by omega : k < k + 1)]
    omega
  · rw [spliceAt_of_gt _ _ (by omega : i < k), spliceAt_of_gt _ _ (by omega : i < k),
      spliceAt_of_gt _ _ (by omega : i < k + 1), spliceAt_of_gt _ _ (by omega : i < k + 1)]
    omega

end Crossing

/-! ## The cancellation at two paths

The `2 × 2` Jacobi--Trudi determinant is a difference of two path sums.  Every
pair in the subtracted term crosses, every crossing pair of the leading term is
carried to it by the splice, and the splice is a weight-preserving bijection, so
what survives is the non-crossing pairs.
-/

section TwoPaths

variable {R : Type*} [CommRing R]

theorem hPaths_eq_empty_of_lt {b s e : ℕ} (h : e < s) : hPaths b s e = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun q hq => ?_
  have h1 := hPaths_zero hq
  have h2 := hPaths_top hq (le_refl b)
  have h3 := hPaths_mono hq (Nat.zero_le b)
  omega

/-- The total weight of the paths from `s` to `e`: the entry of the
Jacobi--Trudi matrix over the even alphabet. -/
noncomputable def edgeSum (b : ℕ) (β : ℕ → R) (s e : ℕ) : R :=
  ∑ q ∈ hPaths b s e, pathWeight b β q

theorem edgeSum_eq_jtCoeff (b : ℕ) (β : ℕ → R) (s e : ℕ) :
    edgeSum b β s e = jtCoeff (fun m => completeHom b m β) e s := by
  rw [jtCoeff]
  rcases le_or_gt s e with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, e = s + m := ⟨e - s, by omega⟩
    rw [if_pos h, edgeSum, hPaths_sum_eq_completeHom, Nat.add_sub_cancel_left]
  · rw [if_neg (by omega), edgeSum, hPaths_eq_empty_of_lt h, Finset.sum_empty]

/-- Shifting both indices of a Jacobi--Trudi entry leaves it unchanged: only the
difference of the two is read. -/
theorem jtCoeff_succ_succ (d : ℕ → R) (p q : ℕ) : jtCoeff d (p + 1) (q + 1) = jtCoeff d p q := by
  unfold jtCoeff
  split_ifs with h1 h2 h2
  · congr 1
    omega
  · omega
  · omega
  · rfl

/-- **The `2 × 2` determinant as path sums.**  The sources are `μ_0 + 1, μ_1` and
the sinks `λ_0 + 1, λ_1`: the shift by `m - 1 - u` turns weakly decreasing row
lengths into strictly decreasing endpoints, which is what makes a non-crossing
family force the identity permutation. -/
theorem jacobiTrudiDet_two_eq_edgeSum {b : ℕ} (β : ℕ → R) (lam mu : YoungDiagram) :
    jacobiTrudiDet (fun m => completeHom b m β) lam mu 2
      = edgeSum b β (mu.rowLen 0 + 1) (lam.rowLen 0 + 1)
          * edgeSum b β (mu.rowLen 1) (lam.rowLen 1)
        - edgeSum b β (mu.rowLen 0 + 1) (lam.rowLen 1)
          * edgeSum b β (mu.rowLen 1) (lam.rowLen 0 + 1) := by
  have h1 : jtCoeff (fun m => completeHom b m β) (lam.rowLen 0) (mu.rowLen 0)
      = jtCoeff (fun m => completeHom b m β) (lam.rowLen 0 + 1) (mu.rowLen 0 + 1) :=
    (jtCoeff_succ_succ _ _ _).symm
  have h2 : jtCoeff (fun m => completeHom b m β) (lam.rowLen 1 + 1) (mu.rowLen 1 + 1)
      = jtCoeff (fun m => completeHom b m β) (lam.rowLen 1) (mu.rowLen 1) :=
    jtCoeff_succ_succ _ _ _
  rw [jacobiTrudiDet, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Fin.val_zero, Fin.val_one, Nat.add_zero, edgeSum_eq_jtCoeff]
  rw [h1, h2]
  ring

/-- **The transposed term is entirely crossing.**  A path from the higher source
to the lower sink and one from the lower source to the higher sink must share a
lattice point: the first starts to the right and finishes to the left. -/
theorem crosses_of_lt {b s₁ e₁ s₂ e₂ : ℕ} {q r : ℕ → ℕ} (hq : q ∈ hPaths b s₁ e₁)
    (hr : r ∈ hPaths b s₂ e₂) (hs : s₂ < s₁) (he : e₁ < e₂) : Crosses b q r := by
  have hb : q b ≤ r b := by rw [hPaths_top hq le_rfl, hPaths_top hr le_rfl]; omega
  have hex : ∃ k, q k ≤ r k := ⟨b, hb⟩
  have hspec : q (Nat.find hex) ≤ r (Nat.find hex) := Nat.find_spec hex
  have hkb : Nat.find hex ≤ b := Nat.find_le hb
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, hPaths_zero hq, hPaths_zero hr] at hspec
    omega
  have hmin : ¬ q (Nat.find hex - 1) ≤ r (Nat.find hex - 1) :=
    Nat.find_min hex (by omega)
  have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  refine ⟨Nat.find hex - 1, mem_crossSet.mpr ⟨by omega, ?_, ?_⟩⟩
  · rw [hsucc]
    exact le_trans (hPaths_mono hq (by omega : Nat.find hex - 1 ≤ Nat.find hex)) hspec
  · rw [hsucc]
    exact le_trans (by omega : r (Nat.find hex - 1) ≤ q (Nat.find hex - 1))
      (hPaths_mono hq (by omega))

/-- The splice of a crossing pair, at the least height where it crosses. -/
noncomputable def swapPair (b : ℕ) (x : (ℕ → ℕ) × (ℕ → ℕ)) : (ℕ → ℕ) × (ℕ → ℕ) :=
  (spliceAt (crossHeight b x.1 x.2) x.1 x.2, spliceAt (crossHeight b x.1 x.2) x.2 x.1)

theorem swapPair_swapPair {b s₁ e₁ s₂ e₂ : ℕ} {x : (ℕ → ℕ) × (ℕ → ℕ)}
    (h1 : x.1 ∈ hPaths b s₁ e₁) (h2 : x.2 ∈ hPaths b s₂ e₂) (hc : Crosses b x.1 x.2) :
    swapPair b (swapPair b x) = x := by
  have hh := crossHeight_spliceAt h1 h2 hc
  refine Prod.ext ?_ ?_ <;>
    · change spliceAt (crossHeight b _ _) _ _ = _
      rw [swapPair, hh]
      simp only []
      rw [spliceAt_spliceAt]

/-- **Rung 3.**  Splicing at the least crossing height is a weight-preserving
bijection from the crossing pairs of the leading term onto all the pairs of the
transposed term. -/
theorem sum_crossing_eq_sum_transposed {b s₁ e₁ s₂ e₂ : ℕ} (β : ℕ → R)
    (hs : s₂ < s₁) (he : e₂ < e₁) :
    ∑ x ∈ (hPaths b s₁ e₁ ×ˢ hPaths b s₂ e₂).filter fun x => Crosses b x.1 x.2,
        pathWeight b β x.1 * pathWeight b β x.2
      = ∑ x ∈ hPaths b s₁ e₂ ×ˢ hPaths b s₂ e₁,
        pathWeight b β x.1 * pathWeight b β x.2 := by
  refine Finset.sum_nbij' (swapPair b) (swapPair b) (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · rw [Finset.mem_filter, Finset.mem_product] at hx
    obtain ⟨⟨h1, h2⟩, hc⟩ := hx
    obtain ⟨-, hc1, hc2⟩ := mem_crossSet.mp (crossHeight_mem hc)
    exact Finset.mem_product.mpr ⟨spliceAt_mem h1 h2 (crossHeight_lt hc) hc1,
      spliceAt_mem h2 h1 (crossHeight_lt hc) hc2⟩
  · rw [Finset.mem_product] at hx
    obtain ⟨h1, h2⟩ := hx
    have hc : Crosses b x.1 x.2 := crosses_of_lt h1 h2 hs (by omega)
    obtain ⟨-, hc1, hc2⟩ := mem_crossSet.mp (crossHeight_mem hc)
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨spliceAt_mem h1 h2 (crossHeight_lt hc) hc1,
       spliceAt_mem h2 h1 (crossHeight_lt hc) hc2⟩, ?_⟩
    exact ⟨crossHeight b x.1 x.2, crossesAt_spliceAt h1 h2 (crossHeight_lt hc)⟩
  · rw [Finset.mem_filter, Finset.mem_product] at hx
    exact swapPair_swapPair hx.1.1 hx.1.2 hx.2
  · rw [Finset.mem_product] at hx
    exact swapPair_swapPair hx.1 hx.2 (crosses_of_lt hx.1 hx.2 hs (by omega))
  · rw [Finset.mem_filter, Finset.mem_product] at hx
    obtain ⟨⟨h1, h2⟩, hc⟩ := hx
    obtain ⟨-, hc1, hc2⟩ := mem_crossSet.mp (crossHeight_mem hc)
    exact (pathWeight_spliceAt_mul h1 h2 ⟨hc1, hc2⟩ β).symm

/-- **Skew Jacobi--Trudi at two rows, one alphabet, in the path model.**  The
`2 × 2` determinant `det [h_{λ_u - μ_v - u + v}]` over the even alphabet is the
total weight of the pairs of non-crossing paths.

This is the Lindström--Gessel--Viennot statement at `m = 2`.  What it is not yet
is `SkewJacobiTrudi` at `m = 2`: that needs the non-crossing pairs identified
with the tableaux of `λ/μ`, which is stated but not proved below. -/
theorem jacobiTrudiDet_two_eq_sum_nonCrossing {b : ℕ} (β : ℕ → R) (lam mu : YoungDiagram) :
    jacobiTrudiDet (fun m => completeHom b m β) lam mu 2
      = ∑ x ∈ (hPaths b (mu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ
                hPaths b (mu.rowLen 1) (lam.rowLen 1)).filter
                  fun x => ¬ Crosses b x.1 x.2,
          pathWeight b β x.1 * pathWeight b β x.2 := by
  have hprod : ∀ s t : Finset (ℕ → ℕ),
      (∑ q ∈ s, pathWeight b β q) * ∑ r ∈ t, pathWeight b β r
        = ∑ x ∈ s ×ˢ t, pathWeight b β x.1 * pathWeight b β x.2 := fun s t => by
    rw [Finset.sum_mul_sum, Finset.sum_product]
  have hmu : mu.rowLen 1 ≤ mu.rowLen 0 := mu.rowLen_anti 0 1 (by omega)
  have hlam : lam.rowLen 1 ≤ lam.rowLen 0 := lam.rowLen_anti 0 1 (by omega)
  rw [jacobiTrudiDet_two_eq_edgeSum, edgeSum, edgeSum, edgeSum, edgeSum, hprod, hprod,
    ← sum_crossing_eq_sum_transposed (b := b) (s₁ := mu.rowLen 0 + 1)
      (e₁ := lam.rowLen 0 + 1) (s₂ := mu.rowLen 1) (e₂ := lam.rowLen 1) β
      (by omega) (by omega),
    ← Finset.sum_filter_add_sum_filter_not
      (hPaths b (mu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ hPaths b (mu.rowLen 1) (lam.rowLen 1))
      (fun x => Crosses b x.1 x.2)]
  ring

end TwoPaths

/-! ## What remains

Two things stand between `jacobiTrudiDet_two_eq_sum_nonCrossing` and
`JacobiTrudi.SkewJacobiTrudi`, and they are independent of one another.
-/

section Residue

variable {R : Type*} [CommRing R]

/-- **Non-crossing is separation.**  Two paths whose sources are ordered and
which never share a lattice point stay apart by a full step: the left path has
passed height `i+1` before the right one leaves height `i`.

This is the form the tableau bijection consumes — it is exactly the strict
inequality that makes a column of the two-row filling increase. -/
theorem lt_of_not_crosses {b s₁ e₁ s₂ e₂ : ℕ} {q r : ℕ → ℕ} (hq : q ∈ hPaths b s₁ e₁)
    (hr : r ∈ hPaths b s₂ e₂) (hs : s₂ < s₁) (h : ¬ Crosses b q r) :
    ∀ i, i < b → r (i + 1) < q i := by
  have hstep : ∀ i, i < b → r (i + 1) < q i ∨ q (i + 1) < r i := by
    intro i hi
    by_contra hcon
    simp only [not_or, Nat.not_lt] at hcon
    exact h ⟨i, mem_crossSet.mpr ⟨hi, hcon.1, hcon.2⟩⟩
  intro i
  induction i with
  | zero =>
    intro hi
    rcases hstep 0 hi with h1 | h1
    · exact h1
    · have h2 := hPaths_zero hq
      have h3 := hPaths_zero hr
      have h4 := hPaths_mono hq (show 0 ≤ 0 + 1 by omega)
      omega
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    rcases hstep (i + 1) hi with h1 | h1
    · exact h1
    · have h4 := hPaths_mono hq (show i ≤ i + 1 + 1 by omega)
      omega

/-- At no odd variables the alphabet of is the even factor
alone: only `q = 0` survives in `superHom`, and `e_0 = 1`. -/
theorem superHom_zero_odd (b m : ℕ) (β α : ℕ → R) : superHom b 0 m β α = completeHom b m β := by
  rw [superHom, Finset.sum_eq_single_of_mem m (Finset.self_mem_range_succ m)]
  · rw [Nat.sub_self, elemHom_zero, mul_one]
  · intro p hp hne
    rw [elemHom_eq_zero_of_lt (by have := Finset.mem_range.mp hp; omega) α, mul_zero]

/-- **Residue one: the tableau bijection.**  The non-crossing pairs of paths for
a pair of two-row shapes carry the total weight of the semistandard tableaux of
`λ / μ`.

`lt_of_not_crosses` supplies the separation and `pathLetter` the letters, so what
is missing is the two round trips and the matching of the weight — the `m = 2`
case of `Shields.pathOfWord` / `Shields.wordOfPath` run on a skew shape
rather than a single row.

Checked over 100 shape pairs and 307 non-crossing families by
`scripts/verify_appB_lgv_paths.py`, check (6). -/
def NonCrossingIsSkewSchur (b : ℕ) (β : ℕ → R) : Prop :=
  ∀ lam mu : YoungDiagram, mu ≤ lam → (∀ i, 2 ≤ i → lam.rowLen i = 0) →
    ∑ x ∈ (hPaths b (mu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ
            hPaths b (mu.rowLen 1) (lam.rowLen 1)).filter fun x => ¬ Crosses b x.1 x.2,
        pathWeight b β x.1 * pathWeight b β x.2
      = skewSchur lam mu b β

/-- **`SkewJacobiTrudi` at two rows and no odd variables**, given the tableau
bijection.  Every other ingredient — the Leibniz expansion, the crossing swap,
the sign reversal, the alphabet — is proved above; this is what they buy. -/
theorem skewJacobiTrudi_two_of_nonCrossing {b : ℕ} {β α : ℕ → R}
    (h : NonCrossingIsSkewSchur b β) (lam mu : YoungDiagram) (hmu : mu ≤ lam)
    (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) :
    jacobiTrudiDet (fun m => superHom b 0 m β α) lam mu 2
      = superSkewSchur lam mu b 0 β α := by
  have hd : (fun m => superHom b 0 m β α) = fun m => completeHom b m β :=
    funext fun m => superHom_zero_odd b m β α
  rw [hd, jacobiTrudiDet_two_eq_sum_nonCrossing, h lam mu hmu hrow,
    superSkewSchur_zero_odd β α hmu]

end Residue

end Shields
