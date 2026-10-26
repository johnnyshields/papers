/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/AlternatingNear.lean
import SkewRibbonCoarsenings.DepthCancel

/-!
# Alternating near-concatenations and the all-odd invariant

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:depth`
(`eq:OA`, and the notation of `thm:lift`).

`altCuts w R S j` is the cut set of `Alt_j(R,S) = R ⊙ S ⊙ R ⊙ ⋯ ⊙ S ⊙ R` (`2j+1` factors) for two
compositions of common weight `w`; `wordCuts` is the cut set of a near-concatenation of `m`
alternating cells starting at an arbitrary phase `p`, to which `altCuts` is identified.  The ordinary
truncation `F^{[<s]}` is `truncLT` (ordinary degree is the number of `h`-factors, every `h_j` having
degree one), and `OA` is the invariant `eq:OA`.  `ordGE k f` (from `DepthCancel`) says that `f` has no
monomial of ordinary degree `< k`; it carries the degree bookkeeping.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open MvPolynomial Finset

/-- The near-concatenation of `m` cells of weight `w` whose `k`-th cell (counted from `0`) is `R`
when `k + p` is even and `S` otherwise.  No cut is placed at a cell boundary. -/
def wordCuts (w : ℕ) (R S : Finset ℕ) (p m : ℕ) : Finset ℕ :=
  (range m).biUnion fun k => (if Even (k + p) then R else S).image (k * w + ·)

lemma mem_wordCuts {w : ℕ} {R S : Finset ℕ} {p m x : ℕ} :
    x ∈ wordCuts w R S p m ↔
      ∃ k < m, ∃ y ∈ (if Even (k + p) then R else S), k * w + y = x := by
  simp [wordCuts]

lemma wordCuts_congr {w : ℕ} {R S : Finset ℕ} {p p' : ℕ} (h : p % 2 = p' % 2) (m : ℕ) :
    wordCuts w R S p m = wordCuts w R S p' m := by
  have : ∀ k, Even (k + p) ↔ Even (k + p') := fun k => by
    simp only [Nat.even_iff]; omega
  unfold wordCuts
  refine Finset.biUnion_congr rfl fun k _ => ?_
  simp only [this k]

lemma wordCuts_swap (w : ℕ) (R S : Finset ℕ) (p m : ℕ) :
    wordCuts w R S (p + 1) m = wordCuts w S R p m := by
  unfold wordCuts
  refine Finset.biUnion_congr rfl fun k _ => ?_
  have : Even (k + (p + 1)) ↔ ¬ Even (k + p) := by
    simp only [Nat.even_iff]; omega
  by_cases h : Even (k + p) <;> simp [h, this]

/-- A near-concatenation splits into two near-concatenations at any cell boundary. -/
lemma wordCuts_add (w : ℕ) (R S : Finset ℕ) (p m k : ℕ) :
    wordCuts w R S p (m + k) =
      nearCuts (m * w) (wordCuts w R S p m) ((wordCuts w R S (p + m) k)) := by
  ext x
  simp only [nearCuts, mem_union, mem_wordCuts, mem_image]
  constructor
  · rintro ⟨i, hi, y, hy, rfl⟩
    by_cases him : i < m
    · exact Or.inl ⟨i, him, y, hy, rfl⟩
    · refine Or.inr ⟨(i - m) * w + y, ⟨i - m, by omega, y, ?_, rfl⟩, ?_⟩
      · have : i - m + (p + m) = i + p := by omega
        rwa [this]
      · have : i = (i - m) + m := by omega
        conv_rhs => rw [this]
        ring
  · rintro (⟨i, hi, y, hy, rfl⟩ | ⟨z, ⟨i, hi, y, hy, rfl⟩, rfl⟩)
    · exact ⟨i, by omega, y, hy, rfl⟩
    · refine ⟨m + i, by omega, y, ?_, ?_⟩
      · have : m + i + p = i + (p + m) := by omega
        rwa [this]
      · ring

/-- `eq:OA` (notation): the cut set of `Alt_j(R,S) = R ⊙ S ⊙ R ⊙ ⋯ ⊙ S ⊙ R` (`2j+1` factors),
built by appending the pair `S ⊙ R` with the near-concatenation `⊙`; identified with the word of
`2j+1` alternating cells in `altCuts_eq_wordCuts`. -/
def altCuts (w : ℕ) (R S : Finset ℕ) : ℕ → Finset ℕ
  | 0 => R
  | j + 1 => nearCuts ((2 * j + 1) * w) (altCuts w R S j) (nearCuts w S R)

lemma wordCuts_one (w : ℕ) (R S : Finset ℕ) (p : ℕ) :
    wordCuts w R S p 1 = if Even p then R else S := by
  ext x
  simp only [mem_wordCuts]
  constructor
  · rintro ⟨k, hk, y, hy, rfl⟩
    obtain rfl : k = 0 := by omega
    simpa using hy
  · intro hx
    exact ⟨0, by omega, x, by simpa using hx, by simp⟩

lemma altCuts_eq_wordCuts (w : ℕ) (R S : Finset ℕ) (j : ℕ) :
    altCuts w R S j = wordCuts w R S 0 (2 * j + 1) := by
  induction j with
  | zero => simp [altCuts, wordCuts_one]
  | succ j ih =>
    have e : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by ring
    have h2 : wordCuts w R S (0 + (2 * j + 1)) 2 = nearCuts w S R := by
      rw [wordCuts_congr (p' := 1) (by omega), show (2 : ℕ) = 1 + 1 from rfl, wordCuts_add,
        wordCuts_one, wordCuts_one]
      simp
    rw [altCuts, ih, e, wordCuts_add w R S 0 (2 * j + 1) 2, h2]

/-! ### Cut-set validity -/

lemma isCutSet_wordCuts {w : ℕ} {R S : Finset ℕ} (hR : IsCutSet w R) (hS : IsCutSet w S)
    (p m : ℕ) : IsCutSet (m * w) (wordCuts w R S p m) := by
  intro x hx
  obtain ⟨k, hk, y, hy, rfl⟩ := mem_wordCuts.mp hx
  have hy' : 0 < y ∧ y < w := by
    split_ifs at hy
    · exact Finset.mem_Ioo.mp (hR hy)
    · exact Finset.mem_Ioo.mp (hS hy)
  have : (k + 1) * w ≤ m * w := Nat.mul_le_mul_right _ hk
  exact Finset.mem_Ioo.mpr ⟨by omega, by nlinarith⟩

lemma isCutSet_nearCuts {n n' : ℕ} {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n' S') :
    IsCutSet (n + n') (nearCuts n S S') := by
  intro x hx
  simp only [nearCuts, Finset.mem_union, Finset.mem_image] at hx
  rcases hx with hx | ⟨y, hy, rfl⟩
  · have := Finset.mem_Ioo.mp (hS hx)
    exact Finset.mem_Ioo.mpr ⟨this.1, by omega⟩
  · have := Finset.mem_Ioo.mp (hS' hy)
    exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩

lemma isCutSet_concatCuts {n n' : ℕ} {S S' : Finset ℕ} (hn : 0 < n) (hn' : 0 < n')
    (hS : IsCutSet n S) (hS' : IsCutSet n' S') :
    IsCutSet (n + n') (concatCuts n S S') := by
  intro x hx
  simp only [concatCuts, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hx
  rcases hx with (hx | rfl) | ⟨y, hy, rfl⟩
  · have := Finset.mem_Ioo.mp (hS hx)
    exact Finset.mem_Ioo.mpr ⟨this.1, by omega⟩
  · exact Finset.mem_Ioo.mpr ⟨hn, by omega⟩
  · have := Finset.mem_Ioo.mp (hS' hy)
    exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩

lemma isCutSet_altCuts {w : ℕ} {R S : Finset ℕ} (hR : IsCutSet w R) (hS : IsCutSet w S) (j : ℕ) :
    IsCutSet ((2 * j + 1) * w) (altCuts w R S j) := by
  rw [altCuts_eq_wordCuts]
  exact isCutSet_wordCuts hR hS 0 _

/-! ### Ordinary degree -/

/-- The ordinary truncation `F^{[<s]}`: the sum of the homogeneous components of ordinary
degree `< s` (the ordinary degree of a monomial in the `h_j` is its number of `h`-factors, each
`h_j` counting one). -/
noncomputable def truncLT (s : ℕ) (f : Lam) : Lam :=
  ∑ i ∈ Finset.range s, MvPolynomial.homogeneousComponent i f

lemma coeff_truncLT (s : ℕ) (f : Lam) (m : ℕ+ →₀ ℕ) :
    (truncLT s f).coeff m = if Finsupp.degree m < s then f.coeff m else 0 := by
  unfold truncLT
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_homogeneousComponent]
  rw [Finset.sum_ite_eq (Finset.range s) (Finsupp.degree m) (fun _ => f.coeff m)]
  simp

/-- `F^{[<s]} = 0` exactly when `F` has no monomial of ordinary degree `< s`. -/
lemma truncLT_eq_zero_iff {s : ℕ} {f : Lam} : truncLT s f = 0 ↔ ordGE s f := by
  constructor
  · intro h m hm
    have := congrArg (fun p : Lam => p.coeff m) h
    simp only [coeff_truncLT, if_pos hm] at this
    simpa using this
  · intro h
    ext m
    rw [coeff_truncLT]
    split_ifs with hm
    · exact h m hm
    · simp

/-- `eq:OA`: the all-odd invariant.  For compositions `R, S` of common weight `w`, for every
`j ≥ 0` the polynomials `G_{Alt_j(R,S)}` and `G_{Alt_j(S,R)}` agree below ordinary degree `s`. -/
def OA (w : ℕ) (R S : Finset ℕ) (s : ℕ) : Prop :=
  ∀ j : ℕ, truncLT s (G ((2 * j + 1) * w) (altCuts w R S j) -
    G ((2 * j + 1) * w) (altCuts w S R j)) = 0

lemma OA_iff {w : ℕ} {R S : Finset ℕ} {s : ℕ} :
    OA w R S s ↔ ∀ j : ℕ, ordGE s (G ((2 * j + 1) * w) (altCuts w R S j) -
      G ((2 * j + 1) * w) (altCuts w S R j)) := by
  unfold OA
  exact forall_congr' fun j => truncLT_eq_zero_iff

/-! ### Words with retained cell boundaries -/

/-- The near-concatenation of `N` cells (phase `p`) together with cuts at the cell boundaries
`A` (cell indices, scaled by the cell weight `w`). -/
def wordBd (w : ℕ) (R S : Finset ℕ) (p N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  wordCuts w R S p N ∪ A.image (· * w)

lemma wordBd_empty (w : ℕ) (R S : Finset ℕ) (p N : ℕ) : wordBd w R S p N ∅ = wordCuts w R S p N := by
  simp [wordBd]

lemma wordBd_congr (w : ℕ) (R S : Finset ℕ) {p p' : ℕ} (h : p % 2 = p' % 2) (N : ℕ)
    (A : Finset ℕ) : wordBd w R S p N A = wordBd w R S p' N A := by
  unfold wordBd; rw [wordCuts_congr h]

lemma wordBd_near (w : ℕ) (R S : Finset ℕ) (p a c : ℕ) (Bl Br : Finset ℕ) :
    nearCuts (a * w) (wordBd w R S p a Bl) (wordBd w R S (p + a) c Br) =
      wordBd w R S p (a + c) (Bl ∪ Br.image (a + ·)) := by
  ext x
  simp only [nearCuts, wordBd, wordCuts_add, Finset.mem_union, Finset.mem_image]
  constructor
  · intro h
    grind
  · intro h
    grind

lemma isCutSet_wordBd {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R)
    (hS : IsCutSet w S) (p N : ℕ) {A : Finset ℕ} (hA : ∀ x ∈ A, 0 < x ∧ x < N) :
    IsCutSet (N * w) (wordBd w R S p N A) := by
  intro x hx
  simp only [wordBd, Finset.mem_union, Finset.mem_image] at hx
  rcases hx with hx | ⟨y, hy, rfl⟩
  · exact isCutSet_wordCuts hR hS p N hx
  · obtain ⟨h1, h2⟩ := hA y hy
    exact Finset.mem_Ioo.mpr ⟨Nat.mul_pos h1 hw, Nat.mul_lt_mul_of_pos_right h2 hw⟩

lemma wordBd_insert (w : ℕ) (R S : Finset ℕ) (p N a : ℕ) (A : Finset ℕ) :
    wordBd w R S p N (insert a A) = insert (a * w) (wordBd w R S p N A) := by
  unfold wordBd
  rw [Finset.image_insert, Finset.union_insert]

lemma wordBd_near' (w : ℕ) (R S : Finset ℕ) {p q : ℕ} (a c : ℕ) (h : q % 2 = (p + a) % 2)
    (Bl Br : Finset ℕ) :
    nearCuts (a * w) (wordBd w R S p a Bl) (wordBd w R S q c Br) =
      wordBd w R S p (a + c) (Bl ∪ Br.image (a + ·)) := by
  rw [wordBd_congr w R S h]; exact wordBd_near w R S p a c Bl Br

lemma concatCuts_eq_insert_near (n : ℕ) (S S' : Finset ℕ) :
    concatCuts n S S' = insert n (nearCuts n S S') := by
  unfold concatCuts nearCuts
  rw [Finset.union_right_comm, Finset.union_comm _ {n}]
  rfl

/-! ### The lifted roots of `eq:sharpness-lift` -/

/-- `eq:sharpness-lift`: `E = R ⊙ S`. -/
def liftE (w : ℕ) (R S : Finset ℕ) : Finset ℕ := nearCuts w R S

/-- `eq:sharpness-lift`: `F = R · S`. -/
def liftF (w : ℕ) (R S : Finset ℕ) : Finset ℕ := concatCuts w R S

/-- `eq:sharpness-lift`: `R' = E · (F ⊙ E)`, of weight `6w`. -/
def liftR (w : ℕ) (R S : Finset ℕ) : Finset ℕ :=
  concatCuts (2 * w) (liftE w R S) (nearCuts (2 * w) (liftF w R S) (liftE w R S))

/-- `eq:sharpness-lift`: `S' = (E ⊙ F) · E`, of weight `6w`. -/
def liftS (w : ℕ) (R S : Finset ℕ) : Finset ℕ :=
  concatCuts (4 * w) (nearCuts (2 * w) (liftE w R S) (liftF w R S)) (liftE w R S)

lemma liftE_eq (w : ℕ) (R S : Finset ℕ) : liftE w R S = wordBd w R S 0 2 ∅ := by
  rw [wordBd_empty, show (2 : ℕ) = 1 + 1 from rfl, wordCuts_add, wordCuts_one, wordCuts_one]
  simp [liftE]

lemma liftF_eq (w : ℕ) (R S : Finset ℕ) : liftF w R S = wordBd w R S 0 2 {1} := by
  have h : wordBd w R S 0 2 {1} = insert (1 * w) (wordBd w R S 0 2 ∅) :=
    wordBd_insert w R S 0 2 1 ∅
  rw [show ({1} : Finset ℕ) = {1} from rfl] at h
  unfold liftF
  rw [concatCuts_eq_insert_near, ← liftE, liftE_eq, one_mul] at *
  exact h.symm

/-- The lifted root `R'` is the six-cell word `R S R S R S` with cell boundaries `2, 3` available. -/
lemma liftR_eq (w : ℕ) (R S : Finset ℕ) : liftR w R S = wordBd w R S 0 6 {2, 3} := by
  have hF : nearCuts (2 * w) (liftF w R S) (liftE w R S) = wordBd w R S 0 4 {1} := by
    rw [liftF_eq, liftE_eq, show (2 : ℕ) * w = 2 * w from rfl,
      wordBd_near' w R S 2 2 (by omega)]
    simp
  have h2 : nearCuts (2 * w) (liftE w R S) (wordBd w R S 0 4 {1}) = wordBd w R S 0 6 {3} := by
    rw [liftE_eq, wordBd_near' w R S 2 4 (by omega)]
    simp
  have h3 : wordBd w R S 0 6 {2, 3} = insert (2 * w) (wordBd w R S 0 6 {3}) := by
    rw [show ({2, 3} : Finset ℕ) = insert 2 {3} from rfl, wordBd_insert]
  unfold liftR
  rw [hF, concatCuts_eq_insert_near, h2, h3]

/-- The lifted root `S'` is the six-cell word `R S R S R S` with cell boundaries `3, 4`
available. -/
lemma liftS_eq (w : ℕ) (R S : Finset ℕ) : liftS w R S = wordBd w R S 0 6 {3, 4} := by
  have h1 : nearCuts (2 * w) (liftE w R S) (liftF w R S) = wordBd w R S 0 4 {3} := by
    rw [liftF_eq, liftE_eq, wordBd_near' w R S 2 2 (by omega)]
    simp
  have h2 : nearCuts (4 * w) (wordBd w R S 0 4 {3}) (liftE w R S) = wordBd w R S 0 6 {3} := by
    rw [liftE_eq, wordBd_near' w R S 4 2 (by omega)]
    simp
  have h3 : wordBd w R S 0 6 {3, 4} = insert (4 * w) (wordBd w R S 0 6 {3}) := by
    rw [show ({3, 4} : Finset ℕ) = insert 4 {3} by ext; simp; omega, wordBd_insert]
  unfold liftS
  rw [h1, concatCuts_eq_insert_near, h2, h3]

end SkewRibbonCoarsenings
