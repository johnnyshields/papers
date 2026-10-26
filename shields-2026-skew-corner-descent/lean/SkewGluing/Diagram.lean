/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval
import Mathlib.Logic.Relation
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import SkewGluing.Tactics

/-!
# Diagrams and diagonal geometry

Formalizes diagram coordinates used in `shields-2026-skew-corner-descent.tex`, «Corner
cofactors and common cores» (`sec:corner`). A diagram is a finite set of cells `(i, j) : ℤ × ℤ`
(row `i`, column `j`) with content `j - i`. This supporting layer defines skew diagrams,
edge-connectedness, diagonal profiles, and affine operations used by the marked-composition
definitions.

TODO-COPIED: copied from skew-factor-gluing.

Sorry-free.
-/

namespace SkewGluing

/-- A diagram: a finite set of cells `(row, column)`. -/
abbrev Diagram := Finset (ℤ × ℤ)

/-- The content `c(i, j) = j - i` of a cell. -/
def content (x : ℤ × ℤ) : ℤ := x.2 - x.1

/-- The cell `(i, i + k)` has content `k`. -/
theorem content_mk_add (i k : ℤ) : content (i, i + k) = k := by
  simp [content]

/-- The diagonal step `e = (1, 1)`. -/
def eCell : ℤ × ℤ := (1, 1)

/-- Two cells share an edge. -/
def CellAdj (x y : ℤ × ℤ) : Prop := |x.1 - y.1| + |x.2 - y.2| = 1

instance : DecidableRel CellAdj := fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- A diagram is *skew* if it is convex for the northwest-to-southeast order: whenever
`(i₁, j₁)` and `(i₂, j₂)` lie in it with `i₁ ≤ i₂` and `j₁ ≤ j₂`, so does every cell
between them. -/
def IsSkew (D : Diagram) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, x.1 ≤ y.1 → x.2 ≤ y.2 →
    ∀ i ∈ Finset.Icc x.1 y.1, ∀ j ∈ Finset.Icc x.2 y.2, (i, j) ∈ D

instance (D : Diagram) : Decidable (IsSkew D) := by unfold IsSkew; infer_instance

/-- A diagram is *edge-connected* if it is nonempty and any two of its cells are joined by a
chain of cells of the diagram, consecutive ones sharing an edge. -/
def IsEdgeConnected (D : Diagram) : Prop :=
  D.Nonempty ∧ ∀ x ∈ D, ∀ y ∈ D,
    Relation.ReflTransGen (fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b) x y

/-- A connected skew diagram: skew and edge-connected. -/
def IsConnectedSkew (D : Diagram) : Prop := IsSkew D ∧ IsEdgeConnected D

/-! ## Affine operations -/

/-- Translation of a diagram by `v`. -/
def translate (v : ℤ × ℤ) (D : Diagram) : Diagram := D.image (· + v)

/-- Rotation through `180` degrees, `D*`, as the negation `x ↦ -x` (a specific
representative of the translation class). -/
def rotate (D : Diagram) : Diagram := D.image (fun x => -x)

/-- Transpose. -/
def transpose (D : Diagram) : Diagram := D.image Prod.swap

/-- Antitransposition `AT(i, j) = (-j, -i)`. -/
def antitranspose (D : Diagram) : Diagram := D.image (fun x => (-x.2, -x.1))

/-! ## The diagonal profile -/

/-- The set of contents occupied by a diagram. -/
def contents (D : Diagram) : Finset ℤ := D.image content

/-- The span `N_D`: the number of occupied contents. -/
def span (D : Diagram) : ℕ := (contents D).card

/-- The rows of the cells of content `k`. -/
def diagRows (D : Diagram) (k : ℤ) : Finset ℤ :=
  (D.filter fun x => content x = k).image Prod.fst

/-- The first (northernmost) row `ℓ_k` of the content-`k` diagonal (`0` if it is empty). -/
def diagLo (D : Diagram) (k : ℤ) : ℤ :=
  if h : (diagRows D k).Nonempty then (diagRows D k).min' h else 0

/-- The last (southernmost) row `h_k` of the content-`k` diagonal (`0` if it is empty). -/
def diagHi (D : Diagram) (k : ℤ) : ℤ :=
  if h : (diagRows D k).Nonempty then (diagRows D k).max' h else 0

/-- The smallest content (`0` for the empty diagram). -/
def minContent (D : Diagram) : ℤ :=
  if h : (contents D).Nonempty then (contents D).min' h else 0

/-- The largest content (`0` for the empty diagram). -/
def maxContent (D : Diagram) : ℤ :=
  if h : (contents D).Nonempty then (contents D).max' h else 0

/-- The southwest cell: the cell on the smallest content (northernmost such cell). -/
def sw (D : Diagram) : ℤ × ℤ :=
  (diagLo D (minContent D), diagLo D (minContent D) + minContent D)

/-- The northeast cell: the cell on the largest content (northernmost such cell). -/
def ne (D : Diagram) : ℤ × ℤ :=
  (diagLo D (maxContent D), diagLo D (maxContent D) + maxContent D)

/-- The bit `A_k = ℓ_{k-1} - ℓ_k`, indexed by the content `k`. -/
def bitA (D : Diagram) (k : ℤ) : ℤ := diagLo D (k - 1) - diagLo D k

/-- The bit `B_k = h_{k-1} - h_k`, indexed by the content `k`. -/
def bitB (D : Diagram) (k : ℤ) : ℤ := diagHi D (k - 1) - diagHi D k

/-- The height `H_k = h_k - ℓ_k + 1` of the content-`k` diagonal. -/
def height (D : Diagram) (k : ℤ) : ℤ := diagHi D k - diagLo D k + 1

/-- The southwest normalization: translate so that the southwest cell is `(0, 0)`. -/
def normalize (D : Diagram) : Diagram := translate (-(sw D)) D

/-- Skew diagram `λ / μ` from row lengths: row `i` occupies columns `[μ_i, λ_i)`. -/
def skewOf (lam mu : List ℕ) : Diagram :=
  (Finset.range lam.length).biUnion fun i =>
    (Finset.Ico ((mu.getD i 0 : ℕ) : ℤ) ((lam.getD i 0 : ℕ) : ℤ)).image fun j => ((i : ℤ), j)

/-! ## Basic API for the diagonal profile -/

theorem cellAdj_iff {x y : ℤ × ℤ} :
    CellAdj x y ↔ (x.1 = y.1 ∧ (x.2 = y.2 + 1 ∨ y.2 = x.2 + 1)) ∨
      (x.2 = y.2 ∧ (x.1 = y.1 + 1 ∨ y.1 = x.1 + 1)) := by
  unfold CellAdj
  rcases abs_cases (x.1 - y.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (x.2 - y.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega

theorem CellAdj.symm' {x y : ℤ × ℤ} (h : CellAdj x y) : CellAdj y x := by
  rw [cellAdj_iff] at h ⊢
  omega

theorem IsSkew.mem {D : Diagram} (hs : IsSkew D) {a b c d i j : ℤ} (h₁ : (a, b) ∈ D)
    (h₂ : (c, d) ∈ D) (hac : a ≤ c) (hbd : b ≤ d) (hai : a ≤ i) (hic : i ≤ c) (hbj : b ≤ j)
    (hjd : j ≤ d) : (i, j) ∈ D :=
  hs _ h₁ _ h₂ hac hbd i (Finset.mem_Icc.mpr ⟨hai, hic⟩) j (Finset.mem_Icc.mpr ⟨hbj, hjd⟩)

theorem mem_diagRows {D : Diagram} {k i : ℤ} : i ∈ diagRows D k ↔ (i, i + k) ∈ D := by
  unfold diagRows
  simp only [Finset.mem_image, content, Prod.exists]
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    have h1 := (Finset.mem_filter.mp hab)
    have : b = a + k := by have := h1.2; simp only at this; omega
    simpa [this] using h1.1
  · intro h
    exact ⟨i, i + k, Finset.mem_filter.mpr ⟨h, by simp⟩, rfl⟩

theorem mem_contents {D : Diagram} {k : ℤ} : k ∈ contents D ↔ (diagRows D k).Nonempty := by
  unfold contents
  simp only [Finset.mem_image, Finset.Nonempty, mem_diagRows, Prod.exists]
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨a, by simpa [content] using hab⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, i + k, hi, by simp [content]⟩

theorem mem_contents_iff {D : Diagram} {k : ℤ} : k ∈ contents D ↔ ∃ i, (i, i + k) ∈ D := by
  rw [mem_contents]
  simp [Finset.Nonempty, mem_diagRows]

theorem content_mem_contents {D : Diagram} {x : ℤ × ℤ} (hx : x ∈ D) :
    content x ∈ contents D :=
  Finset.mem_image_of_mem _ hx

theorem diagLo_eq {D : Diagram} {k : ℤ} (h : (diagRows D k).Nonempty) :
    diagLo D k = (diagRows D k).min' h := by
  simp [diagLo, h]

theorem diagHi_eq {D : Diagram} {k : ℤ} (h : (diagRows D k).Nonempty) :
    diagHi D k = (diagRows D k).max' h := by
  simp [diagHi, h]

theorem diagLo_le {D : Diagram} {k i j : ℤ} (h : (i, j) ∈ D) (hk : j - i = k) :
    diagLo D k ≤ i := by
  have hij : j = i + k := by omega
  subst hij
  have hne : (diagRows D k).Nonempty := ⟨i, mem_diagRows.mpr h⟩
  rw [diagLo_eq hne]
  exact Finset.min'_le _ _ (mem_diagRows.mpr h)

theorem le_diagHi {D : Diagram} {k i j : ℤ} (h : (i, j) ∈ D) (hk : j - i = k) :
    i ≤ diagHi D k := by
  have hij : j = i + k := by omega
  subst hij
  have hne : (diagRows D k).Nonempty := ⟨i, mem_diagRows.mpr h⟩
  rw [diagHi_eq hne]
  exact Finset.le_max' _ _ (mem_diagRows.mpr h)

theorem diagLo_mem {D : Diagram} {k : ℤ} (hk : k ∈ contents D) :
    (diagLo D k, diagLo D k + k) ∈ D := by
  have hne := mem_contents.mp hk
  rw [diagLo_eq hne]
  exact mem_diagRows.mp (Finset.min'_mem _ hne)

theorem diagHi_mem {D : Diagram} {k : ℤ} (hk : k ∈ contents D) :
    (diagHi D k, diagHi D k + k) ∈ D := by
  have hne := mem_contents.mp hk
  rw [diagHi_eq hne]
  exact mem_diagRows.mp (Finset.max'_mem _ hne)

theorem diagLo_le_diagHi {D : Diagram} {k : ℤ} (hk : k ∈ contents D) :
    diagLo D k ≤ diagHi D k :=
  le_diagHi (diagLo_mem hk) (by ring)

/-! ## The diagonal criterion -/

/-- The diagonal-shape conditions used by this supporting diagram API. -/
def HasDiagonalShape (D : Diagram) : Prop :=
  D.Nonempty ∧
  (∀ x ∈ D, ∀ y ∈ D, ∀ k ∈ Finset.Icc (content x) (content y), k ∈ contents D) ∧
  (∀ x ∈ D, ∀ y ∈ D, content x = content y →
    ∀ i ∈ Finset.Icc x.1 y.1, (i, i + content x) ∈ D) ∧
  (∀ k ∈ contents D, k - 1 ∈ contents D →
    bitA D k ∈ ({0, 1} : Finset ℤ) ∧ bitB D k ∈ ({0, 1} : Finset ℤ)) ∧
  (∀ k ∈ contents D, (k - 1 ∉ contents D ∨ k + 1 ∉ contents D) → diagLo D k = diagHi D k)

instance (D : Diagram) : Decidable (HasDiagonalShape D) := by
  unfold HasDiagonalShape; infer_instance

theorem content_adj {x y : ℤ × ℤ} (h : CellAdj x y) :
    content y = content x + 1 ∨ content x = content y + 1 := by
  rw [cellAdj_iff] at h
  unfold content
  omega

/-- The contents of an edge-connected diagram form an interval. -/
theorem contents_interval_of_edgeConnected {D : Diagram} (hD : IsEdgeConnected D) :
    ∀ x ∈ D, ∀ y ∈ D, ∀ k ∈ Finset.Icc (content x) (content y), k ∈ contents D := by
  intro x hx y hy
  have key : ∀ z, Relation.ReflTransGen (fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b) x z →
      ∀ k, (content x ≤ k ∧ k ≤ content z) ∨ (content z ≤ k ∧ k ≤ content x) →
        k ∈ contents D := by
    intro z hz
    induction hz with
    | refl =>
      intro k hk
      have : k = content x := by omega
      subst this
      exact content_mem_contents hx
    | @tail b c _ hstep ih =>
      intro k hk
      have hc : c ∈ D := hstep.2.1
      have := content_adj hstep.2.2
      by_cases hkc : k = content c
      · subst hkc; exact content_mem_contents hc
      · exact ih k (by omega)
  intro k hk
  rw [Finset.mem_Icc] at hk
  exact key y (hD.2 x hx y hy) k (Or.inl hk)

/-- The `⟹` direction of the diagonal criterion. -/
theorem hasDiagonalShape_of_isConnectedSkew {D : Diagram} (h : IsConnectedSkew D) :
    HasDiagonalShape D := by
  obtain ⟨hs, hc⟩ := h
  refine ⟨hc.1, contents_interval_of_edgeConnected hc, ?_, ?_, ?_⟩
  · intro x hx y hy hxy i hi
    rw [Finset.mem_Icc] at hi
    have hxy' : x.2 - x.1 = y.2 - y.1 := hxy
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    simp only [content] at hxy' hi ⊢
    exact hs.mem hx hy (by omega) (by omega) hi.1 hi.2 (by omega) (by omega)
  · intro k hk hk1
    have hl := diagLo_mem hk
    have hl1 := diagLo_mem hk1
    have hh := diagHi_mem hk
    have hh1 := diagHi_mem hk1
    have e1 : ∀ i, (i, i + k) ∈ D → diagLo D k ≤ i := fun i hi => diagLo_le hi (by ring)
    have e2 : ∀ i, (i, i + (k - 1)) ∈ D → diagLo D (k - 1) ≤ i :=
      fun i hi => diagLo_le hi (by ring)
    have e3 : ∀ i, (i, i + k) ∈ D → i ≤ diagHi D k := fun i hi => le_diagHi hi (by ring)
    have e4 : ∀ i, (i, i + (k - 1)) ∈ D → i ≤ diagHi D (k - 1) :=
      fun i hi => le_diagHi hi (by ring)
    simp only [bitA, bitB, Finset.mem_insert, Finset.mem_singleton]
    have a1 : diagLo D k ≤ diagLo D (k - 1) := by
      by_contra hlt
      have := hs.mem hl1 hl (a := diagLo D (k - 1)) (c := diagLo D k) (i := diagLo D (k - 1))
        (j := diagLo D (k - 1) + k) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
      have := e1 _ this
      omega
    have a2 : diagLo D (k - 1) ≤ diagLo D k + 1 := by
      have : diagLo D (k - 1) ≤ diagLo D k + 1 ∨ diagLo D k + 1 < diagLo D (k - 1) := by omega
      rcases this with h | hlt
      · exact h
      · have h5 := hs.mem hl hl1 (i := diagLo D k + 1) (j := diagLo D k + k) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
        have := e2 (diagLo D k + 1) (by convert h5 using 2; ring)
        omega
    have b1 : diagHi D k ≤ diagHi D (k - 1) := by
      by_contra hlt
      have h5 := hs.mem hh1 hh (i := diagHi D k) (j := diagHi D k + k - 1) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      have := e4 (diagHi D k) (by convert h5 using 2; ring)
      omega
    have b2 : diagHi D (k - 1) ≤ diagHi D k + 1 := by
      by_contra hlt
      have h5 := hs.mem hh hh1 (i := diagHi D k + 1) (j := diagHi D k + 1 + k) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      have := e3 (diagHi D k + 1) h5
      omega
    omega
  · intro k hk hend
    have hl := diagLo_mem hk
    have hh := diagHi_mem hk
    have hlh := diagLo_le_diagHi hk
    by_contra hne
    have hlt : diagLo D k < diagHi D k := lt_of_le_of_ne hlh hne
    rcases hend with h1 | h1
    · apply h1
      have h5 := hs.mem hl hh (i := diagHi D k) (j := diagHi D k + k - 1) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      exact mem_contents_iff.mpr ⟨diagHi D k, by convert h5 using 2; ring⟩
    · apply h1
      have h5 := hs.mem hl hh (i := diagLo D k) (j := diagLo D k + k + 1) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      exact mem_contents_iff.mpr ⟨diagLo D k, by convert h5 using 2; ring⟩

section Converse

variable {D : Diagram}

theorem HasDiagonalShape.between (h : HasDiagonalShape D) {a b k : ℤ} (ha : a ∈ contents D)
    (hb : b ∈ contents D) (hak : a ≤ k) (hkb : k ≤ b) : k ∈ contents D := by
  have := h.2.1 _ (diagLo_mem ha) _ (diagLo_mem hb) k
  simp only [content, Finset.mem_Icc] at this
  exact this ⟨by omega, by omega⟩

theorem HasDiagonalShape.mem_iff (h : HasDiagonalShape D) {k i : ℤ} :
    (i, i + k) ∈ D ↔ k ∈ contents D ∧ diagLo D k ≤ i ∧ i ≤ diagHi D k := by
  constructor
  · intro hi
    exact ⟨mem_contents_iff.mpr ⟨i, hi⟩, diagLo_le hi (by ring), le_diagHi hi (by ring)⟩
  · rintro ⟨hk, h1, h2⟩
    have := h.2.2.1 _ (diagLo_mem hk) _ (diagHi_mem hk) (by simp [content]) i
      (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    simpa [content] using this

theorem HasDiagonalShape.diagLo_anti (h : HasDiagonalShape D) {a b : ℤ} (ha : a ∈ contents D)
    (hb : b ∈ contents D) (hab : a ≤ b) :
    diagLo D b ≤ diagLo D a ∧ diagLo D a ≤ diagLo D b + (b - a) := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ n hn ih =>
    have hn' : n ∈ contents D := h.between ha hb hn (by omega)
    have := (h.2.2.2.1 (n + 1) hb (by simpa using hn')).1
    simp only [bitA, Finset.mem_insert, Finset.mem_singleton, add_sub_cancel_right] at this
    have := ih hn'
    omega

theorem HasDiagonalShape.diagHi_anti (h : HasDiagonalShape D) {a b : ℤ} (ha : a ∈ contents D)
    (hb : b ∈ contents D) (hab : a ≤ b) :
    diagHi D b ≤ diagHi D a ∧ diagHi D a ≤ diagHi D b + (b - a) := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ n hn ih =>
    have hn' : n ∈ contents D := h.between ha hb hn (by omega)
    have := (h.2.2.2.1 (n + 1) hb (by simpa using hn')).2
    simp only [bitB, Finset.mem_insert, Finset.mem_singleton, add_sub_cancel_right] at this
    have := ih hn'
    omega

theorem minContent_mem (hD : D.Nonempty) : minContent D ∈ contents D := by
  have hc : (contents D).Nonempty := hD.image _
  simp only [minContent, hc, ↓reduceDIte]
  exact Finset.min'_mem _ _

theorem maxContent_mem (hD : D.Nonempty) : maxContent D ∈ contents D := by
  have hc : (contents D).Nonempty := hD.image _
  simp only [maxContent, hc, ↓reduceDIte]
  exact Finset.max'_mem _ _

theorem minContent_le {k : ℤ} (hk : k ∈ contents D) : minContent D ≤ k := by
  have hc : (contents D).Nonempty := ⟨k, hk⟩
  simp only [minContent, hc, ↓reduceDIte]
  exact Finset.min'_le _ _ hk

theorem le_maxContent {k : ℤ} (hk : k ∈ contents D) : k ≤ maxContent D := by
  have hc : (contents D).Nonempty := ⟨k, hk⟩
  simp only [maxContent, hc, ↓reduceDIte]
  exact Finset.le_max' _ _ hk

theorem HasDiagonalShape.mem_contents_iff (h : HasDiagonalShape D) {k : ℤ} :
    k ∈ contents D ↔ minContent D ≤ k ∧ k ≤ maxContent D := by
  constructor
  · intro hk
    exact ⟨minContent_le hk, le_maxContent hk⟩
  · rintro ⟨h1, h2⟩
    exact h.between (minContent_mem h.1) (maxContent_mem h.1) h1 h2

/-- The `⟸` direction of the diagonal criterion, skewness. -/
theorem isSkew_of_hasDiagonalShape (h : HasDiagonalShape D) : IsSkew D := by
  have hne := h.1
  have hc0 := minContent_mem hne
  have hc1 := maxContent_mem hne
  have sing0 : diagLo D (minContent D) = diagHi D (minContent D) :=
    h.2.2.2.2 _ hc0 (Or.inl (fun hm => by have := minContent_le hm; omega))
  have sing1 : diagLo D (maxContent D) = diagHi D (maxContent D) :=
    h.2.2.2.2 _ hc1 (Or.inr (fun hm => by have := le_maxContent hm; omega))
  intro x hx y hy hxy1 hxy2 i hi j hj
  rw [Finset.mem_Icc] at hi hj
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only at hxy1 hxy2 hi hj
  have hx' : (a, a + (b - a)) ∈ D := by convert hx using 2; ring
  have hy' : (c, c + (d - c)) ∈ D := by convert hy using 2; ring
  have hxm := h.mem_iff.mp hx'
  have hym := h.mem_iff.mp hy'
  have hij : (i, i + (j - i)) = (i, j) := by simp
  rw [← hij, h.mem_iff]
  obtain ⟨hk1, hl1, hh1⟩ := hxm
  obtain ⟨hk2, hl2, hh2⟩ := hym
  have r1 := (h.mem_contents_iff.mp hk1)
  have r2 := (h.mem_contents_iff.mp hk2)
  -- range bounds
  have u1 := h.diagLo_anti hk1 hc1 r1.2
  have u2 := h.diagHi_anti hk2 hc1 r2.2
  have d1 := h.diagLo_anti hc0 hk1 r1.1
  have d2 := h.diagHi_anti hc0 hk2 r2.1
  have hkr : j - i ∈ contents D := by
    rw [h.mem_contents_iff]
    constructor <;> omega
  refine ⟨hkr, ?_, ?_⟩
  · rcases le_total (b - a) (j - i) with hle | hle
    · have := h.diagLo_anti hk1 hkr hle
      omega
    · have := h.diagLo_anti hkr hk1 hle
      omega
  · rcases le_total (j - i) (d - c) with hle | hle
    · have := h.diagHi_anti hkr hk2 hle
      omega
    · have := h.diagHi_anti hk2 hkr hle
      omega

/-- Each cell off the last diagonal has its eastern or northern neighbor on the next one. -/
theorem HasDiagonalShape.exists_next (h : HasDiagonalShape D) {x : ℤ × ℤ} (hx : x ∈ D)
    (hlt : content x < maxContent D) :
    ∃ z ∈ D, CellAdj x z ∧ content z = content x + 1 := by
  obtain ⟨a, b⟩ := x
  simp only [content] at hlt
  obtain ⟨k, hk⟩ : ∃ k, k = b - a := ⟨_, rfl⟩
  have hx' : (a, a + k) ∈ D := by convert hx using 2; omega
  obtain ⟨hk0, hl, hh⟩ := h.mem_iff.mp hx'
  have hk1 : k + 1 ∈ contents D := by
    rw [h.mem_contents_iff]
    have := minContent_le hk0
    omega
  have step := h.diagHi_anti hk0 hk1 (by omega)
  have step2 := h.diagLo_anti hk0 hk1 (by omega)
  have hlh := diagLo_le_diagHi hk1
  by_cases hcase : a ≤ diagHi D (k + 1)
  · refine ⟨(a, a + (k + 1)), ?_, ?_, ?_⟩
    · exact h.mem_iff.mpr ⟨hk1, by omega, hcase⟩
    · simp only [cellAdj_iff, true_and]; omega
    · simp only [content]; omega
  · refine ⟨(a - 1, a + k), ?_, ?_, ?_⟩
    · have : (a - 1, a + k) = (a - 1, a - 1 + (k + 1)) := by simp
      rw [this]
      exact h.mem_iff.mpr ⟨hk1, by omega, by omega⟩
    · simp only [cellAdj_iff]; omega
    · simp only [content]; omega

/-- The `⟸` direction of the diagonal criterion, connectedness. -/
theorem isEdgeConnected_of_hasDiagonalShape (h : HasDiagonalShape D) : IsEdgeConnected D := by
  refine ⟨h.1, ?_⟩
  have hc1 := maxContent_mem h.1
  have sing1 : diagLo D (maxContent D) = diagHi D (maxContent D) :=
    h.2.2.2.2 _ hc1 (Or.inr (fun hm => by have := le_maxContent hm; omega))
  set top : ℤ × ℤ := (diagLo D (maxContent D), diagLo D (maxContent D) + maxContent D) with htop
  have reach : ∀ n : ℕ, ∀ x ∈ D, maxContent D - content x = n →
      Relation.ReflTransGen (fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b) x top := by
    intro n
    induction n with
    | zero =>
      intro x hx hn
      have hxc : content x = maxContent D := by
        have := le_maxContent (content_mem_contents hx); omega
      have h1 := diagLo_le hx hxc
      have h2 := le_diagHi hx hxc
      have : x = top := by
        obtain ⟨a, b⟩ := x
        simp only [content] at hxc
        simp only [htop, Prod.mk.injEq]
        omega
      rw [this]
    | succ n ih =>
      intro x hx hn
      have hlt : content x < maxContent D := by omega
      obtain ⟨z, hz, hadj, hzc⟩ := h.exists_next hx hlt
      exact Relation.ReflTransGen.head ⟨hx, hz, hadj⟩ (ih z hz (by omega))
  intro x hx y hy
  have rx := reach (maxContent D - content x).toNat x hx
    (by have := le_maxContent (content_mem_contents hx); omega)
  have ry := reach (maxContent D - content y).toNat y hy
    (by have := le_maxContent (content_mem_contents hy); omega)
  have hsymm : Std.Symm (fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b) :=
    ⟨fun a b hab => ⟨hab.2.1, hab.1, hab.2.2.symm'⟩⟩
  exact rx.trans (Std.Symm.symm _ _ ry)

/-- The diagonal criterion for this supporting diagram API. -/
theorem isConnectedSkew_iff_diagonal {D : Diagram} :
    IsConnectedSkew D ↔ HasDiagonalShape D :=
  ⟨hasDiagonalShape_of_isConnectedSkew,
    fun h => ⟨isSkew_of_hasDiagonalShape h, isEdgeConnected_of_hasDiagonalShape h⟩⟩

instance (D : Diagram) : Decidable (IsConnectedSkew D) :=
  decidable_of_iff _ isConnectedSkew_iff_diagonal.symm

end Converse

theorem diagLo_eq_of {D : Diagram} {k l : ℤ} (h : (l, l + k) ∈ D)
    (hmin : ∀ i, (i, i + k) ∈ D → l ≤ i) : diagLo D k = l := by
  have h1 := diagLo_le (k := k) h (by ring)
  have h2 := hmin _ (diagLo_mem (mem_contents_iff.mpr ⟨l, h⟩))
  omega

theorem diagHi_eq_of {D : Diagram} {k l : ℤ} (h : (l, l + k) ∈ D)
    (hmax : ∀ i, (i, i + k) ∈ D → i ≤ l) : diagHi D k = l := by
  have h1 := le_diagHi (k := k) h (by ring)
  have h2 := hmax _ (diagHi_mem (mem_contents_iff.mpr ⟨l, h⟩))
  omega

/-- **The diagonal criterion in constructive form.**  A finite cell set whose diagonal of content
`k ∈ [c₀, c₁]` consists of the rows `[lo k, hi k]`, with steps `lo (k - 1) - lo k` and
`hi (k - 1) - hi k` in `{0, 1}` and singleton end diagonals, is a connected skew diagram. -/
theorem isConnectedSkew_of_rows (D : Diagram) (c₀ c₁ : ℤ) (lo hi : ℤ → ℤ) (hc : c₀ ≤ c₁)
    (hrows : ∀ i k : ℤ, (i, i + k) ∈ D ↔ c₀ ≤ k ∧ k ≤ c₁ ∧ lo k ≤ i ∧ i ≤ hi k)
    (hne : ∀ k, c₀ ≤ k → k ≤ c₁ → lo k ≤ hi k)
    (hA : ∀ k, c₀ < k → k ≤ c₁ → lo (k - 1) - lo k = 0 ∨ lo (k - 1) - lo k = 1)
    (hB : ∀ k, c₀ < k → k ≤ c₁ → hi (k - 1) - hi k = 0 ∨ hi (k - 1) - hi k = 1)
    (h0 : lo c₀ = hi c₀) (h1 : lo c₁ = hi c₁) : IsConnectedSkew D := by
  have hcell : ∀ k i : ℤ, (i, i + k) ∈ D ↔ c₀ ≤ k ∧ k ≤ c₁ ∧ lo k ≤ i ∧ i ≤ hi k :=
    fun k i => hrows i k
  have hmem : ∀ x : ℤ × ℤ, x ∈ D ↔
      c₀ ≤ content x ∧ content x ≤ c₁ ∧ lo (content x) ≤ x.1 ∧ x.1 ≤ hi (content x) := by
    rintro ⟨a, b⟩
    have := hcell (b - a) a
    rw [show a + (b - a) = b by ring] at this
    exact this
  have hcont : ∀ k, k ∈ contents D ↔ c₀ ≤ k ∧ k ≤ c₁ := by
    intro k
    rw [mem_contents_iff]
    constructor
    · rintro ⟨i, hi'⟩
      rw [hcell] at hi'; exact ⟨hi'.1, hi'.2.1⟩
    · rintro ⟨h1', h2'⟩
      exact ⟨lo k, (hcell k (lo k)).mpr ⟨h1', h2', le_refl _, hne k h1' h2'⟩⟩
  have hlo : ∀ k, c₀ ≤ k → k ≤ c₁ → diagLo D k = lo k := by
    intro k h1' h2'
    exact diagLo_eq_of ((hcell k (lo k)).mpr ⟨h1', h2', le_refl _, hne k h1' h2'⟩)
      (fun i hi' => ((hcell k i).mp hi').2.2.1)
  have hhi : ∀ k, c₀ ≤ k → k ≤ c₁ → diagHi D k = hi k := by
    intro k h1' h2'
    exact diagHi_eq_of ((hcell k (hi k)).mpr ⟨h1', h2', hne k h1' h2', le_refl _⟩)
      (fun i hi' => ((hcell k i).mp hi').2.2.2)
  rw [isConnectedSkew_iff_diagonal]
  refine ⟨⟨(lo c₀, lo c₀ + c₀), (hcell c₀ (lo c₀)).mpr ⟨le_refl _, hc, le_refl _,
    hne c₀ (le_refl _) hc⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy k hk
    have hx' := (hmem x).mp hx
    have hy' := (hmem y).mp hy
    rw [Finset.mem_Icc] at hk
    exact (hcont k).mpr ⟨by omega, by omega⟩
  · intro x hx y hy hxy i hi'
    have hx' := (hmem x).mp hx
    have hy' := (hmem y).mp hy
    rw [← hxy] at hy'
    rw [Finset.mem_Icc] at hi'
    have := (hcell (content x) i).mpr ⟨hx'.1, hx'.2.1, by omega, by omega⟩
    exact this
  · intro k hk hk'
    rw [hcont] at hk hk'
    unfold bitA bitB
    rw [hlo k hk.1 hk.2, hlo (k - 1) hk'.1 hk'.2, hhi k hk.1 hk.2, hhi (k - 1) hk'.1 hk'.2]
    have a1 := hA k (by omega) hk.2
    have b1 := hB k (by omega) hk.2
    constructor <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;> omega
  · intro k hk hend
    rw [hcont] at hk
    rw [hlo k hk.1 hk.2, hhi k hk.1 hk.2]
    rcases hend with h | h
    · have : k = c₀ := by
        by_contra hne'
        apply h
        rw [hcont]; omega
      rw [this]; exact h0
    · have : k = c₁ := by
        by_contra hne'
        apply h
        rw [hcont]; omega
      rw [this]; exact h1

/-! ## Span, southwest and northeast cells, normalization -/

section Span

variable {D : Diagram}

theorem HasDiagonalShape.contents_eq (h : HasDiagonalShape D) :
    contents D = Finset.Icc (minContent D) (maxContent D) := by
  ext k
  rw [h.mem_contents_iff, Finset.mem_Icc]

/-- For a connected skew diagram, the span is `max content - min content + 1`. -/
theorem span_eq_of_isConnectedSkew (h : IsConnectedSkew D) :
    (span D : ℤ) = maxContent D - minContent D + 1 := by
  have h' := isConnectedSkew_iff_diagonal.mp h
  unfold span
  rw [h'.contents_eq, Int.card_Icc]
  have : minContent D ≤ maxContent D := minContent_le (maxContent_mem h'.1)
  omega

theorem sw_mem (hD : D.Nonempty) : sw D ∈ D := by
  have := diagLo_mem (minContent_mem hD)
  exact this

theorem ne_mem (hD : D.Nonempty) : ne D ∈ D := diagLo_mem (maxContent_mem hD)

theorem content_sw (_ : D.Nonempty) : content (sw D) = minContent D := by
  simp [sw, content]

theorem content_ne (_ : D.Nonempty) : content (ne D) = maxContent D := by
  simp [ne, content]

theorem mem_translate {v y : ℤ × ℤ} : y ∈ translate v D ↔ y - v ∈ D := by
  unfold translate
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨y - v, h, by simp⟩

theorem mem_normalize {y : ℤ × ℤ} : y ∈ normalize D ↔ y + sw D ∈ D := by
  unfold normalize
  rw [mem_translate]
  simp

/-- Every cell of a connected skew diagram has content between that of `sw` and `ne`. -/
theorem content_sw_le {x : ℤ × ℤ} (hx : x ∈ D) : content (sw D) ≤ content x := by
  rw [content_sw ⟨x, hx⟩]
  exact minContent_le (content_mem_contents hx)

theorem content_le_ne {x : ℤ × ℤ} (hx : x ∈ D) : content x ≤ content (ne D) := by
  rw [content_ne ⟨x, hx⟩]
  exact le_maxContent (content_mem_contents hx)

end Span

/-! ## Reconstruction from the bit words -/

/-- The first row `ℓ_k = -(A_1 + ⋯ + A_k)` of the content-`k` diagonal reconstructed from the
bit word `A` (southwest cell at `(0, 0)`). -/
def bitsLo (A : ℕ → ℤ) (k : ℕ) : ℤ := -∑ m ∈ Finset.range k, A (m + 1)

/-- The height word `H_k = 1 + ∑_{m ≤ k} (A_m - B_m)`. -/
def heightWord (A B : ℕ → ℤ) (k : ℕ) : ℤ := 1 + ∑ m ∈ Finset.range k, (A (m + 1) - B (m + 1))

/-- The diagram with bit words `A`, `B` and southwest cell `(0, 0)`: on content `k < N` it
occupies the rows `ℓ_k, …, ℓ_k + H_k - 1`, where `ℓ_k = -(A_1 + ⋯ + A_k)`. -/
def fromBits (N : ℕ) (A B : ℕ → ℤ) : Diagram :=
  (Finset.range N).biUnion fun k =>
    (Finset.Icc (bitsLo A k) (bitsLo A k + heightWord A B k - 1)).image fun i =>
      (i, i + (k : ℤ))

/-- Admissible bit words of span `N`: the bits `A_k, B_k` (`1 ≤ k < N`) lie in `{0, 1}`, the
heights are positive, and the last height is one (the first, `H_0`, is one by definition). -/
def IsBitData (N : ℕ) (A B : ℕ → ℤ) : Prop :=
  0 < N ∧ (∀ k, 1 ≤ k → k < N → (A k = 0 ∨ A k = 1) ∧ (B k = 0 ∨ B k = 1)) ∧
    (∀ k, k < N → 0 < heightWord A B k) ∧ heightWord A B (N - 1) = 1

theorem mem_fromBits {N : ℕ} {A B : ℕ → ℤ} {i j : ℤ} :
    (i, j) ∈ fromBits N A B ↔
      ∃ k : ℕ, k < N ∧ j = i + k ∧ bitsLo A k ≤ i ∧ i ≤ bitsLo A k + heightWord A B k - 1 := by
  unfold fromBits
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_Icc,
    Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, i', ⟨h1, h2⟩, rfl, rfl⟩
    exact ⟨k, hk, rfl, h1, h2⟩
  · rintro ⟨k, hk, rfl, h1, h2⟩
    exact ⟨k, hk, i, ⟨h1, h2⟩, rfl, rfl⟩

theorem heightWord_succ (A B : ℕ → ℤ) (k : ℕ) :
    heightWord A B (k + 1) = heightWord A B k + (A (k + 1) - B (k + 1)) := by
  simp [heightWord, Finset.sum_range_succ]
  ring

theorem bitsLo_succ (A : ℕ → ℤ) (k : ℕ) : bitsLo A (k + 1) = bitsLo A k - A (k + 1) := by
  simp [bitsLo, Finset.sum_range_succ]
  ring

/-- The last row `h_k = ℓ_k + H_k - 1` equals `-(B_1 + ⋯ + B_k)`. -/
theorem bitsLo_add_heightWord (A B : ℕ → ℤ) (k : ℕ) :
    bitsLo A k + heightWord A B k - 1 = bitsLo B k := by
  induction k with
  | zero => simp [bitsLo, heightWord]
  | succ k ih =>
    rw [bitsLo_succ, heightWord_succ, bitsLo_succ]
    omega

theorem mem_fromBits' {N : ℕ} {A B : ℕ → ℤ} {i j : ℤ} :
    (i, j) ∈ fromBits N A B ↔
      ∃ k : ℕ, k < N ∧ j = i + k ∧ bitsLo A k ≤ i ∧ i ≤ bitsLo B k := by
  rw [mem_fromBits]
  simp only [bitsLo_add_heightWord]

section FromBits

variable {N : ℕ} {A B : ℕ → ℤ}

theorem bitsLo_le_of_isBitData (h : IsBitData N A B) {k : ℕ} (hk : k < N) :
    bitsLo A k ≤ bitsLo B k := by
  have := h.2.2.1 k hk
  have := bitsLo_add_heightWord A B k
  omega

theorem mem_fromBits_diag (_ : IsBitData N A B) {k : ℕ} {i : ℤ} (hk : k < N) :
    (i, i + k) ∈ fromBits N A B ↔ bitsLo A k ≤ i ∧ i ≤ bitsLo B k := by
  rw [mem_fromBits']
  constructor
  · rintro ⟨k', hk', hjk, h1, h2⟩
    have : k' = k := by exact_mod_cast (by omega : (k' : ℤ) = k)
    subst this
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨k, hk, rfl, h1, h2⟩

theorem mem_contents_fromBits (h : IsBitData N A B) {k : ℤ} :
    k ∈ contents (fromBits N A B) ↔ 0 ≤ k ∧ k < N := by
  rw [mem_contents_iff]
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_fromBits'] at hi
    obtain ⟨k', hk', hjk, -, -⟩ := hi
    omega
  · rintro ⟨h0, h1⟩
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    exact ⟨bitsLo A n, (mem_fromBits_diag h (by omega)).mpr
      ⟨le_refl _, bitsLo_le_of_isBitData h (by omega)⟩⟩

theorem diagLo_fromBits (h : IsBitData N A B) {n : ℕ} (hn : n < N) :
    diagLo (fromBits N A B) n = bitsLo A n := by
  apply diagLo_eq_of ((mem_fromBits_diag h hn).mpr
    ⟨le_refl _, bitsLo_le_of_isBitData h hn⟩)
  intro i hi
  exact ((mem_fromBits_diag h hn).mp hi).1

theorem diagHi_fromBits (h : IsBitData N A B) {n : ℕ} (hn : n < N) :
    diagHi (fromBits N A B) n = bitsLo B n := by
  apply diagHi_eq_of ((mem_fromBits_diag h hn).mpr
    ⟨bitsLo_le_of_isBitData h hn, le_refl _⟩)
  intro i hi
  exact ((mem_fromBits_diag h hn).mp hi).2

theorem fromBits_hasDiagonalShape (h : IsBitData N A B) :
    HasDiagonalShape (fromBits N A B) := by
  have hN := h.1
  have hhi : ∀ k, bitsLo A k + heightWord A B k - 1 = bitsLo B k :=
    bitsLo_add_heightWord A B
  have hbits := h.2.1
  have hlast := h.2.2.2
  have memD := fun (k : ℕ) (i : ℤ) (hk : k < N) => mem_fromBits_diag h (i := i) hk
  have contD := fun k : ℤ => mem_contents_fromBits h (k := k)
  have loD := fun (n : ℕ) (hn : n < N) => diagLo_fromBits h hn
  have hiD := fun (n : ℕ) (hn : n < N) => diagHi_fromBits h hn
  have hle := fun (k : ℕ) (hk : k < N) => bitsLo_le_of_isBitData h hk
  refine ⟨⟨(0, 0), ?_⟩, ?_, ?_, ?_, ?_⟩
  · have := (memD 0 0 hN).mpr (by simp [bitsLo])
    simpa using this
  · intro x hx y hy k hk
    rw [Finset.mem_Icc] at hk
    have h1 := (contD _).mp (content_mem_contents hx)
    have h2 := (contD _).mp (content_mem_contents hy)
    exact (contD k).mpr ⟨by omega, by omega⟩
  · intro x hx y hy hxy i hi
    rw [Finset.mem_Icc] at hi
    have h1 := (contD _).mp (content_mem_contents hx)
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h1.1
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    simp only [content] at hxy hn h1 hi ⊢
    have hxm : (a, a + (n : ℤ)) ∈ fromBits N A B := by convert hx using 2; omega
    have hym : (c, c + (n : ℤ)) ∈ fromBits N A B := by convert hy using 2; omega
    have e1 := (memD n a (by omega)).mp hxm
    have e2 := (memD n c (by omega)).mp hym
    have : (i, i + (b - a)) = (i, i + (n : ℤ)) := by simp; omega
    rw [this]
    exact (memD n i (by omega)).mpr ⟨by omega, by omega⟩
  · intro k hk hk1
    have hk' := (contD k).mp hk
    have hk1' := (contD (k - 1)).mp hk1
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk'.1
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm
    have hbA := (hbits (m + 1) (by omega) (by omega))
    have e1 : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
    have hlo := loD m (by omega)
    have hlo' := loD (m + 1) (by omega)
    have hh := hiD m (by omega)
    have hh' := hiD (m + 1) (by omega)
    simp only [bitA, bitB, e1, hlo, hlo', hh, hh', bitsLo_succ]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro k hk hend
    have hk' := (contD k).mp hk
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk'.1
    rw [loD n (by omega), hiD n (by omega)]
    rcases hend with h | h
    · have : n = 0 := by
        by_contra hn
        exact h ((contD _).mpr ⟨by omega, by omega⟩)
      subst this
      simp [bitsLo]
    · have : n = N - 1 := by
        by_contra hn
        exact h ((contD _).mpr ⟨by omega, by omega⟩)
      subst this
      have := hhi (N - 1)
      omega

theorem isConnectedSkew_fromBits (h : IsBitData N A B) : IsConnectedSkew (fromBits N A B) :=
  isConnectedSkew_iff_diagonal.mpr (fromBits_hasDiagonalShape h)

theorem minContent_fromBits (h : IsBitData N A B) : minContent (fromBits N A B) = 0 := by
  have h' := fromBits_hasDiagonalShape h
  have hmem := minContent_mem h'.1
  have h1 := (mem_contents_fromBits h).mp hmem
  have h2 := minContent_le ((mem_contents_fromBits h).mpr ⟨le_refl (0 : ℤ), by have := h.1; omega⟩)
  omega

theorem maxContent_fromBits (h : IsBitData N A B) :
    maxContent (fromBits N A B) = (N : ℤ) - 1 := by
  have h' := fromBits_hasDiagonalShape h
  have hmem := maxContent_mem h'.1
  have h1 := (mem_contents_fromBits h).mp hmem
  have hN := h.1
  have h2 := le_maxContent ((mem_contents_fromBits h).mpr
    ⟨(by omega : (0 : ℤ) ≤ (N : ℤ) - 1), by omega⟩)
  omega

theorem span_fromBits (h : IsBitData N A B) : span (fromBits N A B) = N := by
  have := span_eq_of_isConnectedSkew (isConnectedSkew_fromBits h)
  rw [minContent_fromBits h, maxContent_fromBits h] at this
  omega

theorem sw_fromBits (h : IsBitData N A B) : sw (fromBits N A B) = (0, 0) := by
  have := diagLo_fromBits h h.1
  simp only [Nat.cast_zero] at this
  simp [sw, minContent_fromBits h, this, bitsLo]

theorem bitA_fromBits (h : IsBitData N A B) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < N) :
    bitA (fromBits N A B) (minContent (fromBits N A B) + k) = A k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
  rw [minContent_fromBits h]
  simp only [bitA, zero_add, e1, diagLo_fromBits h (by omega : m < N),
    diagLo_fromBits h hk, bitsLo_succ]
  ring

theorem bitB_fromBits (h : IsBitData N A B) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < N) :
    bitB (fromBits N A B) (minContent (fromBits N A B) + k) = B k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
  rw [minContent_fromBits h]
  simp only [bitB, zero_add, e1, diagHi_fromBits h (by omega : m < N),
    diagHi_fromBits h hk, bitsLo_succ]
  ring

end FromBits

/-! ### The reconstruction is inverse to taking bits -/

section Reconstruction

variable {D : Diagram}

/-- A connected skew diagram, southwest-normalized, is the diagram reconstructed from its
bit words (the bit words read from content `minContent D` on). -/
theorem normalize_eq_fromBits (h : IsConnectedSkew D) :
    normalize D = fromBits (span D) (fun k => bitA D (minContent D + k))
      (fun k => bitB D (minContent D + k)) := by
  have h' := isConnectedSkew_iff_diagonal.mp h
  have hne := h'.1
  have hc0 := minContent_mem hne
  have hspan := span_eq_of_isConnectedSkew h
  have sing : diagLo D (minContent D) = diagHi D (minContent D) :=
    h'.2.2.2.2 _ hc0 (Or.inl (fun hm => by have := minContent_le hm; omega))
  set c₀ := minContent D with hc₀
  set s := diagLo D c₀ with hs
  have loA : ∀ n : ℕ, n < span D →
      bitsLo (fun k => bitA D (c₀ + k)) n = diagLo D (c₀ + n) - s := by
    intro n
    induction n with
    | zero => intro _; simp [bitsLo]; omega
    | succ n ih =>
      intro hn
      have e1 : c₀ + ((n + 1 : ℕ) : ℤ) - 1 = c₀ + n := by push_cast; ring
      rw [bitsLo_succ, ih (by omega)]
      simp only [bitA, e1]
      push_cast
      ring_nf
  have hiB : ∀ n : ℕ, n < span D →
      bitsLo (fun k => bitB D (c₀ + k)) n = diagHi D (c₀ + n) - s := by
    intro n
    induction n with
    | zero => intro _; simp [bitsLo]; omega
    | succ n ih =>
      intro hn
      have e1 : c₀ + ((n + 1 : ℕ) : ℤ) - 1 = c₀ + n := by push_cast; ring
      rw [bitsLo_succ, ih (by omega)]
      simp only [bitB, e1]
      push_cast
      ring_nf
  ext ⟨i, j⟩
  rw [mem_fromBits']
  unfold normalize
  rw [mem_translate]
  have hsw : sw D = (s, s + c₀) := rfl
  have e2 : ((i, j) - -sw D) = (i + s, (i + s) + (j - i + c₀)) := by
    rw [hsw]; ext <;> simp; ring
  rw [e2]
  constructor
  · intro hm
    obtain ⟨hk, h1, h2⟩ := h'.mem_iff.mp hm
    have hr := h'.mem_contents_iff.mp hk
    refine ⟨(j - i).toNat, by omega, by omega, ?_, ?_⟩
    · rw [loA _ (by omega)]
      have : c₀ + (((j - i).toNat : ℕ) : ℤ) = j - i + c₀ := by omega
      rw [this]; omega
    · rw [hiB _ (by omega)]
      have : c₀ + (((j - i).toNat : ℕ) : ℤ) = j - i + c₀ := by omega
      rw [this]; omega
  · rintro ⟨n, hn, hj, h1, h2⟩
    rw [loA n hn] at h1
    rw [hiB n hn] at h2
    have hk : j - i + c₀ = c₀ + n := by omega
    rw [hk]
    refine h'.mem_iff.mpr ⟨h'.mem_contents_iff.mpr ⟨by omega, by omega⟩, ?_, ?_⟩ <;> omega

theorem isBitData_of_isConnectedSkew (h : IsConnectedSkew D) :
    IsBitData (span D) (fun k => bitA D (minContent D + k))
      (fun k => bitB D (minContent D + k)) := by
  have h' := isConnectedSkew_iff_diagonal.mp h
  have hspan := span_eq_of_isConnectedSkew h
  have hc0 := minContent_mem h'.1
  have sing : diagLo D (minContent D) = diagHi D (minContent D) :=
    h'.2.2.2.2 _ hc0 (Or.inl (fun hm => by have := minContent_le hm; omega))
  have sing1 : diagLo D (maxContent D) = diagHi D (maxContent D) :=
    h'.2.2.2.2 _ (maxContent_mem h'.1)
      (Or.inr (fun hm => by have := le_maxContent hm; omega))
  have hH : ∀ n : ℕ, n < span D →
      heightWord (fun k => bitA D (minContent D + k)) (fun k => bitB D (minContent D + k)) n
        = height D (minContent D + n) := by
    intro n
    induction n with
    | zero => intro _; simp [heightWord, height, sing]
    | succ n ih =>
      intro hn
      rw [heightWord_succ, ih (by omega)]
      have e1 : minContent D + ((n + 1 : ℕ) : ℤ) - 1 = minContent D + n := by push_cast; ring
      simp only [height, bitA, bitB, e1]
      push_cast
      ring_nf
  have hle := minContent_le (maxContent_mem h'.1)
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro k hk1 hk2
    have hk : minContent D + k ∈ contents D := h'.mem_contents_iff.mpr ⟨by omega, by omega⟩
    have hk' : minContent D + k - 1 ∈ contents D := h'.mem_contents_iff.mpr ⟨by omega, by omega⟩
    have := h'.2.2.2.1 _ hk hk'
    simpa [bitA, bitB] using this
  · intro k hk
    rw [hH k hk]
    have hmem : minContent D + k ∈ contents D :=
      h'.mem_contents_iff.mpr ⟨by omega, by omega⟩
    have := diagLo_le_diagHi hmem
    simp only [height]; omega
  · have hk : span D - 1 < span D := by omega
    rw [hH _ hk]
    have e1 : minContent D + ((span D - 1 : ℕ) : ℤ) = maxContent D := by omega
    rw [e1]
    simp only [height]
    omega

end Reconstruction

/-- Southwest-normalized connected skew diagrams are determined by their span and bit words:
two connected skew diagrams with the same span and the same bit words (read from the least
content) are translates of one another. -/
theorem eq_translate_of_bits {D₁ D₂ : Diagram} (h₁ : IsConnectedSkew D₁)
    (h₂ : IsConnectedSkew D₂) (hN : span D₁ = span D₂)
    (hA : ∀ k : ℕ, 1 ≤ k → k < span D₁ →
      bitA D₁ (minContent D₁ + k) = bitA D₂ (minContent D₂ + k))
    (hB : ∀ k : ℕ, 1 ≤ k → k < span D₁ →
      bitB D₁ (minContent D₁ + k) = bitB D₂ (minContent D₂ + k)) :
    ∃ v, D₂ = translate v D₁ := by
  have e1 := normalize_eq_fromBits h₁
  have e2 := normalize_eq_fromBits h₂
  have hAB : fromBits (span D₁) (fun k => bitA D₁ (minContent D₁ + k))
        (fun k => bitB D₁ (minContent D₁ + k)) =
      fromBits (span D₂) (fun k => bitA D₂ (minContent D₂ + k))
        (fun k => bitB D₂ (minContent D₂ + k)) := by
    ext ⟨i, j⟩
    rw [mem_fromBits', mem_fromBits']
    have hs : ∀ n : ℕ, n < span D₁ →
        bitsLo (fun k => bitA D₁ (minContent D₁ + k)) n =
          bitsLo (fun k => bitA D₂ (minContent D₂ + k)) n ∧
        bitsLo (fun k => bitB D₁ (minContent D₁ + k)) n =
          bitsLo (fun k => bitB D₂ (minContent D₂ + k)) n := by
      intro n
      induction n with
      | zero => intro _; simp [bitsLo]
      | succ n ih =>
        intro hn
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        rw [bitsLo_succ, bitsLo_succ, bitsLo_succ, bitsLo_succ, ih1, ih2]
        have := hA (n + 1) (by omega) hn
        have := hB (n + 1) (by omega) hn
        constructor <;> push_cast at * <;> omega
    constructor
    · rintro ⟨n, hn, hj, h1, h2⟩
      refine ⟨n, by omega, hj, ?_, ?_⟩
      · rw [← (hs n hn).1]; exact h1
      · rw [← (hs n hn).2]; exact h2
    · rintro ⟨n, hn, hj, h1, h2⟩
      refine ⟨n, by omega, hj, ?_, ?_⟩
      · rw [(hs n (by omega)).1]; exact h1
      · rw [(hs n (by omega)).2]; exact h2
  rw [← e1, ← e2] at hAB
  refine ⟨sw D₂ - sw D₁, ?_⟩
  ext x
  have m1 := mem_normalize (D := D₁) (y := x - sw D₂)
  have m2 := mem_normalize (D := D₂) (y := x - sw D₂)
  rw [mem_translate]
  have : x - (sw D₂ - sw D₁) = (x - sw D₂) + sw D₁ := by abel
  rw [this, ← m1, hAB, m2]
  simp

/-- **Reconstruction from bit words.**  Two admissible bit words of span `N` define a connected
skew diagram of span `N` with those bit words and southwest cell `(0, 0)`, and any connected
skew diagram with the same span and bit words is a translate of it. -/
theorem exists_unique_connectedSkew_of_bits {N : ℕ} {A B : ℕ → ℤ} (h : IsBitData N A B) :
    IsConnectedSkew (fromBits N A B) ∧ span (fromBits N A B) = N ∧
      sw (fromBits N A B) = (0, 0) ∧
      (∀ k : ℕ, 1 ≤ k → k < N →
        bitA (fromBits N A B) (minContent (fromBits N A B) + k) = A k ∧
        bitB (fromBits N A B) (minContent (fromBits N A B) + k) = B k) ∧
      ∀ D : Diagram, IsConnectedSkew D → span D = N →
        (∀ k : ℕ, 1 ≤ k → k < N → bitA D (minContent D + k) = A k ∧
          bitB D (minContent D + k) = B k) →
        ∃ v, D = translate v (fromBits N A B) := by
  refine ⟨isConnectedSkew_fromBits h, span_fromBits h, sw_fromBits h,
    fun k hk1 hk => ⟨bitA_fromBits h hk1 hk, bitB_fromBits h hk1 hk⟩, ?_⟩
  intro D hD hN hbits
  refine (eq_translate_of_bits (isConnectedSkew_fromBits h) hD
    (by rw [span_fromBits h, hN]) ?_ ?_).imp fun v hv => hv
  · intro k hk1 hk
    rw [span_fromBits h] at hk
    rw [bitA_fromBits h hk1 hk, (hbits k hk1 hk).1]
  · intro k hk1 hk
    rw [span_fromBits h] at hk
    rw [bitB_fromBits h hk1 hk, (hbits k hk1 hk).2]

/-! ## Invariance under translation, rotation, transposition, antitransposition -/

section Invariance

variable {D : Diagram}

theorem content_add (x v : ℤ × ℤ) : content (x + v) = content x + content v := by
  simp [content]; ring

theorem mem_rotate {y : ℤ × ℤ} : y ∈ rotate D ↔ -y ∈ D := by
  unfold rotate
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨-y, h, by simp⟩

theorem mem_antitranspose {y : ℤ × ℤ} : y ∈ antitranspose D ↔ (-y.2, -y.1) ∈ D := by
  unfold antitranspose
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨(-y.2, -y.1), h, by simp⟩

theorem mem_transpose {y : ℤ × ℤ} : y ∈ transpose D ↔ y.swap ∈ D := by
  unfold transpose
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨y.swap, h, by simp⟩

theorem rotate_rotate : rotate (rotate D) = D := by
  ext y; rw [mem_rotate, mem_rotate]; simp

theorem transpose_transpose : transpose (transpose D) = D := by
  ext y; rw [mem_transpose, mem_transpose]; simp

theorem antitranspose_antitranspose : antitranspose (antitranspose D) = D := by
  ext y; rw [mem_antitranspose, mem_antitranspose]; simp

theorem translate_translate (v w : ℤ × ℤ) :
    translate v (translate w D) = translate (v + w) D := by
  ext y; rw [mem_translate, mem_translate, mem_translate]; simp [sub_sub]

theorem translate_zero : translate 0 D = D := by
  ext y; rw [mem_translate]; simp

theorem translate_injective (v : ℤ × ℤ) {D₁ D₂ : Diagram}
    (h : translate v D₁ = translate v D₂) : D₁ = D₂ := by
  ext y
  have := congrArg (fun S => y + v ∈ S) h
  simpa [mem_translate] using this

theorem isEdgeConnected_image {f : ℤ × ℤ → ℤ × ℤ} (hf : ∀ a b, CellAdj a b → CellAdj (f a) (f b))
    (h : IsEdgeConnected D) : IsEdgeConnected (D.image f) := by
  refine ⟨h.1.image _, ?_⟩
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  exact Relation.ReflTransGen.lift f (p := fun a b => a ∈ D.image f ∧ b ∈ D.image f ∧ CellAdj a b)
    (fun a b hab => ⟨Finset.mem_image_of_mem _ hab.1, Finset.mem_image_of_mem _ hab.2.1,
      hf _ _ hab.2.2⟩) x y (h.2 x hx y hy)

theorem isSkew_translate (v : ℤ × ℤ) (h : IsSkew D) : IsSkew (translate v D) := by
  intro x hx y hy h1 h2 i hi j hj
  rw [mem_translate] at hx hy ⊢
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Finset.mem_Icc] at *
  exact h.mem hx hy (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem isSkew_rotate (h : IsSkew D) : IsSkew (rotate D) := by
  intro x hx y hy h1 h2 i hi j hj
  rw [mem_rotate] at hx hy ⊢
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Finset.mem_Icc] at *
  exact h.mem hy hx (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem isSkew_transpose (h : IsSkew D) : IsSkew (transpose D) := by
  intro x hx y hy h1 h2 i hi j hj
  rw [mem_transpose] at hx hy ⊢
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Finset.mem_Icc, Prod.swap] at *
  exact h.mem hx hy (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem isSkew_antitranspose (h : IsSkew D) : IsSkew (antitranspose D) := by
  intro x hx y hy h1 h2 i hi j hj
  rw [mem_antitranspose] at hx hy ⊢
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Finset.mem_Icc] at *
  exact h.mem hy hx (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem isConnectedSkew_translate (v : ℤ × ℤ) (h : IsConnectedSkew D) :
    IsConnectedSkew (translate v D) :=
  ⟨isSkew_translate v h.1, isEdgeConnected_image (f := (· + v)) (fun a b hab => by
    rw [cellAdj_iff] at hab ⊢; simp only [Prod.fst_add, Prod.snd_add]; omega) h.2⟩

theorem isConnectedSkew_rotate (h : IsConnectedSkew D) : IsConnectedSkew (rotate D) :=
  ⟨isSkew_rotate h.1, isEdgeConnected_image (f := fun x => -x) (fun a b hab => by
    rw [cellAdj_iff] at hab ⊢; simp only [Prod.fst_neg, Prod.snd_neg]; omega) h.2⟩

theorem isConnectedSkew_transpose (h : IsConnectedSkew D) : IsConnectedSkew (transpose D) :=
  ⟨isSkew_transpose h.1, isEdgeConnected_image (f := Prod.swap) (fun a b hab => by
    rw [cellAdj_iff] at hab ⊢; simp only [Prod.fst_swap, Prod.snd_swap]; omega) h.2⟩

theorem isConnectedSkew_antitranspose (h : IsConnectedSkew D) :
    IsConnectedSkew (antitranspose D) :=
  ⟨isSkew_antitranspose h.1,
    isEdgeConnected_image (f := fun x => (-x.2, -x.1)) (fun a b hab => by
      rw [cellAdj_iff] at hab ⊢; simp only; omega) h.2⟩

theorem isConnectedSkew_normalize (h : IsConnectedSkew D) : IsConnectedSkew (normalize D) :=
  isConnectedSkew_translate _ h

theorem contents_translate (v : ℤ × ℤ) :
    contents (translate v D) = (contents D).image (· + content v) := by
  ext k
  simp only [contents, translate, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨content x, ⟨x, hx, rfl⟩, (content_add x v).symm⟩
  · rintro ⟨c, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x + v, ⟨x, hx, rfl⟩, content_add x v⟩

theorem span_translate (v : ℤ × ℤ) : span (translate v D) = span D := by
  unfold span
  rw [contents_translate, Finset.card_image_of_injective _ (add_left_injective _)]

theorem contents_rotate : contents (rotate D) = (contents D).image (fun k => -k) := by
  ext k
  simp only [contents, rotate, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨content x, ⟨x, hx, rfl⟩, by simp [content]; ring⟩
  · rintro ⟨c, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨-x, ⟨x, hx, rfl⟩, by simp [content]; ring⟩

theorem span_rotate : span (rotate D) = span D := by
  unfold span
  rw [contents_rotate, Finset.card_image_of_injective _ neg_injective]

theorem contents_transpose : contents (transpose D) = (contents D).image (fun k => -k) := by
  ext k
  simp only [contents, transpose, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨content x, ⟨x, hx, rfl⟩, by simp [content]⟩
  · rintro ⟨c, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x.swap, ⟨x, hx, rfl⟩, by simp [content]⟩

theorem span_transpose : span (transpose D) = span D := by
  unfold span
  rw [contents_transpose, Finset.card_image_of_injective _ neg_injective]

/-- Antitransposition fixes every content. -/
theorem content_antitranspose (x : ℤ × ℤ) : content (-x.2, -x.1) = content x := by
  simp [content]; ring

theorem contents_antitranspose : contents (antitranspose D) = contents D := by
  ext k
  simp only [contents, antitranspose, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (content_antitranspose x).symm ▸ rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(-x.2, -x.1), ⟨x, hx, rfl⟩, content_antitranspose x⟩

theorem span_antitranspose : span (antitranspose D) = span D := by
  unfold span
  rw [contents_antitranspose]

end Invariance

section SwNe

variable {D : Diagram}

theorem minContent_eq_of {k : ℤ} (hk : k ∈ contents D) (h : ∀ k' ∈ contents D, k ≤ k') :
    minContent D = k :=
  le_antisymm (minContent_le hk) (h _ (minContent_mem (by
    obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
    exact ⟨_, hi⟩)))

theorem maxContent_eq_of {k : ℤ} (hk : k ∈ contents D) (h : ∀ k' ∈ contents D, k' ≤ k) :
    maxContent D = k :=
  le_antisymm (h _ (maxContent_mem (by
    obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
    exact ⟨_, hi⟩))) (le_maxContent hk)

theorem mem_contents_translate {v : ℤ × ℤ} {k : ℤ} :
    k ∈ contents (translate v D) ↔ k - content v ∈ contents D := by
  rw [contents_translate]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩; simpa using hc
  · intro h; exact ⟨k - content v, h, by ring⟩

theorem minContent_translate (hD : D.Nonempty) (v : ℤ × ℤ) :
    minContent (translate v D) = minContent D + content v := by
  apply minContent_eq_of
  · rw [mem_contents_translate]; simpa using minContent_mem hD
  · intro k hk
    rw [mem_contents_translate] at hk
    have := minContent_le hk
    omega

theorem maxContent_translate (hD : D.Nonempty) (v : ℤ × ℤ) :
    maxContent (translate v D) = maxContent D + content v := by
  apply maxContent_eq_of
  · rw [mem_contents_translate]; simpa using maxContent_mem hD
  · intro k hk
    rw [mem_contents_translate] at hk
    have := le_maxContent hk
    omega

theorem diagLo_translate (v : ℤ × ℤ) (k : ℤ) (hk : k ∈ contents D) :
    diagLo (translate v D) (k + content v) = diagLo D k + v.1 := by
  apply diagLo_eq_of
  · rw [mem_translate]
    have := diagLo_mem hk
    convert this using 2 <;> simp [content]; ring
  · intro i hi
    rw [mem_translate] at hi
    have := diagLo_le (D := D) (k := k) hi (by simp [content]; ring)
    simp at this
    omega

theorem diagHi_translate (v : ℤ × ℤ) (k : ℤ) (hk : k ∈ contents D) :
    diagHi (translate v D) (k + content v) = diagHi D k + v.1 := by
  apply diagHi_eq_of
  · rw [mem_translate]
    have := diagHi_mem hk
    convert this using 2 <;> simp [content]; ring
  · intro i hi
    rw [mem_translate] at hi
    have := le_diagHi (D := D) (k := k) hi (by simp [content]; ring)
    simp at this
    omega

theorem sw_translate (hD : D.Nonempty) (v : ℤ × ℤ) : sw (translate v D) = sw D + v := by
  have := diagLo_translate v _ (minContent_mem hD)
  simp only [sw, minContent_translate hD, this]
  ext <;> simp [content]; ring

theorem ne_translate (hD : D.Nonempty) (v : ℤ × ℤ) : ne (translate v D) = ne D + v := by
  have := diagLo_translate v _ (maxContent_mem hD)
  simp only [ne, maxContent_translate hD, this]
  ext <;> simp [content]; ring

/-- Normalization is constant on translation classes. -/
theorem normalize_translate (hD : D.Nonempty) (v : ℤ × ℤ) :
    normalize (translate v D) = normalize D := by
  unfold normalize
  rw [sw_translate hD, translate_translate]
  congr 1
  abel

theorem mem_contents_rotate {k : ℤ} : k ∈ contents (rotate D) ↔ -k ∈ contents D := by
  rw [contents_rotate]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩; simpa using hc
  · intro h; exact ⟨-k, h, by simp⟩

theorem minContent_rotate (hD : D.Nonempty) : minContent (rotate D) = -maxContent D := by
  apply minContent_eq_of
  · rw [mem_contents_rotate]; simpa using maxContent_mem hD
  · intro k hk
    rw [mem_contents_rotate] at hk
    have := le_maxContent hk
    omega

theorem maxContent_rotate (hD : D.Nonempty) : maxContent (rotate D) = -minContent D := by
  apply maxContent_eq_of
  · rw [mem_contents_rotate]; simpa using minContent_mem hD
  · intro k hk
    rw [mem_contents_rotate] at hk
    have := minContent_le hk
    omega

theorem diagLo_rotate (k : ℤ) : diagLo (rotate D) (-k) = - diagHi D k := by
  by_cases hk : k ∈ contents D
  · apply diagLo_eq_of
    · rw [mem_rotate]
      have := diagHi_mem hk
      convert this using 2 <;> simp [add_comm]
    · intro i hi
      rw [mem_rotate] at hi
      have := le_diagHi (D := D) (k := k) (i := -i) (j := -(i + -k)) (by
        convert hi using 2) (by ring)
      omega
  · have h1 : diagRows (rotate D) (-k) = ∅ := by
      ext i
      simp only [Finset.notMem_empty, iff_false]
      intro hi
      rw [mem_diagRows, mem_rotate] at hi
      exact hk (mem_contents_iff.mpr ⟨-i, by convert hi using 2; simp [add_comm]⟩)
    have h2 : diagRows D k = ∅ := by
      ext i
      simp only [Finset.notMem_empty, iff_false]
      intro hi
      exact hk (mem_contents.mpr ⟨i, hi⟩)
    simp [diagLo, diagHi, h1, h2]

theorem diagHi_rotate (k : ℤ) : diagHi (rotate D) k = - diagLo D (-k) := by
  have := diagLo_rotate (D := rotate D) k
  rw [rotate_rotate] at this
  omega

theorem sw_rotate (h : IsConnectedSkew D) : sw (rotate D) = -(ne D) := by
  have h' := isConnectedSkew_iff_diagonal.mp h
  have sing1 : diagLo D (maxContent D) = diagHi D (maxContent D) :=
    h'.2.2.2.2 _ (maxContent_mem h'.1)
      (Or.inr (fun hm => by have := le_maxContent hm; omega))
  have := diagLo_rotate (D := D) (maxContent D)
  simp only [sw, ne, minContent_rotate h'.1, this, ← sing1]
  ext <;> simp [add_comm]

theorem ne_rotate (h : IsConnectedSkew D) : ne (rotate D) = -(sw D) := by
  have h' := isConnectedSkew_iff_diagonal.mp h
  have sing0 : diagLo D (minContent D) = diagHi D (minContent D) :=
    h'.2.2.2.2 _ (minContent_mem h'.1)
      (Or.inl (fun hm => by have := minContent_le hm; omega))
  have := diagLo_rotate (D := D) (minContent D)
  rw [← sing0] at this
  simp only [ne, sw, maxContent_rotate h'.1, this]
  ext <;> simp [add_comm]

end SwNe

/-! ## Checked examples -/

section Examples

/-- The inner `(4, 4, 2) / (2)` of the gauge example is a connected skew diagram. -/
example : IsConnectedSkew (skewOf [4, 4, 2] [2]) := by decide

/-- The hook `(2, 1)` and its rotation `(2, 2) / (1)`. -/
example : IsConnectedSkew (skewOf [2, 1] []) := by decide

example : translate (1, 1) (rotate (skewOf [2, 1] [])) = skewOf [2, 2] [1] := by decide

/-- Two cells that are not edge-connected: `(2, 1) / (1)` is skew but disconnected. -/
example : IsSkew (skewOf [2, 1] [1]) ∧ ¬ IsConnectedSkew (skewOf [2, 1] [1]) := by decide

/-- A diagonal pair of cells is not skew (the rectangle between them is missing). -/
example : ¬ IsSkew ({(0, 0), (1, 1)} : Diagram) := by decide

/-- A staircase `(2, 1)` with a hole: not skew. -/
example : ¬ IsSkew ({(0, 0), (0, 2), (1, 0), (1, 1), (1, 2)} : Diagram) := by decide

example : span (skewOf [4, 4, 2] [2]) = 6 := by decide
example : sw (skewOf [4, 4, 2] [2]) = (2, 0) := by decide
example : ne (skewOf [4, 4, 2] [2]) = (0, 3) := by decide

/-- The bit words of the `2 × 2` square: `A = (1, 0)`, `B = (0, 1)`, heights `1, 2, 1`. -/
example : normalize (skewOf [2, 2] []) =
    fromBits 3 (fun k => if k = 1 then 1 else 0) (fun k => if k = 2 then 1 else 0) := by
  decide

/-- The bit words of the hook `(2, 1)`: `A = B = (1, 0)`, heights `1, 1, 1`. -/
example : normalize (skewOf [2, 1] []) =
    fromBits 3 (fun k => if k = 1 then 1 else 0) (fun k => if k = 1 then 1 else 0) := by
  decide

example : IsBitData 3 (fun k => if k = 1 then 1 else 0) (fun k => if k = 2 then 1 else 0) := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro k h1 h2; interval_cases k <;> simp
  · intro k hk; interval_cases k <;> simp [heightWord, Finset.sum_range_succ]
  · simp [heightWord, Finset.sum_range_succ]

end Examples

end SkewGluing
