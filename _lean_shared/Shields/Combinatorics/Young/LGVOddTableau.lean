/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.LGVMixed
import Shields.Combinatorics.Young.LGVTableau

/-!
# The mixed alphabet at `m` rows

`Shields.Combinatorics.Young.LGVMixed` reduces the `m × m` Jacobi--Trudi determinant over the
mixed alphabet to the non-intersecting families of `m` mixed paths, at every `m` and with no
hypotheses, and leaves one residue: `Shields.NonIntersectingIsSuperSkewSchur`, that those families
carry the branching sum.  Three ingredients stood between the two, each proved at two rows only.
This module proves all three at every `m` and discharges the residue.

* **The odd tableau bijection at `m` columns.**  Column `i` of `λ' / ν'` is the word of the path
  of row `i`, read at the source `Shields.jtSource` prescribes, `ν_i + (m-1-i)`, and the cell
  `(j, i)` carries the letter that path writes at abscissa `j + (m-1-i)`.  `Shields.eRowPath`
  traces a column, `Shields.eSkewEntryM` reads back, and
  `Shields.sum_nonEIntersecting_eq_skewSchurTranspose` is the identity.  Point disjointness is the
  weak row condition and the unit step is `col_strict`, exactly as at two columns; what is new is
  the offset.  Consecutive columns differ by one, so a weak row inequality buys a full step
  (`Shields.lt_eRowPath_succ`), and a general pair chains through the columns between them -- in
  the reading direction with a **gap**, `Shields.le_famPath_of_not_eIntersects`: columns
  `i₁ < i₂` are separated by `i₂ - i₁`, which is exactly the difference of their offsets.
* **The splice at height `b`, at `m` paths.**  `Shields.sum_nonIntersecting_mixed_split`: fixing
  the abscissa of every path at height `b`, the mixed families factor into a non-crossing even
  family below and a non-meeting odd family above, weight for weight.  `Shields.mIntersects_iff`
  is the one new fact -- the mixed predicate on a family is the even predicate on the truncations
  *or* the odd predicate on the shifts.
* **The dictionary.**  The `m` abscissae at height `b` are the intermediate shape:
  `Shields.mRows` builds the diagram with prescribed row lengths, and
  `Shields.shapeOfAbscissae` sends `c` to the shape with `ν_i = c_i - (m-1-i)`, inverse to
  `ν ↦ jtSource ν m`.  A fiber whose `c` is not strictly decreasing has an empty odd half, and
  strict decrease of `c` is exactly the partition condition on `ν` once the offsets are
  subtracted.

## Main results

* `Shields.nonIntersectingIsSuperSkewSchur` -- the residue, at every `m`.
* `Shields.skewJacobiTrudi` -- hence the skew Jacobi--Trudi identity for the mixed alphabet with
  nothing assumed: for every `μ ⊆ λ` inside `m` rows, over any commutative ring,
  `det [d_{λ_u - μ_v - u + v}]_{u,v < m} = s_{λ/μ}(β | α)`.
* `Shields.toeplitzMinor_pos_iff_uncond` -- the positivity criterion for the associated Toeplitz
  minor, with the identity discharged.

## Implementation notes

The offset `m - 1 - i` and the direction of the transpose are the two places an off-by-one is
invisible to a proof assistant, which would simply prove a different self-consistent statement.
Both are pinned by the non-vacuity instance at three rows carried at the end of this module, where
the transpose is what decides.

## Tags

Lindström-Gessel-Viennot, Jacobi-Trudi, skew Schur function, super Schur function, semistandard
tableau, Toeplitz minor
-/

namespace Shields

open Finset

/-! ## Where a column word puts its profile

Two bounds on `ePathOfWord`, one on each side, saying that the counting set of a
strictly increasing word is an initial segment.  `LGVOddTableau` proves them
inline for its two columns; both directions of the separation consume them.
-/

section Word

variable {a : ℕ}

/-- A letter below `i` puts its abscissa behind the profile at height `i`. -/
theorem lt_ePathOfWord {s len : ℕ} (T : BoundedSSYT (rect len 1) a) {i j : ℕ}
    (hj : j < len) (h : T j 0 < i) : s + j < ePathOfWord a s len T i := by
  have hsub : Finset.range (j + 1) ⊆ (Finset.range len).filter fun j' => T j' 0 < i := by
    intro j' hj'
    rw [Finset.mem_range] at hj'
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      lt_of_le_of_lt (boundedSSYT_col_mono T (by omega : j' ≤ j) hj) h⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  have hval : ePathOfWord a s len T i
      = s + ((Finset.range len).filter fun j' => T j' 0 < i).card := rfl
  omega

/-- A letter at or above `i` stops the profile at its abscissa. -/
theorem ePathOfWord_le {s len : ℕ} (T : BoundedSSYT (rect len 1) a) {i j : ℕ}
    (h : i ≤ T j 0) : ePathOfWord a s len T i ≤ s + j := by
  have hsub : ((Finset.range len).filter fun j' => T j' 0 < i) ⊆ Finset.range j := by
    intro j' hj'
    rw [Finset.mem_filter, Finset.mem_range] at hj'
    rw [Finset.mem_range]
    by_contra hcon
    exact absurd (boundedSSYT_col_mono T (by omega : j ≤ j') hj'.1) (by omega)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  have hval : ePathOfWord a s len T i
      = s + ((Finset.range len).filter fun j' => T j' 0 < i).card := rfl
  omega

end Word

/-! ## Point disjointness for a family

`EMeets` on every pair, exactly as `LGVInvolution.Intersects` is `Crosses` on
every pair.
-/

section Family

variable {m : ℕ}

/-- Two odd paths of the family share a point. -/
def EIntersects (a : ℕ) (G : Fin m → ℕ → ℕ) : Prop :=
  ∃ u v : Fin m, u < v ∧ EMeets a (G u) (G v)

instance (a : ℕ) (G : Fin m → ℕ → ℕ) : Decidable (EIntersects a G) := by
  unfold EIntersects; infer_instance

end Family

/-! ## Cells of a conjugate skew shape inside `m` rows

`LGVOddTableau` splits `λ' / ν'` into its two columns by case analysis on the
column index.  At `m` rows the same split is a `biUnion` over `range m`.
-/

section Cells

variable {lam nu : YoungDiagram} {m : ℕ}

/-- With no row of `λ` beyond the `m`-th, every cell of `λ' / ν'` is in a column
below `m`. -/
theorem lt_of_mem_skewCells_transpose (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) {i j : ℕ}
    (h : (j, i) ∈ skewCells lam.transpose nu.transpose) : i < m := by
  by_contra hc
  have h2 := (mem_skewCells_transpose.mp h).2
  rw [hrow i (by omega)] at h2
  omega

/-- The cells of `λ' / ν'` are the disjoint union of the column segments
`Ico ν_i λ_i`. -/
theorem skewCells_transpose_eq_biUnion (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    skewCells lam.transpose nu.transpose = (Finset.range m).biUnion fun i =>
      Finset.Ico (nu.rowLen i) (lam.rowLen i) ×ˢ ({i} : Finset ℕ) := by
  ext c
  obtain ⟨j, i⟩ := c
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_Ico]
  constructor
  · intro hc
    obtain ⟨h1, h2⟩ := mem_skewCells_transpose.mp hc
    exact ⟨i, lt_of_mem_skewCells_transpose hrow hc, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨i', -, ⟨h1, h2⟩, hi⟩
    subst hi
    exact mem_skewCells_transpose.mpr ⟨h1, h2⟩

/-- A product over the cells of `λ' / ν'` splits into its columns.  This is
`prod_skewCells_transpose_two_cols` at every `m`. -/
theorem prod_skewCells_transpose_cols {M : Type*} [CommMonoid M]
    (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) (f : ℕ → ℕ → M) :
    ∏ c ∈ skewCells lam.transpose nu.transpose, f c.1 c.2
      = ∏ i ∈ Finset.range m, ∏ j ∈ Finset.Ico (nu.rowLen i) (lam.rowLen i), f j i := by
  rw [skewCells_transpose_eq_biUnion hrow, Finset.prod_biUnion]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_product']
    simp only [Finset.prod_singleton]
  · intro i₁ _ i₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc₁ hc₂
    rw [Finset.mem_product, Finset.mem_singleton] at hc₁ hc₂
    exact hne (hc₁.2.symm.trans hc₂.2)

end Cells

/-! ## The paths of a conjugate tableau at `m` columns

Column `i` runs through `Shields.ePathOfWord` from the source `jtSource`
names, `ν_i + (m-1-i)`.  The family is indexed by source, matching
`LGVMixed`.
-/

section Rows

variable {a : ℕ} {lam nu : YoungDiagram} {m : ℕ}

/-- The odd path column `i` of `λ' / ν'` traces. -/
noncomputable def eRowPath (a m : ℕ) (lam nu : YoungDiagram)
    (T : BoundedSkewSSYT lam.transpose nu.transpose a) (i : ℕ) : ℕ → ℕ :=
  ePathOfWord a (rowSource nu m i) (lam.rowLen i - nu.rowLen i) (eColWord a lam nu T i)

theorem eRowPath_mem (hnu : nu ≤ lam) (T : BoundedSkewSSYT lam.transpose nu.transpose a)
    (i : ℕ) :
    eRowPath a m lam nu T i ∈ ePaths a (rowSource nu m i) (lam.rowLen i + (m - 1 - i)) := by
  have h := rowLen_mono hnu i
  have hmem := ePathOfWord_mem a (rowSource nu m i) (lam.rowLen i - nu.rowLen i)
    (eColWord a lam nu T i)
  rwa [show rowSource nu m i + (lam.rowLen i - nu.rowLen i) = lam.rowLen i + (m - 1 - i) by
    rw [rowSource]; omega] at hmem

/-- **The weak row condition is separation, at consecutive columns.**  Column
`i+1` sits strictly left of column `i` at every height.  The offsets of the two
columns differ by exactly one, which is what makes the weak inequality of the
tableau buy a full step. -/
theorem lt_eRowPath_succ (hnu : nu ≤ lam) (T : BoundedSkewSSYT lam.transpose nu.transpose a)
    {k u : ℕ} (hu : u + 1 < m) :
    eRowPath a m lam nu T (u + 1) k < eRowPath a m lam nu T u k := by
  have hnurow : nu.rowLen (u + 1) ≤ nu.rowLen u := nu.rowLen_anti u (u + 1) (by omega)
  have hlamrow : lam.rowLen (u + 1) ≤ lam.rowLen u := lam.rowLen_anti u (u + 1) (by omega)
  have h0 : nu.rowLen u ≤ lam.rowLen u := rowLen_mono hnu u
  have h1 : nu.rowLen (u + 1) ≤ lam.rowLen (u + 1) := rowLen_mono hnu (u + 1)
  have hoff : m - 1 - u = (m - 1 - (u + 1)) + 1 := by omega
  have hq := hPaths_le (ePaths_mem (eRowPath_mem (m := m) hnu T u)) k
  have hr := hPaths_le (ePaths_mem (eRowPath_mem (m := m) hnu T (u + 1))) k
  rw [rowSource] at hq hr
  by_contra hcon
  rw [Nat.not_lt] at hcon
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, eRowPath a m lam nu T u k = j₀ + (m - 1 - u) :=
    ⟨eRowPath a m lam nu T u k - (m - 1 - u), by omega⟩
  have hj₀nu : nu.rowLen u ≤ j₀ := by omega
  have hj₀lam : j₀ < lam.rowLen (u + 1) := by omega
  have ha : k ≤ T.1 j₀ u := by
    by_contra hlt
    rw [Nat.not_le] at hlt
    have hjj : j₀ - nu.rowLen u < lam.rowLen u - nu.rowLen u := by omega
    have hstep : rowSource nu m u + (j₀ - nu.rowLen u) < eRowPath a m lam nu T u k :=
      lt_ePathOfWord (s := rowSource nu m u) (i := k) (eColWord a lam nu T u) hjj (by
        rw [eColWord_apply T u hjj, show nu.rowLen u + (j₀ - nu.rowLen u) = j₀ by omega]
        exact hlt)
    simp only [rowSource] at hstep
    omega
  have hb : T.1 j₀ (u + 1) < k := by
    by_contra hgt
    rw [Nat.not_lt] at hgt
    have hjj : j₀ - nu.rowLen (u + 1) < lam.rowLen (u + 1) - nu.rowLen (u + 1) := by omega
    have hstep : eRowPath a m lam nu T (u + 1) k
        ≤ rowSource nu m (u + 1) + (j₀ - nu.rowLen (u + 1)) :=
      ePathOfWord_le (s := rowSource nu m (u + 1)) (i := k)
        (j := j₀ - nu.rowLen (u + 1)) (eColWord a lam nu T (u + 1)) (by
          rw [eColWord_apply T (u + 1) hjj,
            show nu.rowLen (u + 1) + (j₀ - nu.rowLen (u + 1)) = j₀ by omega]
          exact hgt)
    simp only [rowSource] at hstep
    omega
  have hrw : T.1 j₀ u ≤ T.1 j₀ (u + 1) :=
    T.1.row_weak (by omega) (mem_transpose_iff_lt_rowLen.mpr hj₀lam)
      fun hc => absurd (mem_transpose_iff_lt_rowLen.mp hc) (by omega)
  omega

/-- **The weak row condition is separation.**  Chaining the consecutive case:
for `u < v` the path of column `v` sits strictly left of the path of column
`u`. -/
theorem lt_eRowPath (hnu : nu ≤ lam) (T : BoundedSkewSSYT lam.transpose nu.transpose a)
    (k : ℕ) : ∀ v u : ℕ, u < v → v < m → eRowPath a m lam nu T v k < eRowPath a m lam nu T u k := by
  intro v
  induction v with
  | zero => intro u hu; omega
  | succ v ih =>
    intro u huv hv
    rcases Nat.lt_or_ge u v with hlt | hge
    · exact lt_trans (lt_eRowPath_succ (m := m) hnu T hv) (ih u hlt (by omega))
    · obtain rfl : u = v := by omega
      exact lt_eRowPath_succ (m := m) hnu T hv

/-- The family of odd paths a bounded tableau of `λ' / ν'` traces, indexed by
source. -/
noncomputable def eFamOfSkew (a m : ℕ) (lam nu : YoungDiagram)
    (T : BoundedSkewSSYT lam.transpose nu.transpose a) : Fin m → ℕ → ℕ :=
  fun w => eRowPath a m lam nu T (w : ℕ)

theorem eFamOfSkew_mem (hnu : nu ≤ lam) (T : BoundedSkewSSYT lam.transpose nu.transpose a)
    (w : Fin m) :
    eFamOfSkew a m lam nu T w ∈ ePaths a (jtSource nu m w) (jtSink lam m w) :=
  eRowPath_mem hnu T (w : ℕ)

/-- The family of a bounded tableau of `λ' / ν'` shares no point. -/
theorem not_eIntersects_eFamOfSkew (hnu : nu ≤ lam)
    (T : BoundedSkewSSYT lam.transpose nu.transpose a) :
    ¬ EIntersects a (eFamOfSkew a m lam nu T) := by
  rintro ⟨u, v, huv, k, hk⟩
  obtain ⟨-, hk1⟩ := mem_eMeetSet.mp hk
  have hlt := lt_eRowPath (m := m) hnu T k (v : ℕ) (u : ℕ) (Fin.lt_def.mp huv) v.isLt
  have h1 : eFamOfSkew a m lam nu T u k = eRowPath a m lam nu T (u : ℕ) k := rfl
  have h2 : eFamOfSkew a m lam nu T v k = eRowPath a m lam nu T (v : ℕ) k := rfl
  omega

end Rows

/-! ## The tableau of a non-meeting family

The cell `(j, i)` reads the letter column `i`'s path writes at abscissa
`j + (m-1-i)`.  Columns increase strictly because the letters of an odd path do;
rows increase weakly because the family shares no point — and there the offsets
enter, since columns `i₁ < i₂` are separated by `i₂ - i₁`, exactly the
difference of their offsets.
-/

section Reading

variable {a : ℕ} {lam nu : YoungDiagram} {m : ℕ}

/-- A path of the family read at a natural index below `m`, with its
endpoints. -/
theorem eFamPath_mem {G : Fin m → ℕ → ℕ}
    (hG : ∀ w : Fin m, G w ∈ ePaths a (jtSource nu m w) (jtSink lam m w)) {i : ℕ} (hi : i < m) :
    famPath G i ∈ ePaths a (rowSource nu m i) (lam.rowLen i + (m - 1 - i)) := by
  rw [famPath, dif_pos hi]
  exact hG ⟨i, hi⟩

/-- **Point disjointness separates two columns by their offset gap.**  A family
sharing no point has its paths strictly ordered, so columns `i₁ < i₂` are
separated by `i₂ - i₁`. -/
theorem le_famPath_of_not_eIntersects {G : Fin m → ℕ → ℕ}
    (hG : ∀ w : Fin m, G w ∈ ePaths a (jtSource nu m w) (jtSink lam m w))
    (hnI : ¬ EIntersects a G) {k : ℕ} (hk : k ≤ a) :
    ∀ v u : ℕ, u < v → v < m → famPath G v k + (v - u) ≤ famPath G u k := by
  have hstep : ∀ u : ℕ, u + 1 < m → famPath G (u + 1) k < famPath G u k := by
    intro u hu
    have hq := hG ⟨u, by omega⟩
    have hr := hG ⟨u + 1, hu⟩
    have hs : jtSource nu m ⟨u + 1, hu⟩ < jtSource nu m ⟨u, by omega⟩ :=
      strictAnti_jtSource nu m (Fin.mk_lt_mk.mpr (by omega))
    have hnm : ¬ EMeets a (G ⟨u, by omega⟩) (G ⟨u + 1, hu⟩) := fun hc =>
      hnI ⟨⟨u, by omega⟩, ⟨u + 1, hu⟩, Fin.mk_lt_mk.mpr (by omega), hc⟩
    have hlt := lt_of_not_eMeets hq hr hs hnm k hk
    have e1 : famPath G u = G ⟨u, by omega⟩ := by rw [famPath, dif_pos (show u < m by omega)]
    have e2 : famPath G (u + 1) = G ⟨u + 1, hu⟩ := by rw [famPath, dif_pos hu]
    rw [e1, e2]
    exact hlt
  intro v
  induction v with
  | zero => intro u hu; omega
  | succ v ih =>
    intro u huv hv
    rcases Nat.lt_or_ge u v with hlt | hge
    · have h1 := hstep v hv
      have h2 := ih u hlt (by omega)
      omega
    · have hvu : v = u := by omega
      subst hvu
      have := hstep v hv
      omega

/-- The filling of `λ' / ν'` read off a family of odd paths. -/
noncomputable def eSkewEntryM (a m : ℕ) (lam nu : YoungDiagram) (G : Fin m → ℕ → ℕ)
    (j i : ℕ) : ℕ :=
  if (j, i) ∈ skewCells lam.transpose nu.transpose then
    pathLetter a (rowSource nu m i) (famPath G i) (j - nu.rowLen i)
  else 0

theorem eSkewEntryM_of_mem {G : Fin m → ℕ → ℕ} {i j : ℕ}
    (h : (j, i) ∈ skewCells lam.transpose nu.transpose) :
    eSkewEntryM a m lam nu G j i
      = pathLetter a (rowSource nu m i) (famPath G i) (j - nu.rowLen i) :=
  if_pos h

theorem eSkewEntryM_of_notMem {G : Fin m → ℕ → ℕ} {i j : ℕ}
    (h : (j, i) ∉ skewCells lam.transpose nu.transpose) : eSkewEntryM a m lam nu G j i = 0 :=
  if_neg h

/-- **The row of the reading increases weakly.**  The letter column `i₁` writes
at abscissa `j + (m-1-i₁)` is at most the one column `i₂` writes at
`j + (m-1-i₂)`, because the two paths are separated by `i₂ - i₁`, which is
exactly the difference of the two offsets. -/
theorem eSkewEntryM_row_weak (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) {G : Fin m → ℕ → ℕ}
    (hG : ∀ w : Fin m, G w ∈ ePaths a (jtSource nu m w) (jtSink lam m w))
    (hnI : ¬ EIntersects a G) {i₁ i₂ j : ℕ} (hi : i₁ < i₂)
    (hc₁ : (j, i₁) ∈ skewCells lam.transpose nu.transpose)
    (hc₂ : (j, i₂) ∈ skewCells lam.transpose nu.transpose) :
    eSkewEntryM a m lam nu G j i₁ ≤ eSkewEntryM a m lam nu G j i₂ := by
  have hi₂ : i₂ < m := lt_of_mem_skewCells_transpose hrow hc₂
  have hi₁ : i₁ < m := by omega
  obtain ⟨hj₁, hj₁'⟩ := mem_skewCells_transpose.mp hc₁
  obtain ⟨hj₂, hj₂'⟩ := mem_skewCells_transpose.mp hc₂
  have hq₁ := eFamPath_mem hG hi₁
  have hq₂ := eFamPath_mem hG hi₂
  rw [eSkewEntryM_of_mem hc₁, eSkewEntryM_of_mem hc₂]
  set A := pathLetter a (rowSource nu m i₂) (famPath G i₂) (j - nu.rowLen i₂) with hA
  have hAa : A < a := by
    refine pathLetter_lt_height (ePaths_mem hq₂) ?_
    rw [rowSource]
    omega
  have hjr : j + (m - 1 - i₂) < famPath G i₂ (A + 1) := by
    have h := (pathLetter_lt_iff (ePaths_mem hq₂) (show A + 1 ≤ a by omega)).mp
      (Nat.lt_succ_self _)
    rw [rowSource] at h
    omega
  have hgap := le_famPath_of_not_eIntersects hG hnI (show A + 1 ≤ a by omega) i₂ i₁ hi hi₂
  have hoff : (m - 1 - i₂) + (i₂ - i₁) = m - 1 - i₁ := by omega
  refine Nat.lt_succ_iff.mp ((pathLetter_lt_iff (ePaths_mem hq₁) (show A + 1 ≤ a by omega)).mpr ?_)
  rw [rowSource]
  omega

/-- **The column of the reading increases strictly.**  This is the unit step of
the odd model: `pathLetter_strictMono`. -/
theorem eSkewEntryM_col_strict (hnu : nu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0)
    {G : Fin m → ℕ → ℕ}
    (hG : ∀ w : Fin m, G w ∈ ePaths a (jtSource nu m w) (jtSink lam m w))
    {i j₁ j₂ : ℕ} (hj : j₁ < j₂) (hc₁ : (j₁, i) ∈ skewCells lam.transpose nu.transpose)
    (hc₂ : (j₂, i) ∈ skewCells lam.transpose nu.transpose) :
    eSkewEntryM a m lam nu G j₁ i < eSkewEntryM a m lam nu G j₂ i := by
  have hi : i < m := lt_of_mem_skewCells_transpose hrow hc₂
  have hlen : nu.rowLen i ≤ lam.rowLen i := rowLen_mono hnu i
  obtain ⟨hj₁, hj₁'⟩ := mem_skewCells_transpose.mp hc₁
  obtain ⟨hj₂, hj₂'⟩ := mem_skewCells_transpose.mp hc₂
  have hmem : famPath G i ∈ ePaths a (rowSource nu m i)
      (rowSource nu m i + (lam.rowLen i - nu.rowLen i)) := by
    have hx := eFamPath_mem hG hi
    rwa [show rowSource nu m i + (lam.rowLen i - nu.rowLen i) = lam.rowLen i + (m - 1 - i) by
      rw [rowSource]; omega]
  rw [eSkewEntryM_of_mem hc₁, eSkewEntryM_of_mem hc₂]
  exact pathLetter_strictMono hmem (by omega) (by omega)

/-- The bounded tableau of the conjugate shape that a non-meeting family of odd
paths carries. -/
noncomputable def eSkewOfFam (hnu : nu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0)
    {G : Fin m → ℕ → ℕ}
    (hG : ∀ w : Fin m, G w ∈ ePaths a (jtSource nu m w) (jtSink lam m w))
    (hnI : ¬ EIntersects a G) : BoundedSkewSSYT lam.transpose nu.transpose a :=
  ⟨{ entry := eSkewEntryM a m lam nu G
     row_weak' := by
       intro j i₁ i₂ hi hlam hnnu
       have hj₂ : j < lam.rowLen i₂ := mem_transpose_iff_lt_rowLen.mp hlam
       have hj₁ : nu.rowLen i₁ ≤ j := by
         by_contra hc
         exact hnnu (mem_transpose_iff_lt_rowLen.mpr (by omega))
       have hlamanti : lam.rowLen i₂ ≤ lam.rowLen i₁ := lam.rowLen_anti i₁ i₂ (by omega)
       have hnuanti : nu.rowLen i₂ ≤ nu.rowLen i₁ := nu.rowLen_anti i₁ i₂ (by omega)
       exact eSkewEntryM_row_weak hrow hG hnI hi
         (mem_skewCells_transpose.mpr ⟨hj₁, by omega⟩)
         (mem_skewCells_transpose.mpr ⟨by omega, hj₂⟩)
     col_strict' := by
       intro j₁ j₂ i hj hlam hnnu
       have hj₂' : j₂ < lam.rowLen i := mem_transpose_iff_lt_rowLen.mp hlam
       have hj₁ : nu.rowLen i ≤ j₁ := by
         by_contra hc
         exact hnnu (mem_transpose_iff_lt_rowLen.mpr (by omega))
       exact eSkewEntryM_col_strict hnu hrow hG hj
         (mem_skewCells_transpose.mpr ⟨hj₁, by omega⟩)
         (mem_skewCells_transpose.mpr ⟨by omega, hj₂'⟩)
     zeros' := fun hc => eSkewEntryM_of_notMem hc },
   by
     intro j i hcell
     have hi := lt_of_mem_skewCells_transpose hrow hcell
     obtain ⟨hj, hj'⟩ := mem_skewCells_transpose.mp hcell
     change eSkewEntryM a m lam nu G j i < a
     rw [eSkewEntryM_of_mem hcell]
     refine pathLetter_lt_height (ePaths_mem (eFamPath_mem hG hi)) ?_
     rw [rowSource]
     omega⟩

theorem eSkewOfFam_apply (hnu : nu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0)
    {G : Fin m → ℕ → ℕ}
    (hG : ∀ w : Fin m, G w ∈ ePaths a (jtSource nu m w) (jtSink lam m w))
    (hnI : ¬ EIntersects a G) (j i : ℕ) :
    (eSkewOfFam hnu hrow hG hnI).1 j i = eSkewEntryM a m lam nu G j i :=
  rfl

end Reading

/-! ## The two round trips -/

section RoundTrip

variable {a : ℕ} {lam nu : YoungDiagram} {m : ℕ}

/-- Family to tableau and back. -/
theorem eFamOfSkew_eSkewOfFam (hnu : nu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0)
    {G : Fin m → ℕ → ℕ}
    (hG : ∀ w : Fin m, G w ∈ ePaths a (jtSource nu m w) (jtSink lam m w))
    (hnI : ¬ EIntersects a G) : eFamOfSkew a m lam nu (eSkewOfFam hnu hrow hG hnI) = G := by
  funext w
  have hw : (w : ℕ) < m := w.isLt
  have hlen : nu.rowLen (w : ℕ) ≤ lam.rowLen (w : ℕ) := rowLen_mono hnu (w : ℕ)
  have hmem : famPath G (w : ℕ) ∈ ePaths a (rowSource nu m (w : ℕ))
      (rowSource nu m (w : ℕ) + (lam.rowLen (w : ℕ) - nu.rowLen (w : ℕ))) := by
    have hx := eFamPath_mem hG hw
    rwa [show rowSource nu m (w : ℕ) + (lam.rowLen (w : ℕ) - nu.rowLen (w : ℕ))
      = lam.rowLen (w : ℕ) + (m - 1 - (w : ℕ)) by rw [rowSource]; omega]
  change eRowPath a m lam nu (eSkewOfFam hnu hrow hG hnI) (w : ℕ) = G w
  rw [← famPath_val G w]
  refine ePathOfWord_eq_of_entry hmem _ fun j hj => ?_
  rw [eColWord_apply _ (w : ℕ) hj, eSkewOfFam_apply,
    eSkewEntryM_of_mem (mem_skewCells_transpose_col (w : ℕ) hj),
    show nu.rowLen (w : ℕ) + j - nu.rowLen (w : ℕ) = j by omega]

/-- Tableau to family and back. -/
theorem eSkewOfFam_eFamOfSkew (hnu : nu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0)
    (T : BoundedSkewSSYT lam.transpose nu.transpose a) {hG hnI} :
    eSkewOfFam (G := eFamOfSkew a m lam nu T) hnu hrow hG hnI = T := by
  refine BoundedSkewSSYT.ext fun j i => ?_
  change eSkewEntryM a m lam nu (eFamOfSkew a m lam nu T) j i = T.1 j i
  by_cases hcell : (j, i) ∈ skewCells lam.transpose nu.transpose
  · have hi := lt_of_mem_skewCells_transpose hrow hcell
    obtain ⟨hj, hj'⟩ := mem_skewCells_transpose.mp hcell
    have hlen : nu.rowLen i ≤ lam.rowLen i := rowLen_mono hnu i
    have hfp : famPath (eFamOfSkew a m lam nu T) i = eRowPath a m lam nu T i := by
      rw [famPath, dif_pos hi]
      rfl
    rw [eSkewEntryM_of_mem hcell, hfp, eRowPath,
      pathLetter_ePathOfWord _ (show j - nu.rowLen i < lam.rowLen i - nu.rowLen i by omega),
      eColWord_apply T i (by omega), show nu.rowLen i + (j - nu.rowLen i) = j by omega]
  · rw [eSkewEntryM_of_notMem hcell]
    exact (T.zeros hcell).symm

end RoundTrip

/-! ## Weights, and the odd identity at `m` columns -/

section OddIdentity

variable {R : Type*} [CommRing R] {a : ℕ} {lam nu : YoungDiagram} {m : ℕ}

/-- The weight of a non-meeting family of odd paths is the weight of the tableau
of the conjugate shape it carries. -/
theorem prod_pathWeight_eq_prod_skewCells_transpose (hnu : nu ≤ lam)
    (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) (α : ℕ → R) {G : Fin m → ℕ → ℕ}
    (hG : ∀ w : Fin m, G w ∈ ePaths a (jtSource nu m w) (jtSink lam m w)) :
    ∏ w, pathWeight a α (G w)
      = ∏ c ∈ skewCells lam.transpose nu.transpose, α (eSkewEntryM a m lam nu G c.1 c.2) := by
  have hL : ∏ w : Fin m, pathWeight a α (G w)
      = ∏ i ∈ Finset.range m, pathWeight a α (famPath G i) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => pathWeight a α (famPath G i)) m]
    exact Finset.prod_congr rfl fun w _ => by rw [famPath_val]
  rw [hL, prod_skewCells_transpose_cols hrow fun j i => α (eSkewEntryM a m lam nu G j i)]
  refine Finset.prod_congr rfl fun i hi => ?_
  have him := Finset.mem_range.mp hi
  have hlen : nu.rowLen i ≤ lam.rowLen i := rowLen_mono hnu i
  have hmem : famPath G i ∈ hPaths a (rowSource nu m i)
      (rowSource nu m i + (lam.rowLen i - nu.rowLen i)) := by
    have hx := ePaths_mem (eFamPath_mem hG him)
    rwa [show rowSource nu m i + (lam.rowLen i - nu.rowLen i) = lam.rowLen i + (m - 1 - i) by
      rw [rowSource]; omega]
  rw [pathWeight_eq_prod_letters hmem α, Finset.prod_Ico_eq_prod_range]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [eSkewEntryM_of_mem (mem_skewCells_transpose_col i (Finset.mem_range.mp hj)),
    show nu.rowLen i + j - nu.rowLen i = j by omega]

/-- **The odd tableau bijection at `m` columns.**  For `λ` inside `m` rows, the
families of `m` odd paths from the sources of `ν` to the sinks of `λ` that share
no point carry the total weight of the semistandard tableaux of the conjugate
skew shape `λ' / ν'`.

This is `LGVOddTableau.nonMeetingIsSkewSchurTranspose` at every `m`, and it holds
over any commutative ring with no hypothesis beyond the shape. -/
theorem sum_nonEIntersecting_eq_skewSchurTranspose (a m : ℕ) (α : ℕ → R)
    (lam nu : YoungDiagram) (hnu : nu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    ∑ G ∈ (Fintype.piFinset fun w : Fin m =>
          ePaths a (jtSource nu m w) (jtSink lam m w)).filter fun G => ¬ EIntersects a G,
        ∏ w, pathWeight a α (G w)
      = skewSchur lam.transpose nu.transpose a α := by
  rw [skewSchur]
  refine Finset.sum_bij'
    (fun G hG => eSkewOfFam (G := G) hnu hrow
      (fun w => Fintype.mem_piFinset.mp (Finset.mem_filter.mp hG).1 w)
      (Finset.mem_filter.mp hG).2)
    (fun T _ => eFamOfSkew a m lam nu T) (fun G _ => Finset.mem_univ _) (fun T _ => ?_)
    (fun G hG => ?_) (fun T _ => eSkewOfFam_eFamOfSkew hnu hrow T) (fun G hG => ?_)
  · exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (eFamOfSkew_mem hnu T),
      not_eIntersects_eFamOfSkew hnu T⟩
  · exact eFamOfSkew_eSkewOfFam hnu hrow _ _
  · exact prod_pathWeight_eq_prod_skewCells_transpose hnu hrow α
      (fun w => Fintype.mem_piFinset.mp (Finset.mem_filter.mp hG).1 w)

end OddIdentity

/-! ## The splice at height `b`, at `m` paths

`LGVOdd.sum_nonMeeting_mixed_split` separates a *pair* of mixed paths at height
`b`.  The same separation runs at `m` paths: the mixed predicate on a family is
the even predicate on the truncations or the odd predicate on the shifts, and the
weights factor the same way.
-/

section Split

variable {m : ℕ}

/-- **The mixed predicate on a family separates.**  A family shares a lattice
point exactly when its truncations cross below height `b` or its shifts meet
from height `b` on. -/
theorem mIntersects_iff (b a : ℕ) (F : Fin m → ℕ → ℕ) :
    MIntersects b a F ↔ Intersects b F ∨ EIntersects a fun w => shiftAt b (F w) := by
  constructor
  · rintro ⟨u, v, huv, h⟩
    rcases (mMeets_iff_mixedMeets b a _ _).mp h with hc | he
    · exact Or.inl ⟨u, v, huv, hc⟩
    · exact Or.inr ⟨u, v, huv, he⟩
  · rintro (⟨u, v, huv, h⟩ | ⟨u, v, huv, h⟩)
    · exact ⟨u, v, huv, (mMeets_iff_mixedMeets b a _ _).mpr (Or.inl h)⟩
    · exact ⟨u, v, huv, (mMeets_iff_mixedMeets b a _ _).mpr (Or.inr h)⟩

theorem intersects_truncAt (b : ℕ) (F : Fin m → ℕ → ℕ) :
    Intersects b (fun w => truncAt b (F w)) ↔ Intersects b F := by
  unfold Intersects Crosses
  simp only [crossSet_truncAt]

theorem intersects_glueAt (b : ℕ) (Y Z : Fin m → ℕ → ℕ) :
    Intersects b (fun w => glueAt b (Y w) (Z w)) ↔ Intersects b Y := by
  unfold Intersects Crosses
  simp only [crossSet_glueAt]

variable {R : Type*} [CommRing R]

/-- **The splice of a family.**  Both the weights and the non-intersection
condition separate at height `b`: a non-intersecting family of mixed paths
through the abscissae `c` is a non-crossing family of even paths below height `b`
together with a non-meeting family of odd paths above it, and the fiber sum is
the product of the two.

This is `LGVOdd.sum_nonMeeting_mixed_split` at every `m`. -/
theorem sum_nonIntersecting_mixed_split (b a : ℕ) (S C c : Fin m → ℕ) (β α : ℕ → R) :
    ∑ F ∈ (Fintype.piFinset fun w => mixedPaths b a (S w) (C w)).filter
            (fun F => (∀ w, F w b = c w) ∧ ¬ MIntersects b a F),
        ∏ w, mixedWeight b a β α (F w)
      = (∑ Y ∈ (Fintype.piFinset fun w => hPaths b (S w) (c w)).filter
            fun Y => ¬ Intersects b Y, ∏ w, pathWeight b β (Y w))
        * ∑ Z ∈ (Fintype.piFinset fun w => ePaths a (c w) (C w)).filter
            fun Z => ¬ EIntersects a Z, ∏ w, pathWeight a α (Z w) := by
  rw [sum_mul_sum_prod]
  refine Finset.sum_nbij'
    (fun F => ((fun w => truncAt b (F w)), fun w => shiftAt b (F w)))
    (fun x => fun w => glueAt b (x.1 w) (x.2 w))
    (fun F hF => ?_) (fun x hx => ?_) (fun F hF => ?_) (fun x hx => ?_) (fun F hF => ?_)
  · rw [Finset.mem_filter, Fintype.mem_piFinset] at hF
    obtain ⟨hmem, hc, hnI⟩ := hF
    rw [mIntersects_iff, not_or] at hnI
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun w => ?_, ?_⟩,
      Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun w => ?_, hnI.2⟩⟩
    · rw [← hc w]; exact truncAt_mem (hmem w)
    · rw [intersects_truncAt]; exact hnI.1
    · rw [← hc w]; exact shiftAt_mem (hmem w)
  · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Fintype.mem_piFinset,
      Fintype.mem_piFinset] at hx
    obtain ⟨⟨hY, hYc⟩, hZ, hZm⟩ := hx
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun w => glueAt_mem (hY w) (hZ w),
      fun w => ?_, ?_⟩
    · change glueAt b (x.1 w) (x.2 w) b = c w
      rw [glueAt_of_le _ _ le_rfl]
      exact hPaths_top (hY w) le_rfl
    · rw [mIntersects_iff, not_or, intersects_glueAt]
      refine ⟨hYc, ?_⟩
      have hshift : (fun w => shiftAt b (glueAt b (x.1 w) (x.2 w))) = x.2 :=
        funext fun w => shiftAt_glueAt (hY w) (hZ w)
      rw [hshift]
      exact hZm
  · exact funext fun w => glueAt_truncAt_shiftAt b (F w)
  · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Fintype.mem_piFinset,
      Fintype.mem_piFinset] at hx
    obtain ⟨⟨hY, -⟩, hZ, -⟩ := hx
    exact Prod.ext (funext fun w => truncAt_glueAt (hY w))
      (funext fun w => shiftAt_glueAt (hY w) (hZ w))
  · change ∏ w, mixedWeight b a β α (F w)
      = (∏ w, pathWeight b β (truncAt b (F w))) * ∏ w, pathWeight a α (shiftAt b (F w))
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => by rw [mixedWeight, pathWeight_truncAt]

end Split

/-! ## The dictionary: `m` abscissae are an intermediate shape

The intermediate shape `ν` of the super branching rule is the vector of abscissae
the family occupies at height `b`, once the Jacobi--Trudi offsets are subtracted.
`mRows` builds a diagram from prescribed row lengths, and `shapeOfAbscissae` is
the passage; `jtSource ν m` is its inverse.
-/

section Dictionary

/-- The Young diagram with rows `r 0, …, r (m-1)` and no others.  Weakly
decreasing `r` is what makes those row lengths come back out. -/
def mRows : ℕ → (ℕ → ℕ) → YoungDiagram
  | 0, _ => ⊥
  | (n + 1), r => mRows n r ⊔ rect (n + 1) (r n)

theorem mem_mRows {m : ℕ} {r : ℕ → ℕ} {i j : ℕ} :
    (i, j) ∈ mRows m r ↔ ∃ k, k < m ∧ i ≤ k ∧ j < r k := by
  induction m with
  | zero =>
    constructor
    · intro h; exact absurd h (YoungDiagram.notMem_bot _)
    · rintro ⟨k, hk, -, -⟩; omega
  | succ n ih =>
    change (i, j) ∈ mRows n r ⊔ rect (n + 1) (r n) ↔ _
    rw [YoungDiagram.mem_sup, ih, mem_rect]
    constructor
    · rintro (⟨k, h1, h2, h3⟩ | ⟨h1, h2⟩)
      · exact ⟨k, by omega, h2, h3⟩
      · exact ⟨n, by omega, by omega, h2⟩
    · rintro ⟨k, h1, h2, h3⟩
      rcases Nat.lt_or_ge k n with h | h
      · exact Or.inl ⟨k, h, h2, h3⟩
      · obtain rfl : k = n := by omega
        exact Or.inr ⟨by omega, h3⟩

theorem rowLen_mRows {m : ℕ} {r : ℕ → ℕ}
    (hanti : ∀ k₁ k₂, k₁ ≤ k₂ → k₂ < m → r k₂ ≤ r k₁) (i : ℕ) :
    (mRows m r).rowLen i = if i < m then r i else 0 := by
  have key : ∀ j : ℕ, (i, j) ∈ mRows m r ↔ j < if i < m then r i else 0 := by
    intro j
    rw [mem_mRows]
    split_ifs with hi
    · constructor
      · rintro ⟨k, h1, h2, h3⟩
        exact lt_of_lt_of_le h3 (hanti i k h2 h1)
      · intro h
        exact ⟨i, hi, le_rfl, h⟩
    · constructor
      · rintro ⟨k, h1, h2, -⟩
        omega
      · intro h
        omega
  have h1 := key ((mRows m r).rowLen i)
  have h2 := key (if i < m then r i else 0)
  rw [YoungDiagram.mem_iff_lt_rowLen] at h1 h2
  omega

/-- The row lengths a vector of abscissae names: the abscissa less the
Jacobi--Trudi offset. -/
def abscissaRowLen (m : ℕ) (c : Fin m → ℕ) (i : ℕ) : ℕ :=
  if h : i < m then c ⟨i, h⟩ - (m - 1 - i) else 0

/-- The intermediate shape a vector of abscissae names. -/
def shapeOfAbscissae (m : ℕ) (c : Fin m → ℕ) : YoungDiagram := mRows m (abscissaRowLen m c)

/-- The abscissae of a fiber that survives: strictly decreasing, which after the
offsets is exactly the partition condition. -/
def AbscissaDrop {m : ℕ} (c : Fin m → ℕ) : Prop := ∀ u v : Fin m, u < v → c v < c u

instance {m : ℕ} (c : Fin m → ℕ) : Decidable (AbscissaDrop c) := by
  unfold AbscissaDrop; infer_instance

/-- A strictly decreasing vector of naturals drops by at least the index gap. -/
theorem add_sub_le_of_abscissaDrop {m : ℕ} {c : Fin m → ℕ} (h : AbscissaDrop c) :
    ∀ (v u : ℕ) (hu : u ≤ v) (hv : v < m),
      c ⟨v, hv⟩ + (v - u) ≤ c ⟨u, lt_of_le_of_lt hu hv⟩ := by
  intro v
  induction v with
  | zero =>
    intro u hu hv
    obtain rfl : u = 0 := by omega
    omega
  | succ v ih =>
    intro u hu hv
    rcases Nat.lt_or_ge u (v + 1) with hlt | hge
    · have hstep : c ⟨v + 1, hv⟩ < c ⟨v, by omega⟩ :=
        h ⟨v, by omega⟩ ⟨v + 1, hv⟩ (Fin.mk_lt_mk.mpr (by omega))
      have := ih u (by omega) (show v < m by omega)
      omega
    · obtain rfl : u = v + 1 := by omega
      omega

theorem abscissaRowLen_anti {m : ℕ} {c : Fin m → ℕ} (h : AbscissaDrop c) :
    ∀ k₁ k₂, k₁ ≤ k₂ → k₂ < m → abscissaRowLen m c k₂ ≤ abscissaRowLen m c k₁ := by
  intro k₁ k₂ h12 h2
  have hgap := add_sub_le_of_abscissaDrop h k₂ k₁ h12 h2
  rw [abscissaRowLen, abscissaRowLen, dif_pos h2, dif_pos (show k₁ < m by omega)]
  omega

theorem rowLen_shapeOfAbscissae {m : ℕ} {c : Fin m → ℕ} (h : AbscissaDrop c) (i : ℕ) :
    (shapeOfAbscissae m c).rowLen i = abscissaRowLen m c i := by
  rw [shapeOfAbscissae, rowLen_mRows (abscissaRowLen_anti h)]
  split_ifs with hi
  · rfl
  · rw [abscissaRowLen, dif_neg hi]

/-- **The abscissae are the shape.**  `jtSource` of the shape a vector names is
the vector itself, provided every abscissa clears its own offset. -/
theorem jtSource_shapeOfAbscissae {m : ℕ} {c : Fin m → ℕ} (h : AbscissaDrop c)
    (hoff : ∀ w : Fin m, m - 1 - (w : ℕ) ≤ c w) (w : Fin m) :
    jtSource (shapeOfAbscissae m c) m w = c w := by
  have hw := w.isLt
  have hc := hoff w
  rw [jtSource, rowLen_shapeOfAbscissae h, abscissaRowLen, dif_pos hw]
  have : (⟨(w : ℕ), hw⟩ : Fin m) = w := rfl
  rw [this]
  omega

/-- **The shape is the abscissae.**  A shape inside `m` rows is recovered from
its own Jacobi--Trudi sources. -/
theorem shapeOfAbscissae_jtSource {m : ℕ} {nu : YoungDiagram}
    (hnu : ∀ i, m ≤ i → nu.rowLen i = 0) :
    shapeOfAbscissae m (jtSource nu m) = nu := by
  have hanti : ∀ k₁ k₂, k₁ ≤ k₂ → k₂ < m →
      abscissaRowLen m (jtSource nu m) k₂ ≤ abscissaRowLen m (jtSource nu m) k₁ := by
    intro k₁ k₂ h12 h2
    have h1 : k₁ < m := by omega
    have hle : nu.rowLen k₂ ≤ nu.rowLen k₁ := nu.rowLen_anti k₁ k₂ h12
    rw [abscissaRowLen, abscissaRowLen, dif_pos h2, dif_pos h1]
    change nu.rowLen k₂ + (m - 1 - k₂) - (m - 1 - k₂) ≤ nu.rowLen k₁ + (m - 1 - k₁) - (m - 1 - k₁)
    omega
  refine eq_of_rowLen fun i => ?_
  rw [shapeOfAbscissae, rowLen_mRows hanti]
  split_ifs with hi
  · rw [abscissaRowLen, dif_pos hi]
    change nu.rowLen i + (m - 1 - i) - (m - 1 - i) = nu.rowLen i
    omega
  · exact (hnu i (by omega)).symm

end Dictionary

/-! ## The residue at every `m`

The non-intersecting mixed families are fibered over their abscissae at height
`b`; each fiber factors into an even and an odd half; a fiber whose abscissae are
not strictly decreasing has an empty odd half; and the surviving fibers are the
intermediate shapes.
-/

section Residue

variable {R : Type*} [CommRing R]

/-- A family of odd paths whose sources are not strictly decreasing while its
sinks are either meets or is impossible: this is what empties the fibers of the
splice that no intermediate shape indexes. -/
theorem eFilter_eq_empty_of_not_drop {a m : ℕ} {c C : Fin m → ℕ} (hC : StrictAnti C)
    (h : ¬ AbscissaDrop c) :
    ((Fintype.piFinset fun w => ePaths a (c w) (C w)).filter
      fun Z => ¬ EIntersects a Z) = ∅ := by
  obtain ⟨u, v, huv, hle⟩ : ∃ u v : Fin m, u < v ∧ c u ≤ c v := by
    rw [AbscissaDrop, not_forall] at h
    obtain ⟨u, hu⟩ := h
    rw [not_forall] at hu
    obtain ⟨v, hv⟩ := hu
    rw [not_forall] at hv
    obtain ⟨huv, hlt⟩ := hv
    exact ⟨u, v, huv, by omega⟩
  refine Finset.eq_empty_of_forall_notMem fun Z hZ => ?_
  rw [Finset.mem_filter, Fintype.mem_piFinset] at hZ
  obtain ⟨hmem, hnI⟩ := hZ
  have hnm : ¬ EMeets a (Z u) (Z v) := fun hc => hnI ⟨u, v, huv, hc⟩
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact hnm ⟨0, mem_eMeetSet.mpr ⟨Nat.zero_le a, by
      rw [hPaths_zero (ePaths_mem (hmem u)), hPaths_zero (ePaths_mem (hmem v))]; exact heq⟩⟩
  · have hsym : ¬ EMeets a (Z v) (Z u) := fun hc => hnm (by rwa [EMeets, eMeetSet_comm])
    have hsep := lt_of_not_eMeets (hmem v) (hmem u) hlt hsym a le_rfl
    rw [hPaths_top (ePaths_mem (hmem u)) le_rfl, hPaths_top (ePaths_mem (hmem v)) le_rfl] at hsep
    exact absurd (hC huv) (by omega)

/-- **The residue at every `m`.**  The non-intersecting families of `m` mixed
paths from the sources of `μ` to the sinks of `λ` carry the branching sum of
the super branching rule.

This is `LGVMixed.NonIntersectingIsSuperSkewSchur`, proved there at `m ≤ 2` and
carried as a hypothesis beyond.  The three ingredients are the splice at `m`
paths, the odd tableau bijection at `m` columns, and the dictionary carrying the
abscissae at height `b` to the intermediate shapes; the even half is
`LGVTableauM.sum_nonIntersecting_eq_skewSchur`. -/
theorem nonIntersectingIsSuperSkewSchur (b a m : ℕ) (β α : ℕ → R) :
    NonIntersectingIsSuperSkewSchur b a m β α := by
  intro lam mu hmu hrow
  set T : Finset (Fin m → ℕ) :=
    Fintype.piFinset fun w => Finset.Icc (jtSource mu m w) (jtSink lam m w) with hT
  have hmaps : ∀ F ∈ (Fintype.piFinset fun w : Fin m =>
      mixedPaths b a (jtSource mu m w) (jtSink lam m w)).filter
        (fun F => ¬ MIntersects b a F), (fun w => F w b) ∈ T := by
    intro F hF
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hF
    refine Fintype.mem_piFinset.mpr fun w => Finset.mem_Icc.mpr ?_
    exact hPaths_le (mixedPaths_mem (hF.1 w)) b
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- every fiber factors into its even and its odd half
  have hfib : ∀ c ∈ T,
      ∑ F ∈ ((Fintype.piFinset fun w : Fin m =>
          mixedPaths b a (jtSource mu m w) (jtSink lam m w)).filter
            (fun F => ¬ MIntersects b a F)).filter (fun F => (fun w => F w b) = c),
          ∏ w, mixedWeight b a β α (F w)
        = (∑ Y ∈ (Fintype.piFinset fun w => hPaths b (jtSource mu m w) (c w)).filter
              fun Y => ¬ Intersects b Y, ∏ w, pathWeight b β (Y w))
          * ∑ Z ∈ (Fintype.piFinset fun w => ePaths a (c w) (jtSink lam m w)).filter
              fun Z => ¬ EIntersects a Z, ∏ w, pathWeight a α (Z w) := by
    intro c _
    rw [Finset.filter_filter,
      ← sum_nonIntersecting_mixed_split b a (jtSource mu m) (jtSink lam m) c β α]
    refine Finset.sum_congr (Finset.filter_congr fun F _ => ?_) fun _ _ => rfl
    rw [funext_iff]
    tauto
  rw [Finset.sum_congr rfl hfib]
  -- a fiber whose abscissae are not strictly decreasing has an empty odd half
  have hvanish : ∀ c ∈ T, c ∉ T.filter (fun c => AbscissaDrop c) →
      (∑ Y ∈ (Fintype.piFinset fun w => hPaths b (jtSource mu m w) (c w)).filter
          fun Y => ¬ Intersects b Y, ∏ w, pathWeight b β (Y w))
        * (∑ Z ∈ (Fintype.piFinset fun w => ePaths a (c w) (jtSink lam m w)).filter
            fun Z => ¬ EIntersects a Z, ∏ w, pathWeight a α (Z w)) = 0 := by
    intro c hc hnot
    rw [Finset.mem_filter] at hnot
    have hdrop : ¬ AbscissaDrop c := fun hd => hnot ⟨hc, hd⟩
    rw [eFilter_eq_empty_of_not_drop (strictAnti_jtSink lam m) hdrop, Finset.sum_empty, mul_zero]
  rw [← Finset.sum_subset (Finset.filter_subset _ T) hvanish,
    superSkewSchur_eq_branching _ _ _ _ _ _ hmu]
  -- the box condition, with the offsets written out
  have hbox' : ∀ c : Fin m → ℕ,
      (∀ w : Fin m, c w ∈ Finset.Icc (jtSource mu m w) (jtSink lam m w)) →
      ∀ (i : ℕ) (hi : i < m),
        mu.rowLen i + (m - 1 - i) ≤ c ⟨i, hi⟩ ∧ c ⟨i, hi⟩ ≤ lam.rowLen i + (m - 1 - i) :=
    fun c hc i hi => Finset.mem_Icc.mp (hc ⟨i, hi⟩)
  -- the surviving fibers are the intermediate shapes
  refine Finset.sum_nbij' (fun c => shapeOfAbscissae m c) (fun nu => jtSource nu m)
    (fun c hc => ?_) (fun nu hnu => ?_) (fun c hc => ?_) (fun nu hnu => ?_) (fun c hc => ?_)
  · -- the shape of a surviving fiber lies between `mu` and `lam`
    rw [Finset.mem_filter, hT, Fintype.mem_piFinset] at hc
    obtain ⟨hbox, hdrop⟩ := hc
    have hrl : ∀ i, (shapeOfAbscissae m c).rowLen i = abscissaRowLen m c i :=
      rowLen_shapeOfAbscissae hdrop
    refine mem_youngIcc.mpr ⟨le_iff_rowLen.mpr fun i => ?_, le_iff_rowLen.mpr fun i => ?_⟩ <;>
      rw [hrl i, abscissaRowLen]
    · by_cases hi : i < m
      · rw [dif_pos hi]
        have := hbox' c hbox i hi
        omega
      · rw [dif_neg hi]
        have : lam.rowLen i = 0 := hrow i (by omega)
        have := rowLen_mono hmu i
        omega
    · by_cases hi : i < m
      · rw [dif_pos hi]
        have := hbox' c hbox i hi
        omega
      · rw [dif_neg hi]
        omega
  · -- an intermediate shape names a surviving fiber
    obtain ⟨h1, h2⟩ := mem_youngIcc.mp hnu
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun w => Finset.mem_Icc.mpr ?_,
      fun u v huv => strictAnti_jtSource nu m huv⟩
    exact ⟨by rw [jtSource, jtSource]; have := rowLen_mono h1 (w : ℕ); omega,
      by rw [jtSource, jtSink]; have := rowLen_mono h2 (w : ℕ); omega⟩
  · -- fiber to shape and back
    rw [Finset.mem_filter, hT, Fintype.mem_piFinset] at hc
    obtain ⟨hbox, hdrop⟩ := hc
    refine funext fun w => jtSource_shapeOfAbscissae hdrop (fun w' => ?_) w
    have h1 : mu.rowLen (w' : ℕ) + (m - 1 - (w' : ℕ)) ≤ c w' :=
      (hbox' c hbox (w' : ℕ) w'.isLt).1
    omega
  · -- shape to fiber and back
    obtain ⟨-, h2⟩ := mem_youngIcc.mp hnu
    exact shapeOfAbscissae_jtSource fun i hi =>
      Nat.le_zero.mp (hrow i hi ▸ rowLen_mono h2 i)
  · -- the summand: the even half is `s_{ν/μ}(β)` and the odd half is `s_{λ'/ν'}(α)`
    rw [Finset.mem_filter, hT, Fintype.mem_piFinset] at hc
    obtain ⟨hbox, hdrop⟩ := hc
    have hoff : ∀ w : Fin m, m - 1 - (w : ℕ) ≤ c w := by
      intro w
      have h1 : mu.rowLen (w : ℕ) + (m - 1 - (w : ℕ)) ≤ c w := (hbox' c hbox (w : ℕ) w.isLt).1
      omega
    have hsrc : ∀ w : Fin m, jtSource (shapeOfAbscissae m c) m w = c w :=
      jtSource_shapeOfAbscissae hdrop hoff
    have hsink : ∀ w : Fin m, jtSink (shapeOfAbscissae m c) m w = c w := fun w => hsrc w
    have hrl : ∀ i, (shapeOfAbscissae m c).rowLen i = abscissaRowLen m c i :=
      rowLen_shapeOfAbscissae hdrop
    have hnurow : ∀ i, m ≤ i → (shapeOfAbscissae m c).rowLen i = 0 := by
      intro i hi
      rw [hrl i, abscissaRowLen, dif_neg (by omega)]
    have hmunu : mu ≤ shapeOfAbscissae m c := by
      refine le_iff_rowLen.mpr fun i => ?_
      rw [hrl i, abscissaRowLen]
      by_cases hi : i < m
      · rw [dif_pos hi]
        have := hbox' c hbox i hi
        omega
      · rw [dif_neg hi]
        have : lam.rowLen i = 0 := hrow i (by omega)
        have := rowLen_mono hmu i
        omega
    have hnulam : shapeOfAbscissae m c ≤ lam := by
      refine le_iff_rowLen.mpr fun i => ?_
      rw [hrl i, abscissaRowLen]
      by_cases hi : i < m
      · rw [dif_pos hi]
        have := hbox' c hbox i hi
        omega
      · rw [dif_neg hi]
        omega
    have heven := sum_nonIntersecting_eq_skewSchur b m β (shapeOfAbscissae m c) mu hmunu hnurow
    have hodd := sum_nonEIntersecting_eq_skewSchurTranspose a m α lam (shapeOfAbscissae m c)
      hnulam hrow
    simp only [hsink] at heven
    simp only [hsrc] at hodd
    rw [← heven, ← hodd]

/-- **the skew Jacobi--Trudi identity at every `m`, with the odd alphabet, unconditionally.**
For `λ` inside `m` rows,

`det [d_{λ_u - μ_v - u + v}]_{u,v < m} = s_{λ/μ}(β | α)`,

over any commutative ring, every `b`, `a`, `β`, `α` and every `μ ⊆ λ`.  The
cancellation is `LGVMixed.mixedJacobiTrudiDet_eq_sum_nonIntersecting` and the
tableau side is `nonIntersectingIsSuperSkewSchur`. -/
theorem skewJacobiTrudi (b a : ℕ) (β α : ℕ → R) :
    SkewJacobiTrudi (fun k => superHom b a k β α) b a β α :=
  skewJacobiTrudi_of_nonIntersecting fun m => nonIntersectingIsSuperSkewSchur b a m β α

/-- The determinant form, for a determinant of any prescribed alphabet whose
coefficients are those of `ρ_D`. -/
theorem jacobiTrudiDet_eq_superSkewSchur {b a : ℕ} {β α : ℕ → R} {d : ℕ → R}
    (hd : ∀ k, d k = superHom b a k β α) {lam mu : YoungDiagram} {m : ℕ} (hmu : mu ≤ lam)
    (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    jacobiTrudiDet d lam mu m = superSkewSchur lam mu b a β α := by
  rw [funext hd]
  exact skewJacobiTrudi b a β α lam mu m hmu hrow

/-- **the skew Jacobi--Trudi identity on the shapes of the Toeplitz application.**  The Toeplitz
minor `Δ_C` of the Toeplitz minor is the branching sum of the super branching rule, with
`SkewJacobiTrudi` supplied rather than assumed. -/
theorem toeplitzMinor_eq_superSkewSchur_uncond {b a : ℕ} {β α : ℕ → R} {d : ℕ → R}
    (hd : ∀ k, d k = superHom b a k β α) {n k L Lk : ℕ} (hL : Lk + k = L) (hkn : k ≤ n)
    (hnL : n ≤ Lk) {I : Finset ℕ} (hIn : I ⊆ Finset.range n) (hkI : ∀ x, x < k → x ∈ I) :
    toeplitzMinor d k I.card I (tailSet n k I)
      = superSkewSchur (betaDiagram I L) (betaDiagram (tailSet n k I) Lk) b a β α := by
  rw [funext hd]
  exact toeplitzMinor_eq_superSkewSchur (skewJacobiTrudi b a β α) hL hkn hnL hIn hkI

end Residue

/-! ## The endpoint order, unconditionally

`JacobiTrudi.endpoint_order_of_skewJacobiTrudi` runs at `b < a` and carried
`SkewJacobiTrudi` as a hypothesis.  It is now supplied.
-/

section Endpoint

/-- `SkewJacobiTrudi` for any alphabet whose coefficients are those of `ρ_D`. -/
theorem skewJacobiTrudi_of_eq {R : Type*} [CommRing R] {b a : ℕ} {β α d : ℕ → R}
    (hd : ∀ k, d k = superHom b a k β α) : SkewJacobiTrudi d b a β α := by
  rw [funext hd]
  exact skewJacobiTrudi b a β α

/-- **the skew-hook criterion and the block condition on the minor, with
nothing assumed.**  `Δ_C` is positive exactly when `I` satisfies the packing rule
the block condition. -/
theorem toeplitzMinor_pos_iff_uncond {b a : ℕ} {β α d : ℕ → ℝ}
    (hd : ∀ k, d k = superHom b a k β α) {n k L Lk : ℕ} (hL : Lk + k = L) (hkn : k ≤ n)
    (hnL : n ≤ Lk) (hba : b < a) (hka : k ≤ a) (hβ : ∀ i, i < b → 0 < β i)
    (hα : ∀ i, i < a → 0 < α i) {I : Finset ℕ} (hIn : I ⊆ Finset.range n)
    (hkI : ∀ x, x < k → x ∈ I) :
    0 < toeplitzMinor d k I.card I (tailSet n k I) ↔ BlockCondition n k a b I :=
  toeplitzMinor_pos_iff (skewJacobiTrudi_of_eq hd) hL hkn hnL hba hka hβ hα hIn hkI

end Endpoint

/-! ## Non-vacuity

The smallest instance at three rows where the transpose decides, evaluated.
-/

section Instance

variable {R : Type*} [CommRing R]

/-- **The transpose is pinned at three rows.**  With no even variables the mixed
model is the odd one, and on the column `λ = (1,1,1)` the `3 × 3` determinant
over the alphabet `ρ_D` is a *complete* homogeneous polynomial, `h_3(α)`.  An
untransposed correspondence would return `e_3` here, which is why the odd
bijection at `m` columns lands on `λ' / ν'` rather than on `λ / ν`.  This is
`LGVOddTableau.elemDet_two_column` one row further up. -/
theorem jacobiTrudiDet_three_column_odd (a : ℕ) (β α : ℕ → R) :
    jacobiTrudiDet (fun k => superHom 0 a k β α) (rect 3 1) ⊥ 3 = completeHom a 3 α := by
  have hbot : (⊥ : YoungDiagram).transpose = ⊥ := by
    ext c
    simp
  rw [skewJacobiTrudi 0 a β α (rect 3 1) ⊥ 3 bot_le (fun i hi => rowLen_rect_of_le (by omega)),
    superSkewSchur_zero_even β α bot_le, transpose_rect, hbot, completeHom]

end Instance

section AxiomGuards

end AxiomGuards

end Shields
