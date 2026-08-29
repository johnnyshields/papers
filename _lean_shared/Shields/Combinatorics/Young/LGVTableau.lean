/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.SkewCells
import Shields.Combinatorics.Young.LGVInvolution

/-!
# Lindström--Gessel--Viennot at every number of rows: families of paths and skew tableaux

`Shields.Combinatorics.Young.LGVInvolution` collapses the signed sum over families of
lattice paths onto the non-intersecting families.  This file supplies the other half of the
argument: a non-intersecting family of `m` paths *is* a bounded semistandard tableau of the
skew shape, and the two carry the same weight.

Both directions are explicit.  A tableau sends row `i` to the path that reads that row as a
word, offset by `m - 1 - i` so that the rows are separated; a family sends the cell `(i, j)`
to the letter row `i`'s path writes at abscissa `j + (m - 1 - i)`.  Rows increase weakly
because letters do, and columns increase strictly because consecutive paths never meet.  The
two constructions are mutually inverse, and the product over the skew cells splits into rows
that are exactly the path weights, so the skew Jacobi--Trudi identity over the even alphabet
follows at every commutative ring, every shape pair and every `m`.

## Main definitions

* `Shields.rowSource`, `Shields.rowPath`, `Shields.famOfSkew`: the family of paths a
  bounded skew tableau traces, indexed by source.
* `Shields.skewEntryM`, `Shields.skewOfFam`: the tableau a non-intersecting family reads.

## Main results

* `Shields.not_intersects_famOfSkew`: the family of a tableau is non-intersecting.
* `Shields.famOfSkew_skewOfFam` and `Shields.skewOfFam_famOfSkew`: the two round trips.
* `Shields.prod_pathWeight_eq_prod_skewCells`: the weight of a family is the weight of the
  tableau it carries.
* `Shields.sum_nonIntersecting_eq_skewSchur`: **the correspondence at `m` rows.**  The
  non-intersecting families from the sources of `μ` to the sinks of `λ` carry the total
  weight of the semistandard tableaux of `λ / μ`.
* `Shields.jacobiTrudiDet_eq_skewSchur` and `Shields.skewJacobiTrudi_even`: skew
  Jacobi--Trudi over the even alphabet, and the same statement as the predicate
  `Shields.SkewJacobiTrudi` at no odd variables.
* `Shields.toeplitzMinor_eq_superSkewSchur_even`: the Toeplitz-minor form of it.
* `Shields.jacobiTrudiDet_three_column`: the smallest instance that needs the selection of a
  crossing among three paths rather than two.

## Tags

Lindström--Gessel--Viennot, lattice path, semistandard tableau, skew Schur function,
Jacobi--Trudi
-/

namespace Shields

open Finset

/-! ## The paths of a tableau at `m` rows

Row `i` runs through `Shields.pathOfWord` from the source `jtSource` names,
`μ_i + (m-1-i)`.  The family is indexed by source, so `famOfSkew` is a
`Fin m`-indexed family with exactly the endpoints
`jacobiTrudiDet_eq_sum_nonIntersecting` sums over.
-/

section Rows

variable {b : ℕ} {lam mu : YoungDiagram} {m : ℕ}

/-- The source of row `i`, at a natural-number index: `jtSource` read off `ℕ`. -/
def rowSource (mu : YoungDiagram) (m i : ℕ) : ℕ := mu.rowLen i + (m - 1 - i)

theorem rowSource_val (mu : YoungDiagram) (m : ℕ) (u : Fin m) :
    rowSource mu m u = jtSource mu m u := rfl

/-- Advancing from the source of row `i` by the length of a segment of that row
lands at the abscissa the segment ends on, offset by `m - 1 - i`. -/
theorem rowSource_add_sub (mu : YoungDiagram) (m : ℕ) {i j : ℕ} (h : mu.rowLen i ≤ j) :
    rowSource mu m i + (j - mu.rowLen i) = j + (m - 1 - i) := by
  rw [rowSource]; omega

/-- The path row `i` of a bounded skew tableau traces. -/
noncomputable def rowPath (hmu : mu ≤ lam) (m : ℕ) (T : BoundedSkewSSYT lam mu b) (i : ℕ) :
    ℕ → ℕ :=
  pathOfWord b (rowSource mu m i) (lam.rowLen i - mu.rowLen i) (rowWord hmu T i)

theorem rowPath_mem (hmu : mu ≤ lam) (m : ℕ) (T : BoundedSkewSSYT lam mu b) (i : ℕ) :
    rowPath hmu m T i ∈ hPaths b (rowSource mu m i) (lam.rowLen i + (m - 1 - i)) := by
  have hmem := pathOfWord_mem b (rowSource mu m i) (lam.rowLen i - mu.rowLen i) (rowWord hmu T i)
  rwa [rowSource_add_sub mu m (rowLen_mono hmu i)] at hmem

/-- A letter of row `i` below `k` puts its abscissa behind that row's path at
height `k`. -/
theorem lt_rowPath_of_entry (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) {i j k : ℕ}
    (hj : mu.rowLen i ≤ j) (hj' : j < lam.rowLen i) (h : T.1 i j < k) :
    j + (m - 1 - i) < rowPath hmu m T i k := by
  have hjj : j - mu.rowLen i < lam.rowLen i - mu.rowLen i := by omega
  have hstep := lt_pathOfWord (s := rowSource mu m i) (rowWord hmu T i) hjj (by
    rw [rowWord_apply hmu T i hjj, show mu.rowLen i + (j - mu.rowLen i) = j by omega]
    exact h)
  rwa [rowSource_add_sub mu m hj] at hstep

/-- A letter of row `i` at or above `k` stops that row's path at its abscissa. -/
theorem rowPath_le_of_entry (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) {i j k : ℕ}
    (hj : mu.rowLen i ≤ j) (hj' : j < lam.rowLen i) (h : k ≤ T.1 i j) :
    rowPath hmu m T i k ≤ j + (m - 1 - i) := by
  have hjj : j - mu.rowLen i < lam.rowLen i - mu.rowLen i := by omega
  have hstep := pathOfWord_le (s := rowSource mu m i) (i := k) (rowWord hmu T i) (by
    rw [rowWord_apply hmu T i hjj, show mu.rowLen i + (j - mu.rowLen i) = j by omega]
    exact h)
  rwa [rowSource_add_sub mu m hj] at hstep

/-- The family of paths a bounded skew tableau traces, indexed by source. -/
noncomputable def famOfSkew (hmu : mu ≤ lam) (m : ℕ) (T : BoundedSkewSSYT lam mu b) :
    Fin m → ℕ → ℕ := fun u => rowPath hmu m T u

theorem famOfSkew_mem (hmu : mu ≤ lam) (m : ℕ) (T : BoundedSkewSSYT lam mu b) (u : Fin m) :
    famOfSkew hmu m T u ∈ hPaths b (jtSource mu m u) (jtSink lam m u) :=
  rowPath_mem hmu m T u

/-- **Column strictness is separation, at consecutive rows.**  Row `i+1` has left
height `k+1` before row `i` reaches height `k`.  The offsets of the two rows
differ by one, which is what makes the strict column inequality of the tableau
buy a full step between the paths.

No bound on `k` is needed: above `b` both profiles sit at their sinks, and those
are `jtSink`, which strictly decreases. -/
theorem lt_rowPath_succ (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) {k u : ℕ}
    (hu : u + 1 < m) :
    rowPath hmu m T (u + 1) (k + 1) < rowPath hmu m T u k := by
  have hmurow : mu.rowLen (u + 1) ≤ mu.rowLen u := mu.rowLen_anti u (u + 1) (by omega)
  have hlamrow : lam.rowLen (u + 1) ≤ lam.rowLen u := lam.rowLen_anti u (u + 1) (by omega)
  have hoff : m - 1 - u = (m - 1 - (u + 1)) + 1 := by omega
  have hq := hPaths_le (rowPath_mem hmu m T u) k
  have hr := hPaths_le (rowPath_mem hmu m T (u + 1)) (k + 1)
  rw [rowSource] at hq hr
  by_contra hcon
  rw [Nat.not_lt] at hcon
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, rowPath hmu m T u k = j₀ + (m - 1 - u) :=
    ⟨rowPath hmu m T u k - (m - 1 - u), by omega⟩
  have hj₀mu : mu.rowLen u ≤ j₀ := by omega
  have hj₀lam : j₀ < lam.rowLen (u + 1) := by omega
  have ha : k ≤ T.1 u j₀ := by
    by_contra hlt
    rw [Nat.not_le] at hlt
    have hx := lt_rowPath_of_entry (m := m) hmu T hj₀mu (by omega) hlt
    omega
  have hb : T.1 (u + 1) j₀ ≤ k := by
    by_contra hgt
    rw [Nat.not_le] at hgt
    have hx := rowPath_le_of_entry (m := m) hmu T (i := u + 1) (j := j₀) (k := k + 1)
      (by omega) hj₀lam (by omega)
    omega
  have hcol : T.1 u j₀ < T.1 (u + 1) j₀ :=
    T.1.col_strict (by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr hj₀lam)
      fun hc => absurd (YoungDiagram.mem_iff_lt_rowLen.mp hc) (by omega)
  omega

/-- **Column strictness is separation.**  Chaining the consecutive case: for
`u < v` the path of row `v` has left height `k+1` before the path of row `u`
reaches height `k`. -/
theorem lt_rowPath (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) (k : ℕ) :
    ∀ v u : ℕ, u < v → v < m → rowPath hmu m T v (k + 1) < rowPath hmu m T u k := by
  intro v
  induction v with
  | zero => intro u hu; omega
  | succ v ih =>
    intro u huv hv
    rcases Nat.lt_or_ge u v with hlt | hge
    · have h1 := lt_rowPath_succ (m := m) hmu T (u := v) (k := k) hv
      have h2 : rowPath hmu m T v k ≤ rowPath hmu m T v (k + 1) :=
        hPaths_mono (rowPath_mem hmu m T v) (by omega)
      have h3 := ih u hlt (by omega)
      omega
    · obtain rfl : u = v := by omega
      exact lt_rowPath_succ (m := m) hmu T hv

/-- The family of a bounded skew tableau shares no lattice point. -/
theorem not_intersects_famOfSkew (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) :
    ¬ Intersects b (famOfSkew hmu m T) := by
  rintro ⟨u, v, huv, k, hk⟩
  obtain ⟨-, hk1, -⟩ := mem_crossSet.mp hk
  have hlt := lt_rowPath hmu T k v u (Fin.lt_def.mp huv) v.isLt
  have h1 : famOfSkew hmu m T u k = rowPath hmu m T (u : ℕ) k := rfl
  have h2 : famOfSkew hmu m T v (k + 1) = rowPath hmu m T (v : ℕ) (k + 1) := rfl
  omega

end Rows

/-! ## The tableau of a non-intersecting family

The cell `(i, j)` reads the letter row `i`'s path writes at abscissa
`j + (m-1-i)`.  Rows increase weakly because letters do; columns increase
strictly because consecutive rows never meet, and a general pair of rows chains
through the rows between them.
-/

section Reading

variable {b : ℕ} {lam mu : YoungDiagram} {m : ℕ}

/-- The filling of `lam / mu` read off a family of paths. -/
noncomputable def skewEntryM (b m : ℕ) (lam mu : YoungDiagram) (F : Fin m → ℕ → ℕ)
    (i j : ℕ) : ℕ :=
  if (i, j) ∈ skewCells lam mu then
    pathLetter b (rowSource mu m i) (famPath F i) (j - mu.rowLen i)
  else 0

theorem skewEntryM_of_mem {F : Fin m → ℕ → ℕ} {i j : ℕ} (h : (i, j) ∈ skewCells lam mu) :
    skewEntryM b m lam mu F i j
      = pathLetter b (rowSource mu m i) (famPath F i) (j - mu.rowLen i) :=
  if_pos h

theorem skewEntryM_of_notMem {F : Fin m → ℕ → ℕ} {i j : ℕ}
    (h : (i, j) ∉ skewCells lam mu) : skewEntryM b m lam mu F i j = 0 :=
  if_neg h

/-- A path of the family read at a natural index below `m`, with its endpoints. -/
theorem famPath_mem {F : Fin m → ℕ → ℕ}
    (hF : ∀ w : Fin m, F w ∈ hPaths b (jtSource mu m w) (jtSink lam m w)) {i : ℕ} (hi : i < m) :
    famPath F i ∈ hPaths b (rowSource mu m i) (lam.rowLen i + (m - 1 - i)) := by
  rw [famPath_of_lt F hi]
  exact hF ⟨i, hi⟩

/-- **The column of the reading increases strictly at consecutive rows.**  The
letter row `i` writes at abscissa `j + (m-1-i)` is below the one row `i+1`
writes at `j + (m-1-i) - 1`, because the two paths are separated by a full
step. -/
theorem skewEntryM_col_step (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) {F : Fin m → ℕ → ℕ}
    (hF : ∀ w : Fin m, F w ∈ hPaths b (jtSource mu m w) (jtSink lam m w))
    (hnI : ¬ Intersects b F) {i j : ℕ} (hc₀ : (i, j) ∈ skewCells lam mu)
    (hc₁ : (i + 1, j) ∈ skewCells lam mu) :
    skewEntryM b m lam mu F i j < skewEntryM b m lam mu F (i + 1) j := by
  have hi1 : i + 1 < m := lt_of_mem_skewCells hrow hc₁
  have hi0 : i < m := by omega
  have hq := famPath_mem hF hi0
  have hr := famPath_mem hF hi1
  have hfp0 := famPath_of_lt F hi0
  have hfp1 := famPath_of_lt F hi1
  have hnc : ¬ Crosses b (famPath F i) (famPath F (i + 1)) := by
    rw [hfp0, hfp1]
    exact fun hcr => hnI ⟨⟨i, hi0⟩, ⟨i + 1, hi1⟩, Fin.mk_lt_mk.mpr (by omega), hcr⟩
  obtain ⟨hj0, hj0'⟩ := mem_skewCells_row_of_mem hc₀
  obtain ⟨hj1, hj1'⟩ := mem_skewCells_row_of_mem hc₁
  have hoff : m - 1 - i = (m - 1 - (i + 1)) + 1 := by omega
  rw [skewEntryM_of_mem hc₀, skewEntryM_of_mem hc₁]
  set A := pathLetter b (rowSource mu m (i + 1)) (famPath F (i + 1)) (j - mu.rowLen (i + 1))
    with hA
  have hAb : A < b := by
    refine pathLetter_lt_height hr ?_
    rw [rowSource]
    omega
  have hjr : j + (m - 1 - (i + 1)) < famPath F (i + 1) (A + 1) := by
    have h := (pathLetter_lt_iff hr (show A + 1 ≤ b by omega)).mp (Nat.lt_succ_self _)
    rw [rowSource] at h
    omega
  have hs : rowSource mu m (i + 1) < rowSource mu m i := by
    have hanti := mu.rowLen_anti i (i + 1) (by omega)
    rw [rowSource, rowSource]
    omega
  have hsep := lt_of_not_crosses hq hr hs hnc A hAb
  refine (pathLetter_lt_iff hq (show A ≤ b by omega)).mpr ?_
  rw [rowSource]
  omega

/-- **The column of the reading increases strictly.**  A general pair of rows
chains through the rows between them: every cell of the column between the two
is itself a skew cell. -/
theorem skewEntryM_col_strict (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) {F : Fin m → ℕ → ℕ}
    (hF : ∀ w : Fin m, F w ∈ hPaths b (jtSource mu m w) (jtSink lam m w))
    (hnI : ¬ Intersects b F) {i₁ i₂ j : ℕ} (hi : i₁ < i₂) (hlam : (i₂, j) ∈ lam)
    (hnmu : (i₁, j) ∉ mu) :
    skewEntryM b m lam mu F i₁ j < skewEntryM b m lam mu F i₂ j := by
  revert hlam
  induction i₂, hi using Nat.le_induction with
  | base =>
    intro hlam
    exact skewEntryM_col_step hrow hF hnI
      (mem_skewCells.mpr ⟨lam.up_left_mem (by omega) le_rfl hlam, hnmu⟩)
      (mem_skewCells.mpr ⟨hlam, notMem_of_row_le (by omega) hnmu⟩)
  | succ i₂ h ih =>
    intro hlam
    have hlam' : (i₂, j) ∈ lam := lam.up_left_mem (by omega) le_rfl hlam
    refine lt_trans (ih hlam') (skewEntryM_col_step hrow hF hnI ?_ ?_)
    · exact mem_skewCells.mpr ⟨hlam', notMem_of_row_le (by omega) hnmu⟩
    · exact mem_skewCells.mpr ⟨hlam, notMem_of_row_le (by omega) hnmu⟩

/-- The bounded skew tableau a non-intersecting family carries. -/
noncomputable def skewOfFam (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) {F : Fin m → ℕ → ℕ}
    (hF : ∀ w : Fin m, F w ∈ hPaths b (jtSource mu m w) (jtSink lam m w))
    (hnI : ¬ Intersects b F) : BoundedSkewSSYT lam mu b :=
  ⟨{ entry := skewEntryM b m lam mu F
     row_weak' := by
       intro i j₁ j₂ hj hlam hnmu
       have hc₁ : (i, j₁) ∈ skewCells lam mu :=
         mem_skewCells.mpr ⟨lam.up_left_mem le_rfl hj.le hlam, hnmu⟩
       have hc₂ : (i, j₂) ∈ skewCells lam mu :=
         mem_skewCells.mpr ⟨hlam, notMem_of_col_le hj.le hnmu⟩
       rw [skewEntryM_of_mem hc₁, skewEntryM_of_mem hc₂]
       exact pathLetter_mono _ _ _ (by omega)
     col_strict' := fun hi hlam hnmu => skewEntryM_col_strict hrow hF hnI hi hlam hnmu
     zeros' := fun hc => skewEntryM_of_notMem hc },
   by
     intro i j hcell
     have hi := lt_of_mem_skewCells hrow hcell
     obtain ⟨hj, hj'⟩ := mem_skewCells_row_of_mem hcell
     change skewEntryM b m lam mu F i j < b
     rw [skewEntryM_of_mem hcell]
     refine pathLetter_lt_height (famPath_mem hF hi) ?_
     rw [rowSource]
     omega⟩

theorem skewOfFam_apply (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) {F : Fin m → ℕ → ℕ}
    (hF : ∀ w : Fin m, F w ∈ hPaths b (jtSource mu m w) (jtSink lam m w))
    (hnI : ¬ Intersects b F) (i j : ℕ) :
    (skewOfFam hrow hF hnI).1 i j = skewEntryM b m lam mu F i j :=
  rfl

end Reading

/-! ## The two round trips -/

section RoundTrip

variable {b : ℕ} {lam mu : YoungDiagram} {m : ℕ}

/-- Family to tableau and back. -/
theorem famOfSkew_skewOfFam (hmu : mu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0)
    {F : Fin m → ℕ → ℕ}
    (hF : ∀ w : Fin m, F w ∈ hPaths b (jtSource mu m w) (jtSink lam m w))
    (hnI : ¬ Intersects b F) : famOfSkew hmu m (skewOfFam hrow hF hnI) = F := by
  funext u
  have hu : (u : ℕ) < m := u.isLt
  have hlen : mu.rowLen (u : ℕ) ≤ lam.rowLen (u : ℕ) := rowLen_mono hmu u
  have hmem : famPath F (u : ℕ) ∈ hPaths b (rowSource mu m (u : ℕ))
      (rowSource mu m (u : ℕ) + (lam.rowLen (u : ℕ) - mu.rowLen (u : ℕ))) := by
    have hx := famPath_mem hF hu
    rwa [rowSource_add_sub mu m hlen]
  change rowPath hmu m (skewOfFam hrow hF hnI) (u : ℕ) = F u
  rw [← famPath_val F u]
  refine pathOfWord_eq_of_entry hmem _ fun j hj => ?_
  rw [rowWord_apply hmu _ (u : ℕ) hj, skewOfFam_apply,
    skewEntryM_of_mem (mem_skewCells_row hmu (u : ℕ) hj),
    show mu.rowLen (u : ℕ) + j - mu.rowLen (u : ℕ) = j by omega]

/-- Tableau to family and back. -/
theorem skewOfFam_famOfSkew (hmu : mu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0)
    (T : BoundedSkewSSYT lam mu b) {hF hnI} :
    skewOfFam (F := famOfSkew hmu m T) hrow hF hnI = T := by
  refine BoundedSkewSSYT.ext fun i j => ?_
  change skewEntryM b m lam mu (famOfSkew hmu m T) i j = T.1 i j
  by_cases hcell : (i, j) ∈ skewCells lam mu
  · have hi := lt_of_mem_skewCells hrow hcell
    obtain ⟨hj, hj'⟩ := mem_skewCells_row_of_mem hcell
    have hlen : mu.rowLen i ≤ lam.rowLen i := rowLen_mono hmu i
    have hfp : famPath (famOfSkew hmu m T) i = rowPath hmu m T i :=
      famPath_of_lt _ hi
    rw [skewEntryM_of_mem hcell, hfp, rowPath,
      pathLetter_pathOfWord _ (show j - mu.rowLen i < lam.rowLen i - mu.rowLen i by omega),
      rowWord_apply hmu T i (by omega), show mu.rowLen i + (j - mu.rowLen i) = j by omega]
  · rw [skewEntryM_of_notMem hcell]
    exact (T.zeros hcell).symm

end RoundTrip

/-! ## Weights

The product over the skew cells splits into its `m` rows, and each row is the
weight of its path.  This is `prod_skewCells_eq_pathWeight` with the two-row
split replaced by `prod_skewCells_rows`.
-/

section Weight

variable {R : Type*} [CommRing R] {b : ℕ} {lam mu : YoungDiagram} {m : ℕ}

/-- The weight of a family is the weight of the tableau it carries. -/
theorem prod_pathWeight_eq_prod_skewCells (hmu : mu ≤ lam)
    (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) (β : ℕ → R) {F : Fin m → ℕ → ℕ}
    (hF : ∀ w : Fin m, F w ∈ hPaths b (jtSource mu m w) (jtSink lam m w)) :
    ∏ w, pathWeight b β (F w)
      = ∏ c ∈ skewCells lam mu, β (skewEntryM b m lam mu F c.1 c.2) := by
  rw [prod_univ_eq_prod_range_famPath F (pathWeight b β),
    prod_skewCells_rows hrow fun i j => β (skewEntryM b m lam mu F i j)]
  refine Finset.prod_congr rfl fun i hi => ?_
  have him := Finset.mem_range.mp hi
  have hlen : mu.rowLen i ≤ lam.rowLen i := rowLen_mono hmu i
  have hmem : famPath F i ∈ hPaths b (rowSource mu m i)
      (rowSource mu m i + (lam.rowLen i - mu.rowLen i)) := by
    have hx := famPath_mem hF him
    rwa [rowSource_add_sub mu m hlen]
  rw [pathWeight_eq_prod_letters hmem β, Finset.prod_Ico_eq_prod_range]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [skewEntryM_of_mem (mem_skewCells_row hmu i (Finset.mem_range.mp hj)),
    show mu.rowLen i + j - mu.rowLen i = j by omega]

end Weight

/-! ## The identity at `m` rows

The two constructions are mutually inverse and weight-preserving, so the
non-intersecting families and the tableaux of `λ/μ` have the same generating
function.  With `jacobiTrudiDet_eq_sum_nonIntersecting` this is over the even
alphabet at every shape and every `m`.
-/

section Identity

variable {R : Type*} [CommRing R]

/-- **The family-to-tableau correspondence at `m` rows.**  For `λ` inside `m`
rows, the non-intersecting families of `m` paths from the sources of `μ` to the
sinks of `λ` carry the total weight of the semistandard tableaux of `λ / μ`.

This is `LGV.NonCrossingIsSkewSchur` at every `m`; the two-row case is
`nonCrossingIsSkewSchur` (see `nonCrossingIsSkewSchur_of_two`). -/
theorem sum_nonIntersecting_eq_skewSchur (b m : ℕ) (β : ℕ → R) (lam mu : YoungDiagram)
    (hmu : mu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    ∑ F ∈ (Fintype.piFinset fun w : Fin m =>
          hPaths b (jtSource mu m w) (jtSink lam m w)).filter fun F => ¬ Intersects b F,
        ∏ w, pathWeight b β (F w)
      = skewSchur lam mu b β := by
  rw [skewSchur]
  refine Finset.sum_bij'
    (fun F hF => skewOfFam (F := F) hrow
      (fun w => Fintype.mem_piFinset.mp (Finset.mem_filter.mp hF).1 w)
      (Finset.mem_filter.mp hF).2)
    (fun T _ => famOfSkew hmu m T) (fun F _ => Finset.mem_univ _) (fun T _ => ?_)
    (fun F hF => ?_) (fun T _ => skewOfFam_famOfSkew hmu hrow T) (fun F hF => ?_)
  · exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (famOfSkew_mem hmu m T),
      not_intersects_famOfSkew hmu T⟩
  · exact famOfSkew_skewOfFam hmu hrow _ _
  · exact prod_pathWeight_eq_prod_skewCells hmu hrow β
      (fun w => Fintype.mem_piFinset.mp (Finset.mem_filter.mp hF).1 w)

/-- **The `m × m` Jacobi--Trudi determinant over the even alphabet.**  For `λ`
inside `m` rows it is the skew Schur polynomial `s_{λ/μ}(β_0, …, β_{b-1})`. -/
theorem jacobiTrudiDet_eq_skewSchur {b m : ℕ} (β : ℕ → R) (lam mu : YoungDiagram)
    (hmu : mu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    jacobiTrudiDet (fun k => completeHom b k β) lam mu m = skewSchur lam mu b β := by
  rw [jacobiTrudiDet_eq_sum_nonIntersecting,
    sum_nonIntersecting_eq_skewSchur b m β lam mu hmu hrow]

/-- **`JacobiTrudi.SkewJacobiTrudi` over the even alphabet, at every shape and
every `m`, with no hypothesis carried.** at `a = 0`:

`det [h_{λ_u - μ_v - u + v}]_{u,v ≤ m} = s_{λ/μ}(β | ∅)`. -/
theorem skewJacobiTrudi_even (b : ℕ) (β α : ℕ → R) :
    SkewJacobiTrudi (fun k => superHom b 0 k β α) b 0 β α := by
  intro lam mu m hmu hrow
  have hd : (fun k => superHom b 0 k β α) = fun k => completeHom b k β :=
    funext fun k => superHom_zero_odd b k β α
  rw [hd, jacobiTrudiDet_eq_skewSchur β lam mu hmu hrow, superSkewSchur_zero_odd β α hmu]

/-- The same statement unrolled, for a determinant of any prescribed alphabet
whose coefficients are those of `ρ_D` at no odd variables. -/
theorem jacobiTrudiDet_eq_superSkewSchur_even {b : ℕ} {β α : ℕ → R} {d : ℕ → R}
    (hd : ∀ k, d k = superHom b 0 k β α) {lam mu : YoungDiagram} {m : ℕ} (hmu : mu ≤ lam)
    (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    jacobiTrudiDet d lam mu m = superSkewSchur lam mu b 0 β α := by
  rw [funext hd]
  exact skewJacobiTrudi_even b β α lam mu m hmu hrow

/-- ** on the appendix's own shapes, at no odd variables.**
The Toeplitz minor `Δ_C` of is the skew Schur function of, with `SkewJacobiTrudi` supplied rather
than assumed. -/
theorem toeplitzMinor_eq_superSkewSchur_even {b : ℕ} {β α : ℕ → R} {d : ℕ → R}
    (hd : ∀ k, d k = superHom b 0 k β α) {n k L Lk : ℕ} (hL : Lk + k = L) (hkn : k ≤ n)
    (hnL : n ≤ Lk) {I : Finset ℕ} (hIn : I ⊆ Finset.range n) (hkI : ∀ x, x < k → x ∈ I) :
    toeplitzMinor d k I.card I (tailSet n k I)
      = superSkewSchur (betaDiagram I L) (betaDiagram (tailSet n k I) Lk) b 0 β α := by
  rw [funext hd]
  exact toeplitzMinor_eq_superSkewSchur (skewJacobiTrudi_even b β α) hL hkn hnL hIn hkI

/-- The two-row identity of `LGVTableau` is this one at `m = 2`: the reading of a
non-intersecting pair by source is the reading `nonCrossingIsSkewSchur` uses. -/
theorem nonCrossingIsSkewSchur_of_two (b : ℕ) (β : ℕ → R) : NonCrossingIsSkewSchur b β := by
  intro lam mu hmu hrow
  rw [← sum_nonIntersecting_two β lam mu, sum_nonIntersecting_eq_skewSchur b 2 β lam mu hmu hrow]

end Identity

/-! ## Non-vacuity

The smallest instance that needs the three-path selection: on the column
`λ = (1,1,1)` in three even variables the `3 × 3` determinant is `β_0 β_1 β_2`.
-/

section Instance

variable {R : Type*} [CommRing R]

theorem jacobiTrudiDet_three_column (β : ℕ → R) :
    jacobiTrudiDet (fun k => completeHom 3 k β) (rect 3 1) ⊥ 3 = β 0 * β 1 * β 2 := by
  rw [jacobiTrudiDet_eq_skewSchur β (rect 3 1) ⊥ bot_le
      (fun i hi => rowLen_rect_of_le (by omega)),
    skewSchur_bot, schur_rect, pow_one, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_one]

end Instance


/-! ### Axiom footprint -/

/-- info: 'Shields.famOfSkew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms famOfSkew

/-- info: 'Shields.skewOfFam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms skewOfFam

end Shields
