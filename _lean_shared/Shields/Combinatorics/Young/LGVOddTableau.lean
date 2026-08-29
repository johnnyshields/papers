/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.LGVMixed
import Shields.Combinatorics.Young.SkewCells
import Shields.Combinatorics.Young.LGVTableau

/-!
# The mixed alphabet at `m` rows

`Shields.Combinatorics.Young.LGVMixed` reduces the `m × m` Jacobi--Trudi determinant over the
mixed alphabet to the non-intersecting families of `m` mixed paths, at every `m` and with no
hypotheses, and leaves one residue: `Shields.NonIntersectingIsSuperSkewSchur`, that those families
carry the branching sum.  `Shields.Combinatorics.Young.LGVOddResidue` fibers those families over
their abscissae at height `b` and asks in return for two tableau bijections at `m`.  The even one
is `Shields.Combinatorics.Young.LGVTableau`; the odd one is proved here, and with it the residue
is discharged.

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
  have hmem := ePathOfWord_mem a (rowSource nu m i) (lam.rowLen i - nu.rowLen i)
    (eColWord a lam nu T i)
  rwa [rowSource_add_sub nu m (rowLen_mono hnu i)] at hmem

/-- A letter of column `i` below `k` puts its abscissa behind that column's path
at height `k`. -/
theorem lt_eRowPath_of_entry (T : BoundedSkewSSYT lam.transpose nu.transpose a) {i j k : ℕ}
    (hj : nu.rowLen i ≤ j) (hj' : j < lam.rowLen i) (h : T.1 j i < k) :
    j + (m - 1 - i) < eRowPath a m lam nu T i k := by
  have hjj : j - nu.rowLen i < lam.rowLen i - nu.rowLen i := by omega
  have hstep := lt_ePathOfWord (s := rowSource nu m i) (i := k) (eColWord a lam nu T i) hjj (by
    rw [eColWord_apply T i hjj, show nu.rowLen i + (j - nu.rowLen i) = j by omega]
    exact h)
  rwa [rowSource_add_sub nu m hj] at hstep

/-- A letter of column `i` at or above `k` stops that column's path at its abscissa. -/
theorem eRowPath_le_of_entry (T : BoundedSkewSSYT lam.transpose nu.transpose a) {i j k : ℕ}
    (hj : nu.rowLen i ≤ j) (hj' : j < lam.rowLen i) (h : k ≤ T.1 j i) :
    eRowPath a m lam nu T i k ≤ j + (m - 1 - i) := by
  have hjj : j - nu.rowLen i < lam.rowLen i - nu.rowLen i := by omega
  have hstep := ePathOfWord_le (s := rowSource nu m i) (i := k) (j := j - nu.rowLen i)
    (eColWord a lam nu T i) (by
      rw [eColWord_apply T i hjj, show nu.rowLen i + (j - nu.rowLen i) = j by omega]
      exact h)
  rwa [rowSource_add_sub nu m hj] at hstep

/-- **The weak row condition is separation, at consecutive columns.**  Column
`i+1` sits strictly left of column `i` at every height.  The offsets of the two
columns differ by exactly one, which is what makes the weak inequality of the
tableau buy a full step. -/
theorem lt_eRowPath_succ (hnu : nu ≤ lam) (T : BoundedSkewSSYT lam.transpose nu.transpose a)
    {k u : ℕ} (hu : u + 1 < m) :
    eRowPath a m lam nu T (u + 1) k < eRowPath a m lam nu T u k := by
  have hnurow : nu.rowLen (u + 1) ≤ nu.rowLen u := nu.rowLen_anti u (u + 1) (by omega)
  have hlamrow : lam.rowLen (u + 1) ≤ lam.rowLen u := lam.rowLen_anti u (u + 1) (by omega)
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
    have hx := lt_eRowPath_of_entry (m := m) T hj₀nu (by omega) hlt
    omega
  have hb : T.1 j₀ (u + 1) < k := by
    by_contra hgt
    rw [Nat.not_lt] at hgt
    have hx := eRowPath_le_of_entry (m := m) T (i := u + 1) (j := j₀) (k := k)
      (by omega) hj₀lam hgt
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
  rw [famPath_of_lt G hi]
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
    have e1 := famPath_of_lt G (show u < m by omega)
    have e2 := famPath_of_lt G hu
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
    rwa [rowSource_add_sub nu m hlen]
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
    rwa [rowSource_add_sub nu m hlen]
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
    have hfp : famPath (eFamOfSkew a m lam nu T) i = eRowPath a m lam nu T i :=
      famPath_of_lt _ hi
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
  rw [prod_univ_eq_prod_range_famPath G (pathWeight a α),
    prod_skewCells_transpose_cols hrow fun j i => α (eSkewEntryM a m lam nu G j i)]
  refine Finset.prod_congr rfl fun i hi => ?_
  have him := Finset.mem_range.mp hi
  have hlen : nu.rowLen i ≤ lam.rowLen i := rowLen_mono hnu i
  have hmem : famPath G i ∈ hPaths a (rowSource nu m i)
      (rowSource nu m i + (lam.rowLen i - nu.rowLen i)) := by
    have hx := ePaths_mem (eFamPath_mem hG him)
    rwa [rowSource_add_sub nu m hlen]
  rw [pathWeight_eq_prod_letters hmem α, Finset.prod_Ico_eq_prod_range]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [eSkewEntryM_of_mem (mem_skewCells_transpose_col i (Finset.mem_range.mp hj)),
    show nu.rowLen i + j - nu.rowLen i = j by omega]

/-- **The odd tableau bijection at `m` columns.**  For `λ` inside `m` rows, the
families of `m` odd paths from the sources of `ν` to the sinks of `λ` that share
no point carry the total weight of the semistandard tableaux of the conjugate
skew shape `λ' / ν'`.

This is `nonMeetingIsSkewSchurTranspose` at every `m`, and it holds
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

/-! ## The residue at every `m`

`sum_nonIntersecting_mixed_eq_superSkewSchur` fibers the non-intersecting mixed
families over their abscissae at height `b` and carries the two tableau bijections in its type.
Both are now theorems at every `m`, so the residue closes and the skew Jacobi--Trudi identity for
the mixed alphabet follows with nothing assumed.
-/

section Residue

variable {R : Type*} [CommRing R]

/-- **The residue at every `m`.**  The non-intersecting families of `m` mixed
paths from the sources of `μ` to the sinks of `λ` carry the branching sum of
the super branching rule.

This is `LGVMixed.NonIntersectingIsSuperSkewSchur`, proved there at `m ≤ 2` and
carried as a hypothesis beyond.  The fibering over the abscissae at height `b` is
`sum_nonIntersecting_mixed_eq_superSkewSchur`, which asks for the two tableau
bijections; both are theorems at every `m` -- the even one is
`sum_nonIntersecting_eq_skewSchur` and the odd one is
`sum_nonEIntersecting_eq_skewSchurTranspose` above. -/
theorem nonIntersectingIsSuperSkewSchur (b a m : ℕ) (β α : ℕ → R) :
    NonIntersectingIsSuperSkewSchur b a m β α := by
  intro lam mu hmu hrow
  exact sum_nonIntersecting_mixed_eq_superSkewSchur (sum_nonIntersecting_eq_skewSchur b m β)
    (sum_nonEIntersecting_eq_skewSchurTranspose a m α) lam mu hmu hrow

/-- **the skew Jacobi--Trudi identity at every `m`, with the odd alphabet, unconditionally.**
For `λ` inside `m` rows,

`det [d_{λ_u - μ_v - u + v}]_{u,v < m} = s_{λ/μ}(β | α)`,

over any commutative ring, every `b`, `a`, `β`, `α` and every `μ ⊆ λ`.  The
cancellation is `mixedJacobiTrudiDet_eq_sum_nonIntersecting` and the
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
`elemDet_two_column` one row further up. -/
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


/-! ### Axiom footprint -/

/-- info: 'Shields.toeplitzMinor_pos_iff_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toeplitzMinor_pos_iff_uncond

end Shields
