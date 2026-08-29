/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Shields.LinearAlgebra.Matrix.CauchyBinet
import Shields.LinearAlgebra.Matrix.TotallyNonneg.Basic
import Shields.Order.SignChanges

/-!
# Schoenberg's variation-diminishing property

A **totally nonnegative** matrix cannot increase the number of sign changes of the vector it acts
on: `S^-(Ax) \le S^-(x)`.  This is Schoenberg's variation-diminishing property, the analytic
content behind the location of the zeros of a Polya-frequency generating function.

## Main results

* `Shields.RectMinorsNonneg` -- every minor of a rectangular matrix is nonnegative
* `Shields.minors_eq_zero_of_alternating` -- if a totally nonnegative `(p+1) \times p` matrix
  carries a strictly alternating vector in its column span, every maximal minor vanishes
* `Shields.altIndices_lt_of_rectMinorsNonneg` -- the core bound: a totally nonnegative matrix with
  `p` columns maps every vector to one with fewer than `p` sign changes, unless the image is zero
* `Shields.signChanges_mulVec_le` -- **variation diminution** for a vector with no zero entry

## Implementation notes

**No density theorem and no rank theory are used.**  The classical proof perturbs a totally
nonnegative matrix to a strictly totally positive one, which needs Whitney's reduction theorem.
Here the degenerate case is not excluded but consumed: when the maximal minors of the
`(p+1) \times p` matrix all vanish, its columns are dependent -- read off the Gram determinant
`\det(C^{T}C)`, which Cauchy--Binet expands as a sum of squares of those minors -- so one column
can be deleted and the induction on the number of columns proceeds.

The block decomposition of the acting vector is a matrix factorization `x = W v` with `v` strictly
alternating, where `W` places `|x_j|` in the column indexed by the number of sign changes before
`j`.  `W` has at most one nonzero per row, so its minors are `0` or `1`.

## References

* [S. Karlin, *Total Positivity*][Karlin1968TotalPositivity], Ch. 5 § 3
* [A. Pinkus, *Totally Positive Matrices*][Pinkus2010TotallyPositive], § 3.1

## Tags

total positivity, variation diminishing, sign change, Polya frequency
-/

open Finset Matrix

namespace Shields

variable {M n p : ℕ}

/-! ### Rectangular total nonnegativity -/

/-- Every increasing-selection minor of a rectangular matrix is nonnegative. -/
def RectMinorsNonneg {M n : ℕ} (A : Matrix (Fin M) (Fin n) ℝ) : Prop :=
  ∀ (k : ℕ) (f : Fin k → Fin M) (g : Fin k → Fin n), StrictMono f → StrictMono g →
    0 ≤ (A.submatrix f g).det

theorem RectMinorsNonneg.submatrixRows {A : Matrix (Fin M) (Fin n) ℝ} (hA : RectMinorsNonneg A)
    {M' : ℕ} {i : Fin M' → Fin M} (hi : StrictMono i) :
    RectMinorsNonneg (A.submatrix i id) := fun k f g hf hg => hA k (i ∘ f) g (hi.comp hf) hg

theorem RectMinorsNonneg.submatrixCols {A : Matrix (Fin M) (Fin n) ℝ} (hA : RectMinorsNonneg A)
    {n' : ℕ} {σ : Fin n' → Fin n} (hσ : StrictMono σ) :
    RectMinorsNonneg (A.submatrix id σ) := fun k f g hf hg => hA k f (σ ∘ g) hf (hσ.comp hg)

theorem RectMinorsNonneg.entry_nonneg {A : Matrix (Fin M) (Fin n) ℝ} (hA : RectMinorsNonneg A)
    (i : Fin M) (j : Fin n) : 0 ≤ A i j := by
  have := hA 1 (fun _ => i) (fun _ => j) (Subsingleton.strictMono _) (Subsingleton.strictMono _)
  simpa [Matrix.det_fin_one] using this

/-! ### Every increasing selection omits exactly one index -/

/-- A strictly monotone map `Fin p → Fin (p+1)` skips exactly one value, so it is a `succAbove`. -/
theorem exists_succAbove_eq {f : Fin p → Fin (p + 1)} (hf : StrictMono f) :
    ∃ a : Fin (p + 1), f = a.succAbove := by
  have hcard : (univ.image f).card = p := by
    rw [Finset.card_image_of_injective _ hf.injective, Finset.card_univ, Fintype.card_fin]
  obtain ⟨a, ha⟩ : ∃ a : Fin (p + 1), a ∉ univ.image f := by
    by_contra hc
    push Not at hc
    have : (univ : Finset (Fin (p + 1))).card ≤ (univ.image f).card :=
      Finset.card_le_card fun b _ => hc b
    simp [hcard] at this
  refine ⟨a, strictMono_eq_of_image_eq hf (Fin.strictMono_succAbove a) ?_⟩
  have hsub : ∀ (g : Fin p → Fin (p + 1)), Function.Injective g → (∀ t, g t ≠ a) →
      univ.image g = ({a}ᶜ : Finset (Fin (p + 1))) := by
    intro g hg hga
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro b hb
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hb
      simpa using hga t
    · rw [Finset.card_compl, Finset.card_singleton, Finset.card_image_of_injective _ hg]
      simp
  rw [hsub f hf.injective (fun t hc => ha (hc ▸ Finset.mem_image_of_mem f (Finset.mem_univ t))),
    hsub _ (Fin.strictMono_succAbove a).injective (fun t => Fin.succAbove_ne a t)]

/-! ### An alternating vector in the column span kills every maximal minor -/

/-- The augmented square matrix: the columns of `C` followed by `C z`. -/
private noncomputable def augment (C : Matrix (Fin (p + 1)) (Fin p) ℝ) (z : Fin p → ℝ) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  Matrix.of fun a b => Fin.lastCases ((C *ᵥ z) a) (fun t => C a t) b

private theorem det_augment (C : Matrix (Fin (p + 1)) (Fin p) ℝ) (z : Fin p → ℝ) :
    (augment C z).det = 0 := by
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Fin.lastCases (-1) z, ?_, ?_⟩
  · intro hc
    have h0 := congrFun hc (Fin.last p)
    rw [Fin.lastCases_last] at h0
    norm_num at h0
  · funext a
    change (∑ b : Fin (p + 1), augment C z a b * (Fin.lastCases (-1) z : Fin (p + 1) → ℝ) b) = 0
    rw [Fin.sum_univ_castSucc]
    simp only [augment, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
    have hmv : (C *ᵥ z) a = ∑ t : Fin p, C a t * z t := rfl
    rw [hmv]
    ring

/-- A sequence whose consecutive products are negative has `(-1)^b w_0 w_b > 0`: the signs
alternate, so no entry vanishes and the sign of `w_0 w_b` is the parity of `b`. -/
private theorem sign_alternating {p : ℕ} (hp : 0 < p) {w : Fin (p + 1) → ℝ}
    (halt : ∀ a : Fin p, w a.castSucc * w a.succ < 0) (b : Fin (p + 1)) :
    0 < (-1 : ℝ) ^ (b : ℕ) * (w 0 * w b) := by
  induction b using Fin.induction with
  | zero =>
      simp only [Fin.val_zero, pow_zero, one_mul]
      refine mul_self_pos.mpr fun hc => ?_
      have h0 := halt ⟨0, hp⟩
      rw [show (⟨0, hp⟩ : Fin p).castSucc = (0 : Fin (p + 1)) from rfl, hc, zero_mul] at h0
      exact lt_irrefl 0 h0
  | succ c ih =>
      have hlt := halt c
      have hsq : 0 < w c.castSucc * w c.castSucc := by
        refine mul_self_pos.mpr fun hc => ?_
        rw [hc, zero_mul] at hlt
        exact lt_irrefl 0 hlt
      rw [show (c.succ : ℕ) = (c.castSucc : ℕ) + 1 by simp, pow_add, pow_one]
      nlinarith [mul_pos ih (neg_pos.mpr hlt), hsq]

/-- **The alternating combination of maximal minors vanishes.**  Bordering `C` with `C z` gives a
singular matrix -- the vector `(z, -1)` lies in its kernel -- and expanding the determinant along
that appended column is the identity below, with the sign of the `b`-th term rewritten as the
parity of `b`. -/
private theorem sum_alt_mulVec_minor_eq_zero {p : ℕ} (C : Matrix (Fin (p + 1)) (Fin p) ℝ)
    (z : Fin p → ℝ) :
    ∑ b : Fin (p + 1), ((-1 : ℝ) ^ (b : ℕ) * ((C *ᵥ z) 0 * (C *ᵥ z) b))
        * (C.submatrix b.succAbove id).det = 0 := by
  have hlap := Matrix.det_succ_column (augment C z) (Fin.last p)
  rw [det_augment] at hlap
  have hsub : ∀ b : Fin (p + 1),
      (augment C z).submatrix b.succAbove (Fin.last p).succAbove
        = C.submatrix b.succAbove id := fun b => by ext r t; simp [augment, Fin.succAbove_last]
  have hentry : ∀ b : Fin (p + 1), augment C z b (Fin.last p) = (C *ᵥ z) b :=
    fun b => by simp [augment]
  simp only [hsub, hentry, Fin.val_last] at hlap
  have hpow : ∀ b : Fin (p + 1),
      ((-1 : ℝ) ^ p) * ((-1 : ℝ) ^ ((b : ℕ) + p)) = (-1 : ℝ) ^ (b : ℕ) := fun b => by
    rw [← pow_add, show p + ((b : ℕ) + p) = (b : ℕ) + 2 * p by ring, pow_add, pow_mul]
    norm_num
  have hz : ((-1 : ℝ) ^ p * (C *ᵥ z) 0) * (∑ b : Fin (p + 1),
      (-1 : ℝ) ^ ((b : ℕ) + p) * (C *ᵥ z) b * (C.submatrix b.succAbove id).det) = 0 := by
    rw [← hlap]; ring
  rw [Finset.mul_sum] at hz
  rw [← hz]
  exact Finset.sum_congr rfl fun b _ => by rw [← hpow b]; ring

/-- **A strictly alternating vector in the column span kills every maximal minor.**  The augmented
matrix is singular; expanding its determinant along the appended column gives an alternating sum
of the maximal minors of `C` against the entries of `C z`, and the alternation makes every term
of that sum nonnegative, so each vanishes. -/
theorem minors_eq_zero_of_alternating {p : ℕ} (hp : 0 < p)
    {C : Matrix (Fin (p + 1)) (Fin p) ℝ} (hC : RectMinorsNonneg C) {z : Fin p → ℝ}
    (halt : ∀ a : Fin p, (C *ᵥ z) a.castSucc * (C *ᵥ z) a.succ < 0) (a : Fin (p + 1)) :
    (C.submatrix a.succAbove id).det = 0 := by
  have hpar := sign_alternating hp halt
  have hMnn : ∀ b : Fin (p + 1), 0 ≤ (C.submatrix b.succAbove id).det := fun b =>
    hC p (b.succAbove) id (Fin.strictMono_succAbove b) strictMono_id
  have hterm : ∀ b ∈ (univ : Finset (Fin (p + 1))),
      0 ≤ ((-1 : ℝ) ^ (b : ℕ) * ((C *ᵥ z) 0 * (C *ᵥ z) b))
        * (C.submatrix b.succAbove id).det := fun b _ => mul_nonneg (hpar b).le (hMnn b)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp
    (sum_alt_mulVec_minor_eq_zero C z) a (Finset.mem_univ a)
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h (ne_of_gt (hpar a))
  · exact h

/-! ### Vanishing maximal minors force a column dependency -/

/-- **Cauchy--Binet reads the Gram determinant as a sum of squares of maximal minors**, so if they
all vanish the columns are dependent. -/
theorem exists_mulVec_eq_zero_of_minors_eq_zero {m p : ℕ} {D : Matrix (Fin m) (Fin p) ℝ}
    (h : ∀ f : Fin p → Fin m, StrictMono f → (D.submatrix f id).det = 0) :
    ∃ c : Fin p → ℝ, c ≠ 0 ∧ D *ᵥ c = 0 := by
  have hgram : (Dᵀ * D).det = 0 := by
    rw [det_mul_eq_sum_increasing]
    refine Finset.sum_eq_zero fun f hf => ?_
    rw [mem_increasingSelections] at hf
    rw [h f hf, mul_zero]
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hgram
  refine ⟨c, hc0, ?_⟩
  have hmem : c ∈ LinearMap.ker (Dᵀ * D).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hc
  rw [Matrix.ker_mulVecLin_transpose_mul_self, LinearMap.mem_ker,
    Matrix.mulVecLin_apply] at hmem
  exact hmem

/-- A column dependency lets one column be deleted without changing the image of any vector. -/
theorem exists_dropCol {m p : ℕ} {D : Matrix (Fin m) (Fin (p + 1)) ℝ}
    {c : Fin (p + 1) → ℝ} (hc0 : c ≠ 0) (hc : D *ᵥ c = 0) (z : Fin (p + 1) → ℝ) :
    ∃ (j : Fin (p + 1)) (z' : Fin p → ℝ),
      (D.submatrix id j.succAbove) *ᵥ z' = D *ᵥ z := by
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := Function.ne_iff.mp hc0
  refine ⟨j, fun t => z (j.succAbove t) - z j * c (j.succAbove t) / c j, ?_⟩
  funext i
  have hz : (D *ᵥ z) i = D i j * z j + ∑ t : Fin p, D i (j.succAbove t) * z (j.succAbove t) :=
    Fin.sum_univ_succAbove (fun b => D i b * z b) j
  have hcz : D i j * c j + ∑ t : Fin p, D i (j.succAbove t) * c (j.succAbove t) = 0 := by
    rw [← Fin.sum_univ_succAbove (fun b => D i b * c b) j]
    exact congrFun hc i
  have hlhs : ((D.submatrix id j.succAbove) *ᵥ
      (fun t => z (j.succAbove t) - z j * c (j.succAbove t) / c j)) i
      = ∑ t : Fin p, D i (j.succAbove t) * (z (j.succAbove t) - z j * c (j.succAbove t) / c j) :=
    rfl
  rw [hlhs, hz]
  have hsplit :
      ∑ t : Fin p, D i (j.succAbove t) * (z (j.succAbove t) - z j * c (j.succAbove t) / c j)
      = (∑ t : Fin p, D i (j.succAbove t) * z (j.succAbove t))
        - (z j / c j) * ∑ t : Fin p, D i (j.succAbove t) * c (j.succAbove t) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hsplit, show ∑ t : Fin p, D i (j.succAbove t) * c (j.succAbove t) = -(D i j * c j) from by
    linarith [hcz]]
  field

/-! ### The core bound -/

/-- **The inductive step.**  With the bound known at `p` columns, suppose `D z` alternates at
`k ≥ p + 1` indices.  Restricting to the first `p + 2` of them gives a matrix whose maximal minors
all vanish, so its columns are dependent; dropping one leaves `D z` on those rows unchanged, and
the induction hypothesis applies to the shorter matrix. -/
private theorem altIndices_step {p : ℕ}
    (ih : ∀ (M : ℕ) (D : Matrix (Fin M) (Fin p) ℝ), RectMinorsNonneg D →
      ∀ (z : Fin p → ℝ) (k : ℕ), AltIndices (D *ᵥ z) k → k < p ∨ D *ᵥ z = 0)
    (M : ℕ) (D : Matrix (Fin M) (Fin (p + 1)) ℝ) (hD : RectMinorsNonneg D)
    (z : Fin (p + 1) → ℝ) (k : ℕ) (hk : AltIndices (D *ᵥ z) k) :
    k < p + 1 ∨ D *ᵥ z = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hkp, -⟩ := hcon
  obtain ⟨i, hi, halt⟩ := hk
  have hle : (p + 1) + 1 ≤ k + 1 := by omega
  set C := D.submatrix (fun a : Fin (p + 2) => i (Fin.castLE hle a)) id with hCdef
  have hCtn : RectMinorsNonneg C := hD.submatrixRows (hi.comp (Fin.strictMono_castLE hle))
  have hCval : ∀ a : Fin (p + 2), (C *ᵥ z) a = (D *ᵥ z) (i (Fin.castLE hle a)) := fun _ => rfl
  have hCalt : ∀ a : Fin (p + 1), (C *ᵥ z) a.castSucc * (C *ᵥ z) a.succ < 0 := by
    intro a
    have has : (a : ℕ) < k := by have := a.isLt; omega
    rw [hCval, hCval,
      show Fin.castLE hle a.castSucc = (⟨(a : ℕ), has⟩ : Fin k).castSucc from Fin.ext (by simp),
      show Fin.castLE hle a.succ = (⟨(a : ℕ), has⟩ : Fin k).succ from Fin.ext (by simp)]
    exact halt ⟨(a : ℕ), has⟩
  obtain ⟨c, hc0, hcz⟩ := exists_mulVec_eq_zero_of_minors_eq_zero (D := C) (fun f hf => by
    obtain ⟨a, rfl⟩ := exists_succAbove_eq hf
    exact minors_eq_zero_of_alternating (by omega) hCtn hCalt a)
  obtain ⟨j, z', hz'⟩ := exists_dropCol hc0 hcz z
  rcases ih (p + 2) _ (hCtn.submatrixCols (Fin.strictMono_succAbove j)) z' (p + 1)
    ⟨id, strictMono_id, fun a => by rw [hz']; exact hCalt a⟩ with hlt | hzero
  · omega
  · rw [hz'] at hzero
    have := hCalt ⟨0, by omega⟩
    rw [hzero] at this
    simp at this

/-- **A totally nonnegative matrix with `p` columns cannot produce `p` sign changes.**  The
induction is on the number of columns: if the image alternates that often, the maximal minors of
the restricted matrix all vanish, a column can be deleted, and the shorter matrix produces the
same image. -/
theorem altIndices_lt_of_rectMinorsNonneg :
    ∀ (p M : ℕ) (D : Matrix (Fin M) (Fin p) ℝ), RectMinorsNonneg D → ∀ (z : Fin p → ℝ) (k : ℕ),
      AltIndices (D *ᵥ z) k → k < p ∨ D *ᵥ z = 0 := by
  intro p
  induction p with
  | zero =>
      intro M D _ z k _
      exact Or.inr (funext fun i => by simp [Matrix.mulVec, dotProduct])
  | succ p ih => exact altIndices_step ih

/-! ### Products, and the block decomposition of the acting vector -/

theorem rectMinorsNonneg_mul {M n r : ℕ} {A : Matrix (Fin M) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin r) ℝ} (hA : RectMinorsNonneg A) (hB : RectMinorsNonneg B) :
    RectMinorsNonneg (A * B) := by
  intro k f g hf hg
  rw [Matrix.submatrix_mul A B f id g Function.bijective_id, det_mul_eq_sum_increasing]
  refine Finset.sum_nonneg fun h hh => ?_
  rw [mem_increasingSelections] at hh
  exact mul_nonneg (hA k f h hf hh) (hB k h g hh hg)

/-- **A `0`-`1` matrix whose pattern is a monotone map has nonnegative determinant.**  Only the
identity permutation can survive: a nonzero Leibniz term forces the monotone index map to agree
with a strictly monotone one after permuting, and that pins the permutation. -/
theorem det_pattern_nonneg {r n q : ℕ} {φ : Fin n → ℕ} (hφ : Monotone φ)
    {h : Fin r → Fin n} (hh : StrictMono h) {g : Fin r → Fin (q + 1)} (hg : StrictMono g) :
    0 ≤ (Matrix.of fun a b : Fin r => if φ (h a) = (g b : ℕ) then (1 : ℝ) else 0).det := by
  rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin r))]
  · rw [Equiv.Perm.sign_one, one_smul]
    refine Finset.prod_nonneg fun a _ => ?_
    dsimp only [Matrix.of_apply, Equiv.Perm.coe_one, id_eq]
    split <;> norm_num
  · intro σ _ hσ
    have hzero : ∏ a, (Matrix.of fun a b : Fin r =>
        if φ (h a) = (g b : ℕ) then (1 : ℝ) else 0) (σ a) a = 0 := by
      by_contra hc
      have hall : ∀ a, φ (h (σ a)) = (g a : ℕ) := fun a => by
        by_contra hca
        exact hc (Finset.prod_eq_zero (Finset.mem_univ a)
          (by dsimp only [Matrix.of_apply]; rw [if_neg hca]))
      have hψmono : Monotone fun a => φ (h a) := hφ.comp hh.monotone
      have hσmono : StrictMono σ := by
        intro a b hab
        by_contra hcon
        have hba : φ (h (σ b)) ≤ φ (h (σ a)) := hψmono (not_lt.mp hcon)
        rw [hall b, hall a] at hba
        have := hg hab
        rw [Fin.lt_def] at this
        omega
      exact hσ (perm_eq_one_of_strictMono hσmono)
    rw [hzero, smul_zero]
  · intro hc; exact absurd (Finset.mem_univ _) hc

/-- The block matrix of `x`: it carries `|x_j|` in the column indexed by the number of sign
changes of `x` before `j`. -/
noncomputable def blockMatrix {n : ℕ} (x : Fin n → ℝ) (q : ℕ) : Matrix (Fin n) (Fin (q + 1)) ℝ :=
  Matrix.of fun j t => if jumpCount (vecExt x) (j : ℕ) = (t : ℕ) then |x j| else 0

theorem rectMinorsNonneg_blockMatrix {n : ℕ} (x : Fin n → ℝ) (q : ℕ) :
    RectMinorsNonneg (blockMatrix x q) := by
  intro k f g hf hg
  have hEq : (blockMatrix x q).submatrix f g
      = Matrix.of fun a b : Fin k => |x (f a)| *
        (Matrix.of fun a' b' : Fin k =>
          if jumpCount (vecExt x) ((f a' : ℕ)) = ((g b' : ℕ)) then (1 : ℝ) else 0) a b := by
    ext a b
    simp only [blockMatrix, Matrix.submatrix_apply, Matrix.of_apply]
    split <;> simp
  rw [hEq, Matrix.det_mul_column]
  refine mul_nonneg (Finset.prod_nonneg fun a _ => abs_nonneg _) ?_
  exact det_pattern_nonneg (φ := fun j : Fin n => jumpCount (vecExt x) (j : ℕ))
    (fun a b hab => monotone_jumpCount _ (by exact_mod_cast hab)) hf hg

private theorem abs_div_sign {a b : ℝ} (h : 0 < b * a) : |a| * (b / |b|) = a := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · have ha : a < 0 := by nlinarith
    have hq : b / |b| = -1 := by rw [abs_of_neg hb, div_neg, div_self hb.ne]
    rw [hq, abs_of_neg ha]; ring
  · exact absurd h (by rw [hb, zero_mul]; exact lt_irrefl 0)
  · have ha : 0 < a := by nlinarith
    have hq : b / |b| = 1 := by rw [abs_of_pos hb, div_self hb.ne']
    rw [hq, abs_of_pos ha]; ring

private theorem abs_mul_pow_sign {a b : ℝ} {e : ℕ} (h : 0 < (-1 : ℝ) ^ e * (b * a)) :
    |a| * ((-1 : ℝ) ^ e * (b / |b|)) = a := by
  rcases Nat.even_or_odd e with he | he
  · rw [he.neg_one_pow] at h ⊢
    rw [one_mul] at h
    rw [one_mul]
    exact abs_div_sign h
  · rw [he.neg_one_pow] at h ⊢
    have h' : 0 < (-b) * a := by nlinarith
    have hres := abs_div_sign h'
    rw [abs_neg] at hres
    rw [show (-1 : ℝ) * (b / |b|) = (-b) / |b| by ring]
    exact hres

/-- **The block factorization.**  `x = W v` with `v` strictly alternating and `W` the block
matrix, which is where the sign pattern of `x` is converted into a matrix with `S^-(x) + 1`
columns. -/
theorem blockMatrix_mulVec {n : ℕ} {x : Fin n → ℝ} (hx : ∀ j, x j ≠ 0) (hn : 0 < n) :
    (blockMatrix x (jumpCount (vecExt x) (n - 1))) *ᵥ
      (fun t => (-1 : ℝ) ^ (t : ℕ) * (x ⟨0, hn⟩ / |x ⟨0, hn⟩|)) = x := by
  funext j
  have hune : ∀ p ≤ n - 1, vecExt x p ≠ 0 := fun p hp => vecExt_ne_zero hx (by omega)
  have hjn : (j : ℕ) ≤ n - 1 := by have := j.isLt; omega
  have hcle : jumpCount (vecExt x) (j : ℕ) ≤ jumpCount (vecExt x) (n - 1) :=
    monotone_jumpCount _ hjn
  change (∑ t : Fin (jumpCount (vecExt x) (n - 1) + 1),
      blockMatrix x (jumpCount (vecExt x) (n - 1)) j t *
        ((-1 : ℝ) ^ (t : ℕ) * (x ⟨0, hn⟩ / |x ⟨0, hn⟩|))) = x j
  rw [Finset.sum_eq_single (⟨jumpCount (vecExt x) (j : ℕ), by omega⟩ :
      Fin (jumpCount (vecExt x) (n - 1) + 1))]
  · have hp := jumpCount_parity hune (j : ℕ) hjn
    rw [vecExt_of_lt hn, vecExt_coe] at hp
    simp only [blockMatrix, Matrix.of_apply]
    exact abs_mul_pow_sign hp
  · intro t _ hne
    simp only [blockMatrix, Matrix.of_apply]
    rw [if_neg (fun hc => hne (Fin.ext hc.symm)), zero_mul]
  · intro hc; exact absurd (Finset.mem_univ _) hc

/-! ### Variation diminution -/

/-- **Schoenberg's variation-diminishing property**, in the form the sector argument uses: a
totally nonnegative matrix acting on a vector with no zero entry produces a vector alternating
along at most `S^-(x) + 1` indices. -/
theorem altIndices_mulVec_le {M n : ℕ} {A : Matrix (Fin M) (Fin n) ℝ} (hA : RectMinorsNonneg A)
    {x : Fin n → ℝ} (hx : ∀ j, x j ≠ 0) {k : ℕ} (hk : AltIndices (A *ᵥ x) k) :
    k ≤ jumpCount (vecExt x) (n - 1) := by
  have hkill : A *ᵥ x = 0 → k = 0 := by
    intro hz
    rw [hz] at hk
    obtain ⟨i, -, halt⟩ := hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact hk0
    · exact absurd (halt ⟨0, hk0⟩) (by simp)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : A *ᵥ x = 0 := funext fun i => by simp [Matrix.mulVec, dotProduct]
    simp [hkill hzero]
  · have hWv := blockMatrix_mulVec hx hn
    have hfac : (A * blockMatrix x (jumpCount (vecExt x) (n - 1))) *ᵥ
        (fun t => (-1 : ℝ) ^ (t : ℕ) * (x ⟨0, hn⟩ / |x ⟨0, hn⟩|)) = A *ᵥ x := by
      rw [← Matrix.mulVec_mulVec, hWv]
    have hAW := rectMinorsNonneg_mul hA (rectMinorsNonneg_blockMatrix x
      (jumpCount (vecExt x) (n - 1)))
    rw [← hfac] at hk
    rcases altIndices_lt_of_rectMinorsNonneg (jumpCount (vecExt x) (n - 1) + 1) M _ hAW _ k hk with
      hlt | hz
    · omega
    · rw [hfac] at hz
      simp [hkill hz]

/-- **Variation diminution.**  A totally nonnegative matrix does not increase the number of sign
changes of a vector with no zero entry. -/
theorem signChanges_mulVec_le {M n : ℕ} {A : Matrix (Fin M) (Fin n) ℝ} (hA : RectMinorsNonneg A)
    {x : Fin n → ℝ} (hx : ∀ j, x j ≠ 0) :
    signChanges (A *ᵥ x) ≤ signChanges x := by
  refine signChanges_le fun k hk => le_trans (altIndices_mulVec_le hA hx hk) ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · exact le_signChanges (altIndices_jumpCount hx hn)


/-! ### Axiom footprint -/

/-- info: 'Shields.minors_eq_zero_of_alternating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minors_eq_zero_of_alternating

/-- info: 'Shields.signChanges_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signChanges_mulVec_le

end Shields
