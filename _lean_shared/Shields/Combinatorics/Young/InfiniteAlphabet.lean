/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.ElementarySymmetric

/-!
# Skew Schur functions at an infinite alphabet

A skew Schur function in `n` nonnegative variables increases with `n` and is bounded by
`(∑ x)^{|λ/μ|}`, so for a summable nonnegative alphabet the truncations converge.  The
bound comes from the tableau description directly: a bounded skew tableau is determined
by its entries on the skew cells, so the tableaux inject into the functions from the skew
cells to `{0,…,n-1}`, and the sum over *all* such functions is the product of the sums.

## Main results

* `Shields.skewSchur_mono` — monotonicity in the number of variables.
* `Shields.skewSchur_le_pow` — the bound `(∑_{i<n} x_i)^{|λ/μ|}`.
* `Shields.tendsto_completeHom` — **the infinite complete homogeneous symmetric
  function**, as a monotone limit of the truncations.

## Papers depending on this file

* `growing-rank-edrei` — the passage of `eq:rect-schur` to an infinite even alphabet.
-/

open Finset Filter Topology

namespace Shields

variable {lam mu : YoungDiagram} {n m : ℕ}

/-! ### Monotonicity in the number of variables -/

/-- A tableau bounded by `n` is one bounded by any larger `m`. -/
def widenBound (h : n ≤ m) (T : BoundedSkewSSYT lam mu n) : BoundedSkewSSYT lam mu m :=
  ⟨T.1, fun i j hc => lt_of_lt_of_le (T.2 i j hc) h⟩

theorem widenBound_injective (h : n ≤ m) :
    Function.Injective (widenBound (lam := lam) (mu := mu) h) := by
  intro T T' hTT'
  exact Subtype.ext (congrArg (fun T : BoundedSkewSSYT lam mu m => T.1) hTT')

/-- **A skew Schur function increases with the number of variables**, for a nonnegative
alphabet: the tableaux bounded by `n` are among those bounded by `m`. -/
theorem skewSchur_mono {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) (h : n ≤ m) :
    skewSchur lam mu n x ≤ skewSchur lam mu m x := by
  classical
  rw [skewSchur, skewSchur]
  have himg : ∑ T : BoundedSkewSSYT lam mu n, ∏ c ∈ skewCells lam mu, x (T c.1 c.2)
      = ∑ T ∈ Finset.image (widenBound h) Finset.univ,
          ∏ c ∈ skewCells lam mu, x (T c.1 c.2) :=
    (Finset.sum_image (g := widenBound (lam := lam) (mu := mu) h)
      (f := fun T : BoundedSkewSSYT lam mu m => ∏ c ∈ skewCells lam mu, x (T c.1 c.2))
      (fun T _ T' _ hTT' => widenBound_injective h hTT')).symm
  rw [himg]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun T _ _ => Finset.prod_nonneg fun c _ => hx _)

/-! ### The bound -/

/-- A bounded skew tableau is determined by its entries on the skew cells. -/
theorem restrictNat_injective (lam mu : YoungDiagram) (n : ℕ) :
    Function.Injective fun (T : BoundedSkewSSYT lam mu n) (c : skewCells lam mu) =>
      T c.1.1 c.1.2 := by
  intro T T' h
  refine BoundedSkewSSYT.ext fun i j => ?_
  by_cases hc : (i, j) ∈ skewCells lam mu
  · exact congrFun h ⟨(i, j), hc⟩
  · rw [T.zeros hc, T'.zeros hc]

/-- **The tableau bound.**  A skew Schur function in `n` nonnegative variables is at most
`(∑_{i<n} x_i)` raised to the number of skew cells: the tableaux inject into the
functions from the skew cells to `{0,…,n-1}`, and summing the weight over *all* those
functions gives the product of the sums. -/
theorem skewSchur_le_pow {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) (lam mu : YoungDiagram) (n : ℕ) :
    skewSchur lam mu n x ≤ (∑ i ∈ Finset.range n, x i) ^ (skewCells lam mu).card := by
  rw [skewSchur]
  have hweight : ∀ T : BoundedSkewSSYT lam mu n,
      ∏ c ∈ skewCells lam mu, x (T c.1 c.2)
        = ∏ c : skewCells lam mu, x (T c.1.1 c.1.2) :=
    fun T => (Finset.prod_coe_sort (skewCells lam mu) (fun c => x (T c.1 c.2))).symm
  have hstep : ∑ T : BoundedSkewSSYT lam mu n, ∏ c ∈ skewCells lam mu, x (T c.1 c.2)
      = ∑ f ∈ Finset.image
          (fun (T : BoundedSkewSSYT lam mu n) (c : skewCells lam mu) => T c.1.1 c.1.2)
          Finset.univ, ∏ c : skewCells lam mu, x (f c) := by
    rw [Finset.sum_image
      (g := fun (T : BoundedSkewSSYT lam mu n) (c : skewCells lam mu) => T c.1.1 c.1.2)
      (f := fun f : skewCells lam mu → ℕ => ∏ c : skewCells lam mu, x (f c))
      (fun T _ T' _ h => restrictNat_injective lam mu n h)]
    exact Finset.sum_congr rfl fun T _ => hweight T
  rw [hstep]
  have hsub : Finset.image
      (fun (T : BoundedSkewSSYT lam mu n) (c : skewCells lam mu) => T c.1.1 c.1.2)
      Finset.univ ⊆ Fintype.piFinset fun _ : skewCells lam mu => Finset.range n := by
    intro f hf
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hf
    exact Fintype.mem_piFinset.mpr fun c =>
      Finset.mem_range.mpr (T.lt_of_mem_cells c.2)
  calc ∑ f ∈ Finset.image
        (fun (T : BoundedSkewSSYT lam mu n) (c : skewCells lam mu) => T c.1.1 c.1.2)
        Finset.univ, ∏ c : skewCells lam mu, x (f c)
      ≤ ∑ f ∈ Fintype.piFinset fun _ : skewCells lam mu => Finset.range n,
          ∏ c : skewCells lam mu, x (f c) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun f _ _ => Finset.prod_nonneg fun c _ => hx _)
    _ = ∏ _c : skewCells lam mu, ∑ i ∈ Finset.range n, x i :=
        Finset.sum_prod_piFinset _ _
    _ = (∑ i ∈ Finset.range n, x i) ^ (skewCells lam mu).card := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-! ### The complete homogeneous symmetric function at an infinite alphabet -/

variable {β : ℕ → ℝ}

theorem completeHom_mono (hβ : ∀ i, 0 ≤ β i) (p : ℕ) :
    Monotone fun b => completeHom b p β := by
  intro b b' h
  exact skewSchur_mono hβ h

theorem card_skewCells_rect_bot (r s : ℕ) :
    (skewCells (rect r s) ⊥).card = r * s := by
  rw [skewCells_bot, cells_rect, Finset.card_product, Finset.card_range, Finset.card_range]

theorem completeHom_le_pow (hβ : ∀ i, 0 ≤ β i) (b p : ℕ) :
    completeHom b p β ≤ (∑ i ∈ Finset.range b, β i) ^ p := by
  have h := skewSchur_le_pow hβ (rect 1 p) ⊥ b
  rwa [card_skewCells_rect_bot, one_mul] at h

/-- **The infinite complete homogeneous symmetric function exists.**  For a summable
nonnegative alphabet the truncated `h_p` increase and are bounded by `(∑ β)^p`, so they
converge. -/
theorem tendsto_completeHom (hβ0 : ∀ i, 0 ≤ β i) (hβ : Summable β) (p : ℕ) :
    Tendsto (fun b => completeHom b p β) atTop (𝓝 (⨆ b, completeHom b p β)) := by
  refine tendsto_atTop_ciSup (completeHom_mono hβ0 p) ⟨(∑' i, β i) ^ p, ?_⟩
  rintro _ ⟨b, rfl⟩
  refine (completeHom_le_pow hβ0 b p).trans ?_
  refine pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => hβ0 i) ?_ p
  exact Summable.sum_le_tsum _ (fun i _ => hβ0 i) hβ


/-! ### Axiom footprint -/

/-- info: 'Shields.tendsto_completeHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_completeHom

end Shields
