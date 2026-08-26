/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.AngularBookkeeping
import ForgacsTran.PhaseCount

/-!
# The retained blocks of `eq:Omega-M`

`subsec:proof` counts on "each component of `Ω_M ∩ (α,β)`" and then sums.  This
module builds that family and proves the three facts the sum needs: the blocks
are ordered, they avoid every deleted window, and their lengths add up to the
retained length.

## Main statements

* `clampTo` and its four lemmas — projection onto `[A,b]`, monotone and
  `1`-Lipschitz, which is what keeps the telescoping exact while confining every
  endpoint to the trimmed interval.
* `blockLeft`, `blockRight` — the family, cut at the deleted windows.
* `sum_blockLength` — the telescoping identity, and `sum_blockLength_ge` the
  bound `|Ω_M ∩ (α,β)| ≥ (b - A) - 2ρJ` it gives.
* `block_avoid` — a nondegenerate block meets no deleted window.
* `exists_blockZeros` — the per-block application of
  `PhaseCount.exists_interiorZeros_of_dominance_Ioo`, with the counts, the root
  sets and their pairwise disjointness.

## Implementation notes

**One radius, not `J` of them.**  `eq:amplitude-deletion` gives the window at
`θ_j` the half-width `e^{-cM/ν_j}`, which varies with the multiplicity, and a
family of *nested* windows has no ordered block decomposition at all: the naive
cut at `θ_j ± ρ_j` produces a block sitting inside a wider neighbour's window,
where `eq:dominance-bound` says nothing.  Every window is therefore taken at the
largest half-width `e^{-cM/N}`, `N = max_j ν_j`, which contains all of them —
that is `AngularBookkeeping.windowRadius_le`, and it is the reason that lemma
exists.  The enlarged family is still exponentially small, so
`eq:amplitude-window-negligible` is unaffected.

**The clamp is what makes the sum exact.**  A window straddling `α` or `π/r`
puts a cut point outside the trimmed interval, and the block beyond it would
then carry positive length with no dominance bound behind it.  Projecting every
cut point into `[A,b]` fixes that, and it costs nothing: the projection is
`1`-Lipschitz, so the deleted length is still at most `2ρ` per window, and it is
monotone, so the blocks stay ordered.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Angular discrepancy and
proof of the main theorem» (`subsec:proof`, `eq:Omega-M`,
`eq:angular-distinct-lower`).

## Tags

angular discrepancy, retained blocks, zero counting
-/

namespace ForgacsTran

open Set

/-! ### The projection onto the trimmed interval -/

/-- Projection of `x` onto `[A, b]`. -/
noncomputable def clampTo (A b x : ℝ) : ℝ := min b (max A x)

theorem clampTo_le (A b x : ℝ) : clampTo A b x ≤ b := min_le_left _ _

theorem le_clampTo {A b : ℝ} (hAb : A ≤ b) (x : ℝ) : A ≤ clampTo A b x :=
  le_min hAb (le_max_left _ _)

theorem clampTo_mono (A b : ℝ) : Monotone (clampTo A b) := fun _ _ h =>
  min_le_min le_rfl (max_le_max le_rfl h)

/-- The projection is `1`-Lipschitz, which is what caps a deleted window's
contribution at its own length however far outside `[A,b]` it reaches. -/
theorem clampTo_sub_le (A b : ℝ) {x y : ℝ} (hxy : x ≤ y) :
    clampTo A b y - clampTo A b x ≤ y - x := by
  have hmax : max A y - max A x ≤ y - x := by
    rcases le_total A y with h | h
    · rw [max_eq_right h]
      have := le_max_right A x
      linarith
    · have hx : max A x = A := max_eq_left (le_trans hxy h)
      rw [max_eq_left h, hx]
      linarith
  have hxle : max A x ≤ max A y := max_le_max le_rfl hxy
  have hmin : min b (max A y) - min b (max A x) ≤ max A y - max A x := by
    rcases le_total b (max A x) with h | h
    · rw [min_eq_left h, min_eq_left (le_trans h hxle)]
      linarith
    · rw [min_eq_right h]
      rcases le_total b (max A y) with h' | h'
      · rw [min_eq_left h']
        linarith
      · rw [min_eq_right h']
  simp only [clampTo]
  linarith

/-- Inside the interval the projection is the identity. -/
theorem clampTo_eq_self {A b x : ℝ} (h1 : A ≤ x) (h2 : x ≤ b) : clampTo A b x = x := by
  simp [clampTo, max_eq_right h1, min_eq_right h2]

/-! ### The block family -/

/-- The left endpoint of the `i`-th retained block: the right edge of the
`(i-1)`-st deleted window, projected into `[A,b]`, with the trimmed interval's
own left endpoint opening the family. -/
noncomputable def blockLeft (A b ρ : ℝ) (e : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then A else clampTo A b (e (i - 1) + ρ)

/-- The right endpoint of the `i`-th retained block: the left edge of the `i`-th
deleted window, projected into `[A,b]`, with the trimmed interval's own right
endpoint closing the family. -/
noncomputable def blockRight (A b ρ : ℝ) (e : ℕ → ℝ) (J i : ℕ) : ℝ :=
  if i = J then b else clampTo A b (e i - ρ)

theorem blockLeft_mem {A b ρ : ℝ} (hAb : A ≤ b) (e : ℕ → ℝ) (i : ℕ) :
    blockLeft A b ρ e i ∈ Icc A b := by
  unfold blockLeft
  split
  · exact ⟨le_rfl, hAb⟩
  · exact ⟨le_clampTo hAb _, clampTo_le _ _ _⟩

theorem blockRight_mem {A b ρ : ℝ} (hAb : A ≤ b) (e : ℕ → ℝ) (J i : ℕ) :
    blockRight A b ρ e J i ∈ Icc A b := by
  unfold blockRight
  split
  · exact ⟨hAb, le_rfl⟩
  · exact ⟨le_clampTo hAb _, clampTo_le _ _ _⟩

/-- **The telescoping identity.**  Summing the block lengths recovers the length
of the trimmed interval less the projected length of each deleted window. -/
theorem sum_blockLength {A b ρ : ℝ} (e : ℕ → ℝ) (J : ℕ) :
    ∑ i ∈ Finset.range (J + 1),
        (blockRight A b ρ e J i - blockLeft A b ρ e i)
      = (b - A)
        - ∑ i ∈ Finset.range J, (clampTo A b (e i + ρ) - clampTo A b (e i - ρ)) := by
  rw [Finset.sum_sub_distrib]
  have hR : ∑ i ∈ Finset.range (J + 1), blockRight A b ρ e J i
      = (∑ i ∈ Finset.range J, clampTo A b (e i - ρ)) + b := by
    rw [Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have : i ≠ J := Nat.ne_of_lt (Finset.mem_range.1 hi)
      simp [blockRight, this]
    · simp [blockRight]
  have hL : ∑ i ∈ Finset.range (J + 1), blockLeft A b ρ e i
      = (∑ i ∈ Finset.range J, clampTo A b (e i + ρ)) + A := by
    rw [Finset.sum_range_succ']
    congr 1
  rw [hR, hL, Finset.sum_sub_distrib]
  ring

/-- **`|Ω_M ∩ (α,β)|` from below.**  Each deleted window costs at most its own
length, so the retained length is the trimmed length less `2ρJ`. -/
theorem sum_blockLength_ge {A b ρ : ℝ} (hρ : 0 ≤ ρ) (e : ℕ → ℝ) (J : ℕ) :
    (b - A) - 2 * ρ * J
      ≤ ∑ i ∈ Finset.range (J + 1),
          (blockRight A b ρ e J i - blockLeft A b ρ e i) := by
  rw [sum_blockLength]
  have hstep : ∀ i ∈ Finset.range J,
      clampTo A b (e i + ρ) - clampTo A b (e i - ρ) ≤ 2 * ρ := by
    intro i _
    have := clampTo_sub_le A b (x := e i - ρ) (y := e i + ρ) (by linarith)
    linarith
  have := Finset.sum_le_sum hstep
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hcast : (J : ℝ) * (2 * ρ) = 2 * ρ * J := by ring
  rw [hcast] at this
  linarith

/-! ### The blocks are ordered -/

theorem blockLeft_mono {A b ρ : ℝ} (hAb : A ≤ b) {e : ℕ → ℝ} {J : ℕ}
    (he : ∀ i j, i < j → j < J → e i ≤ e j) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ J) :
    blockLeft A b ρ e i ≤ blockLeft A b ρ e j := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa [blockLeft] using (blockLeft_mem (ρ := ρ) hAb e j).1
  have hj0 : j ≠ 0 := by omega
  have hi0 : i ≠ 0 := by omega
  simp only [blockLeft, hi0, hj0, if_false]
  refine clampTo_mono A b ?_
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have : e (i - 1) ≤ e (j - 1) := by
      rcases Nat.lt_or_ge (i - 1) (j - 1) with h | h
      · exact he _ _ h (by omega)
      · have : i - 1 = j - 1 := by omega
        rw [this]
    linarith

theorem blockRight_mono {A b ρ : ℝ} (hAb : A ≤ b) {e : ℕ → ℝ} {J : ℕ}
    (he : ∀ i j, i < j → j < J → e i ≤ e j) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ J) :
    blockRight A b ρ e J i ≤ blockRight A b ρ e J j := by
  rcases eq_or_lt_of_le hj with hjeq | hjJ
  · have hb : blockRight A b ρ e J j = b := by simp [blockRight, hjeq]
    rw [hb]
    exact (blockRight_mem (ρ := ρ) hAb e J i).2
  have hiJ : i ≠ J := by omega
  have hjJ' : j ≠ J := by omega
  simp only [blockRight, hiJ, hjJ', if_false]
  refine clampTo_mono A b ?_
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have : e i ≤ e j := he _ _ hlt hjJ
    linarith

/-- Consecutive blocks are separated by the window between them. -/
theorem blockRight_le_blockLeft_succ {A b ρ : ℝ} (hρ : 0 ≤ ρ) (e : ℕ → ℝ) {J i : ℕ}
    (hi : i < J) :
    blockRight A b ρ e J i ≤ blockLeft A b ρ e (i + 1) := by
  have h1 : i ≠ J := Nat.ne_of_lt hi
  simp only [blockRight, blockLeft, h1, if_false, Nat.succ_ne_zero, Nat.add_sub_cancel]
  exact clampTo_mono A b (by linarith)

/-- The blocks are ordered end to end, which is both the disjointness the count
needs and the `hord` input of
`PhaseVariation.linear_phase_variation_components`. -/
theorem blockRight_le_blockLeft {A b ρ : ℝ} (hAb : A ≤ b) (hρ : 0 ≤ ρ) {e : ℕ → ℝ}
    {J : ℕ} (he : ∀ i j, i < j → j < J → e i ≤ e j) {i j : ℕ} (hij : i < j)
    (hj : j ≤ J) :
    blockRight A b ρ e J i ≤ blockLeft A b ρ e j :=
  le_trans (blockRight_le_blockLeft_succ hρ e (by omega))
    (blockLeft_mono hAb he (by omega) hj)

/-! ### A nondegenerate block avoids every deleted window -/

/-- Below the ceiling the projection does not move a point down. -/
theorem le_clampTo_of_lt {A b x : ℝ} (h : clampTo A b x < b) : x ≤ clampTo A b x := by
  simp only [clampTo] at h ⊢
  rcases le_total (max A x) b with h1 | h1
  · rw [min_eq_right h1]; exact le_max_right _ _
  · rw [min_eq_left h1] at h; exact absurd h (lt_irrefl b)

/-- Above the floor the projection does not move a point up. -/
theorem clampTo_le_of_lt {A b x : ℝ} (hAb : A ≤ b) (h : A < clampTo A b x) :
    clampTo A b x ≤ x := by
  simp only [clampTo] at h ⊢
  rcases le_total x A with h1 | h1
  · rw [max_eq_left h1, min_eq_right hAb] at h; exact absurd h (lt_irrefl A)
  · rw [max_eq_right h1]; exact min_le_right _ _

/-- **`eq:Omega-M`.**  A block of positive length carries no point of any deleted
window, so `eq:dominance-bound` holds across it.

Degenerate blocks are not exempted by fiat — they are excluded, because the
projection can collapse a block onto an endpoint that a straddling window
covers.  Such a block carries no count and none is asked of it. -/
theorem block_avoid {A b ρ : ℝ} (hAb : A ≤ b) (hρ : 0 < ρ) {e : ℕ → ℝ} {J : ℕ}
    (he : ∀ i j, i < j → j < J → e i ≤ e j) {i : ℕ} (hi : i ≤ J)
    (hlt : blockLeft A b ρ e i < blockRight A b ρ e J i)
    {θ : ℝ} (hθ : θ ∈ Icc (blockLeft A b ρ e i) (blockRight A b ρ e J i))
    {j : ℕ} (hj : j < J) :
    ρ ≤ |θ - e j| := by
  rcases Nat.lt_or_ge j i with hji | hji
  · -- a window to the left of the block: the block starts at or beyond its right edge
    have hi0 : i ≠ 0 := by omega
    have hbelow : e j ≤ e (i - 1) := by
      rcases Nat.lt_or_ge j (i - 1) with h | h
      · exact he _ _ h (by omega)
      · have hij : j = i - 1 := by omega
        rw [hij]
    have hLform : blockLeft A b ρ e i = clampTo A b (e (i - 1) + ρ) := by
      simp [blockLeft, hi0]
    have hLb : blockLeft A b ρ e i < b :=
      lt_of_lt_of_le hlt (blockRight_mem (ρ := ρ) hAb e J i).2
    have hge : e (i - 1) + ρ ≤ blockLeft A b ρ e i := by
      rw [hLform]; exact le_clampTo_of_lt (by rw [← hLform]; exact hLb)
    have : ρ ≤ θ - e j := by
      have := hθ.1; linarith
    rw [abs_of_nonneg (by linarith)]
    linarith
  · -- a window to the right of the block: the block ends at or before its left edge
    have hiJ : i ≠ J := by omega
    have habove : e i ≤ e j := by
      rcases eq_or_lt_of_le hji with h | h
      · rw [h]
      · exact he _ _ h hj
    have hRform : blockRight A b ρ e J i = clampTo A b (e i - ρ) := by
      simp [blockRight, hiJ]
    have hRA : A < blockRight A b ρ e J i :=
      lt_of_le_of_lt (blockLeft_mem (ρ := ρ) hAb e i).1 hlt
    have hle : blockRight A b ρ e J i ≤ e i - ρ := by
      rw [hRform]; exact clampTo_le_of_lt hAb (by rw [← hRform]; exact hRA)
    have : ρ ≤ e j - θ := by
      have := hθ.2; linarith
    rw [abs_of_nonpos (by linarith)]
    linarith

/-! ### The per-block count

`PhaseCount.exists_interiorZeros_of_dominance_Ioo` on one block, under the
dichotomy the sum needs: a block whose phase turns by at least `π` carries the
count `eq:angular-distinct-lower` asks of it, and a block that turns by less
carries none — and none is asked, because `(M+1)|ℐ|/π - Var_ℐψ/π - 2` is then
negative.  That is the whole reason the paper's `-2` is there and not a `-1`. -/

/-- Blocks laid end to end have disjoint open `z`-images, so no zero is counted
twice. -/
theorem notMem_ofReal_Ioo {u v u' v' : ℝ} (h : v ≤ u') {w : ℂ}
    (hw : w ∈ Complex.ofReal '' Set.Ioo u v) : w ∉ Complex.ofReal '' Set.Ioo u' v' := by
  rintro ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ := hw
  have : x = y := by exact_mod_cast hxy
  rw [this] at hx
  exact absurd (lt_of_lt_of_le hx.2 (le_trans h hy.1.le)) (lt_irrefl _)

/-- **`eq:angular-distinct-lower` on one block.**  From `eq:principal-decomposition`
and `eq:dominance-bound` on the retained set, each block of the family carries at
least `(M+1)|ℐ|/π - Var_ℐψ/π - 2` distinct zeros of the coefficient polynomial,
strictly inside its own `z`-image.

The branch `ψ i` is per block, which is what `lem:amplitude-divisor` forces: `arg W`
has no continuous branch across a zero of the amplitude.  The *bound* on the
variation is not per block — `varψ` is a function here and nothing constrains its
sum, which is imposed where the constants are built.

`eq:phase-derivative-bound` enters **pointwise**, as `|ψ'| < M+1` on each block,
not as a uniform `κ` with `κ < M+1` beside it.  The retained range moves with
`M`, so a `κ` obtained by compactness on it is a `κ_M` and the uniform form
turns a threshold on `M` into a growth claim about `κ_M`
(`AngularBookkeeping.strictMonoOn_phase_lt`). -/
theorem exists_blockZeros {k M : ℕ}
    {P : Polynomial ℝ} {z τ Rm : ℝ → ℝ} {W : ℝ → ℂ} {ψ dψ : Fin k → ℝ → ℝ}
    {Lb Rb varψ : Fin k → ℝ} {Ret : Set ℝ} {A b : ℝ}
    (hLmem : ∀ i, Lb i ∈ Icc A b) (hRmem : ∀ i, Rb i ∈ Icc A b)
    (hret : ∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ret)
    (hzmono : StrictMonoOn z (Icc A b))
    (hτ : ∀ θ ∈ Icc A b, 0 < τ θ)
    (hWne : ∀ θ ∈ Ret, W θ ≠ 0)
    (hpolar : ∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
      W θ = (‖W θ‖ : ℂ) * Complex.exp ((ψ i θ : ℂ) * Complex.I))
    (hdec : ∀ θ ∈ Icc A b, τ θ * P.eval (z θ)
      = 2 * (W θ * Complex.exp (-((((M : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I)).re + Rm θ)
    (hdomb : ∀ θ ∈ Ret, |Rm θ| ≤ ‖W θ‖ / 2)
    (hψd : ∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ)
    (hκ : ∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1)
    (hvarnn : ∀ i, 0 ≤ varψ i)
    (hvar : ∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) :
    ∀ i : Fin k, ∃ (n : ℕ) (Z : Finset ℂ),
      ((M : ℝ) + 1) * (Rb i - Lb i) / Real.pi - varψ i / Real.pi - 2 ≤ (n : ℝ) ∧
      n ≤ Z.card ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' Set.Ioo (z (Lb i)) (z (Rb i))) := by
  intro i
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  by_cases hturn : Real.pi ≤ ((M : ℝ) + 1) * (Rb i - Lb i) - varψ i
  · have hlen : 0 < Rb i - Lb i := by nlinarith [hvarnn i]
    have hab : Lb i ≤ Rb i := by linarith
    have hΦdef : ∀ θ ∈ Icc (Lb i) (Rb i),
        (fun θ => ((M : ℝ) + 1) * θ - ψ i θ) θ = ((M : ℝ) + 1) * θ - ψ i θ :=
      fun _ _ => rfl
    have hnd : Lb i < Rb i := by linarith
    have hcont := continuousOn_phase_congr (M := M) hΦdef (hψd i hnd)
    have hmono := strictMonoOn_phase_congr_lt (M := M) hΦdef (hψd i hnd) (hκ i hnd)
    have hincr : ψ i (Rb i) - ψ i (Lb i) ≤ varψ i :=
      le_trans (le_abs_self _) (hvar i hnd)
    have hΦ : ((M : ℝ) + 1) * (Rb i - Lb i) - varψ i
        ≤ (fun θ => ((M : ℝ) + 1) * θ - ψ i θ) (Rb i)
          - (fun θ => ((M : ℝ) + 1) * θ - ψ i θ) (Lb i) := by
      simp only
      nlinarith [hincr]
    have hsub : Icc (Lb i) (Rb i) ⊆ Icc A b :=
      Icc_subset_Icc (hLmem i).1 (hRmem i).2
    have hRetsub : Icc (Lb i) (Rb i) ⊆ Ret := hret i (by linarith)
    obtain ⟨n, Z, hn, hnZ, hZr, hZm⟩ :=
      exists_interiorZeros_of_dominance_Ioo (P := P) (z := z) (τ := τ) (Rm := Rm)
        (W := W) (φ := fun θ => ((M : ℝ) + 1) * θ) (ψ := ψ i)
        (Φ := fun θ => ((M : ℝ) + 1) * θ - ψ i θ)
        (L := ((M : ℝ) + 1) * (Rb i - Lb i) - varψ i)
        hab hcont hmono hturn hΦ hΦdef (hzmono.mono hsub)
        (fun θ hθ => hτ θ (hsub hθ)) (fun θ hθ => hWne θ (hRetsub hθ))
        (hpolar i hnd) (fun θ hθ => hdec θ (hsub hθ))
        (fun θ hθ => hdomb θ (hRetsub hθ))
    refine ⟨n, Z, ?_, hnZ, hZr, hZm⟩
    have hsplit : (((M : ℝ) + 1) * (Rb i - Lb i) - varψ i) / Real.pi - 2
        = ((M : ℝ) + 1) * (Rb i - Lb i) / Real.pi - varψ i / Real.pi - 2 := by
      field_simp
    linarith [hsplit ▸ hn]
  · refine ⟨0, ∅, ?_, by simp, by simp, by simp⟩
    push Not at hturn
    have h1 : (((M : ℝ) + 1) * (Rb i - Lb i) - varψ i) / Real.pi < 1 := by
      rw [div_lt_one hπ]; exact hturn
    have hsplit : (((M : ℝ) + 1) * (Rb i - Lb i) - varψ i) / Real.pi
        = ((M : ℝ) + 1) * (Rb i - Lb i) / Real.pi - varψ i / Real.pi := by
      field_simp
    rw [hsplit] at h1
    push_cast
    linarith

end ForgacsTran
