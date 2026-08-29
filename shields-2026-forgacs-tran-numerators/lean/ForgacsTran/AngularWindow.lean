/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.AngularBlocks
import ForgacsTran.AngularDiscrepancy
import ForgacsTran.ConsequencesComposition

/-!
# `eq:angular-distinct-lower` on an angular window

`AngularBlocks` builds the retained blocks of `eq:Omega-M` and counts on each;
`AngularDiscrepancy` prices the sum.  This module runs the two together and
delivers the manuscript's own left-hand side: a `Finset` of distinct zeros of the
coefficient polynomial inside `z(I_{α,β})`, of cardinality at least

  `(M+1)(β-α)/π - C₀ - C₁K`,  `C₀ = (4h+1+κ₀)/π + 2`,  `C₁ = κ₁/π + 2`.

## Main statements

* `exists_windowZeros` — `eq:angular-distinct-lower`, with the blocks built and
  the correction priced.
* `abs_windowCount_sub_le` — `eq:angular-discrepancy`, the two-sided bound, from
  the lower bound on the window and on the two complementary windows.

## Implementation notes

**Where the uniformity is discharged.**  `h`, `κ₀` and `κ₁` are parameters of
both theorems, so neither carries the uniformity on its own — a caller may
instantiate them at quantities that see the weight and the statements stay true.
What they contribute is that the correction assembles into `C₀ + C₁K` with `K`
appearing only as a multiplier.  The uniformity is the binder order at the
producer of `ConsequencesComposition.FTAngularDiscrepancy`, where `h` comes from
`thm:weighted-dominance` and `κ₀`, `κ₁` from `cor:linear-phase-variation`, all
before the weight is quantified.

**The trimmed window may be empty, and that is a case, not an edge case.**  When
`β - α` is below the endpoint collar `2h/M` there is no retained block at all.
The bound still holds, and for the reason the collar was priced at `4h` in the
first place: `(M+1)(β-α)/π` is then under `4h/π`, which `C₀` already carries.
Nothing is assumed about `α` and `β` beyond `0 ≤ α ≤ β ≤ π/r`.

**The branch enters as a supply over families, not as one function.**
`lem:amplitude-divisor` gives `arg W` no continuous branch across an amplitude
zero, so there is no single `ψ` on `(α,β)`; what `cor:linear-phase-variation`
bounds is the *summed* variation over the components.  `hbranch` below is that
statement — one branch per block, and one bound on the sum — and it is why the
quadratic trap `(J+1)(κ₀ + κ₁K)` cannot be expressed here.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Angular discrepancy and
proof of the main theorem» (`subsec:proof`, `prop:angular-discrepancy`,
`eq:Omega-M`, `eq:angular-distinct-lower`, `eq:angular-discrepancy`).

## Tags

angular discrepancy, zero counting, retained blocks
-/

namespace ForgacsTran

open Set Real

/-- **`eq:angular-distinct-lower`.**  The distinct zeros of the coefficient
polynomial inside the angular window `z(I_{α,β})`, at least
`(M+1)(β-α)/π - C₀ - C₁K` of them, built by the phase count on each retained
block of `eq:Omega-M` and summed.

`e` enumerates the amplitude zeros of `lem:amplitude-divisor` in increasing
order and `ρ` is the common half-width of `eq:amplitude-deletion` — common,
because a nested family of windows has no ordered block decomposition
(`AngularBlocks`).  `hwin` is `eq:amplitude-window-negligible`. -/
theorem exists_windowZeros
    {P : Polynomial ℝ} {z τ Rm : ℝ → ℝ} {W : ℝ → ℂ} {e : ℕ → ℝ} {Ret : Set ℝ}
    {J M K : ℕ} {ρ hcol κ₀ κ₁ bnd α β : ℝ}
    (hM : 1 ≤ M) (hh : 0 < hcol) (hρ : 0 < ρ)
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ bnd)
    (hJK : J ≤ K) (hwin : ((M : ℝ) + 1) * (2 * ρ * J) ≤ 1)
    (he : ∀ i j, i < j → j < J → e i ≤ e j)
    (hzmono : StrictMonoOn z (Ioo 0 bnd)) (hzcont : ContinuousOn z (Ioo 0 bnd))
    (hτ : ∀ θ ∈ Ioo 0 bnd, 0 < τ θ)
    (hRet : ∀ θ, hcol / M ≤ θ → θ ≤ bnd - hcol / M →
      (∀ j, j < J → ρ ≤ |θ - e j|) → θ ∈ Ret)
    (hWne : ∀ θ ∈ Ret, W θ ≠ 0)
    (hdomb : ∀ θ ∈ Ret, |Rm θ| ≤ ‖W θ‖ / 2)
    (hdec : ∀ θ ∈ Ioo 0 bnd, τ θ * P.eval (z θ)
      = 2 * (W θ * Complex.exp (-((((M : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I)).re + Rm θ)
    (hκ₀ : 0 ≤ κ₀) (hκ₁ : 0 ≤ κ₁)
    (hbranch : ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc 0 bnd) → (∀ i, Rb i ∈ Icc 0 bnd) →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ret) →
      ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          W θ = (‖W θ‖ : ℂ) * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
        (∀ i, 0 ≤ varψ i) ∧
        (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
        ∑ i, varψ i ≤ κ₀ + κ₁ * K) :
    ∃ Z : Finset ℂ,
      ((M : ℝ) + 1) * (β - α) / π - ((4 * hcol + 1 + κ₀) / π + 2) - (κ₁ / π + 2) * K
          ≤ (Z.card : ℝ) ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ ftWindow z α β) := by
  classical
  have hπ : (0 : ℝ) < π := pi_pos
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le one_pos hMR
  have hcolpos : (0 : ℝ) < hcol / M := by positivity
  have hcolnn : (0 : ℝ) ≤ hcol / M := hcolpos.le
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  set A : ℝ := max α (hcol / M) with hA
  set Bd : ℝ := min β (bnd - hcol / M) with hBd
  by_cases hAB : A ≤ Bd
  · -- the trimmed window carries blocks
    have hαA : α ≤ A := le_max_left _ _
    have hcA : hcol / M ≤ A := le_max_right _ _
    have hBβ : Bd ≤ β := min_le_left _ _
    have hBc : Bd ≤ bnd - hcol / M := min_le_right _ _
    have hA0 : 0 < A := lt_of_lt_of_le hcolpos hcA
    have hBb : Bd < bnd := lt_of_le_of_lt hBc (by linarith)
    have hsub0 : Icc A Bd ⊆ Ioo 0 bnd := fun _ hx =>
      ⟨lt_of_lt_of_le hA0 hx.1, lt_of_le_of_lt hx.2 hBb⟩
    have hsubc : Icc A Bd ⊆ Icc 0 bnd := fun _ hx => Ioo_subset_Icc_self (hsub0 hx)
    set k : ℕ := J + 1 with hk
    set Lb : Fin k → ℝ := fun i => blockLeft A Bd ρ e (i : ℕ) with hLb
    set Rb : Fin k → ℝ := fun i => blockRight A Bd ρ e J (i : ℕ) with hRb
    have hLmem : ∀ i, Lb i ∈ Icc A Bd := fun i => blockLeft_mem (ρ := ρ) hAB e _
    have hRmem : ∀ i, Rb i ∈ Icc A Bd := fun i => blockRight_mem (ρ := ρ) hAB e J _
    have hord : ∀ i j : Fin k, i < j → Rb i ≤ Lb j := fun i j hij =>
      blockRight_le_blockLeft hAB hρ.le he (Fin.lt_def.1 hij) (Nat.lt_succ_iff.1 j.isLt)
    have hret : ∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ret := by
      intro i hlt θ hθ
      refine hRet θ (le_trans hcA (le_trans (hLmem i).1 hθ.1))
        (le_trans (le_trans hθ.2 (hRmem i).2) hBc) fun j hj => ?_
      exact block_avoid hAB hρ he (Nat.lt_succ_iff.1 i.isLt) hlt hθ hj
    obtain ⟨ψ, dψ, varψ, hpolar, hψd, hκ, hvarnn, hvar, hvarsum⟩ :=
      hbranch k Lb Rb (fun i => hsubc (hLmem i)) (fun i => hsubc (hRmem i)) hord hret
    have hblk := exists_blockZeros (M := M) (P := P) (z := z) (τ := τ) (Rm := Rm)
      (W := W) (ψ := ψ) (dψ := dψ) (Lb := Lb) (Rb := Rb) (varψ := varψ) (Ret := Ret)
      (A := A) (b := Bd) hLmem hRmem hret (hzmono.mono hsub0)
      (fun θ hθ => hτ θ (hsub0 hθ)) hWne hpolar (fun θ hθ => hdec θ (hsub0 hθ)) hdomb
      hψd hκ hvarnn hvar
    choose n Zb hn hnZ hZr hZm using hblk
    -- the retained length, from the telescoping sum of the blocks
    have hAle : A ≤ α + hcol / M := max_le (by linarith) (by linarith)
    have hBge : β - hcol / M ≤ Bd := le_min (by linarith) (by linarith)
    have hlensum : β - α - (2 * hcol / M + 2 * ρ * J) ≤ ∑ i, (Rb i - Lb i) := by
      have hfin : ∑ i, (Rb i - Lb i)
          = ∑ i ∈ Finset.range (J + 1),
              (blockRight A Bd ρ e J i - blockLeft A Bd ρ e i) :=
        Fin.sum_univ_eq_sum_range
          (fun i => blockRight A Bd ρ e J i - blockLeft A Bd ρ e i) (J + 1)
      rw [hfin]
      have := sum_blockLength_ge (A := A) (b := Bd) (ρ := ρ) hρ.le e J
      have hdouble : 2 * hcol / M = hcol / M + hcol / M := by ring
      linarith
    have hkK : ((J + 1 : ℕ) : ℝ) ≤ (K : ℝ) + 1 := by
      have : (J : ℝ) ≤ (K : ℝ) := by exact_mod_cast hJK
      push_cast
      linarith
    have hcount := angular_count_lower_uniform (n := n) (len := fun i => Rb i - Lb i)
      (varψ := varψ) (M := M) (K := K) (α := α) (β := β) (h := hcol) (κ₀ := κ₀)
      (κ₁ := κ₁) (collar := 2 * hcol / M) (windows := 2 * ρ * J) hh.le hM hn hlensum
      (by rw [mul_div_assoc]) (by positivity) hwin hvarsum hkK
    -- the block zero sets are pairwise disjoint, so they add
    have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin k)), ∀ j ∈ (Finset.univ : Finset (Fin k)),
        i ≠ j → Disjoint (Zb i) (Zb j) := by
      have key : ∀ i j : Fin k, i < j → Disjoint (Zb i) (Zb j) := by
        intro i j hij
        refine Finset.disjoint_left.2 fun w hwi hwj => ?_
        have hzle : z (Rb i) ≤ z (Lb j) :=
          hzmono.monotoneOn (hsub0 (hRmem i)) (hsub0 (hLmem j)) (hord i j hij)
        exact notMem_ofReal_Ioo hzle (hZm i w hwi) (hZm j w hwj)
      intro i _ j _ hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact key i j h
      · exact (key j i h).symm
    refine ⟨Finset.univ.biUnion Zb, ?_, ?_, ?_⟩
    · have hcard : (Finset.univ.biUnion Zb).card = ∑ i, (Zb i).card :=
        Finset.card_biUnion hdisj
      have hsum : ∑ i, (n i : ℝ) ≤ ((∑ i, (Zb i).card : ℕ) : ℝ) := by
        have : ∑ i, n i ≤ ∑ i, (Zb i).card := Finset.sum_le_sum fun i _ => hnZ i
        calc ∑ i, (n i : ℝ) = ((∑ i, n i : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((∑ i, (Zb i).card : ℕ) : ℝ) := by exact_mod_cast this
      rw [hcard]
      linarith
    · intro w hw
      obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.1 hw
      exact hZr i w hwi
    · intro w hw
      obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.1 hw
      obtain ⟨x, hx, rfl⟩ := hZm i w hwi
      -- `eq:angular-subinterval` on the block, not on the whole window: the block is a
      -- compact subinterval of the *open* arc, so nothing is asked of `z` at either end
      have hLR : Lb i ≤ Rb i := by
        by_contra hcon
        exact absurd (hzmono.monotoneOn (hsub0 (hRmem i)) (hsub0 (hLmem i))
          (not_le.1 hcon).le) (not_le.2 (lt_trans hx.1 hx.2))
      have hblk : Icc (Lb i) (Rb i) ⊆ Ioo 0 bnd := fun _ hy =>
        hsub0 ⟨le_trans (hLmem i).1 hy.1, le_trans hy.2 (hRmem i).2⟩
      have himg : z '' Ioo (Lb i) (Rb i) = Ioo (z (Lb i)) (z (Rb i)) :=
        image_Ioo_eq_Ioo (hzmono.mono hblk) (hzcont.mono hblk) le_rfl hLR le_rfl
      have hsubw : z '' Ioo (Lb i) (Rb i) ⊆ z '' Ioo α β :=
        subset_ftInterval_image (le_trans hαA (hLmem i).1) (le_trans (hRmem i).2 hBβ)
      rw [← himg] at hx
      exact ⟨x, hsubw hx, rfl⟩
  · -- the collar swallows the window
    refine ⟨∅, ?_, by simp, by simp⟩
    have hd2 : 2 * hcol / M = hcol / M + hcol / M := by ring
    have hgap : β - α ≤ 2 * hcol / M := by
      have hlt : Bd < A := lt_of_not_ge hAB
      rw [hA, hBd] at hlt
      rcases le_total β (bnd - hcol / M) with hb | hb <;>
        rcases le_total α (hcol / M) with ha | ha
      · rw [min_eq_left hb, max_eq_right ha] at hlt; linarith
      · rw [min_eq_left hb, max_eq_left ha] at hlt; linarith
      · rw [min_eq_right hb, max_eq_right ha] at hlt; linarith
      · rw [min_eq_right hb, max_eq_left ha] at hlt; linarith
    have hprod : ((M : ℝ) + 1) * (β - α) ≤ 4 * hcol := by
      have hMp : (0 : ℝ) < (M : ℝ) + 1 := by linarith
      have h1 : ((M : ℝ) + 1) * (β - α) ≤ ((M : ℝ) + 1) * (2 * hcol / M) :=
        mul_le_mul_of_nonneg_left hgap hMp.le
      refine le_trans h1 ?_
      rw [mul_div_assoc', div_le_iff₀ hMpos]
      nlinarith [hh.le, hMR]
    have h2 : ((M : ℝ) + 1) * (β - α) / π ≤ (4 * hcol + 1 + κ₀) / π := by
      apply div_le_div_of_nonneg_right _ hπ.le
      linarith
    have h3 : (0 : ℝ) ≤ (κ₁ / π + 2) * K := by positivity
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

/-! ### The two-sided bound

`subsec:proof` gets `eq:angular-discrepancy` from `eq:angular-distinct-lower`
alone: the window's own lower bound is one half, and the same bound on the two
complementary windows, compared against `deg F_M`, is the other.  The
complementary zeros are genuinely new because `z` is injective across the arc —
`ConsequencesComposition.notMem_ftWindow`. -/

open scoped Classical in
/-- **`eq:angular-discrepancy`.**  The lower bound, applied to `(α,β)` and to the
two complementary intervals, gives the two-sided bound at twice the constants.

`hlower` is `eq:angular-distinct-lower` *uniformly in the window*, which is what
lets one hypothesis serve all three applications.  `exists_windowZeros` supplies
it, with `C₀` and `C₁` built from `h`, `κ₀`, `κ₁` alone. -/
theorem abs_windowCount_sub_le {Pc : Polynomial ℂ} {z : ℝ → ℝ} {M K : ℕ}
    {C₀ C₁ bnd α β : ℝ}
    (hP : Pc ≠ 0) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hzmono : StrictMonoOn z (Ioo 0 bnd))
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ bnd)
    (hdeg : (Pc.natDegree : ℝ) ≤ ((M : ℝ) + 1) * bnd / π)
    (hlower : ∀ α' β' : ℝ, 0 ≤ α' → α' ≤ β' → β' ≤ bnd →
      ∃ Z : Finset ℂ, ((M : ℝ) + 1) * (β' - α') / π - C₀ - C₁ * K ≤ (Z.card : ℝ) ∧
        (∀ w ∈ Z, Pc.IsRoot w) ∧ (∀ w ∈ Z, w ∈ ftWindow z α' β')) :
    |(Multiset.card ((Pc.roots).filter (· ∈ ftWindow z α β)) : ℝ)
        - ((M : ℝ) + 1) * (β - α) / π|
      ≤ 2 * C₀ + 2 * C₁ * K := by
  classical
  have hπ : (0 : ℝ) < π := pi_pos
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hbnd : 0 ≤ bnd := le_trans hα (le_trans hαβ hβ)
  obtain ⟨Zin, hZinc, hZinr, hZinm⟩ := hlower α β hα hαβ hβ
  obtain ⟨Zlo, hZloc, hZlor, hZlom⟩ := hlower 0 α le_rfl hα (le_trans hαβ hβ)
  obtain ⟨Zhi, hZhic, hZhir, hZhim⟩ := hlower β bnd (le_trans hα hαβ) hβ le_rfl
  have hin : ((M : ℝ) + 1) * (β - α) / π - (C₀ + C₁ * K)
      ≤ (Multiset.card ((Pc.roots).filter (· ∈ ftWindow z α β)) : ℝ) := by
    have hcard : (Zin.card : ℝ)
        ≤ (Multiset.card ((Pc.roots).filter (· ∈ ftWindow z α β)) : ℝ) := by
      exact_mod_cast card_le_count_filter hP _ hZinr hZinm
    linarith
  have hout : ((M : ℝ) + 1) * bnd / π - ((M : ℝ) + 1) * (β - α) / π
        - (2 * C₀ + 2 * C₁ * K)
      ≤ (Zlo.card : ℝ) + (Zhi.card : ℝ) := by
    have hsplit : ((M : ℝ) + 1) * (α - 0) / π + ((M : ℝ) + 1) * (bnd - β) / π
        = ((M : ℝ) + 1) * bnd / π - ((M : ℝ) + 1) * (β - α) / π := by
      field
    linarith
  have := ft_angular_discrepancy (P := Pc) hP
    (z := z) (a := 0) (b := bnd) (α := α) (β := β)
    (T := ((M : ℝ) + 1) * bnd / π) (Tab := ((M : ℝ) + 1) * (β - α) / π)
    (C₁ := C₀ + C₁ * K) (C₂ := 2 * C₀ + 2 * C₁ * K) (C₃ := 0)
    hzmono.injOn hα hαβ hβ hZlor hZlom hZhir hZhim hin hout (by linarith)
  refine le_trans this (max_le (by nlinarith) (by linarith))

end ForgacsTran
