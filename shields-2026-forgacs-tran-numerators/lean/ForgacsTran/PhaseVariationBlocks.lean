/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.PhaseVariation

/-!
# `cor:linear-phase-variation` in the block shape the supply states

`PhaseVariation.linear_phase_variation_components` sums the phase variation over an
ordered family indexed by a `Finset ℕ` of abstract sets;
`AngularDiscrepancyFT.FTPhaseSupply` states its variation clause over `Fin k` blocks
`[L i, R i]` and asks for real-valued `varψ i` rather than an `ENNReal` variation.
This module is the two conversions, and one bridge that the composition cannot do
without.

**The bridge is the point.**  The supply bundles six clauses about **one** `ψ`.  Two
different terms produce them.  The factorization, the differentiability and the
derivative bound come from a branch built on `W` itself --
`EndpointCofactorBound.exists_phase_branch_of_bound`, at `ViewingAngle.polarAngle W dW 0` --
while the variation bound comes from the branch written as the fixed factor's angle plus
one `ViewingAngle.polarAngle` per zero of `B`, which is the only form in which
`eq:linear-phase-variation`'s constants do not see `B`.  Each side type-checks alone
and nothing in a build compares them.  `sub_eq_sub_of_hasDerivAt_eq` is what does:
two branches of the same argument have the same **derivative** on a block, namely
`Im(W'/W)`, and two functions with one derivative on an interval have one increment.
That is a statement about logarithmic derivatives, not about polar decompositions,
and it is what the composition below consumes.

## Main statements

* `finExt`, `finExt_coe`, `sum_eVariationOn_finExt`, `finExtFun`, `finExtFun_coe`,
  `sum_eVariationOn_finExtFun` -- a `Fin k` family of sets, and of functions, extended past
  `k`, which is the whole of the index conversion.
* `sum_eVariationOn_branch_le` -- `exists_varPhase_of_blocks`'s `hroots` at one zero of
  `B`, in whichever of the two states that zero is in, off `ViewingAngle`'s ordered
  component bounds.
* `linear_phase_variation_components_fin` -- `linear_phase_variation_components` over
  `Fin k`, the supply's own index type.
* `exists_varPhase_of_blocks` -- the supply's three variation clauses, about the
  summed branch, with the constants `κ₀` and `κ₁ = 𝒦_γ + π` of
  `eq:linear-phase-variation`.
* `sub_eq_sub_of_hasDerivAt_eq` -- two functions with one derivative on `[a,b]` have
  one increment across it.
* `exists_varPhase_of_blocks_of_derivEq` -- the same three clauses about **any**
  family of branches whose derivatives agree with the summed branch's on each block,
  which is the form the supply consumes.

## Implementation notes

**The bound arrives already summed, and no restatement may take a per-block cap.**
Bounding each block separately by `κ₀ + κ₁·deg B` and adding gives
`(J+1)(κ₀ + κ₁·deg B)`, quadratic in `deg B` once `J ≤ deg B`, which is exactly the
uniformity `thm:main` clause 3 asserts.  Every hypothesis below that mentions the
constants mentions them under a `∑`.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
and the principal amplitude» (`sec:geometry`, `cor:linear-phase-variation`,
`eq:linear-phase-variation`), in the form «Angular discrepancy and proof of the main
theorem» (`subsec:proof`) consumes it.

## Tags

phase variation, blocks, uniformity, weight polynomial
-/

namespace ForgacsTran

open Set Real

/-- A `Fin k` family of sets read as an `ℕ`-indexed one, empty past `k`.

The variation machinery is written over a `Finset ℕ` -- `ViewingAngle.eVariationOn_sum_le`
inducts on the maximum -- and `AngularDiscrepancyFT.FTPhaseSupply` indexes its blocks by
`Fin k`.  This is the whole of the conversion, and it is a definition rather than a step
inside one proof because every per-root bound a caller brings from `ViewingAngle` needs the
same conversion. -/
noncomputable def finExt {k : ℕ} (J : Fin k → Set ℝ) : ℕ → Set ℝ :=
  fun n => if h : n < k then J ⟨n, h⟩ else ∅

theorem finExt_coe {k : ℕ} (J : Fin k → Set ℝ) (i : Fin k) : finExt J (i : ℕ) = J i := by
  simp only [finExt, dif_pos i.isLt, Fin.eta]

theorem sum_eVariationOn_finExt {k : ℕ} (f : ℝ → ℝ) (J : Fin k → Set ℝ) :
    ∑ n ∈ Finset.range k, eVariationOn f (finExt J n) = ∑ i, eVariationOn f (J i) := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => eVariationOn f (finExt J n)) k]
  exact Finset.sum_congr rfl fun i _ => by rw [finExt_coe]

/-- A `Fin k` family of functions read as an `ℕ`-indexed one, zero past `k`.  The
companion of `finExt`, for the case where the branch itself varies from block to block --
which is what a zero of `B` that the arc **meets** forces. -/
noncomputable def finExtFun {k : ℕ} (ψ : Fin k → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun n => if h : n < k then ψ ⟨n, h⟩ else 0

theorem finExtFun_coe {k : ℕ} (ψ : Fin k → ℝ → ℝ) (i : Fin k) :
    finExtFun ψ (i : ℕ) = ψ i := by
  simp only [finExtFun, dif_pos i.isLt, Fin.eta]

theorem sum_eVariationOn_finExtFun {k : ℕ} (ψ : Fin k → ℝ → ℝ) (J : Fin k → Set ℝ) :
    ∑ n ∈ Finset.range k, eVariationOn (finExtFun ψ n) (finExt J n)
      = ∑ i, eVariationOn (ψ i) (J i) := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun n => eVariationOn (finExtFun ψ n) (finExt J n)) k]
  exact Finset.sum_congr rfl fun i _ => by rw [finExt_coe, finExtFun_coe]

/-- **`linear_phase_variation_components` over `Fin k`.**  The supply indexes its blocks
by `Fin k`; the variation machinery is written over a `Finset ℕ`, because
`ViewingAngle.eVariationOn_sum_le` inducts on the maximum.  Extending the block family
by the empty set past `k` moves one statement to the other with no mathematical content
in between. -/
theorem linear_phase_variation_components_fin {k : ℕ} {ψ₀ : ℝ → ℝ} {J : Fin k → Set ℝ}
    {ψ : ℂ → Fin k → ℝ → ℝ} {κ₀ Kγ : ℝ} {B : Polynomial ℂ} {s : Set ℝ}
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hJ : ∀ i, J i ⊆ s)
    (hord : ∀ i j : Fin k, i < j → ∀ x ∈ J i, ∀ y ∈ J j, x ≤ y)
    (h0 : eVariationOn ψ₀ s ≤ ENNReal.ofReal κ₀)
    (hroots : ∀ β ∈ B.roots,
      ∑ i, eVariationOn (ψ β i) (J i) ≤ ENNReal.ofReal (Kγ + π)) :
    ∑ i, eVariationOn (fun x => ψ₀ x + (B.roots.map (fun β => ψ β i x)).sum) (J i)
      ≤ ENNReal.ofReal (κ₀ + (Kγ + π) * B.natDegree) := by
  classical
  set J' : ℕ → Set ℝ := finExt J with hJ'def
  set ψ' : ℂ → ℕ → ℝ → ℝ := fun β n => if h : n < k then ψ β ⟨n, h⟩ else 0 with hψ'def
  have hJ'eq : ∀ i : Fin k, J' (i : ℕ) = J i := fun i => finExt_coe J i
  have hψ'eq : ∀ (β : ℂ) (i : Fin k), ψ' β (i : ℕ) = ψ β i := by
    intro β i; simp only [hψ'def, dif_pos i.isLt, Fin.eta]
  have hmemrange : ∀ n ∈ Finset.range k, n < k := fun n hn => Finset.mem_range.1 hn
  have key := linear_phase_variation_components (ψ₀ := ψ₀) (J := J') (ψ := ψ')
    (κ₀ := κ₀) (Kγ := Kγ) (B := B) (s := s) (Finset.range k) hκ₀ hKγ
    (fun n hn => by
      simp only [hJ'def, finExt, dif_pos (hmemrange n hn)]
      exact hJ _)
    (fun i hi j hj hij => by
      simp only [hJ'def, finExt, dif_pos (hmemrange i hi), dif_pos (hmemrange j hj)]
      exact hord _ _ (by exact hij))
    h0
    (fun β hβ => by
      refine le_trans (le_of_eq ?_) (hroots β hβ)
      rw [← Fin.sum_univ_eq_sum_range (fun n => eVariationOn (ψ' β n) (J' n)) k]
      exact Finset.sum_congr rfl fun i _ => by rw [hJ'eq i, hψ'eq β i])
  refine le_trans (le_of_eq ?_) key
  rw [← Fin.sum_univ_eq_sum_range
    (fun n => eVariationOn (fun x => ψ₀ x + (B.roots.map (fun β => ψ' β n x)).sum) (J' n)) k]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hJ'eq i]
  refine congrArg (fun f => eVariationOn f (J i)) ?_
  funext x
  refine congrArg (fun m : Multiset ℝ => ψ₀ x + m.sum) ?_
  exact Multiset.map_congr rfl fun β _ => by rw [hψ'eq β i]

/-- **The supply's variation clauses, about the summed branch.**  `varψ i` is the
variation of the `i`-th block's branch, and the finiteness that names it as a real
number comes from the summed bound rather than being assumed.

`κ₁` is `𝒦_γ + π`, a constant of the principal arc alone, and the `deg B` it multiplies
is the only place the weight appears. -/
theorem exists_varPhase_of_blocks {k : ℕ} {ψ₀ : ℝ → ℝ} {Lb Rb : Fin k → ℝ}
    {ψ : ℂ → Fin k → ℝ → ℝ} {κ₀ Kγ : ℝ} {B : Polynomial ℂ} {s : Set ℝ}
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ s)
    (hord : ∀ i j : Fin k, i < j → Rb i ≤ Lb j)
    (h0 : eVariationOn ψ₀ s ≤ ENNReal.ofReal κ₀)
    (hroots : ∀ β ∈ B.roots,
      ∑ i, eVariationOn (ψ β i) (Icc (Lb i) (Rb i)) ≤ ENNReal.ofReal (Kγ + π)) :
    ∃ varψ : Fin k → ℝ, (∀ i, 0 ≤ varψ i) ∧
      (∀ i, Lb i ≤ Rb i →
        |(ψ₀ (Rb i) + (B.roots.map (fun β => ψ β i (Rb i))).sum)
          - (ψ₀ (Lb i) + (B.roots.map (fun β => ψ β i (Lb i))).sum)| ≤ varψ i) ∧
      ∑ i, varψ i ≤ κ₀ + (Kγ + π) * B.natDegree := by
  have hKπ : (0 : ℝ) ≤ Kγ + π := by linarith [Real.pi_pos]
  exact exists_varPhase_of_sum_eVariationOn
    (ψ := fun i x => ψ₀ x + (B.roots.map (fun β => ψ β i x)).sum)
    (add_nonneg hκ₀ (mul_nonneg hKπ (Nat.cast_nonneg _)))
    (linear_phase_variation_components_fin hκ₀ hKγ hJ
      (fun i j hij x hx y hy => le_trans hx.2 (le_trans (hord i j hij) hy.1)) h0 hroots)

/-- **`exists_varPhase_of_blocks`'s `hroots`, at one zero of `B`.**  Radon's bound
(`lem:viewing-angle`) summed over the ordered blocks, in whichever of the two states the
zero is in: one the arc misses keeps a single branch across every block and costs
`𝒦_γ + π`; one the arc meets at `m` carries the branch based at `a` on the blocks left of
`m` and at `b` on those right of it, and costs `𝒦_γ`, which is under the same cap.

**The cap is on the sum, not on a block.**  `ViewingAngle`'s own statements are already
summed -- that is what `eVariationOn_sum_le` is for -- and this restates them over
`Fin k` without weakening that.  A per-block reading would give `(J+1)(𝒦_γ + π)` per zero
and `deg B` times that in total, quadratic, which is the uniformity
`cor:linear-phase-variation` exists for. -/
theorem sum_eVariationOn_branch_le {γ dγ d2γ : ℝ → ℂ} {U : Set ℝ} {a b Kγ : ℝ} {β : ℂ}
    {k : ℕ} {Lb Rb : Fin k → ℝ} {ψ : Fin k → ℝ → ℝ}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0) (hKγ : 0 ≤ Kγ)
    (hKvar : eVariationOn (polarAngle dγ d2γ 0 a) (Icc a b) ≤ ENNReal.ofReal Kγ)
    (hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ Icc a b)
    (hord : ∀ i j : Fin k, i < j → Rb i ≤ Lb j)
    (hstate :
      (∃ S : Finset ℝ, (∀ x ∈ Icc a b, γ x ≠ β) ∧ (∀ x ∈ S, x ∈ Icc a b)
          ∧ (∀ x ∈ Ioo a b, ∀ j : ℤ,
              polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (j : ℝ) * π → x ∈ S)
          ∧ ∀ i, ψ i = polarAngle γ dγ β a)
        ∨ (∃ m, a ≤ m ∧ m ≤ b ∧ ∃ S₁ S₂ : Finset ℝ, γ m = β
            ∧ (∀ x ∈ Icc a b, x ≠ m → γ x ≠ β)
            ∧ (∀ x ∈ Ioo a m, ∀ j : ℤ,
                polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (j : ℝ) * π → x ∈ S₁)
            ∧ (∀ x ∈ Ioo m b, ∀ j : ℤ,
                polarAngle dγ d2γ 0 a x - polarAngle γ dγ β b x = (j : ℝ) * π → x ∈ S₂)
            ∧ ∀ i, (Icc (Lb i) (Rb i) ⊆ Ico a m ∧ ψ i = polarAngle γ dγ β a)
                ∨ (Icc (Lb i) (Rb i) ⊆ Ioc m b ∧ ψ i = polarAngle γ dγ β b))) :
    ∑ i, eVariationOn (ψ i) (Icc (Lb i) (Rb i)) ≤ ENNReal.ofReal (Kγ + π) := by
  classical
  set J : Fin k → Set ℝ := fun i => Icc (Lb i) (Rb i) with hJdef
  have hordN : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k, i < j →
      ∀ x ∈ finExt J i, ∀ y ∈ finExt J j, x ≤ y := by
    intro i hi j hj hij x hx y hy
    simp only [finExt, dif_pos (Finset.mem_range.1 hi)] at hx
    simp only [finExt, dif_pos (Finset.mem_range.1 hj)] at hy
    exact le_trans hx.2 (le_trans (hord _ _ (by exact hij)) hy.1)
  have hJN : ∀ i ∈ Finset.range k, finExt J i ⊆ Icc a b := by
    intro i hi
    simp only [finExt, dif_pos (Finset.mem_range.1 hi)]
    exact hJ _
  have hKπ : ENNReal.ofReal Kγ + ENNReal.ofReal π = ENNReal.ofReal (Kγ + π) :=
    (ENNReal.ofReal_add hKγ Real.pi_pos.le).symm
  rcases hstate with ⟨S, hne, hSsub, hS, hψ⟩ | ⟨m, ham, hmb, S₁, S₂, hm, hne, hS₁, hS₂, hside⟩
  · have heq : ∑ i, eVariationOn (ψ i) (J i)
        = ∑ i, eVariationOn (polarAngle γ dγ β a) (J i) :=
      Finset.sum_congr rfl fun i _ => by rw [hψ i]
    rw [heq, ← sum_eVariationOn_finExt, ← hKπ]
    exact le_trans (viewing_angle_bound_components_off_arc hab hU hsub hd hd2 hc2 hreg hne
      S hSsub hS (Finset.range k) hJN hordN) (by gcongr)
  · rw [← sum_eVariationOn_finExtFun, ← hKπ]
    refine le_trans (viewing_angle_bound_components_of_meet ham hmb hU hsub hd hd2 hc2 hreg
      hm hne S₁ S₂ hS₁ hS₂ (Finset.range k) ?_ hordN) (le_trans hKvar le_self_add)
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    simp only [finExt, finExtFun, dif_pos hik]
    exact hside ⟨i, hik⟩

/-- **One derivative, one increment.**  Two branches of the argument of the same
nonvanishing function have the same derivative on a block, `Im(W'/W)`; this is what
turns that into the equality of increments the supply's variation clause needs.

The mean value theorem at bound `0`, and nothing else. -/
theorem sub_eq_sub_of_hasDerivAt_eq {f g f' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (f' x) x)
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    f v - f u = g v - g u := by
  have hd : ∀ x ∈ Icc a b, HasDerivWithinAt (fun y => f y - g y) 0 (Icc a b) x := by
    intro x hx
    have h := ((hf x hx).sub (hg x hx)).hasDerivWithinAt (s := Icc a b)
    rwa [sub_self] at h
  have hb := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y => f y - g y) (f' := fun _ => (0 : ℝ)) (C := 0) hd
    (fun _ _ => by norm_num) hu hv
  have hzero : (f v - g v) - (f u - g u) = 0 := by
    have h0 : ‖(f v - g v) - (f u - g u)‖ ≤ 0 := by simpa using hb
    exact norm_le_zero_iff.1 h0
  linarith [hzero]

/-- **The supply's variation clauses, about the branch the supply's other clauses use.**
`exists_varPhase_of_blocks` bounds the increments of the summed branch; the supply's
factorization and derivative clauses are about a branch built on `W` itself.  `hderiv`
is what identifies the two: on each block both have derivative `dψ i`, which for a
branch of `arg W` is `Im(W'/W)` and for the summed branch is that same quantity read off
the logarithmic derivative of `eq:W-on-g`.

Stated with `hderiv` rather than with the polar factorization on purpose: what has to
be checked is an identity between derivatives, and asking for the factorization instead
would ask the caller to build a second polar decomposition it does not need. -/
theorem exists_varPhase_of_blocks_of_derivEq {k : ℕ} {ψ₀ : ℝ → ℝ} {Lb Rb : Fin k → ℝ}
    {ψ : ℂ → Fin k → ℝ → ℝ} {Ψ dΨ : Fin k → ℝ → ℝ}
    {κ₀ Kγ : ℝ} {B : Polynomial ℂ} {s : Set ℝ}
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ s)
    (hord : ∀ i j : Fin k, i < j → Rb i ≤ Lb j)
    (h0 : eVariationOn ψ₀ s ≤ ENNReal.ofReal κ₀)
    (hroots : ∀ β ∈ B.roots,
      ∑ i, eVariationOn (ψ β i) (Icc (Lb i) (Rb i)) ≤ ENNReal.ofReal (Kγ + π))
    (hΨ : ∀ i, Lb i < Rb i → ∀ x ∈ Icc (Lb i) (Rb i), HasDerivAt (Ψ i) (dΨ i x) x)
    (hsum : ∀ i, Lb i < Rb i → ∀ x ∈ Icc (Lb i) (Rb i),
      HasDerivAt (fun y => ψ₀ y + (B.roots.map (fun β => ψ β i y)).sum) (dΨ i x) x) :
    ∃ varψ : Fin k → ℝ, (∀ i, 0 ≤ varψ i) ∧
      (∀ i, Lb i ≤ Rb i → |Ψ i (Rb i) - Ψ i (Lb i)| ≤ varψ i) ∧
      ∑ i, varψ i ≤ κ₀ + (Kγ + π) * B.natDegree := by
  obtain ⟨varψ, hnn, hinc, hsumle⟩ :=
    exists_varPhase_of_blocks hκ₀ hKγ hJ hord h0 hroots
  refine ⟨varψ, hnn, fun i hi => ?_, hsumle⟩
  rcases eq_or_lt_of_le hi with heq | hlt
  · rw [heq, sub_self, abs_zero]
    exact hnn i
  have hL : Lb i ∈ Icc (Lb i) (Rb i) := ⟨le_rfl, hi⟩
  have hR : Rb i ∈ Icc (Lb i) (Rb i) := ⟨hi, le_rfl⟩
  have heq := sub_eq_sub_of_hasDerivAt_eq (f := Ψ i)
    (g := fun y => ψ₀ y + (B.roots.map (fun β => ψ β i y)).sum)
    (f' := dΨ i) (hΨ i hlt) (hsum i hlt) hL hR
  rw [heq]
  exact hinc i hi

end ForgacsTran
