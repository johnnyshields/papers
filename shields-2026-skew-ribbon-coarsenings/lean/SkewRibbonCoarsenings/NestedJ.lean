/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.ChainSums
import SkewRibbonCoarsenings.Defs

/-!
# The functional `𝓙_y` and antichain contraction

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:detector` (`eq:J`) and the
antichain contraction used in the proof of `thm:nested`.

`Jcal` is `eq:J` for a labeled list `m : Fin k → ℕ`; `JJ` is the same difference of chain sums over
a sublist `T` of an arbitrary label type; `JJ_contract` is the contraction
`𝓙_Y(T) = θ 𝓙_{m x}(T ∖ {x})` valid when the shift `Y` changes the cut value only at `{x}` and at
`T ∖ {x}`, with opposite increments.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

/-- `eq:J`: `𝓙_y(𝐌) = ∑_π [∏_{j=1}^{k-1} b(y + ∑_{h ≤ j} m_{π(h)})
- ∏_{j=1}^{k-1} b(∑_{h ≤ j} m_{π(h)})]` for a labeled list `m : Fin k → ℕ`, with `b` the cut
indicator of the cut set `S` on `ℤ/n`. -/
def Jcal (n : ℕ) (S : Finset ℕ) (y : ℕ) {k : ℕ} (m : Fin k → ℕ) : ℤ :=
  ∑ π : Equiv.Perm (Fin k),
    (∏ j ∈ Finset.Ico 1 k, cutInd n S ((y + partialSum m π j : ℕ) : ZMod n) -
      ∏ j ∈ Finset.Ico 1 k, cutInd n S ((partialSum m π j : ℕ) : ZMod n))

/-- The chain-sum form of `eq:J` over a sublist `T` of positions: the difference of the chain sums
of the shifted and the unshifted cut weights. -/
def JJ {ι : Type*} [DecidableEq ι] (n : ℕ) (S : Finset ℕ) (m : ι → ℕ) (Y : ℕ)
    (T : Finset ι) : ℤ :=
  chainSum (fun X => cutInd n S ((Y + ∑ i ∈ X, m i : ℕ) : ZMod n)) ∅ T -
    chainSum (fun X => cutInd n S ((∑ i ∈ X, m i : ℕ) : ZMod n)) ∅ T

/-- `eq:J` as a difference of chain sums over the whole list: maximal chains are orderings. -/
lemma Jcal_eq_JJ (n : ℕ) (S : Finset ℕ) (y : ℕ) {k : ℕ} (m : Fin k → ℕ) :
    Jcal n S y m = JJ n S m y Finset.univ := by
  unfold Jcal JJ
  rw [chainSum_eq_sum_perm (fun t => cutInd n S ((y + t : ℕ) : ZMod n)) m,
    chainSum_eq_sum_perm (fun t => cutInd n S ((t : ℕ) : ZMod n)) m, Finset.sum_sub_distrib]

variable {ι : Type*} [DecidableEq ι]

/-- Antichain contraction for `𝓙`: if the shift `Y` changes the cut value only at `{x}` and
`T ∖ {x}`, with increments `θ` and `-θ`, then `𝓙_Y(T) = θ 𝓙_{m x}(T ∖ {x})`. -/
lemma JJ_contract (n : ℕ) (S : Finset ℕ) (m : ι → ℕ) (Y : ℕ) {T : Finset ι} {x : ι}
    (hx : x ∈ T) (hne : (T.erase x).Nonempty) (θ : ℤ)
    (hdiff : ∀ X : Finset ι, ∅ ⊂ X → X ⊂ T → X ≠ {x} → X ≠ T.erase x →
      cutInd n S ((Y + ∑ i ∈ X, m i : ℕ) : ZMod n) = cutInd n S ((∑ i ∈ X, m i : ℕ) : ZMod n))
    (h1 : cutInd n S ((Y + m x : ℕ) : ZMod n) - cutInd n S ((m x : ℕ) : ZMod n) = θ)
    (h2 : cutInd n S ((Y + ∑ i ∈ T.erase x, m i : ℕ) : ZMod n) -
      cutInd n S ((∑ i ∈ T.erase x, m i : ℕ) : ZMod n) = -θ) :
    JJ n S m Y T = θ * JJ n S m (m x) (T.erase x) := by
  have key := chainSum_contraction (F' := fun X => cutInd n S ((Y + ∑ i ∈ X, m i : ℕ) : ZMod n))
    (F := fun X => cutInd n S ((∑ i ∈ X, m i : ℕ) : ZMod n)) hx hne θ
    (fun X h1' h2' h3 h4 => hdiff X h1' h2' h3 h4)
    (by simpa using h1) (by simpa using h2)
  have hcongr : chainSum (fun X => cutInd n S ((∑ i ∈ insert x X, m i : ℕ) : ZMod n)) ∅
      (T.erase x) = chainSum (fun X => cutInd n S ((m x + ∑ i ∈ X, m i : ℕ) : ZMod n)) ∅
      (T.erase x) := by
    apply chainSum_congr (Finset.empty_subset _)
    intro X _ hX
    have hxX : x ∉ X := fun h => (Finset.notMem_erase x T) (hX.subset h)
    rw [Finset.sum_insert hxX]
  unfold JJ
  rw [hcongr] at key
  linarith

end SkewRibbonCoarsenings
