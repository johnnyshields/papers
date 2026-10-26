/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.PeriodicCutEncoding

/-!
# Full-code propagation through actual even discrepancies

The full-code induction step in factor-reversal reconstruction for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
The refined signed period excludes new odd discrepancies.  Every
remaining full-code discrepancy is an actual member of the computed
next frontier, hence divisible by its refined gcd.  Sorry-free.
-/

namespace SkewClassInflation

/-- Refined signed periods make every old frontier translation a full-code period off the holes. -/
theorem evenCutCode_frontier_periods {N : ℕ} (α : Composition N) (hN : 0 < N)
    (p d : ℕ) (T : Finset ℕ) (hpN : p ∣ N) (hdp : d ∣ p)
    (hT : ∀ t ∈ T, p ∣ t)
    (hD : ∀ x ∈ evenCutDisagreements α p T, d ∣ x)
    (hP : Function.Periodic (periodMask (compositionCutSignInt α) d) (d : ℤ)) :
    ∀ t ∈ T, Function.Periodic (periodMask (compositionCutCode α) d) (t : ℤ) := by
  classical
  intro t ht
  have hdt : d ∣ t := hdp.trans (hT t ht)
  have hdN : d ∣ N := hdp.trans hpN
  have hsignPeriod := periodic_nat_of_dvd (periodMask (compositionCutSignInt α) d) d t hdt hP
  apply periodMask_periodic _ d t hdt
  intro z hz
  let x := compositionCutResidue N z
  let y := (x + t) % N
  have hxN : x < N := compositionCutResidue_lt N hN z
  have hdx : ¬ d ∣ x := fun h => hz ((compositionCutResidue_dvd N d hN hdN z).mp h)
  have hpx : ¬ p ∣ x := fun h => hdx (hdp.trans h)
  have hx0 : 0 < x := by
    by_contra hh
    have he : x = 0 := by omega
    exact hdx (by rw [he]; exact dvd_zero d)
  have hy : compositionCutResidue N (z + (t : ℤ)) = y :=
    compositionCutResidue_add_nat N hN z t
  have hsign := periodMask_periodic_value (compositionCutSignInt α) d t hdt hsignPeriod z hz
  change compositionCutSign α (compositionCutResidue N (z + t)) = compositionCutSign α x at hsign
  rw [hy] at hsign
  change compositionCutCodeNat α (compositionCutResidue N (z + t)) = compositionCutCodeNat α x
  rw [hy]
  by_contra hne
  have heven := compositionCutCodeNat_disagreement α x y hsign.symm (Ne.symm hne)
  have hxD : x ∈ evenCutDisagreements α p T :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hx0, hxN⟩,
      hpx, t, ht, heven.1, heven.2.1, heven.2.2⟩
  exact hdx (hD x hxD)

/-- The actual next gcd supplies full-code propagation from the old period and frontier. -/
theorem evenCutClosure_code_refinement {N : ℕ} (α : Composition N) (hN : 0 < N)
    (q : ℕ) (T : Finset ℕ) (hqN : q ∣ N)
    (hQ : Function.Periodic
      (periodMask (compositionCutCode α) (q.gcd (T.gcd id))) (q : ℤ))
    (hP : Function.Periodic
      (periodMask (compositionCutSignInt α)
        (evenCutClosureStep α (q.gcd (T.gcd id), T)).1)
      ((evenCutClosureStep α (q.gcd (T.gcd id), T)).1 : ℤ)) :
    Function.Periodic
      (periodMask (compositionCutCode α)
        (evenCutClosureStep α (q.gcd (T.gcd id), T)).1)
      (q.gcd (T.gcd id) : ℤ) := by
  let p := q.gcd (T.gcd id)
  let d := (evenCutClosureStep α (p, T)).1
  have hdp : d ∣ p := evenCutClosureStep_dvd α (p, T)
  have hpq : p ∣ q := Nat.gcd_dvd_left _ _
  have hpT : p ∣ T.gcd id := Nat.gcd_dvd_right _ _
  have hT : ∀ t ∈ T, p ∣ t := fun t ht => hpT.trans (Finset.gcd_dvd ht)
  have hpN : p ∣ N := hpq.trans hqN
  have hD : ∀ x ∈ evenCutDisagreements α p T, d ∣ x := by
    intro x hx
    have hg : d ∣ (evenCutDisagreements α p T).gcd id := Nat.gcd_dvd_right _ _
    exact hg.trans (Finset.gcd_dvd hx)
  have hfront := evenCutCode_frontier_periods α hN p d T hpN hdp hT hD hP
  have hq := periodMask_refine (compositionCutCode α) d p q hdp (hdp.trans hpq) hQ
  exact periodic_gcd_frontier (periodMask (compositionCutCode α) d) q T hq hfront

end SkewClassInflation
