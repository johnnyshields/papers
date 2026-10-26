/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.DeterminationPeriods
import SkewClassInflation.OverlapWords

/-!
# Signed-period obstruction for the actual overlap word

The signed cut function of an overlap word has a full short period and an
initial zero interval.  Together these exclude the nontrivial punctured
period that actual nonreconstructibility would produce.  This is the ribbon
input to `lem:overlap-power-rigidity` of
`shields-2026-skew-class-inflation.tex`.  Sorry-free.
-/

namespace SkewClassInflation

/-- An interval period and initial zeros kill every defined punctured-period value. -/
theorem guarded_overlap_period_vanish (f : ℕ → ℤ) (N Q p δ L : ℕ)
    (hp : 0 < p) (hpN : p < N) (hδ : 0 < δ)
    (hweight : N = L * Q + δ) (hpdiv : p ∣ N) (hbound : p + Q ≤ N)
    (hsmall : ∀ x, 0 < x → x + p < N → ¬ p ∣ x → f (x + p) = f x)
    (hlarge : ∀ x, 0 < x → x + Q < N → f (x + Q) = f x)
    (hzero : ∀ x, 0 < x → x ≤ δ → f x = 0) :
    ∀ x, 0 < x → x < N → ¬ p ∣ x → f x = 0 := by
  classical
  let _ : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hreduce : ∀ n, 0 < n → n < N → ¬ p ∣ n → f n = f (n % p) :=
    guarded_period_reduce f p p N hp (dvd_refl p) (by
      intro x hx hxN hn _
      exact hsmall x hx hxN hn)
  let G : ZMod p → ℤ := fun x => if x = 0 then 0 else f x.val
  have hagree (n : ℕ) (hn0 : 0 < n) (hnN : n < N) (hn : ¬ p ∣ n) :
      G (n : ZMod p) = f n := by
    have hcast : (n : ZMod p) ≠ 0 := fun he => hn ((ZMod.natCast_eq_zero_iff n p).mp he)
    simp only [G, ite_eq_right hcast, ZMod.val_natCast]
    exact (hreduce n hn0 hnN hn).symm
  have hstep : ∀ x : ZMod p, x ≠ 0 → x + (Q : ZMod p) ≠ 0 →
      G (x + (Q : ZMod p)) = G x := by
    intro x hx hnext
    have hx0 : 0 < x.val := Nat.pos_of_ne_zero (fun he => hx ((ZMod.val_eq_zero x).mp he))
    have hxp := ZMod.val_lt x
    have hxn : ((x.val + Q : ℕ) : ZMod p) = x + (Q : ZMod p) := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val]
    have hn : ¬ p ∣ x.val + Q := by
      intro hd
      apply hnext
      rw [← hxn]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
    have hnat := hagree (x.val + Q) (by omega) (by omega) hn
    rw [hxn] at hnat
    rw [hnat, hlarge x.val hx0 (by omega)]
    exact (by simp only [G, ite_eq_right hx])
  have hgd : Q.gcd p ∣ δ := by
    have hn := (Nat.gcd_dvd_right Q p).trans hpdiv
    have hm : Q.gcd p ∣ L * Q := dvd_mul_of_dvd_right (Nat.gcd_dvd_left Q p) L
    rw [hweight] at hn
    exact (Nat.dvd_add_iff_right hm).mpr hn
  have hgle : Q.gcd p ≤ δ := Nat.le_of_dvd hδ hgd
  intro x hx hxN hn
  by_cases hδp : δ < p
  · have hGzero : ∀ r : ℕ, 1 ≤ r → r ≤ δ → G (r : ZMod p) = 0 := by
      intro r hr hrδ
      have hrp : r < p := hrδ.trans_lt hδp
      have hrnot : ¬ p ∣ r := by
        intro hd
        have := Nat.le_of_dvd (by omega : 0 < r) hd
        omega
      rw [hagree r (by omega) (hrp.trans hpN) hrnot]
      exact hzero r (by omega) hrδ
    have hall := overlap_period_obstruction Q p δ hp hδp hgle G hstep hGzero
    have hxn : (x : ZMod p) ≠ 0 := fun he => hn ((ZMod.natCast_eq_zero_iff _ _).mp he)
    exact (hagree x hx hxN hn).symm.trans (hall _ hxn)
  · have hr0 : 0 < x % p := Nat.pos_of_ne_zero (fun he => hn (Nat.dvd_of_mod_eq_zero he))
    rw [hreduce x hx hxN hn]
    exact hzero _ hr0 (by have := Nat.mod_lt x hp; omega)

/-- Reversing the actual composition negates its signed cut function. -/
theorem compositionCutSign_reverse {N : ℕ} (α : Composition N) (x : ℕ) (hx : x ≤ N) :
    compositionCutSign α.reverse x = -compositionCutSign α x := by
  classical
  simp only [compositionCutSign, properCuts_reverse_iff α x hx,
    properCuts_reverse_iff α (N - x) (Nat.sub_le _ _), Nat.sub_sub_self hx]
  ring

/-- A nonreconstructible source itself has a nonzero value off a genuine signed period. -/
theorem nonreconstructible_signed_period_witness {N : ℕ} (α : Composition N)
    (hn : ¬ ribbonReconstructible α) :
    ∃ p k : ℕ, 1 < p ∧ p < N ∧ p ∣ N ∧ 0 < k ∧ k < N ∧ ¬ p ∣ k ∧
      compositionCutSign α k ≠ 0 ∧
      ∀ x, 0 < x → x + p < N → ¬ p ∣ x →
        compositionCutSign α (x + p) = compositionCutSign α x := by
  obtain ⟨γ, k, hγ, _, hnγ, hk0, hkN, ht, hk, hkr, hfirst⟩ :=
    exists_normalized_first_single_cut α hn
  obtain ⟨hp, hpN, hd, hnot, hperiod⟩ := undeterminedGcd_signed_period γ k hk hkr hfirst
    (undeterminedCuts_nonempty γ hnγ k hk hkr)
  have hsign : compositionCutSign γ k = 1 := by
    rw [compositionCutSign_of_one γ k ht, ite_eq_left hk]
  refine ⟨undeterminedGcd γ k, k, hp, hpN, hd, hk0, hkN, hnot, ?_, ?_⟩
  · intro he
    rcases hγ with hγ | hγ
    · rw [hγ, he] at hsign
      omega
    · rw [hγ, compositionCutSign_reverse α k hkN.le, he] at hsign
      omega
  · intro x hx hxN hn
    have he := hperiod x hx hxN hn
    rcases hγ with hγ | hγ
    · simpa only [hγ] using he
    · have hsignγ (z : ℕ) (hz : z ≤ N) :
          compositionCutSign γ z = -compositionCutSign α z :=
        (congrArg (fun A : Composition N => compositionCutSign A z) hγ).trans
          (compositionCutSign_reverse α z hz)
      rw [hsignγ (x + undeterminedGcd γ k) (by omega), hsignγ x (by omega)] at he
      omega

namespace OverlapWord

/-- The actual overlap's cuts are invariant under each bounded whole-period shift. -/
theorem cut_shift (R : OverlapWord) (m x : ℕ) (hx : 0 < x)
    (hxN : x + R.period < (m + 1) * R.period + R.delta) :
    (x + R.period ∈ properCuts (R.composition m) ↔ x ∈ properCuts (R.composition m)) := by
  have hQ := R.delta_lt_period
  rw [R.properCuts_periodic m (x + R.period) (by omega) hxN,
    R.properCuts_periodic m x hx (by omega)]
  simp only [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]

/-- Both actual reflected cut indicators share the overlap period throughout their domain. -/
theorem cutSign_shift (R : OverlapWord) (m x : ℕ) (hx : 0 < x)
    (hxN : x + R.period < (m + 1) * R.period + R.delta) :
    compositionCutSign (R.composition m) (x + R.period) =
      compositionCutSign (R.composition m) x := by
  classical
  let N := (m + 1) * R.period + R.delta
  have hforward := R.cut_shift m x hx hxN
  have hbackward := R.cut_shift m (N - (x + R.period)) (by dsimp [N]; omega)
    (by dsimp [N]; omega)
  have he : N - (x + R.period) + R.period = N - x := by dsimp [N]; omega
  rw [he] at hbackward
  dsimp only [N] at hbackward
  simp only [compositionCutSign, hforward, hbackward]

/-- The overlap endpoint margins give an actual initial zero interval for the signed cuts. -/
theorem cutSign_initial_zero (R : OverlapWord) (m x : ℕ)
    (hxδ : x ≤ R.delta) : compositionCutSign (R.composition m) x = 0 := by
  classical
  have hleft : x ∉ properCuts (R.composition m) := by
    intro hcut
    obtain ⟨j, _, y, hy, he⟩ := (R.properCuts_composition m x).mp hcut
    have hb := R.cuts_bounds y hy
    omega
  have hright : (m + 1) * R.period + R.delta - x ∉ properCuts (R.composition m) := by
    intro hcut
    obtain ⟨j, hj, y, hy, he⟩ := (R.properCuts_composition m _).mp hcut
    have hb := R.cuts_bounds y hy
    have hmul := Nat.mul_le_mul_right R.period hj
    have hs : (m + 1) * R.period = m * R.period + R.period := by ring
    omega
  simp only [compositionCutSign, ite_eq_right hleft, ite_eq_right hright, sub_self]

/-- Every actual overlapped ribbon with at least two copies has only its two orientations.

**Differs from the paper's route.** The signed-period consequence of actual
nonreconstructibility already contradicts the overlap's initial zeros and full
period.  The full factor-reversal classification is unnecessary for this input.
-/
theorem reconstructible (R : OverlapWord) (m : ℕ) (hm : 1 ≤ m) :
    ribbonReconstructible (R.composition m) := by
  classical
  by_contra hn
  obtain ⟨p, k, hp, hpN, hd, hk0, hkN, hnot, hnonzero, hperiod⟩ :=
    nonreconstructible_signed_period_witness (R.composition m) hn
  have hQ := R.delta_lt_period
  have hδ := R.delta_pos
  have hhalf : 2 * p ≤ (m + 1) * R.period + R.delta := by
    obtain ⟨q, hq⟩ := hd
    have hq2 : 2 ≤ q := by
      by_contra he
      have hqle : q ≤ 1 := by omega
      interval_cases q <;> simp_all
    have he := Nat.mul_le_mul_left p hq2
    omega
  have hhalfQ : 2 * R.period ≤ (m + 1) * R.period :=
    Nat.mul_le_mul_right R.period (by omega)
  have hbound : p + R.period ≤ (m + 1) * R.period + R.delta := by omega
  have hall := guarded_overlap_period_vanish (compositionCutSign (R.composition m))
    ((m + 1) * R.period + R.delta) R.period p R.delta (m + 1) (by omega) hpN hδ rfl hd
    hbound hperiod (R.cutSign_shift m) (fun x _ hxδ => R.cutSign_initial_zero m x hxδ)
  exact hnonzero (hall k hk0 hkN hnot)

end OverlapWord

end SkewClassInflation
