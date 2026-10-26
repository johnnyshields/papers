/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/Termination.lean
import SkewRibbonCoarsenings.Propagation
import SkewRibbonCoarsenings.LiteralFactor
import SkewRibbonCoarsenings.CompositionProduct

/-!
# Realization at the original weight: termination

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:realization`
(`prop:termination`, `eq:common-factor`).

`maskPeriodSeq` is the iteration `p_0 = e`, `p_{j+1} = per(𝓑_{p_j})` (the least period of the mask
among the divisors of `n`).  Under the hypothesis that every chain of strict increases propagates
(`DetectorsVanish` for every `MaskChain` prefix) and that the starting mask is `d`-periodic,
`p_j ∣ p_{j+1} ∣ d` (`termination_dvd`), the iteration stabilizes (`termination_stable`), and at
its stable value `p` both cut sets are literal compositions with the same inner factor
(`termination_common_factor`).  `termination_or_detector` is the dichotomy used by the local
alternative: either the common factor, or a chain prefix carrying a positive detector.
Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset Nested

/-- The least period of `f : ℤ/n → ℤ` among the positive divisors of `n` (`per(f)`). -/
noncomputable def leastPer {n : ℕ} (f : ZMod n → ℤ) : ℕ := by
  classical
  exact if hex : ∃ m, 0 < m ∧ m ∣ n ∧ IsPeriod f m then Nat.find hex else 0

lemma leastPer_spec {n : ℕ} [NeZero n] (f : ZMod n → ℤ) : IsLeastPeriod f (leastPer f) := by
  classical
  have hex : ∃ m, 0 < m ∧ m ∣ n ∧ IsPeriod f m :=
    ⟨n, Nat.pos_of_ne_zero (NeZero.ne n), dvd_rfl, fun x => by simp⟩
  have hl : leastPer f = Nat.find hex := by unfold leastPer; rw [dif_pos hex]
  rw [hl]
  obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex
  refine ⟨h1, h2, h3, fun q hq hqn hper => ?_⟩
  exact Nat.find_min' hex ⟨hq, hqn, hper⟩

/-- `prop:termination`: the iteration `p_0 = e`, `p_{j+1} = per(𝓑_{p_j})`. -/
noncomputable def maskPeriodSeq (n : ℕ) (S : Finset ℕ) (e : ℕ) : ℕ → ℕ
  | 0 => e
  | j + 1 => leastPer (maskFun n S (maskPeriodSeq n S e j))

section Termination

variable {n : ℕ} {S S' : Finset ℕ} {d e : ℕ}

@[simp] lemma maskPeriodSeq_zero : maskPeriodSeq n S e 0 = e := rfl

lemma maskPeriodSeq_succ (j : ℕ) :
    maskPeriodSeq n S e (j + 1) = leastPer (maskFun n S (maskPeriodSeq n S e j)) := rfl

/-- `p_{j+1}` is the least period of `𝓑_{p_j}` (among the divisors of `n`). -/
theorem maskPeriodSeq_least (h : NormalizedSetting n S S' d e) (j : ℕ) :
    IsLeastPeriod (maskFun n S (maskPeriodSeq n S e j)) (maskPeriodSeq n S e (j + 1)) := by
  haveI := neZero_of_setting h
  rw [maskPeriodSeq_succ]
  exact leastPer_spec _

lemma maskPeriodSeq_pos (h : NormalizedSetting n S S' d e) (j : ℕ) : 0 < maskPeriodSeq n S e j := by
  cases j with
  | zero => exact h.e_pos
  | succ j => exact (maskPeriodSeq_least h j).1

/-- The least period divides every period. -/
lemma dvd_of_period_least [NeZero n] {f : ZMod n → ℤ} {m r : ℕ} (hl : IsLeastPeriod f m)
    (hr : IsPeriod f r) : m ∣ r := by
  have hmem : ((r : ℕ) : ZMod n) ∈ periodGroup f := fun x => hr x
  exact (nat_dvd_iff_val hl.2.1 r).mpr (dvd_of_mem_periodGroup hl hmem)

/-- Once the iteration repeats a value it is constant. -/
lemma maskPeriodSeq_stable {i : ℕ} (hi : maskPeriodSeq n S e i = maskPeriodSeq n S e (i + 1)) :
    ∀ m, i ≤ m → maskPeriodSeq n S e m = maskPeriodSeq n S e i := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [maskPeriodSeq_succ, ih, ← maskPeriodSeq_succ, hi]

/-- Remasking: if `𝓑_{q'}` has period `r`, `q ∣ q'` and `q ∣ r`, then `𝓑_q` has period `r`. -/
lemma mask_period_of_dvd [NeZero n] {q q' r : ℕ} (hqn : q ∣ n) (hqq : q ∣ q') (hqr : q ∣ r)
    (hper : IsPeriod (maskFun n S q') r) : IsPeriod (maskFun n S q) r := by
  intro x
  have hr : q ∣ ((r : ℕ) : ZMod n).val := (nat_dvd_iff_val hqn r).mp hqr
  by_cases hx : q ∣ x.val
  · rw [maskFun_of_dvd hx, maskFun_of_dvd ((dvd_val_add hqn hr).mpr hx)]
  · have hxr : ¬ q ∣ (x + (r : ZMod n)).val := fun hh => hx ((dvd_val_add hqn hr).mp hh)
    have hx' : ¬ q' ∣ x.val := fun hh => hx (hqq.trans hh)
    have hxr' : ¬ q' ∣ (x + (r : ZMod n)).val := fun hh => hxr (hqq.trans hh)
    have := hper x
    rw [maskFun_of_not_dvd hxr', maskFun_of_not_dvd hx'] at this
    rw [maskFun_of_not_dvd hxr, maskFun_of_not_dvd hx]
    exact this

/-- A period of a mask `𝓑_q` (`e ∣ q ∣ d`) is a period of `w`, hence divisible by `e`. -/
lemma e_dvd_of_mask_period [NeZero n] (h : NormalizedSetting n S S' d e) {q r : ℕ}
    (heq : e ∣ q) (hqd : q ∣ d) (hr : IsPeriod (maskFun n S q) r) : e ∣ r := by
  have hmem : ((r : ℕ) : ZMod n) ∈ periodGroup (maskFun n S q) := fun x => hr x
  have hneg := (periodGroup (maskFun n S q)).neg_mem hmem
  have hw : IsPeriod (wFun n S S' d) r := by
    intro x
    have h1 := h.mask_odd q heq hqd (x + (r : ZMod n))
    have h2 := h.mask_odd q heq hqd x
    have h3 := hr x
    have h4 := hneg (-x)
    rw [show -(x + (r : ZMod n)) = -x + -(r : ZMod n) by ring, h4, h3] at h1
    omega
  exact dvd_of_period_least h.e_least hw

/-- The divisibility step of `prop:termination`: if the chain divides through `p_j` and
`p_j ∣ d`, then `p_j ∣ p_{j+1}`. -/
lemma maskPeriodSeq_dvd_step (h : NormalizedSetting n S S' d e) {j : ℕ}
    (hS : ∀ k < j, maskPeriodSeq n S e k ∣ maskPeriodSeq n S e (k + 1))
    (hjd : maskPeriodSeq n S e j ∣ d) :
    maskPeriodSeq n S e j ∣ maskPeriodSeq n S e (j + 1) := by
  haveI := neZero_of_setting h
  have hchain : ∀ i k, i ≤ k → k ≤ j → maskPeriodSeq n S e i ∣ maskPeriodSeq n S e k := by
    intro i k hik hkj
    induction k, hik using Nat.le_induction with
    | base => exact dvd_rfl
    | succ k hik ih => exact (ih (by omega)).trans (hS k (by omega))
  have hjn : maskPeriodSeq n S e j ∣ n := hjd.trans h.d_dvd_n
  have hr : IsPeriod (maskFun n S (maskPeriodSeq n S e j)) (maskPeriodSeq n S e (j + 1)) :=
    (maskPeriodSeq_least h j).2.2.1
  have hej : e ∣ maskPeriodSeq n S e j := by
    have := hchain 0 j (Nat.zero_le _) le_rfl
    simpa using this
  have key : ∀ k, k ≤ j → maskPeriodSeq n S e k ∣ maskPeriodSeq n S e (j + 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact e_dvd_of_mask_period h hej hjd hr
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hkj := hchain k j (by omega) le_rfl
      have hkn : maskPeriodSeq n S e k ∣ n := hkj.trans hjn
      have hper := mask_period_of_dvd (S := S) hkn hkj h1 hr
      exact dvd_of_period_least (maskPeriodSeq_least h k) hper
  exact key j le_rfl

/-- The state of the iteration at step `j`: divisibilities through `p_j`, `p_j ∣ d`, and
`𝓑_{p_j}` is `d`-periodic. -/
def TermState (n : ℕ) (S : Finset ℕ) (d e j : ℕ) : Prop :=
  (∀ k < j, maskPeriodSeq n S e k ∣ maskPeriodSeq n S e (k + 1)) ∧
    maskPeriodSeq n S e j ∣ d ∧ IsPeriod (maskFun n S (maskPeriodSeq n S e j)) d

/-- The hypothesis of `prop:termination`: "every subsequent propagation succeeds", i.e. all
applicable positive detectors vanish for every chain prefix of the iteration. -/
def PropagationSucceeds (n : ℕ) (S S' : Finset ℕ) (d e : ℕ) : Prop :=
  ∀ L, MaskChain n S d e L (maskPeriodSeq n S e) →
    DetectorsVanish n S S' d e L (maskPeriodSeq n S e)

lemma termState (h : NormalizedSetting n S S' d e) (h0 : IsPeriod (maskFun n S e) d)
    (hvan : PropagationSucceeds n S S' d e) : ∀ j, TermState n S d e j := by
  haveI := neZero_of_setting h
  intro j
  induction j with
  | zero => exact ⟨fun k hk => by omega, by simpa using h.e_dvd_d, by simpa using h0⟩
  | succ j ih =>
    obtain ⟨hS, hjd, hper⟩ := ih
    have hdv := maskPeriodSeq_dvd_step h hS hjd
    have hd1 : maskPeriodSeq n S e (j + 1) ∣ d :=
      dvd_of_period_least (maskPeriodSeq_least h j) hper
    have hS' : ∀ k < j + 1, maskPeriodSeq n S e k ∣ maskPeriodSeq n S e (k + 1) := by
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact hS k hk
      · exact hdv
    refine ⟨hS', hd1, ?_⟩
    by_cases heq : maskPeriodSeq n S e (j + 1) = maskPeriodSeq n S e j
    · rw [heq]; exact hper
    · have hlt : maskPeriodSeq n S e j < maskPeriodSeq n S e (j + 1) := by
        have := Nat.le_of_dvd (maskPeriodSeq_pos h (j + 1)) hdv
        omega
      have hstrict : ∀ i, i < j + 1 →
          maskPeriodSeq n S e i < maskPeriodSeq n S e (i + 1) := by
        intro i hi
        have hle := Nat.le_of_dvd (maskPeriodSeq_pos h (i + 1)) (hS' i hi)
        by_contra hnot
        have hieq : maskPeriodSeq n S e i = maskPeriodSeq n S e (i + 1) := by omega
        have h1 := maskPeriodSeq_stable hieq (j + 1) (by omega)
        have h2 := maskPeriodSeq_stable hieq j (by omega)
        exact heq (by rw [h1, h2])
      have hc : MaskChain n S d e (j + 1) (maskPeriodSeq n S e) :=
        { one_le := by omega
          p_zero := rfl
          lt := hstrict
          dvd := hS'
          dvd_d := hd1
          periodic := fun i _ => (maskPeriodSeq_least h i).2.2.1 }
      exact propagation h hc (fun i _ => maskPeriodSeq_least h i) (hvan _ hc)

/-- `prop:termination`: `p_j ∣ p_{j+1} ∣ d` at every step. -/
theorem termination_dvd (h : NormalizedSetting n S S' d e) (h0 : IsPeriod (maskFun n S e) d)
    (hvan : PropagationSucceeds n S S' d e) (j : ℕ) :
    maskPeriodSeq n S e j ∣ maskPeriodSeq n S e (j + 1) ∧ maskPeriodSeq n S e (j + 1) ∣ d :=
  let hs := termState h h0 hvan (j + 1)
  ⟨hs.1 j (Nat.lt_succ_self j), hs.2.1⟩

/-- `prop:termination`: the chain stabilizes. -/
theorem termination_stable (h : NormalizedSetting n S S' d e) (h0 : IsPeriod (maskFun n S e) d)
    (hvan : PropagationSucceeds n S S' d e) :
    ∃ j, maskPeriodSeq n S e j = maskPeriodSeq n S e (j + 1) := by
  by_contra hno
  push Not at hno
  have hge : ∀ j, j ≤ maskPeriodSeq n S e j := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hdv := (termination_dvd h h0 hvan j).1
      have hle := Nat.le_of_dvd (maskPeriodSeq_pos h (j + 1)) hdv
      have := hno j
      omega
  have h1 := hge (d + 1)
  have h2 := Nat.le_of_dvd h.d_pos (termination_dvd h h0 hvan d).2
  omega

/-- Membership in a cut set off the `d`-grid does not depend on the orientation. -/
lemma mem_iff_of_not_dvd [NeZero n] (h : NormalizedSetting n S S' d e) {x : ℕ} (hx : ¬ d ∣ x) :
    x ∈ S ↔ x ∈ S' := by
  by_cases hxn : x < n
  · have hv : ¬ d ∣ ((x : ℕ) : ZMod n).val := by rwa [ZMod.val_natCast_of_lt hxn]
    have := h.cutInd_eq_of_not_dvd hv
    unfold cutInd at this
    rw [ZMod.val_natCast_of_lt hxn] at this
    by_cases h1 : x ∈ S <;> by_cases h2 : x ∈ S' <;> simp [h1, h2] at this ⊢
  · have h1 : x ∉ S := fun hh => hxn (Finset.mem_Ioo.mp (h.cuts hh)).2
    have h2 : x ∉ S' := fun hh => hxn (Finset.mem_Ioo.mp (h.cuts' hh)).2
    simp [h1, h2]

lemma mem_iff_cutInd [NeZero n] {S₀ : Finset ℕ} {m : ℕ} (hm : m < n) :
    m ∈ S₀ ↔ cutInd n S₀ (m : ZMod n) = 1 := by
  unfold cutInd
  rw [ZMod.val_natCast_of_lt hm]
  by_cases h1 : m ∈ S₀ <;> simp [h1]

/-- `prop:termination`, `eq:common-factor`.  Assume the starting mask `𝓑_e` is `d`-periodic
(`mask_periodic_of_four_vanish`) and every subsequent propagation succeeds
(`PropagationSucceeds`).  Then the iteration stabilizes at a proper inner size `p` with
`3 ≤ p ≤ d < n`, `p ∣ d`, and the two cut sets are literal compositions with the same inner factor
`E` (`eq:composition-cuts`): `S = compCuts (n / p) A p E` and `S' = compCuts (n / p) A' p E`. -/
theorem termination_common_factor (h : NormalizedSetting n S S' d e)
    (h0 : IsPeriod (maskFun n S e) d) (hvan : PropagationSucceeds n S S' d e) :
    ∃ (p : ℕ) (A A' E : Finset ℕ), 3 ≤ p ∧ p ≤ d ∧ p ∣ d ∧ p ∣ n ∧ p < n ∧
      IsCutSet (n / p) A ∧ IsCutSet (n / p) A' ∧ IsCutSet p E ∧
      S = compCuts (n / p) A p E ∧ S' = compCuts (n / p) A' p E := by
  haveI := neZero_of_setting h
  obtain ⟨j, hj⟩ := termination_stable h h0 hvan
  obtain ⟨p, hp⟩ : ∃ p, p = maskPeriodSeq n S e j := ⟨_, rfl⟩
  have hpd : p ∣ d := by rw [hp]; exact (termState h h0 hvan j).2.1
  have hep : e ∣ p := by
    have hs := (termState h h0 hvan j).1
    have : ∀ k, k ≤ j → e ∣ maskPeriodSeq n S e k := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih => intro hk; exact (ih (by omega)).trans (hs k (by omega))
    rw [hp]; exact this j le_rfl
  have hp0 : 0 < p := by rw [hp]; exact maskPeriodSeq_pos h j
  have hp3 : 3 ≤ p := le_trans h.three_le_e (Nat.le_of_dvd hp0 hep)
  have hpled : p ≤ d := Nat.le_of_dvd h.d_pos hpd
  have hpn : p ∣ n := hpd.trans h.d_dvd_n
  have hpltn : p < n := lt_of_le_of_lt hpled h.d_lt
  have hper : IsPeriod (maskFun n S p) p := by
    have := (maskPeriodSeq_least h j).2.2.1
    rw [← hj, ← hp] at this
    exact this
  have hoff : ∀ x, ¬ p ∣ x → (x ∈ S ↔ x ∈ S') :=
    fun x hx => mem_iff_of_not_dvd h (fun hh => hx (hpd.trans hh))
  -- off-grid periodicity of both cut sets
  have offS : OffGridPeriodic n S p := by
    intro x hx hnd
    have hp1 := hper (x : ZMod n)
    rw [show (x : ZMod n) + (p : ZMod n) = ((x + p : ℕ) : ZMod n) by push_cast; ring,
      maskFun_nat_of_ndvd hpn (show ¬ p ∣ x + p from fun hh =>
        hnd ((Nat.dvd_add_left dvd_rfl).mp hh)), maskFun_nat_of_ndvd hpn hnd] at hp1
    rw [mem_iff_cutInd (by omega : x < n), mem_iff_cutInd hx, hp1]
  have offS' : OffGridPeriodic n S' p := by
    intro x hx hnd
    have hnd2 : ¬ p ∣ x + p := fun hh => hnd ((Nat.dvd_add_left dvd_rfl).mp hh)
    rw [← hoff x hnd, ← hoff (x + p) hnd2]
    exact offS x hx hnd
  obtain ⟨A, E, hA, hE, hSE⟩ := (literal_factor_iff hp0 hpn h.cuts).mpr offS
  obtain ⟨A', E', hA', hE', hSE'⟩ := (literal_factor_iff hp0 hpn h.cuts').mpr offS'
  have hm : 0 < n / p := Nat.div_pos (Nat.le_of_lt hpltn) hp0
  have hu := (literal_factor_unique hp0 hm hA hE hSE).1
  have hu' := (literal_factor_unique hp0 hm hA' hE' hSE').1
  have hsame := (literal_factor_same_inner hp0 h.cuts h.cuts' offS offS').mpr hoff
  have hEE : E = E' := by rw [hu, hu', hsame]
  subst hEE
  exact ⟨p, A, A', E, hp3, hpled, hpd, hpn, hpltn, hA, hA', hE, hSE, hSE'⟩

/-- The dichotomy used by `prop:local-alternative`: either every propagation succeeds and the two
cut sets have a proper literal common inner factor (`eq:common-factor`), or some strict prefix of
the iteration is a chain of least periods (`eq:chain`) carrying a nonzero positive detector of
total `n` (the `L + 4`-block detector of `thm:nested`, with `|ΔK| ≤ 2`). -/
theorem termination_or_detector (h : NormalizedSetting n S S' d e)
    (h0 : IsPeriod (maskFun n S e) d) :
    (∃ (p : ℕ) (A A' E : Finset ℕ), 3 ≤ p ∧ p ≤ d ∧ p ∣ d ∧ p ∣ n ∧ p < n ∧
      IsCutSet (n / p) A ∧ IsCutSet (n / p) A' ∧ IsCutSet p E ∧
      S = compCuts (n / p) A p E ∧ S' = compCuts (n / p) A' p E) ∨
    ∃ (L a r s z : ℕ) (y : ℕ → ℕ), MaskChain n S d e L (maskPeriodSeq n S e) ∧
      (∀ i, i < L → IsLeastPeriod (maskFun n S (maskPeriodSeq n S e i))
        (maskPeriodSeq n S e (i + 1))) ∧
      PositiveDetector n S S' d e L (maskPeriodSeq n S e) a r s z y := by
  by_cases hvan : PropagationSucceeds n S S' d e
  · exact Or.inl (termination_common_factor h h0 hvan)
  · right
    unfold PropagationSucceeds at hvan
    push Not at hvan
    obtain ⟨L, hc, hnv⟩ := hvan
    obtain ⟨a, r, s, z, y, hD⟩ := not_detectorsVanish_iff.mp hnv
    exact ⟨L, a, r, s, z, y, hc, fun i _ => maskPeriodSeq_least h i, hD⟩

end Termination

end SkewRibbonCoarsenings
