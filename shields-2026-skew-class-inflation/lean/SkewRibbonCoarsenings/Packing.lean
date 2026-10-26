/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/Packing.lean
import SkewRibbonCoarsenings.Selection
import SkewRibbonCoarsenings.NestedIdentity

/-!
# Realization at the original weight: packing

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:realization`
(`lem:packing`, `eq:packing-ledger`, `eq:packing-budget`, `eq:original-weight`).

`PositiveDetector` is a positive labeled list of total `n` (the data `NestedData` of
`eq:chain`--`eq:layers`) with nonzero labeled difference `ΔK`; `DetectorsVanish` is the hypothesis
"all applicable positive detectors of `thm:nested` vanish".  `packing` is `lem:packing`: from the
probes of `lem:selection` (or their reflections) it builds a positive detector of total `n`.
Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset Nested

section Detector

variable {n : ℕ} {S S' : Finset ℕ} {d e L : ℕ} {p : ℕ → ℕ}

/-- `eq:packing-ledger`: `C_box = 3 p_1 + ∑_{i=2}^L p_i`. -/
def packBox (p : ℕ → ℕ) (L : ℕ) : ℕ := 3 * p 1 + ∑ i ∈ Finset.Icc 2 L, p i

/-- A positive detector of `thm:nested`: positive labeled data of total `n` satisfying
`eq:chain`--`eq:layers` (`NestedData`, with `a ∈ supp v`) whose labeled difference
`ΔK = K_b - K_c` at the list `(a, y_{L-1}, …, y_0, r, s, z)` is nonzero (so of absolute value one
or two, by `nested_identity`). -/
structure PositiveDetector (n : ℕ) (S S' : Finset ℕ) (d e L : ℕ) (p : ℕ → ℕ) (a r s z : ℕ)
    (y : ℕ → ℕ) : Prop where
  data : NestedData n S S' d e L p a r s z y
  ne : (K S (detList L a r s z y) : ℤ) - (K S' (detList L a r s z y) : ℤ) ≠ 0

/-- The hypothesis of `prop:propagation`: all applicable positive detectors of `thm:nested` for the
chain `p` vanish: every positive list of total `n` satisfying `eq:chain`--`eq:layers` has
`K_b = K_c`. -/
def DetectorsVanish (n : ℕ) (S S' : Finset ℕ) (d e L : ℕ) (p : ℕ → ℕ) : Prop :=
  ∀ (a r s z : ℕ) (y : ℕ → ℕ), NestedData n S S' d e L p a r s z y →
    K S (detList L a r s z y) = K S' (detList L a r s z y)

lemma not_detectorsVanish_iff :
    ¬ DetectorsVanish n S S' d e L p ↔
      ∃ (a r s z : ℕ) (y : ℕ → ℕ), PositiveDetector n S S' d e L p a r s z y := by
  unfold DetectorsVanish
  push Not
  constructor
  · rintro ⟨a, r, s, z, y, hD, hne⟩
    exact ⟨a, r, s, z, y, ⟨hD, fun h0 => hne (by omega)⟩⟩
  · rintro ⟨a, r, s, z, y, hD, hne⟩
    exact ⟨a, r, s, z, y, hD, fun h0 => hne (by rw [h0]; ring)⟩

/-- A positive detector has labeled difference of absolute value at most two
(`thm:nested`). -/
lemma PositiveDetector.abs_le (h : NormalizedSetting n S S' d e) {a r s z : ℕ} {y : ℕ → ℕ}
    (D : PositiveDetector n S S' d e L p a r s z y) :
    |(K S (detList L a r s z y) : ℤ) - (K S' (detList L a r s z y) : ℤ)| ≤ 2 :=
  (nested_identity h D.data).2.1

/-! ### Elementary facts about the chain -/

lemma MaskChain.mono (hc : MaskChain n S d e L p) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ L) :
    p i ≤ p j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hc.lt j (by omega)).le

lemma MaskChain.pos (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p) {i : ℕ}
    (hi : i ≤ L) : 0 < p i := by
  have := hc.mono (Nat.zero_le i) hi
  rw [hc.p_zero] at this
  have := h.three_le_e
  omega

lemma MaskChain.two_mul_le (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p) {i : ℕ}
    (hi : i + 1 ≤ L) : 2 * p i ≤ p (i + 1) := by
  obtain ⟨k, hk⟩ := hc.dvd i (by omega)
  have hlt := hc.lt i (by omega)
  have hpos := hc.pos h (i := i) (by omega)
  rw [hk] at hlt ⊢
  have : 2 ≤ k := by
    by_contra hk2
    interval_cases k <;> simp at hlt
  nlinarith

lemma sum_Icc_two (p : ℕ → ℕ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 2 (m + 1), p i = ∑ i ∈ Finset.range m, p (i + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma packBox_eq (p : ℕ → ℕ) {L : ℕ} (hL : 1 ≤ L) :
    packBox p L = 3 * p 1 + ∑ i ∈ Finset.range (L - 1), p (i + 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  unfold packBox
  rw [sum_Icc_two, Nat.add_sub_cancel]

lemma packBox_le (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p) :
    packBox p L ≤ 2 * p L + p 1 := by
  have key : ∀ m, m + 1 ≤ L → 3 * p 1 + ∑ i ∈ Finset.Icc 2 (m + 1), p i ≤ 2 * p (m + 1) + p 1 := by
    intro m
    induction m with
    | zero => intro _; simp; omega
    | succ m ih =>
      intro hm
      rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc]
      have h1 := ih (by omega)
      have h2 := hc.two_mul_le h (i := m + 1) hm
      omega
  obtain ⟨m, hm⟩ : ∃ m, L = m + 1 := ⟨L - 1, by have := hc.one_le; omega⟩
  have := key m (by omega)
  unfold packBox
  rw [hm]
  omega

/-- `eq:packing-budget`: `W ≥ C_box - p_1`, written without truncated subtraction. -/
def PackingBudget (p : ℕ → ℕ) (L W : ℕ) : Prop := packBox p L ≤ W + p 1

/-- `lem:packing`, "in particular": the budget `eq:packing-budget` holds as soon as `W ≥ 2 P`. -/
lemma packingBudget_of_two_mul (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p)
    {W : ℕ} (hW : 2 * p L ≤ W) : PackingBudget p L W := by
  unfold PackingBudget
  have : packBox p L ≤ 2 * p L + p 1 := packBox_le h hc
  omega

end Detector

/-! ### The reflection computations -/

section Reflection

variable {n : ℕ} {S S' : Finset ℕ} {d e L : ℕ} {p : ℕ → ℕ}

/-- `H_y(r, s, z)` of `eq:deltaH` as `probeH` (the bridge of `BottomProbes` to `NestedBottom`). -/
lemma probeH_eq_Hfun (n : ℕ) (S S' : Finset ℕ) (d e y r s z : ℕ) :
    probeH n S S' d e y (r : ZMod n) (s : ZMod n) (z : ZMod n) = Hfun n S S' d e y r s z := by
  simp [probeH, probeF, Hfun, fY]

/-- `θ_i` of `eq:deltaH` as `thetaProbe`. -/
lemma thetaProbe_eq_thetaFun (n : ℕ) (S : Finset ℕ) (p y : ℕ → ℕ) (i : ℕ) :
    thetaProbe n S (p (i + 1)) (y i) (y (i + 1)) = thetaFun n S p y i := rfl

/-- Padding the first bottom probe by a multiple of a period `q` of `𝓑_e` (with `e ∣ q`) leaves
`H_y` unchanged. -/
lemma Hfun_pad [NeZero n] (h : NormalizedSetting n S S' d e) {q : ℕ} (heq : e ∣ q)
    (hper : IsPeriod (maskFun n S e) q) (y r s z k : ℕ) :
    Hfun n S S' d e y (r + k * q) s z = Hfun n S S' d e y r s z := by
  have hf : fY n S e y (r + k * q) = fY n S e y r := by
    unfold fY
    have h1 : ((r + k * q + y : ℕ) : ZMod n) = ((r + y : ℕ) : ZMod n) + ((k * q : ℕ) : ZMod n) := by
      push_cast; ring
    have h2 : ((r + k * q : ℕ) : ZMod n) = (r : ZMod n) + ((k * q : ℕ) : ZMod n) := by
      push_cast; ring
    rw [h1, h2, isPeriod_mul_cast hper k, isPeriod_mul_cast hper k]
  have hw : wFun n S S' d ((r + k * q : ℕ) : ZMod n) = wFun n S S' d (r : ZMod n) := by
    have : ((r + k * q : ℕ) : ZMod n) = (r : ZMod n) + ((k * q : ℕ) : ZMod n) := by
      push_cast; ring
    rw [this]
    exact isPeriod_add_dvd h.e_least.2.2.1 (heq.trans (dvd_mul_left q k)) _
  unfold Hfun
  rw [hf, hw]

/-- The reflection of a mask value: for a period `Q ∣ N` of `𝓑_q` (`e ∣ q ∣ d`),
`𝓑_q(N - x) = 𝓑_q(x) - w(x)`. -/
lemma mask_sub_of_period [NeZero n] (h : NormalizedSetting n S S' d e) {q Q N : ℕ}
    (heq : e ∣ q) (hqd : q ∣ d) (hper : IsPeriod (maskFun n S q) Q) (hN : Q ∣ N)
    (x : ZMod n) :
    maskFun n S q ((N : ZMod n) - x) = maskFun n S q x - wFun n S S' d x := by
  have h1 : (N : ZMod n) - x = -x + (N : ZMod n) := by ring
  rw [h1, isPeriod_add_dvd hper hN]
  have := h.mask_odd q heq hqd x
  omega

/-- `𝓑_q` is even at multiples of `e`, modulo a period: if `x + x' = M`, `Q ∣ M`, `Q` a period of
`𝓑_q` and `e ∣ x`, then `𝓑_q(x') = 𝓑_q(x)`. -/
lemma mask_reflect_eq [NeZero n] (h : NormalizedSetting n S S' d e) {q Q M x x' : ℕ}
    (heq : e ∣ q) (hqd : q ∣ d) (hper : IsPeriod (maskFun n S q) Q) (hM : Q ∣ M) (hx : e ∣ x)
    (hxx : x + x' = M) : maskFun n S q (x' : ZMod n) = maskFun n S q (x : ZMod n) := by
  have c : (x' : ZMod n) = (M : ZMod n) - (x : ZMod n) := by
    have := congrArg (fun m : ℕ => (m : ZMod n)) hxx
    simp only [Nat.cast_add] at this
    linear_combination this
  rw [c, mask_sub_of_period h heq hqd hper hM, wFun_nat_of_dvd_e h hx]
  ring

/-- `f_{y'}(r') = f_y(r)` when `y + y' ≡ 0` and `r + r' ≡ 0` modulo a period `q` of `𝓑_e`,
`e ∣ y`: `f_{-y}(-x) = f_y(x)`. -/
lemma fY_reflect [NeZero n] (h : NormalizedSetting n S S' d e) {q y y' M r r' : ℕ}
    (heq : e ∣ q) (hper : IsPeriod (maskFun n S e) q) (hy : e ∣ y) (hyy : y + y' = M)
    (hM : q ∣ M) (hrr : r + r' = q) : fY n S e y' r' = fY n S e y r := by
  unfold fY
  have c1 : ((r' + y' : ℕ) : ZMod n) = ((q + M : ℕ) : ZMod n) - ((r + y : ℕ) : ZMod n) := by
    have h0 : r' + y' + (r + y) = q + M := by omega
    have := congrArg (fun m : ℕ => (m : ZMod n)) h0
    simp only [Nat.cast_add] at this ⊢
    linear_combination this
  have c2 : ((r' : ℕ) : ZMod n) = ((q : ℕ) : ZMod n) - (r : ZMod n) := by
    have := congrArg (fun m : ℕ => (m : ZMod n)) hrr
    simp only [Nat.cast_add] at this
    linear_combination this
  have hw : wFun n S S' d ((r + y : ℕ) : ZMod n) = wFun n S S' d (r : ZMod n) := by
    rw [Nat.add_comm]; exact wFun_add_of_dvd h r hy
  rw [c1, c2, mask_sub_of_period h dvd_rfl h.e_dvd_d hper (Nat.dvd_add_right dvd_rfl |>.mpr hM),
    mask_sub_of_period h dvd_rfl h.e_dvd_d hper dvd_rfl, hw]
  ring

/-- `w(r') = -w(r)` when `r + r' = q` with `e ∣ q`. -/
lemma w_reflect [NeZero n] (h : NormalizedSetting n S S' d e) {q r r' : ℕ} (heq : e ∣ q)
    (hrr : r + r' = q) : wFun n S S' d (r' : ZMod n) = - wFun n S S' d (r : ZMod n) := by
  have c : (r' : ZMod n) = -(r : ZMod n) + (q : ZMod n) := by
    have := congrArg (fun m : ℕ => (m : ZMod n)) hrr
    simp only [Nat.cast_add] at this
    linear_combination this
  rw [c, isPeriod_add_dvd h.e_least.2.2.1 heq, h.w_odd]

/-- The bottom reflection of `lem:packing`: `H_{y_0'}(r', s', z') = -H_{y_0}(r, s, z)`. -/
lemma Hfun_reflect [NeZero n] (h : NormalizedSetting n S S' d e) {q y y' M r s z r' s' z' : ℕ}
    (heq : e ∣ q) (hper : IsPeriod (maskFun n S e) q) (hy : e ∣ y) (hyy : y + y' = M)
    (hM : q ∣ M) (hr : r + r' = q) (hs : s + s' = q) (hz : z + z' = q) :
    Hfun n S S' d e y' r' s' z' = - Hfun n S S' d e y r s z := by
  unfold Hfun
  rw [fY_reflect h heq hper hy hyy hM hr, fY_reflect h heq hper hy hyy hM hs,
    fY_reflect h heq hper hy hyy hM hz, w_reflect h heq hr, w_reflect h heq hs,
    w_reflect h heq hz]
  ring

/-- `Δ' = -Δ` of `lem:packing`: with `W = n - a`, `P ∣ W` and `t ∈ p_{L-1} ℤ \ P ℤ`, the target
`t' = W - t` has `b(a + t') - b(t') = -(b(a + t) - b(t))`. -/
lemma deltaFun_reflect [NeZero n] (h : NormalizedSetting n S S' d e) {P a t : ℕ}
    (hPn : P ∣ n) (heP : e ∣ P) (hPd : P ∣ d) (hPa : P ∣ a) (het : e ∣ t) (hPt : ¬ P ∣ t)
    (han : a ≤ n) (htW : t ≤ n - a) :
    deltaFun n S a (n - a - t) = - deltaFun n S a t := by
  unfold deltaFun
  have c1 : ((a + (n - a - t) : ℕ) : ZMod n) = -((t : ℕ) : ZMod n) := by
    have : a + (n - a - t) = n - t := by omega
    rw [this]; exact natCast_sub_eq_neg' (by omega)
  have c2 : (((n - a - t : ℕ)) : ZMod n) = -(((a + t : ℕ)) : ZMod n) := by
    have : n - a - t = n - (a + t) := by omega
    rw [this]; exact natCast_sub_eq_neg' (by omega)
  have hPat : ¬ P ∣ a + t := fun hh => hPt ((Nat.dvd_add_right hPa).mp hh)
  have heat : e ∣ a + t := Nat.dvd_add ((heP.trans hPa)) het
  rw [c1, c2, cutInd_neg_eq h hPn heP hPd hPt, cutInd_neg_eq h hPn heP hPd hPat,
    wFun_nat_of_dvd_e h het, wFun_nat_of_dvd_e h heat]
  ring

end Reflection

/-! ### Padding -/

section Padding

variable {n : ℕ} {S S' : Finset ℕ} {d e L : ℕ} {p : ℕ → ℕ}

lemma sum_range_eq_of_last (y : ℕ → ℕ) {L : ℕ} (hL : 1 ≤ L) :
    ∑ k ∈ Finset.range L, y k = ∑ i ∈ Finset.range (L - 1), y i + y (L - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  simp [Finset.sum_range_succ]

/-- Padding of `lem:packing`: a list with all nested factors nonzero and total at most `n`, the
deficit a multiple of `p_1`, becomes a positive detector of total exactly `n` after adding the
deficit to the first bottom probe. -/
lemma pad [NeZero n] (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p)
    {a r s z : ℕ} {y : ℕ → ℕ} (ha0 : 0 < a) (hva : vFun n S S' (a : ZMod n) ≠ 0)
    (hdvd : ∀ k < L, p k ∣ y k) (hndvd : ∀ k < L, ¬ p (k + 1) ∣ y k)
    (hr : ¬ e ∣ r) (hs : ¬ e ∣ s) (hz : ¬ e ∣ z)
    (hle : a + ∑ k ∈ Finset.range L, y k + (r + s + z) ≤ n)
    (hmod : p 1 ∣ n - (a + ∑ k ∈ Finset.range L, y k + (r + s + z)))
    (hΔ : deltaFun n S a (y (L - 1)) ≠ 0)
    (hθ : ∀ i, i + 2 ≤ L → thetaFun n S p y i ≠ 0)
    (hH : Hfun n S S' d e (y 0) r s z ≠ 0) :
    ∃ r', PositiveDetector n S S' d e L p a r' s z y := by
  obtain ⟨k, hk⟩ := hmod
  have he1 : e ∣ p 1 := by
    have := hc.dvd 0 hc.one_le
    rwa [hc.p_zero] at this
  have hper0 : IsPeriod (maskFun n S e) (p 1) := by
    simpa [hc.p_zero] using hc.periodic 0 hc.one_le
  refine ⟨r + k * p 1, ?_⟩
  have hD : NestedData n S S' d e L p a (r + k * p 1) s z y :=
    { L_pos := hc.one_le
      p0 := hc.p_zero
      pL_dvd := hc.dvd_d
      chain := hc.dvd
      strict := hc.lt
      period := hc.periodic
      a_pos := ha0
      a_supp := hva
      sum_eq := by
        rw [Nat.mul_comm] at hk
        generalize p 1 * k = c at hk
        omega
      dvd_y := hdvd
      ndvd_y := hndvd
      ndvd_r := fun hh => hr ((Nat.dvd_add_left (he1.trans (dvd_mul_left _ _))).mp hh)
      ndvd_s := hs
      ndvd_z := hz }
  refine ⟨hD, ?_⟩
  rw [(nested_identity h hD).1, Hfun_pad h he1 hper0]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hva) hΔ) ?_) hH
  exact Finset.prod_ne_zero_iff.mpr fun i hi => hθ i (by simp at hi; omega)

end Padding


/-! ### The reflected list and the packing lemma -/

section Packing

variable {n : ℕ} {S S' : Finset ℕ} {d e L : ℕ} {p : ℕ → ℕ}

/-- The total `y_k + y_k'` of a probe and its reflection: `p_{k+2}` for `k ≤ L - 2` and `W = n - a`
for the target `k = L - 1`. -/
def reflTot (n a L : ℕ) (p : ℕ → ℕ) (k : ℕ) : ℕ := if k + 1 < L then p (k + 2) else n - a

/-- The reflected probes of `lem:packing`: `y_i' = p_{i+2} - y_i` for `i ≤ L - 2` and
`y_{L-1}' = t' = W - t`. -/
def reflProbe (n a L : ℕ) (p y : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k + 1 < L then p (k + 2) - y k else n - a - y k

lemma reflProbe_add {n a L : ℕ} {p y : ℕ → ℕ} {k : ℕ} (hk : y k ≤ reflTot n a L p k) :
    y k + reflProbe n a L p y k = reflTot n a L p k := by
  unfold reflProbe reflTot at *
  split_ifs at * <;> omega

lemma sum_reflTot (n a p) {L : ℕ} (hL : 1 ≤ L) :
    ∑ k ∈ Finset.range L, reflTot n a L p k = ∑ i ∈ Finset.range (L - 1), p (i + 2) + (n - a) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  rw [Finset.sum_range_succ, Nat.add_sub_cancel]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [reflTot, hi]
  · simp [reflTot]

/-- The reflected probes are `θ`-equivalent: `θ_i' = θ_i` (`lem:packing`). -/
lemma thetaFun_reflect [NeZero n] (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p)
    {a : ℕ} {y : ℕ → ℕ} (hy : ∀ k < L, y k ≤ reflTot n a L p k)
    (hdiv : ∀ k < L, p (k + 1) ∣ reflTot n a L p k) (hdy : ∀ k < L, p k ∣ y k) {i : ℕ}
    (hi : i + 2 ≤ L) :
    thetaFun n S p (reflProbe n a L p y) i = thetaFun n S p y i := by
  have hsum : ∀ k < L, y k + reflProbe n a L p y k = reflTot n a L p k :=
    fun k hk => reflProbe_add (hy k hk)
  have hi1 : i + 1 < L := by omega
  have hi0 : i < L := by omega
  have hq : e ∣ p (i + 1) := by
    have := hc.dvd_le (Nat.zero_le (i + 1)) (by omega)
    rwa [hc.p_zero] at this
  have hqd : p (i + 1) ∣ d := (hc.dvd_le (show i + 1 ≤ L by omega) le_rfl).trans hc.dvd_d
  have hper : IsPeriod (maskFun n S (p (i + 1))) (p (i + 2)) := hc.periodic (i + 1) hi1
  have hei : ∀ k < L, e ∣ y k := fun k hk => by
    have := hc.dvd_le (Nat.zero_le k) hk.le
    rw [hc.p_zero] at this
    exact this.trans (hdy k hk)
  have hmi : reflTot n a L p i = p (i + 2) := by simp [reflTot, hi1]
  have hM : p (i + 2) ∣ reflTot n a L p i + reflTot n a L p (i + 1) := by
    rw [hmi]
    exact dvd_add dvd_rfl (by simpa using hdiv (i + 1) hi1)
  unfold thetaFun
  have h1 := mask_reflect_eq h hq hqd hper hM (x := y i + y (i + 1)) (x' := reflProbe n a L p y i + reflProbe n a L p y (i + 1))
    (Nat.dvd_add (hei i hi0) (hei (i + 1) hi1)) (by
      have := hsum i hi0
      have := hsum (i + 1) hi1
      omega)
  have h2 := mask_reflect_eq h hq hqd hper (M := p (i + 2)) dvd_rfl (x := y i) (x' := reflProbe n a L p y i)
    (hei i hi0) (by have := hsum i hi0; omega)
  rw [h1, h2]

/-- `lem:packing`, `eq:packing-ledger`, `eq:packing-budget`, `eq:original-weight`.  In the
least-period setting of `lem:selection` (`hc`, `hleast`), let `0 < a < n` represent an element of
`supp v`, `W = n - a`, and `t ∈ p_{L-1} ℤ \ P ℤ` with `0 < t < W` and `b(a + t) ≠ b(t)`.  If
`W ≥ C_box - p_1` (`PackingBudget`; in particular if `W ≥ 2 P`, `packingBudget_of_two_mul`), then
the selected probes or their reflected versions can be padded to a positive detector of total `n`
(`PositiveDetector`: `NestedData` with `a + ∑ y + (r + s + z) = n`, `eq:original-weight`, and
`ΔK ≠ 0`); its target `y_{L-1}` is `t`, or `t' = W - t` when reflection was needed. -/
theorem packing [NeZero n] (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p)
    (hleast : ∀ i, i < L → IsLeastPeriod (maskFun n S (p i)) (p (i + 1)))
    {a t : ℕ} (ha0 : 0 < a) (han : a < n) (hva : vFun n S S' (a : ZMod n) ≠ 0)
    (htW : t < n - a) (ht1 : p (L - 1) ∣ t) (ht2 : ¬ p L ∣ t)
    (hΔ : cutInd n S ((a + t : ℕ) : ZMod n) ≠ cutInd n S (t : ZMod n))
    (hbud : PackingBudget p L (n - a)) :
    ∃ (y : ℕ → ℕ) (r s z : ℕ), (y (L - 1) = t ∨ y (L - 1) = n - a - t) ∧
      PositiveDetector n S S' d e L p a r s z y := by
  have hL := hc.one_le
  obtain ⟨y, r, s, z, hyt, hθ, ⟨hr0, hr1, hs0, hs1, hz0, hz1⟩, hH, hlay, hre, hse, hze, hcong⟩ :=
    selection h hc hleast ht1 ht2
  have hPn : p L ∣ n := hc.dvd_n h le_rfl
  have hPd : p L ∣ d := hc.dvd_d
  have hPa : p L ∣ a := hPd.trans (dvd_of_vFun_ne h hva)
  have hPW : p L ∣ n - a := Nat.dvd_sub hPn hPa
  have hp1L : p 1 ∣ p L := hc.dvd_le hL le_rfl
  have hp1W : p 1 ∣ n - a := hp1L.trans hPW
  have he1 : e ∣ p 1 := by
    have := hc.dvd 0 hL
    rwa [hc.p_zero] at this
  have heP : e ∣ p L := he1.trans hp1L
  have het : e ∣ t := by
    have := hc.dvd_le (Nat.zero_le (L - 1)) (by omega)
    rw [hc.p_zero] at this
    exact this.trans ht1
  have hdy : ∀ k < L, p k ∣ y k := fun k hk => (hlay k hk).1
  have hndy : ∀ k < L, ¬ p (k + 1) ∣ y k := fun k hk => (hlay k hk).2
  have hΔ' : deltaFun n S a t ≠ 0 := fun h0 => hΔ (by unfold deltaFun at h0; omega)
  have hθ' : ∀ i, i + 2 ≤ L → thetaFun n S p y i ≠ 0 := fun i hi => (hθ i hi).2.2
  have hH' : Hfun n S S' d e (y 0) r s z ≠ 0 := by
    rw [← probeH_eq_Hfun]; exact hH
  have hp0 : 0 < p 1 := hc.pos h hL
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = ∑ i ∈ Finset.range (L - 1), y i := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ i ∈ Finset.range (L - 1), p (i + 2) := ⟨_, rfl⟩
  have hp1Q : p 1 ∣ Q := by
    rw [hQ]
    refine Finset.dvd_sum fun i hi => ?_
    simp only [Finset.mem_range] at hi
    exact hc.dvd_le (by omega : 1 ≤ i + 2) (by omega)
  have hbox : packBox p L = 3 * p 1 + Q := by rw [packBox_eq p hL, hQ]
  have hcongN : p 1 ∣ t + S1 + (r + s + z) := by
    have : (p 1 : ℤ) ∣ ((t + S1 + (r + s + z) : ℕ) : ℤ) := by
      have e1 : ((t + S1 + (r + s + z) : ℕ) : ℤ) =
          (t : ℤ) + ∑ i ∈ range (L - 1), (y i : ℤ) + r + s + z := by
        rw [hS1]; push_cast; ring
      rw [e1]; exact hcong
    exact_mod_cast this
  have hlast : y (L - 1) = t := hyt
  have hsumy : ∑ k ∈ Finset.range L, y k = S1 + t := by
    rw [sum_range_eq_of_last y hL, hlast, hS1]
  unfold PackingBudget at hbud
  by_cases hfit : a + (S1 + t) + (r + s + z) ≤ n
  · -- the original list fits
    have hmod : p 1 ∣ n - (a + ∑ k ∈ Finset.range L, y k + (r + s + z)) := by
      rw [hsumy]
      have h2 : n - a = (t + S1 + (r + s + z)) + (n - (a + S1 + t + (r + s + z))) := by omega
      rw [h2] at hp1W
      have := (Nat.dvd_add_right hcongN).mp hp1W
      have e : a + (S1 + t) + (r + s + z) = a + S1 + t + (r + s + z) := by ring
      rw [e]; exact this
    obtain ⟨r', hD⟩ := pad h hc ha0 hva hdy hndy hre hse hze (by rw [hsumy]; omega) hmod
      (by rw [hlast]; exact hΔ') hθ' hH'
    exact ⟨y, r', s, z, Or.inl hlast, hD⟩
  · -- reflect
    push Not at hfit
    have hge : n - a - t + p 1 ≤ S1 + (r + s + z) := by
      have hdiv : p 1 ∣ (S1 + (r + s + z)) - (n - a - t) := by
        have h2 : (S1 + (r + s + z)) - (n - a - t) = (t + S1 + (r + s + z)) - (n - a) := by
          omega
        rw [h2]; exact Nat.dvd_sub hcongN hp1W
      have hpos : 0 < (S1 + (r + s + z)) - (n - a - t) := by omega
      have := Nat.le_of_dvd hpos hdiv
      omega
    obtain ⟨Y, hY⟩ : ∃ Y, Y = reflProbe n a L p y := ⟨_, rfl⟩
    have hytot : ∀ k < L, y k ≤ reflTot n a L p k := by
      intro k hk
      unfold reflTot
      split_ifs with hk1
      · exact (hθ k (by omega)).2.1.le
      · have : k = L - 1 := by omega
        subst this; omega
    have hdivtot : ∀ k < L, p (k + 1) ∣ reflTot n a L p k := by
      intro k hk
      unfold reflTot
      split_ifs with hk1
      · exact hc.dvd (k + 1) hk1
      · have : k + 1 = L := by omega
        rw [this]; exact hPW
    have hsum : ∀ k < L, y k + Y k = reflTot n a L p k := fun k hk => by
      rw [hY]; exact reflProbe_add (hytot k hk)
    have hYlast : Y (L - 1) = n - a - t := by
      simp [hY, reflProbe, hlast, show ¬ (L - 1 + 1 < L) by omega]
    obtain ⟨S1', hS1'⟩ : ∃ S1', S1' = ∑ i ∈ Finset.range (L - 1), Y i := ⟨_, rfl⟩
    have hSS : S1 + S1' = Q := by
      rw [hS1, hS1', hQ, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [hsum i (by omega)]
      have hi1 : i + 1 < L := by omega
      simp [reflTot, hi1]
    have hsumY : ∑ k ∈ Finset.range L, Y k = S1' + (n - a - t) := by
      rw [sum_range_eq_of_last Y hL, hYlast, hS1']
    -- reflected bottom probes
    obtain ⟨r', hr'⟩ : ∃ r', r' = p 1 - r := ⟨_, rfl⟩
    obtain ⟨s', hs'⟩ : ∃ s', s' = p 1 - s := ⟨_, rfl⟩
    obtain ⟨z', hz'⟩ : ∃ z', z' = p 1 - z := ⟨_, rfl⟩
    have hfit' : a + ∑ k ∈ Finset.range L, Y k + (r' + s' + z') ≤ n := by
      rw [hsumY]; omega
    have hmod' : p 1 ∣ n - (a + ∑ k ∈ Finset.range L, Y k + (r' + s' + z')) := by
      have h2 : t + S1 + (r + s + z) =
          (n - (a + ∑ k ∈ Finset.range L, Y k + (r' + s' + z'))) + (Q + 3 * p 1) := by
        rw [hsumY]; omega
      rw [h2] at hcongN
      exact (Nat.dvd_add_left (Nat.dvd_add hp1Q (dvd_mul_left (p 1) 3))).mp hcongN
    have hdY : ∀ k < L, p k ∣ Y k := by
      intro k hk
      have h1 : p k ∣ reflTot n a L p k :=
        (hc.dvd k hk).trans (hdivtot k hk)
      have := hsum k hk
      exact (Nat.dvd_add_right (hdy k hk)).mp (this ▸ h1)
    have hndY : ∀ k < L, ¬ p (k + 1) ∣ Y k := by
      intro k hk hh
      apply hndy k hk
      have := hsum k hk
      have h1 := hdivtot k hk
      rw [← this] at h1
      exact (Nat.dvd_add_left hh).mp h1
    have hr'e : ¬ e ∣ r' := by
      intro hh
      apply hre
      rw [hr'] at hh
      have : e ∣ r + (p 1 - r) := by
        rw [Nat.add_sub_cancel' hr1.le]; exact he1
      exact (Nat.dvd_add_left hh).mp this
    have hs'e : ¬ e ∣ s' := by
      intro hh
      apply hse
      rw [hs'] at hh
      have : e ∣ s + (p 1 - s) := by
        rw [Nat.add_sub_cancel' hs1.le]; exact he1
      exact (Nat.dvd_add_left hh).mp this
    have hz'e : ¬ e ∣ z' := by
      intro hh
      apply hze
      rw [hz'] at hh
      have : e ∣ z + (p 1 - z) := by
        rw [Nat.add_sub_cancel' hz1.le]; exact he1
      exact (Nat.dvd_add_left hh).mp this
    have hΔY : deltaFun n S a (Y (L - 1)) ≠ 0 := by
      rw [hYlast, deltaFun_reflect h hPn heP hPd hPa het ht2 han.le htW.le]
      exact neg_ne_zero.mpr hΔ'
    have hθY : ∀ i, i + 2 ≤ L → thetaFun n S p Y i ≠ 0 := by
      intro i hi
      rw [hY, thetaFun_reflect h hc hytot hdivtot hdy hi]
      exact hθ' i hi
    have hHY : Hfun n S S' d e (Y 0) r' s' z' ≠ 0 := by
      have hper0 : IsPeriod (maskFun n S e) (p 1) := by
        simpa [hc.p_zero] using hc.periodic 0 hL
      have hy0e : e ∣ y 0 := by
        have := hc.dvd_le (Nat.zero_le 0) (by omega : 0 ≤ L)
        rw [hc.p_zero] at this
        have h0 := hdy 0 (by omega)
        rw [hc.p_zero] at h0
        exact h0
      have hrr : r + r' = p 1 := by omega
      have hss : s + s' = p 1 := by omega
      have hzz : z + z' = p 1 := by omega
      rw [Hfun_reflect h he1 hper0 hy0e (hsum 0 (by omega)) (hdivtot 0 (by omega)) hrr hss hzz]
      exact neg_ne_zero.mpr hH'
    obtain ⟨r'', hD⟩ := pad h hc ha0 hva hdY hndY hr'e hs'e hz'e hfit' hmod' hΔY hθY hHY
    exact ⟨Y, r'', s', z', Or.inr hYlast, hD⟩

end Packing

end SkewRibbonCoarsenings
