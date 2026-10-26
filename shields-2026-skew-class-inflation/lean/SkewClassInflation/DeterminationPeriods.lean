/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.DeterminationPropagation
import SkewClassInflation.GuardedPeriodExtension

/-!
# Signed-cut periods from actual undetermined coordinates

The finite prefix-gcd induction used in the nonsymmetric ribbon input to
`lem:overlap-power-rigidity` of `shields-2026-skew-class-inflation.tex`.
The period and its strict lower bound are derived from actual coarsening
coefficients, not supplied as hypotheses.  Sorry-free.
-/

namespace SkewClassInflation

/-- The gcd of all actual undetermined coordinates through the specified point. -/
noncomputable def undeterminedPrefixGcd {N : ℕ} (α : Composition N) (k m : ℕ) : ℕ :=
  ((undeterminedCuts α k).filter (fun j => j ≤ m)).gcd id

/-- A prefix gcd divides every actual undetermined coordinate in that prefix. -/
theorem undeterminedPrefixGcd_dvd {N : ℕ} (α : Composition N) (k m j : ℕ)
    (hj : j ∈ undeterminedCuts α k) (hjm : j ≤ m) : undeterminedPrefixGcd α k m ∣ j :=
  Finset.gcd_dvd (Finset.mem_filter.mpr ⟨hj, hjm⟩)

/-- Excluding every earlier undetermined coordinate by a divisor produces determination. -/
theorem cutDetermined_of_prefix_divisibility {N : ℕ} (α : Composition N) (k c d : ℕ)
    (hdiv : ∀ j ∈ undeterminedCuts α k, j < d → c ∣ j)
    (x : ℕ) (hx : 0 < x) (hxd : x < d) (hdN : d ≤ N) (hn : ¬ c ∣ x) :
    cutDetermined α k x := by
  classical
  by_contra hnot
  exact hn (hdiv x (Finset.mem_filter.mpr
    ⟨Finset.mem_Ioo.mpr ⟨hx, hxd.trans_le hdN⟩, hnot⟩) hxd)

/-- Every finite undetermined prefix supplies its true signed period and excludes the first cut. -/
theorem undetermined_prefix_period {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1) :
    ∀ m, m ∈ undeterminedCuts α k →
      0 < undeterminedPrefixGcd α k m ∧ ¬ undeterminedPrefixGcd α k m ∣ k ∧
      (∀ x, 0 < x → x < undeterminedPrefixGcd α k m →
        compositionCutSign α x = -compositionCutSign α (undeterminedPrefixGcd α k m - x)) ∧
      (∀ x, 0 < x → x + undeterminedPrefixGcd α k m < m →
        ¬ undeterminedPrefixGcd α k m ∣ x →
        compositionCutSign α (x + undeterminedPrefixGcd α k m) = compositionCutSign α x) := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    have hmN := Finset.mem_Ioo.mp (Finset.mem_filter.mp hm).1
    have hkm := undeterminedCuts_after_first α k hk hfirst m hm
    have hk0 : 0 < k := (properCuts_bounds α k hk).1
    let S := (undeterminedCuts α k).filter (fun j => j < m)
    by_cases hS : S.Nonempty
    · let p := S.max' hS
      have hpS : p ∈ S := Finset.max'_mem S hS
      have hpT : p ∈ undeterminedCuts α k := (Finset.mem_filter.mp hpS).1
      have hpm : p < m := (Finset.mem_filter.mp hpS).2
      have hp0 : 0 < p := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hpT).1).1
      obtain ⟨hc, hck, hanti, hperiod⟩ := ih p hpm hpT
      let c := undeterminedPrefixGcd α k p
      have hcp : c ∣ p := undeterminedPrefixGcd_dvd α k p p hpT le_rfl
      have hcm : c < m := (Nat.le_of_dvd hp0 hcp).trans_lt hpm
      have hdiv : ∀ j ∈ undeterminedCuts α k, j < m → c ∣ j := by
        intro j hj hjm
        exact undeterminedPrefixGcd_dvd α k p j hj
          (Finset.le_max' S j (Finset.mem_filter.mpr ⟨hj, hjm⟩))
      have hdet (x : ℕ) (hx : 0 < x) (hxm : x < m) (hn : ¬ c ∣ x) :
          cutDetermined α k x :=
        cutDetermined_of_prefix_divisibility α k c m hdiv x hx hxm hmN.2.le hn
      have hlarge : ∀ x, 0 < x → x + p < m → ¬ c ∣ x → ¬ c ∣ x + p →
          compositionCutSign α (x + p) = compositionCutSign α x := by
        intro x hx hxp hn hnext
        exact undetermined_cutSign_shift α k p hpT x hx (hxp.trans hmN.2)
          (hdet x hx (by omega) hn) (hdet (x + p) (by omega) hxp hnext)
      have hsmall : ∀ x, 0 < x → x + c < p → ¬ c ∣ x → ¬ c ∣ x + c →
          compositionCutSign α (x + c) = compositionCutSign α x := by
        intro x hx hxp hn _
        exact hperiod x hx hxp hn
      have hstep := guarded_period_extend (compositionCutSign α) c p m hc hp0 hcp
        hsmall hlarge
      have hantiM : ∀ x, 0 < x → x < m → periodPointDefined true c x →
          periodPointDefined true c (m - x) →
          compositionCutSign α x = -compositionCutSign α (m - x) := by
        intro x hx hxm hn hnext
        have hn' : ¬ c ∣ x := hn.resolve_left (by decide)
        have hnext' : ¬ c ∣ m - x := hnext.resolve_left (by decide)
        have he := undetermined_cutSign_antisymm α k m hm x hx hxm
          (hdet x hx hxm hn') (hdet (m - x) (by omega) (by omega) hnext')
        omega
      obtain ⟨hzero, hnextPeriod, hnextAnti⟩ :=
        antisymmetric_interval_gcd (compositionCutSign α) true c m hc hcm hanti hantiM
          (by
            intro x hx hxm hn hnext
            exact hstep x hx hxm (hn.resolve_left (by decide))
              (hnext.resolve_left (by decide)))
      have hprefix : (undeterminedCuts α k).filter (fun j => j ≤ m) =
          insert m ((undeterminedCuts α k).filter (fun j => j ≤ p)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hj, hjm⟩
          by_cases he : j = m
          · exact Or.inl he
          · exact Or.inr ⟨hj, Finset.le_max' S j
              (Finset.mem_filter.mpr ⟨hj, by omega⟩)⟩
        · rintro (rfl | ⟨hj, hjp⟩)
          · exact ⟨hm, le_rfl⟩
          · exact ⟨hj, by omega⟩
      have hgcd : undeterminedPrefixGcd α k m = c.gcd m := by
        unfold undeterminedPrefixGcd
        rw [hprefix, Finset.gcd_insert]
        exact Nat.gcd_comm _ _
      rw [hgcd]
      refine ⟨Nat.gcd_pos_of_pos_left m hc, ?_, hnextAnti, hnextPeriod⟩
      intro hd
      have hz := hzero k hk0 hkm (Or.inr hck) hd
      have ht : compositionCutType α k = 1 := by
        simp [compositionCutType, hk, hkr]
      rw [compositionCutSign_of_one α k ht, ite_eq_left hk] at hz
      omega
    · have hsingle : (undeterminedCuts α k).filter (fun j => j ≤ m) = {m} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hj, hjm⟩
          by_contra he
          exact hS ⟨j, Finset.mem_filter.mpr ⟨hj, by omega⟩⟩
        · rintro rfl
          exact ⟨hm, le_rfl⟩
      have hgcd : undeterminedPrefixGcd α k m = m := by
        simp [undeterminedPrefixGcd, hsingle]
      rw [hgcd]
      refine ⟨hmN.1, ?_, ?_, ?_⟩
      · intro hd
        have := Nat.le_of_dvd hk0 hd
        omega
      · intro x hx hxm
        have hmin : ∀ j < m, cutDetermined α k j := by
          intro j hjm
          by_cases hj0 : 0 < j
          · by_contra hnot
            exact hS ⟨j, Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hj0, hjm.trans hmN.2⟩,
                hnot⟩, hjm⟩⟩
          · exact cutDetermined_of_not_one α k j (by
              have he : j = 0 := by omega
              subst j
              rw [compositionCutType_outside α 0 (Or.inl rfl)]
              omega)
        have he := first_undetermined_cutSign_antisymm α k m hm hmin x hx hxm
        omega
      · intro x hx hxm
        omega

/-- The actual undetermined gcd is a nontrivial signed-cut period of the entire interval. -/
theorem undeterminedGcd_signed_period {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty) :
    1 < undeterminedGcd α k ∧ undeterminedGcd α k < N ∧
      undeterminedGcd α k ∣ N ∧ ¬ undeterminedGcd α k ∣ k ∧
      ∀ x, 0 < x → x + undeterminedGcd α k < N → ¬ undeterminedGcd α k ∣ x →
        compositionCutSign α (x + undeterminedGcd α k) = compositionCutSign α x := by
  classical
  let m := (undeterminedCuts α k).max' hne
  have hm : m ∈ undeterminedCuts α k := Finset.max'_mem _ _
  have hm0 := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hm).1).1
  have hprefix : (undeterminedCuts α k).filter (fun j => j ≤ m) =
      undeterminedCuts α k := by
    apply Finset.filter_eq_self.mpr
    intro j hj
    exact Finset.le_max' _ j hj
  have hgcd : undeterminedPrefixGcd α k m = undeterminedGcd α k := by
    unfold undeterminedPrefixGcd undeterminedGcd
    rw [hprefix]
  obtain ⟨hc, hck, _, hperiod⟩ := undetermined_prefix_period α k hk hkr hfirst m hm
  rw [hgcd] at hc hck hperiod
  let c := undeterminedGcd α k
  have hcm : c ∣ m := undeterminedGcd_dvd α k m hm
  have hc1 : 1 < c := by
    by_contra he
    have heq : c = 1 := by omega
    apply hck
    change c ∣ k
    rw [heq]
    exact one_dvd k
  have hdiv : ∀ j ∈ undeterminedCuts α k, j < N → c ∣ j := by
    intro j hj _
    exact undeterminedGcd_dvd α k j hj
  have hdet (x : ℕ) (hx : 0 < x) (hxN : x < N) (hn : ¬ c ∣ x) :
      cutDetermined α k x :=
    cutDetermined_of_prefix_divisibility α k c N hdiv x hx hxN le_rfl hn
  have hsmall : ∀ x, 0 < x → x + c < m → ¬ c ∣ x → ¬ c ∣ x + c →
      compositionCutSign α (x + c) = compositionCutSign α x := by
    intro x hx hxm hn _
    exact hperiod x hx hxm hn
  have hlarge : ∀ x, 0 < x → x + m < N → ¬ c ∣ x → ¬ c ∣ x + m →
      compositionCutSign α (x + m) = compositionCutSign α x := by
    intro x hx hxm hn hnext
    exact undetermined_cutSign_shift α k m hm x hx hxm
      (hdet x hx (by omega) hn) (hdet (x + m) (by omega) hxm hnext)
  have hall := guarded_period_extend (compositionCutSign α) c m N hc hm0 hcm hsmall hlarge
  refine ⟨hc1, undeterminedGcd_lt_weight α k hne,
    undeterminedGcd_dvd_weight α k hne, hck, ?_⟩
  intro x hx hxN hn
  exact hall x hx hxN hn (by
    intro he
    exact hn ((Nat.dvd_add_iff_left (dvd_refl c)).mpr he))

/-- Nonreconstructibility supplies an oriented source with a genuine nontrivial signed period. -/
theorem nonreconstructible_exists_signed_period {N : ℕ} (α : Composition N)
    (hn : ¬ ribbonReconstructible α) :
    ∃ γ : Composition N, ∃ k p : ℕ, (γ = α ∨ γ = α.reverse) ∧
      coarseningInventory γ = coarseningInventory α ∧
      1 < p ∧ p < N ∧ p ∣ N ∧ ¬ p ∣ k ∧ k ∈ properCuts γ ∧
      ∀ x, 0 < x → x + p < N → ¬ p ∣ x →
        compositionCutSign γ (x + p) = compositionCutSign γ x := by
  obtain ⟨γ, k, hγ, hInv, hnγ, _, _, _, hk, hkr, hfirst⟩ :=
    exists_normalized_first_single_cut α hn
  have hne := undeterminedCuts_nonempty γ hnγ k hk hkr
  obtain ⟨hp, hpN, hdiv, hnot, hperiod⟩ :=
    undeterminedGcd_signed_period γ k hk hkr hfirst hne
  exact ⟨γ, k, undeterminedGcd γ k, hγ, hInv, hp, hpN, hdiv, hnot, hk, hperiod⟩

end SkewClassInflation
