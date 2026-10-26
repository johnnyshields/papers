import SkewGluing.PeriodWords.Core

/-!
# The three small-overlap cases of the period-word lemma

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-periods`).

For an equivalence relation `J` containing the edges of a period `s` (with at most one exceptional
residue) and of a larger period `ℓ`, the hypotheses of `related_of_gcd_dvd` are verified in the
three cases used by `lem:gluing-periods`:

* `s` full, `ℓ` with at most one exceptional residue, length `≥ 2ℓ - 1` (the shorter clause of
  (i));
* `s` full, `ℓ` with at most two exceptional residues in `[0, u]`, length `≥ 2ℓ + u - 1` (iii);
* `s` with at most one exceptional residue, `ℓ` with at most one in `[0, u]`, length
  `≥ 2ℓ + u - 1` (ii, and (i) when the full period is the larger).

Sorry-free.
-/

namespace SkewGluing
namespace PeriodWords

variable {J : ℤ → ℤ → Prop}

theorem eq_of_dvd_sub_of_mem_Icc {s : ℕ} {y y' : ℤ} (hy : y ∈ Finset.Icc (1 : ℤ) s)
    (hy' : y' ∈ Finset.Icc (1 : ℤ) s) (h : (s : ℤ) ∣ y - y') : y = y' := by
  simp only [Finset.mem_Icc] at hy hy'
  have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
  omega

/-- Below the period `ℓ`, residues are positions. -/
theorem emod_eq_self_of_lt {ℓ : ℕ} {y : ℤ} (h0 : 0 ≤ y) (h1 : y < ℓ) : y % (ℓ : ℤ) = y :=
  Int.emod_eq_of_lt h0 h1

/-- **Full smaller period, one exceptional residue of the larger period, length `2ℓ - 1`.** -/
theorem related_full_one_hole (hJ : Equivalence J) {L s ℓ : ℕ} {T : Finset ℤ}
    (hs : 0 < s) (hsℓ : s < ℓ) (hnd : ¬ s ∣ ℓ) (hT : T.card ≤ 1) (hL : 2 * ℓ ≤ L + 1)
    (heS : ∀ x y, periodEdge L s ∅ x y → J x y) (heT : ∀ x y, periodEdge L ℓ T x y → J x y)
    {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd s ℓ : ℕ) : ℤ) ∣ y - x) : J x y := by
  refine related_of_gcd_dvd hJ hs hnd (by omega) (by simp) heS heT ?_ (by simp) hx hy hxy
    (by simp) (by simp)
  intro y hy y' hy' hm hm'
  have key : ∀ y ∈ Finset.Icc (1 : ℤ) s, Missing L s ℓ ∅ T y → y ∈ T := by
    intro y hy hm
    simp only [Finset.mem_Icc] at hy
    have hye : y % (ℓ : ℤ) = y := emod_eq_self_of_lt (by omega) (by omega)
    by_contra hyT
    simp only [Missing, Finset.notMem_empty, false_or] at hm
    apply hm
    refine ⟨y, ?_, by rwa [hye], by simp⟩
    simp only [Finset.mem_Icc]
    omega
  exact Finset.card_le_one.1 hT y (key y hy hm) y' (key y' hy' hm')

/-- **Full smaller period, at most two exceptional residues of the larger period in `[0, u]`,
length `2ℓ + u - 1`.**

**Differs from the paper's route.** The paper rules out two lost cyclic edges by forcing `ℓ = 2s`;
here the two multiples of `ℓ` in `(0, 2ℓ)` that the exchange produces are compared directly. -/
theorem related_full_two_holes (hJ : Equivalence J) {L s ℓ u : ℕ} {T : Finset ℤ}
    (hs : 0 < s) (hsℓ : s < ℓ) (hnd : ¬ s ∣ ℓ) (hTu : ∀ t ∈ T, 0 ≤ t ∧ t ≤ u)
    (hT : T.card ≤ 2) (hL : 2 * ℓ + u ≤ L + 1)
    (heS : ∀ x y, periodEdge L s ∅ x y → J x y) (heT : ∀ x y, periodEdge L ℓ T x y → J x y)
    {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd s ℓ : ℕ) : ℤ) ∣ y - x) : J x y := by
  refine related_of_gcd_dvd hJ hs hnd (by omega) (by simp) heS heT ?_ (by simp) hx hy hxy
    (by simp) (by simp)
  have hsℓ' : (s : ℤ) < ℓ := by exact_mod_cast hsℓ
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  have hℓ' : (0 : ℤ) < ℓ := by omega
  -- a missing class has both representatives `y` and `y + s` exceptional
  have key : ∀ y ∈ Finset.Icc (1 : ℤ) s, Missing L s ℓ ∅ T y →
      y ∈ T ∧ (y + s) % (ℓ : ℤ) ∈ T := by
    intro y hy hm
    simp only [Finset.mem_Icc] at hy
    have hye : y % (ℓ : ℤ) = y := emod_eq_self_of_lt (by omega) (by omega)
    simp only [Missing, Finset.notMem_empty, false_or] at hm
    have hyT : y ∈ T := by
      by_contra hyT
      apply hm
      refine ⟨y, ?_, by rwa [hye], by simp⟩
      simp only [Finset.mem_Icc]
      omega
    refine ⟨hyT, ?_⟩
    by_contra hyT'
    apply hm
    have := hTu y hyT
    refine ⟨y + s, ?_, hyT', ⟨1, by ring⟩⟩
    simp only [Finset.mem_Icc]
    omega
  intro y hy y' hy' hm hm'
  by_contra hne
  obtain ⟨hyT, hys⟩ := key y hy hm
  obtain ⟨hyT', hys'⟩ := key y' hy' hm'
  have hy1 := hy
  have hy1' := hy'
  simp only [Finset.mem_Icc] at hy1 hy1'
  have hTeq : T = {y, y'} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    · rw [Finset.card_pair hne]; exact hT
  have hne1 : (y + s) % (ℓ : ℤ) ≠ y := by
    intro h
    have h2 : (ℓ : ℤ) ∣ s := by
      have := dvd_sub_of_emod_eq (n := ℓ) (a := y + s) (b := y) (by
        rw [h]; exact (emod_eq_self_of_lt (by omega) (by omega)).symm)
      simpa using this
    have := Int.le_of_dvd hs' h2
    omega
  have hne2 : (y' + s) % (ℓ : ℤ) ≠ y' := by
    intro h
    have h2 : (ℓ : ℤ) ∣ s := by
      have := dvd_sub_of_emod_eq (n := ℓ) (a := y' + s) (b := y') (by
        rw [h]; exact (emod_eq_self_of_lt (by omega) (by omega)).symm)
      simpa using this
    have := Int.le_of_dvd hs' h2
    omega
  rw [hTeq] at hys hys'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hys hys'
  have e1 : (y + s) % (ℓ : ℤ) = y' := hys.resolve_left hne1
  have e2 : (y' + s) % (ℓ : ℤ) = y := hys'.resolve_right hne2
  have hy'e : y' % (ℓ : ℤ) = y' := emod_eq_self_of_lt (by omega) (by omega)
  have hye : y % (ℓ : ℤ) = y := emod_eq_self_of_lt (by omega) (by omega)
  obtain ⟨m1, hm1⟩ := dvd_sub_of_emod_eq (n := ℓ) (a := y + s) (b := y') (by rw [e1, hy'e])
  obtain ⟨m2, hm2⟩ := dvd_sub_of_emod_eq (n := ℓ) (a := y' + s) (b := y) (by rw [e2, hye])
  have hm1' : 1 ≤ m1 := by
    by_contra h
    nlinarith
  have hm2' : 1 ≤ m2 := by
    by_contra h
    nlinarith
  nlinarith

/-- **Exceptional residues in both periods, at most one in each, the larger one in `[0, u]`,
length `2ℓ + u - 1`.**  The side condition `2ℓ ≤ L ∨ 0 ∈ T` only excludes the position `ℓ` at
length `2ℓ - 1` with no exceptional residue `0` of the larger period. -/
theorem related_hole_one_hole (hJ : Equivalence J) {L s ℓ u : ℕ} {Ss T : Finset ℤ}
    (hs : 0 < s) (hsℓ : s < ℓ) (hnd : ¬ s ∣ ℓ) (hSs : Ss.card ≤ 1) (hTu : ∀ t ∈ T, 0 ≤ t ∧ t ≤ u)
    (hT : T.card ≤ 1) (hL : 2 * ℓ + u ≤ L + 1) (hL' : 2 * ℓ ≤ L ∨ (0 : ℤ) ∈ T)
    (heS : ∀ x y, periodEdge L s Ss x y → J x y) (heT : ∀ x y, periodEdge L ℓ T x y → J x y)
    {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd s ℓ : ℕ) : ℤ) ∣ y - x)
    (hx' : ¬ (x % (s : ℤ) ∈ Ss ∧ x % (ℓ : ℤ) ∈ T))
    (hy' : ¬ (y % (s : ℤ) ∈ Ss ∧ y % (ℓ : ℤ) ∈ T)) : J x y := by
  have hsℓ' : (s : ℤ) < ℓ := by exact_mod_cast hsℓ
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  refine related_of_gcd_dvd hJ hs hnd (by omega) (Finset.card_le_one.1 hSs) heS heT ?_ ?_ hx hy hxy
    hx' hy'
  · intro y hy y' hy' hm hm'
    have key : ∀ y ∈ Finset.Icc (1 : ℤ) s, Missing L s ℓ Ss T y → y % (s : ℤ) ∈ Ss := by
      intro y hy hm
      by_contra hyS
      apply hm.elim hyS
      simp only [Finset.mem_Icc] at hy
      have hye : y % (ℓ : ℤ) = y := emod_eq_self_of_lt (by omega) (by omega)
      by_cases hyT : y % (ℓ : ℤ) ∈ T
      · rw [hye] at hyT
        have := hTu y hyT
        have hz : (y + s) % (ℓ : ℤ) ∉ T := by
          intro h
          have h2 := Finset.card_le_one.1 hT _ h _ hyT
          have h3 : (ℓ : ℤ) ∣ s := by
            simpa using dvd_sub_of_emod_eq (n := ℓ) (a := y + s) (b := y) (by
              rw [h2]; exact (emod_eq_self_of_lt (by omega) (by omega)).symm)
          have := Int.le_of_dvd hs' h3
          omega
        refine fun h => ?_
        exact absurd (show Avail L s ℓ T y from ⟨y + s, by
          simp only [Finset.mem_Icc]; omega, hz, ⟨1, by ring⟩⟩) h
      · exact fun h => absurd (show Avail L s ℓ T y from ⟨y, by
          simp only [Finset.mem_Icc]; omega, hyT, by simp⟩) h
    exact eq_of_dvd_sub_of_mem_Icc hy hy' (dvd_sub_of_emod_eq
      (Finset.card_le_one.1 hSs _ (key y hy hm) _ (key y' hy' hm')))
  · intro z hz hzS hzT
    simp only [Finset.mem_Icc] at hz ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hL2 : ¬ 2 * ℓ ≤ L := by omega
    have h0 : (0 : ℤ) ∈ T := hL'.resolve_left hL2
    have hzl : z = ℓ := by omega
    apply hzT
    rw [hzl, Int.emod_self]
    exact h0

end PeriodWords
end SkewGluing
