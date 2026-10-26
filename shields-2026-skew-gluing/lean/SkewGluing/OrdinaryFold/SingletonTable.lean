import SkewGluing.OrdinaryFold

/-!
# The phases of a first root at remainder one

Formalizes `shields-2026-skew-gluing.tex`, «Two ordinary roots»
(`prop:gluing-ordinary-fold`),
the display for `w_g = 1` in its proof: in a supplied case-(a) chart the phases `(t, s)`, the
initial budget `ε = C_0` and the projected `(A, B)` phases lie in one of two rows,
`(t, s) = (0, w)` with `ε = 0` and projected phases `(0, 1)`, or `(t, s) = (1, w - 1)` with `ε = 1`
and projected phases `(1, 0)`.  The cap budgets alone leave a third row `(t, s) = (w - 1, 1)`, which
the positivity of the lower copy and the pinch `H_{w_g} = 1` exclude.

The statement is `GcdPair.singleton_table`, on the words of two roots, and
`OrdinaryPair.singleton_table`, for charts.  The end-step column of the table is not stated here.

Sorry-free.
-/

namespace SkewGluing
namespace OrdinaryDrift

variable {A B A0 B0 : ℕ → ℤ} {N g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ}

/-- The three rows the cap budgets allow, before the third is excluded. -/
private theorem GcdPair.singleton_table_aux
    (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hwg : wg = 1) (hb : 1 ≤ b) (hha : ha₁ < b * g + wg) (hhb1 : 1 ≤ hb₁)
    (hMpos : ∀ z, z < b * g + wg → 1 + (if hb₁ ≤ z then 1 else 0) ≤ heightWord A B z) :
    (A0 0 - B0 0 = 0 ∧ ha₁ = 0 ∧ hb₁ = b * g + 1 ∧ ha₁ % g = 0 ∧ hb₁ % g = 1) ∨
    (A0 0 - B0 0 = 1 ∧ ha₁ = 1 ∧ hb₁ = b * g ∧ ha₁ % g = 1 ∧ hb₁ % g = 0) ∨
    (A0 0 - B0 0 = 1 ∧ ha₁ = b * g ∧ hb₁ = 1 ∧ ha₁ % g = 0 ∧ hb₁ % g = 1) := by
  subst hwg
  have sc := h.slotScalars hha hhb1
  have hg := h.g_pos
  have hwg := h.wg_lt
  have hhb := h.root₁.hb_le
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h.drift_full
  obtain ⟨G1, G2, G3, G4⟩ := h.cap_facts
  have hτs := h.tau_struct hha
  have hσs := h.sigma_struct hhb
  have E1 := h.budget_initial
  simp only [hhb1, ite_true] at E1
  have E2 := h.budget_terminal
  simp only [hha, ite_true] at E2
  have hbg : g ≤ b * g := Nat.le_mul_of_pos_left g hb
  have hm := hMpos 1 (by omega)
  rw [d7] at hm
  have hs1 : ¬ (hb₁ ≤ 1) := by
    intro hcon
    simp only [hcon, ite_true] at hm
    omega
  have hmod1 : (b * g + 1) % g = 1 := by
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  have hmod2 : (b * g) % g = 0 := Nat.mul_mod_left b g
  have hmod3 : 1 % g = 1 := Nat.mod_eq_of_lt (by omega)
  have hτ : ha₁ % g = 0 ∨ ha₁ % g = 1 := by have := sc.tau_le; omega
  have hσ : hb₁ % g = 0 ∨ hb₁ % g = 1 := by have := sc.sigma_le; omega
  have hρ := sc.rho
  have hbit1 := h.A0_bit (ha₁ % g) (Nat.mod_lt _ hg)
  have hbit2 := h.B0_bit (hb₁ % g) (Nat.mod_lt _ hg)
  have hbit3 := h.A0_bit 0 hg
  have hbit4 := h.B0_bit 0 hg
  have hbit5 := h.A0_bit 1 hwg
  have hbit6 := h.B0_bit 1 hwg
  have hsum : genSum (incr A0 B0 g) 1 = A0 1 - B0 1 := by
    simp [genSum, incr, hmod3]
  rw [hsum] at d3
  rcases hτ with ht | ht <;> rcases hσ with hs | hs <;>
    simp only [ht, hs] at G3 G4 E1 E2 hρ hbit1 hbit2 ⊢ <;>
    rcases hτs with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ <;>
    rcases hσs with ⟨h5, h6⟩ | ⟨h5, h6, h7, h8⟩ <;> simp only [hmod1, hmod2, hmod3] at * <;>
    split_ifs at E1 E2 <;>
    simp only [and_true, zero_ne_one, one_ne_zero, and_false, or_false, false_or] <;> omega

/-- **The singleton table.**  Let `w_g = 1` and `w = b g + 1` with `b ≥ 1`.  For a first root of
case (a) with nonempty mark whose lower copy has positive heights, the exceptional phases `t = ha₁`,
`s = hb₁`, the budget `ε = A⁰_0 - B⁰_0` and the phases `(t mod g, s mod g)` lie in one of the two
rows of the table.  The row `(t, s) = (w - 1, 1)` cannot occur: a lower middle tail on diagonal `1`
would give the parent height `2` there, against the pinch `H_{w_g} = 1`. -/
theorem GcdPair.singleton_table (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hwg : wg = 1) (hb : 1 ≤ b) (hha : ha₁ < b * g + wg) (hhb1 : 1 ≤ hb₁)
    (hMpos : ∀ z, z < b * g + wg → 1 + (if hb₁ ≤ z then 1 else 0) ≤ heightWord A B z) :
    (A0 0 - B0 0 = 0 ∧ ha₁ = 0 ∧ hb₁ = b * g + 1 ∧ ha₁ % g = 0 ∧ hb₁ % g = 1) ∨
    (A0 0 - B0 0 = 1 ∧ ha₁ = 1 ∧ hb₁ = b * g ∧ ha₁ % g = 1 ∧ hb₁ % g = 0) := by
  rcases h.singleton_table_aux hwg hb hha hhb1 hMpos with k | k | ⟨-, -, k3, -, -⟩
  · exact Or.inl k
  · exact Or.inr k
  · exfalso
    subst hwg
    have hg := h.g_pos
    have hbg : g ≤ b * g := Nat.le_mul_of_pos_left g hb
    obtain ⟨-, -, -, -, -, -, d7, -, -, -⟩ := h.drift_full
    have hm := hMpos 1 (by omega)
    rw [d7] at hm
    simp only [k3, le_refl, ite_true] at hm
    omega

end OrdinaryDrift


open OrdinaryFold

/-- **The singleton table, for charts.**  Two ordinary roots of nondividing periods in the setting
`eq:gluing-gcd-data` with `w_g = 1`, the first of case (a) and of width `w ≥ 2`: for its phases
`s`, `t` and the generic bits `A⁰`, `B⁰`, with `ε = A⁰_0 - B⁰_0`, one of
`(t, s) = (0, w)`, `ε = 0`, projected phases `(0, 1)`;
`(t, s) = (1, w - 1)`, `ε = 1`, projected phases `(1, 0)`
holds, the projected phases being `(t mod g, s mod g)`. -/
theorem OrdinaryPair.singleton_table {F : Diagram} {χ₁ χ₂ : Chart} (h : OrdinaryPair F χ₁ χ₂)
    (hca : χ₁.ω.case = .a) {g a b c d M : ℕ} (hd : GcdData F χ₁ χ₂ g a b c d M 1)
    (hw : 2 ≤ χ₁.ω.width) :
    ∃ (s t : ℤ) (A0 B0 : ℕ → ℤ), χ₁.ω.IsPhases s t ∧
      ((A0 0 - B0 0 = 0 ∧ t = 0 ∧ s = (χ₁.ω.width : ℤ) ∧ t % (g : ℤ) = 0 ∧ s % (g : ℤ) = 1) ∨
      (A0 0 - B0 0 = 1 ∧ t = 1 ∧ s = (χ₁.ω.width : ℤ) - 1 ∧ t % (g : ℤ) = 1 ∧
        s % (g : ℤ) = 0)) := by
  obtain ⟨s₁, t₁, s₂, t₂, A0, B0, hph₁, hph₂, hG⟩ := h.gcdPair hd
  have e1 : ordHoleA χ₁.ω.case s₁ t₁ = t₁ := by simp [ordHoleA, hca]
  have e2 : ordHoleB χ₁.ω.case s₁ t₁ = s₁ := by simp [ordHoleB, hca]
  rw [e1, e2] at hG
  have hw1 := hd.width₁
  have hg := hG.g_pos
  have hwg := hG.wg_lt
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph₁
  have hwz : χ₁.ω.widthZ = (χ₁.ω.width : ℤ) := rfl
  have hb : 1 ≤ b := by
    by_contra hcon
    have : b = 0 := by omega
    subst this
    omega
  have hha : t₁.toNat < b * g + 1 := by omega
  have hhb1 : 1 ≤ s₁.toNat := by omega
  have hMpos : ∀ z, z < b * g + 1 →
      1 + (if s₁.toNat ≤ z then 1 else 0) ≤ heightWord (ordFold_wA F) (ordFold_wB F) z := by
    intro z hz
    exact h.proper₁.markHeights h.chart₁ hca h.nonempty₁ hph₁ z (by omega)
  refine ⟨s₁, t₁, A0, B0, hph₁, ?_⟩
  have key := hG.singleton_table rfl hb hha hhb1 hMpos
  have hgz : (0 : ℤ) < g := by exact_mod_cast hg
  rcases key with ⟨k1, k2, k3, k4, k5⟩ | ⟨k1, k2, k3, k4, k5⟩
  · left
    refine ⟨k1, by omega, by omega, ?_, ?_⟩
    · have : t₁ = 0 := by omega
      rw [this]; simp
    · have : s₁ % (g : ℤ) = ((s₁.toNat % g : ℕ) : ℤ) := by
        rw [Int.natCast_mod, Int.toNat_of_nonneg (by omega)]
      rw [this, k5]; simp
  · right
    refine ⟨k1, by omega, by omega, ?_, ?_⟩
    · have : t₁ % (g : ℤ) = ((t₁.toNat % g : ℕ) : ℤ) := by
        rw [Int.natCast_mod, Int.toNat_of_nonneg (by omega)]
      rw [this, k4]; simp
    · have : s₁ % (g : ℤ) = ((s₁.toNat % g : ℕ) : ℤ) := by
        rw [Int.natCast_mod, Int.toNat_of_nonneg (by omega)]
      rw [this, k5]; simp

/-! ### Checked example

Two ordinary roots of the row `(15)`, of periods `4` and `6` and widths `3` and `3`: `g = 2`,
`w_g = 1`, and the first width is at least two. -/

/-- The row `(7)` with the mark of period four, width three. -/
def ordFold_rowSevenWideMark : MarkedInner where
  E := skewOf [7] []
  W := {(0, 0), (0, 1), (0, 2)}
  v := (0, 4)
  case := .a

/-- The row `(9)` with the mark of period six, width three. -/
def ordFold_rowNineMark : MarkedInner where
  E := skewOf [9] []
  W := {(0, 0), (0, 1), (0, 2)}
  v := (0, 6)
  case := .a

example : ordFold_rowSevenWideMark.IsLegal ∧ ordFold_rowNineMark.IsLegal := by decide +kernel

theorem ordFold_row15_ordinaryPair : OrdinaryPair (skewOf [15] [])
    ⟨skewOf [3] [], ordFold_rowSevenWideMark⟩ ⟨skewOf [2] [], ordFold_rowNineMark⟩ := by
  refine ⟨?_, ?_, ⟨0, ?_⟩, ⟨0, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Chart.IsProperLegal; decide +kernel
  · unfold Chart.IsProperLegal; decide +kernel
  · decide +kernel
  · decide +kernel
  all_goals decide +kernel

theorem ordFold_row15_gcdData : GcdData (skewOf [15] [])
    ⟨skewOf [3] [], ordFold_rowSevenWideMark⟩ ⟨skewOf [2] [], ordFold_rowNineMark⟩ 2 2 1 3 1 7 1 :=
  by
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by norm_num, ?_, by norm_num, ?_, ?_⟩ <;>
    decide +kernel

/-- The singleton table applies to the roots of the row `(15)`. -/
example := ordFold_row15_ordinaryPair.singleton_table rfl ordFold_row15_gcdData (by decide +kernel)

end SkewGluing
