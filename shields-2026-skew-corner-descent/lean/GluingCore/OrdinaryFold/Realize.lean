/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/OrdinaryFold/Realize.lean`. -/
import GluingCore.OrdinaryFold.Generic
import GluingCore.OrdinaryFold.Compose
import GluingCore.CommonFactorGraph

/-!
# The fold of two ordinary roots: the root from the slot form of the words

Formalizes `shields-2026-skew-factor-gluing.tex`, «Two ordinary roots»
(`prop:gluing-ordinary-fold`),
the construction of the period-`g` root from the generic boundary words.

`SlotWords` is the *slot form* of the boundary words of a diagram `F` of span `N = M g + w_g`
(`0 < w_g < g`): the words are the generic `g`-periodic words of `lem:gluing-periods` (ii) except on
the residues `τ` (northwest word) and `σ` (southeast word), the exceptional bits at these residues
at the two ends are those of `eq:gluing-caps`, and the four singleton diagonals
`eq:gluing-pinches` of `lem:gluing-ordinary-drift` hold.

`SlotWords.exists_root` builds, from the slot form, the inner `G`
(`GluingCore.OrdinaryFold.Generic`),
the legal case-(a) mark on it (`GluingCore.OrdinaryFold.Mark`), the outer `D` with the bits
`A^D_j = A_{jg+τ}`, `B^D_j = B_{jg+σ}` (the reading of the outer from the slots, as in
`eq:gluing-mixed-inverse` for the mixed charts), and proves `F = D ∘_ω G` by comparing boundary
words (`GluingCore.OrdinaryFold.Compose`).

Sorry-free.
-/

namespace GluingCore
namespace OrdinaryFold

open OrdinaryDrift

/-- The slot form, case (a), of the boundary words `(A, B)` of a diagram of span
`N = M g + w_g`, with generic bits `A⁰`, `B⁰` and slots `τ < w_g`, `1 ≤ σ ≤ w_g`.  The last four
fields are the private-endpoint bits of the two horizontal attachments (`A⁰_{w_g} = 0`,
`B⁰_0 = 0`, `A⁰_0 = 1` if `τ ≥ 1`) and the positivity of the heights of the retained lower copy. -/
structure SlotWords (A B A0 B0 : ℕ → ℤ) (N g M wg τ σ : ℕ) : Prop where
  N_eq : N = M * g + wg
  M_ge : 2 ≤ M
  wg_pos : 1 ≤ wg
  wg_lt : wg < g
  τ_lt : τ < wg
  σ_pos : 1 ≤ σ
  σ_le : σ ≤ wg
  words : WordData A B N
  A0_bit : ∀ j, j < g → A0 j = 0 ∨ A0 j = 1
  B0_bit : ∀ j, j < g → B0 j = 0 ∨ B0 j = 1
  delta : ∑ j ∈ Finset.range g, A0 j = ∑ j ∈ Finset.range g, B0 j
  rho : A0 τ = B0 σ
  genA : ∀ x, 1 ≤ x → x < N → x % g ≠ τ → A x = A0 (x % g)
  genB : ∀ x, 1 ≤ x → x < N → x % g ≠ σ → B x = B0 (x % g)
  capA_init : 1 ≤ τ → A τ = 1
  capB_init : B σ = 0
  capA_term : A (N - wg + τ) = 0
  capB_term : σ < wg → B (N - wg + σ) = 1
  pinch_wg : heightWord A B wg = 1
  pinch_g : heightWord A B (g - 1) = 1
  pinch_Ng : heightWord A B (N - g) = 1
  pinch_Nwg : heightWord A B (N - 1 - wg) = 1
  pos : ∀ r, r < wg → 1 + (if σ ≤ r then 1 else 0) ≤ heightWord A B r
  A_wg : A0 wg = 0
  B_zero : B0 0 = 0
  A_zero : 1 ≤ τ → A0 0 = 1

variable {A B A0 B0 : ℕ → ℤ} {N g M wg τ σ : ℕ}

namespace SlotWords

theorem first_block (h : SlotWords A B A0 B0 N g M wg τ σ) {j : ℕ} (hj1 : 1 ≤ j) (hjg : j < g) :
    innerA A0 g τ j = A j ∧ innerB B0 g wg σ j = B j := by
  have hN := h.N_eq
  have hM := h.M_ge
  have hjN : j < N := by
    have : g ≤ M * g := Nat.le_mul_of_pos_left g (by omega)
    omega
  constructor
  · by_cases hjt : j = τ
    · subst hjt
      simp [innerA, hj1, h.capA_init hj1]
    · have h1 : ¬ (1 ≤ τ ∧ j = τ) := fun hh => hjt hh.2
      have h2 : j ≠ g + τ := by omega
      simp only [innerA, h1, h2, ite_false]
      rw [h.genA j hj1 hjN (by rw [Nat.mod_eq_of_lt hjg]; exact hjt), Nat.mod_eq_of_lt hjg]
  · by_cases hjs : j = σ
    · subst hjs
      simp [innerB, h.capB_init]
    · have h2 : ¬ (σ < wg ∧ j = g + σ) := by omega
      simp only [innerB, hjs, h2, ite_false]
      rw [h.genB j hj1 hjN (by rw [Nat.mod_eq_of_lt hjg]; exact hjs), Nat.mod_eq_of_lt hjg]

theorem last_block (h : SlotWords A B A0 B0 N g M wg τ σ) {i : ℕ} (hi : i < wg) :
    innerA A0 g τ (g + i) = A (N - wg + i) ∧ innerB B0 g wg σ (g + i) = B (N - wg + i) := by
  have hN := h.N_eq
  have hM := h.M_ge
  have hwg := h.wg_lt
  have hτ := h.τ_lt
  have hσ := h.σ_le
  have hmod : (N - wg + i) % g = i := by
    have : N - wg + i = i + g * M := by rw [hN]; simp; ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hx1 : 1 ≤ N - wg + i := by
    have : g ≤ M * g := Nat.le_mul_of_pos_left g (by omega)
    omega
  have hxN : N - wg + i < N := by omega
  constructor
  · by_cases hit : i = τ
    · subst hit
      have h1 : ¬ (1 ≤ i ∧ g + i = i) := by omega
      simp only [innerA, h1, ite_false, ite_true]
      exact h.capA_term.symm
    · have h1 : ¬ (1 ≤ τ ∧ g + i = τ) := by omega
      have h2 : g + i ≠ g + τ := by omega
      simp only [innerA, h1, h2, ite_false]
      rw [h.genA _ hx1 hxN (by rw [hmod]; exact hit), hmod]
      congr 1
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · by_cases his : i = σ
    · subst his
      have h1 : g + i ≠ i := by omega
      have h2 : i < wg := hi
      simp only [innerB, h1, h2, true_and, ite_false, ite_true]
      exact (h.capB_term h2).symm
    · have h1 : g + i ≠ σ := by omega
      have h2 : ¬ (σ < wg ∧ g + i = g + σ) := by omega
      simp only [innerB, h1, h2, ite_false]
      rw [h.genB _ hx1 hxN (by rw [hmod]; exact his), hmod]
      congr 1
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]


/-- The heights of the inner agree with those of the parent on the first block. -/
theorem height_first (h : SlotWords A B A0 B0 N g M wg τ σ) {k : ℕ} (hk : k < g) :
    heightWord (innerA A0 g τ) (innerB B0 g wg σ) k = heightWord A B k :=
  heightWord_congr fun x hx1 hx2 => h.first_block hx1 (by omega)

/-- The heights of the inner on the last block are those of the parent on its last `w_g` steps. -/
theorem height_last (h : SlotWords A B A0 B0 N g M wg τ σ) :
    ∀ i, i ≤ wg → heightWord (innerA A0 g τ) (innerB B0 g wg σ) (g - 1 + i) =
      heightWord A B (N - wg - 1 + i) := by
  have hN := h.N_eq
  have hM := h.M_ge
  have hwg := h.wg_lt
  have hMg : g ≤ M * g := Nat.le_mul_of_pos_left g (by omega)
  intro i
  induction i with
  | zero =>
    intro _
    rw [add_zero, add_zero, h.height_first (by omega)]
    have e : N - wg - 1 = N - 1 - wg := by omega
    rw [e, h.pinch_g, h.pinch_Nwg]
  | succ i ih =>
    intro hi
    have e1 : g - 1 + (i + 1) = (g - 1 + i) + 1 := by omega
    have e2 : N - wg - 1 + (i + 1) = (N - wg - 1 + i) + 1 := by omega
    rw [e1, e2, heightWord_succ, heightWord_succ, ih (by omega)]
    have e3 : g - 1 + i + 1 = g + i := by omega
    have e4 : N - wg - 1 + i + 1 = N - wg + i := by omega
    rw [e3, e4]
    obtain ⟨ha, hb⟩ := h.last_block (i := i) (by omega)
    rw [ha, hb]

theorem isBitData_inner (h : SlotWords A B A0 B0 N g M wg τ σ) :
    IsBitData (g + wg) (innerA A0 g τ) (innerB B0 g wg σ) := by
  have hN := h.N_eq
  have hM := h.M_ge
  have hwg := h.wg_lt
  have hwg1 := h.wg_pos
  have hMg : g ≤ M * g := Nat.le_mul_of_pos_left g (by omega)
  have hτ := h.τ_lt
  have hσ := h.σ_le
  have hσ1 := h.σ_pos
  refine ⟨by omega, fun k hk1 hk2 => ?_, fun k hk => ?_, ?_⟩
  · constructor
    · unfold innerA
      split_ifs
      · right; rfl
      · left; rfl
      · exact h.A0_bit _ (Nat.mod_lt _ (by omega))
    · unfold innerB
      split_ifs
      · left; rfl
      · right; rfl
      · exact h.B0_bit _ (Nat.mod_lt _ (by omega))
  · by_cases hkg : k < g
    · rw [h.height_first hkg]
      exact h.words.pos k (by omega)
    · have e : k = g - 1 + (k + 1 - g) := by omega
      rw [e, h.height_last (k + 1 - g) (by omega)]
      exact h.words.pos _ (by omega)
  · have e : g + wg - 1 = g - 1 + wg := by omega
    rw [e, h.height_last wg le_rfl]
    have e2 : N - wg - 1 + wg = N - 1 := by omega
    rw [e2]
    exact h.words.last


end SlotWords

theorem heightWord_add_window (A B : ℕ → ℤ) (n m : ℕ) :
    heightWord A B (n + m) = heightWord A B n + ∑ i ∈ Finset.range m, (A (n + 1 + i) - B (n + 1 +
        i)) := by
  unfold heightWord
  rw [Finset.sum_range_add]
  have : ∑ x ∈ Finset.range m, (A (n + x + 1) - B (n + x + 1)) =
      ∑ i ∈ Finset.range m, (A (n + 1 + i) - B (n + 1 + i)) := by
    apply Finset.sum_congr rfl; intro i _; congr 2 <;> ring
  rw [this]; ring

theorem eq_of_mod_eq_of_close {p q g : ℕ} (h : p % g = q % g) (hpq : p ≤ q) (hlt : q < p + g) :
    p = q := by
  have h1 : (q - p) % g = 0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  have h2 : g ∣ q - p := Nat.dvd_of_mod_eq_zero h1
  have := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
  omega

/-- A window of `g` consecutive steps of the parent words adds up to the exceptional bits at the
slots, as the generic bits cancel (`Δ = 0` and `A⁰_τ = B⁰_σ`): this is the identity that makes the
outer heights the private parent heights. -/
theorem height_window_gen {N g wg τ σ x0 : ℕ} (hg0 : 0 < g) (hwg : wg < g) (hτ : τ ≤ wg)
    (hσ : σ ≤ wg)
    (genA : ∀ x, 1 ≤ x → x < N → x % g ≠ τ → A x = A0 (x % g))
    (genB : ∀ x, 1 ≤ x → x < N → x % g ≠ σ → B x = B0 (x % g))
    (delta : ∑ j ∈ Finset.range g, A0 j = ∑ j ∈ Finset.range g, B0 j) (rho : A0 τ = B0 σ)
    (hx0 : x0 % g = wg) (hlt : x0 + g < N) :
    heightWord A B (x0 + g) = heightWord A B x0 +
      (A (x0 + g - wg + τ) - B (x0 + g - wg + σ)) := by
  have hdecomp : x0 = (x0 / g) * g + wg := by
    have := Nat.div_add_mod x0 g
    rw [hx0] at this
    linarith
  set j := x0 / g with hj
  have hp1 : (x0 + g - wg + τ) % g = τ := by
    have : x0 + g - wg + τ = τ + g * (j + 1) := by rw [hdecomp]; ring_nf; omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hq1 : (x0 + g - wg + σ) % g = σ := by
    have : x0 + g - wg + σ = σ + g * (j + 1) := by rw [hdecomp]; ring_nf; omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [heightWord_add_window A B x0 g, Finset.sum_sub_distrib]
  -- northwest
  have hAwin : ∀ i ∈ Finset.range g, A (x0 + 1 + i) = A0 ((x0 + 1 + i) % g) +
      (if x0 + 1 + i = x0 + g - wg + τ then A (x0 + g - wg + τ) - A0 τ else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hpi : x0 + 1 + i = x0 + g - wg + τ
    · simp only [hpi, hp1, ite_true]; ring
    · simp only [hpi, ite_false, add_zero]
      have : (x0 + 1 + i) % g ≠ τ := by
        intro hmod
        apply hpi
        rcases le_total (x0 + 1 + i) (x0 + g - wg + τ) with hle | hle
        · exact eq_of_mod_eq_of_close (by rw [hmod, hp1]) hle (by omega)
        · exact (eq_of_mod_eq_of_close (by rw [hmod, hp1]) hle (by omega)).symm
      rw [genA _ (by omega) (by omega) this]
  have hBwin : ∀ i ∈ Finset.range g, B (x0 + 1 + i) = B0 ((x0 + 1 + i) % g) +
      (if x0 + 1 + i = x0 + g - wg + σ then B (x0 + g - wg + σ) - B0 σ else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hpi : x0 + 1 + i = x0 + g - wg + σ
    · simp only [hpi, hq1, ite_true]; ring
    · simp only [hpi, ite_false, add_zero]
      have : (x0 + 1 + i) % g ≠ σ := by
        intro hmod
        apply hpi
        rcases le_total (x0 + 1 + i) (x0 + g - wg + σ) with hle | hle
        · exact eq_of_mod_eq_of_close (by rw [hmod, hq1]) hle (by omega)
        · exact (eq_of_mod_eq_of_close (by rw [hmod, hq1]) hle (by omega)).symm
      rw [genB _ (by omega) (by omega) this]
  rw [Finset.sum_congr rfl hAwin, Finset.sum_congr rfl hBwin, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_window_periodic A0 g (x0 + 1), sum_window_periodic B0 g (x0 + 1),
    sum_window_ite (x0 + g - wg + τ) x0 g _, sum_window_ite (x0 + g - wg + σ) x0 g _]
  simp only [show x0 + 1 ≤ x0 + g - wg + τ ∧ x0 + g - wg + τ < x0 + 1 + g by omega,
    show x0 + 1 ≤ x0 + g - wg + σ ∧ x0 + g - wg + σ < x0 + 1 + g by omega, and_self, ite_true]
  have := delta
  have := rho
  linarith


/-- The words of the outer at the slot: `A^D_j = A_{jg+τ}`, `B^D_j = B_{jg+σ}`. -/
def outerWord (A : ℕ → ℤ) (g c j : ℕ) : ℤ := A (j * g + c)

namespace SlotWords

theorem height_window (h : SlotWords A B A0 B0 N g M wg τ σ) {x0 : ℕ}
    (hx0 : x0 % g = wg) (hlt : x0 + g < N) :
    heightWord A B (x0 + g) = heightWord A B x0 +
      (A (x0 + g - wg + τ) - B (x0 + g - wg + σ)) := by
  have hwg := h.wg_lt
  have hτ := h.τ_lt
  have hσ := h.σ_le
  exact height_window_gen (by omega) hwg hτ.le hσ h.genA h.genB h.delta h.rho hx0 hlt

theorem height_outer (h : SlotWords A B A0 B0 N g M wg τ σ) :
    ∀ j, j + 1 ≤ M → heightWord (outerWord A g τ) (outerWord B g σ) j =
      heightWord A B (j * g + wg) := by
  have hN := h.N_eq
  have hM := h.M_ge
  have hwg := h.wg_lt
  have hτ := h.τ_lt
  intro j
  induction j with
  | zero =>
    intro _
    simp only [heightWord, Finset.range_zero, Finset.sum_empty, add_zero, zero_mul, zero_add]
    exact h.pinch_wg.symm.trans (by simp [heightWord]) |>.symm |>.symm
  | succ j ih =>
    intro hj
    rw [heightWord_succ, ih (by omega)]
    have e1 : (j + 1) * g + wg = (j * g + wg) + g := by ring
    have hx0 : (j * g + wg) % g = wg := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hwg]
    have hlt : j * g + wg + g < N := by
      have : (j + 1) * g ≤ (M - 1) * g := Nat.mul_le_mul_right g (by omega)
      have h2 : (M - 1) * g + g = M * g := by
        have : M = (M - 1) + 1 := by omega
        conv_rhs => rw [this]
        ring
      nlinarith
    rw [e1, h.height_window hx0 hlt]
    have e2 : j * g + wg + g - wg + τ = (j + 1) * g + τ := by ring_nf; omega
    have e3 : j * g + wg + g - wg + σ = (j + 1) * g + σ := by ring_nf; omega
    rw [e2, e3]
    rfl


theorem isBitData_outer (h : SlotWords A B A0 B0 N g M wg τ σ) :
    IsBitData M (outerWord A g τ) (outerWord B g σ) := by
  have hN := h.N_eq
  have hM := h.M_ge
  have hwg := h.wg_lt
  have hτ := h.τ_lt
  have hσ := h.σ_le
  have hσ1 := h.σ_pos
  have hlt : ∀ j, j + 1 ≤ M → j * g + wg < N := by
    intro j hj
    have : (j + 1) * g ≤ M * g := Nat.mul_le_mul_right g hj
    nlinarith
  refine ⟨by omega, fun j hj1 hj2 => ?_, fun j hj => ?_, ?_⟩
  · have hjg : g ≤ j * g := Nat.le_mul_of_pos_left g (by omega)
    have := hlt j hj2
    constructor
    · exact (h.words.bits (j * g + τ) (by omega) (by omega)).1
    · exact (h.words.bits (j * g + σ) (by omega) (by omega)).2
  · rw [h.height_outer j (by omega)]
    exact h.words.pos _ (hlt j (by omega))
  · rw [h.height_outer (M - 1) (by omega)]
    have e : (M - 1) * g + wg = N - g := by
      have : M = (M - 1) + 1 := by omega
      rw [hN]
      conv_rhs => rw [this]
      rw [add_mul, one_mul]
      omega
    rw [e]
    exact h.pinch_Ng

end SlotWords


/-- The data of a legal case-(a) mark on the inner, as used to compare words. -/
structure MarkFacts (ω : MarkedInner) (AG BG : ℕ → ℤ) (g wg τ σ : ℕ) : Prop where
  legal : ω.IsLegalNonempty
  case_a : ω.case = .a
  phases : ω.IsPhases σ τ
  period : ω.period = g
  width : ω.widthZ = wg
  minE : minContent ω.E = 0
  lo_eq : ∀ a : ℕ, a < g + wg → ω.lo a = bitsLo AG a
  hi_eq : ∀ a : ℕ, a < g + wg → ω.hi a = bitsLo BG a
  W_lo : ∀ z : ℕ, z < wg → diagLo ω.W (minContent ω.E + z) = ω.lo z
  W_hi : ∀ z : ℕ, z < wg → diagHi ω.W (minContent ω.E + z) = ω.hi z - if σ ≤ z then 1 else 0

theorem SlotWords.wordA_compose (h : SlotWords A B A0 B0 N g M wg τ σ) {ω : MarkedInner}
    {AG BG : ℕ → ℤ} (hAG : AG = innerA A0 g τ) (hm : MarkFacts ω AG BG g wg τ σ)
    {D : Diagram} (hD : IsConnectedSkew D) (hm0 : minContent D = 0)
    (hM : maxContent D = (M : ℤ) - 1)
    (hAD : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ M → bitA D j = A (j * g + τ))
    (hspan : (span (ω.compose D) : ℤ) = N) :
    ∀ k : ℕ, 1 ≤ k → k < N → wordA (ω.compose D) k = A k := by
  have hN := h.N_eq
  have hM2 := h.M_ge
  have hwg := h.wg_lt
  have hτ := h.τ_lt
  have hσ := h.σ_le
  have hσ1 := h.σ_pos
  have hg0 : 0 < g := by omega
  obtain ⟨hl, hca, hph, hq, hw, hminE, hlo, hhi, hWlo, hWhi⟩ := hm
  have hqg : ω.period = (g : ℤ) := hq
  intro k hk1 hkN
  obtain ⟨J, a, hk, hag⟩ : ∃ J a, k = J * g + a ∧ a < g :=
    ⟨k / g, k % g, (Nat.div_add_mod' k g).symm, Nat.mod_lt _ hg0⟩
  subst hk
  have hmod : (J * g + a) % g = a := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hag]
  have hJM : J ≤ M := by
    by_contra hcon
    have : (M + 1) * g ≤ J * g := Nat.mul_le_mul_right g (by omega)
    nlinarith
  have hvalid : ValidClass (minContent D) (maxContent D) ω.widthZ J a := by
    rw [hm0, hM, hw]
    by_cases hJM' : J + 1 ≤ M
    · left
      refine ⟨by omega, by omega⟩
    · right
      have hJe : J = M := by omega
      refine ⟨by rw [hJe]; ring, ?_⟩
      by_contra hcon
      have : M * g + wg ≤ J * g + a := by rw [hJe]; omega
      omega
  have hpos : ((J : ℤ) - minContent D) * ω.period + a = ((J * g + a : ℕ) : ℤ) := by
    rw [hm0, hqg]; push_cast; ring
  have hWloZ : ∀ z : ℤ, 0 ≤ z → z < ω.widthZ → diagLo ω.W (minContent ω.E + z) = ω.lo z := by
    intro z hz0 hz1
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
    exact hWlo n (by omega)
  by_cases hat : a = τ
  · subst hat
    rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
    · -- first block: the cap
      subst hJ0
      have hτ1 : 1 ≤ a := by omega
      have hc := (hl.caps_a hD hca hph).1 (by omega)
      simp only [zero_mul, zero_add] at hc ⊢
      rw [h.capA_init hτ1]
      exact hc
    · by_cases hJM' : J + 1 ≤ M
      · -- interior: the bit of the outer
        have h1 := hl.wordA_slot hD hca hph hWloZ (J := J) (by rw [hm0]; omega)
          (by rw [hM]; omega)
        rw [hm0] at h1
        have h2 := hAD J hJpos hJM'
        rw [h2] at h1
        have e : (((J : ℤ) - 0) * ω.period + a) = ((J * g + a : ℕ) : ℤ) := by
          rw [hqg]; push_cast; ring
        rw [e] at h1
        exact h1
      · -- last block: the cap
        have hJe : J = M := by omega
        have hc := (hl.caps_a hD hca hph).2.2.1
        rw [hspan, hw] at hc
        have e : (N : ℤ) - wg + a = ((J * g + a : ℕ) : ℤ) := by
          rw [hN, hJe]; push_cast; ring
        rw [e] at hc
        rw [hc]
        have := h.capA_term
        have e2 : N - wg + a = J * g + a := by rw [hN, hJe]; omega
        rw [e2] at this
        exact this.symm
  · have hat' : (a : ℤ) ≠ τ := by omega
    have hex := hl.wordA_generic hD hca hph (J := J) (a := a) (by omega) (by omega) hvalid
      (fun h0 => by
        rw [hm0]
        have : a = 0 := by exact_mod_cast h0
        subst this
        rcases Nat.eq_zero_or_pos J with h | h
        · subst h; simp at hk1
        · omega) hat'
    rw [hpos] at hex
    rw [hex]
    by_cases ha0 : a = 0
    · subst ha0
      have hτ1 : 1 ≤ τ := by omega
      simp only [Nat.cast_zero, ite_true]
      have := h.genA (J * g + 0) hk1 hkN (by rw [hmod]; omega)
      rw [this, hmod]
      exact (h.A_zero hτ1).symm
    · have ha1 : 1 ≤ a := by omega
      have e1 : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub ha1]; ring
      simp only [show (a : ℤ) ≠ 0 by omega, ite_false]
      rw [e1, hlo (a - 1) (by omega), hlo a (by omega)]
      have e2 := bitsLo_succ AG (a - 1)
      have e3 : a - 1 + 1 = a := by omega
      rw [e3] at e2
      have e4 : AG a = innerA A0 g τ a := by rw [hAG]
      have e5 : innerA A0 g τ a = A0 (a % g) := by
        have h1 : ¬ (1 ≤ τ ∧ a = τ) := fun hh => hat hh.2
        have h2 : a ≠ g + τ := by omega
        simp only [innerA, h1, h2, ite_false]
      rw [h.genA (J * g + a) hk1 hkN (by rw [hmod]; exact hat), hmod]
      rw [Nat.mod_eq_of_lt hag] at e5
      linarith

theorem SlotWords.wordB_compose (h : SlotWords A B A0 B0 N g M wg τ σ) {ω : MarkedInner}
    {AG BG : ℕ → ℤ} (hBG : BG = innerB B0 g wg σ) (hm : MarkFacts ω AG BG g wg τ σ)
    {D : Diagram} (hD : IsConnectedSkew D) (hm0 : minContent D = 0)
    (hM : maxContent D = (M : ℤ) - 1)
    (hBD : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ M → bitB D j = B (j * g + σ))
    (hspan : (span (ω.compose D) : ℤ) = N) :
    ∀ k : ℕ, 1 ≤ k → k < N → wordB (ω.compose D) k = B k := by
  have hN := h.N_eq
  have hM2 := h.M_ge
  have hwg := h.wg_lt
  have hτ := h.τ_lt
  have hσ := h.σ_le
  have hσ1 := h.σ_pos
  have hg0 : 0 < g := by omega
  obtain ⟨hl, hca, hph, hq, hw, hminE, hlo, hhi, hWlo, hWhi⟩ := hm
  have hqg : ω.period = (g : ℤ) := hq
  intro k hk1 hkN
  obtain ⟨J, a, hk, hag⟩ : ∃ J a, k = J * g + a ∧ a < g :=
    ⟨k / g, k % g, (Nat.div_add_mod' k g).symm, Nat.mod_lt _ hg0⟩
  subst hk
  have hmod : (J * g + a) % g = a := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hag]
  have hJM : J ≤ M := by
    by_contra hcon
    have : (M + 1) * g ≤ J * g := Nat.mul_le_mul_right g (by omega)
    nlinarith
  have hvalid : ValidClass (minContent D) (maxContent D) ω.widthZ J a := by
    rw [hm0, hM, hw]
    by_cases hJM' : J + 1 ≤ M
    · left
      refine ⟨by omega, by omega⟩
    · right
      have hJe : J = M := by omega
      refine ⟨by rw [hJe]; ring, ?_⟩
      by_contra hcon
      have : M * g + wg ≤ J * g + a := by rw [hJe]; omega
      omega
  have hpos : ((J : ℤ) - minContent D) * ω.period + a = ((J * g + a : ℕ) : ℤ) := by
    rw [hm0, hqg]; push_cast; ring
  have hWhiZ : ∀ z : ℤ, 0 ≤ z → z < ω.widthZ →
      diagHi ω.W (minContent ω.E + z) = ω.hi z - if (σ : ℤ) ≤ z then 1 else 0 := by
    intro z hz0 hz1
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
    have := hWhi n (by omega)
    simpa using this
  by_cases hat : a = σ
  · subst hat
    rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
    · subst hJ0
      have hc := (hl.caps_a hD hca hph).2.1
      simp only [zero_mul, zero_add] at hc ⊢
      rw [h.capB_init]
      exact hc
    · by_cases hJM' : J + 1 ≤ M
      · have h1 := hl.wordB_slot hD hca hph hWhiZ (J := J) (by rw [hm0]; omega)
          (by rw [hM]; omega)
        rw [hm0] at h1
        have h2 := hBD J hJpos hJM'
        rw [h2] at h1
        have e : (((J : ℤ) - 0) * ω.period + a) = ((J * g + a : ℕ) : ℤ) := by
          rw [hqg]; push_cast; ring
        rw [e] at h1
        exact h1
      · have hJe : J = M := by omega
        have hσw : a < wg := by
          by_contra hcon
          have : M * g + wg ≤ J * g + a := by rw [hJe]; omega
          omega
        have hc := (hl.caps_a hD hca hph).2.2.2 (by omega)
        rw [hspan, hw] at hc
        have e : (N : ℤ) - wg + a = ((J * g + a : ℕ) : ℤ) := by
          rw [hN, hJe]; push_cast; ring
        rw [e] at hc
        rw [hc]
        have := h.capB_term hσw
        have e2 : N - wg + a = J * g + a := by rw [hN, hJe]; omega
        rw [e2] at this
        exact this.symm
  · have hat' : (a : ℤ) ≠ σ := by omega
    have hex := hl.wordB_generic hD hca hph (J := J) (a := a) (by omega) (by omega) hvalid
      (fun h0 => by
        rw [hm0]
        have : a = 0 := by exact_mod_cast h0
        subst this
        rcases Nat.eq_zero_or_pos J with h | h
        · subst h; simp at hk1
        · omega) hat'
    rw [hpos] at hex
    rw [hex]
    by_cases ha0 : a = 0
    · subst ha0
      simp only [Nat.cast_zero, ite_true]
      have := h.genB (J * g + 0) hk1 hkN (by rw [hmod]; omega)
      rw [this, hmod]
      exact h.B_zero.symm
    · have ha1 : 1 ≤ a := by omega
      have e1 : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub ha1]; ring
      simp only [show (a : ℤ) ≠ 0 by omega, ite_false]
      rw [e1, hhi (a - 1) (by omega), hhi a (by omega)]
      have e2 := bitsLo_succ BG (a - 1)
      have e3 : a - 1 + 1 = a := by omega
      rw [e3] at e2
      have e5 : BG a = B0 (a % g) := by
        have h2 : ¬ (σ < wg ∧ a = g + σ) := by omega
        simp only [hBG, innerB, hat, h2, ite_false]
      rw [h.genB (J * g + a) hk1 hkN (by rw [hmod]; exact hat), hmod]
      rw [Nat.mod_eq_of_lt hag] at e5
      linarith

/-- **The root of the slot form** (`prop:gluing-ordinary-fold`, `w_g ≥ 1`).  A diagram `F` whose
boundary words are in the slot form `SlotWords` has a proper legal period-`g` root: the inner `G`
with
its legal case-(a) mark and the outer read from the slots. -/
theorem SlotWords.exists_root (h : SlotWords A B A0 B0 N g M wg τ σ) {F : Diagram}
    (hF : IsConnectedSkew F) (hspF : span F = N)
    (hFA : ∀ k : ℕ, 1 ≤ k → k < N → wordA F k = A k)
    (hFB : ∀ k : ℕ, 1 ≤ k → k < N → wordB F k = B k) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period = g ∧ χ.ω.case = .a ∧
      χ.ω.W.Nonempty ∧ χ.ω.width = wg := by
  have hN := h.N_eq
  have hM2 := h.M_ge
  have hwg := h.wg_lt
  have hwg1 := h.wg_pos
  have hτ := h.τ_lt
  have hσ := h.σ_le
  have hσ1 := h.σ_pos
  have hg2 : 2 ≤ g := by omega
  set AG := innerA A0 g τ with hAG
  set BG := innerB B0 g wg σ with hBG
  have hbd := h.isBitData_inner
  have hsw : heightWord AG BG wg = 1 := by
    rw [h.height_first hwg]; exact h.pinch_wg
  have hsq : heightWord AG BG (g - 1) = 1 := by
    rw [h.height_first (by omega)]; exact h.pinch_g
  have hpos : ∀ r, r < wg → 1 + (if σ ≤ r then 1 else 0) ≤ heightWord AG BG r := by
    intro r hr
    rw [h.height_first (by omega)]
    exact h.pos r hr
  have sg := slotGeom_of_generic hwg1 hwg hτ hσ1 hσ h.delta h.rho hbd hsw hsq hpos h.A_wg h.B_zero
  set v₁ := A0 τ - ∑ j ∈ Finset.range g, A0 j with hv₁
  set Gd := fromBits (g + wg) AG BG with hGd
  have hG : DiagSet Gd 0 ((g : ℤ) + wg - 1) (loZ AG) (loZ BG) := by
    have := diagSet_fromBits hbd
    have e1 : ((g + wg : ℕ) : ℤ) - 1 = (g : ℤ) + wg - 1 := by push_cast; ring
    rw [e1] at this
    exact this
  set ω := SlotGeom.mark Gd (g : ℤ) (wg : ℤ) (σ : ℤ) v₁ (loZ BG) with hω
  have hleg : ω.IsLegal := SlotGeom.mark_isLegal hG sg
  have hnon : ω.W.Nonempty := SlotGeom.mark_nonempty hG sg
  have hmf : MarkFacts ω AG BG g wg τ σ := by
    refine ⟨⟨hleg, hnon⟩, rfl, SlotGeom.mark_phases hG sg, SlotGeom.mark_period, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · exact SlotGeom.mark_width hG sg
    · exact hG.minContent_eq sg.shape
    · intro a ha
      have := SlotGeom.mark_lo hG sg (a := (a : ℤ)) (by omega) (by omega)
      rw [this, loZ_natCast]
    · intro a ha
      have := SlotGeom.mark_hi hG sg (a := (a : ℤ)) (by omega) (by omega)
      rw [this, loZ_natCast]
    · intro z hz
      have hW := SlotGeom.diagSet_lowerCopy hG sg.w_pos sg.w_lt (σ := (σ : ℤ))
        (hi := loZ BG)
      have hmin : minContent ω.E = 0 := hG.minContent_eq sg.shape
      rw [hmin, zero_add]
      change diagLo (SlotGeom.lowerCopy Gd (wg : ℤ) (σ : ℤ) (loZ BG)) (z : ℤ) = ω.lo z
      rw [hW.diagLo_eq (SlotGeom.shape_lowerCopy sg) (by omega) (by omega)]
      rw [SlotGeom.mark_lo hG sg (by omega) (by omega)]
    · intro z hz
      have hW := SlotGeom.diagSet_lowerCopy hG sg.w_pos sg.w_lt (σ := (σ : ℤ))
        (hi := loZ BG)
      have hmin : minContent ω.E = 0 := hG.minContent_eq sg.shape
      rw [hmin, zero_add]
      change diagHi (SlotGeom.lowerCopy Gd (wg : ℤ) (σ : ℤ) (loZ BG)) (z : ℤ) = ω.hi z -
        if σ ≤ z then 1 else 0
      rw [hW.diagHi_eq (SlotGeom.shape_lowerCopy sg) (by omega) (by omega)]
      rw [SlotGeom.mark_hi hG sg (by omega) (by omega)]
      unfold SlotGeom.hiW
      simp only [Nat.cast_le]
  -- the outer
  have hDbd := h.isBitData_outer
  set Dd := fromBits M (outerWord A g τ) (outerWord B g σ) with hDd
  have hDcs : IsConnectedSkew Dd := isConnectedSkew_fromBits hDbd
  have hm0 : minContent Dd = 0 := minContent_fromBits hDbd
  have hM : maxContent Dd = (M : ℤ) - 1 := maxContent_fromBits hDbd
  have hspD : span Dd = M := span_fromBits hDbd
  have hAD : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ M → bitA Dd j = A (j * g + τ) := by
    intro j hj1 hj2
    have := bitA_fromBits hDbd hj1 (by omega)
    rw [hm0, zero_add] at this
    exact this
  have hBD : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ M → bitB Dd j = B (j * g + σ) := by
    intro j hj1 hj2
    have := bitB_fromBits hDbd hj1 (by omega)
    rw [hm0, zero_add] at this
    exact this
  have hspan : (span (ω.compose Dd) : ℤ) = N := by
    rw [MarkedInner.span_compose hDcs hleg, hspD, SlotGeom.mark_period (G := Gd) (q := (g : ℤ))
      (w := (wg : ℤ)) (σ := (σ : ℤ)) (v₁ := v₁) (hi := loZ BG)]
    have := SlotGeom.mark_width hG sg
    rw [hN]
    push_cast
    have e : ((ω.width : ℕ) : ℤ) = wg := this
    rw [e]
  have hcsF' : IsConnectedSkew (ω.compose Dd) := hleg.isConnectedSkew_compose hDcs
  have hwA := h.wordA_compose hAG hmf hDcs hm0 hM hAD hspan
  have hwB := h.wordB_compose hBG hmf hDcs hm0 hM hBD hspan
  have hspN : span (ω.compose Dd) = N := by exact_mod_cast hspan
  obtain ⟨t, ht⟩ := eq_translate_of_bits hcsF' hF (by rw [hspN, hspF])
    (fun k hk1 hk2 => by
      have e1 := hwA k hk1 (by omega)
      have e2 := hFA k hk1 (by omega)
      unfold wordA at e1 e2
      rw [e1, e2])
    (fun k hk1 hk2 => by
      have e1 := hwB k hk1 (by omega)
      have e2 := hFB k hk1 (by omega)
      unfold wordB at e1 e2
      rw [e1, e2])
  refine ⟨⟨Dd, ω⟩, ⟨hDcs, ?_, ?_, hleg⟩, ⟨t, ht⟩, ?_, ?_, ?_, ?_⟩
  · change 2 ≤ Dd.card
    have h1 : span Dd ≤ Dd.card := Finset.card_image_le
    omega
  · change 2 ≤ Gd.card
    have h1 : span Gd ≤ Gd.card := Finset.card_image_le
    have h2 : span Gd = g + wg := span_fromBits hbd
    omega
  · exact SlotGeom.mark_period
  · rfl
  · exact hnon
  · have := SlotGeom.mark_width hG sg
    exact_mod_cast this

end OrdinaryFold
end GluingCore
