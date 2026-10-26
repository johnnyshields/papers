/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/OrdinaryFold/Fold.lean`. -/
import GluingCore.OrdinaryFold.Params
import GluingCore.OrdinaryFold.Scalar
import GluingCore.OrdinaryDrift
import GluingCore.OrdinaryFold.Empty

/-!
# The slot form of the words of two ordinary roots

Formalizes `shields-2026-skew-factor-gluing.tex`, «Two ordinary roots» (`prop:gluing-ordinary-fold`,
`eq:gluing-ordinary-slot`).

From the setting `GcdPair` of two ordinary roots of nondividing periods whose first root has case
(a), a nonempty mark and a lower copy of positive heights (`GcdPair.slotWords_a`,
`GcdPair.slotWords_b`), the boundary words of the parent are in the slot form `SlotWords` of
`GluingCore.OrdinaryFold.Realize`, for the slots `τ`, `σ` the residues modulo `g` of the
exceptional phases of the first root: either for the words themselves (the folded mark has case
(a)) or for their antitransposed words (the folded mark has case (b)).  At remainder zero the words
are in the form `EmptyWords` (`GcdPair.emptyWords`).

Sorry-free.
-/

namespace GluingCore
namespace OrdinaryDrift

open OrdinaryFold

variable {A B A0 B0 : ℕ → ℤ} {N g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ}

theorem mod_of_between {x g bg : ℕ} (_hg : 0 < g) (hbg : g ∣ bg) (h1 : bg ≤ x) (h2 : x < bg + g) :
    x % g = x - bg := by
  obtain ⟨k, rfl⟩ := hbg
  have : x = (x - g * k) + g * k := by omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The residue of the first exceptional phase modulo `g`: either the phase itself, or its excess
over `b g`. -/
theorem GcdPair.tau_struct (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hha : ha₁ < b * g + wg) :
    (ha₁ < g ∧ ha₁ % g = ha₁) ∨
      (g ≤ ha₁ ∧ ha₁ % g = ha₁ - b * g ∧ b * g ≤ ha₁ ∧ ha₁ < b * g + g) := by
  obtain ⟨G1, G2, -, -⟩ := h.cap_facts
  have hg := h.g_pos
  have hwg := h.wg_lt
  by_cases h1 : ha₁ < g
  · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
  · right
    have h2 : ¬ (ha₁ + wg < b * g + wg) := by
      intro hlt
      have := G1 (by omega) (by omega)
      have := G2 (by omega) hlt
      omega
    have h3 : b * g ≤ ha₁ := by omega
    exact ⟨by omega, mod_of_between hg (Dvd.intro_left b rfl) h3 (by omega), h3, by omega⟩

theorem GcdPair.sigma_struct (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hhb : hb₁ ≤ b * g + wg) :
    (hb₁ < g ∧ hb₁ % g = hb₁) ∨
      (g ≤ hb₁ ∧ hb₁ % g = hb₁ - b * g ∧ b * g ≤ hb₁ ∧ hb₁ < b * g + g) := by
  obtain ⟨-, -, G3, G4⟩ := h.cap_facts
  have hg := h.g_pos
  have hwg := h.wg_lt
  by_cases h1 : hb₁ < g
  · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
  · right
    have h2 : b * g ≤ hb₁ := by
      by_contra hcon
      have := G3 (by omega) (by omega)
      have := G4 (by omega) (by omega)
      omega
    exact ⟨by omega, mod_of_between hg (Dvd.intro_left b rfl) h2 (by omega), h2, by omega⟩


theorem GcdPair.genA_first (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) {x : ℕ}
    (hx1 : 1 ≤ x) (hxN : x < N) (hne : x % (a * g) ≠ ha₁) : A x = A0 (x % g) :=
  h.genA x hx1 hxN fun hh => hne hh.1

theorem GcdPair.genB_first (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) {x : ℕ}
    (hx1 : 1 ≤ x) (hxN : x < N) (hne : x % (a * g) ≠ hb₁) : B x = B0 (x % g) :=
  h.genB x hx1 hxN fun hh => hne hh.1

/-- The position `N - w_g + r`, `r < g`, is `≡ b g + r` modulo `p = a g`, and `≡ r` modulo `g`. -/
theorem GcdPair.terminal_pos (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) {r : ℕ}
    (hr : r < wg) : (N - wg + r) % (a * g) = b * g + r ∧ (N - wg + r) % g = r := by
  obtain ⟨k, -, hk⟩ := h.root₁.rep
  have hwq := h.root₁.hwq
  have hwg := h.wg_lt
  have hk' : N = (a * g) * k + (b * g + wg) := by rw [hk]; ring
  have e : N - wg + r = (b * g + r) + (a * g) * k := by omega
  constructor
  · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · have e2 : N - wg + r = r + g * (b + a * k) := by
      have : g * (b + a * k) = b * g + (a * g) * k := by ring
      omega
    rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem GcdPair.capA_init_tau (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hha : ha₁ < b * g + wg) (h1 : 1 ≤ ha₁ % g) : A (ha₁ % g) = 1 := by
  obtain ⟨G1, -, -, -⟩ := h.cap_facts
  have hg := h.g_pos
  have hwg := h.wg_lt
  have hN2 := h.root₁.two_q_le
  have hag : g ≤ a * g := Nat.le_mul_of_pos_left g (by have := h.a_ge; omega)
  rcases h.tau_struct hha with ⟨h2, h3⟩ | ⟨h2, h3, h4, h5⟩
  · rw [h3]
    exact h.root₁.capA_init (by omega)
  · have hbg : g ≤ b * g := by
      have : 1 ≤ b := by
        by_contra hb0
        have : b = 0 := by omega
        subst this; omega
      exact Nat.le_mul_of_pos_left g this
    have hlt : ha₁ % g < g := Nat.mod_lt _ hg
    have e1 := h.genA_first (x := ha₁ % g) h1 (by omega) (by
      rw [Nat.mod_eq_of_lt (by omega)]; omega)
    rw [e1, Nat.mod_eq_of_lt hlt]
    exact G1 (by omega) (by omega)

theorem GcdPair.capB_init_sigma (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hhb : hb₁ ≤ b * g + wg) (h1 : 1 ≤ hb₁ % g) : B (hb₁ % g) = 0 := by
  obtain ⟨-, -, G3, -⟩ := h.cap_facts
  have hg := h.g_pos
  have hwg := h.wg_lt
  have hN2 := h.root₁.two_q_le
  have hag : g ≤ a * g := Nat.le_mul_of_pos_left g (by have := h.a_ge; omega)
  rcases h.sigma_struct hhb with ⟨h2, h3⟩ | ⟨h2, h3, h4, h5⟩
  · rw [h3]
    exact h.root₁.capB_init (by omega)
  · have hlt : hb₁ % g < g := Nat.mod_lt _ hg
    have e1 := h.genB_first (x := hb₁ % g) h1 (by omega) (by
      rw [Nat.mod_eq_of_lt (by omega)]; omega)
    rw [e1, Nat.mod_eq_of_lt hlt]
    exact G3 (by omega) (by omega)

theorem GcdPair.capA_term_tau (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hha : ha₁ < b * g + wg) (h1 : ha₁ % g < wg) : A (N - wg + ha₁ % g) = 0 := by
  obtain ⟨-, G2, -, -⟩ := h.cap_facts
  have hg := h.g_pos
  have hwg := h.wg_lt
  have hN2 := h.root₁.two_q_le
  have hag : g ≤ a * g := Nat.le_mul_of_pos_left g (by have := h.a_ge; omega)
  have hwq := h.root₁.hwq
  rcases h.tau_struct hha with ⟨h2, h3⟩ | ⟨h2, h3, h4, h5⟩
  · rw [h3] at h1 ⊢
    by_cases hb0 : b = 0
    · subst hb0
      have := h.root₁.capA_term hha
      simpa using this
    · have hbg : g ≤ b * g := Nat.le_mul_of_pos_left g (by omega)
      obtain ⟨m1, m2⟩ := h.terminal_pos h1
      have hne : (N - wg + ha₁) % (a * g) ≠ ha₁ := by rw [m1]; omega
      rw [h.genA_first (by omega) (by omega) hne, m2]
      have := G2 hha (by omega)
      rwa [h3] at this
  · have e : N - (b * g + wg) + ha₁ = N - wg + ha₁ % g := by rw [h3]; omega
    have := h.root₁.capA_term hha
    rwa [e] at this

theorem GcdPair.capB_term_sigma (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hhb : hb₁ ≤ b * g + wg) (h1 : hb₁ % g < wg) : B (N - wg + hb₁ % g) = 1 := by
  obtain ⟨-, -, -, G4⟩ := h.cap_facts
  have hg := h.g_pos
  have hwg := h.wg_lt
  have hN2 := h.root₁.two_q_le
  have hag : g ≤ a * g := Nat.le_mul_of_pos_left g (by have := h.a_ge; omega)
  have hwq := h.root₁.hwq
  rcases h.sigma_struct hhb with ⟨h2, h3⟩ | ⟨h2, h3, h4, h5⟩
  · rw [h3] at h1 ⊢
    by_cases hb0 : b = 0
    · subst hb0
      have := h.root₁.capB_term (by omega)
      simpa using this
    · have hbg : g ≤ b * g := Nat.le_mul_of_pos_left g (by omega)
      obtain ⟨m1, m2⟩ := h.terminal_pos h1
      have hne : (N - wg + hb₁) % (a * g) ≠ hb₁ := by rw [m1]; omega
      rw [h.genB_first (by omega) (by omega) hne, m2]
      have := G4 (by omega) (by omega)
      rwa [h3] at this
  · have e : N - (b * g + wg) + hb₁ = N - wg + hb₁ % g := by rw [h3]; omega
    have := h.root₁.capB_term (by omega)
    rwa [e] at this


theorem genSum_incr_zero (A0 B0 : ℕ → ℤ) (g : ℕ) : genSum (incr A0 B0 g) 0 = 0 := by
  simp [genSum]

theorem genSum_incr_succ (A0 B0 : ℕ → ℤ) (g n : ℕ) :
    genSum (incr A0 B0 g) (n + 1) = genSum (incr A0 B0 g) n + (A0 ((n + 1) % g) - B0 ((n + 1) % g))
        := by
  simp only [genSum, Finset.sum_range_succ, incr]

/-- Shifting by a multiple of `g` does not change the generic partial sums. -/
theorem genSum_shift (A0 B0 : ℕ → ℤ) {g : ℕ} (hΔ : genSum (incr A0 B0 g) g = 0)
    (m r : ℕ) : genSum (incr A0 B0 g) (m * g + r) = genSum (incr A0 B0 g) r := by
  rw [genSum_mul_add (incr_periodic A0 B0), hΔ]; ring

theorem heightWord_dual (A B : ℕ → ℤ) (k : ℕ) :
    heightWord (fun j => 1 - B j) (fun j => 1 - A j) k = heightWord A B k := by
  unfold heightWord
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring


/-- The scalar data of the first root at the slots `τ = ha₁ mod g`, `σ = hb₁ mod g`. -/
structure SlotScalars (A B A0 B0 : ℕ → ℤ) (N g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ)
    (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) : Prop where
  tau_le : ha₁ % g ≤ wg
  sigma_le : hb₁ % g ≤ wg
  rho : A0 (ha₁ % g) = B0 (hb₁ % g)

theorem GcdPair.slotScalars (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hha : ha₁ < b * g + wg) (hhb1 : 1 ≤ hb₁) :
    SlotScalars A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂ h := by
  obtain ⟨d1, d2, d3, d4, -, -, -, -, -, -⟩ := h.drift_full
  obtain ⟨G1, G2, G3, G4⟩ := h.cap_facts
  have hg := h.g_pos
  have hwg := h.wg_lt
  have hhb := h.root₁.hb_le
  have hbg : b * g = 0 ∨ g ≤ b * g := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · left; simp [h0]
    · right; exact Nat.le_mul_of_pos_left g h0
  have hτs := h.tau_struct hha
  have hσs := h.sigma_struct hhb
  have hlt : ∀ x, x % g < g := fun x => Nat.mod_lt _ hg
  have E1 := h.budget_initial
  simp only [hhb1, ite_true] at E1
  have E2 := h.budget_terminal
  simp only [hha, ite_true] at E2
  have hbit := h.A0_bit
  have hbit' := h.B0_bit
  have hτr : ha₁ % g ≤ wg := scalar_range_a g wg (b * g) ha₁ (ha₁ % g) (A0 (ha₁ % g)) hwg hbg hha
    hτs G1 (fun hh => G2 hha hh)
  have hσr : hb₁ % g ≤ wg := scalar_range_b g wg (b * g) hb₁ (hb₁ % g) (B0 (hb₁ % g)) hwg hbg hhb
    hσs (G3 hhb1) G4
  refine ⟨hτr, hσr, ?_⟩
  have b1 := hbit (ha₁ % g) (hlt _)
  have b2 := hbit' (hb₁ % g) (hlt _)
  have b3 := hbit 0 hg
  have b4 := hbit' 0 hg
  have b5 := hbit wg hwg
  have b6 := hbit' wg hwg
  refine scalar_rho wg (b * g) ha₁ hb₁ (ha₁ % g) (hb₁ % g) _ _ _ _ _ _
    ⟨b1, b2, b3, b4, b5, b6⟩ (fun h0 => by rw [h0]) (fun h0 => by rw [h0]) d2 d4 E1 E2 hhb
    (fun h0 => by rw [h0]; simp) ?_
  intro hbe
  rcases hσs with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · have : b * g = 0 := by omega
    omega
  · omega


theorem GcdPair.M_ge (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) : 2 ≤ N / g := by
  have hg := h.g_pos
  have hN2 := h.root₁.two_q_le
  have ha2 := h.a_ge
  rw [Nat.le_div_iff_mul_le hg]
  nlinarith

theorem GcdPair.N_eq (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) :
    N = (N / g) * g + wg := by
  have := Nat.div_add_mod N g
  rw [h.N_mod] at this
  linarith

theorem GcdPair.delta (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) :
    ∑ j ∈ Finset.range g, A0 j = ∑ j ∈ Finset.range g, B0 j := by
  obtain ⟨d1, -⟩ := h.drift_full
  have := ordFold_genSum_incr_period A0 B0 (g := g)
  rw [d1, Finset.sum_sub_distrib] at this
  linarith


/-- **The slot form, case (a).**  Two ordinary roots whose first root has case (a) (an upper
exceptional phase `ha₁ < w`, a lower `hb₁ ≥ 1`) and a lower copy of positive heights
(`hMpos`: the heights of the first band read `1 + [z ≥ hb₁]` at least) have parent words in the
slot form `SlotWords`, for the slots `τ = ha₁ mod g`, `σ = hb₁ mod g`, provided the folded mark has
case (a) (`hnew`). -/
theorem GcdPair.slotWords_a (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hwg1 : 1 ≤ wg) (hha : ha₁ < b * g + wg) (hhb1 : 1 ≤ hb₁)
    (hMpos : ∀ z, z < b * g + wg → 1 + (if hb₁ ≤ z then 1 else 0) ≤ heightWord A B z)
    (hnew : A0 (ha₁ % g) = 1 ∨ ha₁ % g < hb₁ % g) :
    SlotWords A B A0 B0 N g (N / g) wg (ha₁ % g) (hb₁ % g) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h.drift_full
  obtain ⟨G1, G2, G3, G4⟩ := h.cap_facts
  have sc := h.slotScalars hha hhb1
  have hg := h.g_pos
  have hwg := h.wg_lt
  have hhb := h.root₁.hb_le
  have hbg : b * g = 0 ∨ g ≤ b * g := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · left; simp [h0]
    · right; exact Nat.le_mul_of_pos_left g h0
  have hτs := h.tau_struct hha
  have hσs := h.sigma_struct hhb
  have hlt : ∀ x, x % g < g := fun x => Nat.mod_lt _ hg
  have E1 := h.budget_initial
  simp only [hhb1, ite_true] at E1
  have E2 := h.budget_terminal
  simp only [hha, ite_true] at E2
  have b1 := h.A0_bit (ha₁ % g) (hlt _)
  have b2 := h.B0_bit (hb₁ % g) (hlt _)
  have b3 := h.A0_bit 0 hg
  have b4 := h.B0_bit 0 hg
  have b5 := h.A0_bit wg hwg
  have b6 := h.B0_bit wg hwg
  have sa := scalar_a g wg (b * g) ha₁ hb₁ (ha₁ % g) (hb₁ % g) (A0 (ha₁ % g)) (B0 (hb₁ % g))
    (A0 0) (B0 0) (A0 wg) (B0 wg) hwg hha hhb1 hhb hτs hσs ⟨b1, b2, b3, b4, b5, b6⟩
    (fun h0 => by rw [h0]) (fun h0 => by rw [h0]) (fun h0 => by rw [h0]) (fun h0 => by rw [h0])
    E1 E2 sc.tau_le sc.sigma_le sc.rho hnew
  obtain ⟨sa1, sa2, sa3, sa4, sa5⟩ := sa
  have hdivA : ∀ x, x % (a * g) % g = x % g := fun x => Nat.mod_mod_of_dvd x (Dvd.intro_left a rfl)
  have hN2 := h.root₁.two_q_le
  have hwq := h.root₁.hwq
  have hag : g ≤ a * g := Nat.le_mul_of_pos_left g (by have := h.a_ge; omega)
  refine ⟨h.N_eq, h.M_ge, hwg1, hwg, sa1, sa2, sc.sigma_le, h.words, h.A0_bit, h.B0_bit,
    h.delta, sc.rho, ?_, ?_, fun h1 => h.capA_init_tau hha h1,
    h.capB_init_sigma hhb sa2, h.capA_term_tau hha sa1,
    fun h1 => h.capB_term_sigma hhb h1, d7, d8, d9, d10, ?_, sa3, sa4, sa5⟩
  · intro x hx1 hxN hne
    apply h.genA x hx1 hxN
    rintro ⟨h1, -⟩
    apply hne
    rw [← hdivA x, h1]
  · intro x hx1 hxN hne
    apply h.genB x hx1 hxN
    rintro ⟨h1, -⟩
    apply hne
    rw [← hdivA x, h1]
  · intro r hr
    have hr1 := h.height₁ (k := r) (by omega) (by omega)
    have hr2 := h.height₁ (k := b * g + r) (by omega) (by omega)
    rw [genSum_shift A0 B0 d1] at hr2
    simp only [hhb1, ite_true] at hr1 hr2
    have hp1 := h.words.pos r (by omega)
    have hm1 := hMpos r (by omega)
    have hm2 := hMpos (b * g + r) (by omega)
    rw [hr1] at hp1 hm1
    rw [hr2] at hm2
    have := scalar_pos_a g wg (b * g) ha₁ hb₁ (ha₁ % g) (hb₁ % g) r (A0 (ha₁ % g))
      (B0 (hb₁ % g)) (A0 0) (B0 0) (A0 wg) (B0 wg) (genSum (incr A0 B0 g) r) hwg hbg hha hhb1
      hhb hτs hσs ⟨b1, b2⟩ G1 (G3 hhb1) sc.rho hnew hr (by omega) hm1 hm2
    rw [hr1]
    exact this


theorem sum_dual (A0 : ℕ → ℤ) (g : ℕ) :
    ∑ j ∈ Finset.range g, (1 - A0 j) = g - ∑ j ∈ Finset.range g, A0 j := by
  simp [Finset.sum_sub_distrib]

/-- **The slot form for the antitransposed words**, the folded mark having case (b).  With the
hypotheses of `GcdPair.slotWords_a`, but the folded mark not of case (a) (`hnew` fails), the
antitransposed words `(1 - B, 1 - A)` are in the slot form for the slots `(σ, τ)`. -/
theorem GcdPair.slotWords_b (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hwg1 : 1 ≤ wg) (hha : ha₁ < b * g + wg) (hhb1 : 1 ≤ hb₁)
    (hMpos : ∀ z, z < b * g + wg → 1 + (if hb₁ ≤ z then 1 else 0) ≤ heightWord A B z)
    (hnew : ¬ (A0 (ha₁ % g) = 1 ∨ ha₁ % g < hb₁ % g)) :
    SlotWords (fun k => 1 - B k) (fun k => 1 - A k) (fun j => 1 - B0 j) (fun j => 1 - A0 j)
      N g (N / g) wg (hb₁ % g) (ha₁ % g) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h.drift_full
  obtain ⟨G1, G2, G3, G4⟩ := h.cap_facts
  have sc := h.slotScalars hha hhb1
  have hg := h.g_pos
  have hwg := h.wg_lt
  have hhb := h.root₁.hb_le
  have hbg : b * g = 0 ∨ g ≤ b * g := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · left; simp [h0]
    · right; exact Nat.le_mul_of_pos_left g h0
  have hτs := h.tau_struct hha
  have hσs := h.sigma_struct hhb
  have hlt : ∀ x, x % g < g := fun x => Nat.mod_lt _ hg
  have E1 := h.budget_initial
  simp only [hhb1, ite_true] at E1
  have E2 := h.budget_terminal
  simp only [hha, ite_true] at E2
  have b1 := h.A0_bit (ha₁ % g) (hlt _)
  have b2 := h.B0_bit (hb₁ % g) (hlt _)
  have b3 := h.A0_bit 0 hg
  have b4 := h.B0_bit 0 hg
  have b5 := h.A0_bit wg hwg
  have b6 := h.B0_bit wg hwg
  have hN2 := h.root₁.two_q_le
  have hwq := h.root₁.hwq
  have hag : g ≤ a * g := Nat.le_mul_of_pos_left g (by have := h.a_ge; omega)
  have hdivA : ∀ x, x % (a * g) % g = x % g := fun x => Nat.mod_mod_of_dvd x (Dvd.intro_left a rfl)
  -- the instances of the heights
  have hMbg : 1 + (if hb₁ ≤ b * g then 1 else 0) ≤ 1 +
      (if ha₁ ≤ b * g then (if 1 ≤ ha₁ then 1 - A0 (ha₁ % g) else 0) else 0) +
      (if hb₁ ≤ b * g then B0 (hb₁ % g) else 0) := by
    have hk := h.height₁ (k := b * g) (by omega) (by omega)
    have := genSum_shift A0 B0 d1 b 0
    rw [Nat.add_zero] at this
    rw [this, genSum_incr_zero] at hk
    simp only [hhb1, ite_true] at hk
    have hm := hMpos (b * g) (by omega)
    rw [hk] at hm
    omega
  have hPw1 : 1 ≤ 1 + (-(A0 0 - B0 0) - (A0 wg - B0 wg)) +
      (if ha₁ ≤ wg - 1 then (if 1 ≤ ha₁ then 1 - A0 (ha₁ % g) else 0) else 0) +
      (if hb₁ ≤ wg - 1 then B0 (hb₁ % g) else 0) := by
    have hk := h.height₁ (k := wg - 1) (by omega) (by omega)
    simp only [hhb1, ite_true] at hk
    have hs := genSum_incr_succ A0 B0 g (wg - 1)
    have e : wg - 1 + 1 = wg := by omega
    rw [e, Nat.mod_eq_of_lt hwg, d3] at hs
    have hp := h.words.pos (wg - 1) (by omega)
    rw [hk] at hp
    omega
  have hnew' : ¬ (A0 (ha₁ % g) = 1 ∨ ha₁ % g < hb₁ % g) := hnew
  have sb1 := scalar_b1 g wg (b * g) ha₁ hb₁ (ha₁ % g) (hb₁ % g) (A0 (ha₁ % g)) (B0 (hb₁ % g))
    (A0 0) (B0 0) hwg1 hhb1 hτs hσs ⟨b1, b2⟩ (fun h0 => by rw [h0]) (fun h0 => by rw [h0]) E1
    sc.rho hnew' hMbg
  have sb2 := scalar_b2 g wg (b * g) ha₁ hb₁ (ha₁ % g) (hb₁ % g) (A0 (ha₁ % g)) (B0 (hb₁ % g))
    (A0 0) (B0 0) (A0 wg) (B0 wg) hwg1 hwg hha hhb1 hhb hτs hσs ⟨b1, b2, b3, b4, b5, b6⟩
    (fun h0 => by rw [h0]) (fun h0 => by rw [h0]) E1 E2 sc.rho hnew' sc.tau_le sc.sigma_le hPw1
  obtain ⟨sb3, sb4, sb5⟩ := scalar_b345 g wg (b * g) ha₁ hb₁ (ha₁ % g) (hb₁ % g)
    (A0 (ha₁ % g)) (B0 (hb₁ % g)) (A0 0) (B0 0) (A0 wg) (B0 wg) hha hhb1 hhb hτs hσs
    ⟨b1, b2, b3, b4, b5, b6⟩ (fun h0 => by rw [h0]) E1 E2 sc.rho hnew' sb1 sb2
  have hbits := h.words.bits
  refine ⟨h.N_eq, h.M_ge, hwg1, hwg, by omega, sb1, sc.tau_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun k hk1 hk2 => ?_, fun k hk => ?_, ?_⟩
    · have := hbits k hk1 hk2
      constructor <;> omega
    · rw [heightWord_dual]; exact h.words.pos k hk
    · rw [heightWord_dual]; exact h.words.last
  · intro j hj
    have := h.B0_bit j hj
    omega
  · intro j hj
    have := h.A0_bit j hj
    omega
  · simp only [sum_dual]
    have := h.delta
    linarith
  · have := sc.rho
    omega
  · intro x hx1 hxN hne
    have : B x = B0 (x % g) := by
      apply h.genB x hx1 hxN
      rintro ⟨h1, -⟩
      apply hne
      rw [← hdivA x, h1]
    omega
  · intro x hx1 hxN hne
    have : A x = A0 (x % g) := by
      apply h.genA x hx1 hxN
      rintro ⟨h1, -⟩
      apply hne
      rw [← hdivA x, h1]
    omega
  · intro h1
    have := h.capB_init_sigma hhb h1
    simp only [this]; norm_num
  · have := h.capA_init_tau hha sb1
    simp only [this]; norm_num
  · have := h.capB_term_sigma hhb (by omega)
    simp only [this]; norm_num
  · intro h1
    have := h.capA_term_tau hha h1
    simp only [this]; norm_num
  · rw [heightWord_dual]; exact d7
  · rw [heightWord_dual]; exact d8
  · rw [heightWord_dual]; exact d9
  · rw [heightWord_dual]; exact d10
  · intro r hr
    have hr1 := h.height₁ (k := r) (by omega) (by omega)
    have hr2 := h.height₁ (k := b * g + r) (by omega) (by omega)
    rw [genSum_shift A0 B0 d1] at hr2
    simp only [hhb1, ite_true] at hr1 hr2
    have hp1 := h.words.pos r (by omega)
    have hm1 := hMpos r (by omega)
    have hm2 := hMpos (b * g + r) (by omega)
    rw [hr1] at hp1 hm1
    rw [hr2] at hm2
    have := scalar_pos_b g wg (b * g) ha₁ hb₁ (ha₁ % g) (hb₁ % g) r (A0 (ha₁ % g))
      (B0 (hb₁ % g)) (genSum (incr A0 B0 g) r) hwg hbg hha hhb1 hhb hτs hσs ⟨b1, b2⟩ G1
      (G3 hhb1) sc.rho hnew' sb1 hr (by omega) hm1 hm2
    rw [heightWord_dual, hr1]
    exact this
  · omega
  · omega
  · intro h1
    have := sb5 h1
    omega


/-- **The form of the words at remainder zero.**  Two ordinary roots (the first of case (a)) with
`w_g = 0` and `g ≥ 2` have boundary words in the form `EmptyWords`. -/
theorem GcdPair.emptyWords (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hwg0 : wg = 0) (hg2 : 2 ≤ g) (hha : ha₁ < b * g + wg) (hhb1 : 1 ≤ hb₁) :
    EmptyWords A B A0 B0 N g (N / g) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h.drift_full
  have sc := h.slotScalars hha hhb1
  have hg := h.g_pos
  have hτ0 : ha₁ % g = 0 := by have := sc.tau_le; omega
  have hσ0 : hb₁ % g = 0 := by have := sc.sigma_le; omega
  have hdivA : ∀ x, x % (a * g) % g = x % g := fun x => Nat.mod_mod_of_dvd x (Dvd.intro_left a rfl)
  refine ⟨?_, h.M_ge, hg2, h.words, ?_, ?_, h.delta, ?_, d8, d9⟩
  · have := h.N_eq
    rw [hwg0] at this
    simpa using this
  · intro x hx1 hxN hne
    apply h.genA x hx1 hxN
    rintro ⟨h1, -⟩
    apply hne
    rw [← hdivA x, h1, hτ0]
  · intro x hx1 hxN hne
    apply h.genB x hx1 hxN
    rintro ⟨h1, -⟩
    apply hne
    rw [← hdivA x, h1, hσ0]
  · have := sc.rho
    rw [hτ0, hσ0] at this
    exact this

end OrdinaryDrift
end GluingCore
