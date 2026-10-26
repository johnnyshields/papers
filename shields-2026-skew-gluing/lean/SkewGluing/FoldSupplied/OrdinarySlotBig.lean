import SkewGluing.FoldSupplied.OrdinaryFacts

/-!
# The slot form of the words of an ordinary inner at width at least `g`

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`, `v ≥ g`, `a = v mod g > 0`): when the projected contact of the row
class is not below the projected contact of the column class, the boundary words of the inner are in
the slot form `SlotWords` of the fold with slots `τ = t mod g`, `σ = s mod g`.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open OrdinaryDrift OrdinaryFold

variable {A B : ℕ → ℤ} {r v s t g : ℕ}

namespace OrdCtx

/-- The exceptional contacts lie in the first block at width at least `g`, and `s ≥ g`. -/
theorem big_aux (c : OrdCtx A B r v s t g) (ha : 0 < v % g) (hvg : g ≤ v) :
    g ≤ s ∧ t ≤ (v / g - 1) * g + t % g := by
  have hg := c.g_pos
  obtain ⟨Y0, X0, Yd, Xd, -⟩ := c.big_facts ha hvg
  have hs1 := c.h.s_pos
  have ht := c.h.t_lt
  refine ⟨?_, ?_⟩
  · by_contra hcon
    have hmod : s % g = s := Nat.mod_eq_of_lt (by omega)
    unfold xx at X0
    rw [hmod] at X0
    simp only [zero_mul, zero_add] at X0
    unfold natB at X0
    have : s ≠ 0 := by omega
    simp [this] at X0
  · have hkt : yy A g (t % g) (t / g) = 1 := by
      unfold yy
      rw [Nat.div_add_mod' t g]
      unfold natC
      by_cases ht0 : t = 0
      · simp [ht0]
      · simp only [ht0, if_false]; exact c.h.capA (by omega)
    have hle : t / g ≤ v / g := Nat.div_le_div_right (by omega)
    have hne : t / g ≠ v / g := fun hh => by rw [hh] at hkt; omega
    have hlt : t / g < v / g := by omega
    have : t = t / g * g + t % g := (Nat.div_add_mod' t g).symm
    have h2 : t / g ≤ v / g - 1 := by omega
    have h3 : t / g * g ≤ (v / g - 1) * g := Nat.mul_le_mul_right g h2
    omega


/-- **The slot form, type (a), width at least `g`.** -/
theorem slotWords_a_big (c : OrdCtx A B r v s t g) (ha : 0 < v % g) (hvg : g ≤ v)
    (hts : t % g ≤ s % g) :
    SlotWords A B (fun ρ => if ρ = t % g then 0 else natC A ρ)
      (fun ρ => if ρ = s % g then 0 else natB B s ρ) (r + v) g (r / g + v / g) (v % g)
      (t % g) (s % g) := by
  have hg := c.g_pos
  have hvr := c.h.v_lt
  have hglt := c.glt
  have hs1 := c.h.s_pos
  have hs2 := c.h.s_le
  have ht := c.h.t_lt
  obtain ⟨Y0, X0, Yd, Xd, Ed1, Pa, hta, hsa, psi_lb, phi_lb⟩ := c.big_facts ha hvg
  obtain ⟨hsg, htle⟩ := c.big_aux ha hvg
  have hag := Nat.mod_lt v hg
  have hv : v = v / g * g + v % g := (Nat.div_add_mod' v g).symm
  have hP := c.h.phi_constraints
  obtain ⟨-, Pge1, Pv0, Pge0, Pr, Pv1⟩ := hP
  obtain ⟨R, hR⟩ := c.gr
  have hRr : r / g = R := by rw [hR]; exact Nat.mul_div_cancel_left R hg
  have hR2 : 2 ≤ R := by
    by_contra hcon
    have : g * R ≤ g * 1 := Nat.mul_le_mul_left g (by omega)
    omega
  have hmulle : ∀ k, k ≤ R → k * g ≤ r := by
    intro k hk
    have := Nat.mul_le_mul_right g hk
    rw [hR]; linarith [Nat.mul_comm g R]
  set d := v / g with hd
  set a := v % g with ha_def
  have hd1 : 1 ≤ d := (Nat.le_div_iff_mul_le hg).mpr (by omega)
  have hdR : d < R := by
    by_contra hcon
    have h1 := Nat.mul_le_mul_right g (show R ≤ d by omega)
    have h2 : r ≤ d * g := by rw [hR]; linarith [Nat.mul_comm g R]
    omega
  obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hdd : (d' + 1) * g = d' * g + g := by ring
  have hdg1 : (d + 1) * g ≤ r := hmulle (d + 1) (by omega)
  have hdg2 : (d + 1) * g = d * g + g := by ring
  have hd'1 : (d' + 1) * g ≤ r := hmulle (d' + 1) (by omega)
  have hτ := c.tau_lt
  have hσ := c.sigma_lt
  have hpos : ∀ z, z < v → 1 ≤ Phi A B s z := Pge1
  -- block formulas at the first and last blocks
  have B0f : ∀ z, z < g → Phi A B s z = Psi A B s (t % g) (s % g) z + (if t % g ≤ z then 1 else 0) := by
    intro z hz
    have e := c.Phi_blockE (k := 0) (z := z) (by simp; omega) hz
    simp only [zero_mul, zero_add] at e
    rw [e, Echarge_zero, Y0, X0]
    simp
  have Bdf : ∀ z, z < g → Phi A B s (d * g + z) = 1 + Psi A B s (t % g) (s % g) z -
      (if s % g ≤ z then 1 else 0) := by
    intro z hz
    have e := c.Phi_blockE (k := d) (z := z) (by omega) hz
    rw [e, Ed1, Yd, Xd]
    simp
  have Pa1 : ∀ z, z + 1 = a → Psi A B s (t % g) (s % g) a =
      Psi A B s (t % g) (s % g) z + gam A B s (t % g) (s % g) a := by
    intro z hz; rw [← hz]; exact Psi_succ _ _ _ _ _ _
  -- G1: the contacts
  have hσ1 : 1 ≤ s % g := by
    by_contra hcon
    have hs0 : s % g = 0 := by omega
    have ht0 : t % g = 0 := by omega
    have e := Bdf 0 hg
    have p := hpos (d * g + 0) (by omega)
    rw [e] at p
    have : Psi A B s (t % g) (s % g) 0 = 0 := by
      simp [Psi, gam, hs0, ht0]
    rw [this] at p
    simp [hs0] at p
  have hτa : t % g < a := by
    by_contra hcon
    have hta' : t % g = a := by omega
    have hsa' : s % g = a := by omega
    obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have h1 := Pa1 a' ha'.symm
    have h2 : gam A B s (t % g) (s % g) a = 0 := by
      simp [gam, hta', hsa']
    have h3 := phi_lb a' (by omega)
    have h4 : ¬ t % g ≤ a' := by omega
    simp only [h4, if_false] at h3
    omega
  have hr_eq : r = R * g := by rw [hR]; ring
  have hbit := c.h.words.bits
  have hdg : g ≤ d * g := Nat.le_mul_of_pos_left g (by omega)
  -- the position facts at the last block
  have hAb : ∀ b, b = d * g + t % g → natC A b = 0 := by
    intro b hb; have : yy A g (t % g) d = natC A b := by unfold yy; rw [hb]
    omega
  have hBb : ∀ b, b = d * g + s % g → natB B s b = 1 := by
    intro b hb; have : xx B s g (s % g) d = natB B s b := by unfold xx; rw [hb]
    omega
  have hmod_gen : ∀ x, x % g ≠ t % g → 1 ≤ x → x < r + v → A x = natC A (x % g) :=
    fun x hne hx1 hxN => c.generic_A hx1 hxN hne
  have hHnat : ∀ m, m < r → heightWord A B m = Phi A B s m + (if s ≤ m then 1 else 0) :=
    fun m hm => c.h.height_native hm
  have hH2 : ∀ z, z < v → heightWord A B (r + z) = 1 + Phi A B s z - (if t ≤ z then 1 else 0) :=
    fun z hz => c.h.height_second hz
  have hN : r + v = (r / g + v / g) * g + v % g := by
    rw [hRr]
    have e3 : (R + d) * g = R * g + d * g := by ring
    rw [e3]; omega
  refine ⟨hN, by omega, ha, hag, hτa, hσ1, hsa, c.h.words, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases h1 : j = t % g
    · simp [h1]
    · simp only [h1, if_false]
      exact c.natC_bit (by omega)
  · intro j hj
    by_cases h1 : j = s % g
    · simp [h1]
    · simp only [h1, if_false]
      exact c.natB_bit (by omega)
  · have h := c.charge_zero
    unfold Psi at h
    rw [show g - 1 + 1 = g by omega] at h
    simp only [gam] at h
    rw [Finset.sum_sub_distrib] at h
    linarith
  · simp
  · intro x hx1 hxN hne
    simp only [hne, if_false]
    exact c.generic_A hx1 hxN hne
  · intro x hx1 hxN hne
    simp only [hne, if_false]
    exact c.generic_B hx1 hxN hne
  · intro h1
    have e := c.h.A_native (i := t % g) h1
    have : yy A g (t % g) 0 = natC A (t % g) := by unfold yy; simp
    omega
  · have e := c.h.B_native (i := s % g) hσ1
    have : xx B s g (s % g) 0 = natB B s (s % g) := by unfold xx; simp
    have b := (hbit (s % g) hσ1 (by omega)).2
    split_ifs at e <;> omega
  · have hb1 : d * g + t % g + 1 ≤ v := by omega
    have c1 := c.h.copyA (d * g + t % g) (by omega) (by omega)
    have e : r + v - a + t % g = r + (d * g + t % g) := by omega
    rw [e]
    have b := (hbit (r + (d * g + t % g)) (by omega) (by omega)).1
    have e1 := c.h.A_native (i := d * g + t % g) (by omega)
    have e2 := hAb (d * g + t % g) rfl
    split_ifs at c1 <;> omega
  · intro hs'
    have c1 := c.h.copyB (d * g + s % g) (by omega) (by omega)
    have e : r + v - a + s % g = r + (d * g + s % g) := by omega
    rw [e]
    have e1 := c.h.B_native (i := d * g + s % g) (by omega)
    have e2 := hBb (d * g + s % g) rfl
    omega
  · -- pinch_wg
    rw [hHnat a (by omega), B0f a hag, Pa]
    have : ¬ s ≤ a := by omega
    simp [this]
    omega
  · -- pinch_g
    rw [hHnat (g - 1) (by omega), B0f (g - 1) (by omega), c.charge_zero]
    have : ¬ s ≤ g - 1 := by omega
    have h2 : t % g ≤ g - 1 := by omega
    simp [this, h2]
  · -- pinch_Ng
    have e : r + v - g = r + (d' * g + a) := by rw [hd'] at hv; omega
    rw [e, hH2 _ (by rw [hd'] at hv; omega)]
    have e1 := c.Phi_blockE (k := d') (z := a) (by omega) hag
    rw [e1, Pa] at *
    have Ed' : Echarge A B s g (t % g) (s % g) d = Echarge A B s g (t % g) (s % g) d' +
        yy A g (t % g) d' - xx B s g (s % g) d' := by
      rw [hd']; exact Echarge_succ _ _ _ _ _ _ _
    have h2 : t ≤ d' * g + a := by
      have : (d - 1) = d' := by omega
      rw [this] at htle
      omega
    simp only [hta, hsa, if_true, h2]
    omega
  · -- pinch_Nwg
    have e : r + v - 1 - a = r + (d' * g + (g - 1)) := by rw [hd'] at hv; omega
    rw [e, hH2 _ (by rw [hd'] at hv; omega)]
    have e1 := c.Phi_blockE (k := d') (z := g - 1) (by omega) (by omega)
    have Ed' : Echarge A B s g (t % g) (s % g) d = Echarge A B s g (t % g) (s % g) d' +
        yy A g (t % g) d' - xx B s g (s % g) d' := by
      rw [hd']; exact Echarge_succ _ _ _ _ _ _ _
    have h2 : t ≤ d' * g + (g - 1) := by
      have : (d - 1) = d' := by omega
      rw [this] at htle
      omega
    have t1 : t % g ≤ g - 1 := by omega
    have t2 : s % g ≤ g - 1 := by omega
    rw [e1, c.charge_zero] at *
    simp only [t1, t2, h2, if_true]
    omega
  · intro z hz
    rw [hHnat z (by omega), B0f z (by omega)]
    have h1 := psi_lb z hz
    have h2 := phi_lb z (by omega)
    have h3 : ¬ s ≤ z := by omega
    simp only [h3, if_false]
    split_ifs at h1 h2 ⊢ <;> omega
  · show (if a = t % g then 0 else natC A a) = 0
    have hne : a ≠ t % g := by omega
    simp only [hne, if_false]
    obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have h1 := Pa1 a' ha'.symm
    have h2 := psi_lb a' (by omega)
    have b1 := c.natC_bit (i := a) (by omega)
    have b2 := c.natB_bit (i := a) (by omega)
    unfold gam at h1
    simp only [hne, if_false] at h1
    split_ifs at h1 h2 <;> omega
  · simp [natB]
  · intro h1
    have hne : (0 : ℕ) ≠ t % g := by omega
    simp [hne, natC]

end OrdCtx

end FoldSupplied
end SkewGluing
