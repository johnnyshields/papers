import SkewGluing.FoldSupplied.OrdinarySlotSmall

/-!
# The slot form of the words of an ordinary inner, type (b)

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`, `v ≥ g`, `a = v mod g > 0`): when the projected contact of the row
class is below that of the column class, the antitransposed words `(1 - B, 1 - A)` are in the slot
form `SlotWords` with slots `σ = s mod g` and `τ = t mod g`; the construction then runs on the
antitranspose, and the resulting mark has type (b).

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open OrdinaryDrift OrdinaryFold

variable {A B : ℕ → ℤ} {r v s t g : ℕ}

namespace OrdCtx

/-- **The slot form, type (b), width at least `g`**, for the antitransposed words. -/
theorem slotWords_b_big (c : OrdCtx A B r v s t g) (ha : 0 < v % g) (hvg : g ≤ v)
    (hst : s % g < t % g) :
    SlotWords (fun k => 1 - B k) (fun k => 1 - A k)
      (fun ρ => if ρ = s % g then 0 else 1 - natB B s ρ)
      (fun ρ => if ρ = t % g then 0 else 1 - natC A ρ) (r + v) g (r / g + v / g) (v % g)
      (s % g) (t % g) := by
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
  have B0f : ∀ z, z < g → Phi A B s z = Psi A B s (t % g) (s % g) z + (if t % g ≤ z then 1 else 0) := by
    intro z hz
    have e := c.Phi_blockE (k := 0) (z := z) (by simp; omega) hz
    simp only [zero_mul, zero_add] at e
    rw [e, Echarge_zero, Y0, X0]
    simp
  have Pa1 : ∀ z, z + 1 = a → Psi A B s (t % g) (s % g) a =
      Psi A B s (t % g) (s % g) z + gam A B s (t % g) (s % g) a := by
    intro z hz; rw [← hz]; exact Psi_succ _ _ _ _ _ _
  have hσa : s % g < a := by omega
  have hσ1' : 1 ≤ t % g := by omega
  have hr_eq : r = R * g := by rw [hR]; ring
  have hbit := c.h.words.bits
  have hdg : g ≤ d * g := Nat.le_mul_of_pos_left g (by omega)
  have hAb : ∀ b, b = d * g + t % g → natC A b = 0 := by
    intro b hb; have : yy A g (t % g) d = natC A b := by unfold yy; rw [hb]
    omega
  have hBb : ∀ b, b = d * g + s % g → natB B s b = 1 := by
    intro b hb; have : xx B s g (s % g) d = natB B s b := by unfold xx; rw [hb]
    omega
  have hHnat : ∀ m, m < r → heightWord A B m = Phi A B s m + (if s ≤ m then 1 else 0) :=
    fun m hm => c.h.height_native hm
  have hH2 : ∀ z, z < v → heightWord A B (r + z) = 1 + Phi A B s z - (if t ≤ z then 1 else 0) :=
    fun z hz => c.h.height_second hz
  have hN : r + v = (r / g + v / g) * g + v % g := by
    rw [hRr]
    have e3 : (R + d) * g = R * g + d * g := by ring
    rw [e3]; omega
  have hdual := heightWord_dual A B
  have hbits' := c.h.words
  have hwd : WordData (fun k => 1 - B k) (fun k => 1 - A k) (r + v) := by
    refine ⟨fun k hk1 hk2 => ?_, fun k hk => ?_, ?_⟩
    · have := hbits'.bits k hk1 hk2; omega
    · rw [hdual]; exact hbits'.pos k hk
    · rw [hdual]; exact hbits'.last
  refine ⟨hN, by omega, ha, hag, hσa, hσ1', hta, hwd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases h1 : j = s % g
    · simp [h1]
    · simp only [h1, if_false]
      have := c.natB_bit (i := j) (by omega); omega
  · intro j hj
    by_cases h1 : j = t % g
    · simp [h1]
    · simp only [h1, if_false]
      have := c.natC_bit (i := j) (by omega); omega
  · -- delta
    have h := c.charge_zero
    unfold Psi at h
    rw [show g - 1 + 1 = g by omega] at h
    have e1 : ∑ ρ ∈ Finset.range g, ((if ρ = s % g then (0 : ℤ) else 1 - natB B s ρ) -
        (if ρ = t % g then 0 else 1 - natC A ρ)) =
        ∑ ρ ∈ Finset.range g, gam A B s (t % g) (s % g) ρ +
          (∑ ρ ∈ Finset.range g, (if ρ = s % g then (0 : ℤ) else 1) -
            ∑ ρ ∈ Finset.range g, (if ρ = t % g then (0 : ℤ) else 1)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ρ _
      unfold gam
      split_ifs <;> ring
    have e2 : ∑ ρ ∈ Finset.range g, (if ρ = s % g then (0 : ℤ) else 1) =
        ∑ ρ ∈ Finset.range g, (if ρ = t % g then (0 : ℤ) else 1) := by
      have hs' : s % g < g := hσ
      have ht' : t % g < g := hτ
      simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
        mul_one]
      have f1 : (Finset.filter (fun ρ => ¬ρ = s % g) (Finset.range g)).card = g - 1 := by
        have : Finset.filter (fun ρ => ¬ρ = s % g) (Finset.range g) =
            (Finset.range g).erase (s % g) := by
          ext x; simp [Finset.mem_erase, and_comm]
        rw [this, Finset.card_erase_of_mem (Finset.mem_range.mpr hs')]; simp
      have f2 : (Finset.filter (fun ρ => ¬ρ = t % g) (Finset.range g)).card = g - 1 := by
        have : Finset.filter (fun ρ => ¬ρ = t % g) (Finset.range g) =
            (Finset.range g).erase (t % g) := by
          ext x; simp [Finset.mem_erase, and_comm]
        rw [this, Finset.card_erase_of_mem (Finset.mem_range.mpr ht')]; simp
      rw [f1, f2]
    have hdel : ∑ ρ ∈ Finset.range g, ((if ρ = s % g then (0 : ℤ) else 1 - natB B s ρ) -
        (if ρ = t % g then 0 else 1 - natC A ρ)) = 0 := by
      rw [e1, e2, sub_self, add_zero]; exact h
    rw [Finset.sum_sub_distrib] at hdel
    linarith
  · simp
  · intro x hx1 hxN hne
    have := c.generic_B hx1 hxN hne
    simp only [hne, if_false]
    rw [this]
  · intro x hx1 hxN hne
    have := c.generic_A hx1 hxN hne
    simp only [hne, if_false]
    rw [this]
  · intro h1
    have e := c.h.B_native (i := s % g) h1
    have : xx B s g (s % g) 0 = natB B s (s % g) := by unfold xx; simp
    have b := (hbit (s % g) h1 (by omega)).2
    split_ifs at e <;> omega
  · have e := c.h.A_native (i := t % g) hσ1'
    have : yy A g (t % g) 0 = natC A (t % g) := by unfold yy; simp
    omega
  · -- capA_term: the dual of capB_term
    have c1 := c.h.copyB (d * g + s % g) (by omega) (by omega)
    have e : r + v - a + s % g = r + (d * g + s % g) := by omega
    change 1 - B (r + v - a + s % g) = 0
    rw [e]
    have e1 := c.h.B_native (i := d * g + s % g) (by omega)
    have e2 := hBb (d * g + s % g) rfl
    omega
  · intro h1
    have c1 := c.h.copyA (d * g + t % g) (by omega) (by omega)
    have e : r + v - a + t % g = r + (d * g + t % g) := by omega
    change 1 - A (r + v - a + t % g) = 1
    rw [e]
    have b := (hbit (r + (d * g + t % g)) (by omega) (by omega)).1
    have e1 := c.h.A_native (i := d * g + t % g) (by omega)
    have e2 := hAb (d * g + t % g) rfl
    split_ifs at c1 <;> omega
  · -- pinch_wg
    change heightWord (fun k => 1 - B k) (fun k => 1 - A k) a = 1
    rw [hdual, hHnat a (by omega), B0f a hag, Pa]
    have : ¬ s ≤ a := by omega
    simp [this]
    omega
  · show heightWord (fun k => 1 - B k) (fun k => 1 - A k) (g - 1) = 1
    rw [hdual, hHnat (g - 1) (by omega), B0f (g - 1) (by omega), c.charge_zero]
    have : ¬ s ≤ g - 1 := by omega
    have h2 : t % g ≤ g - 1 := by omega
    simp [this, h2]
  · show heightWord (fun k => 1 - B k) (fun k => 1 - A k) (r + v - g) = 1
    rw [hdual]
    have e : r + v - g = r + (d' * g + a) := by rw [hd'] at hv; omega
    rw [e, hH2 _ (by rw [hd'] at hv; omega)]
    have e1 := c.Phi_blockE (k := d') (z := a) (by omega) hag
    have Ed' : Echarge A B s g (t % g) (s % g) d = Echarge A B s g (t % g) (s % g) d' +
        yy A g (t % g) d' - xx B s g (s % g) d' := by
      rw [hd']; exact Echarge_succ _ _ _ _ _ _ _
    have h2 : t ≤ d' * g + a := by
      have : (d - 1) = d' := by omega
      rw [this] at htle
      omega
    rw [e1, Pa]
    simp only [hta, hsa, if_true, h2]
    omega
  · show heightWord (fun k => 1 - B k) (fun k => 1 - A k) (r + v - 1 - a) = 1
    rw [hdual]
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
    rw [e1, c.charge_zero]
    simp only [t1, t2, h2, if_true]
    omega
  · intro z hz
    change 1 + (if t % g ≤ z then 1 else 0) ≤ heightWord (fun k => 1 - B k) (fun k => 1 - A k) z
    rw [hdual, hHnat z (by omega), B0f z (by omega)]
    have h1 := psi_lb z hz
    have h2 := phi_lb z (by omega)
    have h3 : ¬ s ≤ z := by omega
    simp only [h3, if_false]
    split_ifs at h1 h2 ⊢ <;> omega
  · show (if a = s % g then 0 else 1 - natB B s a) = 0
    have hne : a ≠ s % g := by omega
    simp only [hne, if_false]
    obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have h1 := Pa1 a' ha'.symm
    have h2 := psi_lb a' (by omega)
    have b1 := c.natC_bit (i := a) (by omega)
    have b2 := c.natB_bit (i := a) (by omega)
    unfold gam at h1
    simp only [hne, if_false] at h1
    split_ifs at h1 h2 <;> omega
  · have hne : (0 : ℕ) ≠ t % g := by omega
    simp [hne, natC]
  · intro h1
    have hne : (0 : ℕ) ≠ s % g := by omega
    simp [hne, natB]

end OrdCtx

end FoldSupplied
end SkewGluing
