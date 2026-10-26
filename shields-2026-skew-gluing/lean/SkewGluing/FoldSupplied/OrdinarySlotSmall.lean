import SkewGluing.FoldSupplied.OrdinarySlotBig

/-!
# The slot form of the words of an ordinary inner at width below `g`

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`, `v < g`): the contacts are already confined (`τ = t`, `σ = s`), the
original gauge is kept, and the words are in the slot form `SlotWords` whatever the order of the
two contacts.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open OrdinaryDrift OrdinaryFold

variable {A B : ℕ → ℤ} {r v s t g : ℕ}

namespace OrdCtx

/-- The charge of all `r / g` blocks vanishes. -/
theorem echarge_end (c : OrdCtx A B r v s t g) {R : ℕ} (hR : r = g * R) :
    Echarge A B s g (t % g) (s % g) R = 0 := by
  have hg := c.g_pos
  have hv1 := c.h.v_pos
  have hvr := c.h.v_lt
  have hR1 : 1 ≤ R := by
    by_contra hcon
    have : R = 0 := by omega
    subst this; omega
  have hQ := c.Qs_formula hR R le_rfl
  rw [c.charge_zero] at hQ
  have hr1 : (r - 1) + 1 = R * g := by rw [hR]; ring_nf; omega
  have hPhi : Phi A B s (r - 1) = ∑ i ∈ Finset.range (R * g), fN A B s i := by
    unfold Phi; rw [hr1]
  have h0 := c.h.phi_constraints
  have hPhi0 : Phi A B s (r - 1) = 0 := h0.2.2.2.2.1
  rw [hPhi0] at hPhi
  rw [← hPhi] at hQ
  simpa using hQ.symm

/-- **The slot form, `v < g`.** -/
theorem slotWords_small (c : OrdCtx A B r v s t g) (hvg : v < g) :
    SlotWords A B (fun ρ => if ρ = t % g then 0 else natC A ρ)
      (fun ρ => if ρ = s % g then 0 else natB B s ρ) (r + v) g (r / g + v / g) (v % g)
      (t % g) (s % g) := by
  have hg := c.g_pos
  have hvr := c.h.v_lt
  have hglt := c.glt
  have hv1 := c.h.v_pos
  have hs1 := c.h.s_pos
  have hs2 := c.h.s_le
  have ht := c.h.t_lt
  have hP := c.h.phi_constraints
  obtain ⟨-, Pge1, Pv0, Pge0, Pr, Pv1⟩ := hP
  obtain ⟨R, hR⟩ := c.gr
  have hRr : r / g = R := by rw [hR]; exact Nat.mul_div_cancel_left R hg
  have hR2 : 2 ≤ R := by
    by_contra hcon
    have : g * R ≤ g * 1 := Nat.mul_le_mul_left g (by omega)
    omega
  have hvmod : v % g = v := Nat.mod_eq_of_lt hvg
  have hvdiv : v / g = 0 := Nat.div_eq_of_lt hvg
  have htmod : t % g = t := Nat.mod_eq_of_lt (by omega)
  have hsmod : s % g = s := Nat.mod_eq_of_lt (by omega)
  have hbit := c.h.words.bits
  have hr_eq : r = R * g := by rw [hR]; ring
  have hmulle : ∀ k, k ≤ R → k * g ≤ r := by
    intro k hk
    have := Nat.mul_le_mul_right g hk
    rw [hR]; linarith [Nat.mul_comm g R]
  have hHnat : ∀ m, m < r → heightWord A B m = Phi A B s m + (if s ≤ m then 1 else 0) :=
    fun m hm => c.h.height_native hm
  have Y0 : yy A g (t % g) 0 = 1 := by
    unfold yy; simp only [zero_mul, zero_add, htmod]
    unfold natC
    by_cases ht0 : t = 0
    · simp [ht0]
    · simp only [ht0, if_false]; exact c.h.capA (by omega)
  have X0 : xx B s g (s % g) 0 = 1 := by
    unfold xx; simp only [zero_mul, zero_add, hsmod]
    unfold natB
    have : s ≠ 0 := by omega
    simp [this]
  have B0f : ∀ z, z < g → Phi A B s z = Psi A B s (t % g) (s % g) z +
      (if t % g ≤ z then 1 else 0) - (if s % g ≤ z then 1 else 0) := by
    intro z hz
    have e := c.Phi_blockE (k := 0) (z := z) (by simp; omega) hz
    simp only [zero_mul, zero_add] at e
    rw [e, Echarge_zero, Y0, X0]
    simp
  have Pa : Psi A B s (t % g) (s % g) v = 0 := by
    have e := B0f v hvg
    rw [Pv0] at e
    have t1 : t % g ≤ v := by omega
    have t2 : s % g ≤ v := by omega
    simp only [t1, t2, if_true] at e
    omega
  have hN : r + v = (r / g + v / g) * g + v % g := by
    rw [hRr, hvdiv, hvmod, hr_eq]; ring
  have hsr : v < r := hvr
  refine ⟨hN, by omega, by omega, by omega, by omega, by omega, by omega, c.h.words, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rw [htmod]; exact c.h.capA (by omega)
  · rw [hsmod]; exact c.h.capB
  · -- capA_term
    have e : r + v - v % g + t % g = r + t := by rw [hvmod, htmod]; omega
    rw [e]
    by_cases ht0 : t = 0
    · subst ht0; simpa using c.h.A_r
    · have c1 := c.h.copyA t (by omega) ht
      simp only [if_true] at c1
      have b := (hbit (r + t) (by omega) (by omega)).1
      have := c.h.capA (by omega)
      omega
  · intro hs'
    have e : r + v - v % g + s % g = r + s := by rw [hvmod, hsmod]; omega
    rw [e]
    have hsv : s < v := by rw [hsmod, hvmod] at hs'; exact hs'
    have c1 := c.h.copyB s (by omega) hsv
    simp only [if_true] at c1
    rw [c1, c.h.capB]; norm_num
  · rw [hvmod]; exact c.h.sing_v
  · rw [hHnat (g - 1) (by omega), B0f (g - 1) (by omega), c.charge_zero]
    have t1 : t % g ≤ g - 1 := by omega
    have t2 : s % g ≤ g - 1 := by omega
    have t3 : s ≤ g - 1 := by omega
    simp [t1, t2, t3]
  · -- pinch_Ng
    have hm : r + v - g = (R - 1) * g + v % g := by
      obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
      have : r = R' * g + g := by rw [hR]; ring
      simp only [Nat.add_sub_cancel]
      omega
    have hmr : (R - 1) * g + v % g < r := by
      have := hmulle R le_rfl
      have h2 : R * g = (R - 1) * g + g := by
        obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring
      omega
    rw [hm, hHnat _ hmr]
    have e1 := c.Phi_blockE (k := R - 1) (z := v % g) hmr (by omega)
    have hER := c.echarge_end hR
    have hE : Echarge A B s g (t % g) (s % g) R = Echarge A B s g (t % g) (s % g) (R - 1) +
        yy A g (t % g) (R - 1) - xx B s g (s % g) (R - 1) := by
      obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      exact Echarge_succ _ _ _ _ _ _ _
    have t1 : t % g ≤ v % g := by omega
    have t2 : s % g ≤ v % g := by omega
    have t3 : s ≤ (R - 1) * g + v % g := by
      have : g ≤ (R - 1) * g := by
        obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        exact Nat.le_mul_of_pos_left g (by omega)
      omega
    have Pa' : Psi A B s (t % g) (s % g) (v % g) = 0 := by rw [hvmod]; exact Pa
    rw [e1, Pa']
    simp only [t1, t2, t3, if_true]
    omega
  · have e : r + v - 1 - v % g = r - 1 := by rw [hvmod]; omega
    rw [e]; exact c.h.sing_r
  · intro z hz
    rw [hvmod] at hz
    have := c.h.mpos z hz
    rw [hsmod]; exact this
  · show (if v % g = t % g then 0 else natC A (v % g)) = 0
    have hne : v % g ≠ t % g := by omega
    simp only [hne, if_false]
    rw [hvmod]
    have := c.h.A_native (i := v) (by omega)
    have := c.h.A_v
    omega
  · simp [natB]
  · intro h1
    have hne : (0 : ℕ) ≠ t % g := by omega
    simp [hne, natC]

end OrdCtx

end FoldSupplied
end SkewGluing
