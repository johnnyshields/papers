import SkewGluing.FoldSupplied.OrdinaryPhi

/-!
# The block form of the native heights

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`), equation `ge:eq:ordinary-block`.

With the residue classes of the native words constant off the classes `τ = t mod g` and
`σ = s mod g`, the native height at the position `k g + z` is
`Φ(k g + z) = E k + Ψ z + [τ ≤ z] y_k - [σ ≤ z] x_k` (`Phi_block`), where `Ψ` sums the generic
increments of the residues `0, …, z`, `y_k` and `x_k` are the values of the exceptional classes in
block `k`, and `E k = ∑_{i<k} (y_i - x_i)`.  The generic charge of a block vanishes
(`OrdCtx.charge_zero`), because both exceptional classes are nonempty.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open OrdinaryDrift

variable {A B : ℕ → ℤ} {r v s t g : ℕ}

/-- The generic increment of the residue `ρ`, with the exceptional residues `τ`, `σ` removed. -/
def gam (A B : ℕ → ℤ) (s τ σ ρ : ℕ) : ℤ :=
  (if ρ = τ then 0 else natC A ρ) - (if ρ = σ then 0 else natB B s ρ)

/-- The generic height `Ψ z` of the residues `0, …, z`. -/
def Psi (A B : ℕ → ℤ) (s τ σ z : ℕ) : ℤ := ∑ ρ ∈ Finset.range (z + 1), gam A B s τ σ ρ

/-- The value of the exceptional column class in block `k`. -/
def yy (A : ℕ → ℤ) (g τ k : ℕ) : ℤ := natC A (k * g + τ)

/-- The value of the exceptional row class in block `k`. -/
def xx (B : ℕ → ℤ) (s g σ k : ℕ) : ℤ := natB B s (k * g + σ)

/-- The charge `E k = ∑_{i<k} (y_i - x_i)` carried into block `k`. -/
def Echarge (A B : ℕ → ℤ) (s g τ σ k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, (yy A g τ i - xx B s g σ i)

/-- The hypotheses of the ordinary residue fold at remainder `a = v mod g`. -/
structure OrdCtx (A B : ℕ → ℤ) (r v s t g : ℕ) : Prop where
  h : OrdWords A B r v s t
  g2 : 2 ≤ g
  gr : g ∣ r
  glt : g < r
  hC : ClassConst (natC A) g r t
  hB : ClassConst (natB B s) g r s

namespace OrdCtx

theorem g_pos (c : OrdCtx A B r v s t g) : 0 < g := by have := c.g2; omega

theorem rmod (c : OrdCtx A B r v s t g) : r % g = 0 := Nat.mod_eq_zero_of_dvd c.gr

theorem natC_bit (c : OrdCtx A B r v s t g) {i : ℕ} (hi : i < r + v) : natC A i = 0 ∨ natC A i = 1 := by
  unfold natC
  by_cases h0 : i = 0
  · simp [h0]
  · simp only [h0, if_false]
    exact (c.h.words.bits i (by omega) hi).1

theorem natB_bit (c : OrdCtx A B r v s t g) {i : ℕ} (hi : i < r + v) : natB B s i = 0 ∨ natB B s i = 1 := by
  unfold natB
  by_cases h0 : i = 0
  · simp [h0]
  · simp only [h0, if_false]
    by_cases hs : i = s
    · simp [hs]
    · simp only [hs, if_false]
      exact (c.h.words.bits i (by omega) hi).2

theorem natC_block (c : OrdCtx A B r v s t g) {k ρ : ℕ} (hk : k * g + ρ < r) (hρ : ρ < g) :
    natC A (k * g + ρ) = if ρ = t % g then yy A g (t % g) k else natC A ρ := by
  have hg := c.g_pos
  have hmod : (k * g + ρ) % g = ρ := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hρ]
  have hρr : ρ < r := by have := c.glt; omega
  by_cases h1 : ρ = t % g
  · simp only [h1, if_true]; rfl
  · simp only [h1, if_false]
    exact c.hC (k * g + ρ) ρ hk hρr (by rw [hmod, Nat.mod_eq_of_lt hρ]) (by rw [hmod]; exact h1)

theorem natB_block (c : OrdCtx A B r v s t g) {k ρ : ℕ} (hk : k * g + ρ < r) (hρ : ρ < g) :
    natB B s (k * g + ρ) = if ρ = s % g then xx B s g (s % g) k else natB B s ρ := by
  have hg := c.g_pos
  have hmod : (k * g + ρ) % g = ρ := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hρ]
  have hρr : ρ < r := by have := c.glt; omega
  by_cases h1 : ρ = s % g
  · simp only [h1, if_true]; rfl
  · simp only [h1, if_false]
    exact c.hB (k * g + ρ) ρ hk hρr (by rw [hmod, Nat.mod_eq_of_lt hρ]) (by rw [hmod]; exact h1)

theorem f_block (c : OrdCtx A B r v s t g) {k ρ : ℕ} (hk : k * g + ρ < r) (hρ : ρ < g) :
    fN A B s (k * g + ρ) = gam A B s (t % g) (s % g) ρ +
      (if ρ = t % g then yy A g (t % g) k else 0) -
        (if ρ = s % g then xx B s g (s % g) k else 0) := by
  unfold fN gam
  rw [c.natC_block hk hρ, c.natB_block hk hρ]
  split_ifs <;> ring

/-- `Φ` at the position `k g + z` of block `k`. -/
theorem Phi_block (c : OrdCtx A B r v s t g) {k z : ℕ} (hk : k * g + z < r) (hz : z < g) :
    Phi A B s (k * g + z) = (∑ i ∈ Finset.range (k * g), fN A B s i) + Psi A B s (t % g) (s % g) z +
      (if t % g ≤ z then yy A g (t % g) k else 0) - (if s % g ≤ z then xx B s g (s % g) k else 0) := by
  have hg := c.g_pos
  unfold Phi Psi
  rw [show k * g + z + 1 = k * g + (z + 1) by ring, Finset.sum_range_add]
  have : ∑ ρ ∈ Finset.range (z + 1), fN A B s (k * g + ρ) =
      ∑ ρ ∈ Finset.range (z + 1), gam A B s (t % g) (s % g) ρ +
        (if t % g ≤ z then yy A g (t % g) k else 0) -
          (if s % g ≤ z then xx B s g (s % g) k else 0) := by
    have hr : ∀ ρ ∈ Finset.range (z + 1), fN A B s (k * g + ρ) =
        gam A B s (t % g) (s % g) ρ + (if ρ = t % g then yy A g (t % g) k else 0) -
          (if ρ = s % g then xx B s g (s % g) k else 0) := by
      intro ρ hρ
      rw [Finset.mem_range] at hρ
      exact c.f_block (by omega) (by omega)
    rw [Finset.sum_congr rfl hr, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_range]
    have e1 : (t % g < z + 1) ↔ t % g ≤ z := by omega
    have e2 : (s % g < z + 1) ↔ s % g ≤ z := by omega
    simp only [e1, e2]
  rw [this]; ring

/-- One block adds the generic charge `Ψ (g - 1)` and the two exceptional values. -/
theorem Qs_succ (c : OrdCtx A B r v s t g) {k : ℕ} (hk : (k + 1) * g ≤ r) :
    ∑ i ∈ Finset.range ((k + 1) * g), fN A B s i =
      (∑ i ∈ Finset.range (k * g), fN A B s i) + Psi A B s (t % g) (s % g) (g - 1) +
        yy A g (t % g) k - xx B s g (s % g) k := by
  have hg := c.g_pos
  have e : (k + 1) * g = k * g + g := by ring
  rw [e, Finset.sum_range_add]
  have hr : ∀ ρ ∈ Finset.range g, fN A B s (k * g + ρ) =
      gam A B s (t % g) (s % g) ρ + (if ρ = t % g then yy A g (t % g) k else 0) -
        (if ρ = s % g then xx B s g (s % g) k else 0) := by
    intro ρ hρ
    rw [Finset.mem_range] at hρ
    have : k * g + g ≤ r := by rw [← e]; exact hk
    exact c.f_block (by omega) hρ
  rw [Finset.sum_congr rfl hr, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range]
  have e1 : t % g < g := Nat.mod_lt _ hg
  have e2 : s % g < g := Nat.mod_lt _ hg
  have e3 : g - 1 + 1 = g := by omega
  simp only [e1, e2, if_true, Psi, e3]
  ring

theorem Qs_formula (c : OrdCtx A B r v s t g) {R : ℕ} (hR : r = g * R) :
    ∀ k, k ≤ R → ∑ i ∈ Finset.range (k * g), fN A B s i =
      k * Psi A B s (t % g) (s % g) (g - 1) + Echarge A B s g (t % g) (s % g) k := by
  intro k
  induction k with
  | zero => intro _; simp [Echarge]
  | succ k ih =>
    intro hk
    have h1 : (k + 1) * g ≤ r := by rw [hR]; nlinarith
    rw [c.Qs_succ h1, ih (by omega)]
    unfold Echarge
    rw [Finset.sum_range_succ]
    push_cast
    ring

theorem yy_bit (c : OrdCtx A B r v s t g) {k : ℕ} (hk : k * g + t % g < r) :
    yy A g (t % g) k = 0 ∨ yy A g (t % g) k = 1 := by
  have := c.h.v_lt
  exact c.natC_bit (by omega)

theorem xx_bit (c : OrdCtx A B r v s t g) {k : ℕ} (hk : k * g + s % g < r) :
    xx B s g (s % g) k = 0 ∨ xx B s g (s % g) k = 1 := by
  have := c.h.v_lt
  exact c.natB_bit (by omega)

/-- The generic charge of a block vanishes. -/
theorem charge_zero (c : OrdCtx A B r v s t g) : Psi A B s (t % g) (s % g) (g - 1) = 0 := by
  have hg := c.g_pos
  obtain ⟨R, hR⟩ := c.gr
  have hv1 := c.h.v_pos
  have hvr := c.h.v_lt
  have ht := c.h.t_lt
  have hs1 := c.h.s_pos
  have hs2 := c.h.s_le
  have hR2 : 2 ≤ R := by
    have := c.glt
    by_contra hcon
    have : g * R ≤ g * 1 := Nat.mul_le_mul_left g (by omega)
    omega
  have hQ := c.Qs_formula hR R le_rfl
  have hr1 : (r - 1) + 1 = R * g := by rw [hR]; ring_nf; omega
  have hPhi : Phi A B s (r - 1) = ∑ i ∈ Finset.range (R * g), fN A B s i := by
    unfold Phi; rw [hr1]
  have h0 := c.h.phi_constraints
  have hPhi0 : Phi A B s (r - 1) = 0 := h0.2.2.2.2.1
  rw [hPhi0] at hPhi
  rw [← hPhi] at hQ
  -- the exceptional sums
  set κ := Psi A B s (t % g) (s % g) (g - 1) with hκ
  have hkt : t / g < R := by
    rw [Nat.div_lt_iff_lt_mul hg]; nlinarith
  have hks : s / g < R := by
    rw [Nat.div_lt_iff_lt_mul hg]; nlinarith
  have hy : ∀ k ∈ Finset.range R, 0 ≤ yy A g (t % g) k ∧ yy A g (t % g) k ≤ 1 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have : k * g + t % g < r := by
      have h1 : (k + 1) * g ≤ R * g := Nat.mul_le_mul_right g hk
      have h2 := Nat.mod_lt t hg
      rw [hR]; nlinarith
    rcases c.yy_bit this with h | h <;> omega
  have hx : ∀ k ∈ Finset.range R, 0 ≤ xx B s g (s % g) k ∧ xx B s g (s % g) k ≤ 1 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have : k * g + s % g < r := by
      have h1 : (k + 1) * g ≤ R * g := Nat.mul_le_mul_right g hk
      have h2 := Nat.mod_lt s hg
      rw [hR]; nlinarith
    rcases c.xx_bit this with h | h <;> omega
  have hy1 : 1 ≤ ∑ k ∈ Finset.range R, yy A g (t % g) k := by
    have h1 : yy A g (t % g) (t / g) = 1 := by
      unfold yy
      rw [Nat.div_add_mod' t g]
      unfold natC
      by_cases ht0 : t = 0
      · simp [ht0]
      · simp only [ht0, if_false]; exact c.h.capA (by omega)
    calc (1 : ℤ) = yy A g (t % g) (t / g) := h1.symm
      _ ≤ _ := Finset.single_le_sum (f := fun k => yy A g (t % g) k)
          (fun k hk => (hy k hk).1) (Finset.mem_range.mpr hkt)
  have hx1 : 1 ≤ ∑ k ∈ Finset.range R, xx B s g (s % g) k := by
    have h1 : xx B s g (s % g) (s / g) = 1 := by
      unfold xx
      rw [Nat.div_add_mod' s g]
      unfold natB
      have : s ≠ 0 := by omega
      simp [this]
    calc (1 : ℤ) = xx B s g (s % g) (s / g) := h1.symm
      _ ≤ _ := Finset.single_le_sum (f := fun k => xx B s g (s % g) k)
          (fun k hk => (hx k hk).1) (Finset.mem_range.mpr hks)
  have hyR : ∑ k ∈ Finset.range R, yy A g (t % g) k ≤ R := by
    calc _ ≤ ∑ k ∈ Finset.range R, (1 : ℤ) := Finset.sum_le_sum fun k hk => (hy k hk).2
      _ = R := by simp
  have hxR : ∑ k ∈ Finset.range R, xx B s g (s % g) k ≤ R := by
    calc _ ≤ ∑ k ∈ Finset.range R, (1 : ℤ) := Finset.sum_le_sum fun k hk => (hx k hk).2
      _ = R := by simp
  unfold Echarge at hQ
  rw [Finset.sum_sub_distrib] at hQ
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hk1 : κ ≤ -1 := by omega
    have : (R : ℤ) * κ ≤ (R : ℤ) * (-1) := mul_le_mul_of_nonneg_left hk1 (by positivity)
    linarith
  · have hk1 : 1 ≤ κ := by omega
    have : (R : ℤ) * 1 ≤ (R : ℤ) * κ := mul_le_mul_of_nonneg_left hk1 (by positivity)
    linarith

end OrdCtx

end FoldSupplied
end SkewGluing
