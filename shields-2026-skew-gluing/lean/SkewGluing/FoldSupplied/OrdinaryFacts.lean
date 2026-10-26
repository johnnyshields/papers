import SkewGluing.FoldSupplied.OrdinaryGeneric

/-!
# The exceptional classes at width at least `g`

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`, the case `v ≥ g`, `a = v mod g > 0`): the first complete window
has positive terminal height, so the exceptional column class starts at one and the exceptional row
class at zero; the last window ends at height zero, so they end at zero and one; and both contacts
project into `[0, a]`.

`OrdCtx.big_facts` collects the exceptional values and the charge carried into the last block.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open OrdinaryDrift

variable {A B : ℕ → ℤ} {r v s t g : ℕ}

theorem Echarge_succ (A B : ℕ → ℤ) (s g τ σ k : ℕ) :
    Echarge A B s g τ σ (k + 1) = Echarge A B s g τ σ k + yy A g τ k - xx B s g σ k := by
  unfold Echarge; rw [Finset.sum_range_succ]; ring

theorem Psi_succ (A B : ℕ → ℤ) (s τ σ z : ℕ) :
    Psi A B s τ σ (z + 1) = Psi A B s τ σ z + gam A B s τ σ (z + 1) := by
  unfold Psi; rw [Finset.sum_range_succ]

theorem Echarge_zero (A B : ℕ → ℤ) (s g τ σ : ℕ) : Echarge A B s g τ σ 0 = 0 := by
  simp [Echarge]

namespace OrdCtx

/-- The block form of `Φ` with the generic charge removed. -/
theorem Phi_blockE (c : OrdCtx A B r v s t g) {k z : ℕ} (hk : k * g + z < r) (hz : z < g) :
    Phi A B s (k * g + z) = Echarge A B s g (t % g) (s % g) k + Psi A B s (t % g) (s % g) z +
      (if t % g ≤ z then yy A g (t % g) k else 0) -
        (if s % g ≤ z then xx B s g (s % g) k else 0) := by
  obtain ⟨R, hR⟩ := c.gr
  have hg := c.g_pos
  have hkR : k ≤ R := by
    by_contra hcon
    have : g * (k) ≥ g * (R + 1) := Nat.mul_le_mul_left g (by omega)
    nlinarith
  rw [c.Phi_block hk hz, c.Qs_formula hR k hkR, c.charge_zero]
  push_cast; ring

theorem tau_lt (c : OrdCtx A B r v s t g) : t % g < g := Nat.mod_lt _ c.g_pos
theorem sigma_lt (c : OrdCtx A B r v s t g) : s % g < g := Nat.mod_lt _ c.g_pos

theorem yy_bit' (c : OrdCtx A B r v s t g) {k : ℕ} (hk : k * g + t % g < r) :
    yy A g (t % g) k = 0 ∨ yy A g (t % g) k = 1 := c.yy_bit hk

/-- **The exceptional classes at width `v ≥ g`.** -/
theorem big_facts (c : OrdCtx A B r v s t g) (ha : 0 < v % g) (hvg : g ≤ v) :
    yy A g (t % g) 0 = 1 ∧ xx B s g (s % g) 0 = 0 ∧
    yy A g (t % g) (v / g) = 0 ∧ xx B s g (s % g) (v / g) = 1 ∧
    Echarge A B s g (t % g) (s % g) (v / g) = 1 ∧ Psi A B s (t % g) (s % g) (v % g) = 0 ∧
    t % g ≤ v % g ∧ s % g ≤ v % g ∧
    (∀ z, z < v % g → (if s % g ≤ z then 1 else 0) ≤ Psi A B s (t % g) (s % g) z) ∧
    (∀ z, z < g → 1 ≤ Psi A B s (t % g) (s % g) z + (if t % g ≤ z then 1 else 0)) := by
  have hg := c.g_pos
  have hvr := c.h.v_lt
  have hglt := c.glt
  have hP := c.h.phi_constraints
  obtain ⟨-, Pge1, Pv0, -, -, -⟩ := hP
  have hag := Nat.mod_lt v hg
  have hv : v = v / g * g + v % g := (Nat.div_add_mod' v g).symm
  set d := v / g with hd
  set a := v % g with ha_def
  have hd1 : 1 ≤ d := (Nat.le_div_iff_mul_le hg).mpr (by omega)
  obtain ⟨R, hR⟩ := c.gr
  have hmulle : ∀ k, k ≤ R → k * g ≤ r := by
    intro k hk
    have := Nat.mul_le_mul_right g hk
    rw [hR]; linarith [Nat.mul_comm g R]
  have hdR : d < R := by
    by_contra hcon
    have h1 := Nat.mul_le_mul_right g (show R ≤ d by omega)
    have h2 : r ≤ d * g := by rw [hR]; linarith [Nat.mul_comm g R]
    omega
  have hτ := c.tau_lt
  have hσ := c.sigma_lt
  obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hpos : ∀ z, z < v → 1 ≤ Phi A B s z := Pge1
  -- bits
  have hy0 := c.yy_bit (k := 0) (by simp; omega)
  have hx0 := c.xx_bit (k := 0) (by simp; omega)
  have hdg1 : (d + 1) * g ≤ r := hmulle (d + 1) (by omega)
  have hdg2 : (d + 1) * g = d * g + g := by ring
  have hyd := c.yy_bit (k := d) (by omega)
  have hxd := c.xx_bit (k := d) (by omega)
  -- step 1: the first window
  have e1 := c.Phi_blockE (k := 0) (z := g - 1) (by simp; omega) (by omega)
  have p1 := hpos (0 * g + (g - 1)) (by simp; omega)
  rw [e1, Echarge_zero, c.charge_zero] at p1
  have t1 : t % g ≤ g - 1 := by omega
  have t2 : s % g ≤ g - 1 := by omega
  simp only [t1, t2, if_true] at p1
  have Y0 : yy A g (t % g) 0 = 1 := by omega
  have X0 : xx B s g (s % g) 0 = 0 := by omega
  -- step 2: the charge before the last block
  have hd'1 : (d' + 1) * g ≤ r := hmulle (d' + 1) (by omega)
  have hd'2 : (d' + 1) * g = d' * g + g := by ring
  have e2 := c.Phi_blockE (k := d') (z := g - 1) (by omega) (by omega)
  have hd'g : d' * g + (g - 1) < v := by
    have : (d' + 1) * g = d' * g + g := by ring
    rw [hd'] at hv; omega
  have p2 := hpos _ hd'g
  rw [e2, c.charge_zero] at p2
  simp only [t1, t2, if_true] at p2
  have Ed' : Echarge A B s g (t % g) (s % g) d = Echarge A B s g (t % g) (s % g) d' +
      yy A g (t % g) d' - xx B s g (s % g) d' := by
    rw [hd']; exact Echarge_succ _ _ _ _ _ _ _
  have E1 : 1 ≤ Echarge A B s g (t % g) (s % g) d := by omega
  -- step 3: the first window at the remainder
  have e3 := c.Phi_blockE (k := 0) (z := a) (by simp; omega) hag
  have p3 := hpos (0 * g + a) (by simp; omega)
  rw [e3, Echarge_zero, Y0, X0] at p3
  -- step 4: the last block ends at height zero
  have e4 := c.Phi_blockE (k := d) (z := a) (by omega) hag
  have p4 : Phi A B s (d * g + a) = 0 := by rw [← hv]; exact Pv0
  rw [e4] at p4
  have main : yy A g (t % g) d = 0 ∧ xx B s g (s % g) d = 1 ∧
      Echarge A B s g (t % g) (s % g) d = 1 ∧ Psi A B s (t % g) (s % g) a = 0 ∧
      t % g ≤ a ∧ s % g ≤ a := by
    by_cases h1 : t % g ≤ a <;> by_cases h2 : s % g ≤ a <;>
      simp only [h1, h2, if_true, if_false] at p3 p4 <;> omega
  obtain ⟨Yd, Xd, Ed1, Pa, hta, hsa⟩ := main
  refine ⟨Y0, X0, Yd, Xd, Ed1, Pa, hta, hsa, ?_, ?_⟩
  · intro z hz
    have e5 := c.Phi_blockE (k := d) (z := z) (by omega) (by omega)
    have p5 := hpos (d * g + z) (by omega)
    rw [e5, Ed1, Yd, Xd] at p5
    split_ifs at p5 ⊢ <;> omega
  · intro z hz
    have e5 := c.Phi_blockE (k := 0) (z := z) (by simp; omega) hz
    have p5 := hpos (0 * g + z) (by simp; omega)
    rw [e5, Echarge_zero, Y0, X0] at p5
    split_ifs at p5 ⊢ <;> omega

end OrdCtx

end FoldSupplied
end SkewGluing
