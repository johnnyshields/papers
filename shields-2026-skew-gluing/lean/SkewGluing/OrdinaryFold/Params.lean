import SkewGluing.OrdinaryFold.Realize

/-!
# The fold parameters read off two ordinary roots

Formalizes `shields-2026-skew-gluing.tex`, «Two ordinary roots» (`prop:gluing-ordinary-fold`,
`lem:gluing-ordinary-drift`): from the setting `GcdPair` of two ordinary roots of nondividing
periods (`SkewGluing.OrdinaryDrift.Words`), the facts about the caps of the first root, in terms
of the generic bits modulo `g`, used to choose the slots `τ`, `σ` of the fold.

Sorry-free.
-/

namespace SkewGluing
namespace OrdinaryDrift

variable {A B A0 B0 : ℕ → ℤ} {N g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ}

theorem GcdPair.shift_mod (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) (x : ℕ) :
    (N - (b * g + wg) + x) % g = x % g := by
  obtain ⟨r, -, hr⟩ := h.root₁.rep
  have : N - (b * g + wg) + x = x + g * (r * a) := by rw [hr]; simp; ring
  rw [this, Nat.add_mul_mod_self_left]

/-- The caps of the first root read through the generic bits (`eq:gluing-caps` and the windows of
`lem:gluing-ordinary-drift`). -/
theorem GcdPair.cap_facts (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) :
    (1 ≤ ha₁ → wg < ha₁ → A0 (ha₁ % g) = 1) ∧
    (ha₁ < b * g + wg → ha₁ + wg < b * g + wg → A0 (ha₁ % g) = 0) ∧
    (1 ≤ hb₁ → wg < hb₁ → B0 (hb₁ % g) = 0) ∧
    (hb₁ < b * g + wg → hb₁ + wg < b * g + wg → B0 (hb₁ % g) = 1) := by
  obtain ⟨-, -, -, -, d5, d6, -, -, -, -⟩ := h.drift_full
  have hN2 := h.root₁.two_q_le
  have hwq := h.root₁.hwq
  have hha := h.root₁.ha_le
  have hhb := h.root₁.hb_le
  have hmax : a * g ≤ max (a * g) (c * g) := le_max_left _ _
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · have := (d5 ha₁ h2 (by omega) (by omega)).1
    rw [← this]; exact h.root₁.capA_init h1
  · have h3 := h.root₁.capA_term (by omega)
    have := (d6 (N - (b * g + wg) + ha₁) (by omega) (by omega)).1
    rw [h.shift_mod] at this
    rw [← this]; exact h3
  · have := (d5 hb₁ h2 (by omega) (by omega)).2
    rw [← this]; exact h.root₁.capB_init h1
  · have h3 := h.root₁.capB_term (by omega)
    have := (d6 (N - (b * g + wg) + hb₁) (by omega) (by omega)).2
    rw [h.shift_mod] at this
    rw [← this]; exact h3



theorem GcdPair.genA₁ (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) :
    ∀ x, 1 ≤ x → x < a * g → x < N → x ≠ ha₁ → A x = A0 (x % g) := by
  intro x hx1 hx2 hx3 hx4
  apply h.genA x hx1 hx3
  rintro ⟨h1, -⟩
  rw [Nat.mod_eq_of_lt hx2] at h1; exact hx4 h1

theorem GcdPair.genB₁ (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) :
    ∀ x, 1 ≤ x → x < a * g → x < N → x ≠ hb₁ → B x = B0 (x % g) := by
  intro x hx1 hx2 hx3 hx4
  apply h.genB x hx1 hx3
  rintro ⟨h1, -⟩
  rw [Nat.mod_eq_of_lt hx2] at h1; exact hx4 h1

/-- The heights of the parent on the first `p` diagonals: generic increments plus the initial
deviations of the first root. -/
theorem GcdPair.height₁ (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) {k : ℕ}
    (hk : k < a * g) (hkN : k < N) :
    heightWord A B k = 1 + genSum (incr A0 B0 g) k +
      (if ha₁ ≤ k then (if 1 ≤ ha₁ then 1 - A0 (ha₁ % g) else 0) else 0) +
      (if hb₁ ≤ k then (if 1 ≤ hb₁ then B0 (hb₁ % g) else 0) else 0) :=
  height_formula h.root₁ h.genA₁ h.genB₁ k hk hkN

/-- **The first budget** (`eq:gluing-pinch-equations`): the initial deviations of the first root
add up to `ε = C_0`. -/
theorem GcdPair.budget_initial (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) :
    (if 1 ≤ ha₁ then 1 - A0 (ha₁ % g) else 0) + (if 1 ≤ hb₁ then B0 (hb₁ % g) else 0) =
      A0 0 - B0 0 := by
  obtain ⟨d1, -, d3, -, -, -, -, -, -, -⟩ := h.drift_full
  obtain ⟨⟨e1, -, -, -⟩, -⟩ := h.pinch_equations
  unfold devA devB at e1
  rw [d1, d3] at e1
  linarith

/-- **The second budget** (`eq:gluing-pinch-equations` for the reversed words): the terminal
deviations of the first root add up to `-C_{w_g} = B⁰_{w_g} - A⁰_{w_g}`. -/
theorem GcdPair.budget_terminal (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) :
    (if hb₁ < b * g + wg then 1 - B0 (hb₁ % g) else 0) +
      (if ha₁ < b * g + wg then A0 (ha₁ % g) else 0) = B0 wg - A0 wg := by
  have hr := h.reverse
  obtain ⟨d1, -, d3, -, -, -, -, -, -, -⟩ := hr.drift_full
  obtain ⟨⟨e1, -, -, -⟩, -⟩ := hr.pinch_equations
  have hg := h.g_pos
  have hNg := h.N_mod
  have hwq := h.root₁.hwq
  have hha := h.root₁.ha_le
  have hhb := h.root₁.hb_le
  have hN2 := h.root₁.two_q_le
  have hxg : ∀ x, x % g ≤ N := fun x => by
    have := Nat.mod_lt x hg
    have : g ≤ a * g := Nat.le_mul_of_pos_left g (by have := h.a_ge; omega)
    omega
  have key : ∀ x, x ≤ b * g + wg → (N - ((b * g + wg - x) % g)) % g = x % g := by
    intro x hx
    rw [← sub_mod_mod (by omega) (hxg _)]
    have : N - (b * g + wg - x) = (N - (b * g + wg)) + x := by omega
    rw [this, h.shift_mod]
  unfold devA devB at e1
  rw [d1, d3] at e1
  simp only [key _ hha, key _ hhb] at e1
  have e0 : (N - 0) % g = wg := by simpa using hNg
  rw [e0] at e1
  have c1 : (1 ≤ b * g + wg - hb₁) ↔ hb₁ < b * g + wg := by omega
  have c2 : (1 ≤ b * g + wg - ha₁) ↔ ha₁ < b * g + wg := by omega
  simp only [c1, c2] at e1
  linarith

end OrdinaryDrift
end SkewGluing
