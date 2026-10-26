/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Fiber
import SkewRibbonCoarsenings.TriangleIdentity

/-!
# The four-block detector

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:detector`
(`lem:four-start`, `eq:four-identity`).

`four_identity` is `eq:four-identity` (stated as `2 ΔK = v(a) ∑_cyc …`), `four_bound` its bound
`|ΔK| ≤ 2`, and `mask_periodic_of_four_vanish` the last assertion of `lem:four-start`: if every
four-block difference vanishes then `𝓑_e` is `d`-periodic.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset Equiv

/-- Sum over the orderings of four labeled points of `β(x_{π0}) β(x_{π0}+x_{π1}) β(-x_{π3})`:
the chain sum `eq:K` for four labels summing to zero, written through the last label. -/
def sum4 {n : ℕ} (β : ZMod n → ℤ) (x : Fin 4 → ZMod n) : ℤ :=
  ∑ π : Perm (Fin 4), β (x (π 0)) * β (x (π 0) + x (π 1)) * β (-x (π 3))

theorem perm4_sum_ite {R : Type*} [AddCommMonoid R] (g : Fin 4 → Fin 4 → Fin 4 → R) :
    ∑ π : Perm (Fin 4), g (π 0) (π 1) (π 3) =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ l : Fin 4, if i ≠ j ∧ i ≠ l ∧ j ≠ l then g i j l else 0 := by
  have hinj : Set.InjOn (fun π : Perm (Fin 4) => (π 0, π 1, π 3))
      (univ : Finset (Perm (Fin 4))) := by
    intro π _ π' _ h
    revert π π'
    decide +kernel
  have himg : (univ : Finset (Perm (Fin 4))).image (fun π => (π 0, π 1, π 3)) =
      univ.filter fun t : Fin 4 × Fin 4 × Fin 4 =>
        t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
    decide +kernel
  rw [← Finset.sum_image (f := fun t : Fin 4 × Fin 4 × Fin 4 => g t.1 t.2.1 t.2.2) hinj, himg,
    Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]

theorem sum4_expand {n : ℕ} (β : ZMod n → ℤ) (x : Fin 4 → ZMod n) :
    sum4 β x = β (x 0) * β (x 0 + x 1) * β (-x 3) + β (x 0) * β (x 0 + x 1) * β (-x 2)
    + β (x 0) * β (x 0 + x 2) * β (-x 3) + β (x 0) * β (x 0 + x 2) * β (-x 1)
    + β (x 0) * β (x 0 + x 3) * β (-x 2) + β (x 0) * β (x 0 + x 3) * β (-x 1)
    + β (x 1) * β (x 1 + x 0) * β (-x 3) + β (x 1) * β (x 1 + x 0) * β (-x 2)
    + β (x 1) * β (x 1 + x 2) * β (-x 3) + β (x 1) * β (x 1 + x 2) * β (-x 0)
    + β (x 1) * β (x 1 + x 3) * β (-x 2) + β (x 1) * β (x 1 + x 3) * β (-x 0)
    + β (x 2) * β (x 2 + x 0) * β (-x 3) + β (x 2) * β (x 2 + x 0) * β (-x 1)
    + β (x 2) * β (x 2 + x 1) * β (-x 3) + β (x 2) * β (x 2 + x 1) * β (-x 0)
    + β (x 2) * β (x 2 + x 3) * β (-x 1) + β (x 2) * β (x 2 + x 3) * β (-x 0)
    + β (x 3) * β (x 3 + x 0) * β (-x 2) + β (x 3) * β (x 3 + x 0) * β (-x 1)
    + β (x 3) * β (x 3 + x 1) * β (-x 2) + β (x 3) * β (x 3 + x 1) * β (-x 0)
    + β (x 3) * β (x 3 + x 2) * β (-x 1) + β (x 3) * β (x 3 + x 2) * β (-x 0) := by
  unfold sum4
  rw [perm4_sum_ite (fun i j l => β (x i) * β (x i + x j) * β (-x l))]
  simp [Fin.sum_univ_four]
  ring

/-- `eq:K` for four labels: `K_b` is the sum over orderings of the product of the retained
cut indicators at the three proper partial sums. -/
theorem K_four {n : ℕ} {S : Finset ℕ} (hS : IsCutSet n S) (a : Fin 4 → ℕ)
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) :
    (K S a : ℤ) = sum4 (cutInd n S) (fun i => ((a i : ℕ) : ZMod n)) := by
  have hlt : ∀ i, a i < n := by
    intro i
    have h4 : ∑ j, a j = a 0 + a 1 + a 2 + a 3 := Fin.sum_univ_four a
    have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2; have h3 := hpos 3
    fin_cases i <;> simp <;> omega
  unfold K sum4
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro π _
  have hs : a (π 0) + a (π 1) + a (π 2) + a (π 3) = n := by
    have := Equiv.sum_comp π a
    rw [Fin.sum_univ_four, Fin.sum_univ_four] at this
    rw [Fin.sum_univ_four] at hsum
    omega
  have e1 : partialSum a π 1 = a (π 0) := by
    simp [partialSum, Finset.sum_filter]
  have e2 : partialSum a π 2 = a (π 0) + a (π 1) := by
    simp only [partialSum, Finset.sum_filter, Fin.sum_univ_four]
    simp
  have e3 : partialSum a π 3 = a (π 0) + a (π 1) + a (π 2) := by
    simp only [partialSum, Finset.sum_filter, Fin.sum_univ_four]
    simp
  have hcond : (∀ j < 4, 0 < j → partialSum a π j ∈ S) ↔
      (a (π 0) ∈ S ∧ a (π 0) + a (π 1) ∈ S ∧ a (π 0) + a (π 1) + a (π 2) ∈ S) := by
    constructor
    · intro h
      exact ⟨e1 ▸ h 1 (by omega) (by omega), e2 ▸ h 2 (by omega) (by omega),
        e3 ▸ h 3 (by omega) (by omega)⟩
    · rintro ⟨h1, h2, h3⟩ j hj hj0
      interval_cases j
      · rw [e1]; exact h1
      · rw [e2]; exact h2
      · rw [e3]; exact h3
  simp only [hcond]
  have hl0 := hlt (π 0)
  have hl1 : a (π 0) + a (π 1) < n := by
    have := hpos (π 2); have := hpos (π 3); omega
  have hl3 := hlt (π 3)
  have hcast : ((a (π 0) : ℕ) : ZMod n) + ((a (π 1) : ℕ) : ZMod n) =
      ((a (π 0) + a (π 1) : ℕ) : ZMod n) := by push_cast; ring
  rw [hcast, cutInd_natCast hl0, cutInd_natCast hl1, cutInd_neg_natCast hS hl3]
  have : n - a (π 3) = a (π 0) + a (π 1) + a (π 2) := by omega
  rw [this]
  by_cases h1 : a (π 0) ∈ S <;> by_cases h2 : a (π 0) + a (π 1) ∈ S <;>
    by_cases h3 : a (π 0) + a (π 1) + a (π 2) ∈ S <;> simp [h1, h2, h3]

theorem four_algebra {n : ℕ} (β γ : ZMod n → ℤ) (x : Fin 4 → ZMod n)
    (hsum : x 0 + x 1 + x 2 + x 3 = 0)
    (g1 : γ (x 1) = β (x 1)) (g2 : γ (x 2) = β (x 2)) (g3 : γ (x 3) = β (x 3))
    (gm1 : γ (-x 1) = β (-x 1)) (gm2 : γ (-x 2) = β (-x 2)) (gm3 : γ (-x 3) = β (-x 3))
    (ga1 : γ (x 0 + x 1) = β (x 0 + x 1)) (ga2 : γ (x 0 + x 2) = β (x 0 + x 2))
    (ga3 : γ (x 0 + x 3) = β (x 0 + x 3))
    (gma1 : γ (-(x 0 + x 1)) = β (-(x 0 + x 1))) (gma2 : γ (-(x 0 + x 2)) = β (-(x 0 + x 2)))
    (gma3 : γ (-(x 0 + x 3)) = β (-(x 0 + x 3)))
    (hτ : γ (x 0) + γ (-x 0) = β (x 0) + β (-x 0))
    (w1 : β (-(x 0 + x 1)) = β (x 0 + x 1) - (β (x 1) - β (-x 1)))
    (w2 : β (-(x 0 + x 2)) = β (x 0 + x 2) - (β (x 2) - β (-x 2)))
    (w3 : β (-(x 0 + x 3)) = β (x 0 + x 3) - (β (x 3) - β (-x 3))) :
    2 * (sum4 β x - sum4 γ x) = (β (x 0) - γ (x 0)) *
      (((β (x 2) - β (-x 2)) + (β (x 3) - β (-x 3))) *
          ((β (x 1) + β (-x 1)) - (β (x 0 + x 1) + β (-(x 0 + x 1))))
        + ((β (x 3) - β (-x 3)) + (β (x 1) - β (-x 1))) *
          ((β (x 2) + β (-x 2)) - (β (x 0 + x 2) + β (-(x 0 + x 2))))
        + ((β (x 1) - β (-x 1)) + (β (x 2) - β (-x 2))) *
          ((β (x 3) + β (-x 3)) - (β (x 0 + x 3) + β (-(x 0 + x 3))))) := by
  have h12 : x 1 + x 2 = -(x 0 + x 3) := by linear_combination hsum
  have h13 : x 1 + x 3 = -(x 0 + x 2) := by linear_combination hsum
  have h23 : x 2 + x 3 = -(x 0 + x 1) := by linear_combination hsum
  have h21 : x 2 + x 1 = -(x 0 + x 3) := by linear_combination hsum
  have h31 : x 3 + x 1 = -(x 0 + x 2) := by linear_combination hsum
  have h32 : x 3 + x 2 = -(x 0 + x 1) := by linear_combination hsum
  have h10 : x 1 + x 0 = x 0 + x 1 := add_comm _ _
  have h20 : x 2 + x 0 = x 0 + x 2 := add_comm _ _
  have h30 : x 3 + x 0 = x 0 + x 3 := add_comm _ _
  have gm0 : γ (-x 0) = β (x 0) + β (-x 0) - γ (x 0) := by linarith
  rw [sum4_expand, sum4_expand]
  simp only [h12, h13, h23, h21, h31, h32, h10, h20, h30, gm0, g1, g2, g3, gm1, gm2, gm3, ga1, ga2,
    ga3, gma1, gma2, gma3, w1, w2, w3]
  ring

/-- The labeled difference `ΔK(a, r, s, z) = K_b(a, r, s, z) - K_c(a, r, s, z)` of four labels. -/
def deltaK4 (n : ℕ) (S S' : Finset ℕ) (a r s z : ℕ) : ℤ :=
  (K S ![a, r, s, z] : ℤ) - (K S' ![a, r, s, z] : ℤ)

section Identity

variable {n : ℕ} {S S' : Finset ℕ} {d e : ℕ}

lemma val_natCast_of_lt' {m : ℕ} (hm : m < n) : ((m : ℕ) : ZMod n).val = m :=
  ZMod.val_natCast_of_lt hm

/-- A positive natural number below `n` is off the `d`-grid of `ℤ/n` exactly when it is not
divisible by `d`. -/
lemma not_dvd_val_natCast {m : ℕ} (hm : m < n) (hd : ¬ d ∣ m) : ¬ d ∣ ((m : ℕ) : ZMod n).val := by
  rwa [val_natCast_of_lt' hm]

/-- `lem:four-start`, `eq:four-identity`.  In the normalized setting, for `0 < a < n`
representing an element of `supp v` and `r, s, z` positive and off the `d`-grid with
`a + r + s + z = n`:
`2 ΔK(a, r, s, z) = v(a) ∑_cyc (w(s) + w(z)) (τ(r) - τ(r + a))`. -/
theorem four_identity (h : NormalizedSetting n S S' d e) {a r s z : ℕ} (ha : 0 < a) (hr : 0 < r) (hs : 0 < s)
    (hz : 0 < z) (hva : vFun n S S' (a : ZMod n) ≠ 0) (hrd : ¬ d ∣ r) (hsd : ¬ d ∣ s)
    (hzd : ¬ d ∣ z) (hsum : a + r + s + z = n) :
    2 * deltaK4 n S S' a r s z = vFun n S S' (a : ZMod n) *
      ((wFun n S S' d (s : ZMod n) + wFun n S S' d (z : ZMod n)) *
          (tauFun n S (r : ZMod n) - tauFun n S ((r : ZMod n) + (a : ZMod n)))
        + (wFun n S S' d (z : ZMod n) + wFun n S S' d (r : ZMod n)) *
          (tauFun n S (s : ZMod n) - tauFun n S ((s : ZMod n) + (a : ZMod n)))
        + (wFun n S S' d (r : ZMod n) + wFun n S S' d (s : ZMod n)) *
          (tauFun n S (z : ZMod n) - tauFun n S ((z : ZMod n) + (a : ZMod n)))) := by
  have hn : 0 < n := by omega
  haveI : NeZero n := ⟨hn.ne'⟩
  have hdn : d ∣ n := h.d_dvd_n
  have hda : d ∣ (a : ZMod n).val := h.dvd_of_v_ne hva
  have hrn : r < n := by omega
  have hsn : s < n := by omega
  have hzn : z < n := by omega
  -- the four points
  set x : Fin 4 → ZMod n := fun i => ((![a, r, s, z] i : ℕ) : ZMod n) with hx
  have hx0 : x 0 = (a : ZMod n) := rfl
  have hx1 : x 1 = (r : ZMod n) := rfl
  have hx2 : x 2 = (s : ZMod n) := rfl
  have hx3 : x 3 = (z : ZMod n) := rfl
  have hsumz : x 0 + x 1 + x 2 + x 3 = 0 := by
    rw [hx0, hx1, hx2, hx3]
    have : ((a + r + s + z : ℕ) : ZMod n) = 0 := by rw [hsum]; exact ZMod.natCast_self n
    push_cast at this; exact this
  have hKb : (K S ![a, r, s, z] : ℤ) = sum4 (cutInd n S) x := by
    apply K_four h.cuts
    · intro i; fin_cases i <;> simp <;> omega
    · simp [Fin.sum_univ_four]; omega
  have hKc : (K S' ![a, r, s, z] : ℤ) = sum4 (cutInd n S') x := by
    apply K_four h.cuts'
    · intro i; fin_cases i <;> simp <;> omega
    · simp [Fin.sum_univ_four]; omega
  -- off-grid facts
  have off : ∀ y : ZMod n, ¬ d ∣ y.val → cutInd n S' y = cutInd n S y :=
    fun y hy => (h.cutInd_eq_of_not_dvd hy).symm
  have offneg : ∀ y : ZMod n, ¬ d ∣ y.val → ¬ d ∣ (-y).val := fun y hy => by
    rwa [dvd_val_neg hdn]
  have offadd : ∀ y : ZMod n, ¬ d ∣ y.val → ¬ d ∣ (x 0 + y).val := fun y hy => by
    rw [add_comm, dvd_val_add hdn (by rw [hx0]; exact hda)]; exact hy
  have hr' : ¬ d ∣ (x 1).val := not_dvd_val_natCast hrn hrd
  have hs' : ¬ d ∣ (x 2).val := not_dvd_val_natCast hsn hsd
  have hz' : ¬ d ∣ (x 3).val := not_dvd_val_natCast hzn hzd
  have wsh : ∀ y : ZMod n, ¬ d ∣ y.val →
      wFun n S S' d (x 0 + y) = wFun n S S' d y := fun y _ => by
    rw [add_comm]; exact h.w_add_d (by rw [hx0]; exact hda) y
  have wrel : ∀ y : ZMod n, ¬ d ∣ y.val →
      cutInd n S (-(x 0 + y)) = cutInd n S (x 0 + y) - (cutInd n S y - cutInd n S (-y)) := by
    intro y hy
    have h1 := h.wFun_eq_off (offadd y hy)
    have h2 := h.wFun_eq_off hy
    rw [wsh y hy, h2] at h1
    linarith
  have key := four_algebra (cutInd n S) (cutInd n S') x hsumz
    (off _ hr') (off _ hs') (off _ hz')
    (off _ (offneg _ hr')) (off _ (offneg _ hs')) (off _ (offneg _ hz'))
    (off _ (offadd _ hr')) (off _ (offadd _ hs')) (off _ (offadd _ hz'))
    (off _ (by rw [dvd_val_neg hdn]; exact offadd _ hr'))
    (off _ (by rw [dvd_val_neg hdn]; exact offadd _ hs'))
    (off _ (by rw [dvd_val_neg hdn]; exact offadd _ hz'))
    (h.tau_eq (x 0)).symm (wrel _ hr') (wrel _ hs') (wrel _ hz')
  unfold deltaK4
  rw [hKb, hKc]
  rw [key]
  have e1 := h.wFun_eq_off hr'
  have e2 := h.wFun_eq_off hs'
  have e3 := h.wFun_eq_off hz'
  have hv : vFun n S S' (a : ZMod n) = cutInd n S (x 0) - cutInd n S' (x 0) := by
    rw [hx0]; rfl
  have c1 : (x 0 + x 1) = (r : ZMod n) + (a : ZMod n) := by rw [hx0, hx1]; ring
  have c2 : (x 0 + x 2) = (s : ZMod n) + (a : ZMod n) := by rw [hx0, hx2]; ring
  have c3 : (x 0 + x 3) = (z : ZMod n) + (a : ZMod n) := by rw [hx0, hx3]; ring
  unfold tauFun
  rw [hv, hx1, hx2, hx3] at *
  rw [← c1, ← c2, ← c3] at *
  rw [e1, e2, e3]

/-! ### The bound `|ΔK| ≤ 2` -/

/-- For `A` on the `d`-grid and `y` off it, `b(-(A + y)) = b(A + y) - (b(y) - b(-y))`
(`w(A + y) = w(y)` and `w = b(·) - b(-·)` off the grid). -/
lemma cutInd_neg_shift (h : NormalizedSetting n S S' d e) [NeZero n] {A y : ZMod n}
    (hA : d ∣ A.val) (hy : ¬ d ∣ y.val) :
    cutInd n S (-(A + y)) = cutInd n S (A + y) - (cutInd n S y - cutInd n S (-y)) := by
  have hdn := h.d_dvd_n
  have hAy : ¬ d ∣ (A + y).val := by
    rw [add_comm, dvd_val_add hdn hA]; exact hy
  have h1 := h.wFun_eq_off hAy
  have h2 := h.wFun_eq_off hy
  have h3 : wFun n S S' d (A + y) = wFun n S S' d y := by
    rw [add_comm]; exact h.w_add_d hA y
  rw [h3, h2] at h1
  linarith

/-- `τ(y) - τ(y + A) = 2 (b(y) - b(y + A))` for `y` off the `d`-grid, `A` on it. -/
lemma tauFun_diff (h : NormalizedSetting n S S' d e) [NeZero n] {A y : ZMod n}
    (hA : d ∣ A.val) (hy : ¬ d ∣ y.val) :
    tauFun n S y - tauFun n S (y + A) = 2 * (cutInd n S y - cutInd n S (y + A)) := by
  have := cutInd_neg_shift h hA hy
  unfold tauFun
  rw [add_comm y A, show -(A + y) = -(A + y) from rfl, this]
  ring

/-- `w(y) (b(y) - b(y + A)) = 0` for `y` off the `d`-grid, `A` on it. -/
lemma w_mul_diff (h : NormalizedSetting n S S' d e) [NeZero n] {A y : ZMod n}
    (hA : d ∣ A.val) (hy : ¬ d ∣ y.val) :
    wFun n S S' d y * (cutInd n S y - cutInd n S (y + A)) = 0 := by
  have h1 := cutInd_neg_shift h hA hy
  have h2 := h.wFun_eq_off hy
  rw [h2, add_comm y A]
  have c1 := cutInd_cases n S y
  have c2 := cutInd_cases n S (-y)
  have c3 := cutInd_cases n S (A + y)
  have c4 := cutInd_cases n S (-(A + y))
  rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2 <;> rcases c3 with c3 | c3 <;>
    rcases c4 with c4 | c4 <;> simp only [c1, c2, c3, c4] at h1 ⊢ <;> omega

lemma cutInd_sub_tern (y A : ZMod n) (S : Finset ℕ) :
    cutInd n S y - cutInd n S (y + A) = 0 ∨ cutInd n S y - cutInd n S (y + A) = 1 ∨
      cutInd n S y - cutInd n S (y + A) = -1 := by
  have c1 := cutInd_cases n S y
  have c2 := cutInd_cases n S (y + A)
  omega

theorem tern_bound_four (p q r u v w : ℤ) (hp : p = 0 ∨ p = 1 ∨ p = -1) (hq : q = 0 ∨ q = 1 ∨ q = -1)
    (hr : r = 0 ∨ r = 1 ∨ r = -1) (hu : u = 0 ∨ u = 1 ∨ u = -1) (hv : v = 0 ∨ v = 1 ∨ v = -1)
    (hw : w = 0 ∨ w = 1 ∨ w = -1) (h1 : p * u = 0) (h2 : q * v = 0) (h3 : r * w = 0) :
    |p * (v + w) + q * (u + w) + r * (u + v)| ≤ 2 := by
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> simp_all

/-- `lem:four-start`: the bound `|ΔK(a, r, s, z)| ≤ 2`. -/
theorem four_bound (h : NormalizedSetting n S S' d e) {a r s z : ℕ} (ha : 0 < a) (hr : 0 < r)
    (hs : 0 < s) (hz : 0 < z) (hva : vFun n S S' (a : ZMod n) ≠ 0) (hrd : ¬ d ∣ r)
    (hsd : ¬ d ∣ s) (hzd : ¬ d ∣ z) (hsum : a + r + s + z = n) :
    |deltaK4 n S S' a r s z| ≤ 2 := by
  have hn : 0 < n := by omega
  haveI : NeZero n := ⟨hn.ne'⟩
  have hdn := h.d_dvd_n
  have hda : d ∣ (a : ZMod n).val := h.dvd_of_v_ne hva
  have key := four_identity h ha hr hs hz hva hrd hsd hzd hsum
  have hr' : ¬ d ∣ ((r : ℕ) : ZMod n).val := not_dvd_val_natCast (by omega) hrd
  have hs' : ¬ d ∣ ((s : ℕ) : ZMod n).val := not_dvd_val_natCast (by omega) hsd
  have hz' : ¬ d ∣ ((z : ℕ) : ZMod n).val := not_dvd_val_natCast (by omega) hzd
  rw [tauFun_diff h hda hr', tauFun_diff h hda hs', tauFun_diff h hda hz'] at key
  have hv : vFun n S S' (a : ZMod n) = 0 ∨ vFun n S S' (a : ZMod n) = 1 ∨
      vFun n S S' (a : ZMod n) = -1 := by
    unfold vFun
    have c1 := cutInd_cases n S (a : ZMod n)
    have c2 := cutInd_cases n S' (a : ZMod n)
    omega
  have hb := tern_bound_four
    (cutInd n S (r : ZMod n) - cutInd n S ((r : ZMod n) + (a : ZMod n)))
    (cutInd n S (s : ZMod n) - cutInd n S ((s : ZMod n) + (a : ZMod n)))
    (cutInd n S (z : ZMod n) - cutInd n S ((z : ZMod n) + (a : ZMod n)))
    (wFun n S S' d (r : ZMod n)) (wFun n S S' d (s : ZMod n)) (wFun n S S' d (z : ZMod n))
    (cutInd_sub_tern _ _ S) (cutInd_sub_tern _ _ S) (cutInd_sub_tern _ _ S)
    (w_cases d _) (w_cases d _) (w_cases d _)
    (by rw [mul_comm]; exact w_mul_diff h hda hr') (by rw [mul_comm]; exact w_mul_diff h hda hs')
    (by rw [mul_comm]; exact w_mul_diff h hda hz')
  have hD : deltaK4 n S S' a r s z = vFun n S S' (a : ZMod n) *
      ((cutInd n S (r : ZMod n) - cutInd n S ((r : ZMod n) + (a : ZMod n))) *
        (wFun n S S' d (s : ZMod n) + wFun n S S' d (z : ZMod n)) +
      (cutInd n S (s : ZMod n) - cutInd n S ((s : ZMod n) + (a : ZMod n))) *
        (wFun n S S' d (r : ZMod n) + wFun n S S' d (z : ZMod n)) +
      (cutInd n S (z : ZMod n) - cutInd n S ((z : ZMod n) + (a : ZMod n))) *
        (wFun n S S' d (r : ZMod n) + wFun n S S' d (s : ZMod n))) := by
    linarith
  rw [hD, abs_mul]
  have hv1 : |vFun n S S' (a : ZMod n)| ≤ 1 := by
    rcases hv with h0 | h0 | h0 <;> rw [h0] <;> simp
  calc _ ≤ 1 * 2 := mul_le_mul hv1 hb (abs_nonneg _) (by norm_num)
    _ = 2 := by norm_num

end Identity

/-! ### The periodicity conclusion of `lem:four-start`

The circle `ℤ/W`, `W = n - a`, is realized as `W`-periodic functions on `ℤ`, with the
representative map `Rm W`. -/

namespace FourStart

/-- Representative in `{0, …, W-1}` of an integer modulo `W`. -/
def Rm (W : ℕ) (x : ℤ) : ℕ := (x % (W : ℤ)).toNat

lemma Rm_cast {W : ℕ} (hW : 0 < W) (x : ℤ) : ((Rm W x : ℕ) : ℤ) = x % W :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hW.ne'))

lemma Rm_lt {W : ℕ} (hW : 0 < W) (x : ℤ) : Rm W x < W := by
  have h1 := Rm_cast hW x
  have h2 := Int.emod_lt_of_pos x (by exact_mod_cast hW : (0 : ℤ) < W)
  omega

lemma Rm_of_lt {W : ℕ} (hW : 0 < W) {m : ℕ} (hm : m < W) : Rm W (m : ℤ) = m := by
  have := Rm_cast hW (m : ℤ)
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hm)] at this
  omega

lemma Rm_add_W (W : ℕ) (x : ℤ) : Rm W (x + W) = Rm W x := by simp [Rm]

lemma Rm_eq {W : ℕ} (hW : 0 < W) (x : ℤ) : (Rm W x : ℤ) = x - W * (x / W) := by
  rw [Rm_cast hW]; have := Int.emod_add_mul_ediv x W; linarith

lemma Rm_dvd_iff {W d : ℕ} (hW : 0 < W) (hdW : d ∣ W) (x : ℤ) : (d : ℤ) ∣ x ↔ d ∣ Rm W x := by
  have hdW' : (d : ℤ) ∣ (W : ℤ) := by exact_mod_cast hdW
  have h2 := Rm_eq hW x
  constructor
  · intro hx
    have h3 : (d : ℤ) ∣ (Rm W x : ℤ) := by
      rw [h2]; exact dvd_sub hx (dvd_mul_of_dvd_left hdW' _)
    exact_mod_cast h3
  · intro hx
    have hx' : (d : ℤ) ∣ (Rm W x : ℤ) := by exact_mod_cast hx
    have h4 : x = (Rm W x : ℤ) + W * (x / W) := by rw [h2]; ring
    rw [h4]; exact dvd_add hx' (dvd_mul_of_dvd_left hdW' _)

lemma Rm_eq_of_dvd {W m : ℕ} (hW : 0 < W) (hm : m < W) {x : ℤ} (h : (W : ℤ) ∣ (m : ℤ) - x) :
    Rm W x = m := by
  have h1 := Rm_cast hW x
  have h2 : x ≡ (m : ℤ) [ZMOD W] := Int.modEq_iff_dvd.mpr h
  have h3 : x % (W : ℤ) = (m : ℤ) := by
    have := h2; unfold Int.ModEq at this
    rw [this, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hm)]
  omega

lemma Rm_neg {W : ℕ} (hW : 0 < W) {x : ℤ} (hx : Rm W x ≠ 0) : Rm W (-x) = W - Rm W x := by
  have hlt := Rm_lt hW x
  apply Rm_eq_of_dvd hW (by omega)
  have h1 := Rm_eq hW x
  have : ((W - Rm W x : ℕ) : ℤ) = (W : ℤ) - (Rm W x : ℤ) := by omega
  rw [this, h1]
  exact ⟨1 + x / W, by ring⟩

lemma three_sum {W X Y Z : ℕ} (hX : 0 < X) (hXW : X < W) (hY : 0 < Y) (hYW : Y < W)
    (hZ : 0 < Z) (hZW : Z < W) (hd : (W : ℤ) ∣ (X : ℤ) + Y + Z) :
    X + Y + Z = W ∨ X + Y + Z = 2 * W := by
  obtain ⟨k, hk⟩ := hd
  have hk0 : 0 ≤ k := by
    by_contra hneg
    replace hneg := lt_of_not_ge hneg
    have : (W : ℤ) * k ≤ -(W : ℤ) := by nlinarith [(by omega : (1 : ℤ) ≤ W)]
    omega
  have hk' : X + Y + Z = W * k.toNat := by
    zify; rw [Int.toNat_of_nonneg hk0]; exact hk
  have h1 : 0 < k.toNat := by
    rcases Nat.eq_zero_or_pos k.toNat with h0 | h0
    · rw [h0] at hk'; omega
    · exact h0
  have h2 : k.toNat < 3 := by
    by_contra hge
    replace hge := le_of_not_gt hge
    have : W * 3 ≤ W * k.toNat := Nat.mul_le_mul_left _ hge
    omega
  have : k.toNat = 1 ∨ k.toNat = 2 := by omega
  rcases this with h | h <;> rw [h] at hk' <;> omega

/-- Finite-orbit argument of `lem:four-start`: a sequence `T` of period `M` with values in `{1}` or
in `{0, 2}`, with `T j - T (j + t) = C₁` for `j < M - t` and `T j - T (j + (M - t)) = C₂` for
`j < t`, and `2 t < M`, is invariant under the shift by `t`. -/
theorem shift_invariance (T : ℕ → ℤ) (M t : ℕ) (ht : 0 < t) (hM : 2 * t < M)
    (hper : ∀ j, T (j + M) = T j)
    (hcase : (∀ j, T j = 1) ∨ (∀ j, T j = 0 ∨ T j = 2)) (C₁ C₂ : ℤ)
    (h1 : ∀ j, j < M - t → T j - T (j + t) = C₁)
    (h2 : ∀ j, j < t → T j - T (j + (M - t)) = C₂) :
    ∀ j, j < M → T (j + t) = T j := by
  have hC : C₁ = 0 := by
    rcases hcase with h | h
    · have := h1 0 (by omega); rw [h 0, zero_add, h t] at this; omega
    · have e1 := h1 0 (by omega)
      have e2 := h1 t (by omega)
      have e3 := h 0; have e4 := h t; have e5 := h (t + t)
      rw [zero_add] at e1
      omega
  have hsum := sum_range_shift_periodic T hper t
  have hsplit : ∑ j ∈ range M, T (j + t) = ∑ j ∈ range (M - t), T (j + t) +
      ∑ i ∈ range t, T (M - t + i + t) := by
    have := Finset.sum_range_add (fun j => T (j + t)) (M - t) t
    rwa [show M - t + t = M by omega] at this
  have hsplit2 : ∑ j ∈ range M, T j = ∑ j ∈ range (M - t), T j + ∑ i ∈ range t, T (M - t + i) := by
    have := Finset.sum_range_add T (M - t) t
    rwa [show M - t + t = M by omega] at this
  have hfirst : ∑ j ∈ range (M - t), T (j + t) = ∑ j ∈ range (M - t), T j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have := h1 j (Finset.mem_range.mp hj)
    omega
  have hwrap : ∀ i, i < t → T (M - t + i + t) - T (M - t + i) = C₂ := by
    intro i hi
    have h3 : T (M - t + i + t) = T i := by
      rw [show M - t + i + t = i + M by omega, hper]
    have := h2 i hi
    rw [h3, show M - t + i = i + (M - t) by omega]
    omega
  have hsumw : ∑ i ∈ range t, (T (M - t + i + t) - T (M - t + i)) = t * C₂ := by
    rw [Finset.sum_congr rfl (fun i hi => hwrap i (Finset.mem_range.mp hi))]
    simp
  have hsub : ∑ i ∈ range t, (T (M - t + i + t) - T (M - t + i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    linarith
  have hC2 : C₂ = 0 := by
    rw [hsub] at hsumw
    have : (t : ℤ) * C₂ = 0 := hsumw.symm
    rcases mul_eq_zero.mp this with h | h
    · omega
    · exact h
  intro j hj
  by_cases hjt : j < M - t
  · have := h1 j hjt
    omega
  · obtain ⟨i, rfl⟩ : ∃ i, j = M - t + i := ⟨j - (M - t), by omega⟩
    have := hwrap i (by omega)
    omega

end FourStart


open FourStart

section Periodic

variable {n : ℕ} {S S' : Finset ℕ} {d e : ℕ}

/-- The hypothesis of the last assertion of `lem:four-start`: every four-block difference
`ΔK(a, r, s, z)`, `a` a positive representative of an element of `supp v` and `r, s, z`
positive and off the `d`-grid with `a + r + s + z = n`, vanishes. -/
def FourBlockVanish (n : ℕ) (S S' : Finset ℕ) (d : ℕ) : Prop :=
  ∀ a r s z : ℕ, 0 < a → 0 < r → 0 < s → 0 < z → vFun n S S' (a : ZMod n) ≠ 0 →
    ¬ d ∣ r → ¬ d ∣ s → ¬ d ∣ z → a + r + s + z = n → deltaK4 n S S' a r s z = 0

/-- `τ(m) - τ(m + a)` for natural `m`. -/
def gDiff (n : ℕ) (S : Finset ℕ) (a m : ℕ) : ℤ :=
  tauFun n S (m : ZMod n) - tauFun n S ((m + a : ℕ) : ZMod n)

lemma tauFun_neg (x : ZMod n) : tauFun n S (-x) = tauFun n S x := by
  unfold tauFun; rw [neg_neg]; ring

lemma cyc_zero (h : NormalizedSetting n S S' d e) (hz : FourBlockVanish n S S' d)
    {a r s z : ℕ} (ha : 0 < a) (hr : 0 < r) (hs : 0 < s) (hz' : 0 < z)
    (hva : vFun n S S' (a : ZMod n) ≠ 0) (hrd : ¬ d ∣ r) (hsd : ¬ d ∣ s) (hzd : ¬ d ∣ z)
    (hsum : a + r + s + z = n) :
    (wFun n S S' d (s : ZMod n) + wFun n S S' d (z : ZMod n)) * gDiff n S a r
    + (wFun n S S' d (z : ZMod n) + wFun n S S' d (r : ZMod n)) * gDiff n S a s
    + (wFun n S S' d (r : ZMod n) + wFun n S S' d (s : ZMod n)) * gDiff n S a z = 0 := by
  have key := four_identity h ha hr hs hz' hva hrd hsd hzd hsum
  rw [hz a r s z ha hr hs hz' hva hrd hsd hzd hsum] at key
  have key2 := key.symm
  rw [mul_zero] at key2
  rcases mul_eq_zero.mp key2 with h0 | h0
  · exact absurd h0 hva
  · simp only [gDiff, Nat.cast_add]
    linarith [h0]

/-- `w` on `ℤ`, through the cast to `ℤ/n`. -/
def wInt (n : ℕ) (S S' : Finset ℕ) (d : ℕ) (x : ℤ) : ℤ := wFun n S S' d (x : ZMod n)

/-- The function `φ_a` of `lem:four-start` on the circle `ℤ/W`, `W = n - a`, as a `W`-periodic
function on `ℤ`, without the factor `1/2`: the value is `τ(m) - τ(m + a)` at the representative
`0 ≤ m < W`, and `0` on the `d`-grid. -/
def phiInt (n : ℕ) (S : Finset ℕ) (d a : ℕ) (x : ℤ) : ℤ :=
  if d ∣ Rm (n - a) x then 0 else gDiff n S a (Rm (n - a) x)

lemma natCast_sub_eq_neg' {m : ℕ} (hm : m ≤ n) : ((n - m : ℕ) : ZMod n) = -(m : ZMod n) := by
  rw [Nat.cast_sub hm, ZMod.natCast_self]; ring

section Setup

variable [NeZero n]

lemma wInt_add_W (h : NormalizedSetting n S S' d e) {a : ℕ} (ha : a < n) (hda : d ∣ a) (x : ℤ) :
    wInt n S S' d (x + ((n - a : ℕ) : ℤ)) = wInt n S S' d x := by
  unfold wInt
  have hdn := h.d_dvd_n
  have hy : d ∣ (-(a : ZMod n)).val := by
    rw [dvd_val_neg hdn]; exact (nat_dvd_iff_val hdn a).mp hda
  have h1 := h.w_add_d hy (x : ZMod n)
  have h2 : ((x + ((n - a : ℕ) : ℤ) : ℤ) : ZMod n) = (x : ZMod n) + -(a : ZMod n) := by
    push_cast; rw [natCast_sub_eq_neg' ha.le]
  rw [h2]; exact h1

lemma wInt_neg (h : NormalizedSetting n S S' d e) (x : ℤ) :
    wInt n S S' d (-x) = - wInt n S S' d x := by
  unfold wInt; push_cast; exact h.w_odd _

lemma wInt_add_e (h : NormalizedSetting n S S' d e) (x : ℤ) :
    wInt n S S' d (x + e) = wInt n S S' d x := by
  unfold wInt; push_cast; exact h.e_least.2.2.1 _

lemma wInt_shift_d (h : NormalizedSetting n S S' d e) {x : ℤ} (hx : (d : ℤ) ∣ x) (y : ℤ) :
    wInt n S S' d (x + y) = wInt n S S' d y := by
  unfold wInt; push_cast
  rw [add_comm]
  exact h.w_add_d ((int_dvd_iff_val h.d_dvd_n x).mp hx) _

lemma wInt_of_dvd (h : NormalizedSetting n S S' d e) {x : ℤ} (hx : (d : ℤ) ∣ x) :
    wInt n S S' d x = 0 := by
  unfold wInt
  exact wFun_of_dvd ((int_dvd_iff_val h.d_dvd_n x).mp hx)

lemma wInt_Rm (h : NormalizedSetting n S S' d e) {a : ℕ} (ha : a < n) (hda : d ∣ a) (x : ℤ) :
    wInt n S S' d (Rm (n - a) x : ℤ) = wInt n S S' d x := by
  have hW : 0 < n - a := by omega
  have := periodic_int_mul (fun y => wInt_add_W h ha hda y) (-(x / ((n - a : ℕ) : ℤ))) x
  rw [Rm_eq hW x]
  rw [← this]; congr 1; ring

end Setup



lemma wInt_natCast (m : ℕ) : wInt n S S' d (m : ℤ) = wFun n S S' d (m : ZMod n) := by
  simp [wInt]

lemma wInt_period_dvd [NeZero n] (h : NormalizedSetting n S S' d e) (t : ℤ)
    (ht : ∀ x : ℤ, wInt n S S' d (x + t) = wInt n S S' d x) : (e : ℤ) ∣ t := by
  have hmem : (t : ZMod n) ∈ periodGroup (wFun n S S' d) := by
    intro y
    have := ht (y.val : ℤ)
    unfold wInt at this
    simpa using this
  have := dvd_of_mem_periodGroup h.e_least hmem
  exact (int_dvd_iff_val h.e_dvd_n t).mpr this

lemma gDiff_neg {a m : ℕ} (ha : a ≤ n) (hm : m ≤ n - a) :
    gDiff n S a (n - a - m) = - gDiff n S a m := by
  unfold gDiff
  have h1 : ((n - a - m : ℕ) : ZMod n) = -((a : ZMod n) + (m : ZMod n)) := by
    rw [show n - a - m = n - (a + m) by omega, natCast_sub_eq_neg' (by omega)]; push_cast; ring
  have h2 : ((n - a - m + a : ℕ) : ZMod n) = -(m : ZMod n) := by
    rw [show n - a - m + a = n - m by omega, natCast_sub_eq_neg' (by omega)]
  have h3 : ((m + a : ℕ) : ZMod n) = (m : ZMod n) + (a : ZMod n) := by push_cast; ring
  rw [h1, h2, h3, tauFun_neg, tauFun_neg, add_comm (a : ZMod n)]
  ring

section Phi

variable {a : ℕ}

lemma phiInt_add_W (x : ℤ) : phiInt n S d a (x + ((n - a : ℕ) : ℤ)) = phiInt n S d a x := by
  unfold phiInt; rw [Rm_add_W]

lemma phiInt_Rm (ha : a < n) (x : ℤ) :
    phiInt n S d a (Rm (n - a) x : ℤ) = phiInt n S d a x := by
  have hW : 0 < n - a := by omega
  unfold phiInt
  rw [Rm_of_lt hW (Rm_lt hW x)]

lemma phiInt_of_lt {m : ℕ} (ha : a < n) (hm : m < n - a) (hd : ¬ d ∣ m) :
    phiInt n S d a (m : ℤ) = gDiff n S a m := by
  have hW : 0 < n - a := by omega
  unfold phiInt; rw [Rm_of_lt hW hm]; simp [hd]

lemma phiInt_of_dvd (h : NormalizedSetting n S S' d e) (ha : a < n) (hda : d ∣ a) {x : ℤ} (hx : (d : ℤ) ∣ x) :
    phiInt n S d a x = 0 := by
  have hW : 0 < n - a := by omega
  have hdW : d ∣ n - a := Nat.dvd_sub h.d_dvd_n hda
  unfold phiInt
  rw [if_pos ((Rm_dvd_iff hW hdW x).mp hx)]

lemma phiInt_neg (h : NormalizedSetting n S S' d e) (ha : a < n) (hda : d ∣ a) (x : ℤ) :
    phiInt n S d a (-x) = - phiInt n S d a x := by
  have hW : 0 < n - a := by omega
  have hdW : d ∣ n - a := Nat.dvd_sub h.d_dvd_n hda
  by_cases hX : Rm (n - a) x = 0
  · have h1 : phiInt n S d a x = 0 := by
      unfold phiInt; rw [hX]; simp
    have h2 : Rm (n - a) (-x) = 0 := by
      have := Rm_eq hW x
      rw [hX] at this
      simp only [Nat.cast_zero] at this
      apply Rm_eq_of_dvd hW hW
      exact ⟨x / ((n - a : ℕ) : ℤ) , by push_cast at this ⊢; linarith⟩
    have h3 : phiInt n S d a (-x) = 0 := by
      unfold phiInt; rw [h2]; simp
    rw [h1, h3]; ring
  · have hneg := Rm_neg hW hX
    have hlt := Rm_lt hW x
    by_cases hd : d ∣ Rm (n - a) x
    · have h1 : phiInt n S d a x = 0 := by unfold phiInt; rw [if_pos hd]
      have h2 : phiInt n S d a (-x) = 0 := by
        unfold phiInt; rw [hneg, if_pos (Nat.dvd_sub hdW hd)]
      rw [h1, h2]; ring
    · have hd2 : ¬ d ∣ n - a - Rm (n - a) x := fun hh => hd (by
        have := Nat.dvd_sub hdW hh
        rwa [Nat.sub_sub_self hlt.le] at this)
      unfold phiInt
      rw [hneg, if_neg hd, if_neg hd2, gDiff_neg ha.le hlt.le]


end Phi

/-- The cyclic sum of the balance equation for `(w, φ)`. -/
def cycI (w φ : ℤ → ℤ) (x y z : ℤ) : ℤ :=
  (w y + w z) * φ x + (w z + w x) * φ y + (w x + w y) * φ z

lemma gDiff_eq_two_mul (h : NormalizedSetting n S S' d e) [NeZero n] {a m : ℕ} (hm : m < n)
    (hda : d ∣ a) (hd : ¬ d ∣ m) (ha : a < n) :
    gDiff n S a m = 2 * (cutInd n S (m : ZMod n) - cutInd n S ((m : ZMod n) + (a : ZMod n))) := by
  have hdn := h.d_dvd_n
  have h1 : d ∣ (a : ZMod n).val := (nat_dvd_iff_val hdn a).mp hda
  have h2 : ¬ d ∣ (m : ZMod n).val := not_dvd_val_natCast hm hd
  have := tauFun_diff h h1 h2
  unfold gDiff
  rw [show ((m + a : ℕ) : ZMod n) = (m : ZMod n) + (a : ZMod n) by push_cast; ring]
  exact this

section Main

variable [NeZero n] {a : ℕ}

lemma wInt_mul_phiInt (h : NormalizedSetting n S S' d e) (ha : a < n) (hda : d ∣ a) (x : ℤ) :
    wInt n S S' d x * phiInt n S d a x = 0 := by
  have hW : 0 < n - a := by omega
  have hdW : d ∣ n - a := Nat.dvd_sub h.d_dvd_n hda
  by_cases hx : (d : ℤ) ∣ x
  · rw [phiInt_of_dvd h ha hda hx, mul_zero]
  · have hX : ¬ d ∣ Rm (n - a) x := fun hh => hx ((Rm_dvd_iff hW hdW x).mpr hh)
    have hXlt := Rm_lt hW x
    have e1 : phiInt n S d a x = gDiff n S a (Rm (n - a) x) := by
      rw [← phiInt_Rm ha x]
      exact phiInt_of_lt ha hXlt hX
    have e2 : wInt n S S' d x = wFun n S S' d ((Rm (n - a) x : ℕ) : ZMod n) := by
      rw [← wInt_Rm h ha hda x]; exact wInt_natCast _
    rw [e1, e2, gDiff_eq_two_mul h (by omega) hda hX ha]
    have := w_mul_diff h ((nat_dvd_iff_val h.d_dvd_n a).mp hda)
      (not_dvd_val_natCast (by omega : Rm (n - a) x < n) hX)
    rw [mul_left_comm, this, mul_zero]


/-- Four-block vanishing, in the circle coordinates: for `X, Y, Z ∈ (0, W)` off the `d`-grid with
`X + Y + Z = W`, the cyclic balance sum of `(w, φ_a)` vanishes. -/
lemma cycI_zero_of_sum (h : NormalizedSetting n S S' d e) (hz : FourBlockVanish n S S' d)
    (ha0 : 0 < a) (ha : a < n) (hva : vFun n S S' (a : ZMod n) ≠ 0) {X Y Z : ℕ}
    (hX0 : 0 < X) (hY0 : 0 < Y) (hZ0 : 0 < Z) (hXd : ¬ d ∣ X) (hYd : ¬ d ∣ Y) (hZd : ¬ d ∣ Z)
    (hsum : X + Y + Z = n - a) :
    cycI (wInt n S S' d) (phiInt n S d a) X Y Z = 0 := by
  have := cyc_zero h hz ha0 hX0 hY0 hZ0 hva hXd hYd hZd (by omega)
  have hX : phiInt n S d a (X : ℤ) = gDiff n S a X := phiInt_of_lt ha (by omega) hXd
  have hY : phiInt n S d a (Y : ℤ) = gDiff n S a Y := phiInt_of_lt ha (by omega) hYd
  have hZ : phiInt n S d a (Z : ℤ) = gDiff n S a Z := phiInt_of_lt ha (by omega) hZd
  unfold cycI
  rw [hX, hY, hZ, wInt_natCast, wInt_natCast, wInt_natCast]
  linarith


lemma cycI_neg (w φ : ℤ → ℤ) (hw : ∀ x, w (-x) = -w x) (hφ : ∀ x, φ (-x) = -φ x) (x y z : ℤ) :
    cycI w φ (-x) (-y) (-z) = cycI w φ x y z := by
  unfold cycI; rw [hw, hw, hw, hφ, hφ, hφ]; ring

/-- The balance equation for `(w, φ_a)`, in the cyclic form: `x + y + z ≡ 0 (mod W)`, none on the
`d`-grid. -/
lemma cycI_zero_int (h : NormalizedSetting n S S' d e) (hz : FourBlockVanish n S S' d)
    (ha0 : 0 < a) (ha : a < n) (hva : vFun n S S' (a : ZMod n) ≠ 0) (hda : d ∣ a) {x y z : ℤ}
    (hx : ¬ (d : ℤ) ∣ x) (hy : ¬ (d : ℤ) ∣ y) (hzz : ¬ (d : ℤ) ∣ z)
    (hs : ((n - a : ℕ) : ℤ) ∣ x + y + z) :
    cycI (wInt n S S' d) (phiInt n S d a) x y z = 0 := by
  have hW : 0 < n - a := by omega
  have hdW : d ∣ n - a := Nat.dvd_sub h.d_dvd_n hda
  set W := n - a with hWdef
  have hX : ¬ d ∣ Rm W x := fun hh => hx ((Rm_dvd_iff hW hdW x).mpr hh)
  have hY : ¬ d ∣ Rm W y := fun hh => hy ((Rm_dvd_iff hW hdW y).mpr hh)
  have hZ : ¬ d ∣ Rm W z := fun hh => hzz ((Rm_dvd_iff hW hdW z).mpr hh)
  have hX0 : 0 < Rm W x := Nat.pos_of_ne_zero fun h0 => hX (by rw [h0]; exact dvd_zero _)
  have hY0 : 0 < Rm W y := Nat.pos_of_ne_zero fun h0 => hY (by rw [h0]; exact dvd_zero _)
  have hZ0 : 0 < Rm W z := Nat.pos_of_ne_zero fun h0 => hZ (by rw [h0]; exact dvd_zero _)
  have hXl := Rm_lt hW x
  have hYl := Rm_lt hW y
  have hZl := Rm_lt hW z
  have hsum : (W : ℤ) ∣ (Rm W x : ℤ) + Rm W y + Rm W z := by
    rw [Rm_eq hW x, Rm_eq hW y, Rm_eq hW z]
    have : (x - W * (x / W)) + (y - W * (y / W)) + (z - W * (z / W)) =
        (x + y + z) - W * (x / W + y / W + z / W) := by ring
    rw [this]
    exact dvd_sub hs (dvd_mul_right _ _)
  have hw : ∀ u : ℤ, wInt n S S' d (Rm W u : ℤ) = wInt n S S' d u := wInt_Rm h ha hda
  have hφ : ∀ u : ℤ, phiInt n S d a (Rm W u : ℤ) = phiInt n S d a u := phiInt_Rm ha
  have key : ∀ X Y Z : ℕ, 0 < X → 0 < Y → 0 < Z → X < W → Y < W → Z < W → ¬ d ∣ X → ¬ d ∣ Y →
      ¬ d ∣ Z → X + Y + Z = W → cycI (wInt n S S' d) (phiInt n S d a) X Y Z = 0 :=
    fun X Y Z hX0 hY0 hZ0 _ _ _ hXd hYd hZd hs =>
      cycI_zero_of_sum h hz ha0 ha hva hX0 hY0 hZ0 hXd hYd hZd hs
  unfold cycI
  rw [← hw x, ← hw y, ← hw z, ← hφ x, ← hφ y, ← hφ z]
  rcases three_sum hX0 hXl hY0 hYl hZ0 hZl hsum with h1 | h2
  · have := key _ _ _ hX0 hY0 hZ0 hXl hYl hZl hX hY hZ h1
    unfold cycI at this
    exact this
  · -- negate
    have e1 : ((W - Rm W x : ℕ) : ℤ) = -(Rm W x : ℤ) + W := by omega
    have e2 : ((W - Rm W y : ℕ) : ℤ) = -(Rm W y : ℤ) + W := by omega
    have e3 : ((W - Rm W z : ℕ) : ℤ) = -(Rm W z : ℤ) + W := by omega
    have kk := key (W - Rm W x) (W - Rm W y) (W - Rm W z) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
      (fun hh => hX (by
        have := Nat.dvd_sub hdW hh
        rwa [Nat.sub_sub_self hXl.le] at this))
      (fun hh => hY (by
        have := Nat.dvd_sub hdW hh
        rwa [Nat.sub_sub_self hYl.le] at this))
      (fun hh => hZ (by
        have := Nat.dvd_sub hdW hh
        rwa [Nat.sub_sub_self hZl.le] at this))
      (by omega)
    unfold cycI at kk
    rw [e1, e2, e3] at kk
    rw [wInt_add_W h ha hda, wInt_add_W h ha hda, wInt_add_W h ha hda,
      phiInt_add_W, phiInt_add_W, phiInt_add_W,
      wInt_neg h, wInt_neg h, wInt_neg h, phiInt_neg h ha hda, phiInt_neg h ha hda,
      phiInt_neg h ha hda] at kk
    linarith


/-- The balance equation `eq:FE` for `(w, φ_a)` on the circle `ℤ/W`, as `W`-periodic functions
on `ℤ` (the case analysis of the paper's proof of `lem:four-start`). -/
lemma fe_phi (h : NormalizedSetting n S S' d e) (hz : FourBlockVanish n S S' d)
    (ha0 : 0 < a) (ha : a < n) (hva : vFun n S S' (a : ZMod n) ≠ 0) (hda : d ∣ a) (x y : ℤ) :
    wInt n S S' d x * phiInt n S d a y + phiInt n S d a x * wInt n S S' d y =
      wInt n S S' d (x + y) * (phiInt n S d a x + phiInt n S d a y) +
        phiInt n S d a (x + y) * (wInt n S S' d x + wInt n S S' d y) := by
  refine fe_of_offgrid (g := d) (wInt_neg h) (fun x y hx => wInt_shift_d h hx y)
    (fun x hx => phiInt_of_dvd h ha hda hx) (wInt_mul_phiInt h ha hda) ?_ x y
  intro x y hx hy hxy
  have := cycI_zero_int h hz ha0 ha hva hda hx hy (z := -(x + y))
    (fun hh => hxy ((dvd_neg).mp hh)) (by simp)
  unfold cycI at this
  rw [wInt_neg h, phiInt_neg h ha hda] at this
  linarith

/-- `lem:fiber` applied to `(w, φ_a)`: `φ_a(t + e) = φ_a(t)` for `e ∤ t`. -/
lemma phi_period (h : NormalizedSetting n S S' d e) (hz : FourBlockVanish n S S' d)
    (ha0 : 0 < a) (ha : a < n) (hva : vFun n S S' (a : ZMod n) ≠ 0) (hda : d ∣ a) {t : ℤ}
    (ht : ¬ (e : ℤ) ∣ t) : phiInt n S d a (t + e) = phiInt n S d a t :=
  fiber_period_int (W := n - a) (e := e) (by omega) (wInt_add_W h ha hda) (wInt_neg h)
    (wInt_add_e h) (fun t ht => wInt_period_dvd h t ht) (wInt_mul_phiInt h ha hda)
    (fe_phi h hz ha0 ha hva hda) ht

end Main

end Periodic



section Orbit

variable {n : ℕ} {S S' : Finset ℕ} {d e : ℕ}

/-- `w(x) ≠ 0` forces `τ(x) = 1`, and `w(x) = 0` off the `d`-grid forces `τ(x) ∈ {0, 2}`. -/
lemma tau_of_w_ne [NeZero n] (h : NormalizedSetting n S S' d e) {x : ZMod n} (hx : ¬ d ∣ x.val)
    (hw : wFun n S S' d x ≠ 0) : tauFun n S x = 1 := by
  have := h.wFun_eq_off hx
  unfold tauFun
  have c1 := cutInd_cases n S x
  have c2 := cutInd_cases n S (-x)
  omega

lemma tau_of_w_eq [NeZero n] (h : NormalizedSetting n S S' d e) {x : ZMod n} (hx : ¬ d ∣ x.val)
    (hw : wFun n S S' d x = 0) : tauFun n S x = 0 ∨ tauFun n S x = 2 := by
  have := h.wFun_eq_off hx
  unfold tauFun
  have c1 := cutInd_cases n S x
  have c2 := cutInd_cases n S (-x)
  omega

variable [NeZero n]

/-- The constancy of `φ_a` along an `e`-progression: `lem:fiber` applied to `(w, φ_a)`. -/
lemma gDiff_const (h : NormalizedSetting n S S' d e) (hz : FourBlockVanish n S S' d) {a : ℕ}
    (ha0 : 0 < a) (ha : a < n) (hva : vFun n S S' (a : ZMod n) ≠ 0) {r : ℕ} (hr0 : 0 < r)
    (hre : r < e) (hrW : r < n - a) {j : ℕ} (hj : r + j * e < n - a) :
    gDiff n S a (r + j * e) = gDiff n S a r := by
  have hda : d ∣ a := (nat_dvd_iff_val h.d_dvd_n a).mpr (h.dvd_of_v_ne hva)
  have hne : ¬ e ∣ r := fun hh => by have := Nat.le_of_dvd hr0 hh; omega
  have hned : ∀ m, ¬ e ∣ m → ¬ d ∣ m := fun m hm hd => hm (h.e_dvd_d.trans hd)
  have hper : ∀ t : ℤ, ¬ (e : ℤ) ∣ t → phiInt n S d a (t + e) = phiInt n S d a t :=
    fun t ht => phi_period h hz ha0 ha hva hda ht
  have h1 := fiber_shift_int hper (t := (r : ℤ)) (by exact_mod_cast hne) (j : ℤ)
  have e1 : phiInt n S d a ((r : ℤ) + (j : ℤ) * e) = gDiff n S a (r + j * e) := by
    have := phiInt_of_lt (S := S) (d := d) ha hj
      (hned _ (fun hh => hne (by
        have : e ∣ r + j * e := hh
        exact (Nat.dvd_add_left (dvd_mul_left e j)).mp this)))
    simpa using this
  have e2 : phiInt n S d a (r : ℤ) = gDiff n S a r := phiInt_of_lt ha hrW (hned _ hne)
  rw [← e1, ← e2]; exact h1


lemma wFun_natCast_add_mul (h : NormalizedSetting n S S' d e) (r j : ℕ) :
    wFun n S S' d ((r + j * e : ℕ) : ZMod n) = wFun n S S' d (r : ZMod n) := by
  have := periodic_int_mul (fun y => wInt_add_e h y) (j : ℤ) (r : ℤ)
  have h2 : (((r : ℤ) + (j : ℤ) * (e : ℤ) : ℤ)) = ((r + j * e : ℕ) : ℤ) := by push_cast; ring
  rw [h2] at this
  rw [← wInt_natCast, ← wInt_natCast]; exact this

/-- One-sided finite-orbit consequence of `lem:four-start`: if `0 < a`, `2 a < n`, `a` represents
an element of `supp v`, then `τ(x + a) = τ(x)` off the `e`-grid. -/
theorem tau_shift_small (h : NormalizedSetting n S S' d e) (hz : FourBlockVanish n S S' d)
    {a : ℕ} (ha0 : 0 < a) (ha2 : 2 * a < n) (hva : vFun n S S' (a : ZMod n) ≠ 0)
    {x : ZMod n} (hx : ¬ e ∣ x.val) :
    tauFun n S (x + (a : ZMod n)) = tauFun n S x := by
  have ha : a < n := by omega
  have hda : d ∣ a := (nat_dvd_iff_val h.d_dvd_n a).mpr (h.dvd_of_v_ne hva)
  have hea : e ∣ a := h.e_dvd_d.trans hda
  have hne : e ∣ n := h.e_dvd_n
  have he0 := h.e_pos
  obtain ⟨M, hM⟩ := hne
  obtain ⟨t, ht⟩ := hea
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0] at ht; omega
    · exact h0
  have hMt : 2 * t < M := by
    have : e * (2 * t) < e * M := by nlinarith
    exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
  have hMt' : t < M := by omega
  -- the opposite support point
  have hva' : vFun n S S' ((n - a : ℕ) : ZMod n) ≠ 0 := by
    rw [natCast_sub_eq_neg' ha.le, h.v_neg]; simpa using hva
  have hda' : d ∣ n - a := Nat.dvd_sub h.d_dvd_n hda
  have hn : n - a = e * (M - t) := by
    rw [Nat.mul_sub, ← hM, ← ht]
  set m := x.val with hm
  have hmn : m < n := ZMod.val_lt x
  set r := m % e with hr
  set j := m / e with hj
  have hmrj : m = r + j * e := by rw [hr, hj]; have := Nat.mod_add_div m e; linarith [mul_comm e (m / e)]
  have hr0 : 0 < r := Nat.pos_of_ne_zero fun h0 => hx (Nat.dvd_of_mod_eq_zero h0)
  have hre : r < e := Nat.mod_lt _ he0
  have hjM : j < M := by
    by_contra hge
    replace hge := le_of_not_gt hge
    have : e * M ≤ e * j := Nat.mul_le_mul_left _ hge
    nlinarith
  set T : ℕ → ℤ := fun i => tauFun n S ((r + i * e : ℕ) : ZMod n) with hT
  have hTper : ∀ i, T (i + M) = T i := by
    intro i
    simp only [hT]
    congr 1
    have : r + (i + M) * e = (r + i * e) + n := by rw [hM]; ring
    rw [this]; push_cast; rw [ZMod.natCast_self, add_zero]
  have hoff : ∀ i, ¬ d ∣ r + i * e := fun i hd => by
    have := h.e_dvd_d.trans hd
    have h2 : e ∣ r := (Nat.dvd_add_left (dvd_mul_left e i)).mp this
    have := Nat.le_of_dvd hr0 h2; omega
  have hoff' : ∀ i, ¬ d ∣ ((r + i * e : ℕ) : ZMod n).val := by
    intro i hdv
    exact hoff i ((nat_dvd_iff_val h.d_dvd_n _).mpr hdv)
  have hcase : (∀ i, T i = 1) ∨ (∀ i, T i = 0 ∨ T i = 2) := by
    by_cases hw : wFun n S S' d (r : ZMod n) = 0
    · right; intro i
      exact tau_of_w_eq h (hoff' i) (by rw [wFun_natCast_add_mul h]; exact hw)
    · left; intro i
      exact tau_of_w_ne h (hoff' i) (by rw [wFun_natCast_add_mul h]; exact hw)
  have hr1 : r + 0 * e = r := by ring
  -- constancy for the shifts a and n - a
  have c1 : ∀ i, i < M - t → T i - T (i + t) = gDiff n S a r := by
    intro i hi
    have hlt : r + i * e < n - a := by
      rw [hn]; nlinarith
    have := gDiff_const h hz ha0 ha hva hr0 hre (by rw [hn]; nlinarith) hlt
    have e1 : gDiff n S a (r + i * e) = T i - T (i + t) := by
      simp only [gDiff, hT]
      congr 3
      rw [ht]; ring
    rw [← e1, this]
  have c2 : ∀ i, i < t → T i - T (i + (M - t)) = gDiff n S (n - a) r := by
    intro i hi
    have hlt : r + i * e < n - (n - a) := by
      rw [Nat.sub_sub_self ha.le, ht]; nlinarith
    have := gDiff_const h hz (by omega) (by omega) hva' hr0 hre
      (by rw [Nat.sub_sub_self ha.le, ht]; nlinarith) hlt
    have e1 : gDiff n S (n - a) (r + i * e) = T i - T (i + (M - t)) := by
      simp only [gDiff, hT]
      congr 3
      rw [hn]; ring
    rw [← e1, this]
  have := shift_invariance T M t ht0 hMt hTper hcase _ _ c1 c2 j hjM
  simp only [hT] at this
  have e3 : ((r + (j + t) * e : ℕ) : ZMod n) = x + (a : ZMod n) := by
    have : r + (j + t) * e = m + a := by rw [hmrj, ht]; ring
    rw [this]; push_cast; rw [hm, ZMod.natCast_zmod_val]
  have e4 : ((r + j * e : ℕ) : ZMod n) = x := by
    rw [← hmrj, hm, ZMod.natCast_zmod_val]
  rw [e3, e4] at this
  exact this


/-- `τ` with the `e`-grid zeroed. -/
def tauMask (n : ℕ) (S : Finset ℕ) (e : ℕ) (x : ZMod n) : ℤ :=
  if e ∣ x.val then 0 else tauFun n S x

lemma gcd_mem_periodGroup {f : ZMod n → ℤ} {a b : ℕ} (ha : ((a : ℕ) : ZMod n) ∈ periodGroup f)
    (hb : ((b : ℕ) : ZMod n) ∈ periodGroup f) : ((Nat.gcd a b : ℕ) : ZMod n) ∈ periodGroup f := by
  have h1 : ((Nat.gcd a b : ℕ) : ZMod n) = (Nat.gcdA a b) • ((a : ℕ) : ZMod n) +
      (Nat.gcdB a b) • ((b : ℕ) : ZMod n) := by
    have := Nat.gcd_eq_gcd_ab a b
    have h2 := congrArg (fun z : ℤ => (z : ZMod n)) this
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at h2
    simp only [zsmul_eq_mul]
    push_cast at h2 ⊢
    linear_combination h2
  rw [h1]
  exact add_mem (zsmul_mem ha _) (zsmul_mem hb _)

lemma finset_gcd_mem_periodGroup {f : ZMod n → ℤ} (s : Finset ℕ)
    (hs : ∀ k ∈ s, ((k : ℕ) : ZMod n) ∈ periodGroup f) :
    ((s.gcd id : ℕ) : ZMod n) ∈ periodGroup f := by
  classical
  induction s using Finset.induction with
  | empty => simpa using zero_mem _
  | insert k s hk ih =>
    rw [Finset.gcd_insert]
    exact gcd_mem_periodGroup (hs k (Finset.mem_insert_self _ _))
      (ih fun k' hk' => hs k' (Finset.mem_insert_of_mem hk'))

/-- `lem:four-start`, last assertion: if every four-block difference vanishes, the mask
`𝓑_e` is `d`-periodic. -/
theorem mask_periodic_of_four_vanish (h : NormalizedSetting n S S' d e)
    (hz : FourBlockVanish n S S' d) : IsPeriod (maskFun n S e) d := by
  have hdn := h.d_dvd_n
  have hen := h.e_dvd_n
  -- shifts by elements of the support preserve `tauMask`
  have hsupp : ∀ k ∈ (Finset.range n).filter (fun k : ℕ => vFun n S S' (k : ZMod n) ≠ 0),
      ((k : ℕ) : ZMod n) ∈ periodGroup (tauMask n S e) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkn, hvk⟩ := hk
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        exfalso
        have h00 : vFun n S S' 0 = 0 := by
          have := h.v_neg 0
          rw [neg_zero] at this
          omega
        rw [Nat.cast_zero] at hvk
        exact hvk h00
      · exact h0
    have hdk : d ∣ k := (nat_dvd_iff_val hdn k).mpr (h.dvd_of_v_ne hvk)
    have hek : e ∣ k := h.e_dvd_d.trans hdk
    have hne : 2 * k ≠ n := by
      intro h2
      apply hvk
      have h3 : ((k : ℕ) : ZMod n) = -((k : ℕ) : ZMod n) := by
        have : (((k + k : ℕ)) : ZMod n) = 0 := by
          rw [show k + k = n by omega, ZMod.natCast_self]
        push_cast at this
        linear_combination this
      have := h.v_neg ((k : ℕ) : ZMod n)
      rw [← h3] at this
      omega
    -- tauMask preserved by shift by `a` when `2a < n`
    have key : ∀ a : ℕ, 0 < a → 2 * a < n → vFun n S S' (a : ZMod n) ≠ 0 →
        ∀ x : ZMod n, tauMask n S e (x + (a : ZMod n)) = tauMask n S e x := by
      intro a ha0 ha2 hva x
      have hea : e ∣ a := h.e_dvd_d.trans ((nat_dvd_iff_val hdn a).mpr (h.dvd_of_v_ne hva))
      have hea' : e ∣ (a : ZMod n).val := (nat_dvd_iff_val hen a).mp hea
      unfold tauMask
      by_cases hx : e ∣ x.val
      · rw [if_pos hx, if_pos ((dvd_val_add hen hea').mpr hx)]
      · rw [if_neg hx, if_neg (fun hh => hx ((dvd_val_add hen hea').mp hh))]
        exact tau_shift_small h hz ha0 ha2 hva hx
    intro x
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact key k hk0 hlt hvk x
    · have ha' : n - k < n := by omega
      have hva' : vFun n S S' ((n - k : ℕ) : ZMod n) ≠ 0 := by
        rw [natCast_sub_eq_neg' hkn.le, h.v_neg]; simpa using hvk
      have := key (n - k) (by omega) (by omega) hva' (x + (k : ZMod n))
      rw [natCast_sub_eq_neg' hkn.le] at this
      rw [show x + (k : ZMod n) + -(k : ZMod n) = x by ring] at this
      exact this.symm
  have hG := finset_gcd_mem_periodGroup _ hsupp
  have hn0 : (((n : ℕ)) : ZMod n) ∈ periodGroup (tauMask n S e) := by
    rw [ZMod.natCast_self]; exact zero_mem _
  have hd := gcd_mem_periodGroup hn0 hG
  have hdeq : d = Nat.gcd n (((Finset.range n).filter
      (fun k : ℕ => vFun n S S' (k : ZMod n) ≠ 0)).gcd id) := h.d_eq
  rw [← hdeq] at hd
  -- conclude for the mask
  intro x
  by_cases hx : e ∣ x.val
  · have hed : e ∣ ((d : ℕ) : ZMod n).val := (nat_dvd_iff_val hen d).mp h.e_dvd_d
    rw [maskFun_of_dvd hx, maskFun_of_dvd ((dvd_val_add hen hed).mpr hx)]
  · have hed : e ∣ ((d : ℕ) : ZMod n).val := (nat_dvd_iff_val hen d).mp h.e_dvd_d
    have hx' : ¬ e ∣ (x + (d : ZMod n)).val := fun hh => hx ((dvd_val_add hen hed).mp hh)
    rw [maskFun_of_not_dvd hx', maskFun_of_not_dvd hx]
    have hxd : ¬ d ∣ x.val := fun hh => hx (h.e_dvd_d.trans hh)
    have hxd' : ¬ d ∣ (x + (d : ZMod n)).val := fun hh => hxd (by
      have hdd : d ∣ ((d : ℕ) : ZMod n).val := (nat_dvd_iff_val hdn d).mp dvd_rfl
      exact (dvd_val_add hdn hdd).mp hh)
    have t1 := hd x
    unfold tauMask at t1
    rw [if_neg hx', if_neg hx] at t1
    have w1 := h.w_period x
    have e1 := h.wFun_eq_off hxd
    have e2 := h.wFun_eq_off hxd'
    unfold tauFun at t1
    -- b(x) = (τ(x) + w(x)) / 2
    have hb1 : 2 * cutInd n S x = (cutInd n S x + cutInd n S (-x)) + wFun n S S' d x := by
      rw [e1]; ring
    have hb2 : 2 * cutInd n S (x + (d : ZMod n)) =
        (cutInd n S (x + (d : ZMod n)) + cutInd n S (-(x + (d : ZMod n)))) +
          wFun n S S' d (x + (d : ZMod n)) := by
      rw [e2]; ring
    omega

end Orbit

end SkewRibbonCoarsenings
