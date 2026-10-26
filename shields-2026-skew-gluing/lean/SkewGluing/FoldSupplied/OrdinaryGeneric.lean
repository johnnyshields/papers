import SkewGluing.FoldSupplied.OrdinaryBlock

/-!
# The generic bits of the inner

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`): off the exceptional residues `τ = t mod g`, `σ = s mod g`, both
boundary words of the inner at every position `1 ≤ x < r + v` repeat the completed native word of
the residue `x mod g` (`OrdCtx.generic_A`, `OrdCtx.generic_B`).  Positions of the upper band read
the lower band through the copy relation, and position `r` reads the cap one of the native column
word.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open OrdinaryDrift

variable {A B : ℕ → ℤ} {r v s t g : ℕ}

namespace OrdCtx

theorem generic_A (c : OrdCtx A B r v s t g) {x : ℕ} (hx1 : 1 ≤ x) (hxN : x < r + v)
    (hx : x % g ≠ t % g) : A x = natC A (x % g) := by
  have hg := c.g_pos
  have hrg := c.rmod
  have hgr : g ≤ r := Nat.le_of_dvd (by have := c.h.v_lt; have := c.h.v_pos; omega) c.gr
  have hvr := c.h.v_lt
  have key : ∀ y, 1 ≤ y → y < r → y % g ≠ t % g → A y = natC A (y % g) := by
    intro y hy1 hyr hyg
    have hmod : y % g % g = y % g := Nat.mod_mod _ _
    have hyl : y % g < r := lt_of_lt_of_le (Nat.mod_lt _ hg) hgr
    have e1 := c.hC y (y % g) hyr hyl hmod.symm hyg
    rw [← e1, c.h.A_native hy1]
  by_cases hxr : x < r
  · exact key x hx1 hxr hx
  · by_cases hb0 : x = r
    · subst hb0
      rw [c.h.A_r, hrg]
      have ht1 : 1 ≤ t := by
        by_contra hcon
        have : t = 0 := by omega
        apply hx; rw [hrg, this]; simp
      simp only [ht1, if_true]
      unfold natC; simp
    · have hb1 : 1 ≤ x - r := by omega
      have hbv : x - r < v := by omega
      have hbr : x - r < r := by omega
      have hmx : (x - r) % g = x % g := by
        have : x = r + (x - r) := by omega
        conv_rhs => rw [this, Nat.add_mod, hrg]
        simp
      have hbt : x - r ≠ t := fun hh => hx (by rw [← hmx, hh])
      have c1 := c.h.copyA (x - r) hb1 hbv
      simp only [hbt, if_false, sub_zero] at c1
      have e : r + (x - r) = x := by omega
      rw [e] at c1
      rw [c1, key (x - r) hb1 hbr (by rw [hmx]; exact hx), hmx]

theorem generic_B (c : OrdCtx A B r v s t g) {x : ℕ} (hx1 : 1 ≤ x) (hxN : x < r + v)
    (hx : x % g ≠ s % g) : B x = natB B s (x % g) := by
  have hg := c.g_pos
  have hrg := c.rmod
  have hgr : g ≤ r := Nat.le_of_dvd (by have := c.h.v_lt; have := c.h.v_pos; omega) c.gr
  have hvr := c.h.v_lt
  have key : ∀ y, 1 ≤ y → y < r → y % g ≠ s % g → B y = natB B s (y % g) := by
    intro y hy1 hyr hyg
    have hmod : y % g % g = y % g := Nat.mod_mod _ _
    have hyl : y % g < r := lt_of_lt_of_le (Nat.mod_lt _ hg) hgr
    have e1 := c.hB y (y % g) hyr hyl hmod.symm hyg
    have hys : y ≠ s := fun hh => hyg (by rw [hh])
    have := c.h.B_native (i := y) hy1
    simp only [hys, if_false, add_zero] at this
    rw [← e1, this]
  by_cases hxr : x < r
  · exact key x hx1 hxr hx
  · by_cases hb0 : x = r
    · subst hb0
      rw [c.h.B_r, hrg]
      unfold natB; simp
    · have hb1 : 1 ≤ x - r := by omega
      have hbv : x - r < v := by omega
      have hbr : x - r < r := by omega
      have hmx : (x - r) % g = x % g := by
        have : x = r + (x - r) := by omega
        conv_rhs => rw [this, Nat.add_mod, hrg]
        simp
      have hbs : x - r ≠ s := fun hh => hx (by rw [← hmx, hh])
      have c1 := c.h.copyB (x - r) hb1 hbv
      simp only [hbs, if_false, add_zero] at c1
      have e : r + (x - r) = x := by omega
      rw [e] at c1
      rw [c1, key (x - r) hb1 hbr (by rw [hmx]; exact hx), hmx]

end OrdCtx

end FoldSupplied
end SkewGluing
