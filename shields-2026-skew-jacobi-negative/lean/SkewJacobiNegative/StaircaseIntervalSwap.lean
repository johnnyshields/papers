/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseQuarticAlgebra

/-!
# Last-row exchange at an isolated interval contact

The interval-contact swap step in `thm:staircase-residual-matching`.
The exact defect is a coordinate-times-binomial difference.
-/

namespace SkewJacobiNegative.Staircase
open HessenbergExpansion

/-- The last-row exchange defect is a coordinate-times-binomial difference. -/
theorem fourInterval_last_swap_defect {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d r s t : ℤ) :
    fourInterval h a b c d r s t-fourInterval h a b d c r s t =
      h s*(h d*(h r*h (a+b+c-r-s)-h a*h (b+c-s))-
        h c*(h r*h (a+b+d-r-s)-h a*h (b+d-s))) := by
  unfold fourInterval
  rw [show d+c-t=c+d-t by ring,
    show b+d+c-s-t=b+c+d-s-t by ring,
    show a+b+d+c-r-s-t=a+b+c+d-r-s-t by ring]
  ring

private theorem interval_psi_eq_B (q : ℕ+) (a b r s t k : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (ha : r < a)
    (hb : r+s < b) (hk : q.val+t < k) (hu : a+b-r=q.val) :
    bar q r*bar q (a+b+k-r-s)-bar q a*bar q (b+k-s) =
      quadraticB r a (b+k-s) := by
  have hR := bar_eq_complete_of_ne q r (by omega)
  have hA := bar_eq_complete_of_ne q a (by omega)
  have hV := bar_eq_complete_of_ne q (b+k-s) (by omega)
  have hX := bar_eq_complete_of_ne q (a+b+k-r-s) (by omega)
  rw [hR,hA,hV,hX]
  rw [show a+b+k-r-s=a+(b+k-s)-r by ring]
  rfl

/-- Once an isolated first merged interval is fixed, its last two rows cannot
be exchanged by equality of the actual specialized four-row polynomials.

**Differs from the paper's route.** The classified quadratic factors recover
the last row directly; the paper reads the private largest defect generator. -/
theorem interval_last_swap_key (q : ℕ+) (a b c d r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (ha : r < a)
    (hb : r+s < b) (hc : q.val+t < c) (hd : q.val+t < d)
    (hu : a+b-r=q.val)
    (he : fourInterval (bar q) a b c d r s t=fourInterval (bar q) a b d c r s t) :
    c=d := by
  have hz := sub_eq_zero.mpr he
  rw [fourInterval_last_swap_defect,
    bar_eq_complete_of_ne q s (by omega),
    bar_eq_complete_of_ne q d (by omega),bar_eq_complete_of_ne q c (by omega),
    interval_psi_eq_B q a b r s t c hr hs ht ha hb hc hu,
    interval_psi_eq_B q a b r s t d hr hs ht ha hb hd hu] at hz
  have hsne : complete s ≠ 0 := (complete_ne_zero_iff s).mpr hs.le
  have hprod : complete d*quadraticB r a (b+c-s)=complete c*quadraticB r a (b+d-s) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hsne)
  have hread := variable_times_B_reading d r a (b+c-s) c r a (b+d-s)
    (by omega) (by omega) hr ha (by omega) hr ha (by omega) hprod
  exact hread.1.symm

end SkewJacobiNegative.Staircase
