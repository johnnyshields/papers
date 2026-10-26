import SkewGluing.OlsonHarris.Plan.CornerCase.Crem.ArithRight

/-!
# Integer arithmetic of the remainder after removing a lifted left ribbon

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`), the cell identity for a ribbon removable on the left.

Pure statements about integers: the row-interval clauses `cellForm` of a composite on the
diagonal `J q + a`, in terms of the data of the outer on the diagonals `J - 1` and `J`
(`lJ`, `hJ`, `lJ1`, `hJ1` are the first and last rows; `cJ`, `cJ1` the membership of the two
diagonals; `wJ`, `wJ1` their membership in the window of the ribbon; `zJ`, `zJ1` that the
diagonal has a single cell; `bt` that `lJ + 1 = lJ1`).  Here the cells of the window are the
first cells of the diagonals.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

namespace Rem


set_option hygiene false in
/-- Case analysis on the seven atoms, then linear arithmetic. -/
macro "arith_split_left" : tactic => `(tactic| (
  unfold cellFormP
  rcases em cJ with hc | hc <;> rcases em cJ1 with hc1 | hc1 <;>
  rcases em wJ with hw | hw <;> rcases em wJ1 with hw1 | hw1 <;>
  rcases em zJ with hz | hz <;> rcases em zJ1 with hz1 | hz1 <;>
  rcases em bt with hb | hb <;>
  · have e1 := hc; have e2 := hc1; have e3 := hw; have e4 := hw1; have e5 := hz
    have e6 := hz1; have e7 := hb
    rw [hcJ] at e1; rw [hcJ1] at e2; rw [hwJ] at e3; rw [hwJ1] at e4; rw [hzJ] at e5
    rw [hzJ1] at e6; rw [hbt] at e7
    simp only [hc, hc1, hw, hw1, hz, hz1, hb, true_and, and_true, true_or, or_true, false_and,
      and_false, false_or, or_false, not_true_eq_false, not_false_eq_true, and_self, or_self]
    all_goals (try simp only [hw, hw1, true_and, false_and, false_or, or_false,
      not_true_eq_false, not_false_eq_true] at heJ heJ1)
    all_goals omega))

set_option maxHeartbeats 4000000 in
-- the case analysis on seven atoms produces 128 omega calls
/-- Row clauses on the diagonal `J q + a`, left ribbon, regime a < t (`dH = 1`,
`[s ≤ a] = 0`, `[t ≤ a] = 0`). -/
theorem left_arith_a (w a loa hia ρ J j0 m mD MD lJ hJ lJ1 hJ1 : ℤ)
    (eJ eJ1 : ℤ) (cJ cJ1 wJ wJ1 zJ zJ1 bt : Prop)
    (heJ : (wJ ∧ eJ = 1) ∨ (¬ wJ ∧ eJ = 0)) (heJ1 : (wJ1 ∧ eJ1 = 1) ∨ (¬ wJ1 ∧ eJ1 = 0))
    (hcJ : cJ ↔ (mD ≤ J ∧ J ≤ MD)) (hcJ1 : cJ1 ↔ (mD ≤ J - 1 ∧ J - 1 ≤ MD))
    (hwJ : wJ ↔ (j0 ≤ J ∧ J < j0 + m)) (hwJ1 : wJ1 ↔ (j0 ≤ J - 1 ∧ J - 1 < j0 + m))
    (hzJ : zJ ↔ lJ = hJ) (hzJ1 : zJ1 ↔ lJ1 = hJ1) (hbt : bt ↔ lJ + 1 = lJ1)
    (hwa : a < w) (hWb : loa ≤ hia - 0)
    (hm : 1 ≤ m) (hw0 : mD ≤ j0) (hw1 : j0 + m - 1 ≤ MD)
    (_hhJ : mD ≤ J → J ≤ MD → lJ ≤ hJ) (hhJ1 : mD ≤ J - 1 → J - 1 ≤ MD → lJ1 ≤ hJ1)
    (hbitl : mD ≤ J - 1 → J ≤ MD → 0 ≤ lJ1 - lJ ∧ lJ1 - lJ ≤ 1)
    (hbith : mD ≤ J - 1 → J ≤ MD → 0 ≤ hJ1 - hJ ∧ hJ1 - hJ ≤ 1)
    (hend : (J = mD ∨ J = MD) → mD ≤ J → J ≤ MD → lJ = hJ)
    (hend1 : (J - 1 = mD ∨ J - 1 = MD) → mD ≤ J - 1 → J - 1 ≤ MD → lJ1 = hJ1)
    (hS : J = j0 → ¬ (mD ≤ J - 1 ∧ J - 1 ≤ MD) ∨ lJ1 - lJ = 1)
    (hT : J = j0 + m → ¬ (mD ≤ J ∧ J ≤ MD) ∨ lJ = lJ1) :
    (cellFormP w a loa hia ρ 1 0 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
      ¬ (cellFormP w a loa hia ρ 1 0 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
        ¬ cellFormP w a loa hia (ρ + 1) 1 0 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
        wJ1))
    ↔
    (cellFormP w a loa hia ρ 1 0 (cJ ∧ ¬ (wJ ∧ zJ)) (cJ1 ∧ ¬ (wJ1 ∧ zJ1))
        (hJ - lJ + 1 - eJ) (hJ1 - lJ1 + 1 - eJ1) (lJ + eJ + 1 = lJ1 + eJ1) ∨
     (wJ ∧ zJ ∧ w ≤ a ∧ loa ≤ ρ ∧ ρ + 1 ≤ hia) ∨
     ((wJ1 ∧ zJ1 ∧ ¬ (cJ ∧ lJ ≤ lJ1 ∧ lJ1 ≤ hJ)) ∧ a < w ∧ loa ≤ ρ ∧ ρ ≤ hia - 0) ∨
     ((wJ ∧ zJ ∧ ¬ (cJ1 ∧ lJ1 ≤ lJ + 1 ∧ lJ + 1 ≤ hJ1)) ∧ a < w ∧ loa ≤ ρ ∧
        ρ ≤ hia - 0)) := by
  arith_split_left

set_option maxHeartbeats 4000000 in
-- the case analysis on seven atoms produces 128 omega calls
/-- Row clauses on the diagonal `J q + a`, left ribbon, regime t ≤ a < s (`dH = 0`,
`[s ≤ a] = 0`, `[t ≤ a] = 1`). -/
theorem left_arith_b (w a loa hia ρ J j0 m mD MD lJ hJ lJ1 hJ1 : ℤ)
    (eJ eJ1 : ℤ) (cJ cJ1 wJ wJ1 zJ zJ1 bt : Prop)
    (heJ : (wJ ∧ eJ = 1) ∨ (¬ wJ ∧ eJ = 0)) (heJ1 : (wJ1 ∧ eJ1 = 1) ∨ (¬ wJ1 ∧ eJ1 = 0))
    (hcJ : cJ ↔ (mD ≤ J ∧ J ≤ MD)) (hcJ1 : cJ1 ↔ (mD ≤ J - 1 ∧ J - 1 ≤ MD))
    (hwJ : wJ ↔ (j0 ≤ J ∧ J < j0 + m)) (hwJ1 : wJ1 ↔ (j0 ≤ J - 1 ∧ J - 1 < j0 + m))
    (hzJ : zJ ↔ lJ = hJ) (hzJ1 : zJ1 ↔ lJ1 = hJ1) (hbt : bt ↔ lJ + 1 = lJ1)
    (hwa : a < w) (hWb : loa ≤ hia - 0)
    (hm : 1 ≤ m) (hw0 : mD ≤ j0) (hw1 : j0 + m - 1 ≤ MD)
    (hhJ : mD ≤ J → J ≤ MD → lJ ≤ hJ) (hhJ1 : mD ≤ J - 1 → J - 1 ≤ MD → lJ1 ≤ hJ1)
    (hbitl : mD ≤ J - 1 → J ≤ MD → 0 ≤ lJ1 - lJ ∧ lJ1 - lJ ≤ 1)
    (hbith : mD ≤ J - 1 → J ≤ MD → 0 ≤ hJ1 - hJ ∧ hJ1 - hJ ≤ 1)
    (hend : (J = mD ∨ J = MD) → mD ≤ J → J ≤ MD → lJ = hJ)
    (hend1 : (J - 1 = mD ∨ J - 1 = MD) → mD ≤ J - 1 → J - 1 ≤ MD → lJ1 = hJ1)
    (hS : J = j0 → ¬ (mD ≤ J - 1 ∧ J - 1 ≤ MD) ∨ lJ1 - lJ = 1)
    (hT : J = j0 + m → ¬ (mD ≤ J ∧ J ≤ MD) ∨ lJ = lJ1) :
    (cellFormP w a loa hia ρ 0 0 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
      ¬ (cellFormP w a loa hia ρ 0 0 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
        ¬ cellFormP w a loa hia (ρ + 1) 0 0 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
        wJ))
    ↔
    (cellFormP w a loa hia ρ 0 0 (cJ ∧ ¬ (wJ ∧ zJ)) (cJ1 ∧ ¬ (wJ1 ∧ zJ1))
        (hJ - lJ + 1 - eJ) (hJ1 - lJ1 + 1 - eJ1) (lJ + eJ + 1 = lJ1 + eJ1) ∨
     (wJ ∧ zJ ∧ w ≤ a ∧ loa ≤ ρ ∧ ρ + 1 ≤ hia) ∨
     ((wJ1 ∧ zJ1 ∧ ¬ (cJ ∧ lJ ≤ lJ1 ∧ lJ1 ≤ hJ)) ∧ a < w ∧ loa ≤ ρ ∧ ρ ≤ hia - 0) ∨
     ((wJ ∧ zJ ∧ ¬ (cJ1 ∧ lJ1 ≤ lJ + 1 ∧ lJ + 1 ≤ hJ1)) ∧ a < w ∧ loa ≤ ρ ∧
        ρ ≤ hia - 1)) := by
  arith_split_left

set_option maxHeartbeats 4000000 in
-- the case analysis on seven atoms produces 128 omega calls
/-- Row clauses on the diagonal `J q + a`, left ribbon, regime s ≤ a < w (`dH = (-1)`,
`[s ≤ a] = 1`, `[t ≤ a] = 1`). -/
theorem left_arith_c (w a loa hia ρ J j0 m mD MD lJ hJ lJ1 hJ1 : ℤ)
    (eJ eJ1 : ℤ) (cJ cJ1 wJ wJ1 zJ zJ1 bt : Prop)
    (heJ : (wJ ∧ eJ = 1) ∨ (¬ wJ ∧ eJ = 0)) (heJ1 : (wJ1 ∧ eJ1 = 1) ∨ (¬ wJ1 ∧ eJ1 = 0))
    (hcJ : cJ ↔ (mD ≤ J ∧ J ≤ MD)) (hcJ1 : cJ1 ↔ (mD ≤ J - 1 ∧ J - 1 ≤ MD))
    (hwJ : wJ ↔ (j0 ≤ J ∧ J < j0 + m)) (hwJ1 : wJ1 ↔ (j0 ≤ J - 1 ∧ J - 1 < j0 + m))
    (hzJ : zJ ↔ lJ = hJ) (hzJ1 : zJ1 ↔ lJ1 = hJ1) (hbt : bt ↔ lJ + 1 = lJ1)
    (hwa : a < w) (hWb : loa ≤ hia - 1)
    (hm : 1 ≤ m) (hw0 : mD ≤ j0) (hw1 : j0 + m - 1 ≤ MD)
    (hhJ : mD ≤ J → J ≤ MD → lJ ≤ hJ) (hhJ1 : mD ≤ J - 1 → J - 1 ≤ MD → lJ1 ≤ hJ1)
    (hbitl : mD ≤ J - 1 → J ≤ MD → 0 ≤ lJ1 - lJ ∧ lJ1 - lJ ≤ 1)
    (hbith : mD ≤ J - 1 → J ≤ MD → 0 ≤ hJ1 - hJ ∧ hJ1 - hJ ≤ 1)
    (hend : (J = mD ∨ J = MD) → mD ≤ J → J ≤ MD → lJ = hJ)
    (hend1 : (J - 1 = mD ∨ J - 1 = MD) → mD ≤ J - 1 → J - 1 ≤ MD → lJ1 = hJ1)
    (hS : J = j0 → ¬ (mD ≤ J - 1 ∧ J - 1 ≤ MD) ∨ lJ1 - lJ = 1)
    (hT : J = j0 + m → ¬ (mD ≤ J ∧ J ≤ MD) ∨ lJ = lJ1) :
    (cellFormP w a loa hia ρ (-1) 1 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
      ¬ (cellFormP w a loa hia ρ (-1) 1 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
        ¬ cellFormP w a loa hia (ρ + 1) (-1) 1 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
        wJ))
    ↔
    (cellFormP w a loa hia ρ (-1) 1 (cJ ∧ ¬ (wJ ∧ zJ)) (cJ1 ∧ ¬ (wJ1 ∧ zJ1))
        (hJ - lJ + 1 - eJ) (hJ1 - lJ1 + 1 - eJ1) (lJ + eJ + 1 = lJ1 + eJ1) ∨
     (wJ ∧ zJ ∧ w ≤ a ∧ loa ≤ ρ ∧ ρ + 1 ≤ hia) ∨
     ((wJ1 ∧ zJ1 ∧ ¬ (cJ ∧ lJ ≤ lJ1 ∧ lJ1 ≤ hJ)) ∧ a < w ∧ loa ≤ ρ ∧ ρ ≤ hia - 1) ∨
     ((wJ ∧ zJ ∧ ¬ (cJ1 ∧ lJ1 ≤ lJ + 1 ∧ lJ + 1 ≤ hJ1)) ∧ a < w ∧ loa ≤ ρ ∧
        ρ ≤ hia - 1)) := by
  arith_split_left

set_option maxHeartbeats 4000000 in
-- the case analysis on seven atoms produces 128 omega calls
/-- Row clauses on the diagonal `J q + a`, left ribbon, regime w ≤ a (`dH = (-1)`,
`[s ≤ a] = 1`, `[t ≤ a] = 1`). -/
theorem left_arith_p (w a loa hia ρ J j0 m mD MD lJ hJ lJ1 hJ1 : ℤ)
    (eJ eJ1 : ℤ) (cJ cJ1 wJ wJ1 zJ zJ1 bt : Prop)
    (heJ : (wJ ∧ eJ = 1) ∨ (¬ wJ ∧ eJ = 0)) (heJ1 : (wJ1 ∧ eJ1 = 1) ∨ (¬ wJ1 ∧ eJ1 = 0))
    (hcJ : cJ ↔ (mD ≤ J ∧ J ≤ MD)) (hcJ1 : cJ1 ↔ (mD ≤ J - 1 ∧ J - 1 ≤ MD))
    (hwJ : wJ ↔ (j0 ≤ J ∧ J < j0 + m)) (hwJ1 : wJ1 ↔ (j0 ≤ J - 1 ∧ J - 1 < j0 + m))
    (hzJ : zJ ↔ lJ = hJ) (hzJ1 : zJ1 ↔ lJ1 = hJ1) (hbt : bt ↔ lJ + 1 = lJ1)
    (hwa : w ≤ a) (hWb : loa ≤ hia)
    (hm : 1 ≤ m) (hw0 : mD ≤ j0) (hw1 : j0 + m - 1 ≤ MD)
    (_hhJ : mD ≤ J → J ≤ MD → lJ ≤ hJ) (_hhJ1 : mD ≤ J - 1 → J - 1 ≤ MD → lJ1 ≤ hJ1)
    (_hbitl : mD ≤ J - 1 → J ≤ MD → 0 ≤ lJ1 - lJ ∧ lJ1 - lJ ≤ 1)
    (_hbith : mD ≤ J - 1 → J ≤ MD → 0 ≤ hJ1 - hJ ∧ hJ1 - hJ ≤ 1)
    (_hend : (J = mD ∨ J = MD) → mD ≤ J → J ≤ MD → lJ = hJ)
    (_hend1 : (J - 1 = mD ∨ J - 1 = MD) → mD ≤ J - 1 → J - 1 ≤ MD → lJ1 = hJ1)
    (_hS : J = j0 → ¬ (mD ≤ J - 1 ∧ J - 1 ≤ MD) ∨ lJ1 - lJ = 1)
    (_hT : J = j0 + m → ¬ (mD ≤ J ∧ J ≤ MD) ∨ lJ = lJ1) :
    (cellFormP w a loa hia ρ (-1) 1 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
      ¬ (cellFormP w a loa hia ρ (-1) 1 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
        ¬ cellFormP w a loa hia (ρ + 1) (-1) 1 cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
        wJ))
    ↔
    (cellFormP w a loa hia ρ (-1) 1 (cJ ∧ ¬ (wJ ∧ zJ)) (cJ1 ∧ ¬ (wJ1 ∧ zJ1))
        (hJ - lJ + 1 - eJ) (hJ1 - lJ1 + 1 - eJ1) (lJ + eJ + 1 = lJ1 + eJ1) ∨
     (wJ ∧ zJ ∧ w ≤ a ∧ loa ≤ ρ ∧ ρ + 1 ≤ hia) ∨
     ((wJ1 ∧ zJ1 ∧ ¬ (cJ ∧ lJ ≤ lJ1 ∧ lJ1 ≤ hJ)) ∧ a < w ∧ loa ≤ ρ ∧ ρ ≤ hia - 1) ∨
     ((wJ ∧ zJ ∧ ¬ (cJ1 ∧ lJ1 ≤ lJ + 1 ∧ lJ + 1 ≤ hJ1)) ∧ a < w ∧ loa ≤ ρ ∧
        ρ ≤ hia - 1)) := by
  arith_split_left


/-- **The cell identity for a ribbon removable on the left, in integers.**  On the diagonal
`J q + a` (`0 ≤ a < q`), the cells of the composite of `D` that are not removed (all but the last
cell of each diagonal of the window) are the cells of the composite of `D \ A`, together with
the copies of `\overline O`, `W`, `\overline W` left by the single-cell diagonals of the window. -/
theorem left_arith (w s t q a loa hia ρ J j0 m mD MD lJ hJ lJ1 hJ1 : ℤ)
    (eJ eJ1 : ℤ) (cJ cJ1 wJ wJ1 zJ zJ1 bt : Prop)
    (heJ : (wJ ∧ eJ = 1) ∨ (¬ wJ ∧ eJ = 0)) (heJ1 : (wJ1 ∧ eJ1 = 1) ∨ (¬ wJ1 ∧ eJ1 = 0))
    (hcJ : cJ ↔ (mD ≤ J ∧ J ≤ MD)) (hcJ1 : cJ1 ↔ (mD ≤ J - 1 ∧ J - 1 ≤ MD))
    (hwJ : wJ ↔ (j0 ≤ J ∧ J < j0 + m)) (hwJ1 : wJ1 ↔ (j0 ≤ J - 1 ∧ J - 1 < j0 + m))
    (hzJ : zJ ↔ lJ = hJ) (hzJ1 : zJ1 ↔ lJ1 = hJ1) (hbt : bt ↔ lJ + 1 = lJ1)
    (_ha0 : 0 ≤ a) (_haq : a < q) (_hwq : w < q) (hts : t < s) (_ht0 : 0 ≤ t) (hsw : s ≤ w)
    (hlh : loa ≤ hia) (hWb : a < w → loa ≤ hia - (if s ≤ a then 1 else 0))
    (hm : 1 ≤ m) (hw0 : mD ≤ j0) (hw1 : j0 + m - 1 ≤ MD)
    (hhJ : mD ≤ J → J ≤ MD → lJ ≤ hJ) (hhJ1 : mD ≤ J - 1 → J - 1 ≤ MD → lJ1 ≤ hJ1)
    (hbitl : mD ≤ J - 1 → J ≤ MD → 0 ≤ lJ1 - lJ ∧ lJ1 - lJ ≤ 1)
    (hbith : mD ≤ J - 1 → J ≤ MD → 0 ≤ hJ1 - hJ ∧ hJ1 - hJ ≤ 1)
    (hend : (J = mD ∨ J = MD) → mD ≤ J → J ≤ MD → lJ = hJ)
    (hend1 : (J - 1 = mD ∨ J - 1 = MD) → mD ≤ J - 1 → J - 1 ≤ MD → lJ1 = hJ1)
    (hS : J = j0 → ¬ (mD ≤ J - 1 ∧ J - 1 ≤ MD) ∨ lJ1 - lJ = 1)
    (hT : J = j0 + m → ¬ (mD ≤ J ∧ J ≤ MD) ∨ lJ = lJ1) :
    (cellFormP w a loa hia ρ (if a < t then 1 else if a < s then 0 else -1)
        (if s ≤ a then 1 else 0) cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
      ¬ (cellFormP w a loa hia ρ (if a < t then 1 else if a < s then 0 else -1)
          (if s ≤ a then 1 else 0) cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
        ¬ cellFormP w a loa hia (ρ + 1) (if a < t then 1 else if a < s then 0 else -1)
          (if s ≤ a then 1 else 0) cJ cJ1 (hJ - lJ + 1) (hJ1 - lJ1 + 1) bt ∧
        (if t ≤ a then wJ else wJ1)))
    ↔
    (cellFormP w a loa hia ρ (if a < t then 1 else if a < s then 0 else -1)
        (if s ≤ a then 1 else 0) (cJ ∧ ¬ (wJ ∧ zJ)) (cJ1 ∧ ¬ (wJ1 ∧ zJ1))
        (hJ - lJ + 1 - eJ) (hJ1 - lJ1 + 1 - eJ1) (lJ + eJ + 1 = lJ1 + eJ1) ∨
     (wJ ∧ zJ ∧ w ≤ a ∧ loa ≤ ρ ∧ ρ + 1 ≤ hia) ∨
     ((wJ1 ∧ zJ1 ∧ ¬ (cJ ∧ lJ ≤ lJ1 ∧ lJ1 ≤ hJ)) ∧ a < w ∧ loa ≤ ρ ∧
        ρ ≤ hia - (if s ≤ a then 1 else 0)) ∨
     ((wJ ∧ zJ ∧ ¬ (cJ1 ∧ lJ1 ≤ lJ + 1 ∧ lJ + 1 ≤ hJ1)) ∧ a < w ∧ loa ≤ ρ ∧
        ρ ≤ hia - (if t ≤ a then 1 else 0))) := by
  by_cases hwa : a < w
  · have hWb' := hWb hwa
    have hno : ¬ w ≤ a := by omega
    by_cases h1 : a < t
    · have h2 : ¬ s ≤ a := by omega
      have h3 : ¬ t ≤ a := by omega
      simp only [h1, h2, h3, ↓reduceIte] at hWb' ⊢
      exact left_arith_a w a loa hia ρ J j0 m mD MD lJ hJ lJ1 hJ1 eJ eJ1 cJ cJ1 wJ wJ1
        zJ zJ1 bt heJ heJ1 hcJ hcJ1 hwJ hwJ1 hzJ hzJ1 hbt hwa hWb' hm hw0 hw1 hhJ hhJ1 hbitl hbith
        hend hend1 hS hT
    · by_cases h2 : a < s
      · have h3 : ¬ s ≤ a := by omega
        have h4 : t ≤ a := by omega
        simp only [h1, h2, h3, h4, ↓reduceIte] at hWb' ⊢
        exact left_arith_b w a loa hia ρ J j0 m mD MD lJ hJ lJ1 hJ1 eJ eJ1 cJ cJ1 wJ wJ1
          zJ zJ1 bt heJ heJ1 hcJ hcJ1 hwJ hwJ1 hzJ hzJ1 hbt hwa hWb' hm hw0 hw1 hhJ hhJ1 hbitl
          hbith hend hend1 hS hT
      · have h3 : s ≤ a := by omega
        have h4 : t ≤ a := by omega
        simp only [h1, h2, h3, h4, ↓reduceIte] at hWb' ⊢
        exact left_arith_c w a loa hia ρ J j0 m mD MD lJ hJ lJ1 hJ1 eJ eJ1 cJ cJ1 wJ wJ1
          zJ zJ1 bt heJ heJ1 hcJ hcJ1 hwJ hwJ1 hzJ hzJ1 hbt hwa hWb' hm hw0 hw1 hhJ hhJ1 hbitl
          hbith hend hend1 hS hT
  · have hwa' : w ≤ a := by omega
    have hsa : s ≤ a := by omega
    have hta : ¬ a < t := by omega
    have hsa' : ¬ a < s := by omega
    have h4 : t ≤ a := by omega
    simp only [hsa, hta, hsa', h4, ↓reduceIte]
    exact left_arith_p w a loa hia ρ J j0 m mD MD lJ hJ lJ1 hJ1 eJ eJ1 cJ cJ1 wJ wJ1
      zJ zJ1 bt heJ heJ1 hcJ hcJ1 hwJ hwJ1 hzJ hzJ1 hbt hwa' hlh hm hw0 hw1 hhJ hhJ1 hbitl hbith
      hend hend1 hS hT

end Rem

end Corner

end Plan

end SkewGluing
