/-
# Axiom regression guard

A build-time check that the development stays sorry-free and axiom-clean.  Each
`#guard_msgs in #print axioms …` pins the axiom footprint of a headline result to
Lean's three standard axioms `[propext, Classical.choice, Quot.sound]`.  If a
`sorry` or a stray `axiom` ever creeps into a dependency, the reported footprint
changes and `#guard_msgs` turns the mismatch into a build error — so `lake build`
fails rather than silently degrading the "axiom-free" claim.

Because the §§2–4 analytic inputs are bundled as the `FTInputs` hypothesis
(`Bridge`) rather than posited as global axioms, even `main_bound` and
`main_bound_interval` report only the standard three: the analytic dependence is
in their *type*, not the ambient axiom set.
-/
import ForgacsTran.Main
import ForgacsTran.Reduction
import ForgacsTran.LinearCase
import ForgacsTran.Necessity

open ForgacsTran

-- §5 `sec:proof` — the counting engine and its wrappers
-- (plus the §3 `sec:geometry` interval/ray inclusions).
/-- info: 'ForgacsTran.exceptionalRoots_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exceptionalRoots_card_le

/-- info: 'ForgacsTran.le_card_roots_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms le_card_roots_filter

/-- info: 'ForgacsTran.ftInterval_subset_posRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftInterval_subset_posRay

-- §2 `sec:reduction` — numerator as initial data, and eventual-degree upper bound.
/-- info: 'ForgacsTran.initial_data_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial_data_unique

/-- info: 'ForgacsTran.eventual_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventual_natDegree_le

-- §5 `sec:proof`, `prop:linear-case` — the excluded elementary case.
/-- info: 'ForgacsTran.Plin_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plin_recurrence

/-- info: 'ForgacsTran.Plin_exceptional_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plin_exceptional_eq

/-- info: 'ForgacsTran.Plin_exceptional_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plin_exceptional_card_le

-- §6 `sec:consequences`, `prop:N-dependence` — necessity of the numerator dependence.
/-- info: 'ForgacsTran.exceptional_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exceptional_unbounded

/-- info: 'ForgacsTran.dvd_exceptional_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dvd_exceptional_le

-- Analytic bundle: consistency witness (Bridge).
/-- info: 'ForgacsTran.ftInputsWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftInputsWitness

/-- info: 'ForgacsTran.ftInputs_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftInputs_nonempty

-- Analytic bundle: degree bound derived from the §2 recurrence, not assumed (Bridge).
/-- info: 'ForgacsTran.FTInputs.ofRecurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTInputs.ofRecurrence

-- §1 `thm:main` — the headline theorem, with no custom axioms.
/-- info: 'ForgacsTran.main_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound

/-- info: 'ForgacsTran.main_bound_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound_interval

/-- info: 'ForgacsTran.main_bound_ofRecurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound_ofRecurrence

/-- info: 'ForgacsTran.interior_distinct_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_distinct_count

-- `Plin_ne_zero` lies outside the transitive closure of the guards above, so it is guarded
-- explicitly: without this, a `sorry` there would leave every other guard green.
/-- info: 'ForgacsTran.Plin_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plin_ne_zero

/-- info: 'ForgacsTran.Plin_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plin_unique

/-- info: 'ForgacsTran.denomConv_dlin_Plin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms denomConv_dlin_Plin

/-- info: 'ForgacsTran.ftRay_subset_posRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftRay_subset_posRay
