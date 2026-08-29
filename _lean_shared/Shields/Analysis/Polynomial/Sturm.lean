/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Sturm families and strict interlacing

A **Sturm family** on an interval `(u,v)` is a sequence of real polynomials `Q 0, Q 1, \ldots`
with `\deg Q m = m`, prescribed alternating signs at the endpoints, and one sign relation in the
interior: **at a zero of `Q m` the two neighbors `Q (m+1)` and `Q (m-1)` take values of opposite
sign**.  That single relation forces the whole classical picture, unconditionally:

* every `Q m` has exactly `m` roots, all simple and all inside `(u,v)`;
* consecutive members **strictly interlace**, `z_0 < x_0 < z_1 < \cdots < x_{m-1} < z_m`.

The proof is an induction on `m` carrying the alternation of the previous member along the zeros
of the current one.  The sign relation transfers that alternation one step; the intermediate value
theorem then places a zero of `Q (m+1)` in each of the `m+1` intervals cut out by `u`, the zeros
of `Q m`, and `v`; and the degree exhausts them, so every zero is simple and the interlacing is
strict.

## Main results

* `Shields.IsSturmFamily` — the hypotheses, as a structure.
* `Shields.IsSturmRoots` — the induction's invariant: an enumeration of the zeros of one member,
  strictly increasing, interior, simple, with the previous member alternating along it.
* `Shields.exists_isSturmRoots` — **every member has a full set of simple interior zeros**.
* `Shields.exists_strict_interlacing` — **consecutive members strictly interlace**.
* `Shields.IsSturmFamily.card_roots` — hence `Q m` has exactly `m` roots with multiplicity.

## Implementation notes

Nothing here is about a specific family; the interior sign relation is a hypothesis, and where it
comes from — a three-term recurrence, a determinant identity, an orthogonality — is the caller's
business.  The endpoint conditions are stated as strict sign conditions rather than as
non-vanishing plus a count, because that is what an induction on the degree can consume directly.

## References

* C. Sturm, *Mémoire sur la résolution des équations numériques*, 1835.
* G. Szegő, *Orthogonal polynomials*, AMS Colloquium Publications 23, 4th ed., 1975, §3.3.

## Tags

sturm sequence, interlacing, real roots, simple zeros, intermediate value theorem
-/

open Polynomial

namespace Shields

variable {Q : ℕ → Polynomial ℝ} {u v : ℝ}

/-- A polynomial taking values of opposite (weak) sign at `a` and `b` vanishes somewhere on the
closed interval they span. -/
theorem exists_root_of_eval_mul_nonpos (P : Polynomial ℝ) {a b : ℝ}
    (hsign : P.eval a * P.eval b ≤ 0) : ∃ c ∈ Set.uIcc a b, P.eval c = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => P.eval x) (Set.uIcc a b) := P.continuousOn
  have h0 : (0 : ℝ) ∈ Set.uIcc (P.eval a) (P.eval b) :=
    Set.mem_uIcc.mpr ((mul_nonpos_iff.mp hsign).elim (fun h => Or.inr ⟨h.2, h.1⟩) Or.inl)
  obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc hcont h0
  exact ⟨c, hc, hc0⟩

/-- A polynomial taking values of **strictly** opposite sign at `a ≤ b` vanishes somewhere in the
**open** interval.  The intermediate value theorem places a zero in the closed interval, and
neither endpoint is that zero because neither endpoint value is `0`. -/
theorem exists_root_mem_Ioo_of_eval_mul_neg (P : Polynomial ℝ) {a b : ℝ} (hab : a ≤ b)
    (hsign : P.eval a * P.eval b < 0) : ∃ c ∈ Set.Ioo a b, P.eval c = 0 := by
  obtain ⟨c, hc, hc0⟩ := exists_root_of_eval_mul_nonpos P hsign.le
  rw [Set.uIcc_of_le hab] at hc
  refine ⟨c, ⟨lt_of_le_of_ne hc.1 ?_, lt_of_le_of_ne hc.2 ?_⟩, hc0⟩
  · intro heq
    rw [← heq] at hc0
    rw [hc0, zero_mul] at hsign
    exact lt_irrefl 0 hsign
  · intro heq
    rw [heq] at hc0
    rw [hc0, mul_zero] at hsign
    exact lt_irrefl 0 hsign

/-- With no zero on the closed interval spanned by `a` and `b`, a polynomial keeps one sign
there. -/
theorem eval_mul_pos_of_no_root (P : Polynomial ℝ) {a b : ℝ}
    (hno : ∀ c ∈ Set.uIcc a b, P.eval c ≠ 0) : 0 < P.eval a * P.eval b := by
  rcases le_or_gt (P.eval a * P.eval b) 0 with hle | hlt
  · obtain ⟨c, hc, hc0⟩ := exists_root_of_eval_mul_nonpos P hle
    exact absurd hc0 (hno c hc)
  · exact hlt

/-- **A polynomial of degree at most `n` carrying `n` distinct roots has no others, and every one
of them is simple.**  Listing the roots as an injective family `z : Fin n → R` identifies `P.roots`
with that family, so the count, the exhaustiveness and the multiplicities all read off it. -/
theorem roots_eq_map_of_injective_of_natDegree_le {R : Type*} [CommRing R] [IsDomain R]
    {P : Polynomial R} (hP : P ≠ 0) {n : ℕ} {z : Fin n → R} (hz : Function.Injective z)
    (hroot : ∀ j, P.eval (z j) = 0) (hdeg : P.natDegree ≤ n) :
    P.roots = Multiset.map z Finset.univ.val := by
  classical
  have hcard : (Finset.image z Finset.univ).card = n := by
    rw [Finset.card_image_of_injective _ hz, Finset.card_univ, Fintype.card_fin]
  have himg : (Finset.image z Finset.univ).val = Multiset.map z Finset.univ.val := by
    rw [Finset.image_val, Multiset.dedup_eq_self.mpr (Multiset.Nodup.map hz Finset.univ.nodup)]
  rw [← himg]
  exact Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    (fun t ht => by obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht; exact hroot j)
    (hdeg.trans hcard.ge) hP

/-- A **Sturm family** on `(u,v)`: degrees increasing by one, alternating signs at the left
endpoint, positive at the right, and the interior sign relation `toda` — at a zero of the `m`-th
member the two neighbors take values of opposite sign.  The relation is required only inside
`(u,v)`. -/
structure IsSturmFamily (Q : ℕ → Polynomial ℝ) (u v : ℝ) : Prop where
  /-- The interval is nondegenerate. -/
  lt : u < v
  /-- The `m`-th member has degree exactly `m`. -/
  degree : ∀ m, (Q m).natDegree = m
  /-- At an interior zero of one member, its two neighbors have opposite signs. -/
  toda : ∀ m : ℕ, 1 ≤ m → ∀ x ∈ Set.Ioo u v, (Q m).eval x = 0 →
      (Q (m + 1)).eval x * (Q (m - 1)).eval x < 0
  /-- The alternating endpoint sign at the left end. -/
  left : ∀ m, 0 < (-1 : ℝ) ^ m * (Q m).eval u
  /-- The positive endpoint value at the right end. -/
  right : ∀ m, 0 < (Q m).eval v

theorem IsSturmFamily.ne_zero (h : IsSturmFamily Q u v) (m : ℕ) : Q m ≠ 0 := by
  intro h0
  have := h.right m
  rw [h0] at this
  simp at this

/-- The full conclusion at level `m`, phrased for an explicit increasing list `x` of the zeros.

`gapSign` records the sign of `Q m` between consecutive zeros: a point of `(u,v)` lying above
the first `j` zeros and below the remaining `m - j` carries the sign `(-1)^{m-j}`.  `prevSign`
records that the previous member alternates on those zeros.  Both are what the induction step
consumes, and both are re-established for `m + 1`. -/
structure IsSturmRoots (Q : ℕ → Polynomial ℝ) (u v : ℝ) (m : ℕ) (x : Fin m → ℝ) : Prop where
  /-- The zeros are listed in increasing order. -/
  mono : StrictMono x
  /-- Every zero lies in the open interval. -/
  mem : ∀ i, x i ∈ Set.Ioo u v
  /-- Every listed point is a zero. -/
  isRoot : ∀ i, (Q m).eval (x i) = 0
  /-- The list is exhaustive: there is no other real zero. -/
  exhaust : ∀ t : ℝ, (Q m).eval t = 0 → ∃ i, t = x i
  /-- Every zero is simple. -/
  simple : ∀ i, (Q m).rootMultiplicity (x i) = 1
  /-- Counted with multiplicity there are exactly `m` zeros. -/
  card : Multiset.card (Q m).roots = m
  /-- The sign of `Q m` on the `j`-th gap is `(-1)^{m-j}`. -/
  gapSign : ∀ j : ℕ, j ≤ m → ∀ t : ℝ, t ∈ Set.Ioo u v →
      (∀ i : Fin m, i.val < j → x i < t) → (∀ i : Fin m, j ≤ i.val → t < x i) →
      0 < (-1 : ℝ) ^ (m - j) * (Q m).eval t
  /-- The previous member alternates in sign on the zeros of `Q m`. -/
  prevSign : ∀ i : Fin m, 0 < (-1 : ℝ) ^ (m - 1 - i.val) * (Q (m - 1)).eval (x i)

/-- The induction starts at `m = 0`, where `Q 0` is a positive constant with no zero. -/
theorem isSturmRoots_zero (h : IsSturmFamily Q u v) :
    IsSturmRoots Q u v 0 (fun i => i.elim0) := by
  have hconst : ∀ t : ℝ, (Q 0).eval t = (Q 0).coeff 0 := by
    intro t
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero (h.degree 0)]
    simp
  have hpos : ∀ t : ℝ, 0 < (Q 0).eval t := by
    intro t
    rw [hconst t, ← hconst v]
    exact h.right 0
  refine ⟨fun a => a.elim0, fun i => i.elim0, fun i => i.elim0, ?_, fun i => i.elim0, ?_, ?_,
    fun i => i.elim0⟩
  · intro t ht
    exact absurd ht (ne_of_gt (hpos t))
  · have hle := Polynomial.card_roots' (Q 0)
    rw [h.degree 0] at hle
    exact Nat.le_zero.mp hle
  · intro j hj t _ _ _
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    simpa using hpos t

/-- **The walls of one interlacing step.**  The `m + 2` points `u, x 0, …, x (m-1), v`, packaged
as a single `w : ℕ → ℝ` characterized by three equations, together with their strict monotonicity
on `[0, m+1]`.

Indexing the walls by `ℕ` rather than by `Fin (m+2)` is what keeps the gap argument free of index
arithmetic: the `j`-th gap is `(w j, w (j+1))` at every `j ≤ m`, with no case split at the ends.
Only the three equations are ever used, never the formula defining `w`. -/
theorem exists_sturmWalls {m : ℕ} {x : Fin m → ℝ} (hx : IsSturmRoots Q u v m x)
    (h : IsSturmFamily Q u v) :
    ∃ w : ℕ → ℝ, w 0 = u ∧ (∀ (j : ℕ) (hj : j < m), w (j + 1) = x ⟨j, hj⟩) ∧ w (m + 1) = v ∧
      (∀ j : ℕ, j ≤ m → w j < w (j + 1)) ∧ (∀ a b : ℕ, a < b → b ≤ m + 1 → w a < w b) := by
  obtain ⟨w, hw0, hwsucc, hwtop⟩ :
      ∃ w : ℕ → ℝ, w 0 = u ∧ (∀ (j : ℕ) (hj : j < m), w (j + 1) = x ⟨j, hj⟩) ∧ w (m + 1) = v :=
    ⟨fun j => if j = 0 then u else if hj : j - 1 < m then x ⟨j - 1, hj⟩ else v, by simp,
      fun j hj => by simp [hj], by simp⟩
  have hwlt : ∀ j : ℕ, j ≤ m → w j < w (j + 1) := by
    intro j hj
    match j, hj with
    | 0, _ =>
      rw [hw0]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [hwtop]; exact h.lt
      · rw [hwsucc 0 hm]; exact (hx.mem ⟨0, hm⟩).1
    | (i + 1), hj =>
      have him : i < m := by omega
      rw [hwsucc i him]
      by_cases hi1 : i + 1 < m
      · rw [hwsucc (i + 1) hi1]; exact hx.mono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
      · rw [show i + 1 + 1 = m + 1 by omega, hwtop]; exact (hx.mem ⟨i, him⟩).2
  exact ⟨w, hw0, hwsucc, hwtop, hwlt, fun a b hab hb =>
    strictMonoOn_Iic_of_lt_succ (n := m + 1) (fun j hj => hwlt j (Nat.lt_succ_iff.mp hj))
      ((hab.trans_le hb).le) hb hab⟩

/-- **`Q (m+1)` alternates in sign along the walls**: its sign at the `j`-th wall is
`(-1)^{m+1-j}`.

At the two ends this is the family's own boundary sign condition.  At an interior wall -- a root of
`Q m` -- it is Toda's three-term relation, which forces `Q (m+1)` and `Q (m-1)` to take opposite
signs there, and `Q (m-1)` alternates by the inductive hypothesis.

This is the content of the step.  Once it is known, the roots are the intermediate value theorem
applied to each gap and nothing more. -/
theorem sturmWalls_sign {m : ℕ} {x : Fin m → ℝ} (hx : IsSturmRoots Q u v m x)
    (h : IsSturmFamily Q u v) {w : ℕ → ℝ} (hw0 : w 0 = u)
    (hwsucc : ∀ (j : ℕ) (hj : j < m), w (j + 1) = x ⟨j, hj⟩) (hwtop : w (m + 1) = v)
    {j : ℕ} (hj : j ≤ m + 1) :
    0 < (-1 : ℝ) ^ (m + 1 - j) * (Q (m + 1)).eval (w j) := by
  by_cases hj0 : j = 0
  · subst hj0
    rw [hw0, Nat.sub_zero]
    exact h.left (m + 1)
  by_cases hjm : j = m + 1
  · subst hjm
    rw [hwtop, Nat.sub_self, pow_zero, one_mul]
    exact h.right (m + 1)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have him : i < m := by omega
  have hm1 : 1 ≤ m := by omega
  have hprev := hx.prevSign ⟨i, him⟩
  have htoda := h.toda m hm1 (x ⟨i, him⟩) (hx.mem ⟨i, him⟩) (hx.isRoot ⟨i, him⟩)
  rw [hwsucc i him, show m + 1 - (i + 1) = (m - 1 - i) + 1 by omega, pow_succ]
  rcases neg_one_pow_eq_or ℝ (m - 1 - i) with ha | ha <;> rw [ha] at hprev ⊢ <;> nlinarith

/-- **A zero of `Q (m+1)` in every gap.**  Consecutive walls carry opposite signs of `Q (m+1)`,
because their exponents differ by one, so the intermediate value theorem puts a zero strictly
inside each of the `m + 1` intervals the walls cut out. -/
theorem exists_root_mem_gap {m : ℕ} {w : ℕ → ℝ} (hwlt : ∀ j : ℕ, j ≤ m → w j < w (j + 1))
    (hwsign : ∀ j : ℕ, j ≤ m + 1 → 0 < (-1 : ℝ) ^ (m + 1 - j) * (Q (m + 1)).eval (w j))
    (j : Fin (m + 1)) :
    ∃ c : ℝ, w j.val < c ∧ c < w (j.val + 1) ∧ (Q (m + 1)).eval c = 0 := by
  have hjm : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
  have hs1 := hwsign j.val (by omega)
  have hs2 := hwsign (j.val + 1) (by omega)
  rw [show m + 1 - j.val = (m - j.val) + 1 by omega, pow_succ] at hs1
  rw [show m + 1 - (j.val + 1) = m - j.val by omega] at hs2
  have hneg : (Q (m + 1)).eval (w j.val) * (Q (m + 1)).eval (w (j.val + 1)) < 0 := by
    rcases neg_one_pow_eq_or ℝ (m - j.val) with ha | ha <;> rw [ha] at hs1 hs2 <;> nlinarith
  obtain ⟨c, hc, hc0⟩ := exists_root_mem_Ioo_of_eval_mul_neg _ (hwlt j.val hjm).le hneg
  exact ⟨c, hc.1, hc.2, hc0⟩

/-- **The sign of `Q (m+1)` is the same throughout a gap as at the wall bounding it.**

Every zero of `Q (m+1)` is one of the `z i`, and each of those lies strictly on one side of both
`w j` and any point `t` of the `j`-th gap -- below both when `i < j`, above both when `j \le i`.  So
no zero separates `w j` from `t`, and the sign at the wall carries across. -/
theorem sturmGap_sign {m : ℕ} {w : ℕ → ℝ} {z : Fin (m + 1) → ℝ}
    (hwmono : ∀ a b : ℕ, a ≤ b → b ≤ m + 1 → w a ≤ w b)
    (hzlo : ∀ i : Fin (m + 1), w i.val < z i) (hzhi : ∀ i : Fin (m + 1), z i < w (i.val + 1))
    (hexhaust : ∀ t : ℝ, (Q (m + 1)).eval t = 0 → ∃ i, t = z i)
    (hwsign : ∀ j : ℕ, j ≤ m + 1 → 0 < (-1 : ℝ) ^ (m + 1 - j) * (Q (m + 1)).eval (w j))
    {j : ℕ} (hj : j ≤ m + 1) {t : ℝ} (hlo : ∀ i : Fin (m + 1), i.val < j → z i < t)
    (hhi : ∀ i : Fin (m + 1), j ≤ i.val → t < z i) :
    0 < (-1 : ℝ) ^ (m + 1 - j) * (Q (m + 1)).eval t := by
  have hanchor := hwsign j hj
  have hsame : 0 < (Q (m + 1)).eval (w j) * (Q (m + 1)).eval t := by
    refine eval_mul_pos_of_no_root _ fun c hc hc0 => ?_
    obtain ⟨i, rfl⟩ := hexhaust c hc0
    rw [Set.mem_uIcc] at hc
    rcases lt_or_ge i.val j with hij | hij
    · rcases hc with ⟨ha, -⟩ | ⟨hb, -⟩ <;>
        linarith [(hzhi i).trans_le (hwmono _ _ (Nat.succ_le_of_lt hij) hj), hlo i hij]
    · rcases hc with ⟨-, ha⟩ | ⟨-, hb⟩ <;>
        linarith [(hwmono j i.val hij i.isLt.le).trans_lt (hzlo i), hhi i hij]
  rcases neg_one_pow_eq_or ℝ (m + 1 - j) with ha | ha <;> rw [ha] at hanchor ⊢ <;> nlinarith

/-- **The induction step.**  The previous member alternates on the zeros of `Q m`; the interior
sign relation transfers that alternation to `Q (m+1)`; the intermediate value theorem then puts
one zero of `Q (m+1)` in each of the `m + 1` intervals cut out by `u`, the zeros of `Q m`, and
`v`; and `deg (Q (m+1)) = m + 1` exhausts them, so every zero is simple and the interlacing is
strict. -/
theorem IsSturmRoots.step {m : ℕ} {x : Fin m → ℝ} (hx : IsSturmRoots Q u v m x)
    (h : IsSturmFamily Q u v) :
    ∃ z : Fin (m + 1) → ℝ, IsSturmRoots Q u v (m + 1) z ∧
      ∀ i : Fin m, z i.castSucc < x i ∧ x i < z i.succ := by
  obtain ⟨w, hw0, hwsucc, hwtop, hwlt, hwstrict⟩ := exists_sturmWalls hx h
  have hwroot : ∀ i : Fin m, w (i.val + 1) = x i := fun i => hwsucc i.val i.isLt
  have hwmono : ∀ a b : ℕ, a ≤ b → b ≤ m + 1 → w a ≤ w b := fun a b hab hb =>
    (eq_or_lt_of_le hab).elim (fun heq => (congrArg w heq).le) fun hlt => (hwstrict a b hlt hb).le
  have hwsign := fun (j : ℕ) (hj : j ≤ m + 1) => sturmWalls_sign hx h hw0 hwsucc hwtop hj
  -- One zero of `Q (m+1)` in each of the `m + 1` gaps.
  choose z hzlo hzhi hzroot using exists_root_mem_gap hwlt hwsign
  have hzmono : StrictMono z := fun a b hab =>
    ((hzhi a).trans_le (hwmono _ _ hab b.isLt.le)).trans (hzlo b)
  have hzmem : ∀ j : Fin (m + 1), z j ∈ Set.Ioo u v := fun j =>
    ⟨hw0 ▸ (hwmono 0 j.val (Nat.zero_le _) j.isLt.le).trans_lt (hzlo j),
      hwtop ▸ (hzhi j).trans_le (hwmono _ _ j.isLt le_rfl)⟩
  -- The `m + 1` zeros found exhaust `Q (m+1)`, whose degree is `m + 1`.
  have hseq := roots_eq_map_of_injective_of_natDegree_le (h.ne_zero (m + 1)) hzmono.injective
    hzroot (le_of_eq (h.degree (m + 1)))
  have hexhaust : ∀ t : ℝ, (Q (m + 1)).eval t = 0 → ∃ j, t = z j := fun t ht =>
    (Multiset.mem_map.mp (hseq ▸ Polynomial.mem_roots'.mpr ⟨h.ne_zero (m + 1), ht⟩)).imp
      fun j hj => hj.2.symm
  refine ⟨z, ⟨hzmono, hzmem, hzroot, hexhaust, fun j => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← Polynomial.count_roots, hseq, Multiset.count_map_eq_count' _ _ hzmono.injective]; simp
  · rw [hseq, Multiset.card_map]; simp
  · exact fun j hj t _ hlo hhi => sturmGap_sign hwmono hzlo hzhi hexhaust hwsign hj hlo hhi
  · -- The alternation of `Q m` on the new zeros is the gap sign one level down.
    intro j; simp only [Nat.add_sub_cancel]
    refine hx.gapSign j.val j.is_le (z j) (hzmem j) (fun i hi => ?_) fun i hi => ?_
    · rw [← hwroot i]; exact (hwmono _ _ hi j.isLt.le).trans_lt (hzlo j)
    · rw [← hwroot i]; exact (hzhi j).trans_le (hwmono _ _ (by omega) (by have := i.isLt; omega))
  · exact fun i => ⟨hwroot i ▸ hzhi i.castSucc, hwroot i ▸ hzlo i.succ⟩

/-- **Every member carries a full set of simple interior zeros**, as many as its degree. -/
theorem exists_isSturmRoots (h : IsSturmFamily Q u v) (m : ℕ) :
    ∃ x : Fin m → ℝ, IsSturmRoots Q u v m x := by
  induction m with
  | zero => exact ⟨_, isSturmRoots_zero h⟩
  | succ m ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨z, hz, -⟩ := hx.step h
    exact ⟨z, hz⟩

/-- **Strict interlacing of consecutive degrees.**  The `m + 1` zeros of `Q (m+1)` separate the
`m` zeros of `Q m`: `z_0 < x_0 < z_1 < ⋯ < x_{m-1} < z_m`. -/
theorem exists_strict_interlacing (h : IsSturmFamily Q u v) (m : ℕ) :
    ∃ (x : Fin m → ℝ) (z : Fin (m + 1) → ℝ),
      IsSturmRoots Q u v m x ∧ IsSturmRoots Q u v (m + 1) z ∧
        ∀ i : Fin m, z i.castSucc < x i ∧ x i < z i.succ := by
  obtain ⟨x, hx⟩ := exists_isSturmRoots h m
  obtain ⟨z, hz, hint⟩ := hx.step h
  exact ⟨x, z, hx, hz, hint⟩

/-- `Q m` has exactly `m` roots counted with multiplicity, and therefore `m` distinct simple
roots by `exists_isSturmRoots`. -/
theorem IsSturmFamily.card_roots (h : IsSturmFamily Q u v) (m : ℕ) :
    Multiset.card (Q m).roots = m := by
  obtain ⟨x, hx⟩ := exists_isSturmRoots h m
  exact hx.card


/-! ### Axiom footprint -/

/-- info: 'Shields.exists_strict_interlacing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_strict_interlacing

/-- info: 'Shields.IsSturmFamily.card_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsSturmFamily.card_roots

end Shields
