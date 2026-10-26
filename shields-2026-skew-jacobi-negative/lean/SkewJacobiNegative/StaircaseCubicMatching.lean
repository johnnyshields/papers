/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseResidualAlgebra

/-!
# Cubic staircase residual matching

Exact cubic matching of actual normalized primitive factors on the four-row component domain.
-/

namespace SkewJacobiNegative.Staircase

open Gluing HessenbergExpansion

namespace CubicNecessity

abbrev Triple := Fin 3 → ℤ

inductive Kind where
  | left
  | right
  | interval

def domain (q a b c d r s t : ℤ) : Prop :=
  0 < q ∧ 0 < r ∧ 0 < s ∧ 0 < t ∧
  r < a ∧ r + s < b ∧ s + t < c ∧ q + t < d ∧
  a ≠ q ∧ r ≠ q ∧ s ≠ q ∧ t ≠ q

def contact (k : Kind) (q a b c r s t : ℤ) : Prop :=
  match k with
  | .left => b = q ∧ r = s
  | .right => c = q ∧ s = t
  | .interval => a + b - r = q ∧ a = s

/-- Signed inventories retain all multiplicities.  Only genuinely erased terms
are omitted; equal surviving terms are never deduplicated. -/
def positive (k : Kind) (q a b c d r s t : ℤ) : List Triple :=
  match k with
  | .left =>
      (if c = q then [] else [![c, a + q - r, d]]) ++
      [![a, q + c - r, d], ![r, t, a + q + c + d - 2 * r - t]]
  | .right =>
      [![a, b + q - s, d]] ++
      (if b = q then [] else [![a, b, q + d - s]]) ++
      [![r, s, a + b + q + d - r - 2 * s]]
  | .interval =>
      (if b + c - s = q then [] else [![s, b + c - s, d]]) ++
      [![t, b, c + d - t], ![r, t, q + c + d - s - t]]

def negative (k : Kind) (q a b c d r s t : ℤ) : List Triple :=
  match k with
  | .left =>
      [![r, a + q + c - 2 * r, d],
       ![t, a + q - r, c + d - t],
       ![t, a, q + c + d - r - t]]
  | .right =>
      [![r, a + b + q - r - s, d]] ++
      (if a + b - r = q then [] else [![r, a + b - r, q + d - s]]) ++
      [![s, a, b + q + d - 2 * s]]
  | .interval =>
      (if c = q then [] else [![b, c, d]]) ++
      [![r, q + c - s, d], ![s, t, b + c + d - s - t]]

noncomputable def model (k : Kind) (q a b c d r s t : ℤ) : CompleteRing :=
  ((positive k q a b c d r s t).map tripleTerm).sum -
    ((negative k q a b c d r s t).map tripleTerm).sum

theorem model_left (q : ℕ+) (a b c d r s t : ℤ) :
    model .left q.val a b c d r s t = leftMiddleCubic q a c d r t := by
  simp only [model, positive, negative, leftMiddleCubic, bar,
    eraseGenerator_complete]
  split_ifs <;> simp [tripleTerm] <;> ring

theorem model_right (q : ℕ+) (a b c d r s t : ℤ) :
    model .right q.val a b c d r s t = rightMiddleCubic q a b d r s := by
  simp only [model, positive, negative, rightMiddleCubic, bar,
    eraseGenerator_complete]
  split_ifs <;> simp [tripleTerm] <;> ring

theorem model_interval (q : ℕ+) (a b c d r s t : ℤ) :
    model .interval q.val a b c d r s t =
      intervalExtractionCubic q b c d r s t := by
  simp only [model, positive, negative, intervalExtractionCubic, bar,
    eraseGenerator_complete]
  split_ifs <;> simp [tripleTerm] <;> ring

theorem domain_of_component {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) :
    domain q.val (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (P.g 0) (P.g 1) (P.g 2) := by
  obtain ⟨hr, hs, ht, ha', hb', hc', hd⟩ := P.four_domain hP.thick.hessenberg
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hq : (0 : ℤ) < q.val := by exact_mod_cast q.pos
  have hpos (j : Fin 3) : (0 : ℤ) < P.g j := by
    exact_mod_cast hP.gap_pos j
  have hne (j : Fin 3) : (P.g j : ℤ) ≠ q.val := by
    exact_mod_cast hP.gap_ne j
  have hane : (P.r 0 : ℤ) ≠ q.val := by exact_mod_cast ha
  have hp0 := hpos 0
  have hp1 := hpos 1
  have hp2 := hpos 2
  have hn0 := hne 0
  have hn1 := hne 1
  have hn2 := hne 2
  dsimp [domain]
  omega

theorem actual_model {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hd : (canonicalPrimitive hP).totalDegree = 3) :
    ∃ k : Kind,
      contact k q.val (P.r 0) (P.r 1) (P.r 2) (P.g 0) (P.g 1) (P.g 2) ∧
      canonicalPrimitive hP = model k q.val
        (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2) := by
  rcases four_nonendpoint_cubic_cases hP ha hd with
    ⟨hb, hrs⟩ | ⟨hc, hst⟩ | ⟨hu, has⟩
  · refine ⟨.left, ⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast hb
    · exact_mod_cast hrs
    · rw [canonical_four_left_middle hP ha hb hrs, model_left]
  · refine ⟨.right, ⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast hc
    · exact_mod_cast hst
    · rw [canonical_four_right_middle hP ha hc hst, model_right]
  · refine ⟨.interval, ⟨hu, ?_⟩, ?_⟩
    · exact_mod_cast has
    · rw [canonical_four_interval_extraction hP ha hu has, model_interval]

theorem inventory_positive {k : Kind} {q a b c d r s t : ℤ}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t) :
    ∀ u ∈ positive k q a b c d r s t ++ negative k q a b c d r s t,
      ∀ i : Fin 3, 0 < u i := by
  intro u hu i
  cases k <;> dsimp [contact] at hk <;>
    dsimp [positive, negative] at hu <;> split_ifs at hu
  all_goals
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
  all_goals
    repeat' first
    | (rcases hu with hu | hu)
    | (subst u)
    | (cases hu)
  all_goals
    fin_cases i <;> dsimp at * <;>
      norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Fin.reduceFinMk] <;> dsimp [domain] at hdom <;> omega

/-- The full interval, before replacing a contacted row. -/
def cubicFullIndex (a b c d r s t : ℤ) : ℤ := a + b + c + d - r - s - t

def leadingGap (k : Kind) (s t : ℤ) : ℤ :=
  match k with
  | .right => s
  | .left | .interval => t

def leadingTriple (k : Kind) (a b c d r s t : ℤ) : Triple :=
  ![r, leadingGap k s t, cubicFullIndex a b c d r s t]

/-- The positive inventory after removing its unique full-interval term. -/
def properPositive (k : Kind) (q a b c d r s t : ℤ) : List Triple :=
  match k with
  | .left =>
      (if c = q then [] else [![c, a + q - r, d]]) ++ [![a, q + c - r, d]]
  | .right =>
      [![a, b + q - s, d]] ++ (if b = q then [] else [![a, b, q + d - s]])
  | .interval =>
      (if b + c - s = q then [] else [![s, b + c - s, d]]) ++ [![t, b, c + d - t]]

/-- The sole possible internal opposite-sign coincidence on the right chart. -/
def rightCancellation (q a d r s : ℤ) : Prop := d = r ∧ a = q + r - s

instance rightCancellationDecidable (q a d r s : ℤ) : Decidable (rightCancellation q a d r s) := by
  unfold rightCancellation
  infer_instance

def reducedPositive (k : Kind) (q a b c d r s t : ℤ) : List Triple :=
  match k with
  | .right => if rightCancellation q a d r s then [![a, b, q + d - s]]
      else properPositive .right q a b c d r s t
  | .left | .interval => properPositive k q a b c d r s t

def reducedNegative (k : Kind) (q a b c d r s t : ℤ) : List Triple :=
  match k with
  | .right => if rightCancellation q a d r s then
      [![r, a + b + q - r - s, d], ![s, a, b + q + d - 2 * s]]
      else negative .right q a b c d r s t
  | .left | .interval => negative k q a b c d r s t


theorem positive_split {k : Kind} {q a b c d r s t : ℤ}
    (hk : contact k q a b c r s t) :
    positive k q a b c d r s t =
      properPositive k q a b c d r s t ++ [leadingTriple k a b c d r s t] := by
  cases k with
  | left =>
      have hF : cubicFullIndex a b c d r s t = a + q + c + d - 2 * r - t := by
        dsimp [cubicFullIndex, contact] at *
        omega
      simp only [positive, properPositive, leadingTriple, leadingGap, hF,
        List.append_assoc, List.cons_append, List.nil_append]
  | right =>
      have hF : cubicFullIndex a b c d r s t = a + b + q + d - r - 2 * s := by
        dsimp [cubicFullIndex, contact] at *
        omega
      simp only [positive, properPositive, leadingTriple, leadingGap, hF,
        List.append_assoc, List.cons_append, List.nil_append]
  | interval =>
      have hF : cubicFullIndex a b c d r s t = q + c + d - s - t := by
        dsimp [cubicFullIndex, contact] at *
        omega
      simp only [positive, properPositive, leadingTriple, leadingGap, hF,
        List.append_assoc, List.cons_append, List.nil_append]

theorem full_index_bounds {q a b c d r s t : ℤ}
    (hdom : domain q a b c d r s t) :
    0 < cubicFullIndex a b c d r s t ∧
      r < cubicFullIndex a b c d r s t ∧ s < cubicFullIndex a b c d r s t ∧
      t < cubicFullIndex a b c d r s t := by
  dsimp [domain, cubicFullIndex] at *
  omega

theorem leadingGap_pos {q a b c d r s t : ℤ} (k : Kind)
    (hdom : domain q a b c d r s t) : 0 < leadingGap k s t := by
  cases k <;> dsimp [leadingGap, domain] at * <;> omega

theorem leadingGap_lt_full {q a b c d r s t : ℤ} (k : Kind)
    (hdom : domain q a b c d r s t) :
    leadingGap k s t < cubicFullIndex a b c d r s t := by
  have h := full_index_bounds hdom
  cases k <;> dsimp [leadingGap] <;> omega

/-- Every proper factor is strictly below the full interval, including colliding labels. -/
theorem proper_inventory_below {k : Kind} {q a b c d r s t : ℤ}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t) :
    ∀ u ∈ properPositive k q a b c d r s t ++ negative k q a b c d r s t,
      ∀ i : Fin 3, u i < cubicFullIndex a b c d r s t := by
  intro u hu i
  cases k <;> dsimp [contact] at hk <;>
    dsimp [properPositive, negative] at hu <;> split_ifs at hu
  all_goals simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
  all_goals repeat' first
  | (rcases hu with hu | hu)
  | (subst u)
  | (cases hu)
  all_goals fin_cases i <;> dsimp at * <;> dsimp [domain, cubicFullIndex] at * <;> omega

theorem proper_inventory_positive {k : Kind} {q a b c d r s t : ℤ}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t) :
    ∀ u ∈ properPositive k q a b c d r s t ++ negative k q a b c d r s t,
      ∀ i : Fin 3, 0 < u i := by
  intro u hu i
  apply inventory_positive hdom hk u _ i
  rw [positive_split hk]
  rcases List.mem_append.mp hu with hu | hu
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hu)))
  · exact List.mem_append.mpr (Or.inr hu)

theorem right_cancellation_survivors {q a b c d r s t : ℤ}
    (hdom : domain q a b c d r s t) (hk : contact .right q a b c r s t)
    (he : rightCancellation q a d r s) : b ≠ q ∧ a + b - r ≠ q := by
  rcases hdom with ⟨hq, hr, hs, ht, ha, hb, hc, hd, hane, hrne, hsne, htne⟩
  have hst := hk.2
  have hdeq := he.1
  have haeq := he.2
  constructor <;> omega

theorem reduced_positive_mem {k : Kind} {q a b c d r s t : ℤ} {x : Triple}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t)
    (hx : x ∈ reducedPositive k q a b c d r s t) :
    x ∈ properPositive k q a b c d r s t := by
  cases k with
  | left => exact hx
  | interval => exact hx
  | right =>
      by_cases he : rightCancellation q a d r s
      · have hb := (right_cancellation_survivors hdom hk he).1
        simp only [reducedPositive, if_pos he, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rw [hx]
        simp [properPositive, hb]
      · simpa only [reducedPositive, if_neg he] using hx

theorem reduced_negative_mem {k : Kind} {q a b c d r s t : ℤ} {x : Triple}
    (hx : x ∈ reducedNegative k q a b c d r s t) :
    x ∈ negative k q a b c d r s t := by
  cases k with
  | left => exact hx
  | interval => exact hx
  | right =>
      by_cases he : rightCancellation q a d r s
      · simp only [reducedNegative, if_pos he, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with hx | hx
        · rw [hx]; simp [negative]
        · rw [hx]; simp [negative]
      · simpa only [reducedNegative, if_neg he] using hx

/-- Only the unique right internal pair is canceled, with one occurrence per sign. -/
theorem reduced_parts_eq {k : Kind} {q a b c d r s t : ℤ}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t) :
    ((properPositive k q a b c d r s t).map tripleTerm).sum -
        ((negative k q a b c d r s t).map tripleTerm).sum =
      ((reducedPositive k q a b c d r s t).map tripleTerm).sum -
        ((reducedNegative k q a b c d r s t).map tripleTerm).sum := by
  cases k with
  | left => rfl
  | interval => rfl
  | right =>
      by_cases he : rightCancellation q a d r s
      · obtain ⟨hb, hu⟩ := right_cancellation_survivors hdom hk he
        have hdeq := he.1
        have haeq := he.2
        have hU : a + b - r = b + q - s := by rw [haeq]; ring
        have hA : q + d - s = a := by rw [hdeq]; exact haeq.symm
        have hword : tripleTerm ![a, b + q - s, d] =
            tripleTerm ![r, a + b - r, q + d - s] := by
          simp only [tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          rw [hU, hA, hdeq]
          ring
        simp only [reducedPositive, reducedNegative, if_pos he,
          properPositive, negative, if_neg hb, if_neg hu, List.map_append,
          List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero]
        linear_combination hword
      · simp only [reducedPositive, reducedNegative, if_neg he]


private theorem triple_derivative_zero (v : ℕ+) (T : Triple)
    (hne : ∀ i, T i ≠ (v.val : ℤ)) : MvPolynomial.pderiv v (tripleTerm T) = 0 := by
  simp only [tripleTerm, MvPolynomial.pderiv_mul, residual_pderiv_complete,
    if_neg (hne 0), if_neg (hne 1), if_neg (hne 2), zero_mul, mul_zero, zero_add]

private theorem product_derivative_top (v : ℕ+) (r g F : ℤ)
    (hr : r ≠ (v.val : ℤ)) (hg : g ≠ (v.val : ℤ)) (hF : F = (v.val : ℤ)) :
    MvPolynomial.pderiv v (complete r * complete g * complete F) =
      complete r * complete g := by
  have hr0 : MvPolynomial.pderiv v (complete r) = 0 := by
    rw [residual_pderiv_complete, if_neg hr]
  have hg0 : MvPolynomial.pderiv v (complete g) = 0 := by
    rw [residual_pderiv_complete, if_neg hg]
  have hF1 : MvPolynomial.pderiv v (complete F) = 1 := by
    rw [residual_pderiv_complete, if_pos hF]
  simp only [MvPolynomial.pderiv_mul, hr0, hg0, hF1,
    zero_mul, mul_zero, zero_add, mul_one]

private theorem product_derivative_zero (v : ℕ+) (r g F : ℤ)
    (hr : r ≠ (v.val : ℤ)) (hg : g ≠ (v.val : ℤ)) (hF : F ≠ (v.val : ℤ)) :
    MvPolynomial.pderiv v (complete r * complete g * complete F) = 0 := by
  have hr0 : MvPolynomial.pderiv v (complete r) = 0 := by
    rw [residual_pderiv_complete, if_neg hr]
  have hg0 : MvPolynomial.pderiv v (complete g) = 0 := by
    rw [residual_pderiv_complete, if_neg hg]
  have hF0 : MvPolynomial.pderiv v (complete F) = 0 := by
    rw [residual_pderiv_complete, if_neg hF]
  simp only [MvPolynomial.pderiv_mul, hr0, hg0, hF0,
    zero_mul, mul_zero, zero_add]

private theorem triple_list_derivative_zero (v : ℕ+) (L : List Triple)
    (hne : ∀ T ∈ L, ∀ i, T i ≠ (v.val : ℤ)) :
    MvPolynomial.pderiv v ((L.map tripleTerm).sum) = 0 := by
  induction L with
  | nil => simp
  | cons T L ih =>
      rw [List.map_cons, List.sum_cons, map_add,
        triple_derivative_zero v T (hne T (by simp)), ih]
      · simp
      · intro U hU i
        exact hne U (by simp [hU]) i

theorem model_split {k : Kind} {q a b c d r s t : ℤ}
    (hk : contact k q a b c r s t) :
    model k q a b c d r s t =
      ((properPositive k q a b c d r s t).map tripleTerm).sum +
        tripleTerm (leadingTriple k a b c d r s t) -
        ((negative k q a b c d r s t).map tripleTerm).sum := by
  rw [model, positive_split hk]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

theorem model_top {k : Kind} {q a b c d r s t : ℤ}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t)
    (v : ℕ+) (hv : (v.val : ℤ) = cubicFullIndex a b c d r s t) :
    MvPolynomial.pderiv v (model k q a b c d r s t) =
      complete r * complete (leadingGap k s t) := by
  have hbound := proper_inventory_below hdom hk
  have hfull := full_index_bounds hdom
  have hgap := leadingGap_lt_full k hdom
  have hp : MvPolynomial.pderiv v
      (((properPositive k q a b c d r s t).map tripleTerm).sum) = 0 := by
    apply triple_list_derivative_zero
    intro T hT i
    exact fun he => (hbound T (List.mem_append.mpr (Or.inl hT)) i).ne (he.trans hv)
  have hn : MvPolynomial.pderiv v
      (((negative k q a b c d r s t).map tripleTerm).sum) = 0 := by
    apply triple_list_derivative_zero
    intro T hT i
    exact fun he => (hbound T (List.mem_append.mpr (Or.inr hT)) i).ne (he.trans hv)
  have hrne : r ≠ (v.val : ℤ) :=
    fun he => hfull.2.1.ne (he.trans hv)
  have hgne : leadingGap k s t ≠ (v.val : ℤ) :=
    fun he => hgap.ne (he.trans hv)
  have hl : MvPolynomial.pderiv v (tripleTerm (leadingTriple k a b c d r s t)) =
      complete r * complete (leadingGap k s t) := by
    change MvPolynomial.pderiv v
      (complete r * complete (leadingGap k s t) * complete (cubicFullIndex a b c d r s t)) = _
    exact product_derivative_top v r (leadingGap k s t)
      (cubicFullIndex a b c d r s t) hrne hgne hv.symm
  rw [model_split hk, map_sub, map_add, hp, hn, hl]
  simp only [zero_add, sub_zero]

theorem model_above {k : Kind} {q a b c d r s t : ℤ}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t)
    (v : ℕ+) (hv : cubicFullIndex a b c d r s t < (v.val : ℤ)) :
    MvPolynomial.pderiv v (model k q a b c d r s t) = 0 := by
  have hbound := proper_inventory_below hdom hk
  have hfull := full_index_bounds hdom
  have hgap := leadingGap_lt_full k hdom
  have hp : MvPolynomial.pderiv v
      (((properPositive k q a b c d r s t).map tripleTerm).sum) = 0 := by
    apply triple_list_derivative_zero
    intro T hT i
    exact ((hbound T (List.mem_append.mpr (Or.inl hT)) i).trans hv).ne
  have hn : MvPolynomial.pderiv v
      (((negative k q a b c d r s t).map tripleTerm).sum) = 0 := by
    apply triple_list_derivative_zero
    intro T hT i
    exact ((hbound T (List.mem_append.mpr (Or.inr hT)) i).trans hv).ne
  have hrne : r ≠ (v.val : ℤ) := (hfull.2.1.trans hv).ne
  have hgne : leadingGap k s t ≠ (v.val : ℤ) := (hgap.trans hv).ne
  have hl : MvPolynomial.pderiv v (tripleTerm (leadingTriple k a b c d r s t)) = 0 := by
    change MvPolynomial.pderiv v
      (complete r * complete (leadingGap k s t) * complete (cubicFullIndex a b c d r s t)) = 0
    exact product_derivative_zero v r (leadingGap k s t)
      (cubicFullIndex a b c d r s t) hrne hgne hv.ne
  rw [model_split hk, map_sub, map_add, hp, hn, hl]
  simp only [zero_add, sub_zero]

/-- Actual polynomial equality recovers the private full interval and its two gap factors. -/
theorem model_leading_eq {k l : Kind} {q a b c d r s t A B C D R S T : ℤ}
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact k q a b c r s t) (hl : contact l q A B C R S T)
    (he : model k q a b c d r s t = model l q A B C D R S T) :
    cubicFullIndex a b c d r s t = cubicFullIndex A B C D R S T ∧
      ((r = R ∧ leadingGap k s t = leadingGap l S T) ∨
        (r = leadingGap l S T ∧ leadingGap k s t = R)) := by
  have hr : 0 < r := hP.2.1
  have hR : 0 < R := hQ.2.1
  have hg := leadingGap_pos k hP
  have hG := leadingGap_pos l hQ
  have htop := private_top_reading _ _
    (cubicFullIndex a b c d r s t) (cubicFullIndex A B C D R S T)
    (complete r * complete (leadingGap k s t))
    (complete R * complete (leadingGap l S T))
    (full_index_bounds hP).1 (full_index_bounds hQ).1
    (mul_ne_zero ((complete_ne_zero_iff r).mpr hr.le)
      ((complete_ne_zero_iff _).mpr hg.le))
    (mul_ne_zero ((complete_ne_zero_iff R).mpr hR.le)
      ((complete_ne_zero_iff _).mpr hG.le))
    (model_top hP hk) (model_top hQ hl)
    (model_above hP hk) (model_above hQ hl) he
  exact ⟨htop.1, complete_two_product_reading hr hg hR hG htop.2⟩

private theorem augmentation_pderiv_triple (v : ℕ+) (a b c : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    residualAugmentation (MvPolynomial.pderiv v (tripleTerm ![a, b, c])) =
      (if a = (v.val : ℤ) then 1 else 0) +
        (if b = (v.val : ℤ) then 1 else 0) +
        (if c = (v.val : ℤ) then 1 else 0) := by
  simp only [tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    MvPolynomial.pderiv_mul, map_add, map_mul, residual_pderiv_complete,
    residualAugmentation_complete ha, residualAugmentation_complete hb,
    residualAugmentation_complete hc, apply_ite, map_one, map_zero, one_mul, mul_one]
  split_ifs <;> norm_num

/-- The least nonzero derivative augmentation on every left chart is −1 at its outer gap. -/
theorem left_low_derivative (q a c d r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hq : 2 * r < q)
    (hc : r + t < c) (hd : q + t < d) (v : ℕ+)
    (hv : (v.val : ℤ) ≤ t) :
    residualAugmentation (MvPolynomial.pderiv v (model .left q a q c d r r t)) =
      -(if t = (v.val : ℤ) then (1 : ℚ) else 0) := by
  have hA : 0 < a := by omega
  have hC : 0 < c := by omega
  have hD : 0 < d := by omega
  have hU : 0 < a + q - r := by omega
  have hVgt : t < q + c - r := by omega
  have hXgt : t < a + q + c - 2 * r := by omega
  have hWgt : t < c + d - t := by omega
  have hYgt : t < q + c + d - r - t := by omega
  have hFgt : t < a + q + c + d - 2 * r - t := by omega
  have hV := ht.trans hVgt
  have hX := ht.trans hXgt
  have hW := ht.trans hWgt
  have hY := ht.trans hYgt
  have hF := ht.trans hFgt
  have hne (k : ℤ) (hk : t < k) : k ≠ (v.val : ℤ) := by
    intro he
    exact (not_lt_of_ge hv) (he ▸ hk)
  have hcn := hne c (by omega)
  have hdn := hne d (by omega)
  have hVn := hne _ hVgt
  have hXn := hne _ hXgt
  have hWn := hne _ hWgt
  have hYn := hne _ hYgt
  have hFn := hne _ hFgt
  by_cases hcq : c = q
  · have hUn : a + q - r ≠ (v.val : ℤ) := hne _ (by omega)
    simp only [model, positive, negative, if_pos hcq, List.nil_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, map_sub, map_add]
    rw [augmentation_pderiv_triple v a (q + c - r) d hA hV hD,
      augmentation_pderiv_triple v r t (a + q + c + d - 2 * r - t) hr ht hF,
      augmentation_pderiv_triple v r (a + q + c - 2 * r) d hr hX hD,
      augmentation_pderiv_triple v t (a + q - r) (c + d - t) ht hU hW,
      augmentation_pderiv_triple v t a (q + c + d - r - t) ht hA hY]
    simp only [if_neg hdn, if_neg hVn, if_neg hXn, if_neg hWn,
      if_neg hYn, if_neg hFn, if_neg hUn]
    ring
  · simp only [model, positive, negative, if_neg hcq, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, map_sub, map_add]
    rw [augmentation_pderiv_triple v c (a + q - r) d hC hU hD,
      augmentation_pderiv_triple v a (q + c - r) d hA hV hD,
      augmentation_pderiv_triple v r t (a + q + c + d - 2 * r - t) hr ht hF,
      augmentation_pderiv_triple v r (a + q + c - 2 * r) d hr hX hD,
      augmentation_pderiv_triple v t (a + q - r) (c + d - t) ht hU hW,
      augmentation_pderiv_triple v t a (q + c + d - r - t) ht hA hY]
    simp only [if_neg hcn, if_neg hdn, if_neg hVn, if_neg hXn,
      if_neg hWn, if_neg hYn, if_neg hFn]
    ring

private theorem negative_low_marker_not_lt (p f : CompleteRing) (t T : ℤ)
    (ht : 0 < t)
    (hp : ∀ v : ℕ+, (v.val : ℤ) ≤ t →
      residualAugmentation (MvPolynomial.pderiv v p) = -(if t = (v.val : ℤ) then 1 else 0))
    (hf : ∀ v : ℕ+, (v.val : ℤ) ≤ T →
      residualAugmentation (MvPolynomial.pderiv v f) = -(if T = (v.val : ℤ) then 1 else 0))
    (he : p = f) : ¬ t < T := by
  intro hlt
  let v : ℕ+ := ⟨t.toNat, by omega⟩
  have hv : (v.val : ℤ) = t := by dsimp [v]; omega
  have hc := congrArg (fun z : CompleteRing => residualAugmentation (MvPolynomial.pderiv v z)) he
  rw [hp v (le_of_eq hv), hf v ((le_of_eq hv).trans hlt.le)] at hc
  have hne : T ≠ t := ne_of_gt hlt
  norm_num [hv, hne] at hc

private theorem left_domain_bounds {q a b c d r s t : ℤ}
    (hP : domain q a b c d r s t) (hk : contact .left q a b c r s t) :
    0 < r ∧ 0 < t ∧ r < a ∧ 2 * r < q ∧ r + t < c ∧ q + t < d := by
  rcases hP with ⟨hq, hr, hs, ht, ha, hb, hc, hd, hane, hrne, hsne, htne⟩
  obtain ⟨hbq, hrs⟩ := hk
  exact ⟨hr, ht, ha, by omega, by omega, hd⟩

/-- Actual equality orders the leading gap pair; it does not assume a profile classification. -/
theorem left_outer_gap_eq {q a b c d r s t A B C D R S T : ℤ}
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact .left q a b c r s t) (hl : contact .left q A B C R S T)
    (he : model .left q a b c d r s t = model .left q A B C D R S T) : t = T := by
  obtain ⟨hr, ht, ha, hq, hc, hd⟩ := left_domain_bounds hP hk
  obtain ⟨hR, hT, hA, hQq, hC, hD⟩ := left_domain_bounds hQ hl
  have hp : ∀ v : ℕ+, (v.val : ℤ) ≤ t →
      residualAugmentation (MvPolynomial.pderiv v (model .left q a b c d r s t)) =
        -(if t = (v.val : ℤ) then 1 else 0) := by
    intro v hv
    exact left_low_derivative q a c d r t hr ht ha hq hc hd v hv
  have hf : ∀ v : ℕ+, (v.val : ℤ) ≤ T →
      residualAugmentation (MvPolynomial.pderiv v (model .left q A B C D R S T)) =
        -(if T = (v.val : ℤ) then 1 else 0) := by
    intro v hv
    exact left_low_derivative q A C D R T hR hT hA hQq hC hD v hv
  rcases lt_trichotomy t T with hlt | heq | hgt
  · exact (negative_low_marker_not_lt _ _ t T ht hp hf he hlt).elim
  · exact heq
  · exact (negative_low_marker_not_lt _ _ T t hT hf hp he.symm hgt).elim

private theorem left_negative_r_derivative (q a c d r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hq : 2 * r < q)
    (hc : r + t < c) (hd : r < d) (v : ℕ+)
    (hv : (v.val : ℤ) = r) (hrt : t ≠ r) :
    MvPolynomial.pderiv v
      (((negative .left q a q c d r r t).map tripleTerm).sum) =
      complete (a + q + c - 2 * r) * complete d := by
  have hX : a + q + c - 2 * r ≠ (v.val : ℤ) := by omega
  have hD : d ≠ (v.val : ℤ) := by omega
  have hT : t ≠ (v.val : ℤ) := by omega
  have hU : a + q - r ≠ (v.val : ℤ) := by omega
  have hW : c + d - t ≠ (v.val : ℤ) := by omega
  have hA : a ≠ (v.val : ℤ) := by omega
  have hY : q + c + d - r - t ≠ (v.val : ℤ) := by omega
  have h0 : MvPolynomial.pderiv v
      (tripleTerm ![r, a + q + c - 2 * r, d]) =
      complete (a + q + c - 2 * r) * complete d := by
    have hreorder : tripleTerm ![r, a + q + c - 2 * r, d] =
        complete (a + q + c - 2 * r) * complete d * complete r := by
      simp only [tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring
    rw [hreorder]
    exact product_derivative_top v _ _ _ hX hD hv.symm
  have h1 : MvPolynomial.pderiv v
      (tripleTerm ![t, a + q - r, c + d - t]) = 0 := by
    apply triple_derivative_zero
    intro i
    fin_cases i
    · exact hT
    · exact hU
    · exact hW
  have h2 : MvPolynomial.pderiv v
      (tripleTerm ![t, a, q + c + d - r - t]) = 0 := by
    apply triple_derivative_zero
    intro i
    fin_cases i
    · exact hT
    · exact hA
    · exact hY
  simp only [negative, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, map_add, h0, h1, h2]



/-- Removing one occurrence, not every occurrence of an equal element. -/
def pulls {α : Type*} : List α → List (α × List α)
  | [] => []
  | x :: xs => (x, xs) :: (pulls xs).map (fun p => (p.1, x :: p.2))

/-- Exact finite matching with multiplicity. -/
def matching {α : Type*} (R : α → α → Prop) : List α → List α → Prop
  | [], ys => ys = []
  | x :: xs, ys => ∃ p ∈ pulls ys, R x p.1 ∧ matching R xs p.2

theorem matching_nil_iff {α : Type*} (R : α → α → Prop) (ys : List α) :
    matching R [] ys ↔ ys = [] := Iff.rfl

theorem matching_cons_iff {α : Type*} (R : α → α → Prop)
    (x : α) (xs ys : List α) :
    matching R (x :: xs) ys ↔
      ∃ p ∈ pulls ys, R x p.1 ∧ matching R xs p.2 := Iff.rfl

theorem exists_pull {α : Type*} {x : α} {xs : List α} (hx : x ∈ xs) :
    ∃ ys, (x, ys) ∈ pulls xs := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨xs, by simp [pulls]⟩
    · obtain ⟨ys, hys⟩ := ih hx
      refine ⟨a :: ys, ?_⟩
      simp only [pulls, List.mem_cons, List.mem_map]
      exact Or.inr ⟨(x, ys), hys, rfl⟩

theorem pull_members {α : Type*} {xs : List α} {p : α × List α}
    (hp : p ∈ pulls xs) : p.1 ∈ xs ∧ ∀ x ∈ p.2, x ∈ xs := by
  induction xs generalizing p with
  | nil => simp [pulls] at hp
  | cons a xs ih =>
    simp only [pulls, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨p', hp', rfl⟩
    · exact ⟨by simp, by intro x hx; simp [hx]⟩
    · obtain ⟨hhead, htail⟩ := ih hp'
      refine ⟨by simp [hhead], ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (htail x hx)

theorem pull_length {α : Type*} {xs : List α} {p : α × List α}
    (hp : p ∈ pulls xs) : p.2.length + 1 = xs.length := by
  induction xs generalizing p with
  | nil => simp [pulls] at hp
  | cons a xs ih =>
      simp only [pulls, List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨p', hp', rfl⟩
      · simp
      · have h := ih (p := p') hp'
        simpa only [List.length_cons, Nat.succ_eq_add_one] using congrArg Nat.succ h

theorem matching_lengths {α : Type*} {R : α → α → Prop} {xs ys : List α}
    (hm : matching R xs ys) : xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
      change ys = [] at hm
      subst ys
      rfl
  | cons a xs ih =>
      obtain ⟨p, hp, hrel, htail⟩ := (matching_cons_iff _ _ _ _).mp hm
      have htailLength := ih (ys := p.2) htail
      have hpLength := pull_length hp
      simp only [List.length_cons]
      omega

theorem pull_sum {α : Type*} (f : α → CompleteRing)
    {xs : List α} {p : α × List α} (hp : p ∈ pulls xs) :
    (xs.map f).sum = f p.1 + (p.2.map f).sum := by
  induction xs generalizing p with
  | nil => simp [pulls] at hp
  | cons a xs ih =>
    simp only [pulls, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨p', hp', rfl⟩
    · simp
    · simp only [List.map_cons, List.sum_cons]
      rw [ih hp']
      abel

theorem monomial_sum_coeff_nonnegative {α : Type*}
    (e : α → ℕ+ →₀ ℕ) (xs : List α) (v : ℕ+ →₀ ℕ) :
    0 ≤ ((xs.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum).coeff v := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : 0 ≤ (MvPolynomial.monomial (e x) (1 : ℚ)).coeff v := by
      simp only [MvPolynomial.coeff_monomial]
      split_ifs <;> norm_num
    simpa using add_nonneg hx ih

theorem monomial_sum_coeff_zero {α : Type*}
    (e : α → ℕ+ →₀ ℕ) (xs : List α) (v : ℕ+ →₀ ℕ)
    (hn : ∀ x ∈ xs, e x ≠ v) :
    ((xs.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum).coeff v = 0 := by
  classical
  revert hn
  induction xs with
  | nil => intro hn; simp
  | cons x xs ih =>
    intro hn
    have hx := hn x (by simp)
    have hxs : ∀ y ∈ xs, e y ≠ v := by
      intro y hy
      exact hn y (by simp [hy])
    simp [hx, ih hxs]

private theorem monomial_coeff_disjoint_zero {α : Type*}
    (e : α → ℕ+ →₀ ℕ) (xs ys : List α)
    (hdis : ∀ x ∈ xs, ∀ y ∈ ys, e x ≠ e y) (v : ℕ+ →₀ ℕ) :
    ((xs.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum).coeff v = 0 ∨
      ((ys.map (fun y => (MvPolynomial.monomial (e y) 1 : CompleteRing))).sum).coeff v = 0 := by
  classical
  by_cases hx0 :
      ((xs.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum).coeff v = 0
  · exact Or.inl hx0
  · right
    apply monomial_sum_coeff_zero e ys v
    intro y hy hyv
    have hex : ∃ x ∈ xs, e x = v := by
      by_contra hn
      apply hx0
      apply monomial_sum_coeff_zero e xs v
      intro x hx hxv
      exact hn ⟨x, hx, hxv⟩
    obtain ⟨x, hx, hxv⟩ := hex
    exact hdis x hx y hy (hxv.trans hyv.symm)

private theorem nonnegative_disjoint_parts_unique (p n q m : ℚ)
    (hp : 0 ≤ p) (hn : 0 ≤ n) (hq : 0 ≤ q) (hm : 0 ≤ m)
    (hpn : p = 0 ∨ n = 0) (hqm : q = 0 ∨ m = 0)
    (he : p + m = n + q) : p = q ∧ n = m := by
  rcases hpn with hp0 | hn0 <;> rcases hqm with hq0 | hm0 <;>
    constructor <;> linarith

/-- Coefficientwise uniqueness of disjoint positive and negative parts.
Repeated monomials within either sign are retained with their full multiplicity. -/
theorem signed_monomial_parts_unique {α : Type*}
    (e : α → ℕ+ →₀ ℕ) (PP NP PQ NQ : List α)
    (hP : ∀ x ∈ PP, ∀ y ∈ NP, e x ≠ e y)
    (hQ : ∀ x ∈ PQ, ∀ y ∈ NQ, e x ≠ e y)
    (he :
      (PP.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum +
        (NQ.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum =
      (NP.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum +
        (PQ.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum) :
    (PP.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum =
        (PQ.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum ∧
      (NP.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum =
        (NQ.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum := by
  have hcoeff (v : ℕ+ →₀ ℕ) :
      ((PP.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum).coeff v =
          ((PQ.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum).coeff v ∧
        ((NP.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum).coeff v =
          ((NQ.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum).coeff v := by
    have hec := congrArg (fun p : CompleteRing => p.coeff v) he
    simp only [MvPolynomial.coeff_add] at hec
    exact nonnegative_disjoint_parts_unique _ _ _ _
      (monomial_sum_coeff_nonnegative e PP v) (monomial_sum_coeff_nonnegative e NP v)
      (monomial_sum_coeff_nonnegative e PQ v) (monomial_sum_coeff_nonnegative e NQ v)
      (monomial_coeff_disjoint_zero e PP NP hP v)
      (monomial_coeff_disjoint_zero e PQ NQ hQ v) hec
  constructor
  · apply MvPolynomial.ext
    intro v
    exact (hcoeff v).1
  · apply MvPolynomial.ext
    intro v
    exact (hcoeff v).2


/-- Polynomial equality supplies the matching; it is not a caller certificate. -/
theorem monomial_matching {α : Type*}
    (e : α → ℕ+ →₀ ℕ) (R : α → α → Prop) (xs ys : List α)
    (hread : ∀ x ∈ xs, ∀ y ∈ ys, e x = e y → R x y)
    (he : (xs.map (fun x => (MvPolynomial.monomial (e x) 1 : CompleteRing))).sum =
      (ys.map (fun y => (MvPolynomial.monomial (e y) 1 : CompleteRing))).sum) :
    matching R xs ys := by
  classical
  revert ys
  induction xs with
  | nil =>
    intro ys hread he
    cases ys with
    | nil => rfl
    | cons y ys =>
      have hn := monomial_sum_coeff_nonnegative e ys (e y)
      have hc := congrArg (fun p : CompleteRing => p.coeff (e y)) he
      simp at hc
      linarith
  | cons x xs ih =>
    intro ys hread he
    have hx : ∃ y ∈ ys, e y = e x := by
      by_contra hn
      push_neg at hn
      have hz := monomial_sum_coeff_zero e ys (e x) hn
      have hp := monomial_sum_coeff_nonnegative e xs (e x)
      have hc := congrArg (fun p : CompleteRing => p.coeff (e x)) he
      have hc' :
          1 + ((xs.map (fun z => (MvPolynomial.monomial (e z) 1 : CompleteRing))).sum).coeff
            (e x) = 0 := by
        simpa [hz] using hc
      linarith
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨zs, hzs⟩ := exists_pull hy
    have hsum := pull_sum
      (fun z => (MvPolynomial.monomial (e z) 1 : CompleteRing)) hzs
    have htail :
        (xs.map (fun z => (MvPolynomial.monomial (e z) 1 : CompleteRing))).sum =
          (zs.map (fun z => (MvPolynomial.monomial (e z) 1 : CompleteRing))).sum := by
      have hh := he
      simp only [List.map_cons, List.sum_cons] at hh
      rw [hsum, hxy] at hh
      exact add_left_cancel hh
    refine ⟨(y, zs), hzs, hread x (by simp) y hy hxy.symm, ?_⟩
    apply ih zs _ htail
    intro z hz w hw hzw
    exact hread z (by simp [hz]) w ((pull_members hzs).2 w hw) hzw

def tripleRelation (x y : Triple) : Prop :=
  FourRowHessenberg.tripleMatch (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)

theorem triple_reading (x y : Triple) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (he : tripleTerm x = tripleTerm y) : tripleRelation x y := by
  exact residual_triple_product_reading (hx 0) (hx 1) (hx 2)
    (hy 0) (hy 1) (hy 2) he

theorem sum_triple_monomial (xs : List Triple)
    (hx : ∀ x ∈ xs, ∀ i, 0 < x i) :
    (xs.map tripleTerm).sum =
      (xs.map (fun x => (MvPolynomial.monomial (tripleExponent x) 1 : CompleteRing))).sum := by
  revert hx
  induction xs with
  | nil => intro hx; simp
  | cons x xs ih =>
    intro hx
    have hhead := hx x (by simp)
    have htail : ∀ y ∈ xs, ∀ i, 0 < y i := by
      intro y hy i
      exact hx y (by simp [hy]) i
    simp [tripleTerm_monomial x hhead, ih htail]

theorem triple_matching (xs ys : List Triple)
    (hx : ∀ x ∈ xs, ∀ i, 0 < x i)
    (hy : ∀ y ∈ ys, ∀ i, 0 < y i)
    (he : (xs.map tripleTerm).sum = (ys.map tripleTerm).sum) :
    matching tripleRelation xs ys := by
  apply monomial_matching tripleExponent tripleRelation xs ys
  · intro x hxx y hyy hexp
    apply triple_reading x y (hx x hxx) (hy y hyy)
    rw [tripleTerm_monomial x (hx x hxx), tripleTerm_monomial y (hy y hyy), hexp]
  · rw [← sum_triple_monomial xs hx, ← sum_triple_monomial ys hy]
    exact he

theorem triple_relation_term_eq {x y : Triple} (h : tripleRelation x y) :
    tripleTerm x = tripleTerm y := by
  unfold tripleRelation FourRowHessenberg.tripleMatch at h
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  all_goals unfold tripleTerm
  all_goals rw [h0, h1, h2] <;> ring

private theorem matching_term_sum_eq {xs ys : List Triple}
    (hm : matching tripleRelation xs ys) : (xs.map tripleTerm).sum = (ys.map tripleTerm).sum := by
  induction xs generalizing ys with
  | nil =>
      change ys = [] at hm
      subst ys
      rfl
  | cons x xs ih =>
      obtain ⟨p, hp, hrel, htail⟩ := (matching_cons_iff _ _ _ _).mp hm
      rw [List.map_cons, List.sum_cons, triple_relation_term_eq hrel,
        ih (ys := p.2) htail]
      exact (pull_sum tripleTerm hp).symm

private theorem matching_one_reading {x y : Triple}
    (hm : matching tripleRelation [x] [y]) : tripleRelation x y := by
  simpa [matching, pulls] using hm

private theorem matching_two_reading {x0 x1 y0 y1 : Triple}
    (hm : matching tripleRelation [x0, x1] [y0, y1]) :
    (tripleRelation x0 y0 ∧ tripleRelation x1 y1) ∨
      (tripleRelation x0 y1 ∧ tripleRelation x1 y0) := by
  simpa [matching, pulls] using hm

private theorem triple_relation_third_mem {x y : Triple} (h : tripleRelation x y) :
    x 2 = y 0 ∨ x 2 = y 1 ∨ x 2 = y 2 := by
  unfold tripleRelation FourRowHessenberg.tripleMatch at h
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> omega

private theorem shifted_word_eq_iff (δ a c d : ℤ) (hδ : 0 < δ)
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) :
    tripleTerm ![c, a + δ, d] = tripleTerm ![a, c + δ, d] ↔ a = c := by
  constructor
  · intro he
    have hpair : complete c * complete (a + δ) = complete a * complete (c + δ) := by
      apply mul_right_cancel₀ ((complete_ne_zero_iff d).mpr hd.le)
      simpa only [tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] using he
    have hr := complete_two_product_reading hc (add_pos ha hδ) ha (add_pos hc hδ) hpair
    rcases hr with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact h0.symm
    · omega
  · intro he
    rw [he]

private theorem shifted_words_degeneracy_iff (δ a c d A C D : ℤ) (hδ : 0 < δ)
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hC : 0 < C) (hD : 0 < D)
    (hm : matching tripleRelation [![c, a + δ, d], ![a, c + δ, d]]
      [![C, A + δ, D], ![A, C + δ, D]]) : a = c ↔ A = C := by
  have hread := matching_two_reading hm
  constructor
  · intro hac
    have hx := (shifted_word_eq_iff δ a c d hδ ha hc hd).mpr hac
    apply (shifted_word_eq_iff δ A C D hδ hA hC hD).mp
    rcases hread with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact (triple_relation_term_eq h0).symm.trans (hx.trans (triple_relation_term_eq h1))
    · exact (triple_relation_term_eq h1).symm.trans (hx.symm.trans (triple_relation_term_eq h0))
  · intro hAC
    have hy := (shifted_word_eq_iff δ A C D hδ hA hC hD).mpr hAC
    apply (shifted_word_eq_iff δ a c d hδ ha hc hd).mp
    rcases hread with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact (triple_relation_term_eq h0).trans (hy.trans (triple_relation_term_eq h1).symm)
    · exact (triple_relation_term_eq h0).trans (hy.symm.trans (triple_relation_term_eq h1).symm)

private theorem common_shifted_origin (δ A C d D : ℤ) (hδ : 0 < δ) (hAC : A ≠ C)
    (h0 : d = C ∨ d = A + δ ∨ d = D)
    (h1 : d = A ∨ d = C + δ ∨ d = D) : d = D := by
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;> omega

private theorem shifted_words_origin (δ a c d A C D : ℤ) (hδ : 0 < δ) (hAC : A ≠ C)
    (hm : matching tripleRelation [![c, a + δ, d], ![a, c + δ, d]]
      [![C, A + δ, D], ![A, C + δ, D]]) : d = D := by
  rcases matching_two_reading hm with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hd0 := triple_relation_third_mem h0
    have hd1 := triple_relation_third_mem h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hd0 hd1
    exact common_shifted_origin δ A C d D hδ hAC hd0 hd1
  · have hd0 := triple_relation_third_mem h1
    have hd1 := triple_relation_third_mem h0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hd0 hd1
    exact common_shifted_origin δ A C d D hδ hAC hd0 hd1

private theorem shifted_tail_swap_not_lt (δ a c d t : ℤ)
    (hδ : 0 < δ) (ha : 0 < a) (hc : 0 < c) (hd : t < d) (hac : a < c)
    (he :
      complete (a + δ) * complete (c + d - t) +
          complete a * complete (c + d - t + δ) =
        complete (c + δ) * complete (a + d - t) +
          complete c * complete (a + d - t + δ)) : False := by
  let K := c + d - t + δ
  let v : ℕ+ := ⟨K.toNat, by dsimp [K]; omega⟩
  have hv : (v.val : ℤ) = K := by dsimp [v]; omega
  have hnA : a ≠ (v.val : ℤ) := by dsimp [K] at hv; omega
  have hnU : a + δ ≠ (v.val : ℤ) := by dsimp [K] at hv; omega
  have hnC : c ≠ (v.val : ℤ) := by dsimp [K] at hv; omega
  have hnV : c + δ ≠ (v.val : ℤ) := by dsimp [K] at hv; omega
  have hnW : c + d - t ≠ (v.val : ℤ) := by dsimp [K] at hv; omega
  have hnX : a + d - t ≠ (v.val : ℤ) := by dsimp [K] at hv; omega
  have hnY : a + d - t + δ ≠ (v.val : ℤ) := by dsimp [K] at hv; omega
  have hK : c + d - t + δ = (v.val : ℤ) := hv.symm
  have he' := congrArg (MvPolynomial.pderiv v) he
  simp only [map_add, MvPolynomial.pderiv_mul, residual_pderiv_complete,
    if_neg hnA, if_neg hnU, if_neg hnC, if_neg hnV, if_neg hnW,
    if_neg hnX, if_neg hnY, if_pos hK, zero_mul, mul_zero, zero_add,
    add_zero, mul_one] at he'
  exact ((complete_ne_zero_iff a).mpr ha.le) he'

private theorem shifted_tail_swap_eq (δ a c d t : ℤ)
    (hδ : 0 < δ) (ha : 0 < a) (hc : 0 < c) (hd : t < d)
    (he :
      complete (a + δ) * complete (c + d - t) +
          complete a * complete (c + d - t + δ) =
        complete (c + δ) * complete (a + d - t) +
          complete c * complete (a + d - t + δ)) : a = c := by
  rcases lt_trichotomy a c with hac | hac | hac
  · exact (shifted_tail_swap_not_lt δ a c d t hδ ha hc hd hac he).elim
  · exact hac
  · exact (shifted_tail_swap_not_lt δ c a d t hδ hc ha hd hac he.symm).elim

private theorem shifted_pair_decomposition (δ a d A D : ℤ) (hδ : 0 < δ)
    (h : tripleRelation ![a, a + δ, d] ![A, A + δ, D]) :
    (a = A ∧ d = D) ∨
      (d = a + 2 * δ ∧ A = a + δ ∧ D = a) ∨
      (a = A + δ ∧ D = A + 2 * δ ∧ d = A) := by
  unfold tripleRelation FourRowHessenberg.tripleMatch at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> omega

private theorem left_negative_pair_eq (q a c d A C D r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hq : 2 * r < q)
    (hc : r + t < c) (hd : r < d)
    (hA : r < A) (hC : r + t < C) (hD : r < D)
    (hrt : t ≠ r)
    (he : ((negative .left q a q c d r r t).map tripleTerm).sum =
      ((negative .left q A q C D r r t).map tripleTerm).sum) :
    (a + q + c - 2 * r = A + q + C - 2 * r ∧ d = D) ∨
      (a + q + c - 2 * r = D ∧ d = A + q + C - 2 * r) := by
  let v : ℕ+ := ⟨r.toNat, by omega⟩
  have hv : (v.val : ℤ) = r := by dsimp [v]; omega
  have he := congrArg (MvPolynomial.pderiv v) he
  rw [left_negative_r_derivative q a c d r t hr ht ha hq hc hd v hv hrt,
    left_negative_r_derivative q A C D r t hr ht hA hq hC hD v hv hrt] at he
  exact complete_two_product_reading (by omega) (by omega)
    (by omega) (by omega) he

private theorem left_ap_equal_gaps (q a d A D r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r + t < a) (hq : 2 * r < q)
    (hd : r < d) (hA : r + t < A) (hD : r < D)
    (hap : d = a + 2 * (q - r) ∧ A = a + (q - r) ∧ D = a)
    (he : ((negative .left q a q a d r r t).map tripleTerm).sum =
      ((negative .left q A q A D r r t).map tripleTerm).sum) : r = t := by
  by_contra hrt
  have hread := left_negative_pair_eq q a a d A A D r t hr ht
    (by omega) hq ha hd (by omega) hA hD (Ne.symm hrt) he
  rcases hap with ⟨hdEq, hAEq, hDEq⟩
  rcases hread with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega


private theorem mem_optional_singleton {α : Type*} {P : Prop} [Decidable P]
    {x y : α} (hx : x ∈ (if P then [] else [y])) : x = y := by
  by_cases hP : P
  · simp only [if_pos hP, List.not_mem_nil] at hx
  · simpa only [if_neg hP, List.mem_cons, List.not_mem_nil, or_false] using hx

/-- Opposite signs are disjoint after the unique right pair has been removed. -/
theorem reduced_sign_disjoint {k : Kind} {q a b c d r s t : ℤ}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t)
    {x y : Triple} (hx : x ∈ reducedPositive k q a b c d r s t)
    (hy : y ∈ reducedNegative k q a b c d r s t) : ¬ tripleRelation x y := by
  have hyO := reduced_negative_mem hy
  rcases hdom with ⟨hq, hr, hs, ht, ha, hb, hc, hd, hane, hrne, hsne, htne⟩
  cases k with
  | left =>
      obtain ⟨hbq, hrs⟩ := hk
      have hqc : 2 * r < q := by omega
      have hcc : r + t < c := by omega
      have hxw : ∃ i : Fin 3, x = leftMiddlePositive q a c d r t i := by
        change x ∈ properPositive .left q a b c d r s t at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨0, mem_optional_singleton hx⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact ⟨1, hx⟩
      have hyw : ∃ j : Fin 3, y = leftMiddleNegative q a c d r t j := by
        simp only [negative, List.mem_cons, List.not_mem_nil, or_false] at hyO
        rcases hyO with hy | hy | hy
        · exact ⟨0, hy⟩
        · exact ⟨1, hy⟩
        · exact ⟨2, hy⟩
      obtain ⟨i, rfl⟩ := hxw
      obtain ⟨j, rfl⟩ := hyw
      intro he
      exact left_middle_opposite_ne q a c d r t hr ht ha hqc hcc hd i j
        (triple_relation_term_eq he)
  | interval =>
      obtain ⟨hu, has⟩ := hk
      have hrs : r < s := by omega
      have hU : s + b - r = q := by omega
      have hxw : ∃ i : Fin 3, x = intervalPositive q b c d r s t i := by
        change x ∈ properPositive .interval q a b c d r s t at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨0, mem_optional_singleton hx⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact ⟨1, hx⟩
      have hyw : ∃ j : Fin 3, y = intervalNegative q b c d r s t j := by
        change y ∈ (if c = q then [] else [![b, c, d]]) ++
          [![r, q + c - s, d], ![s, t, b + c + d - s - t]] at hyO
        rcases List.mem_append.mp hyO with hy | hy
        · exact ⟨0, mem_optional_singleton hy⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with hy | hy
          · exact ⟨1, hy⟩
          · exact ⟨2, hy⟩
      obtain ⟨i, rfl⟩ := hxw
      obtain ⟨j, rfl⟩ := hyw
      intro he
      exact interval_opposite_ne q b c d r s t hr hrs ht hb hU hc hd i j
        (triple_relation_term_eq he)
  | right =>
      obtain ⟨hcq, hst⟩ := hk
      have hqc : 2 * s < q := by omega
      have hdd : q + s < d := by omega
      have hxw : ∃ i : Fin 3, x = rightMiddlePositive q a b d r s i ∧
          (i = 1 ∨ ¬ rightCancellation q a d r s) := by
        by_cases hcancel : rightCancellation q a d r s
        · simp only [reducedPositive, if_pos hcancel, List.mem_cons,
            List.not_mem_nil, or_false] at hx
          exact ⟨1, hx, Or.inl rfl⟩
        · simp only [reducedPositive, if_neg hcancel] at hx
          rcases List.mem_append.mp hx with hx | hx
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            exact ⟨0, hx, Or.inr hcancel⟩
          · exact ⟨1, mem_optional_singleton hx, Or.inr hcancel⟩
      have hyw : ∃ j : Fin 3, y = rightMiddleNegative q a b d r s j := by
        change y ∈ ([![r, a + b + q - r - s, d]] ++
          (if a + b - r = q then [] else [![r, a + b - r, q + d - s]])) ++
          [![s, a, b + q + d - 2 * s]] at hyO
        rcases List.mem_append.mp hyO with hy | hy
        · rcases List.mem_append.mp hy with hy | hy
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            exact ⟨0, hy⟩
          · exact ⟨1, mem_optional_singleton hy⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          exact ⟨2, hy⟩
      obtain ⟨i, rfl, htag⟩ := hxw
      obtain ⟨j, rfl⟩ := hyw
      intro he
      have hlocus := right_middle_opposite_locus q a b d r s hr hs ha hb hqc hdd i j
        (triple_relation_term_eq he)
      rcases htag with hi | hn
      · have hbad : (1 : Fin 3) = 0 := hi.symm.trans hlocus.1
        exact (by decide : (1 : Fin 3) ≠ 0) hbad
      · exact hn ⟨hlocus.2.2.1, hlocus.2.2.2⟩

/-- Jordan uniqueness yields separate exact matchings of both signed inventories. -/
theorem signed_triple_matching (PP NP PQ NQ : List Triple)
    (hP : ∀ x ∈ PP ++ NP, ∀ i, 0 < x i)
    (hQ : ∀ x ∈ PQ ++ NQ, ∀ i, 0 < x i)
    (hdP : ∀ x ∈ PP, ∀ y ∈ NP, ¬ tripleRelation x y)
    (hdQ : ∀ x ∈ PQ, ∀ y ∈ NQ, ¬ tripleRelation x y)
    (he : (PP.map tripleTerm).sum + (NQ.map tripleTerm).sum =
      (NP.map tripleTerm).sum + (PQ.map tripleTerm).sum) :
    matching tripleRelation PP PQ ∧ matching tripleRelation NP NQ := by
  have hpP (x : Triple) (hx : x ∈ PP) := hP x (List.mem_append.mpr (Or.inl hx))
  have hnP (x : Triple) (hx : x ∈ NP) := hP x (List.mem_append.mpr (Or.inr hx))
  have hpQ (x : Triple) (hx : x ∈ PQ) := hQ x (List.mem_append.mpr (Or.inl hx))
  have hnQ (x : Triple) (hx : x ∈ NQ) := hQ x (List.mem_append.mpr (Or.inr hx))
  have hdisP : ∀ x ∈ PP, ∀ y ∈ NP, tripleExponent x ≠ tripleExponent y := by
    intro x hx y hy hexp
    apply hdP x hx y hy
    apply triple_reading x y (hpP x hx) (hnP y hy)
    rw [tripleTerm_monomial x (hpP x hx), tripleTerm_monomial y (hnP y hy), hexp]
  have hdisQ : ∀ x ∈ PQ, ∀ y ∈ NQ, tripleExponent x ≠ tripleExponent y := by
    intro x hx y hy hexp
    apply hdQ x hx y hy
    apply triple_reading x y (hpQ x hx) (hnQ y hy)
    rw [tripleTerm_monomial x (hpQ x hx), tripleTerm_monomial y (hnQ y hy), hexp]
  rw [sum_triple_monomial PP hpP, sum_triple_monomial NP hnP,
    sum_triple_monomial PQ hpQ, sum_triple_monomial NQ hnQ] at he
  have hparts := signed_monomial_parts_unique tripleExponent PP NP PQ NQ hdisP hdisQ he
  constructor
  · apply triple_matching PP PQ hpP hpQ
    rw [sum_triple_monomial PP hpP, sum_triple_monomial PQ hpQ]
    exact hparts.1
  · apply triple_matching NP NQ hnP hnQ
    rw [sum_triple_monomial NP hnP, sum_triple_monomial NQ hnQ]
    exact hparts.2



/-- Cancel one matched positive minimum, never all occurrences of its monomial. -/
theorem triple_signed_cancel_positive (PP NP PQ NQ : List Triple)
    (hP : ∀ x ∈ PP ++ NP, ∀ i, 0 < x i)
    (hQ : ∀ x ∈ PQ ++ NQ, ∀ i, 0 < x i)
    (he : (PP.map tripleTerm).sum + (NQ.map tripleTerm).sum =
      (NP.map tripleTerm).sum + (PQ.map tripleTerm).sum)
    (p u : Triple × List Triple) (hp : p ∈ pulls PP) (hu : u ∈ pulls PQ)
    (hrel : tripleRelation p.1 u.1) :
    matching tripleRelation (p.2 ++ NQ) (NP ++ u.2) := by
  apply triple_matching
  · intro x hx i
    rcases List.mem_append.mp hx with hx | hx
    · exact hP x (List.mem_append.mpr (Or.inl ((pull_members hp).2 x hx))) i
    · exact hQ x (List.mem_append.mpr (Or.inr hx)) i
  · intro x hx i
    rcases List.mem_append.mp hx with hx | hx
    · exact hP x (List.mem_append.mpr (Or.inr hx)) i
    · exact hQ x (List.mem_append.mpr (Or.inl ((pull_members hu).2 x hx))) i
  · simp only [List.map_append, List.sum_append]
    rw [pull_sum tripleTerm hp, pull_sum tripleTerm hu] at he
    have hword := triple_relation_term_eq hrel
    linear_combination he - hword

/-- The negative minimum is canceled in the opposite two unsigned inventories. -/
theorem triple_signed_cancel_negative (PP NP PQ NQ : List Triple)
    (hP : ∀ x ∈ PP ++ NP, ∀ i, 0 < x i)
    (hQ : ∀ x ∈ PQ ++ NQ, ∀ i, 0 < x i)
    (he : (PP.map tripleTerm).sum + (NQ.map tripleTerm).sum =
      (NP.map tripleTerm).sum + (PQ.map tripleTerm).sum)
    (p u : Triple × List Triple) (hp : p ∈ pulls NP) (hu : u ∈ pulls NQ)
    (hrel : tripleRelation p.1 u.1) :
    matching tripleRelation (PP ++ u.2) (p.2 ++ PQ) := by
  apply triple_matching
  · intro x hx i
    rcases List.mem_append.mp hx with hx | hx
    · exact hP x (List.mem_append.mpr (Or.inl hx)) i
    · exact hQ x (List.mem_append.mpr (Or.inr ((pull_members hu).2 x hx))) i
  · intro x hx i
    rcases List.mem_append.mp hx with hx | hx
    · exact hP x (List.mem_append.mpr (Or.inr ((pull_members hp).2 x hx))) i
    · exact hQ x (List.mem_append.mpr (Or.inl hx)) i
  · simp only [List.map_append, List.sum_append]
    rw [pull_sum tripleTerm hp, pull_sum tripleTerm hu] at he
    have hword := triple_relation_term_eq hrel
    linear_combination he + hword

/-- Square weight of an actual normalized three-factor word. -/
def wordWeight (T : Triple) : ℤ := (T 0) ^ 2 + (T 1) ^ 2 + (T 2) ^ 2

def minimalPositive (k : Kind) (q a b c d r s t : ℤ) : List Triple :=
  match k with
  | .left | .right => properPositive k q a b c d r s t
  | .interval => if c = q then properPositive .interval q a b c d r s t else []

def minimalNegative (k : Kind) (q a b c d r s t : ℤ) : List Triple :=
  match k with
  | .left => if c = q then [![t, a + q - r, c + d - t]] else []
  | .right => if b = q then [![r, a + b - r, q + d - s]] else []
  | .interval => if c = q then [] else [![b, c, d]]

/-- Adding a seam strictly increases square weight under thickness. -/
theorem join_weight_strict (U V g : ℤ) (hU : g < U) (hV : g < V) :
    U ^ 2 + V ^ 2 < g ^ 2 + (U + V - g) ^ 2 := by
  have hp := mul_pos (sub_pos.mpr hU) (sub_pos.mpr hV)
  nlinarith

theorem wordWeight_vec (a b c : ℤ) : wordWeight ![a, b, c] = a ^ 2 + b ^ 2 + c ^ 2 := rfl

/-- Every globally minimal positive word is among the minimal surviving cuts. -/
theorem minimal_positive_promotion {k : Kind} {q a b c d r s t : ℤ} {x : Triple}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t)
    (hx : x ∈ properPositive k q a b c d r s t)
    (hmin : ∀ z ∈ minimalPositive k q a b c d r s t ++
      minimalNegative k q a b c d r s t, wordWeight x ≤ wordWeight z) :
    x ∈ minimalPositive k q a b c d r s t := by
  cases k with
  | left => exact hx
  | right => exact hx
  | interval =>
      by_cases hcq : c = q
      · simpa only [minimalPositive, if_pos hcq] using hx
      · obtain ⟨hq, hr, hs, ht, ha, hb, hc, hd, hane, hrne, hsne, htne⟩ := hdom
        obtain ⟨hu, has⟩ := hk
        have hm := hmin ![b, c, d] (by simp [minimalPositive, minimalNegative, hcq])
        simp only [properPositive, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with hx | hx
        · by_cases hvq : b + c - s = q
          · simp only [if_pos hvq, List.not_mem_nil] at hx
          · simp only [if_neg hvq, List.mem_cons, List.not_mem_nil, or_false] at hx
            subst x
            exfalso
            rw [wordWeight_vec, wordWeight_vec] at hm
            have hj := join_weight_strict b c s (by omega) (by omega)
            nlinarith only [hm, hj]
        · subst x
          exfalso
          rw [wordWeight_vec, wordWeight_vec] at hm
          have hj := join_weight_strict c d t (by omega) (by omega)
          nlinarith only [hm, hj]

/-- The negative-word cover follows from one or two strictly positive joins. -/
theorem minimal_negative_promotion {k : Kind} {q a b c d r s t : ℤ} {x : Triple}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t)
    (hx : x ∈ negative k q a b c d r s t)
    (hmin : ∀ z ∈ minimalPositive k q a b c d r s t ++
      minimalNegative k q a b c d r s t, wordWeight x ≤ wordWeight z) :
    x ∈ minimalNegative k q a b c d r s t := by
  obtain ⟨hq, hr, hs, ht, ha, hb, hc, hd, hane, hrne, hsne, htne⟩ := hdom
  cases k with
  | left =>
      obtain ⟨hbq, hrs⟩ := hk
      have hm1 := hmin ![a, q + c - r, d] (by simp [minimalPositive, properPositive])
      simp only [negative, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx
      · subst x
        exfalso
        rw [wordWeight_vec, wordWeight_vec] at hm1
        have hj := join_weight_strict a (q + c - r) r ha (by omega)
        nlinarith only [hm1, hj]
      · subst x
        by_cases hcq : c = q
        · simp [minimalNegative, hcq]
        · have hm0 := hmin ![c, a + q - r, d] (by
            simp [minimalPositive, properPositive, hcq])
          exfalso
          rw [wordWeight_vec, wordWeight_vec] at hm0
          have hj := join_weight_strict c d t (by omega) (by omega)
          nlinarith only [hm0, hj]
      · subst x
        exfalso
        rw [wordWeight_vec, wordWeight_vec] at hm1
        have hj := join_weight_strict (q + c - r) d t (by omega) (by omega)
        nlinarith only [hm1, hj]
  | right =>
      obtain ⟨hcq, hst⟩ := hk
      have hm0 := hmin ![a, b + q - s, d] (by simp [minimalPositive, properPositive])
      simp only [negative, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (hx | hx) | hx
      · subst x
        exfalso
        rw [wordWeight_vec, wordWeight_vec] at hm0
        have hj := join_weight_strict a (b + q - s) r ha (by omega)
        nlinarith only [hm0, hj]
      · by_cases huq : a + b - r = q
        · simp only [if_pos huq, List.not_mem_nil] at hx
        · simp only [if_neg huq, List.mem_cons, List.not_mem_nil, or_false] at hx
          subst x
          by_cases hbq : b = q
          · simp [minimalNegative, hbq]
          · have hm1 := hmin ![a, b, q + d - s] (by
              simp [minimalPositive, properPositive, hbq])
            exfalso
            rw [wordWeight_vec, wordWeight_vec] at hm1
            have hj := join_weight_strict a b r ha (by omega)
            nlinarith only [hm1, hj]
      · subst x
        exfalso
        rw [wordWeight_vec, wordWeight_vec] at hm0
        have hj := join_weight_strict (b + q - s) d s (by omega) (by omega)
        nlinarith only [hm0, hj]
  | interval =>
      obtain ⟨hu, has⟩ := hk
      have hQ : q = s + b - r := by omega
      simp only [negative, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx
      · by_cases hcq : c = q
        · simp only [if_pos hcq, List.not_mem_nil] at hx
        · simp only [if_neg hcq, List.mem_cons, List.not_mem_nil, or_false] at hx
          subst x
          simp [minimalNegative, hcq]
      · subst x
        by_cases hcq : c = q
        · have hvq : b + c - s ≠ q := by omega
          have hm0 := hmin ![s, b + c - s, d] (by
            simp only [minimalPositive, minimalNegative, if_pos hcq, properPositive,
              if_neg hvq, List.mem_append, List.mem_cons, List.not_mem_nil,
              or_false, true_or, or_true])
          exfalso
          rw [wordWeight_vec, wordWeight_vec, hQ] at hm0
          have hj := join_weight_strict s (b + c - s) r (by omega) (by omega)
          nlinarith only [hm0, hj]
        · have hm0 := hmin ![b, c, d] (by
            simp [minimalPositive, minimalNegative, hcq])
          exfalso
          rw [wordWeight_vec, wordWeight_vec, hQ] at hm0
          have hj := join_weight_strict b c r (by omega) (by omega)
          nlinarith only [hm0, hj]
      · subst x
        by_cases hcq : c = q
        · have hm1 := hmin ![t, b, c + d - t] (by
            simp [minimalPositive, properPositive, hcq])
          exfalso
          rw [wordWeight_vec, wordWeight_vec] at hm1
          have hj := join_weight_strict b (c + d - t) s (by omega) (by omega)
          nlinarith only [hm1, hj]
        · have hm0 := hmin ![b, c, d] (by
            simp [minimalPositive, minimalNegative, hcq])
          exfalso
          rw [wordWeight_vec, wordWeight_vec] at hm0
          have hj1 := join_weight_strict b c s (by omega) (by omega)
          have hj2 := join_weight_strict (b + c - s) d t (by omega) (by omega)
          nlinarith only [hm0, hj1, hj2]


theorem minimal_candidates_nonempty (k : Kind) (q a b c d r s t : ℤ) :
    minimalPositive k q a b c d r s t ++ minimalNegative k q a b c d r s t ≠ [] := by
  cases k <;> dsimp [minimalPositive, minimalNegative, properPositive]
  all_goals split_ifs <;> simp

theorem minimal_positive_mem {k : Kind} {q a b c d r s t : ℤ} {x : Triple}
    (hx : x ∈ minimalPositive k q a b c d r s t) :
    x ∈ properPositive k q a b c d r s t := by
  cases k with
  | left => exact hx
  | right => exact hx
  | interval =>
      by_cases hc : c = q
      · simpa only [minimalPositive, if_pos hc] using hx
      · simp only [minimalPositive, if_neg hc, List.not_mem_nil] at hx

theorem minimal_negative_mem {k : Kind} {q a b c d r s t : ℤ} {x : Triple}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t)
    (hx : x ∈ minimalNegative k q a b c d r s t) :
    x ∈ negative k q a b c d r s t := by
  cases k with
  | left =>
      by_cases hc : c = q
      · simp only [minimalNegative, if_pos hc, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rw [hx]
        simp [negative]
      · simp only [minimalNegative, if_neg hc, List.not_mem_nil] at hx
  | right =>
      by_cases hb : b = q
      · have hu : a + b - r ≠ q := by dsimp [domain] at hdom; omega
        simp only [minimalNegative, if_pos hb, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rw [hx]
        simp [negative, hu]
      · simp only [minimalNegative, if_neg hb, List.not_mem_nil] at hx
  | interval =>
      by_cases hc : c = q
      · simp only [minimalNegative, if_pos hc, List.not_mem_nil] at hx
      · simp only [minimalNegative, if_neg hc, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rw [hx]
        simp [negative, hc]

theorem tripleRelation_symm {x y : Triple} (h : tripleRelation x y) : tripleRelation y x := by
  unfold tripleRelation FourRowHessenberg.tripleMatch at *
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> omega

theorem tripleRelation_weight_eq {x y : Triple} (h : tripleRelation x y) :
    wordWeight x = wordWeight y := by
  unfold tripleRelation FourRowHessenberg.tripleMatch at h
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  all_goals unfold wordWeight
  all_goals rw [h0, h1, h2] <;> ring

/-- The two possible opposite-sign minimal candidates have incompatible largest labels. -/
theorem minimal_opposite_ne {k : Kind} {q a b c d r s t : ℤ}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t)
    {x y : Triple} (hx : x ∈ minimalPositive k q a b c d r s t)
    (hy : y ∈ minimalNegative k q a b c d r s t) : ¬ tripleRelation x y := by
  intro he
  cases k with
  | left =>
      by_cases hc : c = q
      · simp only [minimalPositive, properPositive, hc, ite_true, List.nil_append,
          minimalNegative, List.mem_cons, List.not_mem_nil, or_false] at hx hy
        subst x
        subst y
        unfold tripleRelation FourRowHessenberg.tripleMatch at he
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at he
        dsimp [domain, contact] at hdom hk
        rcases he with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
          ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> omega
      · simp only [minimalNegative, if_neg hc, List.not_mem_nil] at hy
  | right =>
      by_cases hb : b = q
      · simp only [minimalPositive, properPositive, hb, ite_true, List.append_nil,
          minimalNegative, List.mem_cons, List.not_mem_nil, or_false] at hx hy
        subst x
        subst y
        unfold tripleRelation FourRowHessenberg.tripleMatch at he
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at he
        dsimp [domain, contact] at hdom hk
        rcases he with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
          ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> omega
      · simp only [minimalNegative, if_neg hb, List.not_mem_nil] at hy
  | interval =>
      by_cases hc : c = q
      · simp only [minimalNegative, if_pos hc, List.not_mem_nil] at hy
      · simp only [minimalPositive, if_neg hc, List.not_mem_nil] at hx

private theorem pull_members_iff {xs : List Triple} {p : Triple × List Triple}
    (hp : p ∈ pulls xs) (y : Triple) : y ∈ xs ↔ y = p.1 ∨ y ∈ p.2 := by
  induction xs generalizing p with
  | nil => simp [pulls] at hp
  | cons a xs ih =>
      simp only [pulls, List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨p', hp', rfl⟩
      · simp only [List.mem_cons]
      · simp only [List.mem_cons, Prod.fst, Prod.snd]
        rw [ih (p := p') hp']
        tauto

theorem matching_member_left {xs ys : List Triple} (hm : matching tripleRelation xs ys)
    {x : Triple} (hx : x ∈ xs) : ∃ y ∈ ys, tripleRelation x y := by
  induction xs generalizing ys x with
  | nil => simp at hx
  | cons a xs ih =>
      obtain ⟨p, hp, hrel, htail⟩ := (matching_cons_iff _ _ _ _).mp hm
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨p.1, (pull_members hp).1, hrel⟩
      · obtain ⟨y, hy, hxy⟩ := ih (ys := p.2) (x := x) htail hx
        exact ⟨y, (pull_members hp).2 y hy, hxy⟩

theorem matching_member_right {xs ys : List Triple} (hm : matching tripleRelation xs ys)
    {y : Triple} (hy : y ∈ ys) : ∃ x ∈ xs, tripleRelation x y := by
  induction xs generalizing ys y with
  | nil =>
      change ys = [] at hm
      subst ys
      simp at hy
  | cons a xs ih =>
      obtain ⟨p, hp, hrel, htail⟩ := (matching_cons_iff _ _ _ _).mp hm
      rcases (pull_members_iff hp y).mp hy with hy | hy
      · subst y
        exact ⟨a, by simp, hrel⟩
      · obtain ⟨x, hx, hxy⟩ := ih (ys := p.2) (y := y) htail hy
        exact ⟨x, by simp [hx], hxy⟩

theorem exists_minimum_word (L : List Triple) (hne : L ≠ []) :
    ∃ x ∈ L, ∀ y ∈ L, wordWeight x ≤ wordWeight y := by
  induction L with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
      by_cases hxs : xs = []
      · subst xs
        refine ⟨x, by simp, ?_⟩
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        subst y
        exact le_rfl
      · obtain ⟨y, hy, hmin⟩ := ih hxs
        by_cases hw : wordWeight x ≤ wordWeight y
        · refine ⟨x, by simp, ?_⟩
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact le_rfl
          · exact hw.trans (hmin z hz)
        · refine ⟨y, by simp [hy], ?_⟩
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact le_of_lt (lt_of_not_ge hw)
          · exact hmin z hz

/-- A global minimum must cross between equal signs.  The argument preserves
all occurrences and does not enumerate an unsigned matching. -/
theorem signed_minimum_crossing (PP NP PQ NQ MP MN MQ NN : List Triple)
    (hm : matching tripleRelation (PP ++ NQ) (NP ++ PQ))
    (hne : MP ++ MN ≠ [])
    (hMP : ∀ x ∈ MP, x ∈ PP) (hMN : ∀ x ∈ MN, x ∈ NP)
    (hMQ : ∀ x ∈ MQ, x ∈ PQ) (hNN : ∀ x ∈ NN, x ∈ NQ)
    (hpP : ∀ x ∈ PP, (∀ z ∈ MP ++ MN, wordWeight x ≤ wordWeight z) → x ∈ MP)
    (hnP : ∀ x ∈ NP, (∀ z ∈ MP ++ MN, wordWeight x ≤ wordWeight z) → x ∈ MN)
    (hpQ : ∀ x ∈ PQ, (∀ z ∈ MQ ++ NN, wordWeight x ≤ wordWeight z) → x ∈ MQ)
    (hnQ : ∀ x ∈ NQ, (∀ z ∈ MQ ++ NN, wordWeight x ≤ wordWeight z) → x ∈ NN)
    (hoP : ∀ x ∈ MP, ∀ y ∈ MN, ¬ tripleRelation x y)
    (hoQ : ∀ x ∈ MQ, ∀ y ∈ NN, ¬ tripleRelation x y) :
    (∃ x ∈ MP, ∃ y ∈ MQ, tripleRelation x y) ∨
      (∃ x ∈ MN, ∃ y ∈ NN, tripleRelation x y) := by
  have hneAll : (MP ++ MN) ++ (MQ ++ NN) ≠ [] := by
    intro hz
    exact hne (List.append_eq_nil_iff.mp hz).1
  obtain ⟨x, hx, hmin⟩ := exists_minimum_word ((MP ++ MN) ++ (MQ ++ NN)) hneAll
  have boundP (y : Triple) (he : wordWeight y = wordWeight x) :
      ∀ z ∈ MP ++ MN, wordWeight y ≤ wordWeight z := by
    intro z hz
    rw [he]
    exact hmin z (List.mem_append.mpr (Or.inl hz))
  have boundQ (y : Triple) (he : wordWeight y = wordWeight x) :
      ∀ z ∈ MQ ++ NN, wordWeight y ≤ wordWeight z := by
    intro z hz
    rw [he]
    exact hmin z (List.mem_append.mpr (Or.inr hz))
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, hr⟩ := matching_member_left hm
        (List.mem_append.mpr (Or.inl (hMP x hx)))
      rcases List.mem_append.mp hy with hy | hy
      · have hny := hnP y hy (boundP y (tripleRelation_weight_eq hr).symm)
        exact (hoP x hx y hny hr).elim
      · exact Or.inl ⟨x, hx, y, hpQ y hy (boundQ y (tripleRelation_weight_eq hr).symm), hr⟩
    · obtain ⟨y, hy, hr⟩ := matching_member_right hm
        (List.mem_append.mpr (Or.inl (hMN x hx)))
      rcases List.mem_append.mp hy with hy | hy
      · have hpy := hpP y hy (boundP y (tripleRelation_weight_eq hr))
        exact (hoP y hpy x hx hr).elim
      · exact Or.inr ⟨x, hx, y, hnQ y hy (boundQ y (tripleRelation_weight_eq hr)),
          tripleRelation_symm hr⟩
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, hr⟩ := matching_member_right hm
        (List.mem_append.mpr (Or.inr (hMQ x hx)))
      rcases List.mem_append.mp hy with hy | hy
      · exact Or.inl ⟨y, hpP y hy (boundP y (tripleRelation_weight_eq hr)), x, hx, hr⟩
      · have hny := hnQ y hy (boundQ y (tripleRelation_weight_eq hr))
        exact (hoQ x hx y hny (tripleRelation_symm hr)).elim
    · obtain ⟨y, hy, hr⟩ := matching_member_left hm
        (List.mem_append.mpr (Or.inr (hNN x hx)))
      rcases List.mem_append.mp hy with hy | hy
      · exact Or.inr ⟨y, hnP y hy (boundP y (tripleRelation_weight_eq hr).symm), x, hx,
          tripleRelation_symm hr⟩
      · have hpy := hpQ y hy (boundQ y (tripleRelation_weight_eq hr).symm)
        exact (hoQ y hpy x hx (tripleRelation_symm hr)).elim




def rowsA (q l z a b c d : ℤ) : Prop :=
  (a = l ∧ b = q ∧ c = l ∧ d = l + 2 * q - 2 * z) ∨
  (a = l + 2 * q - 2 * z ∧ b = l ∧ c = q ∧ d = l)

def rowsB (q l z a b c d : ℤ) : Prop :=
  (a = l ∧ b = l + q - z ∧ c = q ∧ d = l + q - z) ∨
  (a = l + q - z ∧ b = q ∧ c = l + q - z ∧ d = l)

def identityCoordinates (a b c d r s t A B C D R S T : ℤ) : Prop :=
  a = A ∧ b = B ∧ c = C ∧ d = D ∧ r = R ∧ s = S ∧ t = T

def rotationCoordinates (a b c d r s t A B C D R S T : ℤ) : Prop :=
  a = D ∧ b = C ∧ c = B ∧ d = A ∧ r = T ∧ s = S ∧ t = R

def quartet (q l z a b c d r s t A B C D R S T : ℤ) : Prop :=
  0 < z ∧ 2 * z < q ∧ 2 * z < l ∧ l ≠ q ∧
  r = z ∧ s = z ∧ t = z ∧ R = z ∧ S = z ∧ T = z ∧
  ((rowsA q l z a b c d ∧ rowsB q l z A B C D) ∨
    (rowsB q l z a b c d ∧ rowsA q l z A B C D))

def alternatives (q a b c d r s t A B C D R S T : ℤ) : Prop :=
  identityCoordinates a b c d r s t A B C D R S T ∨
  rotationCoordinates a b c d r s t A B C D R S T ∨
  quartet q a r a b c d r s t A B C D R S T ∨
  quartet q d r a b c d r s t A B C D R S T

private theorem quartet_to_alternatives {q lam z a b c d r s t A B C D R S T : ℤ}
    (h : quartet q lam z a b c d r s t A B C D R S T) :
    alternatives q a b c d r s t A B C D R S T := by
  have hr : r = z := h.2.2.2.2.1
  have hend : a = lam ∨ d = lam := by
    rcases h.2.2.2.2.2.2.2.2.2.2 with ⟨hp, _⟩ | ⟨hp, _⟩
    · rcases hp with hp | hp
      · exact Or.inl hp.1
      · exact Or.inr hp.2.2.2
    · rcases hp with hp | hp
      · exact Or.inl hp.1
      · exact Or.inr hp.2.2.2
  rcases hend with ha | hd
  · exact Or.inr (Or.inr (Or.inl (by simpa only [ha, hr] using h)))
  · exact Or.inr (Or.inr (Or.inr (by simpa only [hd, hr] using h)))

private theorem quartet_reverse {q lam z a b c d r s t A B C D R S T : ℤ}
    (h : quartet q lam z a b c d r s t A B C D R S T) :
    quartet q lam z A B C D R S T a b c d r s t := by
  rcases h with ⟨hz, hq, hlam, hne, hr, hs, ht, hR, hS, hT, hrows⟩
  refine ⟨hz, hq, hlam, hne, hR, hS, hT, hr, hs, ht, ?_⟩
  rcases hrows with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact Or.inr ⟨hq, hp⟩
  · exact Or.inl ⟨hq, hp⟩

private theorem alternatives_reverse {q a b c d r s t A B C D R S T : ℤ}
    (h : alternatives q a b c d r s t A B C D R S T) :
    alternatives q A B C D R S T a b c d r s t := by
  rcases h with h | h | h | h
  · rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact Or.inl ⟨h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm⟩
  · rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact Or.inr (Or.inl ⟨h3.symm, h2.symm, h1.symm, h0.symm,
      h6.symm, h5.symm, h4.symm⟩)
  · exact quartet_to_alternatives (quartet_reverse h)
  · exact quartet_to_alternatives (quartet_reverse h)

private theorem rowsA_mate_rotate {q lam z A B C D : ℤ}
    (h : rowsA q lam z D C B A) : rowsA q lam z A B C D := by
  rcases h with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
  · exact Or.inr ⟨h3, h2, h1, h0⟩
  · exact Or.inl ⟨h3, h2, h1, h0⟩

private theorem rowsB_mate_rotate {q lam z A B C D : ℤ}
    (h : rowsB q lam z D C B A) : rowsB q lam z A B C D := by
  rcases h with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
  · exact Or.inr ⟨h3, h2, h1, h0⟩
  · exact Or.inl ⟨h3, h2, h1, h0⟩

private theorem quartet_mate_rotate {q lam z a b c d r s t A B C D R S T : ℤ}
    (h : quartet q lam z a b c d r s t D C B A T S R) :
    quartet q lam z a b c d r s t A B C D R S T := by
  rcases h with ⟨hz, hq, hlam, hne, hr, hs, ht, hT, hS, hR, hrows⟩
  refine ⟨hz, hq, hlam, hne, hr, hs, ht, hR, hS, hT, ?_⟩
  rcases hrows with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact Or.inl ⟨hp, rowsB_mate_rotate hq⟩
  · exact Or.inr ⟨hp, rowsA_mate_rotate hq⟩

private theorem alternatives_mate_rotate {q a b c d r s t A B C D R S T : ℤ}
    (h : alternatives q a b c d r s t D C B A T S R) :
    alternatives q a b c d r s t A B C D R S T := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact quartet_to_alternatives (quartet_mate_rotate h)
  · exact quartet_to_alternatives (quartet_mate_rotate h)

private theorem left_double_contact_matching
    (q a d A D r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hq : 2 * r < q)
    (hqt : r + t < q) (hd : t < d) (hA : r < A) (hD : t < D)
    (hp : matching tripleRelation [![a, q + q - r, d]] [![A, q + q - r, D]])
    (hn : ((negative .left q a q q d r r t).map tripleTerm).sum =
      ((negative .left q A q q D r r t).map tripleTerm).sum) :
    alternatives q a q q d r r t A q q D r r t := by
  have he := triple_relation_term_eq (matching_one_reading hp)
  have hpair : complete a * complete d = complete A * complete D := by
    apply mul_right_cancel₀ ((complete_ne_zero_iff (q + q - r)).mpr (by omega))
    simp only [tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at he
    linear_combination he
  rcases complete_two_product_reading (by omega) (by omega)
      (by omega) (by omega) hpair with ⟨haA, hdD⟩ | ⟨haD, hdA⟩
  · exact Or.inl ⟨haA, rfl, rfl, hdD, rfl, rfl, rfl⟩
  · by_cases hrt : r = t
    · exact Or.inr (Or.inl ⟨haD, rfl, rfl, hdA, hrt, rfl, hrt.symm⟩)
    · have hread := left_negative_pair_eq q a q d A q D r t hr ht ha hq
        hqt (by omega) hA hqt (by omega) (Ne.symm hrt) hn
      have had : a = d := by
        rcases hread with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
      exact Or.inl ⟨by omega, rfl, rfl, by omega, rfl, rfl, rfl⟩

private theorem left_degenerate_matching
    (q a d A D r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r + t < a) (hq : 2 * r < q)
    (hd : t < d) (hA : r + t < A) (hD : t < D)
    (hane : a ≠ q) (hAne : A ≠ q)
    (hp : matching tripleRelation [![a, a + (q - r), d], ![a, a + (q - r), d]]
      [![A, A + (q - r), D], ![A, A + (q - r), D]])
    (hn : ((negative .left q a q a d r r t).map tripleTerm).sum =
      ((negative .left q A q A D r r t).map tripleTerm).sum) :
    alternatives q a q a d r r t A q A D r r t := by
  have hrel : tripleRelation ![a, a + (q - r), d] ![A, A + (q - r), D] := by
    rcases matching_two_reading hp with h | h
    · exact h.1
    · exact h.1
  rcases shifted_pair_decomposition (q - r) a d A D (by omega) hrel with
      ⟨haA, hdD⟩ | hap | hap
  · exact Or.inl ⟨haA, rfl, haA, hdD, rfl, rfl, rfl⟩
  · have hrt := left_ap_equal_gaps q a d A D r t hr ht ha hq (by omega) hA (by omega) hap hn
    refine Or.inr (Or.inr (Or.inl ?_))
    refine ⟨hr, hq, by omega, hane, rfl, rfl, hrt.symm, rfl, rfl, hrt.symm, ?_⟩
    exact Or.inl ⟨Or.inl ⟨rfl, rfl, rfl, by omega⟩,
      Or.inr ⟨by omega, rfl, by omega, hap.2.2⟩⟩
  · have hrt := left_ap_equal_gaps q A D a d r t hr ht hA hq (by omega) ha (by omega)
      ⟨hap.2.1, hap.1, hap.2.2⟩ hn.symm
    refine Or.inr (Or.inr (Or.inr ?_))
    refine ⟨hr, hq, by omega, by omega, rfl, rfl, hrt.symm, rfl, rfl, hrt.symm, ?_⟩
    exact Or.inr ⟨Or.inr ⟨by omega, rfl, by omega, rfl⟩,
      Or.inl ⟨by omega, rfl, by omega, by omega⟩⟩

private theorem left_nondegenerate_matching
    (q a c d A C D r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hq : 2 * r < q)
    (hc : r + t < c) (hd : t < d)
    (hA : r < A) (hC : r + t < C) (hD : t < D)
    (hac : a ≠ c) (hAC : A ≠ C)
    (hfull : a + c + d = A + C + D)
    (hp : matching tripleRelation [![c, a + (q - r), d], ![a, c + (q - r), d]]
      [![C, A + (q - r), D], ![A, C + (q - r), D]])
    (hn : ((negative .left q a q c d r r t).map tripleTerm).sum =
      ((negative .left q A q C D r r t).map tripleTerm).sum) :
    alternatives q a q c d r r t A q C D r r t := by
  have hdD := shifted_words_origin (q - r) a c d A C D (by omega) hAC hp
  have hsum : a + c = A + C := by omega
  have he := matching_term_sum_eq hp
  have hpairs :
      complete (a + q - r) * complete c + complete a * complete (c + q - r) =
        complete (A + q - r) * complete C + complete A * complete (C + q - r) := by
    apply mul_right_cancel₀ ((complete_ne_zero_iff d).mpr (by omega))
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at he
    have hUa : a + (q - r) = a + q - r := by omega
    have hUc : c + (q - r) = c + q - r := by omega
    have hUA : A + (q - r) = A + q - r := by omega
    have hUC : C + (q - r) = C + q - r := by omega
    rw [hUa, hUc, hUA, hUC, ← hdD] at he
    linear_combination he
  have htop : a + c + q - 2 * r = A + C + q - 2 * r := by omega
  have hM : quadraticM q r a c = quadraticM q r A C := by
    unfold quadraticM
    rw [htop]
    linear_combination -hpairs
  obtain ⟨_, hread⟩ := (quadraticM_eq_iff q r a c r A C hr hq ha (by omega)
    hr hq hA (by omega)).mp hM
  rcases hread with ⟨haA, hcC⟩ | ⟨haC, hcA⟩
  · exact Or.inl ⟨haA, rfl, hcC, hdD, rfl, rfl, rfl⟩
  · have htail :
        complete (a + (q - r)) * complete (c + d - t) +
            complete a * complete (c + d - t + (q - r)) =
          complete (c + (q - r)) * complete (a + d - t) +
            complete c * complete (a + d - t + (q - r)) := by
      apply mul_right_cancel₀ ((complete_ne_zero_iff t).mpr ht.le)
      simp only [negative, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hn
      rw [← haC, ← hcA, ← hdD] at hn
      have hX : c + q + a - 2 * r = a + q + c - 2 * r := by omega
      have hUa : a + (q - r) = a + q - r := by omega
      have hUc : c + (q - r) = c + q - r := by omega
      have hYa : a + d - t + (q - r) = q + a + d - r - t := by omega
      have hYc : c + d - t + (q - r) = q + c + d - r - t := by omega
      rw [hX] at hn
      rw [hUa, hUc, hYa, hYc]
      linear_combination hn
    exact (hac (shifted_tail_swap_eq (q - r) a c d t (by omega)
      (by omega) (by omega) (by omega) htail)).elim


set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem model_matching (k l : Kind)
    (q a b c d r s t A B C D R S T : ℤ)
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact k q a b c r s t) (hl : contact l q A B C R S T)
    (he : model k q a b c d r s t = model l q A B C D R S T) :
    cubicFullIndex a b c d r s t = cubicFullIndex A B C D R S T ∧
      ((r = R ∧ leadingGap k s t = leadingGap l S T) ∨
        (r = leadingGap l S T ∧ leadingGap k s t = R)) ∧
      (((properPositive k q a b c d r s t).map tripleTerm).sum +
        ((negative l q A B C D R S T).map tripleTerm).sum =
        ((negative k q a b c d r s t).map tripleTerm).sum +
        ((properPositive l q A B C D R S T).map tripleTerm).sum) ∧
      matching tripleRelation
        (properPositive k q a b c d r s t ++ negative l q A B C D R S T)
        (negative k q a b c d r s t ++ properPositive l q A B C D R S T) := by
  obtain ⟨hfull, hgap⟩ := model_leading_eq hP hQ hk hl he
  have hword : tripleTerm (leadingTriple k a b c d r s t) =
      tripleTerm (leadingTriple l A B C D R S T) := by
    simp only [leadingTriple, tripleTerm, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    rw [hfull]
    rcases hgap with ⟨hr, hg⟩ | ⟨hr, hg⟩
    · rw [hr, hg]
    · rw [hr, hg]
      ring
  let xs := properPositive k q a b c d r s t ++ negative l q A B C D R S T
  let ys := negative k q a b c d r s t ++ properPositive l q A B C D R S T
  have hxs : ∀ x ∈ xs, ∀ i, 0 < x i := by
    intro x hx i
    rcases List.mem_append.mp hx with hx | hx
    · exact proper_inventory_positive hP hk x
        (List.mem_append.mpr (Or.inl hx)) i
    · exact proper_inventory_positive hQ hl x
        (List.mem_append.mpr (Or.inr hx)) i
  have hys : ∀ y ∈ ys, ∀ i, 0 < y i := by
    intro y hy i
    rcases List.mem_append.mp hy with hy | hy
    · exact proper_inventory_positive hP hk y
        (List.mem_append.mpr (Or.inr hy)) i
    · exact proper_inventory_positive hQ hl y
        (List.mem_append.mpr (Or.inl hy)) i
  have hsum : (xs.map tripleTerm).sum = (ys.map tripleTerm).sum := by
    dsimp [xs, ys]
    simp only [List.map_append, List.sum_append]
    rw [model_split hk, model_split hl] at he
    linear_combination he - hword
  refine ⟨hfull, hgap, ?_, triple_matching xs ys hxs hys hsum⟩
  simpa only [xs, ys, List.map_append, List.sum_append] using hsum

theorem reduced_inventory_positive {k : Kind} {q a b c d r s t : ℤ}
    (hdom : domain q a b c d r s t) (hk : contact k q a b c r s t) :
    ∀ x ∈ reducedPositive k q a b c d r s t ++ reducedNegative k q a b c d r s t,
      ∀ i, 0 < x i := by
  intro x hx i
  apply proper_inventory_positive hdom hk x _ i
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append.mpr (Or.inl (reduced_positive_mem hdom hk hx))
  · exact List.mem_append.mpr (Or.inr (reduced_negative_mem hx))

/-- Actual model equality supplies separate same-sign matchings after exact internal cancellation. -/
theorem model_signed_matching (k l : Kind)
    (q a b c d r s t A B C D R S T : ℤ)
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact k q a b c r s t) (hl : contact l q A B C R S T)
    (he : model k q a b c d r s t = model l q A B C D R S T) :
    cubicFullIndex a b c d r s t = cubicFullIndex A B C D R S T ∧
      ((r = R ∧ leadingGap k s t = leadingGap l S T) ∨
        (r = leadingGap l S T ∧ leadingGap k s t = R)) ∧
      matching tripleRelation (reducedPositive k q a b c d r s t)
        (reducedPositive l q A B C D R S T) ∧
      matching tripleRelation (reducedNegative k q a b c d r s t)
        (reducedNegative l q A B C D R S T) := by
  obtain ⟨hfull, hgap, hraw, hcross⟩ :=
    model_matching k l q a b c d r s t A B C D R S T hP hQ hk hl he
  have heReduced :
      ((reducedPositive k q a b c d r s t).map tripleTerm).sum +
          ((reducedNegative l q A B C D R S T).map tripleTerm).sum =
        ((reducedNegative k q a b c d r s t).map tripleTerm).sum +
          ((reducedPositive l q A B C D R S T).map tripleTerm).sum := by
    have hpartP := reduced_parts_eq hP hk
    have hpartQ := reduced_parts_eq hQ hl
    linear_combination hraw - hpartP + hpartQ
  exact ⟨hfull, hgap, signed_triple_matching _ _ _ _
    (reduced_inventory_positive hP hk) (reduced_inventory_positive hQ hl)
    (fun _ hx _ hy => reduced_sign_disjoint hP hk hx hy)
    (fun _ hx _ hy => reduced_sign_disjoint hQ hl hx hy) heReduced⟩


/-- One same-sign minimum has been removed from each signed polynomial. -/
def minimalCanceledMatching (k l : Kind)
    (q a b c d r s t A B C D R S T : ℤ) : Prop :=
  (∃ p ∈ pulls (properPositive k q a b c d r s t),
    ∃ u ∈ pulls (properPositive l q A B C D R S T),
      p.1 ∈ minimalPositive k q a b c d r s t ∧
      u.1 ∈ minimalPositive l q A B C D R S T ∧ tripleRelation p.1 u.1 ∧
      matching tripleRelation (p.2 ++ negative l q A B C D R S T)
        (negative k q a b c d r s t ++ u.2)) ∨
  (∃ p ∈ pulls (negative k q a b c d r s t),
    ∃ u ∈ pulls (negative l q A B C D R S T),
      p.1 ∈ minimalNegative k q a b c d r s t ∧
      u.1 ∈ minimalNegative l q A B C D R S T ∧ tripleRelation p.1 u.1 ∧
      matching tripleRelation (properPositive k q a b c d r s t ++ u.2)
        (p.2 ++ properPositive l q A B C D R S T))

/-- The minimum crossing and its cancellation are produced by actual polynomial equality. -/
theorem model_minimum_matching (k l : Kind)
    (q a b c d r s t A B C D R S T : ℤ)
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact k q a b c r s t) (hl : contact l q A B C R S T)
    (he : model k q a b c d r s t = model l q A B C D R S T) :
    cubicFullIndex a b c d r s t = cubicFullIndex A B C D R S T ∧
      ((r = R ∧ leadingGap k s t = leadingGap l S T) ∨
        (r = leadingGap l S T ∧ leadingGap k s t = R)) ∧
      minimalCanceledMatching k l q a b c d r s t A B C D R S T := by
  obtain ⟨hfull, hgap, hsum, hm⟩ :=
    model_matching k l q a b c d r s t A B C D R S T hP hQ hk hl he
  have hminimum := signed_minimum_crossing
    (properPositive k q a b c d r s t) (negative k q a b c d r s t)
    (properPositive l q A B C D R S T) (negative l q A B C D R S T)
    (minimalPositive k q a b c d r s t) (minimalNegative k q a b c d r s t)
    (minimalPositive l q A B C D R S T) (minimalNegative l q A B C D R S T)
    hm (minimal_candidates_nonempty k q a b c d r s t)
    (fun _ hx => minimal_positive_mem hx)
    (fun _ hx => minimal_negative_mem hP hk hx)
    (fun _ hx => minimal_positive_mem hx)
    (fun _ hx => minimal_negative_mem hQ hl hx)
    (fun _ hx hmin => minimal_positive_promotion hP hk hx hmin)
    (fun _ hx hmin => minimal_negative_promotion hP hk hx hmin)
    (fun _ hx hmin => minimal_positive_promotion hQ hl hx hmin)
    (fun _ hx hmin => minimal_negative_promotion hQ hl hx hmin)
    (fun _ hx _ hy => minimal_opposite_ne hP hk hx hy)
    (fun _ hx _ hy => minimal_opposite_ne hQ hl hx hy)
  refine ⟨hfull, hgap, ?_⟩
  rcases hminimum with ⟨x, hx, y, hy, hrel⟩ | ⟨x, hx, y, hy, hrel⟩
  · obtain ⟨LP, hp⟩ := exists_pull (minimal_positive_mem hx)
    obtain ⟨LQ, hu⟩ := exists_pull (minimal_positive_mem hy)
    refine Or.inl ⟨(x, LP), hp, (y, LQ), hu, hx, hy, hrel, ?_⟩
    exact triple_signed_cancel_positive _ _ _ _ (proper_inventory_positive hP hk)
      (proper_inventory_positive hQ hl) hsum (x, LP) (y, LQ) hp hu hrel
  · obtain ⟨LP, hp⟩ := exists_pull (minimal_negative_mem hP hk hx)
    obtain ⟨LQ, hu⟩ := exists_pull (minimal_negative_mem hQ hl hy)
    refine Or.inr ⟨(x, LP), hp, (y, LQ), hu, hx, hy, hrel, ?_⟩
    exact triple_signed_cancel_negative _ _ _ _ (proper_inventory_positive hP hk)
      (proper_inventory_positive hQ hl) hsum (x, LP) (y, LQ) hp hu hrel

theorem triple_eq_iff (x y : Triple) :
    x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
  constructor
  · intro h
    exact ⟨congrArg (fun T => T 0) h, congrArg (fun T => T 1) h,
      congrArg (fun T => T 2) h⟩
  · rintro ⟨h0, h1, h2⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2



private theorem aligned_left_matching (q a c d A C D r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hq : 2 * r < q)
    (hc : r + t < c) (hd : t < d)
    (hA : r < A) (hC : r + t < C) (hD : t < D)
    (hane : a ≠ q) (hAne : A ≠ q) (hsum : a + c + d = A + C + D)
    (hpos : matching tripleRelation (properPositive .left q a q c d r r t)
      (properPositive .left q A q C D r r t))
    (hnegative : ((negative .left q a q c d r r t).map tripleTerm).sum =
      ((negative .left q A q C D r r t).map tripleTerm).sum) :
    alternatives q a q c d r r t A q C D r r t := by
  simp only [properPositive] at hpos
  by_cases hcq : c = q
  · by_cases hCq : C = q
    · subst c
      subst C
      simp only [if_pos rfl, List.nil_append] at hpos
      exact left_double_contact_matching q a d A D r t hr ht ha hq hc hd hA hD hpos hnegative
    · have hlen := matching_lengths hpos
      simp only [if_pos hcq, if_neg hCq, List.length_append, List.length_cons,
        List.length_nil] at hlen
      omega
  · by_cases hCq : C = q
    · have hlen := matching_lengths hpos
      simp only [if_neg hcq, if_pos hCq, List.length_append, List.length_cons,
        List.length_nil] at hlen
      omega
    · simp only [if_neg hcq, if_neg hCq, List.cons_append, List.nil_append] at hpos
      have hUa : a + q - r = a + (q - r) := by omega
      have hUc : q + c - r = c + (q - r) := by omega
      have hUA : A + q - r = A + (q - r) := by omega
      have hUC : q + C - r = C + (q - r) := by omega
      simp only [hUa, hUc, hUA, hUC] at hpos
      have hdeg := shifted_words_degeneracy_iff (q - r) a c d A C D
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) hpos
      by_cases hac : a = c
      · have hAC := hdeg.mp hac
        subst c
        subst C
        exact left_degenerate_matching q a d A D r t hr ht hc hq hd hC hD
          hane hAne hpos hnegative
      · have hAC : A ≠ C := fun h => hac (hdeg.mpr h)
        exact left_nondegenerate_matching q a c d A C D r t hr ht ha hq hc hd
          hA hC hD hac hAC hsum hpos hnegative

private theorem model_left_left
    (q a b c d r s t A B C D R S T : ℤ)
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact .left q a b c r s t) (hl : contact .left q A B C R S T)
    (he : model .left q a b c d r s t = model .left q A B C D R S T)
    (hfull : cubicFullIndex a b c d r s t = cubicFullIndex A B C D R S T)
    (hgap : (r = R ∧ leadingGap .left s t = leadingGap .left S T) ∨
      (r = leadingGap .left S T ∧ leadingGap .left s t = R))
    (hm : matching tripleRelation (reducedPositive .left q a b c d r s t)
        (reducedPositive .left q A B C D R S T) ∧
      matching tripleRelation (reducedNegative .left q a b c d r s t)
        (reducedNegative .left q A B C D R S T)) :
    alternatives q a b c d r s t A B C D R S T := by
  have houter : t = T := left_outer_gap_eq hP hQ hk hl he
  have hfirst : r = R := by
    change (r = R ∧ t = T) ∨ (r = T ∧ t = R) at hgap
    rcases hgap with hgap | hgap
    · exact hgap.1
    · exact hgap.1.trans (houter.symm.trans hgap.2)
  clear he hgap
  rcases hk with ⟨hb, hs⟩
  rcases hl with ⟨hB, hS⟩
  subst b
  subst s
  subst B
  subst R
  subst S
  subst T
  obtain ⟨hr, ht, ha, hq, hc, hd⟩ := left_domain_bounds hP ⟨rfl, rfl⟩
  obtain ⟨_, _, hA, _, hC, hD⟩ := left_domain_bounds hQ ⟨rfl, rfl⟩
  have hane := hP.2.2.2.2.2.2.2.2.1
  have hAne := hQ.2.2.2.2.2.2.2.2.1
  have hsum : a + c + d = A + C + D := by
    dsimp [cubicFullIndex] at hfull
    omega
  obtain ⟨hpos, hneg⟩ := hm
  change matching tripleRelation (negative .left q a q c d r r t)
    (negative .left q A q C D r r t) at hneg
  have hnegative := matching_term_sum_eq hneg
  clear hneg hP hQ hfull
  exact aligned_left_matching q a c d A C D r t hr ht ha hq hc (by omega)
    hA hC (by omega) hane hAne hsum hpos hnegative

/-- The interval-extraction chart has the opposite low augmentation sign
from the left middle-contact chart.  Vanishing optional words lie above it. -/
private theorem interval_low_derivative (q b c d r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hrs : r < s)
    (hb : r + s < b) (hc : s + t < c) (hd : q + t < d)
    (hq : s + b - r = q) (v : ℕ+) (hv : (v.val : ℤ) ≤ t) :
    residualAugmentation
      (MvPolynomial.pderiv v (model .interval q s b c d r s t)) =
      (if t = (v.val : ℤ) then (1 : ℚ) else 0) := by
  have hB : 0 < b := by omega
  have hC : 0 < c := by omega
  have hD : 0 < d := by omega
  have hV : 0 < b + c - s := by omega
  have hW : 0 < c + d - t := by omega
  have hF : 0 < q + c + d - s - t := by omega
  have hX : 0 < q + c - s := by omega
  have hY : 0 < b + c + d - s - t := by omega
  have hnC : c ≠ (v.val : ℤ) := by omega
  have hnD : d ≠ (v.val : ℤ) := by omega
  have hnV : b + c - s ≠ (v.val : ℤ) := by omega
  have hnW : c + d - t ≠ (v.val : ℤ) := by omega
  have hnF : q + c + d - s - t ≠ (v.val : ℤ) := by omega
  have hnX : q + c - s ≠ (v.val : ℤ) := by omega
  have hnY : b + c + d - s - t ≠ (v.val : ℤ) := by omega
  simp only [model, positive, negative]
  split_ifs
  all_goals simp only [List.nil_append, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, map_sub, map_add]
  all_goals simp only [
    augmentation_pderiv_triple v s (b + c - s) d hs hV hD,
    augmentation_pderiv_triple v t b (c + d - t) ht hB hW,
    augmentation_pderiv_triple v r t (q + c + d - s - t) hr ht hF,
    augmentation_pderiv_triple v b c d hB hC hD,
    augmentation_pderiv_triple v r (q + c - s) d hr hX hD,
    augmentation_pderiv_triple v s t (b + c + d - s - t) hs ht hY]
  all_goals simp only [if_neg hnC, if_neg hnD, if_neg hnV, if_neg hnW,
    if_neg hnF, if_neg hnX, if_neg hnY]
  all_goals try
    have hnS : s ≠ (v.val : ℤ) := by omega
    simp only [if_neg hnS]
  all_goals try
    have hnB : b ≠ (v.val : ℤ) := by omega
    simp only [if_neg hnB]
  all_goals simp_all only [ite_true, ite_false]
  all_goals ring

private theorem interval_outer_gap_eq {q a b c d r s t A B C D R S T : ℤ}
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact .interval q a b c r s t) (hl : contact .interval q A B C R S T)
    (he : model .interval q a b c d r s t = model .interval q A B C D R S T) :
    t = T := by
  rcases hk with ⟨hmerge, has⟩
  rcases hl with ⟨hMerge, hAS⟩
  subst a
  subst A
  rcases hP with ⟨hp0, hr, hs, ht, hrs, hb, hc, hd, hp8, hp9, hp10, hp11⟩
  rcases hQ with ⟨hq0, hR, hS, hT, hRS, hB, hC, hD, hq8, hq9, hq10, hq11⟩
  have hp : ∀ v : ℕ+, (v.val : ℤ) ≤ t →
      residualAugmentation (MvPolynomial.pderiv v
        (-model .interval q s b c d r s t)) = -(if t = (v.val : ℤ) then 1 else 0) := by
    intro v hv
    simp only [map_neg,
      interval_low_derivative q b c d r s t hr hs ht hrs hb hc hd hmerge v hv]
  have hf : ∀ v : ℕ+, (v.val : ℤ) ≤ T →
      residualAugmentation (MvPolynomial.pderiv v
        (-model .interval q S B C D R S T)) = -(if T = (v.val : ℤ) then 1 else 0) := by
    intro v hv
    simp only [map_neg,
      interval_low_derivative q B C D R S T hR hS hT hRS hB hC hD hMerge v hv]
  have he' := congrArg Neg.neg he
  rcases lt_trichotomy t T with hlt | heq | hgt
  · exact (negative_low_marker_not_lt _ _ t T ht hp hf he' hlt).elim
  · exact heq
  · exact (negative_low_marker_not_lt _ _ T t hT hf hp he'.symm hgt).elim


private theorem opposite_low_markers_ne (p f : CompleteRing) (t T : ℤ)
    (ht : 0 < t) (hT : 0 < T)
    (hp : ∀ v : ℕ+, (v.val : ℤ) ≤ t →
      residualAugmentation (MvPolynomial.pderiv v p) = -(if t = (v.val : ℤ) then 1 else 0))
    (hf : ∀ v : ℕ+, (v.val : ℤ) ≤ T →
      residualAugmentation (MvPolynomial.pderiv v f) = (if T = (v.val : ℤ) then 1 else 0)) :
    p ≠ f := by
  intro he
  let m := min t T
  let v : ℕ+ := ⟨m.toNat, by dsimp [m]; omega⟩
  have hv : (v.val : ℤ) = m := by dsimp [v]; omega
  have hmP : (v.val : ℤ) ≤ t := by rw [hv]; exact min_le_left _ _
  have hmQ : (v.val : ℤ) ≤ T := by rw [hv]; exact min_le_right _ _
  have hh := congrArg (fun z : CompleteRing =>
    residualAugmentation (MvPolynomial.pderiv v z)) he
  rw [hp v hmP, hf v hmQ] at hh
  rcases le_total t T with hle | hle
  · have htV : t = (v.val : ℤ) := by rw [hv]; exact (min_eq_left hle).symm
    rw [if_pos htV] at hh
    split_ifs at hh <;> norm_num at hh
  · have hTV : T = (v.val : ℤ) := by rw [hv]; exact (min_eq_right hle).symm
    rw [if_pos hTV] at hh
    split_ifs at hh <;> norm_num at hh

private theorem right_low_derivative (q a b d r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ha : r < a) (hq : 2 * s < q)
    (hb : r + s < b) (hd : q + s < d) (hu : a + b - r ≠ q)
    (v : ℕ+) (hv : (v.val : ℤ) ≤ r) :
    residualAugmentation (MvPolynomial.pderiv v (model .right q a b q d r s s)) =
      -(if r = (v.val : ℤ) then (1 : ℚ) else 0) := by
  have hA : 0 < a := by omega
  have hB : 0 < b := by omega
  have hD : 0 < d := by omega
  have hV : 0 < b + q - s := by omega
  have hW : 0 < q + d - s := by omega
  have hF : 0 < a + b + q + d - r - 2 * s := by omega
  have hX : 0 < a + b + q - r - s := by omega
  have hU : 0 < a + b - r := by omega
  have hY : 0 < b + q + d - 2 * s := by omega
  have hnA : a ≠ (v.val : ℤ) := by omega
  have hnB : b ≠ (v.val : ℤ) := by omega
  have hnV : b + q - s ≠ (v.val : ℤ) := by omega
  have hnF : a + b + q + d - r - 2 * s ≠ (v.val : ℤ) := by omega
  have hnX : a + b + q - r - s ≠ (v.val : ℤ) := by omega
  have hnU : a + b - r ≠ (v.val : ℤ) := by omega
  have hnY : b + q + d - 2 * s ≠ (v.val : ℤ) := by omega
  simp only [model, positive, negative, if_neg hu]
  split_ifs
  all_goals simp only [List.nil_append, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, map_sub, map_add]
  all_goals simp only [
    augmentation_pderiv_triple v a (b + q - s) d hA hV hD,
    augmentation_pderiv_triple v a b (q + d - s) hA hB hW,
    augmentation_pderiv_triple v r s (a + b + q + d - r - 2 * s) hr hs hF,
    augmentation_pderiv_triple v r (a + b + q - r - s) d hr hX hD,
    augmentation_pderiv_triple v r (a + b - r) (q + d - s) hr hU hW,
    augmentation_pderiv_triple v s a (b + q + d - 2 * s) hs hA hY]
  all_goals simp only [if_neg hnA, if_neg hnB, if_neg hnV, if_neg hnF,
    if_neg hnX, if_neg hnU, if_neg hnY]
  all_goals try
    have hnW : q + d - s ≠ (v.val : ℤ) := by omega
    simp only [if_neg hnW]
  all_goals simp_all only [ite_true, ite_false]
  all_goals ring

private theorem left_right_outer_gap_eq {q a b c d r s t A B C D R S T : ℤ}
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact .left q a b c r s t) (hl : contact .right q A B C R S T)
    (hu : A + B - R ≠ q)
    (he : model .left q a b c d r s t = model .right q A B C D R S T) : t = R := by
  obtain ⟨hr, ht, ha, hq, hc, hd⟩ := left_domain_bounds hP hk
  rcases hk with ⟨hb, hrs⟩
  rcases hl with ⟨hCq, hST⟩
  subst b
  subst s
  subst C
  subst T
  rcases hQ with ⟨hqQ, hR, hS, _, hA, hB, hC, hD, hQ8, hQ9, hQ10, hQ11⟩
  have hp : ∀ v : ℕ+, (v.val : ℤ) ≤ t →
      residualAugmentation (MvPolynomial.pderiv v (model .left q a q c d r r t)) =
        -(if t = (v.val : ℤ) then 1 else 0) :=
    fun v hv => left_low_derivative q a c d r t hr ht ha hq hc hd v hv
  have hf : ∀ v : ℕ+, (v.val : ℤ) ≤ R →
      residualAugmentation (MvPolynomial.pderiv v (model .right q A B q D R S S)) =
        -(if R = (v.val : ℤ) then 1 else 0) :=
    fun v hv => right_low_derivative q A B D R S hR hS hA (by omega) hB hD hu v hv
  rcases lt_trichotomy t R with hlt | heq | hgt
  · exact (negative_low_marker_not_lt _ _ t R ht hp hf he hlt).elim
  · exact heq
  · exact (negative_low_marker_not_lt _ _ R t hR hf hp he.symm hgt).elim

private theorem formal_left_positive (q a c d r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hq : 2 * r < q)
    (hc : r + t < c) (hd : t < d) :
    ∀ X ∈ properPositive .left q a q c d r r t, ∀ i, 0 < X i := by
  intro X hX i
  simp only [properPositive] at hX
  split_ifs at hX
  all_goals simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, false_or] at hX
  all_goals
    repeat' first
    | (rcases hX with hX | hX)
    | (subst X)
  all_goals fin_cases i <;> dsimp <;> omega

private theorem right_positive_rotate (q a b d r s : ℤ) :
    ((properPositive .right q a b q d r s s).map tripleTerm).sum =
      ((properPositive .left q d q b a s s r).map tripleTerm).sum := by
  have hV : q + b - s = b + q - s := by omega
  have hW : q + d - s = d + q - s := by omega
  by_cases hb : b = q
  all_goals simp only [properPositive]
  all_goals split_ifs
  all_goals simp only [List.nil_append, List.cons_append, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    hV, hW]
  all_goals ring

private theorem right_negative_rotate (q a b d r s : ℤ) (hu : a + b - r ≠ q) :
    ((negative .right q a b q d r s s).map tripleTerm).sum =
      ((negative .left q d q b a s s r).map tripleTerm).sum := by
  have h0 : d + q + b - 2 * s = b + q + d - 2 * s := by omega
  have h1 : d + q - s = q + d - s := by omega
  have h2 : b + a - r = a + b - r := by omega
  have h3 : q + b + a - s - r = a + b + q - r - s := by omega
  simp only [negative, if_neg hu, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    h0, h1, h2, h3]
  ring

private theorem model_left_right
    (q a b c d r s t A B C D R S T : ℤ)
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact .left q a b c r s t) (hl : contact .right q A B C R S T)
    (he : model .left q a b c d r s t = model .right q A B C D R S T)
    (hfull : cubicFullIndex a b c d r s t = cubicFullIndex A B C D R S T)
    (hgap : (r = R ∧ leadingGap .left s t = leadingGap .right S T) ∨
      (r = leadingGap .right S T ∧ leadingGap .left s t = R))
    (hm : matching tripleRelation (reducedPositive .left q a b c d r s t)
        (reducedPositive .right q A B C D R S T) ∧
      matching tripleRelation (reducedNegative .left q a b c d r s t)
        (reducedNegative .right q A B C D R S T)) :
    alternatives q a b c d r s t A B C D R S T := by
  have hnc : ¬ rightCancellation q A D R S := by
    intro hc
    have hlen := matching_lengths hm.2
    simp only [reducedNegative, if_pos hc, negative, List.length_cons, List.length_nil] at hlen
    omega
  have hu : A + B - R ≠ q := by
    intro hu
    have hlen := matching_lengths hm.2
    simp only [reducedNegative, if_neg hnc, negative, if_pos hu, List.length_append,
      List.length_cons, List.length_nil] at hlen
    omega
  have houter : t = R := left_right_outer_gap_eq hP hQ hk hl hu he
  have hfirst : r = S := by
    change (r = R ∧ t = S) ∨ (r = S ∧ t = R) at hgap
    rcases hgap with hgap | hgap
    · exact hgap.1.trans (houter.symm.trans hgap.2)
    · exact hgap.1
  clear he hgap
  obtain ⟨hr, ht, ha, hq, hc, hd⟩ := left_domain_bounds hP hk
  have hane := hP.2.2.2.2.2.2.2.2.1
  rcases hk with ⟨hb, hrs⟩
  rcases hl with ⟨hCq, hST⟩
  subst b
  subst s
  subst C
  subst R
  subst S
  subst T
  rcases hQ with ⟨hqQ, _, _, _, hA, hB, hC, hD, hAne, hRne, hSne, hTne⟩
  have hp := matching_term_sum_eq hm.1
  have hn := matching_term_sum_eq hm.2
  simp only [reducedPositive, if_neg hnc] at hp
  simp only [reducedNegative, if_neg hnc] at hn
  have hpRot :
      ((properPositive .left q a q c d r r t).map tripleTerm).sum =
        ((properPositive .left q D q B A r r t).map tripleTerm).sum :=
    hp.trans (right_positive_rotate q A B D t r)
  have hnRot :
      ((negative .left q a q c d r r t).map tripleTerm).sum =
        ((negative .left q D q B A r r t).map tripleTerm).sum :=
    hn.trans (right_negative_rotate q A B D t r hu)
  have hposRot : matching tripleRelation
      (properPositive .left q a q c d r r t)
      (properPositive .left q D q B A r r t) :=
    triple_matching _ _ (formal_left_positive q a c d r t hr ht ha hq hc (by omega))
      (formal_left_positive q D B A r t hr ht (by omega) hq (by omega) hA) hpRot
  have hsum : a + c + d = D + B + A := by
    dsimp [cubicFullIndex] at hfull
    omega
  exact alternatives_mate_rotate
    (aligned_left_matching q a c d D B A r t hr ht ha hq hc (by omega)
      (by omega) (by omega) hA hane (by omega) hsum hposRot hnRot)

private theorem model_left_interval
    (q a b c d r s t A B C D R S T : ℤ)
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact .left q a b c r s t) (hl : contact .interval q A B C R S T)
    (he : model .left q a b c d r s t = model .interval q A B C D R S T) :
    alternatives q a b c d r s t A B C D R S T := by
  obtain ⟨hr, ht, ha, hq, hc, hd⟩ := left_domain_bounds hP hk
  rcases hk with ⟨hb, hrs⟩
  rcases hl with ⟨hmerge, hAS⟩
  subst b
  subst s
  subst A
  rcases hQ with ⟨hqQ, hR, hS, hT, hRS, hB, hC, hD, hAne, hRne, hSne, hTne⟩
  apply False.elim
  apply opposite_low_markers_ne
    (model .left q a q c d r r t) (model .interval q S B C D R S T) t T ht hT
    (fun v hv => left_low_derivative q a c d r t hr ht ha hq hc hd v hv)
    (fun v hv => interval_low_derivative q B C D R S T hR hS hT hRS hB hC hD hmerge v hv)
    he


private theorem right_uc_below_derivative {q a b d r s : ℤ}
    (hP : domain q a b q d r s s) (hu : a + b - r = q)
    (v : ℕ+) (hv : (v.val : ℤ) < q) :
    residualAugmentation (MvPolynomial.pderiv v (model .right q a b q d r s s)) =
      (if a = (v.val : ℤ) then (1 : ℚ) else 0) +
        (if b = (v.val : ℤ) then 1 else 0) := by
  rcases hP with ⟨hq, hr, hs, ht, ha, hb, hc, hd, hane, hrne, hsne, htne⟩
  have hbq : b ≠ q := by omega
  have hA : 0 < a := by omega
  have hB : 0 < b := by omega
  have hD : 0 < d := by omega
  have hV : 0 < b + q - s := by omega
  have hW : 0 < q + d - s := by omega
  have hF : 0 < a + b + q + d - r - 2 * s := by omega
  have hX : 0 < a + b + q - r - s := by omega
  have hY : 0 < b + q + d - 2 * s := by omega
  have hnD : d ≠ (v.val : ℤ) := by omega
  have hnV : b + q - s ≠ (v.val : ℤ) := by omega
  have hnW : q + d - s ≠ (v.val : ℤ) := by omega
  have hnF : a + b + q + d - r - 2 * s ≠ (v.val : ℤ) := by omega
  have hnX : a + b + q - r - s ≠ (v.val : ℤ) := by omega
  have hnY : b + q + d - 2 * s ≠ (v.val : ℤ) := by omega
  simp only [model, positive, negative, if_neg hbq, if_pos hu, List.nil_append,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, map_sub, map_add]
  rw [augmentation_pderiv_triple v a (b + q - s) d hA hV hD,
    augmentation_pderiv_triple v a b (q + d - s) hA hB hW,
    augmentation_pderiv_triple v r s (a + b + q + d - r - 2 * s) hr hs hF,
    augmentation_pderiv_triple v r (a + b + q - r - s) d hr hX hD,
    augmentation_pderiv_triple v s a (b + q + d - 2 * s) hs hA hY]
  simp only [if_neg hnD, if_neg hnV, if_neg hnW, if_neg hnF, if_neg hnX, if_neg hnY]
  ring

private theorem interval_uc_below_derivative {q b d r s t : ℤ}
    (hP : domain q s b q d r s t) (hu : s + b - r = q)
    (v : ℕ+) (hv : (v.val : ℤ) < q) :
    residualAugmentation (MvPolynomial.pderiv v (model .interval q s b q d r s t)) =
      (if b = (v.val : ℤ) then (1 : ℚ) else 0) +
        (if t = (v.val : ℤ) then 1 else 0) := by
  rcases hP with ⟨hq, hr, hs, ht, ha, hb, hc, hd, hane, hrne, hsne, htne⟩
  have hVq : b + q - s ≠ q := by omega
  have hB : 0 < b := by omega
  have hD : 0 < d := by omega
  have hV : 0 < b + q - s := by omega
  have hW : 0 < q + d - t := by omega
  have hF : 0 < q + q + d - s - t := by omega
  have hX : 0 < q + q - s := by omega
  have hY : 0 < b + q + d - s - t := by omega
  have hnD : d ≠ (v.val : ℤ) := by omega
  have hnV : b + q - s ≠ (v.val : ℤ) := by omega
  have hnW : q + d - t ≠ (v.val : ℤ) := by omega
  have hnF : q + q + d - s - t ≠ (v.val : ℤ) := by omega
  have hnX : q + q - s ≠ (v.val : ℤ) := by omega
  have hnY : b + q + d - s - t ≠ (v.val : ℤ) := by omega
  simp only [model, positive, negative, if_neg hVq, if_pos rfl, ite_true, ite_false,
    List.nil_append, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, map_sub, map_add, map_zero]
  rw [augmentation_pderiv_triple v s (b + q - s) d hs hV hD,
    augmentation_pderiv_triple v t b (q + d - t) ht hB hW,
    augmentation_pderiv_triple v r t (q + q + d - s - t) hr ht hF,
    augmentation_pderiv_triple v r (q + q - s) d hr hX hD,
    augmentation_pderiv_triple v s t (b + q + d - s - t) hs ht hY]
  simp only [if_neg hnD, if_neg hnV, if_neg hnW, if_neg hnF, if_neg hnX, if_neg hnY]
  ring

private theorem two_indicator_cancel (q x y z : ℤ) (hy : 0 < y) (hyq : y < q)
    (h : ∀ v : ℕ+, (v.val : ℤ) < q →
      (if x = (v.val : ℤ) then (1 : ℚ) else 0) + (if y = (v.val : ℤ) then 1 else 0) =
        (if x = (v.val : ℤ) then 1 else 0) + (if z = (v.val : ℤ) then 1 else 0)) :
    y = z := by
  let v : ℕ+ := ⟨y.toNat, by omega⟩
  have hv : (v.val : ℤ) = y := by dsimp [v]; omega
  have hh := add_left_cancel (h v (by omega))
  by_contra hne
  have hz : z ≠ (v.val : ℤ) := by omega
  norm_num only [hv, if_pos rfl, if_neg (Ne.symm hne), ite_true] at hh

private theorem two_indicator_reading (q a b A B : ℤ)
    (ha : 0 < a) (hb : 0 < b) (haq : a < q) (hbq : b < q)
    (h : ∀ v : ℕ+, (v.val : ℤ) < q →
      (if a = (v.val : ℤ) then (1 : ℚ) else 0) + (if b = (v.val : ℤ) then 1 else 0) =
        (if A = (v.val : ℤ) then 1 else 0) + (if B = (v.val : ℤ) then 1 else 0)) :
    (a = A ∧ b = B) ∨ (a = B ∧ b = A) := by
  have hit : a = A ∨ a = B := by
    by_contra hn
    push_neg at hn
    let v : ℕ+ := ⟨a.toNat, by omega⟩
    have hv : (v.val : ℤ) = a := by dsimp [v]; omega
    have hh := h v (by omega)
    simp only [hv, if_pos rfl, if_neg (Ne.symm hn.1), if_neg (Ne.symm hn.2)] at hh
    split_ifs at hh <;> norm_num at hh
  rcases hit with hA | hB
  · subst A
    exact Or.inl ⟨rfl, two_indicator_cancel q a b B hb hbq h⟩
  · subst B
    apply Or.inr
    refine ⟨rfl, two_indicator_cancel q a b A hb hbq ?_⟩
    intro v hv
    simpa only [add_comm] using h v hv

private theorem right_shape_counts {q a b c d r s t : ℤ}
    (hP : domain q a b c d r s t) (hk : contact .right q a b c r s t) :
    (a + b - r = q ↔
      (reducedPositive .right q a b c d r s t).length = 2 ∧
        (reducedNegative .right q a b c d r s t).length = 2) ∧
    (rightCancellation q a d r s ↔
      (reducedPositive .right q a b c d r s t).length = 1 ∧
        (reducedNegative .right q a b c d r s t).length = 2) := by
  by_cases hcancel : rightCancellation q a d r s
  · obtain ⟨hbq, hu⟩ := right_cancellation_survivors hP hk hcancel
    simp only [reducedPositive, reducedNegative, if_pos hcancel,
      List.length_cons, List.length_nil]
    norm_num [hu, hcancel]
  · by_cases hbq : b = q
    · have ha : r < a := hP.2.2.2.2.1
      have hu : a + b - r ≠ q := by omega
      simp only [reducedPositive, reducedNegative, if_neg hcancel, properPositive,
        negative, if_pos hbq, if_neg hu, ite_true, ite_false,
        List.length_append, List.length_cons, List.length_nil]
      norm_num [hu, hcancel]
    · by_cases hu : a + b - r = q
      · simp only [reducedPositive, reducedNegative, if_neg hcancel, properPositive,
          negative, if_neg hbq, if_pos hu, ite_true, ite_false,
          List.length_append, List.length_cons, List.length_nil]
        norm_num [hu, hcancel]
      · simp only [reducedPositive, reducedNegative, if_neg hcancel, properPositive,
          negative, if_neg hbq, if_neg hu, ite_true, ite_false,
          List.length_append, List.length_cons, List.length_nil]
        norm_num [hu, hcancel]

private theorem right_first_gap_eq {q a b c d r s t A B C D R S T : ℤ}
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact .right q a b c r s t) (hl : contact .right q A B C R S T)
    (hu : a + b - r ≠ q) (hU : A + B - R ≠ q)
    (he : model .right q a b c d r s t = model .right q A B C D R S T) : r = R := by
  rcases hk with ⟨hcq, hst⟩
  rcases hl with ⟨hCq, hST⟩
  subst c
  subst t
  subst C
  subst T
  rcases hP with ⟨hqP, hr, hs, _, ha, hb, hc, hd, hp8, hp9, hp10, hp11⟩
  rcases hQ with ⟨hqQ, hR, hS, _, hA, hB, hC, hD, hq8, hq9, hq10, hq11⟩
  have hp : ∀ v : ℕ+, (v.val : ℤ) ≤ r →
      residualAugmentation (MvPolynomial.pderiv v (model .right q a b q d r s s)) =
        -(if r = (v.val : ℤ) then 1 else 0) :=
    fun v hv => right_low_derivative q a b d r s hr hs ha (by omega) hb hd hu v hv
  have hf : ∀ v : ℕ+, (v.val : ℤ) ≤ R →
      residualAugmentation (MvPolynomial.pderiv v (model .right q A B q D R S S)) =
        -(if R = (v.val : ℤ) then 1 else 0) :=
    fun v hv => right_low_derivative q A B D R S hR hS hA (by omega) hB hD hU v hv
  rcases lt_trichotomy r R with hlt | heq | hgt
  · exact (negative_low_marker_not_lt _ _ r R hr hp hf he hlt).elim
  · exact heq
  · exact (negative_low_marker_not_lt _ _ R r hR hf hp he.symm hgt).elim

private theorem right_uc_matching {q a b d r s A B D R S : ℤ}
    (hP : domain q a b q d r s s) (hQ : domain q A B q D R S S)
    (hu : a + b - r = q) (hU : A + B - R = q)
    (hfull : cubicFullIndex a b q d r s s = cubicFullIndex A B q D R S S)
    (hgap : (r = R ∧ s = S) ∨ (r = S ∧ s = R))
    (hp : matching tripleRelation (reducedPositive .right q a b q d r s s)
      (reducedPositive .right q A B q D R S S))
    (he : model .right q a b q d r s s = model .right q A B q D R S S) :
    a = A ∧ b = B ∧ d = D ∧ r = R ∧ s = S := by
  have hhist (v : ℕ+) (hv : (v.val : ℤ) < q) :
      (if a = (v.val : ℤ) then (1 : ℚ) else 0) +
          (if b = (v.val : ℤ) then 1 else 0) =
        (if A = (v.val : ℤ) then 1 else 0) +
          (if B = (v.val : ℤ) then 1 else 0) := by
    have hh := congrArg (fun z : CompleteRing =>
      residualAugmentation (MvPolynomial.pderiv v z)) he
    rwa [right_uc_below_derivative hP hu v hv, right_uc_below_derivative hQ hU v hv] at hh
  rcases hP with ⟨hqP, hr, hs, _, ha, hb, hc, hd, hp8, hp9, hp10, hp11⟩
  rcases hQ with ⟨hqQ, hR, hS, _, hA, hB, hC, hD, hq8, hq9, hq10, hq11⟩
  have hread := two_indicator_reading q a b A B (by omega) (by omega)
    (by omega) (by omega) hhist
  have hrR : r = R := by
    rcases hread with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
  have hsS : s = S := by
    rcases hgap with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
  subst R
  subst S
  have hdD : d = D := by
    dsimp [cubicFullIndex] at hfull
    omega
  subst D
  rcases hread with ⟨haA, hbB⟩ | ⟨haB, hbA⟩
  · exact ⟨haA, hbB, rfl, rfl, rfl⟩
  · have hncP : ¬ rightCancellation q a d r s := by
      intro hn
      dsimp [rightCancellation] at hn
      omega
    have hncQ : ¬ rightCancellation q A d r s := by
      intro hn
      dsimp [rightCancellation] at hn
      omega
    have hbq : b ≠ q := by omega
    have hBq : B ≠ q := by omega
    have hh := matching_term_sum_eq hp
    simp only [reducedPositive, if_neg hncP, if_neg hncQ, properPositive,
      if_neg hbq, if_neg hBq, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hh
    rw [← hbA, ← haB] at hh
    have hword : tripleTerm ![b, a + (q - s), d] =
        tripleTerm ![a, b + (q - s), d] := by
      simp only [tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      have hUa : a + (q - s) = a + q - s := by omega
      have hUb : b + (q - s) = b + q - s := by omega
      rw [hUa, hUb]
      linear_combination -hh
    have hab := (shifted_word_eq_iff (q - s) a b d (by omega)
      (by omega) (by omega) (by omega)).mp hword
    exact ⟨by omega, by omega, rfl, rfl, rfl⟩

private theorem model_right_right
    (q a b c d r s t A B C D R S T : ℤ)
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact .right q a b c r s t) (hl : contact .right q A B C R S T)
    (he : model .right q a b c d r s t = model .right q A B C D R S T)
    (hfull : cubicFullIndex a b c d r s t = cubicFullIndex A B C D R S T)
    (hgap : (r = R ∧ leadingGap .right s t = leadingGap .right S T) ∨
      (r = leadingGap .right S T ∧ leadingGap .right s t = R))
    (hm : matching tripleRelation (reducedPositive .right q a b c d r s t)
        (reducedPositive .right q A B C D R S T) ∧
      matching tripleRelation (reducedNegative .right q a b c d r s t)
        (reducedNegative .right q A B C D R S T)) :
    alternatives q a b c d r s t A B C D R S T := by
  have hshapeP := right_shape_counts hP hk
  have hshapeQ := right_shape_counts hQ hl
  have hpLen := matching_lengths hm.1
  have hnLen := matching_lengths hm.2
  have huciff : a + b - r = q ↔ A + B - R = q := by
    rw [hshapeP.1, hshapeQ.1, hpLen, hnLen]
  have hcanceliff : rightCancellation q a d r s ↔ rightCancellation q A D R S := by
    rw [hshapeP.2, hshapeQ.2, hpLen, hnLen]
  rcases hk with ⟨hcq, hst⟩
  rcases hl with ⟨hCq, hST⟩
  subst c
  subst t
  subst C
  subst T
  by_cases hu : a + b - r = q
  · have hU := huciff.mp hu
    obtain ⟨haA, hbB, hdD, hrR, hsS⟩ :=
      right_uc_matching hP hQ hu hU hfull hgap hm.1 he
    exact Or.inl ⟨haA, hbB, rfl, hdD, hrR, hsS, hsS⟩
  · have hU : A + B - R ≠ q := fun h => hu (huciff.mpr h)
    have hrR := right_first_gap_eq hP hQ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hu hU he
    have hsS : s = S := by
      change (r = R ∧ s = S) ∨ (r = S ∧ s = R) at hgap
      rcases hgap with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
    subst R
    subst S
    by_cases hcancelP : rightCancellation q a d r s
    · have hcancelQ := hcanceliff.mp hcancelP
      rcases hcancelP with ⟨hdEq, haEq⟩
      rcases hcancelQ with ⟨hDEq, hAEq⟩
      have hbB : b = B := by
        dsimp [cubicFullIndex] at hfull
        omega
      exact Or.inl ⟨by omega, hbB, rfl, by omega, rfl, rfl, rfl⟩
    · have hcancelQ : ¬ rightCancellation q A D r s :=
        fun h => hcancelP (hcanceliff.mpr h)
      rcases hP with ⟨hqP, hr, hs, _, ha, hb, hc, hd, hp8, hp9, hp10, hp11⟩
      rcases hQ with ⟨hqQ, _, _, _, hA, hB, hC, hD, hq8, hq9, hq10, hq11⟩
      have hp := matching_term_sum_eq hm.1
      have hn := matching_term_sum_eq hm.2
      simp only [reducedPositive, if_neg hcancelP, if_neg hcancelQ] at hp
      simp only [reducedNegative, if_neg hcancelP, if_neg hcancelQ] at hn
      have hpRot :
          ((properPositive .left q d q b a s s r).map tripleTerm).sum =
            ((properPositive .left q D q B A s s r).map tripleTerm).sum :=
        (right_positive_rotate q a b d r s).symm.trans
          (hp.trans (right_positive_rotate q A B D r s))
      have hnRot :
          ((negative .left q d q b a s s r).map tripleTerm).sum =
            ((negative .left q D q B A s s r).map tripleTerm).sum :=
        (right_negative_rotate q a b d r s hu).symm.trans
          (hn.trans (right_negative_rotate q A B D r s hU))
      have hposRot : matching tripleRelation
          (properPositive .left q d q b a s s r)
          (properPositive .left q D q B A s s r) :=
        triple_matching _ _
          (formal_left_positive q d b a s r hs hr (by omega) (by omega) (by omega) ha)
          (formal_left_positive q D B A s r hs hr (by omega) (by omega) (by omega) hA) hpRot
      have hsum : d + b + a = D + B + A := by
        dsimp [cubicFullIndex] at hfull
        omega
      have hres := aligned_left_matching q d b a D B A s r hs hr
        (by omega) (by omega) (by omega) ha (by omega) (by omega) hA
        (by omega) (by omega) hsum hposRot hnRot
      exact alternatives_reverse
        (alternatives_mate_rotate (alternatives_reverse (alternatives_mate_rotate hres)))

private theorem model_right_interval
    (q a b c d r s t A B C D R S T : ℤ)
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact .right q a b c r s t) (hl : contact .interval q A B C R S T)
    (he : model .right q a b c d r s t = model .interval q A B C D R S T)
    (hfull : cubicFullIndex a b c d r s t = cubicFullIndex A B C D R S T)
    (hgap : (r = R ∧ leadingGap .right s t = leadingGap .interval S T) ∨
      (r = leadingGap .interval S T ∧ leadingGap .right s t = R))
    (hm : matching tripleRelation (reducedPositive .right q a b c d r s t)
        (reducedPositive .interval q A B C D R S T) ∧
      matching tripleRelation (reducedNegative .right q a b c d r s t)
        (reducedNegative .interval q A B C D R S T)) :
    alternatives q a b c d r s t A B C D R S T := by
  rcases hk with ⟨hcq, hst⟩
  rcases hl with ⟨hmerge, hAS⟩
  subst c
  subst t
  subst A
  have hDomP := hP
  have hDomQ := hQ
  rcases hP with ⟨hqP, hr, hs, _, ha, hb, hc, hd, hp8, hp9, hp10, hp11⟩
  rcases hQ with ⟨hqQ, hR, hS, hT, hRS, hB, hC, hD, hq8, hq9, hq10, hq11⟩
  by_cases hu : a + b - r = q
  · have hnc : ¬ rightCancellation q a d r s := by
      intro hn
      dsimp [rightCancellation] at hn
      omega
    have hCq : C = q := by
      by_contra hCq
      have hlen := matching_lengths hm.2
      simp only [reducedNegative, if_neg hnc, negative, if_pos hu, if_neg hCq,
        ite_true, ite_false, List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    subst C
    have hhist (v : ℕ+) (hv : (v.val : ℤ) < q) :
        (if a = (v.val : ℤ) then (1 : ℚ) else 0) +
            (if b = (v.val : ℤ) then 1 else 0) =
          (if B = (v.val : ℤ) then 1 else 0) +
            (if T = (v.val : ℤ) then 1 else 0) := by
      have hh := congrArg (fun z : CompleteRing =>
        residualAugmentation (MvPolynomial.pderiv v z)) he
      rwa [right_uc_below_derivative hDomP hu v hv,
        interval_uc_below_derivative hDomQ hmerge v hv] at hh
    have hread := two_indicator_reading q a b B T (by omega) (by omega)
      (by omega) (by omega) hhist
    have hsum : a + b = B + T := by
      rcases hread with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
    have horder : r = R ∧ s = T ∧ S = s := by
      change (r = R ∧ s = T) ∨ (r = T ∧ s = R) at hgap
      rcases hgap with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
    have haS : a = S := by
      rcases hread with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
    have hbB : b = B := by omega
    have hdD : d = D := by
      dsimp [cubicFullIndex] at hfull
      omega
    exact Or.inl ⟨haS, hbB, rfl, hdD, horder.1, by omega, by omega⟩
  · have hp : ∀ v : ℕ+, (v.val : ℤ) ≤ r →
        residualAugmentation (MvPolynomial.pderiv v (model .right q a b q d r s s)) =
          -(if r = (v.val : ℤ) then 1 else 0) :=
      fun v hv => right_low_derivative q a b d r s hr hs ha (by omega) hb hd hu v hv
    have hf : ∀ v : ℕ+, (v.val : ℤ) ≤ T →
        residualAugmentation (MvPolynomial.pderiv v (model .interval q S B C D R S T)) =
          (if T = (v.val : ℤ) then 1 else 0) :=
      fun v hv => interval_low_derivative q B C D R S T hR hS hT hRS hB hC hD hmerge v hv
    exact (opposite_low_markers_ne _ _ r T hr hT hp hf he).elim

private noncomputable def intervalTail (q b c d r s t : ℤ) : CompleteRing :=
  ((properPositive .interval q s b c d r s t).map tripleTerm).sum -
    ((negative .interval q s b c d r s t).map tripleTerm).sum

private theorem interval_tail_derivative (q b c d r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hrs : r < s)
    (hb : r + s < b) (hc : s + t < c) (hd : q + t < d)
    (hq : s + b - r = q) (v : ℕ+) (hv : b + c + d - s - t ≤ (v.val : ℤ)) :
    MvPolynomial.pderiv v (intervalTail q b c d r s t) =
      -(if b + c + d - s - t = (v.val : ℤ) then complete s * complete t else 0) := by
  have h0 : MvPolynomial.pderiv v (tripleTerm ![s, b + c - s, d]) = 0 := by
    apply triple_derivative_zero
    intro i
    fin_cases i <;> dsimp <;> omega
  have h1 : MvPolynomial.pderiv v (tripleTerm ![t, b, c + d - t]) = 0 := by
    apply triple_derivative_zero
    intro i
    fin_cases i <;> dsimp <;> omega
  have h2 : MvPolynomial.pderiv v (tripleTerm ![b, c, d]) = 0 := by
    apply triple_derivative_zero
    intro i
    fin_cases i <;> dsimp <;> omega
  have h3 : MvPolynomial.pderiv v (tripleTerm ![r, q + c - s, d]) = 0 := by
    apply triple_derivative_zero
    intro i
    fin_cases i <;> dsimp <;> omega
  have h4 : MvPolynomial.pderiv v (tripleTerm ![s, t, b + c + d - s - t]) =
      if b + c + d - s - t = (v.val : ℤ) then complete s * complete t else 0 := by
    have hnS : s ≠ (v.val : ℤ) := by omega
    have hnT : t ≠ (v.val : ℤ) := by omega
    simp only [tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      MvPolynomial.pderiv_mul, residual_pderiv_complete, if_neg hnS, if_neg hnT,
      zero_mul, mul_zero, zero_add, add_zero, mul_ite, mul_one]
  unfold intervalTail
  simp only [properPositive, negative]
  split_ifs
  all_goals simp only [
    List.nil_append, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, map_sub, map_add, h0, h1, h2, h3, h4,
    zero_add, add_zero, zero_sub]
  all_goals simp_all only [ite_true, ite_false]

private theorem interval_tail_gap_reading (q b c d r s t B C D S : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hrs : r < s)
    (hb : r + s < b) (hc : s + t < c) (hd : q + t < d)
    (hq : s + b - r = q) (hS : 0 < S) (hrS : r < S)
    (hB : r + S < B) (hC : S + t < C) (hD : q + t < D)
    (hQ : S + B - r = q)
    (he : intervalTail q b c d r s t = intervalTail q B C D r S t) : s = S := by
  have htop (v : ℕ+) (hv : (v.val : ℤ) = b + c + d - s - t) :
      MvPolynomial.pderiv v (intervalTail q b c d r s t) = -(complete s * complete t) := by
    rw [interval_tail_derivative q b c d r s t hr hs ht hrs hb hc hd hq v hv.symm.le,
      if_pos hv.symm]
  have hTop (v : ℕ+) (hv : (v.val : ℤ) = B + C + D - S - t) :
      MvPolynomial.pderiv v (intervalTail q B C D r S t) = -(complete S * complete t) := by
    rw [interval_tail_derivative q B C D r S t hr hS ht hrS hB hC hD hQ v hv.symm.le,
      if_pos hv.symm]
  have habove (v : ℕ+) (hv : b + c + d - s - t < (v.val : ℤ)) :
      MvPolynomial.pderiv v (intervalTail q b c d r s t) = 0 := by
    rw [interval_tail_derivative q b c d r s t hr hs ht hrs hb hc hd hq v hv.le,
      if_neg (ne_of_lt hv), neg_zero]
  have hAbove (v : ℕ+) (hv : B + C + D - S - t < (v.val : ℤ)) :
      MvPolynomial.pderiv v (intervalTail q B C D r S t) = 0 := by
    rw [interval_tail_derivative q B C D r S t hr hS ht hrS hB hC hD hQ v hv.le,
      if_neg (ne_of_lt hv), neg_zero]
  have ht0 := (complete_ne_zero_iff t).mpr ht.le
  have hs0 := (complete_ne_zero_iff s).mpr hs.le
  have hS0 := (complete_ne_zero_iff S).mpr hS.le
  have hread := private_top_reading _ _ _ _ _ _ (by omega) (by omega)
    (neg_ne_zero.mpr (mul_ne_zero hs0 ht0)) (neg_ne_zero.mpr (mul_ne_zero hS0 ht0))
    htop hTop habove hAbove he
  have hprod := neg_injective hread.2
  have hgen := mul_right_cancel₀ ht0 hprod
  exact complete_injective_nonnegative hs.le hS.le hgen


private theorem interval_cross_not_lt (q b c d C D r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hrs : r < s)
    (hb : r + s < b) (hc : s + t < c) (hd : q + t < d)
    (hC : s + t < C) (hD : q + t < D) (hq : s + b - r = q)
    (hcross : d = b + C - s ∧ D = b + c - s) (hlt : C < c)
    (he : ((negative .interval q s b c d r s t).map tripleTerm).sum =
      ((negative .interval q s b C D r s t).map tripleTerm).sum) : False := by
  let X := q + c - s
  let v : ℕ+ := ⟨X.toNat, by dsimp [X]; omega⟩
  have hv : (v.val : ℤ) = X := by dsimp [v]; omega
  have hzP0 : MvPolynomial.pderiv v (tripleTerm ![b, c, d]) = 0 := by
    apply triple_derivative_zero
    intro i
    fin_cases i <;> dsimp <;> dsimp [X] at hv <;> omega
  have hzQ0 : MvPolynomial.pderiv v (tripleTerm ![b, C, D]) = 0 := by
    apply triple_derivative_zero
    intro i
    fin_cases i <;> dsimp <;> dsimp [X] at hv <;> omega
  have hzP2 : MvPolynomial.pderiv v
      (tripleTerm ![s, t, b + c + d - s - t]) = 0 := by
    apply triple_derivative_zero
    intro i
    fin_cases i <;> dsimp <;> dsimp [X] at hv <;> omega
  have hzQ1 : MvPolynomial.pderiv v (tripleTerm ![r, q + C - s, D]) = 0 := by
    apply triple_derivative_zero
    intro i
    fin_cases i <;> dsimp <;> dsimp [X] at hv <;> omega
  have hzQ2 : MvPolynomial.pderiv v
      (tripleTerm ![s, t, b + C + D - s - t]) = 0 := by
    apply triple_derivative_zero
    intro i
    fin_cases i <;> dsimp <;> dsimp [X] at hv <;> omega
  have hp1 : MvPolynomial.pderiv v (tripleTerm ![r, q + c - s, d]) =
      complete r * complete d := by
    have horder : tripleTerm ![r, q + c - s, d] =
        complete r * complete d * complete (q + c - s) := by
      simp only [tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring
    rw [horder]
    exact product_derivative_top v _ _ _ (by dsimp [X] at hv; omega)
      (by dsimp [X] at hv; omega) hv.symm
  have he' := congrArg (MvPolynomial.pderiv v) he
  have hn : complete r * complete d ≠ 0 :=
    mul_ne_zero ((complete_ne_zero_iff r).mpr hr.le)
      ((complete_ne_zero_iff d).mpr (by omega))
  simp only [negative] at he'
  split_ifs at he'
  all_goals simp only [List.nil_append,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, map_add,
    hzP0, hp1, hzP2, hzQ0, hzQ1, hzQ2, zero_add, add_zero] at he'
  all_goals exact hn he'

private theorem interval_cross_eq (q b c d C D r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hrs : r < s)
    (hb : r + s < b) (hc : s + t < c) (hd : q + t < d)
    (hC : s + t < C) (hD : q + t < D) (hq : s + b - r = q)
    (hcross : d = b + C - s ∧ D = b + c - s)
    (he : ((negative .interval q s b c d r s t).map tripleTerm).sum =
      ((negative .interval q s b C D r s t).map tripleTerm).sum) : c = C := by
  rcases lt_trichotomy c C with hlt | heq | hgt
  · exact (interval_cross_not_lt q b C D c d r s t hr hs ht hrs hb hC hD
      hc hd hq ⟨hcross.2, hcross.1⟩ hlt he.symm).elim
  · exact heq
  · exact (interval_cross_not_lt q b c d C D r s t hr hs ht hrs hb hc hd
      hC hD hq hcross hgt he).elim

private theorem model_interval_interval
    (q a b c d r s t A B C D R S T : ℤ)
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact .interval q a b c r s t) (hl : contact .interval q A B C R S T)
    (he : model .interval q a b c d r s t = model .interval q A B C D R S T)
    (hfull : cubicFullIndex a b c d r s t = cubicFullIndex A B C D R S T)
    (hgap : (r = R ∧ leadingGap .interval s t = leadingGap .interval S T) ∨
      (r = leadingGap .interval S T ∧ leadingGap .interval s t = R))
    (hm : matching tripleRelation (reducedPositive .interval q a b c d r s t)
        (reducedPositive .interval q A B C D R S T) ∧
      matching tripleRelation (reducedNegative .interval q a b c d r s t)
        (reducedNegative .interval q A B C D R S T)) :
    alternatives q a b c d r s t A B C D R S T := by
  have houter : t = T := interval_outer_gap_eq hP hQ hk hl he
  have hfirst : r = R := by
    change (r = R ∧ t = T) ∨ (r = T ∧ t = R) at hgap
    rcases hgap with hgap | hgap
    · exact hgap.1
    · exact hgap.1.trans (houter.symm.trans hgap.2)
  clear he hgap
  rcases hk with ⟨hmerge, has⟩
  rcases hl with ⟨hMerge, hAS⟩
  subst a
  subst A
  subst R
  subst T
  rcases hP with ⟨hqP, hr, hs, ht, hrs, hb, hc, hd, hp8, hp9, hp10, hp11⟩
  rcases hQ with ⟨hqQ, _, hS, _, hrS, hB, hC, hD, hq8, hq9, hq10, hq11⟩
  have hp := matching_term_sum_eq hm.1
  have hn := matching_term_sum_eq hm.2
  change ((properPositive .interval q s b c d r s t).map tripleTerm).sum =
    ((properPositive .interval q S B C D r S t).map tripleTerm).sum at hp
  change ((negative .interval q s b c d r s t).map tripleTerm).sum =
    ((negative .interval q S B C D r S t).map tripleTerm).sum at hn
  have htail : intervalTail q b c d r s t = intervalTail q B C D r S t := by
    unfold intervalTail
    linear_combination hp - hn
  have hmid := interval_tail_gap_reading q b c d r s t B C D S
    hr hs ht hrs hb hc hd hmerge hS hrS hB hC hD hMerge htail
  subst S
  have hbB : b = B := by omega
  subst B
  have hsum : c + d = C + D := by
    dsimp [cubicFullIndex] at hfull
    omega
  have finish (hcC : c = C) : alternatives q s b c d r s t s b C D r s t :=
    Or.inl ⟨rfl, rfl, hcC, by omega, rfl, rfl, rfl⟩
  have hpos := hm.1
  change matching tripleRelation (properPositive .interval q s b c d r s t)
    (properPositive .interval q s b C D r s t) at hpos
  by_cases hV : b + c - s = q
  · by_cases hQ : b + C - s = q
    · exact finish (by omega)
    · have hlen := matching_lengths hpos
      simp only [properPositive, if_pos hV, if_neg hQ, List.length_append,
        List.length_cons, List.length_nil] at hlen
      omega
  · by_cases hQ : b + C - s = q
    · have hlen := matching_lengths hpos
      simp only [properPositive, if_neg hV, if_pos hQ, List.length_append,
        List.length_cons, List.length_nil] at hlen
      omega
    · have hW : c + d - t = C + D - t := by omega
      simp only [properPositive, if_neg hV, if_neg hQ, List.map_append,
        List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero] at hp
      have hword : tripleTerm ![s, b + c - s, d] =
          tripleTerm ![s, b + C - s, D] := by
        rw [hW] at hp
        exact add_right_cancel hp
      have hpair : complete (b + c - s) * complete d =
          complete (b + C - s) * complete D := by
        apply mul_left_cancel₀ ((complete_ne_zero_iff s).mpr hs.le)
        simpa only [tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val, mul_assoc] using hword
      rcases complete_two_product_reading (by omega) (by omega)
          (by omega) (by omega) hpair with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact finish (by omega)
      · exact finish (interval_cross_eq q b c d C D r s t hr hs ht hrs
          hb hc hd hC hD hmerge ⟨h1, h0.symm⟩ hn)

/-- Uniform symbolic elimination of the exact collected cubic inventory.
Reversing the two profiles reuses the same extraction mechanism proof. -/
theorem model_necessity (k l : Kind)
    (q a b c d r s t A B C D R S T : ℤ)
    (hP : domain q a b c d r s t) (hQ : domain q A B C D R S T)
    (hk : contact k q a b c r s t) (hl : contact l q A B C R S T)
    (he : model k q a b c d r s t = model l q A B C D R S T) :
    alternatives q a b c d r s t A B C D R S T := by
  obtain ⟨hfull, hgap, hpos, hneg⟩ :=
    model_signed_matching k l q a b c d r s t A B C D R S T hP hQ hk hl he
  cases k <;> cases l
  · exact model_left_left q a b c d r s t A B C D R S T hP hQ hk hl he hfull hgap ⟨hpos, hneg⟩
  · exact model_left_right q a b c d r s t A B C D R S T hP hQ hk hl he hfull hgap ⟨hpos, hneg⟩
  · exact model_left_interval q a b c d r s t A B C D R S T hP hQ hk hl he
  · obtain ⟨hf, hg, hp, hn⟩ := model_signed_matching .left .right
      q A B C D R S T a b c d r s t hQ hP hl hk he.symm
    exact alternatives_reverse
      (model_left_right q A B C D R S T a b c d r s t hQ hP hl hk he.symm hf hg ⟨hp, hn⟩)
  · exact model_right_right q a b c d r s t A B C D R S T hP hQ hk hl he hfull hgap ⟨hpos, hneg⟩
  · exact model_right_interval q a b c d r s t A B C D R S T hP hQ hk hl he hfull hgap ⟨hpos, hneg⟩
  · exact alternatives_reverse
      (model_left_interval q A B C D R S T a b c d r s t hQ hP hl hk he.symm)
  · obtain ⟨hf, hg, hp, hn⟩ := model_signed_matching .right .interval
      q A B C D R S T a b c d r s t hQ hP hl hk he.symm
    exact alternatives_reverse
      (model_right_interval q A B C D R S T a b c d r s t hQ hP hl hk he.symm hf hg ⟨hp, hn⟩)
  · exact model_interval_interval q a b c d r s t A B C D R S T hP hQ hk hl he hfull hgap ⟨hpos, hneg⟩


theorem familyA_orbit_of_coordinates {q : ℕ+} {P : Profile 3} {a z : ℕ}
    (ha : z + z < a) (hq : z + z < q.val)
    (hg : ∀ j, P.g j = z)
    (hr : rowsA q.val a z (P.r 0) (P.r 1) (P.r 2) (P.r 3)) :
    P = residualFamilyA a q.val z z ha hq ∨
      P = (residualFamilyA a q.val z z ha hq).rotate := by
  rcases hr with hr | hr
  · left
    apply Profile.ext
    · funext i
      fin_cases i <;> simp [residualFamilyA] <;> omega
    · funext j
      fin_cases j <;> simp [residualFamilyA, hg]
  · right
    apply Profile.ext
    · funext i
      fin_cases i <;> simp [residualFamilyA, Profile.rotate] <;> omega
    · funext j
      fin_cases j <;> simp [residualFamilyA, Profile.rotate, hg]

theorem familyB_orbit_of_coordinates {q : ℕ+} {P : Profile 3} {a z : ℕ}
    (ha : z + z < a) (hq : z + z < q.val)
    (hg : ∀ j, P.g j = z)
    (hr : rowsB q.val a z (P.r 0) (P.r 1) (P.r 2) (P.r 3)) :
    P = residualFamilyB a q.val z z ha hq ∨
      P = (residualFamilyB a q.val z z ha hq).rotate := by
  rcases hr with hr | hr
  · left
    apply Profile.ext
    · funext i
      fin_cases i <;> simp [residualFamilyB] <;> omega
    · funext j
      fin_cases j <;> simp [residualFamilyB, hg]
  · right
    apply Profile.ext
    · funext i
      fin_cases i <;> simp [residualFamilyB, Profile.rotate] <;> omega
    · funext j
      fin_cases j <;> simp [residualFamilyB, Profile.rotate, hg]

theorem quartet_profiles {q : ℕ+} {P Q : Profile 3} {a z : ℕ}
    (h : quartet q.val a z
      (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2)
      (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.g 0) (Q.g 1) (Q.g 2)) :
    ∃ ha : z + z < a, ∃ hq : z + z < q.val,
      0 < z ∧ a ≠ q.val ∧
      (((P = residualFamilyA a q.val z z ha hq ∨
          P = (residualFamilyA a q.val z z ha hq).rotate) ∧
        (Q = residualFamilyB a q.val z z ha hq ∨
          Q = (residualFamilyB a q.val z z ha hq).rotate)) ∨
       ((P = residualFamilyB a q.val z z ha hq ∨
          P = (residualFamilyB a q.val z z ha hq).rotate) ∧
        (Q = residualFamilyA a q.val z z ha hq ∨
          Q = (residualFamilyA a q.val z z ha hq).rotate))) := by
  obtain ⟨hz, hq, ha, hne, hr, hs, ht, hR, hS, hT, hrows⟩ := h
  have ha' : z + z < a := by omega
  have hq' : z + z < q.val := by omega
  have hPg : ∀ j, P.g j = z := by
    intro j
    fin_cases j <;> dsimp <;> omega
  have hQg : ∀ j, Q.g j = z := by
    intro j
    fin_cases j <;> dsimp <;> omega
  refine ⟨ha', hq', by omega, by omega, ?_⟩
  rcases hrows with ⟨hPA, hQB⟩ | ⟨hPB, hQA⟩
  · exact Or.inl ⟨familyA_orbit_of_coordinates ha' hq' hPg hPA,
      familyB_orbit_of_coordinates ha' hq' hQg hQB⟩
  · exact Or.inr ⟨familyB_orbit_of_coordinates ha' hq' hPg hPB,
      familyA_orbit_of_coordinates ha' hq' hQg hQA⟩

end CubicNecessity

/-- Nonendpoint four-row cubic necessity for the actual canonical primitive.
The ambient component predicates retain only legal orientations of the two
constant-gap residual families. -/
theorem four_nonendpoint_cubic_necessity {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 ≠ q.val) (hA : Q.r 0 ≠ q.val)
    (hdP : (canonicalPrimitive hP).totalDegree = 3)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ) :
    P = Q ∨ P = Q.rotate ∨
      ∃ a z : ℕ, ∃ ha' : z + z < a, ∃ hq' : z + z < q.val,
        0 < z ∧ a ≠ q.val ∧
        (((P = residualFamilyA a q.val z z ha' hq' ∨
            P = (residualFamilyA a q.val z z ha' hq').rotate) ∧
          (Q = residualFamilyB a q.val z z ha' hq' ∨
            Q = (residualFamilyB a q.val z z ha' hq').rotate)) ∨
         ((P = residualFamilyB a q.val z z ha' hq' ∨
            P = (residualFamilyB a q.val z z ha' hq').rotate) ∧
          (Q = residualFamilyA a q.val z z ha' hq' ∨
            Q = (residualFamilyA a q.val z z ha' hq').rotate))) := by
  have hdQ : (canonicalPrimitive hQ).totalDegree = 3 := by
    rw [← he]
    exact hdP
  obtain ⟨k, hk, hmodelP⟩ := CubicNecessity.actual_model hP ha hdP
  obtain ⟨l, hl, hmodelQ⟩ := CubicNecessity.actual_model hQ hA hdQ
  have hmodels := hmodelP.symm.trans (he.trans hmodelQ)
  have hclass := CubicNecessity.model_necessity k l
    q.val (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2)
    (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.g 0) (Q.g 1) (Q.g 2)
    (CubicNecessity.domain_of_component hP ha)
    (CubicNecessity.domain_of_component hQ hA) hk hl hmodels
  rcases hclass with hid | hrot | hfirst | hlast
  · left
    dsimp [CubicNecessity.identityCoordinates] at hid
    apply Profile.ext
    · funext i
      fin_cases i <;> dsimp <;> omega
    · funext j
      fin_cases j <;> dsimp <;> omega
  · right
    left
    dsimp [CubicNecessity.rotationCoordinates] at hrot
    apply Profile.ext
    · funext i
      fin_cases i <;> dsimp <;> simp [Profile.rotate, Fin.rev] <;> omega
    · funext j
      fin_cases j <;> dsimp <;> simp [Profile.rotate, Fin.rev] <;> omega
  · right
    right
    exact ⟨P.r 0, P.g 0,
      CubicNecessity.quartet_profiles (a := P.r 0) (z := P.g 0) hfirst⟩
  · right
    right
    exact ⟨P.r 3, P.g 0,
      CubicNecessity.quartet_profiles (a := P.r 3) (z := P.g 0) hlast⟩


/-- Complete cubic matching: endpoint lifts are recognized by cross-size
rigidity; the remaining actual four-row cubics have exactly the source alternatives. -/
theorem four_cubic_residual_match_iff {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hdP : (canonicalPrimitive hP).totalDegree = 3)
    (hdQ : (canonicalPrimitive hQ).totalDegree = 3) :
    canonicalPrimitive hP = canonicalPrimitive hQ ↔ cubicResidualAlternatives q P Q := by
  constructor
  · intro he
    by_cases ha : P.r 0 = q.val
    · by_cases hA : Q.r 0 = q.val
      · exact Or.inl ⟨ha, hA, (endpoint_cubic_lifts_match_iff hP hQ ha hA hdP hdQ).mp he⟩
      · have hC := four_endpoint_contract_component hP ha
        have hdC : (canonicalPrimitive hC).totalDegree = 3 := by
          rw [← four_endpoint_contract_canonical hP ha]
          exact hdP
        have heC : canonicalPrimitive hQ = canonicalPrimitive hC := by
          rw [← four_endpoint_contract_canonical hP ha]
          exact he.symm
        exact (hA (cross_size_cubic_match hQ hC hdQ hdC heC).1).elim
    · by_cases hA : Q.r 0 = q.val
      · have hD := four_endpoint_contract_component hQ hA
        have hdD : (canonicalPrimitive hD).totalDegree = 3 := by
          rw [← four_endpoint_contract_canonical hQ hA]
          exact hdQ
        have heD : canonicalPrimitive hP = canonicalPrimitive hD := by
          rw [← four_endpoint_contract_canonical hQ hA]
          exact he
        exact (ha (cross_size_cubic_match hP hD hdP hdD heD).1).elim
      · rcases four_nonendpoint_cubic_necessity hP hQ ha hA hdP he with hid | hrot |
          ⟨a, z, ha', hq', hz, haneq, hrel⟩
        · exact Or.inr (Or.inl hid)
        · exact Or.inr (Or.inr (Or.inl hrot))
        · exact Or.inr (Or.inr (Or.inr ⟨a, z, ha', hq', hz, haneq, hrel⟩))
  · exact cubicResidualAlternatives_canonical_eq hP hQ hdP hdQ

end SkewJacobiNegative.Staircase
