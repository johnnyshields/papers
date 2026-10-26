/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.Blocks
import SkewCoframeRigidity.FixedCap.LeftTop
import SkewCoframeRigidity.FixedCap.Factor
import SkewCoframeRigidity.FixedCap.Descent

/-!
# One step of the descent of `sc:fixed-cap`

Formalizes the passage from a common prefix of two diagrams to the next strict block in the proof of
`sc:fixed-cap` of `shields-2026-skew-coframe-rigidity.tex`.  Given two connected normalized diagrams
with the same span, the two observations of `sc:fcp-observations`, and a common prefix of `q` proper
rows and columns cut off from the rest, either the two right coframes agree or the common prefix
extends by one strict block (`step`).  The induction hypothesis is the theorem itself for every
smaller child span.  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

/-- Fixed-cap rigidity for every cap and every pair of diagrams of child span `c`. -/
def CapRigidAt (c : ℕ) : Prop :=
  ∀ {k : ℕ} (K : BetaDiagram (k + 1)) (hK : IsNorm K), K.Connected →
    ∀ {b b' : ℕ} (B : BetaDiagram (b + 1)) (B' : BetaDiagram (b' + 1)) (hB : IsNorm B)
      (hB' : IsNorm B'), B.Connected → B'.Connected → span B = c → B.schur = B'.schur →
      (splice K B hK hB).schur = (splice K B' hK hB').schur → b = b' ∧ HEq B B'

/-- A product identity between coherent determinants descends to the physical ones. -/
theorem schur_mul_of_coh {m1 m2 m3 m4 : ℕ} {D1 : BetaDiagram m1} {D2 : BetaDiagram m2}
    {D3 : BetaDiagram m3} {D4 : BetaDiagram m4}
    (h : schurOf cohLetters D1 * schurOf cohLetters D2 =
      schurOf cohLetters D3 * schurOf cohLetters D4) :
    D1.schur * D2.schur = D3.schur * D4.schur := by
  rw [← algebraMap_cohSchur, ← algebraMap_cohSchur, ← algebraMap_cohSchur,
    ← algebraMap_cohSchur, ← map_mul, ← map_mul] at h
  have h1 := IsFractionRing.injective CohRing CohField h
  have h2 := congrArg physSpec h1
  rw [map_mul, map_mul] at h2
  have e : ∀ {m : ℕ} (D : BetaDiagram m), physSpec (cohSchur D) = physInclude D.schur :=
    fun D => physSpec_schurOf D
  rw [e, e, e, e, ← map_mul, ← map_mul] at h2
  exact physInclude_injective h2

/-- The same with one factor `ϑ` on the right, which becomes `1` physically. -/
theorem schur_mul_of_coh_theta {m1 m2 m3 : ℕ} {D1 : BetaDiagram m1} {D2 : BetaDiagram m2}
    {D3 : BetaDiagram m3}
    (h : schurOf cohLetters D1 * schurOf cohLetters D2 =
      cohLetters 0 * schurOf cohLetters D3) : D1.schur * D2.schur = D3.schur := by
  rw [← algebraMap_cohSchur, ← algebraMap_cohSchur, ← algebraMap_cohSchur,
    ← map_mul] at h
  have e0 : cohLetters 0 = algebraMap CohRing CohField (MvPolynomial.X 0) := rfl
  rw [e0, ← map_mul] at h
  have h1 := IsFractionRing.injective CohRing CohField h
  have h2 := congrArg physSpec h1
  rw [map_mul, map_mul] at h2
  have e : ∀ {m : ℕ} (D : BetaDiagram m), physSpec (cohSchur D) = physInclude D.schur :=
    fun D => physSpec_schurOf D
  have hX : physSpec (MvPolynomial.X 0 : CohRing) = 1 := by simp [physSpec]
  rw [e, e, e, hX, one_mul, ← map_mul] at h2
  exact physInclude_injective h2

variable {n : ℕ}

/-- **The outcome of the next strict block on one side**: the cut `r` closing it, and the value of
the block quantity as a unit or as a numerator over the block's function. -/
theorem block_info {q t : ℕ} {hq : q ≤ n} {K : BetaDiagram (q + 1)} (hKc : K.Connected)
    (hKn : IsNorm K) {D : BetaDiagram (n + 1)} (hDc : D.Connected) (hD : IsNorm D)
    (hm : CapMatches D hq (t : ℤ) K) (hqn : q < n) (hcq : CutAt D q)
    (ht : D.row ⟨q + 1, by omega⟩ = t) :
    ∃ r, q < r ∧ r ≤ n ∧ CutAt D r ∧
      ((r = q + 1 ∧ D.col ⟨q, by omega⟩ = t ∧
          betaOf K D t * (cornerOf cohLetters K * cohLetters 0) = -schurOf cohLetters K) ∨
        ∃ (m0 : ℕ) (E : BetaDiagram (m0 + 1)) (b0 : ℤ) (hEn : IsNorm E), r = q + m0 + 1 ∧
          E.Connected ∧ BlockRel D q m0 E b0 ∧
          betaOf K D t * (cornerOf cohLetters K * schurOf cohLetters E) =
            -schurOf cohLetters (splice K E hKn hEn)) := by
  obtain ⟨r, hqr, hrn, hcr, -, hcase⟩ := exists_block hDc hqn
  refine ⟨r, hqr, hrn, hcr, ?_⟩
  rcases hcase with ⟨hr1, hu⟩ | ⟨m0, E, b0, hr, hEn, hEc, hrel, -⟩
  · left
    subst hr1
    refine ⟨rfl, by rw [hu, ht], ?_⟩
    exact betaOf_unit hKc hKn hDc hD hm hqn hcq hcr ht (by rw [hu, ht])
  · right
    subst hr
    exact ⟨m0, E, b0, hEn, rfl, hEc, hrel,
      betaOf_block hKc hKn hDc hD hm hEn hEc hrel hcq hcr ht⟩

theorem row_nonneg_of_norm {m : ℕ} (D : BetaDiagram (m + 1)) (hD : IsNorm D) (i : Fin (m + 1)) :
    0 ≤ D.row i := by
  have := D.row_nonempty i
  have := col_nonneg D hD i
  omega

/-- The two diagrams agree on the first `q` proper rows and columns. -/
def PrefEq (B B' : BetaDiagram (n + 1)) (q : ℕ) : Prop :=
  (∀ i : Fin (n + 1), 1 ≤ i.val → i.val ≤ q → B.row i = B'.row i) ∧
    ∀ j : Fin (n + 1), j.val < q → B.col j = B'.col j

/-- A common cut at `r` beyond which the two diagrams still agree up to `r`. -/
def ExtendsTo (B B' : BetaDiagram (n + 1)) (r : ℕ) : Prop :=
  CutAt B r ∧ CutAt B' r ∧ PrefEq B B' r

theorem PrefEq.rowPos {B B' : BetaDiagram (n + 1)} {q : ℕ} (h : PrefEq B B' q) (hB : IsNorm B)
    (hB' : IsNorm B') (i : Fin n) (hi : i.val < q) : rowPos B i = rowPos B' i := by
  have h1 := h.1 i.succ (by simp) (by simp; omega)
  have h2 := rowPos_cast B i
  have h3 := rowPos_cast B' i
  have h0 : B.col (Fin.last n) = 0 := hB
  have h0' : B'.col (Fin.last n) = 0 := hB'
  omega

theorem PrefEq.colPos {B B' : BetaDiagram (n + 1)} {q : ℕ} (h : PrefEq B B' q) (hB : IsNorm B)
    (hB' : IsNorm B') (j : Fin n) (hj : j.val < q) : colPos B j = colPos B' j := by
  have h1 := h.2 j.castSucc (by simp; omega)
  have h2 := colPos_cast B j
  have h3 := colPos_cast B' j
  have h0 : B.col (Fin.last n) = 0 := hB
  have h0' : B'.col (Fin.last n) = 0 := hB'
  omega

variable {k : ℕ}

/-- **The block quantity agrees on the two diagrams.**  Once the zero range reaches `t + 1`, the
derivative of the first observation at `h_t` says that the block quantities of the two diagrams,
read through the recursive cap, coincide. -/
theorem beta_setup (K0 : BetaDiagram (k + 1)) (hK0 : IsNorm K0) {B B' : BetaDiagram (n + 1)}
    (hB : IsNorm B) (hB' : IsNorm B') (hBc : B.Connected) (hB'c : B'.Connected)
    (hspan : span B = span B')
    (hO1 : PowerSeries.coeff (span B) (letterSeries *
      ((coframe B - coframe B' : CohField[X]) : PowerSeries CohField)) = 0)
    {q t : ℕ} (hqn : q < n) (hcut : CutAt B q) (hpre : PrefEq B B' q)
    (ht : B.row ⟨q + 1, by omega⟩ = t)
    (hZR : ∀ j, j + (t + 1) ≤ span B + span K0 → (coframe B - coframe B').coeff j = 0) :
    ∃ (K : BetaDiagram (q + 1)) (hKn : IsNorm K), K.Connected ∧
      CapMatches B (by omega : q ≤ n) (t : ℤ) K ∧ CapMatches B' (by omega : q ≤ n) (t : ℤ) K ∧
      betaOf K B t = betaOf K B' t := by
  have hq : q ≤ n := by omega
  have ha : 1 ≤ span K0 := by
    have := span_eq_of_norm K0 hK0
    have := top_pos K0 hK0
    omega
  have ht1 : (t : ℤ) < B.row ⟨q, by omega⟩ := by
    have := B.row_strictAnti (show (⟨q, by omega⟩ : Fin (n + 1)) < ⟨q + 1, by omega⟩ from by
      rw [Fin.lt_def]; simp)
    omega
  have hcol1 : ∀ i : Fin (n + 1), i.val < q → (t : ℤ) < B.col i := by
    intro i hi
    have := hcut ⟨q, hqn⟩ ⟨i.val, by omega⟩ le_rfl hi
    have e : B.row (⟨q, hqn⟩ : Fin n).succ = B.row ⟨q + 1, by omega⟩ := rfl
    have e2 : B.col (⟨i.val, by omega⟩ : Fin n).castSucc = B.col i := rfl
    omega
  set K := capOf B q hq (t : ℤ) ht1 hcol1 with hK
  have hKn : IsNorm K := capOf_isNorm B q hq (t : ℤ) ht1 hcol1
  have hKc : K.Connected := capOf_connected B q hq (t : ℤ) ht1 hcol1 hBc
  have hm : CapMatches B hq (t : ℤ) K :=
    ⟨fun i => (capOf_row B q hq (t : ℤ) ht1 hcol1 i).symm, fun j =>
      (capOf_col_of_lt B q hq (t : ℤ) ht1 hcol1 j.castSucc (by simp)).symm⟩
  have hm' : CapMatches B' hq (t : ℤ) K := by
    constructor
    · intro i
      rw [← (hm.1 i)]
      by_cases hi0 : i.val = 0
      · have e : Fin.castLE (by omega : q + 1 ≤ n + 1) i = 0 := Fin.ext hi0
        rw [e]
        have h1 := row_zero_eq B hB
        have h2 := row_zero_eq B' hB'
        have h3 := span_cast B
        have h4 := span_cast B'
        omega
      · rw [← hpre.1 (Fin.castLE (by omega : q + 1 ≤ n + 1) i) (by simp; omega)
          (by simp; omega)]
    · intro j
      rw [← (hm.2 j), ← hpre.2 (Fin.castLE (by omega : q + 1 ≤ n + 1) j.castSucc) (by simp)]
  refine ⟨K, hKn, hKc, hm, hm', ?_⟩
  have hQ : t ≤ span B → (coframe B - coframe B').coeff (span B - t) = 0 := fun h =>
    hZR _ (by omega)
  have hO := coeff_span_dCoframe_sub t hspan hO1 hQ
  refine betaOf_eq hKc hBc hB'c hB hB' hm hm' t hspan (fun i hi => hpre.rowPos hB hB' i hi)
    (fun i hi hti => ?_) hO
  have := hZR (rowPos B i - t) (by have := rowPos_lt_span B i; omega)
  rwa [Polynomial.coeff_sub, sub_eq_zero] at this

theorem largestLabel_lt_splice {k b : ℕ} (K : BetaDiagram (k + 1)) (E : BetaDiagram (b + 1))
    (hK : IsNorm K) (hE : IsNorm E) : E.largestLabel < (splice K E hK hE).largestLabel := by
  have h1 := splice_span K E hK hE
  have h2 : (splice K E hK hE).col (Fin.last (k + b)) = 0 := splice_norm K E hK hE
  have h3 : E.col (Fin.last b) = 0 := hE
  have h4 := top_pos K hK
  unfold BetaDiagram.largestLabel
  rw [h2, h3]
  omega

/-- A positive cut condition: the row of the next block lies below every prefix column. -/
theorem rowPos_proper_lt_span {D : BetaDiagram (n + 1)} (hD : IsNorm D) {q t : ℕ} (hqn : q < n)
    (ht : D.row ⟨q + 1, by omega⟩ = t) : t < span D := by
  have h1 := rowPos_eq_of_row hD hqn ht
  have h2 := rowPos_lt_span D ⟨q, hqn⟩
  omega

/-- **The two sides' next blocks agree**, given that the block quantities coincide and the induction
hypothesis holds below `c`. -/
theorem step_blocks {c : ℕ} (IH : ∀ c' < c, CapRigidAt c') {B B' : BetaDiagram (n + 1)}
    (hB : IsNorm B) (hB' : IsNorm B') (hBc : B.Connected) (hB'c : B'.Connected)
    (hcB : span B = c) {q t : ℕ} (hqn : q < n) (hcut : CutAt B q) (hcut' : CutAt B' q)
    (hpre : PrefEq B B' q) (ht : B.row ⟨q + 1, by omega⟩ = t)
    (hle : B'.row ⟨q + 1, by omega⟩ ≤ t) {K : BetaDiagram (q + 1)} (hKn : IsNorm K)
    (hKc : K.Connected) (hm : CapMatches B (by omega : q ≤ n) (t : ℤ) K)
    (hm' : CapMatches B' (by omega : q ≤ n) (t : ℤ) K) (hβ : betaOf K B t = betaOf K B' t) :
    ∃ r, q < r ∧ r ≤ n ∧ ExtendsTo B B' r := by
  have hinfoB := block_info hKc hKn hBc hB hm hqn hcut ht
  have hκ := cornerOf_cohLetters_ne_zero hKc
  have hϑ : cohLetters 0 ≠ 0 := by
    unfold cohLetters
    exact (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2
      (MvPolynomial.X_ne_zero 0)
  by_cases hB'eq : B'.row ⟨q + 1, by omega⟩ = t
  · have hinfoB' := block_info hKc hKn hB'c hB' hm' hqn hcut' hB'eq
    obtain ⟨r, hqr, hrn, hcr, hcaseB⟩ := hinfoB
    obtain ⟨r', hqr', hrn', hcr', hcaseB'⟩ := hinfoB'
    rcases hcaseB with ⟨rfl, hcolB, hβB⟩ | ⟨m0, E, b0, hEn, rfl, hEc, hrel, hβB⟩ <;>
      rcases hcaseB' with ⟨rfl, hcolB', hβB'⟩ | ⟨m0', E', b0', hEn', rfl, hEc', hrel', hβB'⟩
    · -- both units
      refine ⟨q + 1, by omega, by omega, hcr, hcr', ?_, ?_⟩
      · intro i hi1 hi2
        by_cases hiq : i.val ≤ q
        · exact hpre.1 i hi1 hiq
        · have : i = ⟨q + 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [this, ht, hB'eq]
      · intro j hj
        by_cases hjq : j.val < q
        · exact hpre.2 j hjq
        · have : j = ⟨q, by omega⟩ := Fin.ext (by simp; omega)
          rw [this, hcolB, hcolB']
    · -- unit against a block
      exfalso
      rw [hβ] at hβB
      have h : schurOf cohLetters K * schurOf cohLetters E' =
          cohLetters 0 * schurOf cohLetters (splice K E' hKn hEn') := by
        linear_combination (schurOf cohLetters E') * hβB - cohLetters 0 * hβB'
      exact not_connected_of_mul _ K E' (splice_connected K E' hKn hEn' hKc hEc')
        (schur_mul_of_coh_theta h)
    · -- a block against a unit
      exfalso
      rw [← hβ] at hβB'
      have h : schurOf cohLetters K * schurOf cohLetters E =
          cohLetters 0 * schurOf cohLetters (splice K E hKn hEn) := by
        linear_combination (schurOf cohLetters E) * hβB' - cohLetters 0 * hβB
      exact not_connected_of_mul _ K E (splice_connected K E hKn hEn hKc hEc)
        (schur_mul_of_coh_theta h)
    · -- two blocks
      rw [hβ] at hβB
      have h : schurOf cohLetters (splice K E hKn hEn) * schurOf cohLetters E' =
          schurOf cohLetters (splice K E' hKn hEn') * schurOf cohLetters E := by
        linear_combination (schurOf cohLetters E') * hβB - (schurOf cohLetters E) * hβB'
      have hphys := schur_mul_of_coh h
      have hNc := splice_connected K E hKn hEn hKc hEc
      have hN'c := splice_connected K E' hKn hEn' hKc hEc'
      have hfac := factor_eq _ _ E E' hNc hN'c hEc hEc' (largestLabel_lt_splice K E hKn hEn)
        (largestLabel_lt_splice K E' hKn hEn') hphys
      have hb0 := hrel.b0_eq hB hEn
      have hb0pos : 1 ≤ b0 := by
        have := col_pos_of_ne_last B hB ⟨q + m0, by have := hrel.hr; omega⟩ (by
          intro h
          have := congrArg Fin.val h
          simp at this
          have := hrel.hr
          omega)
        omega
      have hspE := hrel.span_add hB hEn
      rw [ht, Int.toNat_natCast] at hspE
      have htc := rowPos_proper_lt_span hB hqn ht
      have hspanE : span E < c := by omega
      obtain ⟨hmm, hHEq⟩ := IH (span E) hspanE K hKn hKc E E' hEn hEn' hEc hEc' rfl hfac.1
        hfac.2
      subst hmm
      obtain rfl := eq_of_heq hHEq
      have hbb : b0 = b0' := by
        have h1 := hrel.row 0
        have h2 := hrel'.row 0
        simp only [Fin.val_zero, add_zero] at h1 h2
        rw [ht] at h1
        rw [hB'eq] at h2
        omega
      subst hbb
      refine ⟨q + m0 + 1, by omega, hrel.hr, hcr, hcr', ?_, ?_⟩
      · intro i hi1 hi2
        by_cases hiq : i.val ≤ q
        · exact hpre.1 i hi1 hiq
        · have hi : i = ⟨q + 1 + (i.val - q - 1), by omega⟩ := Fin.ext (by simp; omega)
          have h1 := hrel.row ⟨i.val - q - 1, by omega⟩
          have h2 := hrel'.row ⟨i.val - q - 1, by omega⟩
          rw [hi]
          dsimp only at h1 h2 ⊢
          omega
      · intro j hj
        by_cases hjq : j.val < q
        · exact hpre.2 j hjq
        · have hj' : j = ⟨q + (j.val - q), by omega⟩ := Fin.ext (by simp; omega)
          have h1 := hrel.col ⟨j.val - q, by omega⟩
          have h2 := hrel'.col ⟨j.val - q, by omega⟩
          rw [hj']
          dsimp only at h1 h2 ⊢
          omega
  · -- the other diagram has no row at `t`
    have hlt : B'.row ⟨q + 1, by omega⟩ < t := lt_of_le_of_ne hle hB'eq
    have hlow : ∀ i : Fin n, q ≤ i.val → rowPos B' i < t := by
      intro i hi
      have h1 : B'.row i.succ ≤ B'.row ⟨q + 1, by omega⟩ :=
        B'.row_strictAnti.antitone (by rw [Fin.le_def]; simp; omega)
      have h2 := rowPos_cast B' i
      have h0 : B'.col (Fin.last n) = 0 := hB'
      omega
    have hzero := betaOf_none (K := K) hB'c hcut' hlow
    rw [hzero] at hβ
    exfalso
    obtain ⟨r, hqr, hrn, hcr, hcaseB⟩ := hinfoB
    rcases hcaseB with ⟨-, -, hβB⟩ | ⟨m0, E, b0, hEn, -, hEc, -, hβB⟩
    · rw [hβ, zero_mul] at hβB
      exact schurOf_cohLetters_ne_zero K (neg_eq_zero.1 hβB.symm)
    · rw [hβ, zero_mul] at hβB
      exact schurOf_cohLetters_ne_zero _ (neg_eq_zero.1 hβB.symm)

theorem PrefEq.symm {B B' : BetaDiagram (n + 1)} {q : ℕ} (h : PrefEq B B' q) : PrefEq B' B q :=
  ⟨fun i h1 h2 => (h.1 i h1 h2).symm, fun j hj => (h.2 j hj).symm⟩

theorem ExtendsTo.symm {B B' : BetaDiagram (n + 1)} {r : ℕ} (h : ExtendsTo B B' r) :
    ExtendsTo B' B r := ⟨h.2.1, h.1, h.2.2.symm⟩

/-- **One step of the descent, when the next row of `B'` does not exceed that of `B`.** -/
theorem step_aux {c : ℕ} (IH : ∀ c' < c, CapRigidAt c') {K0 : BetaDiagram (k + 1)}
    (hK0 : IsNorm K0) {B B' : BetaDiagram (n + 1)} (hB : IsNorm B) (hB' : IsNorm B')
    (hBc : B.Connected) (hB'c : B'.Connected) (hcB : span B = c) (hspan : span B = span B')
    (hO1 : PowerSeries.coeff (span B) (letterSeries *
      ((coframe B - coframe B' : CohField[X]) : PowerSeries CohField)) = 0)
    (hO2 : PowerSeries.coeff (span B + span K0) (letterSeries *
      ((leftCoframe K0 * (coframe B - coframe B') : CohField[X]) : PowerSeries CohField)) = 0)
    {q : ℕ} (hqn : q < n) (hcut : CutAt B q) (hcut' : CutAt B' q) (hpre : PrefEq B B' q)
    (hle : B'.row ⟨q + 1, by omega⟩ ≤ B.row ⟨q + 1, by omega⟩) :
    coframe B = coframe B' ∨ ∃ r, q < r ∧ r ≤ n ∧ ExtendsTo B B' r := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, B.row ⟨q + 1, by omega⟩ = t :=
    ⟨(B.row ⟨q + 1, by omega⟩).toNat, (Int.toNat_of_nonneg (row_nonneg_of_norm B hB _)).symm⟩
  have hle' : B'.row ⟨q + 1, by omega⟩ ≤ t := ht ▸ hle
  have hlow : ∀ i : Fin n, q ≤ i.val → rowPos B i ≤ t ∧ rowPos B' i ≤ t := by
    intro i hi
    have h1 : B.row i.succ ≤ B.row ⟨q + 1, by omega⟩ :=
      B.row_strictAnti.antitone (by rw [Fin.le_def]; simp; omega)
    have h1' : B'.row i.succ ≤ B'.row ⟨q + 1, by omega⟩ :=
      B'.row_strictAnti.antitone (by rw [Fin.le_def]; simp; omega)
    have h2 := rowPos_cast B i
    have h3 := rowPos_cast B' i
    have h0 : B.col (Fin.last n) = 0 := hB
    have h0' : B'.col (Fin.last n) = 0 := hB'
    constructor <;> omega
  have hrowPos : ∀ i : Fin n, i.val < q → rowPos B i = rowPos B' i :=
    fun i hi => hpre.rowPos hB hB' i hi
  have hcolPos : ∀ j : Fin n, j.val < q → colPos B j = colPos B' j :=
    fun j hj => hpre.colPos hB hB' j hj
  by_cases hta : t < span K0
  · left
    have hz := zeroRange K0 hK0 hBc hB'c hcut hcut' hrowPos hcolPos t hlow hO2 (span K0) hta
      le_rfl
    refine Polynomial.ext fun j => ?_
    by_cases hj : j ≤ span B
    · have := hz j (by omega)
      rwa [Polynomial.coeff_sub, sub_eq_zero] at this
    · rw [coframe_coeff_eq_zero B hB (by omega), coframe_coeff_eq_zero B' hB' (by omega)]
  · right
    have hz := zeroRange K0 hK0 hBc hB'c hcut hcut' hrowPos hcolPos t hlow hO2 (t + 1)
      (by omega) (by omega)
    obtain ⟨K, hKn, hKc, hm, hm', hβ⟩ := beta_setup K0 hK0 hB hB' hBc hB'c hspan hO1 hqn hcut
      hpre ht hz
    exact step_blocks IH hB hB' hBc hB'c hcB hqn hcut hcut' hpre ht hle' hKn hKc hm hm' hβ

/-- **One step of the descent.**  Either the two right coframes agree, or the common prefix of
proper rows and columns extends to the next common cut. -/
theorem step {c : ℕ} (IH : ∀ c' < c, CapRigidAt c') {K0 : BetaDiagram (k + 1)}
    (hK0 : IsNorm K0) {B B' : BetaDiagram (n + 1)} (hB : IsNorm B) (hB' : IsNorm B')
    (hBc : B.Connected) (hB'c : B'.Connected) (hcB : span B = c) (hspan : span B = span B')
    (hO1 : PowerSeries.coeff (span B) (letterSeries *
      ((coframe B - coframe B' : CohField[X]) : PowerSeries CohField)) = 0)
    (hO2 : PowerSeries.coeff (span B + span K0) (letterSeries *
      ((leftCoframe K0 * (coframe B - coframe B') : CohField[X]) : PowerSeries CohField)) = 0)
    {q : ℕ} (hqn : q < n) (hcut : CutAt B q) (hcut' : CutAt B' q) (hpre : PrefEq B B' q) :
    coframe B = coframe B' ∨ ∃ r, q < r ∧ r ≤ n ∧ ExtendsTo B B' r := by
  rcases le_total (B'.row ⟨q + 1, by omega⟩) (B.row ⟨q + 1, by omega⟩) with hle | hle
  · exact step_aux IH hK0 hB hB' hBc hB'c hcB hspan hO1 hO2 hqn hcut hcut' hpre hle
  · have hneg : (coframe B' - coframe B : CohField[X]) = -(coframe B - coframe B') := by ring
    have hO1' : PowerSeries.coeff (span B') (letterSeries *
        ((coframe B' - coframe B : CohField[X]) : PowerSeries CohField)) = 0 := by
      rw [← hspan, hneg, Polynomial.coe_neg, mul_neg, map_neg, hO1, neg_zero]
    have hO2' : PowerSeries.coeff (span B' + span K0) (letterSeries *
        ((leftCoframe K0 * (coframe B' - coframe B) : CohField[X]) : PowerSeries CohField)) =
        0 := by
      have e : leftCoframe K0 * (coframe B' - coframe B) =
          -(leftCoframe K0 * (coframe B - coframe B')) := by ring
      rw [← hspan, e, Polynomial.coe_neg, mul_neg, map_neg, hO2, neg_zero]
    rcases step_aux IH hK0 hB' hB hB'c hBc (hspan ▸ hcB) hspan.symm hO1' hO2' hqn hcut' hcut
      hpre.symm hle with h | ⟨r, h1, h2, h3⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨r, h1, h2, h3.symm⟩

end SkewCoframeRigidity.FixedCap
