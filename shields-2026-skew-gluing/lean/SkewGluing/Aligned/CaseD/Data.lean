import SkewGluing.Aligned.CaseD.Rows

/-!
# Aligned marks, case (d): the data of the lower mark

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-walk-signs`).

`alD_Data V a θ` collects what the construction of the lower mark `μ` on `V`
(`Z = V ∩ (V - z)`, `z = (θ, θ + a)`) uses, stated on the first and last rows `alD_L`, `alD_H` of
the diagonals of `V` (indexed from `0`): the height differences `e_j = M_j - M_{j+a}` and the
span differences `d_j = S_j - S_{j+a}` form the monotone sequence of `eq:gluing-walk-signs`,
the diagonals `b` and `a - 1` are singletons, and `θ` is one of the two end offsets on each
diagonal.  `alD_data` proves it from a legal mark `η` of displacement content `a q`.

Sorry-free.
-/

namespace SkewGluing

/-- `e_j = M_j - M_{j+a}`, the height difference of the diagonals `j` and `j + a` of `V`. -/
def alD_e (V : Diagram) (a j : ℤ) : ℤ :=
  (alD_H V j - alD_L V j) - (alD_H V (j + a) - alD_L V (j + a))

/-- `d_j = S_j - S_{j+a}`, the difference of the joining spans, with `S_j = h_{j-1} - ℓ_j + 1`. -/
def alD_d (V : Diagram) (a j : ℤ) : ℤ :=
  (alD_H V (j - 1) - alD_L V j) - (alD_H V (j + a - 1) - alD_L V (j + a))

/-- The data of the lower mark: `b = N_V - a`. -/
structure alD_Data (V : Diagram) (a θ : ℤ) : Prop where
  ha : 0 < a
  hb : 0 < (span V : ℤ) - a
  hba : (span V : ℤ) - a < a
  e_bd : ∀ j, 0 ≤ j → j < (span V : ℤ) - a → -1 ≤ alD_e V a j ∧ alD_e V a j ≤ 1
  e_mono : ∀ j, 0 ≤ j → j + 1 < (span V : ℤ) - a → alD_e V a j ≤ alD_e V a (j + 1)
  d_bd : ∀ j, 1 ≤ j → j < (span V : ℤ) - a →
    alD_e V a (j - 1) ≤ alD_d V a j ∧ alD_d V a j ≤ alD_e V a j
  d_last : alD_e V a ((span V : ℤ) - a - 1) ≤ alD_H V ((span V : ℤ) - a - 1) -
      alD_L V ((span V : ℤ) - a) ∧
    alD_H V ((span V : ℤ) - a - 1) - alD_L V ((span V : ℤ) - a) ≤ 1
  d_first : alD_L V a - alD_H V (a - 1) ≤ alD_e V a 0
  singleton_b : alD_L V ((span V : ℤ) - a) = alD_H V ((span V : ℤ) - a)
  singleton_a : alD_L V (a - 1) = alD_H V (a - 1)
  th1 : ∀ j, 0 ≤ j → j < (span V : ℤ) - a →
    θ = alD_L V (j + a) - alD_L V j ∨ θ = alD_H V (j + a) - alD_H V j
  th2 : ∀ j, 1 ≤ j → j < (span V : ℤ) - a →
    θ = alD_H V (j - 1 + a) - alD_H V (j - 1) ∨ θ = alD_L V (j + a) - alD_L V j

namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

theorem alD_Ma1 (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    alD_L V (a - 1) = alD_H V (a - 1) := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hηl := eta_legalNonempty hω hd hV hη hU ha
  have hap := eta_pos hω hV hη hU ha
  have hlt2 := eta_lt_two_mul hω hV hη hU ha
  have hle := eta_le_span hω hV hη hU ha
  have hper : η.period = a * ω.period := ha
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  have hlt := hl.phases_lt (Or.inr hd) hph
  have hph' := hph
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph'
  have h1 := hηl.lo_pred_period_eq_hi
  have h2 := eta_lo_hi_height hω hV hU (η.period - 1)
  have hHU : HU ω V (η.period - 1) = 1 := by omega
  have e : η.period - 1 = (a - 1) * ω.period + (ω.period - 1) := by rw [hper]; ring
  rw [e, HU_interleaved hl hd hV hph hlt (i := a - 1) (α := ω.period - 1) (by omega)
    (by omega) (by omega) (by omega) (by intro he; omega)] at hHU
  have hcu : constU ω (ω.period - 1) = 0 := by
    unfold constU
    have hw : ¬ (ω.period - 1 < ω.widthZ) := by omega
    simp only [hw, ↓reduceIte]
    have := hl.lo_pred_period_eq_hi
    unfold height lo hi at *
    omega
  have hsel : selK s t (ω.period - 1) = 1 := selK_ge hlt (by omega)
  rw [hcu, hsel, zero_add, profIL_odd] at hHU
  have hsp := aligned_span_eq hV
  rw [aligned_profM_eq (by omega)] at hHU
  unfold alD_L alD_H
  omega

theorem alD_data (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hpos : a < (span V : ℤ)) :
    ∃ θ, alD_Data V a θ := by
  obtain ⟨θ, hθ1, hθ2⟩ := exists_theta hω hd hV hη hU ha
  have hap := eta_pos hω hV hη hU ha
  have hlt2 := eta_lt_two_mul hω hV hη hU ha
  obtain ⟨hbd, hmono, hfirst, hlast⟩ := walk_signs hω hd hV hη hU ha
  have hsp := aligned_span_eq hV
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  set b := (span V : ℤ) - a with hb
  -- odd and even values of the walk
  have hodd : ∀ j, 0 ≤ j → j < b → walkDelta V a (2 * minContent V + (2 * j + 1)) =
      alD_e V a j := by
    intro j h0 h1
    have := walkDelta_odd hV (a := a) (j := j) h0 (by omega) (by omega)
    have e : 2 * (minContent V + j) + 1 = 2 * minContent V + (2 * j + 1) := by ring
    rw [e] at this
    rw [this]
    unfold gStep kStep alD_e alD_L alD_H
    have e1 : minContent V + j + a = minContent V + (j + a) := by ring
    rw [e1]; ring
  have heven : ∀ j, 1 ≤ j → j < b → walkDelta V a (2 * minContent V + 2 * j) =
      alD_d V a j := by
    intro j h0 h1
    have := walkDelta_even hV (a := a) (j := j) h0 (by omega) (by omega)
    have e : 2 * (minContent V + j) = 2 * minContent V + 2 * j := by ring
    rw [e] at this
    rw [this]
    unfold gStep kStep alD_d alD_L alD_H
    have e1 : minContent V + j + a = minContent V + (j + a) := by ring
    have e2 : minContent V + (j - 1) + a = minContent V + (j + a - 1) := by ring
    have e3 : minContent V + (j - 1) = minContent V + (j - 1) := rfl
    rw [e1, e2]; ring
  have hb2 : walkDelta V a (2 * minContent V + 2 * b + 1) = 1 := hlast
  -- the last odd index: `M_b = 1`
  have hMb : alD_L V b = alD_H V b := by
    have e : walkDelta V a (2 * minContent V + 2 * b + 1) =
        profM V (minContent V + b) - profM V (minContent V + b + a) := by
      unfold walkDelta
      have e1 : 2 * minContent V + 2 * b + 1 = 2 * (minContent V + b) + 1 := by ring
      have e2 : 2 * (minContent V + b) + 1 + 2 * a = 2 * (minContent V + b + a) + 1 := by ring
      rw [e1, e2, profIL_odd, profIL_odd]
    rw [e] at hb2
    rw [aligned_profM_eq (by omega), aligned_profM_eq_zero (by omega)] at hb2
    unfold alD_L alD_H
    omega
  have hdlast : walkDelta V a (2 * minContent V + 2 * b) = alD_H V (b - 1) - alD_L V b := by
    unfold walkDelta
    have e1 : 2 * minContent V + 2 * b = 2 * (minContent V + b) := by ring
    have e2 : 2 * (minContent V + b) + 2 * a = 2 * (minContent V + b + a) := by ring
    rw [e1, e2, profIL_even, profIL_even, aligned_profS_eq (by omega),
      aligned_profS_eq_one (by omega)]
    unfold alD_L alD_H
    have e3 : minContent V + b - 1 = minContent V + (b - 1) := by ring
    rw [e3]
    ring
  have hdfirst : alD_L V a - alD_H V (a - 1) ≤ alD_e V a 0 := by
    have h2 := hmono (2 * minContent V) (2 * minContent V + (2 * 0 + 1)) (by omega) (by omega)
      (by omega)
    rw [hodd 0 le_rfl (by omega)] at h2
    have e1 : walkDelta V a (2 * minContent V) = alD_L V a - alD_H V (a - 1) := by
      unfold walkDelta
      have e : 2 * minContent V + 2 * a = 2 * (minContent V + a) := by ring
      have e0 : 2 * minContent V = 2 * (minContent V + 0) := by ring
      rw [e, e0, profIL_even, profIL_even]
      have p0 : profS V (minContent V + 0) = 1 := aligned_profS_eq_one (by omega)
      have p1 : profS V (minContent V + a) = alD_H V (a - 1) - alD_L V a + 1 := by
        rw [aligned_profS_eq (by omega)]
        unfold alD_H alD_L
        have e2 : minContent V + a - 1 = minContent V + (a - 1) := by ring
        rw [e2]
      rw [p0, p1]
      ring
    rw [e1] at h2
    exact h2
  refine ⟨θ, ⟨hap, by omega, by omega, ?_, ?_, ?_, ?_, hdfirst, hMb,
    alD_Ma1 hω hd hV hη hU ha, ?_, ?_⟩⟩
  · intro j h0 h1
    have := hbd (2 * minContent V + (2 * j + 1)) (by omega) (by omega)
    rwa [hodd j h0 h1] at this
  · intro j h0 h1
    have := hmono (2 * minContent V + (2 * j + 1)) (2 * minContent V + (2 * (j + 1) + 1))
      (by omega) (by omega) (by omega)
    rwa [hodd j h0 (by omega), hodd (j + 1) (by omega) h1] at this
  · intro j h0 h1
    have h2 := hmono (2 * minContent V + (2 * (j - 1) + 1)) (2 * minContent V + 2 * j)
      (by omega) (by omega) (by omega)
    have h3 := hmono (2 * minContent V + 2 * j) (2 * minContent V + (2 * j + 1))
      (by omega) (by omega) (by omega)
    rw [hodd (j - 1) (by omega) (by omega), heven j h0 h1] at h2
    rw [heven j h0 h1, hodd j (by omega) h1] at h3
    exact ⟨h2, h3⟩
  · have h2 := hmono (2 * minContent V + (2 * (b - 1) + 1)) (2 * minContent V + 2 * b)
      (by omega) (by omega) (by omega)
    have h3 := hmono (2 * minContent V + 2 * b) (2 * minContent V + 2 * b + 1)
      (by omega) (by omega) (by omega)
    rw [hodd (b - 1) (by omega) (by omega), hdlast] at h2
    rw [hdlast, hb2] at h3
    exact ⟨h2, h3⟩
  · intro j h0 h1
    rcases hθ1 j h0 h1 with h | h
    · left; rw [h]; unfold gStep alD_L
      have e1 : minContent V + j + a = minContent V + (j + a) := by ring
      rw [e1]
    · right; rw [h]; unfold kStep alD_H
      have e1 : minContent V + j + a = minContent V + (j + a) := by ring
      rw [e1]
  · intro j h0 h1
    rcases hθ2 j h0 h1 with h | h
    · left; rw [h]; unfold kStep alD_H
      have e1 : minContent V + (j - 1) + a = minContent V + (j - 1 + a) := by ring
      rw [e1]
    · right; rw [h]; unfold gStep alD_L
      have e1 : minContent V + j + a = minContent V + (j + a) := by ring
      rw [e1]

end MarkedInner

end SkewGluing
