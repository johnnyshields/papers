/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/MixedEta/SignB.lean`. -/
import GluingCore.Aligned.MixedEta.Package
import GluingCore.Aligned.MixedEta.Upper

/-!
# Ordinary `ω` of case (b) and mixed `η`: the diagonal package

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, case (b) of the inner mark): `b > 0`, and the rotation of `V` satisfies
the diagonal package of the lower mark.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

namespace MixedEta

variable {ω η : MarkedInner} {V : Diagram} {a : ℤ}

theorem diagLo_rot (V : Diagram) (t : ℤ) :
    diagLo (GluingCore.rotate V) t = - diagHi V (-t) := by
  have := diagLo_rotate (D := V) (-t)
  simpa using this

theorem diagHi_rot (V : Diagram) (t : ℤ) :
    diagHi (GluingCore.rotate V) t = - diagLo V (-t) := diagHi_rotate (D := V) t

theorem oRowLo_b {ω : MarkedInner} (hs : ω.case = .b) (D : Diagram) (j : ℤ) :
    ω.oRowLo D j = j * ω.rowShift - diagHi D j := by simp [oRowLo, hs]

theorem oRowHi_b {ω : MarkedInner} (hs : ω.case = .b) (D : Diagram) (j : ℤ) :
    ω.oRowHi D j = j * ω.rowShift - diagLo D j := by simp [oRowHi, hs]

namespace Setup

variable (S : Setup ω η V a)
include S

theorem eta_lo_last_gen (hw1 : 1 ≤ ω.widthZ) :
    η.lo (η.widthZ - 1 + η.period) =
      ω.oRowLo V (maxContent V) + ω.lo (ω.widthZ - 1 + ω.period) := by
  have hq := S.q_pos
  have hwq := S.w_lt_q
  have hM := S.M_eq
  have hper := S.eta_period
  have hW := S.eta_w
  have hMV : minContent V ≤ maxContent V := by have := S.span_pos; omega
  have hN : maxContent V + 1 - minContent V = (span V : ℤ) := by omega
  have e1 : η.widthZ - 1 + η.period = (maxContent V + 1 - minContent V) * ω.period +
      (ω.widthZ - 1) := by rw [hW, hper, hN]; ring
  have b1 := eta_lo_hi S.hω S.hord S.hV S.hU (J := maxContent V + 1) (ρ := ω.widthZ - 1)
    (by omega) (by omega) (Or.inr ⟨rfl, by omega⟩)
  rw [e1, b1.1, ordLo_prev (by omega)]
  simp only [add_sub_cancel_right]

theorem hs_b_caps (hs : ω.case = .b) :
    1 ≤ ω.widthZ ∧
    (ω.dHi (ω.widthZ - 1) = 0 ∧ ω.hi (ω.widthZ - 1) - ω.hi ω.widthZ = 1 ∧
      ω.dLo (ω.widthZ - 1) + (ω.lo (ω.widthZ - 1) - ω.lo ω.widthZ) = 1) ∧
    (ω.dLo 0 = 0 ∧ ω.lo (ω.period - 1) - ω.lo ω.period = 1 ∧
      ω.dHi 0 + (ω.hi (ω.period - 1) - ω.hi ω.period) = 1) := by
  have hW : ω.W ≠ ∅ := by
    intro hW
    have h : ω.IsLegalEmpty := ⟨S.hω, hW⟩
    have := h.case_a
    rw [hs] at this
    exact absurd this (by decide)
  have h : ω.IsLegalNonempty := ⟨S.hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
  have hT : ω.ordT = 1 := by simp [ordT, hs]
  exact ⟨h.width_pos, (ord_E_facts h S.hord).2.2 hT⟩

/-- For `ω` of case (b), a mixed `η` forces `b > 0`. -/
theorem b_pos_b (hs : ω.case = .b) : 1 ≤ (span V : ℤ) - a := by
  by_contra hb
  have hna := S.a_le
  have hb0 : (span V : ℤ) = a := by omega
  obtain ⟨hw1, ⟨c1, c2, c3⟩, ⟨d1, d2, d3⟩⟩ := S.hs_b_caps hs
  have hq := S.q_pos
  have hM := S.M_eq
  have hLowV := (S.eta_ne.attach.2.2.2 S.hηd).1
  have hUpH := (S.eta_ne.attach.2.2.2 S.hηd).2
  obtain ⟨-, -, h3⟩ := S.eta_ne.lower_caps_V hLowV
  obtain ⟨-, -, h4⟩ := S.eta_ne.upper_caps_H hUpH
  unfold dLo at h3 h4
  simp only [zero_add] at h4
  have hW := S.eta_w
  rw [hb0, sub_self, zero_mul, zero_add] at hW
  have l1 := S.eta_lo_last_gen hw1
  have l2 := S.eta_lo_W (by omega : 0 ≤ (span V : ℤ) - a)
  have l3 := S.eta_lo_pred
  have l4 := S.eta_lo_zero
  rw [l1, l2] at h3
  rw [l3, l4] at h4
  rw [hW] at l2
  have hMa : maxContent V = minContent V + a - 1 := by omega
  rw [hMa] at h3
  have e : minContent V + ((span V : ℤ) - a) = minContent V := by omega
  rw [e] at h3
  unfold dLo at c3 d1
  simp only [zero_add] at d1
  omega



/-- The diagonal package of the rotation of `V` for `ω` of case (b) and `η` of case (d). -/
theorem package_b (hs : ω.case = .b) :
    DPackage (GluingCore.rotate V) a ((span V : ℤ) - a) (a * ω.rowShift - η.v.1) := by
  have hb := S.b_pos_b hs
  have hq := S.q_pos
  have hM := S.M_eq
  have hna := S.two_a_gt
  have hapos := S.a_pos
  have hVne := S.hV.2.1
  have hmin : minContent (GluingCore.rotate V) = -maxContent V := minContent_rotate hVne
  have hmax : maxContent (GluingCore.rotate V) = -minContent V := maxContent_rotate hVne
  obtain ⟨hgh, hg0, hg1, hgr, hgd⟩ := S.gamma_data hb
  have hLo := oRowLo_b hs V
  have hHi := oRowHi_b hs V
  have hmul : ∀ j : ℤ, (j + a) * ω.rowShift = j * ω.rowShift + a * ω.rowShift := fun j => by ring
  have hsl := S.single_lower hb
  have hsu := S.single_upper
  -- the origin rows at `j = -k - a`
  have rng : ∀ k : ℤ, minContent (GluingCore.rotate V) ≤ k →
      k ≤ minContent (GluingCore.rotate V) + ((span V : ℤ) - a) - 1 →
      minContent V ≤ -k - a ∧ -k - a ≤ minContent V + ((span V : ℤ) - a) - 1 := by
    intro k h1 h2
    rw [hmin] at h1 h2
    omega
  refine ⟨isConnectedSkew_rotate S.hV, by rw [hmax, hmin]; omega, hb, by omega, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro k h1 h2
    obtain ⟨j, hj⟩ : ∃ j : ℤ, j = -k - a := ⟨_, rfl⟩
    obtain ⟨r1, r2⟩ := rng k h1 h2
    rw [← hj] at r1 r2
    have F := hgh j r1 r2
    rw [hHi, hHi, hmul] at F
    rw [diagHi_rot, diagHi_rot]
    have e1 : -(k + a) = j := by omega
    have e2 : -k = j + a := by omega
    rw [e1, e2]
    omega
  · intro k h1 h2
    obtain ⟨j, hj⟩ : ∃ j : ℤ, j = -k - a := ⟨_, rfl⟩
    obtain ⟨r1, r2⟩ := rng k h1 h2
    rw [← hj] at r1 r2
    have F := S.private_sides hb r1 r2
    rw [hLo, hLo, hmul] at F
    rw [diagLo_rot, diagLo_rot]
    have e1 : -(k + a) = j := by omega
    have e2 : -k = j + a := by omega
    rw [e1, e2]
    omega
  · intro k k' h1 hkk h2 hg
    obtain ⟨j, hj⟩ : ∃ j : ℤ, j = -k - a := ⟨_, rfl⟩
    obtain ⟨j', hj'⟩ : ∃ j : ℤ, j = -k' - a := ⟨_, rfl⟩
    obtain ⟨r1, r2⟩ := rng k h1 (by omega)
    obtain ⟨r1', r2'⟩ := rng k' (by omega) h2
    rw [← hj] at r1 r2
    rw [← hj'] at r1' r2'
    have T := (S.private_tails hb (j := j') (j' := j) r1' (by omega) r2).2
    rw [hLo, hLo, hmul, hLo, hLo, hmul] at T
    rw [diagLo_rot, diagLo_rot] at hg ⊢
    have e1 : -(k + a) = j := by omega
    have e2 : -k = j + a := by omega
    have e1' : -(k' + a) = j' := by omega
    have e2' : -k' = j' + a := by omega
    rw [e1, e2] at hg
    rw [e1', e2']
    have := T (by omega)
    omega
  · intro k k' h1 hkk h2 hg
    obtain ⟨j, hj⟩ : ∃ j : ℤ, j = -k - a := ⟨_, rfl⟩
    obtain ⟨j', hj'⟩ : ∃ j : ℤ, j = -k' - a := ⟨_, rfl⟩
    obtain ⟨r1, r2⟩ := rng k h1 (by omega)
    obtain ⟨r1', r2'⟩ := rng k' (by omega) h2
    rw [← hj] at r1 r2
    rw [← hj'] at r1' r2'
    have T := (S.private_tails hb (j := j') (j' := j) r1' (by omega) r2).1
    rw [hLo, hLo, hmul, hLo, hLo, hmul] at T
    rw [diagLo_rot, diagLo_rot] at hg ⊢
    have e1 : -(k + a) = j := by omega
    have e2 : -k = j + a := by omega
    have e1' : -(k' + a) = j' := by omega
    have e2' : -k' = j' + a := by omega
    rw [e1', e2'] at hg
    rw [e1, e2]
    have := T (by omega)
    omega
  · rw [diagLo_rot, diagHi_rot]
    rw [hLo, hHi] at hsu
    have e : -(minContent (GluingCore.rotate V) + ((span V : ℤ) - a)) = minContent V + a - 1 := by
      rw [hmin]; omega
    rw [e]
    omega
  · rw [diagLo_rot, diagHi_rot]
    rw [hLo, hHi] at hsl
    have e : -(minContent (GluingCore.rotate V) + a - 1) =
        minContent V + ((span V : ℤ) - a) := by
      rw [hmin]; omega
    rw [e]
    omega
  · intro _
    obtain ⟨hw1, ⟨c1, c2, c3⟩, ⟨d1, d2, d3⟩⟩ := S.hs_b_caps hs
    have hUpH := (S.eta_ne.attach.2.2.2 S.hηd).2
    obtain ⟨-, -, h4⟩ := S.eta_ne.upper_caps_H hUpH
    unfold dLo at h4 d1
    simp only [zero_add] at h4 d1
    rw [S.eta_lo_pred, S.eta_lo_zero] at h4
    have F := hgh (minContent V) (le_refl _) (by omega)
    have hends := S.ends_single
    simp only [hLo, hHi] at hsu hends F h4
    rw [diagHi_rot, diagHi_rot]
    have e1 : -(minContent (GluingCore.rotate V) + ((span V : ℤ) - a) - 1) = minContent V + a := by
      rw [hmin]; omega
    have e2 : -(minContent (GluingCore.rotate V) + ((span V : ℤ) - a)) = minContent V + a - 1 := by
      rw [hmin]; omega
    rw [e1, e2]
    rw [hmul] at F
    have e3 : (minContent V + a - 1) * ω.rowShift =
        (minContent V + a) * ω.rowShift - ω.rowShift := by
      ring
    have e4 : (minContent V + a) * ω.rowShift = minContent V * ω.rowShift + a * ω.rowShift := by
      ring
    have e6 := S.eta_rowShift
    omega
  · intro _
    obtain ⟨hw1, ⟨c1, c2, c3⟩, ⟨d1, d2, d3⟩⟩ := S.hs_b_caps hs
    have hLowV := (S.eta_ne.attach.2.2.2 S.hηd).1
    obtain ⟨-, -, h3⟩ := S.eta_ne.lower_caps_V hLowV
    unfold dLo at h3 c3
    rw [S.eta_lo_last_gen hw1, S.eta_lo_W (by omega)] at h3
    have F := hgh (minContent V + ((span V : ℤ) - a) - 1) (by omega) (le_refl _)
    have e : minContent V + ((span V : ℤ) - a) - 1 + a = maxContent V := by omega
    rw [e] at F
    have hends := S.ends_single
    simp only [hLo, hHi] at hsl hends F h3
    rw [diagHi_rot, diagHi_rot]
    have e1 : -(minContent (GluingCore.rotate V) + a - 1) = minContent V + ((span V : ℤ) - a) := by
      rw [hmin]; omega
    have e2 : -(minContent (GluingCore.rotate V) + a) = minContent V + ((span V : ℤ) - a) - 1 := by
      rw [hmin]; omega
    rw [e1, e2]
    have e3 : (minContent V + ((span V : ℤ) - a)) * ω.rowShift =
        (minContent V + ((span V : ℤ) - a) - 1) * ω.rowShift + ω.rowShift := by ring
    have e5 : maxContent V * ω.rowShift = (minContent V + ((span V : ℤ) - a) - 1) * ω.rowShift +
        a * ω.rowShift := by rw [hM]; ring
    have e6 := S.eta_rowShift
    omega

end Setup

end MixedEta

end MarkedInner

end GluingCore
