/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.Step

/-!
# Fixed-cap rigidity: the descent, unconditionally

Formalizes the descent in the proof of `sc:fixed-cap` of
`shields-2026-skew-coframe-rigidity.tex`: strong induction on the child span, uniformly over every
connected normalized cap, and within a span an induction on the number of proper rows already
identified.  The result is `CapVanishing K` and `CapDescent K` for every connected normalized
cap `K`, hence unconditional `fixed_cap_rigidity`.  Sorry-free, modulo the statements of `Coframe`
on which `Reduction` rests.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {n k : ℕ}

/-- Two diagrams agreeing on every proper row and column are equal. -/
theorem eq_of_prefEq_full {B B' : BetaDiagram (n + 1)} (hB : IsNorm B) (hB' : IsNorm B')
    (hspan : span B = span B') (h : PrefEq B B' n) : B = B' := by
  have hr : B.row = B'.row := by
    funext i
    by_cases hi : i.val = 0
    · have e : i = 0 := Fin.ext hi
      have h1 := row_zero_eq B hB
      have h2 := row_zero_eq B' hB'
      have h3 := span_cast B
      have h4 := span_cast B'
      rw [e]; omega
    · exact h.1 i (by omega) (by omega)
  have hc : B.col = B'.col := by
    funext j
    by_cases hj : j.val < n
    · exact h.2 j hj
    · have e : j = Fin.last n := Fin.ext (by simp; omega)
      rw [e]
      have h1 : B.col (Fin.last n) = 0 := hB
      have h2 : B'.col (Fin.last n) = 0 := hB'
      omega
  cases B with
  | mk row col r1 r2 r3 =>
    cases B' with
    | mk row' col' r1' r2' r3' =>
      simp only at hr hc
      subst hr; subst hc; rfl

/-- **The inner induction.**  Starting from a common cut, the two right coframes agree. -/
theorem descent_prefix {c : ℕ} (IH : ∀ c' < c, CapRigidAt c') {K0 : BetaDiagram (k + 1)}
    (hK0 : IsNorm K0) {B B' : BetaDiagram (n + 1)} (hB : IsNorm B) (hB' : IsNorm B')
    (hBc : B.Connected) (hB'c : B'.Connected) (hcB : span B = c) (hspan : span B = span B')
    (hO1 : PowerSeries.coeff (span B) (letterSeries *
      ((coframe B - coframe B' : CohField[X]) : PowerSeries CohField)) = 0)
    (hO2 : PowerSeries.coeff (span B + span K0) (letterSeries *
      ((leftCoframe K0 * (coframe B - coframe B') : CohField[X]) : PowerSeries CohField)) = 0) :
    ∀ d q : ℕ, n - q = d → q ≤ n → CutAt B q → CutAt B' q → PrefEq B B' q →
      coframe B = coframe B' := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro q hd hqn hcut hcut' hpre
    by_cases hqn' : q = n
    · subst hqn'
      rw [eq_of_prefEq_full hB hB' hspan hpre]
    · rcases step IH hK0 hB hB' hBc hB'c hcB hspan hO1 hO2 (show q < n by omega) hcut hcut'
        hpre with h | ⟨r, hqr, hrn, hr⟩
      · exact h
      · exact ihd (n - r) (by omega) r rfl hrn hr.1 hr.2.1 hr.2.2

/-- **Fixed-cap rigidity at every child span, for every cap.** -/
theorem capRigidAt (c : ℕ) : CapRigidAt c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro k K hK hKc b b' B B' hB hB' hBc hB'c hc h1 h2
    have hb : b = b' := by
      have e1 := BetaDiagram.rowDegree B
      have e2 := BetaDiagram.rowDegree B'
      rw [h1] at e1
      omega
    subst hb
    obtain ⟨hspan, hcorner, e1, e2⟩ := cap_observations K hK hKc B B' hB hB' hBc hB'c h1 h2
    have hcof : coframe B = coframe B' :=
      descent_prefix ih hK hB hB' hBc hB'c hc hspan e1 e2 (b - 0) 0 rfl (Nat.zero_le _)
        (cutAt_zero B) (cutAt_zero B')
        ⟨fun i h1 h2 => by omega, fun j hj => by omega⟩
    exact eq_of_coframe_eq hB hB' hBc hB'c hspan hcof

/-- **The two observations force the right coframes to agree**, for every connected normalized
cap. -/
theorem capVanishing (K : BetaDiagram (k + 1)) (hK : IsNorm K) (_hKc : K.Connected) :
    CapVanishing K := by
  intro b B B' hB hB' hBc hB'c hspan hcorner e1 e2
  exact descent_prefix (fun c' _ => capRigidAt c') hK hB hB' hBc hB'c rfl hspan e1 e2
    (b - 0) 0 rfl (Nat.zero_le _) (cutAt_zero B) (cutAt_zero B')
    ⟨fun i h1 h2 => by omega, fun j hj => by omega⟩

/-- **The descent**: the remaining case of `sc:fixed-cap`, with no assumption. -/
theorem capDescent (K : BetaDiagram (k + 1)) (hK : IsNorm K) (hKc : K.Connected) :
    CapDescent K := fun B B' hB hB' hBc hB'c hspan hcorner e1 e2 _ _ =>
  capVanishing K hK hKc B B' hB hB' hBc hB'c hspan hcorner e1 e2

/-- **Fixed-cap rigidity** (`sc:fixed-cap`), unconditionally: connected normalized diagrams
with the same function and the same function after the same `00`-splice with a connected cap
are equal. -/
theorem fixed_cap_rigidity_unconditional (K : BetaDiagram (k + 1)) (hK : IsNorm K)
    (hKc : K.Connected) {b b' : ℕ} (B : BetaDiagram (b + 1)) (B' : BetaDiagram (b' + 1))
    (hB : IsNorm B) (hB' : IsNorm B') (hBc : B.Connected) (hB'c : B'.Connected)
    (h1 : B.schur = B'.schur)
    (h2 : (splice K B hK hB).schur = (splice K B' hK hB').schur) : b = b' ∧ HEq B B' :=
  capRigidAt (span B) K hK hKc B B' hB hB' hBc hB'c rfl h1 h2

end SkewCoframeRigidity.FixedCap
