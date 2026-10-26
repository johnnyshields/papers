/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationMateData
import SkewClassInflation.ConstantGapRibbons
import SkewClassInflation.RibbonEndpoints

/-!
# General-power mates reduce to actual ribbon equality

The constant-gap comparison in `lem:merged-block-rigidity` of
`shields-2026-skew-class-inflation.tex`.  The mate's row count,
Hessenberg condition, row bounds, and constant gaps are all supplied
from its original full Schur equality.  This proves the reduction to
ribbon equality; no factor-reversal classification is assumed.
Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- Every arbitrary power mate supplies a genuine ribbon equality at the original inner gap. -/
theorem power_mate_ribbon (m : ℕ) (hm : 0 < m) {n : ℕ} (Q : Profile n)
    (he : Q.toBetaDiagram.schur = (A.power m hm).toBetaDiagram.schur) :
    ribbonWord (List.ofFn (fun i => Q.r i - A.c)) =
      ribbonWord (List.ofFn (fun i => (A.power m hm).r i - A.c)) := by
  obtain ⟨_, hQ, hgQ, hrQ⟩ := A.power_mate_reduction m hm Q he
  apply (constant_gap_equality_iff Q (A.power m hm) A.c hQ (A.power_thick m hm)
    (fun i => by have := hrQ i; have := A.c_lt_d; omega)
    (A.powerRows_above_gap m) hgQ (fun _ => rfl)).mp
  exact he

/-- The power-mate consequence of `lem:ribbon-endpoints`, including one nonrigid copy. -/
theorem power_mate_endpoints (m : ℕ) (hm : 0 < m) {n : ℕ} (Q : Profile n)
    (he : Q.toBetaDiagram.schur = (A.power m hm).toBetaDiagram.schur) :
    (Q.r 0 ::ₘ Q.r (Fin.last n) ::ₘ 0 : Multiset ℕ) =
      A.r 0 ::ₘ A.r (Fin.last A.k) ::ₘ 0 := by
  obtain ⟨_, _, _, hrows⟩ := A.power_mate_reduction m hm Q he
  have hend := ribbon_endpoints_of_eq (fun i => Q.r i - A.c)
    (fun i => (A.power m hm).r i - A.c)
    (fun i => Nat.sub_pos_of_lt (A.c_lt_d.trans (hrows i)))
    (fun i => Nat.sub_pos_of_lt (A.powerRows_above_gap m i))
    (A.power_mate_ribbon m hm Q he)
  simp only [A.power_first, A.power_last] at hend
  have hh := congrArg (Multiset.map (fun a : ℕ => a + A.c)) hend
  have h0 : A.c ≤ Q.r 0 := (A.c_lt_d.trans (hrows 0)).le
  have hn : A.c ≤ Q.r (Fin.last n) := (A.c_lt_d.trans (hrows (Fin.last n))).le
  simpa only [Multiset.map_cons, Multiset.map_zero, Nat.sub_add_cancel h0,
    Nat.sub_add_cancel hn, Nat.sub_add_cancel (A.row_above_gap 0).le,
    Nat.sub_add_cancel (A.row_above_gap (Fin.last A.k)).le] using hh

end SkewClassInflation.SaturationInner
