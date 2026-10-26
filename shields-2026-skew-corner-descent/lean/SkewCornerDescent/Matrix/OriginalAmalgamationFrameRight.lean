/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationFrameLeft

/-!
# Actual compatible right borders of the literal amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). The entire core/right and bottom/right blocks agree with
the original upper-window extension, including every right splice. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- The union's whole lower/right rectangle agrees with the original upper-window
extension. Both the core/right coupling and the complete bottom border are retained. -/
theorem originalAmalgamation_frame_right {n m : ℕ}
    (P : Profile n) (A : Profile m) (a b : ℕ) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hsource : n = a + (b + 1)) (hunion : m = n + a) :
    ∀ (i : (Unit ⊕ Fin b) ⊕ Fin a) (j : Unit ⊕ Fin a),
      originalProfileFrame A a b a (by omega) (.inr i)
        (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inr j))) =
      originalProfileFrame P 0 b a (by omega) (.inr i)
        (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inr j))) := by
  obtain ⟨_, hends⟩ := originalAmalgamation_prefix_xi_suffix_zeta P A q v u hq hv hwindow hA
  obtain ⟨_, hcore⟩ := originalAmalgamation_suffix_xi_prefix_zeta P A q v u hq hv hwindow hA
  intro i j
  let k : Fin n := match i with
    | .inl i => ⟨(commonCoreFinEquiv b i).val, by have := (commonCoreFinEquiv b i).isLt; omega⟩
    | .inr i => ⟨b + 1 + i.val, by have := i.isLt; omega⟩
  let s : Fin (n + 1) := ⟨b + 1 + (commonCoreFinEquiv a j).val, by
    have := (commonCoreFinEquiv a j).isLt; omega⟩
  let rA : Fin (m + 1) := ⟨m - n + k.val + 1, by have := k.isLt; omega⟩
  let sA : Fin (m + 1) := ⟨m - n + s.val, by have := s.isLt; omega⟩
  have hrP : (commonCoreFiniteRows 0 b a (.inr i)).val = k.succ.val := by
    rcases i with i | i
    · have he := commonCoreFiniteRows_core 0 b a i
      change (commonCoreFiniteRows 0 b a (.inr (.inl i))).val =
        (commonCoreFinEquiv b i).val + 1
      omega
    · have he := commonCoreFiniteRows_right 0 b a i
      change (commonCoreFiniteRows 0 b a (.inr (.inr i))).val = b + 1 + i.val + 1
      omega
  have hrA : (commonCoreFiniteRows a b a (.inr i)).val = rA.val := by
    rcases i with i | i
    · have he := commonCoreFiniteRows_core a b a i
      change (commonCoreFiniteRows a b a (.inr (.inl i))).val =
        m - n + (commonCoreFinEquiv b i).val + 1
      omega
    · have he := commonCoreFiniteRows_right a b a i
      change (commonCoreFiniteRows a b a (.inr (.inr i))).val = m - n + (b + 1 + i.val) + 1
      omega
  have hsP : (commonCoreFiniteCols 0 b a
      (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inr j)))).val = s.val := by
    simpa only [Nat.zero_add, s] using commonCoreFiniteCols_border 0 b a j
  have hsA : (commonCoreFiniteCols a b a
      (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inr j)))).val = sA.val := by
    have he := commonCoreFiniteCols_border a b a j
    change (commonCoreFiniteCols a b a
      (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inr j)))).val =
        m - n + (b + 1 + (commonCoreFinEquiv a j).val)
    omega
  have hP := originalProfileFrame_entry_of_val P 0 b a (by omega)
    (.inr i) (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inr j)))
    k.succ s hrP hsP
  have hU := originalProfileFrame_entry_of_val A a b a (by omega)
    (.inr i) (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inr j)))
    rA sA hrA hsA
  have hx := (hcore k).1
  change A.xi rA = P.xi k.succ at hx
  have hz := (hends s).2
  change A.zeta sA = P.zeta s at hz
  rw [hU, hP, hx, hz]

end SkewCornerDescent.Matrix.SelectedCoordinate
