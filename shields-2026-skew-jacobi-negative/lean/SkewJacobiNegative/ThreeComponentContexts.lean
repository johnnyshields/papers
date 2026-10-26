/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.SingletonLift

/-!
# Three-component beta contexts

Actual ordered beta lists and determinant expansions in `eq:end-lists`,
`eq:middle-lists`, `eq:end-polynomial`, and `eq:middle-polynomial` of
`shields-2026-skew-jacobi-negative.tex`.  The constructors require neither
 density nor a restriction on the negative sites of the core.
-/

namespace SkewJacobiNegative

/-- The six positive geometric parameters; these are not polynomial certificates. -/
structure ThreeComponentParameters where
  ell : ℤ
  m : ℤ
  g₁ : ℤ
  g₂ : ℤ
  u : ℤ
  v : ℤ
  ell_pos : 0 < ell
  m_pos : 0 < m
  g₁_pos : 0 < g₁
  g₂_pos : 0 < g₂
  u_pos : 0 < u
  v_pos : 0 < v

namespace ThreeComponentParameters

def left (P : ThreeComponentParameters) : ℤ := P.ell + P.g₁
def right (P : ThreeComponentParameters) : ℤ := P.m + P.g₂

theorem left_pos (P : ThreeComponentParameters) : 0 < P.left := by
  have := P.ell_pos
  have := P.g₁_pos
  unfold left
  omega

theorem right_pos (P : ThreeComponentParameters) : 0 < P.right := by
  have := P.m_pos
  have := P.g₂_pos
  unfold right
  omega

/-- Whole-parent rotation exchanges the two singleton and exterior data. -/
def swap (P : ThreeComponentParameters) : ThreeComponentParameters where
  ell := P.m
  m := P.ell
  g₁ := P.g₂
  g₂ := P.g₁
  u := P.v
  v := P.u
  ell_pos := P.m_pos
  m_pos := P.ell_pos
  g₁_pos := P.g₂_pos
  g₂_pos := P.g₁_pos
  u_pos := P.v_pos
  v_pos := P.u_pos

@[simp] theorem swap_left (P : ThreeComponentParameters) : P.swap.left = P.right := rfl
@[simp] theorem swap_right (P : ThreeComponentParameters) : P.swap.right = P.left := rfl
@[simp] theorem swap_swap (P : ThreeComponentParameters) : P.swap.swap = P := by
  cases P
  rfl

end ThreeComponentParameters

namespace BetaDiagram

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

/-- Literal rotation preserves absence of zero indices. -/
theorem rotate_zeroFree (Q : BetaDiagram n) (hQ : Q.ZeroFree) : Q.rotate.ZeroFree := by
  intro i j he
  apply hQ j.rev i.rev
  change -Q.col i.rev = -Q.row j.rev at he
  omega

/-- Translation has no effect on the corner board. -/
@[simp] theorem shifted_cornerPolynomial (Q : BetaDiagram (n + 1)) (c : ℤ) :
    (Q.shifted c).cornerPolynomial = Q.cornerPolynomial := by
  unfold cornerPolynomial
  congr 1
  ext i j
  simp [cornerBoard, betaBoard, shifted]

/-- A separated singleton on the right, normalized at its last column.
The operation is the literal reverse of `singletonCore`. -/
def rightSingletonCore (Q : BetaDiagram (n + 1)) (m g : ℤ)
    (hm : 0 < m) (hg : 0 < g) : BetaDiagram (n + 2) :=
  ((Q.rotate.singletonCore m g hm hg).rotate).shifted
    (m + g - Q.col (Fin.last n))

@[simp] theorem rightSingletonCore_row_core (Q : BetaDiagram (n + 1))
    (m g : ℤ) (hm : 0 < m) (hg : 0 < g) (i : Fin (n + 1)) :
    (Q.rightSingletonCore m g hm hg).row i.castSucc =
      Q.row i + m + g - Q.col (Fin.last n) := by
  simp [rightSingletonCore, shifted, rotate, singletonCore, Fin.rev_castSucc,
    Fin.rev_succ, Fin.rev_rev]
  ring

@[simp] theorem rightSingletonCore_row_last (Q : BetaDiagram (n + 1))
    (m g : ℤ) (hm : 0 < m) (hg : 0 < g) :
    (Q.rightSingletonCore m g hm hg).row (Fin.last (n + 1)) = m := by
  simp [rightSingletonCore, shifted, rotate, singletonCore, Fin.rev_last,
    Fin.rev_zero]

@[simp] theorem rightSingletonCore_col_core (Q : BetaDiagram (n + 1))
    (m g : ℤ) (hm : 0 < m) (hg : 0 < g) (i : Fin (n + 1)) :
    (Q.rightSingletonCore m g hm hg).col i.castSucc =
      Q.col i + m + g - Q.col (Fin.last n) := by
  simp [rightSingletonCore, shifted, rotate, singletonCore, Fin.rev_castSucc,
    Fin.rev_succ, Fin.rev_rev]
  ring

@[simp] theorem rightSingletonCore_col_last (Q : BetaDiagram (n + 1))
    (m g : ℤ) (hm : 0 < m) (hg : 0 < g) :
    (Q.rightSingletonCore m g hm hg).col (Fin.last (n + 1)) = 0 := by
  simp [rightSingletonCore, shifted, rotate, singletonCore, Fin.rev_last,
    Fin.rev_zero]
  ring

@[simp] theorem rightSingletonCore_schur (Q : BetaDiagram (n + 1))
    (m g : ℤ) (hm : 0 < m) (hg : 0 < g) :
    (Q.rightSingletonCore m g hm hg).schur = Q.schur * complete m := by
  simp only [rightSingletonCore, shifted_schur, rotate_schur, singletonCore_schur]
  ring

theorem rightSingletonCore_zeroFree (Q : BetaDiagram (n + 1)) (hZ : Q.ZeroFree)
    (m g : ℤ) (hm : 0 < m) (hg : 0 < g) :
    (Q.rightSingletonCore m g hm hg).ZeroFree :=
  ((Q.rotate.singletonCore m g hm hg).rotate).shifted_zeroFree
    ((Q.rotate.singletonCore m g hm hg).rotate_zeroFree
      (Q.rotate.singletonCore_zeroFree (Q.rotate_zeroFree hZ) m g hm hg)) _

/-- Reverse a bordered right-singleton board to obtain its true left-singleton board. -/
theorem rightSingletonCore_border_schur (Q : BetaDiagram (n + 1))
    (m g x v : ℤ) (hm : 0 < m) (hg : 0 < g) (hx : 0 < x) (hv : 0 < v) :
    ((Q.rightSingletonCore m g hm hg).positiveBorder x v hx hv).schur =
      complete (m + v) * (Q.positiveBorder x (m + g) hx (by omega)).schur -
        complete m * (Q.positiveBorder x (m + g + v) hx (by omega)).schur := by
  let A := Q.rotate.singletonCore m g hm hg
  have he : ((Q.rightSingletonCore m g hm hg).positiveBorder x v hx hv).matrix =
      (A.rotate.positiveBorder x v hx hv).matrix := by
    apply Matrix.ext
    intro i j
    apply congrArg complete
    cases i using Fin.cases <;> cases j using Fin.lastCases <;>
      simp only [rightSingletonCore, shifted, positiveBorder_row_zero,
        positiveBorder_row_succ, positiveBorder_col_castSucc,
        positiveBorder_col_last] <;> ring
  change (((Q.rightSingletonCore m g hm hg).positiveBorder x v hx hv).matrix).det = _
  rw [he]
  change (A.rotate.positiveBorder x v hx hv).schur = _
  rw [positiveBorder_rotate_schur]
  have hctx := Q.rotate.singletonContext_schur m v x g hm hv hx hg
  simp only [singletonContext, shifted_schur] at hctx
  rw [hctx, positiveBorder_rotate_schur, positiveBorder_rotate_schur]

/-- The actual maximal cofactor with component order `(ell),(m),Q`. -/
def threeEndCore (Q : BetaDiagram (n + 1)) (P : ThreeComponentParameters) :
    BetaDiagram (n + 3) :=
  (Q.singletonCore P.m P.g₂ P.m_pos P.g₂_pos).singletonCore
    P.ell P.g₁ P.ell_pos P.g₁_pos

/-- The actual maximal cofactor with component order `(ell),Q,(m)`. -/
def threeMiddleCore (Q : BetaDiagram (n + 1)) (P : ThreeComponentParameters) :
    BetaDiagram (n + 3) :=
  (Q.rightSingletonCore P.m P.g₂ P.m_pos P.g₂_pos).singletonCore
    P.ell P.g₁ P.ell_pos P.g₁_pos

/-- The end-placement parent of `eq:end-lists`. -/
def threeEndContext (Q : BetaDiagram (n + 1)) (P : ThreeComponentParameters) :
    BetaDiagram (n + 4) :=
  (Q.singletonCore P.m P.g₂ P.m_pos P.g₂_pos).singletonContext
    P.ell P.u P.v P.g₁ P.ell_pos P.u_pos P.v_pos P.g₁_pos

/-- The middle-placement parent of `eq:middle-lists`. -/
def threeMiddleContext (Q : BetaDiagram (n + 1)) (P : ThreeComponentParameters) :
    BetaDiagram (n + 4) :=
  (Q.rightSingletonCore P.m P.g₂ P.m_pos P.g₂_pos).singletonContext
    P.ell P.u P.v P.g₁ P.ell_pos P.u_pos P.v_pos P.g₁_pos

theorem threeEndContext_connected (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) : (Q.threeEndContext P).Connected :=
  (Q.singletonCore P.m P.g₂ P.m_pos P.g₂_pos).singletonContext_connected
    P.ell P.u P.v P.g₁ P.ell_pos P.u_pos P.v_pos P.g₁_pos

theorem threeMiddleContext_connected (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) : (Q.threeMiddleContext P).Connected :=
  (Q.rightSingletonCore P.m P.g₂ P.m_pos P.g₂_pos).singletonContext_connected
    P.ell P.u P.v P.g₁ P.ell_pos P.u_pos P.v_pos P.g₁_pos

theorem threeEndContext_zeroFree (Q : BetaDiagram (n + 1)) (hZ : Q.ZeroFree)
    (P : ThreeComponentParameters) : (Q.threeEndContext P).ZeroFree :=
  (Q.singletonCore P.m P.g₂ P.m_pos P.g₂_pos).singletonContext_zeroFree
    (Q.singletonCore_zeroFree hZ P.m P.g₂ P.m_pos P.g₂_pos)
    P.ell P.u P.v P.g₁ P.ell_pos P.u_pos P.v_pos P.g₁_pos

theorem threeMiddleContext_zeroFree (Q : BetaDiagram (n + 1)) (hZ : Q.ZeroFree)
    (P : ThreeComponentParameters) : (Q.threeMiddleContext P).ZeroFree :=
  (Q.rightSingletonCore P.m P.g₂ P.m_pos P.g₂_pos).singletonContext_zeroFree
    (Q.rightSingletonCore_zeroFree hZ P.m P.g₂ P.m_pos P.g₂_pos)
    P.ell P.u P.v P.g₁ P.ell_pos P.u_pos P.v_pos P.g₁_pos

@[simp] theorem threeEndCore_schur (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    (Q.threeEndCore P).schur = complete P.ell * complete P.m * Q.schur := by
  simp only [threeEndCore, singletonCore_schur]
  ring

@[simp] theorem threeMiddleCore_schur (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    (Q.threeMiddleCore P).schur = complete P.ell * complete P.m * Q.schur := by
  simp only [threeMiddleCore, singletonCore_schur, rightSingletonCore_schur]
  ring

/-- The maximal complementary polynomial is the whole three-factor product. -/
@[simp] theorem threeEndContext_cornerPolynomial (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    (Q.threeEndContext P).cornerPolynomial = complete P.ell * complete P.m * Q.schur := by
  simp only [threeEndContext, singletonContext, shifted_cornerPolynomial,
    positiveBorder_cornerPolynomial, singletonCore_schur]
  ring

@[simp] theorem threeMiddleContext_cornerPolynomial (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    (Q.threeMiddleContext P).cornerPolynomial = complete P.ell * complete P.m * Q.schur := by
  simp only [threeMiddleContext, singletonContext, shifted_cornerPolynomial,
    positiveBorder_cornerPolynomial, singletonCore_schur, rightSingletonCore_schur]
  ring

/-- Full end-placement determinant identity, without a density hypothesis. -/
theorem threeEndContext_schur (Q : BetaDiagram (n + 1)) (P : ThreeComponentParameters) :
    (Q.threeEndContext P).schur =
      (complete (P.ell + P.u) * complete (P.m + P.left) -
        complete P.ell * complete (P.m + P.left + P.u)) *
          (Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur -
      complete P.m * complete (P.ell + P.u) *
        (Q.positiveBorder (P.left + P.right) P.v
          (by have := P.left_pos; have := P.right_pos; omega) P.v_pos).schur +
      complete P.ell * complete P.m *
        (Q.positiveBorder (P.left + P.right + P.u) P.v
          (by have := P.left_pos; have := P.right_pos; have := P.u_pos; omega)
          P.v_pos).schur := by
  have hu := P.u_pos
  have hv := P.v_pos
  have hℓ := P.ell_pos
  have hm := P.m_pos
  have hg₁ := P.g₁_pos
  have hg₂ := P.g₂_pos
  have hborder : ∀ (x : ℤ) (hx : 0 < x),
      ((Q.singletonCore P.m P.g₂ hm hg₂).positiveBorder x P.v hx hv).schur =
        complete (P.m + x) * (Q.positiveBorder P.right P.v P.right_pos hv).schur -
          complete P.m * (Q.positiveBorder (P.right + x) P.v (by
            have := P.right_pos; omega) hv).schur := by
    intro x hx
    have h := Q.singletonContext_schur P.m x P.v P.g₂ hm hx hv hg₂
    simpa only [singletonContext, shifted_schur, ThreeComponentParameters.right] using h
  rw [threeEndContext, singletonContext_schur, hborder, hborder]
  have h₁ : P.right + (P.ell + P.g₁) = P.left + P.right := by
    unfold ThreeComponentParameters.left
    ring
  have h₂ : P.right + (P.ell + P.g₁ + P.u) = P.left + P.right + P.u := by
    unfold ThreeComponentParameters.left
    ring
  simp only [h₁, h₂]
  change _ = _
  simp only [ThreeComponentParameters.left]
  ring

/-- Full middle-placement determinant identity, without a density hypothesis. -/
theorem threeMiddleContext_schur (Q : BetaDiagram (n + 1)) (P : ThreeComponentParameters) :
    (Q.threeMiddleContext P).schur =
      complete (P.ell + P.u) * complete (P.m + P.v) *
        (Q.positiveBorder P.left P.right P.left_pos P.right_pos).schur -
      complete P.ell * complete (P.m + P.v) *
        (Q.positiveBorder (P.left + P.u) P.right
          (by have := P.left_pos; have := P.u_pos; omega) P.right_pos).schur -
      complete (P.ell + P.u) * complete P.m *
        (Q.positiveBorder P.left (P.right + P.v) P.left_pos
          (by have := P.right_pos; have := P.v_pos; omega)).schur +
      complete P.ell * complete P.m *
        (Q.positiveBorder (P.left + P.u) (P.right + P.v)
          (by have := P.left_pos; have := P.u_pos; omega)
          (by have := P.right_pos; have := P.v_pos; omega)).schur := by
  rw [threeMiddleContext, singletonContext_schur,
    rightSingletonCore_border_schur, rightSingletonCore_border_schur]
  simp only [ThreeComponentParameters.left, ThreeComponentParameters.right]
  ring

/-- Arbitrary connected mates expose the true three-factor inventory, with
multiplicity.  No decomposition or negative pattern of the mate is assumed. -/
theorem three_context_mate_components (Q : BetaDiagram (n + 1))
    (hC : Q.Connected) (hZ : Q.ZeroFree) (P : ThreeComponentParameters)
    (middle : Bool) (E : BetaDiagram k) (hE : E.Connected)
    (he : (if middle then Q.threeMiddleContext P else Q.threeEndContext P).schur = E.schur) :
    ∃ hrow : k = n + 4,
      let F := E.castOrder hrow
      ∃ hP : F.PositiveCorner, F.ZeroFree ∧
        ∀ K : ComponentDecomposition (F.cornerDiagram hP),
          Multiset.Rel (fun X Y : Σ a : ℕ, BetaDiagram a => X.2.schur = Y.2.schur)
            (([⟨1, singletonDiagram P.ell P.ell_pos⟩,
              ⟨1, singletonDiagram P.m P.m_pos⟩, ⟨n + 1, Q⟩] :
              List (Σ a : ℕ, BetaDiagram a)) : Multiset (Σ a : ℕ, BetaDiagram a))
            (K.components : Multiset _) := by
  let D := if middle then Q.threeMiddleContext P else Q.threeEndContext P
  have hD : D.Connected := by
    cases middle <;> simp only [D, Bool.false_eq_true, if_false, if_true]
    · exact Q.threeEndContext_connected P
    · exact Q.threeMiddleContext_connected P
  have hDZ : D.ZeroFree := by
    cases middle <;> simp only [D, Bool.false_eq_true, if_false, if_true]
    · exact Q.threeEndContext_zeroFree hZ P
    · exact Q.threeMiddleContext_zeroFree hZ P
  have hprod : D.cornerPolynomial = complete P.ell * complete P.m * Q.schur := by
    cases middle <;> simp [D]
  have hrow : k = n + 4 := (D.row_count_of_schur_eq E he).symm
  refine ⟨hrow, ?_⟩
  let F := E.castOrder hrow
  have hFC : F.Connected := (E.castOrder_connected hrow).mpr hE
  have hFeq : D.schur = F.schur := by simpa only [F, castOrder_schur] using he
  have hFZ := D.zeroFree_of_schur_eq F hD hFC hDZ hFeq
  let hPF := F.positiveCorner_of_connected_zeroFree hFC hFZ
  refine ⟨hPF, hFZ, ?_⟩
  intro K
  apply (F.cornerDiagram hPF).component_matching_of_product K
    [⟨1, singletonDiagram P.ell P.ell_pos⟩,
      ⟨1, singletonDiagram P.m P.m_pos⟩, ⟨n + 1, Q⟩]
  · intro X hX
    simp at hX
    rcases hX with rfl | rfl | rfl
    · exact singletonDiagram_connected P.ell P.ell_pos
    · exact singletonDiagram_connected P.m P.m_pos
    · exact hC
  · have hc := D.cornerPolynomial_eq_of_schur_eq F hD hFC hFeq
    rw [hprod, ← F.cornerDiagram_schur hPF] at hc
    simpa only [List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, singletonDiagram_schur, mul_assoc] using hc

/-- All seven ordered row betas in the end placement. -/
theorem threeEndContext_rows (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    (Q.threeEndContext P).row =
      ![Q.row 0 + P.left + P.right + P.u + P.v,
        Q.row 0 + P.left + P.right + P.v,
        Q.row 0 + P.right + P.v,
        P.v + Q.row 0, P.v + Q.row 1, P.v + Q.row 2, P.v + Q.row 3] := by
  funext i
  fin_cases i <;>
    simp [threeEndContext, singletonContext, shifted, singletonCore,
      positiveBorder, ThreeComponentParameters.left, ThreeComponentParameters.right,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.snoc,
      Fin.castPred, Fin.castLT] <;> ring

/-- All seven ordered column betas; the normalization is the manuscript's one. -/
theorem threeEndContext_cols (Q : BetaDiagram 4) (hN : Q.Normalized)
    (P : ThreeComponentParameters) :
    (Q.threeEndContext P).col =
      ![Q.row 0 + P.right + P.g₁ + P.v, Q.row 0 + P.g₂ + P.v,
        P.v + Q.col 0, P.v + Q.col 1, P.v + Q.col 2, P.v, 0] := by
  have hz : Q.col 3 = 0 := by simpa using hN (by omega)
  funext i
  fin_cases i <;>
    simp [threeEndContext, singletonContext, shifted, singletonCore,
      positiveBorder, ThreeComponentParameters.right, hz,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.snoc,
      Fin.castPred, Fin.castLT] <;> ring

/-- The ordered middle row list, not a row-multiset surrogate. -/
theorem threeMiddleContext_rows (Q : BetaDiagram 4) (hN : Q.Normalized)
    (P : ThreeComponentParameters) :
    (Q.threeMiddleContext P).row =
      ![Q.row 0 + P.left + P.right + P.u + P.v,
        Q.row 0 + P.left + P.right + P.v,
        P.v + P.right + Q.row 0, P.v + P.right + Q.row 1,
        P.v + P.right + Q.row 2, P.v + P.right + Q.row 3, P.v + P.m] := by
  have hz : Q.col 3 = 0 := by simpa using hN (by omega)
  funext i
  fin_cases i <;>
    simp [threeMiddleContext, singletonContext, shifted, singletonCore,
      positiveBorder, rightSingletonCore, rotate, ThreeComponentParameters.left,
      ThreeComponentParameters.right, hz, Fin.cons, Fin.cases, Fin.induction,
      Fin.induction.go, Fin.snoc, Fin.castPred, Fin.castLT] <;> ring

/-- The ordered middle column list. -/
theorem threeMiddleContext_cols (Q : BetaDiagram 4) (hN : Q.Normalized)
    (P : ThreeComponentParameters) :
    (Q.threeMiddleContext P).col =
      ![Q.row 0 + P.right + P.g₁ + P.v,
        P.v + P.right + Q.col 0, P.v + P.right + Q.col 1,
        P.v + P.right + Q.col 2, P.v + P.right, P.v, 0] := by
  have hz : Q.col 3 = 0 := by simpa using hN (by omega)
  funext i
  fin_cases i <;>
    simp [threeMiddleContext, singletonContext, shifted, singletonCore,
      positiveBorder, rightSingletonCore, rotate, ThreeComponentParameters.right, hz,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.snoc,
      Fin.castPred, Fin.castLT] <;> ring

/-- A literal end-placement board determines its two exterior margins. -/
theorem threeEndContext_margins (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    (Q.threeEndContext P).topMargin = P.u ∧
      (Q.threeEndContext P).bottomMargin = P.v := by
  let B := (Q.threeEndCore P).positiveBorder P.u P.v P.u_pos P.v_pos
  constructor
  · have ht : B.topMargin = P.u := by simp [B]
    change B.row 0-B.row (0 : Fin (n+3)).succ = P.u at ht
    change (B.row 0+P.v)-(B.row (0 : Fin (n+3)).succ+P.v) = P.u
    omega
  · have hb : B.bottomMargin = P.v := by simp [B]
    change B.col (Fin.last (n+2)).castSucc-B.col (Fin.last (n+3)) = P.v at hb
    change (B.col (Fin.last (n+2)).castSucc+P.v)-
      (B.col (Fin.last (n+3))+P.v) = P.v
    omega

theorem threeMiddleContext_margins (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    (Q.threeMiddleContext P).topMargin = P.u ∧
      (Q.threeMiddleContext P).bottomMargin = P.v := by
  let B := (Q.threeMiddleCore P).positiveBorder P.u P.v P.u_pos P.v_pos
  constructor
  · have ht : B.topMargin = P.u := by simp [B]
    change B.row 0-B.row (0 : Fin (n+3)).succ = P.u at ht
    change (B.row 0+P.v)-(B.row (0 : Fin (n+3)).succ+P.v) = P.u
    omega
  · have hb : B.bottomMargin = P.v := by simp [B]
    change B.col (Fin.last (n+2)).castSucc-B.col (Fin.last (n+3)) = P.v at hb
    change (B.col (Fin.last (n+2)).castSucc+P.v)-
      (B.col (Fin.last (n+3))+P.v) = P.v
    omega

/-- A top shift changes precisely the left singleton's length. -/
theorem singletonCore_extendTop_schur (Q : BetaDiagram (n + 1))
    (s g t : ℤ) (hs : 0 < s) (hg : 0 < g) (ht : 0 < t) :
    ((Q.singletonCore s g hs hg).extendTop t ht).schur =
      complete (s + t) * Q.schur := by
  have hm : ((Q.singletonCore s g hs hg).extendTop t ht).matrix =
      (Q.singletonCore (s + t) g (by omega) hg).matrix := by
    apply Matrix.ext
    intro i j
    apply congrArg complete
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [extendTop, singletonCore] <;> ring
  unfold schur at ⊢
  rw [hm]
  exact Q.singletonCore_schur (s + t) g (by omega) hg

/-- A bottom shift acts inside the true rightmost core. -/
theorem singletonCore_extendBottom_schur (Q : BetaDiagram (n + 1))
    (s g t : ℤ) (hs : 0 < s) (hg : 0 < g) (ht : 0 < t) :
    ((Q.singletonCore s g hs hg).extendBottom t ht).schur =
      complete s * (Q.extendBottom t ht).schur := by
  have hm : ((Q.singletonCore s g hs hg).extendBottom t ht).matrix =
      ((Q.extendBottom t ht).singletonCore s g hs hg).matrix := by
    apply Matrix.ext
    intro i j
    apply congrArg complete
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [extendBottom, singletonCore, Fin.ext_iff] <;> ring
  unfold schur at ⊢
  rw [hm]
  exact (Q.extendBottom t ht).singletonCore_schur s g hs hg

/-- The top endpoint shift of a right singleton board acts inside its core. -/
theorem rightSingletonCore_extendTop_schur (Q : BetaDiagram (n + 1))
    (m g t : ℤ) (hm : 0 < m) (hg : 0 < g) (ht : 0 < t) :
    ((Q.rightSingletonCore m g hm hg).extendTop t ht).schur =
      (Q.extendTop t ht).schur * complete m := by
  have he : ((Q.rightSingletonCore m g hm hg).extendTop t ht).matrix =
      ((Q.extendTop t ht).rightSingletonCore m g hm hg).matrix := by
    apply Matrix.ext
    intro i j
    apply congrArg complete
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [extendTop, rightSingletonCore_row_core, rightSingletonCore_row_last,
        rightSingletonCore_col_core, rightSingletonCore_col_last,
        Fin.castSucc_eq_zero_iff, Fin.last_eq_zero_iff] <;> try split_ifs <;> ring
  unfold schur at ⊢
  rw [he]
  exact (Q.extendTop t ht).rightSingletonCore_schur m g hm hg

/-- The bottom shift changes the right singleton's length, including all ties. -/
theorem rightSingletonCore_extendBottom_schur (Q : BetaDiagram (n + 1))
    (m g t : ℤ) (hm : 0 < m) (hg : 0 < g) (ht : 0 < t) :
    ((Q.rightSingletonCore m g hm hg).extendBottom t ht).schur =
      Q.schur * complete (m + t) := by
  have he : ((Q.rightSingletonCore m g hm hg).extendBottom t ht).matrix =
      ((Q.rightSingletonCore (m + t) g (by omega) hg).shifted (-t)).matrix := by
    apply Matrix.ext
    intro i j
    apply congrArg complete
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [extendBottom, shifted, rightSingletonCore_row_core,
        rightSingletonCore_row_last, rightSingletonCore_col_core,
        rightSingletonCore_col_last, Fin.castSucc_ne_last] <;> ring
  change _ = _
  unfold schur at ⊢
  rw [he]
  change ((Q.rightSingletonCore (m + t) g (by omega) hg).shifted (-t)).schur = _
  rw [shifted_schur, rightSingletonCore_schur] <;> rfl

/-- The actual top first marker factors identically in both placements. -/
theorem threeEndCore_extendTop_schur (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    ((Q.threeEndCore P).extendTop P.u P.u_pos).schur =
      complete (P.ell + P.u) * complete P.m * Q.schur := by
  rw [threeEndCore, singletonCore_extendTop_schur, singletonCore_schur]
  ring

theorem threeMiddleCore_extendTop_schur (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    ((Q.threeMiddleCore P).extendTop P.u P.u_pos).schur =
      complete (P.ell + P.u) * complete P.m * Q.schur := by
  rw [threeMiddleCore, singletonCore_extendTop_schur, rightSingletonCore_schur]
  ring

/-- The different bottom first markers retain the true core extension. -/
theorem threeEndCore_extendBottom_schur (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    ((Q.threeEndCore P).extendBottom P.v P.v_pos).schur =
      complete P.ell * complete P.m * (Q.extendBottom P.v P.v_pos).schur := by
  rw [threeEndCore, singletonCore_extendBottom_schur, singletonCore_extendBottom_schur]
  ring

theorem threeMiddleCore_extendBottom_schur (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    ((Q.threeMiddleCore P).extendBottom P.v P.v_pos).schur =
      complete P.ell * complete (P.m + P.v) * Q.schur := by
  rw [threeMiddleCore, singletonCore_extendBottom_schur, rightSingletonCore_extendBottom_schur]
  ring

/-- The actual connected intermediate in `eq:intermediate-U`.
The first-column gap is produced by `x > ell`. -/
def threeComponentU (Q : BetaDiagram (n + 1)) (ell x u : ℤ)
    (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) : BetaDiagram (n + 2) where
  row := Fin.cons (Q.row 0 + x + u) (Q.extendTop x (by omega)).row
  col := Fin.cons (Q.row 0 + x - ell) Q.col
  row_strictAnti := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
        have h := (Q.extendTop x (by omega)).row_strictAnti.antitone (Fin.zero_le j)
        simp only [Fin.cons_zero, Fin.cons_succ]
        have htop : (Q.extendTop x (by omega)).row 0 = Q.row 0 + x := by
          simp [extendTop]
        rw [htop] at h
        omega
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      | succ j =>
        simpa only [Fin.cons_succ] using (Q.extendTop x (by omega)).row_strictAnti
          (show i < j by simpa using hij)
  col_strictAnti := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
        have h := Q.col_strictAnti.antitone (Fin.zero_le j)
        have h0 := Q.row_nonempty 0
        simp only [Fin.cons_zero, Fin.cons_succ]
        omega
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      | succ j =>
        simpa only [Fin.cons_succ] using Q.col_strictAnti (show i < j by simpa using hij)
  row_nonempty := by
    intro i
    cases i using Fin.cases with
    | zero => simp only [Fin.cons_zero]; omega
    | succ i =>
      simpa only [Fin.cons_succ, extendTop] using
        (Q.extendTop x (by omega)).row_nonempty i

theorem threeComponentU_connected (Q : BetaDiagram (n + 1))
    (hP : Q.PositiveCorner) (ell x u : ℤ)
    (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    (Q.threeComponentU ell x u hℓ hx hu).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  cases i using Fin.cases with
  | zero =>
    simp only [threeComponentU, Fin.cons_zero]
    change Q.row 0 + x - ell ≤ (Q.extendTop x (by omega)).row 0
    simp only [extendTop, ite_true]
    omega
  | succ i =>
    have hin : i.val + 1 < n + 1 := by simpa using hi
    have hp := hP ⟨i.val, by omega⟩
    change Q.col i ≤ (Q.extendTop x (by omega)).row ⟨i.val + 1, hin⟩
    have hn : (⟨i.val + 1, hin⟩ : Fin (n + 1)) ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      change i.val+1 = 0 at hv
      omega
    simp only [extendTop, if_neg hn]
    change Q.col i < Q.row ⟨i.val+1,hin⟩ at hp
    exact hp.le

/-- The connected intermediate has no coordinate divisor. -/
theorem threeComponentU_complete_not_dvd (Q : BetaDiagram (n + 2))
    (hP : Q.PositiveCorner) (ell x u s : ℤ)
    (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) (hs : 0 < s) :
    ¬ complete s ∣ (Q.threeComponentU ell x u hℓ hx hu).schur :=
  (Q.threeComponentU ell x u hℓ hx hu).complete_not_dvd_connected
    (Q.threeComponentU_connected hP ell x u hℓ hx hu) s hs

/-- Its ordinary degree and irreducibility are proved from actual connected lists. -/
theorem threeComponentU_irreducible (Q : BetaDiagram (n + 1))
    (hP : Q.PositiveCorner) (ell x u : ℤ)
    (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    Irreducible (Q.threeComponentU ell x u hℓ hx hu).schur :=
  (Q.threeComponentU ell x u hℓ hx hu).schur_irreducible
    (Q.threeComponentU_connected hP ell x u hℓ hx hu)

/-- Full two-term expansion of the actual intermediate determinant. -/
theorem threeComponentU_schur (Q : BetaDiagram (n + 1)) (ell x u : ℤ)
    (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    (Q.threeComponentU ell x u hℓ hx hu).schur =
      complete (ell + u) * (Q.extendTop x (by omega)).schur -
        complete ell * (Q.extendTop (x + u) (by omega)).schur := by
  classical
  have hfirst : (Q.threeComponentU ell x u hℓ hx hu).matrix.submatrix
      Fin.succ Fin.succ = (Q.extendTop x (by omega)).matrix := by
    apply Matrix.ext
    intro i j
    rfl
  have hsecond : (Q.threeComponentU ell x u hℓ hx hu).matrix.submatrix
      ((0 : Fin (n + 1)).succ).succAbove Fin.succ =
        (Q.extendTop (x + u) (by omega)).matrix := by
    apply Matrix.ext
    intro i j
    apply congrArg complete
    cases i using Fin.cases <;>
      simp [threeComponentU, extendTop, Fin.succ_succAbove_zero,
        Fin.succ_succAbove_succ] <;> ring
  have hz : ∀ i : Fin n,
      (Q.threeComponentU ell x u hℓ hx hu).matrix i.succ.succ 0 = 0 := by
    intro i
    have h := Q.row_strictAnti.antitone (Fin.zero_le i.succ)
    apply complete_of_neg
    simp only [matrix, Matrix.of_apply, threeComponentU, Fin.cons_succ,
      Fin.cons_zero, extendTop, Fin.succ_ne_zero, if_false]
    omega
  unfold schur at ⊢
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succAbove_zero]
  rw [hfirst, hsecond]
  have h0 : (Q.threeComponentU ell x u hℓ hx hu).matrix 0 0 =
      complete (ell + u) := by
    simp only [matrix, Matrix.of_apply, threeComponentU, Fin.cons_zero]
    congr 1
    ring
  have h1 : (Q.threeComponentU ell x u hℓ hx hu).matrix (0 : Fin (n + 1)).succ 0 =
      complete ell := by
    simp only [matrix, Matrix.of_apply, threeComponentU, Fin.cons_zero,
      Fin.cons_succ, extendTop, ite_true]
    congr 1
    ring
  simp only [h0, h1, hz, Fin.val_zero, Fin.val_succ, pow_zero, pow_one,
    one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  ring

/-- The intermediate's zero-free board includes its entire new first column. -/
theorem threeComponentU_zeroFree (Q : BetaDiagram (n + 1)) (hZ : Q.ZeroFree)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    (Q.threeComponentU ell x u hℓ hx hu).ZeroFree := by
  intro i j he
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp only [threeComponentU, Fin.cons_zero] at he; omega
    | succ j =>
      have hc := Q.col_strictAnti.antitone (Fin.zero_le j)
      have hd := Q.row_nonempty 0
      simp only [threeComponentU, Fin.cons_zero, Fin.cons_succ] at he
      omega
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      cases i using Fin.cases with
      | zero =>
        simp only [threeComponentU, Fin.cons_succ, Fin.cons_zero, extendTop, ite_true] at he
        omega
      | succ i =>
        have hr := Q.row_strictAnti.antitone (Fin.zero_le i.succ)
        simp only [threeComponentU, Fin.cons_succ, Fin.cons_zero, extendTop,
          Fin.succ_ne_zero, if_false] at he
        omega
    | succ j =>
      by_cases hi : i = 0
      · have hc := Q.col_strictAnti.antitone (Fin.zero_le j)
        have hd := Q.row_nonempty 0
        simp only [threeComponentU, Fin.cons_succ, hi, extendTop, ite_true] at he
        omega
      · apply hZ i j
        simpa only [threeComponentU, Fin.cons_succ, extendTop, if_neg hi] using he

/-- Ordered beta-list extensionality; the validity proofs are propositionally irrelevant. -/
theorem eq_of_lists (D E : BetaDiagram n) (hr : D.row = E.row) (hc : D.col = E.col) :
    D = E := by
  cases D
  cases E
  cases hr
  cases hc
  rfl

/-- The actual U intermediate is a singleton context over the normalized actual maximal child.
This identifies the precise source of the column/hook rigidity input. -/
theorem threeComponentU_eq_singletonContext (Q : BetaDiagram 4)
    (hP : Q.PositiveCorner) (hN : Q.Normalized)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    Q.threeComponentU ell x u hℓ hx hu =
      ((Q.cornerDiagram hP).shifted (-Q.col 2)).singletonContext
        ell u (Q.col 2) (Q.row 0+x-ell-Q.row 1)
        hℓ hu
        (by
          have hc := Q.col_strictAnti (show (2 : Fin 4) < 3 by decide)
          have hz : Q.col 3 = 0 := by simpa using hN (by omega)
          omega)
        (by
          have hr := Q.row_strictAnti (show (0 : Fin 4) < 1 by decide)
          omega) := by
  have hz : Q.col 3 = 0 := by simpa using hN (by omega)
  apply eq_of_lists
  · funext i
    fin_cases i <;>
      simp [threeComponentU, singletonContext, singletonCore, shifted,
        positiveBorder, cornerDiagram, extendTop, hz, Fin.cons, Fin.cases,
        Fin.induction, Fin.induction.go, Fin.snoc, Fin.castPred, Fin.castLT] <;> ring
  · funext i
    fin_cases i <;>
      simp [threeComponentU, singletonContext, singletonCore, shifted,
        positiveBorder, cornerDiagram, extendTop, hz, Fin.cons, Fin.cases,
        Fin.induction, Fin.induction.go, Fin.snoc, Fin.castPred, Fin.castLT] <;> ring


/-- The bottom intermediate is the actual rotated U diagram, normalized at its last column. -/
def threeComponentZ (Q : BetaDiagram (n + 1)) (m y v : ℤ)
    (hm : 0 < m) (hy : m < y) (hv : 0 < v) : BetaDiagram (n + 2) :=
  ((Q.rotate.threeComponentU m y v hm hy hv).rotate).shifted
    (y+v-Q.col (Fin.last n))

/-- Rotation and translation preserve the full bottom intermediate polynomial. -/
theorem threeComponentZ_schur (Q : BetaDiagram (n + 1)) (m y v : ℤ)
    (hm : 0 < m) (hy : m < y) (hv : 0 < v) :
    (Q.threeComponentZ m y v hm hy hv).schur =
      complete (m+v) * (Q.extendBottom y (by omega)).schur -
        complete m * (Q.extendBottom (y+v) (by omega)).schur := by
  rw [threeComponentZ, shifted_schur, rotate_schur, threeComponentU_schur,
    rotate_extendTop_schur, rotate_extendTop_schur]

theorem threeComponentZ_connected (Q : BetaDiagram (n + 1))
    (hP : Q.PositiveCorner) (m y v : ℤ)
    (hm : 0 < m) (hy : m < y) (hv : 0 < v) :
    (Q.threeComponentZ m y v hm hy hv).Connected := by
  have h := (Q.rotate.threeComponentU m y v hm hy hv).rotate_connected
    (Q.rotate.threeComponentU_connected (Q.rotate_positiveCorner hP) m y v hm hy hv)
  refine ⟨h.1, ?_⟩
  intro i hi
  have hh := h.2 i hi
  change (Q.rotate.threeComponentU m y v hm hy hv).rotate.col i+
      (y+v-Q.col (Fin.last n)) ≤
    (Q.rotate.threeComponentU m y v hm hy hv).rotate.row ⟨i.val+1, hi⟩+
      (y+v-Q.col (Fin.last n))
  omega

theorem threeComponentZ_zeroFree (Q : BetaDiagram (n + 1)) (hZ : Q.ZeroFree)
    (m y v : ℤ) (hm : 0 < m) (hy : m < y) (hv : 0 < v) :
    (Q.threeComponentZ m y v hm hy hv).ZeroFree :=
  (Q.rotate.threeComponentU m y v hm hy hv).rotate.shifted_zeroFree
    ((Q.rotate.threeComponentU m y v hm hy hv).rotate_zeroFree
      (Q.rotate.threeComponentU_zeroFree (Q.rotate_zeroFree hZ) m y v hm hy hv)) _

theorem threeComponentZ_irreducible (Q : BetaDiagram (n + 1))
    (hP : Q.PositiveCorner) (m y v : ℤ)
    (hm : 0 < m) (hy : m < y) (hv : 0 < v) :
    Irreducible (Q.threeComponentZ m y v hm hy hv).schur :=
  (Q.threeComponentZ m y v hm hy hv).schur_irreducible
    (Q.threeComponentZ_connected hP m y v hm hy hv)

/-- The new first row of U introduces no negative entry into its retained core block. -/
theorem threeComponentU_negative_core_iff (Q : BetaDiagram (n + 1))
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u)
    (i j : Fin (n + 1)) :
    (Q.threeComponentU ell x u hℓ hx hu).row i.succ <
        (Q.threeComponentU ell x u hℓ hx hu).col j.succ ↔ Q.row i < Q.col j := by
  by_cases hi : i = 0
  · subst i
    have hc := Q.col_strictAnti.antitone (Fin.zero_le j)
    have hd := Q.row_nonempty 0
    simp only [threeComponentU, Fin.cons_succ, extendTop, ite_true]
    omega
  · simp only [threeComponentU, Fin.cons_succ, extendTop, if_neg hi]

/-- Two genuine singleton cuts reconstruct the end parent and all six positive parameters. -/
theorem three_end_parent_of_cuts (D : BetaDiagram 7) (hP : D.PositiveCorner)
    (hcut₁ : D.row 2 < D.col 0) (hcut₂ : D.row 3 < D.col 1) :
    ∃ (Q : BetaDiagram 4) (P : ThreeComponentParameters),
      Q.Normalized ∧ D.TranslationEquivalent (Q.threeEndContext P) := by
  let Q := ((D.cornerDiagram hP).tail.tail).shifted (-D.col 5)
  let P : ThreeComponentParameters :=
    { ell := D.row 1-D.col 0
      m := D.row 2-D.col 1
      g₁ := D.col 0-D.row 2
      g₂ := D.col 1-D.row 3
      u := D.topMargin
      v := D.bottomMargin
      ell_pos := by have h := hP 0; exact sub_pos.mpr h
      m_pos := by have h := hP 1; exact sub_pos.mpr h
      g₁_pos := sub_pos.mpr hcut₁
      g₂_pos := sub_pos.mpr hcut₂
      u_pos := D.topMargin_pos
      v_pos := D.bottomMargin_pos }
  refine ⟨Q, P, ?_, D.col 6, ?_, ?_⟩
  · intro hn
    simp [Q, Normalized, shifted, tail, cornerDiagram]
  · intro i
    fin_cases i <;>
      simp [Q, P, threeEndContext, singletonContext, singletonCore, shifted,
        positiveBorder, tail, cornerDiagram, topMargin, bottomMargin,
        Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.snoc,
        Fin.castPred, Fin.castLT] <;> ring
  · intro i
    fin_cases i <;>
      simp [Q, P, threeEndContext, singletonContext, singletonCore, shifted,
        positiveBorder, tail, cornerDiagram, topMargin, bottomMargin,
        Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.snoc,
        Fin.castPred, Fin.castLT] <;> ring

/-- Genuine cuts around the four-row middle component reconstruct the full middle lists. -/
theorem three_middle_parent_of_cuts (D : BetaDiagram 7) (hP : D.PositiveCorner)
    (hcut₁ : D.row 2 < D.col 0) (hcut₂ : D.row 6 < D.col 4) :
    ∃ (Q : BetaDiagram 4) (P : ThreeComponentParameters),
      Q.Normalized ∧ D.TranslationEquivalent (Q.threeMiddleContext P) := by
  let Q := ((D.cornerDiagram hP).tail.init).shifted (-D.col 4)
  let P : ThreeComponentParameters :=
    { ell := D.row 1-D.col 0
      m := D.row 6-D.col 5
      g₁ := D.col 0-D.row 2
      g₂ := D.col 4-D.row 6
      u := D.topMargin
      v := D.bottomMargin
      ell_pos := by have h := hP 0; exact sub_pos.mpr h
      m_pos := by have h := hP 5; exact sub_pos.mpr h
      g₁_pos := sub_pos.mpr hcut₁
      g₂_pos := sub_pos.mpr hcut₂
      u_pos := D.topMargin_pos
      v_pos := D.bottomMargin_pos }
  refine ⟨Q, P, ?_, D.col 6, ?_, ?_⟩
  · intro hn
    simp [Q, Normalized, shifted, tail, init, cornerDiagram]
  · intro i
    fin_cases i <;>
      simp [Q, P, threeMiddleContext, singletonContext, singletonCore, rightSingletonCore,
        rotate, shifted, positiveBorder, tail, init, cornerDiagram, topMargin, bottomMargin,
        Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.snoc,
        Fin.castPred, Fin.castLT] <;> ring
  · intro i
    fin_cases i <;>
      simp [Q, P, threeMiddleContext, singletonContext, singletonCore, rightSingletonCore,
        rotate, shifted, positiveBorder, tail, init, cornerDiagram, topMargin, bottomMargin,
        Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.snoc,
        Fin.castPred, Fin.castLT] <;> ring

/-- Three recovered connected leaves give both genuine ordered beta cuts.
The decomposition tree may associate its cuts either way. -/
theorem component_list_three_cuts (D : BetaDiagram n)
    (C : ComponentDecomposition D) (hlen : C.components.length = 3) :
    ∃ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
      (he : a+b+c = n),
      (D.reindexOrder he).row ⟨a, by omega⟩ <
        (D.reindexOrder he).col ⟨a-1, by omega⟩ ∧
      (D.reindexOrder he).row ⟨a+b, by omega⟩ <
        (D.reindexOrder he).col ⟨a+b-1, by omega⟩ ∧
      C.components.map Sigma.fst = [a,b,c] := by
  cases C with
  | empty D =>
    simp only [ComponentDecomposition.components, List.length_nil] at hlen
    omega
  | connected D hD =>
    simp only [ComponentDecomposition.components, List.length_cons,
      List.length_nil] at hlen
    omega
  | @cut n a b D ha hb he hcut L R =>
    have hL := component_list_length_pos _ L ha
    have hR := component_list_length_pos _ R hb
    simp only [ComponentDecomposition.components, List.length_append] at hlen
    by_cases hLs : L.components.length = 1
    · obtain ⟨_, hLe⟩ := component_list_singleton _ L hLs
      have hRs : R.components.length = 2 := by omega
      obtain ⟨b₁,b₂,hb₁,hb₂,heR,hcutR,_,_,hRe⟩ :=
        component_list_two_cut _ R hRs
      have he₃ : a+b₁+b₂ = n := by omega
      refine ⟨a,b₁,b₂,ha,hb₁,hb₂,he₃,?_,?_,?_⟩
      · change D.row ⟨a,by omega⟩ < D.col ⟨a-1,by omega⟩
        change D.row ⟨a,by omega⟩ < D.col ⟨a-1,by omega⟩ at hcut
        exact hcut
      · change D.row ⟨a+b₁,by omega⟩ < D.col ⟨a+b₁-1,by omega⟩
        change D.row ⟨a+b₁,by omega⟩ < D.col ⟨a+(b₁-1),by omega⟩ at hcutR
        have hi : a+(b₁-1) = a+b₁-1 := by omega
        simpa only [hi] using hcutR
      · simp only [ComponentDecomposition.components,hLe,hRe,List.map_append,
          List.map_cons,List.map_nil,List.singleton_append]
    · have hLs' : L.components.length = 2 := by omega
      have hRs : R.components.length = 1 := by omega
      obtain ⟨a₁,a₂,ha₁,ha₂,heL,hcutL,_,_,hLe⟩ :=
        component_list_two_cut _ L hLs'
      obtain ⟨_,hRe⟩ := component_list_singleton _ R hRs
      have he₃ : a₁+a₂+b = n := by omega
      refine ⟨a₁,a₂,b,ha₁,ha₂,hb,he₃,?_,?_,?_⟩
      · change D.row ⟨a₁,by omega⟩ < D.col ⟨a₁-1,by omega⟩
        change D.row ⟨a₁,by omega⟩ < D.col ⟨a₁-1,by omega⟩ at hcutL
        exact hcutL
      · change D.row ⟨a₁+a₂,by omega⟩ < D.col ⟨a₁+a₂-1,by omega⟩
        change D.row ⟨a,by omega⟩ < D.col ⟨a-1,by omega⟩ at hcut
        simpa only [heL] using hcut
      · simp only [ComponentDecomposition.components,hLe,hRe,List.map_append,
          List.map_cons,List.map_nil,List.cons_append,List.nil_append]

/-- Factor matching forces all three possible ordered cut pairs, with no assumed mate pattern. -/
theorem three_cuts_of_factor_inventory (D : BetaDiagram 6)
    (C : ComponentDecomposition D) (Q : BetaDiagram 4)
    (ell m : ℤ) (hℓ : 0 < ell) (hm : 0 < m)
    (hrel : Multiset.Rel
      (fun X Y : Σ a : ℕ, BetaDiagram a => X.2.schur = Y.2.schur)
      (([⟨1,singletonDiagram ell hℓ⟩,⟨1,singletonDiagram m hm⟩,⟨4,Q⟩] :
        List (Σ a : ℕ, BetaDiagram a)) : Multiset (Σ a : ℕ, BetaDiagram a))
      (C.components : Multiset _)) :
    (D.row 1 < D.col 0 ∧ D.row 2 < D.col 1) ∨
    (D.row 1 < D.col 0 ∧ D.row 5 < D.col 4) ∨
    (D.row 4 < D.col 3 ∧ D.row 5 < D.col 4) := by
  have hcard := Multiset.card_eq_card_of_rel hrel
  have hlen : C.components.length = 3 := by simpa using hcard.symm
  obtain ⟨a,b,c,ha,hb,hc,he,hcut₁,hcut₂,horders⟩ :=
    D.component_list_three_cuts C hlen
  have hcounts : Multiset.Rel (fun X Y : Σ a : ℕ, BetaDiagram a => X.1 = Y.1)
      (([⟨1,singletonDiagram ell hℓ⟩,⟨1,singletonDiagram m hm⟩,⟨4,Q⟩] :
        List (Σ a : ℕ, BetaDiagram a)) : Multiset (Σ a : ℕ, BetaDiagram a))
      (C.components : Multiset _) := by
    apply hrel.mono
    intro X _ Y _ hXY
    exact X.2.row_count_of_schur_eq Y.2 hXY
  have hmap :
      (([⟨1,singletonDiagram ell hℓ⟩,⟨1,singletonDiagram m hm⟩,⟨4,Q⟩] :
        List (Σ a : ℕ, BetaDiagram a)) : Multiset (Σ a : ℕ, BetaDiagram a)).map Sigma.fst =
      (C.components : Multiset (Σ a : ℕ, BetaDiagram a)).map Sigma.fst :=
    Multiset.rel_eq.mp (Multiset.rel_map.mpr hcounts)
  have horders' : ([1,1,4] : Multiset ℕ) = ([a,b,c] : Multiset ℕ) := by
    simpa only [Multiset.map_coe, List.map_cons, List.map_nil, horders] using hmap
  have ha' : a = 1 ∨ a = 4 := by
    have hmem : a ∈ ([1,1,4] : Multiset ℕ) := by rw [horders']; simp
    simpa using hmem
  have hb' : b = 1 ∨ b = 4 := by
    have hmem : b ∈ ([1,1,4] : Multiset ℕ) := by rw [horders']; simp
    simpa using hmem
  have hc' : c = 1 ∨ c = 4 := by
    have hmem : c ∈ ([1,1,4] : Multiset ℕ) := by rw [horders']; simp
    simpa using hmem
  rcases ha' with rfl | rfl
  · rcases hb' with rfl | rfl
    · have hc4 : c = 4 := by omega
      subst c
      exact Or.inl ⟨by simpa [reindexOrder] using hcut₁,
        by simpa [reindexOrder] using hcut₂⟩
    · have hc1 : c = 1 := by omega
      subst c
      exact Or.inr (Or.inl ⟨by simpa [reindexOrder] using hcut₁,
        by simpa [reindexOrder] using hcut₂⟩)
  · have hb1 : b = 1 := by omega
    have hc1 : c = 1 := by omega
    subst b
    subst c
    exact Or.inr (Or.inr ⟨by simpa [reindexOrder] using hcut₁,
      by simpa [reindexOrder] using hcut₂⟩)

/-- Every arbitrary connected Schur-equal mate is genuinely an end or middle parent,
up to a whole-parent half-turn.  No mate negative partition or component order is assumed. -/
theorem three_context_mate_forms (Q : BetaDiagram 4) (hC : Q.Connected)
    (hZ : Q.ZeroFree) (P : ThreeComponentParameters) (middle : Bool)
    {k : ℕ} (E : BetaDiagram k) (hE : E.Connected)
    (he : (if middle then Q.threeMiddleContext P else Q.threeEndContext P).schur = E.schur) :
    ∃ hrow : k = 7,
      let F := E.castOrder hrow
      ∃ (R : BetaDiagram 4) (T : ThreeComponentParameters), R.Normalized ∧
        (F.TranslationEquivalent (R.threeEndContext T) ∨
          F.TranslationEquivalent (R.threeMiddleContext T) ∨
          F.rotate.TranslationEquivalent (R.threeEndContext T)) := by
  obtain ⟨hrow,hP,hZF,hK⟩ :=
    Q.three_context_mate_components hC hZ P middle E hE he
  refine ⟨hrow, ?_⟩
  let F := E.castOrder hrow
  let C := (F.cornerDiagram hP).componentDecomposition
  have hrel := hK C
  rcases (F.cornerDiagram hP).three_cuts_of_factor_inventory C Q
      P.ell P.m P.ell_pos P.m_pos hrel with hcuts | hcuts | hcuts
  · have hcut₁ : F.row 2 < F.col 0 := hcuts.1
    have hcut₂ : F.row 3 < F.col 1 := hcuts.2
    obtain ⟨R,T,hRN,hRT⟩ := F.three_end_parent_of_cuts hP hcut₁ hcut₂
    exact ⟨R,T,hRN,Or.inl hRT⟩
  · have hcut₁ : F.row 2 < F.col 0 := hcuts.1
    have hcut₂ : F.row 6 < F.col 4 := hcuts.2
    obtain ⟨R,T,hRN,hRT⟩ := F.three_middle_parent_of_cuts hP hcut₁ hcut₂
    exact ⟨R,T,hRN,Or.inr (Or.inl hRT)⟩
  · have hcut₁ : F.rotate.row 2 < F.rotate.col 0 := by
      have h : F.row 6 < F.col 4 := hcuts.2
      change -F.col 4 < -F.row 6
      omega
    have hcut₂ : F.rotate.row 3 < F.rotate.col 1 := by
      have h : F.row 5 < F.col 3 := hcuts.1
      change -F.col 3 < -F.row 5
      omega
    obtain ⟨R,T,hRN,hRT⟩ :=
      F.rotate.three_end_parent_of_cuts (F.rotate_positiveCorner hP) hcut₁ hcut₂
    exact ⟨R,T,hRN,Or.inr (Or.inr hRT)⟩

/-- Equality of positive coordinate pairs recovers their unordered lengths, including repetitions. -/
theorem singleton_pair_recovery (ell m a b : ℤ)
    (hℓ : 0 < ell) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (he : complete ell * complete m = complete a * complete b) :
    (ell = a ∧ m = b) ∨ (ell = b ∧ m = a) := by
  have hdvd : complete ell ∣ complete a * complete b := by
    rw [← he]
    exact dvd_mul_right _ _
  rcases (complete_prime ell hℓ).dvd_mul.mp hdvd with h | h
  · have hℓa := (complete_dvd_complete_iff ell a hℓ ha).mp h
    subst a
    have hmB : complete m = complete b :=
      mul_left_cancel₀ ((complete_ne_zero_iff _).mpr hℓ.le) he
    exact Or.inl ⟨rfl,complete_injective_nonnegative hm.le hb.le hmB⟩
  · have hℓb := (complete_dvd_complete_iff ell b hℓ hb).mp h
    subst b
    have hmA : complete m = complete a := by
      apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr hℓ.le)
      simpa only [mul_comm (complete a) (complete ell)] using he
    exact Or.inr ⟨rfl,complete_injective_nonnegative hm.le ha.le hmA⟩

/-- A three-factor product identifies the four-row core even if the proposed mate core
was not assumed connected.  Its connectedness is produced by the factor inventory. -/
theorem three_product_core_recovery (Q R : BetaDiagram 4) (hQ : Q.Connected)
    (ell m a b : ℤ) (hℓ : 0 < ell) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (he : complete ell * complete m * Q.schur = complete a * complete b * R.schur) :
    R.Connected ∧ Q.schur = R.schur ∧
      ((ell = a ∧ m = b) ∨ (ell = b ∧ m = a)) := by
  let C := R.componentDecomposition
  let xs : List (Σ k : ℕ, BetaDiagram k) :=
    [⟨1,singletonDiagram ell hℓ⟩,⟨1,singletonDiagram m hm⟩,⟨4,Q⟩]
  let ys : List (Σ k : ℕ, BetaDiagram k) :=
    [⟨1,singletonDiagram a ha⟩,⟨1,singletonDiagram b hb⟩] ++ C.components
  have hxs : ∀ X ∈ xs, X.2.Connected := by
    intro X hX
    simp [xs] at hX
    rcases hX with rfl | rfl | rfl
    · exact singletonDiagram_connected ell hℓ
    · exact singletonDiagram_connected m hm
    · exact hQ
  have hys : ∀ Y ∈ ys, Y.2.Connected := by
    intro Y hY
    change Y ∈ [⟨1,singletonDiagram a ha⟩,⟨1,singletonDiagram b hb⟩] ++ C.components at hY
    rcases List.mem_append.mp hY with hY | hY
    · rcases List.mem_cons.mp hY with he | hY
      · rw [he]
        exact singletonDiagram_connected a ha
      · have he := List.mem_singleton.mp hY
        rw [he]
        exact singletonDiagram_connected b hb
    · exact C.components_connected Y hY
  have hp : (xs.map (fun X => X.2.schur)).prod =
      (ys.map (fun Y => Y.2.schur)).prod := by
    simp only [xs,ys,List.map_append,List.prod_append,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,singletonDiagram_schur,mul_one]
    rw [← C.component_schur_product]
    simpa only [mul_assoc] using he
  have hrel := product_component_matching xs ys hxs hys hp
  have hcard := Multiset.card_eq_card_of_rel hrel
  have hlen : C.components.length = 1 := by
    simp only [xs,ys,Multiset.coe_card,List.length_cons,List.length_nil,
      List.length_append] at hcard
    omega
  have hR : R.Connected := (R.component_list_singleton C hlen).1
  have hprime := UniqueFactorizationMonoid.irreducible_iff_prime.mp (Q.schur_irreducible hQ)
  have hnot : ∀ (s : ℤ) (hs : 0 < s), ¬ Q.schur ∣ complete s := by
    intro s hs h
    have heq := Q.schur_eq_of_connected_dvd (singletonDiagram s hs) hQ
      (singletonDiagram_connected s hs) (by simpa only [singletonDiagram_schur] using h)
    have hn := Q.row_count_of_schur_eq (singletonDiagram s hs) heq
    omega
  have hdiv : Q.schur ∣ complete a * complete b * R.schur := by
    rw [← he]
    exact dvd_mul_left _ _
  have hQR : Q.schur ∣ R.schur := by
    rcases hprime.dvd_mul.mp hdiv with h | h
    · rcases hprime.dvd_mul.mp h with h | h
      · exact False.elim (hnot a ha h)
      · exact False.elim (hnot b hb h)
    · exact h
  have hfun := Q.schur_eq_of_connected_dvd R hQ hR hQR
  have hpair : complete ell * complete m = complete a * complete b := by
    apply mul_right_cancel₀ Q.schur_ne_zero
    simpa only [← hfun] using he
  exact ⟨hR,hfun,singleton_pair_recovery ell m a b hℓ hm ha hb hpair⟩

/-- Full Schur equality of actual placements recovers the connected core function and
both singleton lengths before any margin or orientation comparison is made. -/
theorem three_context_core_recovery (Q R : BetaDiagram 4) (hQ : Q.Connected)
    (P T : ThreeComponentParameters) (middle₁ middle₂ : Bool)
    (he : (if middle₁ then Q.threeMiddleContext P else Q.threeEndContext P).schur =
      (if middle₂ then R.threeMiddleContext T else R.threeEndContext T).schur) :
    R.Connected ∧ Q.schur = R.schur ∧
      ((P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell)) := by
  let A := if middle₁ then Q.threeMiddleContext P else Q.threeEndContext P
  let B := if middle₂ then R.threeMiddleContext T else R.threeEndContext T
  have hA : A.Connected := by
    cases middle₁ <;> simp only [A,Bool.false_eq_true,if_false,if_true]
    · exact Q.threeEndContext_connected P
    · exact Q.threeMiddleContext_connected P
  have hB : B.Connected := by
    cases middle₂ <;> simp only [B,Bool.false_eq_true,if_false,if_true]
    · exact R.threeEndContext_connected T
    · exact R.threeMiddleContext_connected T
  have hcorner := A.cornerPolynomial_eq_of_schur_eq B hA hB he
  have hAc : A.cornerPolynomial = complete P.ell * complete P.m * Q.schur := by
    cases middle₁ <;> simp [A]
  have hBc : B.cornerPolynomial = complete T.ell * complete T.m * R.schur := by
    cases middle₂ <;> simp [B]
  rw [hAc,hBc] at hcorner
  exact three_product_core_recovery Q R hQ P.ell P.m T.ell T.m
    P.ell_pos P.m_pos T.ell_pos T.m_pos hcorner

/-- Complete arbitrary-mate geometric recovery: actual ordered placement lists,
the connected four-row core function, and the singleton order up to exchange. -/
theorem three_context_arbitrary_mate_recovery (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (P : ThreeComponentParameters) (middle : Bool)
    {k : ℕ} (E : BetaDiagram k) (hE : E.Connected)
    (he : (if middle then Q.threeMiddleContext P else Q.threeEndContext P).schur = E.schur) :
    ∃ hrow : k = 7,
      let F := E.castOrder hrow
      ∃ (R : BetaDiagram 4) (T : ThreeComponentParameters),
        R.Normalized ∧ R.Connected ∧ Q.schur = R.schur ∧
        ((P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell)) ∧
        (F.TranslationEquivalent (R.threeEndContext T) ∨
          F.TranslationEquivalent (R.threeMiddleContext T) ∨
          F.rotate.TranslationEquivalent (R.threeEndContext T)) := by
  obtain ⟨hrow,R,T,hRN,hRT⟩ :=
    Q.three_context_mate_forms hC hZ P middle E hE he
  refine ⟨hrow,R,T,hRN,?_⟩
  let F := E.castOrder hrow
  have hEq : (if middle then Q.threeMiddleContext P else Q.threeEndContext P).schur =
      F.schur := by simpa only [F,castOrder_schur] using he
  rcases hRT with hRT | hRT | hRT
  · have hpoly := hEq.trans hRT.schur_eq
    have hrec := three_context_core_recovery Q R hC P T middle false hpoly
    exact ⟨hrec.1,hrec.2.1,hrec.2.2,Or.inl hRT⟩
  · have hpoly := hEq.trans hRT.schur_eq
    have hrec := three_context_core_recovery Q R hC P T middle true hpoly
    exact ⟨hrec.1,hrec.2.1,hrec.2.2,Or.inr (Or.inl hRT)⟩
  · have hpoly := hEq.trans (F.rotate_schur.symm.trans hRT.schur_eq)
    have hrec := three_context_core_recovery Q R hC P T middle false hpoly
    exact ⟨hrec.1,hrec.2.1,hrec.2.2,Or.inr (Or.inr hRT)⟩


/-- The six end-placement parameters are actual beta differences. -/
theorem threeEndContext_parameter_readings (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    (Q.threeEndContext P).row 1-(Q.threeEndContext P).col 0 = P.ell ∧
    (Q.threeEndContext P).row 2-(Q.threeEndContext P).col 1 = P.m ∧
    (Q.threeEndContext P).col 0-(Q.threeEndContext P).row 2 = P.g₁ ∧
    (Q.threeEndContext P).col 1-(Q.threeEndContext P).row 3 = P.g₂ ∧
    (Q.threeEndContext P).topMargin = P.u ∧
    (Q.threeEndContext P).bottomMargin = P.v := by
  rcases Q.threeEndContext_margins P with ⟨hu,hv⟩
  refine ⟨?_,?_,?_,?_,hu,hv⟩ <;>
    simp [threeEndContext,singletonContext,singletonCore,positiveBorder,shifted,
      Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.snoc,
      Fin.castPred,Fin.castLT] <;> ring

/-- The six middle-placement parameters are likewise read without a core-pattern premise. -/
theorem threeMiddleContext_parameter_readings (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    (Q.threeMiddleContext P).row 1-(Q.threeMiddleContext P).col 0 = P.ell ∧
    (Q.threeMiddleContext P).row 6-(Q.threeMiddleContext P).col 5 = P.m ∧
    (Q.threeMiddleContext P).col 0-(Q.threeMiddleContext P).row 2 = P.g₁ ∧
    (Q.threeMiddleContext P).col 4-(Q.threeMiddleContext P).row 6 = P.g₂ ∧
    (Q.threeMiddleContext P).topMargin = P.u ∧
    (Q.threeMiddleContext P).bottomMargin = P.v := by
  rcases Q.threeMiddleContext_margins P with ⟨hu,hv⟩
  refine ⟨?_,?_,?_,?_,hu,hv⟩ <;>
    simp [threeMiddleContext,singletonContext,singletonCore,positiveBorder,
      rightSingletonCore,rotate,shifted,Fin.cons,Fin.cases,Fin.induction,
      Fin.induction.go,Fin.snoc,Fin.castPred,Fin.castLT] <;> ring

theorem threeComponentParameters_eq_of_fields (P T : ThreeComponentParameters)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hg₁ : P.g₁ = T.g₁)
    (hg₂ : P.g₂ = T.g₂) (hu : P.u = T.u) (hv : P.v = T.v) : P = T := by
  cases P
  cases T
  cases hℓ
  cases hm
  cases hg₁
  cases hg₂
  cases hu
  cases hv
  rfl

/-- Translation of actual end lists recovers every parameter, not just the core and singleton lengths. -/
theorem threeEndContext_parameters_of_translation (Q R : BetaDiagram 4)
    (P T : ThreeComponentParameters)
    (he : (Q.threeEndContext P).TranslationEquivalent (R.threeEndContext T)) : P = T := by
  obtain ⟨c,hr,hco⟩ := he
  rcases Q.threeEndContext_parameter_readings P with ⟨hℓ,hm,hg₁,hg₂,hu,hv⟩
  rcases R.threeEndContext_parameter_readings T with ⟨tℓ,tm,tg₁,tg₂,tu,tv⟩
  apply threeComponentParameters_eq_of_fields
  · rw [← hℓ,← tℓ,hr 1,hco 0]
    ring
  · rw [← hm,← tm,hr 2,hco 1]
    ring
  · rw [← hg₁,← tg₁,hco 0,hr 2]
    ring
  · rw [← hg₂,← tg₂,hco 1,hr 3]
    ring
  · rw [← hu,← tu]
    unfold topMargin
    rw [hr 0,hr (0 : Fin 6).succ]
    ring
  · rw [← hv,← tv]
    unfold bottomMargin
    rw [hco (Fin.last 5).castSucc,hco (Fin.last 6)]
    ring

theorem threeMiddleContext_parameters_of_translation (Q R : BetaDiagram 4)
    (P T : ThreeComponentParameters)
    (he : (Q.threeMiddleContext P).TranslationEquivalent (R.threeMiddleContext T)) : P = T := by
  obtain ⟨c,hr,hco⟩ := he
  rcases Q.threeMiddleContext_parameter_readings P with ⟨hℓ,hm,hg₁,hg₂,hu,hv⟩
  rcases R.threeMiddleContext_parameter_readings T with ⟨tℓ,tm,tg₁,tg₂,tu,tv⟩
  apply threeComponentParameters_eq_of_fields
  · rw [← hℓ,← tℓ,hr 1,hco 0]
    ring
  · rw [← hm,← tm,hr 6,hco 5]
    ring
  · rw [← hg₁,← tg₁,hco 0,hr 2]
    ring
  · rw [← hg₂,← tg₂,hco 4,hr 6]
    ring
  · rw [← hu,← tu]
    unfold topMargin
    rw [hr 0,hr (0 : Fin 6).succ]
    ring
  · rw [← hv,← tv]
    unfold bottomMargin
    rw [hco (Fin.last 5).castSucc,hco (Fin.last 6)]
    ring

/-- Source rigidity transports through the actual common beta translation. -/
theorem rotationRigid_shifted (D : BetaDiagram n) (hD : D.RotationRigid) (c : ℤ) :
    (D.shifted c).RotationRigid := by
  rw [rotationRigid_iff_same_order] at hD ⊢
  intro E hE he
  have hp : E.schur = D.schur := by simpa only [shifted_schur] using he
  rcases hD E hE hp with ⟨t,hr,hco⟩ | ⟨t,hr,hco⟩
  · refine Or.inl ⟨t+c,?_,?_⟩
    · intro i
      change D.row i+c = E.row i+(t+c)
      rw [hr i]
      ring
    · intro i
      change D.col i+c = E.col i+(t+c)
      rw [hco i]
      ring
  · refine Or.inr ⟨t+c,?_,?_⟩
    · intro i
      change D.row i+c = t+c-E.col i.rev
      rw [hr i]
      ring
    · intro i
      change D.col i+c = t+c-E.row i.rev
      rw [hco i]
      ring

/-- Source rigidity transports through the literal half-turn of both ordered lists. -/
theorem rotationRigid_rotate (D : BetaDiagram n) (hD : D.RotationRigid) :
    D.rotate.RotationRigid := by
  rw [rotationRigid_iff_same_order] at hD ⊢
  intro E hE he
  have hp : E.schur = D.schur := by simpa only [rotate_schur] using he
  rcases hD E hE hp with ⟨t,hr,hco⟩ | ⟨t,hr,hco⟩
  · refine Or.inr ⟨-t,?_,?_⟩
    · intro i
      change -D.col i.rev = -t-E.col i.rev
      rw [hco i.rev]
      ring
    · intro i
      change -D.row i.rev = -t-E.row i.rev
      rw [hr i.rev]
      ring
  · refine Or.inl ⟨-t,?_,?_⟩
    · intro i
      have hh := hco i.rev
      simp only [Fin.rev_rev] at hh
      change -D.col i.rev = E.row i+(-t)
      rw [hh]
      ring
    · intro i
      have hh := hr i.rev
      simp only [Fin.rev_rev] at hh
      change -D.row i.rev = E.col i+(-t)
      rw [hh]
      ring

/-- The U construction commutes with common beta translation. -/
theorem shifted_threeComponentU (Q : BetaDiagram (n + 1)) (c ell x u : ℤ)
    (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    (Q.shifted c).threeComponentU ell x u hℓ hx hu =
      (Q.threeComponentU ell x u hℓ hx hu).shifted c := by
  apply eq_of_lists
  · funext i
    cases i using Fin.cases
    · simp [threeComponentU,shifted,extendTop] <;> ring
    · simp only [threeComponentU,shifted,Fin.cons_succ,extendTop]
      split_ifs <;> ring
  · funext i
    cases i using Fin.cases <;> simp [threeComponentU,shifted] <;> ring

@[simp] theorem shifted_largestLabel (D : BetaDiagram (n + 1)) (c : ℤ) :
    (D.shifted c).largestLabel = D.largestLabel := by
  simp only [largestLabel,shifted]
  ring

@[simp] theorem shifted_topMargin (D : BetaDiagram (n + 2)) (c : ℤ) :
    (D.shifted c).topMargin = D.topMargin := by
  simp only [topMargin,shifted]
  ring

@[simp] theorem shifted_bottomMargin (D : BetaDiagram (n + 2)) (c : ℤ) :
    (D.shifted c).bottomMargin = D.bottomMargin := by
  simp only [bottomMargin,shifted]
  ring

@[simp] theorem shifted_secondLabel (D : BetaDiagram (n + 2)) (c : ℤ) :
    (D.shifted c).secondLabel = D.secondLabel := by
  rw [secondLabel,shifted_largestLabel,shifted_topMargin,shifted_bottomMargin]
  rfl

@[simp] theorem shifted_borderLargestGenerator (D : BetaDiagram (n + 1)) (c : ℤ) :
    (D.shifted c).borderLargestGenerator = D.borderLargestGenerator := by
  apply Subtype.ext
  simp [borderLargestGenerator]

@[simp] theorem shifted_borderSecondGenerator (D : BetaDiagram (n + 2)) (c : ℤ) :
    (D.shifted c).borderSecondGenerator = D.borderSecondGenerator := by
  apply Subtype.ext
  simp [borderSecondGenerator]

@[simp] theorem shifted_singletonCore (Q : BetaDiagram (n + 1)) (c s g : ℤ)
    (hs : 0 < s) (hg : 0 < g) :
    (Q.shifted c).singletonCore s g hs hg = (Q.singletonCore s g hs hg).shifted c := by
  apply eq_of_lists <;> funext i <;> cases i using Fin.cases <;>
    simp [singletonCore,shifted] <;> ring

@[simp] theorem shifted_positiveBorder (Q : BetaDiagram (n + 1)) (c u v : ℤ)
    (hu : 0 < u) (hv : 0 < v) :
    (Q.shifted c).positiveBorder u v hu hv = (Q.positiveBorder u v hu hv).shifted c := by
  apply eq_of_lists
  · funext i
    cases i using Fin.cases <;> simp [positiveBorder,shifted] <;> ring
  · funext j
    cases j using Fin.lastCases <;> simp [positiveBorder,shifted] <;> ring

theorem shifted_shifted (Q : BetaDiagram n) (a b : ℤ) :
    (Q.shifted a).shifted b = Q.shifted (a+b) := by
  apply eq_of_lists <;> funext i <;> simp [shifted] <;> ring

theorem shifted_threeEndContext (Q : BetaDiagram (n + 1)) (c : ℤ)
    (P : ThreeComponentParameters) :
    (Q.shifted c).threeEndContext P = (Q.threeEndContext P).shifted c := by
  unfold threeEndContext singletonContext
  rw [shifted_singletonCore,shifted_singletonCore,shifted_positiveBorder,
    shifted_shifted,shifted_shifted,add_comm c P.v]

@[simp] theorem shifted_rightSingletonCore (Q : BetaDiagram (n + 1))
    (c m g : ℤ) (hm : 0 < m) (hg : 0 < g) :
    (Q.shifted c).rightSingletonCore m g hm hg = Q.rightSingletonCore m g hm hg := by
  apply eq_of_lists
  · funext i
    cases i using Fin.lastCases with
    | last => simp
    | cast i => simp [rightSingletonCore_row_core,shifted]; ring
  · funext i
    cases i using Fin.lastCases with
    | last => simp
    | cast i => simp [rightSingletonCore_col_core,shifted]; ring

@[simp] theorem shifted_threeMiddleContext (Q : BetaDiagram (n + 1)) (c : ℤ)
    (P : ThreeComponentParameters) :
    (Q.shifted c).threeMiddleContext P = Q.threeMiddleContext P := by
  simp only [threeMiddleContext,shifted_rightSingletonCore]

theorem threeEndContext_of_core_translation (Q R : BetaDiagram (n + 1))
    (h : Q.TranslationEquivalent R) (P : ThreeComponentParameters) :
    (Q.threeEndContext P).TranslationEquivalent (R.threeEndContext P) := by
  obtain ⟨c,hr,hco⟩ := h
  have he : Q = R.shifted c := eq_of_lists Q (R.shifted c) (funext hr) (funext hco)
  rw [he,shifted_threeEndContext]
  exact ⟨c,fun _ => rfl,fun _ => rfl⟩

theorem threeMiddleContext_of_core_translation (Q R : BetaDiagram (n + 1))
    (h : Q.TranslationEquivalent R) (P : ThreeComponentParameters) :
    Q.threeMiddleContext P = R.threeMiddleContext P := by
  obtain ⟨c,hr,hco⟩ := h
  have he : Q = R.shifted c := eq_of_lists Q (R.shifted c) (funext hr) (funext hco)
  rw [he,shifted_threeMiddleContext]

@[simp] theorem threeComponentZ_row_core (Q : BetaDiagram (n + 1)) (m y v : ℤ)
    (hm : 0 < m) (hy : m < y) (hv : 0 < v) (i : Fin (n + 1)) :
    (Q.threeComponentZ m y v hm hy hv).row i.castSucc =
      Q.row i+y+v-Q.col (Fin.last n) := by
  simp [threeComponentZ,shifted,rotate,threeComponentU,Fin.rev_castSucc,Fin.rev_succ]
  ring

@[simp] theorem threeComponentZ_row_last (Q : BetaDiagram (n + 1)) (m y v : ℤ)
    (hm : 0 < m) (hy : m < y) (hv : 0 < v) :
    (Q.threeComponentZ m y v hm hy hv).row (Fin.last (n+1)) = m+v := by
  simp [threeComponentZ,shifted,rotate,threeComponentU,Fin.rev_last,Fin.rev_zero]
  ring

@[simp] theorem threeComponentZ_col_core (Q : BetaDiagram (n + 2)) (m y v : ℤ)
    (hm : 0 < m) (hy : m < y) (hv : 0 < v) (i : Fin (n + 1)) :
    (Q.threeComponentZ m y v hm hy hv).col i.castSucc.castSucc =
      Q.col i.castSucc+y+v-Q.col (Fin.last (n+1)) := by
  simp [threeComponentZ,shifted,rotate,threeComponentU,extendTop,Fin.rev_castSucc,
    Fin.rev_succ,Fin.succ_ne_zero]
  ring

@[simp] theorem threeComponentZ_col_penultimate (Q : BetaDiagram (n + 1)) (m y v : ℤ)
    (hm : 0 < m) (hy : m < y) (hv : 0 < v) :
    (Q.threeComponentZ m y v hm hy hv).col (Fin.last n).castSucc = v := by
  simp [threeComponentZ,shifted,rotate,threeComponentU,extendTop,
    Fin.rev_castSucc,Fin.rev_last]

@[simp] theorem threeComponentZ_col_last (Q : BetaDiagram (n + 1)) (m y v : ℤ)
    (hm : 0 < m) (hy : m < y) (hv : 0 < v) :
    (Q.threeComponentZ m y v hm hy hv).col (Fin.last (n+1)) = 0 := by
  simp [threeComponentZ,shifted,rotate,threeComponentU,extendTop,Fin.rev_last] <;> ring

/-- Translation of equal-data U intermediates recovers the complete core lists. -/
theorem threeComponentU_translation_core (Q R : BetaDiagram 4)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u)
    (he : (Q.threeComponentU ell x u hℓ hx hu).TranslationEquivalent
      (R.threeComponentU ell x u hℓ hx hu)) : Q.TranslationEquivalent R := by
  obtain ⟨c,hr,hco⟩ := he
  refine ⟨c,?_,?_⟩
  · intro i
    have hh := hr i.succ
    by_cases hi : i = 0
    · subst i
      simp only [threeComponentU,Fin.cons_succ,extendTop,ite_true] at hh
      omega
    · simpa only [threeComponentU,Fin.cons_succ,extendTop,if_neg hi] using hh
  · intro i
    simpa only [threeComponentU,Fin.cons_succ] using hco i.succ

theorem threeComponentU_of_core_translation (Q R : BetaDiagram 4)
    (h : Q.TranslationEquivalent R) (ell x u : ℤ)
    (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    (Q.threeComponentU ell x u hℓ hx hu).TranslationEquivalent
      (R.threeComponentU ell x u hℓ hx hu) := by
  obtain ⟨c,hr,hco⟩ := h
  have he : Q = R.shifted c := eq_of_lists Q (R.shifted c) (funext hr) (funext hco)
  rw [he,shifted_threeComponentU]
  exact ⟨c,fun _ => rfl,fun _ => rfl⟩

@[simp] theorem singletonCore_largestLabel (Q : BetaDiagram (n + 1)) (s g : ℤ)
    (hs : 0 < s) (hg : 0 < g) :
    (Q.singletonCore s g hs hg).largestLabel = Q.largestLabel+s+g := by
  simp only [largestLabel,singletonCore,Fin.cons_zero,Fin.cons_last]
  ring

@[simp] theorem rightSingletonCore_largestLabel (Q : BetaDiagram (n + 1)) (m g : ℤ)
    (hm : 0 < m) (hg : 0 < g) :
    (Q.rightSingletonCore m g hm hg).largestLabel = Q.largestLabel+m+g := by
  have hr := Q.rightSingletonCore_row_core m g hm hg (0 : Fin (n+1))
  simp only [Fin.castSucc_zero] at hr
  unfold largestLabel
  rw [hr,rightSingletonCore_col_last]
  ring

@[simp] theorem threeEndContext_largestLabel (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    (Q.threeEndContext P).largestLabel = Q.largestLabel+P.left+P.right+P.u+P.v := by
  simp only [threeEndContext,singletonContext,shifted_largestLabel,
    positiveBorder_largestLabel,singletonCore_largestLabel]
  unfold ThreeComponentParameters.left ThreeComponentParameters.right
  ring

@[simp] theorem threeMiddleContext_largestLabel (Q : BetaDiagram (n + 1))
    (P : ThreeComponentParameters) :
    (Q.threeMiddleContext P).largestLabel = Q.largestLabel+P.left+P.right+P.u+P.v := by
  simp only [threeMiddleContext,singletonContext,shifted_largestLabel,
    positiveBorder_largestLabel,singletonCore_largestLabel,rightSingletonCore_largestLabel]
  unfold ThreeComponentParameters.left ThreeComponentParameters.right
  ring

end BetaDiagram
end SkewJacobiNegative
