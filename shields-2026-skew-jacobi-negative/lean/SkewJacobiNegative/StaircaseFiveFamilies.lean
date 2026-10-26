/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircasePrimitives
import SkewJacobiNegative.NegativeInvariants
import SkewJacobiNegative.Gluing.RowTransport

/-!
# Actual five-row staircase families

The four parameter families in `eq:staircase-families` and their uniform
identities in `thm:staircase-base` of
`shields-2026-skew-jacobi-negative.tex`.  Gaps are overlaps minus one.
The parameter domains include zero gaps and common row/column betas.
-/

namespace SkewJacobiNegative.StaircaseFiveFamilies

open Gluing

/-- The five-row arithmetic domain, including both endpoint bounds. -/
def Domain (a b c d e r s t u : ℤ) : Prop :=
  0 ≤ r ∧ 0 ≤ s ∧ 0 ≤ t ∧ 0 ≤ u ∧
    r < a ∧ r + s < b ∧ s + t < c ∧ t + u < d ∧ u < e

/-- The sixteen signed interval partitions, with numerical labels collected in
one common coefficient ring. -/
def interval {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d e r s t u : ℤ) : R :=
  h a * h b * h c * h d * h e
  - h (a+b-r) * h r * h c * h d * h e
  - h a * h (b+c-s) * h s * h d * h e
  - h a * h b * h (c+d-t) * h t * h e
  - h a * h b * h c * h (d+e-u) * h u
  + h (a+b+c-r-s) * h r * h s * h d * h e
  + h (a+b-r) * h r * h (c+d-t) * h t * h e
  + h (a+b-r) * h r * h c * h (d+e-u) * h u
  + h a * h (b+c+d-s-t) * h s * h t * h e
  + h a * h (b+c-s) * h s * h (d+e-u) * h u
  + h a * h b * h (c+d+e-t-u) * h t * h u
  - h (a+b+c+d-r-s-t) * h r * h s * h t * h e
  - h (a+b+c-r-s) * h r * h s * h (d+e-u) * h u
  - h (a+b-r) * h r * h (c+d+e-t-u) * h t * h u
  - h a * h (b+c+d+e-s-t-u) * h s * h t * h u
  + h (a+b+c+d+e-r-s-t-u) * h r * h s * h t * h u

/-- The actual upper Hessenberg matrix after its six negative entries vanish. -/
def upperMatrix {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d e r s t u : ℤ) : Matrix (Fin 5) (Fin 5) R :=
  !![h a, h (a+b-r), h (a+b+c-r-s), h (a+b+c+d-r-s-t), h (a+b+c+d+e-r-s-t-u);
     h r, h b, h (b+c-s), h (b+c+d-s-t), h (b+c+d+e-s-t-u);
     0, h s, h c, h (c+d-t), h (c+d+e-t-u);
     0, 0, h t, h d, h (d+e-u);
     0, 0, 0, h u, h e]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The finite Laplace expansion normalizes all five-row determinant summands.
/-- Five-row Laplace expansion, without independence or separation assumptions. -/
theorem det_upperMatrix {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d e r s t u : ℤ) :
    (upperMatrix h a b c d e r s t u).det = interval h a b c d e r s t u := by
  norm_num [upperMatrix, interval, Matrix.det_succ_row_zero, Matrix.det_unique,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Arithmetic identification with the genuine beta-index matrix. -/
theorem profile_matrix (P : Profile 4) (hP : P.Hessenberg) :
    (Matrix.of fun i j : Fin 5 => hh (P.xi i - P.zeta j)) =
      upperMatrix hh (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
        (P.g 0) (P.g 1) (P.g 2) (P.g 3) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.of_apply]
  all_goals simp [upperMatrix]
  all_goals first
    | exact hh_of_neg (hP _ _ (by decide))
    | (apply congrArg hh; simp [Profile.xi, Profile.zeta, Fin.sum_univ_succ] <;> ring)

/-- The full determinant expansion also applies to profiles with unit entries. -/
theorem schur_interval (P : Profile 4) (hP : P.Hessenberg) :
    P.schur = interval hh (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      (P.g 0) (P.g 1) (P.g 2) (P.g 3) := by
  rw [Profile.schur, profile_matrix P hP, det_upperMatrix]

/-- Integral words are realized as a normalized connected profile. -/
def profile (a b c d e r s t u : ℤ) (h : Domain a b c d e r s t u) : Profile 4 where
  r i := (![a,b,c,d,e] i).toNat
  g j := (![r,s,t,u] j).toNat
  r_pos := by
    intro i
    rcases h with ⟨hr, hs, ht, hu, ha, hb, hc, hd, he⟩
    fin_cases i <;> simp <;> omega
  g_lt_castSucc := by
    intro j
    rcases h with ⟨hr, hs, ht, hu, ha, hb, hc, hd, he⟩
    fin_cases j <;> simp <;> omega
  g_lt_succ := by
    intro j
    rcases h with ⟨hr, hs, ht, hu, ha, hb, hc, hd, he⟩
    fin_cases j <;> simp <;> omega

@[simp] theorem profile_row (a b c d e r s t u : ℤ)
    (h : Domain a b c d e r s t u) (i : Fin 5) :
    ((profile a b c d e r s t u h).r i : ℤ) = ![a,b,c,d,e] i := by
  rcases h with ⟨hr, hs, ht, hu, ha, hb, hc, hd, he⟩
  fin_cases i <;> simp [profile] <;> omega

@[simp] theorem profile_gap (a b c d e r s t u : ℤ)
    (h : Domain a b c d e r s t u) (i : Fin 4) :
    ((profile a b c d e r s t u h).g i : ℤ) = ![r,s,t,u] i := by
  rcases h with ⟨hr, hs, ht, hu, ha, hb, hc, hd, he⟩
  fin_cases i <;> simp [profile] <;> omega

theorem profile_thick (a b c d e r s t u : ℤ)
    (h : Domain a b c d e r s t u) :
    Staircase.Thick (profile a b c d e r s t u h) := by
  intro j k hjk
  rcases h with ⟨hr, hs, ht, hu, ha, hb, hc, hd, he⟩
  fin_cases j <;> fin_cases k <;> norm_num at hjk
  all_goals (simp [profile]; omega)

/-- Every such five-row profile has the full six-site staircase mask. -/
theorem profile_staircase (a b c d e r s t u : ℤ)
    (h : Domain a b c d e r s t u) :
    ∀ i j : Fin 5,
      (profile a b c d e r s t u h).toBetaDiagram.row i <
        (profile a b c d e r s t u h).toBetaDiagram.col j ↔ j.val+2 ≤ i.val := by
  intro i j
  have hp := (profile_thick a b c d e r s t u h).hessenberg
  by_cases hij : j.val + 1 < i.val
  · have := hp i j hij
    change (profile a b c d e r s t u h).xi i <
      (profile a b c d e r s t u h).zeta j ↔ _
    omega
  · have hab := (profile a b c d e r s t u h).toBetaDiagram_connected
    have hnot : ¬ (profile a b c d e r s t u h).toBetaDiagram.row i <
        (profile a b c d e r s t u h).toBetaDiagram.col j := by
      intro hn
      have := BetaDiagram.negative_lt_predecessor _ hab hn
      omega
    exact iff_of_false hnot (by omega)

/-- Exact full Schur expansion for the integral-word constructor. -/
theorem profile_schur (a b c d e r s t u : ℤ)
    (h : Domain a b c d e r s t u) :
    (profile a b c d e r s t u h).toBetaDiagram.schur =
      interval hh a b c d e r s t u := by
  rw [Profile.toBetaDiagram_schur,
    schur_interval _ (profile_thick a b c d e r s t u h).hessenberg]
  simp [profile_row, profile_gap]

/-- Standing integer parameters for M1 and M2. -/
structure CommutationParameters where
  a : ℤ
  b : ℤ
  t : ℤ
  d : ℤ
  t_nonneg : 0 ≤ t
  d_nonneg : 0 ≤ d
  a_gt : t + d < a
  b_gt : t + d < b
  a_ne_b : a ≠ b

/-- Standing integer parameters for M3 and M4. -/
structure ContactParameters where
  a : ℤ
  b : ℤ
  d : ℤ
  d_nonneg : 0 ≤ d
  a_pos : 1 ≤ a
  b_gt : a + d < b

theorem CommutationParameters.ext {P Q : CommutationParameters}
    (ha : P.a = Q.a) (hb : P.b = Q.b) (ht : P.t = Q.t) (hd : P.d = Q.d) : P = Q := by
  cases P
  cases Q
  cases ha
  cases hb
  cases ht
  cases hd
  rfl

theorem ContactParameters.ext {P Q : ContactParameters}
    (ha : P.a = Q.a) (hb : P.b = Q.b) (hd : P.d = Q.d) : P = Q := by
  cases P
  cases Q
  cases ha
  cases hb
  cases hd
  rfl

private theorem m1F_domain (P : CommutationParameters) :
    Domain (P.a+P.d) (P.b+P.d) (P.a+P.d) (P.a+P.b+P.d) (P.b+P.d)
      (P.t+P.d) P.d (P.t+P.d) (P.t+P.d) := by
  have := P.t_nonneg; have := P.d_nonneg; have := P.a_gt; have := P.b_gt
  dsimp [Domain]
  omega

private theorem m1H_domain (P : CommutationParameters) :
    Domain (P.a+P.d) (P.a+P.b+P.d) (P.b+P.d) (P.a+P.d) (P.b+P.d)
      (P.t+P.d) (P.t+P.d) P.d (P.t+P.d) := by
  have := P.t_nonneg; have := P.d_nonneg; have := P.a_gt; have := P.b_gt
  dsimp [Domain]
  omega

private theorem m2F_domain (P : CommutationParameters) :
    Domain (P.a+P.d) (P.b+P.d) (P.a+P.d) (P.a+P.b-P.t+P.d) (P.b+P.d)
      P.d (P.t+P.d) P.d P.d := by
  have := P.t_nonneg; have := P.d_nonneg; have := P.a_gt; have := P.b_gt
  dsimp [Domain]
  omega

private theorem m2H_domain (P : CommutationParameters) :
    Domain (P.a+P.d) (P.a+P.b-P.t+P.d) (P.b+P.d) (P.a+P.d) (P.b+P.d)
      P.d P.d (P.t+P.d) P.d := by
  have := P.t_nonneg; have := P.d_nonneg; have := P.a_gt; have := P.b_gt
  dsimp [Domain]
  omega

private theorem m3F_domain (P : ContactParameters) :
    Domain (P.a+P.d) (P.b+P.d) (P.b+P.d) (P.b+P.d) (P.a+P.b+P.d)
      P.d P.d P.d (P.a+P.d) := by
  have := P.d_nonneg; have := P.a_pos; have := P.b_gt
  dsimp [Domain]
  omega

private theorem m3H_domain (P : ContactParameters) :
    Domain (P.a+P.d) (P.b+P.d) (P.a+P.b+P.d) (P.b+P.d) (P.b+P.d)
      P.d (P.a+P.d) P.d P.d := by
  have := P.d_nonneg; have := P.a_pos; have := P.b_gt
  dsimp [Domain]
  omega

private theorem m4F_domain (P : ContactParameters) :
    Domain (P.a+P.d) (P.b+P.d) (P.b+P.d) (P.a+P.b+P.d) (P.a+P.b+P.d)
      P.d P.d (P.a+P.d) (P.a+P.d) := by
  have := P.d_nonneg; have := P.a_pos; have := P.b_gt
  dsimp [Domain]
  omega

private theorem m4H_domain (P : ContactParameters) :
    Domain (P.a+P.d) (P.b+P.d) (P.a+P.b+P.d) (P.a+P.b+P.d) (P.b+P.d)
      P.d (P.a+P.d) (P.a+P.d) P.d := by
  have := P.d_nonneg; have := P.a_pos; have := P.b_gt
  dsimp [Domain]
  omega

/-- The first actual M1 representative. -/
def m1F (P : CommutationParameters) : Profile 4 :=
  profile (P.a+P.d) (P.b+P.d) (P.a+P.d) (P.a+P.b+P.d) (P.b+P.d)
    (P.t+P.d) P.d (P.t+P.d) (P.t+P.d) (m1F_domain P)

/-- The second actual M1 representative. -/
def m1H (P : CommutationParameters) : Profile 4 :=
  profile (P.a+P.d) (P.a+P.b+P.d) (P.b+P.d) (P.a+P.d) (P.b+P.d)
    (P.t+P.d) (P.t+P.d) P.d (P.t+P.d) (m1H_domain P)

/-- The first actual M2 representative. -/
def m2F (P : CommutationParameters) : Profile 4 :=
  profile (P.a+P.d) (P.b+P.d) (P.a+P.d) (P.a+P.b-P.t+P.d) (P.b+P.d)
    P.d (P.t+P.d) P.d P.d (m2F_domain P)

/-- The second actual M2 representative. -/
def m2H (P : CommutationParameters) : Profile 4 :=
  profile (P.a+P.d) (P.a+P.b-P.t+P.d) (P.b+P.d) (P.a+P.d) (P.b+P.d)
    P.d P.d (P.t+P.d) P.d (m2H_domain P)

/-- The first actual M3 representative. -/
def m3F (P : ContactParameters) : Profile 4 :=
  profile (P.a+P.d) (P.b+P.d) (P.b+P.d) (P.b+P.d) (P.a+P.b+P.d)
    P.d P.d P.d (P.a+P.d) (m3F_domain P)

/-- The second actual M3 representative. -/
def m3H (P : ContactParameters) : Profile 4 :=
  profile (P.a+P.d) (P.b+P.d) (P.a+P.b+P.d) (P.b+P.d) (P.b+P.d)
    P.d (P.a+P.d) P.d P.d (m3H_domain P)

/-- The first actual M4 representative. -/
def m4F (P : ContactParameters) : Profile 4 :=
  profile (P.a+P.d) (P.b+P.d) (P.b+P.d) (P.a+P.b+P.d) (P.a+P.b+P.d)
    P.d P.d (P.a+P.d) (P.a+P.d) (m4F_domain P)

/-- The second actual M4 representative. -/
def m4H (P : ContactParameters) : Profile 4 :=
  profile (P.a+P.d) (P.b+P.d) (P.a+P.b+P.d) (P.a+P.b+P.d) (P.b+P.d)
    P.d (P.a+P.d) (P.a+P.d) P.d (m4H_domain P)

/-- The B commutation identity in every commutative coefficient ring. -/
theorem b_identity {R : Type*} [CommRing R] (h : ℤ → R) (p m z w : ℤ) :
    interval h p m p (p+m-w) m z w z z =
      interval h p (p+m-w) m p m z z w z := by
  unfold interval
  ring_nf

/-- The A1 identity in every commutative coefficient ring. -/
theorem a1_identity {R : Type*} [CommRing R] (h : ℤ → R) (p m z : ℤ) :
    interval h p m m m (m+p-z) z z z p =
      interval h p m (m+p-z) m m z p z z := by
  unfold interval
  ring_nf

/-- The A2 identity in every commutative coefficient ring. -/
theorem a2_identity {R : Type*} [CommRing R] (h : ℤ → R) (p m z : ℤ) :
    interval h p m m (m+p-z) (m+p-z) z z p p =
      interval h p m (m+p-z) (m+p-z) m z p p z := by
  unfold interval
  ring_nf

/-- M1, with every unit and label coincidence retained. -/
theorem m1_schur_eq (P : CommutationParameters) :
    (m1F P).toBetaDiagram.schur = (m1H P).toBetaDiagram.schur := by
  unfold m1F m1H
  rw [profile_schur, profile_schur]
  convert b_identity hh (P.a+P.d) (P.b+P.d) (P.t+P.d) P.d using 1 <;>
    congr 1 <;> omega

/-- M2, including `t = 0` and `d = 0`. -/
theorem m2_schur_eq (P : CommutationParameters) :
    (m2F P).toBetaDiagram.schur = (m2H P).toBetaDiagram.schur := by
  unfold m2F m2H
  rw [profile_schur, profile_schur]
  convert b_identity hh (P.a+P.d) (P.b+P.d) P.d (P.t+P.d) using 1 <;>
    congr 1 <;> omega

theorem m3_schur_eq (P : ContactParameters) :
    (m3F P).toBetaDiagram.schur = (m3H P).toBetaDiagram.schur := by
  unfold m3F m3H
  rw [profile_schur, profile_schur]
  convert a1_identity hh (P.a+P.d) (P.b+P.d) P.d using 1 <;>
    congr 1 <;> omega

theorem m4_schur_eq (P : ContactParameters) :
    (m4F P).toBetaDiagram.schur = (m4H P).toBetaDiagram.schur := by
  unfold m4F m4H
  rw [profile_schur, profile_schur]
  convert a2_identity hh (P.a+P.d) (P.b+P.d) P.d using 1 <;>
    congr 1 <;> omega

/-- The overlap of M1 and M2 at zero deformation is literal in both words. -/
theorem m1_eq_m2_at_zero (P : CommutationParameters) (ht : P.t = 0) :
    m1F P = m2F P ∧ m1H P = m2H P := by
  constructor <;> apply Profile.ext
  all_goals funext i; fin_cases i <;> simp [m1F, m2F, m1H, m2H, profile, ht]

/-- The ordered row reading is exactly the original natural row word. -/
@[simp] theorem profile_rowLength (P : Profile 4) (i : Fin 5) :
    P.toBetaDiagram.rowLength i = (P.r i : ℤ) := P.xi_sub_zeta i

/-- The four translation-class representatives, with half-turns kept explicit. -/
def quartet (F H : BetaDiagram 5) : Fin 4 → BetaDiagram 5 :=
  ![F,F.rotate,H,H.rotate]

/-- All indexed members of M1 are full Schur equals. -/
theorem m1_quartet_schur (P : CommutationParameters) (i : Fin 4) :
    (quartet (m1F P).toBetaDiagram (m1H P).toBetaDiagram i).schur =
      (m1F P).toBetaDiagram.schur := by
  fin_cases i <;> simp [quartet, BetaDiagram.rotate_schur, m1_schur_eq P]

theorem m2_quartet_schur (P : CommutationParameters) (i : Fin 4) :
    (quartet (m2F P).toBetaDiagram (m2H P).toBetaDiagram i).schur =
      (m2F P).toBetaDiagram.schur := by
  fin_cases i <;> simp [quartet, BetaDiagram.rotate_schur, m2_schur_eq P]

theorem m3_quartet_schur (P : ContactParameters) (i : Fin 4) :
    (quartet (m3F P).toBetaDiagram (m3H P).toBetaDiagram i).schur =
      (m3F P).toBetaDiagram.schur := by
  fin_cases i <;> simp [quartet, BetaDiagram.rotate_schur, m3_schur_eq P]

theorem m4_quartet_schur (P : ContactParameters) (i : Fin 4) :
    (quartet (m4F P).toBetaDiagram (m4H P).toBetaDiagram i).schur =
      (m4F P).toBetaDiagram.schur := by
  fin_cases i <;> simp [quartet, BetaDiagram.rotate_schur, m4_schur_eq P]

/-- Each M1 scheme has four distinct translation classes, even at `t = 0`. -/
theorem m1_quartet_distinct (P : CommutationParameters) (i j : Fin 4)
    (h : (quartet (m1F P).toBetaDiagram (m1H P).toBetaDiagram i).TranslationEquivalent
      (quartet (m1F P).toBetaDiagram (m1H P).toBetaDiagram j)) : i = j := by
  have h0 := h.rowLength_eq 0
  have h1 := h.rowLength_eq 1
  have h3 := h.rowLength_eq 3
  have h4 := h.rowLength_eq 4
  have := P.a_ne_b
  have := P.a_gt
  have := P.b_gt
  have := P.t_nonneg
  have := P.d_nonneg
  fin_cases i <;> fin_cases j
  all_goals first | rfl |
    (simp [quartet, BetaDiagram.rotate_rowLength, profile_rowLength,
      m1F, m1H, profile_row, Fin.rev] at h0 h1 h3 h4; omega)

theorem m2_quartet_distinct (P : CommutationParameters) (i j : Fin 4)
    (h : (quartet (m2F P).toBetaDiagram (m2H P).toBetaDiagram i).TranslationEquivalent
      (quartet (m2F P).toBetaDiagram (m2H P).toBetaDiagram j)) : i = j := by
  have h0 := h.rowLength_eq 0
  have h1 := h.rowLength_eq 1
  have h3 := h.rowLength_eq 3
  have h4 := h.rowLength_eq 4
  have := P.a_ne_b
  have := P.a_gt
  have := P.b_gt
  have := P.t_nonneg
  have := P.d_nonneg
  fin_cases i <;> fin_cases j
  all_goals first | rfl |
    (simp [quartet, BetaDiagram.rotate_rowLength, profile_rowLength,
      m2F, m2H, profile_row, Fin.rev] at h0 h1 h3 h4; omega)

theorem m3_quartet_distinct (P : ContactParameters) (i j : Fin 4)
    (h : (quartet (m3F P).toBetaDiagram (m3H P).toBetaDiagram i).TranslationEquivalent
      (quartet (m3F P).toBetaDiagram (m3H P).toBetaDiagram j)) : i = j := by
  have h0 := h.rowLength_eq 0
  have h1 := h.rowLength_eq 1
  have h3 := h.rowLength_eq 3
  have h4 := h.rowLength_eq 4
  have := P.a_pos
  have := P.b_gt
  have := P.d_nonneg
  fin_cases i <;> fin_cases j
  all_goals first | rfl |
    (simp [quartet, BetaDiagram.rotate_rowLength, profile_rowLength,
      m3F, m3H, profile_row, Fin.rev] at h0 h1 h3 h4; omega)

theorem m4_quartet_distinct (P : ContactParameters) (i j : Fin 4)
    (h : (quartet (m4F P).toBetaDiagram (m4H P).toBetaDiagram i).TranslationEquivalent
      (quartet (m4F P).toBetaDiagram (m4H P).toBetaDiagram j)) : i = j := by
  have h0 := h.rowLength_eq 0
  have h1 := h.rowLength_eq 1
  have h3 := h.rowLength_eq 3
  have h4 := h.rowLength_eq 4
  have := P.a_pos
  have := P.b_gt
  have := P.d_nonneg
  fin_cases i <;> fin_cases j
  all_goals first | rfl |
    (simp [quartet, BetaDiagram.rotate_rowLength, profile_rowLength,
      m4F, m4H, profile_row, Fin.rev] at h0 h1 h3 h4; omega)

/-- Every displayed M1 profile is a connected six-negative staircase. -/
theorem m1_staircase (P : CommutationParameters) :
    (∀ i j : Fin 5, (m1F P).toBetaDiagram.row i < (m1F P).toBetaDiagram.col j ↔
      j.val+2 ≤ i.val) ∧
    (∀ i j : Fin 5, (m1H P).toBetaDiagram.row i < (m1H P).toBetaDiagram.col j ↔
      j.val+2 ≤ i.val) :=
  ⟨profile_staircase _ _ _ _ _ _ _ _ _ (m1F_domain P),
   profile_staircase _ _ _ _ _ _ _ _ _ (m1H_domain P)⟩

theorem m2_staircase (P : CommutationParameters) :
    (∀ i j : Fin 5, (m2F P).toBetaDiagram.row i < (m2F P).toBetaDiagram.col j ↔
      j.val+2 ≤ i.val) ∧
    (∀ i j : Fin 5, (m2H P).toBetaDiagram.row i < (m2H P).toBetaDiagram.col j ↔
      j.val+2 ≤ i.val) :=
  ⟨profile_staircase _ _ _ _ _ _ _ _ _ (m2F_domain P),
   profile_staircase _ _ _ _ _ _ _ _ _ (m2H_domain P)⟩

theorem m3_staircase (P : ContactParameters) :
    (∀ i j : Fin 5, (m3F P).toBetaDiagram.row i < (m3F P).toBetaDiagram.col j ↔
      j.val+2 ≤ i.val) ∧
    (∀ i j : Fin 5, (m3H P).toBetaDiagram.row i < (m3H P).toBetaDiagram.col j ↔
      j.val+2 ≤ i.val) :=
  ⟨profile_staircase _ _ _ _ _ _ _ _ _ (m3F_domain P),
   profile_staircase _ _ _ _ _ _ _ _ _ (m3H_domain P)⟩

theorem m4_staircase (P : ContactParameters) :
    (∀ i j : Fin 5, (m4F P).toBetaDiagram.row i < (m4F P).toBetaDiagram.col j ↔
      j.val+2 ≤ i.val) ∧
    (∀ i j : Fin 5, (m4H P).toBetaDiagram.row i < (m4H P).toBetaDiagram.col j ↔
      j.val+2 ≤ i.val) :=
  ⟨profile_staircase _ _ _ _ _ _ _ _ _ (m4F_domain P),
   profile_staircase _ _ _ _ _ _ _ _ _ (m4H_domain P)⟩

/-- The actual parameter action of Gamma on M1 and M2. -/
def gammaCommutation (P : CommutationParameters) : CommutationParameters where
  a := 2*P.a
  b := 2*P.b
  t := 2*P.t
  d := 2*P.d+1
  t_nonneg := by have := P.t_nonneg; omega
  d_nonneg := by have := P.d_nonneg; omega
  a_gt := by have := P.a_gt; omega
  b_gt := by have := P.b_gt; omega
  a_ne_b := by have := P.a_ne_b; omega

/-- The actual parameter action of Gamma on M3 and M4. -/
def gammaContact (P : ContactParameters) : ContactParameters where
  a := 2*P.a
  b := 2*P.b
  d := 2*P.d+1
  d_nonneg := by have := P.d_nonneg; omega
  a_pos := by have := P.a_pos; omega
  b_gt := by have := P.b_gt; omega

/-- Gamma realizes the same M1 words, rather than an equality of surrogates. -/
theorem m1_gamma (P : CommutationParameters) :
    (m1F P).lift Gluing.rowShiftTwoOne = m1F (gammaCommutation P) ∧
      (m1H P).lift Gluing.rowShiftTwoOne = m1H (gammaCommutation P) := by
  have := P.a_gt; have := P.b_gt; have := P.t_nonneg; have := P.d_nonneg
  constructor <;> apply Profile.ext
  all_goals funext i; fin_cases i <;>
    simp [Profile.lift_r, Profile.lift_g, Gluing.rowShiftTwoOne, m1F, m1H,
      gammaCommutation, profile] <;> omega

theorem m2_gamma (P : CommutationParameters) :
    (m2F P).lift Gluing.rowShiftTwoOne = m2F (gammaCommutation P) ∧
      (m2H P).lift Gluing.rowShiftTwoOne = m2H (gammaCommutation P) := by
  have := P.a_gt; have := P.b_gt; have := P.t_nonneg; have := P.d_nonneg
  constructor <;> apply Profile.ext
  all_goals funext i; fin_cases i <;>
    simp [Profile.lift_r, Profile.lift_g, Gluing.rowShiftTwoOne, m2F, m2H,
      gammaCommutation, profile] <;> omega

theorem m3_gamma (P : ContactParameters) :
    (m3F P).lift Gluing.rowShiftTwoOne = m3F (gammaContact P) ∧
      (m3H P).lift Gluing.rowShiftTwoOne = m3H (gammaContact P) := by
  have := P.a_pos; have := P.b_gt; have := P.d_nonneg
  constructor <;> apply Profile.ext
  all_goals funext i; fin_cases i <;>
    simp [Profile.lift_r, Profile.lift_g, Gluing.rowShiftTwoOne, m3F, m3H,
      gammaContact, profile] <;> omega

theorem m4_gamma (P : ContactParameters) :
    (m4F P).lift Gluing.rowShiftTwoOne = m4F (gammaContact P) ∧
      (m4H P).lift Gluing.rowShiftTwoOne = m4H (gammaContact P) := by
  have := P.a_pos; have := P.b_gt; have := P.d_nonneg
  constructor <;> apply Profile.ext
  all_goals funext i; fin_cases i <;>
    simp [Profile.lift_r, Profile.lift_g, Gluing.rowShiftTwoOne, m4F, m4H,
      gammaContact, profile] <;> omega

/-- The inverse B-to-M1 dictionary when the repeated gap is no smaller. -/
def bM1Parameters (p m z w : ℤ) (hw : 0 ≤ w) (hzw : w ≤ z)
    (hp : z + w < p) (hm : z + w < m) (hne : p ≠ m) : CommutationParameters where
  a := p-w
  b := m-w
  t := z-w
  d := w
  t_nonneg := by omega
  d_nonneg := hw
  a_gt := by omega
  b_gt := by omega
  a_ne_b := by omega

/-- The inverse B-to-M2 dictionary when the exceptional gap is larger. -/
def bM2Parameters (p m z w : ℤ) (hz : 0 ≤ z) (hzw : z < w)
    (hp : z + w < p) (hm : z + w < m) (hne : p ≠ m) : CommutationParameters where
  a := p-z
  b := m-z
  t := w-z
  d := z
  t_nonneg := by omega
  d_nonneg := hz
  a_gt := by omega
  b_gt := by omega
  a_ne_b := by omega

/-- A1 and A2 have one common inverse contact-family dictionary. -/
def aParameters (p m z : ℤ) (hz : 0 ≤ z) (hp : z < p)
    (hm : p + z < m) : ContactParameters where
  a := p-z
  b := m-z
  d := z
  d_nonneg := hz
  a_pos := by omega
  b_gt := by omega

/-- The dictionary matches both actual B profiles in all coordinates. -/
theorem b_m1_words (p m z w : ℤ) (hw : 0 ≤ w) (hzw : w ≤ z)
    (hp : z + w < p) (hm : z + w < m) (hne : p ≠ m) :
    let P := bM1Parameters p m z w hw hzw hp hm hne
    (fun i => ((m1F P).r i : ℤ)) = ![p,m,p,p+m-w,m] ∧
    (fun j => ((m1F P).g j : ℤ)) = ![z,w,z,z] ∧
    (fun i => ((m1H P).r i : ℤ)) = ![p,p+m-w,m,p,m] ∧
    (fun j => ((m1H P).g j : ℤ)) = ![z,z,w,z] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals funext i; fin_cases i <;>
    simp [m1F, m1H, profile_row, profile_gap, bM1Parameters] <;> omega

theorem b_m2_words (p m z w : ℤ) (hz : 0 ≤ z) (hzw : z < w)
    (hp : z + w < p) (hm : z + w < m) (hne : p ≠ m) :
    let P := bM2Parameters p m z w hz hzw hp hm hne
    (fun i => ((m2F P).r i : ℤ)) = ![p,m,p,p+m-w,m] ∧
    (fun j => ((m2F P).g j : ℤ)) = ![z,w,z,z] ∧
    (fun i => ((m2H P).r i : ℤ)) = ![p,p+m-w,m,p,m] ∧
    (fun j => ((m2H P).g j : ℤ)) = ![z,z,w,z] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals funext i; fin_cases i <;>
    simp [m2F, m2H, profile_row, profile_gap, bM2Parameters] <;> omega

theorem a1_m3_words (p m z : ℤ) (hz : 0 ≤ z) (hp : z < p) (hm : p + z < m) :
    let P := aParameters p m z hz hp hm
    (fun i => ((m3F P).r i : ℤ)) = ![p,m,m,m,m+p-z] ∧
    (fun j => ((m3F P).g j : ℤ)) = ![z,z,z,p] ∧
    (fun i => ((m3H P).r i : ℤ)) = ![p,m,m+p-z,m,m] ∧
    (fun j => ((m3H P).g j : ℤ)) = ![z,p,z,z] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals funext i; fin_cases i <;>
    simp [m3F, m3H, profile_row, profile_gap, aParameters] <;> omega

theorem a2_m4_words (p m z : ℤ) (hz : 0 ≤ z) (hp : z < p) (hm : p + z < m) :
    let P := aParameters p m z hz hp hm
    (fun i => ((m4F P).r i : ℤ)) = ![p,m,m,m+p-z,m+p-z] ∧
    (fun j => ((m4F P).g j : ℤ)) = ![z,z,p,p] ∧
    (fun i => ((m4H P).r i : ℤ)) = ![p,m,m+p-z,m+p-z,m] ∧
    (fun j => ((m4H P).g j : ℤ)) = ![z,p,p,z] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals funext i; fin_cases i <;>
    simp [m4F, m4H, profile_row, profile_gap, aParameters] <;> omega

/-- Halving a genuine Gamma-image M1/M2 parameter tuple restores the source
domain, including the original boundary `d = 0`. -/
def ungammaCommutation (P : CommutationParameters)
    (ha : P.a % 2 = 0) (hb : P.b % 2 = 0) (ht : P.t % 2 = 0) (hd : P.d % 2 = 1) :
    CommutationParameters where
  a := P.a / 2
  b := P.b / 2
  t := P.t / 2
  d := (P.d-1) / 2
  t_nonneg := by have := P.t_nonneg; omega
  d_nonneg := by have := P.d_nonneg; omega
  a_gt := by have := P.a_gt; omega
  b_gt := by have := P.b_gt; omega
  a_ne_b := by have := P.a_ne_b; omega

/-- The corresponding inverse parameter action for the contact families. -/
def ungammaContact (P : ContactParameters)
    (ha : P.a % 2 = 0) (hb : P.b % 2 = 0) (hd : P.d % 2 = 1) :
    ContactParameters where
  a := P.a / 2
  b := P.b / 2
  d := (P.d-1) / 2
  d_nonneg := by have := P.d_nonneg; omega
  a_pos := by have := P.a_pos; omega
  b_gt := by have := P.b_gt; omega

theorem gamma_ungamma_commutation (P : CommutationParameters)
    (ha : P.a % 2 = 0) (hb : P.b % 2 = 0) (ht : P.t % 2 = 0) (hd : P.d % 2 = 1) :
    gammaCommutation (ungammaCommutation P ha hb ht hd) = P := by
  apply CommutationParameters.ext
  · change 2 * (P.a / 2) = P.a
    omega
  · change 2 * (P.b / 2) = P.b
    omega
  · change 2 * (P.t / 2) = P.t
    omega
  · change 2 * ((P.d - 1) / 2) + 1 = P.d
    omega

theorem gamma_ungamma_contact (P : ContactParameters)
    (ha : P.a % 2 = 0) (hb : P.b % 2 = 0) (hd : P.d % 2 = 1) :
    gammaContact (ungammaContact P ha hb hd) = P := by
  apply ContactParameters.ext
  · change 2 * (P.a / 2) = P.a
    omega
  · change 2 * (P.b / 2) = P.b
    omega
  · change 2 * ((P.d - 1) / 2) + 1 = P.d
    omega

/-- The Gamma-image congruences are read from the actual M1 row and gap words. -/
theorem m1_image_parity (P : CommutationParameters)
    (h : (m1F P).HasResidue Gluing.rowShiftTwoOne) :
    P.a % 2 = 0 ∧ P.b % 2 = 0 ∧ P.t % 2 = 0 ∧ P.d % 2 = 1 := by
  have ha := h.1 0; have hb := h.1 1
  have ht := h.2 0; have hd := h.2 1
  have := P.a_gt; have := P.b_gt; have := P.d_nonneg; have := P.t_nonneg
  simp [Gluing.rowShiftTwoOne,m1F,profile] at ha hb ht hd
  omega

theorem m2_image_parity (P : CommutationParameters)
    (h : (m2F P).HasResidue Gluing.rowShiftTwoOne) :
    P.a % 2 = 0 ∧ P.b % 2 = 0 ∧ P.t % 2 = 0 ∧ P.d % 2 = 1 := by
  have ha := h.1 0; have hb := h.1 1
  have ht := h.2 1; have hd := h.2 0
  have := P.a_gt; have := P.b_gt; have := P.d_nonneg; have := P.t_nonneg
  simp [Gluing.rowShiftTwoOne,m2F,profile] at ha hb ht hd
  omega

theorem m3_image_parity (P : ContactParameters)
    (h : (m3F P).HasResidue Gluing.rowShiftTwoOne) :
    P.a % 2 = 0 ∧ P.b % 2 = 0 ∧ P.d % 2 = 1 := by
  have ha := h.1 0; have hb := h.1 1; have hd := h.2 0
  have := P.a_pos; have := P.b_gt; have := P.d_nonneg
  simp [Gluing.rowShiftTwoOne,m3F,profile] at ha hb hd
  omega

theorem m4_image_parity (P : ContactParameters)
    (h : (m4F P).HasResidue Gluing.rowShiftTwoOne) :
    P.a % 2 = 0 ∧ P.b % 2 = 0 ∧ P.d % 2 = 1 := by
  have ha := h.1 0; have hb := h.1 1; have hd := h.2 0
  have := P.a_pos; have := P.b_gt; have := P.d_nonneg
  simp [Gluing.rowShiftTwoOne,m4F,profile] at ha hb hd
  omega

end SkewJacobiNegative.StaircaseFiveFamilies
