/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FiveOpeningExpansion
import SkewJacobiNegative.ExteriorGaps
import Mathlib.Tactic.FinCases

/-!
# Five-negative normal forms

Actual profiles and beta diagrams for `eq:five-normal-forms` in
`shields-2026-skew-jacobi-negative.tex`.  All nonnegative labels, including
zero, denote independent variables.  The inequalities distinguish the two
patterns; the cubic identifications are asserted only for the middle pattern.
-/

namespace SkewJacobiNegative.FiveNegative

open MvPolynomial

structure Parameters where
  x : ℕ
  y : ℕ
  c : ℕ
  b : ℕ
  a : ℕ
  u : ℕ
  v : ℕ
  p : ℕ
  tau : ℕ
  deriving DecidableEq

namespace Parameters

def L (t : Parameters) : ℕ := t.u + t.v - t.tau
def q (t : Parameters) : ℕ := t.b - t.p

end Parameters

/-- These are exactly the middle-pattern validity inequalities. -/
def ValidM (t : Parameters) : Prop :=
  t.tau < t.u ∧ t.tau < t.v ∧ t.p < t.b ∧
    t.a < t.x ∧ t.a + t.u < t.y ∧ t.v + t.p < t.c

/-- These are exactly the end-pattern validity inequalities. -/
def ValidE (t : Parameters) : Prop :=
  t.tau < t.u ∧ t.tau < t.v ∧ t.p < t.b ∧
    t.u < t.x ∧ t.a + t.v < t.y ∧ t.a + t.p < t.c

noncomputable def B (u v tau : ℕ) : Gluing.HomLambda :=
  X u * X v - X tau * X (u + v - tau)
noncomputable def F (s z tau : ℕ) : Gluing.HomLambda :=
  X s * X z - X tau * X (z + s - tau)
noncomputable def T (b p z : ℕ) : Gluing.HomLambda :=
  X b * X z - X p * X (z + (b - p))
noncomputable def G (s tau b p z : ℕ) : Gluing.HomLambda :=
  X s * T b p z - X tau * T b p (z + s - tau)
noncomputable def Q (x a s tau z : ℕ) : Gluing.HomLambda :=
  X x * F s z tau - X a * F s (z + x - a) tau

/-- The row and overlap words of the middle pattern. -/
def mProfile (t : Parameters) (h : ValidM t) : Gluing.Profile 4 where
  r := ![t.x, t.y, t.L, t.c, t.b]
  g := ![t.a, t.u, t.v, t.p]
  r_pos := by
    rcases h with ⟨hu, hv, hb, hx, hy, hc⟩
    intro i; fin_cases i <;> simp [Parameters.L] <;> omega
  g_lt_castSucc := by
    rcases h with ⟨hu, hv, hb, hx, hy, hc⟩
    intro i; fin_cases i <;> simp [Parameters.L] <;> omega
  g_lt_succ := by
    rcases h with ⟨hu, hv, hb, hx, hy, hc⟩
    intro i; fin_cases i <;> simp [Parameters.L] <;> omega

/-- The row and overlap words of the oriented end pattern. -/
def eProfile (t : Parameters) (h : ValidE t) : Gluing.Profile 4 where
  r := ![t.x, t.L, t.y, t.c, t.b]
  g := ![t.u, t.v, t.a, t.p]
  r_pos := by
    rcases h with ⟨hu, hv, hb, hx, hy, hc⟩
    intro i; fin_cases i <;> simp [Parameters.L] <;> omega
  g_lt_castSucc := by
    rcases h with ⟨hu, hv, hb, hx, hy, hc⟩
    intro i; fin_cases i <;> simp [Parameters.L] <;> omega
  g_lt_succ := by
    rcases h with ⟨hu, hv, hb, hx, hy, hc⟩
    intro i; fin_cases i <;> simp [Parameters.L] <;> omega

def M (t : Parameters) (h : ValidM t) : BetaDiagram 5 :=
  (mProfile t h).toBetaDiagram

def E (t : Parameters) (h : ValidE t) : BetaDiagram 5 :=
  (eProfile t h).toBetaDiagram

theorem M_connected (t : Parameters) (h : ValidM t) : (M t h).Connected :=
  (mProfile t h).toBetaDiagram_connected

theorem E_connected (t : Parameters) (h : ValidE t) : (E t h).Connected :=
  (eProfile t h).toBetaDiagram_connected

/-- A generic profile's signed matrix indices, before any negative-index truncation. -/
def profileIndex (r : Fin 5 → ℕ) (g : Fin 4 → ℕ) (i j : Fin 5) : ℤ :=
  (∑ k : Fin 4, if i.val ≤ k.val then ((r k.succ : ℤ) - g k) else 0) + r i -
    ∑ k : Fin 4, if j.val ≤ k.val then ((r k.succ : ℤ) - g k) else 0

theorem M_index (t : Parameters) (h : ValidM t) (i j : Fin 5) :
    (M t h).row i - (M t h).col j =
      profileIndex ![t.x,t.y,t.L,t.c,t.b] ![t.a,t.u,t.v,t.p] i j := rfl

theorem E_index (t : Parameters) (h : ValidE t) (i j : Fin 5) :
    (E t h).row i - (E t h).col j =
      profileIndex ![t.x,t.L,t.y,t.c,t.b] ![t.u,t.v,t.a,t.p] i j := rfl

theorem M_opening (t : Parameters) (h : ValidM t) : FiveOpening.HasOpening (M t h) 1 := by
  rcases h with ⟨hu, hv, hb, hx, hy, hc⟩
  have hL : t.L + t.tau = t.u + t.v := by dsimp [Parameters.L]; omega
  intro i j
  have he := M_index t ⟨hu,hv,hb,hx,hy,hc⟩ i j
  fin_cases i <;> fin_cases j <;>
    simp [profileIndex, Fin.sum_univ_succ, FiveOpening.openedRow,
      FiveOpening.openedCol] at he ⊢ <;> omega

theorem E_opening (t : Parameters) (h : ValidE t) : FiveOpening.HasOpening (E t h) 0 := by
  rcases h with ⟨hu, hv, hb, hx, hy, hc⟩
  have hL : t.L + t.tau = t.u + t.v := by dsimp [Parameters.L]; omega
  intro i j
  have he := E_index t ⟨hu,hv,hb,hx,hy,hc⟩ i j
  fin_cases i <;> fin_cases j <;>
    simp [profileIndex, Fin.sum_univ_succ, FiveOpening.openedRow,
      FiveOpening.openedCol] at he ⊢ <;> omega

/-- Read a middle opening directly from the original beta lists. -/
def middleParameters (D : BetaDiagram 5) : Parameters where
  x := (D.row 0 - D.col 0).toNat
  y := (D.row 1 - D.col 1).toNat
  c := (D.row 3 - D.col 3).toNat
  b := (D.row 4 - D.col 4).toNat
  a := (D.row 1 - D.col 0).toNat
  u := (D.row 2 - D.col 1).toNat
  v := (D.row 3 - D.col 2).toNat
  p := (D.row 4 - D.col 3).toNat
  tau := (D.row 3 - D.col 1).toNat

/-- Read an oriented end opening directly from the original beta lists. -/
def endParameters (D : BetaDiagram 5) : Parameters where
  x := (D.row 0 - D.col 0).toNat
  y := (D.row 2 - D.col 2).toNat
  c := (D.row 3 - D.col 3).toNat
  b := (D.row 4 - D.col 4).toNat
  a := (D.row 3 - D.col 2).toNat
  u := (D.row 1 - D.col 0).toNat
  v := (D.row 2 - D.col 1).toNat
  p := (D.row 4 - D.col 3).toNat
  tau := (D.row 2 - D.col 0).toNat

private theorem beta_chain (D : BetaDiagram 5) (hD : D.Connected) :
    D.row 1 < D.row 0 ∧ D.row 2 < D.row 1 ∧ D.row 3 < D.row 2 ∧
    D.row 4 < D.row 3 ∧ D.col 1 < D.col 0 ∧ D.col 2 < D.col 1 ∧
    D.col 3 < D.col 2 ∧ D.col 4 < D.col 3 ∧
    D.col 0 ≤ D.row 1 ∧ D.col 1 ≤ D.row 2 ∧
    D.col 2 ≤ D.row 3 ∧ D.col 3 ≤ D.row 4 := by
  exact ⟨D.row_strictAnti (by decide),D.row_strictAnti (by decide),
    D.row_strictAnti (by decide),D.row_strictAnti (by decide),
    D.col_strictAnti (by decide),D.col_strictAnti (by decide),
    D.col_strictAnti (by decide),D.col_strictAnti (by decide),
    hD.2 0 (by decide),hD.2 1 (by decide),hD.2 2 (by decide),hD.2 3 (by decide)⟩

theorem middleParameters_valid (D : BetaDiagram 5) (hD : D.Connected)
    (ho : FiveOpening.HasOpening D 1) : ValidM (middleParameters D) := by
  rcases beta_chain D hD with ⟨r01,r12,r23,r34,c01,c12,c23,c34,o01,o12,o23,o34⟩
  have hn20 := (ho 2 0).mpr (by simp [FiveOpening.openedRow,FiveOpening.openedCol])
  have hn42 := (ho 4 2).mpr (by simp [FiveOpening.openedRow,FiveOpening.openedCol])
  have ht := FiveOpening.openingLabel_nonneg D ho
  simp [FiveOpening.openingLabel,FiveOpening.openedRow,FiveOpening.openedCol] at ht
  dsimp [ValidM,middleParameters]
  omega

theorem endParameters_valid (D : BetaDiagram 5) (hD : D.Connected)
    (ho : FiveOpening.HasOpening D 0) : ValidE (endParameters D) := by
  rcases beta_chain D hD with ⟨r01,r12,r23,r34,c01,c12,c23,c34,o01,o12,o23,o34⟩
  have hn31 := (ho 3 1).mpr (by simp [FiveOpening.openedRow,FiveOpening.openedCol])
  have hn42 := (ho 4 2).mpr (by simp [FiveOpening.openedRow,FiveOpening.openedCol])
  have ht := FiveOpening.openingLabel_nonneg D ho
  simp [FiveOpening.openingLabel,FiveOpening.openedRow,FiveOpening.openedCol] at ht
  dsimp [ValidE,endParameters]
  omega

private theorem toProfile_r (D : BetaDiagram 5) (hD : D.Connected) (i : Fin 5) :
    (D.toProfile hD).r i = (D.row i - D.col i).toNat := by
  simp [BetaDiagram.toProfile,Gluing.Profile.ofBetaPair,BetaDiagram.normalizedPair]

private theorem toProfile_g (D : BetaDiagram 5) (hD : D.Connected) (i : Fin 4) :
    (D.toProfile hD).g i = (D.row i.succ - D.col i.castSucc).toNat := by
  simp [BetaDiagram.toProfile,Gluing.Profile.ofBetaPair,BetaDiagram.normalizedPair]

theorem middle_profile_reconstruction (D : BetaDiagram 5) (hD : D.Connected)
    (ho : FiveOpening.HasOpening D 1) :
    mProfile (middleParameters D) (middleParameters_valid D hD ho) = D.toProfile hD := by
  rcases beta_chain D hD with ⟨r01,r12,r23,r34,c01,c12,c23,c34,o01,o12,o23,o34⟩
  have ht := FiveOpening.openingLabel_nonneg D ho
  simp [FiveOpening.openingLabel,FiveOpening.openedRow,FiveOpening.openedCol] at ht
  apply Gluing.Profile.ext
  · funext i
    rw [toProfile_r]
    fin_cases i <;> simp [mProfile,middleParameters,Parameters.L] <;> omega
  · funext i
    rw [toProfile_g]
    fin_cases i <;> rfl

theorem end_profile_reconstruction (D : BetaDiagram 5) (hD : D.Connected)
    (ho : FiveOpening.HasOpening D 0) :
    eProfile (endParameters D) (endParameters_valid D hD ho) = D.toProfile hD := by
  rcases beta_chain D hD with ⟨r01,r12,r23,r34,c01,c12,c23,c34,o01,o12,o23,o34⟩
  have ht := FiveOpening.openingLabel_nonneg D ho
  simp [FiveOpening.openingLabel,FiveOpening.openedRow,FiveOpening.openedCol] at ht
  apply Gluing.Profile.ext
  · funext i
    rw [toProfile_r]
    fin_cases i <;> simp [eProfile,endParameters,Parameters.L] <;> omega
  · funext i
    rw [toProfile_g]
    fin_cases i <;> rfl

private theorem profile_translation (D : BetaDiagram 5) (hD : D.Connected) :
    D.TranslationEquivalent (D.toProfile hD).toBetaDiagram := by
  refine ⟨D.col 4,?_,?_⟩
  · intro i
    change D.row i = (D.toProfile hD).xi i + D.col 4
    rw [D.toProfile_xi hD]
    simp
  · intro i
    change D.col i = (D.toProfile hD).zeta i + D.col 4
    rw [D.toProfile_zeta hD]
    simp

theorem middle_reconstruction (D : BetaDiagram 5) (hD : D.Connected)
    (ho : FiveOpening.HasOpening D 1) :
    D.TranslationEquivalent (M (middleParameters D) (middleParameters_valid D hD ho)) := by
  unfold M
  rw [middle_profile_reconstruction D hD ho]
  exact profile_translation D hD

theorem end_reconstruction (D : BetaDiagram 5) (hD : D.Connected)
    (ho : FiveOpening.HasOpening D 0) :
    D.TranslationEquivalent (E (endParameters D) (endParameters_valid D hD ho)) := by
  unfold E
  rw [end_profile_reconstruction D hD ho]
  exact profile_translation D hD

/-- Rotate the other end opening to the orientation used by `E`. -/
theorem rotate_end_opening (D : BetaDiagram 5) (ho : FiveOpening.HasOpening D 2) :
    FiveOpening.HasOpening D.rotate 0 := by
  intro i j
  have hh := ho j.rev i.rev
  fin_cases i <;> fin_cases j <;>
    simp [BetaDiagram.rotate,FiveOpening.openedRow,FiveOpening.openedCol,Fin.rev] at hh ⊢ <;>
    omega

/-- Exhaustion is proved from the original negative count, not supplied as an oracle. -/
theorem normal_form_exhaustion (D : BetaDiagram 5) (hD : D.Connected)
    (hν : negativeCount D = 5) :
    (∃ t, ∃ h : ValidM t, D.TranslationEquivalent (M t h)) ∨
    (∃ t, ∃ h : ValidE t, D.TranslationEquivalent (E t h)) ∨
    (∃ t, ∃ h : ValidE t, D.rotate.TranslationEquivalent (E t h)) := by
  obtain ⟨k,ho⟩ := FiveOpening.opening_inventory D hD hν
  fin_cases k
  · exact Or.inr (Or.inl ⟨endParameters D,endParameters_valid D hD ho,
      end_reconstruction D hD ho⟩)
  · exact Or.inl ⟨middleParameters D,middleParameters_valid D hD ho,
      middle_reconstruction D hD ho⟩
  · have hr := D.rotate_connected hD
    have ho' := rotate_end_opening D ho
    exact Or.inr (Or.inr ⟨endParameters D.rotate,endParameters_valid D.rotate hr ho',
      end_reconstruction D.rotate hr ho'⟩)

/-- The actual two-row determinant for a binomial quadratic. -/
def quadraticDiagram (s z tau : ℕ) (hs : tau < s) (hz : tau < z) : BetaDiagram 2 where
  row := ![(z : ℤ) - tau + s,z]
  col := ![(z : ℤ) - tau,0]
  row_strictAnti := by
    rw [Fin.strictAnti_iff_succ_lt]
    intro i; fin_cases i; simp; omega
  col_strictAnti := by
    rw [Fin.strictAnti_iff_succ_lt]
    intro i; fin_cases i; simp; omega
  row_nonempty := by intro i; fin_cases i <;> simp <;> omega

theorem quadratic_connected (s z tau : ℕ) (hs : tau < s) (hz : tau < z) :
    (quadraticDiagram s z tau hs hz).Connected := by
  refine ⟨by decide,?_⟩
  intro i hi
  have hi0 : i = (0 : Fin 2) := by
    apply Fin.ext
    omega
  subst i
  change (z : ℤ) - tau ≤ z
  omega

private theorem hTilde_nat (k : ℕ) : Gluing.hTilde (k : ℤ) = (X k : Gluing.HomLambda) := by
  rw [Gluing.hTilde,if_neg (show ¬ (k : ℤ) < 0 by omega),Int.toNat_natCast]

theorem quadratic_homSchur (s z tau : ℕ) (hs : tau < s) (hz : tau < z) :
    (quadraticDiagram s z tau hs hz).homSchur = F s z tau := by
  have hm : (quadraticDiagram s z tau hs hz).homMatrix =
      !![Gluing.hTilde (s : ℤ), Gluing.hTilde ((z : ℤ) + s - tau);
        Gluing.hTilde (tau : ℤ), Gluing.hTilde (z : ℤ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [BetaDiagram.homMatrix,quadraticDiagram] <;> congr 1 <;> ring
  have htop : (z : ℤ) + s - tau = (z + s - tau : ℕ) := by omega
  rw [htop] at hm
  simp only [hTilde_nat] at hm
  rw [BetaDiagram.homSchur,hm,Matrix.det_fin_two]
  simp [F]
  ring

theorem F_irreducible (s z tau : ℕ) (hs : tau < s) (hz : tau < z) :
    Irreducible (F s z tau) := by
  rw [← quadratic_homSchur s z tau hs hz]
  exact (quadraticDiagram s z tau hs hz).homSchur_irreducible
    (quadratic_connected s z tau hs hz)

theorem B_eq_F (u v tau : ℕ) : B u v tau = F u v tau := by
  simp [B,F,Nat.add_comm]

theorem B_irreducible (u v tau : ℕ) (hu : tau < u) (hv : tau < v) :
    Irreducible (B u v tau) := by rw [B_eq_F]; exact F_irreducible u v tau hu hv

theorem T_eq_F (b p z : ℕ) (hb : p < b) : T b p z = F b z p := by
  have he : z + (b-p) = z+b-p := by omega
  simp [T,F,he]

theorem T_irreducible (b p z : ℕ) (hb : p < b) (hz : p < z) :
    Irreducible (T b p z) := by rw [T_eq_F b p z hb]; exact F_irreducible b z p hb hz

/-- Connected full-order determinants with at least two rows have no coordinate factor. -/
theorem homSchur_coordinate_not_dvd {n : ℕ} (D : BetaDiagram (n+2))
    (hD : D.Connected) (j : ℕ) : ¬ (X j : Gluing.HomLambda) ∣ D.homSchur := by
  rintro ⟨q,he⟩
  rcases (D.homSchur_irreducible hD).isUnit_or_isUnit he with hX | hq
  · have hd := (isUnit_iff_totalDegree_of_isReduced.mp hX).2
    rw [totalDegree_X] at hd
    omega
  · have hqdeg := (isUnit_iff_totalDegree_of_isReduced.mp hq).2
    have hd := totalDegree_mul (X j : Gluing.HomLambda) q
    rw [← he,D.homSchur_totalDegree,totalDegree_X,hqdeg] at hd
    omega

theorem F_coordinate_not_dvd (s z tau j : ℕ) (hs : tau < s) (hz : tau < z) :
    ¬ (X j : Gluing.HomLambda) ∣ F s z tau := by
  rw [← quadratic_homSchur s z tau hs hz]
  exact homSchur_coordinate_not_dvd _ (quadratic_connected s z tau hs hz) j

theorem B_coordinate_not_dvd (u v tau j : ℕ) (hu : tau < u) (hv : tau < v) :
    ¬ (X j : Gluing.HomLambda) ∣ B u v tau := by
  rw [B_eq_F]; exact F_coordinate_not_dvd u v tau j hu hv

theorem T_coordinate_not_dvd (b p z j : ℕ) (hb : p < b) (hz : p < z) :
    ¬ (X j : Gluing.HomLambda) ∣ T b p z := by
  rw [T_eq_F b p z hb]; exact F_coordinate_not_dvd b z p j hb hz

/-- The three-row Hessenberg profile, with its exact validity conditions. -/
def cubicProfile (r s t a p : ℕ) (ha : a < r) (hp : p < t)
    (hs : a+p < s) : Gluing.Profile 2 where
  r := ![r,s,t]
  g := ![a,p]
  r_pos := by intro i; fin_cases i <;> simp <;> omega
  g_lt_castSucc := by intro i; fin_cases i <;> simp <;> omega
  g_lt_succ := by intro i; fin_cases i <;> simp <;> omega

noncomputable def cubic (r s t a p : ℕ) : Gluing.HomLambda :=
  X r * X s * X t - X a * X (s+r-a) * X t -
    X r * X p * X (t+s-p) + X a * X p * X (t+s+r-p-a)

theorem cubic_homSchur (r s t a p : ℕ) (ha : a < r) (hp : p < t)
    (hs : a+p < s) :
    (cubicProfile r s t a p ha hp hs).toBetaDiagram.homSchur = cubic r s t a p := by
  have hm : (cubicProfile r s t a p ha hp hs).toBetaDiagram.homMatrix =
      !![Gluing.hTilde (r : ℤ), Gluing.hTilde ((s : ℤ) + r - a),
          Gluing.hTilde ((t : ℤ) + s + r - p - a);
        Gluing.hTilde (a : ℤ), Gluing.hTilde (s : ℤ),
          Gluing.hTilde ((t : ℤ) + s - p);
        Gluing.hTilde ((a : ℤ) + p - s), Gluing.hTilde (p : ℤ), Gluing.hTilde (t : ℤ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [BetaDiagram.homMatrix,Gluing.Profile.toBetaDiagram,Gluing.Profile.xi,
        Gluing.Profile.zeta,cubicProfile,Fin.sum_univ_succ] <;> congr 1 <;> ring
  have h1 : (s : ℤ) + r - a = (s + r - a : ℕ) := by omega
  have h2 : (t : ℤ) + s - p = (t + s - p : ℕ) := by omega
  have h3 : (t : ℤ) + s + r - p - a = (t + s + r - p - a : ℕ) := by omega
  have hn : (a : ℤ) + p - s < 0 := by omega
  rw [h1,h2,h3] at hm
  simp only [hTilde_nat] at hm
  simp only [Gluing.hTilde,if_pos hn] at hm
  rw [BetaDiagram.homSchur,hm,Matrix.det_fin_three]
  simp [cubic]
  ring

theorem cubic_irreducible (r s t a p : ℕ) (ha : a < r) (hp : p < t)
    (hs : a+p < s) : Irreducible (cubic r s t a p) := by
  rw [← cubic_homSchur r s t a p ha hp hs]
  exact BetaDiagram.homSchur_irreducible _ (Gluing.Profile.toBetaDiagram_connected _)

theorem G_eq_cubic (s tau b p z : ℕ) (hs : tau < s) (hb : p < b)
    (hz : tau+p < z) : G s tau b p z = cubic s z b tau p := by
  have h1 : z+s-tau+(b-p) = b+z+s-p-tau := by omega
  have h2 : z+(b-p) = b+z-p := by omega
  simp [G,T,cubic,h1,h2]
  ring

theorem Q_eq_cubic (x a s tau z : ℕ) (hx : a < x) (hs : tau < s)
    (hz : a+tau < z) : Q x a s tau z = cubic x z s a tau := by
  have h1 : z+x-a+s-tau = s+z+x-tau-a := by omega
  have h2 : z+s-tau = s+z-tau := by omega
  simp [Q,F,cubic,h1,h2]
  ring

/-- Only the original middle inequalities are used to produce the connected cubic. -/
theorem M_G_irreducible (t : Parameters) (h : ValidM t) :
    Irreducible (G t.u t.tau t.b t.p t.c) := by
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  rw [G_eq_cubic _ _ _ _ _ hu hb (by omega)]
  exact cubic_irreducible _ _ _ _ _ hu hb (by omega)

theorem M_Q_irreducible (t : Parameters) (h : ValidM t) :
    Irreducible (Q t.x t.a t.v t.tau t.y) := by
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  rw [Q_eq_cubic _ _ _ _ _ hx hv (by omega)]
  exact cubic_irreducible _ _ _ _ _ hx hv (by omega)

theorem F_totalDegree (s z tau : ℕ) (hs : tau<s) (hz : tau<z) :
    (F s z tau).totalDegree = 2 := by
  rw [← quadratic_homSchur s z tau hs hz]
  exact BetaDiagram.homSchur_totalDegree _

theorem B_totalDegree (u v tau : ℕ) (hu : tau<u) (hv : tau<v) :
    (B u v tau).totalDegree = 2 := by
  rw [B_eq_F]; exact F_totalDegree u v tau hu hv

theorem opening_negativeCount (D : BetaDiagram 5) (k : Fin 3)
    (ho : FiveOpening.HasOpening D k) : negativeCount D = 5 := by
  classical
  have hs : negativeSites D = Finset.univ.filter (fun z : Fin 5 × Fin 5 =>
      z.2.val+1<z.1.val ∧
        ¬ (z.1=FiveOpening.openedRow k ∧ z.2=FiveOpening.openedCol k)) := by
    ext z
    simp [negativeSites,ho z.1 z.2]
  unfold negativeCount
  rw [hs]
  fin_cases k <;> decide

theorem M_negativeCount (t : Parameters) (h : ValidM t) : negativeCount (M t h)=5 :=
  opening_negativeCount _ 1 (M_opening t h)

theorem E_negativeCount (t : Parameters) (h : ValidE t) : negativeCount (E t h)=5 :=
  opening_negativeCount _ 0 (E_opening t h)

/-- The connected three-row child `(u,c,b; tau,p)` of an actual middle board. -/
def gDiagramM (t : Parameters) (h : ValidM t) : BetaDiagram 3 :=
  (cubicProfile t.u t.c t.b t.tau t.p h.1 h.2.2.1 (by
    rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
    omega)).toBetaDiagram

/-- The connected three-row child `(x,y,v; a,tau)` of an actual middle board. -/
def qDiagramM (t : Parameters) (h : ValidM t) : BetaDiagram 3 :=
  (cubicProfile t.x t.y t.v t.a t.tau h.2.2.2.1 h.2.1 (by
    rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
    omega)).toBetaDiagram

theorem M_G_determinant (t : Parameters) (h : ValidM t) :
    (gDiagramM t h).homSchur=G t.u t.tau t.b t.p t.c := by
  unfold gDiagramM
  rw [cubic_homSchur]
  symm
  apply G_eq_cubic _ _ _ _ _ h.1 h.2.2.1
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  omega

theorem M_Q_determinant (t : Parameters) (h : ValidM t) :
    (qDiagramM t h).homSchur=Q t.x t.a t.v t.tau t.y := by
  unfold qDiagramM
  rw [cubic_homSchur]
  symm
  apply Q_eq_cubic _ _ _ _ _ h.2.2.2.1 h.2.1
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  omega

theorem M_G_coordinate_not_dvd (t : Parameters) (h : ValidM t) (j : ℕ) :
    ¬ (X j : Gluing.HomLambda) ∣ G t.u t.tau t.b t.p t.c := by
  rw [← M_G_determinant t h]
  exact homSchur_coordinate_not_dvd _ (Gluing.Profile.toBetaDiagram_connected _) j

theorem M_Q_coordinate_not_dvd (t : Parameters) (h : ValidM t) (j : ℕ) :
    ¬ (X j : Gluing.HomLambda) ∣ Q t.x t.a t.v t.tau t.y := by
  rw [← M_Q_determinant t h]
  exact homSchur_coordinate_not_dvd _ (Gluing.Profile.toBetaDiagram_connected _) j

end SkewJacobiNegative.FiveNegative
