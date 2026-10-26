/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewJacobiNegative.ExceptionalFiveResponses
import SkewJacobiNegative.SingletonContexts
import SkewJacobiNegative.TenNegativeFamilies
import SkewJacobiNegative.SingletonLift
import SkewJacobiNegative.FiveOpeningComparisons

namespace SkewJacobiNegative.FiveExceptional
open scoped BigOperators

private theorem labelDerivative_congr {k l : ℤ} (hk : 0 < k) (hl : 0 < l)
    (he : k=l) (p : CompleteRing) : labelDerivative k hk p=labelDerivative l hl p := by
  cases he
  rfl
/-- The exceptional singleton locus gives legal seven-row family parameters. -/
def singletonTenParameters (P : Parameters) (hp : P.q < P.b) : TenParameters where
  a := P.q
  b := P.g
  d := P.b - P.q
  a_pos := P.q_pos
  d_nonneg := by omega
  separated := by have := P.b_lt_g; omega

/-- Coordinate form of the interface tie at the exceptional locus. -/
theorem exceptional_interface_tie (P : Parameters) :
    P.g = ((P.b - P.q) + (P.g - P.b)) + P.q := by omega

/-- Once the surviving coordinate monomials identify the singleton length,
all four margins are forced, rather than merely their sum. -/
theorem singleton_locus_of_surviving_coordinates
    (P : Parameters) (s u v g : ℤ)
    (hu : u = P.q) (hv : v = P.g)
    (htie : v = s + g + u) (hs : s = P.b - P.q) :
    (s,u,v,g) = (P.b-P.q,P.q,P.g,P.g-P.b) := by
  have hg : g = P.g - P.b := by omega
  simp [hs, hu, hv, hg]

/-- Every point of the stated locus satisfies all positive-margin hypotheses. -/
theorem singleton_locus_positive (P : Parameters) (hp : P.q < P.b) :
    0 < P.b-P.q ∧ 0 < P.q ∧ 0 < P.g ∧ 0 < P.g-P.b := by
  have := P.q_pos
  have := P.b_lt_g
  omega

/-- The genuine seven-row singleton parent at the exceptional locus. -/
def exceptionalSingleton (P : Parameters) (hp : P.q < P.b) (second : Bool)
    (middle : Bool) : BetaDiagram 7 :=
  let Q := if middle then (F P second).rotate else (H P second).rotate
  Q.singletonContext (P.b-P.q) P.q P.g (P.g-P.b)
    (singleton_locus_positive P hp).1
    (singleton_locus_positive P hp).2.1
    (singleton_locus_positive P hp).2.2.1
    (singleton_locus_positive P hp).2.2.2

/-- Exact resolution of the first family's mixed three-row multiset equation. -/
theorem mixed_rows_first (P : Parameters) (A v : ℤ)
    (h : ({A+P.g, 3*P.g-P.q, v} : Multiset ℤ) =
      {A, 2*P.g, 2*P.g-P.q+v}) :
    (A = P.g ∧ v = P.g) ∨ (A = 3*P.g-P.q ∧ v = 2*P.g) := by
  have hq := P.q_pos
  have hqg : P.q < P.g := lt_of_le_of_lt P.q_le_b P.b_lt_g
  have hc : 3*P.g-P.q ∈ ({A, 2*P.g, 2*P.g-P.q+v} : Multiset ℤ) := by
    rw [← h]
    simp
  have hl : A+P.g ∈ ({A, 2*P.g, 2*P.g-P.q+v} : Multiset ℤ) := by
    rw [← h]
    simp
  have hv : v ∈ ({A, 2*P.g, 2*P.g-P.q+v} : Multiset ℤ) := by
    rw [← h]
    simp
  have hc : 3*P.g-P.q=A ∨ 3*P.g-P.q=2*P.g ∨ 3*P.g-P.q=2*P.g-P.q+v := by simpa using hc
  have hl : A+P.g=A ∨ A+P.g=2*P.g ∨ A+P.g=2*P.g-P.q+v := by simpa using hl
  have hv : v=A ∨ v=2*P.g ∨ v=2*P.g-P.q+v := by simpa using hv
  rcases hc with hc | hc | hc
  · right
    constructor
    · omega
    · rcases hl with hl | hl | hl <;> omega
  · omega
  · left
    constructor
    · rcases hv with hv | hv | hv <;> omega
    · omega

/-- Exact resolution of the second family's mixed three-row multiset equation. -/
theorem mixed_rows_second (P : Parameters) (A v : ℤ)
    (h : ({A+P.g-P.q, 3*P.g-P.q, v} : Multiset ℤ) =
      {A, 2*P.g-P.q, 2*P.g-P.q+v}) :
    (A = P.g ∧ v = P.g) ∨
      (A = 3*P.g-P.q ∧ v = 2*P.g-P.q) := by
  have hq := P.q_pos
  have hqg : P.q < P.g := lt_of_le_of_lt P.q_le_b P.b_lt_g
  have hc : 3*P.g-P.q ∈ ({A, 2*P.g-P.q, 2*P.g-P.q+v} : Multiset ℤ) := by
    rw [← h]
    simp
  have hl : A+P.g-P.q ∈ ({A, 2*P.g-P.q, 2*P.g-P.q+v} : Multiset ℤ) := by
    rw [← h]
    simp
  have hv : v ∈ ({A, 2*P.g-P.q, 2*P.g-P.q+v} : Multiset ℤ) := by
    rw [← h]
    simp
  have hc : 3*P.g-P.q=A ∨ 3*P.g-P.q=2*P.g-P.q ∨ 3*P.g-P.q=2*P.g-P.q+v := by simpa using hc
  have hl : A+P.g-P.q=A ∨ A+P.g-P.q=2*P.g-P.q ∨ A+P.g-P.q=2*P.g-P.q+v := by simpa using hl
  have hv : v=A ∨ v=2*P.g-P.q ∨ v=2*P.g-P.q+v := by simpa using hv
  rcases hc with hc | hc | hc
  · right
    constructor
    · omega
    · rcases hl with hl | hl | hl <;> omega
  · omega
  · left
    constructor
    · rcases hv with hv | hv | hv <;> omega
    · omega

/-- Both mixed alternatives in the third row of the context table are inadmissible. -/
theorem mixed_rows_impossible (P : Parameters) (A v u : ℤ)
    (hu : 0 < u) (ht : v = A+u) (second : Bool)
    (h : if second then
        ({A+P.g-P.q, 3*P.g-P.q, v} : Multiset ℤ) =
          {A, 2*P.g-P.q, 2*P.g-P.q+v}
      else
        ({A+P.g, 3*P.g-P.q, v} : Multiset ℤ) =
          {A, 2*P.g, 2*P.g-P.q+v}) : False := by
  have hqg : P.q < P.g := lt_of_le_of_lt P.q_le_b P.b_lt_g
  have hq := P.q_pos
  cases second
  · obtain h | h := mixed_rows_first P A v h <;> rcases h with ⟨hA,hv⟩ <;> omega
  · obtain h | h := mixed_rows_second P A v h <;> rcases h with ⟨hA,hv⟩ <;> omega

private noncomputable def zeroAt (k : ℤ) : CompleteRing →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ)
    (fun v => if (v.val : ℤ) = k then 0 else 1)

private theorem zeroAt_complete (k l : ℤ) (hl : 0 < l) :
    zeroAt k (complete l) = if l = k then 0 else 1 := by
  let v : ℕ+ := ⟨l.toNat,by omega⟩
  have he : complete l=MvPolynomial.X v := complete_of_pos hl
  rw [he]
  unfold zeroAt
  rw [MvPolynomial.eval₂Hom_X']
  change (if (v.val : ℤ)=k then (0 : ℚ) else 1)=_
  rw [show (v.val : ℤ)=l from Int.toNat_of_nonneg hl.le]

private theorem zeroAt_eq_one (k l : ℤ) (hl : 0 < l) (hne : l≠k) :
    zeroAt k (complete l)=1 := by
  rw [zeroAt_complete k l hl,if_neg hne]

private theorem zeroAt_eq_zero (k : ℤ) (hk : 0 < k) : zeroAt k (complete k)=0 := by
  rw [zeroAt_complete k k hk,if_pos rfl]

/-- The surviving coordinate-monomial equality forces precisely the singleton length. -/
theorem singleton_length_of_coordinate_equality (P : Parameters) (hp : P.q < P.b)
    (s : ℤ) (hs : 0 < s)
    (he : complete (s+P.q) * complete (P.b-P.q) =
      complete s * complete P.b) : s = P.b-P.q := by
  have hq := P.q_pos
  by_contra hn
  have hsqp : s+P.q ≠ P.b := by omega
  have hbqp : P.b-P.q ≠ P.b := by omega
  have hleft : zeroAt P.b (complete (s+P.q) * complete (P.b-P.q)) = 1 := by
    rw [map_mul, zeroAt_complete _ _ (by omega), zeroAt_complete _ _ (by omega)]
    simp [hsqp, hbqp]
  have hright : zeroAt P.b (complete s * complete P.b) = 0 := by
    rw [map_mul, zeroAt_complete _ _ hs, zeroAt_complete _ _ (by omega)]
    simp
  have h := congrArg (zeroAt P.b) he
  rw [hleft, hright] at h
  norm_num at h

/-- Cancellation of the nonzero response determinant yields the exact exceptional locus. -/
theorem singleton_locus_of_interface_zero (P : Parameters) (hp : P.q < P.b)
    (s u v g : ℤ) (hs : 0 < s) (hu : u = P.q) (hv : v = P.g)
    (htie : v = s+g+u) (second : Bool)
    (he : (if second then D2 P else D1 P) *
      (complete (s+P.q)*complete (P.b-P.q) - complete s*complete P.b) = 0) :
    (s,u,v,g) = (P.b-P.q,P.q,P.g,P.g-P.b) := by
  have hd : (if second then D2 P else D1 P) ≠ 0 := by
    cases second
    · exact (D_ne_zero P hp).1
    · exact (D_ne_zero P hp).2
  have hc := (mul_eq_zero.mp he).resolve_left hd
  have hlength := singleton_length_of_coordinate_equality P hp s hs (sub_eq_zero.mp hc)
  exact singleton_locus_of_surviving_coordinates P s u v g hu hv htie hlength

/-- The reverse mixed pairing has exactly the admissible first-family parameter triple. -/
theorem reverse_mixed_first_parameters (P : Parameters) (A v u : ℤ)
    (hu : 0 < u) (ht : v = A+u)
    (h : ({v+P.g, 3*P.g-P.q, A} : Multiset ℤ) =
      {v, 2*P.g, 2*P.g-P.q+A}) :
    (A,v,u) = (2*P.g,3*P.g-P.q,P.g-P.q) := by
  obtain h | h := mixed_rows_first P v A h
  · rcases h with ⟨hv,hA⟩
    omega
  · rcases h with ⟨hv,hA⟩
    have huu : u = P.g-P.q := by omega
    simp [hv,hA,huu]

/-- The second family's reverse mixed pairing has the stated unique parameter triple. -/
theorem reverse_mixed_second_parameters (P : Parameters) (A v u : ℤ)
    (hu : 0 < u) (ht : v = A+u)
    (h : ({v+P.g-P.q, 3*P.g-P.q, A} : Multiset ℤ) =
      {v, 2*P.g-P.q, 2*P.g-P.q+A}) :
    (A,v,u) = (2*P.g-P.q,3*P.g-P.q,P.g) := by
  obtain h | h := mixed_rows_second P v A h
  · rcases h with ⟨hv,hA⟩
    omega
  · rcases h with ⟨hv,hA⟩
    have huu : u = P.g := by omega
    simp [hv,hA,huu]

private noncomputable def allOnes : CompleteRing →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun _ => 1)

private theorem allOnes_complete (k : ℤ) (hk : 0 < k) : allOnes (complete k) = 1 := by
  let v : ℕ+ := ⟨k.toNat,by omega⟩
  have he : complete k=MvPolynomial.X v := complete_of_pos hk
  rw [he]
  unfold allOnes
  exact MvPolynomial.eval₂Hom_X' _ _ v

/-- The unrotated interface coefficient cannot vanish at its forced parameter tie. -/
theorem unrotated_interface_coefficient_ne_zero (P : Parameters) (hp : P.q < P.b)
    (s : ℤ) (hs : 0 < s) (second : Bool) :
    -(if second then D2 P else D1 P) *
      (complete (s+P.q)*complete (P.b-P.q) + complete s*complete P.b) ≠ 0 := by
  have hq := P.q_pos
  apply mul_ne_zero
  · apply neg_ne_zero.mpr
    cases second
    · exact (D_ne_zero P hp).1
    · exact (D_ne_zero P hp).2
  · intro hz
    have he := congrArg allOnes hz
    simp only [map_add, map_mul, map_zero,
      allOnes_complete (s+P.q) (by omega),
      allOnes_complete (P.b-P.q) (by omega),
      allOnes_complete s hs, allOnes_complete P.b (by omega)] at he
    norm_num at he

private theorem zeroAt_response_values (P : Parameters) (hp : P.q < P.b) :
    zeroAt (P.b+2*P.g-P.q) (D2 P) = -1 ∧
    zeroAt (P.b+2*P.g-P.q) (W P) = 0 ∧
    zeroAt (P.b+P.g-P.q) (D2 P) = 0 ∧
    zeroAt (P.b+P.g-P.q) (W P) = -1 := by
  have hq := P.q_pos
  have hg := P.b_lt_g
  have hqb := P.q_le_b
  have hp0 : 0 < P.b := by omega
  have hb0 : 0 < P.b-P.q := by omega
  have hp1 : 0 < P.b+P.g := by omega
  have hb1 : 0 < P.b+P.g-P.q := by omega
  have hp2 : 0 < P.b+2*P.g := by omega
  have hb2 : 0 < P.b+2*P.g-P.q := by omega
  have h20 := zeroAt_eq_one (P.b+2*P.g-P.q) P.b hp0 (by omega)
  have h2b0 := zeroAt_eq_one (P.b+2*P.g-P.q) (P.b-P.q) hb0 (by omega)
  have h21 := zeroAt_eq_one (P.b+2*P.g-P.q) (P.b+P.g) hp1 (by omega)
  have h2b1 := zeroAt_eq_one (P.b+2*P.g-P.q) (P.b+P.g-P.q) hb1 (by omega)
  have h22 := zeroAt_eq_one (P.b+2*P.g-P.q) (P.b+2*P.g) hp2 (by omega)
  have h2b2 := zeroAt_eq_zero (P.b+2*P.g-P.q) hb2
  have h10 := zeroAt_eq_one (P.b+P.g-P.q) P.b hp0 (by omega)
  have h1b0 := zeroAt_eq_one (P.b+P.g-P.q) (P.b-P.q) hb0 (by omega)
  have h11 := zeroAt_eq_one (P.b+P.g-P.q) (P.b+P.g) hp1 (by omega)
  have h1b1 := zeroAt_eq_zero (P.b+P.g-P.q) hb1
  have h12 := zeroAt_eq_one (P.b+P.g-P.q) (P.b+2*P.g) hp2 (by omega)
  have h1b2 := zeroAt_eq_one (P.b+P.g-P.q) (P.b+2*P.g-P.q) hb2 (by omega)
  simp only [D2,W,map_sub,map_add,map_mul,map_pow,h20,h2b0,h21,h2b1,h22,h2b2,
    h10,h1b0,h11,h1b1,h12,h1b2]
  norm_num

/-- The reverse second-family comparison is nonzero for every positive singleton length,
including the resonant length singled out in the manuscript. -/
theorem reverse_second_interface_ne_zero (P : Parameters) (hp : P.q < P.b)
    (s : ℤ) (hs : 0 < s) :
    complete s * D2 P - complete (s+P.g)*complete (P.b-P.q)*W P ≠ 0 := by
  have hq := P.q_pos
  have hg := P.b_lt_g
  have hqb := P.q_le_b
  obtain ⟨hd2, hw2, hd1, hw1⟩ := zeroAt_response_values P hp
  intro hz
  by_cases he : s = P.b+2*P.g-P.q
  · have h := congrArg (zeroAt (P.b+P.g-P.q)) hz
    simp only [map_sub, map_mul, map_zero, hd1, hw1,
      zeroAt_complete _ s hs,
      zeroAt_complete _ (s+P.g) (by omega),
      zeroAt_complete _ (P.b-P.q) (by omega)] at h
    split_ifs at h <;> first | omega | norm_num at h
  · have h := congrArg (zeroAt (P.b+2*P.g-P.q)) hz
    simp only [map_sub, map_mul, map_zero, hd2, hw2,
      zeroAt_complete _ s hs, if_neg he] at h
    norm_num at h

/-- Which seven-row representative corresponds to the rotated exceptional core. -/
def singletonTenKind (second middle : Bool) : TenKind :=
  if second then (if middle then .ha else .fa) else (if middle then .hb else .fb)

private theorem context_rows (Q : BetaDiagram 5) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).row =
      ![Q.row 0+v+g+s+u,Q.row 0+v+g+s,v+Q.row 0,v+Q.row 1,
        v+Q.row 2,v+Q.row 3,v+Q.row 4] := by
  funext i
  cases i using Fin.cases with
  | zero =>
    simpa only [Matrix.cons_val_zero] using Q.singletonContext_row_zero s u v g hs hu hv hg
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      simpa only [Matrix.cons_val_succ,Matrix.cons_val_zero] using
        Q.singletonContext_row_one s u v g hs hu hv hg
    | succ i =>
      rw [BetaDiagram.singletonContext_row_core]
      fin_cases i <;> norm_num [Matrix.cons_val]

private theorem context_cols (Q : BetaDiagram 5) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).col =
      ![v+Q.row 0+g,v+Q.col 0,v+Q.col 1,v+Q.col 2,v+Q.col 3,v+Q.col 4,Q.col 4] := by
  funext i
  cases i using Fin.lastCases with
  | last =>
    rw [BetaDiagram.singletonContext_col_last]
    norm_num [Fin.last,Matrix.cons_val]
  | cast i =>
    cases i using Fin.cases with
    | zero =>
      simpa only [Fin.castSucc_zero,Matrix.cons_val_zero] using
        Q.singletonContext_col_zero s u v g hs hu hv hg
    | succ i =>
      rw [BetaDiagram.singletonContext_col_core]
      fin_cases i <;> norm_num [Fin.castSucc,Matrix.cons_val]

private theorem context_row_lengths (Q : BetaDiagram 5) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).rowLength =
      ![s+u,s+g+Q.row 0-Q.col 0,Q.row 0-Q.col 1,Q.row 1-Q.col 2,
        Q.row 2-Q.col 3,Q.row 3-Q.col 4,v+Q.row 4-Q.col 4] := by
  funext i
  change (Q.singletonContext s u v g hs hu hv hg).row i-
    (Q.singletonContext s u v g hs hu hv hg).col i=_
  rw [context_rows,context_cols]
  fin_cases i <;> norm_num [Matrix.cons_val] <;> ring

private theorem list7_as_sum {α : Type*} (a b c d e f g : α) :
    (([a,b,c,d,e,f,g] : List α) : Multiset α) =
      {a}+{b}+{c}+{d}+{e}+{f}+{g} := rfl

private theorem context_shifted_rows (Q : BetaDiagram 5) (p s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (List.ofFn (Q.singletonContext s u v g hs hu hv hg).rowLength : Multiset ℤ).map
      (fun x => x-p) =
      ([s+u-p,s+g+Q.row 0-Q.col 0-p,Q.row 0-Q.col 1-p,Q.row 1-Q.col 2-p,
        Q.row 2-Q.col 3-p,Q.row 3-Q.col 4-p,v+Q.row 4-Q.col 4-p] : List ℤ) := by
  rw [context_row_lengths]
  simp only [Multiset.map_coe,List.map_ofFn]
  norm_num [List.ofFn_succ,Function.comp_def,Matrix.cons_val]

private theorem sum_fin_seven {R : Type*} [AddCommMonoid R] (f : Fin 7 → R) :
    (∑ i, f i)=f 0+(f 1+(f 2+(f 3+(f 4+(f 5+f 6))))) := by
  norm_num [Fin.sum_univ_succ]

set_option maxHeartbeats 0 in
/-- Literal beta-list correspondence at the exceptional singleton locus. -/
theorem exceptionalSingleton_translation (P : Parameters) (hp : P.q < P.b)
    (second middle : Bool) :
    (exceptionalSingleton P hp second middle).TranslationEquivalent
      ((singletonTenParameters P hp).diagram (singletonTenKind second middle)) := by
  obtain ⟨hs,hu,hv,hg⟩ := singleton_locus_positive P hp
  let Q := if middle then (F P second).rotate else (H P second).rotate
  have hrow := context_rows Q (P.b-P.q) P.q P.g (P.g-P.b) hs hu hv hg
  have hcol := context_cols Q (P.b-P.q) P.q P.g (P.g-P.b) hs hu hv hg
  refine ⟨-(P.b+4*P.g),?_,?_⟩
  · intro i
    change (Q.singletonContext (P.b-P.q) P.q P.g (P.g-P.b) hs hu hv hg).row i=_
    rw [hrow]
    cases second <;> cases middle <;> fin_cases i <;>
      norm_num [Q,singletonTenParameters,singletonTenKind,BetaDiagram.rotate,
        TenParameters.diagram,TenParameters.rowBase,TenParameters.column,F,H,rows,fCols,hCols,
        Fin.rev,Matrix.cons_val] <;> ring
  · intro i
    change (Q.singletonContext (P.b-P.q) P.q P.g (P.g-P.b) hs hu hv hg).col i=_
    rw [hcol]
    cases second <;> cases middle <;> fin_cases i <;>
      norm_num [Q,singletonTenParameters,singletonTenKind,BetaDiagram.rotate,
        TenParameters.diagram,TenParameters.rowBase,TenParameters.column,F,H,rows,fCols,hCols,
        Fin.rev,Matrix.cons_val] <;> ring

/-- Sufficiency is the actual seven-row family identity, not a classifier assumption. -/
theorem exceptionalSingleton_schur_eq (P : Parameters) (hp : P.q < P.b)
    (second : Bool) :
    (exceptionalSingleton P hp second true).schur =
      (exceptionalSingleton P hp second false).schur := by
  have hf := (exceptionalSingleton_translation P hp second true).schur_eq
  have hh := (exceptionalSingleton_translation P hp second false).schur_eq
  rw [hf, hh]
  cases second
  · exact (singletonTenParameters P hp).schur_eq_B.symm
  · exact (singletonTenParameters P hp).schur_eq_A.symm

theorem reflected_core_context_ne (P : Parameters) (hp : P.q < P.b)
    (second middle rotated : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    ((coreCandidate P second middle rotated).singletonContext s u v g hs hu hv hg).schur ≠
      ((coreCandidate P second middle rotated).rotate.singletonContext s u v g hs hu hv hg).schur :=
  BetaDiagram.singletonContext_reflected_core_ne _
    (coreCandidate_endpointLeader P hp second middle rotated) s u v g hs hu hv hg

private theorem row_multiset_of_schur_eq {n m : ℕ} (D : BetaDiagram n) (E : BetaDiagram m)
    (he : D.schur = E.schur) :
    (List.ofFn D.rowLength : Multiset ℤ) = (List.ofFn E.rowLength : Multiset ℤ) := by
  classical
  have hi := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [D.square_initial_monomial, E.square_initial_monomial] at hi
  have hx : D.diagonalExponent = E.diagonalExponent := by
    by_contra hn
    have hc := congrArg (fun p : CompleteRing => p.coeff D.diagonalExponent) hi
    simp [MvPolynomial.coeff_monomial, Ne.symm hn] at hc
  rw [D.diagonalExponent_eq_rowLengths, E.diagonalExponent_eq_rowLengths] at hx
  have hm := (Base.exponentVector_eq_iff _ _).mp hx
  unfold Base.positiveIndexMultiset at hm
  rw [Multiset.filter_eq_self.mpr D.rowLengthList_positive,
    Multiset.filter_eq_self.mpr E.rowLengthList_positive] at hm
  have hc := congrArg (Multiset.map (fun k : ℕ => (k : ℤ))) hm
  have hD : (fun i => ((D.rowLength i).toNat : ℤ)) = D.rowLength := by
    funext i
    exact Int.toNat_of_nonneg (D.rowLength_pos i).le
  have hE : (fun i => ((E.rowLength i).toNat : ℤ)) = E.rowLength := by
    funext i
    exact Int.toNat_of_nonneg (E.rowLength_pos i).le
  simpa only [Multiset.map_coe,List.map_ofFn,Function.comp_def,hD,hE] using hc

private theorem row_square_sum_of_schur_eq {n m : ℕ}
    (D : BetaDiagram n) (E : BetaDiagram m) (he : D.schur = E.schur) :
    (∑ i, D.rowLength i ^ 2) = ∑ i, E.rowLength i ^ 2 := by
  have hm := row_multiset_of_schur_eq D E he
  have hc := congrArg (fun xs : Multiset ℤ => (xs.map (fun k => k^2)).sum) hm
  simpa only [Multiset.map_coe,Multiset.sum_coe,List.map_ofFn,List.sum_ofFn,Function.comp_def] using hc

set_option maxHeartbeats 0 in
/-- Actual row-square invariance forces the unrotated exceptional interface to `A=G`. -/
theorem unrotated_context_row_condition (P : Parameters) (second : Bool)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (he : ((F P second).singletonContext s u v g hs hu hv hg).schur =
      ((H P second).singletonContext s u v g hs hu hv hg).schur) : s+g = P.g := by
  have hq := P.q_pos
  have hqg : P.q < P.g := lt_of_le_of_lt P.q_le_b P.b_lt_g
  have hc := row_square_sum_of_schur_eq _ _ he
  rw [context_row_lengths,context_row_lengths,sum_fin_seven,sum_fin_seven] at hc
  cases second
  · norm_num [F,H,rows,fCols,hCols,Matrix.cons_val] at hc
    have hprod : (s+g-P.g)*(P.g-P.q)=0 := by nlinarith [hc]
    have hzero := (mul_eq_zero.mp hprod).resolve_right (by omega)
    omega
  · norm_num [F,H,rows,fCols,hCols,Matrix.cons_val] at hc
    have hprod : (s+g-P.g)*P.g=0 := by nlinarith [hc]
    have hzero := (mul_eq_zero.mp hprod).resolve_right (by omega)
    omega

set_option maxHeartbeats 0 in
/-- The rotated pair's actual row invariant instead forces `v=G`. -/
theorem rotated_context_row_condition (P : Parameters) (second : Bool)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (he : ((F P second).rotate.singletonContext s u v g hs hu hv hg).schur =
      ((H P second).rotate.singletonContext s u v g hs hu hv hg).schur) : v = P.g := by
  have hq := P.q_pos
  have hqg : P.q < P.g := lt_of_le_of_lt P.q_le_b P.b_lt_g
  have hc := row_square_sum_of_schur_eq _ _ he
  rw [context_row_lengths,context_row_lengths,sum_fin_seven,sum_fin_seven] at hc
  cases second
  · norm_num [BetaDiagram.rotate,F,H,rows,fCols,hCols,Fin.rev,Matrix.cons_val] at hc
    have hprod : (v-P.g)*(P.g-P.q)=0 := by nlinarith [hc]
    have hzero := (mul_eq_zero.mp hprod).resolve_right (by omega)
    omega
  · norm_num [BetaDiagram.rotate,F,H,rows,fCols,hCols,Fin.rev,Matrix.cons_val] at hc
    have hprod : (v-P.g)*P.g=0 := by nlinarith [hc]
    have hzero := (mul_eq_zero.mp hprod).resolve_right (by omega)
    omega

set_option maxHeartbeats 0 in
/-- The mixed three-entry equations are recovered from the actual parent row multisets. -/
theorem mixed_context_row_condition (P : Parameters) (second : Bool)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (he : ((F P second).singletonContext s u v g hs hu hv hg).schur =
      ((H P second).rotate.singletonContext s u v g hs hu hv hg).schur) :
    if second then
      ({s+g+P.g-P.q,3*P.g-P.q,v} : Multiset ℤ) =
        {s+g,2*P.g-P.q,2*P.g-P.q+v}
    else
      ({s+g+P.g,3*P.g-P.q,v} : Multiset ℤ) =
        {s+g,2*P.g,2*P.g-P.q+v} := by
  have hr := row_multiset_of_schur_eq _ _ he
  have hm := congrArg (Multiset.map (fun k : ℤ => k-P.b)) hr
  let common : Multiset ℤ := {s+u-P.b,P.g,2*P.g,2*P.g-P.q}
  let left : Multiset ℤ := {s+g+P.g-(if second then P.q else 0),3*P.g-P.q,v}
  let right : Multiset ℤ := {s+g,2*P.g-(if second then P.q else 0),2*P.g-P.q+v}
  have hLeft : common+left=
      (List.ofFn ((F P second).singletonContext s u v g hs hu hv hg).rowLength : Multiset ℤ).map
        (fun k => k-P.b) := by
    rw [context_shifted_rows]
    cases second <;>
      norm_num [common,left,F,rows,fCols,Matrix.cons_val] <;>
      ring_nf <;>
      (conv_rhs => rw [list7_as_sum]) <;>
      simp only [←Multiset.singleton_add,add_zero] <;> ac_rfl
  have hRight : common+right=
      (List.ofFn ((H P second).rotate.singletonContext s u v g hs hu hv hg).rowLength : Multiset ℤ).map
        (fun k => k-P.b) := by
    rw [context_shifted_rows]
    cases second <;>
      norm_num [common,right,BetaDiagram.rotate,H,rows,hCols,Fin.rev,Matrix.cons_val] <;>
      ring_nf <;>
      (conv_rhs => rw [list7_as_sum]) <;>
      simp only [←Multiset.singleton_add,add_zero] <;> ac_rfl
  have hcancel : left=right := add_left_cancel (hLeft.trans (hm.trans hRight.symm))
  cases second <;> simpa only [left,right,Bool.false_eq_true,↓reduceIte,sub_zero] using hcancel

theorem mixed_context_ne_at_interface_tie (P : Parameters) (second : Bool)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (htie : v = s+g+u) :
    ((F P second).singletonContext s u v g hs hu hv hg).schur ≠
      ((H P second).rotate.singletonContext s u v g hs hu hv hg).schur := by
  intro he
  exact mixed_rows_impossible P (s+g) v u hu htie second
    (mixed_context_row_condition P second s u v g hs hu hv hg he)

/-- The actual interface coefficient, with no endpoint data supplied as a hypothesis. -/
noncomputable def interfaceResidual (Q R : BetaDiagram 5) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) : CompleteRing :=
  complete (s+u) * ((Q.extendTop (s+g) (by omega)).schur -
    (R.extendTop (s+g) (by omega)).schur) -
  complete s * (((Q.extendTop v hv).schur-(R.extendTop v hv).schur) +
    ((Q.extendBottom v hv).schur-(R.extendBottom v hv).schur))

noncomputable def borderPairDifference (Q R : BetaDiagram 5) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) : CompleteRing :=
  (Q.positiveBorder w v hw hv).schur-(R.positiveBorder w v hw hv).schur

private theorem borderPair_erased (Q R : BetaDiagram 5) (hspan : Q.largestLabel=R.largestLabel)
    (hcore : Q.schur=R.schur) (w v : ℤ) (hw : 0 < w) (hv : 0 < v) :
    borderPairDifference Q R w v hw hv =
      eraseGenerator (Q.positiveBorder w v hw hv).borderLargestGenerator
        (Q.positiveBorder w v hw hv).schur -
      eraseGenerator (R.positiveBorder w v hw hv).borderLargestGenerator
        (R.positiveBorder w v hw hv).schur := by
  have hN : (Q.positiveBorder w v hw hv).borderLargestGenerator =
      (R.positiveBorder w v hw hv).borderLargestGenerator := by
    apply Subtype.ext
    simp [BetaDiagram.borderLargestGenerator, hspan]
  rw [BetaDiagram.positiveBorder_erased_corner, BetaDiagram.positiveBorder_erased_corner]
  unfold borderPairDifference
  rw [BetaDiagram.positiveBorder_corner_split, BetaDiagram.positiveBorder_corner_split]
  rw [hcore, hN]
  ring

private theorem borderPair_labels (Q R : BetaDiagram 5) (hspan : Q.largestLabel=R.largestLabel)
    (hcore : Q.schur=R.schur) (w v : ℤ) (hw : 0 < w) (hv : 0 < v) :
    LabelsBelow (borderPairDifference Q R w v hw hv) (Q.largestLabel+max w v+1) := by
  rw [borderPair_erased Q R hspan hcore]
  apply LabelsBelow.sub
  · intro z hz
    have h := (Q.positiveBorder w v hw hv).vars_le_secondLabel z hz
    simp only [BetaDiagram.positiveBorder_secondLabel] at h
    omega
  · intro z hz
    have h := (R.positiveBorder w v hw hv).vars_le_secondLabel z hz
    simp only [BetaDiagram.positiveBorder_secondLabel, ← hspan] at h
    omega

private theorem borderPair_coefficient (Q R : BetaDiagram 5)
    (hspan : Q.largestLabel=R.largestLabel) (hcore : Q.schur=R.schur)
    (w v : ℤ) (hw : 0 < w) (hv : 0 < v) (hne : w ≠ v)
    (k : ℤ) (hk : 0 < k) (hkval : k = Q.largestLabel+max w v) :
    labelDerivative k hk (borderPairDifference Q R w v hw hv) =
      if w < v then (Q.extendTop w hw).schur-(R.extendTop w hw).schur
      else (Q.extendBottom v hv).schur-(R.extendBottom v hv).schur := by
  classical
  let z : ℕ+ := ⟨k.toNat,by omega⟩
  have hM : (Q.positiveBorder w v hw hv).borderSecondGenerator =
      (R.positiveBorder w v hw hv).borderSecondGenerator := by
    apply Subtype.ext
    simp [BetaDiagram.borderSecondGenerator,hspan]
  have hzM : z=(Q.positiveBorder w v hw hv).borderSecondGenerator := by
    apply Subtype.ext
    change k.toNat=_
    simp only [BetaDiagram.borderSecondGenerator,BetaDiagram.positiveBorder_secondLabel]
    congr 1
    omega
  rw [borderPair_erased Q R hspan hcore]
  change MvPolynomial.pderiv z (_-_) = _
  rw [map_sub]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [if_pos h]
    have hQ := Q.positiveBorder_top_coefficient w v hw hv h
    have hR := R.positiveBorder_top_coefficient w v hw hv h
    dsimp only at hQ hR
    have hQz := (congrArg (fun i : ℕ+ => MvPolynomial.pderiv i
      (eraseGenerator (Q.positiveBorder w v hw hv).borderLargestGenerator
        (Q.positiveBorder w v hw hv).schur)) hzM).trans hQ
    have hRz := (congrArg (fun i : ℕ+ => MvPolynomial.pderiv i
      (eraseGenerator (R.positiveBorder w v hw hv).borderLargestGenerator
        (R.positiveBorder w v hw hv).schur)) (hzM.trans hM)).trans hR
    rw [hQz,hRz]
    norm_num
  · rw [if_neg (by omega)]
    have hQ := Q.positiveBorder_bottom_coefficient w v hw hv h
    have hR := R.positiveBorder_bottom_coefficient w v hw hv h
    dsimp only at hQ hR
    have hQz := (congrArg (fun i : ℕ+ => MvPolynomial.pderiv i
      (eraseGenerator (Q.positiveBorder w v hw hv).borderLargestGenerator
        (Q.positiveBorder w v hw hv).schur)) hzM).trans hQ
    have hRz := (congrArg (fun i : ℕ+ => MvPolynomial.pderiv i
      (eraseGenerator (R.positiveBorder w v hw hv).borderLargestGenerator
        (R.positiveBorder w v hw hv).schur)) (hzM.trans hM)).trans hR
    rw [hQz,hRz]
    norm_num

private theorem context_pair_difference (Q R : BetaDiagram 5)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).schur -
      (R.singletonContext s u v g hs hu hv hg).schur =
      complete (s+u)*borderPairDifference Q R (s+g) v (by omega) hv -
        complete s*borderPairDifference Q R (s+g+u) v (by omega) hv := by
  rw [BetaDiagram.singletonContext_schur, BetaDiagram.singletonContext_schur]
  unfold borderPairDifference
  ring

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/PrivateEntries.lean
-- TODO-COPIED: skew-cofactor-independence/lean/SkewCofactorIndependence/PrivateEntries.lean
private theorem pderiv_exterior_pair (M : Matrix (Fin 6) (Fin 6) CompleteRing) (v : ℕ+)
    (ht : M 0 (Fin.last 4).castSucc=MvPolynomial.X v)
    (hb : M (0 : Fin 5).succ (Fin.last 5)=MvPolynomial.X v)
    (hprivate : ∀ a b,
      (a≠0 ∨ b≠(Fin.last 4).castSucc) →
      (a≠(0 : Fin 5).succ ∨ b≠Fin.last 5) →
      MvPolynomial.pderiv v (M a b)=0) :
    MvPolynomial.pderiv v M.det =
      (M.submatrix Fin.succ (Fin.last 4).castSucc.succAbove).det +
        (M.submatrix (1 : Fin 6).succAbove (Fin.last 5).succAbove).det := by
  classical
  let B (j : Fin 6) : Matrix (Fin 5) (Fin 5) CompleteRing := M.submatrix Fin.succ j.succAbove
  let C : Matrix (Fin 5) (Fin 5) CompleteRing :=
    M.submatrix (1 : Fin 6).succAbove (Fin.last 5).succAbove
  have hrow : ∀ j : Fin 6, MvPolynomial.pderiv v (M 0 j) =
      if j=(Fin.last 4).castSucc then 1 else 0 := by
    intro j
    by_cases hj : j=(Fin.last 4).castSucc
    · subst j
      rw [ht,MvPolynomial.pderiv_X_self,if_pos rfl]
    · rw [if_neg hj]
      exact hprivate 0 j (Or.inr hj) (Or.inl (by simp))
  have hminor_private : ∀ j : Fin 6, j≠Fin.last 5 →
      ∀ a b : Fin 5, a≠0 ∨ b≠Fin.last 4 →
      MvPolynomial.pderiv v (B j a b)=0 := by
    intro j hj a b hab
    apply hprivate a.succ (j.succAbove b) (Or.inl (Fin.succ_ne_zero a))
    rcases hab with ha | hb'
    · left
      intro he
      exact ha (Fin.succ_injective _ he)
    · right
      intro he
      have hl : j.succAbove (Fin.last 4)=Fin.last 5 := Fin.succAbove_ne_last_last hj
      exact hb' (Fin.succAbove_right_injective (he.trans hl.symm))
  have hminor_entry : ∀ j : Fin 6, j≠Fin.last 5 → B j 0 (Fin.last 4)=MvPolynomial.X v := by
    intro j hj
    have hl : j.succAbove (Fin.last 4)=Fin.last 5 := Fin.succAbove_ne_last_last hj
    simpa only [B,Matrix.submatrix_apply,hl] using hb
  have hlast_zero : MvPolynomial.pderiv v (B (Fin.last 5)).det=0 := by
    apply pderiv_det_eq_zero
    intro a b
    exact hprivate _ _ (Or.inl (Fin.succ_ne_zero a))
      (Or.inr (Fin.succAbove_ne _ _))
  have hminor : ∀ j : Fin 6, MvPolynomial.pderiv v (B j).det =
      if j=Fin.last 5 then 0 else
        ((B j).submatrix Fin.succ (Fin.last 4).succAbove).det := by
    intro j
    by_cases hj : j=Fin.last 5
    · subst j
      rw [hlast_zero,if_pos rfl]
    · rw [if_neg hj]
      have h := pderiv_det_private_of_derivative_zero (B j) v 0 (Fin.last 4)
        (hminor_entry j hj) (hminor_private j hj)
      have hzero : (0 : Fin 5).succAbove=(Fin.succ : Fin 4 → Fin 5) := by
        funext a
        exact Fin.zero_succAbove a
      rw [hzero] at h
      simpa only [Fin.val_zero,Fin.val_last,zero_add,
        show (-1 : CompleteRing)^4=1 by norm_num,one_mul] using h
  have hsign : ∀ j : Fin 6, MvPolynomial.pderiv v ((-1 : CompleteRing)^j.val)=0 := by
    intro j
    have hc : (-1 : CompleteRing)^j.val=MvPolynomial.C ((-1 : ℚ)^j.val) := by simp
    rw [hc]
    exact MvPolynomial.pderiv_C
  have hterm : ∀ j : Fin 6,
      MvPolynomial.pderiv v ((-1)^j.val*M 0 j*(B j).det) =
        (if j=(Fin.last 4).castSucc then (B j).det else 0) +
        (if j=Fin.last 5 then 0 else
          (-1)^j.val*M 0 j*((B j).submatrix Fin.succ (Fin.last 4).succAbove).det) := by
    intro j
    rw [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_mul,hsign,hrow,hminor]
    fin_cases j <;> norm_num <;> ring
  have hcomp (j : Fin 5) :
      (B j.castSucc).submatrix Fin.succ (Fin.last 4).succAbove =
        C.submatrix Fin.succ j.succAbove := by
    apply Matrix.ext
    intro a b
    simp only [B,C,Matrix.submatrix,Matrix.of_apply,Fin.succAbove_last,
      Fin.one_succAbove_succ,Fin.castSucc_succAbove_castSucc]
  have hCrow (j : Fin 5) : C 0 j=M 0 j.castSucc := by
    simp only [C,Matrix.submatrix,Matrix.of_apply,Fin.one_succAbove_zero,Fin.succAbove_last]
  have hsum :
      (∑ j : Fin 6, if j=Fin.last 5 then 0 else
        (-1)^j.val*M 0 j*((B j).submatrix Fin.succ (Fin.last 4).succAbove).det)=C.det := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_ne_last,if_false,if_true,Fin.val_castSucc,add_zero]
    rw [Matrix.det_succ_row_zero C]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcomp,hCrow]
  rw [Matrix.det_succ_row_zero M,map_sum]
  change (∑ j : Fin 6, MvPolynomial.pderiv v ((-1)^j.val*M 0 j*(B j).det))=_
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [hsum]

private theorem tied_border_down_minor (D : BetaDiagram 5) (t : ℤ) (ht : 0 < t) :
    (D.positiveBorder t t ht ht).matrix.submatrix Fin.succ
        (Fin.last 4).castSucc.succAbove=(D.extendBottom t ht).matrix := by
  apply Matrix.ext
  intro i j
  change complete ((D.positiveBorder t t ht ht).row i.succ -
    (D.positiveBorder t t ht ht).col ((Fin.last 4).castSucc.succAbove j)) =
      complete ((D.extendBottom t ht).row i-(D.extendBottom t ht).col j)
  rw [BetaDiagram.positiveBorder_row_succ]
  fin_cases j <;>
    norm_num [BetaDiagram.positiveBorder,BetaDiagram.extendBottom,Fin.snoc,
      Fin.succAbove,Fin.last] <;> congr 1 <;> ring

private theorem tied_border_up_minor (D : BetaDiagram 5) (t : ℤ) (ht : 0 < t) :
    (D.positiveBorder t t ht ht).matrix.submatrix (1 : Fin 6).succAbove
        (Fin.last 5).succAbove=(D.extendTop t ht).matrix := by
  apply Matrix.ext
  intro i j
  change complete ((D.positiveBorder t t ht ht).row ((1 : Fin 6).succAbove i) -
    (D.positiveBorder t t ht ht).col ((Fin.last 5).succAbove j)) =
      complete ((D.extendTop t ht).row i-(D.extendTop t ht).col j)
  rw [Fin.succAbove_last,BetaDiagram.positiveBorder_col_castSucc]
  cases i using Fin.cases with
  | zero =>
    rw [Fin.one_succAbove_zero,BetaDiagram.positiveBorder_row_zero]
    simp only [BetaDiagram.extendTop,ite_true]
  | succ i =>
    rw [Fin.one_succAbove_succ,BetaDiagram.positiveBorder_row_succ]
    simp only [BetaDiagram.extendTop,Fin.succ_ne_zero,ite_false]

private theorem positiveBorder_tied_derivative (D : BetaDiagram 5) (t : ℤ) (ht : 0 < t) :
    labelDerivative (D.largestLabel+t) (by have := D.largestLabel_pos; omega)
      (D.positiveBorder t t ht ht).schur =
      (D.extendTop t ht).schur+(D.extendBottom t ht).schur := by
  let P := D.positiveBorder t t ht ht
  let K := D.largestLabel+t
  have hK : 0 < K := by have := D.largestLabel_pos; dsimp [K]; omega
  let z : ℕ+ := ⟨K.toNat,by omega⟩
  have hz : (z.val : ℤ)=K := Int.toNat_of_nonneg hK.le
  have hcomplete (l : ℤ) :
      MvPolynomial.pderiv z (complete l)=if l=K then 1 else 0 := by
    change labelDerivative K hK (complete l)=_
    exact labelDerivative_complete K hK l
  have htop : P.matrix 0 (Fin.last 4).castSucc=MvPolynomial.X z := by
    change complete ((D.row 0+t)-D.col (Fin.last 4))=_
    rw [show D.row 0+t-D.col (Fin.last 4)=K by dsimp [K,BetaDiagram.largestLabel]; ring]
    exact complete_of_pos hK
  have hbottom : P.matrix (0 : Fin 5).succ (Fin.last 5)=MvPolynomial.X z := by
    change complete (D.row 0-(D.col (Fin.last 4)-t))=_
    rw [show D.row 0-(D.col (Fin.last 4)-t)=K by dsimp [K,BetaDiagram.largestLabel]; ring]
    exact complete_of_pos hK
  have hspan : P.largestLabel=D.largestLabel+2*t := by
    simp only [P,BetaDiagram.positiveBorder_largestLabel]
    ring
  have hmargin : P.topMargin=t := by simp [P]
  have hprivate : ∀ a b : Fin 6,
      (a≠0 ∨ b≠(Fin.last 4).castSucc) →
      (a≠(0 : Fin 5).succ ∨ b≠Fin.last 5) →
      MvPolynomial.pderiv z (P.matrix a b)=0 := by
    intro a b hab hba
    change MvPolynomial.pderiv z (complete (P.row a-P.col b))=0
    rw [hcomplete]
    apply if_neg
    by_cases hc : a=0 ∧ b=Fin.last 5
    · rcases hc with ⟨rfl,rfl⟩
      change P.largestLabel≠K
      rw [hspan]
      dsimp [K]
      omega
    · have hh := P.tied_margin_private (by simp [P]) a b (by tauto) hab hba
      rw [hspan,hmargin] at hh
      dsimp [K]
      omega
  have hd := pderiv_exterior_pair P.matrix z htop hbottom hprivate
  rw [tied_border_down_minor,tied_border_up_minor] at hd
  change labelDerivative K hK P.schur =
    (D.extendBottom t ht).schur+(D.extendTop t ht).schur at hd
  exact hd.trans (add_comm _ _)

private theorem borderPair_tied_coefficient (Q R : BetaDiagram 5)
    (hspan : Q.largestLabel=R.largestLabel) (t : ℤ) (ht : 0 < t)
    (k : ℤ) (hk : 0 < k) (hkval : k=Q.largestLabel+t) :
    labelDerivative k hk (borderPairDifference Q R t t ht ht) =
      ((Q.extendTop t ht).schur-(R.extendTop t ht).schur) +
        ((Q.extendBottom t ht).schur-(R.extendBottom t ht).schur) := by
  have hQ := positiveBorder_tied_derivative Q t ht
  have hR := positiveBorder_tied_derivative R t ht
  have hqk : 0 < Q.largestLabel+t := by have := Q.largestLabel_pos; omega
  have hrk : 0 < R.largestLabel+t := by have := R.largestLabel_pos; omega
  have hkr : k=R.largestLabel+t := by simpa only [hspan] using hkval
  have hQ' := (labelDerivative_congr hk hqk hkval
    (Q.positiveBorder t t ht ht).schur).trans hQ
  have hR' := (labelDerivative_congr hk hrk hkr
    (R.positiveBorder t t ht ht).schur).trans hR
  unfold borderPairDifference
  rw [map_sub,hQ',hR']
  ring

private theorem borderPair_margin_congr (Q R : BetaDiagram 5)
    (w wp v : ℤ) (hw : 0 < w) (hwp : 0 < wp) (hv : 0 < v) (he : w=wp) :
    borderPairDifference Q R w v hw hv=borderPairDifference Q R wp v hwp hv := by
  cases he
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The tied interface is extracted from the actual parent polynomials for every core pair. -/
theorem tied_interface_coefficient (P : Parameters) (second : Bool)
    (mf rf mr rr : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (htie : v = s+g+u) :
    labelDerivative (P.b+4*P.g+v) (by
      have := P.q_pos; have := P.q_le_b; have := P.b_lt_g; omega)
      (((coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg).schur -
        ((coreCandidate P second mr rr).singletonContext s u v g hs hu hv hg).schur) =
      interfaceResidual (coreCandidate P second mf rf) (coreCandidate P second mr rr)
        s u v g hs hu hv hg := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hgP := P.b_lt_g
  let Q := coreCandidate P second mf rf
  let R := coreCandidate P second mr rr
  let k := P.b+4*P.g+v
  have hk : 0 < k := by dsimp [k]; omega
  have hspan : Q.largestLabel=R.largestLabel := by rw [coreCandidate_span,coreCandidate_span]
  have hcore : Q.schur=R.schur := coreCandidate_schur_eq P second mf rf mr rr
  have hQspan : Q.largestLabel=P.b+4*P.g := coreCandidate_span P second mf rf
  have hd0 := borderPair_coefficient Q R hspan hcore (s+g) v (by omega) hv
    (by omega) k hk (by dsimp [k]; rw [hQspan]; omega)
  rw [if_pos (by omega)] at hd0
  have hd1 := (congrArg (labelDerivative k hk)
    (borderPair_margin_congr Q R (s+g+u) v v (by omega) hv hv htie.symm)).trans
    (borderPair_tied_coefficient Q R hspan v hv k hk (by dsimp [k]; rw [hQspan]))
  have hs0 : labelDerivative k hk (complete (s+u))=0 := by
    rw [labelDerivative_complete,if_neg (by dsimp [k]; omega)]
  have hs1 : labelDerivative k hk (complete s)=0 := by
    rw [labelDerivative_complete,if_neg (by dsimp [k]; omega)]
  rw [context_pair_difference,map_sub,labelDerivative_mul,labelDerivative_mul,
    hs0,hs1,hd0,hd1]
  simp only [zero_mul,zero_add]
  rfl

theorem tied_interface_zero_of_context_eq (P : Parameters) (second : Bool)
    (mf rf mr rr : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (htie : v = s+g+u)
    (he : ((coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg).schur =
      ((coreCandidate P second mr rr).singletonContext s u v g hs hu hv hg).schur) :
    interfaceResidual (coreCandidate P second mf rf) (coreCandidate P second mr rr)
      s u v g hs hu hv hg = 0 := by
  have hc := tied_interface_coefficient P second mf rf mr rr s u v g hs hu hv hg htie
  rw [he, sub_self, map_zero] at hc
  exact hc.symm


private theorem derivative_scalar_mul_response (P : Parameters) (second : Bool)
    (x : ℤ) (hx : 0 < x) (t : ℤ) (ht : 0 < t) (kind : ResponseKind)
    (k : ℤ) (hk : 0 < k) (hscalar : x < k) :
    labelDerivative k hk (complete x * responsePolynomial P second t ht kind) =
      complete x * labelDerivative k hk (responsePolynomial P second t ht kind) := by
  rw [labelDerivative_mul, labelDerivative_complete, if_neg (by omega)]
  ring

/-- All comparisons of the two rotated cores at the surviving interface force the exact locus. -/
theorem rotated_interface_locus (P : Parameters) (hp : P.q < P.b) (second : Bool)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (htie : v = s+g+u) (hvG : v = P.g)
    (he : interfaceResidual (F P second).rotate (H P second).rotate
      s u v g hs hu hv hg = 0) :
    (s,u,v,g) = (P.b-P.q,P.q,P.g,P.g-P.b) := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hgP := P.b_lt_g
  have hqG : P.q < P.g := by omega
  have hA : 0 < s+g := by omega
  have hpoly :
      complete (s+u)*responsePolynomial P second (s+g) hA .down -
        complete s*responsePolynomial P second v hv .sum = 0 := by
    simpa [interfaceResidual, responsePolynomial,
      BetaDiagram.rotate_extendTop_schur, BetaDiagram.rotate_extendBottom_schur,
      add_comm] using he
  have huq : u = P.q := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let k := responseLeader P (s+g) .down
      have hk : 0 < k := by dsimp [k,responseLeader]; omega
      have hsuk : s+u < k := by dsimp [k,responseLeader]; omega
      have hsk : s < k := by omega
      have hhigh : responseLeader P v .sum < k := by dsimp [k,responseLeader]; omega
      have hd := labelDerivative_response P hp second (s+g) hA .down (by simp) hk
      have hc := labelDerivative_response_above P second v hv .sum (by intro _; omega)
        k hk hhigh
      have h := congrArg (labelDerivative k hk) hpoly
      rw [map_sub, derivative_scalar_mul_response P second (s+u) (by omega)
        (s+g) hA .down k hk hsuk,
        derivative_scalar_mul_response P second s hs v hv .sum k hk hsk,
        hd, hc, map_zero] at h
      have hn := mul_ne_zero ((complete_ne_zero_iff (s+u)).2 (by omega))
        (response_coefficient_nonzero P hp second .down)
      apply hn
      simpa using h
    · let k := responseLeader P v .sum
      have hk : 0 < k := by dsimp [k,responseLeader]; omega
      have hsuk : s+u < k := by dsimp [k,responseLeader]; omega
      have hsk : s < k := by omega
      have hhigh : responseLeader P (s+g) .down < k := by dsimp [k,responseLeader]; omega
      have hd := labelDerivative_response_above P second (s+g) hA .down (by simp)
        k hk hhigh
      have hc := labelDerivative_response P hp second v hv .sum (by intro _; omega) hk
      have h := congrArg (labelDerivative k hk) hpoly
      rw [map_sub, derivative_scalar_mul_response P second (s+u) (by omega)
        (s+g) hA .down k hk hsuk,
        derivative_scalar_mul_response P second s hs v hv .sum k hk hsk,
        hd, hc, map_zero] at h
      have hn := mul_ne_zero ((complete_ne_zero_iff s).2 (by omega))
        (response_coefficient_nonzero P hp second .sum)
      apply hn
      simpa using h
  let k := responseLeader P v .sum
  have hk : 0 < k := by dsimp [k,responseLeader]; omega
  have hlead : responseLeader P (s+g) .down = k := by dsimp [k,responseLeader]; omega
  have hsuk : s+u < k := by dsimp [k,responseLeader]; omega
  have hsk : s < k := by omega
  have hd := labelDerivative_response P hp second (s+g) hA .down (by simp)
    (show 0 < responseLeader P (s+g) .down by rw [hlead]; exact hk)
  have hd := (labelDerivative_congr (by rw [hlead]; exact hk) hk hlead
    (responsePolynomial P second (s+g) hA .down)).symm.trans hd
  have hc := labelDerivative_response P hp second v hv .sum (by intro _; omega) hk
  have h := congrArg (labelDerivative k hk) hpoly
  rw [map_sub, derivative_scalar_mul_response P second (s+u) (by omega)
    (s+g) hA .down k hk hsuk,
    derivative_scalar_mul_response P second s hs v hv .sum k hk hsk,
    hd, hc, map_zero] at h
  have hfactor : (if second then D2 P else D1 P) *
      (complete (s+P.q)*complete (P.b-P.q) - complete s*complete P.b) = 0 := by
    rw [huq] at h
    simp only [responseCoefficient] at h
    convert h using 1 <;> ring
  exact singleton_locus_of_interface_zero P hp s u v g hs huq hvG htie second hfactor

theorem rotated_context_locus_at_tie (P : Parameters) (hp : P.q < P.b) (second : Bool)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (htie : v = s+g+u)
    (he : ((F P second).rotate.singletonContext s u v g hs hu hv hg).schur =
      ((H P second).rotate.singletonContext s u v g hs hu hv hg).schur) :
    (s,u,v,g) = (P.b-P.q,P.q,P.g,P.g-P.b) :=
  rotated_interface_locus P hp second s u v g hs hu hv hg htie
    (rotated_context_row_condition P second s u v g hs hu hv hg he)
    (tied_interface_zero_of_context_eq P second true true false true
      s u v g hs hu hv hg htie he)

theorem unrotated_interface_ne_zero (P : Parameters) (hp : P.q < P.b) (second : Bool)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (htie : v = s+g+u) (hAG : s+g = P.g) :
    interfaceResidual (F P second) (H P second) s u v g hs hu hv hg ≠ 0 := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hgP := P.b_lt_g
  have hqG : P.q < P.g := by omega
  have hA : 0 < s+g := by omega
  have hvq : P.q < v := by omega
  intro he
  have hpoly :
      complete (s+u)*responsePolynomial P second (s+g) hA .up -
        complete s*responsePolynomial P second v hv .sum = 0 := he
  have huq : u = P.q := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let k := responseLeader P (s+g) .up
      have hk : 0 < k := by dsimp [k,responseLeader]; omega
      have hsuk : s+u < k := by dsimp [k,responseLeader]; omega
      have hsk : s < k := by omega
      have hhigh : responseLeader P v .sum < k := by dsimp [k,responseLeader]; omega
      have hd := labelDerivative_response P hp second (s+g) hA .up (by simp) hk
      have hc := labelDerivative_response_above P second v hv .sum (by intro _; exact hvq)
        k hk hhigh
      have h := congrArg (labelDerivative k hk) hpoly
      rw [map_sub, derivative_scalar_mul_response P second (s+u) (by omega)
        (s+g) hA .up k hk hsuk,
        derivative_scalar_mul_response P second s hs v hv .sum k hk hsk,
        hd, hc, map_zero] at h
      apply mul_ne_zero ((complete_ne_zero_iff (s+u)).2 (by omega))
        (response_coefficient_nonzero P hp second .up)
      simpa using h
    · let k := responseLeader P v .sum
      have hk : 0 < k := by dsimp [k,responseLeader]; omega
      have hsuk : s+u < k := by dsimp [k,responseLeader]; omega
      have hsk : s < k := by omega
      have hhigh : responseLeader P (s+g) .up < k := by dsimp [k,responseLeader]; omega
      have hd := labelDerivative_response_above P second (s+g) hA .up (by simp)
        k hk hhigh
      have hc := labelDerivative_response P hp second v hv .sum (by intro _; exact hvq) hk
      have h := congrArg (labelDerivative k hk) hpoly
      rw [map_sub, derivative_scalar_mul_response P second (s+u) (by omega)
        (s+g) hA .up k hk hsuk,
        derivative_scalar_mul_response P second s hs v hv .sum k hk hsk,
        hd, hc, map_zero] at h
      apply mul_ne_zero ((complete_ne_zero_iff s).2 (by omega))
        (response_coefficient_nonzero P hp second .sum)
      simpa using h
  let k := responseLeader P v .sum
  have hk : 0 < k := by dsimp [k,responseLeader]; omega
  have hlead : responseLeader P (s+g) .up = k := by dsimp [k,responseLeader]; omega
  have hsuk : s+u < k := by dsimp [k,responseLeader]; omega
  have hsk : s < k := by omega
  have hd := labelDerivative_response P hp second (s+g) hA .up (by simp)
    (show 0 < responseLeader P (s+g) .up by rw [hlead]; exact hk)
  have hd := (labelDerivative_congr (by rw [hlead]; exact hk) hk hlead
    (responsePolynomial P second (s+g) hA .up)).symm.trans hd
  have hc := labelDerivative_response P hp second v hv .sum (by intro _; exact hvq) hk
  have h := congrArg (labelDerivative k hk) hpoly
  rw [map_sub, derivative_scalar_mul_response P second (s+u) (by omega)
    (s+g) hA .up k hk hsuk,
    derivative_scalar_mul_response P second s hs v hv .sum k hk hsk,
    hd, hc, map_zero] at h
  apply unrotated_interface_coefficient_ne_zero P hp s hs second
  rw [huq] at h
  simp only [responseCoefficient] at h
  convert h using 1 <;> ring

theorem unrotated_context_ne_at_interface_tie (P : Parameters) (hp : P.q < P.b)
    (second : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (htie : v = s+g+u) :
    ((F P second).singletonContext s u v g hs hu hv hg).schur ≠
      ((H P second).singletonContext s u v g hs hu hv hg).schur := by
  intro he
  exact unrotated_interface_ne_zero P hp second s u v g hs hu hv hg htie
    (unrotated_context_row_condition P second s u v g hs hu hv hg he)
    (tied_interface_zero_of_context_eq P second true false false false
      s u v g hs hu hv hg htie he)


theorem context_pair_ne_below_interface (P : Parameters) (hp : P.q < P.b)
    (second mf rf mr rr : Bool) (hne : (mf,rf) ≠ (mr,rr))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hbelow : v < s+g+u) :
    ((coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg).schur ≠
      ((coreCandidate P second mr rr).singletonContext s u v g hs hu hv hg).schur := by
  let Q := coreCandidate P second mf rf
  let R := coreCandidate P second mr rr
  have hspan : Q.largestLabel=R.largestLabel := by
    rw [coreCandidate_span, coreCandidate_span]
  have hcore : Q.schur=R.schur := coreCandidate_schur_eq P second mf rf mr rr
  let k := Q.largestLabel+s+g+u
  have hS : Q.largestLabel = P.b+4*P.g := coreCandidate_span P second mf rf
  have hSpos := Q.largestLabel_pos
  have hk : 0 < k := by dsimp [k]; omega
  have hsmall : labelDerivative k hk (borderPairDifference Q R (s+g) v (by omega) hv) = 0 := by
    apply labelDerivative_of_labelsBelow
    intro z hz
    have h := borderPair_labels Q R hspan hcore (s+g) v (by omega) hv z hz
    dsimp [k]
    omega
  have hlarge := borderPair_coefficient Q R hspan hcore (s+g+u) v
    (by omega) hv (by omega) k hk (by dsimp [k]; omega)
  rw [if_neg (by omega)] at hlarge
  have hx0 : labelDerivative k hk (complete (s+u)) = 0 := by
    rw [labelDerivative_complete, if_neg (by dsimp [k]; omega)]
  have hx1 : labelDerivative k hk (complete s) = 0 := by
    rw [labelDerivative_complete, if_neg (by dsimp [k]; omega)]
  intro he
  have hd := context_pair_difference Q R s u v g hs hu hv hg
  rw [he, sub_self] at hd
  have h := congrArg (labelDerivative k hk) hd.symm
  rw [map_sub, labelDerivative_mul, labelDerivative_mul,
    hx0, hx1, hsmall, hlarge, map_zero] at h
  have hne' := (coreCandidate_endpoint_separation P hp second mf rf mr rr hne v hv).2
  have hn := mul_ne_zero ((complete_ne_zero_iff s).2 (by omega)) (sub_ne_zero.mpr hne')
  apply hn
  simpa [Q,R] using h

private def fourChoice {α : Type*} (a b c d : α) (m r : Bool) : α :=
  if m then (if r then b else a) else (if r then d else c)

private theorem fourChoice_ne {α : Type*} {a b c d : α}
    {mf rf mr rr : Bool} (hne : (mf,rf)≠(mr,rr))
    (hab : a≠b) (hcd : c≠d) (hac : a≠c) (hbd : b≠d) (had : a≠d) (hcb : c≠b) :
    fourChoice a b c d mf rf≠fourChoice a b c d mr rr := by
  cases mf <;> cases rf <;> cases mr <;> cases rr <;>
    simp only [fourChoice,Bool.false_eq_true,↓reduceIte] <;> first
      | exact False.elim (hne rfl)
      | assumption
      | exact Ne.symm hab
      | exact Ne.symm hcd
      | exact Ne.symm hac
      | exact Ne.symm hbd
      | exact Ne.symm had
      | exact Ne.symm hcb

private theorem linear_difference {R : Type*} [CommRing R] (c d a b a' b' : R) :
    c*(a-b)-d*(a'-b')=(c*a-d*a')-(c*b-d*b') := by ring

private theorem linear_ne {R : Type*} [CommRing R] (c d a b a' b' : R)
    (h : c*(a-b)-d*(a'-b')≠0) : c*a-d*a'≠c*b-d*b' := by
  apply sub_ne_zero.mp
  rw [←linear_difference]
  exact h

private theorem selected_linear (D E : BetaDiagram 5) (m r : Bool)
    (A B : ℤ) (hA : 0 < A) (hB : 0 < B) (c d : CompleteRing) :
    c*((if r then (if m then D else E).rotate else (if m then D else E)).extendTop A hA).schur -
      d*((if r then (if m then D else E).rotate else (if m then D else E)).extendTop B hB).schur =
      fourChoice
        (c*(D.extendTop A hA).schur-d*(D.extendTop B hB).schur)
        (c*(D.extendBottom A hA).schur-d*(D.extendBottom B hB).schur)
        (c*(E.extendTop A hA).schur-d*(E.extendTop B hB).schur)
        (c*(E.extendBottom A hA).schur-d*(E.extendBottom B hB).schur) m r := by
  cases m <;> cases r <;>
    simp only [fourChoice,Bool.false_eq_true,↓reduceIte,
      BetaDiagram.rotate_extendTop_schur]

private theorem ne_transport {α : Type*} {a b c d : α}
    (ha : a=c) (hb : b=d) (h : c≠d) : a≠b :=
  fun he => h (ha.symm.trans (he.trans hb))

private theorem core_pair_double_top_ne_zero (P : Parameters) (hp : P.q < P.b)
    (second mf rf mr rr : Bool) (hne : (mf,rf) ≠ (mr,rr))
    (s u A : ℤ) (hs : 0 < s) (hu : 0 < u) (hA : s < A) :
    complete (s+u) *
        (((coreCandidate P second mf rf).extendTop A (by omega)).schur -
          ((coreCandidate P second mr rr).extendTop A (by omega)).schur) -
      complete s *
        (((coreCandidate P second mf rf).extendTop (A+u) (by omega)).schur -
          ((coreCandidate P second mr rr).extendTop (A+u) (by omega)).schur) ≠ 0 := by
  have hf := BetaDiagram.singleton_double_top_ne_zero (F P second)
    (coreCandidate_endpointLeader P hp second true false) s u A hs hu hA
  have hh := BetaDiagram.singleton_double_top_ne_zero (H P second)
    (coreCandidate_endpointLeader P hp second false false) s u A hs hu hA
  have hup := response_double_top_ne_zero P hp second .up s u A hs hu hA (by simp)
  have hdown := response_double_top_ne_zero P hp second .down s u A hs hu hA (by simp)
  have hm1 := response_double_top_ne_zero P hp second .mixedFH s u A hs hu hA (by simp)
  have hm2 := response_double_top_ne_zero P hp second .mixedHF s u A hs hu hA (by simp)
  have hf' := linear_ne (complete (s+u)) (complete s)
    ((F P second).extendTop A (by omega)).schur ((F P second).extendBottom A (by omega)).schur
    ((F P second).extendTop (A+u) (by omega)).schur ((F P second).extendBottom (A+u) (by omega)).schur
    (by simpa only [BetaDiagram.endpointDifference] using hf)
  have hh' := linear_ne (complete (s+u)) (complete s)
    ((H P second).extendTop A (by omega)).schur ((H P second).extendBottom A (by omega)).schur
    ((H P second).extendTop (A+u) (by omega)).schur ((H P second).extendBottom (A+u) (by omega)).schur
    (by simpa only [BetaDiagram.endpointDifference] using hh)
  have hu' := linear_ne (complete (s+u)) (complete s)
    ((F P second).extendTop A (by omega)).schur ((H P second).extendTop A (by omega)).schur
    ((F P second).extendTop (A+u) (by omega)).schur ((H P second).extendTop (A+u) (by omega)).schur
    (by simpa only [responsePolynomial] using hup)
  have hd' := linear_ne (complete (s+u)) (complete s)
    ((F P second).extendBottom A (by omega)).schur ((H P second).extendBottom A (by omega)).schur
    ((F P second).extendBottom (A+u) (by omega)).schur ((H P second).extendBottom (A+u) (by omega)).schur
    (by simpa only [responsePolynomial] using hdown)
  have hm1' := linear_ne (complete (s+u)) (complete s)
    ((F P second).extendTop A (by omega)).schur ((H P second).extendBottom A (by omega)).schur
    ((F P second).extendTop (A+u) (by omega)).schur ((H P second).extendBottom (A+u) (by omega)).schur
    (by simpa only [responsePolynomial] using hm1)
  have hm2' := linear_ne (complete (s+u)) (complete s)
    ((H P second).extendTop A (by omega)).schur ((F P second).extendBottom A (by omega)).schur
    ((H P second).extendTop (A+u) (by omega)).schur ((F P second).extendBottom (A+u) (by omega)).schur
    (by simpa only [responsePolynomial] using hm2)
  rw [linear_difference]
  apply sub_ne_zero.mpr
  unfold coreCandidate
  exact ne_transport
    (selected_linear (F P second) (H P second) mf rf A (A+u) (by omega) (by omega)
      (complete (s+u)) (complete s))
    (selected_linear (F P second) (H P second) mr rr A (A+u) (by omega) (by omega)
      (complete (s+u)) (complete s))
    (fourChoice_ne hne hf' hh' hu' hd' hm1' hm2')

theorem context_pair_ne_above_interface (P : Parameters) (hp : P.q < P.b)
    (second mf rf mr rr : Bool) (hne : (mf,rf) ≠ (mr,rr))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (habove : s+g+u < v) :
    ((coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg).schur ≠
      ((coreCandidate P second mr rr).singletonContext s u v g hs hu hv hg).schur := by
  let Q := coreCandidate P second mf rf
  let R := coreCandidate P second mr rr
  have hspan : Q.largestLabel=R.largestLabel := by
    rw [coreCandidate_span, coreCandidate_span]
  have hcore : Q.schur=R.schur := coreCandidate_schur_eq P second mf rf mr rr
  let k := Q.largestLabel+v
  have hSpos := Q.largestLabel_pos
  have hk : 0 < k := by dsimp [k]; omega
  have hd0 := borderPair_coefficient Q R hspan hcore (s+g) v
    (by omega) hv (by omega) k hk (by dsimp [k]; omega)
  have hd1 := borderPair_coefficient Q R hspan hcore (s+g+u) v
    (by omega) hv (by omega) k hk (by dsimp [k]; omega)
  rw [if_pos (by omega)] at hd0 hd1
  have hx0 : labelDerivative k hk (complete (s+u)) = 0 := by
    rw [labelDerivative_complete, if_neg (by dsimp [k]; omega)]
  have hx1 : labelDerivative k hk (complete s) = 0 := by
    rw [labelDerivative_complete, if_neg (by dsimp [k]; omega)]
  intro he
  have hd := context_pair_difference Q R s u v g hs hu hv hg
  rw [he, sub_self] at hd
  have h := congrArg (labelDerivative k hk) hd.symm
  rw [map_sub, labelDerivative_mul, labelDerivative_mul,
    hx0, hx1, hd0, hd1, map_zero] at h
  apply core_pair_double_top_ne_zero P hp second mf rf mr rr hne s u (s+g) hs hu (by omega)
  simpa only [zero_mul,zero_add] using h

theorem context_equality_forces_interface_tie (P : Parameters) (hp : P.q < P.b)
    (second mf rf mr rr : Bool) (hne : (mf,rf) ≠ (mr,rr))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (he : ((coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg).schur =
      ((coreCandidate P second mr rr).singletonContext s u v g hs hu hv hg).schur) :
    v = s+g+u := by
  rcases lt_trichotomy v (s+g+u) with h | h | h
  · exact False.elim (context_pair_ne_below_interface P hp second mf rf mr rr hne
      s u v g hs hu hv hg h he)
  · exact h
  · exact False.elim (context_pair_ne_above_interface P hp second mf rf mr rr hne
      s u v g hs hu hv hg h he)

set_option maxHeartbeats 0 in
theorem reverse_mixed_context_row_condition (P : Parameters) (second : Bool)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (he : ((H P second).singletonContext s u v g hs hu hv hg).schur =
      ((F P second).rotate.singletonContext s u v g hs hu hv hg).schur) :
    if second then
      ({v+P.g-P.q,3*P.g-P.q,s+g} : Multiset ℤ) =
        {v,2*P.g-P.q,2*P.g-P.q+(s+g)}
    else
      ({v+P.g,3*P.g-P.q,s+g} : Multiset ℤ) =
        {v,2*P.g,2*P.g-P.q+(s+g)} := by
  have hr := row_multiset_of_schur_eq _ _ he.symm
  have hm := congrArg (Multiset.map (fun k : ℤ => k-P.b)) hr
  let common : Multiset ℤ := {s+u-P.b,P.g,2*P.g,2*P.g-P.q}
  let left : Multiset ℤ := {v+P.g-(if second then P.q else 0),3*P.g-P.q,s+g}
  let right : Multiset ℤ := {v,2*P.g-(if second then P.q else 0),2*P.g-P.q+(s+g)}
  have hLeft : common+left=
      (List.ofFn ((F P second).rotate.singletonContext s u v g hs hu hv hg).rowLength : Multiset ℤ).map
        (fun k => k-P.b) := by
    rw [context_shifted_rows]
    cases second <;>
      norm_num [common,left,BetaDiagram.rotate,F,rows,fCols,Fin.rev,Matrix.cons_val] <;>
      ring_nf <;>
      (conv_rhs => rw [list7_as_sum]) <;>
      simp only [←Multiset.singleton_add,add_zero] <;> ac_rfl
  have hRight : common+right=
      (List.ofFn ((H P second).singletonContext s u v g hs hu hv hg).rowLength : Multiset ℤ).map
        (fun k => k-P.b) := by
    rw [context_shifted_rows]
    cases second <;>
      norm_num [common,right,H,rows,hCols,Matrix.cons_val] <;>
      ring_nf <;>
      (conv_rhs => rw [list7_as_sum]) <;>
      simp only [←Multiset.singleton_add,add_zero] <;> ac_rfl
  have hcancel : left=right := add_left_cancel (hLeft.trans (hm.trans hRight.symm))
  cases second <;> simpa only [left,right,Bool.false_eq_true,↓reduceIte,sub_zero] using hcancel

theorem reverse_mixed_interface_ne_zero (P : Parameters) (hp : P.q < P.b)
    (second : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hAeq : s+g = if second then 2*P.g-P.q else 2*P.g)
    (hveq : v = 3*P.g-P.q) (hueq : u = if second then P.g else P.g-P.q) :
    interfaceResidual (H P second) (F P second).rotate s u v g hs hu hv hg ≠ 0 := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hgP := P.b_lt_g
  have hqG : P.q < P.g := by omega
  have hA : 0 < s+g := by omega
  have hvq : P.q < v := by omega
  intro he
  have hpoly :
      complete (s+u)*responsePolynomial P second (s+g) hA .mixedHF +
        complete s*responsePolynomial P second v hv .sum = 0 := by
    convert he using 1 <;>
      simp only [interfaceResidual, responsePolynomial,
        BetaDiagram.rotate_extendTop_schur, BetaDiagram.rotate_extendBottom_schur] <;> ring
  let k := responseLeader P (s+g) .mixedHF
  have hk : 0 < k := by dsimp [k,responseLeader]; omega
  have hsuk : s+u < k := by
    cases second <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;>
      dsimp [k,responseLeader] <;> omega
  have hsk : s < k := by omega
  have hd := labelDerivative_response P hp second (s+g) hA .mixedHF (by simp) hk
  have h := congrArg (labelDerivative k hk) hpoly
  rw [map_add, derivative_scalar_mul_response P second (s+u) (by omega)
    (s+g) hA .mixedHF k hk hsuk,
    derivative_scalar_mul_response P second s hs v hv .sum k hk hsk, hd, map_zero] at h
  cases second
  · have hhigh : responseLeader P v .sum < k := by
      dsimp [k,responseLeader]
      simp only [Bool.false_eq_true, ↓reduceIte] at hAeq hueq
      omega
    have hc := labelDerivative_response_above P false v hv .sum (by intro _; exact hvq)
      k hk hhigh
    rw [hc] at h
    apply mul_ne_zero ((complete_ne_zero_iff (s+u)).2 (by omega))
      (response_coefficient_nonzero P hp false .mixedHF)
    simpa using h
  · have hlead : responseLeader P v .sum = k := by
      dsimp [k,responseLeader]
      simp only [↓reduceIte] at hAeq hueq
      omega
    have hc := labelDerivative_response P hp true v hv .sum (by intro _; exact hvq)
      (show 0 < responseLeader P v .sum by rw [hlead]; exact hk)
    have hc := (labelDerivative_congr (by rw [hlead]; exact hk) hk hlead
      (responsePolynomial P true v hv .sum)).symm.trans hc
    rw [hc] at h
    have hn := mul_ne_zero ((complete_ne_zero_iff P.b).2 (by omega))
      (reverse_second_interface_ne_zero P hp s hs)
    apply hn
    simp only [responseCoefficient, K, ↓reduceIte] at h
    simp only [↓reduceIte] at hueq
    rw [hueq] at h
    convert h using 1 <;> ring

theorem reverse_mixed_context_ne_at_interface_tie (P : Parameters) (hp : P.q < P.b)
    (second : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (htie : v = s+g+u) :
    ((H P second).singletonContext s u v g hs hu hv hg).schur ≠
      ((F P second).rotate.singletonContext s u v g hs hu hv hg).schur := by
  intro he
  have hrows := reverse_mixed_context_row_condition P second s u v g hs hu hv hg he
  have hparams : (s+g,v,u) =
      (if second then 2*P.g-P.q else 2*P.g,3*P.g-P.q,
        if second then P.g else P.g-P.q) := by
    cases second
    · exact reverse_mixed_first_parameters P (s+g) v u hu htie hrows
    · exact reverse_mixed_second_parameters P (s+g) v u hu htie hrows
  have hAeq := congrArg (fun x : ℤ×ℤ×ℤ => x.1) hparams
  have hveq := congrArg (fun x : ℤ×ℤ×ℤ => x.2.1) hparams
  have hueq := congrArg (fun x : ℤ×ℤ×ℤ => x.2.2) hparams
  exact reverse_mixed_interface_ne_zero P hp second s u v g hs hu hv hg hAeq hveq hueq
    (tied_interface_zero_of_context_eq P second false false true true
      s u v g hs hu hv hg htie he)

private theorem context_parameters_congr (Q : BetaDiagram 5)
    (s u v g sp up vp gp : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hsp : 0 < sp) (hup : 0 < up) (hvp : 0 < vp) (hgp : 0 < gp)
    (he : (s,u,v,g)=(sp,up,vp,gp)) :
    Q.singletonContext s u v g hs hu hv hg=Q.singletonContext sp up vp gp hsp hup hvp hgp := by
  have h : s=sp ∧ u=up ∧ v=vp ∧ g=gp := by simpa only [Prod.mk.injEq] using he
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  rfl

private theorem context_choice (D E : BetaDiagram 5) (m r : Bool)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (BetaDiagram.singletonContext
      (if r then (if m then D else E).rotate else (if m then D else E)) s u v g hs hu hv hg).schur =
      fourChoice (D.singletonContext s u v g hs hu hv hg).schur
        (D.rotate.singletonContext s u v g hs hu hv hg).schur
        (E.singletonContext s u v g hs hu hv hg).schur
        (E.rotate.singletonContext s u v g hs hu hv hg).schur m r := by
  cases m <;> cases r <;> simp only [fourChoice,Bool.false_eq_true,↓reduceIte]

private theorem candidate_context_choice (P : Parameters) (second m r : Bool)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    ((coreCandidate P second m r).singletonContext s u v g hs hu hv hg).schur =
      fourChoice ((F P second).singletonContext s u v g hs hu hv hg).schur
        ((F P second).rotate.singletonContext s u v g hs hu hv hg).schur
        ((H P second).singletonContext s u v g hs hu hv hg).schur
        ((H P second).rotate.singletonContext s u v g hs hu hv hg).schur m r := by
  unfold coreCandidate
  exact context_choice (F P second) (H P second) m r s u v g hs hu hv hg

private theorem choice_classification {α : Type*} {a b c d : α} {L : Prop}
    (hab : a≠b) (hcd : c≠d) (hac : a≠c) (had : a≠d) (hcb : c≠b)
    (hbd : b=d ↔ L) (mf rf mr rr : Bool) :
    fourChoice a b c d mf rf=fourChoice a b c d mr rr ↔
      (mf,rf)=(mr,rr) ∨ (rf=true ∧ rr=true ∧ L) := by
  have hdb : d=b ↔ L := Eq.comm.trans hbd
  cases mf <;> cases rf <;> cases mr <;> cases rr <;>
    simp [fourChoice,hab,hcd,hac,had,hcb,Ne.symm hab,Ne.symm hcd,
      Ne.symm hac,Ne.symm had,Ne.symm hcb,hbd,hdb]

private theorem rotated_choice_eq {α : Type*} {a b c d : α} (he : b=d) (m n : Bool) :
    fourChoice a b c d m true=fourChoice a b c d n true := by
  cases m <;> cases n <;> simp [fourChoice,he]

private theorem rotated_context_eq_at_locus (P : Parameters) (hp : P.q < P.b)
    (second : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (he : (s,u,v,g)=(P.b-P.q,P.q,P.g,P.g-P.b)) :
    ((F P second).rotate.singletonContext s u v g hs hu hv hg).schur =
      ((H P second).rotate.singletonContext s u v g hs hu hv hg).schur := by
  obtain ⟨hs',hu',hv',hg'⟩ := singleton_locus_positive P hp
  have hf := congrArg BetaDiagram.schur (context_parameters_congr (F P second).rotate
    s u v g (P.b-P.q) P.q P.g (P.g-P.b) hs hu hv hg hs' hu' hv' hg' he)
  have hh := congrArg BetaDiagram.schur (context_parameters_congr (H P second).rotate
    s u v g (P.b-P.q) P.q P.g (P.g-P.b) hs hu hv hg hs' hu' hv' hg' he)
  have hm : ((F P second).rotate.singletonContext (P.b-P.q) P.q P.g (P.g-P.b)
      hs' hu' hv' hg').schur =
      ((H P second).rotate.singletonContext (P.b-P.q) P.q P.g (P.g-P.b)
        hs' hu' hv' hg').schur := by
    simpa only [exceptionalSingleton,Bool.false_eq_true,↓reduceIte] using
      exceptionalSingleton_schur_eq P hp second
  exact hf.trans (hm.trans hh.symm)

set_option maxHeartbeats 0 in
/-- Complete local classification of all six unordered actual core pairs.
No five-row or seven-row classifier is assumed in this theorem. -/
theorem four_core_context_equality_iff (P : Parameters) (hp : P.q < P.b)
    (second mf rf mr rr : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    ((coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg).schur =
        ((coreCandidate P second mr rr).singletonContext s u v g hs hu hv hg).schur ↔
      (mf,rf) = (mr,rr) ∨
        (rf = true ∧ rr = true ∧
          (s,u,v,g) = (P.b-P.q,P.q,P.g,P.g-P.b)) := by
  constructor
  · intro he
    by_cases hsame : (mf,rf) = (mr,rr)
    · exact Or.inl hsame
    have htie := context_equality_forces_interface_tie P hp second mf rf mr rr hsame
      s u v g hs hu hv hg he
    have hfr : ((F P second).singletonContext s u v g hs hu hv hg).schur ≠
        ((F P second).rotate.singletonContext s u v g hs hu hv hg).schur :=
      reflected_core_context_ne P hp second true false s u v g hs hu hv hg
    have hhr : ((H P second).singletonContext s u v g hs hu hv hg).schur ≠
        ((H P second).rotate.singletonContext s u v g hs hu hv hg).schur :=
      reflected_core_context_ne P hp second false false s u v g hs hu hv hg
    have hun := unrotated_context_ne_at_interface_tie P hp second s u v g hs hu hv hg htie
    have hmi := mixed_context_ne_at_interface_tie P second s u v g hs hu hv hg htie
    have hrev := reverse_mixed_context_ne_at_interface_tie P hp second s u v g hs hu hv hg htie
    have hrot :
        ((F P second).rotate.singletonContext s u v g hs hu hv hg).schur =
          ((H P second).rotate.singletonContext s u v g hs hu hv hg).schur ↔
        (s,u,v,g)=(P.b-P.q,P.q,P.g,P.g-P.b) :=
      ⟨rotated_context_locus_at_tie P hp second s u v g hs hu hv hg htie,
        rotated_context_eq_at_locus P hp second s u v g hs hu hv hg⟩
    have hvalue := (candidate_context_choice P second mf rf s u v g hs hu hv hg).symm.trans
      (he.trans (candidate_context_choice P second mr rr s u v g hs hu hv hg))
    exact (choice_classification hfr hhr hun hmi hrev hrot mf rf mr rr).mp hvalue
  · rintro (hsame | ⟨hrf,hrr,hlocus⟩)
    · have hD := congrArg (fun c : Bool×Bool => coreCandidate P second c.1 c.2) hsame
      have hctx := congrArg (fun Q : BetaDiagram 5 => Q.singletonContext s u v g hs hu hv hg) hD
      exact congrArg (fun D : BetaDiagram 7 => D.schur) hctx
    · have hrot := rotated_context_eq_at_locus P hp second s u v g hs hu hv hg hlocus
      have hvalue := rotated_choice_eq (a :=
        ((F P second).singletonContext s u v g hs hu hv hg).schur) (c :=
        ((H P second).singletonContext s u v g hs hu hv hg).schur) hrot mf mr
      have hvalue' :
          fourChoice ((F P second).singletonContext s u v g hs hu hv hg).schur
            ((F P second).rotate.singletonContext s u v g hs hu hv hg).schur
            ((H P second).singletonContext s u v g hs hu hv hg).schur
            ((H P second).rotate.singletonContext s u v g hs hu hv hg).schur mf rf =
          fourChoice ((F P second).singletonContext s u v g hs hu hv hg).schur
            ((F P second).rotate.singletonContext s u v g hs hu hv hg).schur
            ((H P second).singletonContext s u v g hs hu hv hg).schur
            ((H P second).rotate.singletonContext s u v g hs hu hv hg).schur mr rr := by
        rw [hrf,hrr]
        exact hvalue
      exact (candidate_context_choice P second mf rf s u v g hs hu hv hg).trans
        (hvalue'.trans (candidate_context_choice P second mr rr s u v g hs hu hv hg).symm)

theorem four_core_context_margins_eq (P : Parameters) (hp : P.q < P.b)
    (second mf rf mr rr : Bool) (s u v g up vp gp : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hup : 0 < up) (hvp : 0 < vp) (hgp : 0 < gp)
    (he : ((coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg).schur =
      ((coreCandidate P second mr rr).singletonContext s up vp gp hs hup hvp hgp).schur) :
    u=up ∧ v=vp ∧ g=gp := by
  let Q := coreCandidate P second mf rf
  let W := coreCandidate P second mr rr
  have hQ : Q.Connected := coreCandidate_connected P second mf rf
  have hW : W.Connected := coreCandidate_connected P second mr rr
  have hZQ : Q.ZeroFree := coreCandidate_zeroFree P hp second mf rf
  have hZW : W.ZeroFree := coreCandidate_zeroFree P hp second mr rr
  have hcore : Q.schur=W.schur := coreCandidate_schur_eq P second mf rf mr rr
  by_cases hsmall : u < v
  · exact BetaDiagram.singleton_strict_top_margins_eq Q W hQ hW hZQ hZW hcore
      s u v g up vp gp hs hu hv hg hup hvp hgp hsmall he
  · obtain ⟨hveq,hendpoint⟩ :=
      BetaDiagram.singleton_bottom_endpoint_eq_of_schur_eq Q W hQ hW hcore
        s u v g up vp gp hs hu hv hg hup hvp hgp (by omega) he
    subst vp
    have hsame : (mf,rf) = (mr,rr) := by
      by_contra hne
      exact (coreCandidate_endpoint_separation P hp second mf rf mr rr hne v hv).2 hendpoint
    have hm : mf=mr := congrArg Prod.fst hsame
    have hr : rf=rr := congrArg Prod.snd hsame
    have hT : Q.TranslationEquivalent W := by
      refine ⟨0,?_,?_⟩ <;> intro i <;> simp [Q,W,hm,hr]
    obtain ⟨hueq,hgeq⟩ :=
      BetaDiagram.singleton_top_margin_of_bottom_translation Q W hT s u up v g gp
        hs hu hup hv hg hgp he
    exact ⟨hueq,rfl,hgeq⟩

private theorem translation_symm {n : ℕ} {D E : BetaDiagram n}
    (h : D.TranslationEquivalent E) : E.TranslationEquivalent D := by
  obtain ⟨c,hr,hc⟩ := h
  refine ⟨-c,?_,?_⟩ <;> intro i
  · have := hr i
    omega
  · have := hc i
    omega

private theorem translation_trans {n : ℕ} {D E F : BetaDiagram n}
    (h : D.TranslationEquivalent E) (h' : E.TranslationEquivalent F) :
    D.TranslationEquivalent F := by
  obtain ⟨c,hr,hc⟩ := h
  obtain ⟨d,hr',hc'⟩ := h'
  refine ⟨c+d,?_,?_⟩ <;> intro i
  · have := hr i
    have := hr' i
    omega
  · have := hc i
    have := hc' i
    omega

private theorem candidate_exceptional_member (P : Parameters) (second middle rotated : Bool) :
    FiveNegative.ExceptionalMember P second (coreCandidate P second middle rotated) := by
  cases middle <;> cases rotated
  · exact Or.inr (FiveNegative.actual_orbit_refl _)
  · exact Or.inr (Or.inr ⟨0,fun i => by simp [coreCandidate,BetaDiagram.rotate],
      fun i => by simp [coreCandidate,BetaDiagram.rotate]⟩)
  · exact Or.inl (FiveNegative.actual_orbit_refl _)
  · exact Or.inl (Or.inr ⟨0,fun i => by simp [coreCandidate,BetaDiagram.rotate],
      fun i => by simp [coreCandidate,BetaDiagram.rotate]⟩)

private theorem exceptional_member_candidate (P : Parameters) (second : Bool)
    (W : BetaDiagram 5) (h : FiveNegative.ExceptionalMember P second W) :
    ∃ middle rotated, W.TranslationEquivalent (coreCandidate P second middle rotated) := by
  rcases h with ht | ht
  · rcases ht with ht | hr
    · exact ⟨true,false,ht⟩
    · exact ⟨true,true,(W.translation_rotate_iff_rotation (F P second)).mpr hr⟩
  · rcases ht with ht | hr
    · exact ⟨false,false,ht⟩
    · exact ⟨false,true,(W.translation_rotate_iff_rotation (H P second)).mpr hr⟩

theorem exceptional_singleton_first_cut_class (P : Parameters) (hp : P.q < P.b)
    (second mf rf : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (F : BetaDiagram 7) (hF : F.Connected) (hZF : F.ZeroFree)
    (hcut : F.row (0 : Fin 5).succ.succ < F.col 0)
    (he : ((coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg).schur =
      F.schur) :
    ∃ mr rr,
      F.TranslationEquivalent
        ((coreCandidate P second mr rr).singletonContext s u v g hs hu hv hg) ∧
      ((mf,rf) = (mr,rr) ∨
        (rf=true ∧ rr=true ∧ (s,u,v,g)=(P.b-P.q,P.q,P.g,P.g-P.b))) := by
  let Q := coreCandidate P second mf rf
  have hQ : Q.Connected := coreCandidate_connected P second mf rf
  let hPF := F.positiveCorner_of_connected_zeroFree hF hZF
  let W := (F.cornerDiagram hPF).tail
  obtain ⟨sp,up,vp,gp,hsp,hup,hvp,hgp,hTF⟩ :=
    F.singleton_parent_of_first_cut hPF hcut
  have hparent : (Q.singletonContext s u v g hs hu hv hg).schur =
      (W.singletonContext sp up vp gp hsp hup hvp hgp).schur := he.trans hTF.schur_eq
  have hprod := (Q.singletonContext s u v g hs hu hv hg).cornerPolynomial_eq_of_schur_eq
    (W.singletonContext sp up vp gp hsp hup hvp hgp)
    (Q.singletonContext_connected s u v g hs hu hv hg)
    (W.singletonContext_connected sp up vp gp hsp hup hvp hgp) hparent
  rw [BetaDiagram.singletonContext_cornerPolynomial,
    BetaDiagram.singletonContext_cornerPolynomial] at hprod
  have hdiv : complete sp ∣ complete s*Q.schur := by
    rw [hprod]
    exact dvd_mul_right _ _
  have hsEq : sp=s := by
    obtain hd | hd := (BetaDiagram.complete_prime sp hsp).dvd_mul.mp hdiv
    · exact (BetaDiagram.complete_dvd_complete_iff sp s hsp hs).mp hd
    · exact (Q.complete_not_dvd_connected hQ sp hsp hd).elim
  subst sp
  have hcore : Q.schur=W.schur :=
    mul_left_cancel₀ ((complete_ne_zero_iff s).2 hs.le) hprod
  have hW : W.Connected := by
    apply W.connected_of_schur_irreducible (by decide)
    rw [←hcore]
    exact Q.schur_irreducible hQ
  obtain ⟨hn,hmem⟩ := (FiveNegative.five_base_complete_class P second Q hQ
    (candidate_exceptional_member P second mf rf) W hW).mp hcore
  have hmem' : FiveNegative.ExceptionalMember P second W := by
    have hr : hn=rfl := Subsingleton.elim _ _
    rw [hr] at hmem
    simpa [BetaDiagram.castOrder] using hmem
  obtain ⟨mr,rr,hTW⟩ := exceptional_member_candidate P second W hmem'
  have hCTX := BetaDiagram.singletonContext_translation W (coreCandidate P second mr rr)
    hTW s up vp gp hs hup hvp hgp
  have hLiteral := hparent.trans hCTX.schur_eq
  obtain ⟨huEq,hvEq,hgEq⟩ := four_core_context_margins_eq P hp second mf rf mr rr
    s u v g up vp gp hs hu hv hg hup hvp hgp hLiteral
  subst up
  subst vp
  subst gp
  refine ⟨mr,rr,translation_trans hTF hCTX,?_⟩
  exact (four_core_context_equality_iff P hp second mf rf mr rr s u v g hs hu hv hg).mp hLiteral

private theorem rotate_zeroFree {n : ℕ} (D : BetaDiagram n) (hD : D.ZeroFree) :
    D.rotate.ZeroFree := by
  intro i j he
  apply hD j.rev i.rev
  change -D.col i.rev = -D.row j.rev at he
  omega

private theorem motion_of_cast_translation {n : ℕ} (D : BetaDiagram 7)
    (E : BetaDiagram n) (hn : n=7) (h : (E.castOrder hn).TranslationEquivalent D) :
    D.MotionEquivalent E := by
  refine ⟨hn.symm,Or.inl ?_⟩
  exact translation_symm h

private theorem motion_of_cast_rotated_translation {n : ℕ} (D : BetaDiagram 7)
    (E : BetaDiagram n) (hn : n=7) (h : (E.castOrder hn).rotate.TranslationEquivalent D) :
    D.MotionEquivalent E := by
  refine ⟨hn.symm,Or.inr ?_⟩
  exact (D.translation_rotate_iff_rotation (E.castOrder hn)).mp (translation_symm h)

private theorem motion_schur {n : ℕ} (D : BetaDiagram 7) (E : BetaDiagram n)
    (h : D.MotionEquivalent E) : D.schur=E.schur := by
  obtain ⟨hn,hT|hR⟩ := h
  · have he := hT.schur_eq
    rw [BetaDiagram.castOrder_schur] at he
    exact he
  · have hT := (D.translation_rotate_iff_rotation (E.castOrder hn.symm)).mpr hR
    have he := hT.schur_eq
    rw [BetaDiagram.rotate_schur,BetaDiagram.castOrder_schur] at he
    exact he

private theorem motion_of_cast_motion {n : ℕ} (D : BetaDiagram 7)
    (E : BetaDiagram n) (hn : n=7) (h : D.MotionEquivalent (E.castOrder hn)) :
    D.MotionEquivalent E := by
  cases hn
  exact h

private theorem exceptional_singleton_same_order (P : Parameters) (hp : P.q < P.b)
    (second mf rf : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (F : BetaDiagram 7) (hF : F.Connected)
    (he : ((coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg).schur=F.schur) :
    ∃ mr rr,
      ((mf,rf)=(mr,rr) ∨ (rf=true ∧ rr=true ∧ (s,u,v,g)=(P.b-P.q,P.q,P.g,P.g-P.b))) ∧
      ((coreCandidate P second mr rr).singletonContext s u v g hs hu hv hg).MotionEquivalent F := by
  let Q := coreCandidate P second mf rf
  let D := Q.singletonContext s u v g hs hu hv hg
  have hQ : Q.Connected := coreCandidate_connected P second mf rf
  have hZQ : Q.ZeroFree := coreCandidate_zeroFree P hp second mf rf
  have hD : D.Connected := Q.singletonContext_connected s u v g hs hu hv hg
  have hZD : D.ZeroFree := Q.singletonContext_zeroFree hZQ s u v g hs hu hv hg
  have hZF : F.ZeroFree := D.zeroFree_of_schur_eq F hD hF hZD he
  obtain hcut | hcut := BetaDiagram.singleton_mate_singleton_side Q hQ s u v g
    hs hu hv hg F hF hZF he
  · obtain ⟨mr,rr,hT,hallowed⟩ := exceptional_singleton_first_cut_class P hp second mf rf
      s u v g hs hu hv hg F hF hZF hcut he
    exact ⟨mr,rr,hallowed,motion_of_cast_translation _ F rfl hT⟩
  · have hFR : F.rotate.Connected := F.rotate_connected hF
    have hZFR : F.rotate.ZeroFree := rotate_zeroFree F hZF
    have hDR : D.schur=F.rotate.schur := he.trans F.rotate_schur.symm
    obtain ⟨mr,rr,hT,hallowed⟩ := exceptional_singleton_first_cut_class P hp second mf rf
      s u v g hs hu hv hg F.rotate hFR hZFR hcut hDR
    exact ⟨mr,rr,hallowed,motion_of_cast_rotated_translation _ F rfl hT⟩

/-- The complete connected class against arbitrary mates and arbitrary initial row counts. -/
theorem exceptional_singleton_complete_class {n : ℕ} (P : Parameters) (hp : P.q < P.b)
    (second mf rf : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (E : BetaDiagram n) (hE : E.Connected) :
    ((coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg).schur = E.schur ↔
      ∃ mr rr,
        ((mf,rf) = (mr,rr) ∨
          (rf=true ∧ rr=true ∧ (s,u,v,g)=(P.b-P.q,P.q,P.g,P.g-P.b))) ∧
        ((coreCandidate P second mr rr).singletonContext s u v g hs hu hv hg).MotionEquivalent E := by
  constructor
  · intro he
    let D := (coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg
    have hn : n=7 := (D.row_count_of_schur_eq E he).symm
    have hF : (E.castOrder hn).Connected := (E.castOrder_connected hn).mpr hE
    have hDF : D.schur=(E.castOrder hn).schur := he.trans (E.castOrder_schur hn).symm
    obtain ⟨mr,rr,hallowed,hmotion⟩ := exceptional_singleton_same_order P hp second mf rf
      s u v g hs hu hv hg (E.castOrder hn) hF hDF
    exact ⟨mr,rr,hallowed,motion_of_cast_motion _ E hn hmotion⟩
  · rintro ⟨mr,rr,hallowed,hmotion⟩
    have hlocal := (four_core_context_equality_iff P hp second mf rf mr rr
      s u v g hs hu hv hg).mpr hallowed
    exact hlocal.trans (motion_schur _ E hmotion)

theorem exceptional_singleton_rotationRigid (P : Parameters) (hp : P.q < P.b)
    (second mf rf : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hno : ¬ (rf=true ∧ (s,u,v,g)=(P.b-P.q,P.q,P.g,P.g-P.b))) :
    ((coreCandidate P second mf rf).singletonContext s u v g hs hu hv hg).RotationRigid := by
  intro n E hE he
  obtain ⟨mr,rr,hallowed,hmotion⟩ :=
    (exceptional_singleton_complete_class P hp second mf rf s u v g hs hu hv hg E hE).mp he.symm
  rcases hallowed with hsame | ⟨hrf,hrr,hlocus⟩
  · have hm : mf=mr := congrArg Prod.fst hsame
    have hr : rf=rr := congrArg Prod.snd hsame
    simpa only [hm,hr] using hmotion
  · exact False.elim (hno ⟨hrf,hlocus⟩)

private theorem translation_rotate {n : ℕ} {D E : BetaDiagram n}
    (h : D.TranslationEquivalent E) : D.rotate.TranslationEquivalent E.rotate := by
  obtain ⟨c,hr,hc⟩ := h
  refine ⟨-c,?_,?_⟩ <;> intro i
  · have := hc i.rev
    change -D.col i.rev = -E.col i.rev + -c
    omega
  · have := hr i.rev
    change -D.row i.rev = -E.row i.rev + -c
    omega

theorem exceptionalSingleton_not_motion (P : Parameters) (hp : P.q < P.b)
    (second middle other : Bool) (hne : middle ≠ other) :
    ¬ (exceptionalSingleton P hp second middle).MotionEquivalent
      (exceptionalSingleton P hp second other) := by
  rintro ⟨hn,hmotion⟩
  have hhn : hn=rfl := Subsingleton.elim _ _
  rw [hhn] at hmotion
  simp only [BetaDiagram.castOrder] at hmotion
  let T := singletonTenParameters P hp
  let k := singletonTenKind second middle
  let l := singletonTenKind second other
  have hD := exceptionalSingleton_translation P hp second middle
  have hE := exceptionalSingleton_translation P hp second other
  have hkl : k ≠ l := by
    cases second <;> cases middle <;> cases other <;>
      simp only [k,l,singletonTenKind,Bool.false_eq_true,↓reduceIte] <;>
      first | exact False.elim (hne rfl) | decide
  rcases hmotion with hT | hR
  · exact T.not_translation k l hkl
      (translation_trans (translation_symm hD) (translation_trans hT hE))
  · have hTR := ((exceptionalSingleton P hp second middle).translation_rotate_iff_rotation
      (exceptionalSingleton P hp second other)).mpr hR
    have hTR' := translation_trans (translation_symm hD)
      (translation_trans hTR (translation_rotate hE))
    exact T.not_rotation k l (((T.diagram k).translation_rotate_iff_rotation
      (T.diagram l)).mp hTR')

private theorem bool_values_eq {α : Type*} (f : Bool → α) (he : f true=f false)
    (a b : Bool) : f a=f b := by
  cases a <;> cases b
  · rfl
  · exact he.symm
  · exact he
  · rfl

private theorem exceptionalSingleton_connected (P : Parameters) (hp : P.q < P.b)
    (second middle : Bool) : (exceptionalSingleton P hp second middle).Connected := by
  unfold exceptionalSingleton
  exact BetaDiagram.singletonContext_connected (n := 4) _ _ _ _ _ _ _ _ _

theorem exceptionalSingleton_not_rotationRigid (P : Parameters) (hp : P.q < P.b)
    (second middle : Bool) : ¬ (exceptionalSingleton P hp second middle).RotationRigid := by
  intro hrigid
  let E := exceptionalSingleton P hp second (!middle)
  have hE : E.Connected := exceptionalSingleton_connected P hp second (!middle)
  have he : E.schur=(exceptionalSingleton P hp second middle).schur :=
    bool_values_eq (fun b => (exceptionalSingleton P hp second b).schur)
      (exceptionalSingleton_schur_eq P hp second) (!middle) middle
  have hm := hrigid 7 E hE he
  exact exceptionalSingleton_not_motion P hp second middle (!middle)
    (by cases middle <;> decide) hm

/-- The exact singleton exception locus, including both opening types and orientations. -/
theorem exceptional_singleton_rotationRigid_iff (P : Parameters) (hp : P.q < P.b)
    (second middle rotated : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    ((coreCandidate P second middle rotated).singletonContext s u v g hs hu hv hg).RotationRigid ↔
      ¬ (rotated=true ∧ (s,u,v,g)=(P.b-P.q,P.q,P.g,P.g-P.b)) := by
  constructor
  · intro hrigid hbad
    rcases hbad with ⟨hr,hlocus⟩
    obtain ⟨hs',hu',hv',hg'⟩ := singleton_locus_positive P hp
    have hflag := congrArg (fun r =>
      (coreCandidate P second middle r).singletonContext s u v g hs hu hv hg) hr
    have hparams := context_parameters_congr (coreCandidate P second middle true)
      s u v g (P.b-P.q) P.q P.g (P.g-P.b) hs hu hv hg hs' hu' hv' hg' hlocus
    have htarget : (coreCandidate P second middle true).singletonContext
        (P.b-P.q) P.q P.g (P.g-P.b) hs' hu' hv' hg'=exceptionalSingleton P hp second middle := by
      cases middle <;> rfl
    have hDiagram := hflag.trans (hparams.trans htarget)
    exact exceptionalSingleton_not_rotationRigid P hp second middle
      (Eq.mp (congrArg BetaDiagram.RotationRigid hDiagram) hrigid)
  · exact exceptional_singleton_rotationRigid P hp second middle rotated s u v g hs hu hv hg

end SkewJacobiNegative.FiveExceptional
