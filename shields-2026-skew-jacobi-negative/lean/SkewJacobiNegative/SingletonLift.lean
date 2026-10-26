/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.SingletonContexts
import SkewJacobiNegative.EndpointLeaders
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Literal recovery of arbitrary cofactor components

Coefficient-one normalization and actual connected-component factor matching
used by `lem:singleton-lift` in `shields-2026-skew-jacobi-negative.tex`.
The comparison diagram's order and component decomposition are independent.
-/

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
variable {n m : ℕ}

/-- Connected factors dividing one another are literally equal. -/
theorem schur_eq_of_connected_dvd (E : BetaDiagram n) (F : BetaDiagram m)
    (hE : E.Connected) (hF : F.Connected) (h : E.schur ∣ F.schur) :
    E.schur = F.schur := by
  apply E.schur_eq_of_associated F
  exact (E.schur_irreducible hE).associated_of_dvd (F.schur_irreducible hF) h

/-- A same-sign sum of two actual Schur functions cannot vanish. -/
theorem schur_add_schur_ne_zero (E : BetaDiagram n) (F : BetaDiagram m) :
    E.schur + F.schur ≠ 0 := by
  intro hz
  have hp : E.schur = (-1 : ℚ) • F.schur := by
    simpa using (eq_neg_of_add_eq_zero_left hz)
  have he := E.schur_eq_of_proportional F (-1) hp
  have h2 : (2 : CompleteRing) * F.schur = 0 := by
    rw [he] at hz
    linear_combination hz
  exact (mul_ne_zero (by norm_num) F.schur_ne_zero) h2

/-- An irreducible actual connected determinant cannot equal a product of
two nonempty component determinants, with either sign (`eq:margin-separator`). -/
theorem schur_product_add_connected_ne_zero {k : ℕ}
    (E : BetaDiagram n) (F : BetaDiagram m) (T : BetaDiagram k)
    (hn : 0 < n) (hm : 0 < m) (hT : T.Connected) :
    E.schur * F.schur + T.schur ≠ 0 := by
  intro hz
  have he : T.schur = (-E.schur) * F.schur := by
    linear_combination hz
  obtain hE | hF := (T.schur_irreducible hT).isUnit_or_isUnit he
  · exact E.schur_not_isUnit hn (by simpa using hE)
  · exact F.schur_not_isUnit hm hF

/-- Products of actual connected diagrams recover their exact polynomial
inventory, with all multiplicities and no size restriction. -/
theorem connected_product_functions_eq
    (xs ys : List (Σ k : ℕ, BetaDiagram k))
    (hx : ∀ X ∈ xs, X.2.Connected) (hy : ∀ Y ∈ ys, Y.2.Connected)
    (he : (xs.map (fun X => X.2.schur)).prod =
      (ys.map (fun Y => Y.2.schur)).prod) :
    ((xs.map (fun X => X.2.schur)) : Multiset CompleteRing) =
      ((ys.map (fun Y => Y.2.schur)) : Multiset CompleteRing) := by
  let f : Multiset CompleteRing := xs.map (fun X => X.2.schur)
  let g : Multiset CompleteRing := ys.map (fun Y => Y.2.schur)
  have hf : ∀ a ∈ f, Irreducible a := by
    intro a ha
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp (show a ∈ xs.map (fun X => X.2.schur) by
      simpa only [f, Multiset.mem_coe] using ha)
    exact X.2.schur_irreducible (hx X hX)
  have hg : ∀ a ∈ g, Irreducible a := by
    intro a ha
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp (show a ∈ ys.map (fun X => X.2.schur) by
      simpa only [g, Multiset.mem_coe] using ha)
    exact X.2.schur_irreducible (hy X hX)
  have hprod : f.prod = g.prod := by simpa only [f, g, Multiset.prod_coe] using he
  have hrel := UniqueFactorizationMonoid.factors_unique hf hg
    (show Associated f.prod g.prod by
      rw [hprod])
  apply Multiset.rel_eq.mp
  apply hrel.mono
  intro a ha b hb hab
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp (show a ∈ xs.map (fun X => X.2.schur) by
    simpa only [f, Multiset.mem_coe] using ha)
  obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp (show b ∈ ys.map (fun Y => Y.2.schur) by
    simpa only [g, Multiset.mem_coe] using hb)
  exact X.2.schur_eq_of_associated Y.2 hab

/-- Factor matches carry their actual row counts, read from polynomial total degree. -/
theorem product_component_matching
    (xs ys : List (Σ k : ℕ, BetaDiagram k))
    (hx : ∀ X ∈ xs, X.2.Connected) (hy : ∀ Y ∈ ys, Y.2.Connected)
    (he : (xs.map (fun X => X.2.schur)).prod =
      (ys.map (fun Y => Y.2.schur)).prod) :
    Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k =>
      X.2.schur = Y.2.schur ∧ X.1 = Y.1)
      (xs : Multiset _) (ys : Multiset _) := by
  have hfunc : Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k => X.2.schur = Y.2.schur)
      (xs : Multiset _) (ys : Multiset _) := by
    apply Multiset.rel_map.mp
    apply Multiset.rel_eq.mpr
    exact connected_product_functions_eq xs ys hx hy he
  apply hfunc.mono
  intro X _ Y _ hXY
  refine ⟨hXY, ?_⟩
  have hdeg := congrArg MvPolynomial.totalDegree hXY
  simpa only [schur_totalDegree] using hdeg

/-- A positive-order diagram has at least one genuine geometric component. -/
theorem component_list_length_pos (D : BetaDiagram n)
    (C : ComponentDecomposition D) (hn : 0 < n) : 0 < C.components.length := by
  by_contra h
  have hl : C.components = [] := List.length_eq_zero_iff.mp (by omega)
  have hr := C.component_rows_sum
  rw [hl] at hr
  simp only [List.map_nil, List.sum_nil] at hr
  omega

/-- A decomposition with one leaf is literally its connected source diagram. -/
theorem component_list_singleton (D : BetaDiagram n)
    (C : ComponentDecomposition D) (hlen : C.components.length = 1) :
    D.Connected ∧ C.components = [⟨n, D⟩] := by
  cases C with
  | empty D =>
    simp only [ComponentDecomposition.components, List.length_nil] at hlen
    omega
  | connected D hD => exact ⟨hD, rfl⟩
  | cut D ha hb he hcut L R =>
    have hL := component_list_length_pos _ L ha
    have hR := component_list_length_pos _ R hb
    simp only [ComponentDecomposition.components, List.length_append] at hlen
    omega

/-- Two recovered factors imply one actual beta cut with connected pieces.
Their original order is retained, rather than supplied as a mate hypothesis. -/
theorem component_list_two_cut (D : BetaDiagram n)
    (C : ComponentDecomposition D) (hlen : C.components.length = 2) :
    ∃ (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (he : a + b = n),
      (D.reindexOrder he).row ⟨a, by omega⟩ <
        (D.reindexOrder he).col ⟨a - 1, by omega⟩ ∧
      (D.reindexOrder he).betaPrefix.Connected ∧
      (D.reindexOrder he).suffix.Connected ∧
      C.components = [⟨a, (D.reindexOrder he).betaPrefix⟩,
        ⟨b, (D.reindexOrder he).suffix⟩] := by
  cases C with
  | empty D =>
    simp only [ComponentDecomposition.components, List.length_nil] at hlen
    omega
  | connected D hD =>
    simp only [ComponentDecomposition.components, List.length_cons,
      List.length_nil] at hlen
    omega
  | cut D ha hb he hcut L R =>
    have hL := component_list_length_pos _ L ha
    have hR := component_list_length_pos _ R hb
    simp only [ComponentDecomposition.components, List.length_append] at hlen
    obtain ⟨hLC, hLs⟩ := component_list_singleton _ L (by omega)
    obtain ⟨hRC, hRs⟩ := component_list_singleton _ R (by omega)
    refine ⟨_, _, ha, hb, he, hcut, hLC, hRC, ?_⟩
    simp only [ComponentDecomposition.components, hLs, hRs,
      List.cons_append, List.nil_append]

/-- All component functions are recovered from equality, including repeated factors. -/
theorem component_functions_eq (D : BetaDiagram n) (E : BetaDiagram m)
    (C : ComponentDecomposition D) (K : ComponentDecomposition E)
    (he : D.schur = E.schur) :
    ((C.components.map (fun X => X.2.schur)) : Multiset CompleteRing) =
      ((K.components.map (fun X => X.2.schur)) : Multiset CompleteRing) := by
  exact connected_product_functions_eq C.components K.components
    C.components_connected K.components_connected
    (C.component_schur_product.symm.trans (he.trans K.component_schur_product))

/-- Actual geometric leaves match by their functions, without a mate profile assumption. -/
theorem component_function_matching (D : BetaDiagram n) (E : BetaDiagram m)
    (C : ComponentDecomposition D) (K : ComponentDecomposition E)
    (he : D.schur = E.schur) :
    Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k => X.2.schur = Y.2.schur)
      (C.components : Multiset _) (K.components : Multiset _) := by
  apply Multiset.rel_map.mp
  apply Multiset.rel_eq.mpr
  simpa only [Multiset.map_coe] using component_functions_eq D E C K he

/-- Core rigidity turns factor recovery into actual translation or rotation of every leaf. -/
theorem component_motion_matching (D : BetaDiagram n) (E : BetaDiagram m)
    (C : ComponentDecomposition D) (K : ComponentDecomposition E)
    (he : D.schur = E.schur)
    (hR : ∀ X ∈ C.components, X.2.RotationRigid) :
    Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k => X.2.MotionEquivalent Y.2)
      (C.components : Multiset _) (K.components : Multiset _) := by
  apply (D.component_function_matching E C K he).mono
  intro X hX Y hY h
  exact hR X (by simpa using hX) Y.1 Y.2
    (K.components_connected Y (by simpa using hY)) h.symm

/-- A literal one-row diagram realizing the positive singleton generator. -/
def singletonDiagram (s : ℤ) (hs : 0 < s) : BetaDiagram 1 where
  row _ := s
  col _ := 0
  row_strictAnti := by
    intro i j hij
    have he : i = j := Subsingleton.elim _ _
    exact (lt_irrefl _ (he ▸ hij)).elim
  col_strictAnti := by
    intro i j hij
    have he : i = j := Subsingleton.elim _ _
    exact (lt_irrefl _ (he ▸ hij)).elim
  row_nonempty _ := hs

@[simp] theorem singletonDiagram_schur (s : ℤ) (hs : 0 < s) :
    (singletonDiagram s hs).schur = complete s := by
  simp [schur, matrix, singletonDiagram, Matrix.det_unique]

theorem singletonDiagram_connected (s : ℤ) (hs : 0 < s) :
    (singletonDiagram s hs).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  omega

theorem singletonDiagram_rigid (s : ℤ) (hs : 0 < s) :
    (singletonDiagram s hs).RotationRigid := by
  apply rotationRigid_of_nonnegative _ (singletonDiagram_connected s hs)
  intro i j
  exact hs.le

/-- A positive complete generator is prime in the actual rational complete ring. -/
theorem complete_prime (s : ℤ) (hs : 0 < s) : Prime (complete s) := by
  apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
  simpa only [singletonDiagram_schur] using (singletonDiagram s hs).schur_irreducible_one

/-- Different positive complete generators do not divide one another. -/
theorem complete_dvd_complete_iff (s t : ℤ) (hs : 0 < s) (ht : 0 < t) :
    complete s ∣ complete t ↔ s = t := by
  constructor
  · intro h
    have he := (singletonDiagram s hs).schur_eq_of_connected_dvd
      (singletonDiagram t ht) (singletonDiagram_connected s hs)
      (singletonDiagram_connected t ht) (by simpa only [singletonDiagram_schur] using h)
    apply complete_injective_nonnegative hs.le ht.le
    simpa only [singletonDiagram_schur] using he
  · rintro rfl
    exact dvd_rfl

/-- Connected determinants with at least two rows cannot contain a linear singleton factor. -/
theorem complete_not_dvd_connected (Q : BetaDiagram (n + 2)) (hQ : Q.Connected)
    (s : ℤ) (hs : 0 < s) : ¬ complete s ∣ Q.schur := by
  intro h
  have he := (singletonDiagram s hs).schur_eq_of_connected_dvd Q
    (singletonDiagram_connected s hs) hQ (by simpa only [singletonDiagram_schur] using h)
  have hn := (singletonDiagram s hs).row_count_of_schur_eq Q he
  omega

/-- The strict top marker is divisible only by the increased singleton. -/
theorem singleton_top_marker_divisibility (Q : BetaDiagram (n + 2))
    (hQ : Q.Connected) (s q : ℤ) (hs : 0 < s) (hq : 0 < q) :
    ¬ complete s ∣ complete (s + q) * Q.schur ∧
      complete (s + q) ∣ complete (s + q) * Q.schur := by
  refine ⟨?_, dvd_mul_right _ _⟩
  intro h
  obtain h1 | h2 := (complete_prime s hs).dvd_mul.mp h
  · have he := (complete_dvd_complete_iff s (s + q) hs (by omega)).mp h1
    omega
  · exact Q.complete_not_dvd_connected hQ s hs h2

/-- The strict bottom marker is divisible only by the original singleton. -/
theorem singleton_bottom_marker_divisibility (Q : BetaDiagram (n + 2))
    (hQ : Q.Connected) (s q : ℤ) (hs : 0 < s) (hq : 0 < q) :
    complete s ∣ complete s * (Q.extendBottom q hq).schur ∧
      ¬ complete (s + q) ∣ complete s * (Q.extendBottom q hq).schur := by
  refine ⟨dvd_mul_right _ _, ?_⟩
  intro h
  obtain h1 | h2 := (complete_prime (s + q) (by omega)).dvd_mul.mp h
  · have he := (complete_dvd_complete_iff (s + q) s (by omega) hs).mp h1
    omega
  · exact (Q.extendBottom q hq).complete_not_dvd_connected
      (Q.extendBottom_connected hQ q hq) (s + q) (by omega) h2

/-- Neither singleton divides the tied sum.  This also proves nonvanishing
without exposing Schur positivity as an unproved certificate. -/
theorem singleton_tied_marker_divisibility (Q : BetaDiagram (n + 2))
    (hQ : Q.Connected) (s q : ℤ) (hs : 0 < s) (hq : 0 < q) :
    let T := complete (s + q) * Q.schur +
      complete s * (Q.extendBottom q hq).schur
    (¬ complete s ∣ T) ∧ (¬ complete (s + q) ∣ T) ∧ T ≠ 0 := by
  dsimp only
  have htop := Q.singleton_top_marker_divisibility hQ s q hs hq
  have hbot := Q.singleton_bottom_marker_divisibility hQ s q hs hq
  have h1 : ¬ complete s ∣ complete (s + q) * Q.schur +
      complete s * (Q.extendBottom q hq).schur := by
    intro h
    apply htop.1
    have hh := dvd_sub h hbot.1
    simpa only [add_sub_cancel_right] using hh
  have h2 : ¬ complete (s + q) ∣ complete (s + q) * Q.schur +
      complete s * (Q.extendBottom q hq).schur := by
    intro h
    apply hbot.2
    have hh := dvd_sub h htop.2
    simpa only [add_sub_cancel_left] using hh
  refine ⟨h1, h2, ?_⟩
  intro hz
  apply h1
  rw [hz]
  exact dvd_zero _

/-- Unique factorization matches actual source diagrams to all actual mate leaves.
The source list is not a prescribed decomposition of the mate. -/
theorem component_matching_of_product (E : BetaDiagram m)
    (K : ComponentDecomposition E) (L : List (Σ k : ℕ, BetaDiagram k))
    (hL : ∀ X ∈ L, X.2.Connected)
    (he : (L.map (fun X => X.2.schur)).prod = E.schur) :
    Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k => X.2.schur = Y.2.schur)
      (L : Multiset _) (K.components : Multiset _) := by
  apply Multiset.rel_map.mp
  apply Multiset.rel_eq.mpr
  simpa only [Multiset.map_coe] using
    connected_product_functions_eq L K.components hL K.components_connected
      (he.trans K.component_schur_product)

/-- Equality with two connected Schur factors forces one genuine beta-list cut
and two actual connected pieces; the mate is not assumed to have that shape. -/
theorem actual_cut_of_two_connected_factors {k : ℕ}
    (A : BetaDiagram n) (B : BetaDiagram m) (E : BetaDiagram k)
    (hA : A.Connected) (hB : B.Connected) (he : A.schur * B.schur = E.schur) :
    ∃ (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (horder : a + b = k),
      (E.reindexOrder horder).row ⟨a, by omega⟩ <
        (E.reindexOrder horder).col ⟨a - 1, by omega⟩ ∧
      (E.reindexOrder horder).betaPrefix.Connected ∧
      (E.reindexOrder horder).suffix.Connected := by
  obtain ⟨C⟩ := E.exists_componentDecomposition
  have hrel := E.component_matching_of_product C [⟨n, A⟩, ⟨m, B⟩]
    (by
      intro X hX
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact hA
      · exact hB)
    (by simpa only [List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using he)
  have hcard := Multiset.card_eq_card_of_rel hrel
  have hlen : C.components.length = 2 := by simpa using hcard.symm
  obtain ⟨a, b, ha, hb, horder, hcut, hLC, hRC, _⟩ :=
    E.component_list_two_cut C hlen
  exact ⟨a, b, ha, hb, horder, hcut, hLC, hRC⟩

/-- The actual maximal cofactor has its full singleton/core product polynomial. -/
theorem singletonContext_cornerPolynomial (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).cornerPolynomial = complete s * Q.schur := by
  simp only [singletonContext]
  have hm : (((Q.singletonCore s g hs hg).positiveBorder u v hu hv).shifted v).cornerBoard =
      ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).cornerBoard := by
    apply Matrix.ext
    intro i j
    simp [cornerBoard, betaBoard, shifted]
  rw [cornerPolynomial, hm, ← cornerPolynomial,
    positiveBorder_cornerPolynomial, singletonCore_schur]

/-- Every connected mate has the produced row count and zero-free actual core,
whose components are recovered with multiplicity from the singleton product. -/
theorem singleton_mate_components (Q : BetaDiagram (n + 1))
    (hQ : Q.Connected) (hZ : Q.ZeroFree)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (E : BetaDiagram m) (hE : E.Connected)
    (he : (Q.singletonContext s u v g hs hu hv hg).schur = E.schur) :
    ∃ hrow : m = n + 3,
      let F := E.castOrder hrow
      ∃ hP : F.PositiveCorner, F.ZeroFree ∧
        ∀ K : ComponentDecomposition (F.cornerDiagram hP),
          Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k => X.2.schur = Y.2.schur)
            ([(⟨1, singletonDiagram s hs⟩ : Σ k : ℕ, BetaDiagram k),
              (⟨n + 1, Q⟩ : Σ k : ℕ, BetaDiagram k)] : Multiset (Σ k : ℕ, BetaDiagram k))
            (K.components : Multiset _) := by
  let P := Q.singletonContext s u v g hs hu hv hg
  have hPconn := Q.singletonContext_connected s u v g hs hu hv hg
  have hPzero := Q.singletonContext_zeroFree hZ s u v g hs hu hv hg
  have hrow : m = n + 3 := (P.row_count_of_schur_eq E he).symm
  refine ⟨hrow, ?_⟩
  let F := E.castOrder hrow
  have hFconn : F.Connected := (E.castOrder_connected hrow).mpr hE
  have hFeq : P.schur = F.schur := by simpa only [F, castOrder_schur] using he
  have hFzero := P.zeroFree_of_schur_eq F hPconn hFconn hPzero hFeq
  let hPF := F.positiveCorner_of_connected_zeroFree hFconn hFzero
  refine ⟨hPF, hFzero, ?_⟩
  intro K
  apply (F.cornerDiagram hPF).component_matching_of_product K
    [⟨1, singletonDiagram s hs⟩, ⟨n + 1, Q⟩]
  · intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · exact singletonDiagram_connected s hs
    · exact hQ
  · have hcorner := P.cornerPolynomial_eq_of_schur_eq F hPconn hFconn hFeq
    have hprod : P.cornerPolynomial = complete s * Q.schur :=
      Q.singletonContext_cornerPolynomial s u v g hs hu hv hg
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, singletonDiagram_schur, cornerDiagram_schur] using hprod.symm.trans hcorner

/-- The legitimate endpoint-rigidity premise detects orientation at every positive
shift; no nonzero coefficient is assumed in this implication. -/
theorem endpointDifference_eq_zero_iff_of_rigidity (Q : BetaDiagram (n + 2))
    (hQ : Q.Connected) (t : ℤ) (ht : 0 < t)
    (hR : (Q.extendTop t ht).RotationRigid) :
    Q.endpointDifference t ht = 0 ↔ Q.Symmetric := by
  constructor
  · intro hz
    have he : (Q.extendBottom t ht).schur = (Q.extendTop t ht).schur :=
      (sub_eq_zero.mp hz).symm
    obtain htrans | hrot := ((Q.extendTop t ht).rotationRigid_iff_same_order.mp hR)
      (Q.extendBottom t ht) (Q.extendBottom_connected hQ t ht) he
    · exact (Q.extendTop_not_translation_extendBottom t ht htrans).elim
    · exact Q.symmetric_of_extendTop_rotation_extendBottom t ht hrot
  · intro h
    exact Q.endpointDifference_eq_zero_of_symmetric h t ht

/-- The actual two-border difference used to distinguish the two core orientations. -/
noncomputable def borderDifference (Q : BetaDiagram (n + 1)) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) : CompleteRing :=
  (Q.positiveBorder w v hw hv).schur - (Q.positiveBorder v w hv hw).schur

/-- Its candidate largest generator after the common corner cancels. -/
def borderDifferenceGenerator (Q : BetaDiagram (n + 1)) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) : ℕ+ :=
  ⟨(Q.largestLabel + max w v).toNat, by
    have hS := Q.largestLabel_pos
    have hm := le_max_left w v
    omega⟩

@[simp] theorem borderDifferenceGenerator_int (Q : BetaDiagram (n + 1))
    (w v : ℤ) (hw : 0 < w) (hv : 0 < v) :
    ((Q.borderDifferenceGenerator w v hw hv).val : ℤ) = Q.largestLabel + max w v := by
  change ((Q.largestLabel + max w v).toNat : ℤ) = _
  have hS := Q.largestLabel_pos
  have hm := le_max_left w v
  omega

/-- The equal signed corners cancel in the actual full polynomials. -/
theorem borderDifference_residual (Q : BetaDiagram (n + 1))
    (w v : ℤ) (hw : 0 < w) (hv : 0 < v) :
    let A := Q.positiveBorder w v hw hv
    let B := Q.positiveBorder v w hv hw
    Q.borderDifference w v hw hv =
      eraseGenerator A.borderLargestGenerator A.schur -
        eraseGenerator A.borderLargestGenerator B.schur := by
  dsimp only
  let A := Q.positiveBorder w v hw hv
  let B := Q.positiveBorder v w hv hw
  have hN : A.borderLargestGenerator = B.borderLargestGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (A.borderLargestGenerator.val : ℤ) = (B.borderLargestGenerator.val : ℤ)
    simp only [borderLargestGenerator_int, A, B, positiveBorder_largestLabel]
    ring
  have hA := Q.positiveBorder_corner_split w v hw hv
  have hB := Q.positiveBorder_corner_split v w hv hw
  have hEA := Q.positiveBorder_erased_corner w v hw hv
  have hEB := Q.positiveBorder_erased_corner v w hv hw
  dsimp only at hA hB hEA hEB
  rw [← hEA] at hA
  rw [← hEB] at hB
  change B.schur = (-1 : CompleteRing) ^ (n + 1) * Q.schur *
    MvPolynomial.X B.borderLargestGenerator +
    eraseGenerator B.borderLargestGenerator B.schur at hB
  rw [← hN] at hB
  change A.schur = (-1 : CompleteRing) ^ (n + 1) * Q.schur *
    MvPolynomial.X A.borderLargestGenerator +
    eraseGenerator A.borderLargestGenerator A.schur at hA
  change A.schur - B.schur = _
  calc
    A.schur - B.schur =
        ((-1 : CompleteRing) ^ (n + 1) * Q.schur * MvPolynomial.X A.borderLargestGenerator +
          eraseGenerator A.borderLargestGenerator A.schur) -
        ((-1 : CompleteRing) ^ (n + 1) * Q.schur * MvPolynomial.X A.borderLargestGenerator +
          eraseGenerator A.borderLargestGenerator B.schur) :=
      congrArg₂ (fun x y : CompleteRing => x - y) hA hB
    _ = eraseGenerator A.borderLargestGenerator A.schur -
        eraseGenerator A.borderLargestGenerator B.schur := by ring

/-- With the larger first margin, the true top coefficient is the signed
endpoint difference at the smaller margin. -/
theorem borderDifference_coefficient_of_gt (Q : BetaDiagram (n + 2))
    (w v : ℤ) (hw : 0 < w) (hv : 0 < v) (h : v < w) :
    MvPolynomial.pderiv (Q.borderDifferenceGenerator w v hw hv)
      (Q.borderDifference w v hw hv) =
      (-1) ^ (n + 2) * Q.endpointDifference v hv := by
  let A := Q.positiveBorder w v hw hv
  let B := Q.positiveBorder v w hv hw
  let k := Q.borderDifferenceGenerator w v hw hv
  have hN : A.borderLargestGenerator = B.borderLargestGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (A.borderLargestGenerator.val : ℤ) = (B.borderLargestGenerator.val : ℤ)
    simp only [borderLargestGenerator_int, A, B, positiveBorder_largestLabel]
    ring
  have hkA : k = A.borderSecondGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (k.val : ℤ) = (A.borderSecondGenerator.val : ℤ)
    simp only [k, borderDifferenceGenerator_int, borderSecondGenerator_int,
      A, positiveBorder_secondLabel, max_eq_left h.le, min_eq_right h.le]
    ring
  have hkB : k = B.borderSecondGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (k.val : ℤ) = (B.borderSecondGenerator.val : ℤ)
    simp only [k, borderDifferenceGenerator_int, borderSecondGenerator_int,
      B, positiveBorder_secondLabel, max_eq_left h.le, min_eq_left h.le]
    ring
  have hA : MvPolynomial.pderiv k (eraseGenerator A.borderLargestGenerator A.schur) =
      (-1) ^ (n + 3) * (Q.extendBottom v hv).schur := by
    rw [hkA]
    exact Q.positiveBorder_bottom_coefficient w v hw hv h
  have hB : MvPolynomial.pderiv k (eraseGenerator A.borderLargestGenerator B.schur) =
      (-1) ^ (n + 3) * (Q.extendTop v hv).schur := by
    rw [hN, hkB]
    exact Q.positiveBorder_top_coefficient v w hv hw h
  rw [borderDifference_residual, map_sub, hA, hB]
  simp only [show n + 3 = (n + 2) + 1 by omega, pow_succ, endpointDifference]
  ring

/-- Interchanging the two margins reverses the actual difference. -/
theorem borderDifference_flip (Q : BetaDiagram (n + 1))
    (w v : ℤ) (hw : 0 < w) (hv : 0 < v) :
    Q.borderDifference w v hw hv = -Q.borderDifference v w hv hw := by
  unfold borderDifference
  ring

/-- The produced leading index is independent of the order of the two margins. -/
theorem borderDifferenceGenerator_flip (Q : BetaDiagram (n + 1))
    (w v : ℤ) (hw : 0 < w) (hv : 0 < v) :
    Q.borderDifferenceGenerator w v hw hv = Q.borderDifferenceGenerator v w hv hw := by
  apply Subtype.ext
  simp only [borderDifferenceGenerator, max_comm]

/-- The other strict orientation has the opposite common sign. -/
theorem borderDifference_coefficient_of_lt (Q : BetaDiagram (n + 2))
    (w v : ℤ) (hw : 0 < w) (hv : 0 < v) (h : w < v) :
    MvPolynomial.pderiv (Q.borderDifferenceGenerator w v hw hv)
      (Q.borderDifference w v hw hv) =
      (-1) ^ (n + 3) * Q.endpointDifference w hw := by
  rw [borderDifference_flip, borderDifferenceGenerator_flip, map_neg,
    borderDifference_coefficient_of_gt Q v w hv hw h]
  simp only [show n + 3 = (n + 2) + 1 by omega, pow_succ]
  ring

/-- Every occupied generator of the full difference lies below the extracted top. -/
theorem borderDifference_vars_le (Q : BetaDiagram (n + 1))
    (w v : ℤ) (hw : 0 < w) (hv : 0 < v) (k : ℕ+)
    (hk : k ∈ (Q.borderDifference w v hw hv).vars) :
    (k.val : ℤ) ≤ Q.largestLabel + max w v := by
  let A := Q.positiveBorder w v hw hv
  let B := Q.positiveBorder v w hv hw
  have hN : A.borderLargestGenerator = B.borderLargestGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (A.borderLargestGenerator.val : ℤ) = (B.borderLargestGenerator.val : ℤ)
    simp only [borderLargestGenerator_int, A, B, positiveBorder_largestLabel]
    ring
  rw [borderDifference_residual, sub_eq_add_neg] at hk
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hk) with hA | hB
  · have hb := A.vars_le_secondLabel k hA
    simp only [A, positiveBorder_secondLabel] at hb
    omega
  · simp only [MvPolynomial.vars_neg] at hB
    rw [hN] at hB
    have hb := B.vars_le_secondLabel k hB
    simp only [B, positiveBorder_secondLabel] at hb
    omega

/-- A nonsymmetric core with its actual fixed leader has distinct borders
whenever the two positive margins differ. -/
theorem borderDifference_ne_zero (Q : BetaDiagram (n + 2))
    (hQ : Q.EndpointLeader) (w v : ℤ) (hw : 0 < w) (hv : 0 < v)
    (hne : w ≠ v) : Q.borderDifference w v hw hv ≠ 0 := by
  intro hz
  have hh := congrArg (MvPolynomial.pderiv (Q.borderDifferenceGenerator w v hw hv)) hz
  rcases lt_or_gt_of_ne hne with h | h
  · rw [borderDifference_coefficient_of_lt Q w v hw hv h, map_zero] at hh
    exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (EndpointLeader.difference_ne_zero Q hQ w hw)) hh
  · rw [borderDifference_coefficient_of_gt Q w v hw hv h, map_zero] at hh
    exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (EndpointLeader.difference_ne_zero Q hQ v hv)) hh

set_option backward.isDefEq.respectTransparency false in
/-- The coincident outer tops cannot cancel: the second endpoint difference has
the private moving generator of `eq:double-top`. -/
theorem singleton_double_top_ne_zero (Q : BetaDiagram (n + 1))
    (hQ : Q.EndpointLeader) (s u a : ℤ)
    (hs : 0 < s) (hu : 0 < u) (ha : s < a) :
    complete (s + u) * Q.endpointDifference a (by omega) -
      complete s * Q.endpointDifference (a + u) (by omega) ≠ 0 := by
  obtain ⟨κ, hκ, _, c, hc, hd⟩ := hQ
  obtain ⟨r, hr, hcl, hrl⟩ := hd a (by omega)
  obtain ⟨r', hr', hcl', hrl'⟩ := hd (a + u) (by omega)
  let k : ℕ+ := ⟨(κ + a + u).toNat, by omega⟩
  have hk : (k.val : ℤ) = κ + a + u := by dsimp [k]; omega
  have hsmall : LabelsBelow (Q.endpointDifference a (by omega)) (κ + a + u) := by
    rw [hr]
    apply LabelsBelow.add
    · apply LabelsBelow.mul (LabelsBelow.complete (by omega))
      intro v hv
      have := hcl v hv
      omega
    · intro v hv
      have := hrl v hv
      omega
  have h1 : k ∉ (complete (s + u) * Q.endpointDifference a (by omega)).vars :=
    (LabelsBelow.mul (LabelsBelow.complete (by omega)) hsmall).not_mem k hk
  have h2 : k ∉ (complete s).vars :=
    (LabelsBelow.complete (show s < κ + a + u by omega)).not_mem k hk
  have hdc : MvPolynomial.pderiv k (Q.endpointDifference (a + u) (by omega)) = c := by
    rw [hr', complete_of_pos (show 0 < κ + (a + u) by omega)]
    have he : (⟨(κ + (a + u)).toNat, by omega⟩ : ℕ+) = k := by
      apply Subtype.ext
      dsimp [k]
      congr 1
      omega
    rw [he, map_add, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X_self,
      MvPolynomial.pderiv_eq_zero_of_notMem_vars (hcl'.not_mem k (by omega)),
      MvPolynomial.pderiv_eq_zero_of_notMem_vars (hrl'.not_mem k (by omega))]
    ring
  intro hz
  have hh := congrArg (MvPolynomial.pderiv k) hz
  rw [map_sub, MvPolynomial.pderiv_eq_zero_of_notMem_vars h1,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_eq_zero_of_notMem_vars h2, hdc] at hh
  have hprod : complete s * c = 0 := by simpa using hh
  exact (mul_ne_zero ((complete_ne_zero_iff s).mpr (by omega)) hc) hprod

/-- The complete singleton-context orientation difference is nonzero in every
relative-margin regime, including a vanishing summand and equal outer tops. -/
theorem singleton_reflection_difference_ne_zero (Q : BetaDiagram (n + 2))
    (hQ : Q.EndpointLeader) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    complete (s + u) * Q.borderDifference (s + g) v (by omega) hv -
      complete s * Q.borderDifference (s + g + u) v (by omega) hv ≠ 0 := by
  let a := s + g
  have ha : s < a := by dsimp [a]; omega
  have hS := Q.largestLabel_pos
  have hcs := (complete_ne_zero_iff s).mpr hs.le
  have hcsu := (complete_ne_zero_iff (s + u)).mpr (by omega)
  change complete (s + u) * Q.borderDifference a v (by omega) hv -
    complete s * Q.borderDifference (a + u) v (by omega) hv ≠ 0
  rcases lt_trichotomy v (a + u) with hvlt | hveq | hvgt
  · let k := Q.borderDifferenceGenerator (a + u) v (by omega) hv
    have hk : (k.val : ℤ) = Q.largestLabel + a + u := by
      simp only [k, borderDifferenceGenerator_int, max_eq_left hvlt.le]
      ring
    have hsmall : LabelsBelow (Q.borderDifference a v (by omega) hv)
        (Q.largestLabel + a + u) := by
      intro j hj
      have hb := Q.borderDifference_vars_le a v (by omega) hv j hj
      omega
    have hfirst : k ∉
        (complete (s + u) * Q.borderDifference a v (by omega) hv).vars :=
      (LabelsBelow.mul (LabelsBelow.complete (by omega)) hsmall).not_mem k hk
    have hsnot : k ∉ (complete s).vars :=
      (LabelsBelow.complete (show s < Q.largestLabel + a + u by omega)).not_mem k hk
    intro hz
    have hh := congrArg (MvPolynomial.pderiv k) hz
    have hd : MvPolynomial.pderiv k (Q.borderDifference (a + u) v (by omega) hv) =
        (-1) ^ (n + 2) * Q.endpointDifference v hv :=
      Q.borderDifference_coefficient_of_gt (a + u) v (by omega) hv hvlt
    rw [map_sub, MvPolynomial.pderiv_eq_zero_of_notMem_vars hfirst,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_eq_zero_of_notMem_vars hsnot,
      hd, map_zero] at hh
    have hp : complete s * ((-1) ^ (n + 2) * Q.endpointDifference v hv) = 0 := by
      simpa only [zero_mul, zero_add, zero_sub, neg_eq_zero] using hh
    exact (mul_ne_zero hcs (mul_ne_zero
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (EndpointLeader.difference_ne_zero Q hQ v hv))) hp
  · have hsecond : Q.borderDifference (a + u) v (by omega) hv = 0 := by
      simp only [hveq, borderDifference, sub_self]
    rw [hsecond, mul_zero, sub_zero]
    exact mul_ne_zero hcsu
      (Q.borderDifference_ne_zero hQ a v (by omega) hv (by omega))
  · let k := Q.borderDifferenceGenerator a v (by omega) hv
    have hk : (k.val : ℤ) = Q.largestLabel + v := by
      simp only [k, borderDifferenceGenerator_int, max_eq_right (show a ≤ v by omega)]
    have hk2 : k = Q.borderDifferenceGenerator (a + u) v (by omega) hv := by
      apply Subtype.ext
      apply Int.ofNat.inj
      change (k.val : ℤ) =
        ((Q.borderDifferenceGenerator (a + u) v (by omega) hv).val : ℤ)
      have hg := Q.borderDifferenceGenerator_int (a + u) v (by omega) hv
      rw [max_eq_right hvgt.le] at hg
      exact hk.trans hg.symm
    have hsnot : k ∉ (complete s).vars :=
      (LabelsBelow.complete (show s < Q.largestLabel + v by omega)).not_mem k hk
    have hsunot : k ∉ (complete (s + u)).vars :=
      (LabelsBelow.complete (show s + u < Q.largestLabel + v by omega)).not_mem k hk
    have hd1 : MvPolynomial.pderiv k (Q.borderDifference a v (by omega) hv) =
        (-1) ^ (n + 3) * Q.endpointDifference a (by omega) :=
      Q.borderDifference_coefficient_of_lt a v (by omega) hv (by omega)
    have hd2 : MvPolynomial.pderiv k (Q.borderDifference (a + u) v (by omega) hv) =
        (-1) ^ (n + 3) * Q.endpointDifference (a + u) (by omega) := by
      rw [hk2]
      exact Q.borderDifference_coefficient_of_lt (a + u) v (by omega) hv hvgt
    intro hz
    have hh := congrArg (MvPolynomial.pderiv k) hz
    rw [map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_eq_zero_of_notMem_vars hsnot,
      MvPolynomial.pderiv_eq_zero_of_notMem_vars hsunot, hd1, hd2, map_zero] at hh
    have hn := mul_ne_zero (pow_ne_zero (n + 3) (neg_ne_zero.mpr (one_ne_zero :
      (1 : CompleteRing) ≠ 0))) (Q.singleton_double_top_ne_zero hQ s u a hs hu ha)
    apply hn
    linear_combination hh

/-- At recovered margins, reversing a nonsymmetric core changes the actual
singleton-parent polynomial.  All leading coefficients are produced internally. -/
theorem singletonContext_reflected_core_ne (Q : BetaDiagram (n + 2))
    (hQ : Q.EndpointLeader) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).schur ≠
      (Q.rotate.singletonContext s u v g hs hu hv hg).schur := by
  intro he
  apply Q.singleton_reflection_difference_ne_zero hQ s u v g hs hu hv hg
  have hz := sub_eq_zero.mpr he
  rw [singletonContext_schur, singletonContext_schur,
    positiveBorder_rotate_schur, positiveBorder_rotate_schur] at hz
  unfold borderDifference
  linear_combination hz

/-- The full source span, without a normalization assumption on the core. -/
theorem singletonContext_span (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).largestLabel =
      Q.largestLabel + s + g + u + v := by
  unfold largestLabel
  rw [singletonContext_row_zero, singletonContext_col_last]
  ring

/-- The upper separator level is exactly the full span minus the bottom margin. -/
theorem singletonContext_upper_separator (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).row 0 -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 1)).castSucc =
      Q.largestLabel + s + g + u := by
  change (Q.singletonContext s u v g hs hu hv hg).row 0 -
      (Q.singletonContext s u v g hs hu hv hg).col (Fin.last n).succ.castSucc = _
  rw [singletonContext_row_zero, singletonContext_col_core]
  unfold largestLabel
  ring

/-- The other separator level is the actual top core row against the last column. -/
theorem singletonContext_lower_separator (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).row (0 : Fin (n + 1)).succ.succ -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 2)) =
      Q.largestLabel + v := by
  rw [singletonContext_row_core, singletonContext_col_last]
  unfold largestLabel
  ring

/-- Both candidates' second last-column labels are fixed by the common span and top margin. -/
theorem singletonContext_second_last_level (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).row (0 : Fin (n + 2)).succ -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 2)) =
      Q.largestLabel + s + g + v := by
  rw [singletonContext_row_one, singletonContext_col_last]
  unfold largestLabel
  ring

/-- A generator strictly between the remaining separator levels and the second
last-column level is absent from the entire actual determinant. -/
theorem separator_between_levels_zero (D : BetaDiagram (n + 3)) (k : ℕ+)
    (hupper : D.row 0 - D.col (Fin.last (n + 1)).castSucc < (k.val : ℤ))
    (hlower : D.row (0 : Fin (n + 1)).succ.succ -
      D.col (Fin.last (n + 2)) < (k.val : ℤ))
    (hsecond : (k.val : ℤ) <
      D.row (0 : Fin (n + 2)).succ - D.col (Fin.last (n + 2))) :
    MvPolynomial.pderiv k D.schur = 0 := by
  change MvPolynomial.pderiv k D.matrix.det = 0
  apply pderiv_det_eq_zero
  intro i j
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  change k ∉ (complete (D.row i - D.col j)).vars
  rw [mem_vars_complete_iff]
  intro he
  change (k.val : ℤ) = D.row i - D.col j at he
  let r1 : Fin (n + 3) := (0 : Fin (n + 2)).succ
  let r2 : Fin (n + 3) := (0 : Fin (n + 1)).succ.succ
  let p : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  change D.row 0 - D.col p < (k.val : ℤ) at hupper
  change D.row r2 - D.col (Fin.last (n + 2)) < (k.val : ℤ) at hlower
  change (k.val : ℤ) < D.row r1 - D.col (Fin.last (n + 2)) at hsecond
  by_cases hjlast : j = Fin.last (n + 2)
  · subst j
    by_cases hi0 : i = 0
    · subst i
      have hr := D.row_strictAnti (show (0 : Fin (n + 3)) < r1 by
        simp only [r1, Fin.lt_def, Fin.val_zero, Fin.val_succ]; omega)
      omega
    · by_cases hi1 : i = r1
      · subst i
        omega
      · have hir : r2 ≤ i := by
          have h0 := Fin.pos_iff_ne_zero.mpr hi0
          have h1 : i.val ≠ 1 := by
            intro hh
            apply hi1
            apply Fin.ext
            simpa only [r1, Fin.val_succ, Fin.val_zero] using hh
          simp only [r2, Fin.le_def, Fin.val_succ, Fin.val_zero]
          omega
        have hr := D.row_strictAnti.antitone hir
        omega
  · have hjle : j ≤ p := by
      have hh := Fin.lt_last_iff_ne_last.mpr hjlast
      simp only [p, Fin.le_def, Fin.lt_def, Fin.val_last, Fin.val_castSucc] at *
      omega
    have hc := D.col_strictAnti.antitone hjle
    have hr := D.row_strictAnti.antitone (Fin.zero_le i)
    omega

/-- The produced private top index can be compared with a common separator
index without introducing a leading-coefficient hypothesis. -/
theorem singleton_top_separator_at (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hgap : u < v) (hside : Q.largestLabel + v < Q.largestLabel + s + g + u)
    (k : ℕ+) (hk : (k.val : ℤ) = Q.largestLabel + s + g + u) :
    MvPolynomial.pderiv k (Q.singletonContext s u v g hs hu hv hg).schur =
      (-1 : CompleteRing) ^ (n + 1) * (complete s * (Q.extendBottom v hv).schur) := by
  have hsideP : (Q.singletonContext s u v g hs hu hv hg).row
        (0 : Fin (n + 1)).succ.succ -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 2)) <
      (Q.singletonContext s u v g hs hu hv hg).row 0 -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 1)).castSucc := by
    rw [singletonContext_lower_separator, singletonContext_upper_separator]
    exact hside
  obtain ⟨ht, hc⟩ := Q.singleton_top_separator_coefficient s u v g hs hu hv hg hgap hsideP
  let t := Q.largestLabel + s + g + u
  have ht' : 0 < t := by
    simpa only [singletonContext_upper_separator] using ht
  let j : ℕ+ := ⟨t.toNat, by omega⟩
  have hj : j = k := by
    apply Subtype.ext
    apply Int.ofNat.inj
    have hji : (j.val : ℤ) = t := by dsimp [j]; omega
    exact hji.trans hk.symm
  have hh : MvPolynomial.pderiv j (Q.singletonContext s u v g hs hu hv hg).schur =
      (-1 : CompleteRing) ^ (n + 1) * (complete s * (Q.extendBottom v hv).schur) := by
    change (MvPolynomial.pderiv
      (⟨((Q.singletonContext s u v g hs hu hv hg).row 0 -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 1)).castSucc).toNat,
        by omega⟩ : ℕ+)
      (Q.singletonContext s u v g hs hu hv hg).schur : CompleteRing) =
      (-1 : CompleteRing) ^ (n + 1) * (complete s * (Q.extendBottom v hv).schur) at hc
    have hi : (⟨((Q.singletonContext s u v g hs hu hv hg).row 0 -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 1)).castSucc).toNat,
        by omega⟩ : ℕ+) = j := by
      apply Subtype.ext
      exact congrArg Int.toNat (Q.singletonContext_upper_separator s u v g hs hu hv hg)
    rw [hi] at hc
    exact hc
  rw [hj] at hh
  exact hh

/-- The other private index extracts the actual connected complementary diagram. -/
theorem singleton_bottom_separator_at (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hside : Q.largestLabel + s + g + u < Q.largestLabel + v)
    (k : ℕ+) (hk : (k.val : ℤ) = Q.largestLabel + v) :
    MvPolynomial.pderiv k (Q.singletonContext s u v g hs hu hv hg).schur =
      (-1 : CompleteRing) ^ (n + 2) *
        ((Q.singletonContext s u v g hs hu hv hg).lastColumnDiagram
          (Q.singletonContext_positiveCorner s u v g hs hu hv hg)
          (0 : Fin (n + 1)).succ.succ).schur := by
  have hsideP : (Q.singletonContext s u v g hs hu hv hg).row 0 -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 1)).castSucc <
      (Q.singletonContext s u v g hs hu hv hg).row
        (0 : Fin (n + 1)).succ.succ -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 2)) := by
    rw [singletonContext_lower_separator, singletonContext_upper_separator]
    exact hside
  obtain ⟨ht, hc⟩ := Q.singleton_bottom_separator_coefficient s u v g hs hu hv hg hsideP
  let t := Q.largestLabel + v
  have ht' : 0 < t := by simpa only [singletonContext_lower_separator] using ht
  let j : ℕ+ := ⟨t.toNat, by omega⟩
  have hj : j = k := by
    apply Subtype.ext
    apply Int.ofNat.inj
    have hji : (j.val : ℤ) = t := by dsimp [j]; omega
    exact hji.trans hk.symm
  have hh : MvPolynomial.pderiv j (Q.singletonContext s u v g hs hu hv hg).schur =
      (-1 : CompleteRing) ^ (n + 2) *
        ((Q.singletonContext s u v g hs hu hv hg).lastColumnDiagram
          (Q.singletonContext_positiveCorner s u v g hs hu hv hg)
          (0 : Fin (n + 1)).succ.succ).schur := by
    change (MvPolynomial.pderiv
      (⟨((Q.singletonContext s u v g hs hu hv hg).row (0 : Fin (n + 1)).succ.succ -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 2))).toNat,
        by omega⟩ : ℕ+)
      (Q.singletonContext s u v g hs hu hv hg).schur : CompleteRing) =
      (-1 : CompleteRing) ^ (n + 2) *
        ((Q.singletonContext s u v g hs hu hv hg).lastColumnDiagram
          (Q.singletonContext_positiveCorner s u v g hs hu hv hg)
          (0 : Fin (n + 1)).succ.succ).schur at hc
    have hi : (⟨((Q.singletonContext s u v g hs hu hv hg).row (0 : Fin (n + 1)).succ.succ -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 2))).toNat,
        by omega⟩ : ℕ+) = j := by
      apply Subtype.ext
      exact congrArg Int.toNat (Q.singletonContext_lower_separator s u v g hs hu hv hg)
    rw [hi] at hc
    exact hc
  rw [hj] at hh
  exact hh

/-- The connected separator diagram's span lies below the comparison marker. -/
theorem singleton_separator_diagram_span (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    ((Q.singletonContext s u v g hs hu hv hg).lastColumnDiagram
      (Q.singletonContext_positiveCorner s u v g hs hu hv hg)
      (0 : Fin (n + 1)).succ.succ).largestLabel = Q.largestLabel + s + g + u := by
  change (Q.singletonContext s u v g hs hu hv hg).row
      (((0 : Fin (n + 1)).succ.succ).succAbove 0) -
    (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 1)).castSucc = _
  rw [Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero (0 : Fin (n + 1)).succ)]
  exact Q.singletonContext_upper_separator s u v g hs hu hv hg

/-- The full margin separator for two actual candidates, including the tied
maximum and differently oriented literal cores with the same Schur function. -/
theorem singleton_margin_separator (Q W : BetaDiagram (n + 2))
    (hQ : Q.Connected) (hW : W.Connected) (hcore : Q.schur = W.schur)
    (s u vm vp gm gp : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hvm : 0 < vm) (hvp : 0 < vp)
    (hgm : 0 < gm) (hgp : 0 < gp) (hsmall : u < vm) (hincrease : vm < vp)
    (hspan : (Q.singletonContext s u vm gm hs hu hvm hgm).largestLabel =
      (W.singletonContext s u vp gp hs hu hvp hgp).largestLabel) :
    let Pm := Q.singletonContext s u vm gm hs hu hvm hgm
    let Pp := W.singletonContext s u vp gp hs hu hvp hgp
    let T := Pp.lastColumnDiagram
      (W.singletonContext_positiveCorner s u vp gp hs hu hvp hgp)
      (0 : Fin (n + 2)).succ.succ
    let U := Q.largestLabel + s + gm + u
    let V := W.largestLabel + vp
    ∃ k : ℕ+, (k.val : ℤ) = max U V ∧
      MvPolynomial.pderiv k (Pp.schur - Pm.schur) =
        (-1 : CompleteRing) ^ (n + 3) *
          (if V < U then complete s * (Q.extendBottom vm hvm).schur
           else if U < V then T.schur
           else complete s * (Q.extendBottom vm hvm).schur + T.schur) := by
  dsimp only
  let Pm := Q.singletonContext s u vm gm hs hu hvm hgm
  let Pp := W.singletonContext s u vp gp hs hu hvp hgp
  let T := Pp.lastColumnDiagram
    (W.singletonContext_positiveCorner s u vp gp hs hu hvp hgp)
    (0 : Fin (n + 2)).succ.succ
  let U := Q.largestLabel + s + gm + u
  let V := W.largestLabel + vp
  let K := max U V
  have hS := Q.largestLabel_eq_of_schur_eq W hQ hW hcore
  have hN : Q.largestLabel + s + gm + u + vm =
      W.largestLabel + s + gp + u + vp := by
    simpa only [singletonContext_span] using hspan
  have hpos : 0 < K := by
    have hq := Q.largestLabel_pos
    have hmax := le_max_left U V
    dsimp [U, K] at *
    omega
  let k : ℕ+ := ⟨K.toNat, by omega⟩
  have hk : (k.val : ℤ) = K := by dsimp [k]; omega
  refine ⟨k, hk, ?_⟩
  have hupperp : W.largestLabel + s + gp + u < U := by dsimp [U]; omega
  have hlowerm : Q.largestLabel + vm < V := by dsimp [V]; omega
  have hsecondm : K < Q.largestLabel + s + gm + vm := by dsimp [K, U, V]; omega
  have hsecondp : K < W.largestLabel + s + gp + vp := by dsimp [K, U, V]; omega
  rcases lt_trichotomy U V with hlt | heq | hgt
  · have hkv : (k.val : ℤ) = V := by rw [hk]; exact max_eq_right hlt.le
    have hp : MvPolynomial.pderiv k Pp.schur = (-1 : CompleteRing) ^ (n + 3) * T.schur := by
      exact W.singleton_bottom_separator_at s u vp gp hs hu hvp hgp
        (by dsimp [V] at hlt; omega) k hkv
    have hm : MvPolynomial.pderiv k Pm.schur = 0 := by
      apply separator_between_levels_zero
      · rw [singletonContext_upper_separator]
        dsimp [U] at hlt
        omega
      · rw [singletonContext_lower_separator]
        omega
      · rw [singletonContext_second_last_level]
        omega
    change MvPolynomial.pderiv k (Pp.schur - Pm.schur) =
      (-1 : CompleteRing) ^ (n + 3) *
        (if V < U then complete s * (Q.extendBottom vm hvm).schur
         else if U < V then T.schur
         else complete s * (Q.extendBottom vm hvm).schur + T.schur)
    rw [map_sub, hp, hm]
    simp only [lt_asymm hlt, ite_false, hlt, ite_true, sub_zero]
  · have hku : (k.val : ℤ) = U := by
      rw [hk]
      change max U V = U
      exact max_eq_left heq.symm.le
    have hkv : (k.val : ℤ) = V := hku.trans heq
    have hm : MvPolynomial.pderiv k Pm.schur =
        (-1 : CompleteRing) ^ (n + 2) * (complete s * (Q.extendBottom vm hvm).schur) :=
      Q.singleton_top_separator_at s u vm gm hs hu hvm hgm hsmall
        (by dsimp [U, V] at heq hlowerm; omega) k hku
    have hp : MvPolynomial.pderiv k Pp.schur = (-1 : CompleteRing) ^ (n + 3) * T.schur :=
      W.singleton_bottom_separator_at s u vp gp hs hu hvp hgp
        (by dsimp [U, V] at heq hupperp; omega) k hkv
    change MvPolynomial.pderiv k (Pp.schur - Pm.schur) =
      (-1 : CompleteRing) ^ (n + 3) *
        (if V < U then complete s * (Q.extendBottom vm hvm).schur
         else if U < V then T.schur
         else complete s * (Q.extendBottom vm hvm).schur + T.schur)
    rw [map_sub, hp, hm]
    simp only [heq, lt_self_iff_false, ite_false,
      show n + 3 = (n + 2) + 1 by omega, pow_succ]
    ring
  · have hku : (k.val : ℤ) = U := by rw [hk]; exact max_eq_left hgt.le
    have hm : MvPolynomial.pderiv k Pm.schur =
        (-1 : CompleteRing) ^ (n + 2) * (complete s * (Q.extendBottom vm hvm).schur) :=
      Q.singleton_top_separator_at s u vm gm hs hu hvm hgm hsmall
        (by dsimp [U, V] at hgt hlowerm; omega) k hku
    have hp : MvPolynomial.pderiv k Pp.schur = 0 := by
      apply separator_between_levels_zero
      · rw [singletonContext_upper_separator]
        omega
      · rw [singletonContext_lower_separator]
        dsimp [V] at hgt
        omega
      · rw [singletonContext_second_last_level]
        omega
    change MvPolynomial.pderiv k (Pp.schur - Pm.schur) =
      (-1 : CompleteRing) ^ (n + 3) *
        (if V < U then complete s * (Q.extendBottom vm hvm).schur
         else if U < V then T.schur
         else complete s * (Q.extendBottom vm hvm).schur + T.schur)
    rw [map_sub, hp, hm]
    simp only [hgt, ite_true, show n + 3 = (n + 2) + 1 by omega, pow_succ]
    ring

/-- Distinct bottom margins give distinct full singleton-parent polynomials,
including the tied separator maximum and every possible core orientation. -/
theorem singleton_margin_comparison_ne (Q W : BetaDiagram (n + 2))
    (hQ : Q.Connected) (hW : W.Connected) (hZW : W.ZeroFree)
    (hcore : Q.schur = W.schur) (s u vm vp gm gp : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hvm : 0 < vm) (hvp : 0 < vp)
    (hgm : 0 < gm) (hgp : 0 < gp) (hsmall : u < vm) (hincrease : vm < vp)
    (hspan : (Q.singletonContext s u vm gm hs hu hvm hgm).largestLabel =
      (W.singletonContext s u vp gp hs hu hvp hgp).largestLabel) :
    (Q.singletonContext s u vm gm hs hu hvm hgm).schur ≠
      (W.singletonContext s u vp gp hs hu hvp hgp).schur := by
  let Pm := Q.singletonContext s u vm gm hs hu hvm hgm
  let Pp := W.singletonContext s u vp gp hs hu hvp hgp
  let T := Pp.lastColumnDiagram
    (W.singletonContext_positiveCorner s u vp gp hs hu hvp hgp)
    (0 : Fin (n + 2)).succ.succ
  obtain ⟨k, hk, hd⟩ := singleton_margin_separator Q W hQ hW hcore
    s u vm vp gm gp hs hu hvm hvp hgm hgp hsmall hincrease hspan
  have hT : T.Connected :=
    W.singleton_separator_diagram_connected hW hZW s u vp gp hs hu hvp hgp
  have hn : (if W.largestLabel + vp < Q.largestLabel + s + gm + u then
        complete s * (Q.extendBottom vm hvm).schur
      else if Q.largestLabel + s + gm + u < W.largestLabel + vp then T.schur
      else complete s * (Q.extendBottom vm hvm).schur + T.schur) ≠ 0 := by
    split_ifs
    · exact mul_ne_zero ((complete_ne_zero_iff s).mpr hs.le) (Q.extendBottom vm hvm).schur_ne_zero
    · exact T.schur_ne_zero
    · have hh := schur_product_add_connected_ne_zero
        (singletonDiagram s hs) (Q.extendBottom vm hvm) T (by omega) (by omega) hT
      simpa only [singletonDiagram_schur] using hh
  intro he
  have hz : Pp.schur - Pm.schur = 0 := sub_eq_zero.mpr he.symm
  rw [hz, map_zero] at hd
  exact (mul_ne_zero
    (pow_ne_zero (n + 3) (neg_ne_zero.mpr (one_ne_zero : (1 : CompleteRing) ≠ 0))) hn) hd.symm

/-- Once the two margins are recovered, the actual common span fixes the gap. -/
theorem singleton_gap_eq_of_span_eq (Q W : BetaDiagram (n + 1))
    (hQ : Q.Connected) (hW : W.Connected) (hcore : Q.schur = W.schur)
    (s u v gm gp : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v)
    (hgm : 0 < gm) (hgp : 0 < gp)
    (hspan : (Q.singletonContext s u v gm hs hu hv hgm).largestLabel =
      (W.singletonContext s u v gp hs hu hv hgp).largestLabel) : gm = gp := by
  have hS := Q.largestLabel_eq_of_schur_eq W hQ hW hcore
  rw [singletonContext_span, singletonContext_span] at hspan
  omega

/-- Both full separator coefficients have all labels strictly below the common
comparison marker, so the strict and tied extractions are genuine coefficients. -/
theorem singleton_margin_separator_labels (Q W : BetaDiagram (n + 1))
    (hQ : Q.Connected) (hW : W.Connected) (hcore : Q.schur = W.schur)
    (s u vm vp gm gp : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hvm : 0 < vm) (hvp : 0 < vp)
    (hgm : 0 < gm) (hgp : 0 < gp) (hincrease : vm < vp)
    (hspan : (Q.singletonContext s u vm gm hs hu hvm hgm).largestLabel =
      (W.singletonContext s u vp gp hs hu hvp hgp).largestLabel) :
    let T := (W.singletonContext s u vp gp hs hu hvp hgp).lastColumnDiagram
      (W.singletonContext_positiveCorner s u vp gp hs hu hvp hgp)
      (0 : Fin (n + 1)).succ.succ
    let K := max (Q.largestLabel + s + gm + u) (W.largestLabel + vp)
    LabelsBelow (complete s * (Q.extendBottom vm hvm).schur) K ∧
      LabelsBelow T.schur K := by
  dsimp only
  let T := (W.singletonContext s u vp gp hs hu hvp hgp).lastColumnDiagram
    (W.singletonContext_positiveCorner s u vp gp hs hu hvp hgp)
    (0 : Fin (n + 1)).succ.succ
  let K := max (Q.largestLabel + s + gm + u) (W.largestLabel + vp)
  have hS := Q.largestLabel_eq_of_schur_eq W hQ hW hcore
  have hN : Q.largestLabel + s + gm + u + vm =
      W.largestLabel + s + gp + u + vp := by
    simpa only [singletonContext_span] using hspan
  have hU := le_max_left (Q.largestLabel + s + gm + u) (W.largestLabel + vp)
  have hV := le_max_right (Q.largestLabel + s + gm + u) (W.largestLabel + vp)
  have hq := Q.largestLabel_pos
  have hTspan : T.largestLabel = W.largestLabel + s + gp + u :=
    W.singleton_separator_diagram_span s u vp gp hs hu hvp hgp
  refine ⟨?_, ?_⟩
  · apply LabelsBelow.mul
    · apply LabelsBelow.complete
      omega
    · intro j hj
      have hb := (Q.extendBottom vm hvm).vars_le_largestLabel j hj
      rw [border_extendBottom_largestLabel] at hb
      omega
  · intro j hj
    have hb := T.vars_le_largestLabel j hj
    rw [hTspan] at hb
    omega

@[simp] theorem singletonContext_topMargin (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).topMargin = u := by
  change ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).row 0 + v -
    (((Q.singletonCore s g hs hg).positiveBorder u v hu hv).row
      (0 : Fin (n + 2)).succ + v) = u
  rw [positiveBorder_row_zero, positiveBorder_row_succ]
  ring

@[simp] theorem singletonContext_bottomMargin (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).bottomMargin = v := by
  change ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).col
      (Fin.last (n + 1)).castSucc + v -
    (((Q.singletonCore s g hs hg).positiveBorder u v hu hv).col
      (Fin.last (n + 2)) + v) = v
  rw [positiveBorder_col_castSucc, positiveBorder_col_last]
  ring

@[simp] theorem singletonMarker_int (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    ((Q.singletonMarker s u v g hs hu hv hg).val : ℤ) =
      Q.largestLabel + s + g + u + v - min u v := by
  change ((Q.largestLabel + s + g + u + v - min u v).toNat : ℤ) = _
  have hq := Q.largestLabel_pos
  have hm := min_le_left u v
  omega

/-- The computed marker is the parent's actual second complete-generator index. -/
theorem singletonContext_second_generator (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).borderSecondGenerator =
      Q.singletonMarker s u v g hs hu hv hg := by
  apply Subtype.ext
  apply Int.ofNat.inj
  change (((Q.singletonContext s u v g hs hu hv hg).borderSecondGenerator).val : ℤ) =
    ((Q.singletonMarker s u v g hs hu hv hg).val : ℤ)
  rw [borderSecondGenerator_int, singletonMarker_int]
  simp only [secondLabel, singletonContext_span, singletonContext_topMargin,
    singletonContext_bottomMargin]

/-- The border in the first-column identity has the parent's actual corner index. -/
theorem singletonContext_largest_generator (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).borderLargestGenerator =
      (Q.positiveBorder (s + g + u) v (by omega) hv).borderLargestGenerator := by
  apply Subtype.ext
  apply Int.ofNat.inj
  change (((Q.singletonContext s u v g hs hu hv hg).borderLargestGenerator).val : ℤ) =
    (((Q.positiveBorder (s + g + u) v (by omega) hv).borderLargestGenerator).val : ℤ)
  rw [borderLargestGenerator_int, borderLargestGenerator_int]
  simp only [singletonContext_span, positiveBorder_largestLabel]
  ring

/-- The second label survives corner erasure for every singleton context with a
connected nonlinear core, including a tied margin and negative board entries. -/
theorem singleton_secondLabel_derivative_ne_zero (Q : BetaDiagram (n + 2))
    (hQ : Q.Connected) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    let P := Q.singletonContext s u v g hs hu hv hg
    MvPolynomial.pderiv P.borderSecondGenerator
      (eraseGenerator P.borderLargestGenerator P.schur) ≠ (0 : CompleteRing) := by
  dsimp only
  rw [singletonContext_second_generator, singletonContext_largest_generator]
  rcases lt_trichotomy u v with h | h | h
  · rw [singletonContext_top_marker Q s u v g hs hu hv hg h]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (mul_ne_zero ((complete_ne_zero_iff (s + u)).mpr (by omega)) Q.schur_ne_zero)
  · subst v
    rw [singletonContext_tied_marker Q s u g hs hu hg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Q.singleton_tied_marker_divisibility hQ s u hs hu).2.2
  · rw [singletonContext_bottom_marker Q s u v g hs hu hv hg h]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (mul_ne_zero ((complete_ne_zero_iff s).mpr hs.le) (Q.extendBottom v hv).schur_ne_zero)

/-- Actual occurrence, not merely an entrywise upper bound, supplies the reading. -/
theorem singleton_secondLabel_mem_vars (Q : BetaDiagram (n + 2))
    (hQ : Q.Connected) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    let P := Q.singletonContext s u v g hs hu hv hg
    P.borderSecondGenerator ∈ (eraseGenerator P.borderLargestGenerator P.schur).vars := by
  dsimp only
  by_contra hn
  exact Q.singleton_secondLabel_derivative_ne_zero hQ s u v g hs hu hv hg
    (MvPolynomial.pderiv_eq_zero_of_notMem_vars hn)

/-- Full equality recovers the minimum margin from actual occupied generator
support.  Singleton lengths and core functions are not assumed equal here. -/
theorem singleton_min_margin_eq_of_schur_eq (Q W : BetaDiagram (n + 2))
    (hQ : Q.Connected) (hW : W.Connected)
    (sm um vm gm sp up vp gp : ℤ)
    (hsm : 0 < sm) (hum : 0 < um) (hvm : 0 < vm) (hgm : 0 < gm)
    (hsp : 0 < sp) (hup : 0 < up) (hvp : 0 < vp) (hgp : 0 < gp)
    (he : (Q.singletonContext sm um vm gm hsm hum hvm hgm).schur =
      (W.singletonContext sp up vp gp hsp hup hvp hgp).schur) :
    min um vm = min up vp := by
  let Pm := Q.singletonContext sm um vm gm hsm hum hvm hgm
  let Pp := W.singletonContext sp up vp gp hsp hup hvp hgp
  have hCm := Q.singletonContext_connected sm um vm gm hsm hum hvm hgm
  have hCp := W.singletonContext_connected sp up vp gp hsp hup hvp hgp
  have hN := Pm.largestLabel_eq_of_schur_eq Pp hCm hCp he
  have hgen : Pm.borderLargestGenerator = Pp.borderLargestGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (Pm.borderLargestGenerator.val : ℤ) = (Pp.borderLargestGenerator.val : ℤ)
    rw [borderLargestGenerator_int, borderLargestGenerator_int, hN]
  have hmm := Q.singleton_secondLabel_mem_vars hQ sm um vm gm hsm hum hvm hgm
  have hmp := W.singleton_secondLabel_mem_vars hW sp up vp gp hsp hup hvp hgp
  change Pm.borderSecondGenerator ∈ (eraseGenerator Pm.borderLargestGenerator Pm.schur).vars at hmm
  change Pp.borderSecondGenerator ∈ (eraseGenerator Pp.borderLargestGenerator Pp.schur).vars at hmp
  rw [hgen, he] at hmm
  rw [← hgen, ← he] at hmp
  have hb1 := Pp.vars_le_secondLabel Pm.borderSecondGenerator hmm
  have hb2 := Pm.vars_le_secondLabel Pp.borderSecondGenerator hmp
  rw [borderSecondGenerator_int] at hb1 hb2
  have hM : Pm.secondLabel = Pp.secondLabel := le_antisymm hb1 hb2
  have htm : Pm.topMargin = um := Q.singletonContext_topMargin sm um vm gm hsm hum hvm hgm
  have hbm : Pm.bottomMargin = vm := Q.singletonContext_bottomMargin sm um vm gm hsm hum hvm hgm
  have htp : Pp.topMargin = up := W.singletonContext_topMargin sp up vp gp hsp hup hvp hgp
  have hbp : Pp.bottomMargin = vp := W.singletonContext_bottomMargin sp up vp gp hsp hup hvp hgp
  unfold secondLabel at hM
  rw [htm, hbm, htp, hbp] at hM
  omega

/-- The three actual marker polynomials, with both terms retained at a tie. -/
noncomputable def singletonRegimeCoefficient (Q : BetaDiagram (n + 2))
    (s u v : ℤ) (hu : 0 < u) (hv : 0 < v) : CompleteRing :=
  if u < v then complete (s + u) * Q.schur
  else if v < u then complete s * (Q.extendBottom v hv).schur
  else complete (s + u) * Q.schur + complete s * (Q.extendBottom u hu).schur

/-- This regime polynomial is extracted from the actual full parent. -/
theorem singletonRegimeCoefficient_identity (Q : BetaDiagram (n + 2))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    let P := Q.singletonContext s u v g hs hu hv hg
    MvPolynomial.pderiv P.borderSecondGenerator
      (eraseGenerator P.borderLargestGenerator P.schur) =
      (-1 : CompleteRing) ^ (n + 2) * Q.singletonRegimeCoefficient s u v hu hv := by
  dsimp only
  rw [singletonContext_second_generator, singletonContext_largest_generator]
  rcases lt_trichotomy u v with h | h | h
  · rw [singletonContext_top_marker Q s u v g hs hu hv hg h]
    simp only [singletonRegimeCoefficient, h, ite_true]
  · subst v
    rw [singletonContext_tied_marker Q s u g hs hu hg]
    simp only [singletonRegimeCoefficient, lt_self_iff_false, ite_false]
  · rw [singletonContext_bottom_marker Q s u v g hs hu hv hg h]
    simp only [singletonRegimeCoefficient, lt_asymm h, ite_false, h, ite_true]

/-- Equal full parents have equal full marker polynomials at their produced common index. -/
theorem singletonRegimeCoefficient_eq_of_schur_eq (Q W : BetaDiagram (n + 2))
    (hQ : Q.Connected) (hW : W.Connected) (s um vm gm up vp gp : ℤ)
    (hs : 0 < s) (hum : 0 < um) (hvm : 0 < vm) (hgm : 0 < gm)
    (hup : 0 < up) (hvp : 0 < vp) (hgp : 0 < gp)
    (he : (Q.singletonContext s um vm gm hs hum hvm hgm).schur =
      (W.singletonContext s up vp gp hs hup hvp hgp).schur) :
    Q.singletonRegimeCoefficient s um vm hum hvm =
      W.singletonRegimeCoefficient s up vp hup hvp := by
  let Pm := Q.singletonContext s um vm gm hs hum hvm hgm
  let Pp := W.singletonContext s up vp gp hs hup hvp hgp
  have hN := Pm.largestLabel_eq_of_schur_eq Pp
    (Q.singletonContext_connected s um vm gm hs hum hvm hgm)
    (W.singletonContext_connected s up vp gp hs hup hvp hgp) he
  have hq := singleton_min_margin_eq_of_schur_eq Q W hQ hW
    s um vm gm s up vp gp hs hum hvm hgm hs hup hvp hgp he
  have hNgen : Pm.borderLargestGenerator = Pp.borderLargestGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (Pm.borderLargestGenerator.val : ℤ) = (Pp.borderLargestGenerator.val : ℤ)
    rw [borderLargestGenerator_int, borderLargestGenerator_int, hN]
  have hMgen : Pm.borderSecondGenerator = Pp.borderSecondGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (Pm.borderSecondGenerator.val : ℤ) = (Pp.borderSecondGenerator.val : ℤ)
    rw [borderSecondGenerator_int, borderSecondGenerator_int]
    unfold secondLabel
    simp only [Pm, Pp, singletonContext_topMargin, singletonContext_bottomMargin] at *
    rw [hN, hq]
  have hd := congrArg (fun p : CompleteRing =>
    MvPolynomial.pderiv Pm.borderSecondGenerator (eraseGenerator Pm.borderLargestGenerator p)) he
  have hm := Q.singletonRegimeCoefficient_identity s um vm gm hs hum hvm hgm
  have hp := W.singletonRegimeCoefficient_identity s up vp gp hs hup hvp hgp
  have hc : (-1 : CompleteRing) ^ (n + 2) * Q.singletonRegimeCoefficient s um vm hum hvm =
      (-1 : CompleteRing) ^ (n + 2) * W.singletonRegimeCoefficient s up vp hup hvp := by
    calc
      (-1 : CompleteRing) ^ (n + 2) * Q.singletonRegimeCoefficient s um vm hum hvm =
          MvPolynomial.pderiv Pm.borderSecondGenerator
            (eraseGenerator Pm.borderLargestGenerator Pm.schur) := hm.symm
      _ = MvPolynomial.pderiv Pm.borderSecondGenerator
          (eraseGenerator Pm.borderLargestGenerator Pp.schur) := hd
      _ = MvPolynomial.pderiv Pp.borderSecondGenerator
          (eraseGenerator Pp.borderLargestGenerator Pp.schur) := by rw [hMgen, hNgen]
      _ = (-1 : CompleteRing) ^ (n + 2) * W.singletonRegimeCoefficient s up vp hup hvp := hp
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hc

/-- The two genuine singleton divisibility tests identify all three regimes. -/
theorem singletonRegimeCoefficient_divisibility (Q : BetaDiagram (n + 2))
    (hQ : Q.Connected) (s u v : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) :
    (complete s ∣ Q.singletonRegimeCoefficient s u v hu hv ↔ v < u) ∧
      (complete (s + min u v) ∣ Q.singletonRegimeCoefficient s u v hu hv ↔ u < v) := by
  rcases lt_trichotomy u v with h | h | h
  · have hd := Q.singleton_top_marker_divisibility hQ s u hs hu
    have hf : Q.singletonRegimeCoefficient s u v hu hv = complete (s + u) * Q.schur := by
      simp only [singletonRegimeCoefficient, h, ite_true]
    rw [hf, min_eq_left h.le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro hc
      exact (hd.1 hc).elim
    · intro hh
      omega
    · intro _
      exact h
    · intro _
      exact hd.2
  · subst v
    have hd := Q.singleton_tied_marker_divisibility hQ s u hs hu
    have hf : Q.singletonRegimeCoefficient s u u hu hv =
        complete (s + u) * Q.schur + complete s * (Q.extendBottom u hu).schur := by
      simp only [singletonRegimeCoefficient, lt_self_iff_false, ite_false]
    rw [hf, min_self]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro hc
      exact (hd.1 hc).elim
    · intro hh
      omega
    · intro hc
      exact (hd.2.1 hc).elim
    · intro hh
      omega
  · have hd := Q.singleton_bottom_marker_divisibility hQ s v hs hv
    have hf : Q.singletonRegimeCoefficient s u v hu hv =
        complete s * (Q.extendBottom v hv).schur := by
      simp only [singletonRegimeCoefficient, lt_asymm h, ite_false, h, ite_true]
    rw [hf, min_eq_right h.le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro _
      exact h
    · intro _
      exact hd.1
    · intro hc
      exact (hd.2 hc).elim
    · intro hh
      omega

/-- Actual arbitrary core representatives cannot move between strict or tied
margin regimes under equality of the full parent polynomial. -/
theorem singleton_regimes_eq_of_schur_eq (Q W : BetaDiagram (n + 2))
    (hQ : Q.Connected) (hW : W.Connected) (s um vm gm up vp gp : ℤ)
    (hs : 0 < s) (hum : 0 < um) (hvm : 0 < vm) (hgm : 0 < gm)
    (hup : 0 < up) (hvp : 0 < vp) (hgp : 0 < gp)
    (he : (Q.singletonContext s um vm gm hs hum hvm hgm).schur =
      (W.singletonContext s up vp gp hs hup hvp hgp).schur) :
    (um < vm ↔ up < vp) ∧ (vm < um ↔ vp < up) ∧ (um = vm ↔ up = vp) := by
  have hcoef := singletonRegimeCoefficient_eq_of_schur_eq Q W hQ hW
    s um vm gm up vp gp hs hum hvm hgm hup hvp hgp he
  have hq := singleton_min_margin_eq_of_schur_eq Q W hQ hW
    s um vm gm s up vp gp hs hum hvm hgm hs hup hvp hgp he
  have hm := Q.singletonRegimeCoefficient_divisibility hQ s um vm hs hum hvm
  have hp := W.singletonRegimeCoefficient_divisibility hW s up vp hs hup hvp
  have hbottom : vm < um ↔ vp < up := by
    calc
      vm < um ↔ complete s ∣ Q.singletonRegimeCoefficient s um vm hum hvm := hm.1.symm
      _ ↔ complete s ∣ W.singletonRegimeCoefficient s up vp hup hvp := by rw [hcoef]
      _ ↔ vp < up := hp.1
  have htop : um < vm ↔ up < vp := by
    calc
      um < vm ↔ complete (s + min um vm) ∣ Q.singletonRegimeCoefficient s um vm hum hvm :=
        hm.2.symm
      _ ↔ complete (s + min up vp) ∣ W.singletonRegimeCoefficient s up vp hup hvp := by
        rw [hcoef, hq]
      _ ↔ up < vp := hp.2
  refine ⟨htop, hbottom, ?_⟩
  constructor <;> intro hh <;> omega

/-- Literal core translation transports every coordinate of the actual context. -/
theorem singletonContext_translation (Q W : BetaDiagram (n + 1))
    (h : Q.TranslationEquivalent W) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).TranslationEquivalent
      (W.singletonContext s u v g hs hu hv hg) := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
      rw [singletonContext_row_zero, singletonContext_row_zero, hr 0]
      ring
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        rw [singletonContext_row_one, singletonContext_row_one, hr 0]
        ring
      | succ i =>
        rw [singletonContext_row_core, singletonContext_row_core, hr i]
        ring
  · intro j
    cases j using Fin.lastCases with
    | last =>
      rw [singletonContext_col_last, singletonContext_col_last]
      exact hc (Fin.last n)
    | cast j =>
      cases j using Fin.cases with
      | zero =>
        rw [Fin.castSucc_zero, singletonContext_col_zero, singletonContext_col_zero, hr 0]
        ring
      | succ j =>
        rw [singletonContext_col_core, singletonContext_col_core, hc j]
        ring

/-- Two reflections identify the same translation class when the source is symmetric. -/
theorem translation_of_rotation_of_symmetric (Q W : BetaDiagram n)
    (hS : Q.Symmetric) (hR : Q.RotationEquivalent W) : Q.TranslationEquivalent W := by
  obtain ⟨a, hSr, hSc⟩ := hS
  obtain ⟨c, hRr, hRc⟩ := hR
  refine ⟨a - c, ?_, ?_⟩
  · intro i
    have hs := hSr i
    have hr := hRc i.rev
    simp only [Fin.rev_rev] at hr
    omega
  · intro i
    have hs := hSc i
    have hr := hRr i.rev
    simp only [Fin.rev_rev] at hr
    omega

/-- Core rotation transports the top extension to the opposite bottom extension. -/
theorem extendTop_rotation_extendBottom_of_rotation (Q W : BetaDiagram (n + 1))
    (h : Q.RotationEquivalent W) (t : ℤ) (ht : 0 < t) :
    (Q.extendTop t ht).RotationEquivalent (W.extendBottom t ht) := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, ?_⟩
  · intro i
    have hi : i.rev = Fin.last n ↔ i = 0 := by
      rw [Fin.rev_eq_iff, Fin.rev_last]
    simp only [extendTop, extendBottom]
    rw [hr i]
    by_cases h : i = 0 <;> simp [h, hi] <;> omega
  · exact hc

/-- The actual endpoint polynomials follow that literal rotation. -/
theorem extendTop_schur_eq_extendBottom_of_rotation (Q W : BetaDiagram (n + 1))
    (h : Q.RotationEquivalent W) (t : ℤ) (ht : 0 < t) :
    (Q.extendTop t ht).schur = (W.extendBottom t ht).schur := by
  have hR := Q.extendTop_rotation_extendBottom_of_rotation W h t ht
  have hT := ((Q.extendTop t ht).translation_rotate_iff_rotation (W.extendBottom t ht)).mpr hR
  exact hT.schur_eq.trans (W.extendBottom t ht).rotate_schur

/-- Core translation preserves both actual border lists with the same margins. -/
theorem positiveBorder_translation (Q W : BetaDiagram (n + 1))
    (h : Q.TranslationEquivalent W) (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (Q.positiveBorder u v hu hv).TranslationEquivalent (W.positiveBorder u v hu hv) := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
      rw [positiveBorder_row_zero, positiveBorder_row_zero, hr 0]
      ring
    | succ i =>
      rw [positiveBorder_row_succ, positiveBorder_row_succ]
      exact hr i
  · intro j
    cases j using Fin.lastCases with
    | last =>
      rw [positiveBorder_col_last, positiveBorder_col_last, hc (Fin.last n)]
      ring
    | cast j =>
      rw [positiveBorder_col_castSucc, positiveBorder_col_castSucc]
      exact hc j

theorem positiveBorder_schur_eq_of_translation (Q W : BetaDiagram (n + 1))
    (h : Q.TranslationEquivalent W) (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (Q.positiveBorder u v hu hv).schur = (W.positiveBorder u v hu hv).schur :=
  (Q.positiveBorder_translation W h u v hu hv).schur_eq

/-- The bottom or tied marker recovers the literal bottom extension polynomial
and its margin, independently of the core's orientation. -/
theorem singleton_bottom_endpoint_eq_of_schur_eq (Q W : BetaDiagram (n + 2))
    (hQ : Q.Connected) (hW : W.Connected) (hcore : Q.schur = W.schur)
    (s um vm gm up vp gp : ℤ)
    (hs : 0 < s) (hum : 0 < um) (hvm : 0 < vm) (hgm : 0 < gm)
    (hup : 0 < up) (hvp : 0 < vp) (hgp : 0 < gp) (hside : vm ≤ um)
    (he : (Q.singletonContext s um vm gm hs hum hvm hgm).schur =
      (W.singletonContext s up vp gp hs hup hvp hgp).schur) :
    vm = vp ∧ (Q.extendBottom vm hvm).schur = (W.extendBottom vp hvp).schur := by
  have hr := singleton_regimes_eq_of_schur_eq Q W hQ hW
    s um vm gm up vp gp hs hum hvm hgm hup hvp hgp he
  have hq := singleton_min_margin_eq_of_schur_eq Q W hQ hW
    s um vm gm s up vp gp hs hum hvm hgm hs hup hvp hgp he
  have hwp : vp ≤ up := by omega
  have hvEq : vm = vp := by
    rw [min_eq_right hside, min_eq_right hwp] at hq
    exact hq
  refine ⟨hvEq, ?_⟩
  have hc := singletonRegimeCoefficient_eq_of_schur_eq Q W hQ hW
    s um vm gm up vp gp hs hum hvm hgm hup hvp hgp he
  rcases lt_or_eq_of_le hside with hlt | heq
  · have hltp := hr.2.1.mp hlt
    have hm : Q.singletonRegimeCoefficient s um vm hum hvm =
        complete s * (Q.extendBottom vm hvm).schur := by
      simp only [singletonRegimeCoefficient, lt_asymm hlt, ite_false, hlt, ite_true]
    have hp : W.singletonRegimeCoefficient s up vp hup hvp =
        complete s * (W.extendBottom vp hvp).schur := by
      simp only [singletonRegimeCoefficient, lt_asymm hltp, ite_false, hltp, ite_true]
    rw [hm, hp] at hc
    exact mul_left_cancel₀ ((complete_ne_zero_iff s).mpr hs.le) hc
  · have htp := hr.2.2.mp heq.symm
    subst um
    subst up
    subst vp
    simp only [singletonRegimeCoefficient, lt_self_iff_false, ite_false] at hc
    rw [hcore] at hc
    apply mul_left_cancel₀ ((complete_ne_zero_iff s).mpr hs.le)
    linear_combination hc

/-- Core rigidity and endpoint isolation fix the core orientation in the bottom
and tied regimes; endpoint-extension rigidity is not needed. -/
theorem singleton_core_translation_of_bottom_regime (Q W : BetaDiagram (n + 2))
    (hQ : Q.Connected) (hW : W.Connected) (hcore : Q.schur = W.schur)
    (hRQ : Q.RotationRigid) (s um vm gm up vp gp : ℤ)
    (hs : 0 < s) (hum : 0 < um) (hvm : 0 < vm) (hgm : 0 < gm)
    (hup : 0 < up) (hvp : 0 < vp) (hgp : 0 < gp) (hside : vm ≤ um)
    (hIsolation : Q.endpointDifference vm hvm = 0 → Q.Symmetric)
    (he : (Q.singletonContext s um vm gm hs hum hvm hgm).schur =
      (W.singletonContext s up vp gp hs hup hvp hgp).schur) : Q.TranslationEquivalent W := by
  obtain ⟨hvEq, hbottom⟩ := singleton_bottom_endpoint_eq_of_schur_eq Q W hQ hW hcore
    s um vm gm up vp gp hs hum hvm hgm hup hvp hgp hside he
  obtain hT | hR := (Q.rotationRigid_iff_same_order.mp hRQ) W hW hcore.symm
  · exact hT
  · subst vp
    have htop := Q.extendTop_schur_eq_extendBottom_of_rotation W hR vm hvm
    have hd : Q.endpointDifference vm hvm = 0 := by
      apply sub_eq_zero.mpr
      exact htop.trans hbottom.symm
    have hS := hIsolation hd
    exact Q.translation_of_rotation_of_symmetric W hS hR

/-- After orientation and the bottom margin are fixed, unique factorization of
the actual first border term recovers the top margin and then the gap. -/
theorem singleton_top_margin_of_bottom_translation (Q W : BetaDiagram (n + 2))
    (hT : Q.TranslationEquivalent W) (s um up v gm gp : ℤ)
    (hs : 0 < s) (hum : 0 < um) (hup : 0 < up) (hv : 0 < v)
    (hgm : 0 < gm) (hgp : 0 < gp)
    (he : (Q.singletonContext s um v gm hs hum hv hgm).schur =
      (W.singletonContext s up v gp hs hup hv hgp).schur) : um = up ∧ gm = gp := by
  have hS : Q.largestLabel = W.largestLabel := by
    obtain ⟨c, hr, hc⟩ := hT
    unfold largestLabel
    rw [hr 0, hc (Fin.last (n + 1))]
    ring
  have hN := (Q.singletonContext s um v gm hs hum hv hgm).largestLabel_eq_of_schur_eq
    (W.singletonContext s up v gp hs hup hv hgp)
    (Q.singletonContext_connected s um v gm hs hum hv hgm)
    (W.singletonContext_connected s up v gp hs hup hv hgp) he
  rw [singletonContext_span, singletonContext_span] at hN
  have hsum : gm + um = gp + up := by omega
  have hw : s + gm + um = s + gp + up := by omega
  have hsecond : (Q.positiveBorder (s + gm + um) v (by omega) hv).schur =
      (W.positiveBorder (s + gp + up) v (by omega) hv).schur := by
    have hh := Q.positiveBorder_schur_eq_of_translation W hT
      (s + gm + um) v (by omega) hv
    simpa only [hw] using hh
  have hh := he
  rw [singletonContext_schur, singletonContext_schur, hsecond] at hh
  have hproduct : complete (s + um) * (Q.positiveBorder (s + gm) v (by omega) hv).schur =
      complete (s + up) * (W.positiveBorder (s + gp) v (by omega) hv).schur := by
    linear_combination hh
  have hdiv : complete (s + um) ∣
      complete (s + up) * (W.positiveBorder (s + gp) v (by omega) hv).schur := by
    rw [← hproduct]
    exact dvd_mul_right _ _
  have huEq : um = up := by
    obtain hi | hb := (complete_prime (s + um) (by omega)).dvd_mul.mp hdiv
    · have hp := (complete_dvd_complete_iff (s + um) (s + up) (by omega) (by omega)).mp hi
      omega
    · exact ((W.positiveBorder (s + gp) v (by omega) hv).complete_not_dvd_connected
        (W.positiveBorder_connected (s + gp) v (by omega) hv)
        (s + um) (by omega) hb).elim
  exact ⟨huEq, by omega⟩

/-- In the strict top regime the actual marker and all separator maxima recover
both margins and the gap, even before the core orientation is fixed. -/
theorem singleton_strict_top_margins_eq (Q W : BetaDiagram (n + 2))
    (hQ : Q.Connected) (hW : W.Connected) (hZQ : Q.ZeroFree) (hZW : W.ZeroFree)
    (hcore : Q.schur = W.schur) (s um vm gm up vp gp : ℤ)
    (hs : 0 < s) (hum : 0 < um) (hvm : 0 < vm) (hgm : 0 < gm)
    (hup : 0 < up) (hvp : 0 < vp) (hgp : 0 < gp) (hsmall : um < vm)
    (he : (Q.singletonContext s um vm gm hs hum hvm hgm).schur =
      (W.singletonContext s up vp gp hs hup hvp hgp).schur) :
    um = up ∧ vm = vp ∧ gm = gp := by
  have hr := singleton_regimes_eq_of_schur_eq Q W hQ hW
    s um vm gm up vp gp hs hum hvm hgm hup hvp hgp he
  have hq := singleton_min_margin_eq_of_schur_eq Q W hQ hW
    s um vm gm s up vp gp hs hum hvm hgm hs hup hvp hgp he
  have hsmallp := hr.1.mp hsmall
  have huEq : um = up := by
    rw [min_eq_left hsmall.le, min_eq_left hsmallp.le] at hq
    exact hq
  refine ⟨huEq, ?_⟩
  subst up
  have hN := (Q.singletonContext s um vm gm hs hum hvm hgm).largestLabel_eq_of_schur_eq
    (W.singletonContext s um vp gp hs hup hvp hgp)
    (Q.singletonContext_connected s um vm gm hs hum hvm hgm)
    (W.singletonContext_connected s um vp gp hs hup hvp hgp) he
  have hvEq : vm = vp := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact singleton_margin_comparison_ne Q W hQ hW hZW hcore
        s um vm vp gm gp hs hum hvm hvp hgm hgp hsmall h hN he
    · exact singleton_margin_comparison_ne W Q hW hQ hZQ hcore.symm
        s um vp vm gp gm hs hum hvp hvm hgp hgm hsmallp h hN.symm he.symm
  refine ⟨hvEq, ?_⟩
  subst vp
  exact singleton_gap_eq_of_span_eq Q W hQ hW hcore
    s um vm gm gp hs hum hvm hgm hgp hN

/-- Core rotation gives the actual translate of the literal reflected core. -/
theorem rotated_core_translation (Q W : BetaDiagram n) (h : Q.RotationEquivalent W) :
    W.TranslationEquivalent Q.rotate := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, ?_⟩
  · intro i
    have hh := hc i.rev
    simp only [Fin.rev_rev] at hh
    change W.row i = -Q.col i.rev + c
    omega
  · intro i
    have hh := hr i.rev
    simp only [Fin.rev_rev] at hh
    change W.col i = -Q.row i.rev + c
    omega

/-- With actual margins fixed, the genuine endpoint leader excludes the last
possible reflected core; symmetric cores give literal translations directly. -/
theorem singleton_core_translation_at_fixed_margins (Q W : BetaDiagram (n + 2))
    (hW : W.Connected) (hcore : Q.schur = W.schur) (hRQ : Q.RotationRigid)
    (hLeader : ¬ Q.Symmetric → Q.EndpointLeader)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (he : (Q.singletonContext s u v g hs hu hv hg).schur =
      (W.singletonContext s u v g hs hu hv hg).schur) : Q.TranslationEquivalent W := by
  obtain hT | hR := (Q.rotationRigid_iff_same_order.mp hRQ) W hW hcore.symm
  · exact hT
  · by_cases hS : Q.Symmetric
    · exact Q.translation_of_rotation_of_symmetric W hS hR
    · have hTW := Q.rotated_core_translation W hR
      have hp := (W.singletonContext_translation Q.rotate hTW s u v g hs hu hv hg).schur_eq
      exact (Q.singletonContext_reflected_core_ne (hLeader hS) s u v g hs hu hv hg
        (he.trans hp)).elim

/-- Complete comparison of two actual singleton contexts.  The margins,
separator coefficients, and orientation exclusions are all produced internally. -/
theorem singletonContext_rigidity_between_contexts (Q W : BetaDiagram (n + 2))
    (hQ : Q.Connected) (hW : W.Connected) (hZQ : Q.ZeroFree) (hZW : W.ZeroFree)
    (hcore : Q.schur = W.schur) (hRQ : Q.RotationRigid)
    (hLeader : ¬ Q.Symmetric → Q.EndpointLeader)
    (s um vm gm up vp gp : ℤ)
    (hs : 0 < s) (hum : 0 < um) (hvm : 0 < vm) (hgm : 0 < gm)
    (hup : 0 < up) (hvp : 0 < vp) (hgp : 0 < gp)
    (he : (Q.singletonContext s um vm gm hs hum hvm hgm).schur =
      (W.singletonContext s up vp gp hs hup hvp hgp).schur) :
    (Q.singletonContext s um vm gm hs hum hvm hgm).TranslationEquivalent
      (W.singletonContext s up vp gp hs hup hvp hgp) := by
  by_cases hsmall : um < vm
  · obtain ⟨huEq, hvEq, hgEq⟩ := singleton_strict_top_margins_eq Q W hQ hW hZQ hZW hcore
      s um vm gm up vp gp hs hum hvm hgm hup hvp hgp hsmall he
    subst up
    subst vp
    subst gp
    have hT := singleton_core_translation_at_fixed_margins Q W hW hcore hRQ hLeader
      s um vm gm hs hum hvm hgm he
    exact Q.singletonContext_translation W hT s um vm gm hs hum hvm hgm
  · have hside : vm ≤ um := by omega
    have hIsolation (hz : Q.endpointDifference vm hvm = 0) : Q.Symmetric := by
      by_contra hS
      exact EndpointLeader.difference_ne_zero Q (hLeader hS) vm hvm hz
    have hT := singleton_core_translation_of_bottom_regime Q W hQ hW hcore hRQ
      s um vm gm up vp gp hs hum hvm hgm hup hvp hgp hside hIsolation he
    obtain ⟨hvEq, _⟩ := singleton_bottom_endpoint_eq_of_schur_eq Q W hQ hW hcore
      s um vm gm up vp gp hs hum hvm hgm hup hvp hgp hside he
    subst vp
    obtain ⟨huEq, hgEq⟩ := singleton_top_margin_of_bottom_translation Q W hT
      s um up vm gm gp hs hum hup hvm hgm hgp he
    subst up
    subst gp
    exact Q.singletonContext_translation W hT s um vm gm hs hum hvm hgm

/-- An arbitrary actual mate with a produced first singleton cut is recovered
without assuming its core function, singleton length, margins, or orientation. -/
theorem singletonContext_first_cut_comparison (Q : BetaDiagram (n + 2))
    (hQ : Q.Connected) (hZQ : Q.ZeroFree) (hRQ : Q.RotationRigid)
    (hLeader : ¬ Q.Symmetric → Q.EndpointLeader)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (F : BetaDiagram (n + 4)) (hF : F.Connected) (hZF : F.ZeroFree)
    (hcut : F.row (0 : Fin (n + 2)).succ.succ < F.col 0)
    (he : (Q.singletonContext s u v g hs hu hv hg).schur = F.schur) :
    (Q.singletonContext s u v g hs hu hv hg).TranslationEquivalent F := by
  let hP := F.positiveCorner_of_connected_zeroFree hF hZF
  let W := (F.cornerDiagram hP).tail
  obtain ⟨sp, up, vp, gp, hsp, hup, hvp, hgp, hTF⟩ :=
    F.singleton_parent_of_first_cut hP hcut
  have hparent : (Q.singletonContext s u v g hs hu hv hg).schur =
      (W.singletonContext sp up vp gp hsp hup hvp hgp).schur := he.trans hTF.schur_eq
  have hprod := (Q.singletonContext s u v g hs hu hv hg).cornerPolynomial_eq_of_schur_eq
    (W.singletonContext sp up vp gp hsp hup hvp hgp)
    (Q.singletonContext_connected s u v g hs hu hv hg)
    (W.singletonContext_connected sp up vp gp hsp hup hvp hgp) hparent
  rw [singletonContext_cornerPolynomial, singletonContext_cornerPolynomial] at hprod
  have hdiv : complete sp ∣ complete s * Q.schur := by
    rw [hprod]
    exact dvd_mul_right _ _
  have hsEq : sp = s := by
    obtain hd | hd := (complete_prime sp hsp).dvd_mul.mp hdiv
    · exact (complete_dvd_complete_iff sp s hsp hs).mp hd
    · exact (Q.complete_not_dvd_connected hQ sp hsp hd).elim
  subst sp
  have hcore : Q.schur = W.schur :=
    mul_left_cancel₀ ((complete_ne_zero_iff s).mpr hs.le) hprod
  have hW : W.Connected := by
    apply W.connected_of_schur_irreducible (by omega)
    rw [← hcore]
    exact Q.schur_irreducible hQ
  have hZW : W.ZeroFree := by
    intro i j h
    exact hZF i.succ.succ j.succ.castSucc h
  have hTP := singletonContext_rigidity_between_contexts Q W hQ hW hZQ hZW hcore
    hRQ hLeader s u v g up vp gp hs hu hv hg hup hvp hgp hparent
  obtain ⟨cp, hpr, hpc⟩ := hTP
  obtain ⟨cf, hfr, hfc⟩ := hTF
  refine ⟨cp - cf, ?_, ?_⟩
  · intro i
    have hp := hpr i
    have hf := hfr i
    change (Q.singletonContext s u v g hs hu hv hg).row i =
      (W.singletonContext s up vp gp hs hup hvp hgp).row i + cp at hp
    change F.row i = (W.singletonContext s up vp gp hs hup hvp hgp).row i + cf at hf
    omega
  · intro i
    have hp := hpc i
    have hf := hfc i
    change (Q.singletonContext s u v g hs hu hv hg).col i =
      (W.singletonContext s up vp gp hs hup hvp hgp).col i + cp at hp
    change F.col i = (W.singletonContext s up vp gp hs hup hvp hgp).col i + cf at hf
    omega

/-- Unique factorization of the actual maximal cofactor forces the singleton
to one of its two ends.  Both the geometric cut and the row-count match are
produced from the arbitrary mate, rather than assumed as a context shape. -/
theorem singleton_mate_singleton_side (Q : BetaDiagram (n + 2)) (hQ : Q.Connected)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (F : BetaDiagram (n + 4)) (hF : F.Connected) (hZF : F.ZeroFree)
    (he : (Q.singletonContext s u v g hs hu hv hg).schur = F.schur) :
    (F.row (0 : Fin (n + 2)).succ.succ < F.col 0) ∨
      (F.rotate.row (0 : Fin (n + 2)).succ.succ < F.rotate.col 0) := by
  let hP := F.positiveCorner_of_connected_zeroFree hF hZF
  let D := F.cornerDiagram hP
  have hprod := (Q.singletonContext s u v g hs hu hv hg).cornerPolynomial_eq_of_schur_eq F
    (Q.singletonContext_connected s u v g hs hu hv hg) hF he
  rw [singletonContext_cornerPolynomial, ← cornerDiagram_schur F hP] at hprod
  obtain ⟨C⟩ := D.exists_componentDecomposition
  let A := singletonDiagram s hs
  let xs : List (Σ k : ℕ, BetaDiagram k) := [⟨1, A⟩, ⟨n + 2, Q⟩]
  have hrel := D.component_matching_of_product C xs
    (by
      intro X hX
      simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact singletonDiagram_connected s hs
      · exact hQ)
    (by simpa only [xs, A, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, singletonDiagram_schur] using hprod)
  have hcard := Multiset.card_eq_card_of_rel hrel
  have hlen : C.components.length = 2 := by simpa only [xs, Multiset.coe_card,
    List.length_cons, List.length_nil] using hcard.symm
  obtain ⟨a, b, ha, hb, horder, hcut, hLC, hRC, hlist⟩ := D.component_list_two_cut C hlen
  have hrows : Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k => X.1 = Y.1)
      (xs : Multiset _) (C.components : Multiset _) := by
    apply hrel.mono
    intro X _ Y _ hXY
    have hd := congrArg MvPolynomial.totalDegree hXY
    simpa only [schur_totalDegree] using hd
  rw [hlist] at hrows
  obtain ⟨Y, hY, hYrow⟩ := Multiset.exists_mem_of_rel_of_mem hrows
    (show (⟨1, A⟩ : Σ k : ℕ, BetaDiagram k) ∈ (xs : Multiset _) by
      simp only [xs, Multiset.mem_coe, List.mem_cons, true_or])
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hY
  rcases hY with rfl | rfl
  · have ha1 : a = 1 := hYrow.symm
    subst a
    have hr : Fin.cast horder (⟨1, by omega⟩ : Fin (1 + b)) =
        (0 : Fin (n + 2)).succ := by
      apply Fin.ext
      rfl
    have hc : Fin.cast horder (⟨0, by omega⟩ : Fin (1 + b)) =
        (0 : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    change D.row (Fin.cast horder ⟨1, by omega⟩) <
      D.col (Fin.cast horder ⟨0, by omega⟩) at hcut
    rw [hr, hc] at hcut
    change F.row (0 : Fin (n + 2)).succ.succ < F.col 0 at hcut
    exact Or.inl hcut
  · have hb1 : b = 1 := hYrow.symm
    subst b
    have ha2 : a = n + 2 := by omega
    subst a
    have heOrder : horder = rfl := Subsingleton.elim _ _
    rw [heOrder] at hcut
    change D.row (Fin.last (n + 2)) <
      D.col (⟨n + 1, by omega⟩ : Fin (n + 3)) at hcut
    let j : Fin (n + 4) := (⟨n + 1, by omega⟩ : Fin (n + 3)).castSucc
    change F.row (Fin.last (n + 2)).succ < F.col j at hcut
    rw [Fin.succ_last] at hcut
    have hrev : ((0 : Fin (n + 2)).succ.succ : Fin (n + 4)).rev = j := by
      apply Fin.ext
      simp only [j, Fin.val_rev, Fin.val_succ, Fin.val_zero, Fin.val_castSucc]
      omega
    apply Or.inr
    change -F.col ((0 : Fin (n + 2)).succ.succ).rev < -F.row (0 : Fin (n + 4)).rev
    rw [hrev, Fin.rev_zero]
    change F.row (Fin.last (n + 3)) < F.col j at hcut
    omega

/-- Full arbitrary-mate singleton rigidity from the actual core and fixed
leader.  Endpoint isolation is derived at the point of use. -/
theorem singletonContext_rotationRigid (Q : BetaDiagram (n + 2))
    (hQ : Q.Connected) (hZQ : Q.ZeroFree) (hRQ : Q.RotationRigid)
    (hLeader : ¬ Q.Symmetric → Q.EndpointLeader)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).RotationRigid := by
  rw [rotationRigid_iff_same_order]
  intro F hF he
  have hsource := Q.singletonContext_connected s u v g hs hu hv hg
  have hZF := (Q.singletonContext s u v g hs hu hv hg).zeroFree_of_schur_eq F
    hsource hF (Q.singletonContext_zeroFree hZQ s u v g hs hu hv hg) he.symm
  rcases singleton_mate_singleton_side Q hQ s u v g hs hu hv hg F hF hZF he.symm with h | h
  · exact Or.inl (singletonContext_first_cut_comparison Q hQ hZQ hRQ hLeader
      s u v g hs hu hv hg F hF hZF h he.symm)
  · have hFR := F.rotate_connected hF
    have hZFR : F.rotate.ZeroFree := by
      intro i j hh
      apply hZF j.rev i.rev
      change -F.col i.rev = -F.row j.rev at hh
      omega
    have hpoly : (Q.singletonContext s u v g hs hu hv hg).schur = F.rotate.schur :=
      he.symm.trans F.rotate_schur.symm
    have hT := singletonContext_first_cut_comparison Q hQ hZQ hRQ hLeader
      s u v g hs hu hv hg F.rotate hFR hZFR h hpoly
    exact Or.inr (((Q.singletonContext s u v g hs hu hv hg).translation_rotate_iff_rotation F).mp hT)

/-- Dense nonlinear cores supply every premise of the genuine arbitrary-mate
singleton theorem, including the two-row core needed for four-row parents. -/
theorem singletonContext_rotationRigid_of_dense (Q : BetaDiagram (n + 2)) (hD : Q.Dense)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).RotationRigid := by
  have hQ := hD.connected (by omega)
  exact Q.singletonContext_rotationRigid hQ hD.zeroFree
    (Q.rotationRigid_of_nonnegative hQ hD.nonnegative)
    (fun hS => Q.endpointLeader_dense hD hS) s u v g hs hu hv hg

end SkewJacobiNegative.BetaDiagram
