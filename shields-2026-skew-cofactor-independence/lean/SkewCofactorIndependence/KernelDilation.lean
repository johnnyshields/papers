/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.EndpointNormalization

/-!
# Dilation of the full unit kernel

`thm:dilation` for the actual finite unit-relation spaces.  The inherited
summand is the entire unit kernel.  The reverse inclusion uses rational
independence of the actual signed cofactors and derives coefficientwise
vanishing by `dilation_offGrid_independence`.
-/

noncomputable section
namespace SkewCofactorIndependence
open scoped BigOperators
open StrictTriangularPaths

/-- Divisibility of a residue's least representative agrees with divisibility of its lift. -/
theorem residue_grid_iff (t g : ℕ) (hg : 0 < g) (ht : 0 < t) (z : ℤ) :
    t ∣ (z : ZMod (t * g)).val ↔ (t : ℤ) ∣ z := by
  let : NeZero (t * g) := ⟨Nat.ne_of_gt (Nat.mul_pos ht hg)⟩
  let r : ZMod (t * g) := z
  have he : (z : ZMod (t * g)) = (r.val : ℤ) := by
    simpa only [Int.cast_natCast] using (ZMod.natCast_zmod_val r).symm
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub z (r.val : ℤ) (t * g)).1 he
  have hdt : (t : ℤ) ∣ (r.val : ℤ) - z :=
    dvd_trans (by exact_mod_cast (dvd_mul_right t g)) hd
  change t ∣ r.val ↔ (t : ℤ) ∣ z
  constructor
  · intro h
    have hi : (t : ℤ) ∣ (r.val : ℤ) := Int.natCast_dvd_natCast.mpr h
    have hh := dvd_sub hi hdt
    convert hh using 1; ring
  · intro h
    have hh := dvd_add hdt h
    have hi : (t : ℤ) ∣ (r.val : ℤ) := by
      convert hh using 1; ring
    exact Int.natCast_dvd_natCast.mp hi

/-- Transport an actual residue function along an equality of its moduli. -/
def transportResidueFunction {q q' : ℕ} (h : q = q') (f : ZMod q → ℚ) :
    ZMod q' → ℚ :=
  fun r => f (Equiv.cast (congrArg ZMod h.symm) r)

@[simp] theorem transportResidueFunction_intCast {q q' : ℕ}
    (h : q = q') (f : ZMod q → ℚ) (z : ℤ) :
    transportResidueFunction h f (z : ZMod q') = f (z : ZMod q) := by
  cases h
  rfl

/-- Modulus and span transport preserve the actual odd-function equations. -/
theorem transportResidueFunction_odd {q q' N N' : ℕ}
    (hq : q = q') (hN : N = N') (f : oddResidueSpace q N) :
    transportResidueFunction hq f.val ∈ oddResidueSpace q' N' := by
  cases hq
  cases hN
  exact f.property

namespace BetaDiagram
variable {n : ℕ}

/-- The full finite beta interval, with endpoint values retained. -/
def intervalRelation (D : BetaDiagram (n + 1)) (c : ℤ → ℚ) : CompleteRing :=
  ∑ z ∈ Finset.Ioo (D.col (Fin.last n)) (D.row 0), c z • D.unitVariation z

/-- Zero extension from the actual finite available positions. -/
def availableExtension (D : BetaDiagram (n + 1)) (c : D.Available → ℚ) (z : ℤ) : ℚ :=
  if hz : z ∈ D.availablePositions then c ⟨z, hz⟩ else 0

@[simp] theorem availableExtension_available (D : BetaDiagram (n + 1))
    (c : D.Available → ℚ) (z : D.Available) : D.availableExtension c z.val = c z := by
  simp [availableExtension, z.property]

/-- Endpoint cancellation identifies a full-interval relation with its available restriction. -/
theorem intervalRelation_eq (D : BetaDiagram (n + 1)) (hz : D.ZeroFree)
    (c : ℤ → ℚ) : D.intervalRelation c =
      D.unitRelationMap (fun z => c z.val) := by
  classical
  change (∑ z ∈ Finset.Ioo (D.col (Fin.last n)) (D.row 0), c z • D.unitVariation z) =
    ∑ z : D.Available, c z.val • D.unitVariation z.val
  have hs : (∑ z : D.Available, c z.val • D.unitVariation z.val) =
      ∑ z ∈ D.availablePositions, c z • D.unitVariation z :=
    Finset.sum_coe_sort D.availablePositions (fun z : ℤ => c z • D.unitVariation z)
  rw [hs]
  symm
  apply Finset.sum_subset
  · exact Finset.filter_subset _ _
  · intro z hzI hzA
    have he : (∃ i, z = D.row i) ∨ ∃ j, z = D.col j := by
      simp only [availablePositions, Finset.mem_filter, hzI, true_and,
        Finset.mem_image, Finset.mem_univ, true_and, not_and_or, not_not] at hzA
      simpa only [eq_comm] using hzA
    rw [D.unitVariation_endpoint hz z he, smul_zero]

/-- Expanding the actual unit relation produces precisely the cofactor-weighted quadratics. -/
theorem intervalRelation_quadratics (D : BetaDiagram (n + 1))
    (hD : D.Normalized) (c : ℤ → ℚ) :
    D.intervalRelation c =
      ∑ i, ∑ j, D.cofactor i j * returnQuadratic c (D.col j) (D.row i) := by
  classical
  have hb := D.normalized_bounds hD
  have hlast : D.col (Fin.last n) = 0 := hD (by omega)
  have edge (i j : Fin (n + 1)) :
      (∑ z ∈ Finset.Ioo (D.col (Fin.last n)) (D.row 0),
        c z • (positiveGap complete (D.row i) z * positiveGap complete z (D.col j))) =
      returnQuadratic c (D.col j) (D.row i) := by
    unfold returnQuadratic
    symm
    calc
      (∑ z ∈ Finset.Ioo (D.col j) (D.row i),
        c z • (complete (D.row i - z) * complete (z - D.col j))) =
        ∑ z ∈ Finset.Ioo (D.col j) (D.row i),
          c z • (positiveGap complete (D.row i) z * positiveGap complete z (D.col j)) := by
            apply Finset.sum_congr rfl
            intro z hz
            have hp := Finset.mem_Ioo.mp hz
            rw [positiveGap_of_lt complete hp.2, positiveGap_of_lt complete hp.1]
      _ = _ := by
        apply Finset.sum_subset
        · intro z hz
          have hp := Finset.mem_Ioo.mp hz
          simp only [Finset.mem_Ioo, hlast]
          exact ⟨lt_of_le_of_lt (hb.2 j).1 hp.1, lt_of_lt_of_le hp.2 (hb.1 i).2⟩
        · intro z hzI hzE
          simp only [Finset.mem_Ioo, not_and_or, not_lt] at hzE
          rcases hzE with h | h
          · rw [positiveGap_of_le complete h, mul_zero, smul_zero]
          · rw [positiveGap_of_le complete h, zero_mul, smul_zero]
  unfold intervalRelation unitVariation
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← edge i j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [Algebra.smul_def]
  ring

/-- Killing each edge suffices to kill the actual available unit relation. -/
theorem allEdgeReturnsZero.mem_kernel {D : BetaDiagram (n + 1)} {c : ℤ → ℚ}
    (hc : D.allEdgeReturnsZero c) (hz : D.ZeroFree) (hD : D.Normalized) :
    (fun z : D.Available => c z.val) ∈ D.unitKernel := by
  change D.unitRelationMap _ = 0
  rw [← D.intervalRelation_eq hz c, D.intervalRelation_quadratics hD c]
  have hzero (i j : Fin (n + 1)) :
      returnQuadratic c (D.col j) (D.row i) = 0 := hc i j
  simp only [hzero, mul_zero, Finset.sum_const_zero]

/-- Linear relation maps commute with extension along the actual available grid. -/
theorem unitRelationMap_gridLift (D : BetaDiagram (n + 1)) (t : ℕ+)
    (c : D.Available → ℚ) :
    (D.dilate t).unitRelationMap (D.gridLift t c) = dilation t (D.unitRelationMap c) := by
  classical
  change (∑ w : (D.dilate t).Available, D.gridLift t c w •
      (D.dilate t).unitVariation w.val) =
    dilation t (∑ z : D.Available, c z • D.unitVariation z.val)
  rw [map_sum]
  let s : Finset (D.dilate t).Available := Finset.univ.map (D.gridPosition t)
  calc
    (∑ w, D.gridLift t c w • (D.dilate t).unitVariation w.val) =
      ∑ w ∈ s, D.gridLift t c w • (D.dilate t).unitVariation w.val := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro w hw hs
        have hn : ¬ ∃ z, D.gridPosition t z = w := by simpa [s] using hs
        change (if h : ∃ z, D.gridPosition t z = w then c (Classical.choose h) else 0) •
          (D.dilate t).unitVariation w.val = 0
        rw [dite_eq_right hn, zero_smul]
    _ = ∑ z : D.Available, c z • dilation t (D.unitVariation z.val) := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro z hz
      rw [D.gridLift_gridPosition]
      change c z • (D.dilate t).unitVariation ((t : ℕ) * z.val) =
        c z • dilation t (D.unitVariation z.val)
      rw [D.dilate_unitVariation]
    _ = _ := by simp only [map_smul]

/-- Inherited grid relations are exactly, not merely contained in, the base kernel. -/
theorem gridLift_mem_kernel_iff (D : BetaDiagram (n + 1)) (t : ℕ+)
    (c : D.Available → ℚ) :
    D.gridLift t c ∈ (D.dilate t).unitKernel ↔ c ∈ D.unitKernel := by
  change (D.dilate t).unitRelationMap _ = 0 ↔ D.unitRelationMap _ = 0
  rw [D.unitRelationMap_gridLift, dilation_eq_zero_iff]

/-- The full inherited kernel; no arithmetic replacement of the base kernel is made. -/
def inheritedKernel (D : BetaDiagram (n + 1)) (t : ℕ+) :
    Submodule ℚ ((D.dilate t).Available → ℚ) := D.unitKernel.map (D.gridLift t)

/-- The actual image of the off-grid odd residue space under available-position restriction. -/
def arithmeticOffGrid (D : BetaDiagram (n + 1)) (t : ℕ+) :
    Submodule ℚ ((D.dilate t).Available → ℚ) :=
  (offGridResidueSpace (t : ℕ) D.endpointModulus D.span).map
    ((D.dilate t).residueRestriction ((t : ℕ) * D.endpointModulus))

/-- Projection onto the entire inherited coordinate grid. -/
def gridPart (D : BetaDiagram (n + 1)) (t : ℕ+)
    (c : (D.dilate t).Available → ℚ) : (D.dilate t).Available → ℚ :=
  D.gridLift t (D.gridRestrict t c)

/-- The complementary coordinate projection, zero at every grid position. -/
def offGridPart (D : BetaDiagram (n + 1)) (t : ℕ+)
    (c : (D.dilate t).Available → ℚ) : (D.dilate t).Available → ℚ := c - D.gridPart t c

theorem gridPart_add_offGridPart (D : BetaDiagram (n + 1)) (t : ℕ+)
    (c : (D.dilate t).Available → ℚ) : D.gridPart t c + D.offGridPart t c = c := by
  simp [offGridPart]

theorem offGridPart_grid (D : BetaDiagram (n + 1)) (t : ℕ+)
    (c : (D.dilate t).Available → ℚ) (w : (D.dilate t).Available)
    (hw : (t : ℤ) ∣ w.val) : D.offGridPart t c w = 0 := by
  obtain ⟨z, rfl⟩ := (D.gridPosition_range t w).2 hw
  simp [offGridPart, gridPart, gridRestrict]

set_option backward.isDefEq.respectTransparency false in
/-- A nondivisible actual unit has weighted nondivisible degree two. -/
theorem unitVariation_offGrid_homogeneous (D : BetaDiagram (n + 1)) (t : ℕ+)
    (z : ℤ) (hz : ¬ (t : ℤ) ∣ z) :
    MvPolynomial.IsWeightedHomogeneous (offGridWeight t) ((D.dilate t).unitVariation z) 2 := by
  classical
  unfold unitVariation
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i hi
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j hj
  by_cases ha : z < (t : ℕ) * D.row i
  · by_cases hb : (t : ℕ) * D.col j < z
    · let a := offGridReturnIndex t (D.row i) z ha hz
      let b := offGridReturnIndex t (-D.col j) (-z) (by linarith) (by simpa using hz)
      have he : (D.dilate t).cofactor i j *
          positiveGap complete ((D.dilate t).row i) z *
          positiveGap complete z ((D.dilate t).col j) =
          dilation t (D.cofactor i j) * (MvPolynomial.X a.val * MvPolynomial.X b.val) := by
        rw [dilate_cofactor, dilate_row, dilate_col,
          positiveGap_of_lt complete ha, positiveGap_of_lt complete hb,
          complete_of_pos (by omega), complete_of_pos (by omega)]
        have hb' : b.val = ⟨(z - (t : ℕ) * D.col j).toNat, by omega⟩ := by
          apply Subtype.ext
          change ((t : ℕ) * (-D.col j) - (-z)).toNat = _
          congr 1; ring
        rw [hb']
        exact mul_assoc _ _ _
      rw [he]
      simpa using (dilation_weightedHomogeneous t (D.cofactor i j)).mul
        (offGrid_pair_weightedHomogeneous t a b)
    · rw [dilate_col, positiveGap_of_le complete (le_of_not_gt hb), mul_zero]
      exact MvPolynomial.isWeightedHomogeneous_zero ℚ (offGridWeight t) (2 : ℕ)
  · rw [dilate_row, positiveGap_of_le complete (le_of_not_gt ha), mul_zero, zero_mul]
    exact MvPolynomial.isWeightedHomogeneous_zero ℚ (offGridWeight t) (2 : ℕ)

/-- Weighted separation is applied to actual finite relation maps. -/
theorem unitRelationMap_separation (D : BetaDiagram (n + 1)) (t : ℕ+)
    (c : (D.dilate t).Available → ℚ) (hc : c ∈ (D.dilate t).unitKernel) :
    D.gridRestrict t c ∈ D.unitKernel ∧ D.offGridPart t c ∈ (D.dilate t).unitKernel := by
  classical
  let p := (D.dilate t).unitRelationMap (D.gridPart t c)
  let q := (D.dilate t).unitRelationMap (D.offGridPart t c)
  have hp : MvPolynomial.IsWeightedHomogeneous (offGridWeight t) p 0 := by
    rw [show p = dilation t (D.unitRelationMap (D.gridRestrict t c)) from
      D.unitRelationMap_gridLift t _]
    exact dilation_weightedHomogeneous t _
  have hq : MvPolynomial.IsWeightedHomogeneous (offGridWeight t) q 2 := by
    change MvPolynomial.IsWeightedHomogeneous (offGridWeight t)
      (∑ w : (D.dilate t).Available, D.offGridPart t c w •
        (D.dilate t).unitVariation w.val) 2
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro w hw
    by_cases hd : (t : ℤ) ∣ w.val
    · rw [D.offGridPart_grid t c w hd, zero_smul]
      exact MvPolynomial.isWeightedHomogeneous_zero ℚ (offGridWeight t) (2 : ℕ)
    · simpa only [MvPolynomial.smul_eq_C_mul] using
        (D.unitVariation_offGrid_homogeneous t w.val hd).C_mul (D.offGridPart t c w)
  have he : p + q = 0 := by
    change (D.dilate t).unitRelationMap (D.gridPart t c) +
      (D.dilate t).unitRelationMap (D.offGridPart t c) = 0
    rw [← map_add, D.gridPart_add_offGridPart]
    exact hc
  obtain ⟨hpz, hqz⟩ := grid_offGrid_separation t hp hq he
  refine ⟨?_, hqz⟩
  apply (dilation_eq_zero_iff t _).1
  exact (D.unitRelationMap_gridLift t _).symm.trans hpz

/-- The extension of an off-grid vector is zero on every grid integer, endpoints included. -/
theorem availableExtension_offGrid (D : BetaDiagram (n + 1)) (t : ℕ+)
    (c : (D.dilate t).Available → ℚ)
    (hc : ∀ w, (t : ℤ) ∣ w.val → c w = 0) :
    ∀ z, (t : ℤ) ∣ z → (D.dilate t).availableExtension c z = 0 := by
  intro z hz
  unfold availableExtension
  split_ifs with h
  · exact hc ⟨z, h⟩ hz
  · rfl

/-- The manuscript's coefficientwise vanishing is derived from the compiled
independence theorem over the actual disjoint return alphabet. -/
theorem offGrid_relation_edges (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hD : D.Normalized) (hz : D.ZeroFree)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2))
    (c : (D.dilate t).Available → ℚ)
    (hcgrid : ∀ w, (t : ℤ) ∣ w.val → c w = 0)
    (hc : c ∈ (D.dilate t).unitKernel) :
    (D.dilate t).allEdgeReturnsZero ((D.dilate t).availableExtension c) := by
  classical
  let e := (D.dilate t).availableExtension c
  have hegrid : ∀ z, (t : ℤ) ∣ z → e z = 0 :=
    D.availableExtension_offGrid t c hcgrid
  have hrelation : (D.dilate t).intervalRelation e = 0 := by
    rw [(D.dilate t).intervalRelation_eq (hz.dilate t)]
    have hv : (fun z : (D.dilate t).Available => e z.val) = c := by
      funext z
      exact (D.dilate t).availableExtension_available c z
    rw [hv]
    exact hc
  rw [(D.dilate t).intervalRelation_quadratics (hD.dilate t)] at hrelation
  have halphabet : ∑ ij : Fin (n + 1) × Fin (n + 1),
      dilation t (D.cofactor ij.1 ij.2) *
        offGridEmbed t (offGridQuadratic t e (D.col ij.2) (D.row ij.1)) = 0 := by
    simpa only [Fintype.sum_prod_type, dilate_cofactor,
      offGridEmbed_quadratic t e _ _ hegrid, dilate_row, dilate_col] using hrelation
  have hcoeff := dilation_offGrid_independence t
    (fun ij : Fin (n + 1) × Fin (n + 1) => D.cofactor ij.1 ij.2)
    (fun ij => offGridQuadratic t e (D.col ij.2) (D.row ij.1)) hind halphabet
  intro i j
  change returnQuadratic e ((t : ℕ) * D.col j) ((t : ℕ) * D.row i) = 0
  rw [← offGridEmbed_quadratic t e (D.col j) (D.row i) hegrid, hcoeff (i, j), map_zero]

/-- Restriction of off-grid residue functions to the actual dilated available positions. -/
def offGridRestriction (D : BetaDiagram (n + 1)) (t : ℕ+) :
    offGridResidueSpace (t : ℕ) D.endpointModulus D.span →ₗ[ℚ]
      ((D.dilate t).Available → ℚ) :=
  ((D.dilate t).residueRestriction ((t : ℕ) * D.endpointModulus)).comp
    (offGridResidueSpace (t : ℕ) D.endpointModulus D.span).subtype

/-- The image is exactly the manuscript's arithmetic off-grid summand. -/
theorem offGridRestriction_range (D : BetaDiagram (n + 1)) (t : ℕ+) :
    (D.offGridRestriction t).range = D.arithmeticOffGrid t := by
  rw [offGridRestriction, LinearMap.range_comp, Submodule.range_subtype]
  rfl

/-- On every available grid position an off-grid residue restriction is zero. -/
theorem arithmeticOffGrid_grid (D : BetaDiagram (n + 1)) (t : ℕ+) (hn : 1 ≤ n)
    (c : (D.dilate t).Available → ℚ) (hc : c ∈ D.arithmeticOffGrid t)
    (w : (D.dilate t).Available) (hw : (t : ℤ) ∣ w.val) : c w = 0 := by
  obtain ⟨φ, hφ, rfl⟩ := hc
  have hzero := (mem_offGridResidueSpace_iff _ _ _ φ).1 hφ
  exact hzero.2 _ ((residue_grid_iff (t : ℕ) D.endpointModulus
    (D.endpointModulus_pos hn) t.property w.val).2 hw)

/-- Arithmetic residue restrictions are genuine unit relations without cofactor independence. -/
theorem arithmeticOffGrid_le_kernel (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hD : D.Normalized) (hz : D.ZeroFree) :
    D.arithmeticOffGrid t ≤ (D.dilate t).unitKernel := by
  intro c hc
  obtain ⟨φ, hφ, rfl⟩ := hc
  have ho : φ ∈ oddResidueSpace ((t : ℕ) * D.endpointModulus) ((t : ℕ) * D.span) :=
    ⟨hφ.1, fun r hr => False.elim (hr trivial)⟩
  let ψ := transportResidueFunction (D.dilate_endpointModulus t).symm φ
  have hψ : ψ ∈ oddResidueSpace (D.dilate t).endpointModulus (D.dilate t).span :=
    transportResidueFunction_odd (D.dilate_endpointModulus t).symm
      (D.dilate_span t hD).symm ⟨φ, ho⟩
  have hk := ((D.dilate t).residue_allEdgeReturnsZero (hD.dilate t) ⟨ψ, hψ⟩).mem_kernel
    (hz.dilate t) (hD.dilate t)
  have hf : (fun z : (D.dilate t).Available =>
      ψ (z.val : ZMod (D.dilate t).endpointModulus)) =
      (D.dilate t).residueRestriction ((t : ℕ) * D.endpointModulus) φ := by
    funext z
    exact transportResidueFunction_intCast (D.dilate_endpointModulus t).symm φ z.val
  rw [hf] at hk
  exact hk

/-- Inherited base relations are genuine dilated relations without cofactor independence. -/
theorem inheritedKernel_le_kernel (D : BetaDiagram (n + 1)) (t : ℕ+) :
    D.inheritedKernel t ≤ (D.dilate t).unitKernel := by
  rintro c ⟨b, hb, rfl⟩
  exact (D.gridLift_mem_kernel_iff t b).2 hb

/-- The two actual images have disjoint coordinate supports and hence trivial intersection. -/
theorem inherited_arithmetic_disjoint (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) : Disjoint (D.inheritedKernel t) (D.arithmeticOffGrid t) := by
  rw [Submodule.disjoint_def]
  intro c hc ha
  obtain ⟨b, hb, rfl⟩ := hc
  funext w
  by_cases hw : (t : ℤ) ∣ w.val
  · exact D.arithmeticOffGrid_grid t hn _ ha w hw
  · exact D.gridLift_offGrid t b w hw

/-- The unconditional direction of `thm:dilation`, with its actual internal direct sum. -/
theorem dilation_kernel_containment (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hD : D.Normalized) (hz : D.ZeroFree) :
    D.inheritedKernel t ⊔ D.arithmeticOffGrid t ≤ (D.dilate t).unitKernel ∧
      Disjoint (D.inheritedKernel t) (D.arithmeticOffGrid t) :=
  ⟨sup_le (D.inheritedKernel_le_kernel t) (D.arithmeticOffGrid_le_kernel t hD hz),
    D.inherited_arithmetic_disjoint t hn⟩

/-- Every off-grid residue has an actual available representative; endpoints are all grid points. -/
theorem offGrid_residue_available (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hD : D.Normalized)
    (r : ZMod ((t : ℕ) * D.endpointModulus)) (hr : ¬ (t : ℕ) ∣ r.val) :
    ∃ w : (D.dilate t).Available,
      (w.val : ZMod ((t : ℕ) * D.endpointModulus)) = r := by
  let : NeZero ((t : ℕ) * D.endpointModulus) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos t.property (D.endpointModulus_pos hn))⟩
  have hval := ZMod.val_lt r
  have hgN := D.endpointModulus_lt_span hn hD
  have hN := D.span_intCast hD
  have hbase : D.col (Fin.last n) = 0 := hD (by omega)
  have hlast : (D.dilate t).col (Fin.last n) = 0 := by
    simp only [dilate_col, hbase, mul_zero]
  have ht : (0 : ℤ) < (t : ℕ) := by exact_mod_cast t.property
  have hrpos : 0 < r.val := by
    by_contra h
    have he : r.val = 0 := by omega
    exact hr (he ▸ dvd_zero (t : ℕ))
  have hspan : r.val < (t : ℕ) * D.span :=
    lt_trans hval (Nat.mul_lt_mul_of_pos_left hgN t.property)
  have hw : (r.val : ℤ) ∈ (D.dilate t).availablePositions := by
    rw [mem_availablePositions, hlast]
    refine ⟨by exact_mod_cast hrpos, ?_, ?_, ?_⟩
    · change (r.val : ℤ) < (t : ℕ) * D.row 0
      rw [← hN]
      exact_mod_cast hspan
    · intro i he
      apply hr
      apply Int.natCast_dvd_natCast.mp
      rw [he]
      exact dvd_mul_right _ _
    · intro j he
      apply hr
      apply Int.natCast_dvd_natCast.mp
      rw [he]
      exact dvd_mul_right _ _
  exact ⟨⟨r.val, hw⟩, by simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val r⟩

/-- Restriction loses no off-grid residue coordinate. -/
theorem offGridRestriction_injective (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hD : D.Normalized) :
    Function.Injective (D.offGridRestriction t) := by
  intro φ ψ h
  apply Subtype.ext
  funext r
  by_cases hr : (t : ℕ) ∣ r.val
  · rw [φ.property.2 r (by simpa using hr), ψ.property.2 r (by simpa using hr)]
  · obtain ⟨w, hw⟩ := D.offGrid_residue_available t hn hD r hr
    have he := congrFun h w
    change (φ : ZMod ((t : ℕ) * D.endpointModulus) → ℚ)
        (w.val : ZMod ((t : ℕ) * D.endpointModulus)) =
      (ψ : ZMod ((t : ℕ) * D.endpointModulus) → ℚ)
        (w.val : ZMod ((t : ℕ) * D.endpointModulus)) at he
    simpa only [hw] using he

/-- Edgewise vanishing with prescribed grid zeros gives an actual off-grid residue restriction. -/
theorem offGrid_edges_mem_arithmetic (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized)
    (c : (D.dilate t).Available → ℚ)
    (hcgrid : ∀ w, (t : ℤ) ∣ w.val → c w = 0)
    (hedge : (D.dilate t).allEdgeReturnsZero ((D.dilate t).availableExtension c)) :
    c ∈ D.arithmeticOffGrid t := by
  let : NeZero ((t : ℕ) * D.endpointModulus) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos t.property (D.endpointModulus_pos hn))⟩
  obtain ⟨φ₀, hφ₀⟩ := (D.dilate t).endpoint_normalization_word
    hn (hconn.dilate t) (hz.dilate t) (hD.dilate t)
    ((D.dilate t).availableExtension c) hedge
  let φ : oddResidueSpace ((t : ℕ) * D.endpointModulus) ((t : ℕ) * D.span) :=
    ⟨transportResidueFunction (D.dilate_endpointModulus t) φ₀.val,
      transportResidueFunction_odd (D.dilate_endpointModulus t) (D.dilate_span t hD) φ₀⟩
  have hφ : ∀ z : ℤ, 0 < z → z < (D.dilate t).row 0 →
      (D.dilate t).availableExtension c z =
        (φ : ZMod ((t : ℕ) * D.endpointModulus) → ℚ) (z : ZMod ((t : ℕ) * D.endpointModulus)) := by
    intro z hz₁ hz₂
    exact (hφ₀ z hz₁ hz₂).trans
      (transportResidueFunction_intCast (D.dilate_endpointModulus t) φ₀.val z).symm
  have hegrid := D.availableExtension_offGrid t c hcgrid
  have hzero : ∀ r : ZMod ((t : ℕ) * D.endpointModulus),
      (t : ℕ) ∣ r.val → (φ : ZMod ((t : ℕ) * D.endpointModulus) → ℚ) r = 0 := by
    intro r hr
    let z : ℕ := if r.val = 0 then (t : ℕ) * D.endpointModulus else r.val
    have hzpos : 0 < z := by
      dsimp [z]
      split_ifs with h
      · exact Nat.mul_pos t.property (D.endpointModulus_pos hn)
      · omega
    have hzN : z < (t : ℕ) * D.span := by
      have hgN := D.endpointModulus_lt_span hn hD
      have hval := ZMod.val_lt r
      dsimp [z]
      split_ifs <;> nlinarith [t.property]
    have hzgrid : (t : ℤ) ∣ (z : ℤ) := by
      dsimp [z]
      split_ifs
      · exact_mod_cast (dvd_mul_right (t : ℕ) D.endpointModulus)
      · exact_mod_cast hr
    have hzcast : (z : ZMod ((t : ℕ) * D.endpointModulus)) = r := by
      dsimp [z]
      split_ifs with h
      · have he : r = 0 := by apply ZMod.val_injective; simpa using h
        simp [he]
      · exact ZMod.natCast_zmod_val r
    have hN := D.span_intCast hD
    have he := hφ (z : ℤ) (by exact_mod_cast hzpos) (by
      change (z : ℤ) < (t : ℕ) * D.row 0
      rw [← hN]
      exact_mod_cast hzN)
    rw [hegrid _ hzgrid] at he
    simpa only [Int.cast_natCast, hzcast] using he.symm
  refine ⟨(φ : ZMod ((t : ℕ) * D.endpointModulus) → ℚ), ?_, ?_⟩
  · exact (mem_offGridResidueSpace_iff _ _ _ _).2 ⟨φ.property.1, hzero⟩
  · funext w
    have hp := ((D.dilate t).mem_availablePositions w.val).1 w.property
    have hbase : D.col (Fin.last n) = 0 := hD (by omega)
    have hlast : (D.dilate t).col (Fin.last n) = 0 := by
      simp only [dilate_col, hbase, mul_zero]
    exact (hφ w.val (by simpa only [hlast] using hp.1) hp.2.1).symm.trans
      ((D.dilate t).availableExtension_available c w)

/-- Every actual off-grid unit relation is arithmetic when the actual cofactors are independent. -/
theorem offGrid_relation_mem_arithmetic (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2))
    (c : (D.dilate t).Available → ℚ)
    (hcgrid : ∀ w, (t : ℤ) ∣ w.val → c w = 0)
    (hc : c ∈ (D.dilate t).unitKernel) :
    c ∈ D.arithmeticOffGrid t :=
  D.offGrid_edges_mem_arithmetic t hn hconn hz hD c hcgrid
    (D.offGrid_relation_edges t hD hz hind c hcgrid hc)

/-- `thm:dilation`: equality of the actual finite relation space with its two actual images. -/
theorem dilation_kernel (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) :
    (D.dilate t).unitKernel = D.inheritedKernel t ⊔ D.arithmeticOffGrid t ∧
      Disjoint (D.inheritedKernel t) (D.arithmeticOffGrid t) := by
  refine ⟨le_antisymm ?_ (D.dilation_kernel_containment t hn hD hz).1,
    D.inherited_arithmetic_disjoint t hn⟩
  intro c hc
  obtain ⟨hgrid, hoff⟩ := D.unitRelationMap_separation t c hc
  have hi : D.gridPart t c ∈ D.inheritedKernel t :=
    ⟨D.gridRestrict t c, hgrid, rfl⟩
  have ha : D.offGridPart t c ∈ D.arithmeticOffGrid t :=
    D.offGrid_relation_mem_arithmetic t hn hconn hz hD hind _
      (D.offGridPart_grid t c) hoff
  rw [← D.gridPart_add_offGridPart t c]
  exact Submodule.add_mem_sup hi ha

/-- The summand parameters are identified with the actual unit kernel, not only its dimension. -/
def dilationKernelEquiv (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) :
    (D.unitKernel × offGridResidueSpace (t : ℕ) D.endpointModulus D.span) ≃ₗ[ℚ]
      (D.dilate t).unitKernel := by
  let F : (D.unitKernel × offGridResidueSpace (t : ℕ) D.endpointModulus D.span) →ₗ[ℚ]
      ((D.dilate t).Available → ℚ) :=
    ((D.gridLift t).comp D.unitKernel.subtype).comp (LinearMap.fst ℚ _ _) +
      (D.offGridRestriction t).comp (LinearMap.snd ℚ _ _)
  have hF : ∀ x, F x ∈ (D.dilate t).unitKernel := by
    intro x
    apply Submodule.add_mem
    · exact (D.gridLift_mem_kernel_iff t _).2 x.1.property
    · apply D.arithmeticOffGrid_le_kernel t hD hz
      rw [← D.offGridRestriction_range t]
      exact ⟨x.2, rfl⟩
  let G := F.codRestrict (D.dilate t).unitKernel hF
  apply LinearEquiv.ofBijective G
  constructor
  · intro x y h
    have he := congrArg (fun c : (D.dilate t).unitKernel =>
      D.gridRestrict t c.val) h
    have hzero (φ : offGridResidueSpace (t : ℕ) D.endpointModulus D.span) :
        D.gridRestrict t (D.offGridRestriction t φ) = 0 := by
      funext z
      exact D.arithmeticOffGrid_grid t hn _ (by
        rw [← D.offGridRestriction_range t]; exact ⟨φ, rfl⟩)
        (D.gridPosition t z) ⟨z.val, rfl⟩
    have hfirst : x.1 = y.1 := by
      apply Subtype.ext
      simp only [G, F, LinearMap.codRestrict_apply, LinearMap.add_apply,
        LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
        map_add, gridRestrict_gridLift, hzero, add_zero] at he
      change x.1.val = y.1.val at he
      exact he
    have hsecond : x.2 = y.2 := by
      apply D.offGridRestriction_injective t hn hD
      have hh := congrArg Subtype.val h
      change D.gridLift t x.1.val + D.offGridRestriction t x.2 =
        D.gridLift t y.1.val + D.offGridRestriction t y.2 at hh
      rw [hfirst] at hh
      exact add_left_cancel hh
    exact Prod.ext hfirst hsecond
  · intro c
    have hc : c.val ∈ D.inheritedKernel t ⊔ D.arithmeticOffGrid t := by
      rw [← (D.dilation_kernel t hn hconn hz hD hind).1]
      exact c.property
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hc
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    rw [← D.offGridRestriction_range t] at hb
    obtain ⟨φ, rfl⟩ := hb
    refine ⟨(⟨a₀, ha₀⟩, φ), Subtype.ext ?_⟩
    exact hab

/-- The actual grid embedding commutes with common beta normalization. -/
theorem normalization_gridPosition (D : BetaDiagram (n + 1)) (t : ℕ+)
    (z : D.normalizeBetas.Available) :
    D.dilatedNormalizationPositions t (D.normalizeBetas.gridPosition t z) =
      D.gridPosition t (D.normalizationPositions z) := by
  apply Subtype.ext
  change (t : ℕ) * z.val - (-(t : ℕ) * D.col (Fin.last n)) =
    (t : ℕ) * (z.val - (-D.col (Fin.last n)))
  ring

/-- Normalization transports the inherited full grid coordinates, not only arithmetic ones. -/
theorem normalization_gridLift (D : BetaDiagram (n + 1)) (t : ℕ+)
    (f : D.normalizeBetas.Available → ℚ) :
    D.dilatedNormalizationCoordinates t (D.normalizeBetas.gridLift t f) =
      D.gridLift t (D.normalizationCoordinates f) := by
  classical
  funext w
  by_cases hw : ∃ z, D.gridPosition t z = w
  · obtain ⟨z, rfl⟩ := hw
    let z₀ := D.normalizationPositions.symm z
    have he : (D.dilatedNormalizationPositions t).symm (D.gridPosition t z) =
        D.normalizeBetas.gridPosition t z₀ := by
      apply (D.dilatedNormalizationPositions t).injective
      rw [Equiv.apply_symm_apply, D.normalization_gridPosition]
      simp [z₀]
    change D.normalizeBetas.gridLift t f
        ((D.dilatedNormalizationPositions t).symm (D.gridPosition t z)) =
      D.gridLift t (D.normalizationCoordinates f) (D.gridPosition t z)
    rw [he, gridLift_gridPosition, gridLift_gridPosition]
    rfl
  · have hn : ¬ ∃ z, D.normalizeBetas.gridPosition t z =
        (D.dilatedNormalizationPositions t).symm w := by
      rintro ⟨z, hz⟩
      apply hw
      refine ⟨D.normalizationPositions z, ?_⟩
      rw [← D.normalization_gridPosition, hz, Equiv.apply_symm_apply]
    change D.normalizeBetas.gridLift t f
        ((D.dilatedNormalizationPositions t).symm w) =
      D.gridLift t (D.normalizationCoordinates f) w
    change (if h : ∃ z, D.normalizeBetas.gridPosition t z =
        (D.dilatedNormalizationPositions t).symm w then f (Classical.choose h) else 0) =
      (if h : ∃ z, D.gridPosition t z = w then
        D.normalizationCoordinates f (Classical.choose h) else 0)
    rw [dite_eq_right hn, dite_eq_right hw]

theorem normalization_inheritedKernel_map (D : BetaDiagram (n + 1)) (t : ℕ+) :
    (D.normalizeBetas.inheritedKernel t).map
      (D.dilatedNormalizationCoordinates t).toLinearMap = D.inheritedKernel t := by
  rw [inheritedKernel, inheritedKernel, ← D.normalization_kernel_map,
    ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro f
  change D.dilatedNormalizationCoordinates t (D.normalizeBetas.gridLift t f) =
    D.gridLift t (D.normalizationCoordinates f)
  exact D.normalization_gridLift t f

/-- The arithmetic image for an unnormalized core, transported to its actual coordinates.
Its residues are the relative positions `z - b_last` of that core. -/
def relativeArithmeticOffGrid (D : BetaDiagram (n + 1)) (t : ℕ+) :
    Submodule ℚ ((D.dilate t).Available → ℚ) :=
  (D.normalizeBetas.arithmeticOffGrid t).map
    (D.dilatedNormalizationCoordinates t).toLinearMap

/-- No normalized-coordinate premise is needed for the direct containment in `thm:dilation`. -/
theorem dilation_kernel_containment_general (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hz : D.ZeroFree) :
    D.inheritedKernel t ⊔ D.relativeArithmeticOffGrid t ≤ (D.dilate t).unitKernel ∧
      Disjoint (D.inheritedKernel t) (D.relativeArithmeticOffGrid t) := by
  have h := D.normalizeBetas.dilation_kernel_containment t hn
    D.normalizeBetas_normalized (D.normalizeBetas_zeroFree hz)
  have hle := Submodule.map_mono (f := (D.dilatedNormalizationCoordinates t).toLinearMap) h.1
  have hdis := Submodule.disjoint_map (D.dilatedNormalizationCoordinates t).injective h.2
  simpa only [Submodule.map_sup, D.normalization_inheritedKernel_map,
    D.dilatedNormalization_kernel_map, relativeArithmeticOffGrid] using And.intro hle hdis

/-- The full arbitrary-beta-coordinate form of `thm:dilation`. -/
theorem dilation_kernel_general (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) :
    (D.dilate t).unitKernel = D.inheritedKernel t ⊔ D.relativeArithmeticOffGrid t ∧
      Disjoint (D.inheritedKernel t) (D.relativeArithmeticOffGrid t) := by
  have hnormind : LinearIndependent ℚ
      (fun ij : Fin (n + 1) × Fin (n + 1) => D.normalizeBetas.cofactor ij.1 ij.2) := by
    simpa only [normalizeBetas_cofactor] using hind
  have h := D.normalizeBetas.dilation_kernel t hn (D.normalizeBetas_connected hconn)
    (D.normalizeBetas_zeroFree hz) D.normalizeBetas_normalized hnormind
  have he := congrArg (fun p =>
    p.map (D.dilatedNormalizationCoordinates t).toLinearMap) h.1
  have hd := Submodule.disjoint_map (D.dilatedNormalizationCoordinates t).injective h.2
  simpa only [Submodule.map_sup, D.normalization_inheritedKernel_map,
    D.dilatedNormalization_kernel_map, relativeArithmeticOffGrid] using And.intro he hd

/-- An actual kernel equivalence for arbitrary beta translations of the connected core. -/
def dilationKernelEquivGeneral (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) :
    (D.unitKernel × offGridResidueSpace (t : ℕ)
        D.normalizeBetas.endpointModulus D.normalizeBetas.span) ≃ₗ[ℚ]
      (D.dilate t).unitKernel :=
  (LinearEquiv.prodCongr D.normalizationKernelEquiv.symm (LinearEquiv.refl ℚ _)).trans
    ((D.normalizeBetas.dilationKernelEquiv t hn (D.normalizeBetas_connected hconn)
      (D.normalizeBetas_zeroFree hz) D.normalizeBetas_normalized (by
        simpa only [normalizeBetas_cofactor] using hind)).trans
          (D.dilatedNormalizationKernelEquiv t))

/-- Actual residue restriction for arbitrary beta translations of the base core. -/
def relativeOffGridRestriction (D : BetaDiagram (n + 1)) (t : ℕ+) :
    offGridResidueSpace (t : ℕ) D.normalizeBetas.endpointModulus D.normalizeBetas.span →ₗ[ℚ]
      ((D.dilate t).Available → ℚ) :=
  (D.dilatedNormalizationCoordinates t).toLinearMap.comp
    (D.normalizeBetas.offGridRestriction t)

theorem relativeOffGridRestriction_injective (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) : Function.Injective (D.relativeOffGridRestriction t) :=
  (D.dilatedNormalizationCoordinates t).injective.comp
    (D.normalizeBetas.offGridRestriction_injective t hn D.normalizeBetas_normalized)

theorem relativeOffGridRestriction_range (D : BetaDiagram (n + 1)) (t : ℕ+) :
    (D.relativeOffGridRestriction t).range = D.relativeArithmeticOffGrid t := by
  rw [relativeOffGridRestriction, LinearMap.range_comp, offGridRestriction_range]
  rfl

end BetaDiagram
end SkewCofactorIndependence
