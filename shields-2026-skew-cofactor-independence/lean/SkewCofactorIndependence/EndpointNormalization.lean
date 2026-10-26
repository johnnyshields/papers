/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.QuadraticReturns
import SkewCofactorIndependence.WordPeriods

/-!
# Endpoint normalization

The finite-word-to-residue implication in `lem:endpoint-normalization` uses
connectedness, zero-freeness, and order at least two, but not density.
-/

noncomputable section
namespace SkewCofactorIndependence
open scoped BigOperators

/-- Iterated finite-word gcd, with a positive seed that controls every period sum. -/
theorem OneBasedWordPeriod.gcd_finset {α ι : Type*} {w : ℕ → α} {L d : ℕ}
    (hd : OneBasedWordPeriod w L d) (hd0 : 0 < d)
    (s : Finset ι) (p : ι → ℕ)
    (hp : ∀ i ∈ s, OneBasedWordPeriod w L (p i))
    (hL : ∀ i ∈ s, d + p i ≤ L) :
    OneBasedWordPeriod w L (Nat.gcd d (s.gcd p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hd
  | @insert i s hi ih =>
    have hs := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      (fun j hj => hL j (Finset.mem_insert_of_mem hj))
    have hg0 : 0 < Nat.gcd d (s.gcd p) := Nat.gcd_pos_of_pos_left _ hd0
    have hgd : Nat.gcd d (s.gcd p) ≤ d :=
      Nat.le_of_dvd hd0 (Nat.gcd_dvd_left _ _)
    have hpi := hp i (Finset.mem_insert_self i s)
    have hbound := hL i (Finset.mem_insert_self i s)
    rw [Finset.gcd_insert, gcd_eq_nat_gcd,
      Nat.gcd_comm (p i) (s.gcd p), ← Nat.gcd_assoc]
    by_cases hzero : p i = 0
    · simpa [hzero] using hs
    · exact hs.gcd hpi hg0 (Nat.pos_of_ne_zero hzero) (by omega)

/-- Reduction of every index in a finite periodic word to its one-based residue. -/
theorem oneBasedWordPeriod_reduce {α : Type*} {w : ℕ → α} {L g : ℕ}
    (hp : OneBasedWordPeriod w L g) (hg : 0 < g) :
    ∀ z, 1 ≤ z → z ≤ L → w z = w ((z - 1) % g + 1) := by
  intro z
  induction z using Nat.strong_induction_on with
  | h z ih =>
    intro hz hL
    by_cases hzg : z ≤ g
    · have hmod : (z - 1) % g = z - 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmod, Nat.sub_add_cancel hz]
    · have hz' : 1 ≤ z - g := by omega
      have hL' : z - g ≤ L := by omega
      have he := hp (z - g) hz' (by omega)
      have hi := ih (z - g) (by omega) hz' hL'
      have hm : (z - g - 1) % g = (z - 1) % g := by
        have hs : z - 1 = (z - g - 1) + g := by omega
        rw [hs, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
      have he' : w (z - g) = w z := by simpa [Nat.sub_add_cancel (by omega : g ≤ z)] using he
      exact he'.symm.trans (hi.trans (congrArg w (by omega)))

/-- A periodic finite word genuinely factors through the finite residue group. -/
theorem oneBasedWordPeriod_residue {α : Type*} {w : ℕ → α} {L g : ℕ}
    (hp : OneBasedWordPeriod w L g) (hg : 0 < g) :
    ∃ φ : ZMod g → α, ∀ z, 1 ≤ z → z ≤ L → w z = φ (z : ZMod g) := by
  let : NeZero g := ⟨by omega⟩
  let φ : ZMod g → α := fun r => w ((r - 1).val + 1)
  refine ⟨φ, ?_⟩
  intro z hz hL
  have hc : (z : ZMod g) - 1 = ((z - 1 : ℕ) : ZMod g) := by
    rw [← Nat.cast_one, ← Nat.cast_sub hz]
  simpa only [φ, hc, ZMod.val_natCast] using oneBasedWordPeriod_reduce hp hg z hz hL

namespace BetaDiagram
variable {n : ℕ}

/-- Vanishing is imposed on the actual edge quadratics, including the empty edges. -/
def allEdgeReturnsZero (D : BetaDiagram (n + 1)) (c : ℤ → ℚ) : Prop :=
  ∀ i j, returnQuadratic c (D.col j) (D.row i) = 0

/-- The full interval gives the finite word its odd reflection. -/
theorem allEdgeReturnsZero.outer_odd {D : BetaDiagram (n + 1)} {c : ℤ → ℚ}
    (hc : D.allEdgeReturnsZero c) (hD : D.Normalized) :
    ∀ z, 0 < z → z < D.row 0 → c z + c (D.row 0 - z) = 0 := by
  have hz : D.col (Fin.last n) = 0 := hD (by omega)
  have he := (returnQuadratic_eq_zero_iff c (D.col (Fin.last n)) (D.row 0)).1
    (hc 0 (Fin.last n))
  simpa [hz] using he

/-- Comparing the exterior reflection with a row edge gives its row-deficit period. -/
theorem allEdgeReturnsZero.row_period {D : BetaDiagram (n + 1)} {c : ℤ → ℚ}
    (hc : D.allEdgeReturnsZero c) (hD : D.Normalized) (i : Fin (n + 1)) :
    OneBasedWordPeriod (fun z => c (z : ℤ)) (D.span - 1)
      (D.endpointPeriod (Sum.inl i)) := by
  have hb := D.normalized_bounds hD
  have hN := D.span_intCast hD
  have hlast : D.col (Fin.last n) = 0 := hD (by omega)
  have hp : ((D.endpointPeriod (Sum.inl i) : ℕ) : ℤ) = D.row 0 - D.row i := by
    exact Int.natAbs_of_nonneg (sub_nonneg.mpr (hb.1 i).2)
  intro z hz hzL
  have hlocal := (returnQuadratic_eq_zero_iff c _ _).1 (hc i (Fin.last n))
    (z : ℤ) (by rw [hlast]; omega) (by omega)
  have houter := hc.outer_odd hD (D.row i - z) (by omega) (by omega)
  simp only [hlast, add_zero] at hlocal
  have he : D.row 0 - (D.row i - z) = (z + D.endpointPeriod (Sum.inl i) : ℕ) := by
    push_cast
    omega
  rw [he] at houter
  linarith

/-- Comparing the exterior reflection with a column edge gives its column period. -/
theorem allEdgeReturnsZero.col_period {D : BetaDiagram (n + 1)} {c : ℤ → ℚ}
    (hc : D.allEdgeReturnsZero c) (hD : D.Normalized) (j : Fin (n + 1)) :
    OneBasedWordPeriod (fun z => c (z : ℤ)) (D.span - 1)
      (D.endpointPeriod (Sum.inr j)) := by
  have hb := D.normalized_bounds hD
  have hN := D.span_intCast hD
  have hp : ((D.endpointPeriod (Sum.inr j) : ℕ) : ℤ) = D.col j :=
    Int.natAbs_of_nonneg (hb.2 j).1
  intro z hz hzL
  have houter := hc.outer_odd hD (z : ℤ) (by omega) (by omega)
  have hlocal := (returnQuadratic_eq_zero_iff c _ _).1 (hc 0 j)
    (D.row 0 - z) (by omega) (by omega)
  have he : D.row 0 + D.col j - (D.row 0 - z) =
      (z + D.endpointPeriod (Sum.inr j) : ℕ) := by push_cast; omega
  rw [he] at hlocal
  linarith

/-- All edge reflections produce the exact endpoint gcd as a finite word period. -/
theorem allEdgeReturnsZero.gcd_period {D : BetaDiagram (n + 1)} {c : ℤ → ℚ}
    (hc : D.allEdgeReturnsZero c) (hn : 1 ≤ n) (hconn : D.Connected)
    (hz : D.ZeroFree) (hD : D.Normalized) :
    OneBasedWordPeriod (fun z => c (z : ℤ)) (D.span - 1) D.endpointModulus := by
  classical
  let u := D.endpointPeriod (Sum.inl ⟨1, by omega⟩)
  let v := D.endpointPeriod (Sum.inr ⟨n - 1, by omega⟩)
  have hb := D.exterior_periods hn hconn hz hD
  change 0 < u ∧ 0 < v ∧ u + v ≤ D.span - 1 ∧
    (∀ j, u + D.endpointPeriod (Sum.inr j) ≤ D.span - 1) ∧
    (∀ i, v + D.endpointPeriod (Sum.inl i) ≤ D.span - 1) at hb
  have hu := hc.row_period hD ⟨1, by omega⟩
  have hv := hc.col_period hD ⟨n - 1, by omega⟩
  have hd := hu.gcd hv hb.1 hb.2.1 hb.2.2.1
  change OneBasedWordPeriod (fun z => c (z : ℤ)) (D.span - 1) (Nat.gcd u v) at hd
  have hd0 : 0 < Nat.gcd u v := Nat.gcd_pos_of_pos_left _ hb.1
  have hdu : Nat.gcd u v ≤ u := Nat.le_of_dvd hb.1 (Nat.gcd_dvd_left _ _)
  have hdv : Nat.gcd u v ≤ v := Nat.le_of_dvd hb.2.1 (Nat.gcd_dvd_right _ _)
  have hg := hd.gcd_finset hd0 Finset.univ D.endpointPeriod
    (fun i _ => by cases i with
      | inl i => exact hc.row_period hD i
      | inr j => exact hc.col_period hD j)
    (fun i _ => by cases i with
      | inl i =>
        have h := hb.2.2.2.2 i
        omega
      | inr j =>
        have h := hb.2.2.2.1 j
        omega)
  have hdiv : D.endpointModulus ∣ Nat.gcd u v :=
    Nat.dvd_gcd (D.endpointModulus_dvd (Sum.inl ⟨1, by omega⟩))
      (D.endpointModulus_dvd (Sum.inr ⟨n - 1, by omega⟩))
  have he : Nat.gcd (Nat.gcd u v) D.endpointModulus = D.endpointModulus :=
    Nat.gcd_eq_right_iff_dvd.mpr hdiv
  change OneBasedWordPeriod (fun z => c (z : ℤ)) (D.span - 1)
    (Nat.gcd (Nat.gcd u v) D.endpointModulus) at hg
  rw [he] at hg
  exact hg

/-- All row betas reduce to the top row beta and all column betas reduce to zero. -/
theorem endpoint_residues (D : BetaDiagram (n + 1)) (i j : Fin (n + 1)) :
    (D.row i : ZMod D.endpointModulus) = (D.row 0 : ZMod D.endpointModulus) ∧
      (D.col j : ZMod D.endpointModulus) = 0 := by
  constructor
  · apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
    apply Int.natCast_dvd.mpr
    exact D.endpointModulus_dvd (Sum.inl i)
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
    apply Int.natCast_dvd.mpr
    exact D.endpointModulus_dvd (Sum.inr j)

/-- A true odd residue function kills each actual positive-edge quadratic. -/
theorem residue_allEdgeReturnsZero (D : BetaDiagram (n + 1)) (hD : D.Normalized)
    (φ : oddResidueSpace D.endpointModulus D.span) :
    D.allEdgeReturnsZero (fun z => (φ : ZMod D.endpointModulus → ℚ)
      (z : ZMod D.endpointModulus)) := by
  intro i j
  apply (returnQuadratic_eq_zero_iff _ _ _).2
  intro z hb ha
  have hr := D.endpoint_residues i j
  have h := φ.property.1 (z : ZMod D.endpointModulus)
  have hN := D.span_intCast hD
  simpa only [residueReflection, Int.cast_add, Int.cast_sub, hr.1, hr.2,
    add_zero, ← hN, Int.cast_natCast] using h

/-- The complete finite word factors through an odd function of the exact endpoint modulus. -/
theorem endpoint_normalization_word (D : BetaDiagram (n + 1))
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized)
    (c : ℤ → ℚ) (hc : D.allEdgeReturnsZero c) :
    ∃ φ : oddResidueSpace D.endpointModulus D.span,
      ∀ z, 0 < z → z < D.row 0 → c z =
        (φ : ZMod D.endpointModulus → ℚ) (z : ZMod D.endpointModulus) := by
  let : NeZero D.endpointModulus := ⟨ne_of_gt (D.endpointModulus_pos hn)⟩
  obtain ⟨φ, hφ⟩ := oneBasedWordPeriod_residue
    (hc.gcd_period hn hconn hz hD) (D.endpointModulus_pos hn)
  have hN := D.span_intCast hD
  have hgN := D.endpointModulus_lt_span hn hD
  have hrep (r : ZMod D.endpointModulus) :
      ∃ z : ℕ, 1 ≤ z ∧ z < D.span ∧ (z : ZMod D.endpointModulus) = r := by
    by_cases hr : r.val = 0
    · refine ⟨D.endpointModulus, D.endpointModulus_pos hn, hgN, ?_⟩
      have he : r = 0 := by apply (ZMod.val_injective _); simpa using hr
      simp [he]
    · refine ⟨r.val, by omega, lt_of_lt_of_le (ZMod.val_lt r) (by omega), ?_⟩
      exact ZMod.natCast_zmod_val r
  have hodd : φ ∈ oddResidueSpace D.endpointModulus D.span := by
    apply (mem_oddResidueSpace_iff _ _ _).2
    intro r
    obtain ⟨z, hz₁, hz₂, hzr⟩ := hrep r
    have ho := hc.outer_odd hD (z : ℤ) (by omega) (by omega)
    have h₁ := hφ z hz₁ (by omega)
    have h₂ := hφ (D.span - z) (by omega) (by omega)
    have he : ((D.span - z : ℕ) : ℤ) = D.row 0 - z := by omega
    rw [he] at h₂
    rw [h₁, h₂] at ho
    have hcast : ((D.span - z : ℕ) : ZMod D.endpointModulus) =
        (D.span : ZMod D.endpointModulus) - (z : ZMod D.endpointModulus) :=
      Nat.cast_sub (by omega)
    simpa only [← hzr, Int.cast_natCast, hcast] using ho
  refine ⟨⟨φ, hodd⟩, ?_⟩
  intro z hz₁ hz₂
  have he : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz₁.le
  have hcast : (z.toNat : ZMod D.endpointModulus) = (z : ZMod D.endpointModulus) := by
    rw [← Int.cast_natCast, he]
  calc
    c z = c (z.toNat : ℤ) := congrArg c he.symm
    _ = φ (z.toNat : ZMod D.endpointModulus) := hφ z.toNat (by omega) (by omega)
    _ = φ (z : ZMod D.endpointModulus) := congrArg φ hcast

/-- Restriction of an actual residue function to the actual available positions. -/
def residueRestriction (D : BetaDiagram (n + 1)) (q : ℕ) :
    (ZMod q → ℚ) →ₗ[ℚ] (D.Available → ℚ) where
  toFun φ z := φ (z.val : ZMod q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `lem:endpoint-normalization`, with the manuscript's existential endpoint extension. -/
theorem endpoint_normalization (D : BetaDiagram (n + 1)) (hn : 1 ≤ n)
    (hconn : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized)
    (weights : D.Available → ℚ) :
    (∃ c : ℤ → ℚ, (∀ z : D.Available, c z.val = weights z) ∧ D.allEdgeReturnsZero c) ↔
      ∃ φ : oddResidueSpace D.endpointModulus D.span,
        D.residueRestriction D.endpointModulus (φ : ZMod D.endpointModulus → ℚ) = weights := by
  constructor
  · rintro ⟨c, hres, hc⟩
    obtain ⟨φ, hφ⟩ := D.endpoint_normalization_word hn hconn hz hD c hc
    refine ⟨φ, ?_⟩
    funext z
    have hp := (D.mem_availablePositions z.val).1 z.property
    have hlast : D.col (Fin.last n) = 0 := hD (by omega)
    exact (hφ z.val (by simpa [hlast] using hp.1) hp.2.1).symm.trans (hres z)
  · rintro ⟨φ, hφ⟩
    refine ⟨fun z => (φ : ZMod D.endpointModulus → ℚ) (z : ZMod D.endpointModulus), ?_,
      D.residue_allEdgeReturnsZero hD φ⟩
    intro z
    exact congrFun hφ z

end BetaDiagram
end SkewCofactorIndependence
