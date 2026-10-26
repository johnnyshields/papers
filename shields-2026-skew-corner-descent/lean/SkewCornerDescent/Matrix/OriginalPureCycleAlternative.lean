/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPurePhaseAlternative
import SkewCornerDescent.Matrix.OriginalPureCyclicFirst
import SkewCornerDescent.Matrix.OriginalConstantAmalgamationData
import SkewCornerDescent.Matrix.OriginalConstantClosureData
import SkewCornerDescent.Matrix.OriginalComparisonProfilePrefix
import SkewCornerDescent.Matrix.OriginalOrdinaryClosureCofactor
import SkewCornerDescent.Matrix.OriginalProfileWordPeriods

/-!
# Actual pure comparison cycles: identical connectors or nonzero first charge

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
Whole source data supply both comparison diagrams, their complete profiles,
actual cyclic periods, and every onsite height and residue. The pure ordinary
cofactor supplies the binary first discrepancy. The full shared prefix then
supplies the same amplitude to the shorter actual cycle. No binary alphabet,
profile matching, pair gradient or first charge is an assumption. Source
constant data and the actual pinned center are supplied by the primitive
ordinary-pin construction. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

set_option maxHeartbeats 1600000 in
-- The assembly identifies both entire dependent inverse-profile words and their real cycles.
/-- Actual pure corner geometry produces either unchanged shifted incoming
profiles on the ordinary cycle or a nonzero complete first-normal cyclic charge.

**Differs from the paper's route.** The first actual prefix state is the
binary baseline. Coprimality and even transition counts use the nonconstant
completed word directly, without prescribing the closure endpoint bit or
splitting into constant shorter-word cases. -/
theorem originalPure_constant_cycle_alternative {n m an on : ℕ}
    (P : Profile n) (W : Profile m) (A : Profile an) (O : Profile on)
    (q : ℤ) (v u z zO : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hO : originalHorizontalClosure P = translate zO O.cells ∨
      originalVerticalClosure P = translate zO O.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (b a : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hcop : Nat.Coprime b a)
    [NeZero b] [NeZero (b - a)] [NeZero (originalSelectedCount (hD := hD) P)]
    (hKP : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ) (fun j => W.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ a)
    (S : OtherField c.top) (K : ℕ)
    (hS : ∀ i, c.originalInternalResidue P i = S)
    (hgap : ∀ i, c.originalCompletedGap P i = (K : ℤ) - (c.top : ℤ))
    (hcore : ∀ i : Fin (originalSelectedCount (hD := hD) P),
      c.originalSelectedCoreLeft P i = c.originalSelectedCoreLeft P 0 ∧
        c.originalSelectedCoreRight P i = c.originalSelectedCoreRight P 0)
    (hcenter : c.originalInternalResidue O
      ⟨originalSelectedCount (hD := hD) P - 1, by
        rw [originalOrdinaryClosure_selected_count P O zO hO]
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ = S) :
    ∃ hTA : b-a ≤ originalSelectedCount (hD := hD) A - 1 - 1,
    ∃ hTO : b ≤ originalSelectedCount (hD := hD) O - 1 - 1,
      (∀ z : ZMod b, (c.originalInternalEndpointCycle O (by omega) z).1 =
        (c.originalInternalEndpointCycle O (by omega) (z + ((b-a : ℕ) : ZMod b))).1) ∨
      b • normalCyclicFirstCharge
        (normalDiagonalCycle ((c.originalInternalResponseMatrix A).map c.normalSeries)
          (show b-a ≤ originalSelectedCount (hD := hD) A - 1 by omega))
        (normalAdjacentCycle ((c.originalInternalResponseMatrix A).map c.normalSeries) hTA)
        c.normalCoefficient⁻¹ -
      (b-a) • normalCyclicFirstCharge
        (normalDiagonalCycle ((c.originalInternalResponseMatrix O).map c.normalSeries)
          (show b ≤ originalSelectedCount (hD := hD) O - 1 by omega))
        (normalAdjacentCycle ((c.originalInternalResponseMatrix O).map c.normalSeries) hTO)
        c.normalCoefficient⁻¹ ≠ 0 := by
  classical
  have hcountP : originalSelectedCount (hD := hD) P = b := by
    rw [originalSelectedCount_eq_primeOrder, hKP,
      primeOrder_pow (irreducible_cellSchur hD).prime,
      primeOrder_self (irreducible_cellSchur hD).prime, mul_one]
  have hcountW : originalSelectedCount (hD := hD) W = a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime,
      primeOrder_self (irreducible_cellSchur hD).prime, mul_one]
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hC : 0 < originalSelectedCount (hD := hD) W := by rw [hcountW]; exact ha
  obtain ⟨hcA, hinv, hdataA, hcoreA⟩ := c.originalAmalgamation_constant_internal_data
    P W A q v u z hq hv hwindow hW hA hcutq hcutLq hC S K hS hgap hcore
  obtain ⟨hdataO, hcoreO⟩ := c.originalClosure_constant_internal_data
    P O zO hO S K hS hgap hcore hcenter
  have hcountA : originalSelectedCount (hD := hD) A = b+(b-a) := by omega
  have hcountO := originalOrdinaryClosure_selected_count (hD := hD) P O zO hO
  have hTA : b-a ≤ originalSelectedCount (hD := hD) A - 1 - 1 := by omega
  have hTO : b ≤ originalSelectedCount (hD := hD) O - 1 - 1 := by omega
  let hlenA : b-a ≤ originalSelectedCount (hD := hD) A - 1 := by omega
  let hlenO : b ≤ originalSelectedCount (hD := hD) O - 1 := by omega
  let idxO := originalInternalCycleIndex O hlenO
  have hKO : (jtMatrix (fun j : Fin on => O.xi j.succ) (fun j => O.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ (2*b) := by
    rw [originalOrdinaryClosure_complementary_square P O zO hO, hKP, ← pow_mul]
    congr 1
    omega
  have hmaxO := c.originalPure_component_span O (2*b) hKO
  have hleft (i : ZMod b) (l : ℕ) (_ : l < (c.top : ℕ)) :
      (c.originalSelectedCoreLeft O ⟨(idxO i).val, by have := (idxO i).isLt; omega⟩).coeff l =
      (c.originalSelectedCoreLeft O ⟨(idxO 0).val, by have := (idxO 0).isLt; omega⟩).coeff l :=
    congrArg (fun p : Polynomial (OtherField c.top) => p.coeff l)
      ((hcoreO _).1.trans (hcoreO _).1.symm)
  have hright (i : ZMod b) (l : ℕ) (_ : l < (c.top : ℕ)) :
      (c.originalSelectedCoreRight O ⟨(idxO i).val+1, by have := (idxO i).isLt; omega⟩).coeff l =
      (c.originalSelectedCoreRight O ⟨(idxO 0).val+1, by have := (idxO 0).isLt; omega⟩).coeff l :=
    congrArg (fun p : Polynomial (OtherField c.top) => p.coeff l)
      ((hcoreO _).2.trans (hcoreO _).2.symm)
  have hcopShift : Nat.Coprime (b-a) b := (Nat.coprime_self_sub_left (by omega)).mpr hcop.symm
  have halt := c.originalPure_phase_binary_alternative O (2*b) hKO idxO (b-a) hcopShift K
    (fun i => (hdataO (idxO i)).2)
    (fun i => (hdataO (idxO i)).1.trans (hdataO (idxO 0)).1.symm) hmaxO hleft hright
  refine ⟨hTA, hTO, ?_⟩
  rcases halt with hnone | ⟨w, hN, hhalf, hprefix, H, hH, hwH, hresolve,
      η, hη, hηlower, bitsO, hbits0, hnonconstant, hbitsO⟩
  · exact Or.inl hnone
  · obtain ⟨_, _, hshared⟩ := c.originalComparison_shared_profile_prefix
      P A O q v u zO hq hv hwindow hA hO hcutq hcutLq
    have hpref (z : ZMod (b-a)) : c.originalInternalEndpointCycle A hlenA z =
        c.originalInternalEndpointCycle O hlenO (z.val : ZMod b) := by
      have hz := ZMod.val_lt z
      have hzb : z.val < b := by omega
      have he := hshared ⟨z.val, by omega⟩
      simpa only [originalInternalEndpointCycle, finiteWordCycle, ZMod.val_natCast,
        Nat.mod_eq_of_lt hzb] using he
    have hpref0 : c.originalInternalEndpointCycle A hlenA 0 =
        c.originalInternalEndpointCycle O hlenO 0 := by
      simpa only [ZMod.val_zero, Nat.cast_zero] using hpref 0
    have hp (z : ZMod b) (l : ℕ) (hl : l < w) :
        (c.originalInternalEndpointCycle O hlenO z).1.coeff l =
        (c.originalInternalEndpointCycle O hlenO 0).1.coeff l := hprefix z l hl
    have hmatchA (z : ZMod (b-a)) (l : ℕ) (hl : l < w) :
        (c.originalInternalEndpointCycle A hlenA z).1.coeff l =
        (c.originalInternalEndpointCycle A hlenA (z+1)).1.coeff l := by
      rw [hpref, hpref]
      exact (hp _ l hl).trans (hp _ l hl).symm
    let bitsA := fun z : ZMod (b-a) => bitsO (z.val : ZMod b)
    have hbitsA (z : ZMod (b-a)) :
        (c.originalInternalEndpointCycle A hlenA z).1.coeff w -
          (c.originalInternalEndpointCycle A hlenA 0).1.coeff w =
            if bitsA z then η else 0 := by
      rw [hpref, hpref0]
      exact hbitsO (z.val : ZMod b)
    have hperiodA := (c.originalAmalgamation_profile_word_period P A q v u hq hv hwindow hA
      (fun x hx => privateDiagonal_avoids_interior hcutq hx)
      (fun x hx => privateDiagonal_avoids_interior hcutLq hx)).2
    change ∀ i j, j.val = i.val + (originalSelectedCount (hD := hD) A -
      originalSelectedCount (hD := hD) P) →
        c.originalInternalEndpointProfiles A i = c.originalInternalEndpointProfiles A j at hperiodA
    have hshift : originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P =
        b-a := by omega
    rw [hshift] at hperiodA
    have hperiodO := (c.originalClosure_profile_word_period P O zO hO).2
    change ∀ i j, j.val = i.val + originalSelectedCount (hD := hD) P →
      c.originalInternalEndpointProfiles O i = c.originalInternalEndpointProfiles O j at hperiodO
    rw [hcountP] at hperiodO
    have hS0 : S ≠ 0 := by
      have hn := c.originalHessenberg_residue_ne_zero P hB (c.originalPure_component_span P b hKP)
        (originalInternalStateIndex P ⟨0, by omega⟩)
      exact fun hz => hn ((hS _).trans hz)
    have hnonzero := c.originalInternal_pure_cyclic_first_nonzero A O hcopShift.symm hTA hTO
      S hS0 K w hN (by exact_mod_cast hhalf) H hH hresolve
      (fun i => (hdataA i).1) (fun i => (hdataO i).1)
      (fun i => (hdataA i).2) (fun i => (hdataO i).2)
      (fun i j hij => congrArg Prod.snd (hperiodA i j hij))
      (fun i j hij => congrArg Prod.snd (hperiodO i j hij))
      ((hcoreA ⟨1, by omega⟩).2.trans (hcoreA ⟨0, by omega⟩).2.symm)
      hmatchA (fun z l hl => (hp z l hl).trans (hp (z+1) l hl).symm)
      η hη bitsA bitsO hbitsA hbitsO hnonconstant
    exact Or.inr hnonzero.2

end SkewCornerDescent.Matrix.SelectedCoordinate
