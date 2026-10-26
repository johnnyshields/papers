/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPureBinaryProfiles
import SkewCornerDescent.Matrix.OriginalInternalLowCoreAgreement
import SkewCornerDescent.Matrix.OriginalInternalPhaseChoice
import SkewCornerDescent.CyclicPhaseFiberPeriod

/-!
# Produced pure phase discrepancy and its resolving binary data

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
A genuine constant-response, constant-height phase either has no shifted
incoming discrepancy or supplies its least discrepancy. Actual proper-core
jets push that degree above the core span. Coprimality identifies all
earlier coefficients, and complete inverse recurrences then supply the
nonconstant binary data and its strict resolving lower-field support.
The phase and core-jet suppliers remain explicit inputs. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The first visible discrepancy, resolving generator, nonzero amplitude,
and nonconstant bits are all produced from the actual phase profiles. -/
theorem originalPure_phase_binary_alternative {n b : ℕ} [NeZero b]
    (P : Profile n) (k : ℕ)
    (hK : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ k)
    (idx : ZMod b → Fin (originalSelectedCount (hD := hD) P - 1))
    (d : ℕ) (hcop : Nat.Coprime d b) (K : ℤ)
    (hheight : ∀ i, originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P (idx i)) (originalInternalStateIndex P (idx i)) = K)
    (hresponse : ∀ i, c.originalInternalResidue P (idx i) = c.originalInternalResidue P (idx 0))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hleft : ∀ i l, l < (c.top : ℕ) →
      (c.originalSelectedCoreLeft P ⟨(idx i).val, by have := (idx i).isLt; omega⟩).coeff l =
      (c.originalSelectedCoreLeft P ⟨(idx 0).val, by have := (idx 0).isLt; omega⟩).coeff l)
    (hright : ∀ i l, l < (c.top : ℕ) →
      (c.originalSelectedCoreRight P ⟨(idx i).val + 1, by have := (idx i).isLt; omega⟩).coeff l =
      (c.originalSelectedCoreRight P ⟨(idx 0).val + 1, by have := (idx 0).isLt; omega⟩).coeff l) :
    (∀ i, (c.originalInternalEndpointProfiles P (idx i)).1 =
      (c.originalInternalEndpointProfiles P (idx (i + (d : ZMod b)))).1) ∨
    ∃ w : ℕ, (c.top : ℕ) < w ∧ 2 * (w : ℤ) < K ∧
      (∀ i l, l < w → ((c.originalInternalEndpointProfiles P (idx i)).1).coeff l =
        ((c.originalInternalEndpointProfiles P (idx 0)).1).coeff l) ∧
      ∃ H : ℕ+, c.top < H ∧ w < (H : ℕ) ∧
        (H : ℤ) = 2*K - (c.top : ℤ) - 2*(w : ℤ) ∧
        ∃ η : OtherField c.top, η ≠ 0 ∧ η ∈ residueLowerField c.top H ∧
          ∃ bits : ZMod b → Bool, bits 0 = false ∧ (∃ i j, bits i ≠ bits j) ∧
            ∀ i, ((c.originalInternalEndpointProfiles P (idx i)).1).coeff w -
              ((c.originalInternalEndpointProfiles P (idx 0)).1).coeff w =
                if bits i then η else 0 := by
  classical
  obtain ⟨choice, hchoice⟩ :=
    c.originalInternal_phase_discrepancy_choice P idx d K hheight hresponse hmax
  cases choice with
  | none => exact Or.inl hchoice
  | some w =>
    obtain ⟨hw, hhalf, hbefore, i, hdiff⟩ := hchoice
    let A := fun i => (c.originalInternalEndpointProfiles P (idx i)).1
    have hlow (i : ZMod b) (l : ℕ) (hl : l ≤ (c.top : ℕ)) :
        (A i).coeff l = (A 0).coeff l :=
      c.originalInternal_incoming_low_coeff_eq_of_core_jets P (idx i) (idx 0)
        (hleft i) (hright i) l hl
    have hN : (c.top : ℕ) < w := by
      by_contra hn
      have he := (hlow i w (by omega)).trans (hlow (i+(d : ZMod b)) w (by omega)).symm
      exact hdiff (sub_eq_zero.mpr he)
    have hprefix (i : ZMod b) (l : ℕ) (hl : l < w) : (A i).coeff l = (A 0).coeff l := by
      let f := fun i : ZMod b => (A i).coeff l
      have hp : Function.Periodic f (d : ZMod b) := fun j => (hbefore j l hl).symm
      have hg := zmod_periodic_gcd f hp
      rw [hcop.gcd_eq_one, Nat.cast_one] at hg
      have he := hg.nsmul i.val 0
      simpa only [zero_add, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] using he
    have hne : ∃ j, (A j).coeff w ≠ (A 0).coeff w := by
      by_cases hi : (A i).coeff w = (A 0).coeff w
      · refine ⟨i+(d : ZMod b), ?_⟩
        intro hj
        exact hdiff (sub_eq_zero.mpr (hi.trans hj.symm))
      · exact ⟨i, hi⟩
    have hNInt : (c.top : ℤ) < (w : ℤ) := by exact_mod_cast hN
    let H : ℕ+ := ⟨(2*K-(c.top : ℤ)-2*(w : ℤ)).toNat, by omega⟩
    have hHe : (H : ℤ) = 2*K-(c.top : ℤ)-2*(w : ℤ) := by
      exact Int.toNat_of_nonneg (by omega)
    have hNH : c.top < H := by change (c.top : ℕ) < (H : ℕ); omega
    have hwH : w < (H : ℕ) := by omega
    obtain ⟨η, hη, hmem, bits, hbase, hnonconstant, hbits⟩ :=
      c.originalPure_binary_first_differences P k hK idx 0 w hN
        (fun i => by rw [hheight]; exact hhalf) H hwH hprefix hne
    exact Or.inr ⟨w, hN, hhalf, hprefix, H, hNH, hwH, hHe,
      η, hη, hmem, bits, hbase, hnonconstant, hbits⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
