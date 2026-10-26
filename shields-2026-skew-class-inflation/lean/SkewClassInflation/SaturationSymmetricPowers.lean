/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationOverlapWords
import SkewClassInflation.SymmetricRibbonReconstruction

/-!
# Complete power classes for genuinely symmetric inners

The symmetric-inner case of `lem:merged-block-rigidity` of
`shields-2026-skew-class-inflation.tex`.  The source's actual one-copy
deflated word is assumed symmetric, as a property of the given inner.
All mate geometry, higher-word symmetry, and reconstruction inputs
are produced.  No factor-classification hypothesis is used.
Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- Actual one-copy symmetry produces every higher deflated power's literal palindrome. -/
theorem power_deflated_palindrome_of_base
    (hbase : (List.ofFn (fun i => (A.power 1 (by decide)).r i - A.c)).reverse =
      List.ofFn (fun i => (A.power 1 (by decide)).r i - A.c)) (m : ℕ) :
    (List.ofFn (fun i => (A.power (m + 1) (by omega)).r i - A.c)).reverse =
      List.ofFn (fun i => (A.power (m + 1) (by omega)).r i - A.c) := by
  rw [A.power_deflated_word]
  apply A.overlapWord.composition_palindrome_of_base
  rw [← A.power_deflated_word 0]
  exact hbase

/-- Every arbitrary connected power mate equals the actual symmetric source, even at one copy. -/
theorem power_mate_eq_of_symmetric_inner
    (hbase : (List.ofFn (fun i => (A.power 1 (by decide)).r i - A.c)).reverse =
      List.ofFn (fun i => (A.power 1 (by decide)).r i - A.c))
    (m : ℕ) (hm : 0 < m) {n : ℕ} (Q : Profile n)
    (he : Q.toBetaDiagram.schur = (A.power m hm).toBetaDiagram.schur) :
    (⟨n, Q⟩ : ConnectedProfile) = ⟨m * A.k, A.power m hm⟩ := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  obtain ⟨hn, _, hgQ, hrQ⟩ := A.power_mate_reduction (a + 1) hm Q he
  subst n
  have hQ : ∀ i, A.c < Q.r i := fun i => A.c_lt_d.trans (hrQ i)
  have hw := ribbon_eq_reconstruct_of_reverse_word
    (fun i => (A.power (a + 1) hm).r i - A.c) (fun i => Q.r i - A.c)
    (fun i => Nat.sub_pos_of_lt (A.powerRows_above_gap (a + 1) i))
    (fun i => Nat.sub_pos_of_lt (hQ i))
    (A.power_deflated_palindrome_of_base hbase a)
    (A.power_mate_ribbon (a + 1) hm Q he).symm
  have hv := congrArg (List.map (fun x : ℕ => x + A.c)) hw
  rw [List.map_ofFn, List.map_ofFn] at hv
  change List.ofFn (fun i => (A.power (a + 1) hm).r i - A.c + A.c) =
    List.ofFn (fun i => Q.r i - A.c + A.c) at hv
  have hp : (fun i => (A.power (a + 1) hm).r i - A.c + A.c) = (A.power (a + 1) hm).r :=
    funext (fun i => Nat.sub_add_cancel (A.powerRows_above_gap (a + 1) i).le)
  have hq : (fun i => Q.r i - A.c + A.c) = Q.r :=
    funext (fun i => Nat.sub_add_cancel (hQ i).le)
  rw [hp, hq] at hv
  congr 1
  apply Gluing.Profile.ext
  · exact (List.ofFn_injective hv).symm
  · funext j
    exact hgQ j

/-- The unrestricted connected Schur class of each symmetric power is a literal singleton. -/
theorem power_full_class_of_symmetric_inner
    (hbase : (List.ofFn (fun i => (A.power 1 (by decide)).r i - A.c)).reverse =
      List.ofFn (fun i => (A.power 1 (by decide)).r i - A.c))
    (m : ℕ) (hm : 0 < m) :
    (ConnectedProfile.schurClass (⟨m * A.k, A.power m hm⟩ : ConnectedProfile)) =
      {⟨m * A.k, A.power m hm⟩} := by
  ext H
  constructor
  · intro hH
    rcases H with ⟨n, Q⟩
    have he : Q.toBetaDiagram.schur = (A.power m hm).toBetaDiagram.schur := by
      change profileSchur Q = profileSchur (A.power m hm) at hH
      simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hH
    exact Set.mem_singleton_iff.mpr (A.power_mate_eq_of_symmetric_inner hbase m hm Q he)
  · intro hH
    rw [Set.mem_singleton_iff] at hH
    subst H
    rfl

/-- A palindrome in the original inner rows supplies the exact deflated one-copy symmetry. -/
theorem power_one_deflated_palindrome
    (hpal : (List.ofFn A.r).reverse = List.ofFn A.r) :
    (List.ofFn (fun i => (A.power 1 (by decide)).r i - A.c)).reverse =
      List.ofFn (fun i => (A.power 1 (by decide)).r i - A.c) := by
  rw [A.power_one_deflated_word]
  have hh := congrArg (List.map (fun x : ℕ => x - A.c)) hpal
  rw [List.map_reverse] at hh
  simpa only [List.map_ofFn, Function.comp_def] using hh

/-- Every actual positive power of an original palindromic inner has its full singleton class.

**Differs from the paper's route.** Reconstructs the symmetric source from exact
two-part coarsening multiplicities, without a factor-classification input. -/
theorem power_full_class_of_palindromic_inner
    (hpal : (List.ofFn A.r).reverse = List.ofFn A.r) (m : ℕ) (hm : 0 < m) :
    (ConnectedProfile.schurClass (⟨m * A.k, A.power m hm⟩ : ConnectedProfile)) =
      {⟨m * A.k, A.power m hm⟩} :=
  A.power_full_class_of_symmetric_inner (A.power_one_deflated_palindrome hpal) m hm

end SkewClassInflation.SaturationInner
