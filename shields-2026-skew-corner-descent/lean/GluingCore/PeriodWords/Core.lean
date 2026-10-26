-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/PeriodWords/Core.lean
import GluingCore.PeriodWords.Cycle

/-!
# Gcd classes of a two-period system

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-periods`).

For two periods `s, ℓ` with `s ∤ ℓ`, an equivalence relation `J` containing the period edges
relates any two positions of `1, …, L` in the same class modulo `gcd s ℓ`, apart from positions at
which both periods are exceptional, as soon as (a) the edge out of every contracted vertex of the
smaller period is present except for at most one, and (b) every position of the exceptional
`s`-class has an `ℓ`-edge to another class.  The three cases of `lem:gluing-periods` verify (a)
and (b); see `GluingCore.PeriodWords`.

Sorry-free.
-/

namespace GluingCore
namespace PeriodWords

section Core

variable {J : ℤ → ℤ → Prop}

/-- A position with an `ℓ`-edge to a class of non-exceptional `s`-residue is related to a position
of such a class. -/
theorem exists_nonhole_related (hJ : Equivalence J) {L s ℓ : ℕ} {Ss T : Finset ℤ}
    (hnd : ¬ s ∣ ℓ) (hSs : ∀ a ∈ Ss, ∀ b ∈ Ss, a = b)
    (heT : ∀ x y, periodEdge L ℓ T x y → J x y)
    (hatt : ∀ z ∈ Finset.Icc (1 : ℤ) L, z % (s : ℤ) ∈ Ss → z % (ℓ : ℤ) ∉ T →
      z ∈ Finset.Icc (1 : ℤ) ((L : ℤ) - ℓ) ∨ 1 + (ℓ : ℤ) ≤ z)
    {z : ℤ} (hz : z ∈ Finset.Icc (1 : ℤ) L) (hz' : ¬ (z % (s : ℤ) ∈ Ss ∧ z % (ℓ : ℤ) ∈ T)) :
    ∃ z' ∈ Finset.Icc (1 : ℤ) L, z' % (s : ℤ) ∉ Ss ∧ J z z' ∧ (ℓ : ℤ) ∣ z' - z := by
  by_cases h : z % (s : ℤ) ∈ Ss
  · have hzT : z % (ℓ : ℤ) ∉ T := fun h' => hz' ⟨h, h'⟩
    rcases hatt z hz h hzT with h1 | h1
    · refine ⟨z + ℓ, ?_, ?_, heT z _ ⟨h1, hzT, rfl⟩, ⟨1, by ring⟩⟩
      · simp only [Finset.mem_Icc] at h1 ⊢; omega
      · intro h'
        have := hSs _ h' _ h
        exact hnd (Int.natCast_dvd_natCast.1 (by simpa using dvd_sub_of_emod_eq this))
    · refine ⟨z - ℓ, ?_, ?_, hJ.symm (heT (z - ℓ) z ⟨?_, ?_, by ring⟩), ⟨-1, by ring⟩⟩
      · simp only [Finset.mem_Icc] at hz ⊢; omega
      · intro h'
        have := hSs _ h' _ h
        exact hnd (Int.natCast_dvd_natCast.1 (by simpa using dvd_sub_of_emod_eq this))
      · simp only [Finset.mem_Icc] at hz ⊢; omega
      · rw [emod_eq_of_dvd_sub (n := (ℓ : ℤ)) (a := z - ℓ) (b := z) ⟨-1, by ring⟩]
        exact hzT
  · exact ⟨z, hz, h, hJ.refl z, by simp⟩

/-- Some number of translations by `ℓ` carries the contracted residue of `x` to that of `y`, when
their difference is a multiple of the gcd. -/
theorem exists_cycle_index {s ℓ g k l : ℕ} (hs : s = g * k) (hl : ℓ = g * l)
    (hcop : Nat.Coprime k l) {x y : ℤ} (hxy : (g : ℤ) ∣ y - x) :
    ∃ n : ℤ, cycRep s ℓ x n = cycRep s ℓ y 0 := by
  obtain ⟨d, hd⟩ := hxy
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop.symm
  have hsZ : (s : ℤ) = g * k := by exact_mod_cast hs
  have hlZ : (ℓ : ℤ) = g * l := by exact_mod_cast hl
  refine ⟨a * d, ?_⟩
  unfold cycRep
  congr 1
  apply emod_eq_of_dvd_sub
  refine ⟨-(d * b), ?_⟩
  rw [hsZ]
  have hy : y = x + g * d := by linarith
  have h1 : (a : ℤ) * l = 1 - b * k := by linarith
  have : x - 1 + a * d * ℓ - (y - 1 + 0 * ℓ) = g * d * (a * l - 1) := by
    rw [hlZ, hy]; ring
  rw [this, h1]
  ring

/-- **Gcd classes.**  Let `J` be an equivalence relation on positions containing the edges of the
period `s` except at the residues `Ss` and of the period `ℓ` except at the residues `T`, with
`s ∤ ℓ`.  Assume that at most one contracted vertex of `1, …, s` has no outgoing edge, and that
every position of the exceptional `s`-class which is not exceptional for `ℓ` has an `ℓ`-edge in
range.  Then any two positions of `1, …, L` in the same class modulo `gcd s ℓ`, neither exceptional
for both periods, are related.

**Differs from the paper's route.** The paper argues separately in each case of
`lem:gluing-periods`; here one argument on the gcd cycles, with hypotheses verified per case, covers
all of them. -/
theorem related_of_gcd_dvd (hJ : Equivalence J) {L s ℓ : ℕ} {Ss T : Finset ℤ}
    (hs : 0 < s) (hnd : ¬ s ∣ ℓ) (hsL : s ≤ L) (hSs : ∀ a ∈ Ss, ∀ b ∈ Ss, a = b)
    (heS : ∀ x y, periodEdge L s Ss x y → J x y) (heT : ∀ x y, periodEdge L ℓ T x y → J x y)
    (hmiss : ∀ y ∈ Finset.Icc (1 : ℤ) s, ∀ y' ∈ Finset.Icc (1 : ℤ) s,
      Missing L s ℓ Ss T y → Missing L s ℓ Ss T y' → y = y')
    (hatt : ∀ z ∈ Finset.Icc (1 : ℤ) L, z % (s : ℤ) ∈ Ss → z % (ℓ : ℤ) ∉ T →
      z ∈ Finset.Icc (1 : ℤ) ((L : ℤ) - ℓ) ∨ 1 + (ℓ : ℤ) ≤ z)
    {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd s ℓ : ℕ) : ℤ) ∣ y - x)
    (hx' : ¬ (x % (s : ℤ) ∈ Ss ∧ x % (ℓ : ℤ) ∈ T))
    (hy' : ¬ (y % (s : ℤ) ∈ Ss ∧ y % (ℓ : ℤ) ∈ T)) : J x y := by
  obtain ⟨k, l, hcop, hk, hl⟩ := Nat.exists_coprime s ℓ
  set g := Nat.gcd s ℓ with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hs
  have hs' : s = g * k := by rw [mul_comm]; exact hk
  have hl' : ℓ = g * l := by rw [mul_comm]; exact hl
  have hk2 : 2 ≤ k := by
    have hk0 : k ≠ 0 := by rintro rfl; simp at hs'; omega
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hnd (by rw [hs']; simpa using Nat.gcd_dvd_right s ℓ)
    omega
  have hgℓ : (g : ℤ) ∣ ℓ := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right s ℓ)
  have hgs : (g : ℤ) ∣ s := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left s ℓ)
  obtain ⟨x', hx'm, hx'S, hJx, hxd⟩ := exists_nonhole_related hJ hnd hSs heT hatt hx hx'
  obtain ⟨y', hy'm, hy'S, hJy, hyd⟩ := exists_nonhole_related hJ hnd hSs heT hatt hy hy'
  have hrep : ∀ z : ℤ, z ∈ Finset.Icc (1 : ℤ) L → z % (s : ℤ) ∉ Ss →
      J z (cycRep s ℓ z 0) ∧ cycRep s ℓ z 0 % (s : ℤ) ∉ Ss := by
    intro z hz hzS
    have hd : (s : ℤ) ∣ cycRep s ℓ z 0 - z := by
      refine ⟨-((z - 1) / s), ?_⟩
      unfold cycRep
      simp only [zero_mul, add_zero]
      rw [Int.emod_def]
      ring
    have hmem := cycRep_mem hs ℓ z 0
    have hmemL : cycRep s ℓ z 0 ∈ Finset.Icc (1 : ℤ) L := by
      simp only [Finset.mem_Icc] at hmem ⊢; omega
    refine ⟨related_of_dvd hJ hs heS hz hmemL hd hzS, ?_⟩
    rw [emod_eq_of_dvd_sub hd]
    exact hzS
  obtain ⟨hJ1, hS1⟩ := hrep x' hx'm hx'S
  obtain ⟨hJ2, hS2⟩ := hrep y' hy'm hy'S
  have hdiff : (g : ℤ) ∣ y' - x' := by
    have : y' - x' = (y' - y) + (y - x) + (x - x') := by ring
    rw [this]
    exact dvd_add (dvd_add (dvd_trans hgℓ hyd) hxy)
      (dvd_trans hgℓ (by simpa using dvd_neg.2 hxd))
  obtain ⟨n, hn⟩ := exists_cycle_index hs' hl' hcop hdiff
  have hcyc := cycle_rel hJ hs' hl' hg hk2 hcop hsL heS heT hmiss x' 0 n hS1 (by rw [hn]; exact hS2)
  rw [hn] at hcyc
  exact hJ.trans hJx (hJ.trans hJ1 (hJ.trans hcyc (hJ.trans (hJ.symm hJ2) (hJ.symm hJy))))

end Core

end PeriodWords
end GluingCore
