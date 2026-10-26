/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ErosionLowering
import SkewClassInflation.NegativeOneCount
import SkewClassInflation.ZeroIndexCount
import SkewClassInflation.HomogeneousShift
import SkewClassInflation.InflationClasses

/-!
# Exact class transport on zero-free diagrams

Formalizes `lem:zero-free-bijection` in `shields-2026-skew-class-inflation.tex`.
For a connected zero-free diagram that is not a line, erosion and inflation are inverse
bijections between its entire Schur class and the entire Schur class of its erosion, over
every row count, and the bijections commute with rotation.  The inclusion of the general
no-escape theorem is one-sided; the reverse inclusion uses that no member of either class has
a Jacobi--Trudi entry of index \(-1\), so that inflation is the homogeneous shift of
`HomogeneousShift`.  Every connected mate of a zero-free diagram is itself zero-free, because
the number of index zero entries is also a Schur invariant.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

namespace Profile

variable {n : ℕ}

/-- Zero-free: the full beta lists are disjoint, so no board entry has index zero. -/
def ZeroFree (P : Profile n) : Prop := ∀ i j, P.xi i ≠ P.zeta j

/-- A line is a single row or a single column. -/
def IsLine (P : Profile n) : Prop := n = 0 ∨ ∀ i, P.r i = 1

/-- A zero-free diagram that is not a line has at least two rows. -/
theorem pos_of_zeroFree_nonline (P : Profile n) (hz : P.ZeroFree) (hl : ¬ P.IsLine) :
    0 < n := by
  by_contra hn
  exact hl (Or.inl (by omega))

/-- Zero-freeness forces every adjacent overlap to exceed one, and then every row to exceed
one, so that erosion is a connected diagram with no empty row. -/
theorem canDeflate_one_of_zeroFree (P : Profile n) (hz : P.ZeroFree) (hn : 0 < n) :
    CanDeflate 1 P := by
  have hg : ∀ j : Fin n, 1 ≤ P.g j := by
    intro j
    have h1 := P.xi_succ_sub_zeta_castSucc j
    have h2 := hz j.succ j.castSucc
    omega
  refine ⟨fun i => ?_, fun j => hg j⟩
  by_cases hi : i.val < n
  · have h1 := P.g_lt_castSucc ⟨i.val, hi⟩
    have h2 := hg ⟨i.val, hi⟩
    have e : (⟨i.val, hi⟩ : Fin n).castSucc = i := Fin.ext (by simp)
    rw [e] at h1
    omega
  · have hin : i.val = n := by omega
    have hj : n - 1 < n := by omega
    have h1 := P.g_lt_succ ⟨n - 1, hj⟩
    have h2 := hg ⟨n - 1, hj⟩
    have e : (⟨n - 1, hj⟩ : Fin n).succ = i := Fin.ext (by simp; omega)
    rw [e] at h1
    omega

/-- The erosion of a zero-free profile has no board entry of index minus one. -/
theorem negOneCount_deflate_of_zeroFree (P : Profile n) (hz : P.ZeroFree)
    (h : CanDeflate 1 P) : (deflate 1 P h).negOneCount = 0 := by
  rw [negOneCount_eq_zero_iff]
  intro i j hij
  have e := index_inflate 1 (deflate 1 P h) i j
  rw [inflate_deflate] at e
  have := hz i j
  push_cast at e
  omega

/-- On boards without index minus one, one-step inflation is the homogeneous shift
`s_{I T} = h₁^{n+1} s_T(h_j ↦ h_{j+1}/h₁)`. -/
theorem profileSchur_inflate_one_of_negOneCount (T : Profile n) (h : T.negOneCount = 0) :
    algebraMap CompleteRing CompleteField (profileSchur (inflate 1 T)) =
      hOne ^ (n + 1) * shiftDown (profileSchur T) := by
  have hn := (negOneCount_eq_zero_iff T).mp h
  have := det_shift (Matrix.of fun i j : Fin (n + 1) => T.xi i - T.zeta j)
    (fun i j => by simpa using hn i j)
  simp only [Fintype.card_fin] at this
  unfold profileSchur
  have e : (Matrix.of fun i j : Fin (n + 1) =>
      complete ((inflate 1 T).xi i - (inflate 1 T).zeta j)) =
      Matrix.of fun i j : Fin (n + 1) => complete (T.xi i - T.zeta j + 1) := by
    ext i j
    simp only [Matrix.of_apply]
    rw [index_inflate]
    simp
  rw [e]
  exact this

/-- Schur-equal profiles without index minus one stay Schur-equal after one inflation step. -/
theorem profileSchur_inflate_one_eq {P Q : Profile n} (hP : P.negOneCount = 0)
    (hQ : Q.negOneCount = 0) (h : profileSchur P = profileSchur Q) :
    profileSchur (inflate 1 P) = profileSchur (inflate 1 Q) := by
  apply IsFractionRing.injective CompleteRing CompleteField
  rw [profileSchur_inflate_one_of_negOneCount P hP, profileSchur_inflate_one_of_negOneCount Q hQ,
    h]

/-- Zero-freeness is the vanishing of the index zero count. -/
theorem zeroFree_iff_zeroIdxCount (P : Profile n) : P.ZeroFree ↔ P.zeroIdxCount = 0 := by
  rw [zeroIdxCount_eq_zero_iff]
  exact ⟨fun h i j hij => h i j (by omega), fun h i j hij => h i j (by omega)⟩

/-- Every connected mate of a zero-free diagram is zero-free. -/
theorem zeroFree_of_profileSchur_eq {P Q : Profile n} (hz : P.ZeroFree)
    (h : profileSchur Q = profileSchur P) : Q.ZeroFree := by
  rw [zeroFree_iff_zeroIdxCount] at hz ⊢
  rw [zeroIdxCount_eq_of_profileSchur_eq h, hz]

/-- Deflation commutes with global rotation. -/
theorem deflate_rotate (t : ℕ) (P : Profile n) (h : CanDeflate t P) :
    ∃ h' : CanDeflate t P.rotate, (deflate t P h).rotate = deflate t P.rotate h' := by
  have hP : inflate t (deflate t P h).rotate = P.rotate := by
    rw [← inflate_rotate, inflate_deflate]
  have h' : CanDeflate t P.rotate := by
    rw [← hP]
    exact canDeflate_inflate t _
  refine ⟨h', inflate_injective t ?_⟩
  rw [hP, inflate_deflate]

end Profile

/-- **Exact transport on zero-free classes** (`lem:zero-free-bijection`).  For a connected
zero-free diagram that is not a line, inflation is a bijection from the whole Schur class of its
erosion, over all row counts, onto the whole Schur class of the diagram, and erosion is its
inverse on every member.

Every member of the class is zero-free (`Profile.zeroFree_of_profileSchur_eq`).

**Differs from the paper's route.** Surjectivity onto the class of the diagram is the one-sided
no-escape theorem, and zero-freeness of the mates comes from the index zero count being a Schur
invariant, in the same way as the index minus one count, rather than from ordinary-degree
homogeneity. -/
theorem zeroFree_class_transport {n : ℕ} (P : Profile n) (hz : P.ZeroFree) (hl : ¬ P.IsLine) :
    ∃ h : Profile.CanDeflate 1 P,
      Set.BijOn (ConnectedProfile.inflate 1)
        (ConnectedProfile.schurClass ⟨n, Profile.deflate 1 P h⟩)
        (ConnectedProfile.schurClass ⟨n, P⟩) ∧
      ∀ H ∈ ConnectedProfile.schurClass ⟨n, P⟩, ∃ hH : Profile.CanDeflate 1 H.2,
        (⟨H.1, Profile.deflate 1 H.2 hH⟩ : ConnectedProfile) ∈
            ConnectedProfile.schurClass ⟨n, Profile.deflate 1 P h⟩ ∧
          ConnectedProfile.inflate 1 ⟨H.1, Profile.deflate 1 H.2 hH⟩ = H ∧ H.2.ZeroFree := by
  have hn := Profile.pos_of_zeroFree_nonline P hz hl
  have h := Profile.canDeflate_one_of_zeroFree P hz hn
  have hE : Profile.inflate 1 (Profile.deflate 1 P h) = P := Profile.inflate_deflate 1 P h
  have hE0 := Profile.negOneCount_deflate_of_zeroFree P hz h
  have hsub : ConnectedProfile.schurClass ⟨n, P⟩ ⊆
      ConnectedProfile.inflate 1 '' ConnectedProfile.schurClass ⟨n, Profile.deflate 1 P h⟩ := by
    have := ConnectedProfile.inflation_no_escape ⟨n, Profile.deflate 1 P h⟩ 1
    have e : ConnectedProfile.inflate 1 (⟨n, Profile.deflate 1 P h⟩ : ConnectedProfile) =
        ⟨n, P⟩ := by
      simp only [ConnectedProfile.inflate, hE]
    rwa [e] at this
  refine ⟨h, ⟨?_, (ConnectedProfile.inflate_injective 1).injOn, hsub⟩, ?_⟩
  · rintro ⟨m, Q⟩ hQ
    have hQ' : profileSchur Q = profileSchur (Profile.deflate 1 P h) := hQ
    obtain ⟨hmn, -⟩ := profile_invariants Q _ hQ'
    subst hmn
    have hQ0 : Q.negOneCount = 0 := by
      rw [Profile.negOneCount_eq_of_profileSchur_eq hQ', hE0]
    have key := Profile.profileSchur_inflate_one_eq hQ0 hE0 hQ'
    change profileSchur (Profile.inflate 1 Q) = profileSchur P
    rw [key, hE]
  · intro H hH
    obtain ⟨m, Q⟩ := H
    have hH' : profileSchur Q = profileSchur P := hH
    obtain ⟨hmn, -⟩ := profile_invariants Q P hH'
    subst hmn
    have hQ : profileSchur Q = profileSchur (Profile.inflate 1 (Profile.deflate 1 P h)) := by
      rw [hE]; exact hH'
    obtain ⟨R, hR1, hR2⟩ := mate_deflation (Profile.deflate 1 P h) Q 1 hQ
    have hc : Profile.CanDeflate 1 Q := by
      rw [← hR1]; exact Profile.canDeflate_inflate 1 R
    refine ⟨hc, ?_, ?_, Profile.zeroFree_of_profileSchur_eq hz hH'⟩
    · have : Profile.deflate 1 Q hc = R :=
        Profile.inflate_injective 1 (by rw [Profile.inflate_deflate, hR1])
      change profileSchur (Profile.deflate 1 Q hc) = profileSchur (Profile.deflate 1 P h)
      rw [this]; exact hR2
    · simp only [ConnectedProfile.inflate, Profile.inflate_deflate]

end SkewClassInflation
