/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.MainTheorems
import SkewRibbonCoarsenings.LocalAlternativeProof
import SkewRibbonCoarsenings.RibbonExpansion
import SkewRibbonCoarsenings.Recovery

/-!
# The inclusion `ℰ((m) ∘ β) ⊆ {(m) ∘ γ : γ ∈ ℰ(β)}`

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, sections `sec:introduction` and `sec:recognition`
(`eq:old-inclusion`, `cor:class`).

`oldInclusion` proves the inclusion `eq:old-inclusion` from the local alternative
(`prop:local-alternative`, proved in `LocalAlternativeProof`) and composition congruence
(`eq:congruence`), without the cited theorem; `cor_class_unconditional` is `cor:class` with no
hypothesis beyond `m ≥ 1`, `n ≥ 1` and the cut set.

The proof is a strong induction on the weight `N = m n`.  For `η ∼ β^{⊙ m}` the local alternative
gives `η = β^{⊙ m}`, `η = (β^{⊙ m})*`, or a proper literal common inner factor `E` of weight `p`
after orientation.  If `p ∤ n`, the outer factor of `β^{⊙ m}` over `E` is trivial
(`outer_eq_empty_of_not_dvd`), so the second composition equals the first.  If `p ∣ n`, then `β`
itself has the literal inner factor `E`, the outer factor of `β^{⊙ m}` is the near power of that
of `β`, the induction hypothesis applies to the outer pair of weight `N / p`, and `eq:congruence`
reassembles the inner factor.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

/-! ### Membership in a near power -/

/-- A point lies in the near power `β^{⊙ m}` of a weight-`n` composition exactly when it is below
`m n` and its residue mod `n` is a cut of `β`. -/
lemma mem_nearPowerCuts_iff {n : ℕ} {S : Finset ℕ} {m x : ℕ} (hn : 0 < n) (hS : IsCutSet n S) :
    x ∈ nearPowerCuts n S m ↔ x < m * n ∧ x % n ∈ S := by
  rw [mem_nearPowerCuts]
  constructor
  · rintro ⟨j, hj, e, he, rfl⟩
    have he' := Finset.mem_Ioo.mp (hS he)
    have h1 : (j * n + e) % n = e := by
      rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt he'.2
    refine ⟨?_, by rwa [h1]⟩
    calc j * n + e < j * n + n := by omega
      _ = (j + 1) * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right _ hj
  · rintro ⟨hx, hxS⟩
    exact ⟨x / n, (Nat.div_lt_iff_lt_mul hn).mpr hx, x % n, hxS, Nat.div_add_mod' x n⟩

/-- Below the first period, a near power agrees with the composition. -/
lemma mem_nearPowerCuts_of_lt {n : ℕ} {S : Finset ℕ} {m x : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hS : IsCutSet n S) (hx : x < n) : x ∈ nearPowerCuts n S m ↔ x ∈ S := by
  rw [mem_nearPowerCuts_iff hn hS, Nat.mod_eq_of_lt hx]
  exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le hx (Nat.le_mul_of_pos_left n hm), h⟩⟩

/-! ### A literal inner factor of a near power -/

/-- Let a near power `β^{⊙ m}` (weight `m n`) have a literal inner factor `E` of weight `p`
(`β^{⊙ m} = compCuts M A p E`).  Off the `p`-grid, membership of a residue in `S` (mod `n`) and in
`E` (mod `p`) agree. -/
lemma mod_mem_iff_of_nearPower {m n p M : ℕ} {S A E : Finset ℕ} (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p) (hS : IsCutSet n S) (hE : IsCutSet p E) (hMp : m * n = M * p)
    (hP : nearPowerCuts n S m = compCuts M A p E) {x : ℕ} (hx : ¬ p ∣ x) :
    x % n ∈ S ↔ x % p ∈ E := by
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have hpN : p ∣ m * n := ⟨M, by rw [hMp, mul_comm]⟩
  have hnN : n ∣ m * n := dvd_mul_left n m
  have hlt : x % (m * n) < m * n := Nat.mod_lt _ hmn
  have hx'p : ¬ p ∣ x % (m * n) := fun h => hx ((Nat.dvd_mod_iff hpN).mp h)
  have e1 : x % (m * n) % n = x % n := Nat.mod_mod_of_dvd x hnN
  have e2 : x % (m * n) % p = x % p := Nat.mod_mod_of_dvd x hpN
  have h1 : x % (m * n) ∈ nearPowerCuts n S m ↔ x % (m * n) % n ∈ S := by
    rw [mem_nearPowerCuts_iff hn hS]; exact ⟨fun h => h.2, fun h => ⟨hlt, h⟩⟩
  have h2 : x % (m * n) ∈ compCuts M A p E ↔ x % (m * n) % p ∈ E :=
    mem_compCuts_of_not_dvd hp hE hx'p (by rw [← hMp]; exact hlt)
  rw [← e1, ← e2, ← h1, ← h2, hP]

/-- A near power `β^{⊙ m}` with a literal inner factor of weight `p ∤ n` (and `p ∣ m n`) has
trivial outer factor: the outer cut set is empty.  An outer cut `p j` of `β^{⊙ m}` is a cut, so
`p j + n` is a cut off the `p`-grid; its residue mod `p` is that of `n`, so `n` is a cut off the
`p`-grid, but `n` is a multiple of `n`, which no near power cuts. -/
lemma outer_eq_empty_of_not_dvd {m n p M : ℕ} {S A E : Finset ℕ} (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p) (hS : IsCutSet n S) (hE : IsCutSet p E)
    (hMp : m * n = M * p) (hP : nearPowerCuts n S m = compCuts M A p E) (hpn : ¬ p ∣ n) :
    A = ∅ := by
  have L : ∀ x : ℕ, ¬ p ∣ x → (x % n ∈ S ↔ x % p ∈ E) :=
    fun x hx => mod_mem_iff_of_nearPower hm hn hp hS hE hMp hP hx
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have hy : p * j ∈ nearPowerCuts n S m := by
    rw [hP]; exact (mem_compCuts_of_dvd hp hE j).mpr hj
  have hy' : (p * j) % n ∈ S := ((mem_nearPowerCuts_iff hn hS).mp hy).2
  have hz1 : ¬ p ∣ p * j + n := fun h => hpn ((Nat.dvd_add_right (dvd_mul_right p j)).mp h)
  have hz2 : (p * j + n) % n ∈ S := by rwa [Nat.add_mod_right]
  have hz3 : (p * j + n) % p ∈ E := (L _ hz1).mp hz2
  rw [Nat.mul_add_mod] at hz3
  have h4 := (L n hpn).mpr hz3
  rw [Nat.mod_self] at h4
  exact absurd (Finset.mem_Ioo.mp (hS h4)).1 (lt_irrefl 0)

/-- The only composition with the coarsening polynomial of the one-part composition is itself. -/
lemma eq_empty_of_G_eq_empty {M : ℕ} (hM : 1 ≤ M) {A : Finset ℕ} (hA : IsCutSet M A)
    (h : G M A = G M ∅) : A = ∅ := by
  have hE : IsCutSet M (∅ : Finset ℕ) := Finset.empty_subset _
  have h1 := mult_eq_of_G_eq (n := M) (by omega) hA hE h (lam := gaps M A) (gaps_pos (by omega) hA)
  have h2 := mult_self_pos (n := M) (S := A)
  rw [h1] at h2
  unfold mult at h2
  obtain ⟨T, hT⟩ := Finset.card_pos.mp h2
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_empty] at hT
  obtain ⟨rfl, hg⟩ := hT
  have h3 := card_gaps hA
  rw [← hg, gaps_empty, Multiset.card_singleton] at h3
  exact Finset.card_eq_zero.mp (by omega)

/-! ### The class of a near power -/

/-- Every composition `η` with the coarsening polynomial of the near power `β^{⊙ m}` is the near
power `γ^{⊙ m}` of a composition `γ` with `G_γ = G_β`: the inclusion `eq:old-inclusion` at the level
of cut sets, by strong induction on the weight `N = m n`.  Conditional on `hLA`
(`prop:local-alternative`, proved as `localAlternativeOmega`). -/
theorem nearPower_class_aux (hLA : LocalAlternativeOmega) :
    ∀ N : ℕ, ∀ m n : ℕ, m * n = N → 1 ≤ m → 1 ≤ n → ∀ S : Finset ℕ, IsCutSet n S →
      ∀ η : Finset ℕ, IsCutSet N η → G N η = G N (nearPowerCuts n S m) →
        ∃ T, IsCutSet n T ∧ G n T = G n S ∧ η = nearPowerCuts n T m := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro m n hN hm hn S hS η hη hG
  subst hN
  have hm0 : 0 < m := hm
  have hn0 : 0 < n := hn
  have hN0 : 0 < m * n := Nat.mul_pos hm0 hn0
  have hP : IsCutSet (m * n) (nearPowerCuts n S m) := nearPowerCuts_isCutSet hS m
  -- the orientation cases
  have hrevcase : η = revCuts (m * n) (nearPowerCuts n S m) →
      ∃ T, IsCutSet n T ∧ G n T = G n S ∧ η = nearPowerCuts n T m := fun h =>
    ⟨revCuts n S, revCuts_isCutSet hS, G_revCuts n S hS, by rw [h, revCuts_nearPowerCuts hS m]⟩
  rcases hLA (m * n) (nearPowerCuts n S m) η hP hη with
    h | h | ⟨p, d, A, A', E, η'', hp3, hpd, hpdle, hdN, hdltN, hA, hA', hE, hPeq, hor, hη''eq, -⟩ |
      ⟨lam, hc⟩
  · exact ⟨S, hS, rfl, h⟩
  · exact hrevcase h
  · have hpN : p ∣ m * n := hpd.trans hdN
    have hpltN : p < m * n := by omega
    have hηeq : η = compCuts (m * n / p) A' p E ∨
        revCuts (m * n) η = compCuts (m * n / p) A' p E := by
      rcases hor with h | h
      · exact Or.inl (h ▸ hη''eq)
      · exact Or.inr (h ▸ hη''eq)
    have hp0 : 0 < p := by omega
    obtain ⟨M, hM⟩ := hpN
    have hMdiv : m * n / p = M := by rw [hM, Nat.mul_div_cancel_left _ hp0]
    rw [hMdiv] at hA hA' hPeq hηeq
    have hMp : m * n = M * p := by rw [hM, mul_comm]
    have hM1 : 1 ≤ M := by
      rcases Nat.eq_zero_or_pos M with rfl | h
      · omega
      · exact h
    have hG'' : G (m * n) (compCuts M A' p E) = G (m * n) (nearPowerCuts n S m) := by
      rcases hηeq with h | h
      · rw [← h]; exact hG
      · rw [← h, G_revCuts _ _ hη]; exact hG
    have hEq : G M A = G M A' := by
      refine (two_factor_cancel_forward (by omega : 0 < M) hp0 hA hA' hE hE ?_).1
      unfold Equivalent
      rw [← hMp, ← hPeq]
      exact hG''.symm
    by_cases hpn : p ∣ n
    · -- `p ∣ n`: the inner factor lives already in `β`, and the outer pair has smaller weight
      obtain ⟨k, hk⟩ : ∃ k, n = k * p := by
        obtain ⟨k, hk⟩ := hpn
        exact ⟨k, by rw [hk, mul_comm]⟩
      subst hk
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hn0
        · exact h
      have hMk : M = m * k := by
        have : p * M = p * (m * k) := by
          rw [← hM]; ring
        exact Nat.eq_of_mul_eq_mul_left hp0 this
      subst hMk
      have hpN' : p ∣ m * (k * p) := ⟨m * k, by ring⟩
      have hper : OffGridPeriodic (m * (k * p)) (nearPowerCuts (k * p) S m) p :=
        (literal_factor_iff hp0 hpN' hP).mp ⟨A, E, by rw [hMdiv]; exact hA, hE,
          by rw [hMdiv]; exact hPeq⟩
      have hperS : OffGridPeriodic (k * p) S p := by
        intro x hx hxd
        have hxn : x < k * p := by omega
        rw [← mem_nearPowerCuts_of_lt (m := m) hm0 hn0 hS hxn,
          ← mem_nearPowerCuts_of_lt (m := m) hm0 hn0 hS hx]
        exact hper x (by
          calc x + p < k * p := hx
            _ ≤ m * (k * p) := Nat.le_mul_of_pos_left _ hm0) hxd
      obtain ⟨AS, ES, hAS, hES, hSeq⟩ := (literal_factor_iff hp0 (dvd_mul_left p k) hS).mpr hperS
      rw [Nat.mul_div_cancel k hp0] at hAS hSeq
      have hP2 : nearPowerCuts (k * p) S m =
          compCuts (m * k) (nearPowerCuts k AS m) p ES := by
        rw [hSeq]; exact nearPowerCuts_compCuts k AS p ES m
      have hk0 : 0 < k := hk1
      have u1 := literal_factor_unique hp0 (Nat.mul_pos hm0 hk0) hA hE hPeq
      have u2 := literal_factor_unique hp0 (Nat.mul_pos hm0 hk0)
        (nearPowerCuts_isCutSet hAS m) hES hP2
      have hEE : E = ES := u1.1.trans u2.1.symm
      have hAeq : A = nearPowerCuts k AS m := u1.2.trans u2.2.symm
      rw [hAeq] at hEq
      have hlt : m * k < m * (k * p) := by
        have h3 : m * (k * p) = m * k * p := by ring
        have := Nat.mul_pos hm0 hk0
        nlinarith
      obtain ⟨T', hT', hGT', hA'eq⟩ := ih (m * k) hlt m k rfl hm hk1 AS hAS A' hA' hEq.symm
      have hγ : IsCutSet (k * p) (compCuts k T' p ES) := compCuts_isCutSet hp0 hT' hES
      have hGγ : G (k * p) (compCuts k T' p ES) = G (k * p) S := by
        rw [hSeq]
        exact congruence hLA hk1 (by omega) hT' hAS hES hES hGT' rfl
      have hηγ : compCuts (m * k) A' p E = nearPowerCuts (k * p) (compCuts k T' p ES) m := by
        rw [hA'eq, hEE]; exact (nearPowerCuts_compCuts k T' p ES m).symm
      rcases hηeq with h | h
      · exact ⟨_, hγ, hGγ, h.trans hηγ⟩
      · refine ⟨revCuts (k * p) (compCuts k T' p ES), revCuts_isCutSet hγ,
          by rw [G_revCuts _ _ hγ]; exact hGγ, ?_⟩
        rw [← revCuts_nearPowerCuts hγ m, ← hηγ, ← h, revCuts_revCuts hη]
    · -- `p ∤ n`: the outer factor is trivial, so the two compositions coincide up to orientation
      have hAe : A = ∅ := outer_eq_empty_of_not_dvd hm0 hn0 hp0 hS hE hMp hPeq hpn
      subst hAe
      have hA'e : A' = ∅ := eq_empty_of_G_eq_empty hM1 hA' hEq.symm
      subst hA'e
      rcases hηeq with h | h
      · exact ⟨S, hS, rfl, h.trans hPeq.symm⟩
      · refine hrevcase ?_
        rw [← revCuts_revCuts hη, h.trans hPeq.symm]
  · exfalso
    obtain ⟨hpos, _, _, hdiff, _⟩ := hc
    rw [mult_eq_of_G_eq hN0 hP hη hG.symm hpos] at hdiff
    simp at hdiff

/-! ### `eq:old-inclusion` and `cor:class` -/

/-- `eq:old-inclusion`: `ℰ((m) ∘ β) ⊆ {(m) ∘ γ : γ ∈ ℰ(β)}` for every `m ≥ 1` and every
composition `β` of weight `n ≥ 1`, derived from the local alternative and `eq:congruence` rather
than cited from Billera–Thomas–van Willigenburg.

For `η ∼ β^{⊙ m}` the local alternative at weight `m n` gives `η = β^{⊙ m}`, `η = (β^{⊙ m})*`, or a
proper literal common inner factor of weight `p`; a factor with `p ∤ n` forces a trivial outer
factor, and a factor with `p ∣ n` is a literal inner factor of `β` and reduces, through the
induction hypothesis on weight `m n / p`, to the same statement for the outer pair. -/
theorem oldInclusion {m n : ℕ} {S : Finset ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hS : IsCutSet n S) :
    OldInclusion m n S := by
  rintro η ⟨hη, hG⟩
  rw [compCuts_empty] at hG
  obtain ⟨T, hT, hGT, rfl⟩ :=
    nearPower_class_aux localAlternativeOmega (m * n) m n rfl hm hn S hS η hη hG
  exact ⟨T, ⟨hT, hGT⟩, (compCuts_empty m n T).symm⟩

/-- `cor:class`, unconditionally: for every `m ≥ 1`, `ℰ((m) ∘ β) = {(m) ∘ γ : γ ∈ ℰ(β)}`.  The
inclusion `⊇` is `eq:REV` and the inclusion `⊆` is `eq:old-inclusion` (`oldInclusion`); the local
alternative `prop:local-alternative` is discharged by `localAlternativeOmega`. -/
theorem cor_class_unconditional {m n : ℕ} {S : Finset ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hS : IsCutSet n S) :
    invClass (m * n) (compCuts m ∅ n S) = {η | ∃ γ ∈ invClass n S, η = compCuts m ∅ n γ} :=
  cor_class localAlternativeOmega hm hn hS (oldInclusion hm hn hS)

end SkewRibbonCoarsenings
