import SkewGluing.MixedFold.Outer

/-!
# The words of the composite equal those of the parent

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`: "the composition is literally the parent", via `eq:gluing-interface` and
`eq:gluing-mixed-inverse`).

`MixFoldFold.eq_words` is the word-level comparison: a pair of words `(A', B')` with the period
structure and caps of a case-(d) composite of period `g` (`A'` periodic outside the classes `α`,
`β`, `B'` periodic, the first block equal to the parent's, the caps and the interface read off the
outer)
agrees with the parent's words `(A, B)` on `1, …, N - 1`.

Sorry-free.
-/

namespace SkewGluing

open PeriodWords

theorem mixFold_periodExcept_mul {f : ℤ → ℤ} {L p : ℕ} {S : Finset ℤ}
    (hf : PeriodExcept L p S f) (k : ℕ) :
    ∀ x : ℤ, 1 ≤ x → x + k * p ≤ L → x % (p : ℤ) ∉ S → f x = f (x + k * p) := by
  induction k with
  | zero => intro x _ _ _; simp
  | succ k ih =>
    intro x h1 h2 h3
    have e : x + ((k + 1 : ℕ) : ℤ) * p = (x + k * p) + p := by push_cast; ring
    have hm : (x + (k : ℤ) * p) % (p : ℤ) = x % (p : ℤ) := by
      rw [Int.add_emod, Int.mul_emod_left, add_zero, Int.emod_emod_of_dvd _ dvd_rfl]
    rw [e] at h2 ⊢
    rw [ih x h1 (by nlinarith) h3]
    exact hf (x + k * p) (by
      rw [Finset.mem_Icc]; constructor
      · nlinarith [Nat.zero_le (k * p)]
      · omega) (by rw [hm]; exact h3)

/-- A position of an exceptional class: its value is read from the first block, the interface, or
the last block. -/
theorem mixFold_slot_eq {A A' : ℤ → ℤ} {N g M v : ℕ} {ρ : ℤ} (hg : 0 < g) (hvg : v < g)
    (hNz : (N : ℤ) = (M : ℤ) * g + v) (hρ0 : 0 ≤ ρ) (_hρv : ρ ≤ v)
    (h0 : 1 ≤ ρ → A' ρ = A ρ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < M → A' ((j : ℤ) * g + ρ) = A ((j : ℤ) * g + ρ))
    (hend : ρ < v → A' ((M : ℤ) * g + ρ) = A ((M : ℤ) * g + ρ)) {x : ℤ} (hx1 : 1 ≤ x)
    (hx2 : x ≤ (N : ℤ) - 1) (hxρ : x % (g : ℤ) = ρ) : A' x = A x := by
  have hgz : (0 : ℤ) < g := by exact_mod_cast hg
  have hxd : x = (x / (g : ℤ)) * g + ρ := by
    have := Int.emod_def x (g : ℤ); linarith
  have hj0 : 0 ≤ x / (g : ℤ) := Int.ediv_nonneg (by omega) hgz.le
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hj0
  rw [hj] at hxd
  have hjM : j ≤ M := by
    by_contra hcon
    have : (M : ℤ) + 1 ≤ j := by exact_mod_cast (by omega : M + 1 ≤ j)
    nlinarith
  rw [hxd]
  by_cases hj1 : j = 0
  · subst hj1
    have : x = ρ := by simpa using hxd
    have h1 : 1 ≤ ρ := by omega
    simpa using h0 h1
  · by_cases hjm : j < M
    · exact hmid j (by omega) hjm
    · have hjeq : j = M := by omega
      subst hjeq
      have hρ : ρ < v := by nlinarith
      exact hend hρ

namespace MixFoldFold

variable {A B : ℤ → ℤ} {N g M v : ℕ} {α β : ℤ}

/-- **The words of the composite are the words of the parent.** -/
theorem eq_words (hF : MixFoldFold A B N g M v α β) {A' B' : ℤ → ℤ}
    (hA' : PeriodExcept (N - 1) g {α, β} A') (hB' : PeriodExcept (N - 1) g ∅ B')
    (hfirst : ∀ k : ℤ, 1 ≤ k → k ≤ (g : ℤ) - 1 → A' k = A k ∧ B' k = B k)
    (hcα : 1 ≤ α → A' α = 1) (hcβ : A' β = 1)
    (htα : A' ((N : ℤ) - v + α) = 0) (htβ : β < v → A' ((N : ℤ) - v + β) = 0)
    (hBg : B' g = 0) (hAg : 1 ≤ α → A' g = 1)
    (hint : ∀ j : ℕ, 1 ≤ j → j < M →
      A' ((j : ℤ) * g + α) = A ((j : ℤ) * g + α) ∧ A' ((j : ℤ) * g + β) = A ((j : ℤ) * g + β)) :
    ∀ x : ℤ, 1 ≤ x → x ≤ (N : ℤ) - 1 → A' x = A x ∧ B' x = B x := by
  have hg : 0 < g := by have := hF.hv0; have := hF.hvg; omega
  have hgz : (0 : ℤ) < g := by exact_mod_cast hg
  have hM := hF.hM
  have hNN := hF.hN
  have hvg := hF.hvg
  have hv0 := hF.hv0
  have hαβ := hF.hαβ
  have hβv := hF.hβv
  have hα0 := hF.hα
  have hNz : (N : ℤ) = (M : ℤ) * g + v := by exact_mod_cast hNN
  intro x hx1 hx2
  have hclass : ∀ y : ℤ, 1 ≤ y → y ≤ (N : ℤ) - 1 → y % (g : ℤ) ≠ α → y % (g : ℤ) ≠ β →
      A' y = A y := by
    intro y hy1 hy2 hyα hyβ
    have h0 := Int.emod_nonneg (y - 1) hgz.ne'
    have h1 := Int.emod_lt_of_pos (y - 1) hgz
    have hk0 : 0 ≤ (y - 1) / (g : ℤ) := Int.ediv_nonneg (by omega) hgz.le
    have hdecomp : y = ((y - 1) % (g : ℤ) + 1) + ((y - 1) / (g : ℤ)).toNat * g := by
      have := Int.emod_def (y - 1) (g : ℤ)
      rw [Int.toNat_of_nonneg hk0]; linarith
    have hrg : (((y - 1) % (g : ℤ) + 1) % (g : ℤ)) = y % (g : ℤ) := by
      conv_rhs => rw [hdecomp]
      rw [Int.add_mul_emod_self_right]
    have e1 := mixFold_periodExcept_mul hA' ((y - 1) / (g : ℤ)).toNat ((y - 1) % (g : ℤ) + 1)
      (by omega) (by rw [← hdecomp]; omega) (by
        rw [hrg]; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    have e2 := hF.perA_iter ((y - 1) / (g : ℤ)).toNat ((y - 1) % (g : ℤ) + 1) (by omega)
      (by rw [← hdecomp]; omega) (by rw [hrg]; exact hyα) (by rw [hrg]; exact hyβ)
    rw [← hdecomp] at e1 e2
    rw [← e1, ← e2]
    by_cases hrt : (y - 1) % (g : ℤ) + 1 ≤ (g : ℤ) - 1
    · exact (hfirst _ (by omega) hrt).1
    · have hrg' : (y - 1) % (g : ℤ) + 1 = g := by omega
      have hα1 : 1 ≤ α := by
        by_contra hcon
        have : α = 0 := by omega
        apply hyα
        rw [← hrg, hrg', Int.emod_self, this]
      rw [hrg']
      rw [hAg hα1]
      have := hF.perA_iter (M - 1) g (by omega) (by
        have hM1 : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
        rw [hM1]; nlinarith) (by rw [Int.emod_self]; omega) (by rw [Int.emod_self]; omega)
      have e3 : (g : ℤ) + ((M - 1 : ℕ) : ℤ) * g = (M : ℤ) * g := by
        have hM1 : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
        rw [hM1]; ring
      rw [e3, hF.Amg hα1] at this
      exact this.symm
  refine ⟨?_, ?_⟩
  · by_cases hcα' : x % (g : ℤ) = α
    · exact mixFold_slot_eq hg hvg hNz hα0 (by omega) (fun h => (hcα h).trans (hF.capα h).symm)
        (fun j hj1 hj2 => (hint j hj1 hj2).1)
        (fun _ => by
          have e : (N : ℤ) - v + α = (M : ℤ) * g + α := by rw [hNz]; ring
          rw [e] at htα
          rw [htα, hF.termα]) hx1 hx2 hcα'
    · by_cases hcβ' : x % (g : ℤ) = β
      · exact mixFold_slot_eq hg hvg hNz (by omega) hβv (fun _ => (hcβ).trans (hF.capβ).symm)
          (fun j hj1 hj2 => (hint j hj1 hj2).2)
          (fun h => by
            have e : (N : ℤ) - v + β = (M : ℤ) * g + β := by rw [hNz]; ring
            have := htβ h
            rw [e] at this
            rw [this, hF.termβ h]) hx1 hx2 hcβ'
      · exact hclass x hx1 hx2 hcα' hcβ'
  · have h0 := Int.emod_nonneg (x - 1) hgz.ne'
    have h1 := Int.emod_lt_of_pos (x - 1) hgz
    have hk0 : 0 ≤ (x - 1) / (g : ℤ) := Int.ediv_nonneg (by omega) hgz.le
    have hdecomp : x = ((x - 1) % (g : ℤ) + 1) + ((x - 1) / (g : ℤ)).toNat * g := by
      have := Int.emod_def (x - 1) (g : ℤ)
      rw [Int.toNat_of_nonneg hk0]; linarith
    have e1 := mixFold_periodExcept_mul hB' ((x - 1) / (g : ℤ)).toNat ((x - 1) % (g : ℤ) + 1)
      (by omega) (by rw [← hdecomp]; omega) (by simp)
    have e2 := hF.perB_iter ((x - 1) / (g : ℤ)).toNat ((x - 1) % (g : ℤ) + 1) (by omega)
      (by rw [← hdecomp]; omega)
    rw [← hdecomp] at e1 e2
    rw [← e1, ← e2]
    by_cases hrt : (x - 1) % (g : ℤ) + 1 ≤ (g : ℤ) - 1
    · exact (hfirst _ (by omega) hrt).2
    · have hrg' : (x - 1) % (g : ℤ) + 1 = g := by omega
      rw [hrg', hBg, hF.Bg]

end MixFoldFold

end SkewGluing
