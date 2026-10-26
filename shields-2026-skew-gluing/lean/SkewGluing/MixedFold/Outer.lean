import SkewGluing.MixedFold.Inner

/-!
# The outer of the period-`g` root

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`, `eq:gluing-mixed-inverse`).

The outer `D = mixFoldOuter A g M v α β` is the connected skew diagram of span `M` with bits
`A^D_j = A_F(j g + α)`, `B^D_j = 1 - A_F(j g + β)` for `1 ≤ j < M`.  The block relation
`H_{(j+1) g + v} - H_{j g + v} = A_{(j+1)g+α} + A_{(j+1)g+β} - 1` of the parent for every `j`
(`MixFoldFold.block_all`) says that the heights of `D` are the parent's private heights
`H_{j g + v}`, so the bit data are admissible (`MixFoldFold.isBitData_outer`).

Sorry-free.
-/

namespace SkewGluing

open PeriodWords

/-- The first-row word of the outer. -/
def mixFoldOA (A : ℤ → ℤ) (g : ℕ) (α : ℤ) : ℕ → ℤ := fun j => A ((j : ℤ) * g + α)

/-- The last-row word of the outer. -/
def mixFoldOB (A : ℤ → ℤ) (g : ℕ) (β : ℤ) : ℕ → ℤ := fun j => 1 - A ((j : ℤ) * g + β)

/-- The outer of the folded root. -/
def mixFoldOuter (A : ℤ → ℤ) (g M : ℕ) (α β : ℤ) : Diagram :=
  fromBits M (mixFoldOA A g α) (mixFoldOB A g β)

namespace MixFoldFold

variable {A B : ℤ → ℤ} {N g M v : ℕ} {α β : ℤ}

/-- The generic comparison words of the parent: periodic, equal to the parent's words off the
exceptional classes (and zero on them). -/
theorem exists_generic (hF : MixFoldFold A B N g M v α β) :
    ∃ Ab Bb : ℤ → ℤ, (∀ x, Ab (x + g) = Ab x) ∧ (∀ x, Bb (x + g) = Bb x) ∧
      (∀ x, 1 ≤ x → x ≤ (N : ℤ) - 1 → B x = Bb x) ∧
      (∀ x, 1 ≤ x → x ≤ (N : ℤ) - 1 → x % (g : ℤ) ≠ α → x % (g : ℤ) ≠ β → A x = Ab x) ∧
      (∀ x, (x % (g : ℤ) = α ∨ x % (g : ℤ) = β) → Ab x = 0) := by
  have hg : 0 < g := by have := hF.hv0; have := hF.hvg; omega
  have hgz : (0 : ℤ) < g := by exact_mod_cast hg
  have hM := hF.hM
  have hNN := hF.hN
  have hvg := hF.hvg
  refine ⟨fun x => if x % (g : ℤ) = α ∨ x % (g : ℤ) = β then 0 else A ((x - 1) % (g : ℤ) + 1),
    fun x => B ((x - 1) % (g : ℤ) + 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have e : (x + (g : ℤ)) % (g : ℤ) = x % (g : ℤ) := by simp
    have e2 : (x + (g : ℤ) - 1) % (g : ℤ) = (x - 1) % (g : ℤ) := by
      rw [show x + (g : ℤ) - 1 = (x - 1) + g by ring]; simp
    simp only [e, e2]
  · intro x
    have e2 : (x + (g : ℤ) - 1) % (g : ℤ) = (x - 1) % (g : ℤ) := by
      rw [show x + (g : ℤ) - 1 = (x - 1) + g by ring]; simp
    simp only [e2]
  · intro x hx1 hx2
    have h1 : 1 ≤ (x - 1) % (g : ℤ) + 1 := by
      have := Int.emod_nonneg (x - 1) hgz.ne'; omega
    have h2 : (x - 1) % (g : ℤ) + 1 ≤ (N : ℤ) - 1 := by
      have := Int.emod_lt_of_pos (x - 1) hgz
      have : (M : ℤ) * g ≥ 2 * g := by
        have : (2 : ℤ) ≤ M := by exact_mod_cast hM
        nlinarith
      have hNz : (N : ℤ) = (M : ℤ) * g + v := by exact_mod_cast hNN
      omega
    have hB := hF.perB
    have hNe : 1 ≤ N := by omega
    refine mixFold_eq_of_gcd_dvd hg hB hx1 hx2 h1 h2 ?_
    have := Int.emod_def (x - 1) (g : ℤ)
    exact ⟨-((x - 1) / g), by linarith⟩
  · intro x hx1 hx2 hα hβ
    have hn : ¬ (x % (g : ℤ) = α ∨ x % (g : ℤ) = β) := by tauto
    simp only [hn, ite_false]
    have h0 := Int.emod_nonneg (x - 1) hgz.ne'
    have h1 := Int.emod_lt_of_pos (x - 1) hgz
    have hdecomp : x = ((x - 1) % (g : ℤ) + 1) + ((x - 1) / (g : ℤ)).toNat * g := by
      have := Int.emod_def (x - 1) (g : ℤ)
      have h3 : 0 ≤ (x - 1) / (g : ℤ) := Int.ediv_nonneg (by omega) hgz.le
      rw [Int.toNat_of_nonneg h3]; linarith
    have hr : ((x - 1) % (g : ℤ) + 1) % (g : ℤ) = x % (g : ℤ) := by
      have : x = ((x - 1) % (g : ℤ) + 1) + ((x - 1) / (g : ℤ)).toNat * g := hdecomp
      conv_rhs => rw [this]
      rw [Int.add_mul_emod_self_right]
    have := hF.perA_iter ((x - 1) / (g : ℤ)).toNat ((x - 1) % (g : ℤ) + 1) (by omega)
      (by rw [← hdecomp]; omega) (by rw [hr]; exact hα) (by rw [hr]; exact hβ)
    rw [← hdecomp] at this
    exact this.symm
  · intro x hx
    simp only [hx, ite_true]

/-- **The block relation at every block.**  For `j + 2 ≤ M`,
`H_{(j+1) g + v} = H_{j g + v} + A_{(j+1) g + α} + A_{(j+1) g + β} - 1`. -/
theorem block_all (hF : MixFoldFold A B N g M v α β) :
    ∀ j : ℕ, j + 2 ≤ M → mixFold_ht A B ((j + 1) * g + v) = mixFold_ht A B (j * g + v) +
      (A (((j : ℤ) + 1) * g + α) + A (((j : ℤ) + 1) * g + β) - 1) := by
  obtain ⟨Ab, Bb, hAb, hBb, hBeq, hAeq, hAz⟩ := hF.exists_generic
  have hg : 0 < g := by have := hF.hv0; have := hF.hvg; omega
  have hgz : (0 : ℤ) < g := by exact_mod_cast hg
  have hM := hF.hM
  have hNN := hF.hN
  have hvg := hF.hvg
  have hαβ := hF.hαβ
  have hβv := hF.hβv
  have hα0 := hF.hα
  have hv0 := hF.hv0
  have hNz : (N : ℤ) = (M : ℤ) * g + v := by exact_mod_cast hNN
  have key : ∀ j : ℕ, j + 2 ≤ M → mixFold_ht A B ((j + 1) * g + v) = mixFold_ht A B (j * g + v) +
      ((mixFold_ht Ab Bb g - 1) + A (((j : ℤ) + 1) * g + α) + A (((j : ℤ) + 1) * g + β)) := by
    intro j hj
    have hMj : ((j : ℤ) + 2) * g ≤ (M : ℤ) * g := by
      have : (j : ℤ) + 2 ≤ M := by exact_mod_cast hj
      nlinarith
    have e : (j + 1) * g + v = (j * g + v) + g := by ring
    rw [e, mixFold_ht_eq_add_dev A B Ab Bb, mixFold_ht_eq_add_dev A B Ab Bb (j * g + v),
      mixFold_devSum_add', mixFold_gen_ht_add hAb hBb]
    have hW := mixFold_winSum_pair A B Ab Bb (j * g + v) g (((j : ℤ) + 1) * g + α)
      (((j : ℤ) + 1) * g + β) (by omega) (by push_cast; nlinarith) (by push_cast; nlinarith)
      (by push_cast; nlinarith) (by push_cast; nlinarith) (fun y hy1 hy2 hne1 hne2 => by
        push_cast at hy1 hy2
        by_contra hdev
        have hy3 : 1 ≤ y := by nlinarith
        have hy4 : y ≤ (N : ℤ) - 1 := by nlinarith
        have hcl : y % (g : ℤ) = α ∨ y % (g : ℤ) = β := by
          by_contra hc
          push Not at hc
          apply hdev
          unfold mixFold_dev
          rw [hBeq y hy3 hy4, hAeq y hy3 hy4 hc.1 hc.2]; ring
        have uniq : ∀ ρ : ℤ, y % (g : ℤ) = ρ → 0 ≤ ρ → ρ ≤ v → y = ((j : ℤ) + 1) * g + ρ := by
          intro ρ hy hρ0 hρv
          have hd : (g : ℤ) ∣ y - (((j : ℤ) + 1) * g + ρ) := by
            have e1 : (((j : ℤ) + 1) * g + ρ) % (g : ℤ) = ρ := by
              rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod_of_dvd _ dvd_rfl,
                Int.emod_eq_of_lt hρ0 (by omega)]
            exact PeriodWords.dvd_sub_of_emod_eq (by rw [hy, e1])
          have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> nlinarith)
          omega
        rcases hcl with h | h
        · exact hne1 (uniq α h hα0 (by omega))
        · exact hne2 (uniq β h (by omega) hβv))
    have d1 : mixFold_dev A B Ab Bb (((j : ℤ) + 1) * g + α) = A (((j : ℤ) + 1) * g + α) := by
      have hm : (((j : ℤ) + 1) * g + α) % (g : ℤ) = α := by
        rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod_of_dvd _ dvd_rfl,
          Int.emod_eq_of_lt hα0 (by omega)]
      unfold mixFold_dev
      rw [hBeq _ (by nlinarith) (by nlinarith), hAz _ (Or.inl hm)]; ring
    have d2 : mixFold_dev A B Ab Bb (((j : ℤ) + 1) * g + β) = A (((j : ℤ) + 1) * g + β) := by
      have hm : (((j : ℤ) + 1) * g + β) % (g : ℤ) = β := by
        rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod_of_dvd _ dvd_rfl,
          Int.emod_eq_of_lt (by omega) (by omega)]
      unfold mixFold_dev
      rw [hBeq _ (by nlinarith) (by nlinarith), hAz _ (Or.inr hm)]; ring
    rw [d1, d2] at hW
    linarith
  intro j hj
  have h0 := key 0 (by omega)
  have hb := hF.block
  simp only [zero_add, one_mul, Nat.cast_zero, zero_mul] at h0
  rw [h0] at hb
  have hΔ : mixFold_ht Ab Bb g - 1 = -1 := by linarith
  have := key j hj
  rw [hΔ] at this
  linarith

theorem bit_of_bitData (hbd : IsBitData N (fun k : ℕ => A k) (fun k : ℕ => B k)) {y : ℤ}
    (h1 : 1 ≤ y) (h2 : y ≤ (N : ℤ) - 1) : (A y = 0 ∨ A y = 1) ∧ (B y = 0 ∨ B y = 1) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ y by omega)
  exact hbd.2.1 n (by omega) (by omega)

theorem isBitData_outer (hF : MixFoldFold A B N g M v α β)
    (hbd : IsBitData N (fun k : ℕ => A k) (fun k : ℕ => B k)) :
    IsBitData M (mixFoldOA A g α) (mixFoldOB A g β) := by
  obtain ⟨hN0, hbits, hpos, hlast⟩ := hbd
  have hbd' : IsBitData N (fun k : ℕ => A k) (fun k : ℕ => B k) := ⟨hN0, hbits, hpos, hlast⟩
  have hM := hF.hM
  have hNN := hF.hN
  have hvg := hF.hvg
  have hv0 := hF.hv0
  have hαβ := hF.hαβ
  have hβv := hF.hβv
  have hα0 := hF.hα
  have hNz : (N : ℤ) = (M : ℤ) * g + v := by exact_mod_cast hNN
  have hgpos : 0 < g := by omega
  have hg : (g : ℤ) ≥ 1 := by exact_mod_cast hgpos
  have hheights : ∀ j : ℕ, j + 1 ≤ M →
      heightWord (mixFoldOA A g α) (mixFoldOB A g β) j = mixFold_ht A B (j * g + v) := by
    intro j
    induction j with
    | zero => intro _; simp [heightWord, hF.Hv]
    | succ j ih =>
      intro hj
      rw [heightWord_succ, ih (by omega)]
      have := hF.block_all j (by omega)
      rw [this]
      simp only [mixFoldOA, mixFoldOB]
      push_cast
      ring
  refine ⟨by omega, fun k hk1 hk2 => ?_, fun k hk => ?_, ?_⟩
  · have hMk : (k : ℤ) + 1 ≤ M := by exact_mod_cast hk2
    have hk0 : (1 : ℤ) ≤ k := by exact_mod_cast hk1
    have hkg : (k : ℤ) * g + g ≤ (M : ℤ) * g := by nlinarith
    have b1 := bit_of_bitData hbd' (y := (k : ℤ) * g + α) (by nlinarith) (by nlinarith)
    have b2 := bit_of_bitData hbd' (y := (k : ℤ) * g + β) (by nlinarith) (by nlinarith)
    simp only [mixFoldOA, mixFoldOB]
    constructor
    · exact b1.1
    · rcases b2.1 with h | h <;> omega
  · rw [hheights k (by omega)]
    exact hpos _ (by
      have : (k : ℤ) * g + g ≤ (M : ℤ) * g := by
        have hMk : (k : ℤ) + 1 ≤ M := by exact_mod_cast hk
        nlinarith
      have h2 : ((k * g + v : ℕ) : ℤ) < N := by push_cast; omega
      exact_mod_cast h2)
  · rw [hheights (M - 1) (by omega)]
    have : (M - 1) * g + v = N - g := by
      have h2 : (M - 1) * g + g = M * g := by rw [← Nat.succ_mul]; congr 1; omega
      omega
    rw [this]
    exact hF.HNg

end MixFoldFold

end SkewGluing
