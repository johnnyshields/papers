import SkewGluing.Local
import SkewGluing.PeriodWords

/-!
# Boundary words of a composite, read on diagonal classes

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`).

The parent boundary words are `A_k = ℓ_{k-1} - ℓ_k` and `B_k = h_{k-1} - h_k` on the
southwest-normalized contents `0, …, N - 1`, that is `wordA F k = bitA F (minContent F + k)`.  The
diagonal-class presentation `ClassRows` of a composite gives each diagonal at content
`c₀ + (J q + a)` the first row `fLo J a` and the last row `fHi J a`; `classBitLo`, `classBitHi`
read the two words on such a class, and the main theorems of this file turn a statement about
classes into the statement `PeriodExcept` of `lem:gluing-periods`.

Sorry-free.
-/

namespace SkewGluing

/-- The word `A_k = ℓ_{k-1} - ℓ_k` of a diagram, read at the content `minContent F + k`
(`eq:gluing-bits`; the paper normalizes so that the contents are `0, …, N - 1`). -/
def wordA (F : Diagram) (k : ℤ) : ℤ := bitA F (minContent F + k)

/-- The word `B_k = h_{k-1} - h_k` of a diagram, read at the content `minContent F + k`
(`eq:gluing-bits`). -/
def wordB (F : Diagram) (k : ℤ) : ℤ := bitB F (minContent F + k)

/-- The word `A` is unchanged by translating the diagram, on the positions `1, …, N - 1`. -/
theorem wordA_translate {D : Diagram} (hD : IsConnectedSkew D) (t : ℤ × ℤ) {k : ℤ}
    (h1 : 1 ≤ k) (h2 : k < (span D : ℤ)) : wordA (translate t D) k = wordA D k := by
  have hne := hD.2.1
  have hsp := span_eq_of_isConnectedSkew hD
  have hc : ∀ {j : ℤ}, j ∈ contents D ↔ minContent D ≤ j ∧ j ≤ maxContent D :=
    fun {j} => (isConnectedSkew_iff_diagonal.mp hD).mem_contents_iff (k := j)
  unfold wordA bitA
  rw [minContent_translate hne]
  have e1 : minContent D + content t + k - 1 = (minContent D + k - 1) + content t := by ring
  have e2 : minContent D + content t + k = (minContent D + k) + content t := by ring
  rw [e1, e2, diagLo_translate t _ (hc.mpr ⟨by omega, by omega⟩),
    diagLo_translate t _ (hc.mpr ⟨by omega, by omega⟩)]
  ring

/-- The word `B` is unchanged by translating the diagram, on the positions `1, …, N - 1`. -/
theorem wordB_translate {D : Diagram} (hD : IsConnectedSkew D) (t : ℤ × ℤ) {k : ℤ}
    (h1 : 1 ≤ k) (h2 : k < (span D : ℤ)) : wordB (translate t D) k = wordB D k := by
  have hne := hD.2.1
  have hsp := span_eq_of_isConnectedSkew hD
  have hc : ∀ {j : ℤ}, j ∈ contents D ↔ minContent D ≤ j ∧ j ≤ maxContent D :=
    fun {j} => (isConnectedSkew_iff_diagonal.mp hD).mem_contents_iff (k := j)
  unfold wordB bitB
  rw [minContent_translate hne]
  have e1 : minContent D + content t + k - 1 = (minContent D + k - 1) + content t := by ring
  have e2 : minContent D + content t + k = (minContent D + k) + content t := by ring
  rw [e1, e2, diagHi_translate t _ (hc.mpr ⟨by omega, by omega⟩),
    diagHi_translate t _ (hc.mpr ⟨by omega, by omega⟩)]
  ring

/-- The step `fLo J (a - 1) - fLo J a` of the first rows on the class `(J, a)`, with the step of
the class boundary (`a = 0`) read from the last class `(J - 1, q - 1)` of the previous block. -/
def classBitLo (q : ℤ) (fLo : ℤ → ℤ → ℤ) (J a : ℤ) : ℤ :=
  if a = 0 then fLo (J - 1) (q - 1) - fLo J 0 else fLo J (a - 1) - fLo J a

/-- The step `fHi J (a - 1) - fHi J a` of the last rows on the class `(J, a)`, with the step of
the class boundary (`a = 0`) read from the last class `(J - 1, q - 1)` of the previous block. -/
def classBitHi (q : ℤ) (fHi : ℤ → ℤ → ℤ) (J a : ℤ) : ℤ :=
  if a = 0 then fHi (J - 1) (q - 1) - fHi J 0 else fHi J (a - 1) - fHi J a

theorem validClass_pred {m M w J a : ℤ} (hv : ValidClass m M w J a) :
    ValidClass m M w J (a - 1) := by
  unfold ValidClass at hv ⊢
  omega

theorem validClass_prev {m M w J : ℤ} (a : ℤ) (hv : ValidClass m M w J 0)
    (hJ : m + 1 ≤ J) : ValidClass m M w (J - 1) a := by
  unfold ValidClass at hv ⊢
  omega

theorem validClass_ge {m M w J a : ℤ} (hmM : m ≤ M) (hv : ValidClass m M w J a) : m ≤ J := by
  unfold ValidClass at hv
  omega

namespace ClassRows

variable {F : Diagram} {c₀ q w m M : ℤ} {fLo fHi : ℤ → ℤ → ℤ}

/-- The first-row step at the content `c₀ + (J q + a)` of a diagram presented by classes. -/
theorem bitA_class (hc : ClassRows F c₀ q w m M fLo fHi) {J a : ℤ} (h0 : 0 ≤ a) (h1 : a < q)
    (hv : ValidClass m M w J a) (hJ : a = 0 → m + 1 ≤ J) :
    bitA F (c₀ + (J * q + a)) = classBitLo q fLo J a := by
  unfold bitA classBitLo
  by_cases ha : a = 0
  · subst ha
    have hv' := validClass_prev (q - 1) hv (hJ rfl)
    have e : c₀ + (J * q + 0) - 1 = c₀ + ((J - 1) * q + (q - 1)) := by ring
    simp only [ite_true, e]
    rw [hc.diagLo_eq (by omega) (by omega) hv', hc.diagLo_eq (le_refl _) hc.hq hv]
  · have hv' := validClass_pred hv
    have e : c₀ + (J * q + a) - 1 = c₀ + (J * q + (a - 1)) := by ring
    simp only [ha, ite_false, e]
    rw [hc.diagLo_eq (by omega) (by omega) hv', hc.diagLo_eq h0 h1 hv]

/-- The last-row step at the content `c₀ + (J q + a)` of a diagram presented by classes. -/
theorem bitB_class (hc : ClassRows F c₀ q w m M fLo fHi) {J a : ℤ} (h0 : 0 ≤ a) (h1 : a < q)
    (hv : ValidClass m M w J a) (hJ : a = 0 → m + 1 ≤ J) :
    bitB F (c₀ + (J * q + a)) = classBitHi q fHi J a := by
  unfold bitB classBitHi
  by_cases ha : a = 0
  · subst ha
    have hv' := validClass_prev (q - 1) hv (hJ rfl)
    have e : c₀ + (J * q + 0) - 1 = c₀ + ((J - 1) * q + (q - 1)) := by ring
    simp only [ite_true, e]
    rw [hc.diagHi_eq (by omega) (by omega) hv', hc.diagHi_eq (le_refl _) hc.hq hv]
  · have hv' := validClass_pred hv
    have e : c₀ + (J * q + a) - 1 = c₀ + (J * q + (a - 1)) := by ring
    simp only [ha, ite_false, e]
    rw [hc.diagHi_eq (by omega) (by omega) hv', hc.diagHi_eq h0 h1 hv]

/-- The word `A` of a composite at the position `(J - m) q + a`, read on the class `(J, a)`. -/
theorem wordA_class (hc : ClassRows F c₀ q w m M fLo fHi) (hmin : minContent F = c₀ + m * q)
    {J a : ℤ} (h0 : 0 ≤ a) (h1 : a < q) (hv : ValidClass m M w J a)
    (hJ : a = 0 → m + 1 ≤ J) :
    wordA F ((J - m) * q + a) = classBitLo q fLo J a := by
  unfold wordA
  rw [← hc.bitA_class h0 h1 hv hJ, hmin]
  congr 1
  ring

/-- The word `B` of a composite at the position `(J - m) q + a`, read on the class `(J, a)`. -/
theorem wordB_class (hc : ClassRows F c₀ q w m M fLo fHi) (hmin : minContent F = c₀ + m * q)
    {J a : ℤ} (h0 : 0 ≤ a) (h1 : a < q) (hv : ValidClass m M w J a)
    (hJ : a = 0 → m + 1 ≤ J) :
    wordB F ((J - m) * q + a) = classBitHi q fHi J a := by
  unfold wordB
  rw [← hc.bitB_class h0 h1 hv hJ, hmin]
  congr 1
  ring

theorem wordA_class' (hc : ClassRows F c₀ q w m M fLo fHi) (hmin : minContent F = c₀ + m * q)
    {J a k : ℤ} (hk : k = (J - m) * q + a) (h0 : 0 ≤ a) (h1 : a < q)
    (hv : ValidClass m M w J a) (hJ : a = 0 → m + 1 ≤ J) :
    wordA F k = classBitLo q fLo J a := by
  subst hk
  exact hc.wordA_class hmin h0 h1 hv hJ

theorem wordB_class' (hc : ClassRows F c₀ q w m M fLo fHi) (hmin : minContent F = c₀ + m * q)
    {J a k : ℤ} (hk : k = (J - m) * q + a) (h0 : 0 ≤ a) (h1 : a < q)
    (hv : ValidClass m M w J a) (hJ : a = 0 → m + 1 ≤ J) :
    wordB F k = classBitHi q fHi J a := by
  subst hk
  exact hc.wordB_class hmin h0 h1 hv hJ

/-- The classes of the two positions `x` and `x + q` of a word on `1, …, N - 1`, where
`N = (M - m + 1) q + w`. -/
theorem position_class (hc : ClassRows F c₀ q w m M fLo fHi) {x : ℤ} (h1 : 1 ≤ x)
    (h2 : x ≤ (M - m + 1) * q + w - 1) :
    ∃ J a, 0 ≤ a ∧ a < q ∧ x = (J - m) * q + a ∧ ValidClass m M w J a ∧
      (a = 0 → m + 1 ≤ J) := by
  have hq := hc.hq
  have hw := hc.hw
  have hwq := hc.hwq
  refine ⟨m + x / q, x % q, Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq, ?_, ?_, ?_⟩
  · have := Int.mul_ediv_add_emod x q
    have e : (m + x / q - m) * q = q * (x / q) := by ring
    omega
  · rw [hc.valid_iff (Int.emod_nonneg _ hq.ne') (Int.emod_lt_of_pos _ hq)]
    have := Int.mul_ediv_add_emod x q
    have e : (m + x / q) * q = m * q + q * (x / q) := by ring
    have e2 : (M - m + 1) * q = M * q - m * q + q := by ring
    have := Int.emod_nonneg x hq.ne'
    constructor <;> omega
  · intro h0
    have h3 := Int.mul_ediv_add_emod x q
    have h4 := Int.ediv_nonneg (show 0 ≤ x by omega) hq.le
    have : x / q ≠ 0 := fun hz => by rw [hz] at h3; omega
    omega

/-- The rows of the cells of a diagram presented by classes lie between the first and the last row
of their class. -/
theorem row_bounds (hc : ClassRows F c₀ q w m M fLo fHi) {J a : ℤ} (h0 : 0 ≤ a) (h1 : a < q)
    {p : ℤ × ℤ} (hp : p ∈ F) (hcont : content p = c₀ + (J * q + a)) :
    ValidClass m M w J a ∧ fLo J a ≤ p.1 ∧ p.1 ≤ fHi J a := by
  have e : p = (p.1, p.1 + (c₀ + (J * q + a))) := by
    ext
    · rfl
    · simp only [content] at hcont
      omega
  rw [e] at hp
  exact (hc.rows J a p.1 h0 h1).mp hp

end ClassRows

/-- A word on `1, …, N - 1` presented by classes has period `q` except at the residues `S` as soon
as the class steps of the same residue `a ∉ S` agree in consecutive blocks.  Here `N = (M - m + 1)
q + w` is the span of the composite. -/
theorem periodExcept_of_classBit {F : Diagram} {c₀ q w m M : ℤ} {fLo fHi : ℤ → ℤ → ℤ}
    (hc : ClassRows F c₀ q w m M fLo fHi) (hN : (span F : ℤ) = (M - m + 1) * q + w)
    {S : Finset ℤ} {word : ℤ → ℤ} {bit : ℤ → ℤ → ℤ}
    (hword : ∀ J a, 0 ≤ a → a < q → ValidClass m M w J a → (a = 0 → m + 1 ≤ J) →
      word ((J - m) * q + a) = bit J a)
    (hper : ∀ J a, 0 ≤ a → a < q → a ∉ S → ValidClass m M w J a →
      ValidClass m M w (J + 1) a → (a = 0 → m + 1 ≤ J) → bit J a = bit (J + 1) a) :
    PeriodWords.PeriodExcept (span F - 1) q.toNat S word := by
  intro x hx hS
  have hq := hc.hq
  have hw := hc.hw
  have hqq : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq.le
  have hL : (((span F - 1 : ℕ)) : ℤ) = (span F : ℤ) - 1 := by
    have := mul_le_mul_of_nonneg_right (show 1 ≤ M - m + 1 by have := hc.hmM; omega) hq.le
    omega
  rw [Finset.mem_Icc, hL, hqq] at hx
  rw [hqq] at hS ⊢
  obtain ⟨J, a, ha0, haq, rfl, hv, hJ⟩ := hc.position_class (x := x) hx.1 (by omega)
  have hv' : ValidClass m M w (J + 1) a := by
    rw [hc.valid_iff ha0 haq] at hv ⊢
    have e : (J + 1) * q = J * q + q := by ring
    have e2 : (M - m + 1) * q = M * q - m * q + q := by ring
    have e3 : (J - m) * q = J * q - m * q := by ring
    omega
  have e : (J - m) * q + a + q = (J + 1 - m) * q + a := by ring
  rw [e, hword J a ha0 haq hv hJ, hword (J + 1) a ha0 haq hv' (fun _ => by omega)]
  have hS' : a ∉ S := by
    have : ((J - m) * q + a) % q = a := by
      rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod_of_dvd _ dvd_rfl,
        Int.emod_eq_of_lt ha0 haq]
    rwa [this] at hS
  exact hper J a ha0 haq hS' hv hv' hJ

end SkewGluing
