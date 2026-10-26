-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/Local/Assemble.lean
import GluingCore.Composition

/-!
# Assembling a connected skew diagram from its diagonal classes

Formalizes `shields-2026-skew-factor-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (3),
via the diagonal criterion of `eq:gluing-bits`).

A diagram `F` is presented by its diagonals in classes: the diagonal at the content
`c₀ + (j q + a)`, `0 ≤ a < q`, has the rows `[fLo j a, fHi j a]` when `(j, a)` is valid, namely for
`m ≤ j ≤ M`, or for `j = M + 1` and `a < w`.  Under the stepping conditions of the diagonal
criterion, `F` is connected skew and its diagonals are the stated ones.

Sorry-free.
-/

namespace GluingCore

/-- The valid classes `(j, a)`: all residues for `m ≤ j ≤ M`, and the residues `a < w` for
`j = M + 1`. -/
def ValidClass (m M w j a : ℤ) : Prop := (m ≤ j ∧ j ≤ M) ∨ (j = M + 1 ∧ a < w)

/-- The diagram `F` has, on the content `c₀ + (j q + a)`, exactly the rows `[fLo j a, fHi j a]`
for valid classes, with the stepping and end conditions of the diagonal criterion. -/
structure ClassRows (F : Diagram) (c₀ q w m M : ℤ) (fLo fHi : ℤ → ℤ → ℤ) : Prop where
  hq : 0 < q
  hw : 0 ≤ w
  hwq : w < q
  hmM : m ≤ M
  rows : ∀ j a r, 0 ≤ a → a < q →
    ((r, r + (c₀ + (j * q + a))) ∈ F ↔
      ValidClass m M w j a ∧ fLo j a ≤ r ∧ r ≤ fHi j a)
  ne : ∀ j a, 0 ≤ a → a < q → ValidClass m M w j a → fLo j a ≤ fHi j a
  stepA : ∀ j a, 1 ≤ a → a < q → ValidClass m M w j a →
    (fLo j (a - 1) - fLo j a = 0 ∨ fLo j (a - 1) - fLo j a = 1) ∧
    (fHi j (a - 1) - fHi j a = 0 ∨ fHi j (a - 1) - fHi j a = 1)
  stepB : ∀ j, ValidClass m M w j (q - 1) → ValidClass m M w (j + 1) 0 →
    (fLo j (q - 1) - fLo (j + 1) 0 = 0 ∨ fLo j (q - 1) - fLo (j + 1) 0 = 1) ∧
    (fHi j (q - 1) - fHi (j + 1) 0 = 0 ∨ fHi j (q - 1) - fHi (j + 1) 0 = 1)
  first : fLo m 0 = fHi m 0
  last_pos : 0 < w → fLo (M + 1) (w - 1) = fHi (M + 1) (w - 1)
  last_zero : w = 0 → fLo M (q - 1) = fHi M (q - 1)

namespace ClassRows

variable {F : Diagram} {c₀ q w m M : ℤ} {fLo fHi : ℤ → ℤ → ℤ}

theorem valid_iff (hc : ClassRows F c₀ q w m M fLo fHi) {j a : ℤ} (h0 : 0 ≤ a) (h1 : a < q) :
    ValidClass m M w j a ↔ m * q ≤ j * q + a ∧ j * q + a ≤ M * q + q + w - 1 := by
  have hq := hc.hq
  have hw := hc.hw
  have hwq := hc.hwq
  have hmM := hc.hmM
  unfold ValidClass
  have e1 : (M + 1) * q = M * q + q := by ring
  constructor
  · rintro (⟨h2, h3⟩ | ⟨h2, h3⟩)
    · constructor <;> nlinarith [mul_le_mul_of_nonneg_right h2 hq.le,
        mul_le_mul_of_nonneg_right h3 hq.le]
    · subst h2
      have := mul_le_mul_of_nonneg_right (show m ≤ M + 1 by omega) hq.le
      constructor <;> nlinarith
  · rintro ⟨h2, h3⟩
    by_cases hjm : j < m
    · have := mul_le_mul_of_nonneg_right (show j + 1 ≤ m by omega) hq.le
      nlinarith
    · by_cases hjM : j ≤ M
      · exact Or.inl ⟨by omega, hjM⟩
      · by_cases hj1 : j = M + 1
        · subst hj1
          exact Or.inr ⟨rfl, by nlinarith⟩
        · have := mul_le_mul_of_nonneg_right (show M + 2 ≤ j by omega) hq.le
          nlinarith

theorem diagLo_eq (hc : ClassRows F c₀ q w m M fLo fHi) {j a : ℤ} (h0 : 0 ≤ a) (h1 : a < q)
    (hv : ValidClass m M w j a) : diagLo F (c₀ + (j * q + a)) = fLo j a := by
  have hne := hc.ne j a h0 h1 hv
  apply diagLo_eq_of (l := fLo j a)
  · exact (hc.rows j a _ h0 h1).mpr ⟨hv, le_refl _, hne⟩
  · intro i hi
    exact ((hc.rows j a i h0 h1).mp hi).2.1

theorem diagHi_eq (hc : ClassRows F c₀ q w m M fLo fHi) {j a : ℤ} (h0 : 0 ≤ a) (h1 : a < q)
    (hv : ValidClass m M w j a) : diagHi F (c₀ + (j * q + a)) = fHi j a := by
  have hne := hc.ne j a h0 h1 hv
  apply diagHi_eq_of (l := fHi j a)
  · exact (hc.rows j a _ h0 h1).mpr ⟨hv, hne, le_refl _⟩
  · intro i hi
    exact ((hc.rows j a i h0 h1).mp hi).2.2

/-- Every content is decomposed as `c₀ + (j q + a)`. -/
theorem decomp (hc : ClassRows F c₀ q w m M fLo fHi) (c : ℤ) :
    ∃ j a, 0 ≤ a ∧ a < q ∧ c = c₀ + (j * q + a) := by
  have hq := hc.hq
  refine ⟨(c - c₀) / q, (c - c₀) % q, Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq, ?_⟩
  have := Int.mul_ediv_add_emod (c - c₀) q
  have e : (c - c₀) / q * q = q * ((c - c₀) / q) := by ring
  omega

theorem mem_contents (hc : ClassRows F c₀ q w m M fLo fHi) {j a : ℤ} (h0 : 0 ≤ a) (h1 : a < q) :
    c₀ + (j * q + a) ∈ contents F ↔ ValidClass m M w j a := by
  rw [mem_contents_iff]
  constructor
  · rintro ⟨i, hi⟩
    have e : i + (c₀ + (j * q + a)) = i + (c₀ + (j * q + a)) := rfl
    exact ((hc.rows j a i h0 h1).mp hi).1
  · intro hv
    exact ⟨fLo j a, (hc.rows j a _ h0 h1).mpr ⟨hv, le_refl _, hc.ne j a h0 h1 hv⟩⟩

theorem hasDiagonalShape (hc : ClassRows F c₀ q w m M fLo fHi) : HasDiagonalShape F := by
  have hq := hc.hq
  have hw := hc.hw
  have hwq := hc.hwq
  have hmM := hc.hmM
  have hvm : ValidClass m M w m 0 := Or.inl ⟨le_refl _, hmM⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨(fLo m 0, fLo m 0 + (c₀ + (m * q + 0))), ?_⟩
    exact (hc.rows m 0 _ (le_refl _) hq).mpr ⟨hvm, le_refl _, hc.ne m 0 (le_refl _) hq hvm⟩
  · -- the contents form an interval
    intro x hx y hy k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨jx, ax, hax0, haxq, hcx⟩ := hc.decomp (content x)
    obtain ⟨jy, ay, hay0, hayq, hcy⟩ := hc.decomp (content y)
    obtain ⟨jk, ak, hak0, hakq, hck⟩ := hc.decomp k
    have hxv : ValidClass m M w jx ax := by
      have := (hc.mem_contents hax0 haxq).mp (by rw [← hcx]; exact content_mem_contents hx)
      exact this
    have hyv : ValidClass m M w jy ay := by
      have := (hc.mem_contents hay0 hayq).mp (by rw [← hcy]; exact content_mem_contents hy)
      exact this
    rw [hck, hc.mem_contents hak0 hakq, hc.valid_iff hak0 hakq]
    rw [hc.valid_iff hax0 haxq] at hxv
    rw [hc.valid_iff hay0 hayq] at hyv
    omega
  · intro x hx y hy hxy i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨jx, ax, hax0, haxq, hcx⟩ := hc.decomp (content x)
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    simp only [content] at hcx hxy ⊢
    have e1 : x2 = x1 + (c₀ + (jx * q + ax)) := by omega
    have e2 : y2 = y1 + (c₀ + (jx * q + ax)) := by omega
    rw [e1] at hx
    rw [e2] at hy
    have h1 := (hc.rows jx ax _ hax0 haxq).mp hx
    have h2 := (hc.rows jx ax _ hax0 haxq).mp hy
    have : x2 - x1 = c₀ + (jx * q + ax) := by omega
    rw [this]
    exact (hc.rows jx ax i hax0 haxq).mpr
      ⟨h1.1, by simp only at hi; omega, by simp only at hi; omega⟩
  · intro k hk hk1
    obtain ⟨j, a, ha0, haq, hck⟩ := hc.decomp k
    subst hck
    have hv := (hc.mem_contents ha0 haq).mp hk
    by_cases ha : 1 ≤ a
    · have e : c₀ + (j * q + a) - 1 = c₀ + (j * q + (a - 1)) := by ring
      have hv' : ValidClass m M w j (a - 1) := by
        unfold ValidClass at hv ⊢
        omega
      have s := hc.stepA j a ha haq hv
      simp only [bitA, bitB, e, hc.diagLo_eq ha0 haq hv, hc.diagLo_eq (by omega) (by omega) hv',
        hc.diagHi_eq ha0 haq hv, hc.diagHi_eq (by omega) (by omega) hv', Finset.mem_insert,
        Finset.mem_singleton]
      exact s
    · have ha' : a = 0 := by omega
      subst ha'
      have e : c₀ + (j * q + 0) - 1 = c₀ + ((j - 1) * q + (q - 1)) := by ring
      rw [e] at hk1
      have hv' := (hc.mem_contents (by omega) (by omega)).mp hk1
      have hjq : (j - 1) * q + (q - 1) + 1 = j * q + 0 := by ring
      have hv'' : ValidClass m M w (j - 1 + 1) 0 := by
        have : j - 1 + 1 = j := by ring
        rw [this]; exact hv
      have s := hc.stepB (j - 1) hv' hv''
      have e2 : j - 1 + 1 = j := by ring
      rw [e2] at s
      simp only [bitA, bitB, e, hc.diagLo_eq (le_refl _) hq hv,
        hc.diagLo_eq (by omega) (by omega) hv',
        hc.diagHi_eq (le_refl _) hq hv, hc.diagHi_eq (by omega) (by omega) hv',
        Finset.mem_insert, Finset.mem_singleton]
      exact s
  · intro k hk hend
    obtain ⟨j, a, ha0, haq, hck⟩ := hc.decomp k
    subst hck
    have hv := (hc.mem_contents ha0 haq).mp hk
    rw [hc.diagLo_eq ha0 haq hv, hc.diagHi_eq ha0 haq hv]
    have hvu : ValidClass m M w j a := hv
    unfold ValidClass at hv
    rcases hend with hend | hend
    · -- the first diagonal
      have ha : a = 0 := by
        by_contra hna
        have e : c₀ + (j * q + a) - 1 = c₀ + (j * q + (a - 1)) := by ring
        rw [e, hc.mem_contents (by omega) (by omega)] at hend
        exact hend (by unfold ValidClass; omega)
      subst ha
      have hjm : j = m := by
        by_contra hjm
        have e : c₀ + (j * q + 0) - 1 = c₀ + ((j - 1) * q + (q - 1)) := by ring
        rw [e, hc.mem_contents (by omega) (by omega)] at hend
        exact hend (by unfold ValidClass; omega)
      subst hjm
      exact hc.first
    · have hv1 : a + 1 < q ∨ a + 1 = q := by omega
      rcases hv1 with hlt | heq
      · have e : c₀ + (j * q + a) + 1 = c₀ + (j * q + (a + 1)) := by ring
        rw [e, hc.mem_contents (by omega) hlt] at hend
        have hj : j = M + 1 := by
          by_contra hjM
          exact hend (by unfold ValidClass; omega)
        subst hj
        have hwpos : 0 < w := by omega
        have ha : a = w - 1 := by
          by_contra hna
          exact hend (by unfold ValidClass; omega)
        subst ha
        exact hc.last_pos hwpos
      · have e : c₀ + (j * q + a) + 1 = c₀ + ((j + 1) * q + 0) := by
          have : (j + 1) * q = j * q + q := by ring
          omega
        rw [e, hc.mem_contents (le_refl _) hq] at hend
        have hjM : j = M := by
          by_contra hjM
          exact hend (by unfold ValidClass; omega)
        subst hjM
        have hw0 : w = 0 := by
          by_contra hw0
          exact hend (by unfold ValidClass; omega)
        have ha : a = q - 1 := by omega
        subst ha
        exact hc.last_zero hw0

theorem isConnectedSkew (hc : ClassRows F c₀ q w m M fLo fHi) : IsConnectedSkew F :=
  isConnectedSkew_iff_diagonal.mpr hc.hasDiagonalShape

end ClassRows

end GluingCore
