import SkewGluing.MixedFold.Facts

/-!
# The cells of a connected skew diagram by diagonals

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (the diagonal criterion after
`eq:gluing-bits`), in the form used to certify the pieces of a constructed mark.

`mixFold_mem_of_connectedSkew` describes the cells of a connected skew diagram by their diagonal
rows: the converse of `isConnectedSkew_of_rows` (module `Diagram`).

Sorry-free.
-/

namespace SkewGluing

theorem mixFold_mem_of_connectedSkew {E : Diagram} (hE : IsConnectedSkew E) (x : ℤ × ℤ) :
    x ∈ E ↔ content x ∈ contents E ∧ diagLo E (content x) ≤ x.1 ∧ x.1 ≤ diagHi E (content x) := by
  have h := (isConnectedSkew_iff_diagonal.mp hE)
  obtain ⟨a, b⟩ := x
  have e : (a, b) = (a, a + (b - a)) := by ext <;> simp
  rw [e]
  have := h.mem_iff (k := b - a) (i := a)
  simp only [content]
  simpa using this

end SkewGluing
