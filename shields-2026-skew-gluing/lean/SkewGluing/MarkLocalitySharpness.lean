import SkewGluing.MarkLocality

/-!
# The windows of mark locality are sharp at the upper end too

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`), the
remark after `lem:gluing-mark-locality`: "rotation gives the other end".

The row `(3)` and the hook `(2, 1)` agree on the content `0` and, up to translation, on `[1, 2]`,
but their legal width-one marks have cases (a) and (d) (`sharpRow`, `sharpHook` in
`SkewGluing.MarkLocality`).  Rotation turns this into the sharpness at the upper end of the
window: the row `(3)` and the rotated hook `sharpHookRotated` have the same cells on the contents
`[0, w] = [0, 1]`, agree up to translation by `τ = (-1, -1)` on `[N - w, N - 1] = [2, 2]`, but not
on `[N - w - 1, N - 1] = [1, 2]`; their legal width-one marks have cases (a) and (c).

Sorry-free.
-/

namespace SkewGluing

section SharpnessUpper

/-- The rotated hook `(2, 1)`, southwest-normalized: the cells `(0, 0)`, `(0, 1)`, `(-1, 1)`. -/
def sharpHookRotated : Diagram := {(0, 0), (0, 1), (-1, 1)}

/-- The width-one mark of case (c) on the rotated hook: the rotation of `sharpHookMark`,
translated to the southwest-normalized position. -/
def sharpHookRotatedMark : MarkedInner where
  E := sharpHookRotated
  W := {(0, 0)}
  v := (-1, 1)
  case := .c

/-- `sharpHookRotated` is the southwest-normalized rotation of `sharpHook`. -/
example : sharpHookRotated = translate (-1, 1) (rotate sharpHook) := by decide

/-- The rotation of the width-one mark of `sharpHook`, translated, is `sharpHookRotatedMark`. -/
example : (sharpHookMark.rotate.E, sharpHookMark.rotate.W, sharpHookMark.rotate.v,
    sharpHookMark.rotate.case) =
    (translate (1, -1) sharpHookRotated, translate (1, -1) sharpHookRotatedMark.W,
      sharpHookRotatedMark.v, sharpHookRotatedMark.case) := by decide

/-- The row `(3)` is its own rotation, up to translation, and the rotated width-one mark is the
mark `sharpRowMark`. -/
example : sharpRow = translate (0, 2) (rotate sharpRow) := by decide

example : (translate (0, 2) sharpRowMark.rotate.E, translate (0, 2) sharpRowMark.rotate.W,
    sharpRowMark.rotate.v, sharpRowMark.rotate.case) =
    (sharpRowMark.E, sharpRowMark.W, sharpRowMark.v, sharpRowMark.case) := by decide

example : span sharpRow = 3 ∧ span sharpHookRotated = 3 := by decide
example : IsConnectedSkew sharpRow ∧ IsConnectedSkew sharpHookRotated := by decide
example : sw sharpRow = (0, 0) ∧ sw sharpHookRotated = (0, 0) := by decide

/-- The two diagrams have the same cells on the contents `[0, w] = [0, 1]`. -/
example : sharpRow.filter (fun x => 0 ≤ content x ∧ content x ≤ 1) =
    sharpHookRotated.filter (fun x => 0 ≤ content x ∧ content x ≤ 1) := by decide

/-- Up to translation by `τ = (-1, -1)`, with `c(τ) = 0`, they agree on
`[N - w, N - 1] = [2, 2]`. -/
example : translate (-1, -1) (sharpRow.filter (fun x => 2 ≤ content x ∧ content x ≤ 2)) =
    sharpHookRotated.filter (fun x => 2 ≤ content x ∧ content x ≤ 2) := by decide

/-- The upper window cannot be shortened to `[N - w, N - 1]`: up to translation by `τ` the
diagrams differ on `[N - w - 1, N - 1] = [1, 2]`. -/
example : translate (-1, -1) (sharpRow.filter (fun x => 1 ≤ content x ∧ content x ≤ 2)) ≠
    sharpHookRotated.filter (fun x => 1 ≤ content x ∧ content x ≤ 2) := by decide

example : sharpRowMark.IsLegal := by decide
example : sharpHookRotatedMark.IsLegal := by decide
example : sharpRowMark.width = 1 ∧ sharpHookRotatedMark.width = 1 := by decide

/-- The two legal marks have different attachment cases, (a) and (c), so legality does not
transfer: the other case is illegal on each diagram. -/
example : ¬ ({ sharpHookRotatedMark with case := .a } : MarkedInner).IsLegal := by decide
example : ¬ ({ sharpRowMark with case := .c } : MarkedInner).IsLegal := by decide

end SharpnessUpper

end SkewGluing
