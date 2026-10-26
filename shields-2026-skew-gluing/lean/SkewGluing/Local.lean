import SkewGluing.Local.Statements
import SkewGluing.Local.Windows
import SkewGluing.Local.Injective
import SkewGluing.Local.Profile
import SkewGluing.Local.Final

/-!
# Local common-factor gluing: the geometry of a legal mark

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`),
«Diagonal geometry» (`lem:gluing-local`, `eq:gluing-profile`, `eq:gluing-mixed-profile`, and the
fixed-chart injectivity paragraph).

The headline statements are:

* `MarkedInner.IsLegal.gluing_local_one`, `MarkedInner.IsLegal.gluing_local_two`
  (`lem:gluing-local` (1), (2)), for legal marks with a nonempty copy;
* `MarkedInner.IsLegal.isConnectedSkew_compose`, `MarkedInner.IsLegal.compose_first_window`,
  `MarkedInner.IsLegal.compose_last_window`, `MarkedInner.origin_ends_mixed`,
  `MarkedInner.IsLegalNonempty.windows_determine`, `span_compose` (`lem:gluing-local` (3));
* `profM`, `profS`, `MarkedInner.IsLegalNonempty.mixed_profile` (`eq:gluing-profile`,
  `eq:gluing-mixed-profile`);
* `MarkedInner.IsLegal.injective_compose` (fixed-chart injectivity).

The coding of the boundary words, `lem:gluing-coding`, is in `SkewGluing.Coding`.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

/-! ### Checked examples -/

/-- The singleton case-(d) hook mark: legal, with phases `s = 1`, `t = 0`. -/
example : hookInner.IsLegal := by decide

/-- `(3) ∘_ω (2, 1)` and `(2, 2) ∘_ω (2, 1)` are connected skew (the paper's sharpness example). -/
example : IsConnectedSkew (compose (skewOf [3] []) hookInner) := by decide +kernel
example : IsConnectedSkew (compose (skewOf [2, 2] []) hookInner) := by decide +kernel

/-- The chart figure: the composite with the domino is connected skew of span `r q + w = 8`. -/
example : IsConnectedSkew (compose domino chartFigureInner) := by decide +kernel

/-- The first window of `(3) ∘_ω (2, 1)` is the first window of the hook `(2, 1)`, placed at the
origin of the southwest cell of the row `(3)`. -/
example : ((compose (skewOf [3] []) hookInner).filter fun x =>
      content x ≤ minContent hookInner.E + minContent (skewOf [3] []) * hookInner.period +
        hookInner.period - 1) =
    translate (hookInner.origin (skewOf [3] []) (sw (skewOf [3] [])))
      (hookInner.E.filter fun y => content y ≤ minContent hookInner.E + hookInner.period - 1) := by
  decide +kernel

/-- The last window of `(3) ∘_ω (2, 1)`: the diagonals `[w, q + w - 1]` of the hook, placed at the
origin of the northeast cell of the row `(3)`. -/
example : ((compose (skewOf [3] []) hookInner).filter fun x =>
      minContent hookInner.E + maxContent (skewOf [3] []) * hookInner.period + hookInner.width ≤
        content x) =
    translate (hookInner.origin (skewOf [3] []) (ne (skewOf [3] [])))
      (hookInner.E.filter fun y => minContent hookInner.E + hookInner.width ≤ content y) := by
  decide +kernel

end SkewGluing
