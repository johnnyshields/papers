import Lake
open Lake DSL

package «turan-bessel» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib TuranBessel where
  globs := #[.andSubmodules `TuranBessel]
