import Lake
open Lake DSL

package «forgacs-tran» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib ForgacsTran where
  globs := #[.andSubmodules `ForgacsTran]
