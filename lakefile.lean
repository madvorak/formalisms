import Lake
open Lake DSL

package formalisms {
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩, ⟨`linter.oldObtain, false⟩]
}

require "leanprover-community" / "mathlib" @ git "master"

@[default_target]
lean_lib Formalisms {
  globs := #[.submodules `Formalisms]
}
