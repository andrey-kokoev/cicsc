import Lake
open Lake DSL

package cicscLean where
  moreServerArgs := #["-T", "200000"]

lean_lib Cicsc where
  globs := #[.submodules `Cicsc]
