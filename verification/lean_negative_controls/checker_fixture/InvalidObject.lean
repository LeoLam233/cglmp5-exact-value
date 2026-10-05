-- Deliberately invalid external-only object fixture. Never a production proof.
import Lean
open Lean Elab Command
set_option debug.skipKernelTC true
elab "inject_fixture" : command => do
  liftCoreM <| addDecl (.thmDecl {
    name := `TrustFixture.claim
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  })
inject_fixture
