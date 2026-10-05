import Lean
open Lean Elab Command
elab "inject_fixture" : command => do
  liftCoreM <| addDecl (.thmDecl {
    name := `TrustFixture.claim
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro
  })
inject_fixture
