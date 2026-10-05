# Attainment proof-construction history

This directory preserves intermediate work from the v0.2.0 development task. It is not an audit verdict and is not a mathematical premise.

- `column0_attempt01_timeout.lean.txt` and its `.log` preserve the first full 125-entry expansion route, which hit its Lean heartbeat limit. The successful route proves all off-diagonal entries by a general word-by-word invariance lemma and checks the 25 diagonal entries separately. No coordinate or physical scope was removed.
- `generators/` contains historical SymPy helpers used to propose exact polynomial `linear_combination` witnesses. The emitted cores were subsequently split and manually integrated into the production Lean modules. These are development snapshots, not current production regeneration commands. Do not run them from `lean/`: they would overwrite intermediate filenames used by the final integrated modules.
- The generators never serve as trusted arithmetic oracles. Every resulting identity is checked by ordinary Lean ring arithmetic and explicit actual-scalar relations. The final Lean sources are sufficient to replay the proofs without Python or SymPy.
- The canonical Schmidt numerator lists are independently linked through `AttainmentSource.canonical_gamma` to `CanonicalData.gamma`, whose source binding is handled by the shared certificate-source modules.

The completed source map is `docs/LEAN_ATTAINMENT_SOURCE_MAP.md`. Whole-tree audit/release gates are managed separately; development success does not imply that those gates passed.
