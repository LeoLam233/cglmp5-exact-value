# CGLMP5 exact quantum value — Lean formalization

This repository preserves the **AI-assisted exact proof artifact** at v0.1.1 and supplies a Lean formalization of the same standard five-outcome CGLMP theorem. For arbitrary local Hilbert-space dimensions and arbitrary local tensor-product five-outcome POVMs,

\[
\sup I_5 = \mu,
\]

where \(\mu\) is the largest real root of

\[
5\mu^6-65\mu^4+144\mu^2+96\mu+16=0,
\]

numerically

```text
3.015710475522673285523983801961043281714038985152...
```

A five-dimensional bipartite strategy attains equality. The universal upper bound is carried by an exact 14-term positive noncommutative sum-of-squares certificate.

**Evidence and release scope.** The validated baseline is commit `67e0426166c622a63e7daae554560e1ece16a3ba`, tree `c1a5aa737f6bd7f04ea2bc2c22424dd53bcea281`: 985 production modules built, 835 declaration types/axiom sets inspected, genuine fresh-environment kernel replay and required controls completed, and one formal blind semantic/source audit round passed. Round 2 was cancelled before completion; Round 3 was not performed. The 6 October 2026 release contract permits release-layer changes while requiring byte-identical proof-critical payload, valid workflows, successful lightweight remote release CI on the final commit, and verified annotated publication and every asset's GitHub API name, uploaded state, size and SHA-256 digest matching frozen local metadata, with the exact asset count. Both required workflows must actually pass on the final commit; their release checks bind the unchanged proof payload to preserved mathematical evidence without repeating a full clean build or kernel replay. The final Git tree is distinguished from the audited baseline. See [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md) and [the acceptance contract](RELEASE_v0.2.0.md) for evidence scope and required receipts. Internal AI verification is not human peer review.

## Lean proof and replay

- [Complete theorem/source overview](FORMALIZATION_REPORT.md)
- [Published statement versus Lean](STATEMENT_ALIGNMENT.md)
- [Manuscript and exact-data source map](SOURCE_MAP.md)
- [Exact root/bridge axiom sets](AXIOM_AUDIT.md)
- [Pinned clean replay instructions](docs/LEAN_REPLAY.md)
- [v0.2.0 acceptance and receipt contract](RELEASE_v0.2.0.md)

The proof uses Lean 4.34.1 and pinned mathlib dependencies. The public module
`CGLMP5` imports the complete production tree, including independent semantic
controls. The original v0.1.1 scientific target is unchanged; no finite-dimensional,
projective-only, pure-state-only or numerical replacement is used.

The historical v0.1.1 checks listed below remain useful provenance. They do not
substitute for the Lean completion evidence, completed blind audit round, or final release gates.

## Start here

- [Formal manuscript (PDF)](paper/main.pdf), [LaTeX source](paper/main.tex), [build instructions](paper/README.md)
- [Hardened v0.1.1 artifact](artifact_v0.1.1/)
- [Phase-B adjudication](audits/phase_b_2026-10-04/FINAL_PHASE_B_REPORT.md) and [accepted revision plan](audits/phase_b_2026-10-04/CONSOLIDATED_REVISION_PLAN.md)
- [Appended evidence errata](docs/PHASE_B_ERRATA.md) and [provenance](docs/PROVENANCE.md)

- [Frozen v0.1 proof](artifact_v0.1/PROOF.md)
- [Root and algebraic embedding](artifact_v0.1/ROOT_EMBEDDING.md)
- [14-term exact SOS certificate](artifact_v0.1/SOS14.json)
- [Exact kernels](artifact_v0.1/EXACT_KERNELS.json)
- [Exact SOS / Gram data](artifact_v0.1/EXACT_SOS_CANDIDATE.json)
- [Positivity certificate](artifact_v0.1/POSITIVITY_CERTIFICATE.json)
- [Post-one-shot verification record](artifact_v0.1/verification/RECORD.md)
- [Independent Web 6 Pro adversarial audit](audits/web6pro_2026-10-04/AUDIT_REPORT_ZH.md)
- [Release notes](RELEASE_NOTES.md)

## Frozen scientific baseline

The directory [`artifact_v0.1/`](artifact_v0.1/) is the byte-preserved content of the privately frozen `CGLMP5_v0.1_C001.zip`. Its internal `MANIFEST.sha256` remains authoritative for that frozen snapshot. Historical wording inside that directory (for example, statements that the artifact had not yet been published) is intentionally preserved as part of the frozen record and should be read in its original pre-publication context.

Canonical frozen archive:

```text
CGLMP5_v0.1_C001.zip
SHA-256 4940510ce8f7325b21f36515ce853942396fd119a7ea1a24fba3ceddc1dffd45
```

The public GitHub release also carries a later, additive adversarial-audit archive:

```text
CGLMP5_independent_audit_results.zip
SHA-256 e69679a00fb8bb92b69459b5a365d3e1c5200c8ab3709854bec700e1754c25fd
```

The later audit does not modify the frozen scientific baseline.

## Reproduce the hardened checks

From the repository root, with normal CPython 3.12 or later:

```sh
set -euo pipefail
RECEIPTS="$(mktemp -d -t cglmp5-replay.XXXXXX)"
python3 -B artifact_v0.1.1/validate_integer_encoding.py --root artifact_v0.1.1 --output "$RECEIPTS/validate_integer_encoding.json"
python3 -B artifact_v0.1.1/verify_sos14.py --root artifact_v0.1.1 --output "$RECEIPTS/verify_sos14.json"
python3 -B artifact_v0.1.1/verify_independent.py --root artifact_v0.1.1 --output "$RECEIPTS/verify_independent.json"
python3 -B artifact_v0.1.1/verify_statement.py --root artifact_v0.1.1 --output "$RECEIPTS/verify_statement.json"
python3 scripts/check_core_results.py "$RECEIPTS"
# The recorded R01-R14 gate binds the old release's complete files, not v0.2.0.
test "$(git rev-parse refs/tags/v0.1.1)" = 54dc6cabee9b272dd35da736ef9a2208fc715bb8
test "$(git rev-parse 'refs/tags/v0.1.1^{commit}')" = 73b99dd22af68bd7a10927124d0b4ea7d6e8b78f
HISTORICAL="$(mktemp -d -t cglmp5-v011.XXXXXX)"
git archive 73b99dd22af68bd7a10927124d0b4ea7d6e8b78f | tar -x -C "$HISTORICAL"
(
  cd "$HISTORICAL"
  python3 -B scripts/test_release_gate.py
  python3 -B scripts/check_release_gate.py --root .
)
```

The first commands recompute the current canonical core identities and actual-embedding signs. The final block validates the packaged R01–R14 acceptance statuses and source/receipt hashes in an exact archive of the pinned v0.1.1 commit; it does not independently rerun every audit or bind the updated README, citation, source manifest, or editorial paper maintenance. Historical receipt hashes are not rewritten to describe newer files. The current printed-data check and the Lean release gates are separate checks of the current candidate. The full regression replay instructions are under [`verification/`](verification/). Do not run mathematical checkers with `-O`, `-OO`, or nonzero `PYTHONOPTIMIZE`. An exited process is insufficient: require the intended semantic result, and retain failed runs.

The strict input and canonical-format policies are documented in [`artifact_v0.1.1/SCHEMA.md`](artifact_v0.1.1/SCHEMA.md). A packaging rejection of a mathematically equivalent serialization is not a disproof of the represented identity.

## Reproduce the frozen checks (historical)

Use a working copy of `artifact_v0.1/` with CPython 3.12 or later:

```sh
python -B validate_integer_encoding.py --output encoding_current.json
python -B verify_sos14.py --output sos_current.json
python -B verify_independent.py --output gram_current.json
python -B verify_statement.py --output statement_current.json
python -B kill_tests.py
```

The frozen verification record documents the scope and limitations of each check. Hash agreement authenticates bytes; it does not by itself establish mathematical truth.

## Independent adversarial audit

The post-freeze audit in [`audits/web6pro_2026-10-04/`](audits/web6pro_2026-10-04/) rebuilt the load-bearing verification in two exact implementations. Among other checks, it reconstructed the Bell target from the original probability coefficients, preserved same-party noncommutation, verified the SOS identity and positive weights exactly, checked the Gram/LDL bridge, checked the arbitrary-dimension/POVM argument, and verified the full 25-dimensional attaining eigenvector relation. The audit verdict was `SURVIVED ADVERSARIAL AUDIT`, explicitly limited to the attacks actually performed.

## Novelty and scope

The claimed new contribution is the complete exact certificate and its bridge to the dimension-independent five-outcome quantum bound. The numerical optimum, Fourier measurement family, and candidate nonmaximally entangled strategy have prior numerical/structural antecedents. The v0.1 verification record contains the bounded prior-art search used before release. No claim of absolute priority is made.

This repository concerns the **five-outcome** CGLMP case only. It does not claim the corresponding result for arbitrary outcome number, uniqueness/self-testing of the optimizer, or a general closed form for CGLMP maxima.

## Authorship and AI use

Author: **Dehao Lin**, School of Physics, Sun Yat-sen University, Guangzhou, China. ORCID: **0009-0001-4551-8490**.

The research and verification workflow was AI-assisted. AI systems are not listed as authors. The human author is responsible for the public release and for the claims made in this repository. See [AUTHORSHIP.md](AUTHORSHIP.md).

## Versioning

`v0.1.0` is the first public archival release of the frozen candidate and its accumulated verification evidence. The frozen scientific baseline is not rewritten after publication. Future formalization or scientific corrections will be released as later versions rather than by moving or replacing the `v0.1.0` tag.

`v0.1.1` adds the publication manuscript, accepted non-load-bearing Phase-B hardening, and source-bound regression evidence. It leaves the theorem, root polynomial, certificate coefficients, attaining strategy, `artifact_v0.1/`, and the existing `v0.1.0` tag unchanged.

At the historical **v0.1.1** release, Lean formalization had not started. The completed Lean milestone belongs to **v0.2.0** under the preserved-payload acceptance requirements described above. The [frozen Lean handoff](docs/LEAN_HANDOFF.md) records the original formalization contract.

## v0.1.1 evidence discipline

Phase B reported `SURVIVED_MULTI_AUDIT_CORRELATED_FAILURE_ATTACK`, with revision class `NONLOAD_BEARING_HARDENING_ONLY`. Its immutable complete archive is distributed separately as a release asset:

```text
CGLMP5_PhaseB_checkpoint_20261004T092328Z_FINAL_COMPLETE.zip
SHA-256 12e2864ed19d99500b72d4aefe6e2b27939fb67c05aa355b38b997456a55fc43
```

The selected controlling reports under `audits/phase_b_2026-10-04/` retain their original bytes. Their statements describe the Phase-B run; they are not receipts for executions in this release. Fresh release checks and preserved failed attempts live under `verification/`. Each receipt must be interpreted according to the specific source, input hashes, command, and semantic result it records. Agreement among audits is not a substitute for the algebraic identity, actual strict positivity, and analytic representation/POVM proof.

The local POVM bridge uses one fixed embedding for both settings on each party and preserves every joint effect by compression. Compression is not asserted to be multiplicative. The theorem is about the local tensor-product, five-outcome model, with no dimension cutoff.

Repository commits credit substantive AI-assisted code and manuscript work using `Co-authored-by: Codex <noreply@openai.com>`. This software contribution attribution does not make an AI system a manuscript author.
