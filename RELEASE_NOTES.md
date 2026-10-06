# Release notes

## v0.2.0 — Lean formalization acceptance contract

The candidate source tree contains the full original theorem in Lean, including arbitrary local Hilbert spaces and normalized positive states, local tensor-product five-outcome POVMs, the largest sextic root, the bounded commuting-PVM SOS identity, and explicit full25-dimensional attainment. Canonical v0.1.1 data and handoff remain unchanged. Concurrent current-main prior-work attribution/PDF maintenance is preserved separately in `docs/CURRENT_MAIN_EDITORIAL_INTEGRATION.json`; every manuscript TeX byte outside that explicit bibliography paragraph is unchanged.

The validated baseline, commit `67e0426166c622a63e7daae554560e1ece16a3ba` and tree `c1a5aa737f6bd7f04ea2bc2c22424dd53bcea281`, has completion evidence for 985 production-module builds, 835 exact declaration inspections, genuine fresh-environment kernel replay and required controls. One formal blind semantic/source audit round passed. Round 2 was cancelled before completion; Round 3 was not performed. The 6 October 2026 [release contract](RELEASE_v0.2.0.md) requires byte-identical proof-critical payload, valid workflows, actual lightweight remote release CI on the final commit, annotated publication and verification of every release asset's GitHub API name, uploaded state, exact size and usable SHA-256 digest against frozen local metadata, with the exact asset count. Full redownload is conditional on a concrete integrity concern; one small public-route download is optional. The default release CI checks workflow/configuration execution, static integrity, manifests, packaging/release infrastructure and payload correspondence to preserved mathematical evidence, without repeating the full clean build or kernel replay. Release-layer changes have separate final-commit receipts and are not attributed to the baseline audit. This section does not predeclare CI or publication success.

The v0.1.1 and v0.1.0 sections below preserve their historical scope.

## v0.1.1 — 2026-10-04

Additive manuscript and non-load-bearing Phase-B hardening release. The central theorem, exact root polynomial, certificate coefficients and attaining strategy are unchanged.

- Publication manuscript: `paper/main.tex`, verified bibliography, compiled/visually inspected PDF and clean build instructions.
- Strict shared schema and mathematical-entrypoint boundaries in `artifact_v0.1.1/`; metadata/target/source binding and normal-Python replay guard.
- Correct same-fixed-embedding POVM exposition, coefficient-ring versus actual embedding distinction, and honest historical evidence errata.
- Fresh source-bound R01–R14 regression acceptance evidence; failed attempts and subsequent corrected reruns remain visible.
- Substantive Codex repository coauthor trailers, distinct from academic authorship.
- Frozen `artifact_v0.1/`, original audit materials and annotated `v0.1.0` remain unchanged. Immutable complete Phase-B archive is a release asset, SHA-256 `12e2864ed19d99500b72d4aefe6e2b27939fb67c05aa355b38b997456a55fc43`.

See `verification/release_gate.json` for actual gate statuses and source/receipt hashes, `docs/PHASE_B_ERRATA.md` for evidence scope and `docs/PROVENANCE.md` for packaging. The remote release has its own post-publication verification receipt; local receipts alone do not establish remote publication.

No Lean formalization, human peer review, uniqueness/self-testing theorem or arbitrary-outcome theorem is claimed. The later completed Lean milestone is reserved for **v0.2.0**.

## v0.1.0 — 2026-10-04

First public archival release of the CGLMP5 exact-value proof candidate.

### Scientific claim

For the standard five-outcome CGLMP Bell functional with local bound 2, the candidate proves

\[
\sup I_5=\mu,
\]

for arbitrary local Hilbert-space dimensions and arbitrary local five-outcome POVMs, where \(\mu\) is the largest real root of

\[
5\mu^6-65\mu^4+144\mu^2+96\mu+16=0.
\]

The upper bound is supported by an exact 14-term positive noncommutative SOS certificate, and a five-dimensional strategy attains equality.

### Frozen baseline

`artifact_v0.1/` reproduces the content of the pre-publication frozen archive without scientific modification.

- `CGLMP5_v0.1_C001.zip`
- SHA-256: `4940510ce8f7325b21f36515ce853942396fd119a7ea1a24fba3ceddc1dffd45`
- Size: 2,309,383 bytes

### Additive post-freeze audit

A later independent AI adversarial audit is included under `audits/web6pro_2026-10-04/` and as a separate release asset.

- `CGLMP5_independent_audit_results.zip`
- SHA-256: `e69679a00fb8bb92b69459b5a365d3e1c5200c8ab3709854bec700e1754c25fd`

That audit wrote two exact implementations using different scalar representations and Bell-target reconstruction paths, and reported no load-bearing defect in the attacks completed. It is not described as an exhaustive proof or independent human review.

### Verification status at release

Completed evidence includes exact core replays, separated-context adversarial audits, negative controls/mutation tests, a restricted-input lower-bound reconstruction, clean-extraction replay of the frozen archive, and the post-freeze exact adversarial reimplementation.

Not completed at v0.1.0: Lean/proof-assistant formalization, complete unguided rediscovery of the full SOS upper bound, independent human expert validation, or journal peer review.

### Versioning rule

The `v0.1.0` tag is intended to remain immutable. Later formalization or scientific changes belong in subsequent tags/releases.
