# Release notes

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
