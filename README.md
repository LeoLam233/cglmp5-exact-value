# CGLMP5 exact quantum value — proof-carrying candidate v0.1

This repository archives an **AI-assisted exact proof candidate** for the standard five-outcome CGLMP Bell inequality. The claimed theorem is that, for arbitrary local Hilbert-space dimensions and arbitrary local five-outcome POVMs,

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

**Status.** The candidate has undergone exact replay, separated-context AI adversarial audits, mutation tests, a restricted-input reconstruction of the attaining lower-bound branch, and a later independent adversarial audit that reimplemented the load-bearing exact checks in two algebraic representations. No load-bearing defect has been found in the checks completed so far. This is **not** a claim of human peer review, formal verification, or exhaustive mathematical certification.

## Start here

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

## Reproduce the frozen checks

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

A Lean formalization is planned for a subsequent release.
