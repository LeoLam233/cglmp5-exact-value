# v0.2.0 acceptance and receipt contract

This file specifies the acceptance evidence for the candidate source tree. It is
not itself an execution receipt, an audit PASS, or proof of remote publication.

## Fixed theorem

The scientific target remains the v0.1.1 manuscript and handoff: the standard
five-outcome CGLMP functional has local bound 2 and exact quantum maximum equal to
the largest real root of `5*x^6 - 65*x^4 + 144*x^2 + 96*x + 16`. The quantum set
allows arbitrary local complex Hilbert spaces, including nonseparable spaces,
arbitrary local tensor-product five-outcome POVMs, and every normalized positive
state. The maximum is attained by the explicit C^5 tensor C^5 Fourier strategy.
The bounded cross-party commuting PVM SOS identity is a separate theorem root.
See `STATEMENT_ALIGNMENT.md` and `SOURCE_MAP.md` for the exact declarations.

## Acceptance evidence

A release is accepted only if its separately hashed receipts establish all of:

1. A clean relocated whole-production-tree build with pinned Lean, Lake,
   mathlib/dependency revisions and verified official runtime bytes.
2. Genuine fresh-environment kernel replay of the public umbrella, which imports
   every production module. Ordinary object import or an axiom list alone is not
   proof-object revalidation.
3. Complete printed types and exact axiom sets for all final roots and load-bearing
   bridges, agreeing with `AXIOM_AUDIT.md`; no forbidden project axiom or shortcut.
4. Canonical byte/source binding and reproducible generated witnesses, plus
   positive-baseline/destructive controls with inspected semantic failures.
5. Three sequential hostile audit reports: semantic/source correspondence;
   kernel/trust/relocated replay; and destructive reverse-dependency/correlated
   failure attacks. Each report identifies the same final Git tree. Historical
   failed attempts remain distinct; any source-tree change requires all three
   final passing rounds to be rerun on the new exact tree.
6. A verified restorable final backup and source/hash manifest.
7. Normal integration whose remote source tree equals the accepted tree, followed
   by successful CI on that integrated commit.
8. An annotated v0.2.0 tag/release, downloaded release assets with matching hashes,
   and a post-publication remote-verification receipt.

The source tree is frozen before these audit reports are produced. Reports and
replay receipts are external additive artifacts, so recording a result does not
change the audited tree. A commit ID may change through normal integration; the
accepted tree hash must remain identical.

## Manual publication boundary

The separate `release-v0.2.0.yml` workflow is dispatched only after the external
acceptance bundle has been inspected and its consistency checked. Its acceptance
SHA-256 input is an explicit attestation/binding to that verified bundle; the
workflow does not claim to infer scientific or audit success from a hash string.
It independently enforces the exact integrated commit/tree, preserved inputs,
source manifest and latest successful main-push CI. It refuses any existing tag
or release, including a draft without a tag. Tag/ref responses and gate receipts
are retained even if a later publication step fails, enabling inspection without
replacing immutable history. Asset upload, public publication and downloaded-byte
verification remain subsequent controlled steps.

## Trust and provenance

Generated data and Python programs propose or authenticate inputs; they do not
prove the scientific theorem. The finite source/evaluation/positivity/SOS and
operator/POVM/attainment arguments are kernel-visible Lean proofs. The source
manifest excludes only its own bytes; post-freeze receipts have separate hashes.
The exact declared core-axiom sets, rather than a generic “clean” label, are part
of acceptance. Internal AI audits do not claim external human peer review.

The frozen `artifact_v0.1`, `artifact_v0.1.1`, handoff and annotated v0.1.0/v0.1.1
history are retained without scientific rewriting. Current-paper bibliography/PDF
maintenance from commit `1e3282749c9fce2163aaeb8415d8936db88d43ad` is preserved
separately; `docs/CURRENT_MAIN_EDITORIAL_INTEGRATION.json` records the exact
prior-work paragraph replacement and confirms every other manuscript TeX byte
is unchanged from v0.1.1. The controlling mathematical target remains that tag. Development
experiments and failed proof/replay states are preserved in recovery evidence;
they are not substituted for accepted final receipts.
