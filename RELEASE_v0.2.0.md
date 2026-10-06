# v0.2.0 acceptance and receipt contract

This is the release contract authorized on 6 October 2026. It replaces the earlier
requirement for three completed audits on an identical final Git tree. It permits
non-proof release, infrastructure and documentation changes while preserving the
validated proof-critical payload. It is not itself an execution receipt or proof
of final remote CI or publication.

## Fixed theorem

The scientific target remains the v0.1.1 manuscript and handoff: the standard
five-outcome CGLMP functional has local bound 2 and exact quantum maximum equal to
the largest real root of `5*x^6 - 65*x^4 + 144*x^2 + 96*x + 16`. The quantum set
allows arbitrary local complex Hilbert spaces, including nonseparable spaces,
arbitrary local tensor-product five-outcome POVMs, and every normalized positive
state. The maximum is attained by the explicit C^5 tensor C^5 Fourier strategy.
The bounded cross-party commuting PVM SOS identity is a separate theorem root.
See `STATEMENT_ALIGNMENT.md` and `SOURCE_MAP.md` for the exact declarations.

## Validated baseline and actual audit history

The validated baseline is:

- Commit: `67e0426166c622a63e7daae554560e1ece16a3ba`
- Git tree: `c1a5aa737f6bd7f04ea2bc2c22424dd53bcea281`
- Baseline source-manifest SHA-256:
  `3d285fbbcbcaabe946113046d7a4ed1cf4c7679baf61466a28a97f3dbd603370`

Its completion entry gate records 985 production-module builds, 835 inspected
declarations, exact source binding, genuine official fresh-environment kernel
replay and required controls. The 40-stage accepted evidence is explicitly a
composite: 35 successful original stages, a separate successful
`lake env leanchecker --fresh CGLMP5` invocation, and four completed controls.
The original session with no terminal result and the watchdog-stopped attempt
remain preserved and are not counted as successful replay executions.

One formal blind semantic/source audit round passed on this baseline at
`2026-10-05T20:06:06.547451+00:00`. It used four newly initialized auditors and a
continuing coordinator. Its scope and limitations are in the preserved Round 1
report and adjudication. The evidence records have these SHA-256 values:

- `audits/shared/ENTRY_GATE.json`:
  `d8e37b6b057909fa1ff36e0172d8218b60d6d9cb5ba6b2ff15d2a2d92fbfc1b4`
- `audits/round-1/ROUND_RECORD.json`:
  `5c8be49b32075319faa7de5511af4a9a086cd26e053d84ee7739590587d9f80e`
- `audits/round-1/REPORT.md`:
  `09a27300fe926c7389b3ef1689ac4191d15992f28eddb54d99d9eef92ce14374`
- `audits/round-1/COORDINATOR_ADJUDICATION.json`:
  `5ff62dc45266f77f5e6b86cd42030e6d53331fdbb627991314dd52607753c9ab`

These are paths within the preserved evidence, rather than claims that those
records are part of this source tree. Round 2 was cancelled by the release author
at 00:39 UTC on 6 October 2026, after 812 of 985 independent module recompilations;
there is no Round 2 PASS. Round 3 was not performed. Earlier three-round audit
results on the superseded candidate are historical only. Statements in preserved
reports that Round 2 and Round 3 remain required describe the former contract.
They are not current release prerequisites.

## Final acceptance gates

A release is accepted only if its separately hashed receipts establish all of:

1. **Unchanged proof-critical payload.** The complete payload inventory in
   `verification/final_payload_manifest.json` must match baseline Git objects and
   the final tracked files byte for byte. `scripts/check_release_payload.py`
   produces the external `FINAL_PAYLOAD_CHECK.json` result. Coverage includes all
   production Lean sources, generated proof/data witnesses, canonical artifact
   trees and scientific inputs, Lean/toolchain/dependency configuration, and
   machine-readable declaration inventories. Omissions or new proof-critical
   paths must fail. Every allowed release-layer difference must be enumerated.
2. **Valid infrastructure and proof boundary.** Every workflow configuration must
   be valid. The final source manifest, pinned scientific inputs and forbidden
   proof-escape scan must pass. No project axiom, `sorry`, `admit`, proof-critical
   `unsafe`, `native_decide`, or substitute theorem may enter the accepted proof.
3. **Real final-commit remote CI.** The latest completed main-push runs of both
   `verify.yml` and `lean-verification.yml` must succeed on the exact final
   integrated commit. Workflow definitions, local checks, runs on older commits
   and incomplete runs do not satisfy this gate. The final Git tree is recorded
   separately from the baseline tree and payload digest.
4. **Annotated publication.** Create the annotated `v0.2.0` tag on that exact
   commit and the formal GitHub Release. Existing immutable tags and releases
   must not be replaced. Record the tag object, peeled commit and release identity.
5. **Asset verification.** Upload the source, proof and acceptance assets,
   redownload them from the release and compare their SHA-256 values.
   A final remote-verification receipt
   binds the commit, final tree, annotated tag, CI run identities, release and
   downloaded assets to the baseline/payload correspondence and actual audit
   history.

Permitted release-layer-only changes do not require another local whole-project
build, kernel replay or audit sequence. They still require the final payload
comparison and real remote CI. A proof-critical difference fails this contract;
it cannot be reclassified as a documentation or packaging change. The final
entire Git tree is not described as having passed Round 1 or three audit rounds
when its release-layer bytes differ from the baseline.

## Manual publication boundary

The separate `release-v0.2.0.yml` workflow is dispatched only after the external
acceptance bundle has been inspected and its consistency checked. Its acceptance
SHA-256 input binds the verified bundle; a hash string alone does not prove
scientific or audit success. The workflow enforces the exact final commit/tree,
payload correspondence, preserved inputs, source manifest and latest successful
main-push CI. It refuses any existing tag or release, including a draft without a
tag. Tag/ref responses and gate receipts remain preserved if a later step fails.
Asset upload, formal publication and downloaded-byte verification require their
own successful records. No pending publication outcome is labelled PASS here.

## Trust and provenance

Generated data and Python programs propose or authenticate inputs; they do not
prove the scientific theorem. The finite source/evaluation/positivity/SOS and
operator/POVM/attainment arguments are kernel-visible Lean proofs. The final
source manifest excludes only its own bytes; baseline and publication receipts
retain separate hashes. The exact declared core-axiom sets, rather than a generic
“clean” label, are part of acceptance. Internal AI audits do not claim external
human peer review.

The frozen `artifact_v0.1`, `artifact_v0.1.1`, handoff and annotated v0.1.0/v0.1.1
history are retained without scientific rewriting. Current-paper bibliography/PDF
maintenance from commit `1e3282749c9fce2163aaeb8415d8936db88d43ad` is preserved
separately; `docs/CURRENT_MAIN_EDITORIAL_INTEGRATION.json` records the exact
prior-work paragraph replacement and confirms every other manuscript TeX byte
is unchanged from v0.1.1. The controlling mathematical target remains that tag.
Development experiments, failed proof/replay states and cancelled audit work are
preserved as recovery/history evidence and are not substituted for completed
acceptance gates. Existing backup evidence is retained, and recovery backups
remain ongoing preservation work outside the publication gates.
