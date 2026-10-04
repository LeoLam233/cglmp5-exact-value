# Provenance, frozen evidence and release boundaries

## Three distinct objects

1. **Frozen scientific baseline.** [`artifact_v0.1/`](../artifact_v0.1/) retains the original theorem, root polynomial, exact coefficient tables, physical strategy, proof notes and historical verifier sources. The public `v0.1.0` tag is not moved. Historical statements inside this directory are read in their original context.
2. **Frozen audit evidence.** [`audits/phase_b_2026-10-04/`](../audits/phase_b_2026-10-04/) contains byte-preserved controlling Phase-B documents, with `PRESERVED_SOURCE_MAP.json` recording their original archive paths and hashes. The complete immutable Phase-B archive additionally preserves A01–A07 and H01–H03, exploratory sources, unsuccessful/partial attempts, final sources and receipts. Those are historical evidence, not freshly executed v0.1.1 tests.
3. **Additive v0.1.1 hardening and manuscript.** [`artifact_v0.1.1/`](../artifact_v0.1.1/) supplies strict entrypoints and explicit theorem/metadata binding; [`paper/`](../paper/) supplies the standalone manuscript; [`verification/`](../verification/) supplies the new release gate. Fresh receipts identify actual source/input bytes, commands, runtime and semantic results. New wrappers do not retroactively make historical sources strict or historical reports accurate.

The release is `v0.1.1`. The later completed Lean-formalization milestone is reserved for `v0.2.0`; no Lean formalization is claimed here.

## Archive identities

Names below identify the supplied archive contents. A download service may add `(1)` to a filename without changing the archive bytes.

| Object | SHA-256 |
|---|---|
| `CGLMP5_PhaseB_checkpoint_20261004T092328Z_FINAL_COMPLETE.zip` | `12e2864ed19d99500b72d4aefe6e2b27939fb67c05aa355b38b997456a55fc43` |
| `CGLMP5_PHASE_B_FINAL_CORPUS_v2.0(1).zip` inside that checkpoint | `bf372b33162a8f04747fcd5bf2a5600f603800395ff47fd5e7a391b2848d2efe` |
| `CGLMP5_PHASE_A_INPUT_v1.2.zip` | `3bd0ac75d7658694b33addd33070a657cd394a3d8e3e11e3fa67d3db1b4e86b6` |
| `CGLMP5_v0.1_C001.zip` | `4940510ce8f7325b21f36515ce853942396fd119a7ea1a24fba3ceddc1dffd45` |
| `A01_5p6Sol_A1v2.zip` | `3af2ab6d3741540c2d73fb4b225fe1d152a3442ffc37a8fc692fe165c3e36f96` |
| `A02_5p6Sol_ExternalPrompt.zip` | `ff1173e8c5cefa0be5e5ab8c4a8a3bd5c6a17b7bc50670551cbaff296d6125b4` |
| `A03_6Pro_A1v2.zip` | `42eca59eaab55534c717db636b7fb5d2fe362700a3db02b468bc1d1ecec8cf76` |
| `A04_6Pro_ExternalPrompt.zip` | `a4833d0e2876c767af6998811615d8475243edea308f47d7d8b4715adc474386` |
| `A05_Dot_Blind.zip` | `d316ae4abb2e462980904e939ecb763799dc5b1aa31f4968dbcadd988920c659` |
| `A06_DS_V4p1_Flash_ExternalPrompt.zip` | `fb03753b5dba5b85c158c178281dae3bc5ca822f64a85698a8ba5919998f026d` |
| `A07_SpaceBunny_ExternalPrompt.zip` | `bb369236dbe05dc3b49f74c275b3aa0b2ab79c586ceb88c41f201b6d9e2f2b6b` |
| `H01_Web6Pro_independent_audit.zip` | `e69679a00fb8bb92b69459b5a365d3e1c5200c8ab3709854bec700e1754c25fd` |

The Phase-A ZIPs occur inside `work/corpus/CGLMP5_PHASE_B_FINAL/phase_a_audits/` in the Phase-B checkpoint. Their unchanged expanded trees occur under `work/expanded/`. The two frozen baseline ZIPs occur inside `work/corpus/CGLMP5_PHASE_B_FINAL/frozen_baseline/`. The historical sources occur inside `work/corpus/CGLMP5_PHASE_B_FINAL/historical_pre_phase_a/`.

The hash of an archive is a byte identity. It does not independently establish execution history, publication time, authorship, blind input exposure, system/model isolation or mathematical truth. Remote publication verification must separately bind the annotated tag, peeled commit, default branch, downloaded release assets and their digests.

## Git identity and immutable baseline

The release work began from repository commit `1f5a8972df15eb3cbccc6df0d7a12605a6aa25c9`. The frozen annotated `v0.1.0` tag object was `2cabffab133d6d10a91f9e3e37e2426468dcc719`, peeling to that same commit `1f5a8972df15eb3cbccc6df0d7a12605a6aa25c9`. Final `v0.1.1` tag/commit/remote asset identities belong to the release verification receipt and release notes, not to an unverified guess made before publication.

A comparison with the original tag and the original archive is required for the whole `artifact_v0.1/` tree. The new hardening directory does not silently replace frozen data. The four scientific JSON files remain exact byte copies; wrapper/document changes are kept separately identifiable.

## Manifest base directories and historical curation

- `artifact_v0.1/MANIFEST.sha256` is relative to `artifact_v0.1/` and describes that frozen snapshot.
- Repository-level release manifests are relative to the repository root unless they explicitly declare another base. A manifest excludes itself and any intentionally later-created remote receipt to avoid self-referential hashes; its documented scope is part of its meaning.
- A Phase-B path beginning `outputs/` or `work/` is relative to the **final Phase-B archive root**. Some original lane records instead use output-root-relative `RUN_RECEIPTS/`, `INDEPENDENT_CHECKS/` or `lanes/`; [`PHASE_B_ERRATA.md`](PHASE_B_ERRATA.md) resolves these explicitly.
- A05 branch manifests use their original audit archive root; checking them from a script subdirectory gives misleading failures.
- The baseline's historical nested reconstruction manifest is not a current outer manifest. Two original checksums differ from curated report/environment text. The retained original-to-curated map is `artifact_v0.1/verification/receipts/packaging_identity.json`; the historical nested list is `artifact_v0.1/verification/receipts/reconstruction/lower_worker/SHA256SUMS.txt`. Do not edit either to hide that history. See B-S32 and the Phase-B `outputs/lanes/schema/manifest_checks_resolved.json`.

A successful current outer-manifest check does not rewrite the semantics of an older nested checksum. Conversely, a historical original-to-curated mismatch already explained by that map is not evidence that the current outer bytes were silently corrupted.

## Exact theorem versus annotation

The enforced scientific target is the standard five-outcome, local-bound-2 CGLMP functional, with the eight event families and `k=0,1` weights stated in the manuscript and frozen proof. Its maximum is the largest real root in `(3,31/10)` of

`5 t^6 - 65 t^4 + 144 t^2 + 96 t + 16`.

The coefficient list `[5,0,-65,0,144,96,16]` uses **descending** powers. The table basis index is `a + 2b + 6c + 12e` for `s^a x^b u^c i^e`, where `s=+sqrt(5)`, `x=5 mu`, `u=+sqrt(10+2s)`, `a,c,e in {0,1}` and `b in {0,1,2}`. A checker must disclose which metadata fields it enforces and which it only hashes or reports.

Hash binding of proof prose establishes which document was supplied. It does not make arbitrary prose a machine-proved theorem. Cached PASS labels, discovery-stage status, stored word summaries and old positivity intervals are not authoritative substitutes for recomputation. A correct compact SOS authenticates its own represented coefficients; auxiliary E/H/L/D bytes require explicit linkage checks.

Frozen references to `exact_field.py` and `NOVELTY_AND_SCOPE_AUDIT.md` point to historical discovery/provenance material excluded from the reduced scientific payload. They are not missing mathematical premises: the displayed field relations, exact tables and actual-embedding argument suffice for the verification target. Historical claims that external audits or public release had not yet occurred are preserved in their original temporal context.

## Evidence ancestry and limits

The author compact, statement and full Gram checkers share arithmetic and normal-form code. H03 mutates that same engine. A01–A07 names and model/prompt labels do not prove independent source exposure or independent interpretation. The Phase-B coverage matrix separates implementation, parser, arithmetic, normal form, representation, physical-model and receipt dependencies node by node.

The 14 compact weights and the 14 Gram pivots are the same positive algebraic quantities. Distinct exact reimplementations and representation changes reduce particular implementation risks, but do not transform audit agreement into a vote that proves a theorem. Finite-field tests are exact in finite characteristic and do not prove real positivity. Finite numerical searches and SDP diagnostics do not prove a universal dimension-independent maximum. Rationally repaired physical representatives are distinct mathematical objects from raw invalid floating arrays.

This release does not claim absolute originality/priority clearance, self-testing, optimizer uniqueness, arbitrary outcome number, human peer review, proof-assistant verification or exhaustive software correctness. The mathematical claim remains an exact computer-assisted certificate with explicit analytic interfaces.

## Replay status and failure retention

A fresh successful run requires more than exit status zero: it must contain the expected complete semantic result and exact residual/positivity/physical checks. Optimized Python runs must fail closed when assertions are load-bearing. Wrong arguments, fixture construction errors, timeouts, incomplete output, stale receipts and explicit FAIL-with-exit-zero are not mathematical PASS results.

Keep original source and input digests, actual executed/adapted source digests, argv, working directory, versions, optimization flags, seeds where applicable, output digests and failure history. Label unchanged-source replay, path-adapted replay and newly implemented regression distinctly. The portable regression runner may stage unchanged archive trees to satisfy historical path layouts; this does not mean every exploratory historical script was replayed. [`PHASE_B_ERRATA.md`](PHASE_B_ERRATA.md) provides the full 110-row original-claim crosswalk and 138 distinct evidence paths.

## Attribution

Human manuscript author: **Dehao Lin**, ORCID **0009-0001-4551-8490**. AI assistance is disclosed in [`AUTHORSHIP.md`](../AUTHORSHIP.md) and the manuscript. The Git commit trailer `Co-authored-by: Codex <noreply@openai.com>` records repository contribution attribution; it is not academic authorship or independent peer review. A trailer alone is not proof that GitHub's Contributors view has indexed the contribution; that view requires separate remote verification.
