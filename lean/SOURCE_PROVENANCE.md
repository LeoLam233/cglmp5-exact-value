# Canonical source binding (development record)

The immutable scientific input is `artifact_v0.1.1/SOS14.json`, SHA-256
`1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2` (581,335 bytes).
The other three frozen JSON files remain unchanged and their handoff hashes are
recorded in the bootstrap freeze receipt. The compact fourteen-term certificate
is the primary formal route; auxiliary Gram/LDL files are not substitute axioms.

## Two separate checks

1. `scripts/check_source_chunks.py` independently reads the actual emitted Lean
   source fragments, reconstructs every original decimal string, weight,
   coefficient and ordered word record, checks the exact metadata prefix and
   reconstructs the complete original JSON bytes. It records
   `SOURCE_CHUNKS_READBACK.json`. This is input authentication, not a proof oracle.
2. Lean's total `DecimalChunks` parser checks the ASCII decimal digits of each
   at-most-nine-character fragment and reconstructs exact `Int`/`Nat` values by
   positional arithmetic. Per-scalar decoding theorems compose into
   `CertificateSource.canonical_source_decode`. Generic partition-invariance proofs
   in `SourceDecimalSoundness` show this equals parsing the uninterrupted original
   decimal strings; `CertificateSource.canonical_text_decode` exposes that stronger
   conclusion. The resulting typed values are
   exactly the `rawTerms` consumed by `CanonicalData`, the scalar evaluator,
   weight positivity, and the noncommutative SOS identity. Source labels are
   linked to ordered generator evaluation by `SourceWordBridge`.

The canonical header is rendered from checked numeric chunks, not an opaque
literal numeric prefix. `CertificateHeaderProofs` checks the five gamma scalars
and all endpoints of the three original embedding boxes, both as chunks and as
uninterrupted decimal strings. `AttainmentSourceHeader` links the parsed header
gamma through the actual scalar embedding to the physical Schmidt amplitudes.
The remaining metadata lines are preserved byte for byte. The independent reader
also checks these header fields against the frozen source JSON.

No floating conversion is used. Negative signs and denominators have explicit
parsing rules; invalid or empty fragments fail. Positive denominator and word
bounds are separately kernel checked. Separately, `scripts/check_lean_source_bytes.py` independently executes
the actual Lean-defined `canonicalSourceBytes` and compares every output byte with
the canonical JSON, recording `LEAN_SOURCE_BYTES_READBACK.json`. This is an IO
readback check, never a proof oracle.

The source-fragment partition is
lossless: `DecimalChunks.text` concatenates original literal fragments, without
reformatting their numerical values.

The independent reader refuses optimized Python execution, so its assertions
cannot be disabled silently. `scripts/test_source_readback.py` verifies the clean
readback and rejects changed canonical bytes, gamma fragments, source labels and
header linkage. These are provenance-tool controls, not mathematical proofs.
The separate `run_lean_source_binding_corruption.py` recompiles a valid changed
coefficient with unchanged canonical text, requiring the kernel decoder itself
to prove its equality false. It preserves actual original and mutated compile
inputs and refuses to count resource or import failures as successful rejection.
A different arithmetic corruption control tests the actual SOS residual path.

The finite SOS arithmetic and strict positivity are independently checked in
Lean; Python emits data and proposed witnesses, never a trusted theorem. All
computational proofs use the kernel, not `native_decide` or an external evaluator.

## Resource history

Whole-string rendering and later whole-scalar UTF-8 decoding exhausted memory.
Those failed states and logs remain in the recovery evidence. The final source
representation uses small literal decimal fragments to avoid constructing large
UTF-8 buffers in the kernel. This changes proof engineering only, not an input
byte, coefficient, target, or mathematical assumption.

This file describes the design. Completion is only established by the final
whole-tree build, source readback, axiom audit, and release receipts; none is
asserted by this development note alone.
