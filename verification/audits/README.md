# Audit-receipt consistency protocol

This protocol validates **record consistency only** after the actual scientific
audits. It does not run an audit, judge a finding, establish intellectual
independence, or infer scientific correctness from JSON. No synthetic test
fixture is an audit record. Successful output is `CONSISTENT`, always with
`scientific_pass_inferred: false`.

The final acceptance decision still requires independent inspection of the actual
reports, attacks, findings and underlying scientific evidence under the
[external acceptance receipt contract](../../FORMALIZATION_REPORT.md#external-acceptance-receipt-contract).

## Invocation and evidence location

```sh
python -B scripts/check_audit_receipts.py \
  --tree EXACT_FROZEN_GIT_TREE \
  --receipts /absolute/external/audit-bundle/index.json \
  --output /absolute/external/audit-consistency-new.json
```

The supplied tree must be the candidate's lowercase 40-hex Git tree identity,
obtained independently from Git. The checker compares every receipt with that
supplied identity; it does not prove that a report's account of its work is true.
The index and output must be outside the candidate repository. Output files must
be new, preserving previous failed attempts. Outputs cannot replace the index or
any referenced artifact. The checker never edits the candidate.

Every artifact reference has exactly `path` and `sha256`. Paths are portable
relative paths below the index's directory. Absolute paths, empty components,
`.`/`..`, backslashes, symlinks, missing files and candidate-tree artifacts are
rejected. Digests are lowercase SHA256 values over exact bytes. The index and
artifacts are rehashed after validation to detect changes during the check.

## Index and round records

The structural schema is [receipt.schema.json](receipt.schema.json). The executable
checker additionally enforces chronology, distinct coverage, hashes, containment
and fresh-route evidence. Unknown fields and duplicate JSON keys are rejected.

The index has:

- `format_version`: 1
- `git_tree`: the supplied frozen tree
- `rounds`: exactly three records, numbered 1, 2, 3 in that order

Each round has `round`, `status`, `git_tree`, `started_utc`, `finished_utc`,
`report`, `workers`, and `findings`. Status must be `PASS`. A round's report is a
SHA-bound artifact. Times use explicit UTC ISO timestamps, ending in `Z` or
`+00:00`, with at most six fractional digits. Start precedes finish, finish is not
in the future, and successive round intervals cannot overlap or run backward.
Shared endpoint timestamps are allowed.

`workers` contains exactly five records with distinct nonempty `worker_id` values.
Each has `coverage` (nonempty scope text), `status: PASS`, `started_utc`,
`finished_utc`, `report`, `attacks` and `findings`. Every worker interval must lie
inside its round. Workers may run in parallel. Each worker has a separate hashed
report and at least one hashed attack artifact. Report paths cannot be reused
for multiple coverage records. The checker does not interpret whether coverage
text actually satisfies the scientific audit plan; that is a review obligation.

Every round and worker supplies an explicit `findings` array, possibly empty.
Each finding has exactly `id`, `actionable`, `resolved`, `resolution`, and
`evidence`. Finding IDs are distinct within each list. The two flags are booleans.
Every actionable finding must be resolved, with nonempty resolution text and at
least one SHA-bound resolution artifact. Nonactionable observations may remain
recorded without a resolution. Merely changing a classification in JSON does not
scientifically resolve a finding; reviewers must inspect the report and evidence.

## Required round-3 fresh-route pass

Only round 3 additionally requires `fresh_route_pass` with:

- `status: PASS`
- `initial_attacks_finished_utc`
- `started_utc` and `finished_utc`
- a separate SHA-bound `report`
- a nonempty array of SHA-bound `attacks`
- an explicit `findings` array under the same resolution rules

The fresh-route interval must lie within round 3 and begin at or after its
recorded initial-attack finish. Initial attacks must occur after the round starts.
Worker coverage intervals may span both phases. Fresh-route report/attack paths
and exact byte hashes cannot repeat prior-round or initial-stage evidence, nor
duplicate one another. This rules out exact reuse or renaming of old files; it
does **not** prove a new scientific route was genuinely attempted. That explicit
fresh-route record and its evidence require scientific review.

## Tests and outcome

Run `python -B scripts/test_audit_receipts.py`. All fixtures are explicitly
synthetic and temporary. Negative cases include omitted/extra rounds, inconsistent
trees, missing/duplicate worker coverage, non-PASS states, unresolved findings,
overlapping/out-of-order or uncontained times, altered/missing evidence,
traversal/symlinks, absent or reused fresh-route evidence, malformed JSON fields,
and attempts to overwrite the candidate or prior receipts.

Exit 0 means only `CONSISTENT`; exit 1 means `INCONSISTENT`. CLI/path errors also
exit nonzero. The result lists exact observed artifact digests and all detected
consistency errors. Neither exit 0 nor three JSON `PASS` strings are a scientific
audit verdict or publication authorization.
