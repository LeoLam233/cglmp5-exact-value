"""Fail-closed classification of controlled Lean proof failures, not scientific inference."""
import hashlib
import re
from pathlib import Path

BLOCKED_MARKERS = (
    'maximum recursion', 'deep recursion', 'heartbeats', 'out of memory',
    'memory exhausted', 'memory allocation failed', 'bad_alloc', 'stack overflow',
    'segmentation fault', 'interrupted', 'timeout', 'timed out',
    'unknown module', 'unknown identifier', 'unknown constant', 'unknown tactic',
    'object file', 'failed to import', 'invalid header', 'no such file',
    'failed to synthesize', 'typeclass instance problem is stuck',
    'permission denied', 'no space left', 'failed to open', 'cannot open',
    'unexpected token', 'unexpected identifier', 'unexpected end of input',
    'unterminated', 'invalid syntax', 'parser error', 'unknown option',
    'unrecognized option', 'uncaught exception', 'internal error', 'panic at',
)
HEADER = re.compile(r'^(?P<file>.+\.lean):(?P<line>\d+):(?P<column>\d+): error: (?P<summary>.*)$')

FIXTURE_KINDS = {
    'attainment_corrupted_normalized_schmidt': ('unsolved_goals',),
    'attainment_diagonal_surrogate': ('unsolved_goals',),
    'attainment_wrong_fourier_offset': ('unsolved_goals',),
    'compressed_only_attainment': ('unsolved_goals',),
    'compression_homomorphism': ('rfl_mismatch',),
    'proper_isometry_surjective': ('type_mismatch',),
    'same_party_commutation': ('decide_false',),
    'setting_dependent_embedding': ('type_mismatch',),
    'wrong_event_shift': ('decide_false',),
    'wrong_root_branch': ('linarith_failure',),
    'wrong_weight_sign': ('linarith_failure',),
}
SOURCE_KINDS = {
    'event_shift': ('decide_false',),
    'same_party_order': ('unsolved_goals',),
    'root_embedding_sign': ('type_mismatch',),
    'weight_sign': ('type_mismatch', 'application_type_mismatch'),
    'setting_dependent_J': ('change_mismatch', 'type_mismatch'),
}

def diagnostic_kind(summary, body):
    if summary.startswith('Tactic `decide` proved that the proposition') and any(
            line.strip() == 'is false' for line in body.splitlines()):
        return 'decide_false'
    if summary == 'unsolved goals' and '⊢' in body:
        return 'unsolved_goals'
    if summary.startswith('linarith failed to find a contradiction') and '⊢ False' in body:
        return 'linarith_failure'
    if summary.startswith('Tactic `rfl` failed:') and 'is not definitionally equal' in body:
        return 'rfl_mismatch'
    if summary.startswith("'change' tactic failed,") and 'is not definitionally equal to target' in body:
        return 'change_mismatch'
    if summary == 'Type mismatch' and 'has type' in body and 'expected' in body:
        return 'type_mismatch'
    if summary.startswith('Application type mismatch:') and 'has type' in body and 'expected' in body:
        return 'application_type_mismatch'
    return None

def classify_rejection(log, exit_code, source_name, allowed_kinds, *,
                       timed_out=False, expected_count=None):
    lines = log.splitlines()
    markers = [marker for marker in BLOCKED_MARKERS if marker in log.lower()]
    starts = [(i, HEADER.fullmatch(line)) for i, line in enumerate(lines)]
    starts = [(i, match) for i, match in starts if match is not None]
    parsed_lines = {i for i, _ in starts}
    unparsed = [line for i, line in enumerate(lines) if 'error:' in line.lower() and i not in parsed_lines]
    diagnostics = []
    for j, (i, match) in enumerate(starts):
        end = starts[j+1][0] if j+1 < len(starts) else len(lines)
        body = '\n'.join(lines[i+1:end])
        diagnostics.append(dict(file=match['file'], line=int(match['line']),
            column=int(match['column']), summary=match['summary'], body=body,
            kind=diagnostic_kind(match['summary'], body)))
    reasons = []
    if exit_code != 1: reasons.append('Expected ordinary Lean proof-failure exit1')
    if timed_out: reasons.append('Timed out')
    if markers: reasons.append('Resource/parser/import/infrastructure diagnostic present')
    if unparsed: reasons.append('Unparsed error diagnostic present')
    if not diagnostics: reasons.append('No structured proof-failure diagnostic')
    if expected_count is not None and len(diagnostics) != expected_count:
        reasons.append('Unexpected number of proof-failure diagnostics')
    if any(Path(d['file']).name != source_name for d in diagnostics):
        reasons.append('Diagnostic arose outside the expected mutated proof file')
    if any(d['kind'] not in allowed_kinds for d in diagnostics):
        reasons.append('Unexpected or unrecognized proof-failure kind')
    return dict(accepted=not reasons, reasons=reasons, blocked_markers=markers,
                unparsed_error_lines=unparsed, diagnostics=diagnostics,
                expected_source=source_name, expected_kinds=list(allowed_kinds),
                expected_count=expected_count, exit_code=exit_code, timeout=timed_out,
                raw_log_sha256=hashlib.sha256(log.encode()).hexdigest(),
                scope='Expected proof-check failure only; not an independent proof of scientific correctness.')
