# CGLMP5 independent adversarial audit outputs

Read `AUDIT_REPORT_ZH.md` for the verdict, mathematical findings, exact input locations, completed attacks, and limitations.

These are newly written audit implementations, not candidate-provided verifiers. No serialized success flag is used as proof.

## Run

Python 3.10 or newer; standard library only. Extract the original user-supplied package separately, then run:

```sh
python audit.py /path/to/CGLMP5_WEB6PRO_ADVERSARIAL_AUDIT_PACK_v2 --stage full
python crosscheck.py /path/to/CGLMP5_WEB6PRO_ADVERSARIAL_AUDIT_PACK_v2
python negative_controls.py /path/to/CGLMP5_WEB6PRO_ADVERSARIAL_AUDIT_PACK_v2
```

Do not run `crosscheck.py` with `-O`: it explicitly rejects optimized mode because it uses assertions.

`audit.py` and `crosscheck.py` are standalone from each other. `negative_controls.py` imports `audit.py` and launches `crosscheck.py` on a temporary intentionally corrupted copy. The original input is never modified.

## Contents

`audit.py`: exact cyclotomic/cubic arithmetic, event and root checks, two positivity evaluation paths, direct SOS and full Gram checks, complete physical measurement and attainment checks.

`crosscheck.py`: independently implemented radical-tower arithmetic, adjacent-word rewriting, inverse spectral-projector target, fresh 300-bisection root enclosures, exact SOS and strict weight bounds.

`negative_controls.py`: detects coefficient, word, sign, and final-edge phase corruptions.

The `*_results.json` and `*_run.log` files contain actual execution evidence. `environment.json` records the Python runtime. `OUTPUT_SHA256SUMS.txt` hashes the output files. The original input manifest hashes are recorded in `audit_results.json`.

The result is not formal verification or external peer review. No novelty or priority assessment was performed.
