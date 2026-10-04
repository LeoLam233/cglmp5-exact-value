# Environment, exposure, and command receipt

Runtime actually used: python.

Python version: 3.12.14 (main, Aug 25 2026, 14:01:42), MSC v.1944 64 bit (AMD64). Platform: Windows-11-10.0.26300-SP0. NumPy: 2.3.5. SciPy, SymPy, and mpmath were absent. Shell: PowerShell. Cwd for shell calls: <LOCAL_WORKSPACE>. Exact arithmetic uses Fraction and custom code; no CAS or candidate-specific library.

Reproduction from any directory (Python 3.12 plus NumPy):

    python path/to/lower_worker/reconstruct.py

The script defaults to the exposure copy and output directory beside itself. For explicit paths:

    python path/to/reconstruct.py --input path/to/TARGET.exposed.md --output path/to/receipt-output

All newly created files and directories were under <LOCAL_POST_VERIFICATION>/receipts/reconstruction/lower_worker. No files outside that output subtree were edited. The original TARGET.md was read; an identical exposure copy was made only into the output subtree. Other shell content reads were only of the generated checks.json and selected lines of generated exact_computation.log.

Executed shell operations, in order (patch-tool edits are recorded by their resulting source/report files):

1. Get-Content -LiteralPath '<LOCAL_POST_VERIFICATION>\reconstruction_view\TARGET.md' -Raw.
2. New-Item -ItemType Directory -Force -Path '<LOCAL_POST_VERIFICATION>\receipts\reconstruction\lower_worker' | Select-Object FullName.
3. Get-FileHash -Algorithm SHA256 -LiteralPath '<LOCAL_POST_VERIFICATION>\reconstruction_view\TARGET.md'.
4. Python environment query importing sys, platform, numpy, scipy, sympy. Exit code 1, ModuleNotFoundError for scipy. No source files or candidate materials were read by this query.
5. Python query using importlib metadata to record python/platform and numpy/sympy/scipy/mpmath availability. Exit code 0.
6. Patch-tool creation of reconstruct.py, then path-portability patch and first successful execution using the runtime above.
7. Copy-Item -LiteralPath '<LOCAL_POST_VERIFICATION>\reconstruction_view\TARGET.md' -Destination '<LOCAL_POST_VERIFICATION>\receipts\reconstruction\lower_worker\TARGET.exposed.md'.
8. Patch-tool switch to the included exposure copy and exact endpoint nonroot assertions.
9. Python execution of reconstruct.py | Tee-Object -FilePath '<LOCAL_POST_VERIFICATION>\receipts\reconstruction\lower_worker\run_stdout.log'. Exit code 0; all exact and numerical assertions passed.
10. Get-Content -LiteralPath the generated checks.json -Raw to inspect the computed coefficients.
11. Patch-tool addition of exact principal-minor/determinant characteristic checks, followed by the same Python/Tee-Object command. Exit code 0; all checks passed. This is the final code execution captured in run_stdout.log.
12. UTC clock reads recorded 2026-10-03 18:41:55 UTC and 18:42:53 UTC.
13. Select-String on the generated exact_computation.log for Sturm variation counts and f_s endpoint bounds, using -SimpleMatch.
14. Patch-tool creation of the frozen report and this command receipt, followed by SHA-256 receipt generation for all files in this output directory.

The parent messages supplied the task boundary/runtime and a portability/PARTIAL-label reminder. No method hint or other agent result was requested or read. No internet tool, browser, project-memory lookup, file-discovery command, skill source, or external mathematical source was used.
