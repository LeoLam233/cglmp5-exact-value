# Deliberately invalid-object checker control

These are **test fixtures, never production proof modules or production imports**.
`InvalidObject.lean` intentionally bypasses the kernel during fixture construction
so that a stored theorem claims `False` while its supplied proof is `True.intro`.
The valid counterpart uses the ordinary checked declaration path and claims `True`.
The bypass is the fault being injected; it is not an accepted proof technique.

`scripts/run_lean_checker_fixture.py` copies these files into a temporary shadow,
compiles them there, and records all inputs/objects and command outcomes externally.
It requires:

1. both intended objects can be constructed;
2. ordinary pinned `lean --trust=0` imports accept both (demonstrating why that
   frontend flag is insufficient as an imported-proof gate);
3. official module replay accepts the valid object and rejects the invalid one;
4. official `leanchecker --fresh` accepts the valid object and rejects the invalid
   one specifically with the kernel declaration-type-mismatch diagnostic.

Import, timeout, memory, recursion and other infrastructure failures do not count
as the expected kernel rejection. Every deliberate object remains outside the
production module namespace and the frozen candidate's build tree. The fixture runner requires an explicit output directory outside the repository
in every mode, and uses the same candidate-immutability guard as the other
negative controls. Its caller holds one heavyweight scheduler slot.

The original eight-command comparison is included as historical development
evidence in `verification/formalization_development/checker_fixture/CONCLUSION.json`.
The packaged source files here match those validated inputs byte-for-byte. Final
CI must execute the packaged runner on the frozen candidate; historical receipts
alone are insufficient. External outputs follow the formalization report’s
acceptance-receipt contract.
