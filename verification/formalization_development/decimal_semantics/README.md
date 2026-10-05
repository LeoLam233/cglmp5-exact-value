# Decimal source-fragment semantic bridge

`CGLMP5/SourceDecimalSoundness.lean` supplies generic kernel-checked semantics for the fragment parser. Successful `DecimalChunks.natural` decoding agrees with parsing the uninterrupted `String.join` text using `decimalNat`; successful signed decoding agrees with `decimalInt` of the exact reconstructed text. Soundness then lifts through scalar, coefficient and full term records.

The affine character-fold lemma establishes the base10 positional rule for every fragment list. It does not test only the178 instantiated scalar records, assume a decimal conversion oracle, or require construction of a giant source string during the generic proof.

The preserved failed diagnostic concerns an intermediate Lean simplification of the literal minus-sign prefix; the final build receipt confirms its repair. This development receipt is not a final adversarial audit.
