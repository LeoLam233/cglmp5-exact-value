# CGLMP5 manuscript v0.1.1

**Author:** Dehao Lin, ORCID [0009-0001-4551-8490](https://orcid.org/0009-0001-4551-8490).

`main.pdf` is the publication-style manuscript. It includes the exact theorem,
probability convention, algebraic root/embedding, full finite Gram coefficient
data, strict rational positivity, the fixed-common-embedding local-POVM bridge,
the explicit five-dimensional attaining strategy, reproducibility discussion,
limitations, and AI-assistance disclosure. AI systems are not academic authors.

## Clean build

Requirements: a complete TeX Live installation (pdfLaTeX, Latin Modern, AMS,
geometry, microtype, hyperref, natbib, fancyvrb, enumitem), BibTeX, and latexmk.
No shell escape, network download, or solver is needed.

From the repository root:

```sh
cd paper
bash build.sh
```

On an ordinary fully configured TeX installation, the equivalent command is:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

`build.sh` also handles this release environment's preinstalled TeX files with
missing system format/font-map caches. It reconstructs those caches only inside
`paper/.tex-cache/` from already installed TeX resources. It does not install
software or change system files. PDF date and trailer-ID metadata are omitted;
the recorded toolchain is needed for byte-for-byte reproducibility.

To remove temporary TeX outputs without removing the checked-in PDF:

```sh
latexmk -c main.tex
```

## Exact printed-data verification

From the repository root, using normal Python 3 (without `-O`, `-OO`, or a
nonzero `PYTHONOPTIMIZE`):

```sh
python3 paper/check_paper_data.py --output paper/validation/data_correspondence.json
```

This checks the published `.tex` tables against the unchanged four certificate
JSON files via the v0.1.1 strict decoder, reconstructs all phase/kernel/Gram
data, compares all 1,134 compact-polynomial coefficient positions and 14
weights, and replays the full 1,681-word Gram identity and physical attainer.
It also computes all 14 positive leading minors by determinant expansion,
without prior pivot division. The printed interval table uses strictly
outward-rounded rational bounds.

The script uses the canonical cyclotomic arithmetic from `artifact_v0.1.1`.
It is a source/data correspondence check, not an independent arithmetic
implementation. The four mathematical JSON files are byte-identical to
`artifact_v0.1`. All finite data needed to reconstruct the Gram certificate
are printed in the PDF; the repository is not needed merely to build the PDF.

Only if intentionally regenerating the derived table sources:

```sh
python3 paper/check_paper_data.py --write --output paper/validation/data_correspondence.json
```

## Source map

- `main.tex`: theorem, proof, exact reconstruction formulas, interval constants
- `references.bib`: primary-source-verified bibliography
- `phase_supports.tex`: all nonzero phase-matrix entries
- `kernel_data.tex`: all nontrivial small kernel-factor entries
- `parameter_assignments.tex`, `parameter_data.tex`: all 42 real Gram parameters
- `minor_bounds.tex`: exact positive leading-minor enclosures
- `check_paper_data.py`: exact table/certificate correspondence and replay
- `validation/`: source-bound receipts, build history, bibliography provenance,
  and visual-inspection record

The manuscript does not claim uniqueness, self-testing, an all-outcome result,
absolute priority, human peer review, or proof-assistant formal verification.
The label v0.1.1 denotes the manuscript/hardening release; v0.2.0 is reserved
for a later completed formalization milestone.
