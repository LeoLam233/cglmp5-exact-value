#!/usr/bin/env bash
# Clean reproducible build. A standard complete TeX installation needs only latexmk.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p .tex-cache .tex-config
export TEXMFVAR="$PWD/.tex-cache"
export TEXMFCONFIG="$PWD/.tex-config"
# Some container images have the official TeX files but no generated system ls-R
# database. Enable direct file discovery there, without modifying system files.
if ! kpsewhich article.cls >/dev/null 2>&1; then
  if [[ -f /usr/share/texlive/texmf-dist/tex/latex/base/latex.ltx ]]; then
    export TEXMF="{/usr/share/texmf,/usr/share/texlive/texmf-dist}"
  else
    echo 'A complete TeX Live installation is required.' >&2
    exit 1
  fi
fi
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  if [[ ! -f .tex-cache/pdflatex.fmt ]]; then
    (cd .tex-cache && pdftex -ini -interaction=nonstopmode -halt-on-error \
      -jobname=pdflatex -progname=pdflatex -etex pdflatex.ini)
  fi
  export TEXFORMATS="$PWD/.tex-cache:"
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/{cm,cmextra,latxfont,symbols,euler}.map \
      > .tex-cache/pdftex.map
  export TEXFONTMAPS="$PWD/.tex-cache//:"
fi
export SOURCE_DATE_EPOCH=1791072000
export FORCE_SOURCE_DATE=1
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
# Do not mistake a stale PDF or unresolved bibliography for a clean build.
test -s main.pdf
if grep -Eq '(^!|Overfull \\hbox|undefined references|undefined citations|Citation .* undefined)' main.log; then
  echo 'The PDF build has unresolved errors or overfull text.' >&2
  exit 1
fi
