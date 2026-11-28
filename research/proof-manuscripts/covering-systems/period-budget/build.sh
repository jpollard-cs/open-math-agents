#!/bin/sh
set -eu
cd "$(dirname "$0")"
texroot=/usr/share/texlive/texmf-dist
export TEXINPUTS=".:$texroot/tex//:"
export TEXFORMATS=".:"
export TFMFONTS="$texroot/fonts/tfm//:"
export ENCFONTS="$texroot/fonts/enc//:"
export T1FONTS="$texroot/fonts/type1//:"
export TEXFONTMAPS="$texroot/fonts/map//:"
if [ ! -f pdflatex.fmt ]; then
  pdftex -ini -etex -jobname=pdflatex -interaction=batchmode pdflatex.ini
fi
pdflatex -halt-on-error -interaction=nonstopmode period.tex > build.log
pdflatex -halt-on-error -interaction=nonstopmode period.tex >> build.log
