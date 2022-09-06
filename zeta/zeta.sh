#!/bin/bash

# Verifica si czt.sty está en la carpeta.
if [ ! -f "czt.sty" ]; then
  printf "Error: czt.sty no se encuentra en la carpeta.\n"
  exit 1
fi

# Verifica si el .tex no existe
# test EXPRESSION es igual a escribir [ EXPRESSION ]
if [ ! -f "$1.tex" ]; then
  touch $1.tex
fi

# Aplica los cambios hechos en .zed hacia .tex
diff -u $1.tex $1.zed > $1.patch
patch -u $1.tex -i $1.patch

#code $1.tex
pdflatex -synctex=1 -interaction=nonstopmode $1.tex
