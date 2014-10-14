#!/bin/sh
set -e
ocamlfind remove ppx_deriving
ocamlfind install ppx_deriving `find . -iname '*.cm*'` */META
