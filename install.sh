#!/bin/sh

# Build+Install script for OCaml on MinGW.
# This is a pretty dirty workaround until OPAM is ported to MinGW.
# You need Cygwin shell to execute this.

# Set the version

VERSION=1.1

# Crash at any error

set -e

# META

sed "s/%{version}%/$VERSION/g" pkg/META.in > pkg/META

# Build

# native and native-dynlink must be supported

ocaml pkg/build.ml native=true native-dynlink=true

# Install

# ppx_deriving.install is created by the build.
# We extract the install targets from it.
# The following is highly dependent on the form of the file. Therefore very fragile.

INSTALL_TARGETS=`grep -E '^\s+' ppx_deriving.install | sed -E -e 's/^  "\??([^"]+)".*/\1/'`

ocamlfind remove ppx_deriving
ocamlfind install ppx_deriving $INSTALL_TARGETS

# We need to rename ppx_deriving_main.native

DIR=`ocamlfind query ppx_deriving | sed -e 's/\r//g'`
echo $DIR
mv $DIR/ppx_deriving_main.native $DIR/ppx_deriving
