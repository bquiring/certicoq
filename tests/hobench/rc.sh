#!/usr/bin/env bash
# Compiles a benchmark file with the CertiRocq plugin.
eval $(opam env --switch=rocq91 --set-switch)
ulimit -s unlimited
rocq c -R ../../plugin CertiRocq.Plugin -I ../../plugin -R ./ CertiRocq.Tests.hobench "$@"
