import Blake3Prize.Migration.Transport
import Lean
open Lean Elab Command in
run_cmd liftTermElabM do
  for decl in [``Blake3Prize.Migration.shared_law, ``Blake3Prize.Migration.splitKeys_law, ``Blake3Prize.Migration.splitSample_law,
    ``Blake3Prize.Migration.input_disclosure, ``Blake3Prize.Migration.output_disclosure,
    ``Blake3Prize.Migration.views_preserved, ``Blake3Prize.Migration.bound_on_valid_keys,
    ``Blake3Prize.Migration.wins_preserved, ``Blake3Prize.Migration.bound_preserved] do
    for ax in (← collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "forbidden migration axiom: {ax} in {decl}"
  IO.println "PASS: BLAKE3 key law, disclosure, win predicate and ROM bound transport"
