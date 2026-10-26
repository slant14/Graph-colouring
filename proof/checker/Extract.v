(* Extract the verified certificate checkers of Certificate.v to OCaml. *)
From Stdlib Require Import PeanoNat.
From CertCol Require Import Certificate.
From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extraction Language OCaml.
Extract Constant Nat.eqb => "( = )".
Extract Constant Nat.ltb => "( < )".
Extract Constant Nat.eq_dec => "( = )".
Extraction "certcheck.ml" check_coloring check_refutation.
