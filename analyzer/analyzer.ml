(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(*
  Simple driver: parses the file given as argument and prints it back.

  You should modify this file to call your functions instead!
*)

open Frontend
open Domains.Domain

let log fmt =
  if !Options.verbose then Format.fprintf Format.err_formatter fmt
  else Format.fprintf Format.str_formatter fmt

(* parse filename *)
let doit filename =
  let prog = File_parser.parse_file filename in
  let cfg = Tree_to_cfg.prog prog in
  if !Options.verbose then Format.printf "%a" Cfg_printer.print_cfg cfg;
  Cfg_printer.output_dot !Options.cfg_out cfg;

  let module Vars : VARS = struct
    let support = cfg.cfg_vars
  end in
  (match !Options.domain with
  | "constants" ->
      let module I =
        Iterator.Iterator (Domain (Vars)) (Domains.Constant.ConstantDomain)
      in
      log "Starting iterator using constants domain...@.";
      I.iterate cfg
  | "interval" ->
      let module I =
        Iterator.Iterator (Domain (Vars)) (Domains.Interval.IntervalDomain)
      in
      log "Starting iterator using interval domain...@.";
      I.iterate cfg
  | "signs" ->
      let module I =
        Iterator.Iterator (Domain (Vars)) (Domains.Signs.SignsDomain)
      in
      log "Starting iterator using signs domain...@.";
      I.iterate cfg
  | "congruences" ->
      let module I =
        Iterator.Iterator
          (Domain (Vars)) (Domains.Congruences.CongruencesDomain)
      in
      log "Starting iterator using congruences domain...@.";
      I.iterate cfg
  | "product" ->
      let module I =
        Iterator.Iterator
          (Domain (Vars)) (Domains.Reduced_product.ReducedProductDomain)
      in
      log "Starting iterator using reduced product domain...@.";
      I.iterate cfg
  | _ -> failwith "The provided domain argument does not exist.");
  log "End of static analyzer.@."

(* parses arguments to get filename *)
let main () =
  let _ = Options.init () in
  log "\n\nStarting static analyzer...\n";
  log " -> Domain: %s\n" !Options.domain;
  doit !Options.file

let _ = main ()
