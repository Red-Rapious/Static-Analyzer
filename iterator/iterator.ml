(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open Cfg
open Domains.Domain
open Domains.Value_domain

type state = NotVisited | Visited
type direction = Forward | Backward

module Iterator (D : DOMAIN) =
functor
  (ValueDomain : VALUE_DOMAIN)
  ->
  struct
    module D = D (ValueDomain)

    let widen_next = Hashtbl.create 0
    let states = Hashtbl.create 0

    let rec visit_arc arc =
      let destination = arc.arc_dst in
      match Hashtbl.find_opt states destination with
      | None -> visit_node destination
      | Some NotVisited -> Hashtbl.add widen_next destination ()
      | Some Visited -> ()

    and visit_node node : unit =
      Hashtbl.add states node NotVisited;
      List.iter visit_arc node.node_out;
      Hashtbl.add states node Visited

  (* Utility functions used to abstract direction (forward, backward) *)
  let node_in node = function
  | Forward -> node.node_in
  | Backward -> node.node_out
  and node_out node = function
  | Forward -> node.node_out
  | Backward -> node.node_in
  and arc_src arc = function
  | Forward -> arc.arc_src
  | Backward -> arc.arc_dst
  and arc_dst arc = function
  | Forward -> arc.arc_dst
  | Backward -> arc.arc_src
  

  let environment_of_node environment node =
    match Hashtbl.find_opt environment node with
    | None -> D.bottom
    | Some d -> d

  let going_up = ref true
  let rec iter_arc environment arc direction : D.t =
    let domain = environment_of_node environment arc.arc_src
    in
    if !Options.verbose then begin
      Format.printf "Domain before ";
      Cfg_printer.print_inst Format.std_formatter arc.arc_inst ;
      Format.printf "@." ;
      D.print Format.std_formatter domain ;
      Format.printf "@."
    end ;
    match arc.arc_inst with
    | CFG_skip _ -> domain
    | CFG_assign (var, expr) -> 
      if direction = Forward then D.assign domain var expr
      else begin 
        failwith "implement backward"
      end
    | CFG_guard expr -> D.guard domain expr
    | CFG_call func -> 
      if !Options.backward then failwith "" 
      else iterate_function environment func None Forward domain
    | CFG_assert (expr, extent) -> 
      let true_domain = D.guard domain expr 
      and false_domain = D.guard domain (CFG_bool_unary (AST_NOT, expr))
      in

      if direction = Forward && not (D.is_bottom false_domain) then begin
        going_up := false;
        if !Options.backward then begin
          (*Format.printf "%a@ " Errors.pp_err (AssertDetect, ext, expr);*)
          let failed_envs = ref (NodeMap.add (arc_src arc direction) false_domain NodeMap.empty) in
          (*ignore (iterate_function (failed_envs, !envs) fct (Some (arc_src arc direction)) false_domain Backward)*)
          ()
        end;
  
        (* TODO: clean error handling *)
        Format.printf "%a: %s \"%a\"@." Cfg_printer.pp_pos (fst extent) "Assertion failure" Cfg_printer.print_bool_expr expr ;
        if !Options.verbose then begin
          Format.printf "The assertion is false when the value is in the following non-bottom domain:\n" ;
          D.print Format.std_formatter false_domain ; 
          Format.printf "@."
        end
      end else begin
        if !Options.verbose then begin
          Format.printf "The assertion at %a is always true.\nTrue domain:\n" Cfg_printer.pp_pos (fst extent) ;
          D.print Format.std_formatter true_domain ; 
          Format.printf "False domain:\n" ;
          D.print Format.std_formatter false_domain ; 
          Format.printf "@."
        end
      end ; 
      true_domain
  
  (*
    [environment] maintains a map from nodes to abstract values
  *)
  and iterate_function environment (func:func) (entry_node:node option) direction entry_domain  =
    (* TODO: replace node option by node; to do so, change calls using None to calls using func.func_entry *)
    let entry = match entry_node with
    | Some x -> x
    | None -> func.func_entry in
    let children = List.map (fun arc -> (arc_dst arc direction)) entry.node_out in

      (* the set of nodes to update *)
      let worklist = ref (NodeSet.of_list children) in
      Hashtbl.add environment entry entry_domain;

      (* the algorithm is finished when there is no more node in the worklist *)
      while not (NodeSet.is_empty !worklist) do
        (* at each step, a node is extracted from the worklist and updated *)
        let node = NodeSet.choose !worklist in
        worklist := NodeSet.remove node !worklist;

      let sources = List.filter (fun arc -> Hashtbl.mem environment (arc_src arc direction)) (node_in node direction) in 
      let sources_domains = List.map (fun arc -> iter_arc environment arc direction) sources in 
      let join_domain = List.fold_left D.join D.bottom sources_domains in
      
      (* if the node’s abstract value has changed *)
      if Hashtbl.mem environment node |> not && join_domain <> environment_of_node environment node then begin
        let widen_if_necessary = if Hashtbl.mem widen_next node 
                                    then D.widen (environment_of_node environment node) join_domain
                                    else join_domain in
        Hashtbl.add environment node widen_if_necessary ;

        (* putting all the node’s successors into the worklist *)
        List.iter (fun arc -> worklist := NodeSet.add (arc_dst arc direction) !worklist) (node_out node direction)
      end
    done ;

    let func_exit f = match direction with
    | Forward -> f.func_exit
    | Backward -> f.func_entry
    in
    match Hashtbl.find_opt environment (func_exit func) with
    | None -> D.bottom
    | Some d -> d

    let iterate cfg =
      let _ = Random.self_init () in

      let entries = List.map (fun f -> f.func_entry) cfg.cfg_funcs in
      List.iter visit_node entries;

    let environment = Hashtbl.create 0 in 
    let main_func = List.find (fun f -> f.func_name = "main") cfg.cfg_funcs in
    iterate_function environment main_func None Forward D.init  |> ignore

    (*
    let iter_node node: unit =
      Format.printf "<%i>: ⊤@ " node.node_id
    in

    List.iter iter_arc cfg.cfg_arcs;
    Format.printf "Node Values:@   @[<v 0>";
    List.iter iter_node cfg.cfg_nodes;
    Format.printf "@]" ;
    Cfg_printer.print_cfg Format.std_formatter cfg*)
  end
