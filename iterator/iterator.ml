(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open Cfg
open Domains.Domain
open Domains.Value_domain

type state = NotVisited | Visited

module Iterator(D:DOMAIN) = functor (ValueDomain:VALUE_DOMAIN) ->
struct
  module D = D(ValueDomain)
  let widen_next = Hashtbl.create 0
  let states = Hashtbl.create 0
  let rec visit_arc arc =
    let destination = arc.arc_dst in
    match Hashtbl.find_opt states destination with
    | None -> visit_node destination
    | Some NotVisited -> Hashtbl.add widen_next destination ()
    | Some Visited -> ()
  
  and visit_node node : unit =
    Hashtbl.add states node NotVisited ;
    List.iter visit_arc node.node_out ;
    Hashtbl.add states node Visited

  let environment_of_node environment node =
    match Hashtbl.find_opt environment node with
    | None -> D.bottom
    | Some d -> d

  let rec iter_arc environment arc : D.t =
    let domain = environment_of_node environment arc.arc_src
    in
    match arc.arc_inst with
    | CFG_skip _ -> domain
    | CFG_assign (var, expr) -> D.assign domain var expr
    | CFG_guard expr -> D.guard domain expr
    | CFG_call func -> iterate_function environment func None domain
    | CFG_assert (expr, extent) -> 
      let true_domain = D.guard domain expr 
      and false_domain = D.guard domain (CFG_bool_unary (AST_NOT, expr))
      in

      if not (D.is_bottom false_domain) then begin
        (* TODO: clean error handling *)
        Format.printf "%a: %s \"%a\"@." Cfg_printer.pp_pos (fst extent) "Assertion failure" Cfg_printer.print_bool_expr expr
      end ; 
      true_domain
  (*
    [environment] maintains a map from nodes to abstract values
  *)
  and iterate_function environment (func:func) (entry_node:node option) entry_domain =
    (* TODO: replace node option by node; to do so, change calls using None to calls using func.func_entry *)
    let entry = match entry_node with
                | Some x -> x
                | None -> func.func_entry in
    let children = List.map (fun arc -> arc.arc_dst) entry.node_out in

    (* the set of nodes to update *)
    let worklist = ref (NodeSet.of_list children) in
    Hashtbl.add environment entry entry_domain ;

    (* the algorithm is finished when there is no more node in the worklist *)
    while not (NodeSet.is_empty !worklist) do 
      (* at each step, a node is extracted from the worklist and updated *)
      let node = NodeSet.choose !worklist in 
      worklist := NodeSet.remove node !worklist ;

      let sources = List.filter (fun arc -> Hashtbl.mem environment (arc.arc_src)) node.node_in in 
      let sources_domains = List.map (fun arc -> iter_arc environment arc) sources in 
      let join_domain = List.fold_left D.join D.bottom sources_domains in
      
      (* if the node’s abstract value has changed *)
      if Hashtbl.mem environment node |> not && join_domain <> environment_of_node environment node then begin
        let widen_if_necessary = if Hashtbl.mem widen_next node 
                                    then D.widen (environment_of_node environment node) join_domain
                                    else join_domain in
        Hashtbl.add environment node widen_if_necessary ;

        (* putting all the node’s successors into the worklist *)
        List.iter (fun arc -> worklist := NodeSet.add (arc.arc_dst) !worklist) node.node_out
      end
    done ;

    match Hashtbl.find_opt environment func.func_exit with
    | None -> D.bottom
    | Some d -> d

  let iterate cfg =
    let _ = Random.self_init () in

    let entries = List.map (fun f -> f.func_entry) cfg.cfg_funcs in
    List.iter visit_node entries ;
    Hashtbl.iter (fun node () -> Format.printf "node %d added to widen_next\n" node.node_id) widen_next ;

    let environment = Hashtbl.create 0 in 
    let main_func = List.find (fun f -> f.func_name = "main") cfg.cfg_funcs in 

    iterate_function environment main_func None D.init |> ignore

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