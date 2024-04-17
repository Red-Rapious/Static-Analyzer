(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open Cfg
open Domains.Domain
open Domains.Value_domain
open Hashtbl

type state = NotVisited | Visited

module Iterator(D:DOMAIN) = functor (ValueDomain:VALUE_DOMAIN) ->
struct
  let to_widen = Hashtbl.create 0
  let states = Hashtbl.create 0
  let rec iter_arc arc =
    let nei = arc.arc_dst in
    match Hashtbl.find_opt states nei with
    | Some NotVisited -> Hashtbl.add to_widen nei ()
    | Some Visited -> ()
    | None -> iter_node nei
  
  and iter_node node : unit =
    Hashtbl.add states node NotVisited;
    List.iter iter_arc node.node_out;
    Hashtbl.add states node Visited

  let iterate cfg =
    let _ = Random.self_init () in

    List.iter iter_node (List.map (fun f -> f.func_entry) cfg.cfg_funcs);
    Hashtbl.iter (fun node () -> Format.printf "%d marked\n" node.node_id) to_widen

    (*let iter_arc arc: unit =
      match arc.arc_inst with
      | _ -> failwith "TODO"
    in

    let iter_node node: unit =
      Format.printf "<%i>: ⊤@ " node.node_id
    in

    List.iter iter_arc cfg.cfg_arcs;
    Format.printf "Node Values:@   @[<v 0>";
    List.iter iter_node cfg.cfg_nodes;
    Format.printf "@]" ;
    Cfg_printer.print_cfg Format.std_formatter cfg*)
end