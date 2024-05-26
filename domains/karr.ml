open Frontend
open Domain
open Frontend.Abstract_syntax_tree
open Cfg

type constraints = | Bot | Constraints of (Q.t * Q.t array) array ;;

let array_eq a1 a2 = 
        if Array.length a1 <> Array.length a2 then false else
                let r = ref true in 
                let i = ref 0 in 
                while !r && !i < Array.length a1 do
                        if a1.(!i) <> a2.(!i) then r := false
                        done;
                !r

let mono_cons_eq c1 c2 = fst c1 == fst c2 && array_eq (snd c1) (snd c2)

let is_eq = function 
        | Bot, Bot -> true
        | Bot, _ | _, Bot -> false
        | Constraints l1, Constraints l2 -> Array.for_all2 mono_cons_eq l1 l2

let swap_rows m i j =
        let tmp = m.(i) in
        m.(i) <- m.(j);
        m.(j) <- tmp;
;;
              
let rref m =
        try
        let lead = ref 0
        and rows = Array.length m
        and cols = Array.length (snd m.(0)) in
        for r = 0 to pred rows do
                if cols <= !lead then
                        raise Exit;
                let i = ref r in
                while Q.(=) (snd m.(!i)).(!lead)  Q.zero do
                        incr i;
                        if rows = !i then begin
                                i := r;
                                incr lead;
                                if cols = !lead then
                                        raise Exit;
                        end
                done;
                swap_rows m !i r;
                let lv = (snd m.(r)).(!lead) in
                m.(r) <- (Q.(/) (fst m.(r)) lv, Array.map (fun v -> Q.(/) v lv) (snd m.(r)));
                for i = 0 to pred rows do
                        if i <> r then
                                let lv = (snd m.(i)).(!lead) in
                                m.(i) <- ((fst m.(i)), Array.mapi (fun i iv -> Q.(-) iv (Q.( * ) lv ((snd m.(r)).(i)))) (snd m.(i)));
                done;
                incr lead;
        done
        with Exit -> ()
        ;;

let simplify = function 
        | Bot -> Bot
        | Constraints(c) -> rref c; Bot 

;;

module ConstantDomain(Vars:VARS) = struct
        type t = constraints VarMap.t

        let init = 
                List.fold_left (fun map var -> VarMap.add var [|(Q.zero, Array.make (List.length Vars.support) Q.zero)|] map) VarMap.empty Vars.support

        let bottom = 
                List.fold_left (fun map var -> VarMap.add var Bot map) VarMap.empty Vars.support
        
        let is_bottom = function 
        |v -> List.filter (fun entry -> is_eq (snd entry, Bot) ) (VarMap.bindings v) <> []

        let assign domain var int_expr =
                match int_expr with 
                | CFG_int_const(c) -> domain
                | _ -> domain


end 
