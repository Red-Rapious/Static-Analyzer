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
              
let rref c =
        let m = Array.copy c in
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
        done;
        m;
        with Exit -> m;;
        ;;



let line_equal c1 c2 = 
        match c1, c2 with (v1, c1), (v2, c2) -> 
        if Q.(<>) v1 v2 then false else
        let lead1 = ref 0 and 
        lead2 = ref 0 in 
        let l1 = Array.length c1 and 
        l2 = Array.length c2 in
        if l1 <> l2 then false else let r = ref true in
                while Q.(=) (c1.(!lead1)) Q.zero && !lead1 < pred l1 do incr lead1 done;
                while Q.(=) (c2.(!lead2)) Q.zero && !lead2 < pred l2 do incr lead2 done;
                if !lead1 <> !lead2 then r:= false else 
                        while !r && Q.(=) c1.(!lead1) c2.(!lead2) && !lead1 < pred l1 do
                                incr lead1;
                                r:= Q.(=) c1.(!lead1) c2.(!lead2);
                        done;
                !r

module KarrDomain(Vars:VARS) = struct
        type t = constraints 

        let init = let c = Array.make (List.length Vars.support) (Q.zero, Array.make (List.length Vars.support) Q.zero) in 
        for i = 0 to Array.length c do (snd c.(i)).(i) <- Q.one done; Constraints c

        let simplify = function
        | Bot -> Bot
        | Constraints(c) -> 
                let c = rref c in
                let r = ref true in 
                let index = ref (pred (Array.length c)) in
                while !r && !index >= 0 do
                        r:= Array.for_all (Q.(=) Q.zero) (snd c.(!index));
                        index := !index - 1;
                done;
                if !index < 0 then init
                else if !index > Array.length (snd c.(!index)) then Bot 
                else let res = Array.make (List.length Vars.support) (Q.zero, Array.make (List.length Vars.support) Q.zero) in
                for i = 0 to !index do 
                        res.(i) <- c.(i);
                done;
          let index = ref 0 in
          let r = ref true in
          while !r && !index < Array.length res do 
            if Array.for_all (Q.(=) Q.zero) (snd res.(!index) )&& Q.(<>) Q.zero (fst res.(!index)) then r:= false ;
            incr index; 
          done; 
            if !r then Constraints res else Bot

        let bottom = 
        Array.make (List.length Vars.support) Bot
        
        let is_bottom = function t -> is_eq (Bot, simplify t)

        let equal c1 c2 = 
                match simplify c1, simplify c2 with 
                | Bot, Bot -> true
                | Bot, _ | _, Bot -> false
                | Constraints c1, Constraints c2 when Array.length c1 <> Array.length c2 || Array.length (snd c1.(0)) <> Array.length (snd c2.(0)) -> false
                | Constraints c1, Constraints c2 -> 
                let res = ref true and 
                index = ref 0 in 
                while !res && !index < Array.length c1 do 
                        res := line_equal c1.(!index) c2.(!index);
                        incr index
                done;
                !res
        ;;

        let join c1 c2 = 
                match simplify c1, simplify c2 with 
                | Bot, _ | _, Bot -> Bot
                | Constraints c1, Constraints c2 -> 
                        let res = Array.make (2 * Array.length c1) (Q.zero, Array.make (Array.length c1) Q.zero) in 
                        for l1 = 0 to Array.length c1 do 
                                res.(l1) <- c1.(l1);
                                res.(l1 + Array.length c1) <- c1.(l1);
                        done;
                        let res = simplify (Constraints res) in 
                res


        let subset c1 c2 = is_eq (c2, join c1 c2)
        
        let rec has_variable = function 
                | CFG_int_const _ -> false
                | CFG_int_binary(_, e1, e2) -> has_variable e1 || has_variable e2
                | CFG_int_var _ -> true
                | CFG_int_unary (_, e) -> has_variable e
                | CFG_int_rand (_, _) -> false
        
        let rec is_affine = function 
                | CFG_int_const _ -> true
                | CFG_int_rand (_, _) -> true
                | CFG_int_unary(_, e) -> is_affine e
                | CFG_int_var _ -> true
                | CFG_int_binary(AST_PLUS, e1, e2) | CFG_int_binary(AST_MINUS, e1, e2) -> is_affine e1 && is_affine e2
                | CFG_int_binary(AST_MODULO, _, _) -> false (*Dans le cadre de cette implémentation, les égalités affines modulo un nombre ne sont pas prises en charge *)
                | CFG_int_binary(_, e1, e2) -> not (has_variable e1 && has_variable e2) && is_affine e1 && is_affine e2
    
        let evaluate e = if has_variable e then failwith "This should not have happened";
                let rec aux = function 
                | CFG_int_const i -> Some (Q.of_bigint i)
                | CFG_int_unary(AST_UNARY_PLUS, e) -> aux e
                | CFG_int_unary(AST_UNARY_MINUS, e) -> begin match aux e with | Some c -> Some(Q.(~-) c) | None -> None end
                | CFG_int_binary(AST_PLUS, e1, e2) -> begin match aux e1, aux e2 with 
                | None, _ | _, None -> None
                | Some c1, Some c2 -> Some (Q.(+) c1 c2)
                end
                | CFG_int_binary(AST_MINUS, e1, e2) -> begin match aux e1, aux e2 with 
                | None, _ | _, None -> None
                | Some c1, Some c2 -> Some (Q.(-) c1 c2)
                end
                | CFG_int_binary(AST_MULTIPLY, e1, e2) -> begin match aux e1, aux e2 with 
                | None, _ | _, None -> None
                | Some c1, Some c2 -> Some (Q.( * ) c1 c2)
                end
                | CFG_int_binary(AST_DIVIDE, e1, e2) -> begin match aux e1, aux e2 with 
                | None, _ | _, None -> None
                | Some c1, Some c2 when Q.(<>) c2 Q.zero -> Some (Q.(+) c1 c2)
                | _, _ -> None
                end
                | _ -> failwith "Pas traité"
        in aux e

        let assign domain var e = if not (has_variable e) then
                match evaluate e with
                | None -> Bot
                | Some v -> let m = Array.make (List.length Vars.support) (Q.zero, Array.make (List.length Vars.support) Q.zero) in 
                        let c = Array.make (List.length Vars.support) Q.zero in 
                        c.(var.var_id) <- Q.one; 
                        m.(0) <- (v, c);
                        join domain (Constraints m)

                else 
                Bot
                


end 
