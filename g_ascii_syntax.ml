(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Coqast
open Ast
open Pp
open Util
open Names
open Pcoq
open Rawterm
open Topconstr
open Libnames
(*i*)

exception Non_closed_ascii

open Coqlib
(*
let ctrue = lazy
  (reference_of_constr (gen_constant_in_modules "Ascii" init_modules "true"))
let cfalse = lazy
  (reference_of_constr (gen_constant_in_modules "Ascii" init_modules "false"))
let cascii = lazy
  (reference_of_constr (gen_constant_in_modules "Ascii" [["Ascii"]] "Ascii"))

let make_ascii dloc p =
  let rec aux n p = 
     if n = 0 then [] else
     let mp = p mod 2 in
     if mp = 0 then 
     RRef (dloc,Lazy.force cfalse) :: (aux (n-1) (p/2)) else
     RRef (dloc,Lazy.force ctrue) :: (aux (n-1) (p/2)) in
  RApp (dloc,RRef (dloc,Lazy.force cascii), aux 8 p)
*)

let make_dir l = make_dirpath (List.map id_of_string (List.rev l))
let make_dir l = make_dirpath (List.map id_of_string (List.rev l))
let make_qualid dir s = make_qualid (make_dir dir) (id_of_string s)
let ctrue  loc = Qualid (loc,make_qualid ["Coq";"Init";"Datatypes"] "true")
let cfalse loc = Qualid (loc,make_qualid ["Coq";"Init";"Datatypes"] "false")
let cascii loc = Qualid (loc,make_qualid ["Ascii"] "Ascii")

let make_ascii dloc p =
  let rec aux n p = 
     if n = 0 then [] else
     let mp = p mod 2 in
     if mp = 0 then 
     CRef (cfalse dloc):: (aux (n-1) (p/2)) else
     CRef (ctrue dloc) :: (aux (n-1) (p/2)) in
  CAppExpl (dloc,(None,cascii dloc), aux 8 p)

let fmake_ascii s dloc =
  let le = (String.length s) in
  if (le =3) then 
    (make_ascii dloc (int_of_string s)) else
  if ((le =2 ) && ((s.[0])='\\')) then 
    (make_ascii dloc (int_of_char s.[1]))
  else
    (make_ascii dloc (int_of_char s.[0]))

GEXTEND Gram
  GLOBAL: Constr.operconstr;
  Constr.operconstr: LEVEL "0" [ [ "@"; s = STRING -> fmake_ascii s loc ] ];
END

(** old ast-based pp **)

let datatypes_module = make_dir ["Coq";"Init";"Datatypes"]
let make_path dir id = Libnames.encode_kn dir id
let bool_path = make_path datatypes_module (id_of_string "bool")
let glob_bool = IndRef (bool_path,0)
let path_of_true  = ((bool_path,0),1)
let path_of_false = ((bool_path,0),2)
let glob_true  = ConstructRef path_of_true
let glob_false = ConstructRef path_of_false

open Termast

let asttrue  = ast_of_ref glob_true
let astfalse = ast_of_ref glob_false

let rec alistp = function
    | [] -> 0
    | (a::l) when alpha_eq(a,asttrue) ->
         1+2*(alistp l)
    | (a::l) when alpha_eq(a,astfalse) ->
         2*(alistp l)
    | _ -> raise Non_closed_ascii

let alist_val p =
  try 
    Some (alistp p)
  with
    Non_closed_ascii -> None

let ascii_printer p =
  match p with
    Node (_,"ASCII",l) -> 
      begin
      match (alist_val l) with
      | Some 34 -> Some (str "@\"\\\"\"")
      | Some 92 -> Some (str "@\"\\\\\"")
      | Some i -> 
         let s1 =  (String.make 1 (char_of_int i)) in
         let s2 = (String.escaped  s1) in 
         Some 
           (if s1=s2 then
             str "@\"" ++ str s1 ++ str "\""
           else
             str "@\"" ++ str (String.sub s2 1 3) ++ str "\"")
      | None -> None
      end
  | _ -> failwith "Inconsistent pretty-printer rule"

let _ = if !Options.v7 then
Esyntax.declare_primitive_printer "ascii_printer" "string_scope" ascii_printer

(** V8 printer **)
(*
let rec int_of_nat = function
  | RApp (_,RRef (_,s),[a]) when s = glob_S -> add_1 (int_of_nat a)
  | RRef (_,z) when z = glob_O -> zero
  | _ -> raise Non_closed_number
	  
let uninterp_nat p =
  try 
    Some (POS (int_of_nat p))
  with
    Non_closed_number -> None

let rec int_of_nat_pattern = function
  | PatCstr (_,s,[a],_) when ConstructRef s = glob_S ->
      add_1 (int_of_nat_pattern a)
  | PatCstr (_,z,[],_) when ConstructRef z = glob_O -> zero
  | _ -> raise Non_closed_number
	  
let uninterp_nat_pattern p =
  try 
    Some (POS (int_of_nat_pattern p))
  with
    Non_closed_number -> None
*)
