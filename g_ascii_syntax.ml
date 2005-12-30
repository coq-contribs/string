(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

open Pp
open Util
open Names
open Pcoq
open Rawterm
open Topconstr
open Libnames
open Coqlib

exception Non_closed_ascii

let make_dir l = make_dirpath (List.map id_of_string (List.rev l))
let make_path dir id = Libnames.encode_kn dir id

let ascii_module = make_dir ["Ascii"]
let ascii_path = make_path ascii_module (id_of_string "ascii")
let path_of_Ascii = ((ascii_path,0),1)
let glob_Ascii  = ConstructRef path_of_Ascii

let interp_ascii dloc p =
  let rec aux n p = 
     if n = 0 then [] else
     let mp = p mod 2 in
     RRef (dloc,if mp = 0 then glob_false else glob_true)
     :: (aux (n-1) (p/2)) in
  RApp (dloc,RRef(dloc,glob_Ascii), aux 8 p)

let interp_ascii_pat dloc p name =
  let rec aux n p = 
     if n = 0 then [] else
     let mp = p mod 2 in
     PatCstr (dloc,(if mp=0 then path_of_false else path_of_true),[],Anonymous)
     :: (aux (n-1) (p/2)) in
  PatCstr (dloc,path_of_Ascii,aux 8 p,name)

let uninterp_ascii r =
  let rec uninterp_bool_list n = function
    | [] when n = 0 -> 0
    | RRef (_,k)::l when k = glob_true  -> 1+2*(uninterp_bool_list (n-1)  l)
    | RRef (_,k)::l when k = glob_false -> 2*(uninterp_bool_list (n-1) l)
    | _ -> raise Non_closed_ascii in
  try 
    let rec aux = function
    | RApp (_,RRef (_,k),l) when k = glob_Ascii -> uninterp_bool_list 8 l
    | _ -> raise Non_closed_ascii
    in Some (aux r)
  with 
   Non_closed_ascii -> None

(** Ad hoc parser *)

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

(* Cannot use location: no compatibility between ocaml 3.08 and 3.09 *)
 
GEXTEND Gram
  GLOBAL: Constr.operconstr;
  Constr.operconstr: LEVEL "0" 
    [ [ "@@"; s = STRING -> fmake_ascii s dummy_loc ] ];
END
