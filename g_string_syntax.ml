(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
open Coqast
open Ast
open Pp
open Util
open Names
open Pcoq
open Libnames
open Topconstr
open G_ascii_syntax

exception Non_closed_string

(* make a string term from the string s *)

let cstring loc = Qualid (loc,make_qualid ["String"] "String")
let cemptystring loc = Qualid (loc,make_qualid ["String"] "EmptyString")

let make_string s dloc =
  let le = (String.length s) in
  let rec aux n = 
     if n = le then CRef (cemptystring dloc) else
     CAppExpl (dloc,(None,cstring dloc),
       [make_ascii dloc (int_of_char s.[n]); aux (n+1)])
     in aux 0

GEXTEND Gram
  GLOBAL: Constr.operconstr;
  Constr.operconstr: LEVEL "0" [ [ s = STRING -> make_string s loc ] ];
END

(** old ast-based pp **)

open Termast

let ascii_path = make_path (make_dir ["Ascii"]) (id_of_string "ascii")
let path_of_Ascii  = ((ascii_path,0),1)
let glob_Ascii  = ConstructRef path_of_Ascii

let string_path = make_path (make_dir ["String"]) (id_of_string "string")
let path_of_EmptyString  = ((string_path,0),1)
let glob_EmptyString  = ConstructRef path_of_EmptyString
let path_of_String  = ((string_path,0),2)
let glob_String  = ConstructRef path_of_String

let astAscii = ast_of_ref glob_Ascii
let astEmptyString = ast_of_ref glob_EmptyString
let astString = ast_of_ref glob_String

let rec ascii_of_ast p =
  match p with
    | Node (_,"APPLIST", (b::l)) when alpha_eq(b,astAscii) ->
        (match alist_val l with
          | None -> raise Non_closed_string
          | Some l -> 
              let v = String.make 1 (char_of_int l) in
              if v="\"" || v="\\"   then "\\"^v else v)
    | _ -> raise Non_closed_string

let rec string_of_ast p =
  match p with
    | b when alpha_eq(b,astEmptyString) ->
        ""
    | Node (_,"APPLIST", [b;c;d]) when alpha_eq(b,astString) ->
        (ascii_of_ast c)^(string_of_ast d)
    | _ -> raise Non_closed_string

let string_printer p =
  try 
    match p with
    | Node (_,"STRING", [c;d]) -> 
        Some (str "\"" ++ str ((ascii_of_ast c)^(string_of_ast d)) ++ str "\"")
    | _ -> failwith "Inconsistent pretty-printer rule"
  with 
   Non_closed_string -> None

let _ = if !Options.v7 then
  Esyntax.declare_primitive_printer "string_printer" "string_scope" 
    string_printer






