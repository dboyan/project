(* Module Main: The main program.  Deals with processing the command
   line, reading files, building and connecting lexers and parsers, etc. 
   
   For most experiments with the implementation, it should not be
   necessary to change this file.
*)

open Format
open Support.Pervasive
open Support.Error
open Syntax
open Core

let di = dummyinfo

let cmds = [
    Eval(di,
        TmApp(di,
            TmAbs(di, "x", TyInt([(1, 5)]), TmPlus(di, TmVar(di, 0, 1), TmInt(di, 2))),
            TmInt(di,1)));
    Eval(di,
        TmAbs(di, "y", TyInt([(4, 7); (10, 13)]),
            TmMinus(di,
                TmVar(di, 0, 1),
                TmInt(di, 3))));
    Eval(di,
        TmApp(di,
            TmAbs(di, "x", TyInt([(20, 40)]),
                TmIf(di,
                    TmGreater(di,
                        TmVar(di, 0, 0),
                        TmInt(di, 30)),
                    TmPlus(di,
                        TmVar(di, 0, 0),
                        TmInt(di, 10)),
                    TmMinus(di,
                        TmVar(di, 0, 0),
                        TmInt(di, 10)))),
            TmInt(di, 35)));
    Eval(di,
        TmApp(di,
            TmAbs(di, "x", TyInt([(20, 40)]),
                TmIf(di,
                    TmLess(di,
                        TmVar(di, 0, 0),
                        TmInt(di, 30)),
                    TmInt(di, 10),
                    TmInt(di, 50))),
            TmInt(di, 35)));
    Eval(di,
        TmAbs(di, "x", TyInt([(0,65535)]),
        TmAbs(di, "y", TyInt([(0,65535)]),
            TmPlus(di,
                TmVar(di, 1, 0),
                TmVar(di, 0, 0)))));
]

let searchpath = ref [""]

let argDefs = [
  "-I",
      Arg.String (fun f -> searchpath := f::!searchpath),
      "Append a directory to the search path"]

let parseArgs () =
  let inFile = ref (None : string option) in
  Arg.parse argDefs
     (fun s ->
       match !inFile with
         Some(_) -> err "You must specify exactly one input file"
       | None -> inFile := Some(s))
     "";
  match !inFile with
      None -> err "You must specify an input file"
    | Some(s) -> s

let openfile infile = 
  let rec trynext l = match l with
        [] -> err ("Could not find " ^ infile)
      | (d::rest) -> 
          let name = if d = "" then infile else (d ^ "/" ^ infile) in
          try open_in name
            with Sys_error m -> trynext rest
  in trynext !searchpath

let alreadyImported = ref ([] : string list)

let checkbinding fi ctx b = match b with
    NameBind -> NameBind
  | VarBind(tyT) -> VarBind(tyT)
  | TmAbbBind(t,None) -> TmAbbBind(t, Some(typeof ctx t))
  | TmAbbBind(t,Some(tyT)) ->
     let tyT' = typeof ctx t in
     if subtype ctx tyT' tyT then TmAbbBind(t,Some(tyT))
     else error fi "Type of binding does not match declared type"
  | TyVarBind -> TyVarBind
  | TyAbbBind(tyT) -> TyAbbBind(tyT)

let prbindingty ctx b = match b with
    NameBind -> ()
  | TyVarBind -> ()
  | VarBind(tyT) -> pr ": "; printty ctx tyT 
  | TmAbbBind(t, tyT_opt) -> pr ": ";
     (match tyT_opt with
         None -> printty ctx (typeof ctx t)
       | Some(tyT) -> printty ctx tyT)
  | TyAbbBind(tyT) -> pr ":: *"

let rec process_command ctx cmd = match cmd with
  | Eval(fi,t) -> 
      let tyT = typeof ctx t in
      let t' = eval ctx t in
      printtm_ATerm true ctx t'; 
      print_break 1 2;
      pr ": ";
      printty ctx tyT;
      force_newline();
      ctx
  | Bind(fi,x,bind) -> 
      let bind = checkbinding fi ctx bind in
      let bind' = evalbinding ctx bind in
      pr x; pr " "; prbindingty ctx bind'; force_newline();
      addbinding ctx x bind'
  
let process ctx =
  let g ctx c =  
    open_hvbox 0;
    let results = process_command ctx c in
    print_flush();
    results
  in
    List.fold_left g ctx cmds

let main () = 
  let _ = process emptycontext in
  ()

let () = set_max_boxes 1000
let () = set_margin 67
let res = 
  Printexc.catch (fun () -> 
    try main();0 
    with Exit x -> x) 
  ()
let () = print_flush()
let () = exit res
