(* hashcheck.ml -- recompute Megalodon content hashes with Megalodon's own code.

   The round trip in `reverse_translate.py` establishes that the terms
   recovered from Lean are structurally identical to the ones Megalodon
   exported. That is a comparison between two s-expressions, which is one
   step short of the claim worth making: that Megalodon assigns them the
   same content hash.

   This closes that step. It reads the reconstructed terms, rebuilds
   Megalodon's own `tm` values from them, and calls `Syntax.ptm_all_id`
   -- the very function Megalodon uses to assign a proposition its id --
   so the hashes are computed by Megalodon's code rather than by a
   reimplementation of it.

   Input lines:  (RECON "<name>" <kind> <poly> <tm-sexpr>)
   where <kind> is `all` for a proposition (AXIOM/THM, which Megalodon
   ids with `ptm_all_id`) or `lam` for a definition body (DEF, which it
   ids with `ptm_lam_id`).
   Output lines: <name> <hash>

   Build (from a built Megalodon tree):
     ocamlopt -I bin -o bin/hashcheck unix.cmxa bin/ser.cmx bin/hashaux.cmx \
       bin/sha256.cmx bin/hash.cmx bin/mathdata.cmx bin/mathdatapfg.cmx \
       bin/syntax.cmx hashcheck.ml
*)

type sx = A of string | L of sx list

let parse_sexpr (s : string) : sx * int =
  let n = String.length s in
  let rec go i =
    let i = skip i in
    if i >= n then failwith "unexpected end of input"
    else if s.[i] = '(' then
      let rec items acc i =
        let i = skip i in
        if i < n && s.[i] = ')' then (L (List.rev acc), i + 1)
        else let (x, i) = go i in items (x :: acc) i
      in items [] (i + 1)
    else if s.[i] = '"' then
      let b = Buffer.create 64 in
      let rec str j =
        if s.[j] = '"' then (A (Buffer.contents b), j + 1)
        else if s.[j] = '\\' then (Buffer.add_char b s.[j+1]; str (j + 2))
        else (Buffer.add_char b s.[j]; str (j + 1))
      in str (i + 1)
    else
      let j = ref i in
      while !j < n && s.[!j] <> ' ' && s.[!j] <> '(' && s.[!j] <> ')'
            && s.[!j] <> '\t' do incr j done;
      (A (String.sub s i (!j - i)), !j)
  and skip i =
    if i < n && (s.[i] = ' ' || s.[i] = '\t' || s.[i] = '\n' || s.[i] = '\r')
    then skip (i + 1) else i
  in go 0

let rec to_tp (x : sx) : Syntax.tp =
  match x with
  | L [A "PROP"] -> Syntax.Prop
  | L [A "SET"] -> Syntax.Set
  | L [A "TPVAR"; A i] -> Syntax.TpVar (int_of_string i)
  | L [A "AR"; a; b] -> Syntax.Ar (to_tp a, to_tp b)
  | _ -> failwith "to_tp: unrecognised type"

let rec to_tm (x : sx) : Syntax.tm =
  match x with
  | L [A "DB"; A i] -> Syntax.DB (int_of_string i)
  | L [A "TMH"; A h] -> Syntax.TmH h
  | L [A "PRIM"; A i] -> Syntax.Prim (int_of_string i)
  | L [A "AP"; f; a] -> Syntax.Ap (to_tm f, to_tm a)
  | L [A "TPAP"; f; a] -> Syntax.TpAp (to_tm f, to_tp a)
  | L [A "LAM"; a; m] -> Syntax.Lam (to_tp a, to_tm m)
  | L [A "IMP"; p; q] -> Syntax.Imp (to_tm p, to_tm q)
  | L [A "ALL"; a; m] -> Syntax.All (to_tp a, to_tm m)
  | _ -> failwith "to_tm: unrecognised term"

(* ptm_all_id ignores these, but its type demands them *)
let sof : (string, Syntax.ptp) Hashtbl.t = Hashtbl.create 1
let sdel : (string, Syntax.ptm) Hashtbl.t = Hashtbl.create 1

let () =
  let path = Sys.argv.(1) in
  let ch = open_in path in
  let ok = ref 0 and bad = ref 0 in
  (try
     while true do
       let line = input_line ch in
       let line = String.trim line in
       if String.length line > 0 && line.[0] = '(' then begin
         match fst (parse_sexpr line) with
         | L [A "RECON"; A name; A kind; A poly; body] ->
             (try
                let m = to_tm body in
                let p = int_of_string poly in
                let h =
                  if kind = "lam" then Syntax.ptm_lam_id (p, m) sof sdel
                  else Syntax.ptm_all_id (p, m) sof sdel
                in
                Printf.printf "%s %s\n" name h;
                incr ok
              with e ->
                Printf.eprintf "FAILED %s: %s\n" name (Printexc.to_string e);
                incr bad)
         | _ -> ()
       end
     done
   with End_of_file -> ());
  close_in ch;
  Printf.eprintf "hashed %d terms, %d failed\n" !ok !bad
