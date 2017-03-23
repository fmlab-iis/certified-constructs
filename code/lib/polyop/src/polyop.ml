
open Num
open Unix
open Names

let singular_path = "Singular"
let magma_path = "magma"
let vname = "x"

type engine = Singular | Magma

let default_engine = Singular

(* ------------------------------------------------------------------------- *)
(*  Debugging                                                                *)
(* ------------------------------------------------------------------------- *)

let gbdir = "."

let unix s =
  let r = Unix.system s in
  if r = r then ()
  else ()

let init_trace () =
  unix ("echo \"\" > " ^ gbdir ^ "/log_gb")

let trace s =
  unix ("echo \"" ^ s ^ "\n\" >> " ^ gbdir ^ "/log_gb")

let pp_constr x = Pp.msg (Printer.pr_constr x)

let print_constr t =
  if Term.isRel t then trace "Rel"
  else if Term.isVar t then trace "Var"
  else if Term.isInd t then trace "Ind"
  else if Term.isEvar t then trace "Evar"
  else if Term.isMeta t then trace "Meta"
  else if Term.isSort t then trace "Sort"
  else if Term.isCast t then trace "Cast"
  else if Term.isApp t then trace "App"
  else if Term.isLambda t then trace "Lambda"
  else if Term.isLetIn t then trace "LetIn"
  else if Term.isProd t then trace "Prod"
  else if Term.isConst t then trace "Const"
  else if Term.isConstruct t then trace "Construct"
  else if Term.isFix t then trace "Fix"
  else if Term.isCoFix t then trace "CoFix"
  else if Term.isCase t then trace "Case"
  else if Term.isProj t then trace "Proj"
  else trace ""



(* ------------------------------------------------------------------------- *)
(*  Access Coq terms                                                         *)
(* ------------------------------------------------------------------------- *)

(* The contrib name is used to locate errors when loading constrs *)
let contrib_name = "polyop_plugin"

let find_constant contrib dir s =
  Universes.constr_of_global (Coqlib.find_reference contrib dir s)

let init_constant dir s = find_constant contrib_name dir s

let fresh_id_in_env avoid id env =
  (* ids to be avoided *)
  let ids = (avoid@Termops.ids_of_named_context (Environ.named_context env)) in
  (* generate a new id *)
  Namegen.next_ident_away_in_goal id ids

let new_fresh_id avoid id gl =
  fresh_id_in_env avoid id (Proofview.Goal.env gl)



(* ------------------------------------------------------------------------- *)
(*  Positive                                                                 *)
(* ------------------------------------------------------------------------- *)

module CoqBinNums = struct
  let path = ["Coq"; "Numbers"; "BinNums"]
  let _xI : Term.constr lazy_t = lazy (init_constant path "xI")
  let _xO : Term.constr lazy_t = lazy (init_constant path "xO")
  let _xH : Term.constr lazy_t = lazy (init_constant path "xH")
  let _Z0 : Term.constr lazy_t = lazy (init_constant path "Z0")
  let _Zpos : Term.constr lazy_t = lazy (init_constant path "Zpos")
  let _Zneg : Term.constr lazy_t = lazy (init_constant path "Zneg")
end

let num_0 = Int 0
let num_1 = Int 1
let num_2 = Int 2
let num_10 = Int 10

(** Constructs a Coq positive from an OCaml num. *)
let rec cpos_of_onum (n : num) : Constr.t =
  if n </ num_0 then failwith "Not a positive number."
  else if n =/ num_1 then Lazy.force CoqBinNums._xH
  else if mod_num n num_2 =/ num_0 then Constr.mkApp (Lazy.force CoqBinNums._xO, [| cpos_of_onum (quo_num n num_2) |])
  else Constr.mkApp (Lazy.force CoqBinNums._xI, [| cpos_of_onum (quo_num n num_2) |])

(** Constructs an OCaml num from a Coq positive. *)
let rec onum_of_cpos (n : Constr.t) : num =
  if Constr.equal n (Lazy.force CoqBinNums._xH) then num_1
  else
    try
      let (constructor, args) = Term.destApp n in
      if Constr.equal constructor (Lazy.force CoqBinNums._xI) then num_1 +/ (onum_of_cpos args.(0) */ num_2)
      else if Constr.equal constructor (Lazy.force CoqBinNums._xO) then num_0 +/ (onum_of_cpos args.(0) */ num_2)
      else failwith "Not a valid Coq positive."
    with destKO -> failwith "Not a valid Coq positive."

(** Constructs a Coq integer from an OCaml num. *)
let rec cz_of_onum (n : num) : Constr.t =
  if n =/ num_0 then Lazy.force CoqBinNums._Z0
  else if n >/ num_0 then Constr.mkApp (Lazy.force CoqBinNums._Zpos, [| cpos_of_onum n |])
  else Constr.mkApp (Lazy.force CoqBinNums._Zneg, [| cpos_of_onum (abs_num n) |])

(** Constructs an OCaml num from a Coq integer. *)
let onum_of_cz (n : Constr.t) : num =
  if Constr.equal n (Lazy.force CoqBinNums._Z0) then num_0
  else
    try
      let (constructor, args) = Term.destApp n in
      if Constr.equal constructor (Lazy.force CoqBinNums._Zpos) then onum_of_cpos args.(0)
      else if Constr.equal constructor (Lazy.force CoqBinNums._Zneg) then minus_num (onum_of_cpos args.(0))
      else failwith "Not a valid Coq integer."
    with destKO -> failwith "Not a valid Coq integer."

(** Constructs a Coq positive from a number string in OCaml. *)
let cpos_of_ostring (str : string) : Constr.t =
  cpos_of_onum (num_of_string str)

(** Constructs a number string in OCaml from a Coq positive. *)
let ostring_of_cpos (n : Constr.t) : string =
  string_of_num (onum_of_cpos n)



(* ------------------------------------------------------------------------- *)
(*  Term                                                                     *)
(* ------------------------------------------------------------------------- *)

module CoqTerm = struct
  let path = ["PolyOp"; "PolyOp"]
  let _Zero : Term.constr lazy_t = lazy (init_constant path "Zero")
  let _Const : Term.constr lazy_t = lazy (init_constant path "Const")
  let _Var : Term.constr lazy_t = lazy (init_constant path "Var")
  let _Opp : Term.constr lazy_t = lazy (init_constant path "Opp")
  let _Add : Term.constr lazy_t = lazy (init_constant path "Add")
  let _Sub : Term.constr lazy_t = lazy (init_constant path "Sub")
  let _Mul : Term.constr lazy_t = lazy (init_constant path "Mul")
  let _Pow : Term.constr lazy_t = lazy (init_constant path "Pow")
  let _Singular : Term.constr lazy_t = lazy (init_constant path "Singular")
  let _Magma : Term.constr lazy_t = lazy (init_constant path "Magma")
end

type vname = string

type term =
  | Zero
  | Const of Num.num
  | Var of vname
  | Opp of term
  | Add of (term * term)
  | Sub of (term * term)
  | Mul of (term * term)
  | Pow of (term * int)

let is_atomic t =
  match t with
  | Zero | Const _ | Var _ -> true
  | _ -> false

let rec string_of_term (t : term) : string =
  match t with
  | Zero -> "0"
  | Const n -> Num.string_of_num n
  | Var v -> vname ^ v
  | Opp t ->
     if is_atomic t then "-" ^ string_of_term t ^ ""
     else "-(" ^ string_of_term t ^ ")"
  | Add (t1, t2) ->
     (if is_atomic t1 then string_of_term t1 else "(" ^ string_of_term t1 ^ ")")
     ^ " + "
     ^ (if is_atomic t2 then string_of_term t2 else "(" ^ string_of_term t2 ^ ")")
  | Sub (t1, t2) ->
     (if is_atomic t1 then string_of_term t1 else "(" ^ string_of_term t1 ^ ")")
     ^ " - "
     ^ (if is_atomic t2 then string_of_term t2 else "(" ^ string_of_term t2 ^ ")")
  | Mul (t1, t2) ->
     (if is_atomic t1 then string_of_term t1 else "(" ^ string_of_term t1 ^ ")")
     ^ " * "
     ^ (if is_atomic t2 then string_of_term t2 else "(" ^ string_of_term t2 ^ ")")
  | Pow (t1, t2) ->
     (if is_atomic t1 then string_of_term t1 else "(" ^ string_of_term t1 ^ ")")
     ^ " ^ "
     ^ string_of_int t2

let numdom r =
  let r' = Ratio.normalize_ratio (ratio_of_num r) in
  num_of_big_int(Ratio.numerator_ratio r'),
  num_of_big_int(Ratio.denominator_ratio r')

(** Constructs a Coq term from an OCaml term. *)
let rec cterm_of_oterm (t : term) : Constr.t =
  match t with
    Zero -> Lazy.force CoqTerm._Zero
  | Const n ->
     let (m, d) = numdom n in
     Constr.mkApp (Lazy.force CoqTerm._Const, [| cz_of_onum m; cpos_of_onum d |])
  | Var v -> Constr.mkApp (Lazy.force CoqTerm._Var, [| cpos_of_ostring v |])
  | Opp t' -> Constr.mkApp (Lazy.force CoqTerm._Opp, [| cterm_of_oterm t' |])
  | Add (t1, t2) -> Constr.mkApp (Lazy.force CoqTerm._Add, [| cterm_of_oterm t1; cterm_of_oterm t2 |])
  | Sub (t1, t2) -> Constr.mkApp (Lazy.force CoqTerm._Sub, [| cterm_of_oterm t1; cterm_of_oterm t2 |])
  | Mul (t1, t2) -> Constr.mkApp (Lazy.force CoqTerm._Mul, [| cterm_of_oterm t1; cterm_of_oterm t2 |])
  | Pow (t', n) ->
     if n = 0 then cterm_of_oterm (Const (Int 1))
     else if n > 0 then Constr.mkApp (Lazy.force CoqTerm._Pow, [| cterm_of_oterm t'; cpos_of_onum (Int n) |])
     else failwith ("The exponent cannot be negative in the term: " ^ string_of_term t)

(** Constructs an OCaml term from a Coq term. *)
let rec oterm_of_cterm (t : Constr.t) : term =
  if Term.isConst t then
    match Global.body_of_constant (Univ.out_punivs (Term.destConst t)) with
      None -> failwith "Failed to find the definition of constant."
    | Some t' -> oterm_of_cterm t'
  else if Constr.equal t (Lazy.force CoqTerm._Zero) then Zero
  else
    try
      let (constructor, args) = Term.destApp t in
      if Constr.equal constructor (Lazy.force CoqTerm._Const) then Const ((onum_of_cz args.(0)) // (onum_of_cpos args.(1)))
      else if Constr.equal constructor (Lazy.force CoqTerm._Var) then Var (ostring_of_cpos args.(0))
      else if Constr.equal constructor (Lazy.force CoqTerm._Opp) then Opp (oterm_of_cterm args.(0))
      else if Constr.equal constructor (Lazy.force CoqTerm._Add) then Add (oterm_of_cterm args.(0), oterm_of_cterm args.(1))
      else if Constr.equal constructor (Lazy.force CoqTerm._Sub) then Sub (oterm_of_cterm args.(0), oterm_of_cterm args.(1))
      else if Constr.equal constructor (Lazy.force CoqTerm._Mul) then Mul (oterm_of_cterm args.(0), oterm_of_cterm args.(1))
      else if Constr.equal constructor (Lazy.force CoqTerm._Pow) then Pow (oterm_of_cterm args.(0), int_of_num (onum_of_cpos args.(1)))
      else let _ = trace "fail" in failwith "Not a valid term (2)."
    with destKO -> let _ = trace "fail2" in failwith "Not a valid term (1)."



(* ------------------------------------------------------------------------- *)
(*  Engines                                                                  *)
(* ------------------------------------------------------------------------- *)

let coq_singular = 1
let coq_magma = 2

let convert_coq_engine (v : Globnames.global_reference) : engine =
  match v with
  | Globnames.ConstructRef ((ind, _), idx) when Names.MutInd.to_string ind = "PolyOp.PolyOp.engine" ->
     if idx = coq_singular then Singular
     else if idx = coq_magma then Magma
     else failwith "Unknown algorithm."
  | Globnames.ConstRef cr ->
     begin
     match Global.body_of_constant cr with
     | None -> failwith "Unknown algorithm."
     | Some c ->
        if Constr.equal c (Lazy.force CoqTerm._Singular) then Singular
        else if Constr.equal c (Lazy.force CoqTerm._Magma) then Magma
        else failwith "Unknown algorithm."
     end
  | _ -> failwith "Unknown algorithm."

(* ------------------------------------------------------------------------- *)
(*  Find witness                                                             *)
(* ------------------------------------------------------------------------- *)

let rec sum_terms ts =
  match ts with
  | [] -> Zero
  | t::[] -> t
  | t::ts -> Add (t, sum_terms ts)

let rec mul_terms ts =
  match ts with
  | [] -> Zero
  | t::[] -> t
  | t::ts -> Mul (t, mul_terms ts)

let split_regexp rexp s =
  try (Str.split (Str.regexp rexp) s)
  with _ -> [s]

let replace e x s =
  Str.global_replace (Str.regexp e) x s

let mk_pow t p =
  if p = 1 then t
  else Pow (t, p)

(** Get the number of variables. *)
let num_of_vars t =
  let nvars = ref 0 in
  let rec helper t =
    match t with
    | Zero -> ()
    | Const _ -> ()
    | Var v -> nvars := max (!nvars) (int_of_string v)
    | Opp t1 -> helper t1
    | Add (t1, t2) -> helper t1; helper t2
    | Sub (t1, t2) -> helper t1; helper t2
    | Mul (t1, t2) -> helper t1; helper t2
    | Pow (t1, n) -> helper t1 in
  let _ = helper t in
  !nvars

(** Generate n variables. *)
let gen_vars n =
  let lvar = ref [] in
  let _ = for i = 1 to n do lvar := [vname ^ (string_of_int i)]@(!lvar); done in
  !lvar

let rec singular_string_of_term (t : term) : string =
  match t with
  | Zero -> "0"
  | Const n -> "number(" ^ Num.string_of_num n ^ ")"
  | Var v -> vname ^ v
  | Opp t ->
     if is_atomic t then "-" ^ singular_string_of_term t ^ ""
     else "-(" ^ singular_string_of_term t ^ ")"
  | Add (t1, t2) ->
     (if is_atomic t1 then singular_string_of_term t1 else "(" ^ singular_string_of_term t1 ^ ")")
     ^ " + "
     ^ (if is_atomic t2 then singular_string_of_term t2 else "(" ^ singular_string_of_term t2 ^ ")")
  | Sub (t1, t2) ->
     (if is_atomic t1 then singular_string_of_term t1 else "(" ^ singular_string_of_term t1 ^ ")")
     ^ " - "
     ^ (if is_atomic t2 then singular_string_of_term t2 else "(" ^ singular_string_of_term t2 ^ ")")
  | Mul (t1, t2) ->
     (if is_atomic t1 then singular_string_of_term t1 else "(" ^ singular_string_of_term t1 ^ ")")
     ^ " * "
     ^ (if is_atomic t2 then singular_string_of_term t2 else "(" ^ singular_string_of_term t2 ^ ")")
  | Pow (t1, t2) ->
     (if is_atomic t1 then singular_string_of_term t1 else "(" ^ singular_string_of_term t1 ^ ")")
     ^ " ^ "
     ^ string_of_int t2

let rec magma_string_of_term (t : term) : string =
  match t with
  | Zero -> "0"
  | Const n -> Num.string_of_num n
  | Var v -> vname ^ v
  | Opp t ->
     if is_atomic t then "-" ^ magma_string_of_term t ^ ""
     else "-(" ^ magma_string_of_term t ^ ")"
  | Add (t1, t2) ->
     (if is_atomic t1 then magma_string_of_term t1 else "(" ^ magma_string_of_term t1 ^ ")")
     ^ " + "
     ^ (if is_atomic t2 then magma_string_of_term t2 else "(" ^ magma_string_of_term t2 ^ ")")
  | Sub (t1, t2) ->
     (if is_atomic t1 then magma_string_of_term t1 else "(" ^ magma_string_of_term t1 ^ ")")
     ^ " - "
     ^ (if is_atomic t2 then magma_string_of_term t2 else "(" ^ magma_string_of_term t2 ^ ")")
  | Mul (t1, t2) ->
     (if is_atomic t1 then magma_string_of_term t1 else "(" ^ magma_string_of_term t1 ^ ")")
     ^ " * "
     ^ (if is_atomic t2 then magma_string_of_term t2 else "(" ^ magma_string_of_term t2 ^ ")")
  | Pow (t1, t2) ->
     (if is_atomic t1 then magma_string_of_term t1 else "(" ^ magma_string_of_term t1 ^ ")")
     ^ " ^ "
     ^ string_of_int t2

let write_singular_input file vars p c =
  let input_text =
    "ring r = integer, (" ^ (String.concat "," vars) ^ "), lp;\n"
    ^ "poly f = " ^ (singular_string_of_term p) ^ ";\n"
    ^ "poly g = f / " ^ (singular_string_of_term c) ^ ";\n"
    ^ "g;\n"
    ^ "exit;\n" in
  let ch = open_out file in
  let _ = output_string ch input_text; close_out ch in
  trace "INPUT TO SINGULAR:";
  unix ("cat " ^ file ^ " >>  " ^ gbdir ^ "/log_gb");
  trace ""

let write_magma_input file vars p c =
  let input_text =
    "R := IntegerRing();\n"
    ^ "S<" ^ (String.concat "," vars) ^ "> := PolynomialRing(R, " ^ string_of_int (List.length vars) ^ ");\n"
    ^ "f := " ^ (magma_string_of_term p) ^ ";\n"
    ^ "g := " ^ (magma_string_of_term c) ^ ";\n"
    ^ "h, r := Quotrem(f, g);\n"
    ^ "h;\n"
    ^ "exit;\n" in
  let ch = open_out file in
  let _ = output_string ch input_text; close_out ch in
  trace "INPUT TO MAGMA:";
  unix ("cat " ^ file ^ " >>  " ^ gbdir ^ "/log_gb");
  trace ""

let run_singular ifile ofile =
  let t1 = Unix.gettimeofday() in
  unix (singular_path ^ " -q " ^ ifile ^ " 1> " ^ ofile ^ " 2>&1");
  let t2 = Unix.gettimeofday() in
  trace ("Execution time of Singular: " ^ string_of_float (t2 -. t1) ^ " seconds");
  trace "OUTPUT FROM SINGULAR:";
  unix ("cat " ^ ofile ^ " >>  " ^ gbdir ^ "/log_gb");
  trace ""

let run_magma ifile ofile =
  let t1 = Unix.gettimeofday() in
  unix (magma_path ^ " -b " ^ ifile ^ " 1> " ^ ofile ^ " 2>&1");
  let t2 = Unix.gettimeofday() in
  trace ("Execution time of Magma: " ^ string_of_float (t2 -. t1) ^ " seconds");
  trace "OUTPUT FROM MAGMA:";
  unix ("cat " ^ ofile ^ " >>  " ^ gbdir ^ "/log_gb");
  trace ""

let atomic_of_string str =
  let (v, e) =
    match (split_regexp "\\^" str) with
    | [v] -> (v, 1)
    | [v; e] -> (v, int_of_string e)
    | _ -> failwith "atomic_of_string" in
  let (c, v, e) =
    try (Str.search_forward (Str.regexp "\\-*[0-9]+") v 0;
	 (Big_int.big_int_of_string v, "", 1))
    with _ ->
      let v = replace vname "" v in
      if String.sub v 0 1 = "-"
      then (Big_int.big_int_of_int (-1), String.sub v 1 ((String.length v)-1), e)
      else (Big_int.big_int_of_int 1, v, e)
  in
  if Big_int.eq_big_int c (Big_int.big_int_of_int 1) then mk_pow (Var v) e
  else if Big_int.eq_big_int c (Big_int.big_int_of_int (-1)) then Opp (mk_pow (Var v) e)
  else Const (Big_int c)

let mon_of_string str =
  let t = split_regexp "[\\*]" str in
  let mons = List.map atomic_of_string t in
  mul_terms mons

let term_of_string str =
  let str = replace "-" "+-" str in
  let mons = List.map (mon_of_string) (split_regexp "[\\+]" str) in
  sum_terms mons

let read_singular_output file vars =
  (* read the output *)
  let line = ref "" in
  let ch = open_in file in
  let _ =
    try
	  line := input_line ch
    with _ ->
      failwith "Failed to read the output file" in
  let _ = close_in ch in
  (* parse the output *)
  let res = term_of_string !line in
  trace ("parsed witness: " ^ string_of_term res);
  res

let read_magma_output file vars =
  (* read the output *)
  let lines_rev = ref [] in
  let ch = open_in file in
  let _ =
    try
      while true do
	    lines_rev := input_line ch::!lines_rev
      done
    with End_of_file ->
      () in
  let _ = close_in ch in
  (* parse the output *)
  let line = replace " " "" (String.concat "" (List.rev !lines_rev)) in
  let res = term_of_string line in
  trace ("parsed witness: " ^ string_of_term res);
  res

let pdiv ?engine:engine p c =
  init_trace();
  let eng =
    match engine with
    | None -> default_engine
    | Some e -> e in
  let ifile = Filename.temp_file "inputfgb_" "" in
  let ofile = Filename.temp_file "outputfgb_" "" in
  let nvars = num_of_vars p in
  let vars = gen_vars nvars in
  let res =
    match eng with
    | Singular ->
       let _ = write_singular_input ifile vars p c in
       let _ = run_singular ifile ofile in
       let res = read_singular_output ofile vars in
       res
    | Magma ->
       let _ = write_magma_input ifile vars p c in
       let _ = run_magma ifile ofile in
       let res = read_magma_output ofile vars in
       res in
  res
