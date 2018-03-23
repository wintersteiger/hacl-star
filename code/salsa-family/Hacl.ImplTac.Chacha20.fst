module Hacl.ImplTac.Chacha20

open FStar.HyperStack
open FStar.HyperStack.ST
open Spec.Lib.IntTypes

open Spec.Lib.IntBuf
open Spec.Lib.IntBuf.LoadStore
open Spec.Lib.IntBuf.Lemmas
open Spec.Chacha20

module ST = FStar.HyperStack.ST
module LSeq = Spec.Lib.IntSeq
module Spec = Spec.Chacha20

module T = FStar.Tactics

(* Definition of the state *)
type state = lbuffer uint32 16
type idx = n:size_t{v n < 16}


inline_for_extraction
let v = size_v
inline_for_extraction
let index (x:size_nat) = size x

type shuffle (f: Spec.shuffle) = (st: state) -> Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 ->
    preserves_live h0 h1 /\
    modifies1 st h0 h1 /\
    as_lseq st h1 == f (as_lseq st h0)
  ))

inline_for_extraction
let id : shuffle (fun m -> m) = fun _ -> ()

inline_for_extraction
let seq (f1: Spec.shuffle) (f1_st: shuffle f1) (f2: Spec.shuffle) (f2_st: shuffle f2) : Tot (shuffle (f1 @ f2))
= fun st -> f1_st st; f2_st st

module L = FStar.List.Tot

let rec app_head_rev_tail (t: T.term) :
  T.Tac (T.term * list T.argv)
=
  let ins = T.inspect t in
  if T.Tv_App? ins
  then
    let (T.Tv_App u v) = ins in
    let (x, l) = app_head_rev_tail u in
    (x, v :: l)
  else
    (t, [])

let app_head_tail (t: T.term) :
    T.Tac (T.term * list T.argv)
= let (x, l) = app_head_rev_tail t in
  (x, L.rev l)

let rec binders_of_abs (t: T.term) : T.Tac (list T.binder) =
  match T.inspect t with
  | T.Tv_Abs binder body ->
    binder :: binders_of_abs body
  | _ -> []

noeq
type compile_binders_state = {
  compile_binders_rev_new_args: list T.argv;
  compile_binders_rev_new_binders: list T.binder;
  compile_binders_new_env: T.env;
}

let rec compile_binders (s: compile_binders_state) (l: list T.binder) : T.Tac compile_binders_state =
  match l with
  | binder :: body ->
      let binder_ty = T.type_of_binder binder in
      let new_arg, new_binder =
        if T.term_eq binder_ty (quote Spec.idx)
        then 
          let new_binder_ty = quote idx in
          let new_binder = T.fresh_binder new_binder_ty in
          let new_binder_tm = T.pack (T.Tv_Var (T.bv_of_binder new_binder)) in
          ((T.mk_app (quote v) [new_binder_tm, T.Q_Explicit], T.Q_Explicit), new_binder)
        else if T.term_eq binder_ty (quote Spec.state)
        then T.fail "State is forbidden" // quote state
        else 
          let new_binder = T.fresh_binder binder_ty in
            let new_binder_tm = T.pack (T.Tv_Var (T.bv_of_binder new_binder)), T.Q_Explicit in
            let nb = new_binder in
            (new_binder_tm, nb)
      in
      let new_bv = T.bv_of_binder new_binder in
      compile_binders ({
        compile_binders_rev_new_args = new_arg :: s.compile_binders_rev_new_args;
        compile_binders_rev_new_binders = new_binder :: s.compile_binders_rev_new_binders;
        compile_binders_new_env = T.push_binder s.compile_binders_new_env new_binder;
      })
      body
  | _ -> s

// FIXME: is there any way to determine, in a function definition, whether a binder binds an implicit argument?

let compile_abs (t: T.term) : T.Tac compile_binders_state =
  let l = binders_of_abs t in
  let env = T.cur_env () in
  compile_binders
      ({
        compile_binders_rev_new_args = [];
        compile_binders_rev_new_binders = [];
        compile_binders_new_env = env;
      })
      l

let unfold_fv (t: T.fv) : T.Tac T.term =
  let env = T.cur_env () in
  let n = T.inspect_fv t in
  match T.lookup_typ env n with
  | Some s ->
    begin match T.inspect_sigelt s with
    | T.Sg_Let false _ _ def -> def
    | _ -> T.fail "Not a non-recursive let definition"
    end
  | _ -> T.fail "Definition not found"

let unfold' (t: T.term) : T.Tac T.term =
  match T.inspect t with
  | T.Tv_FVar fv -> unfold_fv fv
  | _ -> T.fail "Not a FV"

let _ = T.assert_by_tactic True (fun () ->
  let s = unfold' (quote Spec.quarter_round) in
  let env = T.cur_env () in
  let s' = compile_abs s in
  let l = s'.compile_binders_rev_new_binders in
  match l with [] -> () | a::_ -> begin
    T.print (T.term_to_string (T.type_of_binder a))
  end
)

inline_for_extraction
let plus_equal (a b: idx) : Tot (shuffle (plus_equal (v a) (v b))) =
  fun st -> st.(a) <- 
    let sta = st.(a) in
    let stb = st.(b) in
    add_mod #U32 sta stb

assume val line (a b d: idx) (s: rotval U32) : Tot (shuffle (Spec.line (v a) (v b) (v d) s))

let rec list_all_but_last (#a: Type) (l: list a) : T.Tac (list a) =
  match l with
  | [] -> T.fail "all_but_last"
  | [_] -> []
  | b :: q -> b :: list_all_but_last q

let rec list_last (#a: Type) (l: list a) : T.Tac a =
  match l with
  | [] -> T.fail "last"
  | [b] -> b
  | _ :: q -> list_last q

let transfer_lid_module_to_lid
  (lid_module: T.term)
  (lid_id: T.term)
: T.Tac T.fv
= let i_module = T.inspect lid_module in
  let i_id = T.inspect lid_id in
  match i_module, i_id with
  | T.Tv_FVar v_module, T.Tv_FVar v_id ->
    let module_name = list_all_but_last (T.inspect_fv v_module) in
    let id = list_last (T.inspect_fv v_id) in
    T.pack_fv (L.append module_name [id])
  | _ -> T.fail "make_lid_from_lid_module"

private let some_lid_in_this_module : unit = ()

let transfer_lid_to_this_module
  (lid: T.term)
: T.Tac T.fv
= transfer_lid_module_to_lid (quote some_lid_in_this_module) lid

(*
let l' :  (a: idx) -> (b: idx) -> (d: idx) -> (s: rotval U32) -> Tot (shuffle (Spec.line (v a) (v b) (v d) s)) =
  T.synth_by_tactic (fun () -> T.exact (T.pack (T.Tv_FVar (transfer_lid_module_to_lid some_lid_in_this_module Spec.line))))
*)

let rec compare_module_names (name1 name2: list string) : Tot bool =
  match name1, name2 with
  | [_], [_] -> true
  | a1 :: q1, a2 :: q2 -> a1 = a2 && compare_module_names q1 q2
  | _ -> false

let is_in_same_module_as (t1 t2: T.term) : T.Tac bool =
  let i1 = T.inspect t1 in
  let i2 = T.inspect t2 in
  match i1, i2 with
  | T.Tv_FVar v1, T.Tv_FVar v2 ->
    let n1 = T.inspect_fv v1 in
    let n2 = T.inspect_fv v2 in
    compare_module_names n1 n2
  | _ -> false

let rec compile (ty: T.term) (t: T.term) : T.Tac T.term =
    let (hd, tl) = app_head_tail t in
    if T.term_eq hd (quote Spec.op_At)
    then begin
      match L.rev tl with // BEWARE we reverse the list of arguments here
      | (ar2, T.Q_Explicit) :: (ar1, T.Q_Explicit) :: _ ->
        let ar1' = compile ty ar1 in
        let ar2' = compile ty ar2 in
        let ty = quote Spec.shuffle in
        T.mk_app (quote seq) [
          ar1, T.Q_Explicit;
          ar1', T.Q_Explicit;
          ar2, T.Q_Explicit;
          ar2', T.Q_Explicit;
        ]
      | _ -> T.fail "app"
    end else
    if hd `T.term_eq` (quote v)
    then begin
      match tl with
      | [ar, _] -> ar
      | _ -> T.fail "v"
    end else
    if
      hd `is_in_same_module_as` (quote Spec.state)
    then
      let tdef = unfold' hd in
      let binders = binders_of_abs tdef in
      let hd' = T.pack (T.Tv_FVar (transfer_lid_to_this_module hd)) in
      let tl' = compile_args binders tl in
      T.mk_app hd' tl'
    else
    let ins = T.inspect t in
    if
      let q = quote Spec.idx in
      if T.term_eq ty q
      then
        if T.Tv_Const? ins
        then
          let (T.Tv_Const c) = ins in
          T.C_Int? c
        else false
      else false
    then
      T.mk_app (quote index) [t, T.Q_Explicit]
    else
      (* do not change terms that start with a head symbol that is not a spec function *)
      t

and compile_args (binders: list T.binder) (tl: list T.argv) : T.Tac (list T.argv) =
  match binders, tl with
  | (b :: binders'), ((ar, qual) :: tlq) ->
    let ty = T.type_of_binder b in
    let ar' = compile ty ar in
    (ar', qual) :: compile_args binders' tlq
  | _, [] -> []
  | _ -> T.fail "compile_args: more arguments than binders"

let rec mk_abs (l: list T.binder) (body: T.term) : T.Tac T.term =
  match l with
  | [] -> body
  | b :: q ->
    let body' = mk_abs q body in
    T.pack (T.Tv_Abs b body')

inline_for_extraction
let coerce_shuffle
  (f: Spec.shuffle)
  (f_st: shuffle f)
  (f' : Spec.shuffle)
  (u: unit { (forall s . f s == f' s) } )
: Tot (shuffle f')
= fun s -> f_st s

let compile_def (#a: Type) (v: a) : T.Tac T.term =
  let t_folded = quote v in
  let t_unfolded = unfold' t_folded in
  let env = T.cur_env () in
  let state = compile_abs t_unfolded in
  let new_args = L.rev state.compile_binders_rev_new_args in
  let spec_folded = T.mk_app t_folded new_args in
  let spec_unfolded =
    T.norm_term_env state.compile_binders_new_env [] (T.mk_app t_unfolded new_args)
  in
  let body_before_coerce = compile (quote Spec.shuffle) spec_unfolded in
  let q : T.term = quote () in
  let body = T.mk_app (quote coerce_shuffle) [
    spec_unfolded, T.Q_Explicit;
    body_before_coerce, T.Q_Explicit;
    spec_folded, T.Q_Explicit;
    q, T.Q_Explicit;
  ]
  in
  let res = mk_abs (L.rev state.compile_binders_rev_new_binders) body in
  T.print (T.term_to_string res) ;
  res

#reset-options "--print_bound_var_types --print_full_names"

let _ = T.assert_by_tactic True (fun () ->
  let _ = compile_def Spec.quarter_round in
  ()
)

let synth_def (#a: Type) (v: a) : T.Tac unit =
   let res = compile_def v in
   T.exact res

(*
let quarter_round : (a: idx) -> (b: idx) -> (c: idx) -> (d: idx) -> Tot (
shuffle (Spec.quarter_round (v a) (v b) (v c) (v d))) =
  T.synth_by_tactic (fun () -> synth_def Spec.quarter_round)
*)

let rec mk_arrow (l: list T.binder) (body: T.term) : T.Tac T.term =
  match l with
  | [] -> body
  | b :: q ->
    let body' = mk_arrow q body in
    T.pack (T.Tv_Arrow b (T.pack_comp (T.C_Total body' None)))

let compile_type_of (#a: Type) (v: a) : T.Tac T.term =
  let t_folded = quote v in
  let t_unfolded = unfold' t_folded in
  let state = compile_abs t_unfolded in
  let body = T.mk_app (quote shuffle) [
    T.mk_app t_folded (L.rev state.compile_binders_rev_new_args), T.Q_Explicit;
  ]
  in
  mk_arrow (L.rev state.compile_binders_rev_new_binders) body

let synth_type_of  (#a: Type) (v: a) : T.Tac unit =
  let res = compile_type_of v in
  T.exact res

let quarter_round : T.synth_by_tactic (fun () -> synth_type_of Spec.quarter_round) =
  T.synth_by_tactic (fun () -> synth_def Spec.quarter_round)

let column_round : T.synth_by_tactic (fun () -> synth_type_of Spec.column_round) =
  T.synth_by_tactic (fun () -> synth_def Spec.column_round)

let diagonal_round : T.synth_by_tactic (fun () -> synth_type_of Spec.diagonal_round) =
  T.synth_by_tactic (fun () -> synth_def Spec.diagonal_round)

let double_round : T.synth_by_tactic (fun () -> synth_type_of Spec.double_round) =
  T.synth_by_tactic (fun () -> synth_def Spec.double_round)
