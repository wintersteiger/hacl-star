(**

   This module defines a transformer that performs safe instruction
   reordering.

   Example:

     The following set of instructions can be reordered in any order
     without any observable change in behavior:

       mov rax, 10
       mov rbx, 3

   Usage:

     Given two [codes], [reordering_allowed] tells you whether this
     transformer considers them to be safe permutations of each-other.
     If so, then by using [lemma_reordering], the transformer shows
     that both behave identically (i.e., starting from equivalent
     states, execution of the two [codes] objects should lead to
     equivalent final states).

     If the reordering is not allowed, then this transformer gives a
     (human-readable) reason for why it believes that the reordering
     is not possible.

*)
module Vale.Transformers.InstructionReorder

/// Open all the relevant modules from the x64 semantics.

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.X64.InsLemmas // this one is from [code]; is that ok?; we use it primarily for the sanity checks

/// Open the PossiblyMonad so that we can keep track of failure cases
/// for easier debugging.

open Vale.Transformers.PossiblyMonad

/// Finally some convenience module renamings

module L = FStar.List.Tot

/// We first need to talk about what locations may be accessed (either
/// via a read or via a write) by an instruction.
///
/// This allows us to define read and write sets for instructions.
///
/// REVIEW: Any instruction with [HavocFlags] causes the flags to be
///   part of the write set. Since we don't allow moving instructions
///   past write boundaries which have commonalities, this means that
///   any instruction which havocs the flags will not be allowed to
///   move past another that does the same. We should think of a
///   better way to handle this. One possibility is to tag "intent"
///   into the flags, which means we should be able to move havocing
///   instructions past other havocing instructions. This only fixes
///   up the issue wrt havocs. Another issue might be that we might
///   want to move groups of instructions together. The solution to
///   that would be to group instructions together and move them as a
///   single unit. This will still have the havoc problems, so we will
///   likely need to place some sort of intention bits for the flags.

type access_location : eqtype =
  | ALocMem : access_location
  | ALocStack: access_location
  | ALocReg : reg -> access_location
  | ALocXmm : xmm -> access_location
  | ALocCf : access_location
  | ALocOf : access_location

type access_locations = list access_location

type rw_set = access_locations & access_locations

let access_locations_of_maddr (m:maddr) : access_locations =
  match m with
  | MConst _ -> []
  | MReg r _ -> [ALocReg r]
  | MIndex b _ i _ -> [ALocReg b; ALocReg i]

let access_locations_of_operand (o:operand) : rw_set =
  match o with
  | OConst _ -> [], []
  | OReg r -> [ALocReg r], [ALocReg r]
  | OMem (m, _) -> access_locations_of_maddr m, [ALocMem]
  | OStack (m, _) -> access_locations_of_maddr m, [ALocStack]

let access_locations_of_operand128 (o:operand128) : access_locations & access_locations =
  match o with
  | OReg128 r -> [ALocXmm r], [ALocXmm r]
  | OMem128 (m, _) -> access_locations_of_maddr m, [ALocMem]
  | OStack128 (m, _) -> access_locations_of_maddr m, [ALocStack]

private
let both (x: rw_set) =
  let a, b = x in
  a `L.append` b

let access_locations_of_explicit (t:instr_operand_explicit) (i:instr_operand_t t) : rw_set =
  match t with
  | IOp64 -> access_locations_of_operand i
  | IOpXmm -> access_locations_of_operand128 i

let access_locations_of_implicit (t:instr_operand_implicit) : rw_set =
  match t with
  | IOp64One i -> access_locations_of_operand i
  | IOpXmmOne i -> access_locations_of_operand128 i
  | IOpFlagsCf -> [ALocCf], [ALocCf]
  | IOpFlagsOf -> [ALocOf], [ALocOf]

let rec aux_read_set0 (args:list instr_operand) (oprs:instr_operands_t_args args) : access_locations =
  match args with
  | [] -> []
  | (IOpEx i) :: args ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t_args args) oprs in
    both (access_locations_of_explicit i l) `L.append` aux_read_set0 args r
  | (IOpIm i) :: args ->
    both (access_locations_of_implicit i) `L.append` aux_read_set0 args (coerce #(instr_operands_t_args args) oprs)

let rec aux_read_set1
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args) : access_locations =
  match outs with
  | [] -> aux_read_set0 args oprs
  | (Out, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    fst (access_locations_of_explicit i l) `L.append` aux_read_set1 outs args r
  | (InOut, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    both (access_locations_of_explicit i l) `L.append` aux_read_set1 outs args r
  | (Out, IOpIm i) :: outs ->
    fst (access_locations_of_implicit i) `L.append` aux_read_set1 outs args (coerce #(instr_operands_t outs args) oprs)
  | (InOut, IOpIm i) :: outs ->
    both (access_locations_of_implicit i) `L.append` aux_read_set1 outs args (coerce #(instr_operands_t outs args) oprs)

let read_set (i:instr_t_record) (oprs:instr_operands_t i.outs i.args) : access_locations =
  aux_read_set1 i.outs i.args oprs

let rec aux_write_set
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args) : access_locations =
  match outs with
  | [] -> []
  | (_, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    snd (access_locations_of_explicit i l) `L.append` aux_write_set outs args r
  | (_, IOpIm i) :: outs ->
    snd (access_locations_of_implicit i) `L.append` aux_write_set outs args (coerce #(instr_operands_t outs args) oprs)

let write_set (i:instr_t_record) (oprs:instr_operands_t i.outs i.args) : list access_location =
  let InstrTypeRecord #outs #args #havoc_flags _ = i in
  let ws = aux_write_set outs args oprs in
  match havoc_flags with
  | HavocFlags -> ALocCf :: ALocOf :: ws
  | PreserveFlags -> ws

let rw_set_of_ins (i:ins) : rw_set =
  match i with
  | Instr i oprs _ ->
    read_set i oprs, write_set i oprs
  | Push src t ->
    ALocReg rRsp :: both (access_locations_of_operand src),
    [ALocReg rRsp; ALocStack]
  | Pop dst t ->
    ALocReg rRsp :: ALocStack :: fst (access_locations_of_operand dst),
    ALocReg rRsp :: snd (access_locations_of_operand dst)
  | Alloc _
  | Dealloc _ ->
    [ALocReg rRsp], [ALocReg rRsp]

/// We now need to define what it means for two different access
/// locations to be "disjoint".
///
/// Note that it is safe to say that two operands are not disjoint
/// even if they are, but the converse is not true. That is, to be
/// safe, we can say two operands are disjoint only if it is
/// guaranteed that they are disjoint.

let disjoint_access_location (a1 a2:access_location) : pbool =
  match a1, a2 with
  | ALocCf, ALocCf -> ffalse "carry flag not disjoint from itself"
  | ALocOf, ALocOf -> ffalse "overflow flag not disjoint from itself"
  | ALocCf, _ | ALocOf, _ | _, ALocCf | _, ALocOf -> ttrue
  | ALocMem, ALocMem -> ffalse "memory not disjoint from itself"
  | ALocStack, ALocStack -> ffalse "stack not disjoint from itself"
  | ALocMem, ALocStack | ALocStack, ALocMem -> ttrue
  | ALocReg r1, ALocReg r2 ->
    (r1 <> r2) /- ("register " ^ print_reg_name r1 ^ " not disjoint from itself")
  | ALocXmm r1, ALocXmm r2 ->
    (r1 <> r2) /- ("xmm-register " ^ print_reg_name r1 ^ " not disjoint from itself")
  | ALocReg _, _ | ALocXmm _, _ | _, ALocReg _ | _, ALocXmm _ -> ttrue

let lemma_disjoint_access_location_symmetric (a1 a2:access_location) :
  Lemma
    (ensures (!!(disjoint_access_location a1 a2) = !!(disjoint_access_location a2 a1))) = ()

let disjoint_access_location_from_locations
    (a:access_location) (l:list access_location) : pbool =
  for_all (fun b ->
      disjoint_access_location a b
    ) l

let disjoint_access_locations (l1 l2:list access_location) r : pbool =
  for_all (fun x ->
      disjoint_access_location_from_locations x l2 /+< (r ^ " because ")
  ) l1

let rec lemma_disjoint_access_locations_reason l1 l2 r1 r2 :
  Lemma
    (!!(disjoint_access_locations l1 l2 r1) = !!(disjoint_access_locations l1 l2 r2)) =
  match l1 with
  | [] -> ()
  | _ :: xs -> lemma_disjoint_access_locations_reason xs l2 r1 r2

let rec lemma_disjoint_access_locations_symmetric l1 l2 r :
  Lemma
    (ensures (
        (!!(disjoint_access_locations l1 l2 r) = !!(disjoint_access_locations l2 l1 r))))
    (decreases %[L.length l1 + L.length l2]) =
  match l1, l2 with
  | [], [] -> ()
  | [], x :: xs | x :: xs, [] ->
    lemma_disjoint_access_locations_symmetric xs [] r
  | x :: xs, y :: ys ->
    lemma_disjoint_access_locations_symmetric l1 ys r;
    lemma_disjoint_access_locations_symmetric xs l2 r;
    lemma_disjoint_access_locations_symmetric xs ys r

/// Given two read/write sets corresponding to two neighboring
/// instructions, we can say whether exchanging those two instructions
/// should be allowed.

let rw_exchange_allowed (rw1 rw2 : rw_set) : pbool =
  let (r1, w1), (r2, w2) = rw1, rw2 in
  let disjoint = disjoint_access_locations in
  (disjoint r1 w2 "read set of 1st not disjoint from write set of 2nd") &&.
  (disjoint r2 w1 "read set of 2nd not disjoint from write set of 1st") &&.
  (disjoint w1 w2 "write sets not disjoint")

let ins_exchange_allowed (i1 i2 : ins) : pbool =
  (
    match i1, i2 with
    | Instr _ _ _, Instr _ _ _ ->
      (rw_exchange_allowed (rw_set_of_ins i1) (rw_set_of_ins i2))
    | _, _ ->
      ffalse "non-generic instructions: conservatively disallowed exchange"
  ) /+> normal (" for instructions " ^ print_ins i1 gcc ^ " and " ^ print_ins i2 gcc)

private abstract
let sanity_check_1 =
  assert_norm (!!(
    ins_exchange_allowed
      (make_instr ins_Mov64 (OReg rRax) (OConst 100))
      (make_instr ins_Add64 (OReg rRbx) (OConst 299))))

private abstract
let sanity_check_2 =
  assert_norm (not !!(
    ins_exchange_allowed
      (make_instr ins_Mov64 (OReg rRax) (OConst 100))
      (make_instr ins_Add64 (OReg rRax) (OConst 299))))

let lemma_ins_exchange_allowed_symmetric (i1 i2 : ins) :
  Lemma
    (requires (
        !!(ins_exchange_allowed i1 i2)))
    (ensures (
        !!(ins_exchange_allowed i2 i1))) =
  let b1 = !!(ins_exchange_allowed i1 i2) in
  let b2 = !!(ins_exchange_allowed i2 i1) in
  assert (b1 == !!(rw_exchange_allowed (rw_set_of_ins i1) (rw_set_of_ins i2)));
  assert (b2 == !!(rw_exchange_allowed (rw_set_of_ins i2) (rw_set_of_ins i1)));
  let r1, w1 = rw_set_of_ins i1 in
  let r2, w2 = rw_set_of_ins i2 in
  let disjoint = disjoint_access_locations in
  let aux l1 l2 : (b:bool) = !!(disjoint l1 l2 "") in
  let aux_reason l1 l2 r : Lemma
    (!!(disjoint l1 l2 r) == aux l1 l2) = lemma_disjoint_access_locations_reason l1 l2 "" r in
  FStar.Classical.forall_intro_3 aux_reason;
  assert (b1 == (aux r1 w2 && aux r2 w1 && aux w1 w2));
  assert (b2 == (aux r2 w1 && aux r1 w2 && aux w2 w1));
  lemma_disjoint_access_locations_symmetric w1 w2 "";
  assert (aux w1 w2 = aux w2 w1)

/// First, we must define what it means for two states to be
/// equivalent. Here, we basically say they must be exactly the same.
///
/// TODO: We should figure out a way to handle flags better. Currently
/// any two instructions that havoc flags cannot be exchanged since
/// they will not lead to equiv states.

let equiv_states (s1 s2 : machine_state) : GTot Type0 =
  (s1.ms_ok == s2.ms_ok) /\
  (s1.ms_regs == s2.ms_regs) /\
  (s1.ms_xmms == s2.ms_xmms) /\
  (cf s1.ms_flags = cf s2.ms_flags) /\
  (overflow s1.ms_flags = overflow s2.ms_flags) /\
  (s1.ms_mem == s2.ms_mem) /\
  (s1.ms_memTaint == s2.ms_memTaint) /\
  (s1.ms_stack == s2.ms_stack) /\
  (s1.ms_stackTaint == s2.ms_stackTaint)

(** Same as [equiv_states] but uses extensionality to "think harder";
    useful at lower-level details of the proof. *)
let equiv_states_ext (s1 s2 : machine_state) : GTot Type0 =
  let open FStar.FunctionalExtensionality in
  (feq s1.ms_regs s2.ms_regs) /\
  (feq s1.ms_xmms s2.ms_xmms) /\
  (Map.equal s1.ms_mem s2.ms_mem) /\
  (Map.equal s1.ms_memTaint s2.ms_memTaint) /\
  (Map.equal s1.ms_stack.stack_mem s2.ms_stack.stack_mem) /\
  (Map.equal s1.ms_stackTaint s2.ms_stackTaint) /\
  (equiv_states s1 s2)

private abstract
let sanity_check_equiv_states (s1 s2 s3 : machine_state) :
  Lemma
    (ensures (
        (equiv_states s1 s1) /\
        (equiv_states s1 s2 ==> equiv_states s2 s1) /\
        (equiv_states s1 s2 /\ equiv_states s2 s3 ==> equiv_states s1 s3))) = ()

(** Convenience wrapper around [equiv_states] *)
unfold
let equiv_ostates (s1 s2 : option machine_state) : GTot Type0 =
  (Some? s1 = Some? s2) /\
  (Some? s1 ==>
   (equiv_states (Some?.v s1) (Some?.v s2)))

(** A stricter convenience wrapper around [equiv_states] *)
unfold
let equiv_ostates' (s1 : machine_state) (s2' : option machine_state) : GTot Type0 =
  (Some? s2') /\
  (equiv_states s1 (Some?.v s2'))

/// If evaluation starts from a set of equivalent states, and the
/// exact same thing is evaluated, then the final states are still
/// equivalent.

unfold
let proof_run (s:machine_state) (f:st unit) : machine_state =
  let (), s1 = f s in
  { s1 with ms_ok = s1.ms_ok && s.ms_ok }

let rec lemma_instr_apply_eval_args_equiv_states
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_args_t outs args) (oprs:instr_operands_t_args args)
    (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        (instr_apply_eval_args outs args f oprs s1) ==
        (instr_apply_eval_args outs args f oprs s2))) =
  match args with
  | [] -> ()
  | i :: args ->
    let (v, oprs) : option (instr_val_t i) & _ =
      match i with
      | IOpEx i -> let oprs = coerce oprs in (instr_eval_operand_explicit i (fst oprs) s1, snd oprs)
      | IOpIm i -> (instr_eval_operand_implicit i s1, coerce oprs)
    in
    let f:arrow (instr_val_t i) (instr_args_t outs args) = coerce f in
    match v with
    | None -> ()
    | Some v ->
      lemma_instr_apply_eval_args_equiv_states outs args (f v) oprs s1 s2

let rec lemma_instr_apply_eval_inouts_equiv_states
    (outs inouts:list instr_out) (args:list instr_operand)
    (f:instr_inouts_t outs inouts args) (oprs:instr_operands_t inouts args)
    (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        (instr_apply_eval_inouts outs inouts args f oprs s1) ==
        (instr_apply_eval_inouts outs inouts args f oprs s2))) =
  match inouts with
  | [] ->
    lemma_instr_apply_eval_args_equiv_states outs args f oprs s1 s2
  | (Out, i) :: inouts ->
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
    in
    lemma_instr_apply_eval_inouts_equiv_states outs inouts args (coerce f) oprs s1 s2
  | (InOut, i)::inouts ->
    let (v, oprs) : option (instr_val_t i) & _ =
      match i with
      | IOpEx i -> let oprs = coerce oprs in (instr_eval_operand_explicit i (fst oprs) s1, snd oprs)
      | IOpIm i -> (instr_eval_operand_implicit i s1, coerce oprs)
    in
    let f:arrow (instr_val_t i) (instr_inouts_t outs inouts args) = coerce f in
    match v with
    | None -> ()
    | Some v ->
      lemma_instr_apply_eval_inouts_equiv_states outs inouts args (f v) oprs s1 s2

#push-options "--z3rlimit 10 --max_fuel 1 --max_ifuel 0"

let lemma_instr_write_output_implicit_equiv_states
    (i:instr_operand_implicit) (v:instr_val_t (IOpIm i))
    (s_orig1 s1 s_orig2 s2:machine_state) :
  Lemma
    (requires (
        (equiv_states s_orig1 s_orig2) /\
        (equiv_states s1 s2)))
    (ensures (
        (equiv_states
           (instr_write_output_implicit i v s_orig1 s1)
           (instr_write_output_implicit i v s_orig2 s2)))) =
  let snew1, snew2 =
    (instr_write_output_implicit i v s_orig1 s1),
    (instr_write_output_implicit i v s_orig2 s2) in
  assert (equiv_states_ext snew1 snew2) (* OBSERVE *)

let lemma_instr_write_output_explicit_equiv_states
    (i:instr_operand_explicit) (v:instr_val_t (IOpEx i)) (o:instr_operand_t i)
    (s_orig1 s1 s_orig2 s2:machine_state) :
  Lemma
    (requires (
        (equiv_states s_orig1 s_orig2) /\
        (equiv_states s1 s2)))
    (ensures (
        (equiv_states
           (instr_write_output_explicit i v o s_orig1 s1)
           (instr_write_output_explicit i v o s_orig2 s2)))) =
  let snew1, snew2 =
    (instr_write_output_explicit i v o s_orig1 s1),
    (instr_write_output_explicit i v o s_orig2 s2) in
  assert (equiv_states_ext snew1 snew2) (* OBSERVE *)

#pop-options

let rec lemma_instr_write_outputs_equiv_states
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args)
    (s_orig1 s1:machine_state)
    (s_orig2 s2:machine_state) :
  Lemma
    (requires (
        (equiv_states s_orig1 s_orig2) /\
        (equiv_states s1 s2)))
    (ensures (
        (equiv_states
           (instr_write_outputs outs args vs oprs s_orig1 s1)
           (instr_write_outputs outs args vs oprs s_orig2 s2)))) =
  match outs with
  | [] -> ()
  | (_, i)::outs ->
    (
      let ((v:instr_val_t i), (vs:instr_ret_t outs)) =
        match outs with
        | [] -> (vs, ())
        | _::_ -> let vs = coerce vs in (fst vs, snd vs)
      in
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        lemma_instr_write_output_explicit_equiv_states i v (fst oprs) s_orig1 s1 s_orig2 s2;
        let s1 = instr_write_output_explicit i v (fst oprs) s_orig1 s1 in
        let s2 = instr_write_output_explicit i v (fst oprs) s_orig2 s2 in
        lemma_instr_write_outputs_equiv_states outs args vs (snd oprs) s_orig1 s1 s_orig2 s2
      | IOpIm i ->
        lemma_instr_write_output_implicit_equiv_states i v s_orig1 s1 s_orig2 s2;
        let s1 = instr_write_output_implicit i v s_orig1 s1 in
        let s2 = instr_write_output_implicit i v s_orig2 s2 in
        lemma_instr_write_outputs_equiv_states outs args vs (coerce oprs) s_orig1 s1 s_orig2 s2
    )

let lemma_eval_instr_equiv_states
    (it:instr_t_record) (oprs:instr_operands_t it.outs it.args) (ann:instr_annotation it)
    (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        equiv_ostates
          (eval_instr it oprs ann s1)
          (eval_instr it oprs ann s2))) =
  let InstrTypeRecord #outs #args #havoc_flags i = it in
  let vs1 = instr_apply_eval outs args (instr_eval i) oprs s1 in
  let vs2 = instr_apply_eval outs args (instr_eval i) oprs s2 in
  lemma_instr_apply_eval_inouts_equiv_states outs outs args (instr_eval i) oprs s1 s2;
  assert (vs1 == vs2);
  let s1_new =
    match havoc_flags with
    | HavocFlags -> {s1 with ms_flags = havoc_state_ins s1 (Instr it oprs ann)}
    | PreserveFlags -> s1
  in
  let s2_new =
    match havoc_flags with
    | HavocFlags -> {s2 with ms_flags = havoc_state_ins s2 (Instr it oprs ann)}
    | PreserveFlags -> s2
  in
  assume (overflow s1_new.ms_flags == overflow s2_new.ms_flags); (* TODO FIXME *)
  assume (cf s1_new.ms_flags == cf s2_new.ms_flags); (* TODO FIXME ; [havoc_state_ins] depends upon the entire ms_flags and thus we don't automatically get these working. We have to figure out some workaround for this. *)
  assert (equiv_states s1_new s2_new);
  let os1 = FStar.Option.mapTot (fun vs -> instr_write_outputs outs args vs oprs s1 s1_new) vs1 in
  let os2 = FStar.Option.mapTot (fun vs -> instr_write_outputs outs args vs oprs s2 s2_new) vs2 in
  match vs1 with
  | None -> ()
  | Some vs ->
    lemma_instr_write_outputs_equiv_states outs args vs oprs s1 s1_new s2 s2_new

(* REVIEW: This proof is INSANELY annoying to deal with due to the [Pop].

   TODO: Figure out why it is slowing down so much. It practically
         brings F* to a standstill even when editing, and it acts
         worse during an interactive proof. *)
let lemma_untainted_eval_ins_equiv_states (i : ins) (s1 s2 : machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        equiv_states
          (run (untainted_eval_ins i) s1)
          (run (untainted_eval_ins i) s2))) =
  let s1_orig, s2_orig = s1, s2 in
  let s1_final = run (untainted_eval_ins i) s1 in
  let s2_final = run (untainted_eval_ins i) s2 in
  match i with
  | Instr it oprs ann ->
    lemma_eval_instr_equiv_states it oprs ann s1 s2
  | Push _ _ ->
    assert_spinoff (equiv_states_ext s1_final s2_final)
  | Pop dst t ->
    let stack_op = OStack (MReg rRsp 0, t) in
    let s1 = proof_run s1 (check (valid_src_operand stack_op)) in
    let s2 = proof_run s2 (check (valid_src_operand stack_op)) in
    // assert (equiv_states s1 s2);
    let new_dst1 = eval_operand stack_op s1 in
    let new_dst2 = eval_operand stack_op s2 in
    // assert (new_dst1 == new_dst2);
    let new_rsp1 = (eval_reg rRsp s1 + 8) % pow2_64 in
    let new_rsp2 = (eval_reg rRsp s2 + 8) % pow2_64 in
    // assert (new_rsp1 == new_rsp2);
    let s1 = proof_run s1 (update_operand_preserve_flags dst new_dst1) in
    let s2 = proof_run s2 (update_operand_preserve_flags dst new_dst2) in
    assert (equiv_states_ext s1 s2);
    let s1 = proof_run s1 (free_stack (new_rsp1 - 8) new_rsp1) in
    let s2 = proof_run s2 (free_stack (new_rsp2 - 8) new_rsp2) in
    // assert (equiv_states s1 s2);
    let s1 = proof_run s1 (update_rsp new_rsp1) in
    let s2 = proof_run s2 (update_rsp new_rsp2) in
    assert (equiv_states_ext s1 s2);
    assert_spinoff (equiv_states s1_final s2_final)
  | Alloc _ ->
    assert_spinoff (equiv_states_ext s1_final s2_final)
  | Dealloc _ ->
    assert_spinoff (equiv_states_ext s1_final s2_final)

let rec lemma_taint_match_args_equiv_states
    (args:list instr_operand)
    (oprs:instr_operands_t_args args)
    (memTaint:memTaint_t)
    (stackTaint:memTaint_t)
    (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        (taint_match_args args oprs memTaint stackTaint s1) ==
        (taint_match_args args oprs memTaint stackTaint s2))) =
  match args with
  | [] -> ()
  | i :: args ->
    match i with
    | IOpEx i ->
      let oprs : instr_operand_t i & instr_operands_t_args args = coerce oprs in
      lemma_taint_match_args_equiv_states args (snd oprs) memTaint stackTaint s1 s2
    | IOpIm i ->
      lemma_taint_match_args_equiv_states args (coerce oprs) memTaint stackTaint s1 s2

let rec lemma_taint_match_inouts_equiv_states
    (inouts:list instr_out)
    (args:list instr_operand)
    (oprs:instr_operands_t inouts args)
    (memTaint:memTaint_t)
    (stackTaint:memTaint_t)
    (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        (taint_match_inouts inouts args oprs memTaint stackTaint s1) ==
        (taint_match_inouts inouts args oprs memTaint stackTaint s2))) =
  match inouts with
  | [] -> lemma_taint_match_args_equiv_states args oprs memTaint stackTaint s1 s2
  | (Out, i) :: inouts ->
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
    in
    lemma_taint_match_inouts_equiv_states inouts args oprs memTaint stackTaint s1 s2
  | (InOut, i)::inouts ->
    let (v, oprs) =
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        (taint_match_operand_explicit i (fst oprs) memTaint stackTaint s1, snd oprs)
      | IOpIm i -> (taint_match_operand_implicit i memTaint stackTaint s1, coerce oprs)
    in
    lemma_taint_match_inouts_equiv_states inouts args oprs memTaint stackTaint s1 s2

let lemma_taint_match_ins_equiv_states (i : ins) (s1 s2 : machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        (taint_match_ins i s1.ms_memTaint s1.ms_stackTaint s1) ==
        (taint_match_ins i s2.ms_memTaint s2.ms_stackTaint s2))) =
  match i with
  | Instr (InstrTypeRecord #outs #args _) oprs _ ->
    assert (s1.ms_memTaint == s2.ms_memTaint);
    assert (s1.ms_stackTaint == s2.ms_stackTaint);
    lemma_taint_match_inouts_equiv_states outs args oprs s1.ms_memTaint s1.ms_stackTaint s1 s2
  | Push _ _ | Pop _ _ | Alloc _ | Dealloc _ -> ()

let rec lemma_update_taint_outputs_equiv_states
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args)
    (memTaint:memTaint_t) (stackTaint:memTaint_t)
    (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        (update_taint_outputs outs args oprs memTaint stackTaint s1) ==
        (update_taint_outputs outs args oprs memTaint stackTaint s2))) =
  match outs with
  | [] -> ()
  | (_, i) :: outs ->
    let ((memTaint, stackTaint), oprs) =
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        (update_taint_operand_explicit i (fst oprs) memTaint stackTaint s1, snd oprs)
      | IOpIm i -> (update_taint_operand_implicit i memTaint stackTaint s1, coerce oprs)
    in
    lemma_update_taint_outputs_equiv_states outs args oprs memTaint stackTaint s1 s2

let lemma_update_taint_ins_equiv_states
    (i : ins)
    (memTaint:memTaint_t)
    (stackTaint:memTaint_t)
    (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        (update_taint_ins i memTaint stackTaint s1) ==
        (update_taint_ins i memTaint stackTaint s2))) =
  match i with
  | Instr (InstrTypeRecord #outs #args _) oprs _ ->
    lemma_update_taint_outputs_equiv_states outs args oprs memTaint stackTaint s1 s2
  | Push _ _ | Pop _ _ | Alloc _ | Dealloc _ -> ()

let lemma_eval_ins_equiv_states (i : ins) (s1 s2 : machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        equiv_states
          (machine_eval_ins i s1)
          (machine_eval_ins i s2))) =
  let s10 = run (check (taint_match_ins i s1.ms_memTaint s1.ms_stackTaint)) s1 in
  let s20 = run (check (taint_match_ins i s2.ms_memTaint s2.ms_stackTaint)) s2 in
  lemma_taint_match_ins_equiv_states i s1 s2;
  assert (equiv_states s10 s20);
  let memTaint1, stackTaint1 = update_taint_ins i s1.ms_memTaint s1.ms_stackTaint s10 in
  let memTaint2, stackTaint2 = update_taint_ins i s2.ms_memTaint s2.ms_stackTaint s20 in
  lemma_update_taint_ins_equiv_states i s1.ms_memTaint s2.ms_stackTaint s10 s20;
  assert (memTaint1 == memTaint2);
  assert (stackTaint1 == stackTaint2);
  let s11 = run (untainted_eval_ins i) s10 in
  let s21 = run (untainted_eval_ins i) s20 in
  lemma_untainted_eval_ins_equiv_states i s10 s20;
  let s12 = { s11 with ms_memTaint = memTaint1 ; ms_stackTaint = stackTaint1 } in
  let s22 = { s21 with ms_memTaint = memTaint2 ; ms_stackTaint = stackTaint2 } in
  assert (equiv_states s12 s22)

(** Filter out observation related stuff from the state.

    REVIEW: Figure out _why_ all the taint analysis related stuff is
    part of the core semantics of x64, rather than being separated
    out. *)
let filt_state (s:machine_state) =
  { s with
    ms_trace = [] }

#push-options "--z3rlimit 10 --max_fuel 1 --max_ifuel 1"

let rec lemma_eval_code_equiv_states (c : code) (fuel:nat) (s1 s2 : machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        let s1'', s2'' =
          machine_eval_code c fuel s1,
          machine_eval_code c fuel s2 in
        equiv_ostates s1'' s2''))
    (decreases %[fuel; c; 1]) =
  match c with
  | Ins ins ->
    lemma_eval_ins_equiv_states ins (filt_state s1) (filt_state s2)
  | Block l ->
    lemma_eval_codes_equiv_states l fuel s1 s2
  | IfElse ifCond ifTrue ifFalse ->
    let (st1, b1) = machine_eval_ocmp s1 ifCond in
    let (st2, b2) = machine_eval_ocmp s2 ifCond in
    assert (equiv_states st1 st2);
    assert (b1 == b2);
    let s1' = { st1 with ms_trace = (BranchPredicate b1) :: s1.ms_trace } in
    let s2' = { st2 with ms_trace = (BranchPredicate b2) :: s2.ms_trace } in
    assert (equiv_states s1' s2');
    if b1 then (
      lemma_eval_code_equiv_states ifTrue fuel s1' s2'
    ) else (
      lemma_eval_code_equiv_states ifFalse fuel s1' s2'
    )
  | While _ _ ->
    lemma_eval_while_equiv_states c fuel s1 s2

and lemma_eval_codes_equiv_states (cs : codes) (fuel:nat) (s1 s2 : machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        let s1'', s2'' =
          machine_eval_codes cs fuel s1,
          machine_eval_codes cs fuel s2 in
        equiv_ostates s1'' s2''))
    (decreases %[fuel; cs]) =
  match cs with
  | [] -> ()
  | c :: cs ->
    lemma_eval_code_equiv_states c fuel s1 s2;
    let s1'', s2'' =
      machine_eval_code c fuel s1,
      machine_eval_code c fuel s2 in
    match s1'' with
    | None -> ()
    | _ ->
      let Some s1, Some s2 = s1'', s2'' in
      lemma_eval_codes_equiv_states cs fuel s1 s2

and lemma_eval_while_equiv_states (c : code{While? c}) (fuel:nat) (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        equiv_ostates
          (machine_eval_while c fuel s1)
          (machine_eval_while c fuel s2)))
    (decreases %[fuel; c; 0]) =
  if fuel = 0 then () else (
    let While cond body = c in
    let (s1, b1) = machine_eval_ocmp s1 cond in
    let (s2, b2) = machine_eval_ocmp s2 cond in
    assert (equiv_states s1 s2);
    assert (b1 == b2);
    if not b1 then () else (
      let s1 = { s1 with ms_trace = (BranchPredicate true) :: s1.ms_trace } in
      let s2 = { s2 with ms_trace = (BranchPredicate true) :: s2.ms_trace } in
      assert (equiv_states s1 s2);
      let s_opt1 = machine_eval_code body (fuel - 1) s1 in
      let s_opt2 = machine_eval_code body (fuel - 1) s2 in
      lemma_eval_code_equiv_states body (fuel - 1) s1 s2;
      assert (equiv_ostates s_opt1 s_opt2);
      match s_opt1 with
      | None -> ()
      | Some _ ->
        let Some s1, Some s2 = s_opt1, s_opt2 in
        if s1.ms_ok then (
          lemma_eval_while_equiv_states c (fuel - 1) s1 s2
        ) else ()
    )
  )

#pop-options

/// If an exchange is allowed between two instructions based off of
/// their read/write sets, then both orderings of the two instructions
/// behave exactly the same, as per the previously defined
/// [equiv_states] relation.
///
/// Note that we require (for the overall proof) a notion of the
/// following:
///
///         s1  =====  s2        Key:
///         |          |
///         .          .            + s1, s2, ... : machine_states
///         . f1       . f2         + f1, f2 : some function from a
///         .          .                         machine_state to a
///         |          |                         machine_state
///         V          V            + ===== : equiv_states
///         s1' ===== s2'
///
/// However, proving with the [equiv_states s1 s2] as part of the
/// preconditions requires come complex wrangling and thinking about
/// how different states [s1] and [s2] evolve. In particular, we'd
/// need to show and write something similar _every_ step of the
/// execution of [f1] and [f2]. Instead, we decompose the above
/// diagram into the following:
///
///
///             s1  =====  s2
///            /  \          \
///           .    .          .
///          . f1   . f2       . f2
///         .        .          .
///        /          \          \
///        V          V          V
///        s1' =====  s2''===== s2'
///
///
/// We now have the ability to decompose the left "triangular" portion
/// which is similar to the rectangular diagram above, except the
/// issue of having to manage both [s1] and [s2] is mitigated. Next,
/// if we look at the right "parallelogram" portion of the diagram, we
/// see that this is just the same as saying "running [f2] on
/// [equiv_states] leads to [equiv_states]" which is something that is
/// easier to prove.
///
/// All the parallelogram proofs have already been completed by this
/// point in the file, so only the triangular portions remain (and the
/// one proof that links the two up into a single diagram as above).

unfold
let run2 (f1 f2:st unit) (s:machine_state) : machine_state =
  let open Vale.X64.Machine_Semantics_s in
  run (f1;; f2;; return ()) s

let commutes (s:machine_state) (f1 f2:st unit) : GTot Type0 =
  equiv_states
    (run2 f1 f2 s)
    (run2 f2 f1 s)

let access_location_val_t (a:access_location) : Type0 =
  match a with
  | ALocMem -> heap & memTaint_t
  | ALocStack -> stack & memTaint_t
  | ALocReg _ -> nat64
  | ALocXmm _ -> quad32
  | ALocCf -> bool
  | ALocOf -> bool

let eval_access_location (a:access_location) (s:machine_state) : access_location_val_t a =
  match a with
  | ALocMem -> s.ms_mem, s.ms_memTaint
  | ALocStack -> s.ms_stack, s.ms_stackTaint
  | ALocReg r -> eval_reg r s
  | ALocXmm r -> eval_xmm r s
  | ALocCf -> cf s.ms_flags
  | ALocOf -> overflow s.ms_flags

let unchanged (a:access_location) (f:st unit) (s:machine_state) : GTot Type0 =
  (eval_access_location a s) == (eval_access_location a (run f s))

let rec unchanged_all (as:list access_location) (f:st unit) (s:machine_state) : GTot Type0 =
  match as with
  | [] -> True
  | x :: xs ->
    unchanged x f s /\ unchanged_all xs f s

let rec lemma_eval_instr_unchanged_args
    (outs:list instr_out) (args:list instr_operand)
    (ff:instr_args_t outs args) (oprs:instr_operands_t_args args)
    (f:st unit) (s:machine_state) :
  Lemma
    (requires (
        unchanged_all (aux_read_set0 args oprs) f s))
    (ensures (
        let v0, v1 =
          instr_apply_eval_args outs args ff oprs s,
          instr_apply_eval_args outs args ff oprs (run f s) in
        v0 == v1)) =
  let v0, v1 =
    instr_apply_eval_args outs args ff oprs s,
    instr_apply_eval_args outs args ff oprs (run f s) in
  let reads = aux_read_set0 args oprs in
  match args with
  | [] -> ()
  | i :: args ->
    let (v, v', oprs) : option _ & option _ & _ =
      match i with
      | IOpEx i -> let op, rest = coerce oprs in
        let v, v' =
          instr_eval_operand_explicit i op s,
          instr_eval_operand_explicit i op (run f s)
        in
        admit (); (* XXX: Broke during reordering-common-memory updates *)
        assert (v == v');
        (v, v', rest)
      | IOpIm i ->
        let v, v' =
          instr_eval_operand_implicit i s,
          instr_eval_operand_implicit i (run f s)
        in
        admit (); (* XXX: Broke during reordering-common-memory updates *)
        assert (v == v');
        (v, v', coerce oprs)
    in
    let ff:arrow (instr_val_t i) (instr_args_t outs args) = coerce ff in
    let res = bind_option v (fun v -> instr_apply_eval_args outs args (ff v) oprs s) in
    let res' = bind_option v' (fun v -> instr_apply_eval_args outs args (ff v) oprs (run f s)) in
    match v with
    | None -> ()
    | Some v ->
      let Some v' = v' in
      admit (); (* XXX: Broke during reordering-common-memory updates *)
      let read_op :: _ = reads in
      lemma_eval_instr_unchanged_args outs args (ff v) oprs f s;
      let v0', v1' =
        instr_apply_eval_args outs args (ff v) oprs s,
        instr_apply_eval_args outs args (ff v) oprs (run f s) in
      ()

let rec lemma_eval_instr_unchanged_inouts
    (outs inouts:list instr_out) (args:list instr_operand)
    (ff:instr_inouts_t outs inouts args) (oprs:instr_operands_t inouts args)
    (f:st unit) (s:machine_state) :
  Lemma
    (requires (
        unchanged_all (aux_read_set1 inouts args oprs) f s))
    (ensures (
        let v0, v1 =
          instr_apply_eval_inouts outs inouts args ff oprs s,
          instr_apply_eval_inouts outs inouts args ff oprs (run f s) in
        v0 == v1)) =
  admit (); (* XXX: Broke during reordering-common-memory updates *)
  match inouts with
  | [] ->
    lemma_eval_instr_unchanged_args outs args ff oprs f s
  | (Out, i)::inouts ->
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
    in
    let res = instr_apply_eval_inouts outs inouts args (coerce ff) oprs s in
    admit (); (* XXX: Broke during reordering-common-memory updates *)
    lemma_eval_instr_unchanged_inouts outs inouts args (coerce ff) oprs f s
  | (InOut, i)::inouts ->
    let (v, oprs) : option _ & _ =
      match i with
      | IOpEx i -> let oprs = coerce oprs in (instr_eval_operand_explicit i (fst oprs) s, snd oprs)
      | IOpIm i -> (instr_eval_operand_implicit i s, coerce oprs)
    in
    let ff:arrow (instr_val_t i) (instr_inouts_t outs inouts args) = coerce ff in
    let res = bind_option v (fun v -> instr_apply_eval_inouts outs inouts args (ff v) oprs s) in
    match v with
    | None -> ()
    | Some v ->
      lemma_eval_instr_unchanged_inouts outs inouts args (ff v) oprs f s

let lemma_eval_instr_unchanged
    (it:instr_t_record) (oprs:instr_operands_t it.outs it.args) (ann:instr_annotation it)
    (f:st unit) (s:machine_state) :
  Lemma
    (requires (
        unchanged_all (fst (rw_set_of_ins (Instr it oprs ann))) f s))
    (ensures (
        let InstrTypeRecord #outs #args #havoc_flags i = it in
        let v0, v1 =
          instr_apply_eval outs args (instr_eval i) oprs s,
          instr_apply_eval outs args (instr_eval i) oprs (run f s) in
        v0 == v1)) =
  let InstrTypeRecord #outs #args #havoc_flags i = it in
  lemma_eval_instr_unchanged_inouts outs outs args (instr_eval i) oprs f s

let unchanged_except (exceptions:list access_location) (s1 s2:machine_state) :
  GTot Type0 =
  (forall (a:access_location). {:pattern (eval_access_location a s2)} (
      (!!(disjoint_access_location_from_locations a exceptions) ==>
       (eval_access_location a s1 == eval_access_location a s2))
    )) /\
  (s1.ms_stack.initial_rsp = s2.ms_stack.initial_rsp) /\
  (Set.equal (Map.domain s1.ms_mem) (Map.domain s2.ms_mem)) /\
  (Set.equal (Map.domain s1.ms_stack.stack_mem) (Map.domain s2.ms_stack.stack_mem))

private abstract
let sanity_check_unchanged_except1 s =
  assert (unchanged_except [] s s);
  assert (unchanged_except [ALocCf] s s);
  assert (unchanged_except [ALocCf; ALocOf] s ({s with ms_flags = 0}))

private abstract
[@expect_failure]
let sanity_check_unchanged_except2 s =
  assert (unchanged_except [] s ({s with ms_flags = 0}))

let only_affects (locs:list access_location) (f:st unit) : GTot Type0 =
  forall s. {:pattern unchanged_except locs s (run f s)} (
    unchanged_except locs s (run f s)
  )

let rec unchanged_at (locs:list access_location) (s1 s2:machine_state) : GTot Type0 =
  match locs with
  | [] -> True
  | x :: xs -> (
      (eval_access_location x s1 == eval_access_location x s2) /\
      (unchanged_at xs s1 s2)
    )

let rec unchanged_at_extended (locs:list access_location) (s1 s2:machine_state) : GTot Type0 =
  (forall a. {:pattern (eval_access_location a s1) \/ (eval_access_location a s2)} (
      (not !!(disjoint_access_location_from_locations a locs)) ==> (
        (eval_access_location a s1 == eval_access_location a s2))))

let rec lemma_unchanged_at_extended_implies_unchanged_at locs s1 s2 :
  Lemma
    (requires (unchanged_at_extended locs s1 s2))
    (ensures (unchanged_at locs s1 s2)) =
  match locs with
  | [] -> ()
  | x :: xs ->
    lemma_unchanged_at_extended_implies_unchanged_at xs s1 s2

let bounded_effects (reads writes:list access_location) (f:st unit) : GTot Type0 =
  (only_affects writes f) /\
  (
    forall s1 s2. {:pattern unchanged_at_extended writes (run f s1) (run f s2)} (
      unchanged_at reads s1 s2 ==>
      (unchanged_at_extended writes (run f s1) (run f s2) /\
       (run f s1).ms_ok = (run f s2).ms_ok)
    )
  )

let rec lemma_disjoint_implies_unchanged_at (reads changes:list access_location) (s1 s2:machine_state) :
  Lemma
    (requires (!!(disjoint_access_locations reads changes "") /\
               unchanged_except changes s1 s2))
    (ensures (unchanged_at reads s1 s2)) =
  match reads with
  | [] -> ()
  | x :: xs ->
    lemma_disjoint_implies_unchanged_at xs changes s1 s2

let rec lemma_disjoint_access_location_from_locations_append
  (a:access_location) (as1 as2:list access_location) :
  Lemma (
    (!!(disjoint_access_location_from_locations a as1) /\
     !!(disjoint_access_location_from_locations a as2)) <==>
    (!!(disjoint_access_location_from_locations a (as1 `L.append` as2)))) =
  match as1 with
  | [] -> ()
  | x :: xs ->
    lemma_disjoint_access_location_from_locations_append a xs as2

let lemma_unchanged_except_transitive (a12 a23:list access_location) (s1 s2 s3:machine_state) :
  Lemma
    (requires (unchanged_except a12 s1 s2 /\ unchanged_except a23 s2 s3))
    (ensures (unchanged_except (a12 `L.append` a23) s1 s3)) =
  let aux a : Lemma
    (requires (!!(disjoint_access_location_from_locations a (a12 `L.append` a23))))
    (ensures (eval_access_location a s1 == eval_access_location a s3)) =
    lemma_disjoint_access_location_from_locations_append a a12 a23 in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let lemma_unchanged_except_append_symmetric (a1 a2:list access_location) (s1 s2:machine_state) :
  Lemma
    (requires (unchanged_except (a1 `L.append` a2) s1 s2))
    (ensures (unchanged_except (a2 `L.append` a1) s1 s2)) =
  assert (s1.ms_stack.initial_rsp = s2.ms_stack.initial_rsp);
  let aux a : Lemma
    (requires (
       (!!(disjoint_access_location_from_locations a (a1 `L.append` a2))) \/
       (!!(disjoint_access_location_from_locations a (a2 `L.append` a1)))))
    (ensures (eval_access_location a s1 == eval_access_location a s2)) =
    lemma_disjoint_access_location_from_locations_append a a1 a2;
    lemma_disjoint_access_location_from_locations_append a a2 a1 in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let rec lemma_disjoint_access_location_from_locations_mem
    (a1 a2:list access_location) (a:access_location) :
  Lemma
    (requires (
        (L.mem a a1) /\
        !!(disjoint_access_locations a1 a2 "")))
    (ensures (
        !!(disjoint_access_location_from_locations a a2))) =
  match a1 with
  | [_] -> ()
  | x :: xs ->
    if a = x then () else
    lemma_disjoint_access_location_from_locations_mem xs a2 a

let rec lemma_unchanged_at_mem (as:list access_location) (a:access_location) (s1 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_at_extended as s1 s2) /\
        (L.mem a as)))
    (ensures (
        (eval_access_location a s1 == eval_access_location a s2))) =
  match as with
  | [_] -> ()
  | x :: xs ->
    if a = x then () else
    lemma_unchanged_at_mem xs a s1 s2

let unchanged_upon_both_non_disjoint (a1 a2:list access_location) (s1 s2:machine_state) =
  (forall a. {:pattern (eval_access_location a s1) \/ (eval_access_location a s2)}
     (
       (not (!!(disjoint_access_location_from_locations a a1))) /\
       (not (!!(disjoint_access_location_from_locations a a2)))
     ) ==> (
     eval_access_location a s1 == eval_access_location a s2
   )
  )


let lemma_unchanged_at_combine (a1 a2:list access_location) (sa1 sa2 sb1 sb2:machine_state) :
  Lemma
    (requires (
        !!(disjoint_access_locations a1 a2 "") /\
        (unchanged_upon_both_non_disjoint a1 a2 sa1 sa2) /\
        (unchanged_at_extended a1 sa1 sb2) /\
        (unchanged_except a2 sa1 sb1) /\
        (unchanged_at_extended a2 sa2 sb1) /\
        (unchanged_except a1 sa2 sb2)))
    (ensures (
        (unchanged_at_extended (a1 `L.append` a2) sb1 sb2))) =
  let aux a :
    Lemma
      (requires (not !!(disjoint_access_location_from_locations a (a1 `L.append` a2))))
      (ensures (eval_access_location a sb1 == eval_access_location a sb2)) =
    lemma_disjoint_access_location_from_locations_append a a1 a2
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let lemma_unchanged_except_same_transitive (as:list access_location) (s1 s2 s3:machine_state) :
  Lemma
    (requires (
        (unchanged_except as s1 s2) /\
        (unchanged_except as s2 s3)))
    (ensures (
        (unchanged_except as s1 s3))) = ()

let rec lemma_unchanged_at_extended_and_except (as:list access_location) (s1 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_at_extended as s1 s2) /\
        (unchanged_except as s1 s2)))
    (ensures (
        (unchanged_except [] s1 s2))) = ()

let lemma_equiv_states_when_except_none (s1 s2:machine_state) (ok:bool) :
  Lemma
    (requires (
        (s1.ms_stack.initial_rsp = s2.ms_stack.initial_rsp) /\
        (unchanged_except [] s1 s2)))
    (ensures (
        (equiv_states ({s1 with ms_ok=ok}) ({s2 with ms_ok=ok})))) =
  let open FStar.FunctionalExtensionality in
  FStar.Classical.forall_intro (
    (fun r ->
       assert (eval_access_location (ALocReg r) s1 ==
               eval_access_location (ALocReg r) s2) (* OBSERVE *)
    ) <:
    (r:_) -> Lemma (eval_reg r s1 = eval_reg r s2)
  );
  assert (feq s1.ms_regs s2.ms_regs);
  assert (s1.ms_regs == s2.ms_regs);
  FStar.Classical.forall_intro (
    (fun r ->
       assert (eval_access_location (ALocXmm r) s1 ==
               eval_access_location (ALocXmm r) s2) (* OBSERVE *)
    ) <:
    (r:_) -> Lemma (eval_xmm r s1 = eval_xmm r s2)
  );
  assert (feq s1.ms_xmms s2.ms_xmms);
  assert (s1.ms_xmms == s2.ms_xmms);
  assert (eval_access_location ALocCf s1 == eval_access_location ALocCf s2); (* OBSERVE *)
  assert (eval_access_location ALocOf s1 == eval_access_location ALocOf s2); (* OBSERVE *)
  assert (cf s1.ms_flags = cf s2.ms_flags);
  assert (overflow s1.ms_flags = overflow s2.ms_flags);
  assert (eval_access_location ALocMem s1 == eval_access_location ALocMem s2);
  assert (Map.equal s1.ms_mem s2.ms_mem);
  assert (s1.ms_mem == s2.ms_mem);
  assert (eval_access_location ALocStack s1 == eval_access_location ALocStack s2);
  assert (Map.equal s1.ms_stack.stack_mem s2.ms_stack.stack_mem);
  assert (s1.ms_stack.initial_rsp = s2.ms_stack.initial_rsp);
  assert (s1.ms_stack == s2.ms_stack);
  assert (Map.equal s1.ms_memTaint s2.ms_memTaint);
  assert (s1.ms_memTaint == s2.ms_memTaint);
  assert (Map.equal s1.ms_stackTaint s2.ms_stackTaint);
  assert (s1.ms_stackTaint == s2.ms_stackTaint);
  ()

let rec lemma_disjoint_inversion_flags (a:access_location{ALocCf? a \/ ALocOf? a}) (as:list access_location) :
  Lemma
    (requires (not !!(disjoint_access_location_from_locations a as)))
    (ensures (L.mem a as)) =
  match as with
  | [_] -> ()
  | x :: xs ->
    if a = x then () else (
      lemma_disjoint_inversion_flags a xs
    )

let always_constant (a:access_location) =
  (forall s1 s2. {:pattern (eval_access_location a s1); (eval_access_location a s2)} (
      (eval_access_location a s1 == eval_access_location a s2)))

let lemma_same_not_disjoint (a:access_location) :
  Lemma
    (ensures (
        (not !!(disjoint_access_location a a) \/
        (always_constant a)))) = ()

let rec lemma_mem_not_disjoint (a:access_location) (as1 as2:list access_location) :
  Lemma
    (requires (L.mem a as1 /\ L.mem a as2))
    (ensures (
        (not !!(disjoint_access_locations as1 as2 "")) \/
        (always_constant a))) =
  FStar.Classical.forall_intro (lemma_disjoint_access_locations_reason as1 as2 "");
  lemma_same_not_disjoint a;
  match as1, as2 with
  | [_], [_] -> ()
  | [_], y :: ys ->
    if a = y then () else (
      lemma_mem_not_disjoint a as1 ys
    )
  | x :: xs, y :: ys ->
    if a = x then (
      if a = y then () else (
        lemma_mem_not_disjoint a as1 ys;
        lemma_disjoint_access_locations_symmetric as1 as2 "";
        lemma_disjoint_access_locations_symmetric as1 ys ""
      )
    ) else (
      lemma_mem_not_disjoint a xs as2
    )

(* WARN XXX UNSOUND: This is not true!

   Counterexample to this lemma

     Consider the following:
       a1 = [ALoc64 (OMem (MConst 0))]
       a2 = [ALoc64 (OMem (MConst 8))]
       a = ALoc64 (OMem (MConst 4))

     (Under a stricter notion of disjoint--)

     Now a is not disjoint from a1, nor is it disjoint from
     a2. However, a1 and a2 are disjoint. Thus
     [unchanged_upon_both_non_disjoint] would require that [a] must be
     the same in both worlds, except that it is not, and thus this
     lemma is false.
*)
let lemma_disjoint_conservative
    (a1 a2:list access_location)
    (s s1 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_except a1 s s1) /\
        (unchanged_except a2 s s2) /\
        !!(disjoint_access_locations a1 a2 "")))
    (ensures (
        (unchanged_upon_both_non_disjoint a1 a2 s1 s2))) =
  let aux (a:access_location) :
    Lemma
      (requires (
          (not !!(disjoint_access_location_from_locations a a1)) /\
          (not !!(disjoint_access_location_from_locations a a2))))
      (ensures (
          (eval_access_location a s1 == eval_access_location a s2))) =
    admit ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let lemma_commute (f1 f2:st unit) (r1 w1 r2 w2:list access_location) (s:machine_state) :
  Lemma
    (requires (
        (bounded_effects r1 w1 f1) /\
        (bounded_effects r2 w2 f2) /\
        !!(rw_exchange_allowed (r1, w1) (r2, w2))))
    (ensures (
        equiv_states
          (run2 f1 f2 s)
          (run2 f2 f1 s))) =
  let s12 = run2 f1 f2 s in
  let s21 = run2 f2 f1 s in
  let is1 = run f1 s in
  let is2 = run f2 s in
  let is12 = run f2 is1 in
  let is21 = run f1 is2 in
  FStar.Classical.forall_intro_3 (
    (fun l1 l2 r -> lemma_disjoint_access_locations_reason l1 l2 "" r) <:
    ((l1:_) -> (l2:_) -> (r:_) -> Lemma
       (!!(disjoint_access_locations l1 l2 r) ==
        !!(disjoint_access_locations l1 l2 ""))));
  lemma_disjoint_implies_unchanged_at r1 w2 s is2;
  lemma_disjoint_implies_unchanged_at r2 w1 s is1;
  assert (unchanged_at_extended w1 is1 is21);
  assert (unchanged_at_extended w2 is2 is12);
  assert (unchanged_except w2 s is2);
  assert (unchanged_except w1 s is1);
  assert (unchanged_except w2 is1 is12);
  assert (unchanged_except w1 is2 is21);
  lemma_unchanged_except_transitive w1 w2 s is1 is12;
  assert (unchanged_except (w1 `L.append` w2) s is12);
  lemma_unchanged_except_transitive w2 w1 s is2 is21;
  assert (unchanged_except (w2 `L.append` w1) s is21);
  lemma_unchanged_except_append_symmetric w1 w2 s is12;
  lemma_unchanged_except_append_symmetric w2 w1 s is21;
  lemma_unchanged_except_same_transitive (w1 `L.append` w2) s is12 is21;
  lemma_disjoint_conservative w1 w2 s is1 is2;
  assert (unchanged_upon_both_non_disjoint w1 w2 is1 is2);
  lemma_unchanged_at_combine w1 w2 is1 is2 is12 is21;
  lemma_unchanged_at_extended_and_except (w1 `L.append` w2) is12 is21;
  assert (unchanged_except [] is12 is21);
  assert (s21.ms_ok = s12.ms_ok);
  assert (is12.ms_stack.initial_rsp = is21.ms_stack.initial_rsp);
  lemma_equiv_states_when_except_none is12 is21 s12.ms_ok;
  assert (equiv_states (run2 f1 f2 s) (run2 f2 f1 s))

let lemma_untainted_eval_ins_only_affects_write_aux1 (i:ins{Instr? i}) (s:machine_state) (a:access_location) :
  Lemma
    (requires (
        let r, w = rw_set_of_ins i in
        (!!(disjoint_access_location_from_locations a w))))
    (ensures (
        (eval_access_location a s == eval_access_location a (run (untainted_eval_ins i) s)))) =
  admit ()

let lemma_instr_write_output_explicit_only_affects_write_aux2
    (i:instr_operand_explicit) (v:instr_val_t (IOpEx i)) (o:instr_operand_t i) (s_orig s:machine_state) :
  Lemma
    (requires (
        (s_orig.ms_stack.initial_rsp = s.ms_stack.initial_rsp) /\
        (Set.equal (Map.domain s_orig.ms_mem) (Map.domain s.ms_mem)) /\
        (Set.equal (Map.domain s_orig.ms_stack.stack_mem) (Map.domain s.ms_stack.stack_mem))
      ))
    (ensures (
        (let s1 = instr_write_output_explicit i v o s_orig s in
         (s_orig.ms_stack.initial_rsp = s1.ms_stack.initial_rsp) /\
         (Set.equal (Map.domain s_orig.ms_mem) (Map.domain s1.ms_mem)) /\
         (Set.equal (Map.domain s_orig.ms_stack.stack_mem) (Map.domain s1.ms_stack.stack_mem))))) =
  let s1 = instr_write_output_explicit i v o s_orig s in
  match i with
  | IOp64 -> (
      if valid_dst_operand o s_orig then (
        admit ()
      ) else ()
    )
  | IOpXmm -> (
      admit ()
    )

let lemma_instr_write_output_implicit_only_affects_write_aux2
    (i:instr_operand_implicit) (v:instr_val_t (IOpIm i)) (s_orig s:machine_state) :
  Lemma
    (requires (
        (s_orig.ms_stack.initial_rsp = s.ms_stack.initial_rsp) /\
        (Set.equal (Map.domain s_orig.ms_mem) (Map.domain s.ms_mem)) /\
        (Set.equal (Map.domain s_orig.ms_stack.stack_mem) (Map.domain s.ms_stack.stack_mem))
      ))
    (ensures (
        (let s1 = instr_write_output_implicit i v s_orig s in
         (s_orig.ms_stack.initial_rsp = s1.ms_stack.initial_rsp) /\
         (Set.equal (Map.domain s_orig.ms_mem) (Map.domain s1.ms_mem)) /\
         (Set.equal (Map.domain s_orig.ms_stack.stack_mem) (Map.domain s1.ms_stack.stack_mem))))) =
  admit ()

let rec lemma_instr_write_outputs_only_affects_write_aux2
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (s_orig s:machine_state) :
  Lemma
    (requires (
        (s_orig.ms_stack.initial_rsp = s.ms_stack.initial_rsp) /\
        (Set.equal (Map.domain s_orig.ms_mem) (Map.domain s.ms_mem)) /\
        (Set.equal (Map.domain s_orig.ms_stack.stack_mem) (Map.domain s.ms_stack.stack_mem))
      ))
    (ensures (
        let s1 = instr_write_outputs outs args vs oprs s_orig s in
        (s_orig.ms_stack.initial_rsp = s1.ms_stack.initial_rsp) /\
        (Set.equal (Map.domain s_orig.ms_mem) (Map.domain s1.ms_mem)) /\
        (Set.equal (Map.domain s_orig.ms_stack.stack_mem) (Map.domain s1.ms_stack.stack_mem))
      )) =
  match outs with
  | [] -> ()
  | (_, i)::outs -> (
      let ((v:instr_val_t i), (vs:instr_ret_t outs)) =
        match outs with
        | [] -> (vs, ())
        | _::_ -> let vs = coerce vs in (fst vs, snd vs)
        in
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        lemma_instr_write_output_explicit_only_affects_write_aux2 i v (fst oprs) s_orig s;
        let s = instr_write_output_explicit i v (fst oprs) s_orig s in
        lemma_instr_write_outputs_only_affects_write_aux2 outs args vs (snd oprs) s_orig s
      | IOpIm i ->
        lemma_instr_write_output_implicit_only_affects_write_aux2 i v s_orig s;
        let s = instr_write_output_implicit i v s_orig s in
        lemma_instr_write_outputs_only_affects_write_aux2 outs args vs (coerce oprs) s_orig s
    )

let lemma_eval_instr_only_affects_write_aux2 it oprs ann s0 s1 :
  Lemma
    (requires (
        (Some s1 == eval_instr it oprs ann s0)))
    (ensures (
        (s0.ms_stack.initial_rsp = s1.ms_stack.initial_rsp) /\
        (Set.equal (Map.domain s0.ms_mem) (Map.domain s1.ms_mem)) /\
        (Set.equal (Map.domain s0.ms_stack.stack_mem) (Map.domain s1.ms_stack.stack_mem))
      )) =
  let InstrTypeRecord #outs #args #havoc_flags i = it in
  let Some vs = instr_apply_eval outs args (instr_eval i) oprs s0 in
  let s1' =
    match havoc_flags with
    | HavocFlags -> {s0 with ms_flags = havoc_state_ins s0 (Instr it oprs ann)}
    | PreserveFlags -> s0
  in
  let s1 = instr_write_outputs outs args vs oprs s0 s1' in
  lemma_instr_write_outputs_only_affects_write_aux2 outs args vs oprs s0 s1'

let lemma_untainted_eval_ins_only_affects_write_aux2 (i:ins{Instr? i}) (s:machine_state) :
  Lemma
    (ensures (
        let s' = run (untainted_eval_ins i) s in
        (s.ms_stack.initial_rsp = s'.ms_stack.initial_rsp) /\
        (Set.equal (Map.domain s.ms_mem) (Map.domain s'.ms_mem)) /\
        (Set.equal (Map.domain s.ms_stack.stack_mem) (Map.domain s'.ms_stack.stack_mem))
      )) =
  let Instr it oprs ann = i in
  match eval_instr it oprs ann s with
  | None -> ()
  | Some s' -> lemma_eval_instr_only_affects_write_aux2 it oprs ann s s'

let lemma_untainted_eval_ins_only_affects_write (i:ins{Instr? i}) (s:machine_state) :
  Lemma
    (ensures (
       (let r, w = rw_set_of_ins i in
        (unchanged_except w s (run (untainted_eval_ins i) s))))) =
  FStar.Classical.forall_intro (
    FStar.Classical.move_requires (lemma_untainted_eval_ins_only_affects_write_aux1 i s));
  lemma_untainted_eval_ins_only_affects_write_aux2 i s

let lemma_untainted_eval_ins_unchanged_behavior (i:ins{Instr? i}) (s1 s2:machine_state) :
  Lemma
    (requires (
        let r, w = rw_set_of_ins i in
        (unchanged_at r s1 s2)))
    (ensures (
        let r, w = rw_set_of_ins i in
        let f = untainted_eval_ins i in
        (unchanged_at_extended w (run f s1) (run f s2)) /\
        (run f s1).ms_ok = (run f s2).ms_ok)) =
  admit ()

let lemma_untainted_eval_ins_bounded_effects (i:ins{Instr? i}) :
  Lemma
    (ensures (
        (let r, w = rw_set_of_ins i in
         (bounded_effects r w (untainted_eval_ins i))))) =
  FStar.Classical.forall_intro (lemma_untainted_eval_ins_only_affects_write i);
  FStar.Classical.forall_intro_2 (fun s1 ->
      FStar.Classical.move_requires (lemma_untainted_eval_ins_unchanged_behavior i s1))

let lemma_untainted_eval_ins_exchange (i1 i2 : ins) (s : machine_state) :
  Lemma
    (requires (!!(ins_exchange_allowed i1 i2)))
    (ensures (commutes s
                (untainted_eval_ins i1)
                (untainted_eval_ins i2))) =
  let f = untainted_eval_ins i1 in
  match i2 with
  | Instr it oprs ann ->
    admit ()
  | Push src t ->
    admit ()
  | Pop dst t ->
    admit ()
  | Alloc n ->
    admit ()
  | Dealloc n ->
    admit ()

let lemma_instruction_exchange'_ss (i1 i2 : ins) (s : machine_state) :
  Lemma
    (requires (!!(ins_exchange_allowed i1 i2)))
    (ensures (
        (equiv_states
          (machine_eval_ins i2 (machine_eval_ins i1 s))
          (machine_eval_ins i1 (machine_eval_ins i2 s))))) =
  admit ()

let lemma_instruction_exchange' (i1 i2 : ins) (s1 s2 : machine_state) :
  Lemma
    (requires (
        !!(ins_exchange_allowed i1 i2) /\
        (equiv_states s1 s2)))
    (ensures (
        (let s1', s2' =
           machine_eval_ins i2 (machine_eval_ins i1 s1),
           machine_eval_ins i1 (machine_eval_ins i2 s2) in
         equiv_states s1' s2'))) =
  lemma_instruction_exchange'_ss i1 i2 s1;
  lemma_eval_ins_equiv_states i2 s1 s2;
  lemma_eval_ins_equiv_states i1 (machine_eval_ins i2 s1) (machine_eval_ins i2 s2)

let lemma_instruction_exchange (i1 i2 : ins) (s1 s2 : machine_state) :
  Lemma
    (requires (
        !!(ins_exchange_allowed i1 i2) /\
        (equiv_states s1 s2)))
    (ensures (
        (let s1', s2' =
           machine_eval_ins i2 (filt_state (machine_eval_ins i1 (filt_state s1))),
           machine_eval_ins i1 (filt_state (machine_eval_ins i2 (filt_state s2))) in
         equiv_states s1' s2'))) =
  lemma_eval_ins_equiv_states i1 s1 (filt_state s1);
  lemma_eval_ins_equiv_states i2 s2 (filt_state s2);
  lemma_eval_ins_equiv_states i2 (machine_eval_ins i1 (filt_state s1)) (filt_state (machine_eval_ins i1 (filt_state s1)));
  lemma_eval_ins_equiv_states i1 (machine_eval_ins i2 (filt_state s2)) (filt_state (machine_eval_ins i2 (filt_state s2)));
  lemma_eval_ins_equiv_states i2 (machine_eval_ins i1 s1) (machine_eval_ins i1 (filt_state s1));
  lemma_eval_ins_equiv_states i1 (machine_eval_ins i2 s2) (machine_eval_ins i2 (filt_state s2));
  lemma_instruction_exchange' i1 i2 s1 s2

/// Given that we can perform simple swaps between instructions, we
/// can do swaps between [code]s.

let code_exchange_allowed (c1 c2:code) : pbool =
  match c1, c2 with
  | Ins i1, Ins i2 -> ins_exchange_allowed i1 i2
  | _ -> ffalse "non instruction swaps conservatively disallowed"

let lemma_code_exchange (c1 c2 : code) (fuel:nat) (s1 s2 : machine_state) :
  Lemma
    (requires (
        !!(code_exchange_allowed c1 c2) /\
        (equiv_states s1 s2) /\
        (Some? (machine_eval_codes [c1; c2] fuel s1))))
    (ensures (
        (Some? (machine_eval_codes [c2; c1] fuel s2)) /\
        (let Some s1', Some s2' =
           machine_eval_codes [c1; c2] fuel s1,
           machine_eval_codes [c2; c1] fuel s2 in
         equiv_states s1' s2'))) =
  let Some s1', Some s2' =
    machine_eval_codes [c1; c2] fuel s1,
    machine_eval_codes [c2; c1] fuel s2 in
  match c1, c2 with
  | Ins i1, Ins i2 ->
    let Some s10 = machine_eval_code c1 fuel s1 in
    let Some s11 = machine_eval_code c1 fuel (filt_state s1) in
    // assert_norm (equiv_states s10 s11);
    // assert_norm (equiv_states (machine_eval_ins i1 (filt_state s1)) s11);
    let Some s12 = machine_eval_code c2 fuel (machine_eval_ins i1 (filt_state s1)) in
    // assert_norm (equiv_states s1' s12);
    let Some s13 = machine_eval_code c2 fuel (filt_state (machine_eval_ins i1 (filt_state s1))) in
    // assert_norm (equiv_states s12 s13);
    let s14 = machine_eval_ins i2 (filt_state (machine_eval_ins i1 (filt_state s1))) in
    // assert_norm (equiv_states s13 s14);
    assert_norm (equiv_states s1' s14);
    let Some s20 = machine_eval_code c2 fuel s2 in
    let Some s21 = machine_eval_code c2 fuel (filt_state s2) in
    // assert_norm (equiv_states s20 s21);
    // assert_norm (equiv_states (machine_eval_ins i2 (filt_state s2)) s21);
    let Some s22 = machine_eval_code c1 fuel (machine_eval_ins i2 (filt_state s2)) in
    // assert_norm (equiv_states s2' s22);
    let Some s23 = machine_eval_code c1 fuel (filt_state (machine_eval_ins i2 (filt_state s2))) in
    // assert_norm (equiv_states s22 s23);
    let s24 = machine_eval_ins i1 (filt_state (machine_eval_ins i2 (filt_state s2))) in
    // assert_norm (equiv_states s23 s24);
    assert_norm (equiv_states s2' s24);
    lemma_instruction_exchange i1 i2 s1 s2;
    assert (equiv_states s14 s24);
    sanity_check_equiv_states s1' s14 s24;
    sanity_check_equiv_states s1' s24 s2';
    assert (equiv_states s1' s2')
  | _ -> ()

/// Given that we can perform simple swaps between [code]s, we can
/// define a relation that tells us if some [codes] can be transformed
/// into another using only allowed swaps.

(* WARNING UNSOUND We need to figure out a way to check for equality
   between [code]s.

   THOUGHTS: The only place we _really_ need [eq_code] is within
             [find_code] below. We can probably restructure the code a
             little bit and instead of taking two codes as input, we
             instead take a permutation; not entirely sure what that
             would look like for nested blocks though. Possibly a
             nested set of permutations? On the other hand, in order
             to obtain equality between the different [code]s, we can
             add in a "tag" into the [code] object which is then used
             to expose equality. Not sure what that would look like,
             or what the domino effect for that would be. *)
assume val eq_code (c1 c2 : code) : (b:bool{b <==> c1 == c2})

let rec find_code (c1:code) (cs2:codes) : possibly (i:nat{i < L.length cs2 /\ c1 == L.index cs2 i}) =
  match cs2 with
  | [] -> Err ("Not found: " ^ fst (print_code c1 0 gcc))
  | h2 :: t2 ->
    if eq_code c1 h2 then (
      return 0
    ) else (
      match find_code c1 t2 with
      | Err reason -> Err reason
      | Ok i ->
        return (i+1)
    )

let rec bubble_to_top (cs:codes) (i:nat{i < L.length cs}) : possibly (cs':codes{
    let a, b, c = L.split3 cs i in
    cs' == L.append a c
  }) =
  match cs with
  | [_] -> return []
  | h :: t ->
    let x = L.index cs i in
    if i = 0 then (
      return t
    ) else (
      match bubble_to_top t (i - 1) with
      | Err reason -> Err reason
      | Ok res ->
        match code_exchange_allowed x h with
        | Err reason -> Err reason
        | Ok () ->
          return (h :: res)
    )

let rec reordering_allowed (c1 c2 : codes) : pbool =
  match c1, c2 with
  | [], [] -> ttrue
  | [], _ | _, [] -> ffalse "disagreeing lengths of codes"
  | h1 :: t1, _ ->
    i <-- find_code h1 c2;
    t2 <-- bubble_to_top c2 i;
    (* TODO: Also check _inside_ blocks/ifelse/etc rather than just at the highest level *)
    reordering_allowed t1 t2

/// If there are two sequences of instructions that can be transformed
/// amongst each other, then they behave identically as per the
/// [equiv_states] relation.

#push-options "--initial_fuel 3 --max_fuel 3"
let rec lemma_bubble_to_top (cs : codes) (i:nat{i < L.length cs}) (fuel:nat) (s : machine_state)
    (x : _{x == L.index cs i}) (xs : _{Ok xs == bubble_to_top cs i})
    (s_0 : _{Some s_0 == machine_eval_code x fuel s})
    (s_1 : _{Some s_1 == machine_eval_codes xs fuel s_0}) :
  Lemma
    (ensures (
        let s_final' = machine_eval_codes cs fuel s in
        equiv_ostates' s_1 s_final')) =
  let s_final' = machine_eval_codes cs fuel s in
  match i with
  | 0 -> ()
  | _ ->
    assert !!(code_exchange_allowed x (L.hd cs));
    lemma_code_exchange x (L.hd cs) fuel s s;
    let Ok tlxs = bubble_to_top (L.tl cs) (i - 1) in
    assert (L.tl xs == tlxs);
    assert (L.hd xs == L.hd cs);
    let Some s_start = machine_eval_code (L.hd cs) fuel s in
    let Some s_0' = machine_eval_code x fuel s_start in
    let Some s_0'' = machine_eval_code (L.hd cs) fuel s_0 in
    assert (equiv_states s_0' s_0'');
    lemma_eval_codes_equiv_states tlxs fuel s_0' s_0'';
    let Some s_1' = machine_eval_codes tlxs fuel s_0' in
    lemma_bubble_to_top (L.tl cs) (i - 1) fuel s_start x tlxs s_0' s_1'
#pop-options

let rec lemma_reordering (c1 c2 : codes) (fuel:nat) (s1 s2 : machine_state) :
  Lemma
    (requires (
        !!(reordering_allowed c1 c2) /\
        (equiv_states s1 s2) /\
        (Some? (machine_eval_codes c1 fuel s1))))
    (ensures (
        (Some? (machine_eval_codes c2 fuel s2)) /\
        (let Some s1', Some s2' =
           machine_eval_codes c1 fuel s1,
           machine_eval_codes c2 fuel s2 in
         equiv_states s1' s2'))) =
  match c1 with
  | [] -> ()
  | h1 :: t1 ->
    let Ok i = find_code h1 c2 in
    let Ok t2 = bubble_to_top c2 i in
    lemma_eval_code_equiv_states h1 fuel s1 s2;
    lemma_reordering t1 t2 fuel (Some?.v (machine_eval_code h1 fuel s1)) (Some?.v (machine_eval_code h1 fuel s2));
    let Some s_0 = machine_eval_code h1 fuel s2 in
    let Some s_1 = machine_eval_codes t2 fuel s_0 in
    lemma_bubble_to_top c2 i fuel s2 h1 t2 s_0 s_1