module Vale.Interop.Assumptions
open Vale.Interop.Base
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module MS = Vale.X64.Machine_s

/// st_put provides a atomic global state update of the Low* state.
///
/// This would be implementable in the Low* memory model, if `f` were
/// a `Tot` function.
///
/// However, the construction of the initial machine_state from an
/// initial Low* state is ghost, the transition semantics uses a ghost
/// function instead. So, we need this axiom.
///
/// This also captures the property that intermediate memory states
/// computed by a vale program are not observable from Low*.
///
/// This functions should not be called from Low* directly. If it is,
/// the resulting program will not be compilable in C.
assume
val st_put
      (#a:Type)
      (p:HS.mem -> Type0)
      (f:(h0:HS.mem{p h0} ->
           GTot (x:(a & HS.mem){ST.equal_domains h0 (snd x)})))
  : ST.Stack a
    (requires p)
    (ensures fun h0 x h1 -> f h0 == (x,h1))

/// The initial registers, xmms, flags
///
/// These are currently constant values, which enables certain kinds
/// of correlations between multiple calls from Low* to Vale that
/// should not be supported.
///
/// For instance, a Vale program could read one of the unassigned
/// registers and store it in the heap. A second call to the same
/// procedure may be proven to not update the heap (because it appears
/// to store the same value there). However, depending on compiler
/// details, that unassigned register may actually have a different
/// value on the second call.
///
/// This attack is not possible currently because Vale postconditions
/// underspecify the values of unassigned registers.
///
/// However, we plan to specifically rule out this kind of attack by
/// parameterizing these value by the initial Low* state on the call
/// to Vale and ensuring that the final Low* state after a call to
/// Vale is never equal to the initial state (e.g., by bumping a
/// counter in the low* state).
assume
val init_regs: (regs:(MS.reg_64 -> MS.nat64){regs MS.rRsp >= 4096})

assume
val init_xmms: MS.reg_xmm -> MS.quad32

assume
val init_flags: MS.flag -> option bool

/// Abstract current operating system from Low*
///  This truly does not change between calls
assume
val win: bool
