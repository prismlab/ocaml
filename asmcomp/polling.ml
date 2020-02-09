(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)
open Mach

(* constants *)
let lmax = 4
let k = 2
let e = lmax/k

let is_addr_live i = 
  not (Reg.Set.is_empty (Reg.Set.filter (fun f -> f.typ = Cmm.Addr) i))

let insert_poll_instr instr = 
    { desc = Iop (Ipoll);
      next = instr;
      arg = instr.arg;
      res = [||];
      dbg = Debuginfo.none;
      live = instr.live;
      available_before = Reg_availability_set.Ok Reg_with_debug_info.Set.empty;
      available_across = None;
    }

let rec insert_poll_aux delta instr =
    if (is_addr_live instr.live) then begin
        { instr with next = (insert_poll_aux delta instr.next) }
    end else begin
        match instr.desc with
        (* terminating condition *)
        | Iend -> instr

        (* reset counter *)
        | Iop (Ialloc _) ->
            { instr with next = (insert_poll_aux delta instr.next) }

        (* | Iop (Imove) *)
        (* | Iop (Ispill) *)
        (* | Iop (Ireload) *)
        (*
        ->
            if (instr.Mach.arg.(0).loc = instr.Mach.res.(0).loc) then begin
                { instr with next = (insert_poll_aux delta instr.next) }
            end else begin
                let updated_instr = { instr with next = insert_poll_aux delta instr.next} in
                insert_poll_instr updated_instr
            end
        *)

        | Iop (Iconst_int _)
        | Iop (Iconst_float _)
        | Iop (Iconst_symbol _)
        | Iop (Icall_ind _)
        (* | Iop (Icall_imm _) *)
        (* | Iop (Itailcall_ind _) *)
        (* | Iop (Itailcall_imm _) *)
        (* | Iop (Iextcall _) *)
        | Iop (Istackoffset _)
        (* | Iop (Iload _) *)
        (* | Iop (Iintop _) (* signal_alloc.ml *) *)
        | Iop (Inegf)
        | Iop (Iabsf)
        | Iop (Iaddf)
        | Iop (Isubf)
        | Iop (Imulf)
        | Iop (Idivf)
        | Iop (Ifloatofint)
        | Iop (Iintoffloat)
        | Iop (Iname_for_debugger _)
        ->
            let updated_instr = { instr with next = insert_poll_aux delta instr.next} in
            insert_poll_instr updated_instr
        
        (* other *)
        (* | Iop (Iintop_imm (_, _, is_addr_upd)) -> (* signals_alloc failing *)
            if (is_addr_upd) then begin
                { instr with next = (insert_poll_aux delta instr.next) }
            end else begin
                let updated_instr = { instr with next = insert_poll_aux delta instr.next} in
                insert_poll_instr updated_instr
            end *)
        | Iop (Istore (_, _, is_assign)) ->
            if (is_assign) then begin
                let updated_instr = { instr with next = insert_poll_aux delta instr.next} in
                insert_poll_instr updated_instr
            end else begin
                { instr with next = (insert_poll_aux delta instr.next) }
            end
        | Iop (Ispecific (Istore_int _)) ->
            { instr with next = (insert_poll_aux delta instr.next) }
        (* signal_alloc failing
        | Iop (Ispecific _) ->
            let updated_instr = { instr with next = insert_poll_aux delta instr.next} in
            insert_poll_instr updated_instr
        *)
        | Iop (Ipoll) ->
            assert false
        (* pass through - temp until all instructions handled *)
        | _ -> { instr with next = (insert_poll_aux delta instr.next) }
    end

let insert_poll fun_body =
    insert_poll_aux (lmax-e) fun_body

let fundecl f =
    let new_body =
      if !Clflags.no_poll then
        f.fun_body
      else
        insert_poll f.fun_body
    in
      { f with fun_body = new_body }
