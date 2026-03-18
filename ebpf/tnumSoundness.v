From compcert Require Import Values Integers.
From bpf.ebpf Require Import ebpfBinSem.
From bpf.src Require Import tnum tnum_proof.

Definition tnum_of_operand (v: tnum+int) : tnum :=
  match v with
  | inl t => t
  | inr i => (int64_of_int i, Int64.zero)
  end.

Definition tnum_alu64 (b: aluOp) (dst: tnum) (v2: tnum+int) : tnum :=
  let src := tnum_of_operand v2 in
  match b with
  | LSH   => match v2 with
             | inr i => tnum_lshift dst (int64_of_int i)
             | inl _ => tnum_unknown
             end
  | RSH   => match v2 with
             | inr i => tnum_rshift dst (int64_of_int i)
             | inl _ => tnum_unknown
             end
  | ARSH  => match v2 with
             | inr i => tnum_arshift dst (int64_of_int i)
             | inl _ => tnum_unknown
             end
  | ADD   => tnum_add dst src
  | SUB   => tnum_sub dst src
  | MUL   => tnum_mul dst src 64
  | DIV   => tnum_udiv dst src
  | SDIV  => tnum_sdiv dst src
  | OR    => tnum_or dst src
  | AND   => tnum_and dst src
  | NEG   => tnum_neg dst
  | MOD   => tnum_umod dst src
  (* | SMOD  => tnum_smod dst src *)
  | XOR   => tnum_xor dst src
  | MOV   => src
  | _ => tnum_unknown
  end.

Inductive match_operand : (val + int) -> (tnum + int) -> Prop :=
| match_op_reg : forall (v: val) (t: tnum),
    gamma_val v t ->
    match_operand (inl v) (inl t)
| match_op_imm : forall (i: int),
    match_operand (inr i) (inr i).

Theorem tnum_alu64_sound : 
  forall (op: aluOp) 
         (dst_v: val) (dst_t: tnum) 
         (src_v: val + int) (src_t: tnum + int),
  gamma_val dst_v dst_t ->
  match_operand src_v src_t ->
  gamma_val (eval_alu64 op dst_v src_v) (tnum_alu64 op dst_t src_t).
Proof.
  intros.
  inversion H0.
  - destruct op; simpl.
    + unfold gamma_val.