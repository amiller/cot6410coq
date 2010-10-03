Require Export Basics.
Require Export Lists.
Require Export Poly.

Definition store : Type:=
  nat -> nat.


Definition config : Type :=
 prod nat store.


Inductive instruction:Type :=
  | ZR : nat -> instruction
  | SC : nat -> instruction
  | TF : nat -> nat -> instruction
  | JP : nat -> nat -> nat -> instruction.

Definition program : Type :=
  list instruction.


Fixpoint update_store (n:nat) (v:nat) (s:store) (x:nat) : nat :=
  if beq_nat n x then 0 else s x.


Fixpoint jump_eq (pc pc':nat) (x y:nat) : nat :=
  if beq_nat x y then pc' else S pc.


Definition exec_instruction 
   (ins:instruction) (cfg:config) : config :=
  match cfg with
  | (pc,s) =>
    match ins with
    | ZR n =>   ((S pc), (update_store n 0 s)) 
    | SC n =>   ((S pc), (update_store n (S (s n)) s)) 
    | TF n m => ((S pc), (update_store m (s n) s)) 
    | JP n m x => ((jump_eq pc x (s n) (s x)), s) 
    end
end.


Definition Final (p:program) (c:config) : bool :=
  match c with 
  | (pc, _) => beq_nat pc (length p)
    
end.

Fixpoint nth_d (l:list nat) (d n:nat) : nat :=
  match l,n with
  | nil, _ => d
  | a :: _, 0 => a
  | _ :: l', S n' => nth_d l' d n'
end.

Fixpoint nth_inst (p:program) (n:nat) : instruction :=
  match p, n with
  | a :: _, 0 => a
  | _ :: l', S n' => nth_inst p n'
  | _,_ => ZR 0
end.

Definition EXEC_STEP (P:program) (c:config) : config :=
  match c with 
  | (pc, _) =>
     if Final P c then c 
     else exec_instruction (nth_inst P pc) c
end.

Fixpoint EXEC_STEPS (n:nat) (P:program) (c:config) : config :=
  match n with
  | 0 => c
  | S n' => (EXEC_STEP P (EXEC_STEPS n' P c))
end.

Definition set_init_conf (c:list nat) : config :=
  (0, fun (x:nat) => nth_d c 0 x).


Definition HALTS (P:program) (l:list nat) : Prop :=
  exists n:nat, true = (Final P (EXEC_STEPS n P (set_init_conf l))).

Definition DIVERGES (P:program) (l:list nat) : Prop :=
  ~ HALTS P l.

Check ([ZR 0]).

Example conv1 : HALTS [ZR 0] [].
Proof.
 exists 1. trivial.

Example conv2 : DIVERGES [JP 0 0 0] [].
Proof.
 unfold DIVERGES. 
 admit.
