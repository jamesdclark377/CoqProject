From Coq Require Import Arith ZArith Psatz Bool String List Program.Equality.

Import ListNotations.

Local Open Scope string_scope.

Local Open Scope Z_scope.

Local Open Scope list_scope.

(* Section describing relation operators defining sequences and 
   useful properties about them *)

Set Implicit Arguments.

Section SEQUENCES.

Variable A : Type.       (* Type of states *)
Variable R : A -> A -> Prop.      (* Translation Relation, from state to state *)

(* Zero, one, or several transitions.
   Reflexive, transitive closure of R *)
   
Inductive star : A -> A -> Prop :=
  | star_refl : forall a,
    star a a
  | star_step : forall a b c,
    R a b -> star b c -> star a c.

(* Lemmas *)
Lemma star_one:
  forall (a b : A), R a b -> star a b.
Proof.
  eauto using star.
Qed.

Lemma star_trans:
  forall (a b : A), star a b -> forall c, star b c -> star a c.
Proof.
  induction 1; eauto using star.
Qed.
(* One or several transitions.
  Transitive closure of R *)
  
Inductive plus : A -> A -> Prop :=
  | plus_left : forall a b c,
    R a b -> star b c -> plus a c.

Lemma plus_one:
  forall a b,
  R a b -> plus a b.
Proof.
  eauto using star, plus.
Qed.

Lemma plus_star:
  forall a b,
  plus a b -> star a b.
Proof.
  intros. inversion H. eauto using star.
Qed.

Lemma plus_star_trans:
  forall a b c, plus a b -> star b c -> plus a c.
Proof.
  intros. inversion H. eauto using plus, star_trans.
Qed.

Lemma star_plus_trans:
  forall a b c, star a b -> plus b c -> plus a c.
Proof.
  intros. inversion H0. inversion H; eauto using plus, star, star_trans.
Qed.

Lemma plus_right:
  forall a b c, star a b -> R b c -> plus a c.
Proof.
  eauto using star_plus_trans, plus_one.
Qed.

Definition irred (a: A) : Prop := forall b, ~(R a b).

Definition all_seq_inf (a: A) : Prop :=
  forall b, star a b -> exists c, R b c.
  
Definition infseq_with_function (a: A) : Prop :=
  exists f: Z -> A, f 0 = a /\ forall i, R (f i) (f (1 + i)).
  
CoInductive infseq: A -> Prop :=
  | infseq_step: forall a b,
    R a b -> infseq b -> infseq a.

Remark cycle_infseq:
  forall a, R a a -> infseq a.
Proof.
  intros. cofix COINDHYP. apply infseq_step with a. auto. apply COINDHYP.
Qed.

Lemma infseq_coinduction_principle:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, R a b /\ X b) ->
  forall a, X a -> infseq a.
Proof.
  intros X P. cofix COINDHYP; intros.
  destruct (P a H) as [b [U V]]. apply infseq_step with b; auto.
Qed.

Lemma infseq_coinduction_principle_2:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, plus a b /\ X b) ->
  forall a, X a -> infseq a.
Proof.
  intros.
  apply infseq_coinduction_principle with
    (X := fun a => exists b, star a b /\ X b).
- intros.
  destruct H1 as [b [STAR Xb]]. inversion STAR; subst.
+ destruct (H b Xb) as [c [PLUS Xc]]. inversion PLUS; subst.
  exists b0; split. auto. exists c; auto.
+ exists b0; split. auto. exists b; auto.
- exists a; split. apply star_refl. auto.
Qed.


Lemma infseq_if_all_seq_inf:
  forall a, all_seq_inf a -> infseq a.
Proof.
  apply infseq_coinduction_principle.
  intros. destruct (H a) as [b Rb]. constructor.
  exists b; split; auto.
  unfold all_seq_inf; intros. apply H. apply star_step with b; auto.
Qed.


Lemma infseq_from_function:
  forall a, infseq_with_function a -> infseq a.
Proof.
  apply infseq_coinduction_principle.
  intros. destruct H as [f [P Q]].
  exists (f 1); split.
  subst a. apply Q.
  exists (fun n => f (1 + n)); split. auto. intros. apply Q.
Qed.

Hypothesis R_functional:
  forall a b c, R a b -> R a c -> b = c.
  

Lemma star_star_inv:
  forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
Proof.
  induction 1; intros.
- auto.
- inversion H1; subst.
+ right. eauto using star.
+ assert (b = b0) by (eapply R_functional; eauto). subst b0.
  apply IHstar; auto.
Qed.

Lemma finseq_unique:
  forall a b b',
  star a b -> irred b ->
  star a b' -> irred b' ->
  b = b'.
Proof.
  intros. destruct (star_star_inv H H1).
- inversion H3; subst. auto. elim (H0 _ H4).
- inversion H3; subst. auto. elim (H2 _ H4).
Qed.


Lemma infseq_star_inv:
  forall a b, star a b -> infseq a -> infseq b.
Proof.
  induction 1; intros.
- auto.
- inversion H1; subst.
  assert (b = b0) by (eapply R_functional; eauto). subst b0.
  apply IHstar; auto.
Qed.

Lemma infseq_finseq_excl:
  forall a b,
  star a b -> irred b -> infseq a -> False.
Proof.
  intros.
  assert (infseq b) by (eapply infseq_star_inv; eauto).
  inversion H2. elim (H0 b0); auto.
Qed.

Lemma infseq_all_seq_inf:
  forall a, infseq a -> all_seq_inf a.
Proof.
  intros. unfold all_seq_inf. intros.
  assert (infseq b) by (eapply infseq_star_inv; eauto).
  inversion H1. subst. exists b0; auto.
Qed.

End SEQUENCES.

(* TODO: Proofs *)

   
Definition ident := string.

Definition store : Type := ident -> Z.

Inductive mem_cell2 : Type :=
  | heap_cell (name : ident) (val : Z).

Definition heap := list mem_cell2.

Definition memcell_is_named (cell : mem_cell2) (x : ident) : bool :=
  match cell with
  | (heap_cell n v) => if string_dec x n then true else false
  end.
  
Definition memcell_value (cell : mem_cell2) : Z :=
  match cell with
  | (heap_cell n v) => v
  end.

Fixpoint in_heap (h : heap) (x : ident) : bool :=
  match h with
  | [] => false
  | c :: t => if memcell_is_named c x then true else in_heap t x
  end.

(* Heap Alloc *)

(* Todo: Inits heap cell to '0' value --
    may need to consider semantics *)

(* TODO : Heap alloc/free/update errors result in None option
    consider returning heap unchanged *)
    
(* Definition heap_alloc (x : ident) (h : heap) : option heap :=
  if in_heap h x then None else Some ((heap_cell x 0) :: h). *)

Definition heap_alloc (x : ident) (h : heap) : heap :=
  if in_heap h x then h else (heap_cell x 0) :: h.

Fixpoint heap_free_aux (x : ident) (h : heap) : heap :=
  match h with
  | [] => nil
  | c :: t => if memcell_is_named c x then (heap_free_aux x t) else c :: (heap_free_aux x t)
  end.
  
(* Definition heap_free (x : ident) (h : heap) : option heap :=
  if in_heap h x then Some (heap_free_aux x h) else None. *)
  
Definition heap_free (x : ident) (h : heap) : heap :=
  if in_heap h x then heap_free_aux x h else h. 

Fixpoint heap_update_aux (x : ident) (v : Z) (h : heap) : heap :=
  match h with
  | [] => nil
  | c :: t => if memcell_is_named c x 
                then (heap_cell x v) :: (heap_update_aux x v t)
                else c :: (heap_update_aux x v t)
  end.

(*Definition heap_update (x : ident) (v : Z) (h : heap) : option heap :=
  if in_heap h x then Some (heap_update_aux x v h) else None.*)

Definition heap_update (x : ident) (v : Z) (h : heap) : heap :=
  if in_heap h x then (heap_update_aux x v h) else h.

Definition heap_option_elim (o : option heap) : heap :=
  match o with
  | None => nil
  | Some h => h
  end.
  
  
(*Fixpoint heap_deref_aux (x : ident) (h : heap) : Z :=
  match h with
  | [] => 0 (* should never get here! -- return 0 as default value *)
  | c :: t => if memcell_is_named c x then memcell_value c else heap_deref_aux x t
  end. 
  
Definition heap_dereference (x : ident) (h : heap) : option Z :=
  if in_heap h x then Some (heap_deref_aux x h) else None.

Definition cell_value_option_elim (o : option Z) : Z :=
  match o with
  | None => 0
  | Some n => n
  end. *)
  
Fixpoint heap_dereference (x : ident) (h : heap) : Z :=
  match h with
  | [] => 0
  | c :: t => if memcell_is_named c x then memcell_value c else heap_dereference x t
  end.
  
(* Tests *)
Compute heap_dereference "t" (heap_cell "x" 3 :: heap_cell "y" 6 :: heap_cell "z" 14 :: nil).

Definition update (x : ident) (v : Z) (s : store) : store :=
 fun y => if string_dec x y then v else s y.
 
(*Definition update_heap (x : ident) (v : Z) (h : heap1) : heap1 :=
fun y => if string_dec x y then v else h y.*)

(* Type Definitions *)

(* TODO: Do I need / want a separate expression to refer to a memory reference? 

Inductive mexp : Type :=
  | REF (x : ident).              (* Memory reference expression *)*)
  
Inductive aexp : Type :=
  | CONST (n : Z)                    (* A constant number *)
  | VAR (x : ident)                  (* A variable from the store *)  
(*  | DEREF (m : mexp)                 (* A variable from the heap *) *)
  | DEREF (x : ident)                 (* A variable from the heap *)
  | PLUS (a1 : aexp) (a2 : aexp)      (* A sum of two expressions *)
  | MINUS (a1 : aexp) (a2 : aexp).    (* A difference of two expressions *)
  
Inductive bexp : Type :=
  | TRUE                                    (* Always true *)
  | FALSE                                   (* Always false *)  
  | EQUAL (a1 : aexp) (a2 : aexp)            (* Whether a1 == a2 *) 
  | LESSEQUAL (a1 : aexp) (a2 : aexp)        (* Whether a1 <= a2 *)
  | NOT (b1 : bexp)                          (* Boolean negation *)
  | AND (b1 : bexp) (b2 : bexp).             (* Boolean conjuntion *)
  
(* Useful Derived Forms for Boolean Expressions *)
Definition NOTEQUAL (a1 a2 : aexp) : bexp := NOT (EQUAL a1 a2).
Definition GREATEREQUAL (a1 a2 : aexp) : bexp := LESSEQUAL a2 a1.
Definition GREATER (a1 a2 : aexp) : bexp := NOT (LESSEQUAL a1 a2).
Definition LESS (a1 a2 : aexp) : bexp := GREATER a2 a1.
Definition OR (b1 b2 : bexp) : bexp := NOT (AND (NOT b1) (NOT b2)).
  
Inductive com : Type :=
  | SKIP                                            (* Do nothing *)
  | ASSIGN (x : ident) (a : aexp)                   (* Aexp assignment -- var = a *)
  | ALLOC (x : ident)                               (* Heap allocate a memory cell named 'x' *)
  | FREE (x : ident)                                (* Heap free a memory cell named 'x' *)
  | MEMASSIGN (x : ident) (a : aexp)                (* Mexp assigment -- ref = a *)
  | SEQ (c1 : com) (c2 : com)                        (* sequence c1; c2 *)
  | IFTHENELSE (b : bexp) (c1 : com) (c2 : com)     (* Conditional : if b then c1 else c2 *)
  | WHILE (b : bexp) (c1 : com).                     (* loop while b do c1 done *)
  
Infix ";;" := SEQ (at level 80, right associativity).
  
(* Denotational Semantics *)

Fixpoint aeval (s : store) (h : heap) (a : aexp) : Z :=
  match a with
  | CONST n => n
  | VAR x => s x
  | DEREF x => (heap_dereference x h)
  | PLUS a1 a2 => aeval s h a1 + aeval s h a2
  | MINUS a1 a2 => aeval s h a1 + aeval s h a2
  end.
  
  

Fixpoint beval (s : store) (h : heap) (b : bexp) : bool :=
  match b with
  | TRUE => true
  | FALSE => false
  | EQUAL a1 a2 => aeval s h a1 =? aeval s h a2
  | LESSEQUAL a1 a2 => aeval s h a1 <=? aeval s h a2
  | NOT b1 => negb (beval s h b1)
  | AND b1 b2 => beval s h b1 && beval s h b2
  end.

Inductive cexec : store -> heap -> com -> store -> heap -> Prop := 
  | cexec_skip : forall s h,
      cexec s h SKIP s h
  | cexec_assign : forall s h x a,
      cexec s h (ASSIGN x a) (update x (aeval s h a) s) h
  | cexec_alloc : forall s h x,
      cexec s h (ALLOC x) s (heap_alloc x h)   (* For now -- alloc will init 0 *)
  | cexec_free : forall s h x,
      cexec s h (FREE x) s (heap_free x h)
  | cexec_memassign : forall s h x a,
      cexec s h (MEMASSIGN x a) s (heap_update x (aeval s h a) h)
  | cexec_seq : forall c1 c2 s s' s'' h h' h'',
      cexec s h c1 s' h' -> cexec s' h' c2 s'' h'' ->
      cexec s h (SEQ c1 c2) s'' h''
  | cexec_ifthenelse : forall b c1 c2 s s' h h',
      cexec s h (if beval s h b then c1 else c2) s' h' ->
      cexec s h (IFTHENELSE b c1 c2) s' h'
  | cexec_while_done : forall b c s h,
      beval s h b = false ->
      cexec s h (WHILE b c) s h
  | cexec_while_loop : forall b c s s' s'' h h' h'',
      beval s h b = true -> cexec s h c s' h' -> cexec s' h' (WHILE b c) s'' h'' ->
      cexec s h (WHILE b c) s'' h''.

(* Compilation Relation Section *)

(* Stack machine language definition *)

Inductive instr : Type :=
  | Iconst (n : Z)                    (* Push integer n *)
  | Ivar (x : ident)                  (* Push the current value of variable x *)
  | Isetvar (x : ident)               (* Pop an integer and assign its value to variable x *)
  | Ialloc (x : ident)                (* Allocate a memory cell from the heap, referred to by x *)
  | Ifree (x : ident)                 (* Free memory cell, referred to by x, from the heap *)
  | Ideref (x : ident)                (* Push the current value of memory cell referred to by x *)
  | Isetmem (x : ident)               (* Pop an integer and assign its value to memory cell referred to by x *)
  | Iadd                              (* Pop two integers, push their sum *)
  | Iopp                              (* Pop one integer, push its opposite *)
  | Ibranch (d: Z)                    (* Skip forward of backward d instructions *)
  | Ibeq (d1 : Z) (d0 : Z)             (* Pop two integers, skip d1 instructions if eq, d0 if not eq *)
  | Ible (d1 : Z) (d0 : Z)             (* Pop two integers, skip d1 instructions if leq, d0 if not eq *)
  | Ihalt.                             (* Halt execution *)

Definition code : Type := list instr.
Definition codelen (c : code) : Z := Z.of_nat (List.length c).
Definition stack : Type := list Z.

(* Machine operates on a code C (list of instr) and four variable components 
    -- A program counter (pc) denotinc positition of current instruction in C
    -- An evaluation stack containing integers
    -- A store assigning integer values to variables
    -- A heap of memory cells containing integer values 
*)

Definition config : Type := (Z * stack * store * heap) % type.

(* instruction option to get instruction in code list at PC *)
Fixpoint instr_at (C : code) (pc : Z) : option instr :=
  match C with
  | nil => None
  | i :: C' => if pc =? 0 then Some i else instr_at C' (pc - 1)
  end.
  
(* Small-step semantics of stack machine instructions over a code list *)
Inductive transition (C : code): config -> config -> Prop :=
  | trans_const: forall pc stk s h n,
      instr_at C pc = Some (Iconst n) ->
      transition C (pc, stk, s, h)
                   (pc + 1, n :: stk, s, h)
  | trans_var: forall pc stk s h x,
      instr_at C pc = Some (Ivar x) ->
      transition C (pc, stk, s, h)
                   (pc + 1, s x :: stk, s, h)
  | trans_setvar : forall pc stk s h x n,
      instr_at C pc = Some (Isetvar x) ->
      transition C (pc, n :: stk, s, h)
                   (pc + 1, stk, update x n s, h)
  | trans_alloc : forall pc stk s h x,
      instr_at C pc = Some (Ialloc x) ->
      transition C (pc, stk, s, h)
                   (pc + 1, stk, s, heap_alloc x h)
  | trans_free : forall pc stk s h x,
      instr_at C pc = Some (Ifree x) ->
      transition C (pc, stk, s, h)
                   (pc + 1, stk, s, heap_free x h)
  | trans_deref : forall pc stk s h x,
      instr_at C pc = Some (Ideref x) ->
      transition C (pc, stk, s, h)
                   (pc + 1, heap_dereference x h :: stk, s, h)
  | trans_setmem : forall pc stk s h x n,
      instr_at C pc = Some (Isetmem x) ->
      transition C (pc, n :: stk, s, h)
                   (pc + 1, stk, s, heap_update x n h)
  | trans_add : forall pc stk s h n1 n2,
      instr_at C pc = Some (Iadd) ->
      transition C (pc, n2 :: n1 :: stk, s, h)
                   (pc + 1, (n1 + n2) :: stk, s, h)
  | trans_opp : forall pc stk s h n,
      instr_at C pc = Some (Iopp) ->
      transition C (pc, n :: stk, s, h)
                   (pc + 1, (-n) :: stk, s, h)
  | trans_branch : forall pc stk s h d pc',
      instr_at C pc = Some (Ibranch d) ->
      pc' = pc + 1 + d ->
      transition C  (pc, stk, s, h)
                    (pc', stk, s, h)
  | trans_beq : forall pc stk s h d1 d0 n1 n2 pc',
      instr_at C pc = Some (Ibeq d1 d0) ->
      pc' = pc + 1 + (if n1 =? n2 then d1 else d0) ->
      transition C (pc, n2 :: n1 :: stk, s, h)
                   (pc', stk, s, h)
  | trans_ble : forall pc stk s h d1 d0 n1 n2 pc',
      instr_at C pc = Some (Ible d1 d0) ->
      pc' = pc + 1 + (if n1 <=? n2 then d1 else d0) ->
      transition C (pc, n2 :: n1 :: stk, s, h)
                   (pc', stk, s, h).                  

(* Sequences of transitions define the behavior of the code.
   Proposition to state whether an ending condfiguation is valid, 
     for a given starting configuration, over a code sequence
*)
Definition transitions (C : code) : config -> config -> Prop :=
  star (transition C).
  
Definition machine_terminates (C: code) (s_init: store) (s_final: store) (h_init : heap) (h_final : heap) : Prop :=
  exists pc, transitions C (0, nil, s_init, h_init) (pc, nil, s_final, h_final)
    /\ instr_at C pc = Some Ihalt.
    
Definition machine_diverges (C: code) (s_init: store) (h_init : heap) : Prop :=
  infseq (transition C) (0, nil, s_init, h_init).
  
Definition machine_goes_wrong (C: code) (s_init: store) (h_init: heap) : Prop :=
  exists pc stk s h,
    transitions C (0, nil, s_init, h_init) (pc, stk, s, h)
    /\ irred (transition C) (pc, stk, s, h)
    /\ (instr_at C pc <> Some Ihalt \/ stk <> nil ).  
  
  
(* Add compilation relation, then proofs of correctness *)
Fixpoint compile_aexp (a : aexp) : code :=
  match a with
  | CONST n => Iconst n :: nil
  | VAR x => Ivar x :: nil
  | DEREF x => Ideref x :: nil
  | PLUS a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Iadd :: nil
  | MINUS a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Iopp :: Iadd :: nil
  end.

Fixpoint compile_bexp (b : bexp) (d1 : Z) (d0 : Z) : code :=
  match b with
  | TRUE => if d1 =? 0 then nil else Ibranch d1 :: nil
  | FALSE => if d0 =? 0 then nil else Ibranch d0 :: nil
  | EQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Ibeq d1 d0 :: nil
  | LESSEQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Ible d1 d0 :: nil
  | NOT b1 => compile_bexp b1 d0 d1
  | AND b1 b2 => 
    let code2 := compile_bexp b2 d1 d0 in
    let code1 := compile_bexp b1 0 (codelen code2 + d0) in
    code1 ++ code2
  end.
   
Fixpoint compile_com (c : com) : code := 
  match c with
  | SKIP =>
      nil
  | ASSIGN x a =>
      compile_aexp a ++ Isetvar x :: nil
  | ALLOC x =>
      Ialloc x :: nil
  | FREE x =>
      Ifree x :: nil
  | MEMASSIGN x a =>
      compile_aexp a ++ Isetmem x :: nil
  | SEQ c1 c2 =>
      compile_com c1 ++ compile_com c2
  | IFTHENELSE b ifso ifnot =>
      let code_ifso := compile_com ifso in
      let code_ifnot := compile_com ifnot in 
      compile_bexp b 0 (codelen code_ifso + 1)
      ++ code_ifso
      ++ Ibranch (codelen code_ifnot)
      :: code_ifnot
  | WHILE b body =>
      let code_body := compile_com body in
      let code_test := compile_bexp b 0 (codelen code_body + 1) in
      code_test 
      ++ code_body 
      ++ Ibranch (- (codelen code_test + codelen code_body + 1)) :: nil 
  end.

Definition compile_program (p : com) : code :=
  compile_com p ++ Ihalt :: nil.

Compute compile_program (ALLOC "x").



