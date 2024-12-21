(********************************************)
(** Simple Toy Stack Language **)
Require Import Coq.Strings.String.
(*Require Import Coq.Strings.Ascii.*)
From Coq Require Import Arith.EqNat. Import Nat.
Require Import String.
Require Import List.
Import ListNotations.

From LF Require Import Maps.
From LF Require Export Imp.

(* Data types are nat and bool *)
Inductive data : Type :=
  | num : nat -> data
  | bl : bool -> data.

Definition state := total_map nat.     (* define the state and empty state *)
(*Definition empty_st := (t_empty (bl false)).*)

(* example for how to use data types *)
Definition eval_data (d : data) : data :=
  match d with
  | num n => num n
  | bl b => bl b
  end.

(* instructions are what programs are built from *)
Inductive instr : Type :=
  | Push (d : data)
  | Load (x : string)
  | Asgn (x : string)
  | End
  | NVal
  | NAdd
  | NSub
  | NMul
  | NEq
  | NNeq
  | NLe
  | NGt
  | NAnd
  | NNot.

Definition eval_exp (st : state) (e : instr) (d1 d2 : data) : data :=
  match (e, d1, d2) with
  | (NVal, _, _) => d1
  | (NAdd, (num x), (num y)) => num (x + y)
  | (NAdd, (num x), (bl _)) => num x
  | (NAdd, (bl _), (num y)) => num y
  | (NAdd, (bl _), (bl _)) => bl false
  | (NSub, (num x), (num y)) => num (x - y)
  | (NSub, (num x), (bl _)) => num x
  | (NSub, (bl _), (num y)) => num y
  | (NSub, (bl _), (bl _)) => bl false
  | (NMul, (num x), (num y)) => num (x * y)
  | (NMul, (num x), (bl _)) => num x
  | (NMul, (bl _), (num y)) => num y
  | (NMul, (bl _), (bl _)) => bl false
  | (NEq, (num x), (num y)) => bl (x =? y)
  | (NEq, (bl true), (bl true)) => bl true
  | (NEq, (bl false), (bl false)) => bl true
  | (NEq, _, _) => bl false
  | (NNeq, (num x), (num y)) => bl (negb (x =? y))
  | (NNeq, (bl true), (bl true)) => bl false
  | (NNeq, (bl false), (bl false)) => bl false
  | (NNeq, _, _) => bl true
  | (NLe, (num x), (num y)) => bl (x <=? y)
  | (NLe, _, _) => bl false
  | (NGt, (num x), (num y)) => bl (negb (x <=? y))
  | (NGt, _, _) => bl false
  | (NAnd, (bl x), (bl y)) => bl (andb x y)
  | (NAnd, (bl x), (num y)) => match x with
      | true => num y
      | false => bl false
      end
  | (NAnd, (num x), (bl y)) => match y with
      | true => num x
      | false => bl false
      end
  | (NAnd, (num x), (num _)) => num x (*bl false*)
  | (NNot, (bl x), _) => bl (negb x)
  | (NNot, (num _), _) => bl false
  | _ => bl false
  end.

(* evaluate a single instruction on a given stack and state *)
Definition eval_instr (st : state) (stack : list data) (i : instr) : (state * list data) :=
  match i with
  | Push d => (st, d::stack)
  | Load x => (st, (num (st x))::stack)
  | Asgn x => match stack with    (* PLACE HOLDER *)
      | (num n)::stack' => let st' := t_update st x n in (st', stack')
      | _::stack' => (st, stack')
      | nil => (st, stack)
      end
  | End => match stack with 
      | [] => (st, stack)
      | _ => (st, stack)
      end
  | NVal => match stack with
      | dx::stack' => (st, (eval_exp st NVal dx (bl false))::stack') (*dx::stack*)
      | _ => (st, [])
      end
  | NAdd => match stack with
      | dx::dy::stack' => (st, (eval_exp st NAdd dx dy)::stack')
      | _ => (st, [])
      end
  | NSub => match stack with
      | dx::dy::stack' => (st, (eval_exp st NSub dx dy)::stack')
      | _ => (st, [])
      end
  | NMul => match stack with
      | dx::dy::stack' => (st, (eval_exp st NMul dx dy)::stack')
      | _ => (st, [])
      end
  | NEq => match stack with
      | dx::dy::stack' => (st, (eval_exp st NEq dx dy)::stack')
      | _ => (st, [])
      end
  | NNeq => match stack with
      | dx::dy::stack' => (st, (eval_exp st NNeq dx dy)::stack')
      | _ => (st, [])
      end
  | NLe => match stack with
      | dx::dy::stack' => (st, (eval_exp st NLe dx dy)::stack')
      | _ => (st, [])
      end
  | NGt => match stack with
      | dx::dy::stack' => (st, (eval_exp st NGt dx dy)::stack')
      | _ => (st, [])
      end
  | NAnd => match stack with
      | dx::dy::stack' => (st, (eval_exp st NAnd dx dy)::stack')
      | _ => (st, [])
      end
  | NNot => match stack with
      | dx::stack' => (st, (eval_exp st NNot dx (bl false))::stack')
      | _ => (st, [])
      end
  end.
  
  

(* evaluate entire program (list instr) on stack and state *)
Fixpoint execute (st : state) (stack : list data) (program : list instr) : (state * list data) :=
  match program with
  | (Push d)::p' => let (st', stack') := eval_instr st stack (Push d) in execute st' stack' p'
  | (Load x)::p' => let (st', stack') := eval_instr st stack (Load x) in execute st' stack' p'
  | (Asgn x)::p' => let (st', stack') := eval_instr st stack (Asgn x) in execute st' stack' p'
  | End::_ => eval_instr st stack End
  | NVal::p' => let (st', stack') := eval_instr st stack NVal in execute st' stack' p'
  | NAdd::p' => let (st', stack') := eval_instr st stack NAdd in execute st' stack' p'
  | NSub::p' => let (st', stack') := eval_instr st stack NSub in execute st' stack' p'
  | NMul::p' => let (st', stack') := eval_instr st stack NMul in execute st' stack' p'
  | NEq::p' => let (st', stack') := eval_instr st stack NEq in execute st' stack' p'
  | NNeq::p' => let (st', stack') := eval_instr st stack NNeq in execute st' stack' p'
  | NLe::p' => let (st', stack') := eval_instr st stack NLe in execute st' stack' p'
  | NGt::p' => let (st', stack') := eval_instr st stack NGt in execute st' stack' p'
  | NAnd::p' => let (st', stack') := eval_instr st stack NAnd in execute st' stack' p'
  | NNot::p' => let (st', stack') := eval_instr st stack NNot in execute st' stack' p'
  | _ => (st, stack)
  end.

Check execute.

(*
  ----- Example execute -----
*)
Example execute1 :
     execute empty_st []
       [Push (num 5); Push (num 1); Push (num 3); NSub; End]
   = (empty_st, [(num 2); (num 5)]).
Proof. reflexivity. Qed. 

Definition init_state1 : state := t_update (empty_st) "X" 3.

Example execute2 :
     execute init_state1 [(num 3); (num 4)]
       [Push (num 4); Load "X"; NMul; NAdd; End]
   = (init_state1, [(num 15); (num 4)]).
Proof. simpl. reflexivity. Qed.

Definition init_state2 : state := t_update (empty_st) "X" 1.

Example execute3 :
     execute init_state2 [(bl true); (num 4); (bl false)]
       [NAnd; Load "X"; NAnd; End]
   = (init_state2, [(num 1); (bl false)]).
Proof. simpl. reflexivity. Qed.
(* Compiling IMP to low-level *)

(*--[  Compile arithmetic expressions into list of low-level instructions  ]--*)
Fixpoint compile_aexp (a : aexp) : list instr :=
  match a with
  | ANum n => ([Push (num n)])
  | AId x => [Load x]
  | APlus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [NAdd]
  | AMinus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [NSub]
  | AMult a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [NMul]
  end.

Check compile_aexp.

(*--[  Compile boolean expressions into list of low-level instructions  ]--*)
Fixpoint compile_bexp (b : bexp) : list instr :=
  match b with
  | BTrue => [Push (bl true)]
  | BFalse => [Push (bl false)]
  | BEq a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [NEq]
  | BNeq a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [NNeq]
  | BLe a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [NLe]
  | BGt a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [NGt]
  | BNot b1 => compile_bexp b1 ++ [NNot]
  | BAnd b1 b2 => compile_bexp b1 ++ compile_bexp b2 ++ [NAnd]
  end.

Check compile_bexp.

Fixpoint compile (c : com) : list instr :=
  match c with
  | CAsgn x y => compile_aexp y ++ [Asgn x]
  | CSeq c1 c2 => compile c1 ++ compile c2
  | CIf b c1 c2 =>                    (* <--- PLACE HOLDER *)
      let com_b := compile_bexp b in
      let com_bn := compile_bexp (BNot b) in
      let com_c1 := compile c1 in
      let com_c2 := compile c2 in
      com_b ++ com_c1 ++ [NAnd] ++ com_bn ++ com_c2 ++ [NAnd]
  | CWhile x y =>                     (* <--- PLACE HOLDER *)
      let com_x := compile_bexp x in
      let com_y := compile y in
      com_x ++ com_y
  | _ => []
  end.

(*
******** Proofs for various small things: ********
*)
Lemma execute_empty_stack :
  forall st p,
    execute st [] p = execute st [] p.
Proof.
  simpl.  intros. induction p; reflexivity.
Qed.

Lemma ev_exec_push : forall st stack' i d1 d2,
  execute st stack' ([Push d1]++[Push d2]++[i]) = eval_instr st ([d2]++[d1]++stack') i.
Proof.
  intros. induction i; try reflexivity. simpl. destruct d2; reflexivity.
Qed.
Lemma ev_exec_load : forall st stack' i x1 x2,
  execute st stack' ([Load x1]++[Load x2]++[i]) = eval_instr st ([num (st x2)]++[num (st x1)]++stack') i.
Proof.
  intros. induction i; try reflexivity.
Qed.
Lemma ev_exec_pl : forall st stack' i d1 x2,
  execute st stack' ([Push d1]++[Load x2]++[i]) = eval_instr st ([num (st x2)]++[d1]++stack') i.
Proof.
  intros. induction i; try reflexivity.
Qed.
Lemma ev_exec_lp : forall st stack' i x1 d2,
  execute st stack' ([Load x1]++[Push d2]++[i]) = eval_instr st ([d2]++[num (st x1)]++stack') i.
Proof.
  intros. induction i; try reflexivity. simpl. destruct d2; reflexivity.
Qed.

Lemma execute_empty_program :
  forall st stack p',
    (st, stack) = execute st stack ([End]++p').
Proof.
  simpl. intros. induction stack; reflexivity.
Qed.

Lemma eval_end : forall st stack,
  eval_instr st stack End = (st, stack).
Proof.
  intros. induction stack; try reflexivity.
Qed.

Lemma exec_end_ev : forall st stack p,
  execute st stack ([End]++p) = eval_instr st stack End.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma exec_end : forall st stack p,
  execute st stack ([End]++p) = (st, stack).
Proof. 
  intros. rewrite exec_end_ev. rewrite eval_end. easy.
Qed.

Definition is_end i : bool :=
  match i with
  | End => true
  | _ => false
  end.

Lemma execute_i_p : forall st stack (i : instr) (p : list instr),
  execute st stack ([i] ++ p) = (if (is_end i) then
  eval_instr st stack i
  else
  let (st', stack') := eval_instr st stack i in
  execute st' stack' p).
Proof.
  intros. induction i eqn:Ei; try reflexivity.
Qed.

Lemma p_assoc : forall (i : instr) (p1 p2 : list instr),
  ((i :: p1) ++ p2) = [i]++p1++p2.
Proof.
  intros. rewrite <- app_comm_cons. reflexivity.
Qed.

Lemma stack_i_eq : forall (i : instr) (p : list instr),
  ([i] ++ p) = (i::p).
Proof.
  intros. reflexivity.
Qed.

Lemma execute_app : forall st stack p1 p2,
  execute st stack (p1 ++ p2) = 
  let (st', stack') := execute st stack p1 in
  execute st' stack' p2.
Proof.
  intros st stack p1 p2. generalize dependent stack. induction p1 as [| i p1' IH].
  - reflexivity.
  - rewrite -> p_assoc. intros. rewrite execute_i_p. 
    rewrite <- stack_i_eq. rewrite execute_i_p. 
    destruct i; simpl.
    + . destruct d; simpl.
      -- unfold execute.
     apply IH.  generalize p2. rewrite <- IH. 
  - rewrite -> p_assoc. rewrite -> execute_i_p.
  Admitted.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof. intros n. 
  induction n as [| n' IH].
  * simpl. reflexivity.
  * simpl. rewrite IH. reflexivity.
Qed.
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof. intros n m.
  induction n as [| n' IHn].
  { simpl. 
    rewrite add_0_r.
    reflexivity. }
  { simpl. 
    rewrite IHn.
    trivial. }
Qed.
    
(*
******** Proofs for compiling: ********
*)
(*--[  Prove compile_aexp  ]--*)
Theorem compile_aexp_correct : forall st stack a,
  execute st stack (compile_aexp a) = (st, [num (aeval st a)] ++ stack).
Proof.
  intros. generalize dependent stack. induction a; simpl; try reflexivity.
  - rewrite execute_i_p.
  - destruct a1; destruct a2; simpl; try (unfold eval_exp; rewrite add_comm; reflexivity).
    + sim
    + unfold eval_exp.
   
   - reflexivity.
   - reflexivity. 
   - unfold compile_aexp. rewrite IHa2.
Admitted.


(*--[  Prove compile_bexp  ]--*)
(* - prove correct for just one instruction: *)
Lemma compile_bexp_correct : forall st be,
  execute st [] (compile_bexp be) = (st, [bl (beval st be)]).
Proof.
  intros. induction be; try reflexivity.
  - simpl. destruct a1.
    * Admitted.


(*--[  Prove compile  ]--*)
(* - prove correct for just one instruction: *)
Theorem compile_correct : forall (c : com) (st st' : state) (st_ st'_ : state_),
  ceval c st st' -> execute st_ [] (compile c) = (st'_, []).
Proof.
  intros. induction H.
  - unfold compile. admit.
  - admit.
Admitted.



