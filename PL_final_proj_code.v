(********************************************)
(** Simple Toy Stack Language **)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import String.
Require Import List.
Import ListNotations.

From LF Require Import Maps.
From LF Require Export Imp.

(* Data types are nat and bool *)
Inductive data : Type :=
  | num : nat -> data
  | bl : bool -> data.

Definition state_ := total_map data.     (* define the state and empty state *)
Definition empty_st := (t_empty (bl false)).

(* example for how to use data types *)
Definition eval_data (d : data) : data :=
  match d with
  | num n => num n
  | bl b => bl b
  end.

(* data expressions are the numerical and boolean operations*)
Inductive data_exp : Type :=
  | NNum (d : data)
  | NVar (x : string)
  | NAdd (x y : data)
  | NSub (x y : data)
  | NMul (x y : data)
  | NAnd (x y : data)
  | NNot (d : data).

Definition eval_exp (st : state_) (e : data_exp) : data :=
  match e with
  | NNum (num n) => num n
  | NNum (bl b) => bl b
  | NVar x => st x
  | NAdd (num x) (num y) => num (x + y)
  | NAdd (num x) (bl _) => num x
  | NAdd (bl _) (num y) => num y
  | NAdd (bl _) (bl _) => bl false
  | NSub (num x) (num y) => num (x - y)
  | NSub (num x) (bl _) => num x
  | NSub (bl _) (num y) => num y
  | NSub (bl _) (bl _) => bl false
  | NMul (num x) (num y) => num (x * y)
  | NMul (num x) (bl _) => num x
  | NMul (bl _) (num y) => num y
  | NMul (bl _) (bl _) => bl false
  | NAnd (bl x) (bl y) => bl (andb x y)
  | NAnd (bl x) (num y) => match x with
      | true => num y
      | false => bl false
      end
  | NAnd (num x) (bl y) => match y with
      | true => num x
      | false => bl false
      end
  | NAnd (num _) (num _) => bl false
  | NNot (bl x) => bl (negb x)
  | NNot (num _) => bl false
  end.

(* instructions are what programs are built from *)
Inductive instr : Type :=
  | Push (d : data)
  | Load (x : string)
  | Asgn (x : string)
  | DExp (de : data_exp).

(* evaluate a single instruction on a given stack and state *)
Definition eval_instr (st : state_) (stack : list data) (i : instr) : list data :=
  match i with
  | Push d => d::stack
  | Load x => (st x)::stack
  | Asgn x => stack
  | DExp de => match (de, stack) with
      | (NNum _, dx::stack') => (eval_exp st (NNum dx))::stack
      | (NVar x, stack) => (eval_exp st (NVar x))::stack
      | (NAdd _ _, dx::dy::stack') => (eval_exp st (NAdd dx dy))::stack'
      | (NSub _ _, dx::dy::stack') => (eval_exp st (NSub dx dy))::stack'
      | (NMul _ _, dx::dy::stack') => (eval_exp st (NMul dx dy))::stack'
      | (NAnd _ _, dx::dy::stack') => (eval_exp st (NAnd dx dy))::stack'
      | (NNot _, dx::stack') => (eval_exp st (NNot dx))::stack'
      | (_, []) => stack
      | (_, [_]) => stack
      end
  end.

(* evaluate entire program (list instr) on stack and state *)
Fixpoint execute (st : state_) (stack : list data) (program : list instr) : (state_ * list data) :=
  match program with
  | (Push d)::p' => execute st (d::stack) p'
  | (Load x)::p' => execute st ((st x)::stack) p'
  | (Asgn x)::p' => match stack with
      | d::stack' => let st' := t_update st x d in
          execute st' stack' p'
      | nil => execute st stack p'
      end
  | (DExp de)::p' => match (de, stack) with
      | (NNum _, dx::stack') => execute st ((eval_exp st (NNum dx))::stack) p'
      | (NVar x, stack) => execute st ((eval_exp st (NVar x))::stack) p'
      | (NAdd _ _, dx::dy::stack') => execute st ((eval_exp st (NAdd dx dy))::stack') p'
      | (NSub _ _, dx::dy::stack') => execute st ((eval_exp st (NSub dx dy))::stack') p'
      | (NMul _ _, dx::dy::stack') => execute st ((eval_exp st (NMul dx dy))::stack') p'
      | (NAnd _ _, dx::dy::stack') => execute st ((eval_exp st (NAnd dx dy))::stack') p'
      | (NNot _, dx::stack') => execute st ((eval_exp st (NNot dx))::stack') p'
      | (_, []) => (st, stack)
      | (_, [_]) => (st, stack)
      end
  | _ => (st, stack)
  
  end.

Check execute.

(* Notation so it's easier to write instructions *)
(*Notation "':[' NSub ']:'" := (DExp (NSub (num 0) (num 0))) (at level 50).*)
Notation "'~[' NNot ']~'" := (DExp (NNot (bl false))) (at level 50).
Notation "':[' e ']:'" := (DExp (e (num 0) (num 0))) (at level 50).


(*
  ----- Example execute -----
*)
Example execute1 :
     execute empty_st []
       [Push (num 5); Push (num 1); Push (num 3); :[NSub]: ]
   = (empty_st, [(num 2); (num 5)]).
Proof. simpl. reflexivity. Qed. 

Definition init_state1 : state_ := t_update (t_empty (bl false)) "X" (num 3).

Example execute2 :
     execute init_state1 [(num 3); (num 4)]
       [Push (num 4); Load "X"; :[NMul]:; :[NAdd]:]
   = (init_state1, [(num 15); (num 4)]).
Proof. simpl. reflexivity. Qed.

Definition init_state2 : state_ := t_update (t_empty (bl false)) "X" (bl true).

Example execute3 :
     execute init_state2 [(bl true); (num 4); (bl false)]
       [:[NAnd]:; Load "X"; :[NAnd]:]
   = (init_state2, [(num 4); (bl false)]).
Proof. simpl. reflexivity. Qed.


(* Compiling IMP to low-level *)

Fixpoint compile_aexp (a : aexp) : list instr :=
  match a with
  | ANum n => [Push (num n)]
  | AId x => [Load x]
  | APlus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [:[NAdd]:]
  | AMinus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [:[NSub]:]
  | AMult a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [:[NMul]:]
  end.
Fixpoint compile_bexp (b : bexp) : list instr :=
  match b with
  | BTrue => [Push (bl true)]
  | BFalse => [Push (bl false)]
  | BEq a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [:[NAnd]:]
  | BNeq a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [:[NAnd]:]
  | BLe a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [:[NAnd]:]
  | BGt a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [:[NAnd]:]
  | BNot b1 => compile_bexp b1 ++ [~[NNot]~]
  | BAnd b1 b2 => compile_bexp b1 ++ compile_bexp b2 ++ [:[NAnd]:]
  end.

Check compile_bexp.

Fixpoint compile (c : com) : list instr :=
  match c with
  | CSkip => []
  | CAsgn x y => compile_aexp y ++ [Asgn x]
  | CSeq c1 c2 => compile c1 ++ compile c2
  | CIf b c1 c2 =>
      let com_b := compile_bexp b in
      let com_bn := compile_bexp (BNot b) in
      let com_c1 := compile c1 in
      let com_c2 := compile c2 in
      com_b ++ com_c1 ++ [:[NAnd]:] ++ com_bn ++ com_c2 ++ [:[NAnd]:]
  | CWhile x y =>
      let com_x := compile_bexp x in
      let com_y := compile y in
      com_x ++ com_y
  end.

Check compile.

Theorem compile_aexp_correct : forall (a : aexp) (st_ : state_) (st : state),
  execute st_ [] (compile_aexp a) = (st_, [num (aeval st a)]).
Proof.
  intros. 
Admitted.

Theorem compile_correct : forall (c : com) (st st' : state) (st_ st'_ : state_),
  ceval c st st' -> execute st_ [] (compile c) = (st'_, []).
Proof.
  intros. induction H.
  - unfold compile. admit.
  - admit.
Admitted.

(* Test compilation: *)
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(* 
  Make IMP program and compile it: 
   - Example 1 *)
Definition ex1_program : com :=
  CSeq (CAsgn Z (ANum 2)) (CAsgn X (ANum 6)).

Definition ex1_compiled := compile ex1_program.
Compute ex1_compiled.

Definition final_state_and_stack := execute empty_st [] ex1_compiled.
Definition final_state : state_ := fst final_state_and_stack.
Definition final_stack : list data := snd final_state_and_stack.
Compute final_state Z.
Definition final_state_z_ll := final_state Z.

Definition empty_st2 := (_ !-> 0).
Compute ceval ex1_program empty_st2.


(* Bisimilation Theorem *)
Theorem bisim1 : forall st',
    (ceval (CAsgn Z (ANum 2)) empty_st2 st') ->
    st' Z = 2.
Proof.
  intros. (*apply E_Asgn in H.*)
Admitted.

Theorem bisim2 : forall st st',
    (ceval (CSeq (CAsgn Z (ANum 2)) (CAsgn X (ANum 6))) st st') ->
    num (st' Z) = final_state Z.
Proof.
Admitted.
(*
  apply CAsgn.
  inversion Hceval; subst.
*)

(* Check against execution of Imp directly: *)
Definition ex2_program : com :=
  CIf (BAnd (BTrue) (BTrue)) 
    (CAsgn "Z" (AMult (APlus (AId "X") (AId "Y")) (ANum 2)))
    (CAsgn "Z" (ANum 0)).

Definition ex2_compiled := compile ex1_program.

Compute ex2_compiled.

Definition init_state_ex2 : state := t_update (t_update (t_empty (bl false)) "X" (num 5)) "Y" (num 3).

Compute execute init_state_ex2 [] ex1_compiled.

Example compile2 :
     execute empty_st []
       [Push (num 5); Push (num 1); Push (num 3); :[NSub]: ]
   = [(num 2); (num 5)].
(* FILL IN HERE *)
Proof. simpl. reflexivity. Qed. 






