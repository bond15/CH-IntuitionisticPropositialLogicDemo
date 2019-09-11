Require Import Maps.

(* intuitionistic propositional logic with conjunction, disjunction, implication *)

Inductive type : Type :=
| TUnit : type
| TArrow : type -> type -> type
| TProd : type -> type -> type
| TSum : type -> type -> type.


Inductive term : Type :=
(* Untyped lambda terms *)
| tapp : term -> term -> term
| tabs : string -> type -> term -> term
| tvar : string -> term
(* Truth *)
| tunit : term
(* product *)
| tpair : term -> term -> term
| tfst : term -> term
| tsnd : term -> term.
(* sum *)


Definition context := partial_map type.

Reserved Notation " Gamma '|-' t ';' T " (at level 20).

Inductive has_type : context ->  term -> type -> Prop :=
  (* lambda typing *)
| T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x ; T
  | T_Abs : forall Gamma x T11 T12 t12,
      Gamma & {{x --> T11}} |- t12 ; T12 ->
      Gamma |- tabs x T11 t12 ; TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 ; TArrow T11 T12 ->
      Gamma |- t2 ; T11 ->
      Gamma |- tapp t1 t2 ; T12
  (* unit typing *)
  | T_Unit : forall Gamma,
      Gamma |- tunit ; TUnit
(* Product typing *)
  | T_Pair : forall Gamma t1 t2 A B,
      Gamma |- t1 ; A ->
      Gamma |- t2 ; B ->
      Gamma |- (tpair t1 t2) ; (TProd A B)                            
        
where " Gamma '|-' t ';' T" := (has_type Gamma t T).



Fixpoint beq_ty (T1 T2 : type) : bool :=
  match T1,T2 with
  | TUnit, TUnit => true
                      
  | TArrow A1 B1, TArrow A2 B2 =>
    andb (beq_ty A1 A2) (beq_ty B1 B2)
         
  | TProd A1 B1, TProd A2 B2 =>
    andb (beq_ty A1 A2) (beq_ty B1 B2)

  | _,_ => false
 end.

Fixpoint type_check (Gamma : context) (t : term ) : option type :=
  match t with
  (* lambda terms *)
  | tvar x => Gamma x
  | tabs x A t =>
    match type_check (update Gamma x A) t with
    | Some B => Some (TArrow A B)
    | _ => None
    end
  | tapp t1 t2 =>
    match type_check Gamma t1 , type_check Gamma t2 with
    | Some (TArrow A B) , Some C =>
      if beq_ty A C then Some B else None
    | _,_ => None
    end
   (* unit *)
   | tunit => Some TUnit
   (* product terms *)
   | tpair t1 t2 =>
     match type_check Gamma t1, type_check Gamma t2 with
     | Some A, Some B => Some (TProd A B)
     | _,_ => None
     end

   | tfst t =>
     match type_check Gamma t with
     | Some (TProd A B) => Some A
     | _ => None
     end
       
   | tsnd t =>
     match type_check Gamma t with
     | Some (TProd A B) => Some B
     | _ => None
     end
   end.

Definition isProof (Gamma : context) (t : term ) (T : type ) :=
  match type_check Gamma  t with
  | Some T1 => beq_ty T1 T
  | _ => false
  end.

Theorem curry : forall (P Q R : Prop),  P /\ Q -> ( P -> (Q -> R)) -> ((P/\ Q) -> R).
Proof.
  
  







(* soundness and completeness of the logic *)

Theorem type_checking_sound : forall Gamma t T,
    type_check Gamma t = Some T -> has_type Gamma t T.
Proof.
Admitted.

Theorem type_checking_complete : forall Gamma t T,
    has_type Gamma t T -> type_check Gamma t = Some T.
Proof.
Admitted.

(* Using the Logic *)

Open Scope string_scope.
Definition x := "x".
Definition y := "y".
Definition z := "z".
Definition f := "f".
Definition p := "p".


Set Warnings "-notation-overridden,-parsing".

Notation " '\' x ';' T '_' t " := (tabs x T t)(at level 40).
Notation " t1 ,, t2 " := (pair t1 t2) (at level 40).
Notation " p '.fst' " := (tfst p) (at level 40).
Notation " p '.snd' " := (tsnd p) (at level 40).

Notation " A 'x' B " := (TProd A B) (at level 40).
Notation " A ---> B " := (TArrow A B) (at level 40).


(* Gamma, f : A -> B -> C  |- (A * B) -> C *)

(* \ z : A.  \y : B. f (z ,y) *)

(* \p : A * B. \f : A -> B -> C. F ( pi p) F (p2 p). *)f



  (* NOTE: This proof is not polymorphic.
This proof is explicitly for the TUnit type *)

(* should be able to prove uncurry *)
Definition G:= (@empty type) & {{ f --> TUnit ---> (TUnit ---> TUnit) }}.
Definition uncurryProof := (tabs p (TUnit x TUnit)
                                 (tapp (tapp  (tvar f) (tfst (tvar p))) (tsnd (tvar p)))).
Definition uncurryProp := ( TUnit x TUnit ---> TUnit).

Theorem uncurry : isProof G uncurryProof uncurryProp = true.
Proof.  reflexivity. Qed.

(* proof of curry *)
Definition G':= (@empty type) & {{ f --> TUnit x TUnit ---> TUnit }}.
Definition curryProof := (tabs z (TUnit) (tabs y (TUnit) (tapp (tvar f) (tpair (tvar z) (tvar y))))).
Definition curryProp := (TUnit ---> (TUnit ---> TUnit)).

Theorem curry : isProof G' curryProof curryProp = true.
Proof. reflexivity. Qed.

(* in coq *)

Theorem Coquncurry : forall (P Q R : Prop) ,
    (P -> (Q -> R) ) -> (P /\ Q -> R).
Proof.
  intros P Q R.
  intros f.
  intros p.
  destruct p.
  apply f in H. assumption. assumption.Qed.

Print Coquncurry.
Theorem Coqcurry : forall (P Q R : Prop),
    (P /\ Q -> R) -> (P -> (Q -> R)).
Proof.
  