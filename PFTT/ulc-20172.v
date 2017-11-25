(** 116297 - Tópicos Avançados em Computadores - 2017/2           **)
(** Provas Formais: Uma Introdução à Teoria de Tipos - Turma B    **)
(** Prof. Flávio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(** Aluno:                                                        **)
(** Matrícula:                                                    **)
(*                                                                 *)
(*             Partial Formalization of the confluence             *)
(*                 of the untyped lambda calculus  	           *)		
(*								   *)
(* Flávio L. C. de Moura (http://flaviomoura.mat.br), 2017         *)
(*******************************************************************)

Require Import MSetList.

Fixpoint beq (n m:nat): bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | _ => false
         end
  | S k => match m with
           | 0 => false
           | S p => beq k p
           end
  end.

Definition var := nat.

Declare Module Var_as_OT : UsualOrderedType
  with Definition t := var.
Module Import VarSet := MSetList.Make Var_as_OT.

Definition varset := VarSet.t.

Notation "{}" := (VarSet.empty).
Notation "{{ x }}" := (VarSet.singleton x).
Notation "s [=] t " := (VarSet.Equal s t) (at level 70, no associativity). 
Notation "E \u F" := (VarSet.union E F)  (at level 68, left associativity).
Notation "x \in E" := (VarSet.In x E) (at level 69).
Notation "x \notin E" := (~ VarSet.In x E) (at level 69).
Notation "E << F" := (VarSet.Subset E F) (at level 70, no associativity).
Notation "E \rem F" := (VarSet.remove F E) (at level 70).

(** Untyped terms. *)
Inductive tm : Set :=
| bvar: nat -> tm (* bound variables *)
| fvar: var -> tm (* free variables *)
| app: tm -> tm -> tm 
| abs: tm -> tm.

(** Set if free variables. *)
Fixpoint fv (t : tm) : varset :=
  match t with
  | bvar i    => {}
  | fvar x    => {{x}}
  | app t1 t2 => (fv t1) \u (fv t2)
  | abs t1    => (fv t1)
  end.

(** Metasubstituion. *)
Fixpoint msub_aux (n:nat) (t u: tm) : tm :=
  match t with
  | bvar k => if (beq k n) then u else t
  | fvar x => t
  | app t1 t2 => app (msub_aux n t1 u) (msub_aux n t2 u)
  | abs t1 => abs (msub_aux (S n) t1 u)
  end.

Definition msub (t u: tm) : tm := msub_aux 0 t u.
Notation "t [ u ]" := (msub t u) (at level 70).

Inductive beta : tm -> tm -> Prop :=
   rule: forall (t u: tm), beta (app(abs t) u) (t[u]).

Inductive contextual_closure (Red : tm -> tm -> Prop) : tm -> tm -> Prop :=
| redex : forall t s, Red t s -> contextual_closure Red t s
| app_left : forall t t' u, contextual_closure Red t t' -> 
	  		    contextual_closure Red (app t u) (app t' u)
| app_right : forall t u u', contextual_closure Red u u' -> 
	  		     contextual_closure Red (app t u) (app t u')
| abs_in : forall t t', contextual_closure Red t t' ->
                            contextual_closure Red (abs t) (abs t').

Definition one_step_beta := contextual_closure beta.
Notation "t ->_B u" := (one_step_beta t u) (at level 66).

Inductive transitive_closure_beta : tm -> tm -> Prop :=
  | one_step_reduction : forall t u, t ->_B u -> transitive_closure_beta t u
  | transitive_reduction : forall t u v, t ->_B u -> transitive_closure_beta u v -> transitive_closure_beta t v.
Notation "t ->+B u" := (transitive_closure_beta t u) (at level 66).

Inductive star_closure_beta : tm -> tm -> Prop :=
  | reflexive_reduction : forall t, star_closure_beta t t
  | star_trans_reduction : forall t u, t ->+B u -> star_closure_beta t u.
Notation "t ->*B u" := (star_closure_beta t u) (at level 66).

Lemma one_star_transitive_closure_composition:
    forall t u v, t ->_B u -> u ->*B v -> t ->*B v.
Proof.
Admitted.    

Lemma star_transitive_closure_composition:
    forall t u v, t ->+B u -> u ->*B v -> t ->*B v.
Proof.
Admitted.      

Lemma star_closure_composition:
    forall t u v, t ->*B u -> u ->*B v -> t ->*B v.
Proof.
Admitted.  
  
Axiom strip_lemma: forall (t t1 t2:tm), (t ->_B t1) /\ (t ->*B t2) -> (exists t3: tm, (t1 ->*B t3) /\ (t2 ->*B t3)). 
  
Theorem confluence: forall (t t1 t2:tm), (t ->*B t1) -> (t ->*B t2) -> (exists t3: tm, (t1 ->*B t3) /\ (t2 ->*B t3)). 
Proof.
Admitted.