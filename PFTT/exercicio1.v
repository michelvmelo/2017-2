(** 116297 - Tópicos Avançados em Computadores - Turma B **)
(** Provas Formais: Uma Introdução à Teoria de Tipos     **)
(** Prof. Flávio L. C. de Moura                          **)
(** Email: contato@flaviomoura.mat.br                    **)
(** Homepage: http://flaviomoura.mat.br                  **)

(** Fragmento Implicacional da Lógica Proposicional Intuicionista **)

(** Dicas:

    intro: introdução da implicação
    exact H: a hipótese H corresponde exatamente ao que se quer provar.
    assumption: o que se quer provar é igual a alguma das hipóteses.
    apply H: o tipo alvo de H coincide com o que se quer provar. 
    inversion H: aplica o(s) construtor(es) que permitem gerar a hipótese H. Se nenhum construtor pode ser aplicado, a prova é concluída. Também permite concluir que a partir do absurdo (False) se prova qualquer coisa.

*)

(**
   Nos exercícios abaixos remova o comando 'Admitted' e construa uma prova para as proposições apresentadas.
 *)

Section Exercicios.
Variables A B C D: Prop.

Lemma exercicio1 : A -> B -> A.
Proof.
  intros.
  assumption.
Qed.

Lemma exercicio2 : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  intros.
  apply H.
  - assumption.
  - apply H0.
    assumption.
Qed.

Lemma exercicio3 : (A -> B) -> (C -> A) -> C -> B.
Proof.
  intros.
  apply H.
  apply H0.
  assumption.
Qed.

Lemma exercicio4 : (A -> B -> C) -> B -> A -> C.
Proof.
  intros.
  apply H; assumption.
Qed.  

Lemma exercicio5 : ((((A -> B) -> A) -> A) -> B) -> B. 
Proof.
  intro.
  apply H.
  intro.
  apply H0.
  intro.
  apply H.
  intro.
  assumption.
Qed.

Lemma exercicio6: (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.

Lemma exercicio7: (A -> B -> C) -> (B -> A -> C).
Proof.
  intros.
  apply H; assumption.
Qed.    

Lemma exercicio8: (A -> C) -> A -> B -> C.
Proof.
  intros.
  apply H.
  assumption.
Qed.

Lemma exercicio9: (A -> A -> B) -> A -> B.
Proof.
  intros.
  apply H; assumption.
Qed.  

Lemma exercicio10:  (A -> B) -> (A -> A -> B).
Proof.
  intros.
  apply H.
  assumption.
Qed.

Lemma exercicio11: (A -> B) -> (A -> C) -> (B -> C -> D) -> A -> D.
Proof.
  intros.
  apply H1.
  - apply H.
    assumption.
  - apply H0.
    assumption.
Qed.  

Lemma exercicio12: ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
  intro.
  apply H.
  intro.
  apply H0.
  intro.
  apply H.
  intro.
  assumption.
Qed.

Lemma exercicio13: False -> A.
Proof.
  intro.
  inversion H.
Qed.

Lemma exercicio13': False -> A.
Proof.
  intro.
  (**Search False.**)
  apply False_ind.
  assumption.
Qed.

End Exercicios.
