(** 116297 - T\u00f3picos Avan\u00e7ados em Computadores - Turma B **)
(** Provas Formais: Uma Introdu\u00e7\u00e3o \u00e0 Teoria de Tipos     **)
(** Prof. Fl\u00e1vio L. C. de Moura                          **)
(** Email: contato@flaviomoura.mat.br                    **)
(** Homepage: http://flaviomoura.mat.br                  **)

(** Dicas:

    intro: introdu\u00e7\u00e3o da implica\u00e7\u00e3o
    exact H: a hip\u00f3tese H corresponde exatamente ao que se quer provar.
    assumption: o que se quer provar \u00e9 igual a alguma das hip\u00f3teses.
    apply H: o tipo alvo de H coincide com o que se quer provar. 
    inversion H: aplica o(s) construtor(es) que permitem gerar a hip\u00f3tese H. Se nenhum construtor pode ser aplicado, a prova \u00e9 conclu\u00edda. Tamb\u00e9m permite concluir que a partir do absurdo (False) se prova qualquer coisa.
    left: seleciona o lado esquerdo de uma disjun\u00e7\u00e3o.
    right: seleciona o lado direito de uma disjun\u00e7\u00e3o.
    unfold H: substitui H por sua defini\u00e7\u00e3o.
    assert (F): adiciona a f\u00f3rmula F no contexto uma vez que a mesma seja provada. Consiste em adicionar F como um lema para a prova atual.
    destruct H: faz an\u00e1lise de casos em H
    inversion H: gera as condi\u00e7\u00f5es necess\u00e1rias para a constru\u00e7\u00e3o de H
*)

(**
   Nos exerc\u00edcios abaixos remova o comando 'Admitted' e construa uma prova para as proposi\u00e7\u00f5es apresentadas.
 *)

Section Exercicios.
Variables A B C D: Prop.

Lemma exercicio1 : ~ False.
Proof.
  intro.
  assumption.
Qed.

Lemma exercicio2 : (A -> B) -> ~ B -> ~ A. 
Proof.
  intros.
  intro.
  destruct H0.
  apply H.
  assumption.
Qed.

Lemma exercicio3: A -> ~~A.
Proof.
  intro.
  intro.
  contradiction.
Qed.

Lemma exercicio4: ~~~A -> ~A.
Proof.
  intro.
  intro.
  destruct H.
  intro.
  contradiction.
Qed.

Lemma exercicio5: A -> ~A -> B.
Proof.
  intros.
  contradiction.
Qed.  

Lemma exercicio6 : A -> B -> A /\ B. 
Proof.
  intros.
  split; assumption.
Qed.

Lemma exercicio7 : A /\ B -> B.
Proof.
  intro.
  destruct H.
  assumption.
Qed.  

Lemma exercicio8 : A -> A \/ B.
Proof.
  intro.
  left.
  assumption.
Qed.

Lemma exercicio9 : A \/ B -> (A -> C) -> (B -> C) -> C.
Proof.
  intros.
  destruct H.
  - apply H0.
    assumption.
  - apply H1.
    assumption.
Qed.

Lemma exercicio10: ((A /\ B) -> C) <-> (A -> B -> C).
Proof.
  split.
  - intros.
    apply H.
    split; assumption.
  - intros.
    destruct H0.
    apply H; assumption.
Qed.

Lemma exercicio11: ~~A -> (A \/ ~A) -> A.
Proof.
  intros.
  destruct H0.
  - assumption.
  - contradiction.
Qed.

Lemma exercicio12: ~~(A \/ ~A).
Proof.
  intro.
  case H.
  right.
  intro.
  destruct H.
  left.
  assumption.
Qed.

Definition LEM := A \/ ~A.
Definition Peirce := ((A -> B) -> A) -> A.
Definition NNeg := ~~A -> A.

Lemma exercicio13: LEM -> NNeg.
Proof.
  intro.
  intro.
  destruct H.
  - assumption.
  - contradiction.
Qed.

Lemma exercicio14: NNeg -> Peirce.
Proof.
  intro.
  intro.
  apply H.
  intro.
  case H1.
  apply H0.
  intro.
  contradiction.
Qed.

Lemma exercicio15: (A -> ~A) -> A -> B.
Proof.
  intros.
  destruct H; assumption.
Qed.

End Exercicios.