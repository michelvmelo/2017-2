(** 116297 - Tópicos Avançados em Computadores - Turma B **)
(** Provas Formais: Uma Introdução à Teoria de Tipos     **)
(** Prof. Flávio L. C. de Moura                          **)
(** Email: contato@flaviomoura.mat.br                    **)
(** Homepage: http://flaviomoura.mat.br                  **)

(** Dicas:

    intro: introdução da implicação
    exact H: a hipótese H corresponde exatamente ao que se quer provar.
    assumption: o que se quer provar é igual a alguma das hipóteses.
    apply H: o tipo alvo de H coincide com o que se quer provar. 
    inversion H: aplica o(s) construtor(es) que permitem gerar a hipótese H. Se nenhum construtor pode ser aplicado, a prova é concluída. Também permite concluir que a partir do absurdo (False) se prova qualquer coisa.
    left: seleciona o lado esquerdo de uma disjunção.
    right: seleciona o lado direito de uma disjunção.
    unfold H: substitui H por sua definição.
    assert (F): adiciona a fórmula F no contexto uma vez que a mesma seja provada. Consiste em adicionar F como um lema para a prova atual.
    destruct H: faz análise de casos em H
    inversion H: gera as condições necessárias para a construção de H
*)

(**
   Nos exercícios abaixos remova o comando 'Admitted' e construa uma prova para as proposições apresentadas.
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
  apply H0.
  intro.
  
    
    
    
    
  
  
  
  
Admitted.

Lemma exercicio15: (A -> ~A) -> A -> B.
Proof.
Admitted.

End Exercicios.