(* begin hide *)
From Stdlib Require Import String Arith Lia List.
Import ListNotations.

Notation  "a >=? b" := (Nat.leb b a) (at level 70) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a) (at level 70) : nat_scope.
(* end hide *)

(** ** Árvores binárias *)

(** Utilizaremos números naturais para representar as chaves em cada nó de
    nossas árvores binárias de busca porque os naturais possuem uma ordem
    total [<=?] com diversos teoremas já provados. *)

Definition key := nat.

(** Adicionalmente, os nós armazenarão pares chave/valor, onde o valor
    associado a uma chave terá um tipo [V] qualquer. Definiremos
    indutivamente a estrutura [tree] para representar árvores binárias cujos
    nós contêm uma chave [k] e um valor [v]. As árvores possuem dois
    construtores, [E] que representa a árvore vazia, e [T] que recebe os
    seguintes argumentos:

    - [l]: a subárvore à esquerda do nó atual;
    - [k]: a chave ligada ao nó atual;
    - [v]: o valor associado à chave [k], e;
    - [r]: a subárvore à direita do nó atual.

    Nesta construção, cada chave se liga a apenas um valor. *)

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).

(* begin hide *)
Arguments E {V}.
Arguments T {V}.
(* end hide *)

(** Exemplo: a árvore binária contendo valores do tipo [string]
<<
      4 -> "four"
      /        \
     /          \
  2 -> "two"   5 -> "five"
>>
    é representada a seguir: *)

Definition ex_tree : tree string :=
  (T (T E 2 "two" E) 4 "four" (T E 5 "five" E))%string.

(** A árvore vazia [empty_tree] não contém chaves: *)

Definition empty_tree {V : Type} : tree V := E.

(** ** Busca *)

(** Uma árvore binária de busca é caracterizada pelo seguinte invariante:
    dado qualquer nó não vazio com chave [k], todas as chaves da subárvore à
    esquerda são menores do que [k], e todas as chaves da subárvore à direita
    são maiores do que [k].

Nossa primeira tarefa será formalizar o invariante de uma árvore binária de busca. Faremos isto com a ajuda da função [ForallT]: *)

Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

(** Esta função expressa as condições para que uma árvore satisfaça uma dada
    propriedade [P]: se a árvore for vazia então a propriedade é satisfeita
    por vacuidade, e portanto retorna [True]. Quando a árvore não é vazia, e
    portanto tem a forma [T l k v r], então precisamos que o nó que tem chave
    [k] e valor [v] satisfaça a propriedade [P], assim como as subárvores à
    esquerda e à direita. 

O invariante, chamado [BST], das árvores binárias de busca é composto de dois construtores:

    - O primeiro construtor, denotado por [BST_E], consiste em um axioma que
      estabelece que uma árvore vazia é uma árvore binária de busca.

    - O segundo construtor, denotado por [BST_T], consiste na regra que diz
      que para que uma árvore não vazia [T l x v r] seja uma árvore binária
      de busca é necessário que todas as chaves da subárvore à esquerda sejam
      menores do que [x], todas as chaves da subárvore à direita sejam maiores
      do que [x], e que as subárvores à esquerda e à direita sejam também árvores binárias de busca: *)

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

(* begin hide *)
#[export] Hint Constructors BST : core.
Ltac inv H := inversion H; clear H; subst.
(* end hide *)

(** A primeira operação importante relacionada às árvores binárias de busca
    é certamente a busca, que pode ser implementada de forma muito
    eficiente. Por exemplo, a função [bound k t] retorna [true] quando [k] é
    uma chave de [t], e [false] caso contrário. *)

Fixpoint bound {V : Type} (x : key) (t : tree V) :=
  match t with
  | E => false
  | T l y v r => if x <? y then bound x l
                else if x >? y then bound x r
                     else true
  end.

(** Analogamente, a função [lookup d k t] retorna o valor ligado à chave [k]
    em [t], ou retorna o valor %\emph{default}% [d] quando [k] não é uma chave
    de [t]. *)

Fixpoint lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E => d
  | T l y v r => if x <? y then lookup d x l
                else if x >? y then lookup d x r
                     else v
  end.

(** Observe que se [t] não é uma árvore binária de busca então as funções
    [bound] e [lookup] podem retornar respostas erradas: *)

Module NotBst.
  Open Scope string_scope.

  (** De fato, considere a seguinte árvore que não é uma árvore binária de
      busca: *)

  Definition t : tree string :=
    T (T E 5 "five" E) 4 "four" (T E 2 "two" E).

  (** Ela possui uma ocorrência da chave 2, mas em uma posição não esperada
      pelas funções [bound] e [lookup]: *)

  Example not_bst_bound_wrong :
    bound 2 t = false.
  Proof.
    reflexivity.
  Qed.

  Example not_bst_lookup_wrong :
    lookup "" 2 t <> "two".
  Proof.
    simpl. unfold not. intros contra. discriminate.
  Qed.
End NotBst.

(** ** Inserção *)

(** A segunda operação fundamental de árvores binárias de busca que
    estudaremos neste trabalho é a inserção. A função [insert k v t] insere a
    chave [k] e o valor [v] na árvore binária de busca [t], de forma a
    preservar o invariante de uma árvore binária de busca. Se a chave [k] já
    ocorre em [t], o valor associado a ela é substituído por [v]. *)

Fixpoint insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if x <? y then T (insert x v l) y v' r
                 else if x >? y then T l y v' (insert x v r)
                      else T l x v r
  end.

(* begin hide *)
Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT :   P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H; split.
  - intro H'.
    inv H.
    + reflexivity.
    + contradiction.
  - intro H'; subst.
    inv H; assumption.
Qed.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

#[export] Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply Nat.nlt_ge in H | apply Nat.nle_gt in H]]].
(* end hide *)

(** Vejamos que o predicado [BST] classifica corretamente alguns
    exemplos: *)

Example is_BST_ex :
  BST ex_tree.
Proof.
  unfold ex_tree.
  repeat (constructor; try lia).
Qed.

Example not_BST_ex :
  ~ BST NotBst.t.
Proof.
  unfold NotBst.t. intros contra.
  inv contra. inv H3. lia.
Qed.

(** *** Questão 1 *)
(** Prove que uma árvore vazia (de qualquer tipo) é uma árvore binária de busca. *)

Theorem empty_tree_BST : forall (V : Type),
    BST (@empty_tree V).
Proof.
(* Substitua esta linha pela sua prova. *)Admitted.

(** *** Questão 2 *)
(** Prove que a função [insert] preserva qualquer propriedade dos nós: *)

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t -> forall (k : key) (v : V),
      P k v -> ForallT P (insert k v t).
Proof.
(* Substitua esta linha pela sua prova. *)Admitted.

(** *** Questão 3 *)
(** Prove que ao receber uma árvore binária de busca como argumento, a
    função [insert] gera outra árvore binária de busca. *)

Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> BST (insert k v t).
Proof.
(* Substitua esta linha pela sua prova. *)Admitted.

(** ** A correção das funções de busca [lookup] e [bound] *)

(** Qual o comportamento esperado para as funções [lookup] e [bound]? Ao
    procurarmos uma chave na árvore binária de busca vazia com a função
    [lookup], devemos obter o valor %\emph{default}% [d]: *)

Theorem lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d.
Proof.
  auto.
Qed.

(** Se inserirmos a chave [k] e o valor [v] na árvore binária de busca [t],
    então a busca em [insert k v t] com a função [lookup] retorna [v]: *)

Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v.
Proof.
  induction t; intros; simpl.
  - bdestruct (k <? k); try lia; auto.
  - bdestruct (k <? k0); bdestruct (k0 <? k); simpl; try lia; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try lia; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try lia; auto.
    + bdestruct (k0 <? k0); try lia; auto.
Qed.

(** A tática [bdall] a seguir simplifica esta prova, evitando os passos
    repetitivos: *)

Ltac bdestruct_guard :=
  match goal with
  | |- context [ if ?X =? ?Y then _ else _ ] => bdestruct (X =? Y)
  | |- context [ if ?X <=? ?Y then _ else _ ] => bdestruct (X <=? Y)
  | |- context [ if ?X <? ?Y then _ else _ ] => bdestruct (X <? Y)
  end.

Ltac bdall :=
  repeat (simpl; bdestruct_guard; try lia; auto).

Theorem lookup_insert_eq' :
  forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v.
Proof.
  induction t; intros; bdall.
Qed.

(** *** Questão 4 *)
(** Prove que a busca de uma chave [k'], via a função [lookup], na árvore
    binária de busca [insert k v t], com [k] e [k'] distintos, retorna o
    resultado de buscar [k'] em [t]: *)

Theorem lookup_insert_neq :
  forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
   k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof.
(* Substitua esta linha pela sua prova. *)Admitted.

(** *** Questão 5 *)
(** A relação esperada entre as funções [bound] e [lookup] é que, se [bound k t] retorna [false], então [lookup d k t] retorna o valor  %\emph{default}% [d]. Prove este fato dado pelo seguinte teorema: *)

Theorem bound_default :
  forall (V : Type) (k : key) (d : V) (t : tree V),
    bound k t = false ->
    lookup d k t = d.
Proof.
(* Substitua esta linha pela sua prova. *)Admitted.

(** ** Remoção *)

(** A terceira operação fundamental de árvores binárias de busca é a
    remoção. Remover a chave [x] de uma árvore [T l y v r] com [x <> y] é
    simples: basta remover [x] recursivamente da subárvore adequada. O caso
    interessante ocorre quando [x = y], isto é, quando queremos remover a
    raiz. Se a subárvore à direita [r] for vazia, o resultado é simplesmente
    a subárvore à esquerda [l]. Caso contrário, a raiz é substituída pelo
    %\emph{sucessor}% de [y], ou seja, pela menor chave de [r], que é
    removida de [r]. Esta estratégia é conhecida como %\emph{remoção de
    Hibbard}%.

    A função [remove_min l k v r] recebe as componentes de uma árvore não
    vazia [T l k v r] e retorna uma tripla [(m, w, t')], onde [m] é a menor
    chave da árvore, [w] é o valor associado a [m], e [t'] é a árvore obtida
    removendo-se [m]. Receber as componentes de uma árvore não vazia, ao
    invés de uma árvore qualquer, evita a necessidade de tratar o caso da
    árvore vazia, que não possui menor chave. *)

Fixpoint remove_min {V : Type} (l : tree V) (k : key) (v : V) (r : tree V)
  : key * V * tree V :=
  match l with
  | E => (k, v, r)
  | T ll lk lv lr =>
      let '(m, w, l') := remove_min ll lk lv lr in (m, w, T l' k v r)
  end.

Fixpoint delete {V : Type} (x : key) (t : tree V) : tree V :=
  match t with
  | E => E
  | T l y v r =>
      if x <? y then T (delete x l) y v r
      else if x >? y then T l y v (delete x r)
           else match r with
                | E => l
                | T rl rk rv rr =>
                    let '(m, w, r') := remove_min rl rk rv rr in T l m w r'
                end
  end.

(** Por exemplo, ao removermos a raiz da árvore [ex_tree], ela é
    substituída pela chave [5], que é a menor chave da subárvore à
    direita: *)

Example delete_ex :
  delete 4 ex_tree = (T (T E 2 "two" E) 5 "five" E)%string.
Proof. reflexivity. Qed.

(** Nas provas a seguir, pode ser útil o seguinte lema, que diz que se todos
    os nós de uma árvore satisfazem a propriedade [P], e [P] implica [Q],
    então todos os nós da árvore satisfazem [Q]: *)

Lemma ForallT_impl : forall (V : Type) (P Q : key -> V -> Prop) (t : tree V),
    (forall k v, P k v -> Q k v) -> ForallT P t -> ForallT Q t.
Proof.
  intros V P Q t HPQ; induction t as [| l IHl k v r IHr]; simpl; auto.
  intros [Hk [Hl Hr]]. auto.
Qed.

(** Também será útil uma forma de destruir o resultado de [remove_min] sem
    perder a informação sobre a sua origem. Para isto, utilize a tática
    [destruct (remove_min l k v r) as [[m w] t'] eqn:Hrm]. *)

(** *** Questão 6 *)
(** Prove que a chave removida por [remove_min], assim como a árvore
    resultante, preservam qualquer propriedade dos nós: *)

Lemma ForallT_remove_min :
  forall (V : Type) (P : key -> V -> Prop) (l r t' : tree V) (k m : key) (v w : V),
    ForallT P (T l k v r) ->
    remove_min l k v r = (m, w, t') ->
    P m w /\ ForallT P t'.
Proof.
(* Substitua esta linha pela sua prova. *)Admitted.

(** *** Questão 7 *)
(** Prove que [remove_min] aplicada às componentes de uma árvore binária de
    busca retorna uma árvore binária de busca cujas chaves são todas maiores
    do que a chave removida: *)

Lemma remove_min_BST :
  forall (V : Type) (l r t' : tree V) (k m : key) (v w : V),
    BST (T l k v r) ->
    remove_min l k v r = (m, w, t') ->
    BST t' /\ ForallT (fun y _ => y > m) t'.
Proof.
(* Substitua esta linha pela sua prova. *)Admitted.

(** *** Questão 8 *)
(** Prove que a função [delete] preserva qualquer propriedade dos nós: *)

Lemma ForallT_delete : forall (V : Type) (P : key -> V -> Prop) (k : key) (t : tree V),
    ForallT P t -> ForallT P (delete k t).
Proof.
(* Substitua esta linha pela sua prova. *)Admitted.

(** *** Questão 9 *)
(** Prove que ao receber uma árvore binária de busca como argumento, a
    função [delete] gera outra árvore binária de busca. *)

Theorem delete_BST : forall (V : Type) (k : key) (t : tree V),
    BST t -> BST (delete k t).
Proof.
(* Substitua esta linha pela sua prova. *)Admitted.

