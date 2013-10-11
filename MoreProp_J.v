(* * MoreProp: More about Propositions and Evidence *)
(** MoreProp_J: 命題と根拠についてもう少し *)
Require Export "Prop_J".


(* ####################################################### *)
(* * Relations *)
(** * 関係 *)

(* A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)
(** 数値をパラメータとして持つ命題(例えば、[ev]や[beautiful])は属性（ property ）と 見なすこともできます。つまり、それに属する値についてその命題が証明可能である ような nat の部分集合の定義と見ることができるということです。 同様に、引数（パラメータ）を二つ持つ命題は、その二つの「関係」を表していると 考えられます。つまり、その命題について証明可能な値のペアの集合の定義、 というわけです。 
*)
Module LeModule.  


(* One useful example is the "less than or equal to"
    relation on numbers. *)
(** よく使われるものの例として「等しいかまたは小さい」 という関係があります。 *)
(* The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)
(** この定義はかなり直観的なものになります。これは、ある数値がもう一つの 数値より小さいかまたは等しい、ということを示すには二つの方法があることを 示しています。一つはそれらが同じ数であるかどうかを確認すること。もう 一つは最初の数が。二つ目の数の一つ前の数より小さいかまたは等しい、 ということの根拠を得ることです。 
*)
Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(* Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in chapter [Prop].  We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) -> 2+2=5].) *)
(** コンストラクタ [le_n] と [le_S] を使った [<=] にからむ証明は、前章の [eq] がそうであったように、属性についての証明のいくつかのパターンに倣っています。[<=] の形をしたゴール（例えば [3<=3] や [3<=6] など）に、そのコンストラクタをapply することができますし、inversion のようなタクティックを使って（[(2 <= 1) -> 2+2=5] の証明をしようとする際のように） コンテキストに [<=] を含む仮定から情報を抽出することもできます。
*)
(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)
(** 
    ここで、定義が正しくなされているのかのチェックをしてみましょう。（注意して 欲しいのは、ここでやることが、最初のレクチャーで書いてもらった、ある種のシンプルな「ユニットテスト」のようなものですが、今回のものは以前のものとちょっと違います。今回のものには、[simpl] や [reflexivity] はほとんど役に立ちません。簡約だけで証明できるようなものではないからです。
 *)
Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof. 
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(* The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)
(** 「より小さい」という関係（ [n < m] ）は、[le] を使って定義できます。 *)
End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(* Here are a few more simple relations on numbers: *)
(** 数についての簡単な関係をいくつか示します。*)
Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

(** **** 練習問題 ★★ (total_relation) *)
(* Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)
(** 二つの自然数のペア同士の間に成り立つ帰納的な関係 [total_relation] を
    定義しなさい。 *)
(* FILL IN HERE *)
(** [] *)

(** **** 練習問題 ★★ (empty_relation) *)
(*  Define an inductive relation [empty_relation] (on numbers)
    that never holds. *)
(** 自然数の間では決して成り立たない関係 [empty_relation] を帰納的に
    定義しなさい。 *)
	
(* FILL IN HERE *)
(** [] *)

(** **** 練習問題 ★★, optional (le_exercises) *)
(* Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)
(** 後のコースで必要になる[<=] や [<] といった関係についての事実を示しておきます。その証明自体がとてもよい練習問題に
    なります。*)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  (* FILL IN HERE *) Admitted.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  (* FILL IN HERE *) Admitted.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 unfold lt. 
 (* FILL IN HERE *) Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  (* ヒント: [m]による帰納法の方が簡単に証明出来ます。 *)
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  (* Hint: This theorem can be easily proved without using [induction]. *)
  (* ヒント: この定理は[induction]を使わない方が簡単に証明出来ます。 *)
  (* FILL IN HERE *) Admitted.


(** **** 練習問題 ★★★ (R_provability) *)
Module R.
(* We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)
(** 次は三つや四つの値の間に成り立つ関係を同じように定義してみましょう。
    例えば、次のような数値の三項関係が考えられます。 *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(* - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
*)
(**  - 次の命題のうち、この関係を満たすと証明できると言えるのはどれでしょうか。
      - [R 1 1 2]
      - [R 2 2 6]

    - この関係 [R] の定義からコンストラクタ [c5] を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？端的に（１文で）説明しなさい。

    - この関係 [R] の定義からコンストラクタ [c4] を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？端的に（１文で）説明しなさい。


(* FILL IN HERE *)
[]
*)
(** **** 練習問題 ★★★, optional (R_fact) *)  
(* Relation [R] actually encodes a familiar function.  State and prove two
    theorems that formally connects the relation and the function. 
    That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)
(** 関係 [R] の、等値性に関する特性をあげ、それを証明しなさい。 それは、
    もし [R m n o] が true なら [m] についてどんなことが言えるでしょうか？
    [n] や [o] についてはどうでしょうか？その逆は？
 *)
(* FILL IN HERE *)
(** [] *)

End R.


(* ##################################################### *)
(* * Programming with Propositions *)
(** * 命題によるプログラミング *)

(* A _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop].  Although we haven't discussed this
    explicitly, we have already seen numerous examples. *)
(** 命題（ _proposition_ ）は、"2足す2は4と等しい"のような事実に基づく主張を表現するための文です。Coq において命題は [Prop] 型の式として書かれます。これまであまりそれについて明示的に触れてはきませんでしたが、皆さんはすでに多くの例を見てきています。 *)
Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(* Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)
(** 証明可能な主張も証明不能な主張も、どちらも完全な命題であると言えます。
    しかし単に命題であるということと、証明可能であるということは別ものです！ *)
Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(* Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)
(** [2 + 2 = 4]も[2 + 2 = 5]も[Prop]型として、正しい式です。*)
 	
(* We've mainly seen one place that propositions can appear in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)
(** これまで Coq の中で命題を使う方法は1つしか見ていません。 [Theorem]（あるいは [Lemma]、[Example]）の宣言の中でだけです。 *)
Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(* But they can be used in many other ways.  For example, we have also seen that
    we can give a name to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. *)
(** しかし命題にはもっといろいろな使い方があります。
    例えば、他の種類の式（数字、関数、型、型関数など）と同様に、[Definition] を使うことで命題に名前を与えることができます。 *)
Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(* We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)
(**  命題が使える場所ならどこでも、例えば、[Theorem] 宣言内の主張などとしてこの名前を使うことができます。 *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(* We've seen several ways of constructing propositions.  

       - We can define a new proposition primitively using [Inductive].

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal.

       - We can combine propositions using implication and
         quantification. *)
(** これまでも命題を構築する幾つかの方法を見てきました。

       - [Inductive]を原始的に(公理として)使うことで新しい命題を定義することが出来ます。

       - 同じ型の二つの式[e1]と[e2]が与えられれば、[e1 = e2]という命題を構成して、それらの値が等しいか評価することが出来ます。

       -含意と量化を用いることで命題を結合することが出来ます。*)

(* We have also seen _parameterized propositions_, such as [even] and
    [beautiful]. *)	
(** [even]や[beautiful]のような、パラメータつきの命題をこれまで見てきました。*)
Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even. 
(* ===> even : nat -> Prop *)

(* The type of [even], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)
(** [even]の型、つまり[nat->Prop]は三つの同等な方法で宣言されます。(1)[even]は数を取って命題を返す関数である。
(2)[even]は命題の族であり数[n]によってインデクス化されている。(3)[even]は数に関する性質を表す。
*)

(* Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  For example, we can define functions
    from numbers to propositions... *)
(** *命題(パラメータつきの命題を含む) ）はCoqにおける第一級（_first-class_）市民です。このため、ほかの定義の中でこれらの命題を使うことができます。*)
Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... and then partially apply them: *)
(** ...部分適用もできます。*)

Definition teen : nat->Prop := between 13 19.

(* We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)
(** 他の関数に、引数として命題（パラーメータ化された命題も含む）を渡すことすらできます。 *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(* Here are two more examples of passing parameterized propositions
    as arguments to a function.  

    The first function, [true_for_all_numbers], takes a proposition
    [P] as argument and builds the proposition that [P] is true for
    all natural numbers. *)
(** パラメータ化された命題を引数として渡す関数をさらに2つ紹介します。1つ目の関数は、ある自然数 [n'] について [P] が真ならば常に [n'] の次の数でも [P] が真であることを述べています。*)
Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

  (* The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)
(** そして次の関数は、すべての自然数について与えられた命題が真であることを述べています。 *)
Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(* Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)
(** 最後に、これらを一つにまとめることで、自然数に関する帰納法の原理を自分で再宣言できます。
    パラメータ化された命題 [P] が与えられた場合、[0] について [P] が真であり、[P n'] が真のとき [P (S n')] が真であるならば、すべての自然数について [P] は真である。*)
Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 



(** **** 練習問題 ★★★ (combine_odd_even) *)
(* Complete the definition of the [combine_odd_even] function
    below. It takes as arguments two properties of numbers [Podd] and
    [Peven]. As its result, it should return a new property [P] such
    that [P n] is equivalent to [Podd n] when [n] is odd, and
    equivalent to [Peven n] otherwise. *)
(**	以下の[combine_odd_even]関数の定義を完成させなさい。それは二つの数の性質[Podd]と[Peven]を引数にとります。その結果として、新たな性質[P]、[n]が奇数の時、[P n]は、[Podd n]と等しく、そうでないときは、[Peven n]と等しくなる命題を返却します。*)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (* FILL IN HERE *) admit.

(* To test your definition, see whether you can prove the following
    facts: *)
(** あなたの定義をテストするために、次の事実が証明出来るかどうか確かめなさい。 *)
Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ##################################################### *)
(* One more quick digression, for adventurous souls: if we can define
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)
(** 冒険心を満足させるために、もう少し脱線してみましょう。[Definition] でパラメータ化された命題を定義できるなら、 [Fixpoint] でも定義できていいのではないでしょうか？もちろんできます！しかし、この種の 「再帰的なパラメータ化」は、日常的に使われる数学の分野と必ずしも調和するわけではありません。そんなわけで次の練習問題は、例としてはいささか不自然かもしれません。*)
(** **** 練習問題 ★★★★, optional (true_upto_n__true_everywhere) *)
(*  Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)
(** [true_upto_n_example] を満たすような再帰関数 [true_upto_n__true_everywhere]
    を定義しなさい。
 *)
(* 
Fixpoint true_upto_n__true_everywhere
(* FILL IN HERE *)

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
*)
(** [] *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

