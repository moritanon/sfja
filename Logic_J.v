(* * Logic: Logic in Coq *)
(** * Logic_J: Coqにおける論理 *)

Require Export MoreCoq_J. 



(* Coq's built-in logic is very small: the only primitives are
    [Inductive] definitions, universal quantification ([forall]), and
    implication ([->]), while all the other familiar logical
    connectives -- conjunction, disjunction, negation, existential
    quantification, even equality -- can be encoded using just these.

    This chapter explains the encodings and shows how the tactics
    we've seen can be used to carry out standard forms of logical
    reasoning involving these connectives. *)
(** Coqにあらかじめ組み込まれた論理は極めて小さく、帰納的定義([Inductive])、全称量化([forall])、含意([->])だけがプリミティブです。しかしそれ以外の論理結合子（かつ、または、否定、存在量化子、等号など）も、組み込みのものを用いて定義できます。

    この章では、そのエンコーディング(Coqでどのように表現されるかということか？)を説明し、これまで見て来たタクティックが これらの結合子を含んだ論理的推論の標準形式を実行するためにどのように使用されるのかを示します。*)

(* ########################################################### *)
(* * Propositions *)
(** * 命題 *)

(* In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions ([forall
    x, P]).  In this chapter, we will see how Coq can be used to carry
    out other familiar forms of logical reasoning.

    Before diving into details, let's talk a bit about the status of
    mathematical statements in Coq.  Recall that Coq is a _typed_
    language, which means that every sensible expression in its world
    has an associated type.  Logical claims are no exception: any
    statement we might try to prove in Coq has a type, namely [Prop],
    the type of _propositions_.  We can see this with the [Check]
    command: *)
*)
(** 以前の章で、事実の主張（命題）とそれらが真であるという証拠を表現する方法（証明）の多くの例を見てきました。
とりわけ、e2 = e2という形の等価命題、P → Q という形の含意、そして、∀ x , P という量化命題を広く使用してきました。
この章において、Coqが他の論理形式を用いて推論を行うのか見ていくことにしましょう。

詳細に立ち入る前に、数学的な文がCoqにおいてどのような内部状態を持つのかについてお話ししましょう。Coqが_型付_の言語であることを思い出してください。
その意味するところは、その世界の全ての理解可能な表現が型と結び付いているということです。論理的主張も例外ではありません。
Coqで証明してきたような全ての文は、[Prop]という名前の型を持っています。_命題_という型です。[Check]コマンドで確かめてみましょう。
*)
(* In Coq, the type of things that can (potentially) 
    be proven is [Prop]. *)
(** Coqにおいて、(潜在的に)証明されるものの型は、[Prop]です。*)

Check 3 = 3.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(*  Note that all well-formed propositions have type [Prop] in Coq,
    regardless of whether they are true or not. Simply _being_ a
    proposition is one thing; being _provable_ is something else! *)
(** Coqでは、全てのちゃんとした形の命題は、[Prop]という型を持っており、それが真であるかどうかは関係ありません。
単に_命題である_ということは、その命題が証明可能であるかどうかとは別のことです! *)

Check forall n : nat, n = 2.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

(*  Indeed, propositions don't just have types: they are _first-class
    objects_ that can be manipulated in the same ways as the other
    entities in Coq's world.  So far, we've seen one primary place
    that propositions can appear: in [Theorem] (and [Lemma] and
    [Example]) declarations. *)
(** 確かに、命題は、単に型を持っているだけではありません: Coqの世界の中で、他の構成要素と同じように扱われる_第一級のオブジェクト_(_first-class object_)でもあります。
これまでに命題が現われた最初の場所の一つは、[Theorem](そして[Lemma]と[Example]の宣言でした。 *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(*  But propositions can be used in many other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    have given names to expressions of other sorts. *)
(** しかし命題は、多くの他の方法でも使用されています。例えば、他の種類の式に名前をつけるのと同じように、[Definition]を使って、命題に名前をつけることができます。

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(*  We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)
(** 後なって命題が必要となるあらゆる状況で、その命題につけた名前が使われます。-- 例えば、[Theorem]の宣言の中とかです。*)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(*  We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)
(** _パラメータつきの_命題というものを書くことも出来ます。--すなわち、何か型を物引数を取ったり、命題を返す関数です。
例えば、次の関数は、自然数を引数にとり、その自然数が3と等しいことを主張する命題を返却します: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(*  In Coq, functions that return propositions are said to define
    _properties_ of their arguments.  For instance, here's a
    polymorphic property defining the familiar notion of an _injective
    function_. *)
(** Coqにおいて、命題を返す関数は、それら引数のプロパティを定義するものであると言われます。よく知られた概念である単射関数を定義する多相的な属性の例を挙げてみましょう。*)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

(** The equality operator [=] that we have been using so far is also
    just a function that returns a [Prop]. The expression [n = m] is
    just syntactic sugar for [eq n m], defined using Coq's [Notation]
    mechanism. Because [=] can be used with elements of any type, it
    is also polymorphic: *)
(** これまでにも使用してきた、等しさを表す演算子[=]も[Prop]を返す関数に過ぎません。[n = m]という式は、[eq n m]の糖衣構文であり、
Coqの「Notation]メカニズムを使用して定義されています。[=]はあらゆる型の要素と使用出来るのは、多相的でもあるからです。*)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(** (Notice that we wrote [@eq] instead of [eq]: The type argument [A]
    to [eq] is declared as implicit, so we need to turn off implicit
    arguments to see the full type of [eq].) *)
(** [eq]の代わりに[@eq]と書いたことに気をつけましょう: [eq]に与える型変数[A]は暗黙的に宣言されていますので、
[eq]の完全な型を見るために、暗黙の宣言から切り替える必要があります。*)

(* #################################################################### *)
(*  * Logical Connectives *)
(** * 論理結合子 *)

(*  ** Conjunction *)
(** * 論理積 *)

(*  The _conjunction_ or _logical and_ of propositions [A] and [B] is
    written [A /\ B], denoting the claim that both [A] and [B] are
    true. *)
(** 命題[A]と[B]からなる_論理積_ 又は論理的なand_ は [A /\ B]と書きます。[A]と[B]が共に真であることを主張している。ということを意味します。 *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(*  To prove a conjunction, use the [split] tactic.  Its effect is to
    generate two subgoals, one for each part of the statement: *)
(** 論理積を証明するために、[split]タクティックを使います。その効果は二つのサブゴールを生成して、それぞれの部分に割り当てます。*)
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(*  More generally, the following principle works for any two
    propositions [A] and [B]: *)
(** もっと一般的に言えば、任意の二つの命題[A][B]に対して次に示す原理が働いています。

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(** A logical statement with multiple arrows is just a theorem that
    has several hypotheses.  Here, [and_intro] says that, for any
    propositions [A] and [B], if we assume that [A] is true and we
    assume that [B] is true, then [A /\ B] is also true.

    Since applying a theorem with hypotheses to some goal has the
    effect of generating as many subgoals as there are hypotheses for
    that theorem, we can, apply [and_intro] to achieve the same effect
    as [split]. *)
(** 複数の矢印を持つ論理的な文は仮説を持つ定理に過ぎません。ここで、[and_intro]が言うことは、任意の命題[A]と[B]があるとして、
[A]がtrueであると仮定し、[B]もtrueであると仮定するならば、[A /\ B]もまたtrueである。ということです。

仮説を伴う[and_intro]定理をゴールに適用することによって、仮説のぶんだけ、サブゴールが生成される、[split]と同じ効果があります。

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** 練習問題: ★★ (and_exercise) *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to prove
    something else -- we employ the [destruct] tactic.

    If the proof context contains a hypothesis [H] of the form [A /\
    B], writing [destruct H as [HA HB]] will remove [H] from the
    context and add two new hypotheses: [HA], stating that [A] is
    true, and [HB], stating that [B] is true.  For instance: *)
(**  論理積の文を証明するのはこれまでとします。別の方向 -- 論理積を仮定として使って何かを証明したり---
に行くために、[destruct]タクティックを使うことにします。*)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(*  As usual, we can also destruct [H] when we introduce it instead of
    introducing and then destructing it: *)
(** 通常、[H]を導入してそのあとデストラクトする代わりに、導入したときに[H]をデストラクト出来ます。*)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(*  You may wonder why we bothered packing the two hypotheses [n = 0]
    and [m = 0] into a single conjunction, since we could have also
    stated the theorem with two separate premises: *)
(** 一つの論理積に対して、二つの仮説[n = 0]と[m = 0]をわざわざ包む必要があるんだろうと思うかもしれません。
二つの分かれた前提を持つ定理をすでに提示しているからです。*)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** In this case, there is not much difference between the two
    theorems.  But it is often necessary to explicitly decompose
    conjunctions that arise from intermediate steps in proofs,
    especially in bigger developments.  Here's a simplified
    example: *)
(** この場合、二つの定理の間に違いがあまりありません。しかし、証明の途中で生成される論理積を明示的に分解する必要がしばしば出てきます。
とりわけ、もっと大きい証明を行なうときなどです。ここに単純化した例を示します。

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** Another common situation with conjunctions is that we know [A /\
    B] but in some context we need just [A] (or just [B]).  The
    following lemmas are useful in such cases: *)
(** 別の論理積が出てくるよくある状況は、[A /\ B]であることは知っているが、今Contextに必要なのは単なる[A](または単なる[B])であるような場合です。
次のような補題が、そのようなケースに役に立つでしょう。*)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.  Qed.

(*  **** Exercise: 1 star, optional (proj2)  *)
(** **** 練習問題: ★, optional (proj2) *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of conjuncts in multi-way conjunctions.  The
    following commutativity and associativity theorems come in handy
    in such cases. *)
(** 最後に、and/orの結合の順序を変更することが必要になるときがあります。次の交換法則と結合法則の定理がその場合に役に立つでしょう。*)
(*  The logical conjunction of propositions [P] and [Q] can be
    represented using an [Inductive] definition with one
    constructor. *)
(** 命題 [P] と [Q] の論理積（ [logical conjunction] ）は、コンストラクタを一つしか持たない [Inductive] を使った定義で表せます。 *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.
  
(*  **** Exercise: 2 stars (and_assoc)  *)
(** **** 練習問題: ★★  optional (and_asoc) *)
(*  (In the following proof of associativity, notice how the _nested_
    intro pattern breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP : P], [HQ : Q], and [HR : R].  Finish the proof from
    there.) *)
(** 次の結合性の証明においては、ネストしたintroパターンがどのように仮説[H: P /\ (Q /\ R)]をどのように分解して
[HP: P] [HQ: Q]そして [HE : R]とするかについて、注意して見てください。それから証明を終えてください。*)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
(* FILL IN HERE *) Admitted.
(** [] *)

(*  By the way, the infix notation [/\] is actually just syntactic
    sugar for [and A B].  That is, [and] is a Coq operator that takes
    two propositions as arguments and yields a proposition. *)
(** ところで、[/\]という中置記法は実際には、[and A B]の糖衣構文に過ぎません。すなわち、[and]はCoqの二つの命題を引数にとって、命題を返す演算子であるということです。*)

Check and.
(* ===> and : Prop -> Prop -> Prop *)

(*  ** Disjunction *)
(** ** 論理和 *)

(*  Another important connective is the _disjunction_, or _logical or_
    of two propositions: [A \/ B] is true when either [A] or [B]
    is.  (Alternatively, we can write [or A B], where [or : Prop ->
    Prop -> Prop].)

    To use a disjunctive hypothesis in a proof, we proceed by case
    analysis, which, as for [nat] or other data types, can be done
    with [destruct] or [intros].  Here is an example: *)
(** もうひとつの結合子は二つの命題からなる_論理和、または、論理的 orです: [A \/ B]は [A]または、[B]のどちらかが
真であるときに、真になります。(\/の代わりに[or A B]と書くことが出来ます。その型は[or : Prop -> Prop -> Prop]です。*)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(*  We can see in this example that, when we perform case analysis on
    a disjunction [A \/ B], we must satisfy two proof obligations,
    each showing that the conclusion holds under a different
    assumption -- [A] in the first subgoal and [B] in the second.
    Note that the case analysis pattern ([Hn | Hm]) allows us to name
    the hypothesis that is generated in each subgoal.

    Conversely, to show that a disjunction holds, we need to show that
    one of its sides does. This is done via two tactics, [left] and
    [right].  As their names imply, the first one requires proving the
    left side of the disjunction, while the second requires proving
    its right side.  Here is a trivial use... *)
(** この例の中で、論理和[A \/ B]のケース分析を行なう時、二つの証明の責任、結論が異なる仮定から保持されていること、
-- 最初のサブゴール中の[A]と二つめのサブゴールの[B] -- を満たす必要があります。 ([Hn| Hm])というケース分析パターンは
それぞれのサブゴールで生成される仮説に名前をつける必要があることに注意してください。

反対に、論理和がゴールにある場合、論理和の一方が成り立つことを示す必要があります。これは二つのタクティックを経由することで達成されます。
[left]と[right]です。その名前が示すように、始めの方は、論理和の左側の証明を必要とし、もう一方は、右側を必要とします。
簡単な使い方が以下になります… *)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.


(*  ... and a slightly more interesting example requiring the use of
    both [left] and [right]: *)
(** もう少し興味深い例は[left]と[right]の両方を必要になります。 *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(*  **** Exercise: 1 star (mult_eq_0)  *)
(** **** 練習問題: ★ (mult_eq_0) *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star (or_commut)  *)
(** **** 練習問題: ★ (or_commut) *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  ** Falsehood and Negation *)
(** ** 偽と否定 *)

(*  So far, we have mostly been concerned with proving that certain
    things are _true_ -- addition is commutative, appending lists is
    associative, etc.  Of course, we may also be interested in
    _negative_ results, showing that certain propositions are _not_
    true. In Coq, such negative statements are expressed with the
    negation operator [~].

    To see how negation works, recall the discussion of the _principle
    of explosion_ from the [Tactics] chapter; it asserts that, if we
    assume a contradiction, then any other proposition can be derived.
    Following this intuition, we could define [~ P] ("not [P]") as
    [forall Q, P -> Q].  Coq actually makes a slightly different
    choice, defining [~ P] as [P -> False], where [False] is a
    _particular_ contradictory proposition defined in the standard
    library. *)
(** これまでに
Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can [destruct] it to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** **** Exercise: 2 stars, optional (not_implies_our_not)  *)
(** Show that Coq's definition of negation implies the intuitive one
    mentioned above: *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** This is how we use [not] to state that [0] and [1] are different
    elements of [nat]: *)

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

(** Such inequality statements are frequent enough to warrant a
    special notation, [x <> y]: *)

Check (0 <> 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.

(** It takes a little practice to get used to working with negation in
    Coq.  Even though you can see perfectly well why a statement
    involving negation is true, it can be a little tricky at first to
    get things into the right configuration so that Coq can understand
    it!  Here are proofs of a few familiar facts to get you warmed
    up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced, recommended (double_neg_inf)  *)
(** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
(* FILL IN HERE *)
   []
*)

(** **** Exercise: 2 stars, recommended (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, advanced (informal_not_PNP)  *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)
(** [] *)

(** Similarly, since inequality involves a negation, it requires a
    little practice to be able to work with it fluently.  Here is one
    useful trick.  If you are trying to prove a goal that is
    nonsensical (e.g., the goal state is [false = true]), apply
    [ex_falso_quodlibet] to change the goal to [False].  This makes it
    easier to use assumptions of the form [~P] that may be available
    in the context -- in particular, assumptions of the form
    [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** Since reasoning with [ex_falso_quodlibet] is quite common, Coq
    provides a built-in tactic, [exfalso], for applying it. *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.

(*  ** Truth *)
(** 真 *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    predefined constant [I : True]: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** Unlike [False], which is used extensively, [True] is used quite
    rarely, since it is trivial (and therefore uninteresting) to prove
    as a goal, and it carries no useful information as a hypothesis.
    But it can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s.  We will
    see some examples such uses of [True] later on. *)

(** ** Logical Equivalence *)

(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is just the conjunction of
    two implications. *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. inversion H'.
Qed.

(** **** Exercise: 1 star, optional (iff_properties)  *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Some of Coq's tactics treat [iff] statements specially, avoiding
    the need for some low-level proof-state manipulation.  In
    particular, [rewrite] and [reflexivity] can be used with [iff]
    statements, not just equalities.  To enable this behavior, we need
    to import a special Coq library that allows rewriting with other
    formulas besides equality: *)

Require Import Coq.Setoids.Setoid.

(** Here is a simple example demonstrating how these tactics work with
    [iff].  First, let's prove a couple of basic iff equivalences: *)

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** We can now use these facts with [rewrite] and [reflexivity] to
    give smooth proofs of statements involving equivalences.  Here is
    a ternary version of the previous [mult_0] result: *)

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

(** The [apply] tactic can also be used with [<->]. When given an
    equivalence as its argument, [apply] tries to guess which side of
    the equivalence to use. *)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* ############################################################ *)
(** ** Existential Quantification *)

(** Another important logical connective is _existential
    quantification_.  To say that there is some [x] of type [T] such
    that some property [P] holds of [x], we write [exists x : T,
    P]. As with [forall], the type annotation [: T] can be omitted if
    Coq is able to infer from the context what the type of [x] should
    be.

    To prove a statement of the form [exists x, P], we must show that
    [P] holds for some specific choice of value for [x], known as the
    _witness_ of the existential.  This is done in two steps: First,
    we explicitly tell Coq which witness [t] we have in mind by
    invoking the tactic [exists t]; then we prove that [P] holds after
    all occurrences of [x] are replaced by [t].  Here is an example: *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.  Qed.

(** **** Exercise: 1 star (dist_not_exists)  *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)

(* #################################################################### *)
(*  * Programming with Propositions *)
(** 命題を使ったプログラミング *)

(** The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure:

    - If [l] is the empty list, then [x] cannot occur on it, so the
      property "[x] appears in [l]" is simply false.

    - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
      occurs in [l] if either it is equal to [x'] or it occurs in
      [l']. *)

(** We can translate this directly into a straightforward Coq
    function, [In].  (It can also be found in the Coq standard
    library.) *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested conjunctions. *)

Example In_example_1 : In 4 [3; 4; 5].
Proof.
  simpl. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)

(** We can also prove more generic, higher-level lemmas about [In].
    Note, in the next, how [In] starts out applied to a variable and
    only gets expanded when we do case analysis on this variable: *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** This way of defining propositions, though convenient in some
    cases, also has some drawbacks.  In particular, it is subject to
    Coq's usual restrictions regarding the definition of recursive
    functions, e.g., the requirement that they be "obviously
    terminating."  In the next chapter, we will see how to define
    propositions _inductively_, a different technique with its own set
    of strengths and limitations. *)

(** **** Exercise: 2 stars (In_map_iff)  *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (in_app_iff)  *)
Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (All)  *)
(** Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
  (* FILL IN HERE *) admit.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (combine_odd_even)  *)
(** Complete the definition of the [combine_odd_even] function below.
    It takes as arguments two properties of numbers, [Podd] and
    [Peven], and it should return a property [P] such that [P n] is
    equivalent to [Podd n] when [n] is odd and equivalent to [Peven n]
    otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (* FILL IN HERE *) admit.

(** To test your definition, prove the following facts: *)

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

(* #################################################################### *)
(*  * Applying Theorems to Arguments *)
(** * 定理を引数に適用すること *)

(** One feature of Coq that distinguishes it from many other proof
    assistants is that it treats _proofs_ as first-class objects.

    There is a great deal to be said about this, but it is not
    necessary to understand it in detail in order to use Coq.  This
    section gives just a taste, while a deeper exploration can be
    found in the optional chapters [ProofObjects] and
    [IndPrinciples]. *)

(** We have seen that we can use the [Check] command to ask Coq to
    print the type of an expression.  We can also use [Check] to ask
    what theorem a particular identifier refers to. *)

Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

(** Coq prints the _statement_ of the [plus_comm] theorem in the same
    way that it prints the _type_ of any term that we ask it to
    [Check].  Why?

    The reason is that the identifier [plus_comm] actually refers to a
    _proof object_ -- a data structure that represents a logical
    derivation establishing of the truth of the statement [forall n m
    : nat, n + m = m + n].  The type of this object _is_ the statement
    of the theorem that it is a proof of.

    Intuitively, this makes sense because the statement of a theorem
    tells us what we can use that theorem for, just as the type of a
    computational object tells us what we can do with that object --
    e.g., if we have a term of type [nat -> nat -> nat], we can give
    it two [nat]s as arguments and get a [nat] back.  Similarly, if we
    have an object of type [n = m -> n + n = m + m] and we provide it
    an "argument" of type [n = m], we can derive [n + n = m + m].

    Operationally, this analogy goes even further: by applying a
    theorem, as if it were a function, to hypotheses with matching
    types, we can specialize its result without having to resort to
    intermediate assertions.  For example, suppose we wanted to prove
    the following result: *)

Lemma plus_comm3 :
  forall n m p, n + (m + p) = (p + m) + n.

(** It appears at first sight that we ought to be able to prove this
    by rewriting with [plus_comm] twice to make the two sides match.
    The problem, however, is that the second [rewrite] will undo the
    effect of the first. *)

Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)

(** One simple way of fixing this problem, using only tools that we
    already know, is to use [assert] to derive a specialized version
    of [plus_comm] that can be used to rewrite exactly where we
    want. *)

  rewrite plus_comm.
  assert (H : m + p = p + m).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** A more elegant alternative is to apply [plus_comm] directly to the
    arguments we want to instantiate it with, in much the same way as
    we apply a polymorphic function to a type argument. *)

Lemma plus_comm3_take2 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.

(** You can "use theorems as functions" in this way with almost all
    tactics that take a theorem name as an argument.  Note also that
    theorem application uses the same inference mechanisms as function
    application; thus, it is possible, for example, to supply
    wildcards as arguments to be inferred, or to declare some
    hypotheses to a theorem as implicit by default.  These features
    are illustrated in the proof below. *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples of the idioms from this section in
    later chapters. *)

(* #################################################################### *)
(*  * Coq vs. Set Theory *)
(** * Coq 対 集合論 *)

(** Coq's logical core, the _Calculus of Inductive Constructions_,
    differs in some important ways from other formal systems that are
    used by mathematicians for writing down precise and rigorous
    proofs.  For example, in the most popular foundation for
    mainstream paper-and-pencil mathematics, Zermelo-Fraenkel Set
    Theory (ZFC), a mathematical object can potentially be a member of
    many different sets; a term in Coq's logic, on the other hand, is
    a member of at most one type.  This difference often leads to
    slightly different ways of capturing informal mathematical
    concepts, though these are by and large quite natural and easy to
    work with.  For example, instead of saying that a natural number
    [n] belongs to the set of even numbers, we would say in Coq that
    [ev n] holds, where [ev : nat -> Prop] is a property describing
    even numbers.

    However, there are some cases where translating standard
    mathematical reasoning into Coq can be either cumbersome or
    sometimes even impossible, unless we enrich the core logic with
    additional axioms.  We conclude this chapter with a brief
    discussion of some of the most significant differences between the
    two worlds. *)

(** ** Functional Extensionality

    The equality assertions that we have seen so far mostly have
    concerned elements of inductive types ([nat], [bool], etc.).  But
    since Coq's equality operator is polymorphic, these are not the
    only possibilities -- in particular, we can write propositions
    claiming that two _functions_ are equal to each other: *)

Example function_equality_ex : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

(** In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same outputs:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_.

    Informally speaking, an "extensional property" is one that
    pertains to an object's observable behavior.  Thus, functional
    extensionality simply means that a function's identity is
    completely determined by what we can observe from it -- i.e., in
    Coq terms, the results we obtain after applying it.

    Functional extensionality is not part of Coq's basic axioms: the
    only way to show that two functions are equal is by
    simplification (as we did in the proof of [function_equality_ex]).
    But we can add it to Coq's core logic using the [Axiom]
    command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Using [Axiom] has the same effect as stating a theorem and
    skipping its proof using [Admitted], but it alerts the reader that
    this isn't just something we're going to come back and fill in
    later!

    We can now invoke functional extensionality in proofs: *)

Lemma plus_comm_ext : plus = fun n m => m + n.
Proof.
  apply functional_extensionality. intros n.
  apply functional_extensionality. intros m.
  apply plus_comm.
Qed.

(** Naturally, we must be careful when adding new axioms into Coq's
    logic, as they may render it inconsistent -- that is, it may
    become possible to prove every proposition, including [False]!
    Unfortunately, there is no simple way of telling whether an axiom
    is safe: hard work is generally required to establish the
    consistency of any particular combination of axioms.  Fortunately,
    it is known that adding functional extensionality, in particular,
    _is_ consistent.

    Note that it is possible to check whether a particular proof
    relies on any additional axioms, using the [Print Assumptions]
    command. For instance, if we run it on [plus_comm_ext], we see
    that it uses [functional_extensionality]: *)

Print Assumptions plus_comm_ext.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(** **** Exercise: 5 stars (tr_rev)  *)
(** One problem with the definition of the list-reversing function
    [rev] that we have is that it performs a call to [app] on each
    step; running [app] takes time asymptotically linear in the size
    of the list, which means that [rev] has quadratic running time.
    We can improve this with the following definition: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** This version is said to be _tail-recursive_, because the recursive
    call to the function is the last operation that needs to be
    performed (i.e., we don't have to execute [++] after the recursive
    call); a decent compiler will generate very efficient code in this
    case.  Prove that both definitions are indeed equivalent. *)


Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
(* FILL IN HERE *) Admitted.
(** [] *)

(** ** Propositions and Booleans *)

(** We've seen that Coq has two different ways of encoding logical
    facts: with _booleans_ (of type [bool]), and with
    _propositions_ (of type [Prop]). For instance, to claim that a
    number [n] is even, we can say either (1) that [evenb n] returns
    [true] or (2) that there exists some [k] such that [n = double k].
    Indeed, these two notions of evenness are equivalent, as can
    easily be shown with a couple of auxiliary lemmas (one of which is
    left as an exercise).

    We often say that the boolean [evenb n] _reflects_ the proposition
    [exists k, n = double k].  *)

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: 3 stars (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  (* Hint: Use the [evenb_S] lemma from [Induction.v]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either (1) that [beq_nat n m] returns [true] or (2) that [n =
    m].  These two notions are equivalent. *)

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

(** However, while the boolean and propositional formulations of a
    claim are equivalent from a purely logical perspective, we have
    also seen that they need not be equivalent _operationally_.
    Equality provides an extreme example: knowing that [beq_nat n m =
    true] is generally of little help in the middle of a proof
    involving [n] and [m]; however, if we convert the statement to the
    equivalent form [n = m], we can rewrite with it.

    The case of even numbers is also interesting.  Recall that, when
    proving the backwards direction of
    [even_bool_prop] ([evenb_double], going from the propositional to
    the boolean claim), we used a simple induction on [k]).  On the
    other hand, the converse (the [evenb_double_conv] exercise)
    required a clever generalization, since we can't directly prove
    [(exists k, n = double k) -> evenb n = true].

    For these examples, the propositional claims were more useful than
    their boolean counterparts, but this is not always the case.  For
    instance, we cannot test whether a general proposition is true or
    not in a function definition; as a consequence, the following code
    fragment is rejected: *)

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq complains that [n = 2] has type [Prop], while it expects an
    elements of [bool] (or some other inductive type with two
    elements).  The reason for this error message has to do with the
    _computational_ nature of Coq's core language, which is designed
    so that every function that it can express is computable and
    total.  One reason for this is to allow the extraction of
    executable programs from Coq developments.  As a consequence,
    [Prop] in Coq does _not_ have a universal case analysis operation
    telling whether any given proposition is true or false, since such
    an operation would allow us to write non-computable functions.

    Although general non-computable properties cannot be phrased as
    boolean computations, it is worth noting that even many
    _computable_ properties are easier to express using [Prop] than
    [bool], since recursive function definitions are subject to
    significant restrictions in Coq.  For instance, the next chapter
    shows how to define the property that a regular expression matches
    a given string using [Prop].  Doing the same with [bool] would
    amount to writing a regular expression matcher, which would be
    more complicated, harder to understand, and harder to reason
    about.

    Conversely, an important side benefit of stating facts using
    booleans is enabling some proof automation through computation
    with Coq terms, a technique known as _proof by
    reflection_. Consider the following statement: *)

Example even_1000 : exists k, 1000 = double k.

(** The most direct proof of this fact is to give the value of [k]
    explicitly. *)

 Proof. exists 500. reflexivity. Qed.

(** On the other hand, the proof of the corresponding boolean
    statement is even simpler: *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

(** What is interesting is that, since the two notions are equivalent,
    we can use the boolean formulation to prove the other one without
    mentioning 500 explicitly: *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof size in this
    case, larger proofs can often be made considerably simpler by the
    use of reflection.  As an extreme example, the Coq proof of the
    famous _4-color theorem_ uses reflection to reduce the analysis of
    hundreds of different cases to a boolean computation.  We won't
    cover reflection in great detail, but it serves as a good example
    showing the complementary strengths of booleans and general
    propositions. *)

(** **** Exercise: 2 stars (logical_connectives)  *)
(** The following lemmas relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (beq_nat_false_iff)  *)
(** The following theorem is an alternate "negative" formulation of
    [beq_nat_true_iff] that is more convenient in certain
    situations (we'll see examples in later chapters). *)

Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (beq_list)  *)
(** Given a boolean operator [beq] for testing equality of elements of
    some type [A], we can define a function [beq_list beq] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [beq_list] function below.  To make sure that your
    definition is correct, prove the lemma [beq_list_true_iff]. *)

Fixpoint beq_list {A} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  (* FILL IN HERE *) admit.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, recommended (All_forallb)  *)
(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Tactics]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** Prove the theorem below, which relates [forallb] to the [All]
    property of the above exercise. *)

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.

(** Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

(* FILL IN HERE *)
(** [] *)

(** ** Classical vs. Constructive Logic *)

(** We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Coq function.  You may be
    surprised to learn that a similar restriction applies to _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Coq: *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** To understand operationally why this is the case, recall that, to
    prove a statement of the form [P \/ Q], we use the [left] and
    [right] tactics, which effectively require knowing which side of
    the disjunction holds.  However, the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply, just as Coq doesn't have enough
    information to mechanically decide whether [P] holds or not inside
    a function.  On the other hand, if we happen to know that [P] is
    reflected in some boolean term [b], then knowing whether it holds
    or not is trivial: we just have to check the value of [b].  This
    leads to the following theorem: *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m].

    You may find it strange that the general excluded middle is not
    available by default in Coq; after all, any given claim must be
    either true or false.  Nonetheless, there is an advantage in not
    assuming the excluded middle: statements in Coq can make stronger
    claims than the analogous statements in standard mathematics.
    Notably, if there is a Coq proof of [exists x, P x], it is
    possible to explicitly exhibit a value of [x] for which we can
    prove [P x] -- in other words, every proof of existence is
    necessarily _constructive_.  Because of this, logics like Coq's,
    which do not assume the excluded middle, are referred to as
    _constructive logics_.  More conventional logical systems such as
    ZFC, in which the excluded middle does hold for arbitrary
    propositions, are referred to as _classical_.

    The following example illustrates why assuming the excluded middle
    may lead to non-constructive proofs: *)

(** _Claim_: There exist irrational numbers [a] and [b] such that [a ^
    b] is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.
    If [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b =
    sqrt 2] and we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is
    irrational.  In this case, we can take [a = sqrt 2 ^ sqrt 2] and
    [b = sqrt 2], since [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^
    2 = 2].  []

    Do you see what happened here?  We used the excluded middle to
    consider separately the cases where [sqrt 2 ^ sqrt 2] is rational
    and where it is not, without knowing which one actually holds!
    Because of that, we wind up knowing that such [a] and [b] exist
    but we cannot determine what their actual values are (at least,
    using this line of argument).

    As useful as constructive logic is, it does have its limitations:
    There are many statements that can easily be proven in classical
    logic but that have much more complicated constructive proofs, and
    there are some that are known to have no constructive proof at
    all!  Fortunately, like functional extensionality, the excluded
    middle is known to be compatible with Coq's logic, allowing us to
    add it safely as an axiom.  However, we will not need to do so in
    this book: the results that we cover can be developed entirely
    within constructive logic at negligible extra cost.

    It takes some practice to understand which proof techniques must
    be avoided in constructive reasoning, but arguments by
    contradiction, in particular, are infamous for leading to
    non-constructive proofs.  Here's a typical example: suppose that
    we want to show that there exists [x] with some property [P],
    i.e., such that [P x].  We start by assuming that our conclusion
    is false; that is, [~ exists x, P x]. From this premise, it is not
    hard to derive [forall x, ~ P x].  If we manage to show that this
    intermediate fact results in a contradiction, we arrive at an
    existence proof without ever exhibiting a value of [x] for which
    [P x] holds!

    The technical flaw here, from a constructive standpoint, is that
    we claimed to prove [exists x, P x] using a proof of [~ ~ exists
    x, P x]. However, allowing ourselves to remove double negations
    from arbitrary statements is equivalent to assuming the excluded
    middle, as shown in one of the exercises below.  Thus, this line
    of reasoning cannot be encoded in Coq without assuming additional
    axioms. *)

(** **** Exercise: 3 stars (excluded_middle_irrefutable)  *)
(** The consistency of Coq with the general excluded middle axiom
    requires complicated reasoning that cannot be carried out within
    Coq itself.  However, the following theorem implies that it is
    always safe to assume a decidability axiom (i.e., an instance of
    excluded middle) for any _particular_ Prop [P].  Why? Because we
    cannot prove the negation of such an axiom; if we could, we would
    have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)

Theorem excluded_middle_irrefutable:  forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** It is a theorem of classical logic that the following two
    assertions are equivalent:

    ~ (exists x, ~ P x)
    forall x, P x

    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle. *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (classical_axioms)  *)
(** For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all five propositions (these four plus
    [excluded_middle]) are equivalent. *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.
  
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(* FILL IN HERE *)
(** [] *)

(** $Date: 2015-08-11 12:03:04 -0400 (Tue, 11 Aug 2015) $ *)











(* Here is an example of a provable proposition: *)
(** 証明可能な命題の例です。*)


(* Here is an example of an unprovable proposition: *)
(** 次は、証明不可能な命題の例です。*)


(* Recall that [Check] asks Coq to tell us the type of the indicated 
  expression. *)
(** [Check]は、表示された表現の型をCoqに問い合わせて、我々に教えてくれるんでしたね。*)
(* ########################################################### *)
(* * Proofs and Evidence *)
(** 証明と根拠 *)
(* In Coq, propositions have the same status as other types, such as
    [nat].  Just as the natural numbers [0], [1], [2], etc. inhabit
    the type [nat], a Coq proposition [P] is inhabited by its
    _proofs_.  We will refer to such inhabitants as _proof term_ or
    _proof object_ or _evidence_ for the truth of [P]. 

    In Coq, when we state and then prove a lemma such as:

Lemma silly : 0 * 3 = 0.  
Proof. reflexivity. Qed.

    the tactics we use within the [Proof]...[Qed] keywords tell Coq
    how to construct a proof term that inhabits the proposition.  In
    this case, the proposition [0 * 3 = 0] is justified by a
    combination of the _definition_ of [mult], which says that [0 * 3]
    _simplifies_ to just [0], and the _reflexive_ principle of
    equality, which says that [0 = 0].
*)

(** Coqにおいて、命題は他の型と同じ状態を持ちます。例えば、[nat]のように。自然数の[0],[1],[2]などが[nat]型の世界に属するのと同じように、Coqの命題[P]は、その_証明_の世界に属しています。
[P]が真であるための_証明の項_、_証明オブジェクト_や_根拠_のような住人について見ていくことにしましょう。
  
Coqにおいて、補題を証明するときには、以下のように書きます。

Lemma silly : 0 * 3 = 0.
Proof. reflexivity. Qed.

   我々が[Proof]...[Qed]キーワードの間に使用するタクティックはCoqに命題が連続する証明をどのように構築するかを伝えます。   この場合、命題[0 * 3 = 0]は [0 * 3]は_簡約_の結果0であるとする[mult]の定義と[0 = 0]であるとする_反射的_な同値性の原理の合わせ技で正当化されます。
*)

(** *** *)

Lemma silly : 0 * 3 = 0.
Proof. reflexivity. Qed.

(* We can see which proof term Coq constructs for a given Lemma by
using the [Print] directive: *)
(** [Print]ディレクティブを使用すると、LemmaとしてCoqが構築した証明term?を見ることが出来ます。
*)
Print silly.
(* ===> silly = eq_refl : 0 * 3 = 0 *)

(* Here, the [eq_refl] proof term witnesses the equality. (More on equality later!)*)
(** この[eq_refl」は同値性を証明する証明termです。 (同値性について詳しくは後述!)*)

(* ** Implications _are_ functions *)
(** ** 含意_は_関数なのです *)
(* Just as we can implement natural number multiplication as a
function:
[
mult : nat -> nat -> nat 
]

The _proof term_ for an implication [P -> Q] is a _function_ that
takes evidence for [P] as input and produces evidence for [Q] as its output.
*)     
(** ここで、自然数のかけ算を関数として実装してみましょう 
[
mult : nat -> nat -> nat
]
[P -> Q]という含意を表す_項_は、[P]のための根拠を入力としてとり、出力としてQの根拠を生成する_関数_なのです。
*)

Lemma silly_implication : (1 + 1) = 2  ->  0 * 3 = 0.
Proof. intros H. reflexivity. Qed.

(* We can see that the proof term for the above lemma is indeed a
function: *)
(** 上記補題の proof termが確かに関数であることが分かります: *)

Print silly_implication.
(* ===> silly_implication = fun _ : 1 + 1 = 2 => eq_refl
     : 1 + 1 = 2 -> 0 * 3 = 0 *)

(* ** Defining Propositions *)
(** 命題を定義するということ *)

(* Just as we can create user-defined inductive types (like the
    lists, binary representations of natural numbers, etc., that we
    seen before), we can also create _user-defined_ propositions.

    Question: How do you define the meaning of a proposition?  
*)
(**
ユーザ定義の再帰的な型(これまでに見てきたlistや自然数のバイナリ表記のような)を作ることが出来るように、
_ユーザ定義の_命題もまた作ることが出来ます。

問題：命題の意味はどうやって定義するのでしょうか？
*)

(** *** *)

(* The meaning of a proposition is given by _rules_ and _definitions_
    that say how to construct _evidence_ for the truth of the
    proposition from other evidence.

    - Typically, rules are defined _inductively_, just like any other
      datatype.

    - Sometimes a proposition is declared to be true without
      substantiating evidence.  Such propositions are called _axioms_.  


    In this, and subsequence chapters, we'll see more about how these
    proof terms work in more detail.
*)

(** 命題の意味は命題の正しさのための根拠を他の根拠からどのように構築するかを述べる_規則_と_定義_によって与えられます。

  - 典型的に、規則は他のデータ型と同じように、_帰納的に_定義されます。

  - 時々、命題は、 具体的な根拠なしに宣言されます。そのような命題は、_公理_と呼ばれます。
  
  これからの章において、これらの証明termが細かい点においてどのように働くかを見ていくことにしましょう
  *)
(* ########################################################### *)
(* * Conjunction *)
(** * 論理積、連言（Conjunction、AND） *)

(*  The logical conjunction of propositions [P] and [Q] can be
    represented using an [Inductive] definition with one
    constructor. *)
(** 命題 [P] と [Q] の論理積（ [logical conjunction] ）は、コンストラクタを一つしか持たない [Inductive] を使った定義で表せます。 *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

(* The intuition behind this definition is simple: to
    construct evidence for [and P Q], we must provide evidence
    for [P] and evidence for [Q].  More precisely:

    - [conj p q] can be taken as evidence for [and P Q] if [p]
      is evidence for [P] and [q] is evidence for [Q]; and

    - this is the _only_ way to give evidence for [and P Q] --
      that is, if someone gives us evidence for [and P Q], we
      know it must have the form [conj p q], where [p] is
      evidence for [P] and [q] is evidence for [Q]. 

   Since we'll be using conjunction a lot, let's introduce a more
   familiar-looking infix notation for it. *)

(** この定義の内容を直感的に理解するのに、そうややこしく考える必要はありません。[and P Q] に根拠を与えるには、[P] の根拠と [Q] の根拠が必要だということです。もっと精確に言えば、

    - もし [p] が [P] の根拠で、[q] が [Q] の根拠であるなら、[conj p q] を [and P Q] の根拠とすることができる。

    - これは [and P Q] に根拠を与える唯一の方法であること、即ち、もし [and P Q] の根拠が与えられたならば、その根拠が [conj p q] の形をしており、さらに [p] が [P] の根拠であることと[q] が [Q] の根拠であることがわかるということです。

   今後論理積をよく使うことになるので、もっと馴染みのある、中置記法を導入することにしましょう。 *)

Notation "P /\ Q" := (and P Q) : type_scope.

(*  (The [type_scope] annotation tells Coq that this notation
    will be appearing in propositions, not values.) *)
(** （[type_scope] という注釈は、この記法が値にではなく、命題に現れるものであることを、Coqに伝えています。） *)

(* Consider the "type" of the constructor [conj]: *)
(** コンストラクタ [conj] の型はどのようなものか考えてみましょう。 *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(* Notice that it takes 4 inputs -- namely the propositions [P]
    and [Q] and evidence for [P] and [Q] -- and returns as output the
    evidence of [P /\ Q]. *)
(** conjが四つの引数（ [P] 、[Q] という命題と、[P] 、[Q] の根拠）をとることに注目して下さい。 *)

(* Besides the elegance of building everything up from a tiny
    foundation, what's nice about defining conjunction this way is
    that we can prove statements involving conjunction using the
    tactics that we already know.  For example, if the goal statement
    is a conjuction, we can prove it by applying the single
    constructor [conj], which (as can be seen from the type of [conj])
    solves the current goal and leaves the two parts of the
    conjunction as subgoals to be proved separately. *)
(**
    基本的なことから色々なことを組み立てていくエレガントさはさておき、
    このような方法でconjunctionを定義することの利点は、これを含む
    文を、既に知っているタクティックで証明できることです。
    例えば、もしゴールが論理積を含んでいる場合、このたった一つの
    コンストラクタ[conj]を適用するだけで証明できます。
    それは、[conj]の型を見ても分かるように現在のゴールを解決してから
    conjunctionの二つの部分を別々に証明するべきサブゴールにします。
 *)


Theorem and_example : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  apply conj.
  Case "left". reflexivity.
  Case "right". reflexivity.  Qed.


(* Just for convenience, we can use the tactic [split] as a shorthand for
    [apply conj]. *)
(** [apply conj] とするかわりに [split] タクティックでも同じことができます。便利ですね。 *)

Theorem and_example' : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  split.
    Case "left". reflexivity.
    Case "right". reflexivity.  Qed.

(* ** "Eliminating" conjunctions *) 
(** ** 論理積を"取り除く"ということ *)
(* Conversely, the [inversion] tactic can be used to take a
    conjunction hypothesis in the context, calculate what evidence
    must have been used to build it, and add variables representing
    this evidence to the proof context. *)
(** 逆に、[inversion] タクティックを、コンテキストにある論理積の形をした仮定に使うことで、それの構築に使われた根拠を取り出し、コンテキストに加えることができます。 *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  apply HP.  Qed.

(** **** 練習問題: ★, optional (proj2) *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HP HQ]. 
  split.  
    Case "left". apply HQ. 
    Case "right". apply HP.  Qed.
  

(** **** 練習問題: ★★ (and_assoc) *)
(* In the following proof, notice how the _nested pattern_ in the
    [inversion] breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP: P], [HQ : Q], and [HR : R].  Finish the proof from there: *)
(** 次の証明では、[inversion]が、入れ子構造になった命題[H : P /\ (Q /\ R)]をどのように[HP: P], [HQ : Q], [HR : R] に分解するか、という点に注意しながら証明を完成させなさい。*)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(* ** Iff *)
(** ** Iff （両含意）*)

(* The handy "if and only if" connective is just the conjunction of
    two implications. *)
(** この、"if and only if（～である時、その時に限り）" で表される「両含意」という論理は馴染みのあるもので、次の二つの「ならば（含意）」をandでつないだものです。*)
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. 
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

(** **** 練習問題: ★, optional (iff_properties) *)
(*  Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)
(** 上の、 [<->] が対称であることを示す証明 ([iff_sym]) を使い、それが反射的であること、推移的であることを証明しなさい。*)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *) Admitted.

(*  Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)
(** ヒント: もしコンテキストに iff を含む仮定があれば、[inversion] を使ってそれを二つの含意の式に分割することができます。(なぜそうできるのか考えてみましょう。) *)
(** [] *)

(*  Some of Coq's tactics treat [iff] statements specially, thus
    avoiding the need for some low-level manipulation when reasoning
    with them.  In particular, [rewrite] can be used with [iff]
    statements, not just equalities. *)
(** Coqのいくつかのタクティックは、証明の際に低レベルな操作を避けるため[iff] を特別扱いします。 特に [rewrite] を [iff] に使うと、単なる等式以上のものとして扱ってくれます。 *)

(* ############################################################ *)
(* * Disjunction (Logical "or") *)
(** * 論理和、選言（Disjunction、OR） *)

(*  ** Implementing disjunction *)
(** ** 論理和の実装 *)
(*  Disjunction ("logical or") can also be defined as an
    inductive proposition. *)
(** 論理和（Disjunction、OR）も、帰納的な命題として定義できます。 *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

(** Consider the "type" of the constructor [or_introl]: *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(*  It takes 3 inputs, namely the propositions [P], [Q] and
    evidence of [P], and returns, as output, the evidence of [P \/ Q].
    Next, look at the type of [or_intror]: *)
(** このコンストラクタは三つの入力（ [P]、[Q] と名付けられた命題に加え、[P] の根拠）を引数にとり、[P /\ Q] の根拠を返します。次に、[or_intror] の型を見てみましょう。 *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(*  It is like [or_introl] but it requires evidence of [Q]
    instead of evidence of [P]. *)
(** ほとんど [or_introl] と同じように見えますが、[P] ではなく [Q] の根拠が要求されています。*)

(* Intuitively, there are two ways of giving evidence for [P \/ Q]:

    - give evidence for [P] (and say that it is [P] you are giving
      evidence for -- this is the function of the [or_introl]
      constructor), or

    - give evidence for [Q], tagged with the [or_intror]
      constructor. *)
(** 直観的には、命題 [P \/ Q] に根拠を与える方法は二つあることがわかります。

    - [P] の根拠を与える。（そしてそれが [P] の根拠であることを伝える。これがコンストラクタ [or_introl] の機能です）か、

    - [Q] の根拠をコンストラクタ [or_intror] に与える。 *)

(*  Since [P \/ Q] has two constructors, doing [inversion] on a
    hypothesis of type [P \/ Q] yields two subgoals. *)
(**  [P \/ Q] は二つのコンストラクタを持っているので、 [P \/ Q] の形の仮定に[inversion] を適用すると二つのサブゴールが生成されます。*)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

(** From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)
(** 次のように、[apply or_introl] 、 [apply or_intror] の代わりに [left] 、[right] という短縮版のタクティックを使うこともできます。*)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ.  Qed.





Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. inversion H as [HP | [HQ HR]]. 
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(** **** 練習問題: ★★ (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★, optional (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################### *)
(* ** Relating [/\] and [\/] with [andb] and [orb] (advanced) *)
(** ** [/\] 、 [\/] の[andb] 、[orb] への関連付け *)

(*  We've already seen several places where analogous structures
    can be found in Coq's computational ([Type]) and logical ([Prop])
    worlds.  Here is one more: the boolean operators [andb] and [orb]
    are clearly analogs of the logical connectives [/\] and [\/].
    This analogy can be made more precise by the following theorems,
    which show how to translate knowledge about [andb] and [orb]'s
    behaviors on certain inputs into propositional facts about those
    inputs. *)
(** 我々はすでに、Coqの計算における型([Type]) と論理の命題 ([Prop]) との類似性について見てきました。ここではもう一つ、bool 型を扱う [andb] と[orb] が、[/\] と [\/] とのつながりともいうべきある種の類似性を持っていることに触れましょう。この類似性は、次の定理を見ればもっとはっきりします。これは、[andb] や [orb] が、ある入力に対する振る舞いを、その入力に対する命題にどのように変換するかを示したものです。*)
Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

(** **** 練習問題: ★★, optional (bool_prop) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  (* FILL IN HERE *) Admitted.

(** **** 練習問題: ★★, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** 練習問題: ★★, optional (orb_false_elim)  *)
Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ################################################### *)
(*  * Falsehood *)
(** * 偽であるということ *)
(* Logical falsehood can be represented in Coq as an inductively
    defined proposition with no constructors. *)
(** 論理学でいうところの「偽」は、Coqでは「帰納的に定義されてはいるがコンストラクタを一つも持たない命題」として定義されています。*)

Inductive False : Prop := . 

(*  Intuition: [False] is a proposition for which there is no way
    to give evidence. *)
(** 直観的な理解: [False] は、根拠を示す方法を一つも持たない命題 *)


(*  Since [False] has no constructors, inverting an assumption
    of type [False] always yields zero subgoals, allowing us to
    immediately prove any goal. *)
(** [False] にはコンストラクタがないので、[False] の意味するところのものを反転（invert）してもサブゴールが生成されません。このことはつまり、「偽」からはどんなゴールも証明できる、ということです。*)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(* How does this work? The [inversion] tactic breaks [contra] into
    each of its possible cases, and yields a subgoal for each case.
    As [contra] is evidence for [False], it has _no_ possible cases,
    hence, there are no possible subgoals and the proof is done. *)
(** これはどういうことでしょうか？ [inversion] タクティックは仮定 [contra] をその取りうるケースに分解し、それぞれにサブゴールを生成します。ここで[contra] が [False] の根拠となっているため、そこから取りうるケースは存在しません。このため、証明に値するサブゴールがなくなり、そこで証明が終わってしまうのです。*)

(** *** *)
(*  Conversely, the only way to prove [False] is if there is already
    something nonsensical or contradictory in the context: *)
(** 逆に、[False] を証明する唯一の方法は、コンテキストに何か矛盾がないかを探すことです。*)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(*  Actually, since the proof of [False_implies_nonsense]
    doesn't actually have anything to do with the specific nonsensical
    thing being proved; it can easily be generalized to work for an
    arbitrary [P]: *)
(** 実際、 [False_implies_nonsense] の証明は、特定の意味を持つ証明すべきことを何も持っていないので、任意の [P] に対して簡単に一般化できます。 *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra.  Qed.

(*  The Latin _ex falso quodlibet_ means, literally, "from
    falsehood follows whatever you please."  This theorem is also
    known as the _principle of explosion_. *)
(** ラテン語の 「_ex falso quodlibet_ 」は、文字通り「偽からはあなたの望むものすべてがもたらされる」というような意味です。この定理は、「 _principle of explosion_ 」としても知られています。 *)

(* #################################################### *)
(*  ** Truth *)
(** ** 真であるということ *)

(*  Since we have defined falsehood in Coq, one might wonder whether
    it is possible to define truth in the same way.  We can. *)
(** Coqで「偽」を定義することができたので、同じ考え方で「真」を定義することができるか、ということが次の関心事になります。もちろん、その答えは「Yes」です。 *)

(** **** 練習問題: ★★, advanced (True) *)
(*  Define [True] as another inductively defined proposition.  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.) *)
(** [True] を、帰納的な命題として定義しなさい。（直観的には [True] はただ当たり前のように根拠を示される命題であるべきです。） *)
(* FILL IN HERE *)
(** [] *)

(* However, unlike [False], which we'll use extensively, [True] is
    used fairly rarely. By itself, it is trivial (and therefore
    uninteresting) to prove as a goal, and it carries no useful
    information as a hypothesis. But it can be useful when defining
    complex [Prop]s using conditionals, or as a parameter to 
    higher-order [Prop]s. *)
(** しかしながら、[False] とは違い、広い意味で解釈すると [True] には理論的な意味で奇妙なところがあります。ゴールの証明に使うには当たり前すぎ（それゆえつまらない）、仮定として有意義な情報を与えてくれないのです。しかし条件文や、高階の[Prop]をパラメータで含む複雑な[Prop]を定義するときには役に立つこともあります) *)

(* #################################################### *)
(* * Negation *)
(** * 否定 *)

(** The logical complement of a proposition [P] is written [not
    P] or, for shorthand, [~P]: *)
(** 命題 [P] の論理的な補集合というべきものは、 [not P] もしくは短縮形として[~P] と表されます。 *)

Definition not (P:Prop) := P -> False.

(** The intuition is that, if [P] is not true, then anything at
    all (even [False]) follows from assuming [P]. *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(*  It takes a little practice to get used to working with
    negation in Coq.  Even though you can see perfectly well why
    something is true, it can be a little hard at first to get things
    into the right configuration so that Coq can see it!  Here are
    proofs of a few familiar facts about negation to get you warmed
    up. *)
(** Coqで否定を扱えるようになるにはある程度慣れが必要です。たとえ何かがどう見ても真に思える場合でも、そのことをCoqに納得させるのは最初のうちはなかなか大変です。ウォームアップのつもりで、否定のに関する馴染みのある定理を取り上げてみましょう。 *)

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** 練習問題: ★★, advanced (double_neg_inf) *)
(* Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
*)
(** [double_neg] の非形式的な証明を書きなさい。:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
(* FILL IN HERE *)
   []
*)

(** **** 練習問題: ★★ (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★ (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★, advanced (informal_not_PNP) *)
(*  Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)
(** 命題 [forall P : Prop, ~(P /\ ~P)] の形式的でない証明を（英語で）書きなさい。 *)
(* FILL IN HERE *)
(** [] *)

(* Constructive logic *)
(** 構成的論理 ? Constructive logic *)
(*  Note that some theorems that are true in classical logic are _not_
    provable in Coq's (constructive) logic.  E.g., let's look at how
    this proof gets stuck... *)
(** このうちいくつかは、古典論理ではtrueと判断できるにもかかわらず、Coqの(構成上の)論理では証明できないものがあるので注意が必要です。例えば、この証明がどのように詰まるかを見てみましょう。 *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H. 
  (* どうなっているのでしょうか？ [P] の証明に必要な根拠をどうしても編み出すことができません。 *)
  (* But now what? There is no way to "invent" evidence for [~P] 
     from evidence for [P]. *) 
  Abort.

(** **** 練習問題: ★★★★★, advanced, optional (classical_axioms) *)
(*  For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)
(**  さらなる挑戦を求める人のために、 Coq'Art book (p. 123) から一つ練習問題を
    取り上げてみます。次の五つの文は、よく「古典論理の特性」と考えられている
    もの（Coqにビルトインされている構成的論理の対極にあるもの）です。
    これらをCoqで証明することはできませんが、古典論理を使うことが必要なら、
    矛盾なく「証明されていない公理」として道具に加えることができます。
    これら五つの命題が等価であることを証明しなさい。 *)


Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 

(* FILL IN HERE *)
(** [] *)

(** **** **** 練習問題: ★★★ (excluded_middle_irrefutable) *)
(* This theorem implies that it is always safe to add a decidability
axiom (i.e. an instance of excluded middle) for any _particular_ Prop [P].
Why? Because we cannot prove the negation of such an axiom; if we could,
we would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)
(** この定理は、決定可能な公理(たとえば、排中律のような)を任意の_部分_命題[P]として、いつでも安全につけくわえることが出来ることを意味しています。 
どうしてそんなことが可能であるかと言えば、我々はそのような公理の否定命題を証明出来ないためです; もしそれが可能であるとすると、[~ (P \/ ~P)] と [~ ~ (P \/ ~P)]の両方を持つことが出来てしまいますが、これは矛盾です。*)
Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).  
Proof.
  (* FILL IN HERE *) Admitted.


(* ########################################################## *)
(* ** Inequality *)
(** ** 不等であるということ*)

(*  Saying [x <> y] is just the same as saying [~(x = y)]. *)
(** [x <> y] というのは、[~(x = y)] と同じことです。 *)

Notation "x <> y" := (~ (x = y)) : type_scope.

(*  Since inequality involves a negation, it again requires
    a little practice to be able to work with it fluently.  Here
    is one very useful trick.  If you are trying to prove a goal
    that is nonsensical (e.g., the goal state is [false = true]),
    apply the lemma [ex_falso_quodlibet] to change the goal to
    [False].  This makes it easier to use assumptions of the form
    [~P] that are available in the context -- in particular,
    assumptions of the form [x<>y]. *)
(** 不等性は、その中に「否定」を含んでいるため、やはりその扱いには
    ある程度の慣れが必要です。ここで一つ有用なトリックをお見せしましょう。
    もし、証明すべきゴールがあり得ない式（例えば[false = true]というような文）
    であった場合は、[ex_falso_quodlibet] という補題をapplyで適用すると、ゴールを
    [False]にすることができます。このことを覚えておけば、コンテキストの中の [~P]
    という形の仮定を使うことがとても簡単になります。特に、[x<>y] という形の仮定の
    場合はに有用です。 *)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.


(** *** *)

(** *** *)

(** *** *)

(** *** *)

(** *** *)

(** **** 練習問題: ★★ (false_beq_nat) *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, optional (beq_nat_false) *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

