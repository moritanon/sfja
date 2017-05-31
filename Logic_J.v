(* * Logic: Logic in Coq *)
(** * Logic_J: Coqにおける論理 *)

Require Export Tactics.

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

(*  Note that _all_ syntactically well-formed propositions have type
    [Prop] in Coq, regardless of whether they are true or not.

    Simply _being_ a proposition is one thing; being _provable_ is
    something else! *)
(** Coqでは、文法的に正しい形の_全ての_命題は、[Prop]という型を持っており、それが真であるかどうかは関係ありません。
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
Definition plus_fact : Prop := 2 + 2 = 4.
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
    proposition. *)
(** _パラメータつきの_命題というものを書くことも出来ます。--すなわち、何か型を物引数を取ったり、命題を返す関数です。*)

(*  For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)
(** 例えば、次の関数は、自然数を引数にとり、その自然数が3と等しいことを主張する命題を返却します: *)
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(*  In Coq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. *)
(** Coqにおいて、命題を返す関数は、それら引数のプロパティを定義するものであると言われます。
よく知られた概念である単射関数を定義する(多相的な)属性の例を挙げてみましょう。*)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

(*  The equality operator [=] is also a function that returns a
    [Prop].

    The expression [n = m] is syntactic sugar for [eq n m], defined
    using Coq's [Notation] mechanism. Because [eq] can be used with
    elements of any type, it is also polymorphic: *)
(** これまでにも使用してきた、等しさを表す演算子[=]も[Prop]を返す関数に過ぎません。[n = m]という式は、[eq n m]の糖衣構文であり、
Coqの「Notation]メカニズムを使用して定義されています。[eq]はあらゆる型の要素と使用出来るのは、多相的でもあるからです。*)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(** (Notice that we wrote [@eq] instead of [eq]: The type
    argument [A] to [eq] is declared as implicit, so we need to turn
    off implicit arguments to see the full type of [eq].) *)
(** [eq]の代わりに[@eq]と書いたことに気をつけましょう: [eq]に与える型変数[A]は暗黙的に宣言されていますので、
[eq]の完全な型を見るために、暗黙の宣言から切り替える必要があります。*)

(* ################################################################# *)
(*  * Logical Connectives *)
(** * 論理結合子 *)

(* ================================================================= *)
(*  ** Conjunction *)
(** * 論理積 *)

(*  The _conjunction_ (or _logical and_) of propositions [A] and [B]
    is written [A /\ B], representing the claim that both [A] and [B]
    are true. *)
(** 命題[A]と[B]からなる_論理積_(又は_論理and_) は [A /\ B]と書きます。[A]と[B]が共に真であることを主張している。ということを意味します。 *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(*  To prove a conjunction, use the [split] tactic.  It will generate
    two subgoals, one for each part of the statement: *)
(** 論理積を証明するために、[split]タクティックを使います。その効果は二つのサブゴールを生成して、それぞれの部分に割り当てます。*)
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(*  For any propositions [A] and [B], if we assume that [A] is true
    and we assume that [B] is true, we can conclude that [A /\ B] is
    also true. *)
(*  任意の二つの命題[A]と[B]において、[A]と[B]が真であると仮定したとすると、
    [A /\ B]も真であると結論着けることが出来ます *)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(*  Since applying a theorem with hypotheses to some goal has the
    effect of generating as many subgoals as there are hypotheses for
    that theorem, we can apply [and_intro] to achieve the same effect
    as [split]. *)
(** 仮説を伴う[and_intro]定理をゴールに適用することによって、仮説のぶんだけサブゴールが
生成される、[split]と同じ効果を得ることが出来ます。*)

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
    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
    something else -- we employ the [destruct] tactic.

    If the proof context contains a hypothesis [H] of the form
    [A /\ B], writing [destruct H as [HA HB]] will remove [H] from the
    context and add two new hypotheses: [HA], stating that [A] is
    true, and [HB], stating that [B] is true.  *)
(**  論理積の文を証明するのはこれまでとします。別の方向 -- 論理積を仮定として使って何かを証明したり---
に行くために、[destruct]タクティックを使うことにします。*)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(*  As usual, we can also destruct [H] right when we introduce it,
    instead of introducing and then destructing it: *)
(** 通常、[H]を導入するときに、[H]を正しくデストラクトすることが出来ます。*)

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

(*  For this theorem, both formulations are fine.  But it's important
    to understand how to work with conjunctive hypotheses because
    conjunctions often arise from intermediate steps in proofs,
    especially in bigger developments.  Here's a simple example: *)
(** この定理において、二つの公式の正しさは明らかです。しかし、証明の途中で生成される論理積を明示的に分解する必要がしばしば出てきます。
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

(*  Another common situation with conjunctions is that we know
    [A /\ B] but in some context we need just [A] (or just [B]).
    The following lemmas are useful in such cases: *)
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

(* ================================================================= *)
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
    the hypothesis that is generated in each subgoal. *)
(** この例の中で、論理和[A \/ B]のケース分析を行なう時、二つの証明の責任、結論が異なる仮定から保持されていること、
-- 最初のサブゴール中の[A]と二つめのサブゴールの[B] -- を満たす必要があります。 ([Hn| Hm])というケース分析パターンは
それぞれのサブゴールで生成される仮説に名前をつける必要があることに注意してください。*)

(*  Conversely, to show that a disjunction holds, we need to show that
    one of its sides does. This is done via two tactics, [left] and
    [right].  As their names imply, the first one requires
    proving the left side of the disjunction, while the second
    requires proving its right side.  Here is a trivial use... *)
(** 反対に、論理和がゴールにある場合、論理和の一方が成り立つことを示す必要があります。これは二つのタクティックを経由することで達成されます。
[left]と[right]です。その名前が示すように、始めの方は、論理和の左側の証明を必要とし、もう一方は、右側を必要とします。
簡単な使い方が以下になります… *)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(*  ... and a slightly more interesting example requiring both [left]
    and [right]: *)
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
(** これまでに、我々の関心のほとんどは、あることが、_true_であることを証明することにありました。
-- 加法は可換であるとか、リストの足し算は結合的であるとかです。もちろん我々の関心は,ある命題が真でない、といった_否定的_なものにもあります。
Coqにおいて、そのような否定文は否定の演算子[~]で表すことが出来ます。

否定がどのように働くのか見るために、Tacticsの章から爆発原理の議論を思い出しましょう。爆発原理の主張するところは、
矛盾が仮定された場合、どんな命題も導出可能になってしまうということです。直感的に言えば、[~P]("not [P]")は、[forall Q, P -> Q]と定義されます。
Coqちょっと違った方式をとっており、[~P]を[P -> False]として定義しています。すなわち、[False]は特別に矛盾した命題として
標準ライブラリに定義されています。*)

Module MyNot. 
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.
(* ===> Prop -> Prop *)
End MyNot.
(*  Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can [destruct] it to complete any goal: *)
(** [False]は矛盾命題なので、爆発原理もまた適用することが出来ます。もし、[False]がコンテキストに現われたら[destruct]を使用して、どんなゴールも終了させることが出来ます。*)
Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.
(*  The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)
(** ラテン語の _ex falso quodlibet_ の意味は、文字通り、「偽からは望むもの全てが得られる」というものです。これは爆発原理につけられたもう一つの名前です。*)
(*  **** Exercise: 2 stars, optional (not_implies_our_not)  *)
(** **** 練習問題: ★★, optional (not_implies_our_not) *)
(*  Show that Coq's definition of negation implies the intuitive one
    mentioned above: *)
(** Coqの否定の定義が上記で触れた直感的な理解を含意することを示します。*)
Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(*  This is how we use [not] to state that [0] and [1] are different
    elements of [nat]: *)
(** これは、[0]と[1]が[nat]の要素として異なっているということを述べるために[not]を使う方法です。*)
Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.
(*  Such inequality statements are frequent enough to warrant a
    special notation, [x <> y]: *)
(** このような等しいことの否定を示す文は [x <> y]という記法を使うのにぴったりです。*)
Check (0 <> 1).
(* ===> Prop *)
Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.
(*  It takes a little practice to get used to working with negation in
    Coq.  Even though you can see perfectly well why a statement
    involving negation is true, it can be a little tricky at first to
    get things into the right configuration so that Coq can understand
    it!  Here are proofs of a few familiar facts to get you warmed
    up. *)
(** Coqで否定を扱えるようになるにはある程度慣れが必要です。たとえ否定を含む文がどう見ても真に思える場合でも、そのことをCoqに納得させるのは最初のうちはなかなかトリッキーになりがちです。ウォームアップのつもりで、否定のに関する馴染みのある定理を取り上げてみましょう。 *)
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
(** Write an informal proof of [double_neg]: *)
(** [double_neg] の非形式的な証明を書きなさい。:
   _Theorem_: [P] implies [~~P], for any proposition [P].
   _Proof_:
(* FILL IN HERE *)
   []
*)
(*  **** Exercise: 2 stars, recommended (contrapositive)  *)
(** **** 練習問題: ★★, recommended (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(*  **** Exercise: 1 star (not_both_true_and_false)  *)
(** **** 練習問題: ★ (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(*  **** Exercise: 1 star, advanced (informal_not_PNP)  *)
(** **** 練習問題: ★, advanced (informal_not_PNP) *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)
(* FILL IN HERE *)
(** [] *)
(*  Similarly, since inequality involves a negation, it requires a
    little practice to be able to work with it fluently.  Here is one
    useful trick.  If you are trying to prove a goal that is
    nonsensical (e.g., the goal state is [false = true]), apply
    [ex_falso_quodlibet] to change the goal to [False].  This makes it
    easier to use assumptions of the form [~P] that may be available
    in the context -- in particular, assumptions of the form
    [x<>y]. *)
(** 同様に、非同値式は否定を含んでいるため、慣れるためにやっぱり練習が必要です。ここに役立つトリックを用意しました。もし無意味なゴール([true = false]みたいな)を証明しなければならくなったとき
[ex_falso_quodlibet]を適用することで、ゴールを[False]に変更出来ます。このことは、コンテキスト中にある[~P]という形式の仮定を使うことをより容易にしてくれます。とくに、[x<>y]という形をしている仮定のときには。*)
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
(*  Since reasoning with [ex_falso_quodlibet] is quite common, Coq
    provides a built-in tactic, [exfalso], for applying it. *)
(** [ex_falso_quodlibet]を使った推論はとてもよくあるので、Coqにビルトインされたタクティック[exfalso]が用意されていて、適用することが出来ます。*)
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
(*  Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    predefined constant [I : True]: *)
(** [False]に加えて、Coqの標準ライブラリは[True]も、単に自明に真な命題として定義しています。それを証明するには、予め定義された定数 [I :True]を使います: *)
Lemma True_is_true : True.
Proof. apply I. Qed.
(*  Unlike [False], which is used extensively, [True] is used quite
    rarely, since it is trivial (and therefore uninteresting) to prove
    as a goal, and it carries no useful information as a hypothesis.
    But it can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s.  We will
    see some examples such uses of [True] later on. *)
(** [False] とは違い、広い意味で解釈すると [True] には理論的な意味で奇妙なところがあります。ゴールの証明に使うには当たり前すぎ（それゆえつまらない）、仮定として有意義な情報を与えてくれないのです。しかし条件文や、高階の[Prop]をパラメータで含む複雑な[Prop]を定義するときには役に立つこともあります) *)
(*  ** Logical Equivalence *)
(** ** 論理的同値 *)
(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is just the conjunction of
    two implications. *)
(** この、"if and only if（～である時、その時に限り）" で表される「両含意」という論理は馴染みのあるもので、次の二つの「ならば（含意）」をandでつないだものです。*)
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
(*  **** Exercise: 1 star, optional (iff_properties)  *)
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
(** [] *)
(*  **** Exercise: 3 stars (or_distributes_over_and)  *)
(** **** 練習問題: ★★★, optional (or_distributes_over_and) *)
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
(** Coqのいくつかのタクティックは、証明の際に低レベルな操作を避けるため[iff] を特別扱いします。 特に [rewrite] を [iff] に使うと、単なる等式以上のものとして扱ってくれます。
この振舞を有効にするために、特別なCoqのライブラリをインポートする必要があります。そのライブラリを使うと等式に加えて他の公式の書き換えも出来るようになります。*)
Require Import Coq.Setoids.Setoid.
(** Here is a simple example demonstrating how these tactics work with
    [iff].  First, let's prove a couple of basic iff equivalences: *)
(** 以下は[iff]がどのように動作するかを示す簡単な例です。まず、基本的なiffの同値性を使う証明を二つ行ないましょう *)
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
(*  We can now use these facts with [rewrite] and [reflexivity] to
    give smooth proofs of statements involving equivalences.  Here is
    a ternary version of the previous [mult_0] result: *)
(** これで、[rewrite]と[reflexivity]を使うことが出来るようになりました。等式を含んだ証明をスムーズに行えます。ここで[mult_0]の三変数バージョンを見てみましょう。*)
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
(** [apply]タクティックも[<->]を使うことが出来ます。引数に論理的同値が与えられたら、applyは同値性のどちらを使うべきか推測して使ってくれます。*)
Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.
(* ############################################################ *)
(*  ** Existential Quantification *)
(** * 存在量化子 *)
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
(** もう一つの重要な論理結合子は、存在量化子（ _existential quantification_ ）です。ある[T]型の[x]があって、[x]はプロパティ[P]を満たす、といった意味で、 [exists x : T, P]と書きます。
[forall]と同じように、型注釈[: T]は、Coqが文脈から推論出来るならば、省略可能です。
[exists x, P]という形の文を証明するために、[P]を満たす特定の値[x](、存在の証拠になります)を示す必要があります。 これは二つのステップで行なわれます。第一に、明示的にCoqに証拠[t]を[exists t]タクティックを呼び出すことで示します。
それから、全ての[x]を[t]に置き換えたあとにそれらが全て、[P]を満すことを証明します。次は例です。*)
Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.
(* Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)
(** 逆に、[exists x, P]という存在仮定がコンテキストにある場合は、それをdestructして証拠[x]と、[P]を満す[x]という仮定を得ることが出来ます。*)
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.  Qed.
(*  **** Exercise: 1 star (dist_not_exists)  *)
(** **** 練習問題: ★ (dist_not_exists) *)
(*  Prove that "[P] holds for all [x]" implies "there is no [x] for
(** "全ての [x] について[P] が成り立つ" ならば " [P] を満たさない [x] は存在しない" ということを証明しなさい。 *)
    which [P] does not hold." *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(*  **** Exercise: 2 stars (dist_exists_or)  *)
(** **** 練習問題: ★★ (dist_exists_or) *)
(*  Prove that existential quantification distributes over
    disjunction. *)
(** 存在量化子が論理和において分配法則を満たすことを証明しなさい。 *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)
(* #################################################################### *)
(*  * Programming with Propositions *)
(** 命題を使ったプログラミング *)
(*  The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure:
    - If [l] is the empty list, then [x] cannot occur on it, so the
      property "[x] appears in [l]" is simply false.
    - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
      occurs in [l] if either it is equal to [x'] or it occurs in
      [l']. *)
(** これまでに見て来た論理結合子は、シンプルな命題から複雑な命題までを定義するための豊富な語彙を提供しています。そのことを説明するために、ある要素[x]がリスト中に現れるという主張を表現する方法について見て行くことにしましょう。この属性は単純な再帰的構造を持つことに注意してください。
	
    - [l]が空リストであるならば、[x]は[l]上に現れることはない。そのため、属性 "[x] appears in [l]"は false。
    - [l]が [x' :: l']という形の場合、「x']が[x]と等しいか、[l']の中に現れれば、[x]は[l]に現れると言える。 *)
(*  We can translate this directly into a straightforward Coq
    function, [In].  (It can also be found in the Coq standard
    library.) *)
(** この記述をCoqの関数[In]に直接翻訳出来ます。(同じものはCoqの標準ライブラリにありますが) *)
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.
(*  When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested conjunctions. *)
(** [In]が具体的なリストに適用された場合、ネストした論理和の列に展開されます。*)
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
(*  (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)
(** ところで、最後に捨てられる空パターンの使用に気をつけてください。*)
(*  We can also prove more generic, higher-level lemmas about [In].
    Note, in the next, how [In] starts out applied to a variable and
    only gets expanded when we do case analysis on this variable: *)
(** [In]についての高レベルな補題を使って、もっと一般的に証明することも出来ます。次は[In]がある引数に対してケース分析をしたとき、どのようにその変数に適用を始めて、展開されるのかについて注意してください。*)
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
(** 命題を定義するこの方法は、ある場合では十分に便利ですが、欠点もあります。特に、再帰的関数の定義に関してCoqが課す制限(関数は明々白々に終了しなければならないってやつ)にひっかかる場合です。
次の章において、命題を再帰的に定義する方法を見る予定です。その方法自体に強みと制限もあって、命題を返す関数とは異なるテクニックです。*)
(*  **** Exercise: 2 stars (In_map_iff)  *)
(** **** 練習問題: ★★ (In_map_iff) *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(*  **** Exercise: 2 stars (in_app_iff)  *)
(** **** 練習問題: ★★ (in_map_iff) *)
Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(** **** Exercise: 3 stars (All)  *)
(** **** 練習問題: ★★★ (All) *)
(** Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].
    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)
(** 命題を返す関数は、関数の引数の_属性_と考えることが出来る、ということを思い出してください。たとえば、もし[P]が[nat -> Prop]という型を持っているなら、[P n]は属性[P]が[n]で成り立つ。ということを主張しています。
[In]を参考に、[All]という再帰的関数を書きなさい。関数[All]は属性[P]がリストの全要素で成り立つ、ということを述べる関数です。あなたの定義が正しいことを確かめるために、[All_In]という補題を下に用意しました。(もちろんあなたの定義は[All_In]の左側を単に述べ直すというものであるべきではありません。*)
Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
  (* FILL IN HERE *) admit.
Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(*  **** Exercise: 3 stars (combine_odd_even)  *)
(** **** 練習問題: ★★★ (combine_odd_even) *)
(*  Complete the definition of the [combine_odd_even] function below.
    It takes as arguments two properties of numbers, [Podd] and
    [Peven], and it should return a property [P] such that [P n] is
    equivalent to [Podd n] when [n] is odd and equivalent to [Peven n]
    otherwise. *)
(** [combine_odd_even]の定義を完成させなさい。数についての属性[Podd]と[Peven]を二つ引数として、属性[P]を返します。
[P n]はnが奇数のとき、[Podd n]であり、nが偶数のときは[Peven n]であるような属性です。
Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (* FILL IN HERE *) admit.
(*  To test your definition, prove the following facts: *)
(** あなたの定義をテストするために、以下の事実を証明しましょう *)
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
(*  One feature of Coq that distinguishes it from many other proof
    assistants is that it treats _proofs_ as first-class objects.
    There is a great deal to be said about this, but it is not
    necessary to understand it in detail in order to use Coq.  This
    section gives just a taste, while a deeper exploration can be
    found in the optional chapters [ProofObjects] and
    [IndPrinciples]. *)
(** 他の多くの証明支援系が持っていないCoqの特徴の一つに _証明_そのものが第一級のオブジェクトとして扱える。というのがあります。
このことについて言及することは大変ですし、Coqを使う上で、その詳細を理解しておく必要はありません。このセクションでは、後のオプションの章である[ProofObject]や[IndPrinciples]で詳しく探求することのさわりを伝えます。*)
(*  We have seen that we can use the [Check] command to ask Coq to
    print the type of an expression.  We can also use [Check] to ask
    what theorem a particular identifier refers to. *)
(** [Check]コマンドを使って、式の型をCoqに表示させて来ました。同様に、[Check]を使うことで、特定の識別子を持つ定理が何に言及しているかも分かります。*)
Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)
(*  Coq prints the _statement_ of the [plus_comm] theorem in the same
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
(** なぜ[plus_comm]定理の文が型とおなじく[Check]コマンドという同じ方法で出力されるのでしょうか？
その理由は、[plus_comm]という識別子が実際に参照しているのは、_証明オブジェクト_と呼ばれるものです。
証明オブジェクトは、[forall n m:nat, n + m = m + n]といった真なる文の立証を行う論理的な導出を表すデータ構造です。
このオブジェクトの型は、証明された定理からなる文(statement)です。
直感的に、定理の文とは、計算可能なオブジェクトの型とはそのオブジェクトを -- 型が [nat -> nat -> nat]であるとき、それが二つのnatを引数にとって、natを返すものであることが分かるように -- どのように使うかを示すものであるのと同様に、定理をどう使うかを示すものなので、理にかなっているように聞こえます。同様に、[n = m -> n + n = m + m]という型のオブジェクトは、その[n = m]という型の引数から、[n + n = m + m]を導出することが出来るものです。
   
操作上、このアナロジーは次のようなものです。 定理を適用することによって、まるで関数のように、型を仮定にマッチングさせることで、中間的な表明を必要とすることなく、その結果を追求することが出来ます。
例えば、次の結果を証明しようとしているとします。*)
Lemma plus_comm3 :
  forall n m p, n + (m + p) = (p + m) + n.
(*  It appears at first sight that we ought to be able to prove this
    by rewriting with [plus_comm] twice to make the two sides match.
    The problem, however, is that the second [rewrite] will undo the
    effect of the first. *)
(** 最初の印象として、[plus_comm]を2回使う書き換えだけで証明出来るべきだと思うでしょうが、この問題は、二回目の[rewrite]は最初のrewriteの効果を打ち消してしまします。*)
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite plus_comm.
  (* 最初に戻ってしまいました... *)
(*  One simple way of fixing this problem, using only tools that we
    already know, is to use [assert] to derive a specialized version
    of [plus_comm] that can be used to rewrite exactly where we
    want. *)
(** この問題を解決する最も単純な方法の一つは、我々もすでに知っているツール[assert]を持ちいて、[plus_comm]で我々が望む書き換え方法を導出することです。*)
  rewrite plus_comm.
  assert (H : m + p = p + m).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.
(** A more elegant alternative is to apply [plus_comm] directly to the
    arguments we want to instantiate it with, in much the same way as
    we apply a polymorphic function to a type argument. *)
(** もっとエレガントな選択肢は、[plus_comm]を直接我々が望むところに適用することです。多相的な関数を適用するのと似たような方法です。*)
Lemma plus_comm3_take2 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.
(*  You can "use theorems as functions" in this way with almost all
    tactics that take a theorem name as an argument.  Note also that
    theorem application uses the same inference mechanisms as function
    application; thus, it is possible, for example, to supply
    wildcards as arguments to be inferred, or to declare some
    hypotheses to a theorem as implicit by default.  These features
    are illustrated in the proof below. *)
(** このようにして、定理を関数のように使うことが、 定理の名前を引数にとるほとんど全てのタクティックで、出来ます。定理の適用は関数適用と同じ推論メカニズムを使用することに注意してください。
そのため、例えば、ワイルドカードを引数として型推論させるために使用できます。あるいは、ある仮説を定理として暗黙に最初から宣言出来ます。これらの特徴を下記の証明で見ることが出来ます。*)
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
(*  We will see many more examples of the idioms from this section in
    later chapters. *)
(** 後の章で、このセクションのイデオムの例をもっと見ることになるでしょう。 *)
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
(** Coqの論理の中核は、_再帰構造の計算_であり、ある重要な点で、正確で厳格な証明を書く数学者によって使用されている他の形式システムと違っています。
例えば、もっともポピュラーな紙とペンを使う主流の数学たるツェルメロ-フレンケルの集合論(ZFC)において、 数学的オブジェクトは潜在的に、多くの異なった集合のメンバーでありえますが、一方、Coqの扱うロジックにおいては大抵、一つの型のメンバーです。
この違いは、非形式的な数学的概念を、(これらは全般的に極めて自然で、理解するのがやさしいのですが) を理解するのに、しばしば少し異なった道に導きます。
例えば、「自然数[n]は偶数の集合に属している」と言う代わりにCoqでは、[ev n]が成り立つならば、そのとき、[ev : nat -> Prop]は偶数の属性であると言わねばなりません
しかしながら、通常の数学的推論をCoqに翻訳出来る場合もありますが、コアとなるロジックに公理を追加しないと、翻訳が難しかったり、そもそも不可能な場合があります。
この章の結びとして、手短な議論、二つの世界の最も大きくて重要な違いを論じることにします。*)
(** ** Functional Extensionality
    The equality assertions that we have seen so far mostly have
    concerned elements of inductive types ([nat], [bool], etc.).  But
    since Coq's equality operator is polymorphic, these are not the
    only possibilities -- in particular, we can write propositions
    claiming that two _functions_ are equal to each other: *)
(** ** 関数の外延性 
   これまでに最もたくさん見て来た同値性の主張は、帰納的な型(natやboolなど)を要素としたものでした。しかしCoqの同値オペレータは多相的であるので、可能性だけでなく、--とりわけ、二つの関数がお互いに等しいという主張を持つ命題を書くことも出来ます。*)
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
(** 普通の数学の問題において、二つの関数[f]と[g]はそれらが同じ出力をするならば、等しいとされます。
    (forall x, f x = g x) -> f = g
    これは関数の外延性の原理として知られています。
    非形式的には、伸長特性とは、オブジェクトの観察される振舞に付随しているものです。それゆえ関数の外延性は単純に関数の同一性はそれらから出力されるものい --- Coqの言葉で言えば、我々がそれを適用したあとに得られた結果 --を観察することによって、完璧に決定可能であるというこをと意味します。
    関数の外延性はCoqの基本の公理の一部ではありません。二つの関数が同じであることを示す唯一の方法は簡約です。(我々が、[function_equality_ex]の証明で行なったようにです) しかし、Coqのコア論理に、[Axiom]コマンドを使って、追加することも出来ます。*)
Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.
(** Using [Axiom] has the same effect as stating a theorem and
    skipping its proof using [Admitted], but it alerts the reader that
    this isn't just something we're going to come back and fill in
    later!
    We can now invoke functional extensionality in proofs: *)
(** [Axiom]を使うことは定理を述べたり、証明を[Admitted]を使ってスキップするのと同じ効果がありますが、読者に、これは単に戻ったり、埋めたりするものではないと警告しておきます。。
これで証明中に、関数の外延性を呼び出すことが出来るようになりました。*)
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
(** 当たり前のことですが、新しい公理をCoqの論理に追加することは慎重にならなければなりません。他の公理と矛盾するかもしれないからです。
すなわち、[False]が含まれることによって、全ての命題が証明可能になるかもしれません! 残念なことに、公理が安全かどうかが分かる簡単な方法は存在しません。公理のあらゆる組み合わせが一貫していることを保証することは大変難しいことです。
幸運なことに、関数の外延性公理を追加することは無矛盾であることが知られています。*)
Print Assumptions plus_comm_ext.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)
(*  **** Exercise: 5 stars (tr_rev)  *)
(** **** 練習問題: ★★★★★ (tr_rev) *)
(*  One problem with the definition of the list-reversing function
    [rev] that we have is that it performs a call to [app] on each
    step; running [app] takes time asymptotically linear in the size
    of the list, which means that [rev] has quadratic running time.
    We can improve this with the following definition: *)
(** 以下のリストの逆転を行う関数[rev]には、各ステップ毎に、[app]を呼ばなければならなくなるという問題があります。[app]関数はリストにサイズに比例した時間がかかります。つまり、[rev]関数リストのサイズの二乗に比例する時間が掛るということです。この問題を次の定義で改善しましょう。*)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(*  This version is said to be _tail-recursive_, because the recursive
    call to the function is the last operation that needs to be
    performed (i.e., we don't have to execute [++] after the recursive
    call); a decent compiler will generate very efficient code in this
    case.  Prove that both definitions are indeed equivalent. *)
(** このバージョンは、末尾再帰と呼ばれます。なぜなら、関数の再帰呼び出しが必要になるのが最後だけだからです。(つまり、再帰呼び出しの後に何も実行する必要がありません)  妥当なコンパイラは大変効率的なコードこの場合生成するでしょう。両方の定義が確かに等価であることを証明しなさい。 *)

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
(* FILL IN HERE *) Admitted.
(** [] *)
(*  ** Propositions and Booleans *)
(** ** 命題とブール値 *)
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
(** これまでに論理的な事実をCoqによってエンコードする二つの異なる方法、一つは、[bool]型を持つブール値であり、もう一つは、[Prop]型を持つ命題、を見てきました。例えば、[n]が偶数であることを主張するために、(1) [evenb n]が[true]を返すこと。(2)[n = double k]を満す[k]が存在すること。のどちらかで言うことが出来ます。確かにこれら二つの偶数性の記述は等価です。数個の補助的な補題を使って示すことが出来ます。(その一つは練習問題として残しておきましょう。)
我々はしばしば、ブール値[evenb n]は、命題[exists k, n = double k]を反映している。と言うことがあります。*)

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.
(*  **** Exercise: 3 stars (evenb_double_conv)  *)
(** **** 練習問題: ★★★ (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  (* ヒント: [Induction.v]の [evenb_S]を使いましょう。*)
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
(*  Similarly, to state that two numbers [n] and [m] are equal, we can
    say either (1) that [beq_nat n m] returns [true] or (2) that [n =
    m].  These two notions are equivalent. *)
(** 同様に、二つの数[n]と[m]が等しいことを述べるために、(1) [beq_nat n m]が[true]を返却する。(2)
[n = m]。のどちらかを言うことが出来ます。これら二つの記述は等価です。*)

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.
(*  However, while the boolean and propositional formulations of a
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
(** しかし、主張のブール値による定式化と命題による定式化が純粋に論理的な観点から等しい一方、それらが操作的に必要とするものが異なることも見て来ました。等価性は極端な例を提供します: [beq_nat n m = true]は、[n]と[m]を含む一般的な証明ではあまり役に立たちませんが、[n = m]という形に等価性を変換することが出来れば、それを使ってrewrite出来ます。
偶数のケースもまた興味深いものです。[even_bool_prop]([even_double]を命題からブール値の主張に変換したものです)において、[k]についてのシンプルな帰納法を使いました。一方、逆の[evenb_double_conv]では、直接に、[(exists k, n = double k) => evenb n = true]を証明出来ないので、クレバーな(小賢しい？)一般化を必要としました。これらの例において、命題による主張はブール値によるものよりは便利なのですが、どんな場合でもそうであるとは言えません。例えば、関数定義の中で、一般的な命題がtrueかどうかをテスト出来ません: 結果として、次のコードは却下されます。*)

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
(* Coqにおいては、[n = 2]の型は[Prop]ですが、[bool]型(あるいは、二つの枝を持つ帰納的な型)であることが期待されています。このエラーメッセージの理由は、Coqのコア言語の計算可能という本質を外してはならない、ということです。そのため、Coqのコアにおいて、全ての関数は計算可能であり、かつ完全であるように設計されています。その理由の一つは実行可能なプログラムをCoqのプログラムから抽出ことを許すためです。結果として、Coqにおいて、[Prop]は、与えられた命題が真かどうかを知るための一般的なケース分析をする手段を持っていません。そのような方法は、計算可能な関数として書くことは不可能であるからです。
一般的な計算可能でない属性はブール値の計算として表現出来ませんが、 多くの計算可能な属性が[bool]ではなく、[Prop]を使ってより簡単に表現出来ます。なぜなら再帰関数はCoqにおいて、重大な制限下にあるからです。例えば、次の章において、[Prop]を使って与えられた文字列が正規表現にマッチする属性を定義する方法を学びます。[bool]を持ちいて、正規表現マッチャーを書くことは、より複雑で、理解しにくく、それに関して推論しにくいものになります。
逆に、ブール値を使って事実を述べることの重要な利点は、Coqにおいて、いくつかの証明の自動化を可能にすることです。このテクニックは、「反映による証明」として知られています。次の文で考えましょう。*)

Example even_1000 : exists k, 1000 = double k.
(*  The most direct proof of this fact is to give the value of [k]
    explicitly. *)
(** 最も直接的な証明は、[k]の値を明示的に与えることです。 *)
 Proof. exists 500. reflexivity. Qed.
(* On the other hand, the proof of the corresponding boolean
    statement is even simpler: *)
(** 一方、ブール式に対応する証明はずっとシンプルです。*)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.
(*  What is interesting is that, since the two notions are equivalent,
    we can use the boolean formulation to prove the other one without
    mentioning 500 explicitly: *)
(** 興味深いことは、二つの書き方は等価なので、もう一つを500を明示的に示すことなく証明するために、ブール式を使うことが出来ることです: *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.
(*  Although we haven't gained much in terms of proof size in this
    case, larger proofs can often be made considerably simpler by the
    use of reflection.  As an extreme example, the Coq proof of the
    famous _4-color theorem_ uses reflection to reduce the analysis of
    hundreds of different cases to a boolean computation.  We won't
    cover reflection in great detail, but it serves as a good example
    showing the complementary strengths of booleans and general
    propositions. *)
(** このケースでは、証明の記述量に関して大した利点はありませんでしたが、もっと大きな証明において、リフレクションの使用は顕著にあらわれます。極端な例として、Coqの4色問題の証明では、reflectionの使用によって、数百の異なるケース分析をブール値の計算に変換して減らすことだ出来ました。ここでreflectionの細かな説明は行いませんが、ここでブール値と一般的な命題がお互い補完しあうものであることを示すよい例を示します。*)
(*  **** Exercise: 2 stars (logical_connectives)  *)
(** **** 練習問題: ★★ (logical_connectives)  *)
(*  The following lemmas relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)
(** 次の補題は、この章で学んだ命題の結合と、それに対応するブール値の操作と関係があります。
Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.
Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(*  **** Exercise: 1 star (beq_nat_false_iff)  *)
(** **** 練習問題: ★ (beq_nat_false_iff)  *)
(*  The following theorem is an alternate "negative" formulation of
    [beq_nat_true_iff] that is more convenient in certain
    situations (we'll see examples in later chapters). *)
(** 次の定理は、ある状況では便利な[beq_nat_true_iff]の否定の式の代わりになるものです。(後の章で例を見ることでしょう。*)

Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(*  **** Exercise: 3 stars (beq_list)  *)
(** **** 練習問題: ★★★ (beq_list)  *)
(** Given a boolean operator [beq] for testing equality of elements of
    some type [A], we can define a function [beq_list beq] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [beq_list] function below.  To make sure that your
    definition is correct, prove the lemma [beq_list_true_iff]. *)
(** 型[A]の要素の等価性のテストを行うブール値の演算子[beq]が与えられたとすると、[A]を要素に物リストの等価性をテストする関数[beq_list beq]を定義することが出来ます。下記の[beq_list]関数の定義を完成させ、補題[beq_list_true_iff]を証明しなさい。*)

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
(*  **** Exercise: 2 stars, recommended (All_forallb)  *)
(** **** 練習問題: ★★ , recommended (All_forallb)  *)
(*  Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Tactics]: *)
(** [Tactics]の章の[forall_exists_challenge]にあった[forallb]関数を思い出してください。*)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.
(*  Prove the theorem below, which relates [forallb] to the [All]
    property of the above exercise. *)
(** 下記の定理を証明しなさい。この定理は[forallb]を[All]属性に関係付けます。*)
Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.
(*  Are there any important properties of the function [forallb] which
    are not captured by your specification? *)
(** あなたの[forallb]関数実装が捉え切れていない重要な属性がなにかあるでしょうか？ *)
(* FILL IN HERE *)
(** [] *)
(** ** Classical vs. Constructive Logic *)
(** We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Coq function.  You may be
    surprised to learn that a similar restriction applies to _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Coq: *)
(** Coqの関数を定義する命題[P]が真かどうかをテストすることが出来ないこと見てきました。
同様な制限が証明に課せられていること知って驚くかもしれません。 別の言葉で言えば、次の直感的な推論原理をCoqから引き出すことが出来ません。*)
Definition excluded_middle := forall P : Prop,
  P \/ ~ P.
(*  To understand operationally why this is the case, recall that, to
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
(** これがなぜなのかを手を動かして理解するために、[P \/ Q]という形の文を証明するために、選言のどちらを必要とするかを知るために、[left]と[right]タクティックを使ったことを思い出してください。しかし、例外なく、[excluded_middle]の中で量化された[P]は任意の命題で、どんなものか分かりません。そのため[left]と[right]のどちらを選んで適用すべきかを知るための十分な情報を持っていないのです。一方、[P]があるブール値を反映したものであると知っているならば、それがどちらの値であるかどうか知ることは些細なことです: 単に[b]の値をチェックすればよいのです。このことが以下の定理を導きます。*)

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
(** 特に、自然数[n]と[m]の間の等価性に対する排中律は常に成り立ちます。一般的な排中律が最初からCoqで使えないことは奇妙だと最初は思うかもしれません。結局、どんな主張も真か偽のどっちかであるべきであると。とはいえ、排中律を仮定しないことには利点があります: Coqの文が一般的な数学における類似した主張よりも強い主張を行なうことが出来るのです。とりわけ、Coqの[exists x, P x]の証明は、[P x]を証明するために、明示的に値[x]を提示することが可能です。-- 別の言葉で言うと、全ての存在証明は必ず構成的でなければなりません。このため、排中律を仮定しないCoqと同じロジックは構成的論理と言われます。もっと普通のFZFCのような任意の命題に対する排中律を含む論理体系は、古典的であると言われます。次の例は排中律を仮定することがなぜ非構成的な証明を導くかを説明します。*)

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
(** 主張: [a ^ b] が有理数になるような、無理数[a]と[b]が存在する。
    証明: [sqrt 2]が無理数であることを示すことは難しくない。
    [sqrt 2 ^ sqrt 2]が、有理数であるとする。すると、[a = b = sqrt 2]が、条件を満たす数字である。あるいは、[sqrt 2 ^ sqrt 2]が無理数であったとする。その場合、
  [ a = sqrt 2 ^ sqrt 2]と[b = sqrt 2]が我々の求めるものである。なぜなら、[a ^ b = (sqrt 2 ^ sqrt 2) ^ sqrt 2 = sqrt 2 ^ 2 = 2]と有理数になるからである。証明終り。
    ここで何が起ったか分かりますか？ ここで我々は排中律を[sqrt 2 ^ sqrt 2]が有理数かそうでないかを場合を分けて考えるために使用しました。実際にその値がなんであるか知ることなしにです。このため、そのような[a]と[b]が存在することは分かりますが、実際にその値が何であるかを決定することは出来ません。(少なくともこの論法では)
構成的論理と同じくらい使いやすいように、その限界も持っています: 古典論理で容易く証明出来るけれども、構成的証明では証明が複雑になってしまう文が多くあります。また、そもそも全く証明出来ない文も存在します!幸運なことに、関数の外延性のように、排中律もCoqの論理に混ぜることが可能で、公理として、安全に加えることが許されています。しかし、この本においては、そうする必要はありません:我々がカバーする結果は構成的論理の範囲で達成可能で追加のコストを必要としません。
構成的論理の推論において、どの証明技法を避けるべきなのかを理解するために少しばかり練習が必要ですが、とりわけ、矛盾による論法は非構成的な証明を導くと評判がよろしくありません。ここで、典型的な例を用意しました: ある属性[P]を持つ[x]が存在することを示したいと仮定します。我々の結論が偽であることを仮定して証明を開始します。すなわち、[~ exists x, P x]です。この前提から、[forall x, ~ P x]を導くことは難しくありません。もし、この証明の中間状態が矛盾することをなんとかして示したいとすると、[P x]が成り立つ[x]のどんな値を提示することのない存在証明にたどりつきます。
構成的観点から、この技術的欠陥は、[~ ~ exists x, P x]の証明を使って[exists x, P x]の証明をしたと言うことです。任意の文の二重否定を除去を許すことは、以下の練習問題で見るように、排中律を仮定することと等しいのです。それゆえ、この推論は、Coqにおいては、追加の公理なしで書き下すことは出来ません。*)

(*  ** Exercise: 3 stars (excluded_middle_irrefutable)  *)
(** **** 練習問題: ★★★ (excluded_middle_irrefutable)  *)
(*  The consistency of Coq with the general excluded middle axiom
    requires complicated reasoning that cannot be carried out within
    Coq itself.  However, the following theorem implies that it is
    always safe to assume a decidability axiom (i.e., an instance of
    excluded middle) for any _particular_ Prop [P].  Why? Because we
    cannot prove the negation of such an axiom; if we could, we would
    have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)
(** Coqに排中律を加えた場合の無矛盾性を示すため？にはCoqの内部で実行される複雑な推論を必要とします。しかし、次の定理は、ある"特定の"命題に対して、決定可能性の公理(たとえば、排中律など)を安全に仮定することが出来ることを含意します。なぜでしょうか？我々はそのような公理の否定を証明出来ないからです: もしそれが出来たとすると、[~ (P \/ ~ P) ]と[~ ~ (P \/ ~ P) ]の両方を持つことになり、矛盾してしまうからです。:*)
Theorem excluded_middle_irrefutable:  forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(*  **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** **** 練習問題: ★★★ optional (not_exists_dist)  *)
(** It is a theorem of classical logic that the following two
    assertions are equivalent:
    ~ (exists x, ~ P x)
    forall x, P x
    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle. *)
(** 古典論理において、次の二つの言明は等価です:
    ~ (exists x, ~ P x)
    forall x, P x
    上記の[dist_not_exists]定理は、この等価性の片面です。興味深いことにもう一つの方向は構成的論理では証明出来ません。あなたの仕事は、排中律によってこれが導かれることを示すことです。*)
Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(*  **** Exercise: 5 stars, advanced, optional (classical_axioms)  *)
(** **** 練習問題: ★★★★★★, advanced, optional (classical_axioms)  *)
(** For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.
    Prove that all five propositions (these four plus
    [excluded_middle]) are equivalent. *)
(**  さらなる挑戦を求める人のために、 Coq'Art book (p. 123) から一つ練習問題を取り上げてみます。次のそれぞれの文は、よく「古典論理の特性」と考えられているもの（Coqにビルトインされている構成的論理の対極にあるもの）です。これらをCoqで証明することはできませんが、古典論理を使うことが必要なら、矛盾なく「証明されていない公理」として道具に加えることができます。これら5つの命題(以下の4つに[excluded_middle]を加えたもの)が等価であることを証明しなさい。 *)
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

