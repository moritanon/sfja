(* * Equiv: Program Equivalence *)
(** * Equiv_J: プログラムの同値性 *)


Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import SfLib.
Require Import Maps.
Require Import Imp.

(*  *** Some general advice for working on exercises:

    - Most of the Coq proofs we ask you to do are similar to proofs
      that we've provided.  Before starting to work on exercises
      problems, take the time to work through our proofs (both
      informally, on paper, and in Coq) and make sure you understand
      them in detail.  This will save you a lot of time.

    - The Coq proofs we're doing now are sufficiently complicated that
      it is more or less impossible to complete them simply by random
      experimentation or "following your nose."  You need to start
      with an idea about why the property is true and how the proof is
      going to go.  The best way to do this is to write out at least a
      sketch of an informal proof on paper -- one that intuitively
      convinces you of the truth of the theorem -- before starting to
      work on the formal one.  Alternately, grab a friend and try to
      convince them that the theorem is true; then try to formalize
      your explanation.

    - Use automation to save work!  Some of the proofs in this
      chapter's exercises are pretty long if you try to write out all
      the cases explicitly. *)
(** *** 練習問題を行う上での一般的アドバイス

    - Coqによる証明問題は、そこまでに文中で行ってきた証明となるべく同じようにできるようにしています。
      宿題に取り組む前に、そこまでの証明を自分でも(紙上とCoqの両方で)やってみなさい。
      そして、細部まで理解していることを確認しなさい。
      そうすることは、多くの時間を節約することになるでしょう。

    - 問題にする Coq の証明はそれなりに複雑なため、
      単に怪しそうなところをランダムに探ってみるような方法で解くことはまず無理です。
      なぜその性質が真で、どう進めば証明になるかを最初に考える必要があります。
      そのための一番良い方法は、形式的な証明を始める前に、
      紙の上に非形式的な証明をスケッチでも良いので書いてみることです。
      またあるいは、友達をつかまえ、その定理が真であることの説得を試みて、
      そしてそれから、あなたの説明を形式化するのです。
      そうすることで、定理が成立することを直観的に確信できます。

    - 仕事を減らすために自動化を使いなさい。この章の練習問題の証明のいくつかは、
      もしすべての場合を明示的に書き出すとすると、とても長くなります。*)

(* ####################################################### *)
(* * Behavioral Equivalence *)
(** * 振る舞い同値性 *)

(* In an earlier chapter, we investigated the correctness of a very
    simple program transformation: the [optimize_0plus] function.  The
    programming language we were considering was the first version of
    the language of arithmetic expressions -- with no variables -- so
    in that setting it was very easy to define what it means for a
    program transformation to be correct: it should always yield a
    program that evaluates to the same number as the original.

    To go further and talk about the correctness of program
    transformations in the full Imp language, we need to consider the
    role of variables and state. *)

(** 以前の章で、簡単なプログラム変換の正しさを調べました。
    [optimize_0plus]関数です。
    対象としたプログラミング言語は、算術式の言語の最初のバージョンでした。
    それには変数もなく、そのためプログラム変換が正しいとはどういうことかという意味
    を定義することはとても簡単でした。
    つまり、変換の結果得られるプログラムが常に、
    それを評価すると元のプログラムと同じ数値になるということでした。

    Imp言語全体についてプログラム変換の正しさを語るためには、
    変数の役割、および状態について考えなければなりません。*)

(* ####################################################### *)
(* ** Definitions *)
(** ** 定義 *)

(** For [aexp]s and [bexp]s with variables, the definition we want is
    clear.  We say
    that two [aexp]s or [bexp]s are _behaviorally equivalent_ if they
    evaluate to the same result _in every state_. *)
(** 変数を伴う[aexp]と[bexp]については、どう定義すれば良いかは明らかです。
    2つの[aexp]または[bexp]が振る舞い同値である(_behaviorally equivalent_)とは、
    「すべての状態で」2つの評価結果が同じになることです。*)   

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

(*  For commands, the situation is a little more subtle.  We can't
    simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are started in the
    same initial state," because some commands, when run in some
    starting states, don't terminate in any final state at all!  What
    we need instead is this: two commands are behaviorally equivalent
    if, for any given starting state, they either both diverge or both
    terminate in the same final state.  A compact way to express this
    is "if the first one terminates in a particular state then so does
    the second, and vice versa." *)
(** コマンドについては、状況はもうちょっと微妙です。
    簡単に「2つのコマンドが振る舞い同値であるとは、
    両者を同じ状態から開始すれば同じ状態で終わることである」と言うわけには行きません。
    コマンドによっては,特定の状態から開始したときには、
    停止しないためどのような状態にもならないことがあるからです!
    すると次のように言う必要があります。
    2つのコマンドが振る舞い同値であるとは、任意の与えられた状態から両者をスタートすると、
    両者ともに発散するか、両者ともに停止して同じ状態になることです。
    これを簡潔に表現すると、「1つ目が停止して特定の状態になるならば2つ目も同じになり、
    逆もまた成り立つ」となります。*)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').

(** **** 練習問題: ★★, (equiv_classes) *)

(*  Given the following programs, group together those that are
    equivalent in Imp. Your answer should be given as a list of lists,
    where each sub-list represents a group of equivalent programs. For
    example, if you think programs (a) through (h) are all equivalent
    to each other, but not to (i), your answer should look like this:

       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]

    Write down your answer below in the definition of
    [equiv_classes]. *)
(** 次のプログラムが与えられたとき、[Imp]において等しいものグループを作りなさい。
    あなたの答をリストのリストとして表現し、それぞれのサブリストが等価なプログラムのグループを表すようにしなさい。例えば、(a)から(h)までが全て同じプログラムであり、(i)だけが違うと思うならば、答は次のようになります：

    [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
      [prog_i] ]

    あなたの答えを[equiv_classes]という名前で定義しなさい。*)

Definition prog_a : com :=
  WHILE BNot (BLe (AId X) (ANum 0)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_b : com :=
  IFB BEq (AId X) (ANum 0) THEN
    X ::= APlus (AId X) (ANum 1);;
    Y ::= ANum 1
  ELSE
    Y ::= ANum 0
  FI;;
  X ::= AMinus (AId X) (AId Y);;
  Y ::= ANum 0.

Definition prog_c : com :=
  SKIP.

Definition prog_d : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= APlus (AMult (AId X) (AId Y)) (ANum 1)
  END.

Definition prog_e : com :=
  Y ::= ANum 0.

Definition prog_f : com :=
  Y ::= APlus (AId X) (ANum 1);;
  WHILE BNot (BEq (AId X) (AId Y)) DO
    Y ::= APlus (AId X) (ANum 1)
  END.

Definition prog_g : com :=
  WHILE BTrue DO
    SKIP
  END.

Definition prog_h : com :=
  WHILE BNot (BEq (AId X) (AId X)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_i : com :=
  WHILE BNot (BEq (AId X) (AId Y)) DO
    X ::= APlus (AId Y) (ANum 1)
  END.

Definition equiv_classes : list (list com) :=
(* FILL IN HERE *) admit.
(** [] *)

(* ####################################################### *)
(* ** Examples *)
(** ** 例 *)

(*  Here are some simple examples of equivalences of arithmetic
    and boolean expressions. *)
(** 算術式とブール式の同値性の簡単な例をあげてみます。*)

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  intros st. simpl. omega.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(*  For examples of command equivalence, let's start by looking at
    some trivial program transformations involving [SKIP]: *)
(** コマンドの同値性の例として、
    [SKIP]にからんだ自明な変換から見てみましょう: *)

Theorem skip_left: forall c,
  cequiv
     (SKIP;; c)
     c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

(** **** 練習問題: ★★ (skip_right) *)
(*  Prove that adding a [SKIP] after a command results in an
    equivalent program *)
(** SKIPをコマンドの結果の後ろに追加することはもとのプログラムと等しいことを証明しなさい *)

Theorem skip_right: forall c,
  cequiv
    (c ;; SKIP)
    c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Similarly, here is a simple transformations that optimizes [IFB]
    commands: *)
(** 同様に[IFB]コマンドを最適化する単純な変換です: *)

Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst. assumption. inversion H5.
  - (* <- *)
    apply E_IfTrue. reflexivity. assumption.  Qed.

(*  Of course, few programmers would be tempted to write a conditional
    whose guard is literally [BTrue].  A more interesting case is when
    the guard is _equivalent_ to true:

   _Theorem_: If [b] is equivalent to [BTrue], then [IFB b THEN c1
   ELSE c2 FI] is equivalent to [c1].
*)
(** もちろん、ガードが[BTrue]そのままである条件文を書こうとするプログラマはほとんどいないでしょう。
    より興味深いのは、ガードが真と「同値である」場合です:

   「定理」:もし[b]が[BTrue]と同値ならば、[IFB b THEN c1 ELSE c2 FI]は[c1]と同値である。
*)
(** *** *)
(**
   _Proof_:

     - ([->]) We must show, for all [st] and [st'], that if [IFB b
       THEN c1 ELSE c2 FI / st \\ st'] then [c1 / st \\ st'].

       Proceed by cases on the rules that could possibly have been
       used to show [IFB b THEN c1 ELSE c2 FI / st \\ st'], namely
       [E_IfTrue] and [E_IfFalse].

       - Suppose the final rule rule in the derivation of [IFB b THEN
         c1 ELSE c2 FI / st \\ st'] was [E_IfTrue].  We then have, by
         the premises of [E_IfTrue], that [c1 / st \\ st'].  This is
         exactly what we set out to prove.

       - On the other hand, suppose the final rule in the derivation
         of [IFB b THEN c1 ELSE c2 FI / st \\ st'] was [E_IfFalse].
         We then know that [beval st b = false] and [c2 / st \\ st'].

         Recall that [b] is equivalent to [BTrue], i.e., forall [st],
         [beval st b = beval st BTrue].  In particular, this means
         that [beval st b = true], since [beval st BTrue = true].  But
         this is a contradiction, since [E_IfFalse] requires that
         [beval st b = false].  Thus, the final rule could not have
         been [E_IfFalse].

     - ([<-]) We must show, for all [st] and [st'], that if [c1 / st
       \\ st'] then [IFB b THEN c1 ELSE c2 FI / st \\ st'].

       Since [b] is equivalent to [BTrue], we know that [beval st b] =
       [beval st BTrue] = [true].  Together with the assumption that
       [c1 / st \\ st'], we can apply [E_IfTrue] to derive [IFB b THEN
       c1 ELSE c2 FI / st \\ st'].  []

   Here is the formal version of this proof: *)
(**
   「証明」:

     - ([->]) すべての[st]と[st']に対して、もし[IFB b THEN c1 ELSE c2 FI / st \\ st']
       ならば[c1 / st \\ st']となることを示す。

       [IFB b THEN c1 ELSE c2 FI / st \\ st']を示すのに使うことができた可能性のある規則、
       つまり[E_IfTrue]と[E_IfFalse]とで、場合分けをする。

       - [IFB b THEN c1 ELSE c2 FI / st \\ st']
         の導出の最後の規則が[E_IfTrue]であると仮定する。
         このとき、[E_IfTrue]の仮定より[c1 / st \\ st']となる。
         これはまさに証明したいことである。

       - 一方、[IFB b THEN c1 ELSE c2 FI / st \\ st']
         の導出の最後の規則が[E_IfFalse]と仮定する。
         すると、[beval st b = false]かつ[c2 / st \\ st']となる。

         [b]が[BTrue]と同値であったことから、
         すべての[st]について、[beval st b = beval st BTrue]が成立する。
         これは特に[beval st b = true]を意味する。
         なぜなら[beval st BTrue = true]だからである。
         しかしこれは矛盾である。なぜなら、
         [E_IfFalse]から[beval st b = false]でなければならないからである。
         従って、最後の規則は[E_IfFalse]ではあり得ない。

     - ([<-]) すべての[st]と[st']について、もし[c1 / st\\ st']ならば
       [IFB b THEN c1 ELSE c2 FI / st \\ st']となることを示す。

       [b]が[BTrue]と同値であることから、
       [beval st b] = [beval st BTrue] = [true]となる。
       仮定[c1 / st \\ st']より[E_IfTrue]が適用でき、
       [IFB b THEN c1 ELSE c2 FI / st \\ st']となる。  []
      

   以下がこの証明の形式化版です: *)

Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue  ->
     cequiv
       (IFB b THEN c1 ELSE c2 FI)
       c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      inversion H5.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity.  Qed.

(** **** 練習問題: ★★ (IFB_false) *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★ (swap_if_branches) *)
(* Show that we can swap the branches of an IF by negating its
    condition *)
(** IFの条件の枝が否定によって交換可能であることを示しなさい *)
Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  For [WHILE] loops, we can give a similar pair of theorems.  A loop
    whose guard is equivalent to [BFalse] is equivalent to [SKIP],
    while a loop whose guard is equivalent to [BTrue] is equivalent to
    [WHILE BTrue DO SKIP END] (or any other non-terminating program).
    The first of these facts is easy. *)
(** [WHILE]ループについては、同様の2つ定理があります:
    ガードが[BFalse]と同値であるループは[SKIP]と同値である、というものと、
    ガードが[BTrue]と同値であるループは[WHILE BTrue DO SKIP END]
    (あるいは他の任意の停止しないプログラム)と同値である、というものです。
    1つ目のものは簡単です。*)

Theorem WHILE_false : forall b c,
     bequiv b BFalse ->
     cequiv
       (WHILE b DO c END)
       SKIP.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileEnd *)
      apply E_Skip.
    + (* E_WhileLoop *)
      rewrite Hb in H2. inversion H2.
  - (* <- *)
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity.  Qed.

(** **** 練習問題: ★★, advanced, optional (WHILE_false_informal) *)
(*  Write an informal proof of WHILE_false. *)
(** WHILE_falseの非形式的証明を記述しなさい。

(* FILL IN HERE *)
[]
*)

(* To prove the second fact, we need an auxiliary lemma stating that
    [WHILE] loops whose guards are equivalent to [BTrue] never
    terminate:

    _Lemma_: If [b] is equivalent to [BTrue], then it cannot be the
    case that [(WHILE b DO c END) / st \\ st'].

    _Proof_: Suppose that [(WHILE b DO c END) / st \\ st'].  We show,
    by induction on a derivation of [(WHILE b DO c END) / st \\ st'],
    that this assumption leads to a contradiction.

      - Suppose [(WHILE b DO c END) / st \\ st'] is proved using rule
        [E_WhileEnd].  Then by assumption [beval st b = false].  But
        this contradicts the assumption that [b] is equivalent to
        [BTrue].

      - Suppose [(WHILE b DO c END) / st \\ st'] is proved using rule
        [E_WhileLoop].  Then we are given the induction hypothesis
        that [(WHILE b DO c END) / st \\ st'] is contradictory, which
        is exactly what we are trying to prove!

      - Since these are the only rules that could have been used to
        prove [(WHILE b DO c END) / st \\ st'], the other cases of
        the induction are immediately contradictory. [] *)
(** 2つ目の事実を証明するためには、
    ガードが[BTrue]と同値であるwhileループが停止しないことを言う補題が1つ必要です:

    「補題」:[b]が[BTrue]と同値のとき、
    [(WHILE b DO c END) / st \\ st']となることはない。

    「証明」:[(WHILE b DO c END) / st \\ st']と仮定する。
    [(WHILE b DO c END) / st \\ st']の導出についての帰納法によって、
    この仮定から矛盾が導かれることを示す。

      - [(WHILE b DO c END) / st \\ st']が規則[E_WhileEnd]
        から証明されると仮定する。すると仮定から[beval st b = false]となる。
        しかしこれは、[b]が[BTrue]と同値という仮定と矛盾する。

      - [(WHILE b DO c END) / st \\ st']が規則[E_WhileLoop]
        を使って証明されると仮定する。
        すると帰納法の仮定として
        [(WHILE b DO c END) / st \\ st']が矛盾するということが得られる。
        これはまさに証明しようとしていることである。

      - 上記が[(WHILE b DO c END) / st \\ st']
        の証明に使うことができる可能性がある規則のすべてであり、
        帰納法の他の場合は、すぐに矛盾になる。[] *)

Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st \\ st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H;
    (* Most rules don't apply, and we can rule them out
       by inversion *)
    inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for WHILE loops: *)
  - (* E_WhileEnd *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. inversion H.
  - (* E_WhileLoop *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

(** **** 練習問題: ★★, optional (WHILE_true_nonterm_informal) *)
(* Explain what the lemma [WHILE_true_nonterm] means in English.

(* FILL IN HERE *)
*)
(** 補題[WHILE_true_nonterm]が意味するものを日本語で書きなさい。

(* FILL IN HERE *)
*)
(** [] *)

(** **** 練習問題: ★★, recommended (WHILE_true) *)
(*  Prove the following theorem. _Hint_: You'll want to use
(** 次の定理を証明しなさい。ヒント: ここで[WHILE_true_nonterm]を使いなさい。*)

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* loop doesn't run *)
      apply E_IfFalse. assumption. apply E_Skip.
    + (* loop runs *)
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0).
      assumption. assumption. assumption.
    + (* loop doesn't run *)
      inversion H5; subst. apply E_WhileEnd. assumption.  Qed.

(** **** 練習問題: ★★, optional (seq_assoc) *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  Proving program properties involving assignments is one place
    where the functional-extensionality axiom introduced in the
    [Logic] chapter often comes in handy.  Here are an example and an
    exercise. *)
(** 代入を含むプログラムの属性を証明する際には、[Logic]の章で
導入された関数の外延性公理がしばしば役に立ちます。例と練習問題を示します。*)

Theorem identity_assignment : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
   intros. split; intro H.
     - (* -> *)
       inversion H; subst. simpl.
       replace (t_update st X (st X)) with st.
       + constructor.
       + apply functional_extensionality. intro.
         rewrite t_update_same; reflexivity.
     - (* <- *)
       replace st' with (t_update st' X (aeval st' (AId X))).
       + inversion H. subst. apply E_Ass. reflexivity.
       + apply functional_extensionality. intro.
         rewrite t_update_same. reflexivity.
Qed.

(** **** 練習問題: ★★, recommanded (assign_aequiv) *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(* * Properties of Behavioral Equivalence *)
(** * 振る舞い同値の性質 *)

(* We now turn to developing some of the properties of the program
    equivalences we have defined. *)
(** ここからは、定義したプログラムの同値概念の性質を調べていきましょう。*)

(* ####################################################### *)
(* ** Behavioral Equivalence Is an Equivalence *)
(** ** 振る舞い同値は同値関係である *)

(* First, we verify that the equivalences on [aexps], [bexps], and
    [com]s really are _equivalences_ -- i.e., that they are reflexive,
    symmetric, and transitive.  The proofs are all easy. *)
(** 最初に、[aexps]、[bexps]、[com]の同値が、本当に「同値関係」であること、つまり、
    反射性、対称性、推移性を持つことを検証します。証明はすべて簡単です。 *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (c1 / st \\ st' <-> c2 / st \\ st') as H'.
  { (* Proof of assertion *) apply H. }
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A.  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (c2 / st \\ st'). apply H12. apply H23.  Qed.

(* ######################################################## *)
(* ** Behavioral Equivalence Is a Congruence *)
(** ** 振る舞い同値は合同関係である *)

(* Less obviously, behavioral equivalence is also a _congruence_.
    That is, the equivalence of two subprograms implies the
    equivalence of the larger programs in which they are embedded:

              aequiv a1 a1'
      -----------------------------
      cequiv (i ::= a1) (i ::= a1')

              cequiv c1 c1'
              cequiv c2 c2'
         ------------------------
         cequiv (c1;;c2) (c1';;c2')

    ...and so on for the other forms of commands.

    (Note that we are using the inference rule notation here not as
    part of a definition, but simply to write down some valid
    implications in a readable format. We prove these implications
    below.) *)
(** よりわかりにくいですが、振る舞い同値は、合同関係(_congruence_)でもあります。
    つまり、2つのサブプログラムが同値ならば、それを含むプログラム全体も同値です:

              aequiv a1 a1'
      -----------------------------
      cequiv (i ::= a1) (i ::= a1')

              cequiv c1 c1'
              cequiv c2 c2'
         ------------------------
         cequiv (c1;;c2) (c1';;c2')

    ...など他の形式のコマンドも同様です。

    (注意して欲しいのですが、ここで推論規則の記法を使っていますが、これは定義の一部ではありません。
    単に正しい含意を読みやすい形で書き出しただけです。
    この含意は以下で証明します。) *)

(*  We will see a concrete example of why these congruence
    properties are important in the following section (in the proof of
    [fold_constants_com_sound]), but the main idea is that they allow
    us to replace a small part of a large program with an equivalent
    small part and know that the whole large programs are equivalent
    _without_ doing an explicit proof about the non-varying parts --
    i.e., the "proof burden" of a small change to a large program is
    proportional to the size of the change, not the program. *)

(** 合同性がなぜ重要なのか、
    次の節で具体的な例([fold_constants_com_sound]の証明)によって見ます。
    ただ、メインのアイデアは、大きなプログラムの小さな部分を同値の小さな部分で置き換えると、
    大きなプログラム全体が元のものと同値になることを、
    変化していない部分についての明示的な証明「なしに」わかるということです。
    つまり、大きなプログラムの小さな変更についての証明の負担が、
    プログラムではなく変更に比例するということです。*)

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.  Qed.

(** The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for [WHILE] -- that is, if
    [b1] is equivalent to [b1'] and [c1] is equivalent to [c1'], then
    [WHILE b1 DO c1 END] is equivalent to [WHILE b1' DO c1' END].

    _Proof_: Suppose [b1] is equivalent to [b1'] and [c1] is
    equivalent to [c1'].  We must show, for every [st] and [st'], that
    [WHILE b1 DO c1 END / st \\ st'] iff [WHILE b1' DO c1' END / st
    \\ st'].  We consider the two directions separately.

      - ([->]) We show that [WHILE b1 DO c1 END / st \\ st'] implies
        [WHILE b1' DO c1' END / st \\ st'], by induction on a
        derivation of [WHILE b1 DO c1 END / st \\ st'].  The only
        nontrivial cases are when the final rule in the derivation is
        [E_WhileEnd] or [E_WhileLoop].

          - [E_WhileEnd]: In this case, the form of the rule gives us
            [beval st b1 = false] and [st = st'].  But then, since
            [b1] and [b1'] are equivalent, we have [beval st b1' =
            false], and [E-WhileEnd] applies, giving us [WHILE b1' DO
            c1' END / st \\ st'], as required.

          - [E_WhileLoop]: The form of the rule now gives us [beval st
            b1 = true], with [c1 / st \\ st'0] and [WHILE b1 DO c1
            END / st'0 \\ st'] for some state [st'0], with the
            induction hypothesis [WHILE b1' DO c1' END / st'0 \\
            st'].

            Since [c1] and [c1'] are equivalent, we know that [c1' /
            st \\ st'0].  And since [b1] and [b1'] are equivalent, we
            have [beval st b1' = true].  Now [E-WhileLoop] applies,
            giving us [WHILE b1' DO c1' END / st \\ st'], as
            required.

      - ([<-]) Similar. [] *)
(** ループの合同性は帰納法が必要になるので、さらに少しおもしろいものになります。

    「定理」:[WHILE]についての同値は合同関係である。
    すなわち、もし[b1]が[b1']と同値であり、[c1]が[c1']と同値ならば、
    [WHILE b1 DO c1 END]は[WHILE b1' DO c1' END]と同値である。

    「証明」:[b1]が[b1']と同値、[c1]が[c1']と同値であるとする。
    すべての[st]と[st']について、証明すべきことは、
    [WHILE b1 DO c1 END / st \\ st']の必要十分条件は
    [WHILE b1' DO c1' END / st \\ st']であることである。
    必要条件と十分条件の両方向を別々に証明する。

      - ([->]) [WHILE b1 DO c1 END / st \\ st']ならば
        [WHILE b1' DO c1' END / st \\ st']であることを、
        [WHILE b1 DO c1 END / st \\ st']の導出についての帰納法で示す。
        自明でないのは、導出の最後の規則が[E_WhileEnd]または[E_WhileLoop]のときだけである。

          - [E_WhileEnd]: この場合、
            規則の形から[beval st b1 = false]かつ[st = st']となる。
            しかし[b1]と[b1']が同値であることから
            [beval st b1' = false]になる。
            さらに[E-WhileEnd]を適用すると
            証明すべき[WHILE b1' DO c1' END / st \\ st']が得られる。

          - [E_WhileLoop]: 規則の形から
            [beval st b1 = true]および、ある状態[st'0]について
            帰納法の仮定[WHILE b1' DO c1' END / st'0 \\ st']のもとで、
            [c1 / st \\ st'0]かつ[WHILE b1 DO c1 END / st'0 \\ st']となる。

            [c1]と[c1']が同値であることから、[c1' / st \\ st'0]となる。
            さらに[b1]と[b1']が同値であることから、[beval st b1' = true]となる。
            [E-WhileLoop]を適用すると、
            証明すべき[WHILE b1' DO c1' END / st \\ st']が得られる。

      - ([<-]) 同様である。

    [] *)

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  (* WORKED IN CLASS *)
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  - (* -> *)
    remember (WHILE b1 DO c1 END) as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite <- Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.
  - (* <- *)
    remember (WHILE b1' DO c1' END) as c'while
      eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite -> Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.  Qed.

(** **** 練習問題: ★★★, optional (CSeq_congruence) *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★ (CIf_congruence) *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  For example, here are two equivalent programs and a proof of their
    equivalence... *)
(** 同値である2つのプログラムとその同値の証明の例です... *)

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (* Program 2: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X)   (* <--- changed here *)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
    apply refl_cequiv.
    apply CIf_congruence.
      apply refl_bequiv.
      apply CAss_congruence. unfold aequiv. simpl.
        symmetry. apply minus_diag.
      apply refl_cequiv.
Qed.

(* ####################################################### *)
(*  * Program Transformations *)
(** プログラムの変換 *)

(*  A _program transformation_ is a function that takes a program as
    input and produces some variant of the program as output.
    Compiler optimizations such as constant folding are a canonical
    example, but there are many others. *)
(** プログラム変換(_program transformation_)とは、
    プログラムを入力とし、出力としてそのプログラムの何らかの変形を生成する関数です。
    定数畳み込みのようなコンパイラの最適化は標準的な例ですが、それ以外のものもたくさんあります。*)

(* A program transformation is _sound_ if it preserves the
    behavior of the original program. *)
(** プログラム変換が健全(_sound_)とは、その変換が元のプログラムの振る舞いを保存することです。*)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ######################################################## *)
(* ** The Constant-Folding Transformation *)
(** ** 定数畳み込み変換 *)

(* An expression is _constant_ when it contains no variable
    references.

    Constant folding is an optimization that finds constant
    expressions and replaces them by their values. *)
(** 式が定数(_constant_)であるとは、その式が変数参照を含まないことです。

    定数畳み込みは、定数式をその値に置換する最適化です。*)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId i        => AId i
  | APlus a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp
      (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

(* Note that this version of constant folding doesn't eliminate
    trivial additions, etc. -- we are focusing attention on a single
    optimization for the sake of simplicity.  It is not hard to
    incorporate other ways of simplifying expressions; the definitions
    and proofs just get longer. *)
(** 定数畳み込みのこのバージョンは簡単な足し算等を消去していないことに注意します。
    複雑になるのを避けるため、1つの最適化に焦点を絞っています。
    式の単純化の他の方法を組込むことはそれほど難しいことではありません。
    定義と証明が長くなるだけです。*)

Example fold_aexp_ex2 :
    fold_constants_aexp
      (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6))
                             (AId Y)))
  = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

(*  Not only can we lift [fold_constants_aexp] to [bexp]s (in the
    [BEq] and [BLe] cases), we can also find constant _boolean_
    expressions and evaluate them in-place. *)
(** ([BEq]と[BLe]の場合に)[fold_constants_aexp]を[bexp]
    に持ち上げることができるだけでなく、定数「ブール」式をみつけてその場で評価することもできます。*)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) =>
        if beq_nat n1 n2 then BTrue else BFalse
    | (a1', a2') =>
        BEq a1' a2'
    end
  | BLe a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) =>
        if leb n1 n2 then BTrue else BFalse
    | (a1', a2') =>
        BLe a1' a2'
    end
  | BNot b1  =>
    match (fold_constants_bexp b1) with
    | BTrue => BFalse
    | BFalse => BTrue
    | b1' => BNot b1'
    end
  | BAnd b1 b2  =>
    match (fold_constants_bexp b1, fold_constants_bexp b2)
    with
    | (BTrue, BTrue) => BTrue
    | (BTrue, BFalse) => BFalse
    | (BFalse, BTrue) => BFalse
    | (BFalse, BFalse) => BFalse
    | (b1', b2') => BAnd b1' b2'
    end
  end.

Example fold_bexp_ex1 :
    fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
  = BTrue.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
    fold_constants_bexp
      (BAnd (BEq (AId X) (AId Y))
            (BEq (ANum 0)
                 (AMinus (ANum 2) (APlus (ANum 1)
                                         (ANum 1)))))
  = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.

(*  To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions. *)
(** コマンド内の定数を畳み込みするために、含まれるすべての式に対応する畳み込み関数を適用します。*)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      =>
      SKIP
  | i ::= a  =>
      CAss i (fold_constants_aexp a)
  | c1 ;; c2  =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

(** *** *)
Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    (X ::= APlus (ANum 4) (ANum 5);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y))
             (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0)
             (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) 
     THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END)
  = (* After constant folding: *)
    (X ::= ANum 9;;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
       SKIP
     ELSE
       (Y ::= ANum 0)
     FI;;
     Y ::= ANum 0;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END).
Proof. reflexivity. Qed.

(* ################################################### *)
(*  ** Soundness of Constant Folding *)
(** ** 定数畳み込みの健全性 *)

(*  Now we need to show that what we've done is correct. *)
(** 上でやったことが正しいことを示さなければなりません。*)

(*  Here's the proof for arithmetic expressions: *)
(** 算術式に対する証明です: *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (APlus a1 a2)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(** **** 練習問題: ★★★, optional (fold_bexp_Eq_informal) *)
(*  Here is an informal proof of the [BEq] case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the [BLe] case of the formal proof (without looking at the
    [BEq] case, if possible).

   _Theorem_: The constant folding function for booleans,
   [fold_constants_bexp], is sound.

   _Proof_: We must show that [b] is equivalent to [fold_constants_bexp],
   for all boolean expressions [b].  Proceed by induction on [b].  We
   show just the case where [b] has the form [BEq a1 a2].

   In this case, we must show

       beval st (BEq a1 a2)
     = beval st (fold_constants_bexp (BEq a1 a2)).

   There are two cases to consider:

     - First, suppose [fold_constants_aexp a1 = ANum n1] and
       [fold_constants_aexp a2 = ANum n2] for some [n1] and [n2].

       In this case, we have

           fold_constants_bexp (BEq a1 a2)
         = if beq_nat n1 n2 then BTrue else BFalse

       and

           beval st (BEq a1 a2)
         = beq_nat (aeval st a1) (aeval st a2).

       By the soundness of constant folding for arithmetic
       expressions (Lemma [fold_constants_aexp_sound]), we know

           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1

       and

           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,

       so

           beval st (BEq a1 a2)
         = beq_nat (aeval a1) (aeval a2)
         = beq_nat n1 n2.

       Also, it is easy to see (by considering the cases [n1 = n2] and
       [n1 <> n2] separately) that

           beval st (if beq_nat n1 n2 then BTrue else BFalse)
         = if beq_nat n1 n2 then beval st BTrue else beval st BFalse
         = if beq_nat n1 n2 then true else false
         = beq_nat n1 n2.

       So

           beval st (BEq a1 a2)
         = beq_nat n1 n2.
         = beval st (if beq_nat n1 n2 then BTrue else BFalse),

       as required.

     - Otherwise, one of [fold_constants_aexp a1] and
       [fold_constants_aexp a2] is not a constant.  In this case, we
       must show

           beval st (BEq a1 a2)
         = beval st (BEq (fold_constants_aexp a1)
                         (fold_constants_aexp a2)),

       which, by the definition of [beval], is the same as showing

           beq_nat (aeval st a1) (aeval st a2)
         = beq_nat (aeval st (fold_constants_aexp a1))
                   (aeval st (fold_constants_aexp a2)).

       But the soundness of constant folding for arithmetic
       expressions ([fold_constants_aexp_sound]) gives us

         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),

       completing the case.  []
*)
(** ここに、ブール式の定数畳み込みに関する健全性の議論の[BEq]の場合の非形式的証明を示します。
    これを丁寧に読みその後の形式的証明と比較しなさい。
    次に、形式的証明の[BLe]部分を(もし可能ならば[BEq]の場合を見ないで)記述しなさい。

   「定理」:ブール式に対する定数畳み込み関数[fold_constants_bexp]は健全である。

   「証明」:すべてのブール式[b]について[b]が[fold_constants_bexp]
   と同値であることを示す。
   [b]についての帰納法を行う。
   [b]が[BEq a1 a2]という形の場合を示す。

   この場合、
       beval st (BEq a1 a2)
     = beval st (fold_constants_bexp (BEq a1 a2)).
   を示せば良い。これには2種類の場合がある:

     - 最初に、ある[n1]と[n2]について、[fold_constants_aexp a1 = ANum n1]かつ
       [fold_constants_aexp a2 = ANum n2]と仮定する。

       この場合、
           fold_constants_bexp (BEq a1 a2)
         = if beq_nat n1 n2 then BTrue else BFalse
       かつ
           beval st (BEq a1 a2)
         = beq_nat (aeval st a1) (aeval st a2).
       となる。
       算術式についての定数畳み込みの健全性(補題[fold_constants_aexp_sound])より、
           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1
       かつ
           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,
       である。
       従って、
           beval st (BEq a1 a2)
         = beq_nat (aeval a1) (aeval a2)
         = beq_nat n1 n2.
       となる。また、([n1 = n2]と[n1 <> n2]の場合をそれぞれ考えると)
           beval st (if beq_nat n1 n2 then BTrue else BFalse)
         = if beq_nat n1 n2 then beval st BTrue else beval st BFalse
         = if beq_nat n1 n2 then true else false
         = beq_nat n1 n2.
       となることは明らかである。
       ゆえに
           beval st (BEq a1 a2)
         = beq_nat n1 n2.
         = beval st (if beq_nat n1 n2 then BTrue else BFalse),
       となる。これは求められる性質である。

     - それ以外の場合、[fold_constants_aexp a1]と[fold_constants_aexp a2]
       のどちらかは定数ではない。この場合、
           beval st (BEq a1 a2)
         = beval st (BEq (fold_constants_aexp a1)
                         (fold_constants_aexp a2)),
       を示せば良い。
       [beval]の定義から、これは    
           beq_nat (aeval st a1) (aeval st a2)
         = beq_nat (aeval st (fold_constants_aexp a1))
                   (aeval st (fold_constants_aexp a2)).
       を示すことと同じである。
       算術式についての定数畳み込みの健全性([fold_constants_aexp_sound])より、
         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),
       となり、この場合も成立する。[]
*)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* BTrue and BFalse are immediate *)
    try reflexivity.
  - (* BEq *)
    rename a into a1. rename a0 into a2. simpl.

    (* (Doing induction when there are a lot of constructors makes
        specifying variable names a chore, but Coq doesn't always
        choose nice variable names.  We can rename entries in the
        context with the [rename] tactic: [rename a into a1] will
        change [a] to [a1] in the current goal and context.) *)
    (** (多くのコンストラクタがある場合にinductionを実行すると、変数を特定することが面倒になりますが、 Coqは常にナイスな名前を選んでくれるとは限りません。コンテキストのエントリの名前を[rename]タクティックと使うことで変えることが出来ます。 [rename a into a1]とすると、現在のゴールとコンテキストにある[a]を[a1]に変えてくれるでしょう) *)
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.

      (* The only interesting case is when both a1 and a2
          become constants after folding *)
      (** 興味深い唯一のケースは、a1とa2の両方が折り畳み後に定数になる場合です。*)
      simpl. destruct (beq_nat n n0); reflexivity.
  - (* BLe *)
    (* FILL IN HERE *) admit.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★ (fold_constants_com_sound) *)
(*  Complete the [WHILE] case of the following proof. *)
(** 次の証明の[WHILE]の場合を完成させなさい。*)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* IFB *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).

      (*  (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].) *)
      (** もし最適化がifを削除しないならば、結果はIHと[fold_constants_bexp_sound]から直ちに証明出来ます。 *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  - (* WHILE *)
    (* FILL IN HERE *) Admitted.
(** [] *)

(* ########################################################## *)
(* *** Soundness of (0 + n) Elimination, Redux *)
(** *** (0 + n)の消去の健全性、再び *)

(** **** 練習問題: ★★★★, optional (optimize_0plus) *)
(* Recall the definition [optimize_0plus] from Imp.v:

    Fixpoint optimize_0plus (e:aexp) : aexp :=
      match e with
      | ANum n =>
          ANum n
      | APlus (ANum 0) e2 =>
          optimize_0plus e2
      | APlus e1 e2 =>
          APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 =>
          AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 =>
          AMult (optimize_0plus e1) (optimize_0plus e2)
      end.

   Note that this function is defined over the old [aexp]s,
   without states.

   Write a new version of this function that accounts for variables,
   plus analogous ones for [bexp]s and commands:

     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com

   Prove that these three functions are sound, as we did for
   [fold_constants_*].  Make sure you use the congruence lemmas in
   the proof of [optimize_0plus_com] -- otherwise it will be _long_!

   Then define an optimizer on commands that first folds
   constants (using [fold_constants_com]) and then eliminates [0 + n]
   terms (using [optimize_0plus_com]).

   - Give a meaningful example of this optimizer's output.

   - Prove that the optimizer is sound.  (This part should be _very_
     easy.)  *)
(** Imp_J.vの[optimize_0plus]の定義をふり返ります。
    Fixpoint optimize_0plus (e:aexp) : aexp :=
      match e with
      | ANum n =>
          ANum n
      | APlus (ANum 0) e2 =>
          optimize_0plus e2
      | APlus e1 e2 =>
          APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 =>
          AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 =>
          AMult (optimize_0plus e1) (optimize_0plus e2)
      end.
   この関数は、[aexp]の上で定義されていて、状態を扱わないことに注意します。

   変数を扱えるようにした、この関数の新しいバージョンを記述しなさい。
   また、[bexp]およびコマンドに対しても、同様のものを記述しなさい:

     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com

   これらの関数の健全性を、[fold_constants_*]について行ったのと同様に証明しなさい。
   [optimize_0plus_com]の証明においては、合同性補題を確実に使いなさい
   そうしなければ証明はとても長くなるでしょう!

   次に、コマンドに対して次の処理を行う最適化関数を定義しなさい。行うべき処理は、
   まず定数畳み込みを([fold_constants_com]を使って)行い、
   次に[0 + n]項を([optimize_0plus_com]を使って)消去することです。

   - この最適化関数の出力の意味のある例を示しなさい。

   - この最適化関数が健全であることを示しなさい。(この部分は「とても」簡単なはずです。) *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(* * Proving That Programs Are _Not_ Equivalent *)
(** * プログラムが同値でないことを証明する *)

(*  Suppose that [c1] is a command of the form [X ::= a1; Y ::= a2]
    and [c2] is the command [X ::= a1; Y ::= a2'], where [a2'] is
    formed by substituting [a1] for all occurrences of [X] in [a2].
    For example, [c1] and [c2] might be:

       c1  =  (X ::= 42 + 53;;
               Y ::= Y + X)
       c2  =  (X ::= 42 + 53;;
               Y ::= Y + (42 + 53))

    Clearly, this _particular_ [c1] and [c2] are equivalent.  Is this
    true in general? *)
(** [c1]が[X ::= a1; Y ::= a2]という形のコマンドで、
    [c2]がコマンド[X ::= a1; Y ::= a2']であると仮定します。ただし[a2']は、
    [a2]の中のすべてのXを[a1]で置換したものとします。
    例えば、[c1]と[c2]は次のようなものです。
       c1  =  (X ::= 42 + 53;
               Y ::= Y + X)
       c2  =  (X ::= 42 + 53;;
               Y ::= Y + (42 + 53))
    明らかに、この例の場合は[c1]と[c2]は同値です。
    しかし、一般にそうだと言えるでしょうか？ *)

(*  We will see in a moment that it is not, but it is worthwhile
    to pause, now, and see if you can find a counter-example on your
    own. *)
(** この後すぐ、そうではないことを示します。
    しかし、ここでちょっと立ち止まって、
    自分の力で反例を見つけることができるか試してみるのは意味があることです。 *)

(* Here, formally, is the function that substitutes an arithmetic
    expression for each occurrence of a given variable in another
    expression: *)
(** 次が、式の中の指定された変数を別の算術式で置換する関数の形式的定義です。*)

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId i'       =>
      if beq_id i i' then u else AId i'
  | APlus a1 a2  =>
      APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2  =>
      AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53))
             (APlus (AId Y) (AId X)) 
= (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity.  Qed.

(*  And here is the property we are interested in, expressing the
    claim that commands [c1] and [c2] as described above are
    always equivalent.  *)
(** そして次が、興味対象の性質です。
    上記コマンド[c1]と[c2]が常に同値であることを主張するものです。*)

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

(*  Sadly, the property does _not_ always hold.

    _Theorem_: It is not the case that, for all [i1], [i2], [a1],
    and [a2],

         cequiv (i1 ::= a1;; i2 ::= a2)
                (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

    _Proof_: Suppose, for a contradiction, that for all [i1], [i2],
    [a1], and [a2], we have

      cequiv (i1 ::= a1;; i2 ::= a2)
             (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

    Consider the following program:

         X ::= APlus (AId X) (ANum 1);; Y ::= AId X

    Note that

         (X ::= APlus (AId X) (ANum 1);; Y ::= AId X)
         / empty_state \\ st1,

    where [st1 = { X |-> 1, Y |-> 1 }].

    By our assumption, we know that

        cequiv (X ::= APlus (AId X) (ANum 1);; Y ::= AId X)
               (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))

    so, by the definition of [cequiv], we have

        (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
        / empty_state \\ st1.

    But we can also derive

        (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
        / empty_state \\ st2,

    where [st2 = { X |-> 1, Y |-> 2 }].  Note that [st1 <> st2]; this
    is a contradiction, since [ceval] is deterministic!  [] *)
(** 残念ながら、この性質は、常には成立「しません」。

    「定理」:すべての[i1], [i2], [a1], [a2]について、次が成立するわけではない:

         cequiv (i1 ::= a1;; i2 ::= a2)
                (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).
]]

    「証明」:仮にすべての[i1], [i2], [a1], [a2]について
      cequiv (i1 ::= a1;; i2 ::= a2)
             (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).
    が成立するとする。
    次のプログラムを考える:
         X ::= APlus (AId X) (ANum 1);; Y ::= AId X
    次のことに注意する:
         (X ::= APlus (AId X) (ANum 1);; Y ::= AId X)
         / empty_state \\ st1,
    ここで [st1 = { X |-> 1, Y |-> 1 }]である。

    仮定より、次が言える:
        cequiv (X ::= APlus (AId X) (ANum 1);; Y ::= AId X)
               (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
    すると、[cequiv]の定義より、次が言える:
        (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
        / empty_state \\ st1.
    しかし次のことも言える:
        (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
        / empty_state \\ st2,
    ただし[st2 = { X |-> 1, Y |-> 2 }]である。
    [st1 <> st2]に注意すると、これは[ceval]が決定性を持つことに矛盾する!
      [] *)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent... *)
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= AId X)
      as c1.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  (* ... allows us to show that the command [c2] can terminate
     in two different final states:
        st1 = {X |-> 1, Y |-> 1}
        st2 = {X |-> 1, Y |-> 2}. *)
  remember (t_update (t_update empty_state X 1) Y 1) as st1.
  remember (t_update (t_update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state \\ st1);
  assert (H2: c2 / empty_state \\ st2);
  try (subst;
       apply E_Seq with (st' := (t_update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.  Qed.

(** **** 練習問題: ★★★★ (better_subst_equiv) *)
(*  The equivalence we had in mind above was not complete nonsense --
    it was actually almost right.  To make it correct, we just need to
    exclude the case where the variable [X] occurs in the
    right-hand-side of the first assignment statement. *)
(** 上で成立すると考えていた同値は、完全に意味がないものではありません。
    それは実際、ほとんど正しいのです。それを直すためには、
    最初の代入の右辺に変数[X]が現れる場合を排除すれば良いのです。*)

Inductive var_not_used_in_aexp (X:id) : aexp -> Prop :=
  | VNUNum: forall n, var_not_used_in_aexp X (ANum n)
  | VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (APlus a1 a2)
  | VNUMinus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMinus a1 a2)
  | VNUMult: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMult a1 a2).

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (t_update st i ni) a = aeval st a.
Proof.
  (* FILL IN HERE *) Admitted.

(*  Using [var_not_used_in_aexp], formalize and prove a correct version
    of [subst_equiv_property]. *)
(** [var_not_used_in_aexp]を使って、[subst_equiv_property]の正しいバージョンを形式化し、
    証明しなさい。*)

(* FILL IN HERE *)
(** [] *)

(** **** 練習問題: ★★★, recommended (inequiv_exercise)  *)
(*  Prove that an infinite loop is not equivalent to [SKIP] *)
(** 無限ループは、[SKIP]と等しくないことを証明しなさい *)

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################## *)
(*  * Extended Exercise: Nondeterministic Imp *)
(** * 発展的練習問題: 非決定性を持つ Imp *)

(*  As we have seen (in theorem [ceval_deterministic] in the [Imp]
    chapter), Imp's evaluation relation is deterministic.  However,
    _non_-determinism is an important part of the definition of many
    real programming languages. For example, in many imperative
    languages (such as C and its relatives), the order in which
    function arguments are evaluated is unspecified.  The program
    fragment
(** これまでに([Imp]の章の[ceval_deterministric]の定理で)見て来たように、
Impの評価関係は決定的でした。しかしながら、非決定性は多くの現実のプログラミング
言語の定義の重要な部分を形成しています。例えば、多くの命令型言語(C言語やそれに類似した)において、
引数が評価される順序は未定義です。プログラムの断片の

      x = 0;;
      f(++x, x)
*)(*
    might call [f] with arguments [(1, 0)] or [(1, 1)], depending how
    the compiler chooses to order things.  This can be a little
    confusing for programmers, but it gives the compiler writer useful
    freedom.
*)(**
    [f]の呼び出しは、引数[(1,0)]または、[(1,1)]で行なわれるかもしれず、
    コンパイラがどうやって順序を選択するかに依存しています。このことは、
    プログラマにとって、ちょっとした悩みのタネですが、コンパイラ作者には
    自由が与えられます。
*)(*
    In this exercise, we will extend Imp with a simple
    nondeterministic command and study how this change affects
    program equivalence.  The new command has the syntax [HAVOC X],
    where [X] is an identifier. The effect of executing [HAVOC X] is
    to assign an _arbitrary_ number to the variable [X],
    nondeterministically. For example, after executing the program:
*)(** 
    この練習問題では、Impに簡単な非決定性のコマンドを追加してプログラムの同値性に
    どんな影響があるかを研究することです。新しいコマンドは[HAVOC X]という文法を持ち、
    [X]は識別子です。[HAVOC X]を実行することの影響は、任意の数が、変数[X]に非決定的に
    割り当てられることです。たとえば、次のプログラムを実行すると:

      HAVOC Y;;
      Z ::= Y * 2
*)(*
    the value of [Y] can be any number, while the value of [Z] is
    twice that of [Y] (so [Z] is always even). Note that we are not
    saying anything about the _probabilities_ of the outcomes -- just
    that there are (infinitely) many different outcomes that can
    possibly happen after executing this nondeterministic code.
*)(**
    [Y]の値はどんな数でもありえます。その一方で、[Z]は[Y]の値の倍の値です(そのため
    [Z]は常に偶数です)。出力が可能かどうかについて何も言ってないことに
    注意してください -- ただ、この非決定性のコードを実行したあとでは、
    多くの(無限に)異なる出力がありうるということだけです。
*)(*
    In a sense, a variable on which we do [HAVOC] roughly corresponds
    to an unitialized variable in a low-level language like C.  After
    the [HAVOC], the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made (and
    so it is good to leave it open to the compiler to choose whichever
    will run faster).

    We call this new language _Himp_ (``Imp extended with [HAVOC]''). *)
(**
    ある意味では、[HAVOC]することで得られる変数とは、Cのような低レベルな言語の
    未初期化変数と、ざっくり対応しています。[HAVOC]の後では、変数は固定されてはいるけれど任意の値を持ちます。
    言語の定義の中で非決定性の最も多い原因は、プログラマがどっちだろうと気にしないこと
    (そして、しないからこそ、コンパイラがより速くなるように選択する余地が残されているからです。)

    この新しい言語を_Himp_と呼びます。([HAVOC]拡張されたImpという意味です) *)

Module Himp.

(*  To formalize Himp, we first add a clause to the definition of
    commands. *)
(** Himpを形式化するために、コマンドの定義に一節加えます。*)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.                (* <---- new *)

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).

(** **** 練習問題: ★★ (himp_ceval) *)
(*  Now, we must extend the operational semantics. We have provided
   a template for the [ceval] relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of [ceval]
   to formalize the behavior of the [HAVOC] command? *)
(** ここで、操作的意味論を拡張しなければなりません。big-stepの意味論を満たす[ceval]関係をテンプレートとして
下に提示しておきます。[HAVOC]コマンドの振舞いを形式化するために、[ceval]の定義に
どんな規則を付け加えればよいでしょうか？ *)

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
      aeval st a1 = n ->
      (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = false ->
      c2 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
      beval st b1 = false -> 
      (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (WHILE b1 DO c1 END) / st' \\ st'' ->
      (WHILE b1 DO c1 END) / st \\ st''
(* FILL IN HERE *)

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

(*  As a sanity check, the following claims should be provable for
    your definition: *)
(** TODO *)

Example havoc_example1 : (HAVOC X) / empty_state \\ t_update empty_state X 0.
Proof.
(* FILL IN HERE *) Admitted.

Example havoc_example2 :
  (SKIP;; HAVOC Z) / empty_state \\ t_update empty_state Z 42.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(*  Finally, we repeat the definition of command equivalence from above: *)
(** TODO *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  c1 / st \\ st' <-> c2 / st \\ st'.

(*  Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. *)
(** この定義を非決定性プログラムの同値、非同値の証明に適用してみましょう。*)

(** **** 練習問題: ★★★, (havoc_swap)  *)
(** Are the following two programs equivalent? *)

Definition pXY :=
  HAVOC X;; HAVOC Y.

Definition pYX :=
  HAVOC Y;; HAVOC X.

(** If you think they are equivalent, prove it. If you think they are
    not, prove that. *)


Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★★, optional (havoc_copy)  *)
(** Are the following two programs equivalent? *)

Definition ptwice :=
  HAVOC X;; HAVOC Y.

Definition pcopy :=
  HAVOC X;; Y ::= AId X.

(*  If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the [assert] tactic
    useful.) *)
(** TODO *)

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(*  The definition of program equivalence we are using here has some
    subtle consequences on programs that may loop forever.  What
    [cequiv] says is that the set of possible _terminating_ outcomes
    of two equivalent programs is the same. However, in a language
    with nondeterminism, like Himp, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. The final part of the following exercise illustrates this
    phenomenon.
*)
(** TODO *)

(** **** 練習問題: ★★★★★, advanced (p1_p2_equiv)  *)
(*  Prove that [p1] and [p2] are equivalent. In this and the following
    exercises, try to understand why the [cequiv] definition has the
    behavior it has on these examples. *)
(** [p1]と[p2]が同値であることを証明しなさい。これと次の練習問題で、なぜ[cequiv]の定義がこれらの例において同じふるまいをするかを理解しなさい *)

Definition p1 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC Y;;
    X ::= APlus (AId X) (ANum 1)
  END.

Definition p2 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END.

(* Intuitively, the programs have the same termination
    behavior: either they loop forever, or they terminate in the
    same state they started in.  We can capture the termination
    behavior of [p1] and [p2] individually with these lemmas: *)
(** TODO *)

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ p1 / st \\ st'.
Proof. (* FILL IN HERE *) Admitted.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ p2 / st \\ st'.
Proof.
(* FILL IN HERE *) Admitted.

(*  You should use these lemmas to prove that [p1] and [p2] are actually
    equivalent. *)
(** TODO *)
Theorem p1_p2_equiv : cequiv p1 p2.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★★, advanced (p3_p4_inquiv)  *)
(*  Prove that the following programs are _not_ equivalent. *)
(** 次のプログラム群が同値ではないことを証明しなさい。*)

Definition p3 : com :=
  Z ::= ANum 1;;
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC X;;
    HAVOC Z
  END.

Definition p4 : com :=
  X ::= (ANum 0);;
  Z ::= (ANum 1).


Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★★★, advanced, optional (p5_p6_equiv)  *)

Definition p5 : com :=
  WHILE (BNot (BEq (AId X) (ANum 1))) DO
    HAVOC X
  END.

Definition p6 : com :=
  X ::= ANum 1.


Theorem p5_p6_equiv : cequiv p5 p6.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

End Himp.

(* ####################################################### *)
(* * Additional Exercises *)
(** * さらなる練習問題 *)

(** **** 練習問題: ★★★★, optional (for_while_equiv) *)
(* This exercise extends the optional [add_for_loop] exercise from
    the [Imp] chapter, where you were asked to extend the language 
    of commands with C-style [for] loops.  Prove that the command:

      for (c1 ; b ; c2) {
          c3
      }

    is equivalent to:

       c1 ;
       WHILE b DO
         c3 ;
         c2
       END
*)
(** この練習問題は、Imp_J.vのoptionalの練習問題 add_for_loop を拡張したものです。
    もとの add_for_loop は、コマンド言語に C-言語のスタイルの [for]ループを
    拡張しなさい、というものでした。
    ここでは次のことを証明しなさい:   
      for (c1 ; b ; c2) {
          c3
      }
    は
       c1 ;
       WHILE b DO
         c3 ;
         c2
       END
    と同値である。
*)
(* FILL IN HERE *)
(** [] *)

(** **** 練習問題: ★★★, optional (swap_noninterfering_assignments) *)
(*  (Hint: You'll need [functional_extensionality] for this one.) *)
(** (ヒント: [functional_extensionality]が必要になるでしょう。*)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    (l1 ::= a1;; l2 ::= a2)
    (l2 ::= a2;; l1 ::= a1).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★★, advanced, optional (capprox) *)

(** In this exercise we define an asymmetric variant of program
    equivalence we call _program approximation_. We say that a
    program [c1] _approximates_ a program [c2] when, for each of
    the initial states for which [c1] terminates, [c2] also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows: *)
(** TODO この練習問題では、プログラムの同値性の正反対の変奏を定義します。*)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  c1 / st \\ st' -> c2 / st \\ st'.

(*  For example, the program [c1 = WHILE X <> 1 DO X ::= X - 1 END]
    approximates [c2 = X ::= 1], but [c2] does not approximate [c1]
    since [c1] does not terminate when [X = 0] but [c2] does.  If two
    programs approximate each other in both directions, then they are
    equivalent. *)
(** TODO *)
(*  Find two programs [c3] and [c4] such that neither approximates
    the other. *)
(** TODO *)
Definition c3 : com := (* FILL IN HERE *) admit.
Definition c4 : com := (* FILL IN HERE *) admit.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof. (* FILL IN HERE *) Admitted.

(*  Find a program [cmin] that approximates every other program. *)
(** TODO *)

Definition cmin : com :=
  (* FILL IN HERE *) admit.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof. (* FILL IN HERE *) Admitted.

(*  Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right). *)
(** TODO *)

Definition zprop (c : com) : Prop :=
  (* FILL IN HERE *) admit.


Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** $Date: 2016-05-26 16:17:19 -0400 (Thu, 26 May 2016) $ *)

