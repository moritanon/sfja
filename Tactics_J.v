(*  * Tactics: More Basic Tactics *)
(** * タクティック: 基本的なタクティックについてもう少し *)

(*  This chapter introduces several additional proof strategies
    and tactics that allow us to begin proving more interesting
    properties of functional programs.  We will see:

    - how to use auxiliary lemmas in both "forward-style" and
      "backward-style" proofs;
    - how to reason about data constructors (in particular, how to use
      the fact that they are injective and disjoint);
    - how to strengthen an induction hypothesis (and when such
      strengthening is required); and
    - more details on how to reason by case analysis. *)
(* この章では、興味深い関数プログラムの特質を証明するのに便利な証明戦略とタクティックを幾つか紹介します。
 - "前向き"および、後ろ向きの証明における、補助定理の使いかた。
 - データコンストラクタについての推論。(特にそれらデータが単射であったり、互いに素であるという事実を使用するやりかた)
 - 帰納法の仮定(そのような強力さが必要である場合)の強化の仕方。
 - ケース分析による推論について詳しく。*)

Require Export Poly.

(* ################################################################# *)
(*  * The [apply] Tactic *)
(** * [apply] タクティック *)

(*  We often encounter situations where the goal to be proved is
    _exactly_ the same as some hypothesis in the context or some
    previously proved lemma. *)
(** 証明をしていると、証明すべきゴールがコンテキスト中の仮定と同じであったり以前証明した補題と同じ>であることがしばしばあります。*)
Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.

(*  At this point, we could finish with "[rewrite -> eq2.
    reflexivity.]" as we have done several times before.  We can
    achieve the same effect in a single step by using the [apply]
    tactic instead: *)
(* このような場合は、 "[rewrite -> eq2. reflexivity.]"
   として証明を終えてきましたが、 [apply] タクティックを使えば一回で同じ結果が得られます。*)
  apply eq2.  Qed.

(*  The [apply] tactic also works with _conditional_ hypotheses^
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)
(** また、 [apply] タクティックは、条件付きの仮定や補題にも使うことができます。適用するものに含意が
含まれていれば、含意の前提部分が証明すべきサブゴールに加えられます。*)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(*  You may find it instructive to experiment with this proof
    and see if there is a way to complete it using just [rewrite]
    instead of [apply]. *)
(** この証明で、 [apply] の代わりに [rewrite] を使って証明を終えられるか試してみると有益でしょう。*)

(*  Typically, when we use [apply H], the statement [H] will
    begin with a [forall] that binds some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)
(** [apply H] を使う典型的な例は、 [H] が [forall] で始まり、何らかの全称限量された変数を束縛している場合です。現在のゴールが [H] の帰結部と一致した場合には、変数に対応する適当な値を見つけてくれます。例えば、次の証明で [apply eq2] すると、 [eq2] 内の変数 [q] は [n] に、 [r] は [m] に具体化されます。*)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(*  **** Exercise: 2 stars, optional (silly_ex)  *)
(** **** 練習問題: ★★, optional (silly_ex) *)
(** Complete the following proof without using [simpl]. *)
(** 次の証明を [simpl] を使わずに完成させなさい。 *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal exactly -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)
(** [apply] タクティックを使う場合には、適用する事実（の帰結部）が、ゴールと完全に一致していなければなりません。例えは、等式の左辺と右辺が入れ替わっているだけでも [apply] タクティックは使えません。 *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.

(** Here we cannot use [apply] directly, but we can use the [symmetry]
    tactic, which switches the left and right sides of an equality in
    the goal. *)
(** ここで、[apply]を直接使うことは出来ませんが、[symmetry]タクティックを使って
ゴールの等式の左辺と右辺を入れ替えることができます。 *)
  symmetry.
  simpl. (* (This [simpl] is optional, since [apply] will perform
            simplification first, if needed *)
         (* この[simpl]はオプショナルなものですので、[apply]は必要ならば最初に簡約もしてくれます *)
  apply H.  Qed.

(*  **** Exercise: 3 stars (apply_exercise1)  *)
(** **** 練習問題: ★★★, (apply_exercise1) *)
(*  (_Hint_: You can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [Search] is
    your friend.) *)
(** ヒント: コンテスキト中の補題以外にも、以前に定義した補題を [apply] することができます。こんなときには [Search] を使うのでしたね。*)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star, optionalM (apply_rewrite)  *)
(** **** 練習問題: ★, optionalM (apply_rewrite) *)
(*  Briefly explain the difference between the tactics [apply] and
    [rewrite].  What are the situations where both can usefully be
    applied?
(* FILL IN HERE *)
*)
(** [apply] と [rewrite] の違いを簡単に説明しなさい。どちらもうまく使えるような場面はありますか？
(* FILL IN HERE *)
*)
(** [] *)

(* ################################################################# *)
(*  * The [apply ... with ...] Tactic *)
(** ** [apply ... with ...]タクティック *)

(** The following silly example uses two rewrites in a row to
    get from [[a,b]] to [[e,f]]. *)
(** 次の例は、[[a,b]]から[[e,f]]を得るためにrewriteを二回も使っており、少し要領が悪く思われます。 *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(*  Since this is a common pattern, we might like to pull it out
    as a lemma recording, once and for all, the fact that equality is
    transitive. *)
(** このようなことがよくあるため、同値性(等式)が推移的である事実を補題としておきます。 *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(*  Now, we should be able to use [trans_eq] to prove the above
    example.  However, to do this we need a slight refinement of the
    [apply] tactic. *)
(** そして、[trans_eq]をさきほどの証明に使ってみます。しかし、実際にやってみると[apply]タクティックに多少細工が必要なことがわかります。 *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.

(*  If we simply tell Coq [apply trans_eq] at this point, it can
    tell (by matching the goal against the conclusion of the lemma)
    that it should instantiate [X] with [[nat]], [n] with [[a,b]], and
    [o] with [[e,f]].  However, the matching process doesn't determine
    an instantiation for [m]: we have to supply one explicitly by
    adding [with (m:=[c,d])] to the invocation of [apply]. *)
(** ここで単純に[apply trans_eq]とすると（その補題の結論をゴールにマッチすることで）[X]を[[nat]]に、[n]を[[a,b]]に、[o]を[[e,f]]にあてはめようとします。しかしこのマッチングでは、[m]に何をあてはめるかを決めることができません。そこで、[with (m:=[c,d])]を明示的に情報として追加することで[apply]を動かします。 *)

  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.   Qed.

(** Actually, we usually don't have to include the name [m] in
    the [with] clause; Coq is often smart enough to figure out which
    instantiation we're giving. We could instead write: [apply
    trans_eq with [c;d]]. *)
(**  実際には、このように名前[m]を[with]に与えるということはそれほど多くありません。Coqは多くの場合賢く振舞って、我々の要求を実現してくれます。ちなみにこの上の[apply]はapply trans_eq with [c,d]と書くこともできます。 *)

(*  **** Exercise: 3 stars, optional (apply_with_exercise)  *)
(** **** 練習問題: ★★★, optional (apply_with_exercises) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(*  * The [inversion] Tactic *)
(** *  [inversion] タクティック *)

(*  Recall the definition of natural numbers:

     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.

    It is obvious from this definition that every number has one of
    two forms: either it is the constructor [O] or it is built by
    applying the constructor [S] to another number.  But there is more
    here than meets the eye: implicit in the definition (and in our
    informal understanding of how datatype declarations work in other
    programming languages) are two more facts:

    - The constructor [S] is _injective_.  That is, if [S n = S m], it
      must be the case that [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n]. *)
(** 自然数の定義を思い出してください。
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.
     この定義から、全ての数は二つの形式、コンストラクタ[O]で作られたか、コンストラクタ[S]に他の数値を与えて作られたかのどちらかであることは明白です。しかし両目を見開いてよく見ると、この定義（と、他のプログラミング言語で、データ型の定義がどのように働くか、という非形式的な理解）から、二つの暗黙的な事実が見つかります。
     - コンストラクタ[S]が単射であること。つまり、[S n = S m]となるためのただ一つの方法は[n = m]であること。

     - コンストラクタ[O]とコンストラクタ[S]は、互いに素であること。つまり、[O]はどんな[n]についても[S n]と等しくないということ。 *)

(*  Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor
    is injective and [nil] is different from every non-empty list.
    For booleans, [true] and [false] are different.  (Since neither
    [true] nor [false] take any arguments, their injectivity is not
    interesting.)  And so on. *)
(** 同じ原理が、全ての帰納的に定義された型にあてはまります。全てのコンストラクタは単射で、コンストラクタが違えば同じ値は生まれません。リストについて言えば[cons]コンストラクタは単射で、[nil]は全ての空でないリストと異なっています。[bool]型では、[true]と[false]は異なるものです（ただ、[true]も[false]も引数を取らないため、単射かどうか、という議論は興味深いものではありません）。 *)

(** Coq provides a tactic called [inversion] that allows us to
    exploit these principles in proofs. To see how to use it, let's
    show explicitly that the [S] constructor is injective: *)
(** Coqには、この性質を証明に利用する[inversion]というタクティックが用意されています。使い方を見るために、コンストラクタ[S]が単射であるという事実を明示的に示しましょう。*)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.

(*  By writing [inversion H] at this point, we are asking Coq to
    generate all equations that it can infer from [H] as additional
    hypotheses, replacing variables in the goal as it goes. In the
    present example, this amounts to adding a new hypothesis [H1 : n =
    m] and replacing [n] by [m] in the goal. *)
(** [inversion H]とここで書くことによって、Coqに全ての[H]から導出されうる等式が、 追加の仮説として生成されて、ゴール中の変数も置き換えられます。 実行中の例では、新しい仮説[H1 : n = m]が追加され、[n]が[m]に置き換えられます。*)
  inversion H. reflexivity.  Qed.

(*  Here's a more interesting example that shows how multiple
    equations can be derived at once. *)
(** ここに、複数の等式が一度に展開されるもっと面白い例があります。*)
Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

(*  We can name the equations that [inversion] generates with an
    [as ...] clause: *)
(** [inversion]が生成する等式に、[as ...]を使って名前をつけることも出来ます。 *)
Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H. inversion H as [Hnm]. reflexivity.  Qed.

(*  **** Exercise: 1 star (inversion_ex3)  *)
(** **** 練習問題: ★ (inversion_ex3) *)
Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  When used on a hypothesis involving an equality between
    _different_ constructors (e.g., [S n = O]), [inversion] solves the
    goal immediately. To see why this makes sense, consider the
    following proof: *)
(** 異なるコンストラクタを両端に含む等式(例 [S n = O])の仮定を使用する時に、[inversion]はゴールをただちに解決します。それはどんな意味であるかを見るために、次の証明について考えましょう。*)

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros n.

(*  We can proceed by case analysis on [n]. The first case is
    trivial. *)
(** [n]についての場合分けを使って証明をすすめます。最初のケースは簡単です。*)
  destruct n as [| n'].
  - (* n = 0 *)
    intros H. reflexivity.

(*  However, the second one doesn't look so simple: assuming
    [beq_nat 0 (S n') = true], we must show [S n' = 0], but the latter
    clearly contradictory!  The way forward lies in the assumption.
    After simplifying the goal state, we see that [beq_nat 0 (S n') =
    true] has become [false = true]: *)
(** しかし二番目のケースはそんなに単純に見えません。[beq_nat 0 (S n') = true]と仮定した場合、[S n' = 0]を示す必要がありますが、
これは明らかに矛盾しています！ 仮定のなかはそのままです。？？ ゴールの状態を単純化すると,[beq_nat 0 (S n')]が[false = true]になります。
  - (* n = S n' *)
    simpl.

(** If we use [inversion] on this hypothesis, Coq notices that
    the subgoal we are working on is impossible, and therefore removes
    it from further consideration. *)
(** 「inversion]をこの仮説に対して使用すると、Coqは、サブゴールが不可能であることを伝えてくれて、
それゆえサブゴールを熟慮の末に取り除きます。*)

    intros H. inversion H. Qed.

(*  This is an instance of a general logical principle known as
    the _principle of explosion_, which asserts that a contradiction
    entails anything, even false things.  For instance: *)
(** これは爆発原理として知られる論理学の一般的な原理の一つの例です。この原理は、矛盾からは全てが、偽の命題さえも導かれる。ということを示しています。*)

 
Theorem inversion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

(** If you find the principle of explosion confusing, remember
    that these proofs are not actually showing that the conclusion of
    the statement holds.  Rather, they are arguing that the situation
    described by the premise can never arise, so the implication is
    vacuous.  We'll explore the principle of explosion of more detail
    in the next chapter. *)
(** 爆発原理が分かり難いのでしたら、これらの証明は実際には、論述の結論が有効であることを示しているわけではないことを覚えておいて下さい。
もっと正確に言えば、前提によって描かれる状況は決して起こり得ないと言えます。すなわちその含意は空虚です。次の章でもっと細かく爆発原理について探っていくことにしましょう。*)

(*  **** Exercise: 1 star (inversion_ex6)  *)
(** **** 練習問題: ★ (inversion_ex6)  *)
Example inversion_ex6 : forall (X : Type)
                          (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** To summarize this discussion, suppose [H] is a hypothesis in the
    context or a previously proven lemma of the form

      c a1 a2 ... an = d b1 b2 ... bm

    for some constructors [c] and [d] and arguments [a1 ... an] and
    [b1 ... bm].  Then [inversion H] has the following effect:

    - If [c] and [d] are the same constructor, then, by the
      injectivity of this constructor, we know that [a1 = b1], [a2 =
      b2], etc.; [inversion H] adds these facts to the context, and
      tries to use them to rewrite the goal.

    - If [c] and [d] are different constructors, then the hypothesis
      [H] is contradictory, and the current goal doesn't have to be
      considered at all.  In this case, [inversion H] marks the
      current goal as completed and pops it off the goal stack. *)
(** 以上の議論をまとめると、[H]をコンテキスト中に現われる仮説、
    またはすでに証明された、次のような形をした補題とすると、
      c a1 a2 ... an = d b1 b2 ... bm

コンストラクタ [c]と[d]と引数[a1 ... an]と[b1 ... bn]を持っています。そのとき、[inversion H]は次のような効果を持ちます。

    - もし[c]と[d]が同じコンストラクタであるならば、このコンストラクタの単射性によって、[a1 = b1] [a2 = b2]..であることが分かります。
      [inversio H]はこれらの事実をコンテキストに加えます。そして、それらを使ってゴールを書き換えます。
    - [c]と[d]が異なるコンストラクタである場合、仮説[H]は矛盾していますので
    現在のゴールについて考える必要は全くありません。
    この場合、[Inversion H]は現在のゴールに終了マークをつけてゴールスタックから取り除きます。*)

(*  The injectivity of constructors allows us to reason that
    [forall (n m : nat), S n = S m -> n = m]. The converse of this
    implication is an instance of a more general fact about both
    constructors and functions, which we will find useful in a few
    places below: *)
(** コンストラクタの単射性が、[forall (n m : nat), S n = S m -> n = m]を示している一方で、
    この含意の反対がコンストラクタと関数についての一般的な事実の例です。
    このことはまた後の何箇所かで役立つことになるでしょう。*)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

(* ################################################################# *)
(*  * Using Tactics on Hypotheses *)
(** ** タクティックを仮定に使用する *)

(*  By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic [simpl in H] performs simplification in
    the hypothesis named [H] in the context. *)
(** デフォルトでは、ほとんどのタクティックはゴールの式に作用するだけで、コンテキストの内容には手を>付けません。しかしながら、ほとんどのタクティックは変数を付けることで同じ操作をコンテキストの式に行>うことができます。

    例えば、[simpl in H]というタクティックは、コンテキストの中の[H]と名前のついた仮定に対して簡約を
    します。 *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(*  Similarly, [apply L in H] matches some conditional statement
    [L] (of the form [L1 -> L2], say) against a hypothesis [H] in the
    context.  However, unlike ordinary [apply] (which rewrites a goal
    matching [L2] into a subgoal [L1]), [apply L in H] matches [H]
    against [L1] and, if successful, replaces it with [L2].

    In other words, [apply L in H] gives us a form of "forward
    reasoning": from [L1 -> L2] and a hypothesis matching [L1], it
    produces a hypothesis matching [L2].  By contrast, [apply L] is
    "backward reasoning": it says that if we know [L1->L2] and we are
    trying to prove [L2], it suffices to prove [L1].

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)
(** 同様に、[apply L in H]というタクティックは、ある条件式[L] ([L1 -> L2]といった形の)を、コンテキストにある仮定[H]に適用します。しかし普通の[apply]と異なるのは、[apply L in H]が、[H]が[L1]とマッチすることを調べ、それに成功したらそれを[L2]に書き換えることです。 

    言い換えると、[apply L in H]は、"前向きの推論"の形をとっているといえます。それは、[L1 -> L2]が与えられ、仮定と[L1]がマッチしたら、仮定は[L2]と同じと考えてよい、ということです。逆に、[apply L]は "逆向きの推論"であると言えます。それは、[L1->L2]であることが分かっていて、今証明しようとしているものが[L2]なら、[L1]を証明すればよいとすることです。

    以前やった証明の変種を挙げておきます。逆向きの推論ではなく、前向きの推論を進めましょう。 *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5  ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

(*  Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.
    If you've seen informal proofs before (for example, in a math or
    computer science class), they probably used forward reasoning.  In
    general, idiomatic use of Coq tends to favor backward reasoning,
    but in some situations the forward style can be easier to think
    about.  *)
(** 前向きの推論は、与えられたもの（前提や、すでに証明された定理）からスタートして、そのゴールを次々につなげていき、ゴールに達するまでそれを続けます。逆向きの証明は、ゴールからスタートし、そのゴールが結論となる前提を調べ、それを前提や証明済みの定理にたどりつくまで繰り返します。皆さんがこれまで（数学やコンピュータサイエンスの分野で）見てきた非形式的な証明は、おそらく前向きの証明であったのではないかと思います。一般にCoqでの証明は逆向きの推論となる傾向があります。しかし、状況によっては前向きの推論のほうが簡単で考えやすい、ということもあります。  *) 

(*  **** Exercise: 3 stars, recommended (plus_n_n_injective)  *)
(** **** 練習問題: ★★★, recommended (plus_n_n_injective) *)
(** Practice using "in" variants in this exercise.  (Hint: use
    [plus_n_Sm].) *)
(** 先に述べた"in"を使って次の証明をしなさい。(ヒント: [plus_n_Sm]が使えます。) *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Varying the Induction Hypothesis *)
(** * 帰納法の仮定の変更 *)

(** Sometimes it is important to control the exact form of the
    induction hypothesis when carrying out inductive proofs in Coq.
    In particular, we need to be careful about which of the
    assumptions we move (using [intros]) from the goal to the context
    before invoking the [induction] tactic.  For example, suppose
    we want to show that the [double] function is injective -- i.e.,
    that it maps different arguments to different results:

    Theorem double_injective: forall n m,
      double n = double m -> n = m.

    The way we _start_ this proof is a bit delicate: if we begin with

      intros n. induction n.

    all is well.  But if we begin it with

      intros n m. induction n.

    we get stuck in the middle of the inductive case... *)
(**
   ときどきCoqにおいて、帰納的な証明を実行する際に、仮定を展開することをコントロールすることが重要になることがあります。ゴールからコンテキストへ[induction]タクティックを使用する前に([intros]を使用して)仮定を移動する時は特に気をつける必要があります。例えば、[double]関数が単射である、すなわち、異なる引数で[double]を実行すれば異なる結果になるということ、を示したいとしましょう。
   
   Theorem double_injective: forall n m,
       double n = double m -> n = m.

   この証明を始める方法は少々デリケートです。

       intros n. induction n.

   で始めればうまくいきます。 しかし

       intros n m. induction n.

   で始めてしまうと、帰納段階の途中でつまってしまいます...*)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq.
  - (* n = S n' *) intros eq. destruct m as [| m'].
    + (* m = O *) inversion eq.
    + (* m = S m' *) apply f_equal.

(*  At this point, the induction hypothesis, [IHn'], does _not_ give us
    [n' = m'] -- there is an extra [S] in the way -- so the goal is
    not provable. *)
(** ここでつまってしまいました。  帰納法の仮定 [IHn']は n' = m' を与えてくれません。 --  余計なSがあります。 そのためゴールは証明不可能です。*)

      Abort.

(*  What went wrong? *)
(** 何がいけなかったのでしょうか? *)

(*  The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced [m] into the context --
    intuitively, we have told Coq, "Let's consider some particular [n]
    and [m]..." and we now have to prove that, if [double n = double
    m] for _these particular_ [n] and [m], then [n = m].

    The next tactic, [induction n] says to Coq: We are going to show
    the goal by induction on [n].  That is, we are going to prove, for
    _all_ [n], that the proposition

      - [P n] = "if [double n = double m], then [n = m]"

    holds, by showing

      - [P O]

         (i.e., "if [double O = double m] then [O = m]") and

      - [P n -> P (S n)]

        (i.e., "if [double n = double m] then [n = m]" implies "if
        [double (S n) = double m] then [S n = m]").

    If we look closely at the second statement, it is saying something
    rather strange: it says that, for a _particular_ [m], if we know

      - "if [double n = double m] then [n = m]"

    then we can prove

       - "if [double (S n) = double m] then [S n = m]".

    To see why this is strange, let's think of a particular [m] --
    say, [5].  The statement is then saying that, if we know

      - [Q] = "if [double n = 10] then [n = 5]"

    then we can prove

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    But knowing [Q] doesn't give us any help at all with proving
    [R]!  (If we tried to prove [R] from [Q], we would start with
    something like "Suppose [double (S n) = 10]..." but then we'd be
    stuck: knowing that [double (S n)] is [10] tells us nothing about
    whether [double n] is [10], so [Q] is useless.) *)
(**
  帰納法の仮定を導入した時点で [m] をコンテキストに導入してしまっていることが問題です。直感的に言う
と、これはCoqに「ある特定の [n] と [m] について考えよう」と教えるようなものです。そのため、この特定
の [n] と [m] について [double n = double m] ならば [n = m] を証明しなければなりません。

    次のタクティックス [induction n] はCoqに「このゴールの [n] に関する帰納法で示します」と伝えます
。 なので、命題

      - [P n]  =  "[double n = double m] ならば [n = m]"

    がすべての[n]について成り立つことを

      - [P O]

         (すなわち、"[double O = double m] ならば [O = m]")

      - [P n -> P (S n)]

        (すなわち、 "[double n = double m] ならば [n = m]" が成り立つならば "
        [double (S n) = double m] ならば [S n = m]").

    2つめの文を見ると、これは奇妙なことを言っています。 それによると特定の [m] について

      - "[double n = double m] ならば [n = m]"

    が成り立つならば

       - "[double (S n) = double m] ならば [S n = m]".

    が証明できることになります。

    これがどう奇妙かを説明するために、特定の [m] 、例えば [5] について考えてみましょう。 するとこの
文は

      - [Q] = "[double n = 10] ならば [n = 5]"

    が成り立つならば

      - [R] = "[double (S n) = 10] ならば [S n = 5]".

    が証明できると言っています。

    しかし [Q] を知っていても、[R]を証明するのには何の役にたちません! (もし [Q] から [R] を示そうと
すると「[double (S n) = 10]...を仮定すると...」のようなことを言わないといけませんが、これは途中でつ
まってしまいます。 [double (S n)] が [10] があることは、 [double n]が[10]であるかどうかについては何
も教えてくれません。なので[Q] はここでは役にたちません。)
 *)

(*  To summarize: Trying to carry out this proof by induction on [n]
    when [m] is already in the context doesn't work because we are
    then trying to prove a relation involving _every_ [n] but just a
    _single_ [m]. *)
(** まとめると、[m]がすでにコンテキストにある状態で[n]に関する帰納法による証明がうまくいかないのは、すべての[n]と単一の[m]の関係を示そうとしてしまうかからです。*)

(*  The good proof of [double_injective] leaves [m] in the goal
    statement at the point where the [induction] tactic is invoked on
    [n]: *)
(** [double_injective] のいい証明では、[induction]を[n]に対して使う時点では[m]をゴールに残しています。 *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq.

  - (* n = S n' *) simpl.

(*  Notice that both the goal and the induction hypothesis are
    different this time: the goal asks us to prove something more
    general (i.e., to prove the statement for _every_ [m]), but the IH
    is correspondingly more flexible, allowing us to choose any [m] we
    like when we apply the IH. *)
(** ゴールと帰納法の仮説の両方が異っていることに注意してください。ゴールはもっと一般的な何かを証明するかどうかを我々に尋ねます。(たとえば、全ての[m]についての文を証明するとか)一方IHは、我々
がIHを適用するとき、好きな[m]を選ぶことが出来るといった柔軟なものになります。 *)

    intros m eq.

(*  Now we've chosen a particular [m] and introduced the assumption
    that [double n = double m].  Since we are doing a case analysis on
    [n], we also need a case analysis on [m] to keep the two "in sync." *)
(** ここで我々は特定の[m]を選び、[double n = double m]という仮定を導入します。[n]についてのケース分析を行っているので、[m]についてのケース分析が、それぞれの[n]のケースで必要になります。*)

    destruct m as [| m'].
    + (* m = O *) simpl.

(*  The 0 case is trivial: *)
(** 0の場合は簡単です: *)

      inversion eq.

    + (* m = S m' *)
      apply f_equal.

(*  At this point, since we are in the second branch of the [destruct
    m], the [m'] mentioned in the context is the predecessor of the
    [m] we started out talking about.  Since we are also in the [S]
    branch of the induction, this is perfect: if we instantiate the
    generic [m] in the IH with the current [m'] (this instantiation is
    performed automatically by the [apply] in the next step), then
    [IHn'] gives us exactly what we need to finish the proof. *)
(** ここで、[destruct m]の二つ目のケースに我々はいます。[m']はこの時点のコンテキストのなかで言及されている[m']は実際、我々が言及を開始したものの一つ前のものです。もし、一般の[m]をIHの中で我
々がたった今言及した[m']を用いてインスタンス化する(このインスタンス化は[apply]を実行することで自動的に行われるのですが)ならば、 我々が証明を終らせるために必要なものを確かに与えてくれるでしょう。*)

      apply IHn'. inversion eq. reflexivity. Qed.

(*  What you should take away from all this is that we need to be
    careful about using induction to try to prove something too
    specific: If we're proving a property of [n] and [m] by induction
    on [n], we may need to leave [m] generic. *)
(** 帰納法によって証明しようとしていることが、限定的すぎないかに注意する必要があることを学びました。もし[n]と[m]の性質に関する証明を[n]に関する帰納法で行ないたい場合は、[m]を一般的なままにしておく必要があるかもしれません。 *)

(** The following exercise requires the same pattern. *)
(** 次の練習問題も同じ解法パターンが必要になります。*)

(** **** Exercise: 2 stars (beq_nat_true)  *)
(** **** 練習問題: ★★,  (beq_nat_true) *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advancedM (beq_nat_true_informal)  *)
(** **** 練習問題: ★★, advancedM (beq_nat_true_informal) *)
(** Give a careful informal proof of [beq_nat_true], being as explicit
    as possible about quantifiers. *)
(** [beq_nat_true]の 非形式的な証明を可能な限り、数量子について明示的に行いなさい。*)

(* FILL IN HERE *)
(** [] *)

(*  The strategy of doing fewer [intros] before an [induction] to
    obtain a more general IH doesn't always work by itself; sometimes
    a little _rearrangement_ of quantified variables is needed.
    Suppose, for example, that we wanted to prove [double_injective]
    by induction on [m] instead of [n]. *)
(** この戦略がいつもそのまま使えるわけではありません。ときには、ちょっとした工夫が必要です。 例えば、[double_injective]を[n]ではなく[m]に関する帰納法で示したいとします。 *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

(*  The problem is that, to do induction on [m], we must first
    introduce [n].  (If we simply say [induction m] without
    introducing anything first, Coq will automatically introduce [n]
    for us!)  *)
(**  [m]に関する帰納法の問題点は、最初に[n]をintroしなければいけないことです。 (もし何も導入せずに[induction m]をしても、Coqは自動的に[n]をintroします!) *)

(*  What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    works, but it's not nice: We don't want to have to twist the
    statements of lemmas to fit the needs of a particular strategy for
    proving them -- we want to state them in the most clear and
    natural way. *)
(** どうしたらいいでしょうか?     ありうる方法の一つは、補題の文を書き換えて[n]より先に[m]がくるようにすることです。 これはうまくいきますが、いい方法ではありません。特定の証明戦略のために補題の文をめちゃくちゃにしたくありません。補題の文はできるかぎり明確かつ自然な形であるべきです。*)

(*  What we can do instead is to first introduce all the quantified
    variables and then _re-generalize_ one or more of them,
    selectively taking variables out of the context and putting them
    back at the beginning of the goal.  The [generalize dependent]
    tactic does this. *)
(** その代わりに、いったんすべての限量変数を導入し、そのうちいくつかをコンテキストから取りゴールの先頭に置くことで、再び一般化します。これは[generalize dependent]タクティックスによって実現できます。 *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  (* ここで[n]はゴールに戻されて、[m]についての帰納法を行うことが出来、効率的に一般化された帰納仮定を得ら
れる。*)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

(** Let's look at an informal proof of this theorem.  Note that
    the proposition we prove by induction leaves [n] quantified,
    corresponding to the use of generalize dependent in our formal
    proof.

    _Theorem_: For any nats [n] and [m], if [double n = double m], then
      [n = m].

    _Proof_: Let [m] be a [nat]. We prove by induction on [m] that, for
      any [n], if [double n = double m] then [n = m].

      - First, suppose [m = 0], and suppose [n] is a number such
        that [double n = double m].  We must show that [n = 0].

        Since [m = 0], by the definition of [double] we have [double n =
        0].  There are two cases to consider for [n].  If [n = 0] we are
        done, since [m = 0 = n], as required.  Otherwise, if [n = S n']
        for some [n'], we derive a contradiction: by the definition of
        [double], we can calculate [double n = S (S (double n'))], but
        this contradicts the assumption that [double n = 0].

      - Second, suppose [m = S m'] and that [n] is again a number such
        that [double n = double m].  We must show that [n = S m'], with
        the induction hypothesis that for every number [s], if [double s =
        double m'] then [s = m'].

        By the fact that [m = S m'] and the definition of [double], we
        have [double n = S (S (double m'))].  There are two cases to
        consider for [n].

        If [n = 0], then by definition [double n = 0], a contradiction.

        Thus, we may assume that [n = S n'] for some [n'], and again by
        the definition of [double] we have [S (S (double n')) =
        S (S (double m'))], which implies by inversion that [double n' =
        double m'].  Instantiating the induction hypothesis with [n'] thus
        allows us to conclude that [n' = m'], and it follows immediately
        that [S n' = S m'].  Since [S n' = n] and [S m' = m], this is just
        what we wanted to show. [] *)
(**
この定理の非形式な証明を見てみましょう。なお [n]を限量化したまま帰納法によって命題を証明する箇所は、形式的な証明では generalize dependent を使う箇所に対応します。

_Theorem_: すべての自然数 [n] と [m] について、 [double n = double m] ならば [n = m]。

_Proof_: [m]を[nat]とする。 [m]に関する帰納法によって、 すべての[n] に対して [double n = double m] ならば [n = m] を示す。

  - 最初に [m = 0] と仮定し、[n] を [double n = double m] をみたす数とし、 [n = 0] を示す。
    [m = 0]なので、[double]の定義より[double n = 0]。
    [n] について2つの場合分けが考えれる。
    [n = 0] ならば、それが示したいことなので、すでに終了している。
    そうでなくて[n = S n']となる[n']が存在する場合、矛盾を導くことで証明する。
    [double]の定義により[n = S (S (double n'))]だが、これは仮定 [dobule n = 0] と矛盾する。

  - そうでない場合、[m = S m'] と仮定し、[n]は再び [double n = double m] をみたす数とする。 [n = S m']を示すために、 帰納法の仮定「 すべての数 [s] に対して [double s = double m']ならば[s = m']」を用いる。
    [m = S m']と[double]の定義により、[double n = S (S (double m'))]。 [n]に関して2つの場合分けが考えられる。

    [n = 0]ならば、定義により[double n = 0]となり、矛盾を導ける。

    なので、[n = S n']となる[n']があると仮定すると、再び[double]の定義により、
    [S (S (double n')) = S (S (double m'))]。 ここでinversionにより[double n' = dobule m']。
    帰納法の仮定を[n']をあてはめることで、[n' = m']という結論を導ける。
    [S n' = n]かつ[S m' = m]なので、これにより示せる。 []
*)

(*  Before we close this section and move on to some exercises, let's
    digress briefly and use [beq_nat_true] to prove a similar property
    about identifiers that we'll need in later chapters: *) 
(** このセクションを終える前に、いくつかの練習問題に移ることにしましょう。少し脱線して、[beq_nat_true]を使って、同様な後の章で必要になる識別子についての性質を証明しましょう: *)

Theorem beq_id_true : forall x y,
  beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply beq_nat_true. apply H. }
  rewrite H'. reflexivity.
Qed.

(*  **** Exercise: 3 stars, recommended (gen_dep_practice)  *)
(** **** 練習問題: ★★★ , recommended (gen_dep_practice) *)
(*  Prove this by induction on [l]. *)
(** [l]に関する帰納法で以下を証明しましょう。 *)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, optional (app_length_cons)  *)
(** **** 練習問題: ★★★, optional (app_length_cons) *)
(*  Prove this by induction on [l1], without using [app_length]
    from [Lists]. *)
(** [l1]に関する帰納法を用いて証明しなさい。また、[app_length]は使用しないこと *)

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X)
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 4 stars, optional (app_length_twice)  *)
(** **** 練習問題: ★★★★, optional (app_length_twice) *)
(*  Prove this by induction on [l], without using [app_length] from [Lists]. *)
(** [l]に関する帰納法を用いて証明しなさい。また、[app_length]は使用しないこと *)

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, optional (double_induction)  *)
(** **** 練習問題: ★★★, optional (double_induction)  *)
(*  Prove the following principle of induction over two naturals. *)
(** 次の二つの自然数についての帰納法の原理を証明しなさい *)

Theorem double_induction: forall (P : nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(*  * Unfolding Definitions *)
(** * 定義の展開 *)

(*  It sometimes happens that we need to manually unfold a Definition
    so that we can manipulate its right-hand side.  For example, if we
    define... *)
(** 右辺が操作出来るようにするために、定義を手動で展開することが必要になることがときどき起こります。例えば、以下のような定義をしたとします...*)

Definition square n := n * n.

(*  ... and try to prove a simple fact about [square]... *)
(** ...そして[square]に関する単純な事実を証明しようとします... *)

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.

(** ... we get stuck: [simpl] doesn't simplify anything at this point,
    and since we haven't proved any other facts about [square], there
    is nothing we can [apply] or [rewrite] with.

    To make progress, we can manually [unfold] the definition of
    [square]: *)
(** ここで行き詰まります: [simpl]はここで何も簡約してくれませんし、これまでに[square]に関する他のどんな事実も証明出来てないので、[apply]や[rewrite]出来る定理もありません。

証明を進めるために、[unfold]を手動で、[square]の定義を展開することが出来ます。*)

  unfold square.

(** Now we have plenty to work with: both sides of the equality are
    expressions involving multiplication, and we have lots of facts
    about multiplication at our disposal.  In particular, we know that
    it is commutative and associative, and from these facts it is not
    hard to finish the proof. *)
(** 今や出来ることはたっぷりあります: 同値式の両側は、かけ算を含む式であり、かけ算に関して自由に使えるたくさんの事実があります。 特に、可換性や推移性の事実があれば、証明を終らせるのに苦労することはないでしょう.*)
 
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

(*  At this point, a deeper discussion of unfolding and simplification
    is in order.

    You may already have observed that tactics like [simpl],
    [reflexivity], and [apply] will often unfold the definitions of
    functions automatically when it allows them to make progress.  For
    example, if we define [foo m] to be the constant [5], *)
(** この時点で、unfoldingや簡約のより深い議論は順序よく行なわれています。

すでに[simpl]や[reflexivity]や[apply]のようなタクティックが定義や関数の展開を自動的にしばしば行なうのを見て来られたかもしれません。
例えば、定数[5]である[foo m]を定義したとしましょう。*)

Definition foo (x: nat) := 5.

(*  then the [simpl] in the following proof (or the [reflexivity], if
    we omit the [simpl]) will unfold [foo m] to [(fun x => 5) m] and
    then further simplify this expression to just [5]. *)
(** そのとき次の証明の[simpl](または、[simpl]を省略した場合の[reflexivity])で、[foo m]が[(fun x => 5) m]に展開されて、
さらにこの式がただの[5]にまで簡約されます。*)

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(*  However, this automatic unfolding is rather conservative.  For
    example, if we define a slightly more complicated function
    involving a pattern match... *)
(** しかしながら、この自動的な展開はむしろ保守的なものです。たとえば、パターンマッチを含むもう少し複雑な関数を定義したとします。*)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(*  ...then the analogous proof will get stuck: *)
(** ...その似たような証明は行き詰まります。*)

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

(** The reason that [simpl] doesn't make progress here is that it
    notices that, after tentatively unfolding [bar m], it is left with
    a match whose scrutinee, [m], is a variable, so the [match] cannot
    be simplified further.  (It is not smart enough to notice that the
    two branches of the [match] are identical.)  So it gives up on
    unfolding [bar m] and leaves it alone.  Similarly, tentatively
    unfolding [bar (m+1)] leaves a [match] whose scrutinee is a
    function application (that, itself, cannot be simplified, even
    after unfolding the definition of [+]), so [simpl] leaves it
    alone.

    At this point, there are two ways to make progress.  One is to use
    [destruct m] to break the proof into two cases, each focusing on a
    more concrete choice of [m] ([O] vs [S _]).  In each case, the
    [match] inside of [bar] can now make progress, and the proof is
    easy to complete. *)
(** [simpl]ではここで進展しない理由は、試しに[bar m]を展開した後で、変数である[m]がそのまま残されてしまい、[match]節をこれ以上簡約することが出来なくなるためです。
(二つの[match]の枝が実は同一であるということに気がついてくれるほどには賢くありません) そのため[bar m]を展開することを諦めて、そのままにしておくのです。
同様に、試しに[bar (m+1)]を展開することは、その[match]先が関数であるような[match]を適用します([+]の定義を展開したあとのような場合であっても
それ自身は簡単にはなりえません。) そのため、[simpl]をしても何も起こらないのです。

この時点で、証明をするめるための二つの方法があります。一つは、[destruct m]で証明を二つの場合に分けること、それぞれの場合は、
より具体的な[m]([O]vs[S _])に問題が移ります。それぞれの場合において、[bar]内部の[match]に対して証明を進められますし、
証明を終らせることは易しいでしょう。*)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(*  This approach works, but it depends on our recognizing that the
    [match] hidden inside [bar] is what was preventing us from making
    progress.

    A more straightforward way to finish the proof is to explicitly
    tell Coq to unfold [bar]. *)
(* このアプローチは動きますが、[bar]に隠された[match]は証明をすすめる上での障害であるなにかであるという認識に依存しています。

もっと直接に証明を終わらせる方法が、明示的に、Coqに[bar]をunfoldするように指示することなのです。*)
Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.

(*  Now it is apparent that we are stuck on the [match] expressions on
    both sides of the [=], and we can use [destruct] to finish the
    proof without thinking too hard. *)
(** 今や[=]の両側にある[match]式で詰っていることは明らかですので、[destruct]を使って証明を大して考えることなく終わらせることが出来ます。*)

  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

(* ###################################################### *)
(*  * Using [destruct] on Compound Expressions *)
(** * [destruct]を複合式で使う *)

(** We have seen many examples where [destruct] is used to
    perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)
(** ここまで[destruct]がいくつかの変数の値について場合分けを行う例をたくさん見てきました。しかし時には、ある式の結果についてケース分析をすることで証明を行う必要があります。このような場合にも[destruct]が使えます。


    例を見てください。 *)
Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    - (* beq_nat n 3 = true *) reflexivity.
    - (* beq_nat n 3 = false *) destruct (beq_nat n 5).
      + (* beq_nat n 5 = true *) reflexivity.
      + (* beq_nat n 5 = false *) reflexivity.  Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (beq_nat n 3) then ... else ...].  But either
    [n] is equal to [3] or it isn't, so we can use [destruct (beq_nat
    n 3)] to let us reason about the two cases.

    In general, the [destruct] tactic can be used to perform case
    analysis of the results of arbitrary computations.  If [e] is an
    expression whose type is some inductively defined type [T], then,
    for each constructor [c] of [T], [destruct e] generates a subgoal
    in which all occurrences of [e] (in the goal and in the context)
    are replaced by [c]. *)
(** 上の証明で[sillyfun]を展開すると、[if (beq_nat n 3) then ... else ...]で行き詰まることがわかります。そこで、[n]が[3]である場合とそうでない場合とに[destruct (beq_nat n 3)]を使って二つの場合に分け、証明を行います。

一般的に、[destruct]タクティックは任意の計算の結果の場合分けを行うために使用されます。もし[e]が式で、その式の型が帰納的に定義された型[T]であるような場合、[T]のそれぞれのコンストラクタ[c]について、[destruct e]は[e]のすべての文節に対応するサブゴールを生成し、、起こりえる全ての（ゴールやコンテキストにある）eの状態をコンストラクタcで網羅的に置き換えます。 *)

(** **** Exercise: 3 stars, optional (combine_split)  *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  However, [destruct]ing compound expressions requires a bit of
    care, as such [destruct]s can sometimes erase information we need
    to complete a proof. *)
(** しかし、複合式を[destruct]することは、ほんの少し注意が必要になります。[destruct]が証明を終わらせるのに必要な情報を消去するような場合があるからです。*)
(*  For example, suppose we define a function [sillyfun1] like
    this: *)
(**  例えば、次のような関数[sillyfun1]を定義したとします: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** Now suppose that we want to convince Coq of the (rather
    obvious) fact that [sillyfun1 n] yields [true] only when [n] is
    odd.  By analogy with the proofs we did with [sillyfun] above, it
    is natural to start the proof like this: *)
(** ここで、Coqに[sillyfun1 n]が、[n]が奇数のときだけ[true]となりうることを(当たり前に見えますが)納得させたいとします。先ほど[sillyfun]でやった証明を参考に類推すると、証明はこんな風に始まるのが自然に思えます。 *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* 詰まってしまった... *)
Abort.

(** We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution performed by [destruct] is too brutal -- it threw
    away every occurrence of [beq_nat n 3], but we need to keep some
    memory of this expression and how it was destructed, because we
    need to be able to reason that, since [beq_nat n 3 = true] in this
    branch of the case analysis, it must be that [n = 3], from which
    it follows that [n] is odd.

    What we would really like is to substitute away all existing
    occurences of [beq_nat n 3], but at the same time add an equation
    to the context that records which case we are in.  The [eqn:]
    qualifier allows us to introduce such an equation, giving it a
    name that we choose. *)
(** しかし証明はここで手詰まりになってしまいます。なぜなら、[destruct]を使ったことで、コンテキストからゴールまでたどりつくのに必要な情報がなくなってしまったからです。[destruct]は[beq_nat n 3]の結果起こる事象を全て投げ捨ててしまいますが、我々はそのうち少なくとも一つは残してもらわないと証明が進みません。このケースで必要なのは[beq_nat n 3 = true]で、ここから[n = 3]は明らかで、ここから[n]が奇数であることが導かれます。

実際のところやりたいことは[destruct]を[beq_nat n 3]に直接使ってこの式の結果起こることを全て置き換えてしまうことではなく、置き換えと同時にコンテキストに我々が今いるケースと等しいこと示す等式のレコードを追加してくれることです。[eqn:]という限定子があれば、そのような等式を導入することが出来ます。名前は何でもいいんですが *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra
     equality assumption, which is exactly what we need to
     make progress. *)
  (* ここで上記で詰ったのと同じところまで来ました。上記と違い、コンテキストには等式の形の仮定が追加されています。それを使って証明を進めることが出来ます。*)
    - (* e3 = true *) apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        [eqn:] again in the same way, allow us to finish the
        proof. *)
     (* 証明中の関数本体の二つ目の同値性のテストに来たとき、[eqn:]を再び同様に使用して証明を終らせることが出来ます。*)
      destruct (beq_nat n 5) eqn:Heqe5.
        + (* e5 = true *)
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) inversion eq.  Qed.

(*  **** Exercise: 2 stars (destruct_eqn_practice)  *)
(** **** 練習問題: ★★ (destruct_eqn_practicel) *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(*  * Review *)
(** * レビュー *)

(*  We've now seen many of Coq's most fundamental tactics.  We'll
    introduce a few more in the coming chapters, and later on we'll
    see some more powerful _automation_ tactics that make Coq help us
    with low-level details.  But basically we've got what we need to
    get work done.

    Here are the ones we've seen:

      - [intros]: move hypotheses/variables from goal to context

      - [reflexivity]: finish the proof (when the goal looks like [e =
        e])

      - [apply]: prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: apply a hypothesis, lemma, or constructor to
        a hypothesis in the context (forward reasoning)

      - [apply... with...]: explicitly specify values for variables
        that cannot be determined by pattern matching

      - [simpl]: simplify computations in the goal

      - [simpl in H]: ... or a hypothesis

      - [rewrite]: use an equality hypothesis (or lemma) to rewrite
        the goal

      - [rewrite ... in H]: ... or a hypothesis

      - [symmetry]: changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]: changes a hypothesis of the form [t=u] into
        [u=t]

      - [unfold]: replace a defined constant by its right-hand side in
        the goal

      - [unfold... in H]: ... or a hypothesis

      - [destruct... as...]: case analysis on values of inductively
        defined types

      - [destruct... eqn:...]: specify the name of an equation to be
        added to the context, recording the result of the case
        analysis

      - [induction... as...]: induction on values of inductively
        defined types

      - [inversion]: reason by injectivity and distinctness of
        constructors

      - [assert (H: e)] (or [assert (e) as H]): introduce a "local
        lemma" [e] and call it [H]

      - [generalize dependent x]: move the variable [x] (and anything
        else that depends on it) from the context back to an explicit
        hypothesis in the goal formula *)
(** ここまでに、たくさんの基本的なタクティックを見てきました。これだけあればしばらくの間は困らずに済
むはずです。この先数回のレクチャーで2～3新しいものが出てきますが、その先ではさらに強力な「自動化され
たタクティック」を紹介していきます。それを使うと、多くの低レベルな作業をCoqに処理してもらうことがで>
きます。しかし基本的に、皆さんはもう必要なことを知っていると考えていいでしょう。

    ここまでに出てきたタクティックの一覧です

      - [intros]:
        仮定や変数をゴールからコンテキストに移す

      - [reflexivity]:
        証明を完了させる（ゴールが[e = e]という形になっている場合）

      - [apply]:
        仮定、補助定理、コンストラクタを使ってゴールを証明する

      - [apply... in H]:
        仮定、補助定理、コンストラクタを使ってゴールを証明する（前向きの証明）

      - [apply... with...]:
        パターンマッチだけで決定できなかった変数を、特定の値に明示的に結びつける

      - [simpl]:
        ゴールの式を簡約する

      - [simpl in H]:
        ゴール、もしくは仮定Hの式を簡約する

      - [rewrite]:
        等式の形をした仮定（もしくは定理）を使い、ゴールを書き換える

      - [rewrite ... in H]:
        等式の形をした仮定（もしくは定理）を使い、ゴールや仮定を書き換える

      - [unfold]:
        定義された定数を、ゴールの右側の式で置き換える

      - [unfold... in H]:
        定義された定数を、ゴールや仮定の右側の式で置き換える

      - [destruct... as...]:
        帰納的に定義された型の値について、ケースごとに解析する

      - [destruct... eqn:...]:
        等式に名前を導入して、コンテキストに追加する。ケースごとの分析結果を記録する。

      - [induction... as...]:
        機能的に定義された型の値に帰納法を適用する

      - [inversion]:
        コンストラクタの単射性と独立性を利用して証明を行う

      - [assert (e) as H]:
        定義した補助定理(e)をHという名前でコンテキストに導入する

      - [generalize dependent x]:
        変数[x](とそれに依存する全て)をコンテキストからゴールの式中の明示的な仮説に戻す。
*)
(* ###################################################### *)
(*  * Additional Exercises *)
(** * 追加の練習問題  *)

(*  **** Exercise: 3 stars (beq_nat_sym)  *)
(** **** 練習問題: ★★★ (beq_nat_sym) *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, advanced, optional (beq_nat_sym_informal)  *)
(** **** 練習問題: ★★★, advanced, optional (beq_nat_sym_informal) *)
(** Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].
*)
(* この補題のあなたの形式的な証明に対応する非形式的な証明を与えなさい:
   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof:
   (* FILL IN HERE *)
[]
*)

(*  **** Exercise: 3 stars, optional (beq_nat_trans)  *)
(** **** 練習問題: ★★★, optional (beq_nat_trans) *)
Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, advanced (split_combine)  *)
(** **** 練習問題: ★★★, advanced (split_combine) *)
(** We proved, in an exercise above, that for all lists of pairs,
    [combine] is the inverse of [split].  How would you formalize the
    statement that [split] is the inverse of [combine]?  When is this
    property true?

    Complete the definition of [split_combine_statement] below with a
    property that states that [split] is the inverse of
    [combine]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split] [combine l1 l2 = (l1,l2)] to be true?)  *)
(* 我々はすでに、全ての型のリストのペアでcombineがsplitの逆関数であることを証明しました。ではその逆の「splitはcombineの逆関数である」を示すことはできるでしょうか？

   下記の[split]が[combine]の逆関数であることを述べる[split_combine_statement]の定義を完成させなさい
   。それから、その性質が正しいことを証明しなさい。（なるべくintrosを使うタイミングを遅らせ、帰納法の仮
   定を一般化させておくといいでしょう。 )
      ヒント: split combine l1 l2 = (l1,l2)がtrueとなるl1、l2の条件は何でしょう？ *)

Definition split_combine_statement : Prop :=
(* FILL IN HERE *) admit.

Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.


(** [] *)

(*  **** Exercise: 3 stars, advanced (filter_exercise)  *)
(** **** 練習問題: ★★★, advanced (filter_exercise) *)
(** This one is a bit challenging.  Pay attention to the form of your
    induction hypothesis. *)
(* This one is a bit challenging.  Pay attention to the form of your IH. *)
(** この問題は少し難しいかもしれません。上に上げる仮説の形に注意してください。*)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 4 stars, advanced, recommended (forall_exists_challenge)  *)
(** **** 練習問題: ★★★★, advanced (forall_exists_challenge) *)
(*  Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:

      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb evenb [0;2;4;5] = false

      forallb (beq_nat 5) [] = true

    The second checks whether there exists an element in the list that
    satisfies a given predicate:

      existsb (beq_nat 5) [0;2;3;6] = false

      existsb (andb true) [true;true;false] = true

      existsb oddb [1;0;0;0;0;3] = true

      existsb evenb [] = false

    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].

    Finally, prove a theorem [existsb_existsb'] stating that
    [existsb'] and [existsb] have the same behavior. *)
(** 二つの再帰関数[forallb]、[existsb]を定義しなさい。[forallb]は、リストの全ての要素が与えられた条>
件を満たしているかどうかを返します。:
      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb evenb [0;2;4;5] = false

      forallb (beq_nat 5) [] = true
    二つめのexistsbは、リストのなかに与えられた述語を満たす要素が一つ以上あるかどうかをチェックしま>
す。:
      existsb (beq_nat 5) [0;2;3;6] = false

      existsb (andb true) [true;true;false] = true

      existsb oddb [1;0;0;0;0;3] = true

      existsb evenb [] = false
    次に[existsb']を再帰関数としてではなく、[forallb]と[negb]を使って定義しなさい。.

    そして、[existsb']と[existsb]が同じ振る舞いをすることを証明しなさい。
*)
(* FILL IN HERE *)
(** [] *)

(** $Date: 2016-05-26 16:17:19 -0400 (Thu, 26 May 2016) $ *)
