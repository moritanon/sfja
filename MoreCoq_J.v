(** * MoreCoq_J:  CoqのTacticsについてもう少し*)

Require Export Poly_J.

(** This chapter introduces several more proof strategies and
    tactics that, together, allow us to prove theorems about the
    functional programs we have been writing. In particular, we'll
    reason about functions that work with natural numbers and lists.

    In particular, we will see:
    - how to use auxiliary lemmas, in both forwards and backwards reasoning;
    - how to reason about data constructors, which are injective and disjoint;
    - how to create a strong induction hypotheses (and when
      strengthening is required); and
    - how to reason by case analysis.
 *)
(** この章で、いくつかの証明戦略とタクティックを消化します。それによって、我々がこれまで書いてきた関数型プログラムについて、証明が容易になります。取り分け、自然数とリストについての関数について推論しやすくなるでしょう。

    - 前向き推論と後ろ向き推論の両方において、補題(補助的な証明)の使い方。
    - データコンストラクタについての推論をどのように行うか。 単射であったりお互いが素であることもあります。。
    - 強力な帰納法の仮定の生成の仕方。(強力さが求められる場合に。)
    - ケース分析による推論の仕方。
*)

(* ###################################################### *)
(** * The [apply] Tactic *)

(*  We often encounter situations where the goal to be proved is
    exactly the same as some hypothesis in the context or some
    previously proved lemma. *)
(** 証明をしていると、証明すべきゴールがコンテキスト中の仮定と同じであったり以前証明した補題と同じであることがしばしばあります。*)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with 
     "[rewrite -> eq2. reflexivity.]" as we have 
     done several times above. But we can achieve the
     same effect in a single step by using the 
     [apply] tactic instead: *)
(* このような場合は、
     "[rewrite -> eq2. reflexivity.]"
     として証明を終えてきましたが、 [apply] タクティックを使えば一回で同じ結果が得られます。*)
  apply eq2.  Qed.

(*  The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)
(** また、 [apply] タクティックは、条件付きの仮定や補題にも使うことができます。適用するものに含意が含まれていれば、含意の前提部分が証明すべきサブゴールに加えられます。*)

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
    begin with a [forall] binding some _universal variables_.  When
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

(** **** 練習問題: ★★, optional (silly_ex) *)
(* Complete the following proof without using [simpl]. *)
(** 次の証明を [simpl] を使わずに完成させなさい。 *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal _exactly_ -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)
(** [apply] タクティックを使う場合には、適用する事実（の帰結部）が、ゴールと完全に一致していなければなりません。例えは、等式の左辺と右辺が入れ替わっているだけでも [apply] タクティックは使えません。*)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* Here we cannot use [apply] directly *)
  (* ここでは[apply]が使えません。*)
Abort.

(* In this case we can use the [symmetry] tactic, which switches the
    left and right sides of an equality in the goal. *)
(** そのような場合には [symmetry] タクティックを使って、ゴールの等式の左辺と右辺を入れ替えることができます。 *)

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this [simpl] is unnecessary, since 
            [apply] will do a [simpl] step first. *)  
	(*  実際には、この [simpl] は必須ではありません。 [apply] は最初に [simpl] をします。 *)
  apply H.  Qed.         

(** **** 練習問題: ★★★, recommended (apply_exercise1) *)
(* Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)
(** ヒント: コンテスキト中の補題以外にも、以前に定義した補題を [apply] することができます。こんなときには [SearchAbout] を使うのでしたね。*)
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, optional (apply_rewrite) *)
(* Briefly explain the difference between the tactics [apply] and
    [rewrite].  Are there situations where both can usefully be
    applied? *)
(** [apply] と [rewrite] の違いを簡単に説明しなさい。どちらもうまく使えるような場面はありますか？
  (* FILL IN HERE *)
*)
(** [] *)


(* ###################################################### *)
(* * The [apply ... with ...] Tactic *)
(** ** [apply ... with ...]タクティック *)

(*  The following silly example uses two rewrites in a row to
    get from [[a,b]] to [[e,f]]. *)
(** 次の例は、[[a,b]]から[[e,f]]を得るためにrewriteを二回も使っており、少し要領が悪く思われます。 *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Since this is a common pattern, we might
    abstract it out as a lemma recording once and for all
    the fact that equality is transitive. *)
(** このようなことがよくあるため、等式が推移的である事実を補題としておきます。 *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. 
  reflexivity.  Qed.

(* Now, we should be able to use [trans_eq] to
    prove the above example.  However, to do this we need
    a slight refinement of the [apply] tactic. *)
(** そして、[trans_eq]をさきほどの証明に使ってみます。しかし、実際にやってみると[apply]タクティックに多少細工が必要なことがわかります。 *)	
	
Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  (* If we simply tell Coq [apply trans_eq] at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate [X]
     with [[nat]], [n] with [[a,b]], and [o] with [[e,f]].
     However, the matching process doesn't determine an
     instantiation for [m]: we have to supply one explicitly
     by adding [with (m:=[c,d])] to the invocation of
     [apply]. *)
   (* ここで単純に[apply trans_eq]とすると（その補題の結論をゴールにマッチすることで）[X]を[[nat]]に、[n]を[[a,b]]に、[o]を[[e,f]]にあてはめようとします。しかしこのマッチングでは、[m]に何をあてはめるかを決めることができません。そこで、[with (m:=[c,d])]を明示的に情報として追加することで[apply]を動かします。 *)
  apply trans_eq with (m:=[c;d]). apply eq1. apply eq2.   Qed.

(*  Actually, we usually don't have to include the name [m]
    in the [with] clause; Coq is often smart enough to
    figure out which instantiation we're giving. We could
    instead write: [apply trans_eq with [c,d]]. *)
(**  実際には、このように名前[m]を[with]に与えるということはそれほど多くありません。Coqは多くの場合賢く振舞って、我々の要求を実現してくれます。ちなみにこの上の[apply]はapply trans_eq with [c,d]と書くこともできます。 *)

(** **** 練習問題: ★★★, recommended (apply_with_exercises) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o). 
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################### *)
(* * The [inversion] tactic *)
(** *  [inversion] タクティック *)

(*  Recall the definition of natural numbers:
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.
    It is clear from this definition that every number has one of two
    forms: either it is the constructor [O] or it is built by applying
    the constructor [S] to another number.  But there is more here than
    meets the eye: implicit in the definition (and in our informal
    understanding of how datatype declarations work in other
    programming languages) are two other facts:

    - The constructor [S] is _injective_.  That is, the only way we can
      have [S n = S m] is if [n = m].

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
    constructors are never equal.  For lists, the [cons] constructor is
    injective and [nil] is different from every non-empty list.  For
    booleans, [true] and [false] are unequal.  (Since neither [true]
    nor [false] take any arguments, their injectivity is not an issue.) *)
(** 同じ原理が、全ての帰納的に定義された型にあてはまります。全てのコンストラクタは単射で、コンストラクタが違えば同じ値は生まれません。リストについて言えば[cons]コンストラクタは単射で、[nil]は全ての空でないリストと異なっています。[bool]型では、[true]と[false]は異なるものです（ただ、[true]も[false]も引数を取らないため、単射かどうか、という議論には意味がありません）。 *)
	
(*  Coq provides a tactic called [inversion] that allows us to exploit
    these principles in proofs.
 
    The [inversion] tactic is used like this.  Suppose [H] is a
    hypothesis in the context (or a previously proven lemma) of the
    form
      c a1 a2 ... an = d b1 b2 ... bm
    for some constructors [c] and [d] and arguments [a1 ... an] and
    [b1 ... bm].  Then [inversion H] instructs Coq to "invert" this
    equality to extract the information it contains about these terms:

    - If [c] and [d] are the same constructor, then we know, by the
      injectivity of this constructor, that [a1 = b1], [a2 = b2],
      etc.; [inversion H] adds these facts to the context, and tries
      to use them to rewrite the goal.

    - If [c] and [d] are different constructors, then the hypothesis
      [H] is contradictory.  That is, a false assumption has crept
      into the context, and this means that any goal whatsoever is
      provable!  In this case, [inversion H] marks the current goal as
      completed and pops it off the goal stack. *)
(** Coqには、この性質を証明に利用する[inversion]というタクティックが用意されています。

    [inversion]タクティックは、次のような場合に使います。コンテキストに以下のような形の仮定[H]（や過去に定義された補助定理）がある場合、
      c a1 a2 ... an = d b1 b2 ... bm
    これは、あるコンストラクタ[c]と[d]に、ある引数[a1 ... an]と[b1 ... bm]を与えて評価したものが等しいことを示していますが、
    このような時、[inversion H]とすることで、この等式を"反転"し、そこに含まれている情報を以下のようなやり方で引き出します。

    - もし[c]と[d]が同じコンストラクタの場合、すでに分かっているように、コンストラクタの単射性から、[a1 = b1], [a2 = b2]をが導かれます。
      また、[inversion H]はこの事実をコンテキストに追加し、ゴールの置き換えに使えないかを試します。

    - もし[c]と[d]が違うコンストラクタの場合、仮定[H]は矛盾していることになります。つまり、偽である前提がコンテキストに紛れ込んでいるということになり、これはどんなゴールも証明できてしまうことを意味します。このような場合、[inversion H]は現在のゴールが解決されたものとして、ゴールの一覧から取り除きます。 *)
	  
(*  The [inversion] tactic is probably easier to understand by
    seeing it in action than from general descriptions like the above.
    Below you will find example theorems that demonstrate the use of
    [inversion] and exercises to test your understanding. *)
(** [inversion]タクティックは、このような一般的な説明を読むより、その動きを実際に見てもらったほうが簡単に理解できるでしょう。以下は[inversion]の使い方を見てもらい、理解するための練習を兼ねた定理の例です。 *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity.  Qed.

(*  As a convenience, the [inversion] tactic can also
    destruct equalities between complex values, binding
    multiple variables as it goes. *)
(** 便利なように、[inversion]タクティックは、等式でつながった複合値を展開して、それぞれを対応する相手に結び付けてくれます。 *)

Theorem silly5 : forall (n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(** **** 練習問題: ★ (sillyex1) *)
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra.  Qed.

(** **** 練習問題: ★ (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* While the injectivity of constructors allows us to reason
    [forall (n m : nat), S n = S m -> n = m], the reverse direction of
    the implication is an instance of a more general fact about
    constructors and functions, which we will often find useful: *)
(** コンストラクタの単射性が、[forall (n m : nat), S n = S m -> n = m]を示している一方で、これを逆に適用することで、普通の等式の証明をすることができれば、これまで出てきたいくつかのケースにも使えるでしょう。 *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A), 
    x = y -> f x = f y. 
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed. 





(** **** 練習問題: ★★, optional (practice) *)
(** A couple more nontrivial but not-too-complicated proofs to work
    together in class, or for you to work as exercises. *)
(*二三の些細ではないけれどそれほど入り組んでもいない証明にクラスで一緒に、あるいは、練習として取り組んでみましょう。*) 

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################### *)
(* ** Using Tactics on Hypotheses *)
(** ** タクティックを仮定に使用する *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic [simpl in H] performs simplification in
    the hypothesis named [H] in the context. *)
(** デフォルトでは、ほとんどのタクティックはゴールの式に作用するだけで、コンテキストの内容には手を付けません。しかしながら、ほとんどのタクティックは変数を付けることで同じ操作をコンテキストの式に行うことができます。

    例えば、[simpl in H]というタクティックは、コンテキストの中の[H]と名前のついた仮定に対して簡約をします。 *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b. 
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** Similarly, the tactic [apply L in H] matches some
    conditional statement [L] (of the form [L1 -> L2], say) against a
    hypothesis [H] in the context.  However, unlike ordinary
    [apply] (which rewrites a goal matching [L2] into a subgoal [L1]),
    [apply L in H] matches [H] against [L1] and, if successful,
    replaces it with [L2].
 
    In other words, [apply L in H] gives us a form of "forward
    reasoning" -- from [L1 -> L2] and a hypothesis matching [L1], it
    gives us a hypothesis matching [L2].  By contrast, [apply L] is
    "backward reasoning" -- it says that if we know [L1->L2] and we
    are trying to prove [L2], it suffices to prove [L1].  

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)
(** 同様に、[apply L in H]というタクティックは、ある条件式[L] ([L1 -> L2]といった形の)を、コンテキストにある仮定[H]に適用します。しかし普通の[apply]と異なるのは、[apply L in H]が、[H]が[L1]とマッチすることを調べ、それに成功したらそれを[L2]に書き換えることです。

    言い換えると、[apply L in H]は、"前向きの推論"の形をとっているといえます。それは、[L1 -> L2]が与えられ、仮定と[L1]がマッチしたら、仮定は[L2]と同じと考えてよい、ということです。逆に、[apply L]は"逆向きの推論"であると言えます。それは、[L1->L2]であることが分かっていて、今証明しようとしているものが[L2]なら、[L1]を証明すればよいとすることです。

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
    general, Coq tends to favor backward reasoning, but in some
    situations the forward style can be easier to use or to think
    about.  *)
(** 前向きの推論は、与えられたもの（前提や、すでに証明された定理）からスタートして、そのゴールを次々につなげていき、ゴールに達するまでそれを続けます。逆向きの証明は、ゴールからスタートし、そのゴールが結論となる前提を調べ、それを前提や証明済みの定理にたどりつくまで繰り返します。皆さんがこれまで（数学やコンピュータサイエンスの分野で）見てきた非形式的な証明は、おそらく前向きの証明であったのではないかと思います。一般にCoqでの証明は逆向きの推論となる傾向があります。しかし、状況によっては前向きの推論のほうが簡単で考えやすい、ということもあります。  *)

(** **** 練習問題: ★★★, recommended (plus_n_n_injective) *)
(* Practice using "in" variants in this exercise. *)
(** 先に述べた"in"を使って次の証明をしなさい。 *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* Hint: use the plus_n_Sm lemma *)
	(* ヒント: 補題plus_n_Smを使用します *)
    (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Varying the Induction Hypothesis *)
(** * 帰納法の仮定の変更 *)

(** Sometimes it is important to control the exact form of the
    induction hypothesis when carrying out inductive proofs in Coq.
    In particular, we need to be careful about which of the
    assumptions we move (using [intros]) from the goal to the context
    before invoking the [induction] tactic.  For example, suppose 
    we want to show that the [double] function is injective -- i.e., 
    that it always maps different arguments to different results:  
    Theorem double_injective: forall n m, double n = double m -> n = m. 
    The way we _start_ this proof is a little bit delicate: if we 
    begin it with
      intros n. induction n.
]] 
    all is well.  But if we begin it with
      intros n m. induction n.
    we get stuck in the middle of the inductive case... *)
(** 
   ときどきCoqにおいて、帰納的な証明を実行する際に、仮定を展開することをコントロールすることが重要になることがあります。ゴールからコンテキストへ[induction]タクティックを使用する前に([intros]を使用して)仮定を移動する時は特に気をつける必要があります。例えば、[double]関数が単射である、すなわち、異なる引数で[double]を実行すれば異なる結果になるということ、を示したいとしましょう。
   Theorem double_injective: forall n m, double n = double m -> n = m.
   この証明を始める方法は少々デリケートです。
      intros n. induction n.
で始めればうまくいきます。 しかし
      intros n m. induction n.
で始めてしまうと、帰納段階の途中でつまってしまいます...
*)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = O". simpl. intros eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq. 
  Case "n = S n'". intros eq. destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'".  apply f_equal. 
      (* ここでつまってしまいました。  帰納法の仮定 [IHn']は n' = m' を与えてくれません。 --  邪魔で余計なSがあります。 そのためゴールは証明不可能です。*)
      Abort.

(* What went wrong? *)
(** 何がいけなかったのでしょうか? *)

(** The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced [m] into the context -- 
    intuitively, we have told Coq, "Let's consider some particular
    [n] and [m]..." and we now have to prove that, if [double n =
    double m] for _this particular_ [n] and [m], then [n = m].

    The next tactic, [induction n] says to Coq: We are going to show
    the goal by induction on [n].  That is, we are going to prove that
    the proposition

      - [P n]  =  "if [double n = double m], then [n = m]"

    holds for all [n] by showing

      - [P O]              

         (i.e., "if [double O = double m] then [O = m]")

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

    But knowing [Q] doesn't give us any help with proving [R]!  (If we
    tried to prove [R] from [Q], we would say something like "Suppose
    [double (S n) = 10]..." but then we'd be stuck: knowing that
    [double (S n)] is [10] tells us nothing about whether [double n]
    is [10], so [Q] is useless at this point.) *)
(**
  帰納法の仮定を導入した時点で [m] をコンテキストに導入してしまっていることが問題です。直感的に言うと、これはCoqに「ある特定の [n] と [m] について考えよう」と教えるようなものです。そのため、この特定の [n] と [m] について [double n = double m] ならば [n = m] を証明しなければなりません。

    次のタクティックス [induction n] はCoqに「このゴールの [n] に関する帰納法で示します」と伝えます。 なので、命題

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

    これがどう奇妙かを説明するために、特定の [m] 、例えば [5] について考えてみましょう。 するとこの文は

      - [Q] = "[double n = 10] ならば [n = 5]"

    が成り立つならば

      - [R] = "[double (S n) = 10] ならば [S n = 5]".

    が証明できると言っています。

    しかし [Q] を知っていても、[R]を証明するのには何の役にたちません! (もし [Q] から [R] を示そうとすると「[double (S n) = 10]...を仮定すると...」のようなことを言わないといけませんが、これは途中でつまってしまいます。 [double (S n)] が [10] があることは、 [double n]が[10]であるかどうかについては何も教えてくれません。なので[Q] はここでは役にたちません。)
 *)

(* To summarize: Trying to carry out this proof by induction on [n]
    when [m] is already in the context doesn't work because we are
    trying to prove a relation involving _every_ [n] but just a
    _single_ [m]. *)
(** まとめると、[m]がすでにコンテキストにある状態で[n]に関する帰納法による証明がうまくいかないのは、すべての[n]と単一の[m]の関係を示そうとしてしまうかからです。*)
	
(* The good proof of [double_injective] leaves [m] in the goal
    statement at the point where the [induction] tactic is invoked on
    [n]: *)
(** [double_injective] のいい証明では、[induction]を[n]に対して使う時点では[m]をゴールに残しています。 *)
Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq. 
  Case "n = S n'". 
    (* Notice that both the goal and the induction
       hypothesis have changed: the goal asks us to prove
       something more general (i.e., to prove the
       statement for _every_ [m]), but the IH is
       correspondingly more flexible, allowing us to
       choose any [m] we like when we apply the IH.  *)
	 (* ゴールと帰納法の仮説の両方が変更されたことに注意してください。ゴールはもっと一般的な何かを証明するかどうかを我々に尋ねます。(たとえば、全ての[m]についての文を証明するとか)一方IHは、我々がIHを適用するとき、好きな[m]を選ぶことが出来るといった柔軟なものになります。
	 *)
    intros m eq.
    (* Now we choose a particular [m] and introduce the
       assumption that [double n = double m].  Since we
       are doing a case analysis on [n], we need a case
       analysis on [m] to keep the two "in sync." *)
	 (*
	    ここで我々は特定の[m]を選び、[double n = double m]という仮定を導入します。[n]についてのケース分析を行っているので、[m]についてのケース分析が、それぞれの[n]のケースで必要になります。	 *)
    destruct m as [| m'].
    SCase "m = O". 
      (* The 0 case is trivial *)
      inversion eq.  
    SCase "m = S m'".  
      apply f_equal. 
      (* At this point, since we are in the second
         branch of the [destruct m], the [m'] mentioned
         in the context at this point is actually the
         predecessor of the one we started out talking
         about.  Since we are also in the [S] branch of
         the induction, this is perfect: if we
         instantiate the generic [m] in the IH with the
         [m'] that we are talking about right now (this
         instantiation is performed automatically by
         [apply]), then [IHn'] gives us exactly what we
         need to finish the proof. *)
	 (* ここで、[destruct m]の二つ目のケースに我々はいます。[m']はこの時点のコンテキストのなかで言及されている[m']は実際、我々が言及を開始したものの一つ前のものです。もし、一般の[m]をIHの中で我々がたった今言及した[m']を用いてインスタンス化する(このインスタンス化は[apply]を実行することで自動的に行われるのですが)ならば、
	 我々が証明を終らせるために必要なものを確かに与えてくれるでしょう。なに書いてんだかさっぱり*)
      apply IHn'. inversion eq. reflexivity. Qed.

(*  What this teaches us is that we need to be careful about using
    induction to try to prove something too specific: If we're proving
    a property of [n] and [m] by induction on [n], we may need to
    leave [m] generic. *)
(** 帰納法によって証明しようとしていることが、限定的すぎないかに注意する必要があることを学びました。
    もし[n]と[m]の性質に関する証明を[n]に関する帰納法で行ないたい場合は、[m]を一般的なままにしておく必要があるかもしれません。
*)
(* The proof of this theorem has to be treated similarly: *)
(* この定理の証明も同様の処理を行なう必要があります。*)
(** **** 練習問題: ★★,  (beq_nat_true) *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, advanced (beq_nat_true_informal) *)
(* Give a careful informal proof of [beq_nat_true], being as explicit
    as possible about quantifiers. *)
(** [beq_nat_true]の 非形式的な証明を可能な限り、数量子について明示的に行いなさい。*)
(* FILL IN HERE *)
(** [] *)


(* The strategy of doing fewer [intros] before an [induction] doesn't
    always work directly; sometimes a little _rearrangement_ of
    quantified variables is needed.  Suppose, for example, that we
    wanted to prove [double_injective] by induction on [m] instead of
    [n]. *)
(** この戦略がいつもそのまま使えるわけではありません。ときには、ちょっとした工夫が必要です。 例えば、[double_injective]を[n]ではなく[m]に関する帰納法で示したいとします。 *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq. 
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".  apply f_equal.
        (* Stuck again here, just like before. *)
		(* 以前と同じようにここでまた詰ります。*)
Abort.

(* The problem is that, to do induction on [m], we must first
    introduce [n].  (If we simply say [induction m] without
    introducing anything first, Coq will automatically introduce
    [n] for us!)   *)
(**  [m]に関する帰納法の問題点は、最初に[n]をintroしなければいけないことです。 (もし何も導入せずに[induction m]をしても、Coqは自動的に[n]をintroします!) *)
(*  What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    will work, but it's not nice: We don't want to have to mangle the
    statements of lemmas to fit the needs of a particular strategy for
    proving them -- we want to state them in the most clear and
    natural way. *)
(** どうしたらいいでしょうか?     ありうる方法の一つは、補題の文を書き換えて[n]より先に[m]がくるようにすることです。
   これはうまくいきますが、いい方法ではありません。
   特定の証明戦略のために補題の文をめちゃくちゃにしたくありません。
   補題の文はできるかぎり明確かつ自然な形であるべきです。*)
(*  What we can do instead is to first introduce all the
    quantified variables and then _re-generalize_ one or more of
    them, taking them out of the context and putting them back at
    the beginning of the goal.  The [generalize dependent] tactic
    does this. *)
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
  (* ここで[n]はゴールに戻されて、[m]についての帰納法を行うことが出来、効率的に一般化されたIHを得られる。*)
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

(* Let's look at an informal proof of this theorem.  Note that
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
    done, since this is what we wanted to show.  Otherwise, if [n = S
    n'] for some [n'], we derive a contradiction: by the definition of
    [double] we would have [double n = S (S (double n'))], but this
    contradicts the assumption that [double n = 0].

  - Otherwise, suppose [m = S m'] and that [n] is again a number such
    that [double n = double m].  We must show that [n = S m'], with
    the induction hypothesis that for every number [s], if [double s =
    double m'] then [s = m'].
 
    By the fact that [m = S m'] and the definition of [double], we
    have [double n = S (S (double m'))].  There are two cases to
    consider for [n].

    If [n = 0], then by definition [double n = 0], a contradiction.
    Thus, we may assume that [n = S n'] for some [n'], and again by
    the definition of [double] we have [S (S (double n')) = S (S
    (double m'))], which implies by inversion that [double n' = double
    m'].

    Instantiating the induction hypothesis with [n'] thus allows us to
    conclude that [n' = m'], and it follows immediately that [S n' = S
    m'].  Since [S n' = n] and [S m' = m], this is just what we wanted
    to show. [] *)
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



(*  Here's another illustration of [inversion] and using an
    appropriately general induction hypothesis.  This is a slightly
    roundabout way of stating a fact that we have already proved
    above.  The extra equalities force us to do a little more
    equational reasoning and exercise some of the tactics we've seen
    recently. *)
(** [inversion]と一般的な帰納法の仮定の適切な使用法をもう一つ示しておきましょう。これは既に上で証明した事実の遠回りして述べています。余分な等式があることで、等式の推論とこれまでに見て来たタクティックの練習になります。*)


Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l. induction l as [| v' l'].

  Case "l = []". 
    intros n eq. rewrite <- eq. reflexivity.

  Case "l = v' :: l'". 
    intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. apply IHl'. inversion eq. reflexivity. Qed.

(*  It might be tempting to start proving the above theorem
    by introducing [n] and [eq] at the outset.  However, this leads
    to an induction hypothesis that is not strong enough.  Compare
    the above to the following (aborted) attempt: *)
(** 上記の定理を証明するために、nとeqをコンテキストに上げてから始めてみたくなるかもしれません。しかし、これは、十分に強力でない帰納法の仮定につながります。上記の証明を次の(失敗する)試みとくらべてみましょう。
*)
Theorem length_snoc_bad : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l n eq. induction l as [| v' l'].

  Case "l = []". 
    rewrite <- eq. reflexivity.

  Case "l = v' :: l'". 
    simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. Abort. (* apply IHl'. *) (* IH が適用出来ない! *)


(*  As in the double examples, the problem is that by
    introducing [n] before doing induction on [l], the induction
    hypothesis is specialized to one particular natural number, namely
    [n].  In the induction case, however, we need to be able to use
    the induction hypothesis on some other natural number [n'].
    Retaining the more general form of the induction hypothesis thus
    gives us more flexibility.

    In general, a good rule of thumb is to make the induction hypothesis
    as general as possible. *)
(** doubleの例で見たように、問題は、[l]についての帰納法を始める前に、[n]をコンテキストに導入することです。そのため帰納法の仮定はある特定の[n]という名前の数に特化されてしまいました。しかし帰納法の場合には、他の数[n']についての帰納法の仮定を使えることが必要になります。 帰納法の仮定の一般化された形式を保ち続けることで、我々は柔軟に扱えるようになります。
*)
(** **** 練習問題: ★★★ (gen_dep_practice) *)
(*  Prove this by induction on [l]. *)
(** [l]に関する帰納法で以下を示しなさい。 *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★, advanced, optional (index_after_last_informal) *)
(*  Write an informal proof corresponding to your Coq proof
    of [index_after_last]:
 
     _Theorem_: For all sets [X], lists [l : list X], and numbers
      [n], if [length l = n] then [index n l = None].
 
     _Proof_:
     (* FILL IN HERE *)
[]
*)
(** **** 練習問題: ★★★, optional (index_after_last_informal) *)
(** [index_after_last]のCoqによる証明に対応する非形式的な証明を書きなさい。
     _Theorem_: すべてのSet [X], リスト [l : list X], 自然数[n]に対して、[length l = n] ならば [index (S n) l = None]。

     _Proof_:
     (* FILL IN HERE *)
[]
*)

(** **** 練習問題: ★★★, optional (gen_dep_practice_more) *)
(*  Prove this by induction on [l]. *)
(** [l]に関する帰納法で証明しなさい。 *)

Theorem length_snoc''' : forall (n : nat) (X : Type) 
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★, optional (app_length_cons) *)
(* Prove this by induction on [l1], without using [app_length]. *)
(** [l1]に関する帰納法を用いて証明しなさい。また、[app_length]は使用しないこと *)
Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) 
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★★, optional (app_length_twice) *)
(* Prove this by induction on [l], without using app_length. *)
(** [l]に関する帰納法を用いて証明しなさい。また、app_lengthは使用しないこと *)
Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


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
(** * Using [destruct] on Compound Expressions *)
(** * [destruct]を複合式で使う *)

(* We have seen many examples where the [destruct] tactic is
    used to perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)
(** ここまで[destruct]タクティックがいくつかの変数の値についてケース分析を行う例をたくさん見てきました。しかし時には、ある式の結果についてケース分析をすることで証明を行う必要があります。このような場合にも[destruct]タクティックが使えます。.

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
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.  Qed.

(*  After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (beq_nat n 3) then ... else ...].  Well,
    either [n] is equal to [3] or it isn't, so we use [destruct
    (beq_nat n 3)] to let us reason about the two cases. 

    In general, the [destruct] tactic can be used to perform case
    analysis of the results of arbitrary computations.  If [e] is an
    expression whose type is some inductively defined type [T], then,
    for each constructor [c] of [T], [destruct e] generates a subgoal
    in which all occurrences of [e] (in the goal and in the context)
    are replaced by [c].

*)

(** 上の証明で[sillyfun]を展開すると、[if (beq_nat n 3) then ... else ...]で行き詰まることがわかります。そこで、[n]が[3]である場合とそうでない場合とに[destruct (beq_nat n 3)]を使って二つのケースに分け、証明を行います。 

一般的に、[destruct]タクティックは任意の計算の結果のケース分析を行うために使用されます。もし[e]が式で、その式の型が帰納的に定義された型[T]であるような場合、[T]のそれぞれのコンストラクタ[c]について、[destruct e]は[e]のすべての文節に対応するサブゴールを生成し、、起こりえる全ての（ゴールやコンテキストにある）eの状態をコンストラクタcで網羅的に置き換えます。 
*)

(** **** 練習問題: ★ (override_shadow) *)
Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★,  optional (combine_split) *)
(* Complete the proof below *)
(** 以下の証明を完成させなさい。 *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* Sometimes, doing a [destruct] on a compound expression (a
    non-variable) will erase information we need to complete a proof. *)
(** 時折、(変数でない)複合式をdestructで置き換えする場合に、証明に必要な情報が失われてしまうことがあります。*) 
(* For example, suppose
    we define a function [sillyfun1] like this: *)
(**例えば、関数[sillyfun1]を次のように定義したとします。 *)
Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(* And suppose that we want to convince Coq of the rather
    obvious observation that [sillyfun1 n] yields [true] only when [n]
    is odd.  By analogy with the proofs we did with [sillyfun] above,
    it is natural to start the proof like this: *)
(** そしてCoqを使いよく観察することで、[sillyfun1 n]が、[n]が奇数のときだけ[true]となりうることを示したいとします。先ほど[sillyfun]でやった証明を参考に類推すると、証明はこんな風に始まるのが自然に思えます。 *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* 手詰まり... *)
Abort.

(* We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution peformed by [destruct] is too brutal -- it threw
    away every occurrence of [beq_nat n 3], but we need to keep some
    memory of this expression and how it was destructed, because we
    need to be able to reason that since, in this branch of the case
    analysis, [beq_nat n 3 = true], it must be that [n = 3], from
    which it follows that [n] is odd.

    What we would really like is to substitute away all existing
    occurences of [beq_nat n 3], but at the same time add an equation
    to the context that records which case we are in.  The [eqn:]
    qualifier allows us to introduce such an equation (with whatever
    name we choose). *)
(** しかし証明はここで手詰まりになってしまいます。なぜなら、[destruct]を使ったことで、コンテキストからゴールまでたどりつくのに必要な情報がなくなってしまったからです。
[destruct]は[beq_nat n 3]の結果起こる事象を全て投げ捨ててしまいますが、我々はそのうち少なくとも一つは残してもらわないと証明が進みません。このケースで必要なのは[beq_nat n 3 = true]で、ここから[n = 3]は明らかで、ここから[n]が奇数であることが導かれます。

    実際のところやりたいことは[destruct]を[beq_nat n 3]に直接使ってこの式の結果起こることを全て置き換えてしまうことではなく、置き換えと同時にコンテキストに我々が今いるケースと等しいこと示す等式のレコードを追加してくれることです。
	[eqn:]という限定子があれば、そのような等式を導入することが出来ます。(名前は何でもいいんですが)
*)
Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  (* ここで、コンテキストに新しい変数[e3]と、[e3 = beq_nat n 3]という仮定が追加されます。こうしてから[destruct e3]とすると... *)
    Case "e3 = true". apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
     (* 推論している関数本体の2番目のケースに来た時、[eqn:]をもう一度同様に使用して、証明を終らせることが出来ます。*)
      destruct (beq_nat n 5) eqn:Heqe5. 
        SCase "e5 = true".
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "e5 = false". inversion eq.  Qed.


(** **** 練習問題: ★★ (destruct_eqn_practice) *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★ (override_same) *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################## *)
(* * Review *)
(** * まとめ *)

(* We've now seen a bunch of Coq's fundamental tactics.  We'll
    introduce a few more as we go along through the coming lectures,
    and later in the course we'll introduce some more powerful
    _automation_ tactics that make Coq do more of the low-level work
    in many cases.  But basically we've got what we need to get work
    done.

    Here are the ones we've seen:

      - [intros]: 
        move hypotheses/variables from goal to context 

      - [reflexivity]:
        finish the proof (when the goal looks like [e = e])

      - [apply]:
        prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: 
        apply a hypothesis, lemma, or constructor to a hypothesis in
        the context (forward reasoning)

      - [apply... with...]:
        explicitly specify values for variables that cannot be
        determined by pattern matching

      - [simpl]:
        simplify computations in the goal 

      - [simpl in H]:
        ... or a hypothesis 

      - [rewrite]:
        use an equality hypothesis (or lemma) to rewrite the goal 

      - [rewrite ... in H]:
        ... or a hypothesis 

      - [symmetry]:
        changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]:
        changes a hypothesis of the form [t=u] into [u=t]

      - [unfold]:
        replace a defined constant by its right-hand side in the goal 

      - [unfold... in H]:
        ... or a hypothesis  

      - [destruct... as...]:
        case analysis on values of inductively defined types 

      - [destruct... eqn:...]:
        specify the name of an equation to be added to the context,
        recording the result of the case analysis

      - [induction... as...]:
        induction on values of inductively defined types 

      - [inversion]:
        reason by injectivity and distinctness of constructors

      - [assert (e) as H]:
        introduce a "local lemma" [e] and call it [H] 

      - [generalize dependent x]:
        move the variable [x] (and anything else that depends on it)
        from the context back to an explicit hypothesis in the goal
        formula 
*)

(** ここまでに、たくさんの基本的なタクティックを見てきました。これだけあればしばらくの間は困らずに済むはずです。この先数回のレクチャーで2～3新しいものが出てきますが、その先ではさらに強力な「自動化されたタクティック」を紹介していきます。それを使うと、多くの低レベルな作業をCoqに処理してもらうことができます。しかし基本的に、皆さんはもう必要なことを知っていると考えていいでしょう。


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
(* * Additional Exercises *)
(** * さらなる練習問題 *)

(** **** 練習問題: ★★★ (beq_nat_sym) *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★, advanced, optional (beq_nat_sym_informal) *)
(* この補題のあなたの形式的な証明に対応する非形式的な証明を与えなさい:
   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof:
   (* FILL IN HERE *)
[]
 *)

 
(** **** 練習問題: ★★★, optional (beq_nat_trans) *)
Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★, advanced (split_combine) *)
(* We have just proven that for all lists of pairs, [combine] is the
    inverse of [split].  How would you formalize the statement that
    [split] is the inverse of [combine]?

    Complete the definition of [split_combine_statement] below with a
    property that states that [split] is the inverse of
    [combine]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split] [combine l1 l2 = (l1,l2)] to be true?)  *)

(* 思考練習: 我々はすでに、全ての型のリストのペアでcombineがsplitの逆関数であることを証明しました。ではその逆の「splitはcombineの逆関数である」を示すことはできるでしょうか？ 
   下記の[split]が[combine]の逆関数であることを述べる[split_combine_statement]の定義を完成させなさい。それから、その性質が正しいことを証明しなさい。（なるべくintrosを使うタイミングを遅らせ、帰納法の仮定を一般化させておくといいでしょう。 )
   ヒント: split combine l1 l2 = (l1,l2)がtrueとなるl1、l2の条件は何でしょう？ *)

Definition split_combine_statement : Prop :=
(* FILL IN HERE *) admit.

Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.


(** [] *)

(** **** 練習問題: ★★★ (override_permute) *)
Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★, advanced (filter_exercise) *)
(* This one is a bit challenging.  Pay attention to the form of your IH. *)
(** この問題は少し難しいかもしれません。上に上げる仮説の形に注意してください。*)
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★★, advanced (forall_exists_challenge) *)
(** 二つの再帰関数[forallb]、[existsb]を定義しなさい。[forallb]は、リストの全ての要素が与えられた条件を満たしているかどうかを返します。:
      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true
  
      forallb evenb [0;2;4;5] = false
  
      forallb (beq_nat 5) [] = true
    二つめのexistsbは、リストのなかに与えられた述語を満たす要素が一つ以上あるかどうかをチェックします。:
      existsb (beq_nat 5) [0;2;3;6] = false
 
      existsb (andb true) [true;true;false] = true
 
      existsb oddb [1;0;0;0;0;3] = true
 
      existsb evenb [] = false
    次に[existsb']を再帰関数としてではなく、[forallb]と[negb]を使って定義しなさい。.
 
    そして、[existsb']と[existsb]が同じ振る舞いをすることを証明しなさい。
*)

(* FILL IN HERE *)
(** [] *)

(** $Date: 2014-12-31 16:01:37 -0500 (Wed, 31 Dec 2014) $ *)



