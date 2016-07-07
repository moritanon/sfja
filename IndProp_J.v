(** * IndProp: Inductively Defined Propositions *)

Require Export Logic.

(* ####################################################### *)
(*  * Inductively Defined Propositions *)
(** * 帰納的に定義された命題 *)

(*  In the [Logic] chapter we looked at several ways of writing
    propositions, including conjunction, disjunction, and quantifiers.
    In this chapter, we bring a new tool into the mix: _inductive
    definitions_.

    Recall that we have seen two ways of stating that a number [n] is
    even: We can say (1) [evenb n = true], or (2) [exists k, n =
    double k].  Yet another possibility is to say that [n] is even if
    we can establish its evenness from the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even.

    To illustrate how this new definition of evenness works, let's use
    its rules to show that [4] is even. By rule [ev_SS], it suffices
    to show that [2] is even. This, in turn, is again guaranteed by
    rule [ev_SS], as long as we can show that [0] is even. But this
    last fact follows directly from the [ev_0] rule. *)
(** [Logic]の章において、命題を書く幾つかの方法を見ました。論理積や論理和や数量子などです。 この章においては、新しいツールを導入して、_帰納的な定義_として統合します。
ある数が偶数であることを述べる二つの方法があったことを思いだしてください: (1) [evenb n = true]であることと (2)[exists k, n = double k]とです。 [n]が偶数であると述べるもっと他の方法があります。そのためには以下の規則に従います。

    - 規則 [ev_0]: 0は偶数である。
    - 規則 [ev_SS]: もし[n]が偶数であれば、[S (S n)]も偶数である。

この新しい偶数性についての定義がどう働くかを説明するために、[4]が偶数であることをこの規則を用いて示してみましょう。まずは、[ev_SS]です。それには、[2]が偶数であることを示すことが十分(条件？)です。次にここで、[ev_SS]を用いて[0]が偶数であることを示せる限り、保証しなければなりません。しかし、最後の事実はl[ev_0]から直接に導かれます。*)

(*  We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(** このような多くの定義をこのコースの残りを通して見て行きます。また、これらの読み書きを簡単にする手軽な記法があると非形式的な議論のために役にたちます。推論規則の一つは次のように書きます。*)
(**

                              ------------                        (ev_0)
                                 ev 0

                                  ev n
                             --------------                      (ev_SS)
                              ev (S (S n))

*)

(*  Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [ev_SS] says that, if [n]
    satisfies [ev], then [S (S n)] also does.  If a rule has no
    premises above the line, then its conclusion holds
    unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even: *)
(** 上記規則のそれぞれは、「もしラインの上にある根拠がすべて有効であるならば、ラインの下の結論が導かれる。」という推論規則として体裁を与えられています。たとえば、規則[ev_SS]は、[n]が[ev]を満たすならば、[S (S n)]もそうであるという意味です。ラインの上に前提を持たない場合は、無条件にその結論が導かれます。
規則と規則の適用を使って、証明を証明木として表すことが出来ます。上記の[4]が偶数であることを示す証明をどうやって書き換えるかを以下に示します。*)

(**

                ------  (ev_0)
                 ev 0
                ------ (ev_SS)
                 ev 2
                ------ (ev_SS)
                 ev 4

*)

(*  Why call this a "tree" (rather than a "stack", for example)?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this below. *)
(** なぜこれを"木"と言うのか？(むしろ"棚(stack)"と呼ぶべきなんじゃ？)
もちろん、一般的には、推論の規則は複数の前提を持つことが出来ます。この例を後で示します。*)

(*  Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)
(** これらを全部まとめると、偶数性の定義を形式的なCoqの定義に、[Inductive]宣言を使って書き直すことが出来ます。その定義の中の各コンスラクタが先程の推論規則に対応しています。*)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

(*r This definition is different in one crucial respect from
    previous uses of [Inductive]: its result is not a [Type], but
    rather a function from [nat] to [Prop] -- that is, a property of
    numbers.  Note that we've already seen other inductive definitions
    that result in functions, such as [list], whose type is [Type ->
    Type].  What is new here is that, because the [nat] argument of
    [ev] appears _unnamed_, to the _right_ of the colon, it is allowed
    to take different values in the types of different constructors:
    [0] in the type of [ev_0] and [S (S n)] in the type of [ev_SS].

    In contrast, the definition of [list] names the [X] parameter
    _globally_, to the _left_ of the colon, forcing the result of
    [nil] and [cons] to be the same ([list X]).  Had we tried to bring
    [nat] to the left in defining [ev], we would have seen an error: *)
(* この定義は重要な面で、これまでの[Inductive]の使い方を異なっています: その結果が[Type]でなく、むしろ、[nat]から[Prop]への関数 -- すなわち、数の属性であることです。[Type -> Type]という型をもつ[list]型のような、結果が関数であるような他の帰納的な定義を見て来たことに注意してください。
ここで学ぶ新しいことは、[ev]の引数である[nat]に、_名前がなく_、また[nat]が(:=の直前の)コロンの右側にあるために、コンストラクタが異った値を取ることが許されています。[ev_0]の型のなかにある[0]や、[ev_SS]の型の中にある[S (S n)]のようにです。
逆に、[list]という定義は、グローバルに、コロンの左側で、[X]という名前をパラメータにつけていて、、[nil]や[cons]の結果が、同じ[List X]という型を持つように強制しています。[ev」の定義において、[nat]をコロンの左側に持ってきたとすると、エラーになるのが分かるでしょう。*)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)
(** ===> エラー: 帰納的な型の中にあるパラメータ n は、そのコンスラクタの型の束縛変数のように使うことが許されていません。*)

(*  ("Parameter" here is Coq jargon for an argument on the left of the
    colon in an [Inductive] definition; "index" is used to refer to
    arguments on the right of the colon.) *)
(** ("パラメータ"というのは、Coqにおいて、[Inductive]定義のコロンの左側にある引数のことを表す専門用語です。"index"はコロンの右側にある引数に言及するさいに使われます。)*)

(*  We can think of the definition of [ev] as defining a Coq property
    [ev : nat -> Prop], together with theorems [ev_0 : ev 0] and
    [ev_SS : forall n, ev n -> ev (S (S n))].  Such "constructor
    theorems" have the same status as proven theorems.  In particular,
    we can use Coq's [apply] tactic with the rule names to prove [ev]
    for particular numbers... *)
(** Coqが属性を定義するように、[ev]の定義[ev : nat -> Prop]について、定理:[ev_0 : ev 0]と
l[ev_SS: forall n, ev n -> ev (S (S n))]と一緒に考えてみましょう。そのような、"構造化定理"？は証明された定理と同じ状態です。特に、Coqの[apply]タクティックに規則名を渡して、を特定の数が[ev]であることを証明するために使えます。*)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(*  ... or we can use function application syntax: *)
(** ... あるいは、関数適用の記法で使うことも出来ます。*)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(*  We can also prove theorems that have hypotheses involving [ev]. *)
(** [ev]を含む仮定を持つ定理の証明をすることも出来ます。*)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(*  More generally, we can show that any number multiplied by 2 is even: *)
(** もっと一般的に、あらゆる数に2が掛けられると偶数になることを示しましょう: *)

(*  **** Exercise: 1 star (ev_double)  *)
(** **** 練習問題: ★ (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(** * Using Evidence in Proofs *)
(** * 証明中に根拠を使用すること *)

(*  Besides _constructing_ evidence that numbers are even, we can also
    _reason about_ such evidence.

    Introducing [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is even, but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are even (in the sense of [ev]). *)
(** ある数が偶数であるという根拠を構築する際に、そのような根拠について推論することも出来ます。
    [Inductive]宣言を持つ[ev]を導入することは、Coqにおいて、コンストラクタ[ev_0]と[ev_SS]が、ある数が偶数であるという根拠を構築する正しい方法であるというだけでなく、これら二つのコンスラクタはあらゆる数が偶数であるという根拠になる唯一の方法なのです。([ev]という意味において) *)

(*  In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must have one of two shapes:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)
(** 言い換えると、[ev n]という言明に対して、根拠[E]が与えられたら、[E]は、二つのうちどちらかの形をしていなければならないことは、分かっていると思います。

      - [E] は、[ev_0]である(そして、[n]は[O]である。あるいは、
      - [E] は、[ev_SS n ' E']である'(そして、[n]は[S (S n)]である。そこで、[E']は[ev n']の根拠である.
*)
(** This suggests that it should be possible to analyze a hypothesis
    of the form [ev n] much as we do inductively defined data
    structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)
(** このことは、帰納的に定義されたデータと同じように、[ev n]という形をした仮説を解析することを可能にします。とくに、根拠に対する、帰納や、場合分けによって、根拠を示すことが出来るようになります。これが実際に何を意味すかを少し練習問題をやることで見てみましょう。*)

(*  ** Inversion on Evidence *)
(** ** 根拠に対するInversion *)
(*  Subtracting two from an even number yields another even number.
    We can easily prove this claim with the techniques that we've
    already seen, provided that we phrase it in the right way.  If we
    state it in terms of [evenb], for instance, we can proceed by a
    simple case analysis on [n]: *)
(** ある偶数から、2引くことは、別の偶数を導出します。この主張をこれまでに見た正しい方法で、もっと易しく証明出来ます。もし、[evenb]を使って述べた場合、例えば、[n]について場合分けで証明を進めることが出来ます。 *)

Theorem evenb_minus2: forall n,
  evenb n = true -> evenb (pred (pred n)) = true.
Proof.
  intros [ | [ | n' ] ].
  - (* n = 0 *) reflexivity.
  - (* n = 1; contradiction *) intros H. inversion H.
  - (* n = n' + 2 *) simpl. intros H. apply H.
Qed.

(*  We can state the same claim in terms of [ev], but this quickly
    leads us to an obstacle: Since [ev] is defined inductively --
    rather than as a function -- Coq doesn't know how to simplify a
    goal involving [ev n] after case analysis on [n].  As a
    consequence, the same proof strategy fails: *)
(** 同じ主張を、[ev]を使って述べることも出来ますが、障害にぶちあたります: [ev]は帰納的に定義されている-- 、むしろ関数として定義されている -- ので、Coqは、[n]に関数場合分けをしたとき、[ev n]を含むゴールをどうやって簡約してよいか分からないからです。結果として、同じ戦略では失敗します。*)

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros [ | [ | n' ] ].
  - (* n = 0 *) simpl. intros _. apply ev_0.
  - (* n = 1; 行き詰まりました! *) simpl.
Abort.

(*  The solution is to perform case analysis on the evidence that [ev
    n] _directly_. By the definition of [ev], there are two cases to
    consider:

    - If that evidence is of the form [ev_0], we know that [n = 0].
      Therefore, it suffices to show that [ev (pred (pred 0))] holds.
      By the definition of [pred], this is equivalent to showing that
      [ev 0] holds, which directly follows from [ev_0].

    - Otherwise, that evidence must have the form [ev_SS n' E'], where
      [n = S (S n')] and [E'] is evidence for [ev n'].  We must then
      show that [ev (pred (pred (S (S n'))))] holds, which, after
      simplification, follows directly from [E']. *)
(** この問題の解法は、[ev n]という根拠に対し、_直接_に場合分けを行うことです。[ev]の定義によれば、二つの場合があると考えられます。

    - 証拠が、[ev_0]という形をしている場合、[n = 0]であると分かります。それゆえ、[ev (pred (pred 0))]が成り立つことを示すこが出来れば十分です。
      [pred]の定義によれば、これは、[ev 0]と等しいので、成り立つことが[ev_0]から直接導かれます。

    - そうでない場合、証拠は、[ev_SS n' E']という形をしており、[n = S (S n')]で[E']は、[ev n']の根拠になります。それから、[ev (pred (pred (S (S n'))))]が成り立つことを示さなければなりませんが、簡約を行なうと、それは[E']から直接導かれます。*)

(*  We can invoke this kind of argument in Coq using the [inversion]
    tactic.  Besides allowing us to reason about equalities involving
    constructors, [inversion] provides a case-analysis principle for
    inductively defined propositions.  When used in this way, its
    syntax is similar to [destruct]: We pass it a list of identifiers
    separated by [|] characters to name the arguments to each of the
    possible constructors.  For instance: *)
(** [inversion]タクティックを使った、Coqにおける、この種の引数の呼び出しを行うことができます。コンスラクタを含む等式に関して推論を行うことに加えて、[inversion]タクティックは帰納的に定義された命題のための場合分けの原理を提供してくれあす。このように[inversion]を使うとき、その構文はdestructに似ています。[|]で分けられた、それぞれのコンストラクタの引数に名前のリストを与えることでパス出来ます。例えば*)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** Note that, in this particular case, it is also possible to replace
    [inversion] by [destruct]: *)
(** この特定のケースならば、[inversion]は[destruct]に交換可能なことにも留意しておいて下さい。*)
Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** The difference between the two forms is that [inversion] is more
    convenient when used on a hypothesis that consists of an inductive
    property applied to a complex expression (as opposed to a single
    variable).  Here's is a concrete example.  Suppose that we wanted
    to prove the following variation of [ev_minus2]: *)
(** ふたつの違いは、[inversion]の方が、(単一変数でないような)複雑な式に適用された帰納的な属性からなる仮説に使用する場合、少し便利であることです。ここに完全な例があります。
次の[ev_minus2]のバリエーションを証明したいとします:*)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.

(*  Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)
(** 帰納的に、仮説の根拠が、[ev_0]コンスオラクタから生成されることはありえないことを知っています。なぜなら、[O]と[S]は異なるnatのコンストラクタであるからです。それゆえに、適用出来るケースは[ev_SS]だけです。残念なことに、[destruct]はこれを実現出来るほど賢くありませんし、サブゴールは二つ作成されたままです。さらに悪いことに、そうなっても最終のゴールは変らないまま、証明を終了させるための有用な情報はなんら得られません。*)

Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(*  What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2'] because that argument, [n], is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)
(** 正確には、何が起ったのでしょうか？[destruct]の呼び出しは、それぞれのコンストラクタに対応する値によって、属性の引数の出現すべてを置き換える効果があります。
これは、[ev_minus2']の場合では、引数[n]が最終のゴールに直接名前が出ているために、十分だったのです。しかし、[evSS_ev]の場合は、[S (S n)]を起きかえられる項がどこにもありません。*)

(*  The [inversion] tactic, on the other hand, can detect (1) that the
    first case does not apply, and (2) that the [n'] that appears on
    the [ev_SS] case must be the same as [n].  This allows us to
    complete the proof: *)
(** 一方、[inversion]タクティックは、(1)最初のケースは適用出来ないことを検知出来ます。そして(2)ev_SSのケースに現われる[n']は[n]と同じであるに違いないことを検知します。 これで、証明を終らせることが出来ます。*)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(*  By using [inversion], we can also apply the principle of explosion
    to "obviously contradictory" hypotheses involving inductive
    properties. For example: *)
(** [inversion]を使うことによって、帰納的な属性を含む"明らかに矛盾した"仮定に対する爆発原理を適用することも出来ます。例えば*)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

(*  **** Exercise: 1 star (inversion_practice)  *)
(** **** 練習問題: ★ (inversion_practice)  *)
(*  Prove the following results using [inversion]. *)
(** 次の結果を[inversion]を用いて証明しなさい。*)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The way we've used [inversion] here may seem a bit
    mysterious at first.  Until now, we've only used [inversion] on
    equality propositions, to utilize injectivity of constructors or
    to discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence for
    inductively defined propositions.

    Here's how [inversion] works in general.  Suppose the name [I]
    refers to an assumption [P] in the current context, where [P] has
    been defined by an [Inductive] declaration.  Then, for each of the
    constructors of [P], [inversion I] generates a subgoal in which
    [I] has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove [P].  Some of
    these subgoals will be self-contradictory; [inversion] throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, [inversion]
    adds all equations into the proof context that must hold of the
    arguments given to [P] (e.g., [S (S n') = n] in the proof of
    [evSS_ev]). *)
(** このような [inversion] の使い方は最初はちょっと謎めいて思えるかもしれません。これまでは、 [inversion] は等号に関する命題に対して使い、コンストラクタから元のデータを取り出すためか、別のコンストラクタを区別するためににしか使っていませんでした。しかし、ここでは [inversion] が 帰納的に定義された命題に対する根拠を分析するためにも使えることを紹介しました。

ここで、[inversion] が一般にはどのように動作するかを説明します。 [I] が現在のコンテキストにおいて帰納的に宣言された仮定 [P] を参照しているとします。ここで、[inversion I] は、[P]のコンストラクタごとにサブゴールを生成します。 各サブゴールにおいて、 コンストラクタが [P] を証明するのに必要な条件によって [I] が置き換えられます。サブゴールのうちいくつかは矛盾が存在するので、 [inversion] はそれらを除外します。残っているのは、元のゴールが成り立つことを示すのに必要なサブゴールです。[inversion]は[P]に与えられた引数の全ての等式をコンテキストに加えます。(例、evSS_evの中の[S (S n') = n]のように。) *)

(* ####################################################### *)
(*  ** Induction on Evidence *)
(** ** 根拠に対する帰納法 *)

(*  The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop], we already know that those are equivalent to
    each other). To show that all three coincide, we just need the
    following lemma: *)
(** 上記の[ev_double]練習問題で偶数性の新しい記法が最初の二つによって含意されることを示しました。([even_bool_prop]によって、これでお互いが等価であることが分かりました。)これらが三つがコインの裏表であることを示すために、次の補題が必要になります。*)

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.

(*  We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy would probably
    lead to a dead end, as in the previous section.  Thus, it seems
    better to first try inversion on the evidence for [ev].  Indeed,
    the first case can be solved trivially. *)
(**  ここで、[n]に関する場合わけや、帰納法を使って証明を進めたくなるかもしれません。しかし、[ev]が前提として与えられているため、この戦略は前の問題と同じく行き詰まります。それゆえ、根拠である[ev]に対する帰納法を試すのがよい方法に思われます。たしかに、最初の場合は、簡単に解けます。*)

  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.

(** Unfortunately, the second case is harder.  We need to show [exists
    k, S (S n') = double k], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to an similar
    one that involves a _different_ piece of evidence for [ev]: [E'].
    More formally, we can finish our proof by showing that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result suffices. *)
(** 残念なことに、二つ目の場合はより難しくなります。示す必要があるのは、[exists k, S (S n')]ですが、利用出来る仮定はただ[E']のみで、それは[ev n']であると述べています。これはそのままでは役に立ちませんので、[E]についてのケース分析を行なうことは時間の無駄のようです。
二番目のゴールがより厳密に見ることが出来れば、何かもっと面白いことが起こるのが見えたかもしれません。[E]についてのケース分析をすることで、[ev]の根拠の異なる断片を含む元の結果を減らすことが出来ます。一般的に言えば、以下を示すことで、証明を終わらせることが出来ます。

        exists k', n' = double k',

    これは最初の文と同じに見えるかもしれませんが、[n']が,[n]の代わりに使われています。確かに、Coqに中間結果が十分であると納得させることは難しくありません。 *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k').
      reflexivity. }
    apply I. (* reduce the original goal to the new one *)


(** If this looks familiar, it is no coincidence: We've encountered
    similar problems in the [Induction] chapter, when trying to use
    case analysis to prove results that required induction.  And once
    again the solution is... induction!

    The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypotheses for each recursive occurrence of
    the property in question.

    Let's try our current lemma again: *)
(** 以前にも見たような気がするかもしれませんが、気のせいではありません。[Induction]の章で、似たような問題に遭遇しています。そのときは、必要とされる帰納の結果を証明するために、場合わけを用いました。そう、その時に用いた解決方法は、帰納です！

根拠に対する[induction]の振舞はデータに対する帰納法と同じようなものです。Coqに根拠を生成するそれぞれのコンストラクタに対応するサブゴールを生成させて、それぞれの再帰的な属性の出現に対して帰納仮説を与えて行きます。
もう一度、今の補題をやってみましょう: *)
Abort.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(*  Here, we can see that Coq produced an [IH] that corresponds to
    [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)
(** ここで、Coqが[E']に応答する[IH]を導入しているのが分かります。再帰的な[ev]の出現はその定義のなかで一回きりです。[E']は、[n']に言及しているので、帰納仮説は[n]や他の番号ではなく[n']についてのものです。*)

(*  The equivalence between the second and third definitions of
    evenness now follows. *)
(** 二番目と三番目の偶数の定義の等価性については以下で示します *)

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(*  As we will see in later chapters, induction on evidence is a
    recurring technique when studying the semantics of programming
    languages, where many properties of interest are defined
    inductively.  The following exercises provide simple examples of
    this technique, to help you familiarize yourself with it. *)
(** 後の章で見るように、根拠上の帰納法は、プログラミング言語の意味論を学ぶときに繰り返し出て来るテクニックです。そこで、多くの興味深い属性が帰納的に定義されています。次の練習問題はこのテクニックの簡単な例です。この方法に慣れるのに役立つでしょう。*)

(*  **** Exercise: 2 stars (ev_sum)  *)
(** **** 練習問題: ★★ (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 4 stars, advanced (ev_alternate)  *)
(** **** 練習問題: ★★★★ advanced (ev_alternate)  *)
(*  In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)
(** 一般的に、帰納的に属性を定義する方法は、複数の方法がありえます。例えば、ここに(ちょっと不自然ですが) [ev]の代わりになる定義があります。*)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

(*  Prove that this definition is logically equivalent to
    the old one. *)
(** この定義が論理的に以前の定義と等価なことを証明しなさい。*)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, advanced, recommended (ev_ev__ev)  *)
(** **** 練習問題: ★★★ advanced recommended (ev_ev__ev)  *)
(*  Finding the appropriate thing to do induction on is a
    bit tricky here: *)
(**  何に対して帰納法を行えばいいかを探しなさい。(ちょっとトリッキーですが)  *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, optional (ev_plus_plus)  *)
(** **** 練習問題: ★★★ advanced recommended (ev_ev__ev)  *)
(*  This exercise just requires applying existing lemmas.  No
    induction or even case analysis is needed, though some of the
    rewriting may be tedious. *)
(** 既存の補題を適用する必要のある練習問題です。 帰納法も場合分けも不要ですが、書き換えのうちいくつかはちょっと大変です。*)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(*  * Inductive Relations *)
(** * 帰納的関係 *)

(*  A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)
(** 数値をパラメータとして持つ命題(例えば、[ev]など)は属性 _property_と 見なすこともできます。つまり、それに属する値についてその命題が証明可能である ような nat の部分集合の定義と見ることができるということです。 同様に、引数（パラメータ）を二つ持つ命題は、その二つの「関係」を表していると考えられます。つまり、その命題について証明可能な値のペアの集合の定義、 というわけです。 *)
Module LeModule.

(*  One useful example is the "less than or equal to"
    relation on numbers. *)
(** よく使われるものの例として「等しいかまたは小さい」 という関係があります。 *)

(*  The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)
(** この定義はかなり直観的なものになります。これは、ある数値がもう一つの 数値より小さいかまたは等し>い、ということを示すには二つの方法があることを 示しています。一つはそれらが同じ数であるかどうかを確>認すること。もう 一つは最初の数が。二つ目の数の一つ前の数より小さいかまたは等しい、ということの根拠を得ることです。 *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *
(** コンストラクタ [le_n] と [le_S] を使った [<=] にからむ証明は、前章の [eq] がそうであったように、属性についての証明のいくつかのパターンに倣っています。[<=] の形をしたゴール（例えば [3<=3] や [3<=6] など）に、そのコンストラクタをapply することができますし、inversion のようなタクティックを使って（[(2 <= 1) -> 2+2=5] の証明をしようとする際のように） コンテキストに [<=] を含む仮定から情報を抽出することもできます。*)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)
(** ここで、定義が正しくなされているのかのチェックをしてみましょう。（注意して 欲しいのは、ここでやることが、最初のレクチャーで書いてもらった、ある種のシンプルな「ユニットテスト」のようなものですが、今回のものは以前のものとちょっと違います。今回のものには、[simpl] や [reflexivity] はほとんど役に立ちません。簡約だけで証明できるようなものではないからです。*)

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

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)
(** "より小さい"という関係 [n < m]は、[le]を使って定義出来ます。
End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(*  Here are a few more simple relations on numbers: *)
(** 数についての簡単な関係をいくつか示します。*)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(*  **** Exercise: 2 stars, recommended (total_relation)  *)
(** **** 練習問題: ★★, recommended (total_relation)  *)
(*  Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)
(** 二つの自然数の全てのペア同士の間に成り立つ帰納的な関係 [total_relation] を
    定義しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(*  **** Exercise: 2 stars (empty_relation)  *)
(** **** 練習問題: ★★ (empty_relation)  *)
(*  Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)
(** 自然数の間では決して成り立たない関係 [empty_relation] を帰納的に
    定義しなさい。 *)
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (le_exercises)  *)
(** **** 練習問題: ★★★, optional (le_exercises)  *)
(*  Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)
(** 後のコースで必要になる[<=] や [<] といった関係についての事実を示しておきます。その証明自体がとてもよい練習問題になります。*)
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

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

(*  Hint: The next one may be easiest to prove by induction on [m]. *)
(** ヒント: [m]による帰納法の方が簡単に証明出来ます。 *)

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  (* FILL IN HERE *) Admitted.

(*  Hint: This theorem can easily be proved without using [induction]. *)
(** ヒント: この定理は[induction]を使わない方が簡単に証明出来ます。 *)

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 2 stars, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Module R.

(*  **** Exercise: 3 stars, recommended (R_provability2)  *)
(** **** 練習問題 ★★★, recommended (R_provability2) *)
(** We can define three-place relations, four-place relations,
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

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.*)
(**  - 次の命題のうち、この関係を満たすと証明できると言えるのはどれでしょうか。
      - [R 1 1 2]
      - [R 2 2 6]

     - この関係 [R] の定義からコンストラクタ [c5] を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？端的に（１文で）説明しなさい。

     - この関係 [R] の定義からコンストラクタ [c4] を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？端的に（１文で）説明しなさい。

(* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (R_fact)  *)
(** **** 練習問題 ★★★, optional (R_fact) *)
(*  The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq? *)
(** 上記の関係[R]は実際に、もっと分かりやすい関数をエンコードしたものです。どの関数か挙げなさい。Coqにおけるその関数と関係について述べて、証明しなさい*)

Definition fR : nat -> nat -> nat :=
  (* FILL IN HERE *) admit.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully! *)
(**あるリストが、別のリストのサブシーケンス（ _subsequence_ ）であるとは、最初のリストの要素が全て二つ目のリストに同じ順序で現れるということです。ただし、その間に何か別の要素が入ってもかまいません。例えば、

    [1,2,3]

    は、次のいずれのリストのサブシーケンスでもあります。

    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]

    しかし、次のいずれのリストのサブシーケンスでもありません。

    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - list nat] 上に、そのリストがサブシーケンスであることを意味するような命題 [subseq] を定義しなさい。（ヒント：三つのケースが必要になります）

    -サブシーケンスである、という関係が「反射的」であることを証明しなさい。つまり、どのようなリストも、それ自身のサブシーケンスであるということです。

    - 任意のリスト [l1]、 [l2]、 [l3] について、もし [l1] が [l2] のサブシーケンスならば、 [l1] は [l2 ++ l3] のサブシーケンスでもある、ということを証明しなさい。

    -（これは少し難しいですので、任意とします）サブシーケンスという関係は推移的である、つまり、 [l1] が [l2] のサブシーケンスであり、 [l2] が [l3] のサブシーケンスであるなら、 [l1] は [l3] のサブシーケンスである、というような関係であることを証明しなさい。（ヒント：何について帰納法を適用するか、よくよく注意して下さい!）*)
    (* FILL IN HERE *)
    (** [] *)

(** **** 練習問題 ★★, optional (R_provability) *)
(*  Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)
(** Coq に次のような定義を与えたとします：
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    次のうち、証明可能なのはどの命題でしょうか？

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]] *)
(** [] *)


(* ############################################################ *)
(*  * Case Study: Regular Expressions *)
(** * ケーススタディ: 正規表現 *)

(** The [ev] property provides a simple example for illustrating
    inductive definitions and the basic techniques for reasoning about
    them, but it is not terribly exciting -- after all, it is
    equivalent to the two non-inductive of evenness that we had
    already seen, and does not seem to offer any concrete benefit over
    them.  To give a better sense of the power of inductive
    definitions, we now show how to use them to model a classic
    concept in computer science: _regular expressions_. 

    Regular expressions are a simple language for describing strings,
    defined as elements of the following inductive type.  (The names
    of the constructors should become clear once we explain their
    meaning below.)  *)
(** [ev]属性は、帰納的な定義とそれを使う推論の簡単な例を提供します。しかしそれほど興奮するものでもありません。-- 結局、それまでに見た二つの非帰納的な定義と等価ですし、それらを越えるどんな具体的なメリットもありません。帰納的定義のパワーをもっと感じるために、どうやってコンピュータサイエンスの古典的概念 -- 正規表現 -- を帰納的定義を使ってモデル化するかを見てみましょう。

正規表現は、以下の帰納的な型によって定義された文字列を記述するための単純な言語です。(コンストラクタの名前は、以下のように、それぞれの意味を説明する曖昧でないものであるべきです。*)

Inductive reg_exp (T : Type) : Type :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T -> reg_exp T
| App : reg_exp T -> reg_exp T -> reg_exp T
| Union : reg_exp T -> reg_exp T -> reg_exp T
| Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** Note that this definition is _polymorphic_: Regular expressions in
    [reg_exp T] describe strings with characters drawn from [T] --
    that is, lists of elements of [T].  (We depart slightly from
    standard practice in that we do not require the type [T] to be
    finite.  This results in a somewhat different theory of regular
    expressions, but the difference is not significant for our
    purposes.)

    We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

    - The expression [EmptySet] does not match any string.

    - The expression [EmptyStr] matches the empty string [[]].

    - The expression [Char x] matches the one-character string [[x]].

    - If [re1] matches [s1], and [re2] matches [s2], then [App re1
      re2] matches [s1 ++ s2].

    - If at least one of [re1] and [re2] matches [s], then [Union re1
      re2] matches [s].

    - Finally, if we can write some string [s] as the concatenation of
      a sequence of strings [s = s_1 ++ ... ++ s_k], and the
      expression [re] matches each one of the strings [s_i], then
      [Star re] matches [s].  (As a special case, the sequence of
      strings may be empty, so [Star re] always matches the empty
      string [[]] no matter what [re] is.) *)
(** この定義が多相的なものであることに気がついたでしょうか: [req_exp T]中の正規表現は文字列を[T]から採られる文字によって記述します。すなわち、[T]の要素のリストです。(有限の型[T]を必要としない標準的な練習から開始します。その結果正規表現といくらか異なるものになりますが、この違いは、我々の目的からすれば、重要なものではありません)

正規表現と文字列を以下の規則で結び付けます。そのルールは正規表現が文字列にいつマッチするかを定義します:

    - [EmptySet]式はどんな文字列にもマッチしません。

    - [EmptyStr]式は、空の文字列[[]]にマッチします。

    - [Char x]式は、一文字からなる文字列[[x]]にマッチします。

    - もし [re1]が文字列[s1]にマッチして、[re2]が文字列[s2]にマッチするならば、{App re1 re2]は、[s1 ++ s2]にマッチします。

    - もし、[re1]と[re2]の少くともどちらかが文字列[s]にマッチするならば、[Union re1 re2]は[s]にマッチします。

    - 最後に、もし文字列[s]を[s = s_1 ++ ... ++ s_k]のように、文字列の並びの結合として書くことが出来て、正規表現[re]がそれぞれの文字列[s_i]にマッチするならば、[Star re]は[s]にマッチします。(特別な場合として、文字列の並びが空である場合、[Star re]は常に、[re]が何であるかに関係なく、空の文字列[[]]にマッチします。*)

(*  We can easily translate this informal definition into an
    [Inductive] one as follows: *)
(** この非形式的定義を[Inductive]を使用したものに翻訳するのは簡単です: *)

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

(*  Once again, for readabilit^y, we can also display this definition
    using inference-rule notation.  At the same time, let's introduce
    a more readable infix notation. *)
(** もう一度、読み易いように、この定義を推論規則の記法を使って書き直してみましょう。それど同時に、もっと読み易い記法を導入してみることにしましょう。*)
Notation "s =~ re" := (exp_match s re) (at level 80).

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re

*)

(*  Notice that these rules are not _quite_ the same as the informal
    ones that we gave at the beginning of the section.  First, we
    don't need to include a rule explicitly stating that no string
    matches [EmptySet]; we just don't happen to include any rule that
    would have the effect of some string matching
    [EmptySet].  (Indeed, the syntax of inductive definitions doesn't
    even _allow_ us to give such a "negative rule.")

    Furthermore, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules, but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.) *)
(** これらの規則は、このセクションの最初に見た非形式的なものと全く同じものではないことに気をつけてください。まず[EmptySet]にどんな文字列もマッチしないことを述べる規則を含める必要はありません: [EmptySet]にマッチする文字列の効果を持つどんなルールが含まれることは決してないからです。？
(実際、再帰的定義のシンタックスは、そのような否定的な規則を含めることが許されていません。*)

さらに、[Union]や[Star]の二つの非形式的な規則は、それぞれ二つのコンストラクタに対応します:[MUnionL] / [MUnionR]、[MStar0] / [MStartApp]とにです。その結果、論理的に元の規則に等しくはなるだけでなく、Coqにとっても都合のよいものになります: 再帰的な[exp_match]を直接コンスラクタの引数として与えることが出来るようになるからです。それは、根拠についての帰納法の適用をより簡単にしてくれます。(下記の[exp_match_ex1]と[exp_match_ex2]の練習問題で、再帰的に宣言されたコンストラクタと、非形式的な規則をもっと文字通りに変換したものが論理的に等しいことを証明して下さい。*)
(*  Let's illustrate these rules with a few examples. *)
(** これらの規則を幾つかの例で説明してみましょう。*)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(*  (Notice how the last example applies [MApp] to the strings [[1]]
    and [[2]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Coq wouldn't be able to figure out how to split the
    string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)
(** (最後の例において、[MApp]が[[1]]と[[2]]の文字列に直接どのように適用されているか注意しましょう。
ゴールに[[1]++[2]]ではなく、[[1; 2]]が設定されているので、Coqそれ自身は、その文字列をどのように分割したらよいかを見つけ出すことが出来ません。)
[inversion]を使うことで、ある特定の文字列が正規表現にマッチしないことを示すことが出来ます。*)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(*  We can define helper functions to help write down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)
(** 正規表現を書き下すヘルパ関数を定義することが出来ます。[req_exp_of_list]関数は、引数として受け取ったリストに確かにマッチする正規表現を構築します。*)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(*  We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)
(** [exp_match]に関する一般的な事実を証明することも出来ます。例えば、次の補題は、[re]にマッチする全ての文字列(群)が、[Star re]にもマッチすることを示します。*)
Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(*  (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)
(** (定理のゴールを[MStarApp]で期待される形と全く同じに変更する[app_nil_r]の使用には気をつけましょう。*)
(*  **** Exercise: 3 stars (exp_match_ex1)  *)
(** **** 練習問題: ★★★ stars (exp_match_ex1)  *)
(*  The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)
(** 次の補題は、この節の最初に提示された非形式的なマッチング規則が形式的な帰納的定義からも得られることを示しています。*)
Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  (* FILL IN HERE *) Admitted.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  (* FILL IN HERE *) Admitted.

(*  The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)
(** 次の補題を[Poly]の章の[fold]関数を使って説明すると:[ss : list (list T)]が、文字列[s1,..., sn]を表現しているとすると、[fold app ss []]は、それら全てを結合した結果です。*)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars (reg_exp_of_list)  *)
(** **** 練習問題: ★★★★ stars (reg_exp_of_list)  *)
(*  Prove that [reg_exp_of_list] satisfies the following
    specification: *)
(** [reg_exp_of_list]が次の仕様を満すことを証明しなさい。*)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence.  For
    example, suppose that we wanted to prove the following intuitive
    result: If a regular expression [re] matches some string [s], then
    all elements of [s] must occur somewhere in [re].  To state this
    theorem, we first define a function [re_chars] that lists all
    characters that occur in a regular expression: *)
(** [exp_match]の定義は再帰的構造をしてため、正規表現を含む証明はしばしば根拠に対する帰納法を必要とすると感じてしまうかもしれません。例えば、次の直感的な結果を証明したいと思ったとしましょう:もし、正規表現[re]がある文字列[s]にマッチする場合、[s]の全ての要素は、[re]のどこかに出現しなければならない。
この定理を述べるために、まず、正規表現中の全ての文字を列挙する[re_chars]関数を定義します。*)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(*  We can then phrase our theorem as follows: *)
(** それから次のように定理を表現します: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [
        |x'
        |s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
        |re|s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite in_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite in_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite in_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.

(*  Something interesting happens in the [MStarApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re]), and a second one that applies when [x]
    occurs in [s2] (which matches [Star re]).  This is a good
    illustration of why we need induction on evidence for [exp_match],
    as opposed to [re]: The latter would only provide an induction
    hypothesis for strings that match [re], which would not allow us
    to reason about the case [In x s2]. *)
(** 何か興味深いことが、[MStarApp]のケースで起こりました。ここで、_二つ_の帰納法の仮定が得られました: 一つは、([re]にマッチする)[s1]上に[x]が現われるときに適用され、もう一つは、([Star re]にマッチする)[s2]上に[x]が現れるときに適用されるものです。これは、なぜ[exp_match]の根拠に対する帰納法が、[re]とは対照的に必要となるのかについてのよい説明になっています: 後で、[re]にマッチする文字列のための帰納法の仮定が提供され、[In x s2]のケースについての推論が可能になります。*)

  - (* MStarApp *)
    simpl. rewrite in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(*  **** Exercise: 4 stars (re_not_empty)  *)
(** **** 練習問題: ★★★★ stars (re_not_empty)  *)
(*  Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)
(** 正規表現がある文字列にマッチするかどうかをテストする帰納的な関数[re_not_empty]を書いて、あなたの関数が正しいことを証明しなさい。*)

Fixpoint re_not_empty {T} (re : reg_exp T) : bool :=
  (* FILL IN HERE *) admit.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  ** The [remember] Tactic *)
(** ** [remember] タクティック *)

(*  One potentially confusing feature of the [induction] tactic is
    that it happily lets you try to set up an induction over a term
    that isn't sufficiently general.  The net effect of this will be
    to lose information (much as [destruct] can do), and leave you
    unable to complete the proof. Here's an example: *)
(** [induction]タクティックの混乱しやすいかもしれない特徴として、十分に一般的でない項に対して帰納法を行なうことが出来てしまうことです。このことの正味の影響は([destruct]でよくやるように)情報を失なってしまって、証明を完了出来なくなってしまうことです。次の例では: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(*  Just doing an [inversion] on [H1] won't get us very far in the
    recursive cases. (Try it!). So we need induction. Here is a naive
    first attempt: *)
(** [H1]に対して、[inversion]を行なっても、再帰的なケースの中でどこへも行けません。(やってみましょう！)。そのため、帰納法が必要になります。ここで素朴な方法をまず試してみましょう: *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(*  But now, although we get seven cases (as we would expect from the
    definition of [exp_match]), we lost a very important bit of
    information from [H1]: the fact that [s1] matched something of the
    form [Star re].  This means that we have to give proofs for _all_
    seven constructors of this definition, even though all but two of
    them ([MStar0] and [MStarApp]) are contradictory.  We can still
    get the proof to go through for a few constructors, such as
    [MEmpty]... *)
(** しかしここで、7つのケース([exp_match]の定義から期待されるように)があるにも拘らず、[H1]からの僅かな、しかし非常に重要な情報が失われているのです: [s1]が[Star re]の形式にマッチしたという事実です。
このことは、この定義の7つのコンストラクタ全てに対する証明を与えなければならないことを意味しています。[MStar0]と[MStarApp]の二つを除いて矛盾しているにも拘らず、です。少数のコンスラクタのために、証明を続けることは出来ます。[MEmpty]のように... *)
  - (* MEmpty *)
    simpl. intros H. apply H.

(*  ... but most of them get stuck.  For [MChar], for instance, we
(** ... しかし大抵は詰ってしまいます。たとえば、[MChar]では、*)
    must show that

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    which is clearly impossible. *)

  - (* MChar. 詰った... *)

Abort.

(** The problem is that [induction] over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as [Star re].  In this respect it
    behaves more like [destruct] than like [inversion].

    We can solve this problem by generalizing over the problematic
    expressions with an explicit equality: *)
(** この問題は、命題の仮説に対する[induction]は、完全に一般化された仮説上でしか上手く動かないことです、言い換えると、もっと複雑な表現とちがって、全ての引数が変数であるような仮定、たとえば、[Star re]のようなものです。この点において、[inversion]というよりは、[destruct]に近い振舞いを[induction]
は行ないます。
問題のある表現に対して明示的な等価性をもって一般化してやることで、この問題を解くことが出来ます: *)
*)
Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  s1 =~ re' ->
  re' = Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence directly,
    because the argument to the first hypothesis is sufficiently
    general, which means that we can discharge most cases by inverting
    the [re' = Star re] equality in the context.

    This idiom is so common that Coq provides a tactic to
    automatically generate such equations for us, avoiding thus the
    need for changing the statements of our theorems.  Calling
    [remember e as x] causes Coq to (1) replace all occurrences of the
    expression [e] by the variable [x], and (2) add an equation [x =
    e] to the context.  Here's how we can use it to show the above
    result: *)

Abort.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, which allows us to
    conclude immediately. *)

  - (* MEmpty *)  inversion Heqre'.
  - (* MChar *)   inversion Heqre'.
  - (* MApp *)    inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.

(** In the interesting cases (those that correspond to [Star]), we can
    proceed as usual.  Note that the induction hypothesis [IH2] on the
    [MStarApp] case mentions an additional premise [Star re'' = Star
    re'], which results from the equality generated by [remember]. *)

  - (* MStar0 *)
    inversion Heqre'. intros s H. apply H.
  - (* MStarApp *)
    inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars (exp_match_ex2)  *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ############################################################ *)
(** **** Exercise: 5 stars, advanced (pumping)  *)
(** One of the first interesting theorems in the theory of regular
    expressions is the so-called _pumping lemma_, which states,
    informally, that any sufficiently long string [s] matching a
    regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re]. 

    To begin, we need to define "sufficiently long."  Since we are
    working in a constructive logic, we actually need to be able to
    calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

(** Now, the pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** To streamline the proof (which you are to fill in), the [omega]
    tactic, which is enabled by the following [Require], is helpful in
    several places for automatically completing tedious low-level
    arguments involving equalities or inequalities over natural
    numbers.  We'll return to [omega] in a later chapter, but feel
    free to experiment with it now if you like.  The first case of the
    induction gives an example of how it is used. *)

Require Import Coq.omega.Omega.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  (* FILL IN HERE *) Admitted.

End Pumping.
(** [] *)

(* ####################################################### *)
(** * Improving Reflection *)

(** We've seen in the [Logic] chapter that we often need to
    relate boolean computations to statements in [Prop].
    Unfortunately, performing this conversion by hand can result in
    tedious proof scripts.  Consider the proof of the following
    theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_nat n m) eqn:H.
    + (* beq_nat n m = true *)
      intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly
    apply the [beq_nat_true_iff] lemma to the equation generated by
    destructing [beq_nat n m], to convert the assumption [beq_nat n m
    = true] into the assumption [n = m], which is what we need to
    complete this case.

    We can streamline this proof by defining an inductive proposition
    that yields a better case-analysis principle for [beq_nat n
    m].  Instead of generating an equation such as [beq_nat n m =
    true], which is not directly useful, this principle gives us right
    away the assumption we need: [n = m].  We'll actually define
    something a bit more general, which can be used with arbitrary
    properties (and not just equalities): *)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  Intuitively, it states that the property
    [P] is _reflected_ in (i.e., equivalent to) the boolean [b]: [P]
    holds if and only if [b = true].  To see this, notice that, by
    definition, the only way we can produce evidence that [reflect P
    true] holds is by showing that [P] is true and using the
    [ReflectT] constructor.  If we invert this statement, this means
    that it should be possible to extract evidence for [P] from a
    proof of [reflect P true].  Conversely, the only way to show
    [reflect P false] is by combining evidence for [~ P] with the
    [ReflectF] constructor.

    It is easy to formalize this intuition and show that the two
    statements are indeed equivalent: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P [] H.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

(** **** Exercise: 2 stars, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second).

    To use [reflect] to produce a better proof of
    [filter_not_empty_In], we begin by recasting the
    [beq_nat_iff_true] lemma into a more convenient form in terms of
    [reflect]: *)

Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

(** The new proof of [filter_not_empty_In] now goes as follows.
    Notice how the calls to [destruct] and [apply] are combined into a
    single call to [destruct].  (To see this clearly, look at the two
    proofs of [filter_not_empty_In] in your Coq browser and observe
    the differences in proof state at the beginning of the first case
    of the [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_natP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** Although this technique arguably gives us only a small gain
    in convenience for this particular proof, using [reflect]
    consistently often leads to shorter and clearer proofs. We'll see
    many more examples where [reflect] comes in handy in later
    chapters.

    The use of the [reflect] property was popularized by _SSReflect_,
    a Coq library that has been used to formalize important results in
    mathematics, including as the 4-color theorem and the
    Feit-Thompson theorem.  The name SSReflect stands for _small-scale
    reflection_, i.e., the pervasive use of reflection to simplify
    small proof steps with boolean computations. *)

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars, recommended (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.

*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.

*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)  *)
(** Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  *)
(** A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced (NoDup)  *)
(** Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

(* FILL IN HERE *)

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

(* FILL IN HERE *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, recommended (nostutter)  *)
(** Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  The property "[nostutter mylist]" means that
    [mylist] does not stutter.  Formulate an inductive definition for
    [nostutter].  (This is different from the [NoDup] property in the
    exercise above; the sequence [1;4;1] repeats but does not
    stutter.) *)

Inductive nostutter {X:Type} : list X -> Prop :=
 (* FILL IN HERE *)
.
(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_2:  nostutter (@nil nat).
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_3:  nostutter [5].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* FILL IN HERE *) Admitted.
(* 
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The _pigeonhole principle_ states a basic fact about counting: if
   we distribute more than [n] items into [n] pigeonholes, some
   pigeonhole must contain at least two items.  As often happens, this
   apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  (* FILL IN HERE *) Admitted.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* FILL IN HERE *)
.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
  (* FILL IN HERE *) Admitted.
(** [] *)


(** $Date: 2015-08-11 12:03:04 -0400 (Tue, 11 Aug 2015) $ *)
