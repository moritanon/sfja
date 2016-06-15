(** * 帰納法: 帰納法による証明 *)

(** First, we import all of our definitions from the previous
    chapter. *)
(**まず、前章の定義をすべてインポートしましょう。 *)
Require Export Basics_J.

(** For the [Require Export] to work, you first need to use
    [coqc] to compile [Basics.v] into [Basics.vo].  This is like
    making a .class file from a .java file, or a .o file from a .c
    file.  There are two ways to do it:

     - In CoqIDE:

         Open [Basics.v].  In the "Compile" menu, click on "Compile
         Buffer".

     - From the command line:

         Run [coqc Basics.v]

    *)


(** [Requre Export]を動かすために、[coqc]を使用して、[Basics_J.v]をコンパイルして、[Basics.vo]を生成する必要があります。(これは、.classファイルを .javaファイルから、あるいは、.oファイルを .cファイルから生成するのに似ています。
  コードをコンパイルする方法はふたつあります。

     - CoqIDEで:

         [Basics_J.v] を開き、 "Compile" メニューの "Compile Buffer" をクリックする。

     - コマンドラインから:

        [coqc Basics_J.v] を実行する。


 *)

(* ###################################################################### *)
(*  * Proof by Induction *)
(** 帰納法による証明 *)

(*  We proved in the last chapter that [0] is a neutral element
    for [+] on the left using an easy argument based on
    simplification.  The fact that it is also a neutral element on the
    _right_... *)
(* 一つ前の章で、[0]が[+]の左に置かれた場合、[+]に対して中立な要素であることを簡約に基く易しい論証を使って証明しました。[0]が_右_に置かれた場合はどうなるでしょうか。 *)

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

(* ... cannot be proved in the same simple way.  Just applying
  [reflexivity] doesn't work, since the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)
(** どうやら同じ単純な方法では証明出来ないようです。[reflexivity]を適用するだけでは作用しません。[n + 0]の中の[n]は任意の未知の数字のため、[+]の定義の中の[match]句は簡約されないからです。 *)

Proof.
  intros n.
  simpl. (* 何も起こらない! *)
Abort.

(*  And reasoning by cases using [destruct n] doesn't get us much
   further: the branch of the case analysis where we assume [n = 0]
   goes through fine, but in the branch where [n = S n'] for some [n'] we
   get stuck in exactly the same way.  We could use [destruct n'] to
   get one step further, but, since [n] can be arbitrarily large, if we
   try to keep on like this we'll never be done. *)
(** [destruct n]による場合わけを使った推論も、これ以上進めることが出来ません: [n = 0]の場合は上手く行きますが、[n = S n']のほうではn'で同じように詰まってしまいます。。destruct n'でさらに一歩踏み込んでみたところで、nは任意の大きい数のまま動きません。どうやらまだ来たことがないところに迷い込んでしまったようです。*)

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* ここまでは良い... *)
  - (* n = S n' *)
    simpl.       (* ...しかし、ここでまた詰まります。 *)
Abort.

(*  To prove interesting facts about numbers, lists, and other
    inductively defined sets, we usually need a more powerful
    reasoning principle: _induction_.

    Recall (from high school, a discrete math course, etc.) the
    principle of induction over natural numbers: If [P(n)] is some
    proposition involving a natural number [n] and we want to show
    that [P] holds for _all_ numbers [n], we can reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same but the order is backwards: we
    begin with the goal of proving [P(n)] for all [n] and break it
    down (by applying the [induction] tactic) into two separate
    subgoals: first showing [P(O)] and then showing [P(n') -> P(S
    n')].  Here's how this works for the theorem at hand: *)
(** 数や、リスト、他に再帰的に定義された集合に関する興味深い事実を証明するために、 もっとずっと強力な推論規則が必要になります。それが「帰納法」です。 
高校で習った帰納法の仕組みを思い出して、自然数を考えてみましょう。もしP(n)が自然数nに対する命題であるとすると、Pがどんなnに対しても成り立つことは、以下のような方法で証明できます。

        - [P(O)]が成り立つことを示す;
        - どんなn'に対しても、もし[P(n')]が成り立つなら[P(S n')]も成り立つことを示す;
        - これによって、[P(n)]がどんな[n]でも成り立つと結論される。

Coqでは、それぞれのステップは同じですが順序は逆向きに考えます。まず、ゴールの証明である「任意のnについてP(n)が成り立つ」からはじめ、それを二つの独立したサブゴールに分割します（ここでinductionタクティックを使います）。その結果、一つ目のサブゴールはP(O)、二つ目はP(n') → P(S n')となるはずです。以下は、実際にinductionタクティックが先ほど証明しようとしていた定理にどう作用するかを示したものです。 *)

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.

(*  Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  In the first branch, [n] is replaced by [0] and
    the goal becomes [0 + 0 = 0], which follows by simplification.  In
    the second, [n] is replaced by [S n'] and the assumption [n' + 0 =
    n'] is added to the context (with the name [IHn'], i.e., the
    Induction Hypothesis for [n'] -- notice that this name is
    explicitly chosen in the [as...] clause of the call to [induction]
    rather than letting Coq choose one arbitrarily). The goal in this
    case becomes [(S n') + 0 = S n'], which simplifies to [S (n' + 0)
    = S n'], which in turn follows from [IHn']. *)
(* [destruct]のように、[induction]タクティックもas...句を取り、サブゴールに導入する際の変数の名前を指定することができます。最初のブランチでは[n]は[0]に置き換えられ、ゴールは[0 + 0 = 0]となり、簡約できる状態になります。二つ目のブランチでは、nはS n'に置き換えられ、[n' + 0 = n']が前提としてコンテキストに付け加えられます。（この際、仮定に[IHn']という名前がつけられます。これは「Induction Hypothesys for [n']（[n']についての帰納法の仮定）」というような意味です。二番目のゴールは[(S n') + 0 = S n']となり、[S (n' + 0) = S n']に簡約されます。次に、帰納法の仮定[IHn']を使って証明の残りを完成させます。 *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(*  (The use of the [intros] tactic in these proofs is actually
    redundant.  When applied to a goal that contains quantified
    variables, the [induction] tactic will automatically move them
    into the context as needed.) *)
(** これらの証明での[intros]タクティックの使用は実際には不要です。量化された変数を含むゴールに適用された場合、[induction]タクティックは必要であるなら、自動的に取り除いて、コンテキストに加えます。*)

(*  **** Exercise: 2 stars, recommended (basic_induction)  *)
(** **** 練習問題: ★★, recommended (basic_induction) *)
(*  Prove the following using induction. You might need previously
    proven results. *)
(** 次の補題を帰納法を用いて証明しなさい。これまでに証明した結果が必要になるかもしれません。*)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 2 stars (double_plus)  *)
(** **** 練習問題: ★★ (double_plus) *)
(*  Consider the following function, which doubles its argument: *)
(** 与えられた引数を二倍する次の関数について考えましょう： *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(*  Use induction to prove this simple fact about [double]: *)
(** [double]についてのシンプルなこの事実を証明するために、帰納法を使いなさい。*)

Lemma double_plus : forall n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 2 stars, optional (evenb_S)  *)
(*  One inconveninent aspect of our definition of [evenb n] is that it
    may need to perform a recursive call on [n - 2]. This makes proofs
    about [evenb n] harder when done by induction on [n], since we may
    need an induction hypothesis about [n - 2]. The following lemma
    gives a better characterization of [evenb (S n)]: *)
(** [evenb n]の定義の不便な面の一つとして、[n - 2]についての再帰呼び出しの実行を必要とするかもしれないことです。このことは[evenb n]に関する証明を[n]に関する帰納法よりも難しいものにします。なぜなら、[n - 2]についての帰納的な仮説を必要とするからです。つぎの補題はもっとよい[evenb (S n)]の特徴づけを行ないます。*)

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star (destruct_induction)  *)
(** **** 練習問題: ★ (destruct_induction) *)
(*  Briefly explain the difference between the tactics [destruct] 
    and [induction]. *)
(** [destruct]と[induction]の違いを短く説明しなさい。
* FILL IN HERE *
*)
(** [] *)

(* ###################################################################### *)
(*  * Proofs Within Proofs *)
(** * 証明の中で行う証明 *)

(*  In Coq, as in informal mathematics, large proofs are often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  But sometimes a proof will require some
    miscellaneous fact that is too trivial and of too little general
    interest to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply state and prove the
    needed "sub-theorem" right at the point where it is used.  The
    [assert] tactic allows us to do this.  For example, our earlier
    proof of the [mult_0_plus] theorem referred to a previous theorem
    named [plus_O_n].  We could instead use [assert] to state and
    prove [plus_O_n] in-line: *)
(** Coqでは（非形式的な数学と同様に）大きな証明は高い頻度で、後に出てきた証明が前に出ている証明を参照するような定理の列に分割されます。しかし時折、証明がいくつかの自明で雑他な事実を必要とし、それがまたトップレベルの名前をつけるほどでもなかったりします。こういう場合、状態を単純化し、すでに使われている定理の右に出現するサブ定理を証明することができれば便利です。[assert]タクティックはこれを可能にしてくれます。例えば、最初の方でやった証明[mult_0_plus]は、[plus_O_n]と名付けられた定理の証明から参照されています。[assert]を使うと[plus_O_n]の証明をこんな風に行うことができます。 *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(*  The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (We can also name the assertion with [as] just as
    we did above with [destruct] and [induction], i.e., [assert (0 + n
    = n) as H].)  Note that we surround the proof of this assertion
    with curly braces [{ ... }], both for readability and so that,
    when using Coq interactively, we can see more easily when we have
    finished this sub-proof.  The second goal is the same as the one
    at the point where we invoke [assert] except that, in the context,
    we now have the assumption [H] that [0 + n = n].  That is,
    [assert] generates one subgoal where we must prove the asserted
    fact and a second subgoal where we can use the asserted fact to
    make progress on whatever we were trying to prove in the first
    place. *)
(** [assert]タクティックは、二つのサブゴールを取り込みます。最初のものは[H:]という接頭辞をつけているように、それ自身を主張するもので、Assertion [H]と呼びます。
（まず注意が必要なのは、上で使用した[destruct]や[induction]に[as]句をつけることで、[assert (0 + n = n) as H]というようにassertionに名前をつけられることです。
もう一つ、証明に出てくるassertionに、[Case]を使ってマーキングしている事も注目です。その理由は、読みやすさのため、というだけでなく、例えばCoqをインタラクティブに使っているとき、証明を進めている間にコンテキストから["Proof of assertion"]という文字列が消える瞬間を観察することで、証明の完了を知ることができます。）二つ目のゴールは、[assert]を呼び出した場合と、コンテキストに[0 + n = n] : [H]という仮定が得られることを除けば同じです。このことから、[assert]は、我々が証明しなければならない事実そのものとなるサブゴールと、その最初のサブゴールの証明がどのような値でも成り立つことを使って証明される事実となる二つ目のサブゴールを作成することが分かります。 *)

(*  The [assert] tactic is handy in many sorts of situations.  For
    example, suppose we want to prove that [(n + m) + (p + q) = (m +
    n) + (p + q)]. The only difference between the two sides of the
    [=] is that the arguments [m] and [n] to the first inner [+] are
    swapped, so it seems we should be able to use the commutativity of
    addition ([plus_comm]) to rewrite one into the other.  However,
    the [rewrite] tactic is a little stupid about _where_ it applies
    the rewrite.  There are three uses of [+] here, and it turns out
    that doing [rewrite -> plus_comm] will affect only the _outer_
    one... *)
(** 実際[assert]は多くのシチュエーションで便利に使えるでしょう。例えば、[(n + m)
+ (p + q) = (m + n) + (p + q)]であることを証明するとしましょう。[=]の両側で異なるのは最初のカッコの中の[+]の両側の[n]と[m]が入れ替わっているだけで、このことは加法の交換法則([plus_comm]）があるものを別のものに書き換えることに使用できることを示しています。しかしながら、[rewrite]タクティックは「どこに適用するか」を考える必要がある場合には少々おばかさんです。ここでは[+]が3箇所で使われていますが[rewrite -> plus_comm]は一番外側（つまり中央）の[+]にしか適用されません。 *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)...
     it seems like plus_comm should do the trick! *)
  (* ここで[(n + m)]を[(m + n)]に入れ替えたいのですが、[plus_comm]でこれができるかと試してみると... *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
  (* うまくいきません。Coqは別のところを[rewrite]してしまいます *)
Abort.

(*  To get [plus_comm] to apply at the point where we want it to, we
    can introduce a local lemma stating that [n + m = m + n] (for the
    particular [m] and [n] that we are talking about here), prove this
    lemma using [plus_comm], and then use it to do the desired
    rewrite. *)
(** [plus_comm]を、適用したいポイントに対して使用するには、まず[n + m = m + n]で始まるような補助定理（ここでは何とかしようとしている[m]と[n]を特定するため）を導き、それを望むrewriteに使用します。 *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.

(* ###################################################################### *)
(*  * More Exercises *)
(** * さらなる練習問題 *)

(*  **** Exercise: 3 stars, recommended (mult_comm)  *)
(** **** 練習問題: ★★★ recommanded (mult_comm) *)
(** Use [assert] to help prove this theorem.  You shouldn't need to
    use induction on [plus_swap]. *)
(** [assert]を使用して以下の証明を完成させなさい。ただしinduction（帰納法）を使用しないこと。 *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.

(*  Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.  You may find that [plus_swap] comes in
    handy.) *)

(** では、乗法が可換であることを証明しましょう。おそらく、補助的な定理を定義し、それを使って全体を証明することになると思います。先ほど証明した[plus_swap]が便利に使えるでしょう。 *)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (more_exercises)  *)
(** **** 練習問題: ★★★, optional (more_exercises) *)
(*  Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before you hack!) *)
(** 紙を用意して、下に続く定理が(a)簡約と書き換えだけで証明可能か、(b)[destruct]を使ったcase分割が必要になるか、(c)帰納法が必要となるか、のいずれに属すかを、紙の上だけで考えなさい。予測を紙に書いたら、実際に証明を完成させなさい。証明にはCoqを用いてかまいません。最初に紙を使ったのは「初心忘れるべからず」といった理由です。 *)

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 2 stars, optional (beq_nat_refl)  *)
(** **** 練習問題: ★★, optional (beq_nat_refl) *)
(*  Prove the following theorem.  (Putting the [true] on the left-hand
    side of the equality may look odd, but this is how the theorem is
    stated in the Coq standard library, so we follow suit.  Rewriting
    works equally well in either direction, so we will have no problem
    using the theorem no matter which way we state it.) *)
(** 次の定理を証明しなさい。左辺を[true]と置いてあることが奇妙に感じられるかもしれません。しかし、標準ライブラリの中で定理はこのように提示されているからで、我々もそれに従います。書き換えはどちらか一方の方向に上手く動作するので、定理の記述されている方向に関係なく、定理を使う上で問題になることはありません。*)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(*  **** Exercise: 2 stars, optional (plus_swap')  *)
(** **** 練習問題: ★★, optional (plus_swap') *)
(*  The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to: [replace (t) with (u)]
   replaces (all copies of) expression [t] in the goal by expression
   [u], and generates [t = u] as an additional subgoal. This is often
   useful when a plain [rewrite] acts on the wrong part of the goal.

    Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)]. *)
(** [replace]タクティックは、特定のサブタームを置き換えたいものと置き換えることができます。もう少し正確に言うと、[replace (t) with (u)]は、ゴールにある[t]という式を全て[u]にかきかえ、[t = u]というサブゴールを追加します。この機能は、通常の[rewrite]がゴールの思い通りの場所に作用してくれない場合に有効です。

[replace]タクティックを使用して[plus_swap']の証明をしなさい。ただし[plus_swap]のように[assert (n + m = m + n)]を使用しないで証明を完成させなさい。
*)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, recommended (binary_commute)  *)
(** **** 練習問題: ★★★ (binary_commute) *)
(*  Recall the [increment] and [binary-to-unary] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that these functions commute:
    
               bin --------- incr -------> bin
                |                           |
            bin_to_nat                  bin_to_nat
                |                           |
                v                           v
               nat ---------- S ---------> nat

    That is, incrementing a binary number and then converting it to 
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.  
    Name your theorem [bin_to_nat_pres_incr] ("pres" for "preserves").

    Before you start working on this exercise, please copy the
    definitions from your solution to the [binary] exercise here so
    that this file can be graded on its own.  If you find yourself
    wanting to change your original definitions to make the property
    easier to prove, feel free to do so! *)

(** [Basics_J]の章の[binary]の練習問題で書いた[increment]と[binary-to-unary]関数を思い出してください。それらの関数が可換であること、

               bin --------- incr -------> bin
                |                           |
            bin_to_nat                  bin_to_nat
                |                           |
                v                           v
               nat ---------- S ---------> nat

すなわち、bin値をインクリメントしたあとに自然数に変換すること、bin値を自然数に変換したあとにインクリメントしたものとが同じ結果になることを証明しなさい。 この練習問題にとりかかる前に、このファイルはそれ自体が成績を付ける対象になるため、[binary]の練習問題のあなたの解法からここへコピーしてください。もしあなたの元々の定義を証明を簡単にするために変えたくなったら、自由に変えてください。
*)

(* FILL IN HERE *)
(** [] *)


(*  **** Exercise: 5 stars, advanced (binary_inverse)  *)
(** **** 練習問題: ★★★★★ (binary_inverse) *)
(*  This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    there to complete this one.

    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, this is not true!
        Explain what the problem is.

    (c) Define a "direct" normalization function -- i.e., a function
        [normalize] from binary numbers to binary numbers such that,
        for any binary number b, converting to a natural and then back
        to binary yields [(normalize b)].  Prove it.  (Warning: This
        part is tricky!)

    Again, feel free to change your earlier definitions if this helps
    here. *)
(** この練習問題は前の問題の続きで、2進数に関するものである。前の問題で作成された定義や定理をここで用いてもよい。
(a) まず自然数を2進数に変換する関数を書きなさい。そして「任意の自然数からスタートし、それを2進数にコンバートし、それをさらに自然数にコンバートすると、スタート時の自然数に戻ることを証明しなさい。
(b) あなたはきっと、逆方向についての証明をしたほうがいいのでは、と考えているでしょう。それは、任意の2進数から始まり、それを自然数にコンバートしてから、また2進数にコンバートし直したものが、元の自然数と一致する、という証明です。しかしながら、この結果はtrueにはなりません。！！その原因を説明しなさい。

(c) 2進数を引数として取り、それを一度自然数に変換した後、また2進数に変換したものを返すnormalize関数を作成し、証明しなさい。
 もう一度言いますが、以前のあなたの定義を変更するのは自由です。もしそれがここで役に立つならば。
 *)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(*  * Formal vs. Informal Proof (Optional) *)
(** * 形式的証明と非形式的証明(Optional) *)

(*  "_Informal proofs are algorithms; formal proofs are code_." *)
(** "非形式的な証明はアルゴリズムであり、形式的な証明はコードである" *)

(*  The question of what constitutes a proof of a mathematical
    claim has challenged philosophers for millennia, but a rough and
    ready definition could be this: A proof of a mathematical
    proposition [P] is a written (or spoken) text that instills in the
    reader or hearer the certainty that [P] is true.  That is, a proof
    is an act of communication.

    Acts of communication may involve different sorts of readers.  On
    one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is that [P] can be mechanically
    derived from a certain set of formal logical rules, and the proof
    is a recipe that guides the program in checking this fact.  Such
    recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    and will thus necessarily be _informal_.  Here, the criteria for
    success are less clearly specified.  A "valid" proof is one that
    makes the reader believe [P].  But the same proof may be read by
    many different readers, some of whom may be convinced by a
    particular way of phrasing the argument, while others may not be.
    Some readers may be particularly pedantic, inexperienced, or just
    plain thick-headed; the only way to convince them will be to make
    the argument in painstaking detail.  But other readers, more
    familiar in the area, may find all this detail so overwhelming
    that they lose the overall thread; all they want is to be told the
    main ideas, since it is easier for them to fill in the details for
    themselves than to wade through a written presentation of them.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.

    In practice, however, mathematicians have developed a rich set of
    conventions and idioms for writing about complex mathematical
    objects that -- at least within a certain community -- make
    communication fairly reliable.  The conventions of this stylized
    form of communication give a fairly clear standard for judging
    proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can
    completely forget about informal ones!  Formal proofs are useful
    in many ways, but they are _not_ very efficient ways of
    communicating ideas between human beings. *)
(** 数学的に厳格な証明を構成するとはどういうことなのか、という問題は、千年もの間哲学者を悩ませてきました。しかし少々雑な定義でよければ次のように書くこともができます。数学的な命題[P]の証明とは、それを読む（あるいは聞く）人をして、[P]がtrueであることを納得せしめる文章を書く（語る）ことである、と。このことから、証明はコミュニケーション行為であると言えるでしょう。
さて、このコミュニケーションの相手は、二種類に分けることができます。一方は、Coqのプログラムのように振る舞うような場合で、このケースでの「信用に値する」というのは、[P]が形式的論理のルールに基づく確実な論理から導かれたもので、その証明が、このチェックを行うプログラムをガイドする秘訣になっているようなものです。そんな秘訣が「形式的証明」です。

一方、読者が人間的な存在で、証明が英語などの自然言語で書かれているようなケースは「非形式的証明」であると言えます。こんなケースでの成功の条件は「あまりきちんと明示しないこと」です。とにかく、読んでいる人に納得させてしまえる証明こそが「よい証明」なのです。しかしひとつの証明を複数の読者が見るような場合、ある論点について、ある人は特定の言い回しによって核心に至るかもしれませんが、人によってはそうではないかもしれません。もっと極端な人は、ただ知ったかぶりをする割りに経験は浅い、単なる「頭でっかち」であるかもしれません。そういった人たちを押しなべて納得させる唯一の方法は、ただ骨身を惜しまず細かいところまで論じることなのです。逆にある読者はこういったことに精通しているあまり、細かいことにこだわりすぎて全体的な流れを見失う、ということもあります。多くの人が望んでいることは総論としてどうなのか、ということを知ることで、細かいことを考えていくことは面倒なものです。結局のところ、非形式的な証明でみんなを納得させる標準的な方法はなさそうです。なぜなら、非形式的な書き方で想定される読者全員を納得させる方法はないからです。しかし実際のところ、数学者は複雑な数学的事柄についてたくさんの表記規則のおかげで、証明が正しいか否かを判断するための標準的かつ公正な方法がもたらされたのです。

我々はこのコースでCoqを使用しているのですから、それだけできちんと形式化された証明に乗っていると言えます。しかしこのことは、非形式的な表現を無視していい、ということではありません。形式的証明は多くの場合有効ですが、人と人との間で考えを伝えあう際には必ずしも効率的とは言えないものです。 *)

(*  For example, here is a proof that addition is associative: *)
(** 例えば、下の例は加法が結合的であることを示すものです。 *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(*  Coq is perfectly happy with this.  For a human, however, it
    is difficult to make much sense of it.  We can use comments and
    bullets to show the structure a little more clearly... *)
(** Coqはこのような証明を完璧にこなしてくれますが、上の証明は人間にとってはいささかのみこみにくいと言わざるを得ません。 証明の構造をもう少しはっきりさせるために、コメントやバレットを使うことが出来ます。*)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(*  ... and if you're used to Coq you may be able to step
    through the tactics one after the other in your mind and imagine
    the state of the context and goal stack at each point, but if the
    proof were even a little bit more complicated this would be next
    to impossible.

    A (pedantic) mathematician might write the proof something like
    this: *)
(** ...そして、もしあなたがCoqに十分慣れていて、タクティックを次々と適用しながら証明を進めていき、コンテキストやゴールがどう変化していくかを頭の中だけでイメージしていくことができるようなレベルの人でも、上の証明はかなり複雑で、ほとんど理解不能に思えるかもしれません。

(訳知り顔の)数学者は証明をこんな風に書くでしょう。*)

(*  - _Theorem_: For any [n], [m] and [p],

      n + (m + p) = (n + m) + p.

    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show

        0 + (m + p) = (0 + m) + p.

      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where

        n' + (m + p) = (n' + m) + p.

      We must show

        (S n') + (m + p) = ((S n') + m) + p.

      By the definition of [+], this follows from

        S (n' + (m + p)) = S ((n' + m) + p),

      which is immediate from the induction hypothesis.  _Qed_. *)
(** - 定理：任意の[n],[m],[p]について、以下が成り立つ
[[
n + (m + p) = (n + m) + p.
]]
証明：[n]について帰納法を適用する。

- まず[n = 0]と置くと、以下のようになる
[[
0 + (m + p) = (0 + m) + p.
]]
これは、[+]の定義から直接導くことができる。

- 次に[n = S n']と置き、帰納法の仮定を
[[
n' + (m + p) = (n' + m) + p.
]]
とすると、以下のような式が立つ。
[[
(S n') + (m + p) = ((S n') + m) + p.
]]
ここで、[+]の定義より、以下のように変形できる。
[[
S (n' + (m + p)) = S ((n' + m) + p),
]]
これは、直後の値について帰納法の仮定が成り立つことを示している。 [] *)

(*  The overall form of the proof is basically similar, and of
    course this is no accident: Coq has been designed so that its
    [induction] tactic generates the same sub-goals, in the same
    order, as the bullet points that a mathematician would write.  But
    there are significant differences of detail: the formal proof is
    much more explicit in some ways (e.g., the use of [reflexivity])
    but much less explicit in others (in particular, the "proof state"
    at any given point in the Coq proof is completely implicit,
    whereas the informal proof reminds the reader several times where
    things stand). *)
(** どちらの表現も、やっていることは基本的に同じことです。これはもちろん偶然ではなく、Coqの[induction]タクティックが、数学者が考えるのと同じ目標を、同じサブゴールとして、同じ順番で作成するように作られているだけです。しかしこの二つをよく見ると、重要な違いがあります。形式的証明は、ある部分（[reflexivity]を使っている部分など）ではより明示的ですが、それ以外のところはあまり明示的ではありません。特にあるポイントにおける証明の状態が、Coqの証明では明示されていません。一方、非形式的証明は、途中で何度も「今どのあたりで、どのようになっているか」を思い出させてくれるような書き方になっています。 *)


(*  **** Exercise: 2 stars, advanced, recommended (plus_comm_informal)  *)
(** **** 練習問題: ★★, advanced, recommended (plus_comm_informal)  *)
(*  Translate your solution for [plus_comm] into an informal proof. *)
(** plus_commの証明を、非形式的な証明に書き換えなさい。 *)
(*  Theorem: Addition is commutative.

    Proof: (* FILL IN HERE *)
[]
*)
(** 定理：加法は可換である。 

    Proof: (* FILL IN HERE *)
[]
*)

(*  **** Exercise: 2 stars, optional (beq_nat_refl_informal)  *)
(** **** 練習問題: ★★, optional (beq_nat_refl_informal) *)
(*  Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!

    Theorem: [true = beq_nat n n] for any [n].
*)
(** 次の証明を、[plus_assoc] の非形式的な証明を参考に書き換えなさい。Coqのタクティックを単に言い換えただけにならないように！

定理：true=beq_nat n n forany n.（任意のnについて、nはnと等しいという命題がtrueとなる）

    Proof: (* FILL IN HERE *)
[] *)

(** $Date: 2016-05-26 16:17:19 -0400 (Thu, 26 May 2016) $ *)
