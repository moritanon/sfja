(*  * ProofObjects: The Curry-Howard Correspondence *)
(** * 証明オブジェクト: カーリー-ハワード対応 *)

(** "_Algorithms are the computational content of proofs_."  --Robert Harper *)

Require Export IndProp.

(*  We have seen that Coq has mechanisms both for _programming_,
    using inductive data types like [nat] or [list] and functions over
    these types, and for _proving_ properties of these programs, using
    inductive propositions (like [ev]), implication, universal
    quantification, and the like.  So far, we have mostly treated
    these mechanisms as if they were quite separate, and for many
    purposes this is a good way to think.  But we have also seen hints
    that Coq's programming and proving facilities are closely related.
    For example, the keyword [Inductive] is used to declare both data
    types and propositions, and [->] is used both to describe the type
    of functions on data and logical implication.  This is not just a
    syntactic accident!  In fact, programs and proofs in Coq are
    almost the same thing.  In this chapter we will study how this
    works.

    We have already seen the fundamental idea: provability in Coq is
    represented by concrete _evidence_.  When we construct the proof
    of a basic proposition, we are actually building a tree of
    evidence, which can be thought of as a data structure.

    If the proposition is an implication like [A -> B], then its proof
    will be an evidence _transformer_: a recipe for converting
    evidence for A into evidence for B.  So at a fundamental level,
    proofs are simply programs that manipulate evidence. *)
(** これまでに、Coqが、帰納的に定義された([list]や[nat]などの)データ型とそれら型上の関数を使用したプログラミング(_programming_)の側面と、これらのプログラムの性質を帰納的に定義された([ev]や[eq]などの)命題や含意、全称記号を使用して証明すること(_proving_)の両方のメカニズムを持つことを見て来ました。 いままでのところ、これらのメカニズムを全然別のものであるかのように取り扱ってきました。このことは多くの目的に適います。しかし、Coqのプログラミングと証明のための機能は密接に関係しています。例えば、[Inductive]というキーワードは、データ型と命題の両方の宣言に用いられますし、[->]は、関数の型と論理的な含意の記述の両方に使用されます。これは単なる偶然ではありません。実際、Coqにおいて、プログラムと証明はほとんど同じものです。この章において、Coqがどのように動くのかを学びましょう。
我々はすでに根本的なアイデアを見て来ています。Coqにおける証明可能性は具体的な根拠[_evidence_]において表現されており、我々は実際に根拠の木を構築し、その木はデータ構造と同じものであると考えることが出来ます。もし命題が、[A -> B]のような含意を持っていれば、その証明はBの根拠のためにAの根拠を変換するためのレシピになるでしょう。そのため根本的なレベルにおいては、証明は単純なことに根拠を操作するプログラムなのです。 *)

(*  Question: If evidence is data, what are propositions themselves?

    Answer: They are types!

    Look again at the formal definition of the [ev] property.  *)
(**
   Q. もし根拠がデータなら、命題自身はなんなのでしょう？
      
   A. 型なんです!

   [ev]属性の形式的定義をもう一度見直してみましょう。
*)
Print ev.
(* ==>
  Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS : forall n, ev n -> ev (S (S n)).
*)

(** Suppose we introduce an alternative pronunciation of "[:]".
    Instead of "has type," we can say "is a proof of."  For example,
    the second line in the definition of [ev] declares that [ev_0 : ev
    0].  Instead of "[ev_0] has type [ev 0]," we can say that "[ev_0]
    is a proof of [ev 0]." *)
(** [:]を「--の型を持っている」の代わりに、「--の証明である」と読むものであると仮定してみましょう。
例えば、[ev]の定義の二行目で[ev_0 : ev 0]と宣言しているところで、 [ev 0]は型[ev 0]を持つ。の代わりに、[ev_0は、ev 0]の証明である。と読みます。
*)

(*  This pun between types and propositions -- between [:] as "has type"
    and [:] as "is a proof of" or "is evidence for" -- is called the
    _Curry-Howard correspondence_.  It proposes a deep connection
    between the world of logic and the world of computation:

                 propositions  ~  types
                 proofs        ~  data values

    See [Wadler 2015] for a brief history and an up-to-date exposition.

    Many useful insights follow from this connection.  To begin with,
    it gives us a natural interpretation of the type of the [ev_SS]
    constructor: *)
(** この型と命題の間の類似性([:]の"型である"と"その証明または根拠である"ということ)はカーリーハワード対応と呼ばれます。この対応は、計算機の世界と論理の世界の間に深い関係があることを示唆します。

	 命題          ~   型
	 証明          ~   データ値

     [Wadler 2015]において、簡単な歴史と、今までの変遷を見ることが出来ます。

	この関係から多くの有用な洞察が導かれます。まず、[ev_SS]コンストラクタの型の自然な解釈を得られます: *)

Check ev_SS.
(* ===> ev_SS : forall n,
                  ev n ->
                  ev (S (S n)) *)

(** This can be read "[ev_SS] is a constructor that takes two
    arguments -- a number [n] and evidence for the proposition [ev
    n] -- and yields evidence for the proposition [ev (S (S n))]." *)
(** これは次のように読むことが出来ます。"[ev_SS]は、二つの引数、--数[n]と[ev n]という命題の根拠と--を取るコンストラクタであり、
[ev (S (S n))]という命題の根拠を生成します。"*)

(** Now let's look again at a previous proof involving [ev]. *)

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** As with ordinary data values and functions, we can use the [Print]
    command to see the _proof object_ that results from this proof
    script. *)

Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)
     : ev 4  *)

(** As a matter of fact, we can also write down this proof object
    _directly_, without the need for a separate proof script: *)

Check (ev_SS 2 (ev_SS 0 ev_0)).
(* ===> ev 4 *)

(*  The expression [ev_SS 2 (ev_SS 0 ev_0)] can be thought of as
    instantiating the parameterized constructor [ev_SS] with the
    specific arguments [2] and [0] plus the corresponding proof
    objects for its premises [ev 2] and [ev 0].  Alternatively, we can
    think of [ev_SS] as a primitive "evidence constructor" that, when
    applied to a particular number, wants to be further applied to
    evidence that that number is even; its type,

      forall n, ev n -> ev (S (S n)),

    expresses this functionality, in the same way that the polymorphic
    type [forall X, list X] expresses the fact that the constructor
    [nil] can be thought of as a function from types to empty lists
    with elements of that type. *)
(** [ev_SS 2 (ev_SS 0 ev_0)]という式は、パラメータ付きコンストラクタ[ev_SS]を特定の引数[2]と[0]および、前提である[beautiful 3]と[beautiful 5]に対応する証明オブジェクトを指定して呼び出して、実体化させていると考えることが出来ます。あるいは、[b_sum]は二つの特定の数が適用されたときに、さらに、二つの数がbeautifulである根拠が適用されることを求めるプリミティブな根拠構築器であると考えることも出来ます。
その型は、forall n m, beautiful n -> beautiful m -> beautiful (n+m),です。
前の章において、多相的な型[forall X, list X]がコンストラクタ [nil]がその型の要素の空リストを生成する関数であるのと同じことです。
*)

(*  We saw in the [Logic] chapter that we can use function
    application syntax to instantiate universally quantified variables
    in lemmas, as well as to supply evidence for assumptions that
    these lemmas impose.  For instance: *)
(** [Logic]の章で見たように補題の中の全称化された変数を裏付けるために、また、これらの補題が導入した仮定に根拠を与えるために。関数適用の構文が使用することが出来たこを覚えているかもしれません。例えば:*)

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

(** We can now see that this feature is a trivial consequence of the
    status the Coq grants to proofs and propositions: Lemmas and
    hypotheses can be combined in expressions (i.e., proof objects)
    according to the same basic rules used for programs in the
    language. *)
(** この特質が Coqが証明や命題を扱うことを可能にする状態の小さな並びであることが分かると思います:
  補題や仮説は式と結合し(たとえば、証明オブジェクト) 同じ基本的な、言語内のプログラムのための規則に従います。*)


(* ################################################################# *)
(*  * Proof Scripts *)
(** * 証明スクリプト *)

(** The _proof objects_ we've been discussing lie at the core of how
    Coq operates.  When Coq is following a proof script, what is
    happening internally is that it is gradually constructing a proof
    object -- a term whose type is the proposition being proved.  The
    tactics between [Proof] and [Qed] tell it how to build up a term
    of the required type.  To see this process in action, let's use
    the [Show Proof] command to display the current state of the proof
    tree at various points in the following tactic proof. *)
(** これまで議論してきた_証明オブジェクト_は、Coqの動作の中心です。Coqが証明スクリプトを動かすとき、内部的に起こっていることは、証明オブジェクトを徐々に作りあげていることです。ある項の、その型が証明済みの命題であるような。です。
[Proof]と[Qed]の間にあるタクティックは要求された型の項をどのように構築すればよいのか教えてくれます。[Show Proof]コマンドを使って証明木の現在の状態をタクティックの証明中のいろいろな時点で表示してみましょう。*)

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

(*  At any given moment, Coq has constructed a term with a
    "hole" (indicated by [?Goal] here, and so on), and it knows what
    type of evidence is needed to fill this hole.  *)
(** どの瞬間もCoqは穴を持った項([?Goal]などで示される)を構築していて、それぞれの穴にどんな型の根拠が必要になるかを知っています。 *)

(** Each hole corresponds to a subgoal, and the proof is
    finished when there are no more subgoals.  At this point, the
    evidence we've built stored in the global context under the name
    given in the [Theorem] command. *)
(**    それぞれの穴にはサブゴールが対応しており、証明は、サブゴールがすべて無くなったときに終了します。この時において、[Theorem]コマンドは我々が構築した根拠に名前を与え、グローバルなコンテキストにそれを追加します。 *)

(*  Tactic proofs are useful and convenient, but they are not
    essential: in principle, we can always construct the required
    evidence by hand, as shown above. Then we can use [Definition]
    (rather than [Theorem]) to give a global name directly to a
    piece of evidence. *)
(** タクティックにようる証明は、使いやすいのですが、本質的ではありません。原理的に、われわれは上で見たように、必要とされる根拠を手でいつでも構築することが出来ます。それから、[Definition]コマンドを(むしろ[Theorem]コマンドより)根拠の断片にグローバルな名前を与えるために使っています。*)


Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

(*  All these different ways of building the proof lead to exactly the
    same evidence being saved in the global environment. *)
(** 証明を構築する方法のいろいろありますが、全て皆同じ根拠がグローバル環境にセーブされます。*)

Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

(** **** Exercise: 1 star (eight_is_even)  *)
(** **** 練習問題: ★ (eight_is_even)  *)
(** Give a tactic proof and a proof object showing that [ev 8]. *)
(** [ev 8]であるということを示すタクティックによる証明と証明オブジェクトを書きなさい。*)

Theorem ev_8 : ev 8.
Proof.
  (* FILL IN HERE *) Admitted.

Definition ev_8' : ev 8 :=
  (* FILL IN HERE *) admit.
(** [] *)

(* ##################################################### *)
(*  * Quantifiers, Implications, Functions *)
(** 全称量化、含意、関数 *)

(*  In Coq's computational universe (where data structures and
    programs live), there are two sorts of values with arrows in their
    types: _constructors_ introduced by [Inductive]-ly defined data
    types, and _functions_.

    Similarly, in Coq's logical universe (where we carry out proofs),
    there are two ways of giving evidence for an implication:
    constructors introduced by [Inductive]-ly defined propositions,
    and... functions!

    For example, consider this statement: *)
(** Coqにおける計算機の世界(この章までは我々はほとんどそこに住んでいました)において、二つの種類の、型の中に矢印を持つ値があります。
再帰的[Inductive]に定義されることによって導入されるコンスラクタ(_constructors_)と関数(_function_)	です 

同様に、Coqの論理の世界において、含意のための根拠を与える二つの方法があります。再帰的[Inductive]に定義される命題と...そう。関数です!

例として次の文を考えましょう。 *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

(*  What is the proof object corresponding to [ev_plus4]?

    We're looking for an expression whose _type_ is [forall n, ev n ->
    ev (4 + n)] -- that is, a _function_ that takes two arguments (one
    number and a piece of evidence) and returns a piece of evidence!
    Here it is: *)
(** [ev_plus4]に対応する証明オブジェクトはどのようなものでしょうか？

われわれは、型(_type_)が[forall n, ev n -> ev (4 + n)]である式を探します。すなわち、二つの引数(一つの数値と根拠の断片)を取って、根拠の断片を返す関数(_function_)です! *)

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'.
(* ===> ev_plus4' : forall n : nat, ev n -> ev (4 + n) *)

(** Recall that [fun n => blah] means "the function that, given [n],
    yields [blah]," and that Coq treats [4 + n] and [S (S (S (S n)))]
    as synonyms. Another equivalent way to write this definition is: *)
(** [fun n => blah]は、関数を意味し、その関数は[n]が与えられたら、[blah]を返すものであり、Coqは、[4+n]と[S (S (S (S n)))]
を同義として扱うことを意味することを思いだしましょう。
この定義を書くもう一つの等価な方法は、以下の通りです。 *)

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.
(* ===> ev_plus4'' : forall n : nat, ev n -> ev (4 + n) *)

(** When we view the proposition being proved by [ev_plus4] as a
    function type, one aspect of it may seem a little unusual. The
    second argument's type, [ev n], mentions the _value_ of the first
    argument, [n].  While such _dependent types_ are not found in
    conventional programming languages, they can be useful in
    programming too, as the recent flurry of activity in the
    functional programming community demonstrates.

    Notice that both implication ([->]) and quantification ([forall])
    correspond to functions on evidence.  In fact, they are really the
    same thing: [->] is just a shorthand for a degenerate use of
    [forall] where there is no dependency, i.e., no need to give a
    name to the type on the left-hand side of the arrow. *)
(** [ev_plus4]によって証明される命題を関数型として見るときに、その一つの局面はあまり役に立たないように見えるかもしれません。
二つめの引数の型、[ev n]は最初の引数である[n]の値に言及します。一方そのような依存型(_dependent types_)は通常のプログラミング言語ではあまり見られませんが、それらはとても有用なものなのです。 最近の関数型言語界隈では実装する動きが見られます。

含意[->]と全称量化([forall])は根拠上の関数に対応しています。実際に、それらは本当に同じものです。[->]は、依存性が存在しない場合の[forall]の短縮記法にすぎません。つまり、矢印の左側の型に名前を与える必要がないような場合です。 *)

(*  For example, consider this proposition: *)
(** 例としてこの命題について考えてみましょう *)

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

(*  A proof term inhabiting this proposition would be a function
    with two arguments: a number [n] and some evidence [E] that [n] is
    even.  But the name [E] for this evidence is not used in the rest
    of the statement of [ev_plus2], so it's a bit silly to bother
    making up a name for it.  We could write it like this instead,
    using the dummy identifier [_] in place of a real name: *)
(* この命題を継承する項は数 [n]と [n]が偶数であるという根拠[E]の二つの引数を取る関数になるでしょう。
しかしこの根拠のための名前[E]は[ev_plus2]の残りの文の中で使われません。そのための名前を考えだすために手間をかけることは少しばかばかしいように思われます。以上の代わりにダミーの識別子[_]を用いて以下のように書くことが出来ます。*)

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

(*  Or, equivalently, we can write it in more familiar notation: *)
(** あるいは、もっと書き慣れた方法で書くことも出来ます。 *)
 
Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

(*  In general, "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)
(** 一般的に、"[P -> Q]"というのは、"[forall (_:P), Q]"の糖衣構文です *)

(* ################################################################# *)
(*  * Programming with Tactics *)
(** * タクティックによるプログラミング *)

(*  If we can build proofs by giving explicit terms rather than
    executing tactic scripts, you may be wondering whether we can
    build _programs_ using _tactics_ rather than explicit terms.
    Naturally, the answer is yes! *)
(** 明示的な項を使用して証明を構築できるならば、明示的な項ではなく、タクティックを使用してプログラムを構築することが出来るのでしょうか？
もちろん出来ます ! *)

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.
(* ==>
    add1 = fun n : nat => S n
         : nat -> nat
*)

Compute add1 2.
(* ==> 3 : nat *)

(** Notice that we terminate the [Definition] with a [.] rather than
    with [:=] followed by a term.  This tells Coq to enter _proof
    scripting mode_ to build an object of type [nat -> nat].  Also, we
    terminate the proof with [Defined] rather than [Qed]; this makes
    the definition _transparent_ so that it can be used in computation
    like a normally-defined function.  ([Qed]-defined objects are
    opaque during computation.)

    This feature is mainly useful for writing functions with dependent
    types, which we won't explore much further in this book.  But it
    does illustrate the uniformity and orthogonality of the basic
    ideas in Coq. *)
(**  ここで[Definition]を[:=]とそれに続く項ではなく、[.]で終了させたことに気を付けましょう。
このことはCoqに対して、[nat->nat]型を持つオブジェクトを生成するために、証明スクリプトモードに入ることを告げるものです。
それから、[Qed]ではなく、[Defined]で証明を終わらせたことにも気を付けましょう。これは、定義を普通に定義された関数のように
_透過的_に使用出来るようにしてくれます。([Qed]で定義されたオブジェクトは、計算の上では、不透過です。)

この特徴は、依存型を使って関数を書くのに主に使われますが、この本では深入りしません。しかしこれはCoqの基本的な
概念の統一性と直交性を示すものです。*)

(* ################################################################# *)
(*  * Logical Connectives as Inductive Types *)
(** * 帰納的な型としての論理結合子 *)

(** Inductive definitions are powerful enough to express most of the
    connectives and quantifiers we have seen so far.  Indeed, only
    universal quantification (and thus implication) is built into Coq;
    all the others are defined inductively.  We'll see these
    definitions in this section. *)
(** 帰納的な定義は、これまで見てきたように、結合子と量化子の殆どを表現するのに十分な力を備えています。確かに全称記号(と、含意)はCoqに組込まれています;
すべての他のものは、帰納的に定義されています。このセクションでこれらの定義を見てみましょう *)

Module Props.

(*  ** Conjunction

    To prove that [P /\ Q] holds, we must present evidence for both
    [P] and [Q].  Thus, it makes sense to define a proof object for [P
    /\ Q] as consisting of a pair of two proofs: one for [P] and
    another one for [Q]. This leads to the following definition. *)
(** ** 連言 

  [P /\ Q]を証明するために、[P]と[Q]の両方の根拠を提示しなければなりません。それゆえ、
  [P /\ Q]の証明オブジェクトを二つの証明のペア([P]のために一つと、[Q]のために一つです)を構成するように定義することは必然です。
  このことは次の定義を導きます。*)
*)
Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.

(*  Notice the similarity with the definition of the [prod] type,
    given in chapter [Poly]; the only difference is that [prod] takes
    [Type] arguments, whereas [and] takes [Prop] arguments. *)
(** [Poly」の章の[prod]型の定義との類似性に注目してください。違いは[prod]が、[Type]を引数にとり、[and]が[Prop]を引数に取るという点だけです。*)

Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

(*  This should clarify why [destruct] and [intros] patterns can be
    used on a conjunctive hypothesis.  Case analysis allows us to
    consider all possible ways in which [P /\ Q] was proved -- here
    just one (the [conj] constructor).  Similarly, the [split] tactic
    actually works for any inductively defined proposition with only
    one constructor.  In particular, it works for [and]: *)
(** このことは、なぜ[destruct]と[intros]が連言の仮説に使用されるかについて明確にしてくれます。
ケース分析によって、[P/\Q]が証明される有り得るすべてのルートについて考えることが可能になります。
-- この場合は、[conj]コンストラクタ一つしかありませんが...
同様に、[split]タクティックは帰納的に定義された一つしかコンスラクタを持たないような命題についても実際に動作します。
とりわけ、[and]については特に。*)

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

(*  This shows why the inductive definition of [and] can be
    manipulated by tactics as we've been doing.  We can also use it to
    build proofs directly, using pattern-matching.  For instance: *)
(** このことは、[and]の帰納的定義がなぜ、タクティックによってこれまで行なわれてきたように操作されうるかを示しています。
パターンマッチを用いて直接に証明を組み立てるためにandを使うことが出来ます。例えば *)

Definition and_comm'_aux P Q (H : P /\ Q) :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(*  **** Exercise: 2 stars, optional (conj_fact)  *)
(** **** 練習問題: ★★, optional (conj_fact)  *)
(*  Construct a proof object demonstrating the following proposition. *)
(** 次の命題を立証する証明オブジェクトを構築しなさい *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(*  ** Disjunction

    The inductive definition of disjunction uses two constructors, one
    for each side of the disjunct: *)
(** ** 選言

    選言の帰納的定義は二つのコンストラクタを使います。それぞれが選言の枝になります。*)

Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

End Or.

(*  This declaration explains the behavior of the [destruct] tactic on
    a disjunctive hypothesis, since the generated subgoals match the
    shape of the [or_introl] and [or_intror] constructors.

    Once again, we can also directly write proof objects for theorems
    involving [or], without resorting to tactics. *)
(** この宣言は、選言的仮説上での[destruct]タクティックのふるまいを説明します。
    生成されたサブゴールは[or_introl]と[or_intror]コンストラクタの形にマッチします。

    ここでも、[or]を含む定理のための証明オブジェクトをタクティックに頼ることなく、直接書くことが出来ます。*)

(*  **** Exercise: 2 stars, optional (or_commut'')  *)
(** **** 練習問題: ★★, optional (or_commut'')  *)
(*  Try to write down an explicit proof object for [or_commut] (without
    using [Print] to peek at the ones we already defined!). *)
(** 明示的な証明オブジェクトをすでに定義したそれを[Print]を使って覗くことなく、書下してみましょう *)

Definition or_comm : forall P Q, P \/ Q -> Q \/ P 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** ** Existential Quantification

    To give evidence for an existential quantifier, we package a
    witness [x] together with a proof that [x] satisfies the property
    [P]: *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

End Ex.

(** This may benefit from a little unpacking.  The core definition is
    for a type former [ex] that can be used to build propositions of
    the form [ex P], where [P] itself is a _function_ from witness
    values in the type [A] to propositions.  The [ex_intro]
    constructor then offers a way of constructing evidence for [ex P],
    given a witness [x] and a proof of [P x].

    The more familiar form [exists x, P x] desugars to an expression
    involving [ex]: *)

Check ex (fun n => ev n).
(* ===> exists n : nat, ev n
        : Prop *)

(** Here's how to define an explicit proof object involving [ex]: *)

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(** **** 練習問題: ★ ★s, optional (ex_ev_Sn)  *)
(** Complete the definition of the following proof object: *)

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
(* FILL IN HERE *) admit.
(** [] *)

(** ** [True] and [False] *)

(** The inductive definition of the [True] proposition is simple: *)

Inductive True : Prop :=
  I : True.

(** It has one constructor (so every proof of [True] is the same, so
    being given a proof of [True] is not informative.) *)

(** [False] is equally simple -- indeed, so simple it may look
    syntactically wrong at first glance! *)

Inductive False : Prop :=.

(** That is, [False] is an inductive type with _no_ constructors --
    i.e., no way to build evidence for it. *)

End Props.

(* ################################################################# *)
(* ###################################################### *)
(** * Equality *)

(** Even Coq's equality relation is not built in.  It has the
    following inductive definition.  (Actually, the definition in the
    standard library is a small variant of this, which gives an
    induction principle that is slightly easier to use.) *)
(** Coqには、等価という関係すら組み込まれていませんから、次のように帰納的に定義
    してやります。(実際にはcoqの標準ライブラリでは、これのちょっと違う版が定義されています。帰納の原理がちょっぴり使いやすくなっています。
Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x = y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

(*  The way to think about this definition is that, given a set [X],
    it defines a _family_ of propositions "[x] is equal to [y],"
    indexed by pairs of values ([x] and [y]) from [X].  There is just
    one way of constructing evidence for each member of this family:
    applying the constructor [eq_refl] to a type [X] and a value [x :
    X] yields evidence that [x] is equal to [x]. *)
(** この定義の考え方は次のようなものです。集合 [X] が与えられると、「集合 [X] に属する値 ([x] and [y]) にインデックスされた、[x] は [y] に等しい」というような命題の _集団_ を定義してくれるということです。
この集団に属する命題に根拠を与えるためには、一つの方法しかありません。それは、コンストラクタ [refl_equal] に型 [X] とその値[x : X] を適用し、[x] が [x] と等しいという根拠を生成することです。*)

(** **** 練習問題: ★ ★s (leibniz_equality)  *)
(** **** 練習問題: ★ ★s (leibniz_equality)  *)
(*  The inductive definition of equality corresponds to _Leibniz
    equality_: what we mean when we say "[x] and [y] are equal" is
    that every property on [P] that is true of [x] is also true of
    [y].  *)
(** 同値性の帰納的定義は、ライプニッツの同値性と対応しています。ライプニッツの同値性とは、[x] と [y] が等しいということは、 任意の命題 [P] が[x] でtrueとなるならば [y] でもtrueとなる」ということです。

Lemma leibniz_equality : forall (X : Type) (x y: X),
  x = y -> forall P:X->Prop, P x -> P y.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(*  We can use [eq_refl] to construct evidence that, for example, [2 =
    2].  Can we also use it to construct evidence that [1 + 1 = 2]?
    Yes, we can.  Indeed, it is the very same piece of evidence!  The
    reason is that Coq treats as "the same" any two terms that are
    _convertible_ according to a simple set of computation rules.
    These rules, which are similar to those used by [Compute], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.  *)
(** たとえば、[2 = 2]の根拠を構築するために、[eq_refl]を使うことが出来ます。[1 + 1 = 2]の根拠を構築するために、[eq_refl]を使用することは出来るでしょうか？
はい。実際に出来ます。それらは全く同じ根拠なのです！ その理由は、Coqがシンプルな計算ルールに従うどんな二つの項も"同じもの"として扱うからです。
これらのルールは、[Compute]を使って行なわれるものと似たルールで、関数の適用の評価、定義のインライン展開や[match]節の簡約が含まれます。*)

Lemma four: 2 + 2 = 1 + 3.
Proof.
  apply eq_refl.
Qed.

(*  The [reflexivity] tactic that we have used to prove equalities up
    to now is essentially just short-hand for [apply refl_equal].

    In tactic-based proofs of equality, the conversion rules are
    normally hidden in uses of [simpl] (either explicit or implicit in
    other tactics such as [reflexivity]).  But you can see them
    directly at work in the following explicit proof objects: *)
(** これまでに同値性を証明するために使用してきた[relexivity]タクティックは、本質的には、[apply refl_equal]の略記法であることが分かりました。
タクティックをベースとした同値性の証明において、変換規則は[simpl]の使用に隠されています(暗黙的に、明示的に、[reflexivity]
と他のタクティックも似たようなものです) しかし、証明オブジェクトで明示的に直接動作するのを次の例で見ることが出来ます。*)

Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Set) (x:X), []++[x] = x::[]  :=
  fun (X:Set) (x:X) => eq_refl [x].


End MyEquality.

Definition quiz6 : exists x,  x + 3 = 4
  := ex_intro (fun z => (z + 3 = 4)) 1 (refl_equal 4).

(* ================================================================= *)
(*  ** Inversion, Again *)
(** ** Inversion 再び *)

(*  We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves.

    In general, the [inversion] tactic...

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,

      - adds these equalities to the context (and, for convenience,
        rewrites them in the goal), and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal. *)
(** これまでにも inversion が等値性にからむ仮定や帰納的に定義された命題に対して 使われるところを見てきました。今度もやることは変わりませんが、もう少し近くまで 寄って inversion の振る舞いを観察してみましょう。 

一般的に inversion タクティックは、

  - 帰納的に定義された型 P の命題 H をとる。 

  - その型 P の定義にある各コンストラクタ C が、 
    
    - H が C から成っていると仮定するような新しいサブゴールを作る。 

    - C の引数（前提）を、追加の仮定としてサブゴールのコンテキストに加える。 

    - C の結論（戻り値の型）を現在のゴールとmatchして、 C を適用できるような一連の等式算出する。 

    - そしてこれらの等式をサブゴールのコンテキストに加えてから、 

    - もしこの等式が充足可能でない場合（S n = O というような式を含むなど）は、 即座にサブゴールを解決する。*)

(** _Example_: If we invert a hypothesis built with [or], there are two
   constructors, so two subgoals get generated.  The
   conclusion (result type) of the constructor ([P \/ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.

   _Example_: If we invert a hypothesis built with [and], there is
   only one constructor, so only one subgoal gets generated.  Again,
   the conclusion (result type) of the constructor ([P /\ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.  The
   constructor does have two arguments, though, and these can be seen
   in the context in the subgoal.

   _Example_: If we invert a hypothesis built with [eq], there is
   again only one constructor, so only one subgoal gets generated.
   Now, though, the form of the [refl_equal] constructor does give us
   some extra information: it tells us that the two arguments to [eq]
   must be the same!  The [inversion] tactic adds this fact to the
   context. *)
(** TODO *)
(** $Date: 2016-05-26 16:17:19 -0400 (Thu, 26 May 2016) $ *)

