(** * Basics_J: Coqにおける関数プログラミング *)


(* REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

   (See the [Preface] for why.) 

*)
(* リマインダ:

          #####################################################
          ###  どうか答えを公けに配布しないでください      ###
          #####################################################

   (なぜかは前書きを見てください)

*)


(* [Admitted] is Coq's "escape hatch" that says accept this definition
   without proof.  We use it to mark the 'holes' in the development
   that should be completed as part of your homework exercises.  In
   practice, [Admitted] is useful when you're incrementally developing
   large proofs. *)
(* [Admitted] はCoqにおける"脱出口"のようなものです。Admittedが書かれている定義を証明なしに受け入れることが出来ます。あなたの宿題の一部として完成させるべき証明の穴であることを示すためにそれを我々は使用します。とりわけ、[Admitted]は大きな証明を段階的に構築する時に役に立ちます。*)
Definition admit {T: Type} : T.  Admitted.

(* ###################################################################### *)
(** * 導入 *)

(*  The functional programming style brings programming closer to
    simple, everyday mathematics: If a procedure or method has no side
    effects, then (ignoring efficiency) all we need to understand
    about it is how it maps inputs to outputs -- that is, we can think
    of it as just a concrete method for computing a mathematical
    function.  This is one sense of the word "functional" in
    "functional programming."  The direct connection between programs
    and simple mathematical objects supports both formal correctness
    proofs and sound informal reasoning about program behavior.

    The other sense in which functional programming is "functional" is
    that it emphasizes the use of functions (or methods) as
    _first-class_ values -- i.e., values that can be passed as
    arguments to other functions, returned as results, included in
    data structures, etc.  The recognition that functions can be
    treated as data in this way enables a host of useful and powerful
    idioms.

    Other common features of functional languages include _algebraic
    data types_ and _pattern matching_, which make it easy to
    construct and manipulate rich data structures, and sophisticated
    _polymorphic type systems_ supporting abstraction and code reuse.
    Coq shares all of these features.

    The first half of this chapter introduces the most essential
    elements of Coq's functional programming language.  The second
    half introduces some basic _tactics_ that can be used to prove
    simple properties of Coq programs. *)
(**
  関数型プログラミングのスタイルはプログラミングを数学に近付けます: もしプロシージャやメソッドが副作用を持たないならば、それに関して理解するために必要なものは、入力と出力の対応だけです。すなわち、それらは、数学的な関数を計算するのと全く同じ振舞いであると考えることが出来ます。これは 関数型プログラミングにおいて、"関数型"という単語の一つの理由です。このプログラムと単純な数学的オブジェクトとの直接的な関係は、妥当な非形式的な理由付けと形式的な正当性の証明の両方をサポートします。

  関数型プログラミングが"関数型"である別の意味は、関数(またはメソッド)を_第一級_の値としての使用を重要視することです。すなわち、関数は、他の関数の引数として渡すことが出来る値であり、結果として返されもし、データ構造として格納されます。等々。関数がこのような方法でデータとして扱われうるという認識は、たくさんの有用な表現を可能にします。これからそれを見ていきます。

関数型言語に共通する他の特徴は、_代数的なデータ型_と_パターンマッチ_、それらは、リッチなデータ構造の構築と操作を可能にします。そして、コードの抽象化再利用を可能にする洗練された_多相的な型システム_です。Coqはこれらの特徴を全て備えています。

  この章の最初の半分で、Coqのプログラミング言語としての最も本質的な要素を紹介します。残りの半分は、Coq言語の単純な命題を証明するために使用することの出来る基本的なタクティックの紹介を行います。
*)


(* ###################################################################### *)
(*  * Enumerated Types *)
(** * 列挙型 *)

(*  One unusual aspect of Coq is that its set of built-in
    features is _extremely_ small.  For example, instead of providing
    the usual palette of atomic data types (booleans, integers,
    strings, etc.), Coq offers a powerful mechanism for defining new
    data types from scratch, from which all these familiar types arise
    as instances.

    Naturally, the Coq distribution comes with an extensive standard
    library providing definitions of booleans, numbers, and many
    common data structures like lists and hash tables.  But there is
    nothing magic or primitive about these library definitions.  To
    illustrate this, we will explicitly recapitulate all the
    definitions we need in this course, rather than just getting them
    implicitly from the library.

    To see how this definition mechanism works, let's start with a
    very simple example. *)

(** 
Coqの普通でない特徴の一つは、ビルトインされている機能が極端に小さいことです。例えば、アトミックなデータタイプのよくある一揃い（ブール型や数値型など）の代わりにCoqには、新しい型をスクラッチで定義するための協力な機構が用意されており、その機構によって全てのよくあるこれらの型を表すことが出来ます。
 
  当然のことですが、Coqのディストリビューションには、品揃え豊富な標準ライブラリが付属しており、その中で、ブール型、数値型、その他多くのリストやハッシュテーブルに似たデータ構造を提供しています。しかしながら、それらのライブラリ定義のための魔法やプリミティブは存在しません。それらは、通常のユーザコードです。
このことを説明するために、暗黙的にライブラリからそれらをただ使用するのではなく、明示的に我々がこのコースで必要とする全ての定義を反復して行くことにします。

この定義の仕組みがどう動作するか見る為に、とても単純な例から始めましょう。
*)

(* ###################################################################### *)
(*  ** Days of the Week *)
(** ** 曜日の表し方 *)

(*  The following declaration tells Coq that we are defining
    a new set of data values -- a _type_. *)
(** 次の宣言は、Coqに対して、新しいデータ値のセット（集合）である'型'を定義しています。*)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(*  The type is called [day], and its members are [monday],
    [tuesday], etc.  The second and following lines of the definition
    can be read "[monday] is a [day], [tuesday] is a [day], etc."

    Having defined [day], we can write functions that operate on
    days. *)
(** その型は[day]で、要素は[monday]、[tuesday]...などです。その定義の1行は以下のようにも読めます。"[monday]は[day]。[tuesday]は[day]"といった具合です。
 
 "[day]"が何かを定義できれば、それを利用して関数を書くこともできるでしょう。 *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(*  One thing to note is that the argument and return types of
    this function are explicitly declared.  Like most functional
    programming languages, Coq can often figure out these types for
    itself when they are not given explicitly -- i.e., it performs
    _type inference_ -- but we'll include them to make reading
    easier. *)

(** 一つ注意しておかなければならないことがあります。この関数の定義では、引数の型と戻り値の型が明示されていることです。他の多くの関数型プログラミング言語と同様、Coqはこのように型を明示的に書かずともちゃんと動くようになっています。それはいわゆる「型推論」という機構によって実現されていますが、型を明示した方がプログラムを読みやすくできると判断するなら、いつでもそうしてかまいません。 *)

(*  Having defined a function, we should check that it works on
    some examples.  There are actually three different ways to do this
    in Coq.

    First, we can use the command [Compute] to evaluate a compound
    expression involving [next_weekday]. *)

(** 関数の定義ができたら、いくつかの例を挙げてそれが正しいものであることをチェックしなければなりません。それを実現するために、Coqには三つの方法が用意されています。一つ目の方法は「[Compute]」コマンドを使って、関数[next_weekday]を含んだ式を評価させることです。*)

Compute in (next_weekday friday).
(* ==> monday : day *)
Compute in (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

(*  (We show Coq's responses in comments, but, if you have a
    computer handy, this would be an excellent moment to fire up the
    Coq interpreter under your favorite IDE -- either CoqIde or Proof
    General -- and try this for yourself.  Load this file, [Basics.v],
    from the book's accompanying Coq sources, find the above example,
    submit it to Coq, and observe the result.)

    Second, we can record what we _expect_ the result to be in the
    form of a Coq example: *)
(** Coqの応答をコメントの形で示しています。 もし今あなたの手元にコンピュータがあるなら、CoqのIDEのうち好きなもの（CoqIDEやProofGeneralなどから）を選んで起動し、実際に上のコマンドを入力し動かしてみるといいでしょう。付録の「[Basic.v]」ファイルから上のサンプルを探してCoqに読み込ませ、結果を観察してください。

二番目の方法は、評価の結果として我々が"期待"しているものをCoqに対してあらかじめ以下のような形で例示しておくというものです。 *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(*  This declaration does two things: it makes an
    assertion (that the second weekday after [saturday] is [tuesday]),
    and it gives the assertion a name that can be used to refer to it
    later.

    Having made the assertion, we can also ask Coq to verify it, like
    this: *)

(** この宣言は二つのことを行っています。ひとつは、[saturday]の次の次にあたる平日が、[tuesday]であるということを確認する必要があるということを示すこと。もう一つは、後で参照しやすいように、その確認事項に[test_next_weekday]という名前を与えていることです。
    この確認事項を定義すれば、次のようなコマンドを流すだけで、Coqによって正しさを検証できます。 *)

Proof. simpl. reflexivity.  Qed.

(** The details are not important for now (we'll come back to
    them in a bit), but essentially this can be read as "The assertion
    we've just made can be proved by observing that both sides of the
    equality evaluate to the same thing, after some simplification."

    Third, we can ask Coq to _extract_, from our [Definition], a
    program in some other, more conventional, programming
    language (OCaml, Scheme, or Haskell) with a high-performance
    compiler.  This facility is very interesting, since it gives us a
    way to construct _fully certified_ programs in mainstream
    languages.  Indeed, this is one of the main uses for which Coq was
    developed.  We'll come back to this topic in later chapters. *)

(** この文について細かいことは今は置いておきますが（じきに戻ってきます）、本質的には以下のような意味になります「我々が作成した確認事項は簡約後の両辺の同値チェックによって証明されました。」

 三番目の方法は、Coqで[定義]したものから、他のより一般的な言語（OcamlやScheme、Haskellといった）のプログラムを抽出してしまうことです。この機能は今主流の言語で完全に確認されたプログラムを実現できる道を開いたという意味でとても興味深いものです。ここではこの件について深入りすることはしませんが、もしより深く知りたいという場合はCoq'Art book（Bertot and Casteran著）か、Coqリファレンスマニュアルを参照してください。 *)

(* ###################################################################### *)
(*  ** Booleans *)
(** ** ブール型 *)

(*  In a similar way, we can define the standard type [bool] of
    booleans, with members [true] and [false]. *)
(** 同様にして、[true]と[false]を値としてとる「[bool型]」を定義することができます。 *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(*  Although we are rolling our own booleans here for the sake
    of building up everything from scratch, Coq does, of course,
    provide a default implementation of the booleans in its standard
    library, together with a multitude of useful functions and
    lemmas.  (Take a look at [Coq.Init.Datatypes] in the Coq library
    documentation if you're interested.)  Whenever possible, we'll
    name our own definitions and theorems so that they exactly
    coincide with the ones in the standard library.

    Functions over booleans can be defined in the same way as
    above: *)
(** このようにして、我々は独自のbool型を一から作りあげることもできるのですが、もちろんCoqには標準ライブラリとしてbool型が多くの有用な関数、補助定理と一緒に用意されています。（もし興味があるなら、CoqライブラリドキュメントのCoq.Init.Datatypesを参照してください。）ここでは可能な限り標準ライブラリと正確に同じ機能を、我々独自の名前で定義していくことにしましょう。 

  ブール型を使用する関数は、上記のDay型と同じように定義することができます。 *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.


(*  The last two illustrate Coq's syntax for multi-argument
    function definitions.  The corresponding multi-argument
    application syntax is illustrated by the following four "unit
    tests," which constitute a complete specification -- a truth
    table -- for the [orb] function: *)
(** 後半の二つは、引数を複数持つ関数を定義する方法を示しています。 

 次の四つの単体テストは、関数[orb]が取り得るすべての引数についての完全な仕様（真理値表）となっています。 *)

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(*  We can also introduce some familiar syntax for the boolean
    operations we have just defined. The [Infix] command defines new,
    infix notation for an existing definition. *)
(** 我々が今定義したブール型操作のために馴染み安い記法を導入することも出来ます。[Infix]コマンドは、すでに存在する定義のための新しい中置記法を定義します。*)

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** _A note on notation_: In [.v] files, we use square brackets to
    delimit fragments of Coq code within comments; this convention,
    also used by the [coqdoc] documentation tool, keeps them visually
    separate from the surrounding text.  In the html version of the
    files, these pieces of text appear in a [different font].

    The special phrases [Admitted] and [admit] can be used as a
    placeholder for an incomplete definition or proof.  We'll use them
    in exercises, to indicate the parts that we're leaving for you --
    i.e., your job is to replace [admit] or [Admitted] with real
    definitions or proofs. *)
(** 記法について: [.v]ファイルにおいて、Coqのコード中にコメントを含める場合には、大括弧を使用してコードと区切ります。この慣習は[coqdoc]というドキュメント作成ツールでも利用されているのですが、ソース中のコメントをコードから視覚的に分離することができます。CoqソースのHTML版では、コメントはソースとは[別のフォント]で表示されます。 

特別なフレーズ[Admitted]と[admit]は、定義や証明にある不完全な部分のプレースホルダとして使用されます。我々はこれらをあなたの課題であることを示すために練習問題に使用します。つまり、あなたの仕事は[admit]や[Admitted]と書かれた部分をちゃんとした定義や証明に書き直すことです。*)

(*  **** Exercise: 1 star (nandb)  *)
(*  Remove [admit] and complete the definition of the following
    function; then make sure that the [Example] assertions below can
    each be verified by Coq.  (Remove "[Admitted.]" and fill in each
    proof, following the model of the [orb] tests above.) The function
    should return [true] if either or both of its inputs are
    [false]. *)
(** **** 練習問題: ★ (nandb) *)
(** [admit]を取り除いて次の定義を完成させ、[Example]で記述された確認内容がCoqのチェックをすべて通過することを確認しなさい。([Admitted]を取り除いて、上記の[orb]テストに倣ってそれぞれの証明を埋めなさい。) この関数はどちらか、もしくは両方が[false]になったときに[true]を返すものである。 *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  (* FILL IN HERE *) admit.

Example test_nandb1:               (nandb true false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb2:               (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3:               (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4:               (nandb true true) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star (andb3)  *)
(*  Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)
(** **** 練習問題: ★ (andb3) *)
(**下にある[andb3]関数も同様に行いなさい。この関数は、全ての引数が[true]のとき、[true]を返し、そうでない場合は、falseを返すべきです。*)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (* FILL IN HERE *) admit.

Example test_andb31:                 (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.
Example test_andb32:                 (andb3 false true true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb33:                 (andb3 true false true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb34:                 (andb3 true true false) = false.
(* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################################### *)
(*  ** Function Types *)
(** ** 関数型 *)

(*  Every expression in Coq has a type, describing what sort of
    thing it computes. The [Check] command asks Coq to print the type
    of an expression. *)
(** Coq中の全ての式は型を持ち、その型は、どんな種類の計算をするのかを示しています。 [Check]コマンドを使うと、Coqに、指定した式の型を表示させることができます。*)
(*  For example, the type of [negb true] is [bool]. *)
(** 例えば、（[negb true]）という式の全体の型は[bool]である、という具合です。 *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(*  Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. *)
(** [negb]のような関数は、それ自身が[true]や[false]と同じように値であると考えることもできます。そのようにとらえた場合の値の型を「関数型」と呼び、以下のように矢印を使った型として表します。 *)

Check negb.
(* ===> negb : bool -> bool *)

(*  The type of [negb], written [bool -> bool] and pronounced
    "[bool] arrow [bool]," can be read, "Given an input of type
    [bool], this function produces an output of type [bool]."
    Similarly, the type of [andb], written [bool -> bool -> bool], can
    be read, "Given two inputs, both of type [bool], this function
    produces an output of type [bool]." *)
(** [negb]の型は[bool->bool]と書き、「[bool]から[bool]」と読み、[bool]型の引数をとって[bool]型の戻り値を返す関数と理解することができます。同様に、[andb]の型は[bool -> bool -> bool]と書き、「二つの[bool]型の値を引数として[bool]型の値を作成して戻す」と解釈します。 *)


(* ###################################################################### *)
(*  ** Modules *)
(** ** モジュール *)

(*  Coq provides a _module system_, to aid in organizing large
    developments.  In this course we won't need most of its features,
    but one is useful: If we enclose a collection of declarations
    between [Module X] and [End X] markers, then, in the remainder of
    the file after the [End], these definitions are referred to by
    names like [X.foo] instead of just [foo].  Here, we use this
    feature to introduce the definition of the type [nat] in an inner
    module so that it does not interfere with the one from the
    standard library, which comes with a bit of special notational
    magic.  *)
(** Coqは大規模な開発を支援するためのモジュールシステムを提供しています。このコースではこれらはほとんど必要のないものですが、一つだけ有用なものがあります。プログラムの中のいくつかの要素を[Module X]と[End X]で囲んでおくと、[End X]以降の部分から、囲まれた中の定義を[X.foo]という風に呼び出すことができます。このことは、新しく[foo]という名前で関数を定義しても問題ないということです。逆に、同じスコープの中では、同じ名前での定義はエラーとなります。という訳で、今回我々はこの機能を使って[nat]という型を内部モジュールとして定義します。そうすることで、標準ライブラリの同じ名前の定義を覆い隠してしまわずに済みます。 *)

Module Playground1.

(* ###################################################################### *)
(*  ** Numbers *)
(** ** 数値 *)

(*  The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite set of
    elements.  A more interesting way of defining a type is to give a
    collection of _inductive rules_ describing its elements.  For
    example, we can define the natural numbers as follows: *)
(** 我々がここまでで定義してきた型は「列挙型」の型定義でした。このような型は、有限の要素をすべて列挙することによって定義されます。型を定義するもう一つの方法は、「帰納的な記述」を並べることで要素を記述する方法です。例えば、自然数は（全て並べるわけにはいきませんが）以下のような方法で定義できます。 *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(*  The clauses of this definition can be read:
      - [O] is a natural number (note that this is the letter "[O],"
        not the numeral "[0]").
      - [S] is a "constructor" that takes a natural number and yields
        another one -- that is, if [n] is a natural number, then [S n]
        is too.

    Let's look at this in a little more detail.

    Every inductively defined set ([day], [nat], [bool], etc.) is
    actually a set of _expressions_.  The definition of [nat] says how
    expressions in the set [nat] can be constructed:

    - the expression [O] belongs to the set [nat];
    - if [n] is an expression belonging to the set [nat], then [S n]
      is also an expression belonging to the set [nat]; and
    - expressions formed in these two ways are the only ones belonging
      to the set [nat].

    The same rules apply for our definitions of [day] and [bool]. The
    annotations we used for their constructors are analogous to the
    one for the [O] constructor, indicating that they don't take any
    arguments.

    These three conditions are the precise force of the [Inductive]
    declaration.  They imply that the expression [O], the expression
    [S O], the expression [S (S O)], the expression [S (S (S O))], and
    so on all belong to the set [nat], while other expressions like
    [true], [andb true false], and [S (S false)] do not.

    We can write simple functions that pattern match on natural
    numbers just as we did above -- for example, the predecessor
    function: *)
(** この定義の各句は、以下のように解釈できます。
      - [O]は自然数である（[0]（ゼロ）ではなく"[O]"（オー）であることに注意）
      - [S]は自然数を引数にとり、別の自然数を生成する「コンストラクタ」である。このことは、[n]が自然数なら[S n]も自然数であることを示している。

    この定義にして、もう少し詳しく見ていきましょう。

    これまでに定義してきた帰納的な型（[weekday]、[nat]、[bool]など）は、実際には式の集合とでも言うべきものです。[nat]の定義は、[nat]の要素となる式がどのように構築されるかを表しています。

    - 式[O]（オー）は、[nat]に属する。
    - もし[n]が[nat]に属するならば、[S n]もまた[nat]に属する。
    - これら二つの方法で表された式のみが[nat]に属するものの全てである。*)

(** これら三つの条件によって、[nat]が帰納的([Inductive])な方法で厳格に定義されています。この定義によって、式 [O]、式 [S O]、式  [S (S O)]、式 [S (S (S O))]...が全て[nat]に属する式であることが表されています。また同時に、[true]や[andb true false]、[S (S false)]が[nat]に属さないことも明確にされています。

こうして定義された自然数[nat]をマターンマッチにかけることで、簡単な関数を書いてみましょう。例えば、一つ前の[nat]を返す関数は以下のよう書けます。
 *)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(*  The second branch can be read: "if [n] has the form [S n']
    for some [n'], then return [n']."  *)
(** この２番目の句は「もし[n]が何らかの[n']を用いて[S n']と表せるなら、[n']を返す」と読めます。 *)

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(*  Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of built-in magic for parsing and printing
    them: ordinary arabic numerals can be used as an alternative to
    the "unary" notation defined by the constructors [S] and [O].  Coq
    prints numbers in arabic form by default: *)
(** 自然数というのは非常に一般的な型なので、Coqは自然数を扱ったり表したりするときに若干特別な扱いをします。[S]や[O]を使って定義された"単項の"記法で記述する代わりに一般的に使われるアラビア数字を使うことができます。実際、Coqは数値を表示する際、デフォルトではアラビア数字を用います。 *)

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

(** [nat]のコンストラクタ[S]は、[nat -> nat]型の関数で[minustwo]や[pred]も同様です。 *)

Check S.
Check pred.
Check minustwo.

(*  These are all things that can be applied to a number to yield a
    number.  However, there is a fundamental difference between the
    first one and the other two: functions like [pred] and [minustwo]
    come with _computation rules_ -- e.g., the definition of [pred]
    says that [pred 2] can be simplified to [1] -- while the
    definition of [S] has no such behavior attached.  Although it is
    like a function in the sense that it can be applied to an
    argument, it does not _do_ anything at all!

    For most function definitions over numbers, just pattern matching
    is not enough: we also need recursion.  For example, to check that
    a number [n] is even, we may need to recursively check whether
    [n-2] is even.  To write such functions, we use the keyword
    [Fixpoint]. *)
(** これらが表しているのは、いずれの関数も数を引数にとって数を生成できる、ということです。しかしながらこれらの関数には根本的な違いがあります。[pred]や[minustwo]といった関数には「計算ルール」というものが定義されています。[pred]の定義は、[pred n]が[match n with | O => O | S m' => m' end]のように簡約されることを記述したものですが、一方[S]にはそのような定義がありません。しかし両方とも関数には違いなく、引数を元に評価されるということについては同じで、それ以上のものではないのです。 *)

(** 数値を扱う多くの関数は、単なるパターンマッチだけでは記述できず、再帰的な定義が必要になってきます。例えば、[n]が偶数かどうかを調べて返す関数[evenb]は、[n-2]が偶数であるかどうかを調べる、という再帰的な定義を必要とします。そういう関数を定義する場合、[Fixpoint]というキーワードを使用します。 *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(*  We can define [oddb] by a similar [Fixpoint] declaration, but here
    is a simpler definition that is a bit easier to work with: *)
(** 同じように[Fixpoint]を使って関数[oddb]を定義することもできますが、ここでは次のようにもっとシンプルな用法で簡単に作ってみましょう。 *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    oddb 1 = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    oddb 4 = false.
Proof. simpl. reflexivity.  Qed.

(*  (You will notice if you step through these proofs that
    [simpl] actually has no effect on the goal -- all of the work is
    done by [reflexivity].  We'll see more about why that is shortly.)

    Naturally, we can also define multi-argument functions by
    recursion.  *)
(** すでにお気付きかもしれませんが、証明を進めるときに、[simpl]が実際のgoalに何の影響も与えていません。すべての仕事は、[reflexivity]によって行なわれています。そうなる理由は後程見ることにします。

当然ながら、引数を複数持つ関数も再帰的に定義することができます。 *)

(** ネームスペースを汚さないようにするため、別のモジュールに定義することにしましょう。*)
Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(*  Adding three to two now gives us five, as we'd expect. *)
(** 3に2を加えた結果は、5になるべきですね。 *)

Compute (plus 3 2).

(*  The simplification that Coq performs to reach this conclusion can
    be visualized as follows: *)
(** Coqがこの計算をどう進めて（簡約して）結論を導くかは以下のように表現できます。 *)

(*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))]
      by the second clause of the [match]
==> [S (S (plus (S O) (S (S O))))]
      by the second clause of the [match]
==> [S (S (S (plus O (S (S O)))))]
      by the second clause of the [match]
==> [S (S (S (S (S O))))]
      by the first clause of the [match]
*)

(** As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    definition, [(n m : nat)] means just the same as if we had written
    [(n : nat) (m : nat)]. *)
(** 表記を簡便にするため、複数の引数が同じ型を持つときは、型の記述をまとめることができます。 [(n m : nat)]は[(n : nat) (m : nat)]と書いたのとまったく同じ意味になります。 *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.
(*  You can match two expressions at once by putting a comma
    between them: *)
(** matchに引数を与える際、複数の引数を次のようにカンマで区切って一度に渡すことができます。 *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

(*  The _ in the first line is a _wildcard pattern_.  Writing _ in a
    pattern is the same as writing some variable that doesn't get used
    on the right-hand side.  This avoids the need to invent a bogus
    variable name. *)
(** [minus]の[match]の行に現れる( _ )は、ワイルドカードパターンと呼ばれるものです。パターンの中に _ を書くと、それはその部分が何であってもマッチし、その値が使用されないことを意味します。この _ は、このような場合に無意味な名前をつける必要をなくしてくれます。 *)

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(*  **** Exercise: 1 star (factorial)  *)
(** **** 演習問題: ★ (factorial) *)
(*  Recall the standard mathematical factorial function:
       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

    Translate this into Coq. *)
(** 再帰を使用した、一般的なfactorical（階乗）の定義を思い出してください :
  
    factorial(0)  =  1
    factorial(n)  =  n * factorial(n-1)     (if n>0)

    これをCoqでの定義に書き直しなさい。 *)

Fixpoint factorial (n:nat) : nat :=
  (* FILL IN HERE *) admit.

Example test_factorial1:          (factorial 3) = 6.
(* FILL IN HERE *) Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.
(** [] *)

(** We can make numerical expressions a little easier to read and
    write by introducing _notations_ for addition, multiplication, and
    subtraction. *)
(** ここで紹介する"notation"（表記法）という機能を使うことで、加算、減算、乗算のような数値を扱う式をずっと読みやすく、書きやすくすることができます。 *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)

Check ((0 + 1) + 1).

(*  (The [level], [associativity], and [nat_scope] annotations
    control how these notations are treated by Coq's parser.  The
    details are not important, but interested readers can refer to the
    optional "More on Notation" section at the end of this chapter.)

    Note that these do not change the definitions we've already made:
    they are simply instructions to the Coq parser to accept [x + y]
    in place of [plus x y] and, conversely, to the Coq pretty-printer
    to display [plus x y] as [x + y].

    When we say that Coq comes with nothing built-in, we really mean
    it: even equality testing for numbers is a user-defined
    operation! *)

(*  The [beq_nat] function tests [nat]ural numbers for [eq]uality,
    yielding a [b]oolean.  Note the use of nested [match]es (we could
    also have used a simultaneous match, as we did in [minus].)  *)
(** これらは、これまで我々が定義してきたものを何ら変えるわけではありません。NotationはCoqのパーサに対して[x + y]を[plus x y]と解釈させたり、逆に[plus x y]を[x + y]と表記させたりするためのものです。

各表記法のシンボルは、表記法のスコープ内でのみ有効です。Coqはどのスコープであるかを推測しようとします。[S(O*O)]と書かれていた場合は、それを[nat_scope]であると推測しますし、ソースにデカルト積（タプル）型[bool*bool]と書かれていたら、[type_scope]であると推測します。時には[(x*y)%nat]といった風に、%表記を使ってスコープを明示する必要があるでしょうし、どの表記スコープで解釈したかが[%nat]というような形でCoqからフィードバックされてくることもあります。

表記のスコープは、多くの場合数値に適用されます。ですので[0%nat]という表記を[O]（オー）や[0%Z]（数値のゼロ）という意味で見ることがあります。

 最初の方で、Coqにはほとんど何も用意されていない、という話をしましたが、本当のところ、数値を比較する関数すら自分で作らなければならないのです！! *)
(** [beq_nat]関数は自然数を比較してbool値を返すものです。入れ子になった[match]に気をつけて、以下のソースを読んでください。（二つの変数を一度に[match]させる場合の書き方は、[minus]のところですでに登場しています） *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(*  The [leb] function tests whether its first argument is less than or
  equal to its second argument, yielding a boolean. *)
(** 同様に、[leb]関数は自然数を比較して小さいか等しい、ということを調べてbool値を生成し返します。 *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1:             (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(*  **** Exercise: 1 star (blt_nat)  *)
(*  The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined function. *)
(** **** 練習問題: ★★ (blt_nat) *)
(** [blt_nat]関数は、自然数を比較して小さい、ということを調べてbool値を生成します（ [nat]ural numbers for [l]ess-[t]han）。[Fixpoint]を使用して１から作成するのではなく、すでにこれまで定義した関数を利用して定義しなさい。*)


Definition blt_nat (n m : nat) : bool :=
  (* FILL IN HERE *) admit.

Example test_blt_nat1:             (blt_nat 2 2) = false.
(* FILL IN HERE *) Admitted.
Example test_blt_nat2:             (blt_nat 2 4) = true.
(* FILL IN HERE *) Admitted.
Example test_blt_nat3:             (blt_nat 4 2) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(*  * Proof by Simplification *)
(** * 簡約を用いた証明 *)

(*  Now that we've defined a few datatypes and functions, let's
    turn to stating and proving properties of their behavior.
    Actually, we've already started doing this: each [Example] in the
    previous sections makes a precise claim about the behavior of some
    function on some particular inputs.  The proofs of these claims
    were always the same: use [simpl] to simplify both sides of the
    equation, then use [reflexivity] to check that both sides contain
    identical values.

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    [0] is a "neutral element" for [+] on the left can be proved just
    by observing that [0 + n] reduces to [n] no matter what [n] is, a
    fact that can be read directly off the definition of [plus].*)
(** ここまでに、いくつかの型や関数を定義してきました。が、ここからは少し目先を変えて、こういった型や関数の特性や振る舞いをどうやって知り、証明していくかを考えてみることにしましょう。実際には、すでにこれまでやってきたことでも、その一部に触れています。例えば、前のセクションの[Example]は、ある関数にある特定の値を入力した時の振る舞いについて、あらかじめ想定していたものと正確に一致していると主張してくれます。それらの主張が証明しているものは、以下のものと同じです。

[=]の両側の式を定義に基づいて簡約した結果は、一致している。

(実際、[reflexivity]は[simpl]よりいくぶん多くのことをやってくれるので、覚えておくと後々便利でしょう。例えば、[reflexivity] は定義された句を展開したり、右辺と置き換えるといったことを試みます。この違いから、[reflexivity] が向いているのは、「[reflexivity] によって全てのゴールが自動的に証明され、[reflexivity] が見つけて展開した式をあえて見なくてもよい」という場合で、逆に[simpl]は、我々自身が新しいゴールを読んで理解すべき時（勝手に定義を展開し解釈して欲しくない時）に向いているということになります)

このような「簡約を用いた証明」は、関数のさらに興味深い性質をうまく証明することができます。例えば、[0]が自然数の加算における左単位元（[0]が、左から加えても値が変わらない値であること）であることの証明は、[n]が何であっても[0 + n]を注意深く縮小(簡約)したものが[n]になることを、[+]という関数が「最初の引数を引き継いで再帰的に定義されている」ということを考慮した上で示せればいいということです。 *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.

(* (You may notice that the above statement looks different in
    the [.v] file in your IDE than it does in the HTML rendition in
    your browser, if you are viewing both. In [.v] files, we write the
    [forall] universal quantifier using the reserved identifier
    "forall."  When the [.v] files are converted to HTML, this gets
    transformed into an upside-down-A symbol.) *)
 (**_上記の式が元のソースファイルと最終的なhtml出力とで、違って見えることに気がついたかもしれません。Coqのファイルにおいて、予約語である_forall_を使って[forall]全称修飾子を書く必要があります。これは論理学でよく使用される、引っくり返った"A"としてプリントされます。*)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(*  Moreover, it will be useful later to know that [reflexivity]
    does somewhat _more_ simplification than [simpl] does -- for
    example, it tries "unfolding" defined terms, replacing them with
    their right-hand sides.  The reason for this difference is that,
    if reflexivity succeeds, the whole goal is finished and we don't
    need to look at whatever expanded expressions [reflexivity] has
    created by all this simplification and unfolding; by contrast,
    [simpl] is used in situations where we may have to read and
    understand the new goal that it creates, so we would not want it
    blindly expanding definitions and leaving the goal in a messy
    state. *)
(** さらに、[simpl]が行なう以上の単純化する何かを[reflexivity]は行なってると知ることは後々便利です。例えば、定義された項の折り畳みに挑戦することや、右辺を置き換えたりすることです。この違いがなぜあるかというと、reflexivityが成功した場合、全体のゴールが終了して、[reflexivity]によって生成された簡約や展開を見る必要はありません。一方、[simpl]は新しいゴールを読んで理解しなければならない場合に使用されます。
*)

(*  The form of the theorem we just stated and its proof are
    almost exactly the same as the simpler examples we saw earlier;
    there are just a few differences.

    First, we've used the keyword [Theorem] instead of [Example].
    This difference is purely a matter of style; the keywords
    [Example] and [Theorem] (and a few others, including [Lemma],
    [Fact], and [Remark]) mean exactly the same thing to Coq.

    Second, we've added the quantifier [forall n:nat], so that our
    theorem talks about _all_ natural numbers [n].  In order to prove
    theorems of this form, we need to to be able to reason by
    _assuming_ the existence of an arbitrary natural number [n].  This
    is achieved in the proof by [intros n], which moves the quantifier
    from the goal to a _context_ of current assumptions. In effect, we
    start the proof by saying "Suppose [n] is some arbitrary
    number..."

    The keywords [intros], [simpl], and [reflexivity] are examples of
    _tactics_.  A tactic is a command that is used between [Proof] and
    [Qed] to guide the process of checking some claim we are making.
    We will see several more tactics in the rest of this chapter and
    yet more in future chapters.

    Other similar theorems can be proved with the same pattern. *)
(** この定理と証明の形式の形式はほとんど上記の例と同じですが、僅かに違いがあります。*)
  
(* 一つは、[Exmaple]の代わりに[Theorem]キーワードを使用しています。確かにこれは単なるスタイルの違いで、[Example]と[Theorem]（他にも[Lemma]、[Fact]、[Remark]など）はCoqから見るとすべて同じ意味を持ちます。

二つめは、量化子が加えられている（[forall n:nat]）ことです。そのため我々の定理は_全ての_自然数[n]ついて語っています。この形式の定理を証明するために、任意の自然数[n]の存在を前提とすることで理由付け出来なければなりません。これは[intros n]で証明を開始することで行います。[intros n]は量化子をゴールから現在の仮定の"コンテキスト"に引き上げます。実際、我々も証明を「よし、nを任意の数値としよう」と言って始めます。*)

(** [intros]や[simpl]や[reflexivity]キーワードはタクティックのタクティックの例です。タクティックは、[Proof]と[Qed]の間に記述され、Coqに対して、我々がしようとしている主張の正当性をどのようにチェックすべきかを指示するためのコマンドです。この講義の残りでは、まだ出てきていないタクティックのうちのいくつかを紹介していきましょう。さらにその後の講義ではもっと色々出てくるのですが。*)

(** これらの証明をCoq上で逐次実行し、どのようにゴールやコンテキストが変化するのかをよく観察してください *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(*  The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)
(** 定理の名前についている[_l]という接尾辞は、「左の」と読みます。 *)

(*  It is worth stepping through these proofs to observe how the
    context and the goal change. *)
(** これらの証明を一ステップずつ追ってコンテキストやゴールがどのように変化するのかを観察することはとても有用です。*)
(*  You may want to add calls to [simpl] before [reflexivity] to
    see the simplifications that Coq performs on the terms before
    checking that they are equal.

    Although simplification is powerful enough to prove some fairly
    general facts, there are many statements that cannot be handled by
    simplification alone.  For instance, we cannot use it to prove
    that [0] is also a neutral element for [+] _on the right_. *)
(** Coqが左右の式がイコールであることをチェックする前に、Coqがどのように簡約化するかを見るために、[reflexivity]の前に[simpl]の呼び出しを加えたくなるかもしれません。

 簡約はある種の一般的な事実を証明するには十分に強力ですが、簡約だけでは扱うことの出来ないステートメントも多くあります。例えば、[0]が[+]の右側にある場合に、中立な要素でもあることを証明することは出来ません。*)

Theorem plus_n_O : forall n, n = n + 0.
Proof.
  intros n. simpl. (* 何も起こりません！ *)

(*  (Can you explain why this happens?  Step through both proofs
    with Coq and notice how the goal and context change.)

    When stuck in the middle of a proof, we can use the [Abort]
    command to give up on it for the moment. *)
(** (なぜこうなるのか説明できるでしょうか？ Coqで両方の証明を追いかけて、ゴールやコンテキストがどう変化するのか観察しましょう。
  証明の途中で止まった場合、[Abort]コマンドを使用して、一時的にギブアップすることが出来ます。*)
Abort.


(* ###################################################################### *)
(*  * Proof by Rewriting *)
(** * 書き換え（[Rewriting]）による証明*)

(*  This theorem is a bit more interesting than the others we've
    seen: *)
(** 少しばかり興味深い定理を見てみましょう。 *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

(*  Instead of making a universal claim about all numbers [n] and [m],
    it talks about a more specialized property that only holds when [n
    = m].  The arrow symbol is pronounced "implies."

    As before, we need to be able to reason by assuming the existence
    of some numbers [n] and [m].  We also need to assume the hypothesis
    [n = m]. The [intros] tactic will serve to move all three of these
    from the goal into assumptions in the current context.

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)
(** すべての[n][m]という数に関する一般的な主張を作る代わりに、もっと特殊化された[n = m]の場合に成り立つ命題についてx考えます。矢印記号は"含意"を意味します。

これまで見てきたように、[n] と [m]という数が存在すると仮定することで推論をすることが可能にする必要があります。
それから、[n = m]という仮説を仮定する必要があります。[intros]タクティックはゴールからこれら全てを取り除いて、現在のコンテキストに仮定を加えます。

[n]と[m]が両方とも任意の数なのですから、これをこれまでの証明でやってきたように簡約することはできません。その代わりに、[n = m]ならば、イコールの両側の[n]や[m]を互いに書き換えても等しさは変わらない、というところに注目します。このような書き換えをしてくれるのが[rewrite]タクティックです。 *)

Proof.
  (* 両方の量子化記号をコンテキストに移動します: *)
  intros n m.
  (* 仮定をコンテキストに移動します: *)
  intros H.
  (* 仮定を用いてゴールを書き換えます: *)
  rewrite -> H.
  reflexivity.  Qed.

(*  The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the name [H].
    The third tells Coq to rewrite the current goal ([n + n = m + m])
    by replacing the left side of the equality hypothesis [H] with the
    right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes.) *)
(** 証明の1行目は、∀（forall）がついた、つまり「あらゆる[n],[m]について」の部分をコンテキストに移しています。2行目は、[n = m]ならば、という仮定をコンテキストに写し、[H]という名前をこれに与えています。3行目は、ゴールになっている式([n + n = m + m])に仮定[H]の左側を右側にするような書き換えを施しています。

（[rewrite]の矢印は特に論理に関与していません。単に左側を右側に置き換えているだけです。逆に右側を左側に置き換えたい場合は、[rewrite <-]と書くこともできます。この逆の置き換えも上の証明で試して、Coqの振る舞いがどのように変わるかを観察してください。） *)

(*  **** Exercise: 1 star (plus_id_exercise)  *)
(*  Remove "[Admitted.]" and fill in the proof. *)
(** **** 練習問題: ★ (plus_id_exercise) *)
(** [Admitted.]を削除し、証明を完成させなさい。*)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  The [Admitted] command tells Coq that we want to skip trying
    to prove this theorem and just accept it as a given.  This can be
    useful for developing longer proofs, since we can state subsidiary
    lemmas that we believe will be useful for making some larger
    argument, use [Admitted] to accept them on faith for the moment,
    and continue working on the main argument until we are sure it
    makes sense; then we can go back and fill in the proofs we
    skipped.  Be careful, though: every time you say [Admitted] (or
    [admit]) you are leaving a door open for total nonsense to enter
    Coq's nice, rigorous, formally checked world! *)
(** 以前の例で見たように、Admittedコマンドは、Coqに対して「この証明はあきらめたので、この定理はこれでいいことにしてください」と指示するものです。この機能は、より長い証明をする際に便利です。何か大きな論証をしようとする時、今のところ信用している補足的な命題を示したい時があります。そんな時、[Admitted]を使用すると、その命題を一時的に信用できることにして、それを踏み台にしてより大きな論証を進めることができるのです。そしてそれが完成したのち、あらためて保留していた命題の証明を埋めればいいのです。ただし注意して下さい。[admit]や[Admitted]を使用することは、一時的にドアを開けて、「全て形式的なチェックを受け証明済みの、信用するに足るCoqの世界」から、信用に値しない下界へ足を踏み出していることに他なりません。いつかは戻ってドアを閉めることがお約束です！*)

(*  We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. If the statement
    of the previously proved theorem involves quantified variables,
    as in the example below, Coq tries to instantiate them 
    by matching with the current goal. *)   
(** 仮定の代わりに、前もって証明された定理を使っても[rewrite]タクティックは同じように利用することができます。 *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(*  **** Exercise: 2 stars (mult_S_1)  *)
(** **** 練習問題: ★★, recommended (mult_1_plus) *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(*  * Proof by Case Analysis *)
(** * Case分析 *)

(*  Of course, not everything can be proved by simple
    calculation and rewriting: In general, unknown, hypothetical
    values (arbitrary numbers, booleans, lists, etc.) can block
    simplification.  For example, if we try to prove the following
    fact using the [simpl] tactic as above, we get stuck. *)
(** もちろん、どんな命題でも簡単な計算だけで証明できるという訳ではありません。一般に、未知だったり仮定の（任意のbool、自然数、リストなど）値は、我々が検証しようとしている関数の先頭に記述され、それが簡約の邪魔をしてくれます。例えば、下のような命題をsimplタクティックだけで証明しようとすると、すぐに行き詰まってしまうでしょう。 *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl.  (* does nothing! *)
Abort.

(*  The reason for this is that the definitions of both
    [beq_nat] and [+] begin by performing a [match] on their first
    argument.  But here, the first argument to [+] is the unknown
    number [n] and the argument to [beq_nat] is the compound
    expression [n + 1]; neither can be simplified.

    To make progress, we need to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [beq_nat (n + 1) 0] and check that it is, indeed, [false].  And
    if [n = S n'] for some [n'], then, although we don't know exactly
    what number [n + 1] yields, we can calculate that, at least, it
    will begin with one [S], and this is enough to calculate that,
    again, [beq_nat (n + 1) 0] will yield [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)
(** その原因は、beq_natと+の定義で、共に最初の引数が[match]に渡されていることです。つまり、[+]に渡す最初の引数は[n]という未知数な上に、[beq_nat]の引数は[n + 1]という複合式になっているため、そのまま簡約できないのです。

今求められていることは、[n]を何らかの条件に分割し、先に進めそうな形にすることができないかを検討することです。もし[n]が[O]なら、[beq_nat (n + 1) 0]の結果を得ることはできます。もちろん結果は[false]です。しかしもし[n]が何かの[n']を使って[n = S n']と表せると考えても、我々は[n + 1]の値を得ることはできません。ただ、その式が一つの[S]で始まる（始まらないものは[O]にマッチする）ことに着目すると、[beq_nat]の結果を計算して値を求めることができます。その結果結果[beq_nat (n + 1) 0]は、やはり[false]になるでしょう。

このことから、求められるタクティックはCoqに[n = O]の場合と[n = S n']の場合に分けて考えるように要求するもので、それは[destruct]と呼ばれます。 *)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.   Qed.

(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem. The
    annotation "[as [| n']]" is called an _intro pattern_.  It tells
    Coq what variable names to introduce in each subgoal.  In general,
    what goes between the square brackets is a _list of lists_ of
    names, separated by [|].  In this case, the first component is
    empty, since the [O] constructor is nullary (it doesn't have any
    arguments).  The second component gives a single name, [n'], since
    [S] is a unary constructor.

    The [-] signs on the second and third lines are called _bullets_,
    and they mark the parts of the proof that correspond to each
    generated subgoal.  The proof script that comes after a bullet is
    the entire proof for a subgoal.  In this example, each of the
    subgoals is easily proved by a single use of [reflexivity], which
    itself performs some simplification -- e.g., the first one
    simplifies [beq_nat (S n' + 1) 0] to [false] by first rewriting
    [(S n' + 1)] to [S (n' + 1)], then unfolding [beq_nat], and then
    simplifying the [match].

    Marking cases with bullets is entirely optional: if bullets are
    not present, Coq simply asks you to prove each subgoal in
    sequence, one at a time. But it is a good idea to use bullets.
    For one thing, they make the structure of a proof apparent, making
    it more readable. Also, bullets instruct Coq to ensure that a
    subgoal is complete before trying to verify the next one,
    preventing proofs for different subgoals from getting mixed
    up. These issues become especially important in large
    developments, where fragile proofs lead to long debugging
    sessions.

    There are no hard and fast rules for how proofs should be
    formatted in Coq -- in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit bullets at the beginning of
    lines, then the proof will be readable almost no matter what
    choices are made about other aspects of layout.

    This is also a good place to mention one other piece of somewhat
    obvious advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or writing entire proofs on one line.  Good style lies somewhere
    in the middle.  One reasonable convention is to limit yourself to
    80-character lines.

    The [destruct] tactic can be used with any inductively defined
    datatype.  For example, we use it next to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse. *)
(** [destruct]タクティックは二つのサブゴールを作ります。その両方を別々に、Coqを使って定理として証明していくことになります。一つのサブゴールからもう一つへ移動するための特別なコマンドは必要ありません。一つ目のサブゴールが証明されれば、それは消えて自動的にもう一つのサブゴールにフォーカスが移ります。この証明では、二つに分かれたサブゴールのいずれも[reflexivity]を1回使うだけで簡単に証明できます。

destructについている注釈"[as [| n']]"は、"イントロパターン"と呼ばれるものです。これはCoqに対して、両方のサブゴールに元[n]だった変数をどのような変数名を使って取り入れるかを指示するものです。一般的に[[]]の間にあるものは"名前のリスト"で、"[|]"によって区切られます。このリストの最初の要素は空ですが、これは[nat]の最初のコンストラクタである[O]が引数をとらないからです。二つ目のコンストラクタ[S]は引数を一つ取りますので、リストの二つ目の要素である[n']を名前に使用します。

二行目と三行目にある[-]記号は、_弾丸_と呼ばれて、生成されたサブゴールそれぞれに応答する証明の部分であることの印です。弾丸の後ろにある証明スクリプトはサブゴールへの証明全体になります。この例ではサブゴールそれぞれは、単純な[reflexivity]を使ってそれ自身が行なう単純化で事が済んんでいます。例えば、最初の一つは、最初の書き換えで、[beq_nat (S n' + 1) 0]を[false]に簡約して、それから[beq_nat]を展開して、[match]に簡約してます。

[destruct]タクティックは帰納的に定義された型に対して使用できます。例えば、bool値の否定が反射的であること・・・つまり否定の否定が元と同じになることを証明してみましょう。 *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.  Qed.

(*  Note that the [destruct] here has no [as] clause because
    none of the subcases of the [destruct] need to bind any variables,
    so there is no need to specify any names.  (We could also have
    written [as [|]], or [as []].)  In fact, we can omit the [as]
    clause from _any_ [destruct] and Coq will fill in variable names
    automatically.  This is generally considered bad style, since Coq
    often makes confusing choices of names when left to its own
    devices.

    It is sometimes useful to invoke [destruct] inside a subgoal,
    generating yet more proof obligations. In this case, we use
    different kinds of bullets to mark goals on different "levels."
    For example: *)

(** ここで使われている[destruct]には[as]句がありませんが、ここで展開している[b]の型[bool]の二つのコンストラクタが両方とも引数をとらないため、名前を指定する必要がないのです。このような場合、"[as [|]]"や"[as []]"のように書くこともできます。実際のところほとんどの場合[destruct]の[as]句は省略可能です。その際はCoqの側で自動的に変数名をつけてくれます。これは確かに便利なのですが、よくない書き方とも言えます。Coqはしばしば名前付けに混乱して望ましくない結果を出す場合があります。 *)

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(*  Each pair of calls to [reflexivity] corresponds to the
    subgoals that were generated after the execution of the [destruct
    c] line right above it.  Besides [-] and [+], Coq proofs can also
    use [*] (asterisk) as a third kind of bullet. If we ever encounter
    a proof that generates more than three levels of subgoals, we can
    also enclose individual subgoals in curly braces ([{ ... }]): *)

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

(** Since curly braces mark both the beginning and the end of a
    proof, they can be used for multiple subgoal levels, as this
    example shows. Furthermore, curly braces allow us to reuse the
    same bullet shapes at multiple levels in a proof: *)

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

(** Before closing the chapter, let's mention one final
    convenience.  As you may have noticed, many proofs perform case
    analysis on a variable right after introducing it:

       intros x y. destruct y as [|y].

    This pattern is so common that Coq provides a shorthand for it: we
    can perform case analysis on a variable when introducing it by
    using an intro pattern instead of a variable name. For instance,
    here is a shorter proof of the [plus_1_neq_0] theorem above. *)

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.  Qed.

(** If there are no arguments to name, we can just write [[]]. *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** **** Exercise: 2 stars (andb_true_elim2)  *)
(** Prove the following claim, marking cases (and subcases) with
    bullets when you use [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star (zero_nbeq_plus_1)  *)
(** **** 練習問題: ★ (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(*  ** More on Notation (Optional) *)
(** ** 記法についてもう少し *)

(** (In general, sections marked Optional are not needed to follow the
    rest of the book, except possibly other Optional sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference.)

    Recall the notation definitions for infix plus and times: *)
(** 一般的に、Optionalと見出しにある章は、他のOptionalの章を除いて、本の残りに必要なものではありません。最初に読むときは、これらの章を読み飛ばしたくなるかもしれませんが、将来の参考のために何が書かれているか知っておいたほうがよいでしょう。
 中置の足し算とかけ算の記法の定義を思い出してください 
*)
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(*  For each notation symbol in Coq, we can specify its _precedence
    level_ and its _associativity_.  The precedence level [n] is
    specified by writing [at level n]; this helps Coq parse compound
    expressions.  The associativity setting helps to disambiguate
    expressions containing multiple occurrences of the same
    symbol. For example, the parameters specified above for [+] and
    [*] say that the expression [1+2*3*4] is shorthand for
    [(1+((2*3)*4))]. Coq uses precedence levels from 0 to 100, and
    _left_, _right_, or _no_ associativity.  We will see more examples
    of this later, e.g., in the [Lists]
    chapter.

    Each notation symbol is also associated with a _notation scope_.
    Coq tries to guess what scope is meant from context, so when it
    sees [S(O*O)] it guesses [nat_scope], but when it sees the
    cartesian product (tuple) type [bool*bool] it guesses
    [type_scope].  Occasionally, it is necessary to help it out with
    percent-notation by writing [(x*y)%nat], and sometimes in what Coq
    prints it will use [%nat] to indicate what scope a notation is in.

    Notation scopes also apply to numeral notation ([3], [4], [5],
    etc.), so you may sometimes see [0%nat], which means [O] (the
    natural number [0] that we're using in this chapter), or [0%Z],
    which means the Integer zero (which comes from a different part of
    the standard library). *)
(**  Coqにおける記法のためのそれぞれの記号は、その「優先レベル(precedence level)」と「結合性(associativity)」で記述することが出来ます。優先レベル n は[at level n]というキーワードで記述され、異なるシンボルを含む式の曖昧さを解消する助けになります。結合性は同じシンボルがもっとたくさん出現する式の曖昧さを解消する助けになります。例えば、上記のパラメータであれば、式[1+2*3*4]は式[(1+2((2*3)*4))]の省略された表現であると言うことが出来ます。Coqは、0から100までの優先レベルを使用し、結合性として、left、right、あるいは、noを使用します。

Coqにおける記法のためのそれぞれの記号はまた、記法のスコープのなかで活躍します。Coqは、どんなスコープであるかを推測します。それで、[S*(O*O)]と書かれるときには[nat_scope]であると推測する一方、[bool*bool]型のデカルト積(tuple)が書かれたときには、[type_scope]であると推測します。 まれに[(x*y)%nat]のように書く%記法を使用して、Coqが推測出来るようにしてあげる必要があります。そして時々、Coqはあなたへフィードバックします。[%nat] 何のスコープであるかを指示するために、[%nat]を使用します。
記法のスコープは数の記述にも適用されて、(3,4,5, など) [O]を意味する[0%nat]や、または、整数の0を意味する[0%Z]を見ることが今後あるでしょう。
*)

(* ###################################################################### *)
(*  ** Fixpoints and Structural Recursion (Optional) *)
(** ** Fixpointsと構造再帰(Optional)

(*  Here is a copy of the definition of addition: *)
(** ここに足し算の定義のコピーがあります: *)

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

(*  When Coq checks this definition, it notes that [plus'] is
    "decreasing on 1st argument."  What this means is that we are
    performing a _structural recursion_ over the argument [n] -- i.e.,
    that we make recursive calls only on strictly smaller values of
    [n].  This implies that all calls to [plus'] will eventually
    terminate.  Coq demands that some argument of _every_ [Fixpoint]
    definition is "decreasing."

    This requirement is a fundamental feature of Coq's design: In
    particular, it guarantees that every function that can be defined
    in Coq will terminate on all inputs.  However, because Coq's
    "decreasing analysis" is not very sophisticated, it is sometimes
    necessary to write functions in slightly unnatural ways. *)

(** Coqがこの定義をチェックする際、evenbが再帰的に呼ばれるとき、最初の引数が減少しているかに注目します。これは、ここでいう再帰がnについて構造的再帰（もしくは原始的再帰）であること、つまりnについて常により少ない値で再帰呼び出しを行っているか、ということです。これはevenbが最終的に停止するということを意味しています。CoqはFixpointキーワードで定義される関数が常にこの「減少性」を持つことを要求します。 

各関数の引数のいくつかが"減少的"でなければならない、という要求仕様は、Coqのデザインにおいて基礎となっているものです。特に、そのことによって、Coq上で作成された関数が、どんな入力を与えられても必ずいつか終了する、ということが保障されています。しかし、Coqの"減少的な解析"が「とても洗練されているとまではいえない」ため、時には不自然な書き方で関数を定義しなければならない、ということもあります。 *)

(*  **** Exercise: 2 stars, optional (decreasing)  *)
(** **** 練習問題: ★★, optional (decreasing) *)
(*  To get a concrete sense of this, find a way to write a sensible
    [Fixpoint] definition (of a simple function on numbers, say) that
    _does_ terminate on all inputs, but that Coq will reject because
    of this restriction. *)
(** これを具体的に感じるため、[Fixpoint]で定義された、より「微妙な」関数の書き方を考えてみましょう（自然数に関する簡単な関数でかまいません）。それが全ての入力で停止することと、Coqがそれを、この制限のため受け入れてくれないことを確認しなさい。 *)

(* FILL IN HERE *)

(* ###################################################################### *)
(*  * More Exercises *)
(** * さらなる練習問題 *)

(*  **** Exercise: 2 stars (boolean_functions)  *)
(** **** 練習問題: ★★ (boolean functions) *)
(*  Use the tactics you have learned so far to prove the following
    theorem about boolean functions. *)
(** bool型を扱う関数についての以下の定理を証明するために、これまでに学習したタクティックを使いなさい。*)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  (* FILL IN HERE *) Admitted.

(*  Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x].*)
(** 上記の定理によく似ているけれど、二つめの仮定で関数[f]が [f x = negb x].という性質を持つ、 [negation_fn_applied_twice]という定理を書いて証明しなさい。*)

(* FILL IN HERE *)

(*  **** Exercise: 2 stars (andb_eq_orb)  *)
(*  Prove the following theorem.  (You may want to first prove a
    subsidiary lemma or two. Alternatively, remember that you do
    not have to introduce all hypotheses at the same time.) *)
(** **** 練習問題: ★★ (andb_eq_orb) *)
(* 次の定理を証明しなさい。(おそらく補助的な定理を一つか二つ証明したくなると思います。)*)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars (binary)  *)
(** **** 練習問題: ★★★ (binary) *)
(*  Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    (a) First, write an inductive definition of the type [bin]
        corresponding to this description of binary numbers.

    (Hint: Recall that the definition of [nat] from class,

         Inductive nat : Type :=
           | O : nat
           | S : nat -> nat.

    says nothing about what [O] and [S] "mean."  It just says "[O] is
    in the set called [nat], and if [n] is in the set then so is [S
    n]."  The interpretation of [O] as zero and [S] as successor/plus
    one comes from the way that we _use_ [nat] values, by writing
    functions to do things with them, proving things about them, and
    so on.  Your definition of [bin] should be correspondingly simple;
    it is the functions you will write next that will give it
    mathematical meaning.)

    (b) Next, write an increment function [incr] for binary numbers,
        and a function [bin_to_nat] to convert binary numbers to unary numbers.

    (c) Write five unit tests [test_bin_incr1], [test_bin_incr2], etc.
        for your increment and binary-to-unary functions. Notice that
        incrementing a binary number and then converting it to unary
        should yield the same result as first converting it to unary and
(** これまでとは異なる、通常表記の自然数ではなく2進のシステムで、自然数のより効率的な表現を考えなさい。それは自然数をゼロとゼロに1を加える加算器からなるものを定義する代わりに、以下のような2進の形で表すものです。2進数とは、
      - ゼロであるか,
      - 2進数を2倍したものか,
      - 2進数を2倍したものに1を加えたもの.

    (a) まず、以下のnatの定義に対応するような2進型[bin]の帰納的な定義を完成させなさい。
    (ヒント: [nat]型の定義を思い出してください。
[[
    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.
]]
    nat型の定義[O]や[S]の意味が何かを語るものではなく、（[O]が実際に何であろうが）[O]がnatであって、[n]がnatなら[S]が何であろうと[S n]はnatである、ということを示しているだけです。「[O]がゼロで、[S]は1を加える」という実装がそれを自然数としてみて実際に関数を書き、実行したり証明したりしてみてはじめて実際に意識されます。ここで定義するbinも同様で、次に書く関数が書かれてはじめて型binに実際の数学的な意味が与えられます。)

    (b) 先に定義したbin型の値をインクリメントする関数を作成しなさい。また、bin型をnat型に変換する関数も作成しなさい。

    (c) 自分で定義したインクリメント関数と、bin型をnat型に変換する関数のユニットテストを書きなさい。bin値をまずインクリメントしたものを自然数に変換したものと、先に自然数変換した後にインクリメントしたものの値と等しいことに注意しなさい。
*)

(* FILL IN HERE *)
(** [] *)

(** $Date: 2016-05-26 16:17:19 -0400 (Thu, 26 May 2016) $ *)

