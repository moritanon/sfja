(*  * Poly: Polymorphism and Higher-Order Functions *)
(** * Poly_J:多相性と高階関数 *)

(* Final reminder: Please do not put solutions to the exercises in
   publicly accessible places.  Thank you!! *)
(* Final reminder: どうか練習問題の答を公にアクセス出来る場所に置かないで。ありがとう *)
Require Export Lists.

(* ----------------------------------------------------------------- *)
(*  * Polymorphism *)
(** * ポリモルフィズム（多相性） *)

(*  In this chapter we continue our development of basic
    concepts of functional programming.  The critical new ideas are
    _polymorphism_ (abstracting functions over the types of the data
    they manipulate) and _higher-order functions_ (treating functions
    as data).  We begin with polymorphism. *)
(** この章では、関数型プログラミングの基本的なコンセプトをさらに展開します。重要な、あたらしいアイデアは多相性(複数のデータ型に渡って関数を抽象化すること)と高階関数(データとして関数を取り扱うこと)です。では多相性について始めることにします。
*)


(* ----------------------------------------------------------------- *)
(*  ** Polymorphic Lists *)
(** ** 多相的なリスト *)

(*  For the last couple of chapters, we've been working just
    with lists of numbers.  Obviously, interesting programs also need
    to be able to manipulate lists with elements from other types --
    lists of strings, lists of booleans, lists of lists, etc.  We
    _could_ just define a new inductive datatype for each of these,
    for example... *)
(** ここまでは、数値のリストについて学んできました。もちろん、数値以外の文字列、
ブール値、リストといったものを要素として持つリストを扱えるプログラムは、
より興味深いものとなるでしょう。これまで学んできたことだけでも、
実は新しい帰納的なデータ型を作ることはできるのです。例えば次のように... *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(*  ... but this would quickly become tedious, partly because we
    have to make up different constructor names for each datatype, but
    mostly because we would also need to define new versions of all
    our list manipulating functions ([length], [rev], etc.) for each
    new datatype definition. *)
(** ... しかし、こんなことをやっていると、すぐに嫌になってしまうでしょう。その理由の一つは、データ型ごとに違ったコンストラクタの名前をつけなければならないことですが、もっと大変なのは、こういったリストを扱う関数（[length]、[rev]など）を、新しく対応した型ごとに作る必要が出てくることです。 *)

(*  To avoid all this repetition, Coq supports _polymorphic_
    inductive type definitions.  For example, here is a _polymorphic
    list_ datatype. *)
(** この無駄な繰り返し作業を無くすため、Coqは多相的な帰納的データ型の定義をサポートしています。これを使うと、多相的なリストは以下のように書くことができます。 *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

(*  This is exactly like the definition of [natlist] from the
    previous chapter, except that the [nat] argument to the [cons]
    constructor has been replaced by an arbitrary type [X], a binding
    for [X] has been added to the header, and the occurrences of
    [natlist] in the types of the constructors have been replaced by
    [list X].  (We can re-use the constructor names [nil] and [cons]
    because the earlier definition of [natlist] was inside of a
    [Module] definition that is now out of scope.)

    What sort of thing is [list] itself?  One good way to think
    about it is that [list] is a _function_ from [Type]s to
    [Inductive] definitions; or, to put it another way, [list] is a
    function from [Type]s to [Type]s.  For any particular type [X],
    the type [list X] is an [Inductive]ly defined set of lists whose
    elements are of type [X]. *)
(** これは、前の章にある[natlist]の定義とほとんどそっくりですが、コンストラクタ[cons]の引数の型が[nat]であったのに対し、任意の型を表す[X]がそれに変わっています。この[X]はヘッダに加えられた[X]と結びつけられ、さらに[natlist]であったものが[list X]に置き換わっています（ここで、コンストラクタに[nil]や[cons]といった名前を付けられるのは、最初に定義した[natlist]が[Module]の中で定義されていて、ここからはスコープの外になっているからです）。
 それでは、[list]とはいったい何なのか、ということを正確に考えて見ましょう。これを考える一つの手がかりは、リストが「型を引数にとり、帰納的な定義を返す関数である」と考えることです。あるいは「型を引数にとり、型を返す関数」と考えてもいいかもしれません。任意の型[X]について、[list X]という型は、帰納的に定義されたリストの集合で、その要素の型が[X]となっているものと考えることもできます。
 *)

(*  With this definition, when we use the constructors [nil] and
    [cons] to build lists, we need to tell Coq the type of the
    elements in the lists we are building -- that is, [nil] and [cons]
    are now _polymorphic constructors_.  Observe the types of these
    constructors: *)
(** この定義の下で、コンストラクタ[nil]や[cons]を使う際には、今作ろうとしているリストの要素の型を指定してやる必要があります。なぜなら、今や[nil]も[cons]も多相的なコンストラクタとなっているからです。 *)

Check nil.
(* ===> nil : forall X : Type, list X *)
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(*  (Side note on notation: In .v files, the "forall" quantifier
    is spelled out in letters.  In the generated HTML files and in the
    way various IDEs show .v files (with certain settings of their
    display controls), [forall] is usually typeset as the usual
    mathematical "upside down A," but you'll still see the spelled-out
    "forall" in a few places.  This is just a quirk of typesetting:
    there is no difference in meaning.) *)
(** 記法の点から: .vファイル内で、"forall"量化子は文字で綴られてます。生成されたHTMLファイル内やいくつかの
    IDEの.vファイルの表示(表示設定がそうなっている場合にですが)において、 [forall]は通常、
    数学の"ひっくりかえったA"が見えていると思います。しかし、上記のコメントなど、少数の場所では"forall"がそのまま見えているかもしれません。
    これは植字のよじれに過ぎません。意味に違いはありません *)

(*  The "[forall X]" in these types can be read as an additional
    argument to the constructors that determines the expected types of
    the arguments that follow.  When [nil] and [cons] are used, these
    arguments are supplied in the same way as the others.  For
    example, the list containing [2] and [1] is written like this: *)
(** ここで出てきた"[forall X]"というのは、コンストラクタに追加された引数で、後に続く引数で型を特定させるものです。[nil]や[cons]が使われる際、例えば[2]と[1]を要素に持つリストは、以下のように表されます。  *)

Check (cons nat 2 (cons nat 1 (nil nat))).

(*  (We've written [nil] and [cons] explicitly here because we haven't
    yet defined the [ [] ] and [::] notations for the new version of
    lists.  We'll do that in a bit.) *)
(** （ここでは[nil]や[cons]を明示的に記述していますが、それは我々がまだ[[]]や[::]の表記法（Notation）をまだ記述していないからです。この後でやります） *)

(*  We can now go back and make polymorphic versions of all the
    list-processing functions that we wrote before.  Here is [repeat],
    for example: *)
(** それでは少し話を戻して、以前書いたリスト処理関数を多相版に作り直していきましょう。[repeat]関数は以下のようになります。 *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

(*  As with [nil] and [cons], we can use [repeat] by applying it
    first to a type and then to its list argument: *)
(** [nil]と[cons]も同様に、[repeat]を 最初に型をそして次にリストの引数を適用することで使うことが出来ます。*)   

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

(*  To use [repeat] to build other kinds of lists, we simply
    instantiate it with an appropriate type parameter: *)
(** [repeat]を他の種類のリストを生成するために使うためには、型パラメータを適切に与えるだけで済みます。*)

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity.  Qed.

Module MumbleGrumble.
(* **** Exercise: 2 stars (mumble_grumble) *)
(*  Consider the following two inductively defined types. *)
(** **** 練習問題: ★★, optional (mumble_grumble) *)
(** つぎの、帰納的に定義された二つの型をよく観察してください。 *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(* Which of the following are well-typed elements of [grumble X] for
    some type [X]?
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c]
*)
(** 次の式のうち、ある型[X]について[grumble X]の要素として正しく定義されているものはどれでしょうか。
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c]
(* FILL IN HERE *)
*)
(** [] *)

End MumbleGrumble.

(* ----------------------------------------------------------------- *)
(*  *** Type Annotation Inference *)
(** *** 型推論 *)

(*  Let's write the definition of [repeat] again, but this time we
    won't specify the types of any of the arguments. Will Coq still
    accept it? *)

(** それでは、[repeat]関数の定義をもう一度書いてみましょう。ただし今回は、引数の型を指定しないでおきます。Coqはこれを受け入れてくれるでしょうか？ *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(*  Indeed it will.  Let's see what type Coq has assigned to [repeat']: *)
(** うまくいったようです。Coqが[repeat']にどのような型を設定したのか確認してみましょう。 *)

Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

(*  It has exactly the same type type as [repeat].  Coq was able
    to use _type inference_ to deduce what the types of [X], [x], and
    [count] must be, based on how they are used.  For example, since
    [X] is used as an argument to [cons], it must be a [Type], since
    [cons] expects a [Type] as its first argument; matching [count]
    with [0] and [S] means it must be a [nat]; and so on.

    This powerful facility means we don't always have to write
    explicit type annotations everywhere, although explicit type
    annotations are still quite useful as documentation and sanity
    checks, so we will continue to use them most of the time.  You
    should try to find a balance in your own code between too many
    type annotations (which can clutter and distract) and too
    few (which forces readers to perform type inference in their heads
    in order to understand your code). *)

(** 両者は[repeat]として全く同じ型であることが分かります。Coqは型推論という機構を持っていて、
    これを使い、[X]と[x]と[count]の型が何であるべきかを、その使われ方から導き出します。
    例えば、[X]が[cons]の引数として使われたことがあれば、それは型に違いなく、
    さらに[cons]の最初に引数で型が指定されていて、[l1]が[nil]や[cons]とマッチされているなら、
    それは[list]に違いなかろう、といった具合です。

    このパワフルな機構の存在は、型情報を常にそこら中に書かなければならないわけではない、
    ということを意味します。とはいえ、型を明示的に書くことは、ドキュメント作成やプログラムの
    健全性をチェックする際に大いに意味はあるのですが。とにかく、これからは自分の書くコードで、
    型指定を書くところ、書かないところのバランスを考えていく必要があります
    （多すぎれば、コードが目障りな型指定で読みにくくなりますし、
    少なすぎると、プログラムを読む人に型推論の結果をいちいち推測させなければならなくなります）。
*)

(* ----------------------------------------------------------------- *)
(*  *** Type Argument Synthesis *)
(** *** 引数の同化（Synthesis） *)

(*  To use a polymorphic function, we need to pass it one or
    more types in addition to its other arguments.  For example, the
    recursive call in the body of the [repeat] function above must
    pass along the type [X].  But since the second argument to
    [repeat] is an element of [X], it seems entirely obvious that the
    first argument can only be [X] -- why should we have to write it
    explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write the "implicit argument"
    [_], which can be read as "Please try to figure out for yourself
    what belongs here."  More precisely, when Coq encounters a [_], it
    will attempt to _unify_ all locally available information -- the
    type of the function being applied, the types of the other
    arguments, and the type expected by the context in which the
    application appears -- to determine what concrete type should
    replace the [_].

    This may sound similar to type annotation inference -- indeed, the
    two procedures rely on the same underlying mechanisms.  Instead of
    simply omitting the types of some arguments to a function, like

      repeat' X x count : list X :=

    we can also replace the types with [_]

      repeat' (X : _) (x : _) (count : _) : list X :=

    to tell Coq to attempt to infer the missing information.

    Using implicit arguments, the [count] function can be written like
    this: *)
(** 多相的な関数を使うためには、通常の引数に加えて型を一つ以上渡さなければなりません。例えば、[repeat]関数で自分を再帰している部分には、型[X]として渡されたものをそのまま渡すことになります。しかし[repeat]の二番目の引数は[X]の要素になり、最初の引数は、[X]以外になり得ないのはあきらかに見えます。・・・ならなぜわざわざそれを書く必要があるのでしょう。

    幸いなことに、Coqではこの種の冗長性を避けることができます。型を引数に渡すところではどこでも同化した引数"[_]"を書くことができるのです。これは「ここをあるべき型に解釈してください」という意味です。もう少し正確に言うと、Coqが[_]を見つけると、手近に集められる情報を集めます。それは、適用されている関数の型や、その適用が現れている文脈から予想される型などですが、それを使って[_]と置き換えるべき具体的な型を決定するのです。

    これを聞くと、型推論と同じじゃないかと思われるかもしれません。実際、この二つの機能は水面下にあるメカニズムではつながっています。次のように単に引数の型を省略する代わりに
      repeat' X x count : list X :=
    このように、型を[_]で書くことができるということです。
      repeat' (X : _) (x : _) (count : _) : list X :=
    いずれも、Coqに、欠落している情報を推論させるもので、これを引数の同化といいます。

    引数の同化を使うと、[count]([repeat]?)関数は以下のように書けます。 *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(*  In this instance, we don't save much by writing [_] instead of
    [X].  But in many cases the difference in both keystrokes and
    readability is nontrivial.  For example, suppose we want to write
    down a list containing the numbers [1], [2], and [3].  Instead of
    writing this... *)
(** この例では、[X]を[_]に省略することをあまりしていません。しかし多くの場合、この違いは打鍵数と読み易さの観点からささいなもとのは言えません。例えば、[1],[2],[3]といった数値を保持するリストを書きたい場合、以下のように書く代わりに... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
(*  ...we can use argument synthesis to write this: *)
(** ...引数同化を使って以下のように書くこともできます。 *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ----------------------------------------------------------------- *)
(*  *** Implicit Arguments *)
(** *** 暗黙の引数 *)

(*  We can go further and even avoid writing [_]'s in most cases by
    telling Coq _always_ to infer the type argument(s) of a given
    function.  The [Arguments] directive specifies the name of the
    function (or constructor) and then lists its argument names, with
    curly braces around any arguments to be treated as implicit.  (If
    some arguments of a definition don't have a name, as is often the
    case for constructors, they can be marked with a wildcard pattern
    [_].)*)
(** さらに先に進んで、大抵のケースでプログラム全体が[_]まみれになることを避けるため、特定の関数の引数については常に型推論するよう指定できます。 [Arguments] ディレクティブは、関数やコンスラクタの名前を特定し、その引数名を列挙します。そして、波カッコを引数の前後で囲むことで、その引数を暗黙的に指定されたものとして扱います。*)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(*  Now, we don't have to supply type arguments at all: *)
(** もう型引数を与える必要は全くもってなくなりました: *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(*  Alternatively, we can declare an argument to be implicit
    when defining the function itself, by surrounding it in curly
    braces.  For example: *)
(** また、関数定義の中で、引数を暗黙のものにすることもできます。その際は、次のように引数を中カッコで囲みます。 *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(*  (Note that we didn't even have to provide a type argument to the
    recursive call to [repeat''']; indeed, it would be invalid to
    provide one!)

    We will use the latter style whenever possible, but we will
    continue to use use explicit [Argument] declarations for
    [Inductive] constructors.  The reason for this is that marking the
    parameter of an inductive type as implicit causes it to become
    implicit for the type itself, not just for its constructors.  For
    instance, consider the following alternative definition of the
    [list] type: *)
(** （ここで注意してほしいのは、再帰呼び出しの[repeat''']ではもうすでに型を引数で指定していない、ということです。実のところ、引数に指定するとエラーになってしまいます！）
これからは、この書き方をできるだけ使っていくことにします。ただし、[Inductive]宣言のコンストラクタでは[Implicit Arguments]を明示的に書くようにします。 その理由は、再帰的な型パラメータを暗黙的に宣言することは、コンストラクタだけでなく、その型自身が暗黙的になる事態を引き起します。例えば、次のような[list]型の定義を考えてみましょう。*)

Inductive list' {X:Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.

(*  Because [X] is declared as implicit for the _entire_ inductive
    definition including [list'] itself, we now have to write just
    [list'] whether we are talking about lists of numbers or booleans
    or anything else, rather than [list' nat] or [list' bool] or
    whatever; this is a step too far. *)
(** [X]は [list']それ自身を含んだ再帰的定義全体で、暗黙的に宣言されているために、その[list']が数値やbooleanやその他の型のリストであったとしても、 [list' nat]や[list' bool]などの書き方ではなく、ただ[list']とだけ書かなくてはならなくなりました。やりすぎです。*)

(*  Let's finish by re-implementing a few other standard list
    functions on our new polymorphic lists... *)
(** では、他の標準的なリスト処理関数を多相的に書き直して終りとしましょう。 *)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity.  Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(*  *** Supplying Type Arguments Explicitly *)
(** *** 明示的に型引数を与えること *)

(*  One small problem with declaring arguments [Implicit] is
    that, occasionally, Coq does not have enough local information to
    determine a type argument; in such cases, we need to tell Coq that
    we want to give the argument explicitly just this time.  For
    example, suppose we write this: *)
(** 引数を暗黙的に宣言することには、小さな問題が一つあります。時折、Coqが型を特定するために必要な情報を十分に集められない時があるのです。そういう場合には、その時だけ明示してやります。例えば、もし次のように書きたかったとします。 *)

Fail Definition mynil := nil.

(*  (The [Fail] qualifier that appears before [Definition] can be
    used with _any_ command, and is used to ensure that that command
    indeed fails when executed. If the command does fail, Coq prints
    the corresponding error message, but continues processing the rest
    of the file.)

    Here, Coq gives us an error because it doesn't know what type
    argument to supply to [nil].  We can help it by providing an
    explicit type declaration (so that Coq has more information
    available when it gets to the "application" of [nil]): *)
(** [Fail]という[Definition]の前にある修飾子は、_どんな_コマンドの前でも使うことが出来て、そのコマンドが実行されたらいつでも失敗することを保証するために使われます。コマンドが失敗する際に、Coqはエラーメッセージ応答を表示しますが、ファイルの残りは続けて処理してくれます。
 ここで、Coqは[nil]に与える型パラメータが何だか分からないのでエラーを出します。このようなときは、型宣言を明示的に行うことができます（これによって[nil]を何に適用できるか、という情報が与えられます）。 *)
*)

Definition mynil : list nat := nil.

(*  Alternatively, we can force the implicit arguments to be explicit by
   prefixing the function name with [@]. *)
(** それとは別に、関数名の前に[@]を付けることで暗黙的に宣言された関数に対して型を明示的に与えることができます。 *)

Check @nil.

Definition mynil' := @nil nat.

(*  Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer these when we use the notations. *)
(** 引数同化と暗黙的な引数をつかうことで、リストのノーテーション（表記法）をより便利に記述できます。コンストラクタの型引数を暗黙的に記述すれば、Coqはその表記法を使ったときに型を自動的に推論してくれます。 *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(*  Now lists can be written just the way we'd hope: *)
(** これで、我々の望む書き方ができるようになりました。 *)

Definition list123''' := [1; 2; 3].

(* ----------------------------------------------------------------- *)
(*  *** Exercises *)
(** *** 練習問題 *)

(*  **** Exercise: 2 stars, optional (poly_exercises) *)
(** **** 練習問題: ★★, optional (poly_exercises) *combines them
    into a list of pairs.  In other functional languages, it is often
    called [zip]; we call it [combine] for consistency with Coq's
    standard library. *)
(** 次の関数は二つのリストを引数にとり、一つの"ペアのリスト"を作成します。多くの関数型言語で[zip]関数と呼ばれているものです。Coqの標準ライブラリとぶつからないよう、ここでは[combine]と呼ぶことにします。 *)
(* Note that the pair notation can be used both in expressions and in
    patterns... *)
(** ペアの表記法は、式だけではなくパターンマッチにも使えることに注目してください。 *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(** **** 練習問題: ★ (combine_checks) *)
(*  Try answering the following questions on paper and
    checking your answers in coq:
    - What is the type of [combine] (i.e., what does [Check
      @combine] print?)
    - What does

        Compute (combine [1;2] [false;false;true;true]).

      print?   [] *)
(** 次の質問の答えを紙に書いた後で、Coqの出した答えと同じかチェックしなさい。
    - 関数[combine]の型は何でしょう ([Check @combine]の出力結果は？
    - それでは
        Compute (combine [1;2] [false;false;true;true]).
      は何を出力する？   []
*)

(*  **** Exercise: 2 stars, recommended (split)  *)
(** **** 練習問題: ★★, recommended (split) *)
(*  The function [split] is the right inverse of combine: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit test. *)
(** [split]関数は[combine]と全く逆で、ペアのリストを引数に受け取り、リストのペアを返します。多くの関数型言語とで[unzip]と呼ばれているものです。次の段落のコメントをはずし、[split]関数の定義を完成させなさい。続くテストを通過することも確認しなさい。 *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
(* FILL IN HERE *) admit.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(* ** Polymorphic Options *)
(** ** 多相的オプション *)

(*  One last polymorphic type for now: _polymorphic options_,
    which generalize [natoption] from the previous chapter: *)
(** 最後に、多相的オプションに取り組みます。多相的オプションは、前の章の[natoption]を多相化して定義することにします。 *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

(*  We can now rewrite the [nth_error] function so that it works
    with any type of lists. *)
(** また、[index]関数も、色々な型のリストで使えるように定義し直しましょう。 *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(*  **** Exercise: 1 star, optional (hd_error_poly)  *)
(** **** 練習問題: ★, optional (hd_error_poly)  *)
(*  Complete the definition of a polymorphic version of the
    [hd_error] function from the last chapter. Be sure that it
    passes the unit tests below. *)
(** 前の章に出てきた[hd_error]関数の多相版を定義しなさい。。次の単体テストでの確認も忘れずに。 *)

Definition hd_error {X : Type} (l : list X) : option X :=
  (* FILL IN HERE *) admit.

(*  Once again, to force the implicit arguments to be explicit,
    we can use [@] before the name of the function. *)
(** 再び、暗黙的に定義された引数を明示的に指定してみましょう。関数名の前に[@]をつければいいのでしたね。 *)

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
 (* FILL IN HERE *) Admitted.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
 (* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(* * Functions as Data *)
(** * データとしての関数 *)

(*  Like many other modern programming languages -- including
    all functional languages (ML, Haskell, Scheme, Scala, Clojure,
    etc.) -- Coq treats functions as first-class citizens, allowing
    them to be passed as arguments to other functions, returned as
    results, stored in data structures, etc.*)
(** 他の多くの近代的なプログラミング言語 --全ての関数型言語(ML, Haskell, Scheme, Scala, Clojureなど) を含む -- と同様、Coqは関数をファーストクラスに属するものとして取り扱います。つまりそれは、関数を他の関数の引数として渡したり、結果として関数を返したり、データ構造の中に関数を含めたりすることができるということです。*)

(* ----------------------------------------------------------------- *)
(* ** Higher-Order Functions *)
(** ** 高階関数 *)

(*  Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)

(** 関数を操作する関数を、一般に「高階関数」と呼びます。例えば次のようなものです。 *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(*  The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)
(** ここで引数[f]は関数です。[doit3times]の内容は、値[n]に対して関数[f]を3回適用するものです。 *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** ** Filter *)
(** ** フィルター (Filter)関数 *)

(*  Here is a more useful higher-order function, taking a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filters" the list, returning a new list containing just those
    elements for which the predicate returns [true]. *)
(** 次に紹介するのは、もう少し有用な高階関数です。これは、[X]型のリストと、[X]についての述語（[X]を引数にとり、boolを返す関数）を引数にとり、リストの要素にフィルターをかけて、述語として与えられた関数の結果が[true]となった要素だけのリストを返す関数です。 *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(*  For example, if we apply [filter] to the predicate [evenb]
    and a list of numbers [l], it returns a list containing just the
    even members of [l]. *)
(** 例えば、この[filter]関数に述語として[evenb]と数値のリスト[l]を与えると、リスト[l]の要素の中で偶数の要素だけがリストとなって帰ります。 *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(*  We can use [filter] to give a concise version of the
    [countoddmembers] function from the [Lists] chapter. *)
(** この[filter]を使うことで、 [Lists.v]にある[countoddmembers]関数をもっと簡潔に書くことができます。 *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** ** 無名（匿名）関数 *)

(*  It is arguably a little sad, in the example just above, to
    be forced to define the function [length_is_1] and give it a name
    just to be able to pass it as an argument to [filter], since we
    will probably never use it again.  Moreover, this is not an
    isolated example: when using higher-order functions, we often want
    to pass as arguments "one-off" functions that we will never use
    again; having to give each of these functions a name would be
    tedious.

    Fortunately, there is a better way.  We can construct a function
    "on the fly" without declaring it at the top level or giving it a
    name. *)
(** [filter]関数に渡すためだけに、二度と使われない[length_is_1]といった関数を定義して、それにわざわざ名前を付けるというのは、間違いなく悲しいことです。このようなことは、この例だけの問題ではありません。高階関数を使うときは、引数として"一度しか使わない関数"を渡すことがよくあります。こういう関数にいちいち名前を考えるのは、退屈以外の何物でもありません。

    幸いなことに、いい方法があります。一時的な関数を、名前を付けることも、トップレベルで宣言することもなく作成することができるのです。*)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(* Here is the motivating example from before, rewritten to use
    an anonymous function. *)
(** 次は無名関数を使った書き換えのもう少しマシな例です。 *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(*  **** Exercise: 2 stars (filter_even_gt7)  *)
(** **** 練習問題: ★★, optional (filter_even_gt7) *)

(*  Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)
(** [filter]関数を使い、数値のリストを入力すると、そのうち偶数でなおかつ7より大きい要素だけを取り出す[filter_even_gt7]関数を書きなさい。 *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  (* FILL IN HERE *) admit.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* FILL IN HERE *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars (partition)  *)
(** **** 練習問題: ★★★, optional (partition) *)
(*  Use [filter] to write a Coq function [partition]:
      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X
   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list. *)
(** [filter]関数を使って、[partition]関数を書きなさい。:
  partition : forall X : Type,
              (X -> bool) -> list X -> list X * list X
   型[X]について、[X]型の値がある条件を満たすかを調べる述語[X -> bool]と[X]のリスト[list X]を引数に与えると、[partition]関数はリストのペアを返します。ペアの最初の要素は、与えられたリストのうち、条件を満たす要素だけのリストで、二番目の要素は、条件を満たさないもののリストです。二つのリストの要素の順番は、元のリストの順と同じでなければなりません。*)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
(* FILL IN HERE *) admit.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* FILL IN HERE *) Admitted.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
(* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(*  ** Map *)
(** ** マップ（Map）関数 *)

(* Another handy higher-order function is called [map]. *)
(** もう一つ、便利な高階関数として[map]を挙げます。 *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(*  It takes a function [f] and a list [ l = [n1, n2, n3, ...] ]
    and returns the list [ [f n1, f n2, f n3,...] ], where [f] has
    been applied to each element of [l] in turn.  For example: *)
(** これは、関数[f]とリスト[ l = [n1, n2, n3, ...] ]を引数にとり、関数[f]を[l]の各要素に適用した[ [f n1, f n2, f n3,...] ]というリストを返します。例えばこのようなものです。 *)

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(*  The element types of the input and output lists need not be
    the same, since [map] takes _two_ type arguments, [X] and [Y]; it
    can thus be applied to a list of numbers and a function from
    numbers to booleans to yield a list of booleans: *)
(** 入力されるリストの要素の型と、出力されるリストの要素の型は同じである必要はありません。[map]は、[X]と[Y]二種類の型変数を取るからです。それゆえ、数値のリストと、数値を受け取り[bool]値を返す関数から、bool型のリストを返します。 *)

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

(* It can even be applied to a list of numbers and
    a function from numbers to _lists_ of booleans to
    yield a _list of lists_ of booleans: *)
(** 同じ関数が、数値のリストと、「数値から[bool]型のリストへの関数」を引数にとり、「[bool]型のリストのリスト」を返すような関数にも使えます。 *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.

(*  *** Exercises *)
(** *** 練習問題 *)

(** **** 練習問題: ★★★, optional (map_rev) *)
(*  Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)
(** [map]と[rev]が可換であることを示しなさい。証明には補題をたてて証明する必要があるでしょう。 *)

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, recommended (flat_map) *)
(*  The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:

        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].

*)
(** [map]関数は、[list X]から[list Y]へのマップを、型[X -> Y]の関数を使って実現しています。同じような関数[flat_map]を定義しましょう。これは[list X]から[list Y]へのマップですが、[X -> list Y]となる関数[f]を使用できます。このため、次のように要素ごとの関数[f]の結果を平坦化してやる必要があります。
        flat_map (fun n => [n,n+1,n+2]) [1,5,10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
  (* FILL IN HERE *) admit.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* FILL IN HERE *) Admitted.
(** [] *)

(*  Lists are not the only inductive type that we can write a
    [map] function for.  Here is the definition of [map] for the
    [option] type: *)
(** リストは、[map]関数のような関数に渡すことができる、帰納的に定義された唯一の型、というわけではありません。次の定義は、[option]型のために[map]関数を定義したものです。 *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(*  **** Exercise: 2 stars, optional (implicit_args)  *)
(** **** 練習問題: ★★, optional (implicit_args) *)
(*  The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  (This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.)  [] *)
(** [filter]や[map]関数を定義したり使ったりするケースでは、多くの場合暗黙的な型引数が使われます。暗黙の型引数定義に使われている中括弧を普通の括弧に置き換え、必要なところに型引数を明示的に書くようにして、それが正しいかどうかをCoqでチェックしなさい。 [] *)

(* ----------------------------------------------------------------- *)
(*  ** Fold *)
(** ** 畳み込み（Fold）関数 *)

(*  An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)
(** さらにパワフルな高階関数[fold]に話を移します。この関数はGoogleの分散フレームワーク"map/reduce"でいうところの"reduce"オペレーションに根ざしています。 *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(*  Intuitively, the behavior of the [fold] operation is to
    insert a given binary operator [f] between every pair of elements
    in a given list.  For example, [ fold plus [1;2;3;4] ] intuitively
    means [1+2+3+4].  To make this precise, we also need a "starting
    element" that serves as the initial second input to [f].  So, for
    example,

       fold plus [1;2;3;4] 0

    yields

       1 + (2 + (3 + (4 + 0))).

    Some more examples: *)
(** 直感的に[fold]は、与えられたリストの各要素の間に、与えられた二項演算子[f]を挟み込むように挿入していくような操作です。 例えば、[ fold plus [1,2,3,4] ]は、直感的に[1+2+3+4]と同じ意味です。ただし正確には、二番めの引数に、[f]に最初に与える"初期値"が必要になります。例えば

   fold plus [1,2,3,4] 0

    は、次のように解釈されます。

   1 + (2 + (3 + (4 + 0))).

    もう少しサンプルを見てください。
*)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(*  **** Exercise: 1 star, advanced (fold_types_different)  *)
(** **** 練習問題: ★, optional (fold_types_different) *)
(*  Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different? *)
(** [fold]関数が[X]と[Y]二つの型引数をとっていて、関数[f]が型[X]を引数にとり型[Y]を返すようになっていることに注目してください。[X]と[Y]が別々の型となっていることで、どのような場合に便利であるかを考えてください。 *)

(* ----------------------------------------------------------------- *)
(*  ** Functions That Construct Functions *)
(** ** 関数を作成する関数 *)

(*  Most of the higher-order functions we have talked about so
    far take functions as arguments.  Let's look at some examples that
    involve _returning_ functions as the results of other functions.
    To begin, here is a function that takes a value [x] (drawn from
    some type [X]) and returns a function from [nat] to [X] that
    yields [x] whenever it is called, ignoring its [nat] argument. *)
(** これまで見てきた高階関数は、ほとんどが関数を引数にとるものでした。ここでは、関数が別の関数の戻り値になるような例を見ていきましょう。

    まず、値[x]（型[X]）を引数としてとり、「[nat]型の引数から[X]型の戻り値を返す関数」を返す関数を考えます。戻る関数は、引数に関係なく、生成時に与えられた値｢x｣を常に返すものです。 *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(*  In fact, the multiple-argument functions we have already
    seen are also examples of passing functions as data.  To see why,
    recall the type of [plus]. *)
(** 実は、我々がすでに見た、複数の引数を持つ関数は、関数を引数に渡すサンプルになっているのです。どういうことかは、[plus]関数の型を思い出せば分かります。*)

Check plus.
(* ==> nat -> nat -> nat *)

(*  Each [->] in this expression is actually a _binary_ operator
    on types.  This operator is _right-associative_, so the type of
    [plus] is really a shorthand for [nat -> (nat -> nat)] -- i.e., it
    can be read as saying that "[plus] is a one-argument function that
    takes a [nat] and returns a one-argument function that takes
    another [nat] and returns a [nat]."  In the examples above, we
    have always applied [plus] to both of its arguments at once, but
    if we like we can supply just the first.  This is called _partial
    application_. *)
(** [->]は、型同士の二項演算子ですが、このことはCoqが基本的に引数一つの関数しかサポートしていないことを意味します。さらに、この演算子は右結合であるため、[plus]関数の型は[nat -> (nat -> nat)]の省略であると言えます。これをよく読むと"[plus]は[nat]型の引数を一つ取り、引数が[nat]型一つで[nat]型を返す関数を返す"と読むことができます。以前の例では[plus]に二つの引数を一緒に与えていましたが、もし望むなら最初の一つだけを与えることもできます。これを部分適用といいます。 *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(*  * Additional Exercises *)
(** * さらなる練習問題 *)

Module Exercises.

(*  **** Exercise: 2 stars (fold_length)  *)
(** **** 練習問題: ★★, optional (fold_length) *)
(*  Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternative definition of [length]: *)
(** リストに関する多くの一般的な関数は[fold]を使って書きなおすることができます。例えば、次に示すのは[length]の別な実装です。 *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(*  Prove the correctness of [fold_length]. *)
(** [fold_length]が正しいことを証明しなさい。 *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
(* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars (fold_map)  *)
(** **** 練習問題: ★★★, (fold_map) *)
(*  We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)
(** [map]関数も[fold]を使って書くことができます。以下の[fold_map]を完成させなさい。 *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
(* FILL IN HERE *) admit.

(*  Write down a theorem [fold_map_correct] in Coq stating that
   [fold_map] is correct, and prove it. *)
(** [fold_map]が正しいことを示す定理をCoqで書き、証明しなさい *)

(* FILL IN HERE *)
(** [] *)

(*  **** Exercise: 2 stars, advanced (currying)  *)
(** **** 練習問題: ★★, advanced (currying) *)
(*  In Coq, a function [f : A -> B -> C] really has the type [A
    -> (B -> C)].  That is, if you give [f] a value of type [A], it
    will give you function [f' : B -> C].  If you then give [f'] a
    value of type [B], it will return a value of type [C].  This
    allows for partial application, as in [plus3].  Processing a list
    of arguments with functions that return functions is called
    _currying_, in honor of the logician Haskell Curry.

    Conversely, we can reinterpret the type [A -> B -> C] as [(A *
    B) -> C].  This is called _uncurrying_.  With an uncurried binary
    function, both arguments must be given at once as a pair; there is
    no partial application. *)
(** Coqでは、[f : A -> B -> C]という型の関数は[A -> (B -> C)]型と同じです。このことは、もし上の関数[f]に値[A]を与えると、[f' : B -> C]という型の関数が戻り値として返ってくるということです。これは部分適用の[plus3]でやりましたが、このように、複数の引数から戻り値の型のリストを、関数を返す関数として捉えなおすことを、論理学者ハスケル・カリーにちなんでカリー化、と呼んでいます。

    逆に、[A -> B -> C]型の関数を[(A * B) -> C]型の関数に変換することもできます。これをアンカリー化（非カリー化）といいます。アンカリー化された二項演算は、二つの引数を同時にペアの形で与える必要があり、部分適用はできません。 *)

(*  We can define currying as follows: *)
(** カリー化は以下のように定義できます。 *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(*  As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)
(** 練習問題として、その逆の[prod_uncurry]を定義し、二つの関数が互いに逆関数であることを証明しなさい。 *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  (* FILL IN HERE *) admit.

(*  As a trivial example of the usefulness of currying, we can use it
    to shorten one of the examples that we saw above: *)
(** カリー化のちょっとした有用性の例として、既に見てきたexampleのショートバージョンを作ることが出来ます。*)

Example test_map2: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(*  Thought exercise: before running the following commands, can you
    calculate the types of [prod_curry] and [prod_uncurry]? *)
(** (考える練習: 次のコマンドを実行する前に、[prod_curry]と[prod_uncurry]の型を考えなさい。) *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 2 stars, advanced (nth_error_informal)  *)
(** **** 練習問題: ★★, advanced (nth_error_informal)  *)
(* Recall the definition of the [nth_error] function:

   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
     end.

   Write an informal proof of the following theorem:

   forall X n l, length l = n -> @nth_error X l n = None

(* FILL IN HERE *)
*)
(** [nth_error]関数の定義を思い出してください。

   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
     end.

   次の定理の非形式的な証明を書きましょう。
   forall X n l, length l = n -> @nth_error X l n = None
(** [] *)

(*  **** Exercise: 4 stars, advanced (church_numerals)  *)
(** **** 練習問題: ★★★★, advanced (church_numerals)  *)
(** This exercise explores an alternative way of defining natural
    numbers, using the so-called _Church numerals_, named after
    mathematician Alonzo Church.  We can represent a natural number
    [n] as a function that takes a function [f] as a parameter and
    returns [f] iterated [n] times. *)
(** この練習問題で、アロンゾチャーチにちなんで名付けられた _チャーチ数_ と呼ばれる自然数を定義するもう一つの方法について、詳しく見ていきましょう。自然数[n]は、パラメータとしての関数[f]をとり、[f]を[n]回繰り返して適用する関数として表現されます。もっと形式的には、以下のように表現します。*)

Module Church.
Definition nat := forall X : Type, (X -> X) -> X -> X.

(*  Let's see how to write some numbers with this notation. Iterating
    a function once should be the same as just applying it.  Thus: *)
(** この記法を使って数をどのように書くのかをいくつか見てみましょう。関数適用を一度だけ繰り返すことは、単に関数を実行することを同じことです。つまり、*)

Definition one : nat := 
  fun (X : Type) (f : X -> X) (x : X) => f x.

(*  Similarly, [two] should apply [f] twice to its argument: *)
(** 同様に[two] は[f]を二度、その引数に適用します。*)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** Defining [zero] is somewhat trickier: how can we "apply a function
    zero times"?  The answer is actually simple: just return the
    argument untouched. *)
(** [zero] はいくらか手がこんでます。関数を零回適用するとは、どういうことでしょうか？答えは単純です。引数に対して何もしないだけです。*)

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(*  More generally, a number [n] can be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f].  Notice in
    particular how the [doit3times] function we've defined previously
    is actually just the Church representation of [3]. *)
(** もっと一般的に、数[n]は [ fun X f x => f (f ... (f x) ...)]のように、[f]が[n]回出現するように書きます。とりわけ、以前[doit3times]関数を定義したやりかたは実際に[3]を表していることに注意しましょう。*)

Definition three : nat := @doit3times.

(*  Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)
(** 次の関数の定義を完成させなさい。定義に対応する単体テストが[reflexivity]を使って証明することで、通ることを確認しなさい。*)

(* Successor of a natural number *)
(** 自然数の後者関数 *)

Definition succ (n : nat) : nat :=
  (* FILL IN HERE *) admit.

Example succ_1 : succ zero = one.
Proof. (* FILL IN HERE *) Admitted.

Example succ_2 : succ one = two.
Proof. (* FILL IN HERE *) Admitted.

Example succ_3 : succ two = three.
Proof. (* FILL IN HERE *) Admitted.

(*  Addition of two natural numbers: *)
(** 二つの自然数の和: *)

Definition plus (n m : nat) : nat :=
  (* FILL IN HERE *) admit.

Example plus_1 : plus zero one = one.
Proof. (* FILL IN HERE *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* FILL IN HERE *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* FILL IN HERE *) Admitted.

(*  Multiplication *)
(** 積 *)

Definition mult (n m : nat) : nat :=
  (* FILL IN HERE *) admit.

Example mult_1 : mult one one = one.
Proof. (* FILL IN HERE *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* FILL IN HERE *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* FILL IN HERE *) Admitted.

(* Exponentiation *)
(** 累乗 *)

(*  (_Hint_: Polymorphism plays a crucial role here. However, choosing
    the right type to iterate over can be tricky. If you hit a
    "Universe inconsistency" error, try iterating over a different
    type: [nat] itself is usually problematic.) *)
(** ヒント: 多相がここでは重要な役割を演じます。しかし、繰りかえし適用する正しい型を選ぶことは、技巧的になりえます。もし "Universe inconsistency"エラーに遭遇したら、違う型を試してみましょう。[nat]それ自身は、通常解決の難しいものです。 *)

Definition exp (n m : nat) : nat :=
  (* FILL IN HERE *) admit.

Example exp_1 : exp two two = plus two two.
Proof. (* FILL IN HERE *) Admitted.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. (* FILL IN HERE *) Admitted.

Example exp_3 : exp three zero = one.
Proof. (* FILL IN HERE *) Admitted.

End Church.
(** [] *)

End Exercises.

(** $Date: 2016-05-26 16:17:19 -0400 (Thu, 26 May 2016) $ *)












################################################### *)
Digression: Currying *)
 余談： カリー化 *)

Similarly, but a bit more interestingly, here is a function
at takes a function [f] from numbers to some type [X], a number
], and a value [x], and constructs a function that behaves
actly like [f] except that, when called with the argument [k],
 returns [x]. *)
う少し面白い例を挙げます。次の関数は、数値から型[X]を戻す関数[f]と、数値[k]、型[X]の値[x]を引数にとり、[f]に[k]と同じ引数が与えられた場合だけ値[x]を返し、それ以外のときは[f]に[k]を渡した戻り値を返します。 *)

tion override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
(k':nat) => if beq_nat k k' then x else f k'.

r example, we can apply [override] twice to obtain a
nction from numbers to booleans that returns [false] on [1] and
] and returns [true] on all other arguments. *)
とえば、この[override]関数を数値から[bool]型への関数に以下のように２回適用すると、値が[1]と[3]のときだけ[false]を返し、それ以外はtrueを返すようにすることができます。 *)

tion fmostlytrue := override (override ftrue 1 false) 3 false.

* *)

e override_example1 : fmostlytrue 0 = true.
 reflexivity. Qed.

e override_example2 : fmostlytrue 1 = false.
 reflexivity. Qed.

e override_example3 : fmostlytrue 2 = true.
 reflexivity. Qed.

e override_example4 : fmostlytrue 3 = false.
 reflexivity. Qed.

* *)

** 練習問題: ★ (override_example)  *)
fore starting to work on the following proof, make sure you
derstand exactly what the theorem is saying and can paraphrase
 in your own words.  The proof itself is straightforward. *)
の証明にとりかかる前に、あなたがこの証明の意味することを理解しているか確認するため、証明内容を別の言葉で言い換えてください。証明自体は単純なものです。 *)

m override_example : forall (b:bool),
rride (constfun b) 3 true) 2 = b.

ILL IN HERE *) Admitted.
 *)

'll use function overriding heavily in parts of the rest of the
urse, and we will end up needing to know quite a bit about its
operties.  To prove these properties, though, we need to know
out a few more of Coq's tactics; developing these is the main
pic of the next chapter.  For now, though, let's introduce just
e very useful tactic that will also help us with proving
operties of some of the other functions we have introduced in
is chapter. *)
のコースでこれ以降、関数のオーバーライド（上書き）がよく登場しますが、この性質について多くを知る必要はありません。しかし、これらの性質を証明するには、さらにいくつかのCoqのタクティックを知らなければなりません。それが、この章の残りの部分の主なトピックになります。 *)

################################################### *)

################################################### *)
[unfold]タクティック *)

metimes, a proof will get stuck because Coq doesn't
tomatically expand a function call into its definition.  (This
 a feature, not a bug: if Coq automatically expanded everything
ssible, our proof goals would quickly become enormous -- hard to
ad and slow for Coq to manipulate!) *)
折、Coqが関数を自動的に展開してくれないために証明が行き詰まってしまうことがあります（これは仕様であって、バグではありません。Coqがもし可能な展開を全て自動でやってしまったら、証明のゴールはたちまち巨大化して、読むこともCoqで操作することもできなくなってしまいます）。 *)

m unfold_example_bad : forall m n,
n = m ->
3 n + 1 = m + 1.

os m n H.
t this point, we'd like to do [rewrite -> H], since 
plus3 n] is definitionally equal to [3 + n].  However, 
oq doesn't automatically expand [plus3 n] to its 
efinition. *)
  (* ここでは[rewrite -> H]としたいところです。なぜなら、[plus3 n]はと同じ定義と言えるからです。しかしCoqは[plus3 n]をその定義に従って自動的に展開してくれません。 *)
  Abort.

(*  The [unfold] tactic can be used to explicitly replace a
    defined name by the right-hand side of its definition.  *)
(** [unfold]タクティックは、定義された名前を、その定義の右側の記述に置き換えてくれるものです。  *)

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.  Qed.

(*  Now we can prove a first property of [override]: If we
    override a function at some argument [k] and then look up [k], we
    get back the overridden value. *)
(** 今我々は、[override]の最初の性質を証明することができるようになりました。もしある関数の引数のある値[k]をオーバーライドしてから引数[k]を与えると、オーバーライドされた値が帰る、というものです。 *)

Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.  Qed.

(*  This proof was straightforward, but note that it requires
    [unfold] to expand the definition of [override]. *)
(** この証明はストレートなものですが、[override]関数の展開に[unfold]を必要としている点だけ注意してください。 *)

(** **** 練習問題: ★★ (override_neq) *)
Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  As the inverse of [unfold], Coq also provides a tactic
    [fold], which can be used to "unexpand" a definition.  It is used
    much less often. *)
(** [unfold]の逆の機能として、Coqには[fold]というタクティックも用意されています。これは、展開された定義を元に戻してくれますが、あまり使われることはありません。 *)


