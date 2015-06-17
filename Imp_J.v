(** * Imp: Simple Imperative Programs *)

(* In this chapter, we begin a new direction that will continue for
    the rest of the course.  Up to now most of our attention has been
    focused on various aspects of Coq itself, while from now on we'll
    mostly be using Coq to formalize other things.  (We'll continue to
    pause from time to time to introduce a few additional aspects of
    Coq.)

    Our first case study is a _simple imperative programming language_
    called Imp, embodying a tiny core fragment of conventional
    mainstream languages such as C and Java.  Here is a familiar
    mathematical function written in Imp.
*)
(** この章では、コースの残りに続く新しい方向へ進み始めます。
    ここまではもっぱらCoq自身について学習してきましたが、ここからは、
    主として別のものを形式化するためにCoqを使います。(ときどき、
	いくつかのCoqの付加的な側面について紹介します)
    
    はじめの例は、Imp と呼ばれる単純な命令型プログラミング言語です。
	CやJavaのような標準的な言語のコアな部分を抜き出したようなものです。
    下の例は、おなじみの数学的関数を Imp で書いたものです。
     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END
*)

(* This chapter looks at how to define the _syntax_ and _semantics_
    of Imp; the chapters that follow develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, a widely used logic for
    reasoning about imperative programs. *)
(** この章ではImpの構文(_syntax_)と意味(_semantics_)をどのように定義するかを見ます。
    続く章では、プログラムの同値性(_program equivalence_)の理論を展開し、
    命令型プログラムについての推論のための論理として一番知られているホーア論理
    (_Hoare Logic_)を紹介します。 *)

(* ####################################################### *)
(** *** Sflib *)

(*  A minor technical point: Instead of asking Coq to import our
    earlier definitions from chapter [Logic], we import a small library
    called [Sflib.v], containing just a few definitions and theorems
    from earlier chapters that we'll actually use in the rest of the
    course.  This change should be nearly invisible, since most of what's
    missing from Sflib has identical definitions in the Coq standard
    library.  The main reason for doing it is to tidy the global Coq
    environment so that, for example, it is easier to search for
    relevant theorems. *)
(** マイナーな技術的ポイント: ここまでの定義をLogic_J.vからインポートする代わりに、
    Sflib_J.vという小さなライブラリをインポートします。 このライブラリは、
    前の章の定義や定理のうち、残りの章で実際に使うものだけを集めたものです。 
    読者はそれほど違うものとは感じないでしょう。というのは、 Sflib で抜けているものの
    ほとんどは、Coqの標準ライブラリの定義と同じものだからです。 
    こうする主な理由は、Coqのグローバルな環境を整理して、例えば、
    関係する定理を探すのを容易にするためです。*)

Require Export SfLib.

(* ####################################################### *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(* ####################################################### *)
(** ** Syntax *)

Module AExp.

(* These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)
(** 次の2つの定義は、算術式とブール式の抽象構文(_abstract syntax_)を定めます。*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(* In this chapter, we'll elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1+2*3"] to the AST [APlus (ANum
    1) (AMult (ANum 2) (ANum 3))].  The optional chapter [ImpParser]
    develops a simple implementation of a lexical analyzer and parser
    that can perform this translation.  You do _not_ need to
    understand that file to understand this one, but if you haven't
    taken a course where these techniques are covered (e.g., a
    compilers course) you may want to skim it. *)
(** この章では、プログラマが実際に書く具象構文から抽象構文木への変換は省略します。
    例えば、文字列["1+2*3"]をAST(Abstract Syntax Tree, 抽象構文木) 
    [APlus (ANum 1) (AMult (ANum 2) (ANum 3))] にする変換のことです。
    この変換ができる字句解析器と構文解析器をファイル[ImpParser_J.v]で簡単に実装します。
    このファイル([Imp_J.v])を理解するには[ImpParser_J.v]の理解は必要ではありませんが、
    もしそれらの技術についてのコース(例えばコンパイラコース)を受講していないならば、
    ざっと見てみるのも良いでしょう。 *)

(** For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:*)
(** 比較のため、同じ抽象構文を定義する慣習的なBNF(Backus-Naur Form)
    文法を以下に示します:
    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | not b
        | b and b
*)

(* Compared to the Coq version above...

       - The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written [+] and is an
         infix symbol) while leaving other aspects of lexical analysis
         and parsing (like the relative precedence of [+], [-], and
         [*]) unspecified.  Some additional information -- and human
         intelligence -- would be required to turn this description
         into a formal definition (when implementing a compiler, for
         example).

         The Coq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - On the other hand, the BNF version is lighter and
         easier to read.  Its informality makes it flexible, which is
         a huge advantage in situations like discussions at the
         blackboard, where conveying general ideas is more important
         than getting every detail nailed down precisely.

         Indeed, there are dozens of BNF-like notations and people
         switch freely among them, usually without bothering to say which
         form of BNF they're using because there is no need to: a
         rough-and-ready informal understanding is all that's
         needed. *)
(** 上述のCoq版と比較して...

       - BNFはより非形式的です。例えば、
         BNFは式の表面的な構文についていくらかの情報を与えています
         (可算は[+]と記述され、それは中置記号であるという事実などです)が、
         字句解析と構文解析の他の面は定めないままになっています([+]、[-]、[*]
         の相対的優先順位などです)。
         (例えばコンパイラを実装するときに)この記述を形式的定義にするためには、
         追加の情報、および人間の知性が必要でしょう。

         Coq版はこれらの情報を整合的に省略し、抽象構文だけに集中します。

       - 一方、BNF版はより軽くて、おそらく読むのがより簡単です。
         非形式的であることで柔軟性を持っているので、
         黒板を使って議論する場面などでは特段に有効です。
         そういう場面では、細部をいちいち正確に確定させていくことより、
         全体的アイデアを伝えることが重要だからです。

         実際、BNFのような記法は山ほどあり、人は皆、それらの間を自由に行き来しますし、
         通常はそれらのうちのどのBNFを使っているかを気にしません。
         その必要がないからです。おおざっぱな非形式的な理解だけが必要なのです。 *)


(* It's good to be comfortable with both sorts of notations:
    informal ones for communicating between humans and formal ones for
    carrying out implementations and proofs. *)
(** 両方の記法に通じているのは良いことです。
    非形式的なものは人間とのコミュニケーションのために、
    形式的なものは実装と証明のためにです。 *)

(* ####################################################### *)
(** ** Evaluation *)

(* _Evaluating_ an arithmetic expression produces a number. *)
(** 算術式を評価する(_evaluating_)とその式を1つの数に簡約します。 *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(* Similarly, evaluating a boolean expression yields a boolean. *)
(** 同様に、ブール式を評価するとブール値になります。*)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => ble_nat (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ####################################################### *)
(* ** Optimization *)
(** ** 最適化(Optimization) *)

(* We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0+e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)
(** ここまで定義したものはわずかですが、その定義から既にいくらかのものを得ることができます。
    算術式をとって、それを少し簡単化する関数を定義するとします。
    すべての [0+e] (つまり [(APlus (ANum 0) e)])を単に[e]にするものです。 *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
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

(* To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)
(** この最適化が正しいことをすることを確認するために、
    いくつかの例についてテストして出力がよさそうかを見てみることができます。 *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(* But if we want to be sure the optimization is correct --
    i.e., that evaluating an optimized expression gives the same
    result as the original -- we should prove it. *)
(** しかし、もし最適化が正しいことを確認したいならば、
    -- つまり、最適化した式がオリジナルの式と同じ評価結果を返すことを確認したいならば、
    証明すべきです。 *)

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  Case "ANum". reflexivity.
  Case "APlus". destruct a1.
    SCase "a1 = ANum n". destruct n.
      SSCase "n = 0".  simpl. apply IHa2.
      SSCase "n <> 0". simpl. rewrite IHa2. reflexivity.
    SCase "a1 = APlus a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    SCase "a1 = AMinus a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    SCase "a1 = AMult a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  Case "AMult".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* ####################################################### *)
(* * Coq Automation *)
(** * Coq の自動化 *)

(* The repetition in this last proof is starting to be a little
    annoying.  If either the language of arithmetic expressions or the
    optimization being proved sound were significantly more complex,
    it would begin to be a real problem.

    So far, we've been doing all our proofs using just a small handful
    of Coq's tactics and completely ignoring its powerful facilities
    for constructing parts of proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some
    energy -- Coq's automation is a power tool -- but it will allow us
    to scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, low-level details. *)
(** 前の証明の最後の繰り返しはちょっと面倒です。今のところまだ耐えられますが、
    証明対象の言語や算術式や最適化が今に比べて著しく複雑だったら、現実的に問題になるでしょう。

    ここまで、Coq のタクティックのほんのひとつかみだけですべての証明をしてきていて、
    証明を自動的に構成する非常に強力な機構を完全に無視してきました。
    このセクションではこれらの機構のいくつかを紹介します。
    それ以上のものを、以降のいくつかの章で次第に見ることになるでしょう。
    それらに慣れるには多少エネルギーが必要でしょう。
    -- Coq の自動化は電動工具です。--
    しかし自動化機構を使うことで、より複雑な定義や、より興味深い性質について、
    退屈で繰り返しの多いローレベルな詳細に飲み込まれることなく、
    作業をスケールアップできます。 *)

(* ####################################################### *)
(* ** Tacticals *)
(** ** タクティカル(Tacticals) *)

(* _Tacticals_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)
(** タクティカル(_tactical_)は Coq の用語で、
    他のタクティックを引数に取るタクティックのことです。
    「高階タクティック」("higher-order tactics")と言っても良いでしょう。 *)

(* ####################################################### *)
(* *** The [repeat] Tactical *)
(** *** [repeat] タクティカル *)

(* The [repeat] tactical takes another tactic and keeps applying
    this tactic until the tactic fails. Here is an example showing
    that [100] is even using repeat. *)
(** [repeat]タクティカルは、別のタクティックを引数として取り、そのタクティックが失敗するまで適用を続けます。以下は、repeatを使用した[100]が偶数であることをの証明の例です。*)

Theorem ev100 : ev 100.
Proof.
  repeat (apply ev_SS). (* applies ev_SS 50 times,
                           until [apply ev_SS] fails *)
  apply ev_0.
Qed.
(* Print ev100. *)

(** The [repeat T] tactic never fails; if the tactic [T] doesn't apply
    to the original goal, then repeat still succeeds without changing
    the original goal (it repeats zero times). *)
(** [repeat T]タクティックは決して失敗しません。もし、タクティック[T]が現在のゴールに適用できない場合、ゴールを変更することなく、成功するまで繰り返します。(つまり0回繰り返します。*)
Theorem ev100' : ev 100.
Proof.
  repeat (apply ev_0). (* doesn't fail, applies ev_0 zero times *)
  (* 失敗はしません。ev_0が0回適用されます *)
  repeat (apply ev_SS). apply ev_0. (* we can continue the proof *)
  (* 証明を続行します。 *)
Qed.

(** The [repeat T] tactic does not have any bound on the number of
    times it applies [T]. If [T] is a tactic that always succeeds then
    repeat [T] will loop forever (e.g. [repeat simpl] loops forever
    since [simpl] always succeeds). While Coq's term language is
    guaranteed to terminate, Coq's tactic language is not! *)
(** [repeat T]タクティックは、[T]を適用する回数の限界値について関知しません。
もし、[T]が常に成功する場合、[T]を永久に繰り返します。(例えば、[repeat simpl]は
[simpl]が常に成功するため、無限ループします。) Coqは自身の言語については、終了を保証していますが、
Coqのタクティック言語については、そうではないのです。*)
(* ####################################################### *)
(** *** The [try] Tactical *)

(** If [T] is a tactic, then [try T] is a tactic that is just like [T]
    except that, if [T] fails, [try T] _successfully_ does nothing at
    all (instead of failing). *)
(** [T]がタクティックのとき、タクティック [try T] は[T]と同様ですが、[T]が失敗するとき[try T] は(失敗せずに)
何もしない点が違います。 *)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does [reflexivity] *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (*  [reflexivity] が失敗するだけ *)
  apply HP. (* 別の方法で証明を終わらせることは出来ます。 *)
Qed.

(* Using [try] in a completely manual proof is a bit silly, but
    we'll see below that [try] is very useful for doing automated
    proofs in conjunction with the [;] tactical. *)
(** [try]タクティックを手動の証明で使用することは少し馬鹿げていると思われるかもしれまんが、
こみいった自動化された証明において、[;]と同時に使用することで非常に便利になります *)
(* ####################################################### *)
(* *** The [;] Tactical (Simple Form) *)
(** *** [;]タクティカル(単純な形式) *)

(* In its most commonly used form, the [;] tactical takes two tactics
    as argument: [T;T'] first performs the tactic [T] and then
    performs the tactic [T'] on _each subgoal_ generated by [T]. *)
(** [;]が最も使用されるのは、[T;T']ように、二つのタクティックを引数にとるやりかたです。最初にタクティック[T]が実行され、
次にタクティック[T']が[T]によって生成された、それぞれのサブゴールにおいて実行されます。*)
(* For example, consider the following trivial lemma: *)
(** 例として、次のちょっとした補題について考えてみましょう: *)

Lemma foo : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. reflexivity.
Qed.

(* We can simplify this proof using the [;] tactical: *)
(** [;] タクティカルを使用することで証明がシンプルになります。: *)

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n; (* [destruct] the current goal *)
  simpl; (* then [simpl] each resulting subgoal *)
  reflexivity. (* and do [reflexivity] on each resulting subgoal *)
Qed.

(* Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)
(** [try]と[;]の両方を使うと、
    ちょっと前に悩まされた証明の繰り返しを取り除くことができます。 *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  (* The remaining cases -- ANum and APlus -- are different *)
  Case "ANum". reflexivity.
  Case "APlus".
    destruct a1;
      (* Again, most cases follow directly by the IH *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the [try...] does nothing,
       is when [e1 = ANum n]. In this case, we have to destruct
       [n] (to see whether the optimization applies) and rewrite
       with the induction hypothesis. *)
    SCase "a1 = ANum n". destruct n;
      simpl; rewrite IHa2; reflexivity.   Qed.

(* Coq experts often use this "[...; try... ]" idiom after a tactic
    like [induction] to take care of many similar cases all at once.
    Naturally, this practice has an analog in informal proofs.

    Here is an informal proof of this theorem that matches the
    structure of the formal one: 

    _Theorem_: For all arithmetic expressions [a],
       aeval (optimize_0plus a) = aeval a.
    _Proof_: By induction on [a].  The [AMinus] and [AMult] cases
    follow directly from the IH.  The remaining cases are as follows:

      - Suppose [a = ANum n] for some [n].  We must show
          aeval (optimize_0plus (ANum n)) = aeval (ANum n).
        This is immediate from the definition of [optimize_0plus].

      - Suppose [a = APlus a1 a2] for some [a1] and [a2].  We
        must show
          aeval (optimize_0plus (APlus a1 a2))
        = aeval (APlus a1 a2).
        Consider the possible forms of [a1].  For most of them,
        [optimize_0plus] simply calls itself recursively for the
        subexpressions and rebuilds a new expression of the same form
        as [a1]; in these cases, the result follows directly from the
        IH.

        The interesting case is when [a1 = ANum n] for some [n].
        If [n = ANum 0], then
          optimize_0plus (APlus a1 a2) = optimize_0plus a2
        and the IH for [a2] is exactly what we need.  On the other
        hand, if [n = S n'] for some [n'], then again [optimize_0plus]
        simply calls itself recursively, and the result follows from
        the IH.  [] *)
(** 実際的にはCoqの専門家は、[try]を[induction]のようなタクティックと一緒に使うことで、
    多くの似たような「簡単な」場合を一度に処理します。
    これは自然に非形式的な証明に対応します。

    この定理の形式的な証明の構造にマッチする非形式的な証明は次の通りです:

    「定理」: すべての算術式[e]について
       aeval (optimize_0plus e) = aeval e.
    「証明」: [e]についての帰納法を使う。
    [AMinus]と[AMult]の場合は帰納仮定から直接得られる。
    残るのは以下の場合である:

      - ある[n]について [e = ANum n] とする。示すべきことは次の通りである:
          aeval (optimize_0plus (ANum n)) = aeval (ANum n).
        これは[optimize_0plus]の定義からすぐに得られる。

      - ある[e1]と[e2]について [e = APlus e1 e2] とする。
        示すべきことは次の通りである:
          aeval (optimize_0plus (APlus e1 e2))
        = aeval (APlus e1 e2).
        [e1]のとり得る形を考える。そのほとんどの場合、
        [optimize_0plus]は部分式について単に自分自身を再帰的に呼び出し、
        [e1]と同じ形の新しい式を再構成する。
        これらの場合、結果は帰納仮定からすぐに得られる。

        興味深い場合は、ある[n]について [e1 = ANum n] であるときである。
        このとき [n = ANum 0] ならば次が成立する:
          optimize_0plus (APlus e1 e2) = optimize_0plus e2
        そして[e2]についての帰納仮定がまさに求めるものである。
        一方、ある[n']について [n = S n'] ならば、
        [optimize_0plus]はやはり自分自身を再帰的に呼び出し、
        結果は帰納仮定から得られる。 [] *)

(** This proof can still be improved: the first case (for [a = ANum
    n]) is very trivial -- even more trivial than the cases that we
    said simply followed from the IH -- yet we have chosen to write it
    out in full.  It would be better and clearer to drop it and just
    say, at the top, "Most cases are either immediate or direct from
    the IH.  The only interesting case is the one for [APlus]..."  We
    can make the same improvement in our formal proof too.  Here's how
    it looks: *)
(** この証明はさらに改良できます。最初の場合([e = ANum n] のとき)はかなり自明です。
    帰納仮定からすぐに得られると言ったものより自明でしょう。
    それなのに完全に記述しています。
    これを消して、単に最初に「ほとんどの場合、すぐに、あるいは帰納仮定から直接得られる。
    興味深いのは[APlus]の場合だけである...」
    と言った方がより良く、より明快でしょう。
    同じ改良を形式的な証明にも行うことができます。以下のようになります: *)

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  Case "APlus".
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    SCase "a1 = ANum n". destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(* ####################################################### *)
(* *** The [;] Tactical (General Form) *)
(** *** [;] タクティカル (一般的な形式) *)

(* The [;] tactical has a more general than the simple [T;T'] we've
    seen above, which is sometimes also useful.  If [T], [T1], ...,
    [Tn] are tactics, then
      T; [T1 | T2 | ... | Tn]
   is a tactic that first performs [T] and then performs [T1] on the
   first subgoal generated by [T], performs [T2] on the second
   subgoal, etc.

   So [T;T'] is just special notation for the case when all of the
   [Ti]'s are the same tactic; i.e. [T;T'] is just a shorthand for:
      T; [T' | T' | ... | T']
*)
(** 上記で見た、単純な、[T;T']よりも一般的に[;]を使うことが出来、しぱしば有用です。[T],[T1],...,[Tn]がタクティカルならば、
    T; [T1| T2 | ... | Tn]
   はタクティックで、最初に[T]を行ない、
   [T]によって生成された最初のサブゴールに[T1]を行ない、
   二番目のサブゴールに[T2]を行ない、... という処理をします。 
   すべての[Ti]が同じタクティック[T']であるという特別な場合、
      T; [T' | T' | ... | T']
   と書く代わりに [T;T'] と書くだけで済ますことができます。*)

(* ####################################################### *)
(* ** Defining New Tactic Notations *)
(** ** 新しいタクティック記法を定義する *)

(* Coq also provides several ways of "programming" tactic scripts.

      - The [Tactic Notation] idiom illustrated below gives a handy
        way to define "shorthand tactics" that bundle several tactics
        into a single command.

      - For more sophisticated programming, Coq offers a small
        built-in programming language called [Ltac] with primitives
        that can examine and modify the proof state.  The details are
        a bit too complicated to get into here (and it is generally
        agreed that [Ltac] is not the most beautiful part of Coq's
        design!), but they can be found in the reference manual, and
        there are many examples of [Ltac] definitions in the Coq
        standard library that you can use as examples.

      - There is also an OCaml API, which can be used to build tactics
        that access Coq's internal structures at a lower level, but
        this is seldom worth the trouble for ordinary Coq users.

The [Tactic Notation] mechanism is the easiest to come to grips with,
and it offers plenty of power for many purposes.  Here's an example.
*)
(** Coqはまた、タクティックスクリプトを「プログラミングする」いろいろな方法も提供します。

      - [Tactic Notation] コマンドは、「略記法タクティック」("shorthand tactics")
        を定義する簡単な方法を提供します。
       「略記法タクティック」は、呼ばれると、いろいろなタクティックを一度に適用します。

      - より洗練されたプログラミングのために、
        Coqは[Ltac]と呼ばれる小さなビルトインのプログラミング言語と、
        証明の状態を調べたり変更したりするための[Ltac]のプリミティブを提供します。
        その詳細はここで説明するにはちょっと複雑過ぎます
        (しかも、[Ltac]がCoqの設計の一番美しくない部分だというのは共通見解です!)。
        しかし、詳細はリファレンスマニュアルにありますし、
        Coqの標準ライブラリには、読者が参考にできる[Ltac]の定義のたくさんの例があります。

      - Coqの内部構造のより深いレベルにアクセスする新しいタクティックを作ることができる
        OCaml API も存在します。しかしこれは、普通のCoqユーザにとっては、
        苦労が報われることはほとんどありません。

[Tactic Notation] 機構は取り組むのに一番簡単で、多くの目的に十分なパワーを発揮します。
例を挙げます。
*)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(* This defines a new tactical called [simpl_and_try] which
    takes one tactic [c] as an argument, and is defined to be
    equivalent to the tactic [simpl; try c].  For example, writing
    "[simpl_and_try reflexivity.]" in a proof would be the same as
    writing "[simpl; try reflexivity.]" *)
(** これは1つのタクティック[c]を引数としてとる[simpl_and_try]
    という新しいタクティカルを定義しています。
    そして、タクティック [simpl; try c] と同値なものとして定義されます。
    例えば、証明内で"[simpl_and_try reflexivity.]"と書くことは
    "[simpl; try reflexivity.]"と書くことと同じでしょう。 *)

(* The next subsection gives a more sophisticated use of this
    feature... *)
(** 次のサブセクションでは、この機構のより洗練された使い方を見ます... *)

(* ####################################################### *)
(* *** Bulletproofing Case Analyses *)
(** *** 場合分けを万全にする *)

(** Being able to deal with most of the cases of an [induction]
    or [destruct] all at the same time is very convenient, but it can
    also be a little confusing.  One problem that often comes up is
    that _maintaining_ proofs written in this style can be difficult.
    For example, suppose that, later, we extended the definition of
    [aexp] with another constructor that also required a special
    argument.  The above proof might break because Coq generated the
    subgoals for this constructor before the one for [APlus], so that,
    at the point when we start working on the [APlus] case, Coq is
    actually expecting the argument for a completely different
    constructor.  What we'd like is to get a sensible error message
    saying "I was expecting the [AFoo] case at this point, but the
    proof script is talking about [APlus]."  Here's a nice trick (due
    to Aaron Bohannon) that smoothly achieves this. *)
(** [induction]や[destruct]で、ほとんどの場合を一度に扱えるのはとても便利ですが、
    またちょっと混乱もします。よく起こる問題は、
    このスタイルで記述された証明をメンテナンスすることが難しいということです。
    例えば、後で、[aexp]の定義を拡張して、
    やはり特別な引数をとるコンストラクタを追加したとします。
    このとき上述の証明は成立しなくなっているでしょう。
    なぜなら、
    Coqは[APlus]についてのサブゴールの前にこのコンストラクタに対応するサブゴールを生成し、
    その結果、[APlus]の場合に取りかかる時には、
    Coqは実際にはまったく別のコンストラクタを待っていることになるからです。
    ここで欲しいのは、「この場所で[AFoo]の場合を期待していましたが、
    証明スクリプトは[APlus]について話しています。」という賢いエラーメッセージです。
    以下は、これを難なく可能にするちょっとしたトリックです。 *)

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(* ([Case_aux] implements the common functionality of [Case],
    [SCase], [SSCase], etc.  For example, [Case "foo"] is defined as
    [Case_aux Case "foo".) *)
(** ([Case_aux]は[Case]、[SCase]、[SSCase]等の共通機能を実装します。
    例えば、[Case "foo"]は [Case_aux Case "foo"] と定義されます。) *)

(* For example, if [a] is a variable of type [aexp], then doing
      aexp_cases (induction a) Case
    will perform an induction on [a] (the same as if we had just typed
    [induction a]) and _also_ add a [Case] tag to each subgoal
    generated by the [induction], labeling which constructor it comes
    from.  For example, here is yet another proof of
    [optimize_0plus_sound], using [aexp_cases]: *)
(** 例えば、[a]が型[aexp]の変数のとき、
      aexp_cases (induction e) Case
    と書くと[a]についての帰納法を実行し(単に [induction e] と書いたのと同じです)、
    そして、「その上に」、[induction]によって生成されたそれぞれのサブゴールに[Case]
    タグを付加します。このタグは、そのサブゴールがどのコンストラクタから来たかのラベルです。
    例えば、[aexp_cases]を使った、[optimize_0plus_sound]のさらに別証です: *)

tsi
  intros a.
  aexp_cases (induction a) Case;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  (* At this point, there is already an ["APlus"] case name
     in the context.  The [Case "APlus"] here in the proof
     text has the effect of a sanity check: if the "Case"
     string in the context is anything _other_ than ["APlus"]
     (for example, because we added a clause to the definition
     of [aexp] and forgot to change the proof) we'll get a
     helpful error at this point telling us that this is now
     the wrong case. *)
  (* この時点で、すでに["APlus"]の名前はコンテキストに導入されています。
  [Case "Aplus"]のテキストは証明のこの時点で健全性のチェックの効果を持ちます。
  ：もし、コンテキスト中の"Case"文字列が["APlus"]ではない他のものである場合、(例えば、[aexp]に後から追加されていたにも係らず、証明の変更を忘れていたなど)ここで場合分けが間違っていることに気が付くことが出来ます。*)
  Case "APlus".
    aexp_cases (destruct a1) SCase;
      try (simpl; simpl in IHa1;
           rewrite IHa1; rewrite IHa2; reflexivity).
    SCase "ANum". destruct n;
      simpl; rewrite IHa2; reflexivity.  Qed.

(*  **** Exercise: 3 stars (optimize_0plus_b) *)
(*  Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)
(** **** 練習問題: ★★★ (optimize_0plus_b) *)
(** [optimize_0plus]の変換が[aexp]の値を変えないことから、
    [bexp]の値を変えずに、[bexp]に現れる[aexp]をすべて変換するために
    [optimize_0plus]が適用できるべきでしょう。
    [bexp]についてこの変換をする関数を記述しなさい。そして、
    それが健全であることを証明しなさい。
    ここまで見てきたタクティカルを使って証明を可能な限りエレガントにしなさい。*)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  (* FILL IN HERE *) admit.


Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 4 stars, optional (optimizer) *)
(*  _Design exercise_: The optimization implemented by our
    [optimize_0plus] function is only one of many imaginable
    optimizations on arithmetic and boolean expressions.  Write a more
    sophisticated optimizer and prove it correct.

(* FILL IN HERE *)
*)
(** **** 練習問題: ★★★★, optional (optimizer) *)
(** 設計練習: 定義した[optimize_0plus]関数で実装された最適化は、
    算術式やブール式に対して考えられるいろいろな最適化の単なる1つに過ぎません。
    より洗練された最適化関数を記述し、その正しさを証明しなさい。

(* FILL IN HERE *)
*)
(** [] *)

(* ####################################################### *)
(* ** The [omega] Tactic *)
(** ** [omega]タクティック *)

(* The [omega] tactic implements a decision procedure for a subset of
    first-order logic called _Presburger arithmetic_.  It is based on
    the Omega algorithm invented in 1992 by William Pugh.

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and inequality ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or tell you that
    it is actually false. *)
(** [omega]タクティックは「プレスバーガー算術」
    (_Presburger arithmetic_、「プレスブルガー算術」とも)
    と呼ばれる一階述語論理のサブセットの決定手続き(decision procedure)を実装します。
    William Pugh が1992年に発明したOmegaアルゴリズムに基いています。

    ゴールが以下の要素から構成された全称限量された論理式とします。以下の要素とは:

      - 数値定数、加算([+]と[S])、減算([-]と[pred])、
        定数の積算(これがプレスバーガー算術である条件です)、

      - 等式([=]と[<>])および不等式([<=])、

      - 論理演算子[/\], [\/], [~], [->]

    です。このとき、[omega]を呼ぶと、ゴールを解くか、
    そのゴールが偽であると告げるか、いずれかになります。 *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(** Liebniz wrote, "It is unworthy of excellent men to lose
    hours like slaves in the labor of calculation which could be
    relegated to anyone else if machines were used."  We recommend
    using the omega tactic whenever possible. *)
(** "優れた人間が奴隷に格下げになるような機械でも出来るような誰でも出来る計算に従事して時間を無駄にすることほど勿体ないことはない。"とライプニッツは書いています。*)
(* ####################################################### *)
(* ** A Few More Handy Tactics *)
(** ** 便利なタクティックをさらにいくつか *)

(** Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Delete hypothesis [H] from the context.

     - [subst x]: Find an assumption [x = e] or [e = x] in the
       context, replace [x] with [e] throughout the context and
       current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x].

     - [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, behave just like
       [apply H].

     - [contradiction]: Try to find a hypothesis [H] in the current
       context that is logically equivalent to [False].  If one is
       found, solve the goal.

     - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c]. *)

(** 最後に、役に立ちそうないろいろなタクティックをいくつか紹介します。

     - [clear H]: 仮定[H]をコンテキストから消去します。

     - [subst x]: コンテキストから仮定 [x = e] または [e = x] を発見し、
       [x]をコンテキストおよび現在のゴールのすべての場所で[e]に置き換え、
       この仮定を消去します。

     - [subst]: [x = e] および [e = x] の形のすべての仮定を置換します。

     - [rename... into...]: 証明コンテキストの仮定の名前を変更します。
       例えば、コンテキストが[x]という名前の変数を含んでいるとき、
       [rename x into y] は、すべての[x]の出現を[y]に変えます。

     - [assumption]: ゴールにちょうどマッチする仮定[H]をコンテキストから探そうとします。
       発見されたときは [apply H] と同様に振る舞います。

     - [contradiction]: [False]と同値の仮定[H]をコンテキストから探そうとします。
       発見されたときはゴールを解きます。

     - [constructor]: 現在のゴールを解くのに使えるコンストラクタ[c]を
       (現在の環境の[Inductive]による定義から)探そうとします。
       発見されたときは [apply c] と同様に振る舞います。 *)

(* We'll see many examples of these in the proofs below. *)
(** 以降の証明でこれらのたくさんの例を見るでしょう。 *)

(* ####################################################### *)
(* * Evaluation as a Relation *)
(** * 関係としての評価 *)

(* We have presented [aeval] and [beval] as functions defined by
    [Fixpoints].  Another way to think about evaluation -- one that we
    will see is often more flexible -- is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following one for arithmetic
    expressions... *)
(** [aeval]と[beval]を[Fixpoints]によって定義された関数として示しました。
    評価について考える別の方法は、それを式と値との間の関係(_relation_)と見ることです。

    この考えに立つと、
    算術式についてCoqの[Inductive]による以下の定義が自然に出てきます... *)


Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum  : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(** As is often the case with relations, we'll find it
    convenient to define infix notation for [aevalR].  We'll write [e
    || n] to mean that arithmetic expression [e] evaluates to value
    [n].  (This notation is one place where the limitation to ASCII
    symbols becomes a little bothersome.  The standard notation for
    the evaluation relation is a double down-arrow.  We'll typeset it
    like this in the HTML version of the notes and use a double
    vertical bar as the closest approximation in [.v] files.)  *)
(** 関係についてよく行うように、[aevalR]の中置記法を定義するのが便利です。
    算術式[e]が値[n]に評価されることを [e || n] と書きます。
    (この記法は煩わしいascii記号の限界の1つです。評価関係の標準記法は二重の下向き矢印です。
    HTML版ではそのようにタイプセットしますが、ascii の
    .v ファイルでは可能な近似として縦棒二本を使います。) *)

Notation "e '||' n" := (aevalR e n) : type_scope.

End aevalR_first_try.

(* In fact, Coq provides a way to use this notation in the definition
    of [aevalR] itself.  This avoids situations where we're working on
    a proof involving statements in the form [e || n] but we have to
    refer back to a definition written using the form [aevalR e n].

    We do this by first "reserving" the notation, then giving the
    definition together with a declaration of what the notation
    means. *)
(** 実際は、Coqでは[aevalR]自身の定義中でこの記法を使うことができます。
    これにより、[e || n] の形の主張を含む証明で、[aevalR e n] 
    という形の定義に戻らなければならない状況にならずに済みます。

    このためには、最初に記法を「予約」し、
    それから定義と、記法が何を意味するかの宣言とを一緒に行います。*)

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

  where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
  | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

(* ####################################################### *)
(* ** Inference Rule Notation *)
(** ** 推論規則記法 *)

(* In informal discussions, it is convenient write the rules for
    [aevalR] and similar relations in the more readable graphical form
    of _inference rules_, where the premises above the line justify
    the conclusion below the line (we have already seen them in the
    Prop chapter). *)
(** 非形式的な議論には、[aevalR]や似たような関係についての規則を、
    推論規則(_inference rules_)と呼ばれる、
    より読みやすいグラフィカルな形で書くのが便利です。
    推論規則は、横線の上の前提から、横線の下の結論を導出できることを述べます。
	( すでに、Propの章で見ていると思いますが。) *)

(* For example, the constructor [E_APlus]...
      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)
    ...would be written like this as an inference rule:
                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2
*)
(** 例えば、コンストラクタ[E_APlus]...
      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)
    ...は推論規則として次のように書けるでしょう:
                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2
*)
(* Formally, there is nothing very deep about inference rules:
    they are just implications.  You can read the rule name on the
    right as the name of the constructor and read each of the
    linebreaks between the premises above the line and the line itself
    as [->].  All the variables mentioned in the rule ([e1], [n1],
    etc.) are implicitly bound by universal quantifiers at the
    beginning. (Such variables are often called _metavariables_ to
    distinguish them from the variables of the language we are
    defining.  At the moment, our arithmetic expressions don't include
    variables, but we'll soon be adding them.)  The whole collection
    of rules is understood as being wrapped in an [Inductive]
    declaration (informally, this is either elided or else indicated
    by saying something like "Let [aevalR] be the smallest relation
    closed under the following rules..."). *)
(** 形式的には、推論規則について何も深いものはありません。単なる含意です。
    右に書かれた規則名はコンストラクタで、
    横線より上の前提の間の各改行と横線自体は[->]と読むことができます。
    規則で言及されるすべての変数([e1]、[n1]等)
    は暗黙のうちに冒頭で全称限量子に束縛されています。
    規則の集合全体は[Inductive]宣言で囲われていると理解されます
    (これは完全に暗黙のまま置かれるか、非形式的に
    「[aevalR]は以下の規則について閉じた最小の関係とします...」
    などと述べられるかします)。 *)
(* For example, [||] is the smallest relation closed under these
    rules:
                             -----------                               (E_ANum)
                             ANum n || n

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2

                               e1 || n1
                               e2 || n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 || n1-n2

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 || n1*n2
*)
(** 例えば、[||]は以下の規則について閉じた最小の関係です:
                             -----------                               (E_ANum)
                             ANum n || n

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2

                               e1 || n1
                               e2 || n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 || n1-n2

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 || n1*n2
*)

(* ####################################################### *)
(* ** Equivalence of the Definitions *)
(** ** 等価性の定義 *)
(* It is straightforward to prove that the relational and functional
    definitions of evaluation agree on all possible arithmetic
    expressions... *)
(** 関係による定義と、関数による定義とが、評価が有り得る全ての算術式において一致することの直接的な証明です。*)
Theorem aeval_iff_aevalR : forall a n,
  (a || n) <-> aeval a = n.
Proof.
 split.
 Case "->".
   intros H.
   aevalR_cases (induction H) SCase; simpl.
   SCase "E_ANum".
     reflexivity.
   SCase "E_APlus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMinus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMult".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 Case "<-".
   generalize dependent n.
   aexp_cases (induction a) SCase;
      simpl; intros; subst.
   SCase "ANum".
     apply E_ANum.
   SCase "APlus".
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMinus".
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMult".
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

(* Note: if you're reading the HTML file, you'll see an empty square box instead
of a proof for this theorem.  
You can click on this box to "unfold" the text to see the proof.
Click on the unfolded to text to "fold" it back up to a box. We'll be using
this style frequently from now on to help keep the HTML easier to read.
The full proofs always appear in the .v files. *)
(** 注意： もし、HTMLファイルを読んでいるならば、この定理の証明の代わりに白抜きの四角形が表示されているかもしれません。
その場合は、その四角形をクリックすることで、折り畳まれた証明を"unfold"して見てください。展開された証明はクリックすると折り畳まれます。
これから、HTMLの読み易さのためにしばしばこの形式を用います。完全な証明は常に、.vファイルにあります *)

(* We can make the proof quite a bit shorter by making more
    use of tacticals... *)
(** タクティカルを使用することで、証明はもっと全然短かくすることができます。*) 
Theorem aeval_iff_aevalR' : forall a n,
  (a || n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  Case "->".
    intros H; induction H; subst; reflexivity.
  Case "<-".
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(* **** Exercise: 3 stars  (bevalR) *)
(** **** 練習問題: ★★★  (bevalR) *)
(* Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)
(** 関係[bevalR]を[aevalR]と同じ形式で書きなさい。そしてそれが、[beval]と等価であることを証明しなさい。 *)
(* 
Inductive bevalR:
(* FILL IN HERE *)
*)
(** [] *)
End AExp.

(* ####################################################### *)
(* ** Computational vs. Relational Definitions *)
(** ** 関数による定義 vs. 関係による定義 *)
(** For the definitions of evaluation for arithmetic and boolean
    expressions, the choice of whether to use functional or relational
    definitions is mainly a matter of taste.  In general, Coq has
    somewhat better support for working with relations.  On the other
    hand, in some sense function definitions carry more information,
    because functions are necessarily deterministic and defined on all
    arguments; for a relation we have to show these properties
    explicitly if we need them. Functions also take advantage of Coq's
    computations mechanism.

    However, there are circumstances where relational definitions of
    evaluation are preferable to functional ones.  *)

(** 算術式とブール式の評価の定義について、関数を使うか関係を使うかはほとんど趣味の問題です。
一般に、Coqは関係を扱う方がいくらかサポートが厚いです。 特に帰納法についてはそうです。
一方、 ある意味で関数による定義の方がより多くの情報を持っています。 
なぜなら、関数は決定的でなければならず、 またすべての引数について定義されていなければなりません。 
関数については、必要ならばこれらの性質を明示的に示さなければなりません。

しかしながら、評価の定義として、 関係による定義が関数による定義よりはるかに望ましい状況があります。*) 

Module aevalR_division.

(* For example, suppose that we wanted to extend the arithmetic
    operations by considering also a division operation:*)
(** たとえば、算術の操作を割り算を加えて拡張しようと思ったとしましょう *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.   (* <--- new *)

(* Extending the definition of [aeval] to handle this new operation
    would not be straightforward (what should we return as the result
    of [ADiv (ANum 5) (ANum 0)]?).  But extending [aevalR] is
    straightforward. *)
(** この新しい操作を扱えるように[aeval]の定義を拡張することは簡単には行きません。([ADiv (ANum 5) (ANum 0)]の結果何を返すべきでしょうか？)
しかし、[aevalR]を拡張することは簡単です。*)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)
  | E_ADiv :  forall (a1 a2: aexp) (n1 n2 n3: nat),
      (a1 || n1) -> (a2 || n2) -> (mult n2 n3 = n1) -> (ADiv a1 a2) || n3

where "a '||' n" := (aevalR a n) : type_scope.

End aevalR_division.
Module aevalR_extended.


(*  Suppose, instead, that we want to extend the arithmetic operations
    by a nondeterministic number generator [any]:*)
(** そのかわりに、非決定的な数の生成元である[any]を加えて、計算操作を拡張したいと思ったとします。*)
Inductive aexp : Type :=
  | AAny  : aexp                   (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

(* Again, extending [aeval] would be tricky (because evaluation is
    _not_ a deterministic function from expressions to numbers), but
    extending [aevalR] is no problem: *)
(** もう一度言いますが、[aeval]を拡張することはトリッキーなものになります。(なぜなら評価は、式から数への決定的な関数ではない(_not_)からです。)
しかし [aevalR]ならば問題ありません。
*)
Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny || n                 (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)

where "a '||' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(*  * Expressions With Variables *)
(** * 変数を持つ式 *)

(** Let's turn our attention back to defining Imp.  The next thing we
    need to do is to enrich our arithmetic and boolean expressions
    with variables.  To keep things simple, we'll assume that all
    variables are global and that they only hold numbers. *)
(** Impの定義に戻ることにしましょう。次にしなければならないことは、
    算術式とブール式に変数を拡張することです。
    話を単純にするため、すべての変数はグローバルで、数値だけを持つとしましょう。 *)

(* ##################################################### *)
(*  ** Identifiers *)
(** ** 識別子 *)

(*  To begin, we'll need to formalize _identifiers_ such as program
    variables.  We could use strings for this -- or, in a real
    compiler, fancier structures like pointers into a symbol table.
    But for simplicity let's just use natural numbers as identifiers. *)

(*  (We hide this section in a module because these definitions are
    actually in [SfLib], but we want to repeat them here so that we
    can explain them.) *)
(** 始めに、プログラム変数などの識別子(_identifiers_)を形式化しなければなりません。
    このために文字列を使うこともできるでしょうし、(実際のコンパイラでは)
    シンボルテーブルへのポインタのようなある種の特別な構造を使うこともできるでしょう。
    しかし、簡単にするため、識別子に単に自然数を使います。

    (このセクションをモジュールに隠します。それは、これらの定義が実際には[SfLib_J.v]
    にあるからです。しかし説明のためにここで繰り返します。) *)

Module Id. 

(*  We define a new inductive datatype [Id] so that we won't confuse
    identifiers and numbers.  We use [sumbool] to define a computable
    equality operator on [Id]. *)
(** 新しいデータタイプ[Id]を定義して、識別子と数値を混乱しないようにします。 
   [Id]についての計算可能な同値演算子を定義するために、[sumbool]を使用します。*)

Inductive id : Type :=
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined. 

(* The following lemmas will be useful for rewriting terms involving [eq_id_dec]. *)
(** 次の補題は、[eq_id_dec]を含む式を書き直すのに役立ちます。 *)

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x). 
  Case "x = x". 
    reflexivity.
  Case "x <> x (impossible)". 
    apply ex_falso_quodlibet; apply n; reflexivity. Qed.

(** **** Exercise: 1 star, optional (neq_id) *)
Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


End Id. 

(* ####################################################### *)
(*  ** States *)
(** ** 状態 *)

(** A _state_ represents the current values of all the variables at
    some point in the execution of a program. *)
(** 状態(_state_)はプログラムの実行のある時点のすべての変数の現在値を表します。 *)
(** For simplicity (to avoid dealing with partial functions), we
    let the state be defined for _all_ variables, even though any
    given program is only going to mention a finite number of them. *)
(** 簡単にするため(部分関数を扱うのを避けるため)、
    どのようなプログラムも有限個の変数しか使わないにもかかわらず、
    状態はすべての変数について値を定義しているものとします。 *)

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

(** For proofs involving states, we'll need several simple properties
    of [update]. *)
(** 状態を含む証明のために、[update]についての単純な性質が必要です。 *)

(*  **** Exercise: 1 star (update_eq) *)
(** **** 練習問題: ★, optional (update_eq) *)
Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star (update_neq) *)
(** **** 練習問題: ★, optional (update_neq) *)
Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->                        
  (update st x2 n) x1 = (st x1).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star (update_example) *)
(** **** 練習問題: ★, optional (update_example) *)
(** Before starting to play with tactics, make sure you understand
    exactly what the theorem is saying! *)
(** タクティックを使って遊び始める前に、
    定理が言っていることを正確に理解していることを確認しなさい! *)

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (update_shadow) *)
Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
   (update  (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (update_same) *)
Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (update_permute) *)
Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 -> 
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################### *)
(*  ** Syntax  *)
(** ** 構文  *)

(*  We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)
(** 前に定義した算術式に、単にもう1つコンストラクタを追加することで変数を追加できます: *)


Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)
(** 読み易い例を作りやすくするため、幾つかの変数名を定義しておきましょう *)
Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(** (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in this part of
    the course, this overloading should not cause confusion.) *)
(** (プログラム変数のこの慣習([X], [Y], [Z])は、
    型に大文字の記号を使うという以前の使用法と衝突します。
    コースのこの部分では多相性を多用はしないので、このことが混乱を招くことはないはずです。) *)

(** The definition of [bexp]s is the same as before (using the new
    [aexp]s): *)
(** [bexp]の定義は前と同じです(ただし新しい[aexp]を使います): *)

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

(* ################################################### *)
(*  ** Evaluation  *)
(** ** 評価  *)

(** The arith and boolean evaluators can be extended to handle
    variables in the obvious way: *)
(** 算術とブールの評価器は、自明な方法で変数を扱うように拡張されます: *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                        (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

(* ####################################################### *)
(*  * Commands *)
(** * コマンド *)

(*  Now we are ready define the syntax and behavior of Imp
    _commands_ (often called _statements_). *)
(** さて、Imp コマンド (または主張) の構文と挙動を定義する準備が出来ました *)

(* ################################################### *)
(*  ** Syntax *)
(** ** 構文 *)

(** Informally, commands [c] are described by the following BNF
    grammar:
     c ::= SKIP
         | x ::= a
         | c ; c
         | WHILE b DO c END
         | IFB b THEN c ELSE c FI
    For example, here's the factorial function in Imp.
     Z ::= X;
     Y ::= 1;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;
       Z ::= Z - 1
     END
   When this command terminates, the variable [Y] will contain the
   factorial of the initial value of [X].
*)
(** 非形式的には、コマンドは以下の BNF で表現されます。
    構文:
     c  ::= 'SKIP'
         | X '::=' aexp
         | c ';' c
         | 'WHILE' bexp 'DO' c 'END'
         | 'IFB' bexp 'THEN' c 'ELSE' c 'FI'
    例えば、Imp における階乗関数は以下のようになります。
     Z ::= X;
     Y ::= 1;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;
       Z ::= Z - 1
     END
   このコマンドが終わったとき、変数 [Y] は変数 [X] の階乗の値を持つでしょう。
*)

(*  Here is the formal definition of the syntax of commands: *)
(** 以下に、コマンドの構文の形式的な定義を示します。 *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

(*  As usual, we can use a few [Notation] declarations to make things
    more readable.  We need to be a bit careful to avoid conflicts
    with Coq's built-in notations, so we'll keep this light -- in
    particular, we won't introduce any notations for [aexps] and
    [bexps] to avoid confusion with the numerical and boolean
    operators we've already defined.  We use the keyword [IFB] for
    conditionals instead of [IF], for similar reasons. *)
(** いつものとおり、より読みやすいよう、いくつかの [Notation] 宣言が使えます。
    しかし、Coq の組み込みの表記と衝突しないよう、少し気をつける必要があります 
    (手軽さを維持しつつ！)。
    特に、[aexp] と [bexp] については、
    すでに定義した数値演算子やブール演算子との混同を避けるために、
    新しい表記は導入しません。
    (同様の理由により、条件文に対しては通常使われる [IF] の代わりに 
    [IFB] というキーワードを使います。) *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(*  For example, here is the factorial function again, written as a
    formal definition to Coq: *)
(** 例えば先の階乗関数を Coq での形式的な定義として記述し直すと、
    以下のようになります。*)

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

(* ####################################################### *)
(*  ** Examples *)
(** ** 例 *)

(*  Assignment: *)
(** 割り当て: *)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

(*  Loops: *)
(** ループ: *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

(*  An infinite loop: *)
(** 無限ループ: *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(* ################################################################ *)
(*  * Evaluation *)
(** ** 評価  *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [WHILE] loops don't necessarily terminate makes defining
    an evaluation function tricky... *)
(** 次に、Imp のコマンドの実行が何を意味するかを定義する必要があります。
    [WHILE] ループは、必ずしも終了しないという事実が、これを少々扱いにくいものにしています ... *)

(* #################################### *)
(*  ** Evaluation as a Function (Failed Attempt) *)
(** ** 評価関数(失敗バージョン) *)

(*  Here's an attempt at defining an evaluation function for commands,
    omitting the [WHILE] case. *)
(** 以下は [WHILE] 以外のコマンドの評価関数を得ようとした、最初の試みです。 *)

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        update st x (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.

(* In a traditional functional programming language like ML or
    Haskell we could write the [WHILE] case as follows:
<<
  Fixpoint ceval_fun (st : state) (c : com) : state :=
    match c with
      ...
      | WHILE b DO c END =>
          if (beval st b1)
            then ceval_fun st (c1; WHILE b DO c END)
            else st
    end.
>>
    Coq doesn't accept such a definition ("Error: Cannot guess
    decreasing argument of fix") because the function we want to
    define is not guaranteed to terminate. Indeed, it doesn't always
    terminate: for example, the full version of the [ceval_fun]
    function applied to the [loop] program above would never
    terminate. Since Coq is not just a functional programming
    language, but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is
    an (invalid!) Coq program showing what would go wrong if Coq
    allowed non-terminating recursive functions:
<<
     Fixpoint loop_false (n : nat) : False := loop_false n.
>>
    That is, propositions like [False] would become provable
    (e.g. [loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs, the full version
    of [ceval_fun] cannot be written in Coq -- at least not without
    additional tricks (see chapter [ImpCEvalFun] if curious). *)
(** MLやHaskellといった伝統的な関数型プログラム言語において、[WHILE]は以下のように書けます。 
<<
  Fixpoint ceval_fun (st : state) (c : com) : state :=
    match c with
      ...
      | WHILE b DO c END =>
          if (beval st b1)
            then ceval_fun st (c1; WHILE b DO c END)
            else st
    end.
>>
   Coqはそのような定義を受け入れてはくれません。("Error: Cannot gess decreasing argument of fix" というエラーになります。)
   我々が定義したい関数は、終了を保証しないからです。実際に必ずしも終了しません：
   たとえば、[ceval_fun]の完全なバージョンは、上記の[loop]プログラムを適用した場合、決して終了しません。
   Coqは関数型プログラミング言語であるだけではなく、一貫した論理そのものであり、終了しない可能性のある関数は排除されなければならないのです。  
   ここに、もしCoqが終了しない帰納的な関数を許す場合に、どんなおかしなことが起こるかを示す(間違った)Coqのプログラムをあげておきます。
<<
     Fixpoint loop_false (n : nat) : False := loop_false n.
>>
  すなわち、[False]のような命題が証明可能になってしまします。。(例として、[loop_false 0]は[False]であることの証明である。というように。)
  Coqの論理的一貫性にとってやっかいなことです。
  
  それゆえ、すべての入力について終了が保証出来ないので、[ceval_fun]は決してCoqで書くことが出来ないのです。 -- 少なくとも追加のトリックなしには。
  (気になるなら、[ImpCEvalFun]の章を見てください。)
*)

(* #################################### *)
(*  ** Evaluation as a Relation *)
(** * 関係としての評価 *)

(* Here's a better way: we define [ceval] as a _relation_ rather than
    a _function_ -- i.e., we define it in [Prop] instead of [Type], as
    we did for [aevalR] above. *)
(** ここに改善策があります: [ceval] を関数ではなく関係 (relation) として定義しましょう。
    つまり、上の aevalR と bevalR と同様に Type ではなく Prop で定義しましょう。 *)

(*  This is an important change.  Besides freeing us from the awkward
    workarounds that would be needed to define evaluation as a
    function, it gives us a lot more flexibility in the definition.
    For example, if we added concurrency features to the language,
    we'd want the definition of evaluation to be non-deterministic --
    i.e., not only would it not be total, it would not even be a
    partial function! *)
(** これは重要な変更です。 ステップ指数をすべての場所で引き回す馬鹿馬鹿しさから解放してくれるのに加え、 
    定義での柔軟性を与えてくれます。 例えば、もし言語に並行性の要素を導入したら、評価の定義を非決定的に書きたくなるでしょう。
    つまり、その関数は全関数でないだけでなく、部分関数ですらないかも知れません！ *)


(*  We'll use the notation [c / st || st'] for our [ceval] relation:
    [c / st || st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)
(** ceavl 関係に対する表記として c / st ⇓ st' を使います。
    正確に言うと、c / st || st' と書いたらプログラム c を初期状態 st で評価すると、 
    その結果は最終状態 st' になる、ということを意味します。 これは「c は状態 st を st' に持っていく」とも言えます。 
                           ----------------                            (E_Skip)
                           SKIP / st || st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   x := a1 / st || (update st x n)

                           c1 / st || st'
                          c2 / st' || st''
                         -------------------                            (E_Seq)
                         c1;;c2 / st || st''

                          beval st b1 = true
                           c1 / st || st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                           c2 / st || st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                    ------------------------------                 (E_WhileEnd)
                    WHILE b DO c END / st || st

                          beval st b1 = true
                           c / st || st'
                  WHILE b DO c END / st' || st''
                  ---------------------------------               (E_WhileLoop)
                    WHILE b DO c END / st || st''
*)

(*  Here is the formal definition.  (Make sure you understand
    how it corresponds to the inference rules.) *)
(** 以下に形式的な定義を挙げます。 (上の推論規則とどのように対応するか、確認しておきましょう。)  *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st || (update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

(*  The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)
(** 評価を関数ではなく関係として定義することのコストは、 あるプログラムを実行した結果がとある状態になる、 
    というのを Coq の計算機構にやってもらうだけではなく、 その「証明」を構築する必要がある、ということです。 *)
Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   || (update (update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(* **** Exercise: 2 stars (ceval_example2) *)
(** **** 練習問題: ★★(ceval_example2) *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, advanced (pup_to_n) *)
(** **** 練習問題: ★★★, advanced (pup_to_n) *)
(* Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for X = 2
   (this latter part is trickier than you might expect). *)
(** [1]からXまでの数を合計([1 + 2 + ... + X]を含みます)して、変数Yに結果を格納するImpプログラムを書きなさい。
    このプログラムがX = 2のときに意図したとおりに動くことを証明しなさい。
    後の問題はあなたが考えているよりもトリッキーかもしれません*)
*)
Definition pup_to_n : com :=
  (* FILL IN HERE *) admit.

Theorem pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(** ** Determinism of Evaluation *)
(** ** 実行の決定論 *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it allows us to escape from the
    artificial requirement (imposed by Coq's restrictions on
    [Fixpoint] definitions) that evaluation should be a total
    function.  But it also raises a question: Is the second definition
    of evaluation actually a partial function?  That is, is it
    possible that, beginning from the same state [st], we could
    evaluate some command [c] in different ways to reach two different
    output states [st'] and [st'']?

    In fact, this cannot happen: [ceval] is a partial function.
    Here's the proof: *)
(** 評価の定義を計算的なものから関係的なものに変更するのは、
    評価は全関数であるべきという (Fixpoint の定義における 
    Coq の制限によって課せられる) 不自然な要求から逃れさせてくれる良い変更です。
    しかしこれは、2 つ目の評価の定義は本当に部分関数なのか？という疑問ももたらします。
    つまり、同じ状態 [st] から始めて、あるコマンド [c] を違った方法で評価し、
    2 つの異なる出力状態 [st'] と [st''] に至るのは可能か？ということです。

   実際には、こうなることはありません。評価関係 [ceval] は部分関数です。
   以下に証明を挙げます: *)

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
           intros st2 E2; inversion E2; subst.
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd".
    SCase "b1 evaluates to false".
      reflexivity.
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to true".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(* ####################################################### *)
(*  * Reasoning About Imp Programs *)
(** * Imp プログラムの検証 *)

(** We'll get much deeper into systematic techniques for reasoning
    about Imp programs in the following chapters, but we can do quite
    a bit just working with the bare definitions. *)
(** ここから Imp におけるプログラムの検証に対する系統だったテクニックに深く関わっていきます。
    しかし、その多くはむき出しの (もとの) 定義を扱うだけで出来ます。
    この章では、いくつかの例を探します。*)

(* This section explores some examples. *)
(** このセクションで、いくつか例を見ていきましょう *)
Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st || st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  (* Inverting Heval essentially forces Coq to expand one
     step of the ceval computation - in this case revealing
     that st' must be st extended with the new value of X,
     since plus2 is an assignment *)
  (* Hevalをinvertすることは本質的には、Coqにcevalの計算の一ステップを展開させることと同じです。
     このケースにおいては、plus2は代入であるため、st'がXの新しい値でstに拡大されることが明らかになります。*)
  inversion Heval. subst. clear Heval. simpl.
  apply update_eq.  Qed.

(*  **** Exercise: 3 stars (XtimesYinZ_spec) *)
(** **** 練習問題: ★★★, recommended (XtimesYinZ_spec) *)
(*  State and prove a specification of [XtimesYinZ]. *)
(** XtimesYinZ の Imp プログラムの仕様を書いて証明しなさい。*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (loop_never_stops) *)
Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
    (* Proceed by induction on the assumed derivation showing that
     [loopdef] terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with
     [inversion]). *)
    (** [loopdef]が終了することを示す仮定の導出についての帰納法で進めなさい。
        ほとんどのケースにおいては、ただちに矛盾が導かれ(て[inversion]を使った1stepで解決され)ます *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars (no_whilesR) *)
(** **** 練習問題: ★★, optional (no_whilesR) *)
(*  Consider the definition of the [no_whiles] property below: *)
(** 下に定義されている[no_whiles]の特徴について考えましょう *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ;; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

(*i  This property yields [true] just on programs that
    have no while loops.  Using [Inductive], write a property
    [no_whilesR] such that [no_whilesR c] is provable exactly when [c]
    is a program with no while loops.  Then prove its equivalence
    with [no_whiles]. *)
(** 性質 [no_whiles] はプログラムが while ループを含まない場合 [true] を返します。
    Inductive を使って [c] が while ループのないプログラムのとき証明可能な性質 [no_whilesR] を書きなさい。
    さらに、それが [no_whiles] と等価であることを示しなさい。*)

Inductive no_whilesR: com -> Prop :=
 (* FILL IN HERE *)
  .

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 4 stars (no_whiles_terminating) *)
(** **** 練習問題: ★★★★, optional (no_whiles_terminating) *)
(*  Imp programs that don't involve while loops always terminate.
    State and prove a theorem that says this. *)
(** while ループを含まない Imp プログラムは必ず停止します。
    これを定理として記述し、証明しなさい。*)
(*  (Use either [no_whiles] or [no_whilesR], as you prefer.) *)
(** ([no_whiles] と [no_whilesR] のどちらでも好きなほうを使いなさい。) *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** * Additional Exercises *)

(*  **** Exercise: 3 stars (stack_compiler) *)
(** **** 練習問題: ★★★, recommended (stack_compiler) *)
(*  HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a stack. For instance, the expression
<<
   (2*3)+(3*(4-2))
>>
   would be entered as
<<
   2 3 * 3 4 2 - * +
>>
   and evaluated like this:
<<
  []            |    2 3 * 3 4 2 - * +
  [2]           |    3 * 3 4 2 - * +
  [3, 2]        |    * 3 4 2 - * +
  [6]           |    3 4 2 - * +
  [3, 6]        |    4 2 - * +
  [4, 3, 6]     |    2 - * +
  [2, 4, 3, 6]  |    - * +
  [2, 3, 6]     |    * +
  [6, 6]        |    +
  [12]          |
>>

  The task of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply. *)
(** HP の電卓、Forth や Postscript などのプログラミング言語、
   および Java Virtual Machine などの抽象機械はすべて、スタックを使って算術式を評価します。
   例えば、
<<
   (2*3)+(3*(4-2))
>>
   という式は
<<
   2 3 * 3 4 2 - * +
>>
   と入力され、以下のように実行されるでしょう:
<<
  []            |    2 3 * 3 4 2 - * +
  [2]           |    3 * 3 4 2 - * +
  [3, 2]        |    * 3 4 2 - * +
  [6]           |    3 4 2 - * +
  [3, 6]        |    4 2 - * +
  [4, 3, 6]     |    2 - * +
  [2, 4, 3, 6]  |    - * +
  [2, 3, 6]     |    * +
  [6, 6]        |    +
  [12]          |
>>

  この練習問題のタスクは、[eaxp] をスタック機械の命令列に変換する小さなコンパイラを書き、その正当性を証明することです。

  スタック言語の命令セットは、以下の命令から構成されます:
     - [SPush n]: 数 [n] をスタックにプッシュする。
     - [SLoad X]: ストアから識別子 [X] に対応する値を読み込み、スタックにプッシュする。
     - [SPlus]:   スタックの先頭の 2 つの数をポップし、それらを足して、
                  結果をスタックにプッシュする。
     - [SMinus]:  上と同様。ただし引く。
     - [SMult]:   上と同様。ただし掛ける。
*)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(** Write a function to evaluate programs in the stack language. It
    takes as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and returns the stack after
    executing the program. Test your function on the examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements.  In a sense, it is
    immaterial what we do, since our compiler will never emit such a
    malformed program. *)
(** スタック言語のプログラムを評価するための関数を書きなさい。
    入力として、状態、数のリストとして表現されたスタック
    (スタックの先頭要素はリストの先頭)、
    および命令のリストとして表現されたプログラムを受け取り、
    受け取ったプログラムの実行した後のスタックを返します。
    下にある例で、その関数のテストをしなさい。

    上の仕様では、スタックが 2 つ未満の要素しか含まずに [SPlus] や [SMinus]、
    [SMult] 命令に至った場合を明示していないままなことに注意しましょう。
    我々のコンパイラはそのような奇形のプログラムは生成しないので、
    これは重要でないという意味です。
    しかし正当性の証明をするときは、いくつかの選択のほうが証明をより簡単にすることに気づくかもしれません。*)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
(* FILL IN HERE *) admit.


Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
(* FILL IN HERE *) Admitted.

Example s_execute2 :
     s_execute (update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
(* FILL IN HERE *) Admitted.

(*  Next, write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)
(** 次に、[aexp] をスタック機械のプログラムにコンパイルする関数を書きなさい。
    このプログラムを実行する影響は、もとの式の値をスタックに積むことと同じでなければなりません。*)


Fixpoint s_compile (e : aexp) : list sinstr :=
(* FILL IN HERE *) admit.

(* After you've defined [s_compile], uncomment the following to test
    that it works. *)
(** [s_compile]の定義が終ったら、以下のコメントを外し、テストが正しく動くことを確かめなさい。*)
(* 
Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.
*)
(** [] *)

(** **** Exercise: 3 stars, advanced (stack_compiler_correct) *)
(** The task of this exercise is to prove the correctness of the
    calculator implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)
(** この練習問題の課題は、前の練習問題で実装した計算機の正当性を証明することです。
スタックが 2 つ未満の要素しか含まずに [SPlus] や [SMinus]、[SMult] 命令に至った場合にどうすべきかを明示していない仕様であったことを思い出してください。(あなたは、正当性の証明をより易しく行うために、実装に戻って使いやすいように変更したくなるかもしれません!)

次の定理を証明しなさい。この定理は、[compile]関数が正しく振る舞うことを述べています。
使いやすい帰納法の仮定を得るために、もっと一般的な補題からとりかかる必要があるでしょう。
問題となる定理は、その補題の単純な帰結となるはずです。
*)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 5 stars, advanced (break_imp)  *)
(** **** 練習問題: ★★★★★, advanced (break_imp)  *)
Module BreakImp.

(** Imperative languages such as C or Java often have a [break] or
    similar statement for interrupting the execution of loops. In this
    exercise we will consider how to add [break] to Imp.

    First, we need to enrich the language of commands with an
    additional case. *)
(** CやJavaのような命令型言語は[break]やそれに類似した、ループ実行を中断するための文法を持っていることがよくあります。
この練習問題では、[break]をImpにどうやって追加するかを考えましょう。*)

Inductive com : Type :=
  | CSkip : com
  | CBreak : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "BREAK" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** Next, we need to define the behavior of [BREAK].  Informally,
    whenever [BREAK] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop (if any) should terminate. If there aren't any
    enclosing loops, then the whole program simply terminates. The
    final state should be the same as the one in which the [BREAK]
    statement was executed. *)
(** 次に、[BREAK]の振舞いを定義する必要があります。非形式的には、[BREAK]がコマンド列の中で実行されたらいつでも、
   そのシーケンスの実行を中断し、最も最近のループ(もしあれば)は終了するようにシグナルを出します。
   もし、ループが無ければ、プログラム全体も終了します。
(*    One important point is what to do when there are multiple loops
    enclosing a given [BREAK]. In those cases, [BREAK] should only
    terminate the _innermost_ loop where it occurs. Thus, after
    executing the following piece of code...

    ... the value of [X] should be [1], and not [0].
*)
(** 重要な点は、多重ループにおいて、[BREAK]が現われた場合に、何をすべきか、ということです。これらの場合、
[BREAK]は最も最近(_innermost_)のループだけを終了させるべきです。それゆえ、次のコードの断片の実行後...
   X ::= 0;;
   Y ::= 1;;
   WHILE 0 <> Y DO
     WHILE TRUE DO
       BREAK
     END;;
     X ::= 1;;
     Y ::= Y - 1
   END
   ... [X]の値は[0]ではなく、[1]であるべきです。 *)

(*
    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [BREAK] statement: *)
(**
   この振舞いを表現するもう一つの方法は、[BREAK]文を実行するコマンドの評価がどうであるかを特定する評価関係を別のパラメータとして追加することです。
*)
   
Inductive status : Type :=
  | SContinue : status
  | SBreak : status.

Reserved Notation "c1 '/' st '||' s '/' st'"
                  (at level 40, st, s at level 39).

(** Intuitively, [c / st || s / st'] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that any surrounding loop (or the whole program) should exit
    immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[c / st || s / st']" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([c / st || s / st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [SKIP], then the state doesn't change, and
      execution of any enclosing loop can continue normally.

    - If the command is [BREAK], the state stays unchanged, but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [IF b THEN c1 ELSE c2 FI], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ; c2], we first execute
      [c1]. If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state should be the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal that was
      generated there.

    - Finally, for a loop of the form [WHILE b DO c END], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises. If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration. In either case, since [BREAK] only terminates the
      innermost loop, [WHILE] signals [SContinue]. *)
(** 直感的に、[c / st || s / st']は次のことを意味します。もし、[c]が状態[st]で開始しているならば、それは状態[st']で終了し、囲まれているループ(またはプログラム全体)に対し直ちに([s=SBreak]の場合)終了するか、実行を正常どおり([s = SContinue]の場合)続けるかシグナルを出します。
  "[c / st || s / st']" 関係の定義は、上記で通常の関係の評価として我々が与えた一つ	([c / st || s / st']) にとてもよく似ています。 -- 必要になるのは、終了シグナルを適切にハンドルすることだけです。
   
*)    
    - [SKIP]コマンドの場合、状態は変更されませんし、どんな外部ループも正常に実行を続けることが出来ます。

    - [BREAK]コマンドの場合、状態は不変のままですが、[SBreak]シグナルを送出します。

    - 代入コマンドの場合は、状態の中にある変数の束縛を代入コマンドに従って更新します。そして正常に実行を続けることが出来ます。

    - コマンドが[IF b THEN c1 ELSE c2 FI]の形をしている場合、状態はImpの元々の意味で更新されます。選択された枝の実行からのシグナルを伝播することを除いて。

    - 複文コマンド[c1 ;; c2]の場合、最初にまず[c1]を実行します。もしc1が[SBreak]を送出するなら、c2の実行をスキップして、囲まれている文脈にたいして、[SBreak]シグナルを送出します。その結果として状態は、ただ[c1]だけを実行したものと同じになります。また、[c1]を実行して得た状態の元で、[c2]を実行した場合は、そこで生成されたシグナルを伝播します。

    - 最後に、[WHILE b DO c END]の形のループをとりあげます。そのセマンティクスは、これまでのものとほとんど同じです。違いはただ、[b]がtrueと評価された場合に、[c]を実行し、送出されてるシグナルのチェックを行うことだけです。もし、シグナルが[SContinue]である場合は、元のImpと同じ意味になりますし、[SBreak]の場合は、ループの実行を止めて、状態が結果として、現在の繰り返しの実行による状態と同じなります。いずれにせよ、[BREAK]は最も内側のループだけを終了させ、[WHILE]そのものは、[SContinue]シグナルを送出します。
*)

(*  Based on the above description, complete the definition of the
    [ceval] relation. *)
(** 上記の記述に基いて、[ceval]関係の定義を完成させなさい。*)

Inductive ceval : com -> state -> status -> state -> Prop :=
  | E_Skip : forall st,
      CSkip / st || SContinue / st
  (* FILL IN HERE *)

  where "c1 '/' st '||' s '/' st'" := (ceval c1 st s st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip"
  (* FILL IN HERE *)
  ].

(*  Now the following properties of your definition of [ceval]: *)
(** あなたの[ceval]の定義が次の性質を満たしているか確認しなさい *)
Theorem break_ignore : forall c st st' s,
     (BREAK;; c) / st || s / st' ->
     st = st'.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st || s / st' ->
  s = SContinue.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st || SBreak / st' ->
  (WHILE b DO c END) / st || SContinue / st'.
Proof.
  (* FILL IN HERE *) Admitted.

(*  **** Exercise: 3 stars, advanced, optional (while_break_true)  *)
(** **** 練習問題: ★★★, advanced, optional (while_break_true)  *)
Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st || SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' || SBreak / st'.
Proof.
(* FILL IN HERE *) Admitted.

(*  **** Exercise: 4 stars, advanced, optional (ceval_deterministic)  *)
(** **** 練習問題: ★★★★, advanced, optional (ceval_deterministic)  *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st || s1 / st1  ->
     c / st || s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* FILL IN HERE *) Admitted.

End BreakImp.
(** [] *)

(*  **** Exercise: 3 stars, optional (short_circuit) *)
(** **** 練習問題: ★★★, optional (short_circuit) *)
(*  Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval]. *)
(** 多くのモダンなプログラミング言語はブール演算子 [and] に対し、
    「省略した」実行を使っています。
    [BAnd b1 b2] を実行するには、まず [b1] を評価します。
    それが [false] に評価されるならば、[b2] の評価はせず、
    すぐに [BAnd] 式全体の結果を [false] に評価します。
    そうでなければ、[BAnd] 式の結果を決定するため、[b2] が評価されます。

    このように [BAnd] を省略して評価する、別のバージョンの [beval] を書き、
    それが [beavl] と等価であることを証明しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(*  **** Exercise: 4 stars, optional (add_for_loop) *)
(** **** 練習問題: ★★★★, optional (add_for_loop) *)
(* Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this file
    are accepted by Coq.

    A [for] loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for [for] loops, but feel free
    to play with this too if you like.) *)
(** C 風の [for] ループをコマンドの言語に追加し、[ceval] の定義を
   [for] ループの意味も与えるよう更新して、
   このファイルにあるすべての証明が Coq に通るよう、
   必要なところへ [for] ループに対する場合分けを追加しなさい。

    [for] ループは (a) 初めに実行される主張、
    (b) 各繰り返しで実行される、ループを続けてよいか決定するテスト、
    (c) 各ループの繰り返しの最後に実行される主張、および
    (d) ループの本体を構成する主張によってパラメタ化されていなければなりません。
    ([for] ループに対する具体的な表記の構成を気にする必要はありませんが、
    やりたければ自由にやって構いません。) *)


(* FILL IN HERE *)
(** [] *)


(* <$Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

