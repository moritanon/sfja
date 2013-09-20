(** * 前書き *)

(** この電子文章は「ソフトウェアの基礎」、信頼出来るソフトウェアの数学的基礎という講座のためのものです。トピックスとして、論理の基礎概念、コンピュータによる支援を利用した定理証明とCoq 証明支援システム、関数プログラミング、操作的意味論、ホアレの論理、静的型システムが含まれます。説明は学部生から博士課程の生徒や研究員まで幅広い読者を対象としています。論理学やプログラミング言語の特定のバックグラウンドは求めていませんが、数学の知識があれば役に立つでしょう。

このコースの主な特徴は、教材のテキストがCoqのスクリプトファイルそのものとなっており、学習の進み具合を「形式的」かつ「機械的」にチェックしながら学んでいくことができる、ということです。このコースでは、Coqのインタラクティブモードを使って、ソースを1行1行追いながら動きを理解していきます。講義のほとんどはCoqで組み立てられ、Coq上で作業し演習するようデザインされています。

このファイルは章立てされ整理されており、1学期ぶんの教材として十分で、順番に学習していけるよう、筋道立てて作成されています。さらに加えて、いくつかのトピックについて追加項目があります。主要な章はすべて、学部生と院生の両方の学習に適しています。

 *)



(** * 概要 *)

(** 信頼性のあるソフトウェアを構築することは困難です。現代のソフトウェアシステムの規模と複雑さ、大勢の人がそれらソフトウェアを構築するときに含まれる大量の人間とそれらの上に占める要求の幅が、多大な時間を費してもなお、意図した通りに動作するソフトウェアを構築することを極端に難しくしています。それと同時に、ソフトウェアが我々の社会のあらゆる局面に入りこむ度合いが増加していくにつれて、バグと不安定さに対するコストを増幅させています。

コンピュータサイエンスとソフトウェア工学はこれらの挑戦にソフトウェアの信頼性を改善するためのたくさんの技術を向上させること、ソフトウェアプロジェクトの管理やプログラミングチームの構成（エキストリームプログラミングなど）についての提案からライブラリ（MVCとか、publishing-subscribeなど）やプログラミング言語（オブジェクト指向やアスペクト指向、関数型プログラミングなどなど）をデザインするための哲学まで、果ては、ソフトウェアの性質について特徴付けや理由付けのための数学的手法やそれらの特質を検証に役立つツールなどで答えて来ました。

このコースは、上記の最後の技術セットに焦点を当てています。テキストは、5つの概念の糸を織り合わせます。

 (1) プログラムについての適切なclaims（宣言？）を作成し、それが正当であることを証明すための_論理_からなる基本的なツール

 (2) 厳格な論理的根拠を構築するために_証明支援システム_を使用すること

 (3) プログラミング手法とプログラミングと論理の橋渡しの両方としての_関数型プログラミング_の考え方

 (4) _特定のプログラムの特質についての論拠_のための形式的手法。（例えば、全ての入力に対してループが終了することとか、ソート関数がその仕様を実際に満たしているかとか）

 (5) 所与のプログラミング言語（たとえばよく型付けされたJavaプログラムは実行時に落ちることはないというのは事実です）の_あらゆる_プログラムに対し上手く動作することを保証するために _型システム_を使用すること

それぞれのトピックスはそれ自体がコース全体を満たすほどに豊かな内容を持つものですので、それらを一緒に全部学ぶことは、自然と多くのことを学ばないままということを意味します。しかし我々は読者が それらのテーマがお互いに有用さのなかで輝きを増すことに、そしてそれらがそろって基礎を形作り、より深い探求を容易にするということに同意してくれることを願います。「あとがき （Postscript）」の章に、読んでおいて損はない本、テキストをあげておきました。 *)

(** ** 論理 *)

(**  Logic is the field of study whose subject matter is _proofs_ --
    unassailable arguments for the truth of particular propositions.

    Volumes have been written about the central role of logic in
    computer science.  Manna and Waldinger called it "the calculus of
    computer science," while Halpern et al.'s paper _On the Unusual
    Effectiveness of Logic in Computer Science_ catalogs scores of
    ways in which logic offers critical tools and insights.  

   In particular, the fundamental notion of inductive proofs is
   ubiquitous in all of computer science.  You have surely seen them
   before, in contexts from discrete math to analysis of algorithms,
   but in this course we will examine them much more deeply than you
   have probably done so far. *)



(** ** Proof Assistants *)

(** The flow of ideas between logic and computer science has not gone
    only one way: CS has made its own contributions to logic.  One of
    these has been the development of tools for constructing proofs of
    logical propositions.  These tools fall into two broad categories:

       - _Automated theorem provers_ provide "push-button" operation:
         you give them a proposition and they return either _true_,
         _false_, or _ran out of time_.  Although their capabilities
         are limited to fairly specific sorts of reasoning, they have
         matured enough to be useful now in a huge variety of
         settings.  Examples of such tools include SAT solvers, SMT
         solvers, and model checkers.

       - _Proof assistants_ are hybrid tools that try to automate the
         more routine aspects of building proofs while depending on
         human guidance for more difficult aspects.  Widely used proof
         assistants include Isabelle, Agda, Twelf, ACL2, PVS, and Coq,
         among many others.

    This course is based around Coq, a proof assistant that has been
    under development since 1983 at a number of French research labs
    and universities.  Coq provides a rich environment for interactive
    development of machine-checked formal reasoning.  The kernel of
    the Coq system is a simple proof-checker which guarantees that
    only correct deduction steps are performed.  On top of this
    kernel, the Coq environment provides high-level facilities for
    proof development, including powerful tactics for constructing
    complex proofs semi-automatically, and a large library of common
    definitions and lemmas.
    
    Coq has been a critical enabler for a huge variety of work across
    computer science and mathematics.  

    - As a platform for the modeling of programming languages, it has
      become a standard tool for researchers who need to describe and
      reason about complex language definitions.  It has been used,
      for example, to check the security of the JavaCard platform,
      obtaining the highest level of common criteria certification,
      and for formal specifications of the x86 and LLVM instruction
      sets.

    - As an environment for the development of formally certified
      programs, Coq has been used to build CompCert, a fully-verified
      optimizing compiler for C, for proving the correctness of subtle
      algorithms involving floating point numbers, and as the basis
      for Certicrypt, an environment for reasoning about the security
      of cryptographic algorithms.

    - As a realistic environment for experiments with programming with
      dependent types, it has inspired numerous innovations.  For
      example, the Ynot project at Harvard embeds "relational Hoare
      reasoning" (an extension of the _Hoare Logic_ we will see later
      in this course) in Coq.

    - As a proof assistant for higher-order logic, it has been used to
      validate a number of important results in mathematics.  For
      example, its ability to include complex computations inside
      proofs made it possible to develop the first formally verified
      proof of the 4-color theorem.  This proof had previously been
      controversial among mathematicians because part of it included
      checking a large number of configurations using a program. In
      the Coq formalization, everything is checked, including the
      correctness of the computational part.  More recently, an even
      more massive effort led to a Coq formalization of the
      Feit-Thompson Theorem -- the first major step in the
      classification of finite simple groups. 

   By the way, in case you're wondering about the name, here's what
   the official Coq web site says: "Some French computer scientists
   have a tradition of naming their software as animal species: Caml,
   Elan, Foc or Phox are examples of this tacit convention. In French,
   “coq” means rooster, and it sounds like the initials of the
   Calculus of Constructions CoC on which it is based."  The rooster
   is also the national symbol of France, and "Coq" are the first
   three letters of the name of Thierry Coquand, one of Coq's early
   developers. *)

(** ** Functional Programming *)

(** The term _functional programming_ refers both to a collection of
    programming idioms that can be used in almost any programming
    language and to a particular family of programming languages that are
    designed to emphasize these idioms, including Haskell, OCaml,
    Standard ML, F##, Scala, Scheme, Racket, Common Lisp, Clojure,
    Erlang, and Coq.  

    Functional programming has been developed by researchers over many
    decades -- indeed, its roots go back to Church's lambda-calculus,
    developed in the 1930s before the era of the computer began!  But
    in the past two decades it has enjoyed a surge of interest among
    industrial engineers and language designers, playing a key role in
    high-value systems at companies like Jane St. Capital, Microsoft,
    Facebook, and Ericsson.

    The most basic tenet of functional programming is that, as much as
    possible, computation should be _pure_: the only effect of running
    a computation should be to produce a result; the computation
    should be free from _side effects_ such as I/O, assignments to
    mutable variables, or redirecting pointers.  For example, whereas
    an _imperative_ sorting function might take a list of numbers and
    rearrange the pointers to put the list in order, a pure sorting
    function would take the original list and return a _new_ list
    containing the same numbers in sorted order.

    One significant benefit of this style of programming is that it
    makes programs easier to understand and reason about.  If every
    operation on a data structure yields a new data structure, leaving
    the old one intact, then there is no need to worry about where
    else in the program the structure is being shared, whether a
    change by one part of the program might break an invariant that
    another part of the program thinks is being enforced.  These
    considerations are particularly critical in concurrent programs,
    where any mutable state that is shared between threads is a
    potential source of pernicious bugs.  Indeed, a large part of the
    recent interest in functional programming in industry is due to its
    simple behavior in the presence of concurrency.

    Another reason for the current excitement about functional
    programming is related to this one: functional programs are often
    much easier to parallelize than their imperative counterparts.  If
    running a computation has no effect other than producing a result,
    then it can be run anywhere.  If a data structure is never
    modified in place, it can be copied freely, across cores or across
    the network.  Indeed, the MapReduce idiom that lies at the heart
    of massively distributed query processors like Hadoop and is used
    at Google to index the entire web is an instance of functional
    programming.

    For purposes of this course, functional programming has one other
    significant attraction: it serves as a bridge between logic and
    computer science.  Indeed, Coq itself can be seen as a combination
    of a small but extremely expressive functional programming
    language, together with a set of tools for stating and proving
    logical assertions.  However, when we come to look more closely,
    we will find that these two sides of Coq are actually aspects of
    the very same underlying machinery -- i.e., _proofs are programs_. *)

(** ** Program Verification *)

(** The first third of the book is devoted to developing the
    conceptual framework of logic and functional programming and to
    gaining enough fluency with the essentials of Coq to use it for
    modeling and reasoning about nontrivial artifacts.  From this
    point on, we will increasingly turn our attention to two broad
    topics of critical importance to the enterprise of building
    reliable software (and hardware!): techniques for proving specific
    properties of particular _programs_ and for proving general
    properties of whole programming _languages_.  

    For both of these, the first thing we need is a way of
    representing programs as mathematical objects (so we can talk
    about them precisely) and of describing their behavior in terms of
    mathematical functions or relations.  Our tools for these tasks
    will be _abstract syntax_ and _operational semantics_, a method of
    specifying the behavior of programs by writing abstract
    interpreters.  At the beginning, we will work with operational
    semantics in the so-called "big-step" style, which leads to
    somewhat simpler and more readable definitions, in those cases
    where it is applicable.  Later on, we will switch to a more
    detailed "small-step" style, which helps make some useful
    distinctions between different sorts of "nonterminating" program
    behaviors and which can be applied to a broader range of language
    features, including concurrency.

    The first programming language we consider in detail is Imp, a
    tiny toy language capturing the most fundamental features of
    conventional imperative languages: variables, assignment,
    conditionals, and loops. We study two different ways of reasoning
    about the properties of Imp programs.  

    First, we consider what it means to say that two Imp programs are
    _equivalent_ in the sense that they give the same behaviors for
    all initial memories.  This notion of equivalence then becomes a
    criterion for judging the correctness of _metaprograms_ --
    programs that manipulate other programs, such as compilers and
    optimizers.  We build a simple optimizer for Imp and prove that it
    is correct.

    Second, we develop a methodology for proving that Imp programs
    satisfy some formal specification of their behavior.  We introduce
    the notion of _Hoare triples_ -- Imp programs annotated with pre-
    and post-conditions describing what should be true about the
    memory in which they are started and what they promise to make
    true about the memory in which they terminate -- and the reasoning
    principles of _Hoare Logic_, a "domain-specific logic" specialized
    for convenient compositional reasoning about imperative programs,
    with concepts like "loop invariant" built in.

    This part of the course will give you a taste of the key ideas and
    mathematical tools used for a wide variety of real-world software
    and hardware verification tasks.

*)

(** ** Type Systems *)

(** Our final major topic, covering the last third of the course, is
    _type systems_, a powerful set of tools for establishing
    properties of _all_ programs in a given language.

    Type systems are the best established and most popular example of
    a highly successful class of formal verification techniques known
    as _lightweight formal methods_.  These are reasoning techniques
    of modest power -- modest enough that automatic checkers can be
    built into compilers, linkers, or program analyzers and thus be
    applied even by programmers unfamiliar with the underlying
    theories.  (Other examples of lightweight formal methods include
    hardware and software model checkers and run-time property
    monitoring, a collection of techniques that allow a system to
    detect, dynamically, when one of its components is not behaving
    according to specification).

    In a sense, this topic brings us full circle: the language whose
    properties we study in this part, called the _simply typed
    lambda-calculus_, is essentially a simplified model of the core of
    Coq itself!

*)



(*

  - ソフトウェア工学のための、数学に根ざした論理学
<<
                論理学                       微積分学
         --------------------   =   ----------------------------
           ソフトウェア工学                機械/土木工学
>>
特に、帰納的に定義された集合や関係とその帰納的な証明は、コンピュータサイエンスのいたるところで見られます。このコースでは、帰納法をあらゆる角度から分析します。

  - 関数プログラミング：ソフトウェア開発者が持つべき道具のうち、重要性が特に増している

       - ソフトウェア開発のメインストリームでの方法論での、先進的なプログラミング手法は、関数プログラミングの影響を日増しに強く受けるようになっています。

       - 特に永続的なデータ構造を用い、状態の変化を避けることで、並列プログラミングをシンプルなものとすることができます。

  - プログラミング言語の基礎（このコースの２番目のパート）

        - 表記法　　厳格に表現するテクニック：新しいプログラム言語や、その特色のストレステスト（これは驚くほど普通に行われていることです！）巨大なソフトウェアシステムの多くは基本的なプログラム言語をサブシステムとして持っています（例：正規表現、コマンドラインフォーマット、設定ファイル、SQL、Flash,PDFなどなど）

        - 毎日ソフトウェア作成に使用しているツールに対して、さらに理解を深める。あなたのお気に入りのプログラミング言語が、動作の裏で何を行っているか。

  - Coq　実用に十分な証明支援器

       - 証明支援器は、ソフトウェアやハードウェア開発の両方でますます一般的になりつつあります。Coqはそういったツールであるだけでなく、それを徹底的に学ぶことで、他のツールの理解にも大幅に有利になるようなものです。

*)


(** * 実際の学習について *)


(** ** 章間の依存関係 *)

(** 章と章の間の依存関係をまとめた図と、学習教材へのパスを、[deps.html]にまとめてあります。 *)


(** ** 学習者に要求される知識的前提 *)

(** この資料は、学部生から博士課程、研究者までの幅広い読者に読んでもらえることを想定しています。プログラミング言語や論理学について前提としている知識はさほど大きくありませんが、数学の十分な学位があると理解は早まるでしょう。 *)



(** * Coqについて *)

(** 我々のこのコースでの「研究所」は、Coq証明支援器です。Coqは以下の二つの機能を併せ持っています。
      - シンプルでいささか風変わりな（しかしそのぶん表現力がある）プログラミング言語で、しかも
      - 論理学で言うところの仮定（プログラムの動作に関する仮定も含む）からスタートし、その正当性の証拠を導き出すためのツールです。

    我々は、この両面を同時に研究していきます。
*)


(** ** 学習に必要なもの *)

(** Coqは、Windowsと多くのUNIX変種（LinuxやMacOSを含む）で動きます。具体的には
       - Coqホームページにある最新版のCoq。（全てのサンプルソースはバージョン8.3でコンパイルできることが確認されていますが、8.2でもおそらく動きます）
       - Coqを対話的に操作するIDE。現在、以下の二つから選択できます。
           - ProofGeneralは、Emacs上に作られたIDEです。すでにEmacsに慣れている人向けのものです。Coqとは別にインストールする必要があります。（詳しくはgoogleで"ProofGeneral"を検索してください）
           - CoqIDEは、スタンドアロンで動作するシンプルなIDEです。Coqと一緒に配布されています。しかしいくつかのプラットホームではGUIライブラリなどの追加パッケージをインストールする必要があります。 *)


(** ** 教材となるCoqファイルの入手方法 *)

(** この教材のリリース版のソース（CoqスクリプトとHTMLファイル）をtarで固めたものが、以下のURLで取得できます。
<<
        http://www.cis.upenn.edu/~bcpierce/sf
>>
    この資料の一部だけを使用したい場合は、tarファイルとなっているリリース版を展開して使用してください。
*)


(** * 練習問題について *)

(** この資料の各章には、たくさんの練習問題がついています。"optional（任意）"と記されたり"recommended（推奨）"とされているものもあります。"任意"とされていない問題までやることで、その章で学ぶべきことを6～8時間（長い章でも）の学習で理解できるようになっています。

    練習問題についている"スターレーティング"には、以下のような意味があります。

       - ★：多くの読者が1～2分でできる簡単な問題。"推奨"と明示しているものはありませんが、どちらかというと全て"推奨"とされるべきものです。読者は、この問題に取り組んで、このレベルの問題に慣れておくべきです。

       - ★★：　素直で簡単な問題（5～10分でできるでしょう）

       - ★★★：　少し考えないといけない問題（15～30分ほどかかるでしょう）

       - ★★★★：　さらに難しい問題（1～2時間）
*)


(** * 推奨書籍 *)

(** 「あとがき （[Postscript]）」の章に、読んでおいて損はない本、テキストをあげておきました。 *)


(** * 教育関係者へ *)

(** この資料を自分のコースで使おうと思った場合、ほぼまちがいなくあなたは書き直したり、追加したりしたいところが出てくるでしょう。そういった貢献は大歓迎です。

ぜひBenjamin Pierceまでemailをください。そうすれば、あなた用のsubversionのリポジトリとメーリングリストのアカウントを用意します。リポジトリには、READMEファイルがありますので、次にどうすべきかはそれを参照してください。 *)



(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)