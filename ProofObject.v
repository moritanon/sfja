(*  * ProofObjects: Working with Explicit Evidence in Coq *)
(** * 証明オブジェクト: Coqの中での明示的根拠の働き *)

Require Export MoreLogic_J.

(* ##################################################### *)

(**  We have seen that Coq has mechanisms both for _programming_,
    using inductive data types (like [nat] or [list]) and functions
    over these types, and for _proving_ properties of these programs,
    using inductive propositions (like [ev] or [eq]), implication, and 
    universal quantification.  So far, we have treated these mechanisms
    as if they were quite separate, and for many purposes this is
    a good way to think. But we have also seen hints that Coq's programming and 
    proving facilities are closely related. For example, the
    keyword [Inductive] is used to declare both data types and 
    propositions, and [->] is used both to describe the type of
    functions on data and logical implication. This is not just a
    syntactic accident!  In fact, programs and proofs in Coq are almost
    the same thing.  In this chapter we will study how this works.

    We have already seen the fundamental idea: provability in Coq is
    represented by concrete _evidence_.  When we construct the proof
    of a basic proposition, we are actually building a tree of evidence, 
    which can be thought of as a data structure. If the proposition
    is an implication like [A -> B], then its proof will be an 
    evidence _transformer_: a recipe for converting evidence for
    A into evidence for B.  So at a fundamental level, proofs are simply
    programs that manipulate evidence.
*)
(** これまでに、Coqが、帰納的に定義された([list]や[nat]などの)データ型とそれら型上の関数を使用したプログラミング(_programming_)の側面と、これらのプログラムの性質を帰納的に定義された([ev]や[eq]などの)命題や含意、全称記号を使用して証明すること(_proving_)の両方のメカニズムを持つことを見て来ました。 いままでのところ、これらのメカニズムを全然別のものであるかのように取り扱ってきました。このことは多くの目的に適います。しかし、Coqのプログラミングと証明のための機能は密接に関係しています。例えば、[Inductive]というキーワードは、データ型と命題の両方の宣言に用いられますし、[->]は、関数の型と論理的な含意の記述の両方に使用されます。これは単なる偶然ではありません。実際、Coqにおいて、プログラムと証明はほとんど同じものです。この章において、Coqがどのように動くのかを学びましょう。
我々はすでに根本的なアイデアを見て来ています。Coqにおける証明可能性は具体的な根拠[_evidence_]において表現されており、我々は実際に根拠の木を構築し、その木はデータ構造と同じものであると考えることが出来ます。もし命題が、[A -> B]のような含意を持っていれば、その証明はBの根拠のためにAの根拠を変換するためのレシピになるでしょう。そのため根本的なレベルにおいては、証明は単純なことに根拠を操作するプログラムなのです。 *)
(*
    Q. If evidence is data, what are propositions themselves?

    A. They are types!

    Look again at the formal definition of the [beautiful] property.  *)
(**
   Q. もし根拠がデータなら、命題自身はなんなのでしょう？
   
   A. 型なんです!
*)
Print beautiful. 
(* ==>
  Inductive beautiful : nat -> Prop :=
      b_0 : beautiful 0
    | b_3 : beautiful 3
    | b_5 : beautiful 5
    | b_sum : forall n m : nat, beautiful n -> beautiful m -> beautiful (n + m)
*)

(** *** *)

(* The trick is to introduce an alternative pronunciation of "[:]".
    Instead of "has type," we can also say "is a proof of."  For
    example, the second line in the definition of [beautiful] declares
    that [b_0 : beautiful 0].  Instead of "[b_0] has type 
    [beautiful 0]," we can say that "[b_0] is a proof of [beautiful 0]."
    Similarly for [b_3] and [b_5]. *)
(** トリックは、[:]の"なんとかの型を持っている。"というものとは違うもうひとつの読み方を導入します。
"なんとかの証明は"と読むことも出来ます。例えば、[beautiful]の定義において、二行目で、[b_0 : beautiful 0].と宣言してます。
これは、"[b_0]は[beautiful 0]という型を持っている。"と読むのではなく、"[b_0]は[beautiful 0]の証明である"と読みます。 *)
*)
(** *** *)

(* This pun between types and propositions (between [:] as "has type"
    and [:] as "is a proof of" or "is evidence for") is called the
    _Curry-Howard correspondence_.  It proposes a deep connection
    between the world of logic and the world of computation.
<<
                 propositions  ~  types
                 proofs        ~  data values
>>
    Many useful insights follow from this connection.  To begin with, it
    gives us a natural interpretation of the type of [b_sum] constructor: *)
(** この型と命題の間の類似性([:]の"型である"と"その証明または根拠である"ということ)はカーリーハワード対応と呼ばれます。この対応は、計算機の世界と論理の世界の間に深い関係があることを示唆します。
<<
	 命題          ~  集合 / 型
	 証明          ~  元、要素 / データ値
>>
	この関係から多くの有用な洞察が導かれます。まず、[b_sum]コンストラクタの型の自然な解釈を得られます。 
*)
Check b_sum.
(* ===> b_sum : forall n m, 
                  beautiful n -> 
                  beautiful m -> 
                  beautiful (n+m) *)
(* This can be read "[b_sum] is a constructor that takes four
    arguments -- two numbers, [n] and [m], and two pieces of evidence,
    for the propositions [beautiful n] and [beautiful m], respectively -- 
    and yields evidence for the proposition [beautiful (n+m)]." *)
(** これは次のように読むことが出来ます。"[b_sum]は4つの引数を -- 二つの数 [n]と[m]と、命題[beautiful n]と[beautiful m]のためのそれぞれの根拠を取り --
命題[beautiful (n+m)]の根拠を生成する" *)

(* Now let's look again at a previous proof involving [beautiful]. *)
(** それでは、もういちど先程の[beautiful]を含む証明を見てみましょう *)
Theorem eight_is_beautiful: beautiful 8.
Proof.
    apply b_sum with (n := 3) (m := 5). 
    apply b_3.
    apply b_5. Qed.

(* Just as with ordinary data values and functions, we can use the [Print]
command to see the _proof object_ that results from this proof script. *)
(** 序数を使った値と関数にしか見えませんが、[Print]コマンドを使うと、この証明スクリプトの結果としての証明オブジェクト[_proof object_]を見ることが出来ます。
*)
Print eight_is_beautiful.
(* ===> eight_is_beautiful = b_sum 3 5 b_3 b_5  
     : beautiful 8  *)

(* In view of this, we might wonder whether we can write such
    an expression ourselves. Indeed, we can: 
(** 
ぱっと見、そんな式なら、自分で書けるんじゃないかと思うかもしれません。はい。書けます。*)
Check (b_sum 3 5 b_3 b_5).  
(* ===> beautiful (3 + 5) *)

(* The expression [b_sum 3 5 b_3 b_5] can be thought of as
    instantiating the parameterized constructor [b_sum] with the
    specific arguments [3] [5] and the corresponding proof objects for
    its premises [beautiful 3] and [beautiful 5] (Coq is smart enough
    to figure out that 3+5=8).  Alternatively, we can think of [b_sum]
    as a primitive "evidence constructor" that, when applied to two
    particular numbers, wants to be further applied to evidence that
    those two numbers are beautiful; its type, 
    forall n m, beautiful n -> beautiful m -> beautiful (n+m),
    expresses this functionality, in the same way that the polymorphic
    type [forall X, list X] in the previous chapter expressed the fact
    that the constructor [nil] can be thought of as a function from
    types to empty lists with elements of that type. *)
(** [b_sum 3 5 b_3 b_5]という式は、パラメータ付きコンストラクタ[b_sum]を特定の引数[3]と[5]および、前提である[beautiful 3]と[beautiful 5]に対応する証明オブジェクトを指定して呼び出して、実体化させていると考えることが出来ます。あるいは、[b_sum]は二つの特定の数が適用されたときに、さらに、二つの数がbeautifulである根拠が適用されることを求めるプリミティブな根拠構築器であると考えることも出来ます。
その型は、forall n m, beautiful n -> beautiful m -> beautiful (n+m),です。
前の章において、多相的な型[forall X, list X]がコンストラクタ [nil]がその型の要素の空リストを生成する関数であるのと同じことです。
*)
(* This gives us an alternative way to write the proof that [8] is
    beautiful: *)
(** [8]がbeautifulである証明を書くもう一つの方法を示します。 *)
Theorem eight_is_beautiful': beautiful 8.
Proof.
   apply (b_sum 3 5 b_3 b_5).
Qed.

(* Notice that we're using [apply] here in a new way: instead of just
    supplying the _name_ of a hypothesis or previously proved theorem
    whose type matches the current goal, we are supplying an
    _expression_ that directly builds evidence with the required
    type. *)
(** ここでapplyを新しい方法で使ったことに注意してください, 仮定や以前証明した定理の名前を現在のゴールにマッチする型に合うように与えるのではなく、
  型が必要とする根拠を直接構築する式を与えています。*)

(* ##################################################### *)
(* * Proof Scripts and Proof Objects *)
(** * 証明スクリプトと証明オブジェクト *)

(* These proof objects lie at the core of how Coq operates. 

    When Coq is following a proof script, what is happening internally
    is that it is gradually constructing a proof object -- a term
    whose type is the proposition being proved.  The tactics between
    the [Proof] command and the [Qed] instruct Coq how to build up a
    term of the required type.  To see this process in action, let's
    use the [Show Proof] command to display the current state of the
    proof tree at various points in the following tactic proof. *)
(** これらの証明オブジェクトは、Coqの操作の核心部分です。

     Coqが証明スクリプトを進めるとき、内部的に起きていることは、証明オブジェクトを徐々に生成しています。項の型は証明されるべき命題です。 [Proof]コマンドと[Qed]コマンドの間のタクティックはCoqに要求される型の項をどのように構築するかを指示していきます。このプロセスを実地に見ることために、[Show Proof]コマンドを使用してみましょう。このコマンドは証明タクティックが進める証明木の様々な時点での状態を表示します。)
Theorem eight_is_beautiful'': beautiful 8.
Proof.
   Show Proof.
   apply b_sum with (n:=3) (m:=5).
   Show Proof.
   apply b_3.
   Show Proof.
   apply b_5.
   Show Proof.
Qed.

(* At any given moment, Coq has constructed a term with some
    "holes" (indicated by [?1], [?2], and so on), and it knows what
    type of evidence is needed at each hole.  *)
(** どの瞬間においても、Coqはいくつかの"穴"([?1]や[?2]やその他)を持つ項を構築しています。
そしてその穴に何の根拠の型が必要とされるかをCoqは知っています。*)
(*
    Each of the holes corresponds to a subgoal, and the proof is
    finished when there are no more subgoals.  At this point, the
    [Theorem] command gives a name to the evidence we've built and
    stores it in the global context. *)
(**
   それぞれの穴にはサブゴールが対応しており、証明は、サブゴールがすべて無くなったときに終了します。この時において、[Theorem]コマンドは我々が構築した根拠に名前を与え、グローバルなコンテキストにそれを追加します。 *)
(* Tactic proofs are useful and convenient, but they are not
    essential: in principle, we can always construct the required
    evidence by hand, as shown above. Then we can use [Definition] 
    (rather than [Theorem]) to give a global name directly to a 
    piece of evidence. *)
(** タクティックにようる証明は、使いやすいのですが、本質的ではありません。原理的に、われわれは上で見たように、必要とされる根拠を手でいつでも構築することが出来ます。それから、[Definition]コマンドを(むしろ[Theorem]コマンドより)根拠の断片にグローバルな名前を与えるために使っています。*)
Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

(* All these different ways of building the proof lead to exactly the
    same evidence being saved in the global environment. *)
(** 証明を構築する方法のいろいろありますが、正確におなじグローバル環境にセーブされる根拠に至ります。*)
Print eight_is_beautiful.
(* ===> eight_is_beautiful    = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'.
(* ===> eight_is_beautiful'   = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful''.
(* ===> eight_is_beautiful''  = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'''.
(* ===> eight_is_beautiful''' = b_sum 3 5 b_3 b_5 : beautiful 8 *)

(** ****  練習問題: ★ (six_is_beautiful) *)
(* Give a tactic proof and a proof object showing that [6] is [beautiful]. *)
(** [6]が[beautiful]であるというこを示すタクティックによる証明と証明オブジェクトを書きなさい。*)
Theorem six_is_beautiful :
  beautiful 6.
Proof.
  (* FILL IN HERE *) Admitted.

Definition six_is_beautiful' : beautiful 6 :=
  (* FILL IN HERE *) admit.
(** [] *)

(** ****  練習問題: ★(nine_is_beautiful) *)
(** Give a tactic proof and a proof object showing that [9] is [beautiful]. *)
(** [9]が[beautiful]であるというこを示すタクティックによる証明と証明オブジェクトを書きなさい。*)

Theorem nine_is_beautiful :
  beautiful 9.
Proof.
  (* FILL IN HERE *) Admitted.

Definition nine_is_beautiful' : beautiful 9 :=
  (* FILL IN HERE *) admit.
(** [] *)

(* ##################################################### *)
(* * Quantification, Implications and Functions *)
(** 全称量化、含意 と 関数 *)

(* In Coq's computational universe (where we've mostly been living
    until this chapter), there are two sorts of values with arrows in
    their types: _constructors_ introduced by [Inductive]-ly defined
    data types, and _functions_.

    Similarly, in Coq's logical universe, there are two ways of giving
    evidence for an implication: constructors introduced by
    [Inductive]-ly defined propositions, and... functions!

    For example, consider this statement: *)
(** Coqにおける計算機の世界(この章までは我々はほとんどそこに住んでいました)において、二つの種類の、型の中に矢印を持つ値があります。
再帰的[Inductive]に定義されることによって導入されるコンスラクタ(_constructors_)と関数(_function_)	です 

同様に、Coqの論理の世界において、含意のための根拠を与える二つの方法があります。再帰的[Inductive]に定義される命題と...そう。関数です!

例として次の文を考えましょう。 *)
Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
   intros n H.
   apply b_sum.
   apply b_3.
   apply H.
Qed.

(* What is the proof object corresponding to [b_plus3]? 

    We're looking for an expression whose _type_ is [forall n,
    beautiful n -> beautiful (3+n)] -- that is, a _function_ that
    takes two arguments (one number and a piece of evidence) and
    returns a piece of evidence!  Here it is: *)
(** [b_plus3]に対応する証明オブジェクトはどのようなものでしょうか？

われわれは、型(_type_)が[forall n, beautiful n -> beautiful (3 + n)]である式を探します。すなわち、二つの引数(一つの数値と根拠の断片)を取って、根拠の断片を返す関数(_function_)です! *)
Definition b_plus3' : forall n, beautiful n -> beautiful (3+n) := 
  fun (n : nat) => fun (H : beautiful n) =>
    b_sum 3 n b_3 H.

Check b_plus3'.
(* ===> b_plus3' : forall n : nat, beautiful n -> beautiful (3+n) *)

(* Recall that [fun n => blah] means "the function that, given [n],
    yields [blah]."  Another equivalent way to write this definition is: *)
(** [fun n => blah]は、関数を意味し、その関数は[n]が与えられたら、[blah]を返すものであることを思いだしましょう 
この定義を書くもう一つの等価な方法は、以下の通りです。 *)

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3+n) := 
  b_sum 3 n b_3 H.

Check b_plus3''.
(* ===> b_plus3'' : forall n, beautiful n -> beautiful (3+n) *)

(* When we view the proposition being proved by [b_plus3] as a function type,
    one aspect of it may seem a little unusual. The second argument's
    type, [beautiful n], mentions the _value_ of the first argument, [n].
    While such _dependent types_ are not commonly found in programming
    languages, even functional ones like ML or Haskell, they can
    be useful there too.  

    Notice that both implication ([->]) and quantification ([forall])
    correspond to functions on evidence.  In fact, they are really the
    same thing: [->] is just a shorthand for a degenerate use of
    [forall] where there is no dependency, i.e., no need to give a name
    to the type on the LHS of the arrow. *)                                           
(** [b_plus3]によって証明される命題を関数型として見るときに、その一つの局面はあまり役に立たないように見えるかもしれません。
二つめの引数の型、[beautiful n]は最初の引数である[n]の値に言及します。一方そのような依存型(_dependent types_)は通常のプログラミング言語、MLやHaskellのような関数型言語においてすら現われませんが、それらはとても有用なものなのです。
含意[->]と全称量化([forall])は根拠上の関数に対応しています。実際に、それらは本当に同じものです。[->]は、依存性が存在しない場合の[forall]の短縮記法にすぎません。つまり、LHSの矢印上の型に名前を与える必要がないような場合です。

LHSってなんや？
*)
(* For example, consider this proposition: *)
(** 例としてこの命題について考えてみましょう *)
Definition beautiful_plus3 : Prop := 
  forall n, forall (E : beautiful n), beautiful (n+3).

(** A proof term inhabiting this proposition would be a function
    with two arguments: a number [n] and some evidence [E] that [n] is
    beautiful.  But the name [E] for this evidence is not used in the
    rest of the statement of [funny_prop1], so it's a bit silly to
    bother making up a name for it.  We could write it like this
    instead, using the dummy identifier [_] in place of a real
    name: *)
(* この命題を継承する項は二つの引数
数 [n]と
[n]がbeautifulであるという根拠[E]
を取る関数になるでしょう。
しかしこの根拠のための名前[E]は[funny_prop1]の残りの文の中で使われません。そのための名前を考えだすために手間をかけることは少しばかばかしいように思われます。以上の代わりにダミーの識別子[_]を用いて以下のように書くことが出来ます。*)

Definition beautiful_plus3' : Prop := 
  forall n, forall (_ : beautiful n), beautiful (n+3).

(* Or, equivalently, we can write it in more familiar notation: *)
(** あるいは、もっと書き慣れた方法で書くことも出来ます。 *)
Definition beatiful_plus3'' : Prop :=
  forall n, beautiful n -> beautiful (n+3). 

(** In general, "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)
(** 一般的に、"[P -> Q]"というのは、"[forall (_:P), Q]"の糖衣構文です *)

(* **** Exercise: 2 stars b_times2 *)
(** **** 練習問題 ★★ b_times2 *)
(* Give a proof object corresponding to the theorem [b_times2] from Prop.v *)
(** Prop.vの定理[b_times2]に対応する証明オブジェクトを書きなさい *)
Definition b_times2': forall n, beautiful n -> beautiful (2*n) :=
  (* FILL IN HERE *) admit.
(** [] *)



(* **** Exercise: 2 stars, optional (gorgeous_plus13_po) *) 
(** **** 練習問題 ★★, optional (gorgeous_plus13_po) *) 
(** Give a proof object corresponding to the theorem [gorgeous_plus13] from Prop.v *)
(** Prop.vの定理[gorgeous_plus13]に対応する証明オブジェクトを書きなさい *)

Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n):=
   (* FILL IN HERE *) admit.
(** [] *)




(* It is particularly revealing to look at proof objects involving the 
logical connectives that we defined with inductive propositions in Logic.v. *)
(** 
Logic.vで再帰的な命題として論理的な関係を含む証明オブジェクトを見ることは、とりわけ、理解の一助になります。 *)

Theorem and_example : 
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
   (* Case "left". *)  apply b_0.
   (* Case "right". *)  apply b_3.  Qed.

(* Let's take a look at the proof object for the above theorem. *)
(** 上記の定理の証明オブジェクトをとりあげてみましょう *)

Print and_example. 
(* ===>  conj (beautiful 0) (beautiful 3) b_0 b_3
            : beautiful 0 /\ beautiful 3 *)

(** Note that the proof is of the form
    conj (beautiful 0) (beautiful 3) 
         (...pf of beautiful 3...) (...pf of beautiful 3...)
    as you'd expect, given the type of [conj]. *)
(** [conj]の型が与えられた場合は、あなたが期待したように、
  conj (beautiful 0) (beautiful 3)
    (.. beautiful 0の証明..)    (.. beautiful 3の証明..)
	という形になることに注意しましょう。
*)
(** **** Exercise: 1 star, optional (case_proof_objects) *)
(* The [Case] tactics were commented out in the proof of
    [and_example] to avoid cluttering the proof object.  What would
    you guess the proof object will look like if we uncomment them?
    Try it and see. *)
(** [Case]タクティックは[and_example]の証明ので、証明オブジェクに含まれないように、コメントアウトされていました。
コメントを外すとどのような証明オブジェクトになると思いますか？ 実際にやってみましょう。
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  split.  
    (* Case "left". *) apply HQ. 
    (* Case "right". *) apply HP.  Qed.

(* Once again, we have commented out the [Case] tactics to make the
    proof object for this theorem easier to understand. It is still
    a little complicated, but after performing some simple reduction
    steps, we can see that all that is really happening is taking apart 
    a record containing evidence for [P] and [Q] and rebuilding it in the
    opposite order: *)
(** この定理を理解しやすくするために[Case]タクティックをコメントアウトして証明オブジェクトを生成しています。
ちょっと複雑になりますが、簡約を行なうステップを実行することで、 PとQの根拠を含むレコードを分離して、反対の順序に組上げるときに実際におこる全てのことを見ることができます。
*)
Print and_commut.
(* ===>
    and_commut = 
      fun (P Q : Prop) (H : P /\ Q) =>
        (fun H0 : Q /\ P => H0)
            match H with
            | conj HP HQ => (fun (HP0 : P) (HQ0 : Q) => conj Q P HQ0 HP0) HP HQ
            end
      : forall P Q : Prop, P /\ Q -> Q /\ P *)

(* After simplifying some direct application of [fun] expressions to arguments,
we get: *)
(** [fun]式に引数を直接の適用することによる簡約で、以下のようになります。 *)

(* ===> 
   and_commut = 
     fun (P Q : Prop) (H : P /\ Q) =>
     match H with
     | conj HP HQ => conj Q P HQ HP
     end 
     : forall P Q : Prop, P /\ Q -> Q /\ P *)



(* **** Exercise: 2 stars, optional (conj_fact) *)
(** **** 練習問題 ★★,optional (conj_fact) *)
(* Construct a proof object demonstrating the following proposition. *)
(** 次の命題を立証する証明オブジェクトを書きなさい *)
Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  (* FILL IN HERE *) admit.
(** [] *)


(* **** Exercise: 2 stars, advanced, optional (beautiful_iff_gorgeous) *)
(** **** 練習問題 ★★, advanced, optional (beautiful_iff_gorgeous) *)

(** We have seen that the families of propositions [beautiful] and
    [gorgeous] actually characterize the same set of numbers.
    Prove that [beautiful n <-> gorgeous n] for all [n].  Just for
    fun, write your proof as an explicit proof object, rather than
    using tactics. (_Hint_: if you make use of previously defined
    theorems, you should only need a single line!) *)
(**
同じ数の集合を特徴付ける[beautiful]や[gorgeous]といった命題の仲間達を見てきました。
すべての[n]について、[beautiful <-> gorgeous]であることを証明しなさい。 
あそびやゲームのつもりで、明示的な証明オブジェクトとして証明を書いてみましょう。(ヒント:もし以前に定理を定義しているなら、一行で書けちゃいますよ。)
Definition beautiful_iff_gorgeous :
  forall n, beautiful n <-> gorgeous n :=
  (* FILL IN HERE *) admit.
(** [] *)


(** **** Exercise: 2 stars, optional (or_commut'') *)
(** **** 練習問題 ★★, optional (or_commut'') *)
(** Try to write down an explicit proof object for [or_commut] (without
    using [Print] to peek at the ones we already defined!). *)
(** [or_commut]の明示的な証明オブジェクトを書きなさい。定義済みの定理を[Print]で見たりしてはいけませんよ! *)
(* FILL IN HERE *)
(** [] *)

(* Recall that we model an existential for a property as a pair consisting of 
a witness value and a proof that the witness obeys that property. 
We can choose to construct the proof explicitly. 

For example, consider this existentially quantified proposition: *)
(** 
 根拠となる値とその値が性質を満たす証明からなるペアとして、存在することをモデル化したことを思いだしましょう。
証明を明示的に構築することを選ぶことが出来ます。
例として、次の 存在量化命題を考えましょう。
*)
Check ex.

Definition some_nat_is_even : Prop := 
  ex _ ev.

(* To prove this proposition, we need to choose a particular number
    as witness -- say, 4 -- and give some evidence that that number is
    even. *)
(** この命題を証明するために、特定の数を根拠として選択する必要があります。例えば、4です。
そして、その数が偶数であるという根拠に与えます。 *)
Definition snie : some_nat_is_even := 
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).


(* **** Exercise: 2 stars, optional (ex_beautiful_Sn) *)
(** **** 練習問題 ★★, optional (ex_beautiful_Sn) *)
(** Complete the definition of the following proof object: *)
(** 次の証明オブジェクトの定義を完成させなさい。 *)
Definition p : ex _ (fun n => beautiful (S n)) :=
(* FILL IN HERE *) admit.
(** [] *)



(* ##################################################### *)
(** * Giving Explicit Arguments to Lemmas and Hypotheses *)
(** * Lemma や Hypothesesに明示的に引数を与えること *)

(** Even when we are using tactic-based proof, it can be very useful to
understand the underlying functional nature of implications and quantification. 

For example, it is often convenient to [apply] or [rewrite] 
using a lemma or hypothesis with one or more quantifiers or 
assumptions already instantiated in order to direct what
happens.  For example: *)
(** 
タクティックを使用した証明を使用するときでも、含意や全称量化の基底となる関数的な本質を理解していることは、たいへん有用なことです。

たとえば、一つ以上の量化された補題や仮説、インスタンス化された仮定を使用する[apply]や[rewrite] で何が起こっているかを理解するために、しばしば役に立ちます。
*)
Check plus_comm.
(* ==> 
    plus_comm
     : forall n m : nat, n + m = m + n *)

Lemma plus_comm_r : forall a b c, c + (b + a) = c + (a + b).
Proof.
   intros a b c.
   (* rewrite plus_comm. *) 
      (* rewrites in the first possible spot; not what we want *)
   rewrite (plus_comm b a).  (* directs rewriting to the right spot *)
   reflexivity.  Qed.


(* In this case, giving just one argument would be sufficient. *)
(** このケースにおいて、一つの引数を与えるだけで十分です。 *)
Lemma plus_comm_r' : forall a b c, c + (b + a) = c + (a + b).
Proof.
   intros a b c.
   rewrite (plus_comm b). 
   reflexivity.  Qed.

(* Arguments must be given in order, but wildcards (_)
may be used to skip arguments that Coq can infer.  *)
(** 引数は順序通りに与えられる必要がありますが、ワイルドカードはCoqが推測する引数をスキップするために使用されるかもしれません。 *)
Lemma plus_comm_r'' : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros a b c.
  rewrite (plus_comm _ a).
  reflexivity. Qed.

(** The author of a lemma can choose to declare easily inferable arguments
to be implicit, just as with functions and constructors. 
(** 補題の作者は、関数や、コンストラクタと同じように、より推測しやすい引数を暗黙的に宣言するかどうか選ぶことが出来ます。*)
  The [with] clauses we've already seen is really just a way of
  specifying selected arguments by name rather than position:  *)

Lemma plus_comm_r''' : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros a b c.
  rewrite plus_comm with (n := b). 
  reflexivity. Qed.


(* **** Exercise: 2 stars (trans_eq_example_redux) *)
(** **** 練習問題: ★★ (trans_eq_example_redux) *)
(** Redo the proof of the following theorem (from MoreCoq.v) using
an [apply] of [trans_eq] but _not_ using a [with] clause. *)
(** 次の定理(MoreCoq.vより)を[apply]や[trans_eq]を使ってやりなおしなさい。ただし、[with] を使用せずにです。*)
Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ##################################################### *)
(* * Programming with Tactics (Optional) *)
(** タクティックを使用したプログラミング (Optional) *)

(** If we can build proofs with explicit terms rather than
tactics, you may be wondering if we can build programs using
tactics rather than explicit terms.  Sure! *)
明示的な項を使用して証明を構築できるならば、明示的な項ではなく、タクティックを使用してプログラムを構築することが出来るのでしょうか？
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

Eval compute in add1 2. 
(* ==> 3 : nat *)

(* Notice that we terminate the [Definition] with a [.] rather than with
[:=] followed by a term.  This tells Coq to enter proof scripting mode
to build an object of type [nat -> nat].  Also, we terminate the proof
with [Defined] rather than [Qed]; this makes the definition _transparent_
so that it can be used in computation like a normally-defined function.  

This feature is mainly useful for writing functions with dependent types,
which we won't explore much further in this book.
But it does illustrate the uniformity and orthogonality of the basic ideas in Coq. *)
(**  ここで[Definition]を[:=]とそれに続く項ではなく、[.]で終了させたことに気を付けましょう。
このことはCoqに対して、[nat->nat]型を持つオブジェクトを生成するために、証明スクリプトモードに入ることを告げるものです。
それから、[Qed]ではなく、[Defined]で証明を終わらせたことにも気を付けましょう。
このことは、定義を透過的(_transparent_)にするもので、計算中で、通常に定義された関数のように使用することが出来るようになります。

この性質はおもに、依存型を使った関数を書くときに便利ですが、この本ではこれ以上説明しません。
しかし、このことはCoqの基本的なアイデアが一貫性と直交性にあることを示しています。 *)

(* $Date: 2014-06-05 07:22:21 -0400 (Thu, 05 Jun 2014) $ *)

