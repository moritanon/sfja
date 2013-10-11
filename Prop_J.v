(* * Prop: Propositions and Evidence *)
(** Prop_J: 命題と根拠 *)
Require Export MoreCoq_J.

(* In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions 
    ([forall x, P]).  

    This chapter will take us on a first tour of the
    propositional (logical) side of Coq.
    In particular, we will expand our repertoire of primitive
    propositions to include _user-defined_ propositions, not just
    equality propositions (which are more-or-less "built in" to Coq). 
*)
(**
以前の章で、事実の主張（命題）とそれらが真であるという証拠を表現する方法（証明）の多くの例を見てきました。とりわけ、e1 = e2という形の等価命題、P → Q という形の含意、そして、∀ x , P という量化命題を広く使用してきました。

この章において、Coqの命題の(論理の)側面の最初のツアーを開始します。特に、プリミティブな命題をる量化命題だけないユーザが定義する命題へと(大なり小なりCoqにビルトインされているのですが)レパートリーを増やして行きます。*)

(* ##################################################### *)
(* * Inductively Defined Propositions *)
(** 帰納的に定義された命題 *)

(*  As a running example, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)
(** この章の最初の部分のexampleを実行するにあたって、自然数に関するシンプルな命題を定義し、その命題が示す[beautiful]数をと呼びましょう。 *)

(* Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.  

    More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful]. 
       - Rule [b_5]: The number [5] is [beautiful]. 
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)
(** 非形式的には、もしその数が、0、3、5であれば[beautiful]であり、また二つの[beautiful]数の和からなる数もまた[beautiful]であるとします。


もっと杓子定規な言い方をすると、[beautiful]数は以下の4つのルールによって定義されます。

       - Rule [b_0]: The number [0] は [beautiful]である。
       - Rule [b_3]: The number [3] は [beautiful]である。 
       - Rule [b_5]: The number [5] は [beautiful]である。 
       - Rule [b_sum]: もし[n]と[m]が共に[beautiful]であるならば、その和も[beautiful]である

*)
(* We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(** このような多くの定義をこのコースの残りを通して見て行きます。また、これらの読み書きを簡単にする軽量な記法があると非形式的な議論のために役にたちます。推論ルールの一つは次のように書きます。*)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(* Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  If a rule has no premises above the line, then
    its conclusion hold unconditionally.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)

(** 上記規則のそれぞれは、「もしラインの上にある根拠がすべて有効であるならば、ラインの下の結論が導かれる。」という推論規則として体裁を与えられています。たとえば、b_sumという規則は、「もし[n]と[m]がともに、[beautiful]であるならば、[n+m]もまた[beautiful]である。」ということが導かれるということを示しています。ラインの上に前提を持たない記録は、公理(axioms)と呼ばれます。

これらの規則は、beautifulという属性を定義します。すなわち、もし我々が特定の数が[beautiful]であることを誰かに納得させたければ、我々の論拠がこれらの規則を基にしたものに違いありません。簡単な例として、数[5]が[beautiful]であると主張すると仮定します。この主張を裏付けるために我々は、[b_5]の規則がそう言っていることを示すだけでよいのです。また我々が[8]が[beautiful]であることを主張したくなったときは、我々の主張が[3]と[5]がともに[beautiful]であり（b_3,b_5規則による）、それらの和が8であることから、b_sum規則によってbeautifulであることを示すことが出来ます。これらの論証は次の証明木によって図に示されます。*)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
    
もちろん、[8]が[beautiful]であることを示すための規則の用いかたは他にもあります。たとえば、

         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
[5]と[3]が引っくり返ってるだけかい・・・
*)

(** **** 練習問題 ★ (varieties_of_beauty) *)
(* How many different ways are there to show that [8] is [beautiful]? *)
(** [8]が[beautiful]であることを示す異なる方法はいくつあるでしょうか？ *)
(* FILL IN HERE *)
(** [] *)

(* In Coq, we can express the definition of [beautiful] as
    follows: *)
(** Coqにおいて、[beautiful]の定義は次のように表現します。*)
Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).


(* The first line declares that [beautiful] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    [beautiful]" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  Each of the remaining lines
    embodies one of the rules for [beautiful] numbers.

    The rules introduced this way have the same status as proven 
    theorems; that is, they are true axiomatically. 
    So we can use Coq's [apply] tactic with the rule names to prove 
    that particular numbers are [beautiful].  *)
(** 最初のラインは beautifulが命題であることを、あるいはもっと形式的に、自然数によってインデクス付けされた命題の仲間であることを宣言しています。そのような命題の一群をしばしば数の属性と呼びます。残りのそれぞれの行は、beautiful数ための規則のひとつを構成しています。

この方法で導入された規則は証明された定理と同じ状態を持っています。すなわち、公理的に真なのです。そのため、Coqの[apply]タクティックを規則の名前と共に特定の数が[beautiful]であることを証明するために使用することが出来ます。*)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* これは [b_3]の規則を単純に適用するだけです。 *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* まず[b_sum]規則を使用します。Coqは[n]と[m]を証拠として示すように言ってきます。First we use the rule [b_sum], telling Coq how to instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* [b_sum]によって生成されたサブゴールを解くために、[beautiful 3]と[beautiful 5]の根拠を提示しなければなりません。幸運なことに、われわれは両方の根拠を生成する規則を持っています。*)
   apply b_3.
   apply b_5.
Qed.

(* As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)
(** 期待したとおり、[beautiful]についての仮説を持つ定理の証明も行うことが出来ます。
*)
Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.
  

(** **** 練習問題 ★★ (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(* ** Induction Over Evidence *)
(** ** 根拠上の帰納法 *)

(* Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)
(** 数が[beautiful]であるという根拠を構築際に、そのような根拠について推論することも出来ます。*)
(* The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    two constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)
(**  [beautiful]を[inductive]な宣言を以て導入したという事実は、Coqに[b_0],[b_3],[b_5][b_sum]というコンストラクタが根拠を構築する方法であると教えるだけでなく、これらの二つ？のコンストラクタだけが数がbeautifulであるという根拠を構築する方法であることを教えます。
*)

(** In other words, if someone gives us evidence [E] for the assertion
    [beautiful n], then we know that [E] must have one of four shapes:

      - [E] is [b_0] (and [n] is [O]),
      - [E] is [b_3] (and [n] is [3]), 
      - [E] is [b_5] (and [n] is [5]), or 
      - [E] is [b_sum n1 n2 E1 E2] (and [n] is [n1+n2], where [E1] is
        evidence that [n1] is beautiful and [E2] is evidence that [n2]
        is beautiful). *)
 (** 言い替えると、もし、[beautiful n]という表明の根拠[E]が与えられたら、[E]は以下の4つのどれかの形をしている。ということです。
 
      - [E] は  [b_0] (かつ [n] は [O]),
      - [E] は [b_3] (かつ [n] は [3]), 
      - [E] は [b_5] (かつ [n] は [5]), or 
      - [E] は [b_sum n1 n2 E1 E2] (かつ [n] is [n1+n2], このなかで、 [E1] は
         [n1]  は beautiful を示す根拠でありかつ [E2] は [n2]
        が beautifulであるという根拠である). *)
 
(* This permits us to _analyze_ any hypothesis of the form [beautiful
    n] to see how it was constructed, using the tactics we already
    know.  In particular, we can use the [induction] tactic that we
    have already seen for reasoning about inductively defined _data_
    to reason about inductively defined _evidence_.

    To illustrate this, let's define another property of numbers: *)
(** [beautiful n]という形をしたどのような仮説も、既に知っているタクティックを使用してそれがどのように構築されているかをこれまで見ることで、解析出来るようになります。特に帰納的に定義されたデータを扱うためにこれまでに使用してきた[induction]タクティックを帰納的に定義された根拠を論理的に考えることにも使えます。

これを確かめるために、もう一つ別の数の性質を定義してみましょう。
*)
Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** 練習問題 ★ (gorgeous_tree) *)
(* Write out the definition of [gorgeous] numbers using inference rule
    notation.
(** [gorgeous]数の定義をルールの記法を使用して書いてみましょう。*) 
(* FILL IN HERE *)
[]
*)


(** **** 練習問題 ★ (gorgeous_plus13) *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)

(*  It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)
(** 直感的に[gorgeous]と[beautiful]はわずかに違うルールを使用している表現されているけれども、実際は同じ数が真になるという意味において同じ性質であるように見えます。確かにこのことは証明出来ます。
*)	

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3". 
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.

(* Notice that the argument proceeds by induction on the _evidence_ [H]! *) 
(** この証明が根拠[H]による帰納法によって始まることに気をつけてください *)
(*  Let's see what happens if we try to prove this by induction on [n]
   instead of induction on the evidence [H]. *)
(**  もし根拠[H]による帰納法ではなく、[n]による帰納法で証明しようとすると何が起こるか見てみましょう。*)
Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* 詰った! *)
Abort.

(* The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)
(** ここで起る問題は、[n]についての帰納法を行うことは、役に立つ帰納法の仮定を生みださないことです。我々が興味を持っている性質が[n]の一つ前において(n = S n' と置いた時の。n'の時)どのように振る舞うかを知ることは,それが[n]について成り立つことを証明することの役に立ちません。代わりに我々は、帰納法の仮定が他の数について述べる帰納法の仮定を持てるようになることです。例えば、[n-3]や[n-5]のように。これは[gorgeous]のコンスタクタの形とぴったり合います。
*)

(** **** 練習問題 ★★ (gorgeous_sum) *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題 ★★★, advanced (beautiful__gorgeous) *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題 ★★★, optional (g_times2) *)
(* Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)
(** [g_times2]定理を[gorgeous__beautiful]を使用せずに証明しなさい。
    次の補題が役に立つかもしれません。*)
Lemma helper_g_times2 : forall x y z, x + (z + y)= z + x + y.
Proof.
   (* FILL IN HERE *) Admitted.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl. 
   induction H.
   (* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(* ** From Boolean Functions to Propositions *)
(** ** ブール型を返す関数から命題へ *)
(* In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even: *)
(** [Basics_J]の章において、与えられた数が偶数であればtrueを返却することでテストする[evenb]関数を定義しました。我々はこの関数を「ある数字[n]は偶数である」という命題を定義するために使用出来ます。*)
Definition even (n:nat) : Prop := 
  evenb n = true.

(* That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]."  
    Note that here we have given a name
    to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. This isn't a fundamentally
    new kind of proposition;  it is still just an equality. *)
(** すなわち、「[n]は偶数である」という意味の命題を「関数[evenb]に[n]が適用されたとき[true]を返却する。」という意味で定義することが出来ます。
命題に[Definition]を使用して、他の種類の式に名前を与えるのと同じように、名前を与えたことに注意してください。
これは基本的に、新しい種類の命題ではありません。単なる等式です。
*)

(* Another alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)
(** 他の方法として、偶数であるという概念を直接定義することも出来ます。
 [evenb]関数を経由して間接的に定義するかわりに、ある数が偶数であるという根拠を二つの異なった方法で提示することで、偶数という概念が何を意味するかを言うことが出来ます。*)
Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** This definition says that there are two ways to give
    evidence that a number [m] is even.  First, [0] is even, and
    [ev_0] is evidence for this.  Second, if [m = S (S n)] for some
    [n] and we can give evidence [e] that [n] is even, then [m] is
    also even, and [ev_SS n e] is the evidence. *)
(* この定義は、ある数[m]が偶数であるという根拠を与える二つの方法があることを述べています。一つめは、[0]は偶数であり、[ev_0]がその根拠になります。二つめは、もし、[m = S (S n)]となる[n]があり、[n]が偶数であるという根拠[e]を与えることが出来るならば、[m]は偶数であり、[ev_SS n e]が根拠になります。*)

(** **** 練習問題 ★ (double_even) *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* *** Discussion: Computational vs. Inductive Definitions *)
(** 議論: 計算 vs. 帰納的定義 *)
(* We have seen that the proposition "[n] is even" can be
    phrased in two different ways -- indirectly, via a boolean testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  These two ways of defining
    evenness are about equally easy to state and work with.  Which we
    choose is basically a question of taste.

    However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.  

    One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly into a Coq Fixpoint (or into a recursive
    function in any other common programming language).  We might be
    able to find a clever way of testing this property using a
    [Fixpoint] (indeed, it is not too hard to find one in this case),
    but in general this could require arbitrarily deep thinking.  In
    fact, if the property we are interested in is uncomputable, then
    we cannot define it as a [Fixpoint] no matter how hard we try,
    because Coq requires that all [Fixpoint]s correspond to
    terminating computations.

    On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)
(**これまで、「ある数が偶数である」という命題が二つの異った方法で表現されうることを見てきました。すなわち、
evenbを使用した間接的な方法と、 偶数であることの根拠を構成するものを帰納的に描写する直接的な方法とです。これらの二つの偶数であることを定義する方法は、ほとんど同じような表現で同じように機能します。どちらを選ぶかも、基本的には趣味の問題です。

しかし、興味深いほかの性質、例えば「テスト用の関数を書くのが難しかったり不可能だったりする」ようなことがあることを考えると、直接的な帰納的な定義のほうが好ましいと言えます。

そのような性質の一つは、たとえば[beautiful]です。これは数の集合の定義としてはなんの問題もありませんが、この定義をそのままCoqのFixPointに変換することはできません。(それだけでなく他の言語の再帰関数に変換することもできません。)[Fixpoint] を用いてこの性質をテストするうまい方法を見つけられるかもしれません。(実際のところ、この場合はそれほど難しいことではありません) しかし、一般的にこういうことをしようとすると、かなりあれこれ考える必要があるでしょう。
実際、Coqの [Fixpoint] は停止する計算しか定義できないので、定義しようとする性質が計算不能なものだった場合、どれだけがんばっても [Fixpoint] では定義できません。

    一方、性質 [beautiful] がどのようなものかの根拠を与える帰納的な定義を書くことは、非常に簡単です。
*)

(** **** 練習問題 ★ (ev__even) *)
(* Here is a proof that the inductive definition of evenness implies
    the computational one. *)
(**  ここに偶数性の帰納的な定義が計算的定義を包含するという定理があります。*)
Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0". 
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".  
    unfold even. apply IHE'.  
Qed.

(* Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)
(** この定理は [E]による帰納法の代わりに[n]による帰納法で証明出来るでしょうか？出来ないならなぜ出来ないでしょうか？*)
(* FILL IN HERE *)
(** [] *)

(* The induction principle for inductively defined propositions does
    not follow quite the same form as that of inductively defined
    sets.  For now, you can take the intuitive view that induction on
    evidence [ev n] is similar to induction on [n], but restricts our
    attention to only those numbers for which evidence [ev n] could be
    generated.  We'll look at the induction principle of [ev] in more
    depth below, to explain what's really going on. *)
(** 帰納的に定義された命題のための帰納法の原理は、帰納的に定義された集合のためのものと全く同じものではありません。今の段階では、根拠 [ev n] に対する帰納法は [n] に対する帰納法に似ているが、 [ev n] が成立する数についてのみ着目することができると直感的に理解しておいて問題ありません。 [ev] の帰納法の原理をもっと深く見て行き、実際に何を起こっているかを説明します。
*)
(** **** 練習問題 ★ (l_fails) *)
(** The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   Intuitively, we expect the proof to fail because not every
   number is even. However, what exactly causes the proof to fail?
*)
(** 次の証明はうまくいきません。
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
	直感的に全ての数字は偶数ではないために証明が失敗するだろうことは分かりますが、この証明が失敗している正確な原因はなんでしょうか？
(* FILL IN HERE *)
*)
(** [] *)

(** **** 練習問題 ★★ (ev_sum) *)
(* Here's another exercise requiring induction. *)
(** 帰納法を必要とする別の練習問題です。 *)
Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(* ** [Inversion] on Evidence *)
(** ** 根拠における[Inversion] *)
(* Another situation where we want to analyze evidence for evenness
    is when proving that, if [n] is even, then [pred (pred n))] is
    too.  In this case, we don't need to do an inductive proof.  The
    right tactic turns out to be [inversion].  *)
(** 「[n] が偶数ならば [pred(pred n)] も偶数である」という偶数に関する根拠を分析したいとします。このケースでは、帰納法による証明は必要ありません。使うべき正しいタクティックは[inversion]になります。
*)
Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** 練習問題 ★, optional (ev_minus2_n) *)
(* What happens if we try to use [destruct] on [n] instead of [inversion] on [E]? *)
(** [E]に関する[inversion]ではなく、[n]に関する[destruct]を使った場合、何が起こるでしょうか？ *)
(* FILL IN HERE *)
(** [] *)


(* Another example, in which [inversion] helps narrow down to
the relevant cases. *)
(** [inversion]が関連を絞り込むのに役に立つ別の例です。*)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  apply E'. Qed.

(* These uses of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    (You might also expect that [destruct] would be a more suitable
    tactic to use here. Indeed, it is possible to use [destruct], but 
    it often throws away useful information, and the [eqn:] qualifier
    doesn't help much in this case.)    

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)
(** このような [inversion] の使い方は最初はちょっと謎めいて思えるかもしれません。これまでは、 [inversion] は等号に関する命題に対して使い、コンストラクタから元のデータを取り出すためか、別のコンストラクタを区別するためににしか使っていませんでした。しかし、ここでは [inversion] が 帰納的に定義された命題に対する根拠を分析するためにも使えることを紹介しました。

( もしかしたら、[destruct]タクティックがもっとここで使うには相応しいと思うかもしれません。確かに、[destruct]を使用することは可能です。しかし、[destruct]は必要な情報をしばしば捨ててしまいますし、[eqn:]のような変数もここでは大して役に立ちません。)

ここで、[inversion] が一般にはどのように動作するかを説明します。 [I] が現在のコンテキストにおいて帰納的に宣言された仮定 [P] を参照しているとします。ここで、[inversion I] は、[P]のコンストラクタごとにサブゴールを生成します。 各サブゴールにおいて、 コンストラクタが [P] を証明するのに必要な条件によって [I] が置き換えられます。サブゴールのうちいくつかは矛盾が存在するので、 [inversion] はそれらを除外します。残っているのは、元のゴールが成り立つことを示すのに必要なサブゴールです。

 先ほどの例で、 [inversion] は [ev (S (S n))] の分析に用いられ、 これはコンストラクタ [ev_SS] を使って構築されていることを判定し、そのコンストラクタの引数を仮定に追加した新しいサブゴールを生成しました。(今回は使いませんでしたが、補助的な等式も生成しています。)
    このあとの例では、inversion のより一般的な振る舞いについて調べていきましょう。 *)
	
	
(** **** 練習問題 ★ (inversion_practice) *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.

(* The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)
(**  inversion タクティックは、仮定が矛盾していることを示し、ゴールを達成するためにも使えます。 *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題 ★★★, advanced (ev_ev__ev) *)
(* Finding the appropriate thing to do induction on is a
    bit tricky here: *)
(**  何に対して帰納法を行えばいいかを探しなさい。(ちょっとトリッキーですが)  *)
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題 ★★★, optional (ev_plus_plus) *)
(* Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. *)
(** 既存の補題を適用する必要のある練習問題です。 帰納法も場合分けも不要ですが、書き換えのうちいくつかはちょっと大変です。 Basics_J.v の plus_swap' で使った replace タクティックを使うとよいかもしれません。*)
Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)





(* ####################################################### *)
(* * Additional Exercises *)
(** * 追加練習問題 *)
(** **** 練習問題 ★★★★ (palindromes) *)
(* A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
    c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove that 
       forall l, pal (l ++ rev l).
    - Prove that 
       forall l, pal l -> l = rev l.
*)
(**  palindrome（回文）は、最初から読んでも逆から読んでも同じになるような シーケンスです。 
    - [list X] でパラメータ化され、それが palindrome であることを示すような帰納的命題 [pal] を定義しなさい。（ヒント：これには三つのケースが必要です。この定義は、リストの構造に基いたものとなるはずです。まず一つのコンストラクタ、
    c : forall l, l = rev l -> pal l
      は明らかですが、これはあまりうまくいきません。)
 
    - 以下を証明しなさい。
       forall l, pal (l ++ rev l).
    - 以下を証明しなさい。
       forall l, pal l -> l = rev l.
*)	   
(* FILL IN HERE *)
(** [] *)

(** **** 練習問題 ★★★★★, optional (palindrome_converse) *)
(* Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)
(**  一つ前の練習問題で定義した [pal] を使って、これを証明しなさい。
     forall l, l = rev l -> pal l.
*)
(* FILL IN HERE *)
(** [] *)

(** **** 練習問題 ★★★★, advanced (subsequence) *)
(* A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove that subsequence is reflexive, that is, any list is a
      subsequence of itself.  

    - Prove that for any lists [l1], [l2], and [l3], if [l1] is a
      subsequence of [l2], then [l1] is also a subsequence of [l2 ++
      l3].

    - (Optional, harder) Prove that subsequence is transitive -- that
      is, if [l1] is a subsequence of [l2] and [l2] is a subsequence
      of [l3], then [l1] is a subsequence of [l3].  Hint: choose your
      induction carefully!
*)
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
	
    -（これは少し難しいですので、任意とします）サブシーケンスという関係は推移的である、つまり、 [l1] が [l2] のサブシーケンスであり、 [l2] が [l3] のサブシーケンスであるなら、 [l1] は [l3] のサブシーケンスである、というような関係であることを証明しなさい。（ヒント：何について帰納法を適用するか、よくよく注意して下さい!）
*)
(* FILL IN HERE *)
(** [] *)


(** **** 練習問題 ★★, optional (R_provability) *)
(* Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)
(** Coq に次のような定義を与えたとします：
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    次のうち、証明可能なのはどの命題でしょうか？

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)
(** [] *)


(* $Date: 2013-07-01 18:48:47 -0400 (Mon, 01 Jul 2013) $ *)


