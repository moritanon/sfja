(* * Logic: Logic in Coq *)
(** * Logic_J: Coqにおける論理 *)

Require Export MoreCoq_J. 



(* Coq's built-in logic is very small: the only primitives are
    [Inductive] definitions, universal quantification ([forall]), and
    implication ([->]), while all the other familiar logical
    connectives -- conjunction, disjunction, negation, existential
    quantification, even equality -- can be encoded using just these.

    This chapter explains the encodings and shows how the tactics
    we've seen can be used to carry out standard forms of logical
    reasoning involving these connectives. *)
(** Coqにあらかじめ組み込まれた論理は極めて小さく、帰納的定義([Inductive])、全称量化([forall])、含意([->])だけがプリミティブです。しかしそれ以外の論理結合子（かつ、または、否定、存在量化子、等号など）も、組み込みのものを用いて定義できます。

    この章では、そのエンコーディング(Coqでどのように表現されるかということか？)を説明し、これまで見て来たタクティックが これらの結合子を含んだ論理的推論の標準形式を実行するためにどのように使用されるのかを示します。*)

(* ########################################################### *)
(* * Propositions *)
(** * 命題 *)

(* In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions 
    ([forall x, P]).  
*)
(** 以前の章で、事実の主張（命題）とそれらが真であるという証拠を表現する方法（証明）の多くの例を見てきました。とりわけ、e1 = e2という形の等価命題、P → Q という形の含意、そして、∀ x , P という量化命題を広く使用してきました。
*)
(* In Coq, the type of things that can (potentially) 
    be proven is [Prop]. *)
(** Coqにおいて、(潜在的に)証明されるものの型は、[Prop]です。*)

(* Here is an example of a provable proposition: *)
(** 証明可能な命題の例です。*)

Check (3 = 3).
(* ===> Prop *)

(* Here is an example of an unprovable proposition: *)
(** 次は、証明不可能な命題の例です。*)

Check (forall (n:nat), n = 2).
(* ===> Prop *)

(* Recall that [Check] asks Coq to tell us the type of the indicated 
  expression. *)
(** [Check]は、表示された表現の型をCoqに問い合わせて、我々に教えてくれるんでしたね。*)
(* ########################################################### *)
(* * Proofs and Evidence *)
(** 証明と根拠 *)
(* In Coq, propositions have the same status as other types, such as
    [nat].  Just as the natural numbers [0], [1], [2], etc. inhabit
    the type [nat], a Coq proposition [P] is inhabited by its
    _proofs_.  We will refer to such inhabitants as _proof term_ or
    _proof object_ or _evidence_ for the truth of [P]. 

    In Coq, when we state and then prove a lemma such as:

Lemma silly : 0 * 3 = 0.  
Proof. reflexivity. Qed.

    the tactics we use within the [Proof]...[Qed] keywords tell Coq
    how to construct a proof term that inhabits the proposition.  In
    this case, the proposition [0 * 3 = 0] is justified by a
    combination of the _definition_ of [mult], which says that [0 * 3]
    _simplifies_ to just [0], and the _reflexive_ principle of
    equality, which says that [0 = 0].
*)

(** Coqにおいて、命題は他の型と同じ状態を持ちます。例えば、[nat]のように。自然数の[0],[1],[2]などが[nat]型の世界に属するのと同じように、Coqの命題[P]は、その_証明_の世界に属しています。
[P]が真であるための_証明の項_、_証明オブジェクト_や_根拠_のような住人について見ていくことにしましょう。
  
Coqにおいて、補題を証明するときには、以下のように書きます。

Lemma silly : 0 * 3 = 0.
Proof. reflexivity. Qed.

   我々が[Proof]...[Qed]キーワードの間に使用するタクティックはCoqに命題が連続する証明をどのように構築するかを伝えます。   この場合、命題[0 * 3 = 0]は [0 * 3]は_簡約_の結果0であるとする[mult]の定義と[0 = 0]であるとする_反射的_な同値性の原理の合わせ技で正当化されます。
*)

(** *** *)

Lemma silly : 0 * 3 = 0.
Proof. reflexivity. Qed.

(* We can see which proof term Coq constructs for a given Lemma by
using the [Print] directive: *)
(** [Print]ディレクティブを使用すると、LemmaとしてCoqが構築した証明term?を見ることが出来ます。
*)
Print silly.
(* ===> silly = eq_refl : 0 * 3 = 0 *)

(* Here, the [eq_refl] proof term witnesses the equality. (More on equality later!)*)
(** この[eq_refl」は同値性を証明する証明termです。 (同値性について詳しくは後述!)*)

(* ** Implications _are_ functions *)
(** ** 含意_は_関数なのです *)
(* Just as we can implement natural number multiplication as a
function:
[
mult : nat -> nat -> nat 
]

The _proof term_ for an implication [P -> Q] is a _function_ that
takes evidence for [P] as input and produces evidence for [Q] as its output.
*)     
(** ここで、自然数のかけ算を関数として実装してみましょう 
[
mult : nat -> nat -> nat
]
[P -> Q]という含意を表す_項_は、[P]のための根拠を入力としてとり、出力としてQの根拠を生成する_関数_なのです。
*)

Lemma silly_implication : (1 + 1) = 2  ->  0 * 3 = 0.
Proof. intros H. reflexivity. Qed.

(* We can see that the proof term for the above lemma is indeed a
function: *)
(** 上記補題の proof termが確かに関数であることが分かります: *)

Print silly_implication.
(* ===> silly_implication = fun _ : 1 + 1 = 2 => eq_refl
     : 1 + 1 = 2 -> 0 * 3 = 0 *)

(* ** Defining Propositions *)
(** 命題を定義するということ *)

(* Just as we can create user-defined inductive types (like the
    lists, binary representations of natural numbers, etc., that we
    seen before), we can also create _user-defined_ propositions.

    Question: How do you define the meaning of a proposition?  
*)
(**
ユーザ定義の再帰的な型(これまでに見てきたlistや自然数のバイナリ表記のような)を作ることが出来るように、
_ユーザ定義の_命題もまた作ることが出来ます。

問題：命題の意味はどうやって定義するのでしょうか？
*)

(** *** *)

(* The meaning of a proposition is given by _rules_ and _definitions_
    that say how to construct _evidence_ for the truth of the
    proposition from other evidence.

    - Typically, rules are defined _inductively_, just like any other
      datatype.

    - Sometimes a proposition is declared to be true without
      substantiating evidence.  Such propositions are called _axioms_.  


    In this, and subsequence chapters, we'll see more about how these
    proof terms work in more detail.
*)

(** 命題の意味は命題の正しさのための根拠を他の根拠からどのように構築するかを述べる_規則_と_定義_によって与えられます。

  - 典型的に、規則は他のデータ型と同じように、_帰納的に_定義されます。

  - 時々、命題は、 具体的な根拠なしに宣言されます。そのような命題は、_公理_と呼ばれます。
  
  これからの章において、これらの証明termが細かい点においてどのように働くかを見ていくことにしましょう
  *)
(* ########################################################### *)
(* * Conjunction *)
(** * 論理積、連言（Conjunction、AND） *)

(*  The logical conjunction of propositions [P] and [Q] can be
    represented using an [Inductive] definition with one
    constructor. *)
(** 命題 [P] と [Q] の論理積（ [logical conjunction] ）は、コンストラクタを一つしか持たない [Inductive] を使った定義で表せます。 *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

(* The intuition behind this definition is simple: to
    construct evidence for [and P Q], we must provide evidence
    for [P] and evidence for [Q].  More precisely:

    - [conj p q] can be taken as evidence for [and P Q] if [p]
      is evidence for [P] and [q] is evidence for [Q]; and

    - this is the _only_ way to give evidence for [and P Q] --
      that is, if someone gives us evidence for [and P Q], we
      know it must have the form [conj p q], where [p] is
      evidence for [P] and [q] is evidence for [Q]. 

   Since we'll be using conjunction a lot, let's introduce a more
   familiar-looking infix notation for it. *)

(** この定義の内容を直感的に理解するのに、そうややこしく考える必要はありません。[and P Q] に根拠を与えるには、[P] の根拠と [Q] の根拠が必要だということです。もっと精確に言えば、

    - もし [p] が [P] の根拠で、[q] が [Q] の根拠であるなら、[conj p q] を [and P Q] の根拠とすることができる。

    - これは [and P Q] に根拠を与える唯一の方法であること、即ち、もし [and P Q] の根拠が与えられたならば、その根拠が [conj p q] の形をしており、さらに [p] が [P] の根拠であることと[q] が [Q] の根拠であることがわかるということです。

   今後論理積をよく使うことになるので、もっと馴染みのある、中置記法を導入することにしましょう。 *)

Notation "P /\ Q" := (and P Q) : type_scope.

(*  (The [type_scope] annotation tells Coq that this notation
    will be appearing in propositions, not values.) *)
(** （[type_scope] という注釈は、この記法が値にではなく、命題に現れるものであることを、Coqに伝えています。） *)

(* Consider the "type" of the constructor [conj]: *)
(** コンストラクタ [conj] の型はどのようなものか考えてみましょう。 *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(* Notice that it takes 4 inputs -- namely the propositions [P]
    and [Q] and evidence for [P] and [Q] -- and returns as output the
    evidence of [P /\ Q]. *)
(** conjが四つの引数（ [P] 、[Q] という命題と、[P] 、[Q] の根拠）をとることに注目して下さい。 *)

(* Besides the elegance of building everything up from a tiny
    foundation, what's nice about defining conjunction this way is
    that we can prove statements involving conjunction using the
    tactics that we already know.  For example, if the goal statement
    is a conjuction, we can prove it by applying the single
    constructor [conj], which (as can be seen from the type of [conj])
    solves the current goal and leaves the two parts of the
    conjunction as subgoals to be proved separately. *)
(**
    基本的なことから色々なことを組み立てていくエレガントさはさておき、
    このような方法でconjunctionを定義することの利点は、これを含む
    文を、既に知っているタクティックで証明できることです。
    例えば、もしゴールが論理積を含んでいる場合、このたった一つの
    コンストラクタ[conj]を適用するだけで証明できます。
    それは、[conj]の型を見ても分かるように現在のゴールを解決してから
    conjunctionの二つの部分を別々に証明するべきサブゴールにします。
 *)


Theorem and_example : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  apply conj.
  Case "left". reflexivity.
  Case "right". reflexivity.  Qed.


(* Just for convenience, we can use the tactic [split] as a shorthand for
    [apply conj]. *)
(** [apply conj] とするかわりに [split] タクティックでも同じことができます。便利ですね。 *)

Theorem and_example' : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  split.
    Case "left". reflexivity.
    Case "right". reflexivity.  Qed.

(* ** "Eliminating" conjunctions *) 
(** ** 論理積を"取り除く"ということ *)
(* Conversely, the [inversion] tactic can be used to take a
    conjunction hypothesis in the context, calculate what evidence
    must have been used to build it, and add variables representing
    this evidence to the proof context. *)
(** 逆に、[inversion] タクティックを、コンテキストにある論理積の形をした仮定に使うことで、それの構築に使われた根拠を取り出し、コンテキストに加えることができます。 *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  apply HP.  Qed.

(** **** 練習問題: ★, optional (proj2) *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HP HQ]. 
  split.  
    Case "left". apply HQ. 
    Case "right". apply HP.  Qed.
  

(** **** 練習問題: ★★ (and_assoc) *)
(* In the following proof, notice how the _nested pattern_ in the
    [inversion] breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP: P], [HQ : Q], and [HR : R].  Finish the proof from there: *)
(** 次の証明では、[inversion]が、入れ子構造になった命題[H : P /\ (Q /\ R)]をどのように[HP: P], [HQ : Q], [HR : R] に分解するか、という点に注意しながら証明を完成させなさい。*)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(* ** Iff *)
(** ** Iff （両含意）*)

(* The handy "if and only if" connective is just the conjunction of
    two implications. *)
(** この、"if and only if（～である時、その時に限り）" で表される「両含意」という論理は馴染みのあるもので、次の二つの「ならば（含意）」をandでつないだものです。*)
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. 
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

(** **** 練習問題: ★, optional (iff_properties) *)
(*  Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)
(** 上の、 [<->] が対称であることを示す証明 ([iff_sym]) を使い、それが反射的であること、推移的であることを証明しなさい。*)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *) Admitted.

(*  Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)
(** ヒント: もしコンテキストに iff を含む仮定があれば、[inversion] を使ってそれを二つの含意の式に分割することができます。(なぜそうできるのか考えてみましょう。) *)
(** [] *)

(*  Some of Coq's tactics treat [iff] statements specially, thus
    avoiding the need for some low-level manipulation when reasoning
    with them.  In particular, [rewrite] can be used with [iff]
    statements, not just equalities. *)
(** Coqのいくつかのタクティックは、証明の際に低レベルな操作を避けるため[iff] を特別扱いします。 特に [rewrite] を [iff] に使うと、単なる等式以上のものとして扱ってくれます。 *)

(* ############################################################ *)
(* * Disjunction (Logical "or") *)
(** * 論理和、選言（Disjunction、OR） *)

(*  ** Implementing disjunction *)
(** ** 論理和の実装 *)
(*  Disjunction ("logical or") can also be defined as an
    inductive proposition. *)
(** 論理和（Disjunction、OR）も、帰納的な命題として定義できます。 *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

(** Consider the "type" of the constructor [or_introl]: *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(*  It takes 3 inputs, namely the propositions [P], [Q] and
    evidence of [P], and returns, as output, the evidence of [P \/ Q].
    Next, look at the type of [or_intror]: *)
(** このコンストラクタは三つの入力（ [P]、[Q] と名付けられた命題に加え、[P] の根拠）を引数にとり、[P /\ Q] の根拠を返します。次に、[or_intror] の型を見てみましょう。 *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(*  It is like [or_introl] but it requires evidence of [Q]
    instead of evidence of [P]. *)
(** ほとんど [or_introl] と同じように見えますが、[P] ではなく [Q] の根拠が要求されています。*)

(* Intuitively, there are two ways of giving evidence for [P \/ Q]:

    - give evidence for [P] (and say that it is [P] you are giving
      evidence for -- this is the function of the [or_introl]
      constructor), or

    - give evidence for [Q], tagged with the [or_intror]
      constructor. *)
(** 直観的には、命題 [P \/ Q] に根拠を与える方法は二つあることがわかります。

    - [P] の根拠を与える。（そしてそれが [P] の根拠であることを伝える。これがコンストラクタ [or_introl] の機能です）か、

    - [Q] の根拠をコンストラクタ [or_intror] に与える。 *)

(*  Since [P \/ Q] has two constructors, doing [inversion] on a
    hypothesis of type [P \/ Q] yields two subgoals. *)
(**  [P \/ Q] は二つのコンストラクタを持っているので、 [P \/ Q] の形の仮定に[inversion] を適用すると二つのサブゴールが生成されます。*)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

(** From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)
(** 次のように、[apply or_introl] 、 [apply or_intror] の代わりに [left] 、[right] という短縮版のタクティックを使うこともできます。*)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ.  Qed.





Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. inversion H as [HP | [HQ HR]]. 
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(** **** 練習問題: ★★ (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★, optional (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################### *)
(* ** Relating [/\] and [\/] with [andb] and [orb] (advanced) *)
(** ** [/\] 、 [\/] の[andb] 、[orb] への関連付け *)

(*  We've already seen several places where analogous structures
    can be found in Coq's computational ([Type]) and logical ([Prop])
    worlds.  Here is one more: the boolean operators [andb] and [orb]
    are clearly analogs of the logical connectives [/\] and [\/].
    This analogy can be made more precise by the following theorems,
    which show how to translate knowledge about [andb] and [orb]'s
    behaviors on certain inputs into propositional facts about those
    inputs. *)
(** 我々はすでに、Coqの計算における型([Type]) と論理の命題 ([Prop]) との類似性について見てきました。ここではもう一つ、bool 型を扱う [andb] と[orb] が、[/\] と [\/] とのつながりともいうべきある種の類似性を持っていることに触れましょう。この類似性は、次の定理を見ればもっとはっきりします。これは、[andb] や [orb] が、ある入力に対する振る舞いを、その入力に対する命題にどのように変換するかを示したものです。*)
Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

(** **** 練習問題: ★★, optional (bool_prop) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  (* FILL IN HERE *) Admitted.

(** **** 練習問題: ★★, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** 練習問題: ★★, optional (orb_false_elim)  *)
Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ################################################### *)
(*  * Falsehood *)
(** * 偽であるということ *)
(* Logical falsehood can be represented in Coq as an inductively
    defined proposition with no constructors. *)
(** 論理学でいうところの「偽」は、Coqでは「帰納的に定義されてはいるがコンストラクタを一つも持たない命題」として定義されています。*)

Inductive False : Prop := . 

(*  Intuition: [False] is a proposition for which there is no way
    to give evidence. *)
(** 直観的な理解: [False] は、根拠を示す方法を一つも持たない命題 *)


(*  Since [False] has no constructors, inverting an assumption
    of type [False] always yields zero subgoals, allowing us to
    immediately prove any goal. *)
(** [False] にはコンストラクタがないので、[False] の意味するところのものを反転（invert）してもサブゴールが生成されません。このことはつまり、「偽」からはどんなゴールも証明できる、ということです。*)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(* How does this work? The [inversion] tactic breaks [contra] into
    each of its possible cases, and yields a subgoal for each case.
    As [contra] is evidence for [False], it has _no_ possible cases,
    hence, there are no possible subgoals and the proof is done. *)
(** これはどういうことでしょうか？ [inversion] タクティックは仮定 [contra] をその取りうるケースに分解し、それぞれにサブゴールを生成します。ここで[contra] が [False] の根拠となっているため、そこから取りうるケースは存在しません。このため、証明に値するサブゴールがなくなり、そこで証明が終わってしまうのです。*)

(** *** *)
(*  Conversely, the only way to prove [False] is if there is already
    something nonsensical or contradictory in the context: *)
(** 逆に、[False] を証明する唯一の方法は、コンテキストに何か矛盾がないかを探すことです。*)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(*  Actually, since the proof of [False_implies_nonsense]
    doesn't actually have anything to do with the specific nonsensical
    thing being proved; it can easily be generalized to work for an
    arbitrary [P]: *)
(** 実際、 [False_implies_nonsense] の証明は、特定の意味を持つ証明すべきことを何も持っていないので、任意の [P] に対して簡単に一般化できます。 *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra.  Qed.

(*  The Latin _ex falso quodlibet_ means, literally, "from
    falsehood follows whatever you please."  This theorem is also
    known as the _principle of explosion_. *)
(** ラテン語の 「_ex falso quodlibet_ 」は、文字通り「偽からはあなたの望むものすべてがもたらされる」というような意味です。この定理は、「 _principle of explosion_ 」としても知られています。 *)

(* #################################################### *)
(*  ** Truth *)
(** ** 真であるということ *)

(*  Since we have defined falsehood in Coq, one might wonder whether
    it is possible to define truth in the same way.  We can. *)
(** Coqで「偽」を定義することができたので、同じ考え方で「真」を定義することができるか、ということが次の関心事になります。もちろん、その答えは「Yes」です。 *)

(** **** 練習問題: ★★, advanced (True) *)
(*  Define [True] as another inductively defined proposition.  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.) *)
(** [True] を、帰納的な命題として定義しなさい。（直観的には [True] はただ当たり前のように根拠を示される命題であるべきです。） *)
(* FILL IN HERE *)
(** [] *)

(* However, unlike [False], which we'll use extensively, [True] is
    used fairly rarely. By itself, it is trivial (and therefore
    uninteresting) to prove as a goal, and it carries no useful
    information as a hypothesis. But it can be useful when defining
    complex [Prop]s using conditionals, or as a parameter to 
    higher-order [Prop]s. *)
(** しかしながら、[False] とは違い、広い意味で解釈すると [True] には理論的な意味で奇妙なところがあります。ゴールの証明に使うには当たり前すぎ（それゆえつまらない）、仮定として有意義な情報を与えてくれないのです。しかし条件文や、高階の[Prop]をパラメータで含む複雑な[Prop]を定義するときには役に立つこともあります) *)

(* #################################################### *)
(* * Negation *)
(** * 否定 *)

(** The logical complement of a proposition [P] is written [not
    P] or, for shorthand, [~P]: *)
(** 命題 [P] の論理的な補集合というべきものは、 [not P] もしくは短縮形として[~P] と表されます。 *)

Definition not (P:Prop) := P -> False.

(** The intuition is that, if [P] is not true, then anything at
    all (even [False]) follows from assuming [P]. *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(*  It takes a little practice to get used to working with
    negation in Coq.  Even though you can see perfectly well why
    something is true, it can be a little hard at first to get things
    into the right configuration so that Coq can see it!  Here are
    proofs of a few familiar facts about negation to get you warmed
    up. *)
(** Coqで否定を扱えるようになるにはある程度慣れが必要です。たとえ何かがどう見ても真に思える場合でも、そのことをCoqに納得させるのは最初のうちはなかなか大変です。ウォームアップのつもりで、否定のに関する馴染みのある定理を取り上げてみましょう。 *)

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** 練習問題: ★★, advanced (double_neg_inf) *)
(* Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
*)
(** [double_neg] の非形式的な証明を書きなさい。:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
(* FILL IN HERE *)
   []
*)

(** **** 練習問題: ★★ (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★ (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★, advanced (informal_not_PNP) *)
(*  Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)
(** 命題 [forall P : Prop, ~(P /\ ~P)] の形式的でない証明を（英語で）書きなさい。 *)
(* FILL IN HERE *)
(** [] *)

(* Constructive logic *)
(** 構成的論理 ? Constructive logic *)
(*  Note that some theorems that are true in classical logic are _not_
    provable in Coq's (constructive) logic.  E.g., let's look at how
    this proof gets stuck... *)
(** このうちいくつかは、古典論理ではtrueと判断できるにもかかわらず、Coqの(構成上の)論理では証明できないものがあるので注意が必要です。例えば、この証明がどのように詰まるかを見てみましょう。 *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H. 
  (* どうなっているのでしょうか？ [P] の証明に必要な根拠をどうしても編み出すことができません。 *)
  (* But now what? There is no way to "invent" evidence for [~P] 
     from evidence for [P]. *) 
  Abort.

(** **** 練習問題: ★★★★★, advanced, optional (classical_axioms) *)
(*  For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)
(**  さらなる挑戦を求める人のために、 Coq'Art book (p. 123) から一つ練習問題を
    取り上げてみます。次の五つの文は、よく「古典論理の特性」と考えられている
    もの（Coqにビルトインされている構成的論理の対極にあるもの）です。
    これらをCoqで証明することはできませんが、古典論理を使うことが必要なら、
    矛盾なく「証明されていない公理」として道具に加えることができます。
    これら五つの命題が等価であることを証明しなさい。 *)


Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 

(* FILL IN HERE *)
(** [] *)

(** **** **** 練習問題: ★★★ (excluded_middle_irrefutable) *)
(* This theorem implies that it is always safe to add a decidability
axiom (i.e. an instance of excluded middle) for any _particular_ Prop [P].
Why? Because we cannot prove the negation of such an axiom; if we could,
we would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)
(** この定理は、決定可能な公理(たとえば、排中律のような)を任意の_部分_命題[P]として、いつでも安全につけくわえることが出来ることを意味しています。 
どうしてそんなことが可能であるかと言えば、我々はそのような公理の否定命題を証明出来ないためです; もしそれが可能であるとすると、[~ (P \/ ~P)] と [~ ~ (P \/ ~P)]の両方を持つことが出来てしまいますが、これは矛盾です。*)
Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).  
Proof.
  (* FILL IN HERE *) Admitted.


(* ########################################################## *)
(* ** Inequality *)
(** ** 不等であるということ*)

(*  Saying [x <> y] is just the same as saying [~(x = y)]. *)
(** [x <> y] というのは、[~(x = y)] と同じことです。 *)

Notation "x <> y" := (~ (x = y)) : type_scope.

(*  Since inequality involves a negation, it again requires
    a little practice to be able to work with it fluently.  Here
    is one very useful trick.  If you are trying to prove a goal
    that is nonsensical (e.g., the goal state is [false = true]),
    apply the lemma [ex_falso_quodlibet] to change the goal to
    [False].  This makes it easier to use assumptions of the form
    [~P] that are available in the context -- in particular,
    assumptions of the form [x<>y]. *)
(** 不等性は、その中に「否定」を含んでいるため、やはりその扱いには
    ある程度の慣れが必要です。ここで一つ有用なトリックをお見せしましょう。
    もし、証明すべきゴールがあり得ない式（例えば[false = true]というような文）
    であった場合は、[ex_falso_quodlibet] という補題をapplyで適用すると、ゴールを
    [False]にすることができます。このことを覚えておけば、コンテキストの中の [~P]
    という形の仮定を使うことがとても簡単になります。特に、[x<>y] という形の仮定の
    場合はに有用です。 *)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.


(** *** *)

(** *** *)

(** *** *)

(** *** *)

(** *** *)

(** **** 練習問題: ★★ (false_beq_nat) *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, optional (beq_nat_false) *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

