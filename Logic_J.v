(** * Logic_J: Coqにおける論理 *)
(** * Logic: Logic in Coq *)

Require Export MoreProp_J. 

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
(* * Conjunction *)
(** * 論理積、連言（Conjunction、AND） *)

(*  The logical conjunction of propositions [P] and [Q] can be
    represented using an [Inductive] definition with one
    constructor. *)
(** 命題 [P] と [Q] の論理積（ [logical conjunction] ）は、コンストラクタを一つしか持たない [Inductive] を使った定義で表せます。 *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

(* Note that, like the definition of [ev] in a previous
    chapter, this definition is parameterized; however, in this case,
    the parameters are themselves propositions, rather than numbers. *)
(** 注意してほしいのは、前の章で取り上げた関数 [ev] の定義と同様に、
    この定義もパラメータ化された命題になっていることです。ただしこの場合はパラメータ
    自身も数値ではなく命題です。 *)

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
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
  Case "left". apply b_0.
  Case "right". apply b_3.  Qed.

(* Just for convenience, we can use the tactic [split] as a shorthand for
    [apply conj]. *)
(** [apply conj] とするかわりに [split] タクティックでも同じことができます。便利ですね。 *)

Theorem and_example' : 
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.  Qed.

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

(** **** 練習問題: ★★ (even__ev) *)
(** Now we can prove the other direction of the equivalence of [even]
   and [ev], which we left hanging in chapter [Prop].  Notice that the
   left-hand conjunct here is the statement we are actually interested
   in; the right-hand conjunct is needed in order to make the
   induction hypothesis strong enough that we can carry out the
   reasoning in the inductive step.  (To see why this is needed, try
   proving the left conjunct by itself and observe where things get
   stuck.) *)
(** 今度は、前の章で棚上げしていた [even] と [ev] の等価性をが別の方向から証明してみましょう。ここで左側のandは我々が実際に注目すべきものです。右のandは帰納法の仮定となって帰納法による証明に結びついていくことになるでしょう。なぜこれが必要となるかは、左側のandをそれ自身で証明しようとして、行き詰まってみると分かるでしょう。
 *)

Theorem even__ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  (* ヒント: nに帰納法を使います. *)
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
(* * Disjunction *)
(** * 論理和、選言（Disjunction、OR） *)

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

Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  (* FILL IN HERE *) Admitted.

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
(** [True] を、帰納的な命題として定義しなさい。あなたの定義に対してCoqはどのような帰納的原理を生成してくれるでしょうか。 （直観的には [True] はただ当たり前のように根拠を示される命題であるべきです。） *)
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

Theorem five_not_even :  
  ~ ev 5.
Proof. 
  (* WORKED IN CLASS *)
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn]. 
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.  Qed.

(** **** 練習問題: ★ (ev_not_ev_S) *)
(* Theorem [five_not_even] confirms the unsurprising fact that five
    is not an even number.  Prove this more interesting fact: *)
(** 定理 [five_not_even] は、「５は偶数ではない」というようなとても当たり前の事実を確認するものです。今度はもう少し面白い例です。 *)
Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  unfold not. intros n H. induction H. (* not n! *)
  (* FILL IN HERE *) Admitted.
(** [] *)

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

(** **** 練習問題: ★★, optional (ble_nat_false) *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)




(* ############################################################ *)
(*  * Existential Quantification *)
(** * 存在量化子 *)

(*  Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)
(** もう一つの論理的接続詞は、存在量化子（ _existential
    quantification_ ）です。これは、次のような定義でその意味を
    とらえることができます。 *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)

(** この [ex] は、型引数 [X] とそれに関する属性 [P] によって決まる命題です。「 [P] を満たす [x] が存在する」という主張に根拠を与えるため、ある特定の値 [x] （「証拠」と呼ぶことにします）を具体的に示すことで[P x] の根拠を得ることができます。つまりこれは、 [x] が性質  [P] を持っていることの根拠です。 *)

(*  Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)
(** Coqの容易な表記法[Notation]は、存在量化された命題を記述するための、より馴染みやすい表記を、ビルトインされたを全称量化子と同レベルで実現しています。そのおかげで、「偶数となる自然数が存在する」ことを示す命題を [ex nat ev] と書く代わりに、たとえば [exists x:nat, ev x] のように書くことができます。（これを理解するためにCoqの「表記法」がどのように作用しているかを完全に理解しないといけない、ということではありません。） *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(*  We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)
(** 存在を示す必要がある場合には、だいたいいつも同じようなタクティックの組み合わせが使われます。例えば、ある値の存在を証明する場合には、その値をコンストラクタ [ex_intro] に [apply] すればいいのです。[ex_intro] の前提はその結論に現れないうような変数（これが「証拠」となります）を必要とするため、[apply] を使用する際にはその値をきちんと提示することが必要になります。 *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(*  Note that we have to explicitly give the witness. *)
(** ここで具体的な値を証拠として用意する必要があることに注意してください。 *)

(*  Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)
(** [apply ex_intro with (witness:=e)] と書く代わりに、短縮形として [exists e]と記述することもできます。どちらも同じ意味です。 *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(*  Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
(** 逆に、コンテキストに置かれた仮定の中に存在を示すものがある場合は、それを [inversion] タクティックで取り除くことができます。変数に名前を付けるため [as...] パターンを使っていることに注目してください。Coqはそれを「証拠」につける名前とし、仮定が証拠を保持する根拠をそこから得ます。 （名前をきちんと選ばないと、Coqはそれを単なる証拠としか考えることができず、その先の証明で混乱してしまいます。） *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 

(** **** 練習問題: ★, optional (english_exists) *)
(*  In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
    mean? *)
(** 英語では、以下の命題は何を意味しているでしょうか？
      ex nat (fun n => ev (S n))
 *)
(* FILL IN HERE *)

(** **** 練習問題: ★ (dist_not_exists) *)
(* Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)
(** "全ての [x] について[P] が成り立つ" ならば " [P] を満たさない [x] は存在しない" ということを証明しなさい。 *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★, optional (not_exists_dist) *)
(* (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)
(** 一方、古典論理の「排中律（law of the excluded middle）」が必要とされる場合もあります。 *)
Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★ (dist_exists_or) *)
(* Prove that existential quantification distributes over
    disjunction. *)
(** 存在量化子が論理和において分配法則を満たすことを証明しなさい。 *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)

(* Print dist_exists_or. *)


(* ###################################################### *)
(* * Equality *)
(** * 等しいということ（同値性） *)

(* Even Coq's equality relation is not built in.  It has (roughly)
    the following inductive definition. *)
(** Coqには、等価という関係すら組み込まれていません。次のように(だいたいな感じで)帰納的に定義します。*)
(* (We enclose the definition in a module to avoid confusion with the
    standard library equality, which we have used extensively
    already.) *)
(** （ここではこれまで散々使った標準ライブラリでの定義と衝突すること
    を防ぐために、モジュールの中で定義することにします。） *)

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
  refl_equal : forall x, eq x x.
(*  Standard infix notation: *)
(** 次に定義するのは、標準的な中置記法です*)
Notation "x = y" := (eq x y) 
                    (at level 70, no associativity) 
                    : type_scope.

(* The definition of [=] is a bit subtle.  The way to think about it
    is that, given a set [X], it defines a _family_ of propositions
    "[x] is equal to [y]," indexed by pairs of values ([x] and [y])
    from [X].  There is just one way of constructing evidence for
    members of this family: applying the constructor [refl_equal] to a
    type [X] and a value [x : X] yields evidence that [x] is equal to
    [x]. *)
(** この[=]の定義は少し難解かもしれません。これがどういうものかを考えると、集合 [X] が与えられると、「集合 [X] に属する値 ([x] and [y]) にインデックスされた、[x] は [y] に等しい」というような命題の _集団_ を定義してくれるということです。この集団に属する命題に根拠を与えるためには、一つの方法しかありません。それは、コンストラクタ [refl_equal] に型 [X] とその値[x : X] を適用し、[x] が [x] と等しいという根拠を生成することです。 *)


(** **** 練習問題: ★★ (leibniz_equality) *)
(* The inductive definitions of equality corresponds to _Leibniz equality_: 
   what we mean when we say "[x] and [y] are equal" is that every 
   property on [P] that is true of [x] is also true of [y].  *)
(** "leibniz equality"に対応する帰納的な等価性の定義: 我々が[x]と[y]が等しいと言うときに意味していることは、[x]においてtrueとなる[P]についての全ての性質は、[y]においてもtrueになる。ということです。 *)
Lemma leibniz_equality : forall (X : Type) (x y: X), 
 x = y -> forall P : X -> Prop, P x -> P y.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(*  We can use
    [refl_equal] to construct evidence that, for example, [2 = 2].
    Can we also use it to construct evidence that [1 + 1 = 2]?  Yes:
    indeed, it is the very same piece of evidence!  The reason is that
    Coq treats as "the same" any two terms that are _convertible_
    according to a simple set of computation rules.  These rules,
    which are similar to those used by [Eval compute], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.
*)
(** [refl_equal] は [2 = 2] というような証明に根拠を与えることに使えます。 [1 + 1 = 2] はどうでしょうか？ 答えは Yes です。実際、これらは証明としてはほとんど同じようなものだと言えます。 その理由は Coq が二つの式がシンプルな計算ルールによって交換可能であることをを示し、それを"同値である"として処理しているからです。このルールは [Eval simpl] と同じものです。ただしこれには、関数適用の評価、定義のインライン化、[match] の簡約が含まれています。*)

Lemma four: 2 + 2 = 1 + 3. 
Proof.
  apply refl_equal. 
Qed.

(* The [reflexivity] tactic that we have used to prove equalities up
to now is essentially just short-hand for [apply refl_equal]. *)
(** 我々がこれまでに等価性を証明するために使用してきた[reflexivity]タクティックは本質的には[apply refl_equal]の適用にすぎません。 *)
End MyEquality.


(* ###################################################### *)
(* * Evidence-carrying booleans. *)
(** ブール値を保持する根拠 *)

(** So far we've seen two different forms of equality predicates:
[eq], which produces a [Prop], and
the type-specific forms, like [beq_nat], that produce [boolean]
values.  The former are more convenient to reason about, but
we've relied on the latter to let us use equality tests 
in _computations_.  While it is straightforward to write lemmas
(e.g. [beq_nat_true] and [beq_nat_false]) that connect the two forms,
using these lemmas quickly gets tedious. 

It turns out that we can get the benefits of both forms at once 
by using a construct called [sumbool]. *)
(**今までのところ、二つの異なった形式の等価性を示す述語を見てきました。
命題を生成する [eq]と、[beq_nat]のような、ブール値を生成する、それぞれの型に固有のやり方とです。前者は推論するには便利ですが、計算機で等価性のテストをするにはこれまで後者が頼りになってきました。二つの文をつなげる補題(例として[beq_nat_true]や[beq_nat_false])を書くのは簡単である一方、これらの補題を使用することは、すぐに面倒になります。

sumboolと呼ばれるコンストラクトを使うと、両方の形式を同時に使うことにも利便性があることが分かります。
*)
Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(*  Think of [sumbool] as being like the [boolean] type, but instead
of its values being just [true] and [false], they carry _evidence_
of truth or falsity. This means that when we [destruct] them, we
are left with the relevant evidence as a hypothesis -- just as with [or].
(In fact, the definition of [sumbool] is almost the same as for [or].
The only difference is that values of [sumbool] are declared to be in
[Set] rather than in [Prop]; this is a technical distinction 
that allows us to compute with them.) *) 
(** 単純な[true]や[false]の値としてではなく、[boolean]型と似たものとして[sumbool]をとらえると、それは真であることや偽であることの根拠を導きます。この意味は、我々が、[sumbool]を[destruct]したとき、仮説として関連性のある根拠を持ち続けられる、ということです。ちょうど[or]のように。
(実際、[sumbool]の定義は[or]とほとんど同じです。違う点はただ、[sumbool]の値が[Prop]の中よりむしろ[Set]の中で宣言されている、ということだけです。このことは、それらを使って我々がどのように計算するかについての技術的な違いにすぎません。) *)

(* Here's how we can define a [sumbool] for equality on [nat]s *)
(** [nat]の等価性のために[sumbool]をどのように定義するかを示します。*)
Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 

(** Read as a theorem, this says that equality on [nat]s is decidable:
that is, given two [nat] values, we can always produce either 
evidence that they are equal or evidence that they are not.
Read computationally, [eq_nat_dec] takes two [nat] values and returns
a [sumbool] constructed with [left] if they are equal and [right] 
if they are not; this result can be tested with a [match] or, better,
with an [if-then-else], just like a regular [boolean]. 
(Notice that we ended this proof with [Defined] rather than [Qed]. 
The only difference this makes is that the proof becomes _transparent_,
meaning that its definition is available when Coq tries to do reductions,
which is important for the computational interpretation.)

Here's a simple example illustrating the advantages of the [sumbool] form. *)
(** 定理として見ると、これは[nat]についての等価性は決定可能であることを示しています。すなわち二つの[nat]の値が与えられたら、われわれは常に二つの値が等しいかそうでないかどちらかの根拠を提示することが出来るということです。計算機的に読むと、[eq_nat_dec]は二つの[nat]の値を引数にとり、二つの値が等しければ、[left]によって構築された、あるいは等しくないならば、[right]によって構築された[sumbool]を返却します。この結果は[match]によってテストすることが出来ます。あるいはもっといい方法として、[if-then-else]を用いてテストすることが通常の[boolean]と同じように出来ます。( この証明を[Qed]ではなく、[Defined]を用いて終らせていることに注意してください。このことで発生する唯一の違いは、証明が透明になるということです。その意味は、Coqが計算機的な解釈のために重要な縮小を行おうとしたときにその定義を使用できることです。) *)
Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(* Compare this to the more laborious proof (in MoreCoq.v) for the 
   version of [override] defined using [beq_nat], where we had to
   use the auxiliary lemma [beq_nat_true] to convert a fact about booleans
   to a Prop. *)
(** MoreCoq_J.vにおける[beq_nat]を使った骨の折れる証明と比べてみてください。そちらでは、booleanに関する事実を命題に変換するために[beq_nat_true]の補助的な補題を用いる必要がありました。*)

(** **** 練習問題: ★ (override_shadow') *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(** ** Inversion, Again (Advanced) *)
(** ** 反転再び (応用編)*)

(* We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves...

    In general, the [inversion] tactic

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
(** これまでにも [inversion] が等値性にからむ仮定や帰納的に定義された命題に対して使われるところを見てきました。今度もやることは変わりませんが、もう少し近くまで寄って [inversion] の振る舞いを観察してみましょう。

    一般的に [inversion] タクティックは、

    - 帰納的に定義された型 [P] の命題 [H] をとる。

    - その型 [P] の定義にある各コンストラクタ [C] が、

      - [H] が [C] から成っていると仮定するような新しいサブゴールを作る。

      - [C] の引数（前提）を、追加の仮定としてサブゴールのコンテキストに加える。

      - [C] の結論（戻り値の型）を現在のゴールとmatchして、 [C] を適用できるような一連の等式算出する。

      - そしてこれらの等式をサブゴールのコンテキストに加えてから、

      - もしこの等式が充足可能でない場合（[S n = O] というような式を含むなど）は、
        即座にサブゴールを解決する。 *)

(*  _Example_: If we invert a hypothesis built with [or], there are two
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
   context.  *)
(**    例 :  [or] で構築された仮定を反転（ invert ）すると、[or] に二つのコンストラクタが
   あるため二つのサブゴールが生成されます。コンストラクタ ([P \/ Q]) の結果
   （戻り値の型）は [P] や [Q] の形からくる制約を付けません。そのため追加の等式が
   サブゴールのコンテキストに加えられることはありません。


   例 : [and] で構築された仮定を反転（ invert ）すると、[and] にはコンストラクタが
   一つしかないため、サブゴールも一つしか生成されません。やはり、コンストラクタ
   ([P /\ Q]) の結果（戻り値の型）は [P] や [Q] の形からくる制約を付けず、追加の等式が
   サブゴールのコンテキストに加えられることはありません。このコンストラクタは引数を二つ
   とりますが、それらはサブゴールのコンテキストに現れます。


   例 : [eq] で構築された仮定を反転（ invert ）すると、これにもやはりコンストラクタが
   一つしかないため、サブゴールも一つしか生成されません。しかしこの場合
   コンストラクタ [refl_equal] の形は我々にもう少し情報を与えてくれます。
   それは、[eq] の二つの引数は同じでなければならないという点です。
    [inversion] タクティックはこの事実をコンテキストに加えてくれます。 *)


(** **** 練習問題: ★, optional (dist_and_or_eq_implies_and) *)  
Lemma dist_and_or_eq_implies_and : forall P Q R,
       P /\ (Q \/ R) /\ Q = R -> P/\Q.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)




(* ####################################################### *)
(** * Additional Exercises *)
(** * 追加の練習問題 *)

(** **** 練習問題: ★★★ (all_forallb) *)
(* Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)
(** リストに関する属性 [all] を定義しなさい。それは、型 [X] と属性 [P : X -> Prop]をパラメータとし、 [all X P l]  が「リスト [l] の全ての要素が属性 [P} を満たす」とするものです。 *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  (* FILL IN HERE *)
.

(*  Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)
(** [Poly.v] の練習問題 [forall_exists_challenge] に出てきた関数 [forallb]を思い出してみましょう。 *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(* Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)
(** 属性 [all] を使って関数 [forallb] の仕様を書き、それを満たすことを証明しなさい。できるだけその仕様が厳格になるようにすること。

    関数 [forallb] の重要な性質が、あなたの仕様から洩れている、ということはありませんか？ *)

(* FILL IN HERE *)
(** [] *)

(** **** 練習問題: ★★★★, advanced (filter_challenge) *)
(*  One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)
(** Coq の主な目的の一つは、プログラムが特定の仕様を満たしていることを証明することです。それがどういうことか、[filter] 関数の定義が仕様を満たすか証明してみましょう。まず、その関数の仕様を非形式的に書き出してみます。

    集合 [X] と関数 [test: X->bool]、リスト[l] とその型 [list X] を想定する。さらに、[l] が二つのリスト [l1] と [l2] が順序を維持したままマージされたもので、リスト [l1] の要素はすべて [test] を満たし、 [l2] の要素はすべて満たさないとすると、[filter test l = l1] が成り立つ。

    リスト [l] が [l1] と [l2] を順序を維持したままマージしたものである、とは、それが [l1] と [l2] の要素をすべて含んでいて、しかも 互いに入り組んではいても [l1] 、 [l2] の要素が同じ順序になっている、ということです。例えば、
    [1,4,6,2,3]
    は、以下の二つを順序を維持したままマージしたものです。
    [1,6,2]
    と、
    [4,3]
    課題は、この仕様をCoq の定理の形に書き直し、それを証明することです。（ヒント：まず、一つのりすとが二つのリストをマージしたものとなっている、ということを示す定義を書く必要がありますが、これは帰納的な関係であって、[Fixpoint] で書くようなものではありません。）
 *)

(* FILL IN HERE *)
(** [] *)

(** **** 練習問題: ★★★★★, advanced, optional (filter_challenge_2) *)
(*  A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)
(** [filter] の振る舞いに関する特性を別の切り口で表すとこうなります。「[test] の結果が [true] なる要素だけでできた、リスト [l] のすべての部分リストの中で、[filter test l] が最も長いリストである。」これを形式的に記述し、それを証明しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(** **** 練習問題: ★★★★, advanced (no_repeats) *)
(* The following inductively defined proposition... *)
(** 次の帰納的に定義された命題は、 *)
Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(* ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)
(** 値 [a] がリスト [l] の要素として少なくとも一度は現れるということを言うための、精確な方法を与えてくれます。

    次の二つは[appears_in] に関するウォームアップ問題です。
*)
Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  (* FILL IN HERE *) Admitted.

(*  Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)
(** では、 [appears_in] を使って命題 [disjoint X l1 l2] を定義してください。これは、型 [X] の二つのリスト [l1] 、 [l2] が共通の要素を持たない場合にのみ証明可能な命題です。
 *)

(* FILL IN HERE *)

(* Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)
(** 次は、 [appears_in] を使って帰納的な命題 [no_repeats X l] を定義してください。これは, 型 [X] のリスト [l] の中のどの要素も、他の要素と異なっている場合のみ証明できるような命題です。例えば、[no_repeats nat [1,2,3,4]] や [no_repeats bool []] は証明可能ですが、[no_repeats nat [1,2,1]] や [no_repeats bool [true,true]] は証明できないようなものです。 *)
(* FILL IN HERE *)

(* Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)
(** 最後に、[disjoint]、 [no_repeats]、 [++] （リストの結合）の三つを使った、何か面白い定理を考えて、それを証明してください。 *)

(* FILL IN HERE *)
(** [] *)


(** **** 練習問題: ★★★ (nostutter) *)
(* Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all (except from your study group partner, if
    you have one).

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.) *)
(** 述語の帰納的な定義を定式化できるようになるというのは、これから先の学習に必要なスキルになってきます。

    同じ数値が連続して現れるリストを "stutters" （どもったリスト）と呼ぶことにします。述語 "[nostutter mylist]" は、 [mylist]  が「どもったリスト」でないことを意味しています。[nostutter] の帰納的な定義を記述しなさい。（これは以前の練習問題に出てきた [no_repeats] という述語とは異なるものです。リスト [1,4,1] は repeats ではありますが stutter ではありません。）
 *)

Inductive nostutter:  list nat -> Prop :=
 (* FILL IN HERE *)
.

(*  Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)
(** できた定義が、以下のテストを通過することを確認してください。通過できないものがあったら、定義を修正してもかまいません。あなたの書いた定義が、正しくはあるけれど私の用意した模範解答と異なっているかもしれません。その場合、このテストを通過するために別の証明を用意する必要があります。

    以下の Example にコメントとして提示された証明には、色々な種類の[nostutter] の定義に対応できるようにするため、まだ説明していないタクティックがいくつか使用されています。 まずこれらのコメントをはずしただけの状態で確認できればいいのですが、もしそうしたいなら、これらの証明をもっと基本的なタクティックで書き換えて証明してもかまいません。
 *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
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

(** **** 練習問題: ★★★★, advanced (pigeonhole principle) *)
(*  The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)
(** 「鳩の巣定理（ "pigeonhole principle" ）」は、「数えるあげる」ということについての基本的な事実を提示しています。「もし [n] 個の鳩の巣に[n] 個より多い数のものを入れようとするなら、どのような入れ方をしてもいくつかの鳩の巣には必ず一つ以上のものが入ることになる。」というもので、この、数値に関する見るからに自明な事実を証明するにも、なかなか自明とは言えない手段が必要になります。我々は既にそれを知っているのですが...
 *)
(*  First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)
(** まず、補題を二つほど証明しておきます。（既に数値のリストについては証明済みのものですが、任意のリストについてはのものはまだないので） *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  (* FILL IN HERE *) Admitted.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  (* FILL IN HERE *) Admitted.

(* Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)
(** そして、述語 [repeats] の定義をします（以前の練習問題 [no_repeats] に類似したものです）。それは [repeats X l] が、「 [l] の中に少なくとも一組の同じ要素（型 [X] の）を含む」という主張となるようなものです。 *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* FILL IN HERE *)
.

(* Now here's a way to formalize the pigeonhole principle. List [l2]
   represents a list of pigeonhole labels, and list [l1] represents an
   assignment of items to labels: if there are more items than labels,
   at least two items must have the same label.  You will almost
   certainly need to use the [excluded_middle] hypothesis. *)
(** この「鳩の巣定理」を定式化する方法を一つ挙げておきましょう。リスト [l2] が鳩の巣に貼られたラベルの一覧を、リスト [l1] はそのラベルの、アイテムへの割り当ての一覧を表しているとします。もしラベルよりも沢山のアイテムがあったならば、少なくとも二つのアイテムに同じラベルが貼られていることになります。おそらくこの証明には「排中律（ [excluded_middle] ）」が必要になるでしょう。 *)

Theorem pigeonhole_principle: forall (X:Type) (l1 l2:list X),
  excluded_middle -> 
  (forall x, appears_in x l1 -> appears_in x l2) -> 
  length l2 < length l1 -> 
  repeats l1.  
Proof.  intros X l1. induction l1.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

