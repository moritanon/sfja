(*  * IndPrinciples: Induction Principles *)
(** * 帰納法の原理 *)

(*  With the Curry-Howard correspondence and its realization in Coq in
    mind, we can now take a deeper look at induction principles. *)
(** Coqにおけるカーリーハワード対応とその実現について、帰納法の原理をより深く探って行きましょう。 *)

Require Export "ProofObjects".

(* ##################################################### *)
(** * Basics *)

(** Every time we declare a new [Inductive] datatype, Coq
    automatically generates an _induction principle_ for this type.
    This induction principle is a theorem like any other: If [t] is
    defined inductively, the corresponding induction principle is
    called [t_ind].  Here is the one for natural numbers: *)
(** 新たに[Inductive]なデータ型を宣言するときはいつでも、Coqは自動的にこの型の帰納法の原理 (_induction principle_)を生成します。 型[t]に対応する帰納法の原理は[t_ind]という名前になります。 ここでは自然数に対するものを示します。 *)

Check nat_ind.
(*  ===> nat_ind :
           forall P : nat -> Prop,
              P 0  ->
              (forall n : nat, P n -> P (S n))  ->
              forall n : nat, P n  *)

(*  The [induction] tactic is a straightforward wrapper that, at its
    core, simply performs [apply t_ind].  To see this more clearly,
    let's experiment with directly using [apply nat_ind], instead of
    the [induction] tactic, to carry out some proofs.  Here, for
    example, is an alternate proof of a theorem that we saw in the
    [Basics] chapter. *)
(** [induction] タクティックは、基本的には [apply t_ind] の単純なラッパーです。
    もっとわかりやすくするために、[induction] タクティックのかわりに [apply nat_ind] を使っていくつかの証明をしてみる実験をしてみましょう。
    例えば、[Basics_J] の章で見た定理の別の証明を見てみましょう。 *)

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.  Qed.


(*  This proof is basically the same as the earlier one, but a
    few minor differences are worth noting.

    First, in the induction step of the proof (the ["S"] case), we
    have to do a little bookkeeping manually (the [intros]) that
    [induction] does automatically.

    Second, we do not introduce [n] into the context before applying
    [nat_ind] -- the conclusion of [nat_ind] is a quantified formula,
    and [apply] needs this conclusion to exactly match the shape of
    the goal state, including the quantifier.  The [induction] tactic
    works either with a variable in the context or a quantified
    variable in the goal.

    Third, the [apply] tactic automatically chooses variable names for
    us (in the second subgoal, here), whereas [induction] lets us
    specify (with the [as...]  clause) what names should be used.  The
    automatic choice is actually a little unfortunate, since it
    re-uses the name [n] for a variable that is different from the [n]
    in the original theorem.  This is why the [Case] annotation is
    just [S] -- if we tried to write it out in the more explicit form
    that we've been using for most proofs, we'd have to write [n = S
    n], which doesn't make a lot of sense!  All of these conveniences
    make [induction] nicer to use in practice than applying induction
    principles like [nat_ind] directly.  But it is important to
    realize that, modulo this little bit of bookkeeping, applying
    [nat_ind] is what we are really doing. *)

(** この証明は基本的には前述のものと同じですが、細かい点で特筆すべき違いがあります。
    1つめは、帰納段階の証明（["S"] の場合）において、[induction] が自動でやってくれること（[intros]）を手作業で行なう必要があることです。

    2つめは、[nat_ind] を適用する前にコンテキストに [n] を導入していないことです。
    [nat_ind] の結論は限量子を含む式であり、[apply] で使うためにはこの結論と限量子を含んだゴールの形とぴったりと一致する必要があります。
    [induction] タクティックはコンテキストにある変数にもゴール内の量子化された変数のどちらにでも使えます。

    3つめは、[apply] タクティックは変数名（この場合はサブゴール内で使われる変数名）を自動で選びますが、[induction] は（[as ...] 節によって）使う名前を指定できることです。
    実際には、この自動選択にはちょっと不都合な点があります。元の定理の [n] とは別の変数として [n] を再利用してしまいます。
    これは [Case] 注釈がただの [S] だからです。
    ほかの証明で使ってきたように省略しない形で書くと、これは [n = S n] という意味のなさない形になってしまいます。
    このようなことがあるため、実際には [nat_ind] のような帰納法の原理を直接適用するよりも、素直に [induction] を使ったほうがよいでしょう。
    しかし、ちょっとした例外を除けば実際にやりたいのは [nat_ind] の適用であるということを知っておくことは重要です。 *)
	
(* **** Exercise: 2 stars (plus_one_r') *)
(** **** 練習問題: ★★  (plus_one_r') *)
(* Complete this proof without using the [induction] tactic. *)
(** [induction] タクティックを使わずに、下記の証明を完成させなさい。 *)

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Coq generates induction principles for every datatype defined with
    [Inductive], including those that aren't recursive.  Although of
    course we don't need induction to prove properties of
    non-recursive datatypes, the idea of an induction principle still
    makes sense for them: it gives a way to prove that a property
    holds for all values of the type.

    These generated principles follow a similar pattern. If we define
    a type [t] with constructors [c1] ... [cn], Coq generates a
    theorem with this shape:

    t_ind : forall P : t -> Prop,
              ... case for c1 ... ->
              ... case for c2 ... -> ...
              ... case for cn ... ->
              forall n : t, P n

    The specific shape of each case depends on the arguments to the
    corresponding constructor.  Before trying to write down a general
    rule, let's look at some more examples. First, an example where
    the constructors take no arguments: *)
(**  Coqは[Inductive]によって定義されたあらゆるデータ型に対して帰納法の原理を生成します。その中には、帰納的でないものも含まれます。
(帰納的でないデータ型の性質を証明するために帰納法はもちろん必要ないのですが、帰納法の原理のアイデアは帰納的でないデータ型にたいしても問題なく適用できます。)

このように生成された原理は、似たようなパターンに対しても適用できます。
コンストラクタ [c1] ... [cn] を持った型 [t] を定義すると、Coqは次の形の定理を生成します。
    t_ind :
       forall P : t -> Prop,
            ... c1の場合 ... ->
            ... c2の場合 ... ->
            ...                 ->
            ... cnの場合 ... ->
            forall n : t, P n
    各場合分けの形は、対応するコンストラクタの引数の数によって決まります。
    一般的な規則を紹介する前に、もっと例を見てみましょう。
    最初は、コンストラクタが引数を取らない場合です。
*)
	
Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.
(* ===> yesno_ind : forall P : yesno -> Prop,
                      P yes  ->
                      P no  ->
                      forall y : yesno, P y *)

(* **** Exercise: 1 star, optional (rgb) *)
(** **** 練習問題: ★ , optional (rgb) *)
(** Write out the induction principle that Coq will generate for the
    following datatype.  Write down your answer on paper or type it
    into a comment, and then compare it with what Coq prints. *)
(** 次のデータ型に対してCoqが生成する帰納法の原理を予測しなさい。
    紙かまたはコメント中に答えを書いたのち、Coqの出力と比較しなさい。 *)
Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.
(** [] *)

(* Here's another example, this time with one of the constructors
    taking some arguments. *)
(** 別の例を見てみましょう。引数を受け取るコンストラクタがある場合です。 *)

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.
(* ===> (modulo a little variable renaming)
   natlist_ind :
      forall P : natlist -> Prop,
         P nnil  ->
         (forall (n : nat) (l : natlist),
            P l -> P (ncons n l)) ->
         forall n : natlist, P n *)

(* **** Exercise: 1 star, optional (natlist1) *)
(** **** 練習問題: ★, optional (natlist1) *)
(** Suppose we had written the above definition a little
   differently: *)
(** 上記の定義をすこし変えたとしましょう。 *)

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(* Now what will the induction principle look like? *)
(** このとき、帰納法の原理はどのようになるでしょうか？ *)
(** [] *)

(* From these examples, we can extract this general rule:

    - The type declaration gives several constructors; each
      corresponds to one clause of the induction principle.
    - Each constructor [c] takes argument types [a1] ... [an].
    - Each [ai] can be either [t] (the datatype we are defining) or
      some other type [s].
    - The corresponding case of the induction principle says:

        - "For all values [x1]...[xn] of types [a1]...[an], if [P]
          holds for each of the inductive arguments (each [xi] of type
          [t]), then [P] holds for [c x1 ... xn]".

*)
(** これらの例より、一般的な規則を導くことができます。

    - 型宣言は複数のコンストラクタを持ち、各コンストラクタが帰納法の原理の各節に対応する。
    - 各コンストラクタ [c] は引数 [a1]..[an] を取る。
    - [ai] は [t]（定義しようとしているデータ型）、もしくは別の型 [s] かのどちらかである。
    - 帰納法の原理において各節は以下のことを述べている。
        - "型 [a1]...[an] のすべての値 [x1]...[xn] について、各 [x] について [P] が成り立つならば、[c x1 ... xn] についても [P] が成り立つ"
*)

(* **** Exercise: 1 star, optional (byntree_ind) *)
(** **** 練習問題: ★, optional (byntree_ind) *)
(** Write out the induction principle that Coq will generate for the
    following datatype.  (Again, write down your answer on paper or
    type it into a comment, and then compare it with what Coq
    prints.) *)
(** 次のデータ型に対してCoqが生成する帰納法の原理を予測しなさい。
    もう一度、紙かまたはコメント中に答えを書いたのち、Coqの出力と比較しなさい。 *)
	
Inductive byntree : Type :=
 | bempty : byntree
 | bleaf  : yesno -> byntree
 | nbranch : yesno -> byntree -> byntree -> byntree.
(** [] *)


(* **** Exercise: 1 star, optional (ex_set) *)
(** **** 練習問題: ★,  optional (ex_set) *)
(* Here is an induction principle for an inductively defined
    set.

      ExSet_ind :
         forall P : ExSet -> Prop,
             (forall b : bool, P (con1 b)) ->
             (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
             forall e : ExSet, P e

    Give an [Inductive] definition of [ExSet]: *)
(** ここに帰納的に定義された集合(set)の定義に対する帰納法の原理があります 
      ExSet_ind :
         forall P : ExSet -> Prop,
             (forall b : bool, P (con1 b)) ->
             (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
             forall e : ExSet, P e
    [ExSet]の[Inductive]による帰納的な定義を書きなさい *)

Inductive ExSet : Type :=
  (* FILL IN HERE *)
.
(** [] *)

(*  * Polymorphism *)
(** * 多相性 *)
(*  Next, what about polymorphic datatypes?

    The inductive definition of polymorphic lists
      Inductive list (X:Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X.
    is very similar to that of [natlist].  The main difference is
    that, here, the whole definition is _parameterized_ on a set [X]:
    that is, we are defining a _family_ of inductive types [list X],
    one for each [X].  (Note that, wherever [list] appears in the body
    of the declaration, it is always applied to the parameter [X].)
    The induction principle is likewise parameterized on [X]:

      list_ind :
        forall (X : Type) (P : list X -> Prop),
           P [] ->
           (forall (x : X) (l : list X), P l -> P (x :: l)) ->
           forall l : list X, P l

    Note that the _whole_ induction principle is parameterized on
    [X].  That is, [list_ind] can be thought of as a polymorphic
    function that, when applied to a type [X], gives us back an
    induction principle specialized to the type [list X]. *)
  
(** 次に、多相的なデータ型ではどのようになるでしょうか？

    多相的なリストの帰納的定義は [natlist] によく似ています。
      Inductive list (X:Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X.
     ここでの主な違いは、定義全体が集合 [X] によってパラメータ化されていることです。
     つまり、それぞれの [X] ごとに帰納型 [list X] を定義していることになります。
     (定義本体で [list] が登場するときは、常にパラメータ [X] に適用されていることに
     注意してください。)
     帰納法の原理も同様に [X] によってパラメータ化されます。
     list_ind :
       forall (X : Type) (P : list X -> Prop),
          P [] ->
          (forall (x : X) (l : list X), P l -> P (x :: l)) ->
          forall l : list X, P l
   この全体的な帰納法の原理の形に注目してください。帰納法の原理全体が 
   [X] によってパラメータ化されています。
   別の見方をすると、[list_ind] は多相関数と考えることができます。この関数は、型    [X] が適用されると、[list X] に特化した帰納法の原理を返します。
*)		
(* **** Exercise: 1 star (tree) *)
(** **** 練習問題: ★ (tree) *)
(* Write out the induction principle that Coq will generate for
   the following datatype.  Compare your answer with what Coq
   prints. *)
(** 次のデータ型に対してCoqが生成する帰納法の原理を予測しなさい。
    答えが書けたら、それをCoqの出力と比較しなさい。 *)

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
Check tree_ind.
(** [] *)

(*  **** Exercise: 1 star, optional (mytype)  *)
(** **** 練習問題: ★, optional (mytype)  *)
(** Find an inductive definition that gives rise to the
    following induction principle: *)
(** 以下の帰納法の原理を生成する帰納的定義を探しなさい。

      mytype_ind :
        forall (X : Type) (P : mytype X -> Prop),
            (forall x : X, P (constr1 X x)) ->
            (forall n : nat, P (constr2 X n)) ->
            (forall m : mytype X, P m ->
               forall n : nat, P (constr3 X m n)) ->
            forall m : mytype X, P m

*) 
(** [] *)

(* **** Exercise: 1 star, optional (foo) *)
(** **** 練習問題: ★, optional (foo)  *)
(* Find an inductive definition that gives rise to the
    following induction principle:
(** 以下の帰納法の原理を生成する帰納的定義を探しなさい。

      foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2

*) 
(** [] *)

(** **** Exercise: 1 star, optional (foo') *)
(** **** 練習問題: ★, optional (foo') *)
(* Consider the following inductive definition: *)
(** 次のような帰納的定義があるとします。 *)

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

(*  What induction principle will Coq generate for [foo']?  Fill
   in the blanks, then check your answer with Coq.)
     foo'_ind :
        forall (X : Type) (P : foo' X -> Prop),
              (forall (l : list X) (f : foo' X),
                    _______________________ -> 
                    _______________________   ) ->
             ___________________________________________ ->
             forall f : foo' X, ________________________
*)

(** [foo'] に対してCoqはどのような帰納法の原理を生成するでしょうか?
    空欄を埋め、Coqの結果と比較しなさい
     foo'_ind :
        forall (X : Type) (P : foo' X -> Prop),
              (forall (l : list X) (f : foo' X),
                    _______________________ ->
                    _______________________   ) ->
             ___________________________________________ ->
             forall f : foo' X, ________________________

*)

(** [] *)

(* ##################################################### *)
(*  ** Induction Hypotheses *)
(** **  帰納法の仮定 *)
(* Where does the phrase "induction hypothesis" fit into this story?

    The induction principle for numbers

       forall P : nat -> Prop,
            P 0  ->
            (forall n : nat, P n -> P (S n))  ->
            forall n : nat, P n

   is a generic statement that holds for all propositions
   [P] (or rather, strictly speaking, for all families of
   propositions [P] indexed by a number [n]).  Each time we
   use this principle, we are choosing [P] to be a particular
   expression of type [nat->Prop].

   We can make proofs by induction more explicit by giving
   this expression a name.  For example, instead of stating
   the theorem [mult_0_r] as "[forall n, n * 0 = 0]," we can
   write it as "[forall n, P_m0r n]", where [P_m0r] is defined
   as... *)
(** この概念において"帰納法の仮定"はどこにあてはまるでしょうか?

    数に関する帰納法の原理
       forall P : nat -> Prop,
            P 0  ->
            (forall n : nat, P n -> P (S n))  ->
            forall n : nat, P n  
    は、すべての命題 [P]（より正確には数値 n を引数にとる命題 [P] ）について成り立つ一般的な文です。
    この原理を使うときはいつも、[nat->Prop] という型を持つ式を [P] として選びます。

    この式に名前を与えることで、証明をもっと明確にできます。
    例えば、[mult_0_r] を"[forall n, n * 0 = 0]"と宣言するかわりに、"[forall n, P_m0r n]"と宣言します。
    なお、ここで [P_m0r] は次のように定義されています。
*)		

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

(* ... or equivalently... *)
(** あるいは・・・ *)

Definition P_m0r' : nat->Prop :=
  fun n => n * 0 = 0.
(** でも同じ意味です。 *)

(* Now when we do the proof it is easier to see where [P_m0r]
    appears. *)
(** これで、証明する際に [P_m0r] がどこに現れるかが分かりやすくなります。 *)

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* Note the proof state at this point! *)
    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

(* This extra naming step isn't something that we do in
    normal proofs, but it is useful to do it explicitly for an example
    or two, because it allows us to see exactly what the induction
    hypothesis is.  If we prove [forall n, P_m0r n] by induction on
    [n] (using either [induction] or [apply nat_ind]), we see that the
    first subgoal requires us to prove [P_m0r 0] ("[P] holds for
    zero"), while the second subgoal requires us to prove [forall n',
    P_m0r n' -> P_m0r n' (S n')] (that is "[P] holds of [S n'] if it
    holds of [n']" or, more elegantly, "[P] is preserved by [S]").
    The _induction hypothesis_ is the premise of this latter
    implication -- the assumption that [P] holds of [n'], which we are
    allowed to use in proving that [P] holds for [S n']. *)
(** このように名前をつける手順は通常の証明では不要です。
    しかし、1つ2つ試してみると、帰納法の仮定がどのようなものなのかが分かりやすくなります。
    [forall n, P_m0r n] を [n] による帰納法（[induction] か [apply nat_ind] を使う）によって証明しようとすると、最初のサブゴールでは [P_m0r 0]（"[P] が0に対して成り立つ"）を証明しなければならず、2つめのサブゴールでは [forall n', P_m0r n' -> P_m0r (S n')]（"[P] が [n'] について成り立つならば、[P] が [S n'] についても成り立つ"あるいは" [P] が [S] によって保存される"）を証明しなければなりません。
    帰納法の仮定(_induction hypothesis_)は、2つめの推論の基礎になっています -- [P] が [n'] について成り立つことを仮定することにより、それによって [P] が [S n'] について成り立つことを示すことができます。
*)
(* ##################################################### *)
(* ** More on the [induction] Tactic *)
(** ** [induction] タクティックについてもう少し *)

(** The [induction] tactic actually does even more low-level
    bookkeeping for us than we discussed above.

    Recall the informal statement of the induction principle for
    natural numbers:
      - If [P n] is some proposition involving a natural number n, and
        we want to show that P holds for _all_ numbers n, we can
        reason like this:
          - show that [P O] holds
          - show that, if [P n'] holds, then so does [P (S n')]
          - conclude that [P n] holds for all n.
    So, when we begin a proof with [intros n] and then [induction n],
    we are first telling Coq to consider a _particular_ [n] (by
    introducing it into the context) and then telling it to prove
    something about _all_ numbers (by using induction).

    What Coq actually does in this situation, internally, is to
    "re-generalize" the variable we perform induction on.  For
    example, in our original proof that [plus] is associative... *)
(** [induction] タクティックは、実はこれまで見てきたような、いささか
    低レベルな作業をこなすだけのものではありません。

    自然数に関する帰納的な公理の非形式的な記述を思い出してみてください。:
      - もし [P n] が数値 n を意味する何かの命題だとして、命題 P が全ての数値 n に
        ついて成り立つことを示したい場合は、このような推論を
        することができます。:
          - [P O] が成り立つことを示す
          - もし [P n'] が成り立つなら, [P (S n')] が成り立つことを示す。
          - 任意の n について [P n] が成り立つと結論する。
    我々が証明を [intros n] で始め、次に [induction n] とすると、
    これはCoqに「特定の」 [n] について（それを仮定取り込むことで）考えて
    から、その後でそれを帰納法を使って任意の数値にまで推し進めるよう
    示していることになります。

    このようなときに Coq が内部的に行っていることは、帰納法を適用した変数を
    「再一般化（ _re-generalize_ ）」することです。
    例えば、[plus] の結合則を証明するケースでは... *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* ...we first introduce all 3 variables into the context,
     which amounts to saying "Consider an arbitrary [n], [m], and
     [p]..." *)
  (** ...最初に 3個の変数を全てコンテキストに導入しています。
     これはつまり"任意の [n], [m], [p] について考える"という
     意味になっています... *)
  intros n m p.
  (* ...We now use the [induction] tactic to prove [P n] (that
     is, [n + (m + p) = (n + m) + p]) for _all_ [n],
     and hence also for the particular [n] that is in the context
     at the moment. *)
  (** ...ここで、[induction] タクティックを使い [P n] （任意の [n] に
     ついて [n + (m + p) = (n + m) + p]）を証明し、すぐに、
     コンテキストにある特定の [n] についても証明します。 *)
  induction n as [| n'].
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* In the second subgoal generated by [induction] -- the
       "inductive step" -- we must prove that [P n'] implies
       [P (S n')] for all [n'].  The [induction] tactic
       automatically introduces [n'] and [P n'] into the context
       for us, leaving just [P (S n')] as the goal. *)
    (** [induction] が作成した（帰納法の手順とも言うべき）二つ目の
        ゴールでは、 [P n'] ならば任意の [n'] で [P (S n')] が成り立つ
        ことを証明する必要があります。 この時に [induction] タクティックは
        [P (S n')] をゴールにしたまま、自動的に [n'] と [P n'] を
        コンテキストに導入してくれます。
     *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.


(* It also works to apply [induction] to a variable that is
   quantified in the goal. *)
(** [induction] をゴールにある量化された変数に適用してもかまいません。 *)

Theorem plus_comm' : forall n m : nat, 
  n + m = m + n.
Proof.
  induction n as [| n'].
  - (* n = O *) intros m. rewrite <- plus_n_O. reflexivity.
  - (* n = S n' *) intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(*  Note that [induction n] leaves [m] still bound in the goal --
    i.e., what we are proving inductively is a statement beginning
    with [forall m].

    If we do [induction] on a variable that is quantified in the goal
    _after_ some other quantifiers, the [induction] tactic will
    automatically introduce the variables bound by these quantifiers
    into the context. *)
(** [induction n] が [m] をゴールに残したままにしていることに注目してください。
    つまり、今証明しようとしている帰納的な性質は、[forall m] で表されて
    いるということです。

    もし [induction] をゴールにおいて量化された変数に対して他の量化子の後に
    適用すると、[induction] タクティックは自動的に変数をその量化子に基づいて
    コンテキストに導入します。 *)
	
Theorem plus_comm'' : forall n m : nat, 
  n + m = m + n.
Proof.
  (* Let's do induction on [m] this time, instead of [n]... *)
 (** ここで [n] の代わりに [m] を induction しましょう。... *)
  induction m as [| m'].
  - (* m = O *) simpl. rewrite <- plus_n_O. reflexivity.
  - (* m = S m' *) simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(** **** Exercise: 1 star, optional (plus_explicit_prop) *)
(** **** 練習問題: ★, optional (plus_explicit_prop) *)
(* Rewrite both [plus_assoc'] and [plus_comm'] and their proofs in
    the same style as [mult_0_r''] above -- that is, for each theorem,
    give an explicit [Definition] of the proposition being proved by
    induction, and state the theorem and proof in terms of this
    defined proposition.  *)
(** [plus_assoc'] と [plus_comm'] を、その証明とともに上の [mult_0_r''] と
    同じスタイルになるよう書き直しなさい。このことは、それぞれの定理が
    帰納法で証明された命題に明確な定義を与え、この定義された命題から定理と
    証明を示しています。  *)
	
(* FILL IN HERE *)
(** [] *)

(* ##################################################### *)
(*  * Induction Principles in [Prop] *)
(** * 命題に対する帰納法の原理 *)

(** Earlier, we looked in detail at the induction principles that Coq
    generates for inductively defined _sets_.  The induction
    principles for inductively defined _propositions_ like [ev] are a
    tiny bit more complicated.  As with all induction principles, we
    want to use the induction principle on [ev] to prove things by
    inductively considering the possible shapes that something in [ev]
    can have.  Intuitively speaking, however, what we want to prove
    are not statements about _evidence_ but statements about
    _numbers_: accordingly, we want an induction principle that lets
    us prove properties of numbers by induction on evidence.

    For example, from what we've said so far, you might expect the
    inductive definition of [ev]...

      Inductive ev : nat -> Prop :=
      | ev_0 : ev 0
      | ev_SS : forall n : nat, ev n -> ev (S (S n)).

    ...to give rise to an induction principle that looks like this...

    ev_ind_max : forall P : (forall n : nat, ev n -> Prop),
         P O ev_0 ->
         (forall (m : nat) (E : ev m),
            P m E ->
            P (S (S m)) (ev_SS m E)) ->
         forall (n : nat) (E : gorgeous n),
         P n E

     ... because:

     - Since [ev] is indexed by a number [n] (every [ev] object [E] is
       a piece of evidence that some particular number [n] is even),
       the proposition [P] is parameterized by both [n] and [E] --
       that is, the induction principle can be used to prove
       assertions involving both an even number and the evidence that
       it is even.

     - Since there are two ways of giving evidence of evenness ([ev]
       has two constructors), applying the induction principle
       generates two subgoals:

         - We must prove that [P] holds for [O] and [ev_0].

         - We must prove that, whenever [n] is an even number and [E]
           is an evidence of its evenness, if [P] holds of [n] and
           [E], then it also holds of [S (S n)] and [ev_SS n E].

     - If these subgoals can be proved, then the induction principle
       tells us that [P] is true for _all_ even numbers [n] and
       evidence [E] of their evenness.

    This is more flexibility than we normally need or want: it is
    giving us a way to prove logical assertions where the assertion
    involves properties of some piece of _evidence_ of evenness, while
    all we really care about is proving properties of _numbers_ that
    are even -- we are interested in assertions about numbers, not
    about evidence.  It would therefore be more convenient to have an
    induction principle for proving propositions [P] that are
    parameterized just by [n] and whose conclusion establishes [P] for
    all even numbers [n]:

       forall P : nat -> Prop,
       ... ->
       forall n : nat,
       even n -> P n

    For this reason, Coq actually generates the following simplified
    induction principle for [ev]: *)
(** TODO!!
*)

Check ev_ind.
(* ===> ev_ind
        : forall P : nat -> Prop,
          P 0 ->
          (forall n : nat, ev n -> P n -> P (S (S n))) ->
          forall n : nat,
          ev n -> P n *)

(** In particular, Coq has dropped the evidence term [E] as a
    parameter of the the proposition [P]. *)

(** In English, [ev_ind] says:

    - Suppose, [P] is a property of natural numbers (that is, [P n] is
      a [Prop] for every [n]).  To show that [P n] holds whenever [n]
      is even, it suffices to show:

      - [P] holds for [0],

      - for any [n], if [n] is even and [P] holds for [n], then [P]
        holds for [S (S n)]. *)

(** As expected, we can apply [ev_ind] directly instead of using
    [induction]. *)

Theorem ev_ev' : forall n, ev n -> ev' n.
Proof.
  apply ev_ind.
  - (* ev_0 *)
    apply ev'_0.
  - (* ev_SS *)
    intros m Hm IH.
    apply (ev'_sum 2 m).
    + apply ev'_2.
    + apply IH.
Qed.

(** The precise form of an [Inductive] definition can affect the
    induction principle Coq generates.

    For example, in chapter [IndProp], we defined [<=] as: *)

(* Inductive le : nat -> nat -> Prop :=
     | le_n : forall n, le n n
     | le_S : forall n m, (le n m) -> (le n (S m)). *)

(** This definition can be streamlined a little by observing that the
    left-hand argument [n] is the same everywhere in the definition,
    so we can actually make it a "general parameter" to the whole
    definition, rather than an argument to each constructor. *)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** The second one is better, even though it looks less symmetric.
    Why?  Because it gives us a simpler induction principle. *)

Check le_ind.
(* ===>  forall (n : nat) (P : nat -> Prop),
           P n ->
           (forall m : nat, n <= m -> P m -> P (S m)) ->
           forall n0 : nat, n <= n0 -> P n0 *)
(* ####################################################### *)
(*  * Formal vs. Informal Proofs by Induction *)
(** 帰納法による、形式的証明 vs 非形式的な証明 *)

(*  Question: What is the relation between a formal proof of a
    proposition [P] and an informal proof of the same proposition [P]?

    Answer: The latter should _teach_ the reader how to produce the
    former.

    Question: How much detail is needed??

    Unfortunately, there is no single right answer; rather, there is a
    range of choices.

    At one end of the spectrum, we can essentially give the reader the
    whole formal proof (i.e., the informal proof amounts to just
    transcribing the formal one into words).  This gives the reader
    the ability to reproduce the formal one for themselves, but it
    probably doesn't _teach_ them anything much.

   At the other end of the spectrum, we can say "The theorem is true
   and you can figure out why for yourself if you think about it hard
   enough."  This is also not a good teaching strategy, because often
   writing the proof requires one or more significant insights into
   the thing we're proving, and most readers will give up before they
   rediscover all the same insights as we did.

   In the middle is the golden mean -- a proof that includes all of
   the essential insights (saving the reader the hard part of work
   that we went through to find the proof in the first place) and
   clear high-level suggestions for the more routine parts to save the
   reader from spending too much time reconstructing these
   parts (e.g., what the IH says and what must be shown in each case
   of an inductive proof), but not so much detail that the main ideas
   are obscured.

   Another key point: if we're comparing a formal proof of a
   proposition [P] and an informal proof of [P], the proposition [P]
   doesn't change.  That is, formal and informal proofs are _talking
   about the same world_ and they _must play by the same rules_. *)
TODO 
 (** Q: 命題 [P] の形式的な証明と、同じ命題 [P] の非形式的な証明の間にはどのような関係があるのでしょうか？

    A: 後者は、読む人に「どのように形式的な証明を導くか」を示すようなものとなっているべきです。

    Q: どの程度細かく書く必要があるのですか？

    A: この問いに唯一と言えるような解答はありません。回答には選択の幅があります。

      その範囲の片方の端は、読み手にただ形式的な証明全体を与えればよいという考えです。つまり非形式的な証明は、形式的な証明をただ単に普通の言葉で書き換えただけ	、ということです。この方法は、読み手に形式的な証明を書かせるための能力を与えることはできますが、それについて何かも「教えてくれる」訳ではありません。

      これに対しもう一方の端は、「その定理は真で、頑張ればできるはず」ような記述です。この方法も、「教える」ということに関してはあまりいいやり方とはいえません。なぜなら、証明を記述するときはいつも、今証明しようとしているものの奥深くにまで目を向け考えることが必要とされますが、細かく書きすぎると証明を読む側の人の多くは自分自身の力で同じ思考にたどり着くことなく、あきらめて証明の記述に頼ってしまうでしょう。

      一番の答えはその中間にあります。全ての要点をかいつまんだ証明というのは、「かつてあなたが証明をしたときに非常に苦労した部分について、読む人が同じ苦労をしなくて済むようになっている」ようなものです。そしてまた、読み手が同じような苦労を何時間もかけてする必要がないよう、証明の中で使える部品などを高度に示唆するものでなければなりません（例えば、仮定 IH が何を言っているかや、帰納的な証明のどの部分に現れるかなど）。しかし、詳細が少なすぎると、証明の主要なアイデアがうまく伝わりません。

   もう一つのキーポイント：もし我々が命題 P の形式的な証明と非形式的な証明について話しているならば、命題 P 自体は何も変わりません。このことは、形式的な証明も非形式的な証明も、同じ「世界」について話をしていて、同じルール(_rule_)に基づいていなければならない、と言うことを意味しています。
 *)  
 
(* *** Induction Over an Inductively Defined Set *)
(** *** 帰納的に定義された集合についての帰納法 *)

(* _Template_: 

       - _Theorem_: <Universally quantified proposition of the form
         "For all [n:S], [P(n)]," where [S] is some inductively defined
         set.>

         _Proof_: By induction on [n].

           <one case for each constructor [c] of [S]...>

           - Suppose [n = c a1 ... ak], where <...and here we state
             the IH for each of the [a]'s that has type [S], if any>.
             We must show <...and here we restate [P(c a1 ... ak)]>.

             <go on and prove [P(n)] to finish the case...>

           - <other cases similarly...>                        []

    _Example_:

      - _Theorem_: For all sets [X], lists [l : list X], and numbers
        [n], if [length l = n] then [index (S n) l = None].

        _Proof_: By induction on [l].

        - Suppose [l = []].  We must show, for all numbers [n],
          that, if [length [] = n], then [index (S n) [] =
          None].

          This follows immediately from the definition of [index].

        - Suppose [l = x :: l'] for some [x] and [l'], where
          [length l' = n'] implies [index (S n') l' = None], for
          any number [n'].  We must show, for all [n], that, if
          [length (x::l') = n] then [index (S n) (x::l') =
          None].

          Let [n] be a number with [length l = n].  Since
            length l = length (x::l') = S (length l'),
          it suffices to show that 
            index (S (length l')) l' = None.
]]  
          But this follows directly from the induction hypothesis,
          picking [n'] to be length [l'].  [] *)
 (** _Template_:

       - 定理: < "For all [n:S], [P(n)],"の形で全量子化された命題。ただし [S] は帰納的に定義された集合。>

         証明: [n] についての帰納法で証明する。

           <集合 [S] の各コンストラクタ [c] について...>

           - [n = c a1 ... ak] と仮定して、<...もし必要なら [S] のそれぞれの要素 [a] についてIHであることをを示す。>ならば
              <...ここで再び [P(c a1 ... ak)] を示す> である。

             < [P(n)] を証明してこのケースを終わらせる...>

           - <他のケースも同様に記述する...>                        []

    _Example_:

      - _Theorem_: 任意の集合 [X] 、リスト [l : list X]、 自然数 [n] について、
          もし [length l = n] が成り立つなら、[index (S n) l = None] も成り立つ。

        _Proof_: [l] についての帰納法で証明する。

        - まず、[l = []] と仮定して、任意の [n] でこれが成り立つことを示す。もし length [[] = n] ならば [index (S n) [] = None] 。
          これは index の定義から直接導かれる 。

        - 次に、 [x] と [l'] において [l = x :: l'] と仮定して、任意の [n'] について
          [length l' = n'] ならば [index (S n') l' = None] である時、任意の [n] について、
          もし [length (x::l') = n] ならば [index (S n) (x::l') = None] を示す。

          [n] を [length l = n] となるような数とすると、

            length l = length (x::l') = S (length l'),

          これは以下の十分条件である。

            index (S (length l')) l' = None.

          しかしこれは仮定法の仮定から直接導かれる。
          [l'] の length となるような [n'] を選択すればよい。  [] *)

(* *** Induction Over an Inductively Defined Proposition *)
(** *** 帰納的に定義された命題についての帰納法 *)

(** Since inductively defined proof objects are often called
    "derivation trees," this form of proof is also known as _induction
    on derivations_.

    _Template_:

       - _Theorem_: <Proposition of the form "[Q -> P]," where [Q] is
         some inductively defined proposition (more generally,
         "For all [x] [y] [z], [Q x y z -> P x y z]")>

         _Proof_: By induction on a derivation of [Q].  <Or, more
         generally, "Suppose we are given [x], [y], and [z].  We
         show that [Q x y z] implies [P x y z], by induction on a
         derivation of [Q x y z]"...>

           <one case for each constructor [c] of [Q]...>

           - Suppose the final rule used to show [Q] is [c].  Then
             <...and here we state the types of all of the [a]'s
             together with any equalities that follow from the
             definition of the constructor and the IH for each of
             the [a]'s that has type [Q], if there are any>.  We must
             show <...and here we restate [P]>.

             <go on and prove [P] to finish the case...>

           - <other cases similarly...>                        []

    _Example_

       - _Theorem_: The [<=] relation is transitive -- i.e., for all
         numbers [n], [m], and [o], if [n <= m] and [m <= o], then
         [n <= o].

         _Proof_: By induction on a derivation of [m <= o].

           - Suppose the final rule used to show [m <= o] is
             [le_n]. Then [m = o] and we must show that [n <= m],
             which is immediate by hypothesis.

           - Suppose the final rule used to show [m <= o] is
             [le_S].  Then [o = S o'] for some [o'] with [m <= o'].
             We must show that [n <= S o'].
             By induction hypothesis, [n <= o'].

             But then, by [le_S], [n <= S o'].  [] *)

(** 帰納的に定義された証明オブジェクトは、しばしば”導出木”と呼ばれるため、この形の証明は「導出による帰納法（ _induction on derivations_ ）」として知られています。

    _Template_ :

       - _Theorem_ : <"[Q -> P]," という形を持った命題。ただし [Q] は帰納的に定義された命題（さらに一般的には、"For all [x] [y] [z], [Q x y z -> P x y z]" という形の命題）>

         _Proof_ : [Q] の導出による帰納法で証明する。 <もしくは、さらに一般化して、" [x], [y], [z]を仮定して、[Q x y z] ならば [P x y z] を示す。[Q x y z]の導出による帰納法によって"...>

           <各コンストラクタ [c] による値 [Q] について...>

           - [Q] が [c] であることを示した最後のルールを仮定して、
             <...ここで [a] の全ての型をコンストラクタの定義にある等式と
             共に示し、型 [Q] を持つ [a] がIHであることをそれぞれ示す。>
             ならば <...ここで再び [P] を示す> である。

             <がんばって [P] を証明し、このケースを閉じる...>

           - <他のケースも同様に...>                        []
    _Example_

       - _Theorem_ : [<=] という関係は推移的である -- すなわち、任意の
         数値 [n], [m], [o] について、もし [n <= m] と [m <= o] が成り立つ
         ならば [n <= o] である。

         _Proof_ : [m <= o] についての帰納法で証明する。

           -  [m <= o] が [le_n] であることを示した最後のルールであると仮定しましょう。
              それにより [m = o] であることとその結果が直接導かれます。

           - [m <= o] が [le_S] であることを示した最後のルールであると仮定しましょう。
             それにより [m <= o'] を満たす [o'] について [o = S o'] が成り立つ。
             帰納法の仮定法より [n <= o'] である。

             従って[le_S] より [n <= o] である。  [] *)		   
		   
(** $Date: 2016-05-26 16:17:19 -0400 (Thu, 26 May 2016) $ *)
