(* * More Logic *)
(** * 論理についてもう少し *)

Require Export "Prop_J".

(* ############################################################ *)
(* * Existential Quantification *)
(** * 存在量化子 *)

(* Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)
(** もう一つの論理的接続詞は、存在量化子（ _existential quantification_ ）です。これは、次のような定義でその意味をとらえることができます。 *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(* That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)
(** この [ex] は、型引数 [X] とそれに関する属性 [P] によって決まる命題です。「 [P] を満たす [x] が存在する」という主張に根拠を与えるため、ある特定の値 [x] （「証拠」と呼ぶことにします）を具体的に示すことで[P x] の根拠を得ることができます。つまりこれは、 [x] が性質 [P] を持っていることの根拠です。 *)

(** *** *)
(* Coq's [Notation] facility can be used to introduce more
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

(** *** *)
(* We can use the usual set of tactics for
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

(* Note that we have to explicitly give the witness. *)
(** ここで具体的な値を証拠として用意する必要があることに注意してください。 *)

(** *** *)
(* Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)
(** [apply ex_intro with (witness:=e)] と書く代わりに、短縮形として [exists e]と記述することもできます。どちらも同じ意味です。 *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** *** *)
(* Conversely, if we have an existential hypothesis in the
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


(* Here is another example of how to work with existentials. *)
(** 存在量化子がどのように働くのかを示す例を用意しました。*)
Lemma exists_example_3 : 
  exists (n:nat), even n /\ beautiful n.
Proof.
(* WORKED IN CLASS *)
  exists 8.
  split.
  unfold even. simpl. reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3. apply b_5.
Qed.

(* **** Exercise: 1 star, optional (english_exists) *)
(** **** 練習問題: ★, optional (english_exists) *)
(* In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)
(** 英語では、以下の命題は何を意味しているでしょうか？
ex nat (fun n => ev (S n))
]]
*)

(* FILL IN HERE *)

(*
*)
(* **** Exercise: 1 star (dist_not_exists) *)
(** **** 練習問題: ★ (dist_not_exists) *)
(* Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)
(** "全ての [x] について[P] が成り立つ" ならば " [P] を満たさない [x] は存在しない" ということを証明しなさい。 *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars, optional (not_exists_dist *)
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

(* **** Exercise: 2 stars (dist_exists_or) *)
(** **** 練習問題: ★★ (dist_exists_or) *)
(* Prove that existential quantification distributes over
    disjunction. *)
(** 存在量化子が論理和において分配法則を満たすことを証明しなさい。 *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(* * Evidence-carrying booleans. *)
(** * ブール値を保持する根拠 *)

(* So far we've seen two different forms of equality predicates:
[eq], which produces a [Prop], and
the type-specific forms, like [beq_nat], that produce [boolean]
values.  The former are more convenient to reason about, but
we've relied on the latter to let us use equality tests 
in _computations_.  While it is straightforward to write lemmas
(e.g. [beq_nat_true] and [beq_nat_false]) that connect the two forms,
using these lemmas quickly gets tedious. 
*)
(**今までのところ、二つの異なった形式の等価性を示す述語を見てきました。
命題を生成する [eq]と、[beq_nat]のような、ブール値を生成する、それぞれの型に固有のやり方とです。前者は推論するには便利ですが、計算機で等価性のテストをするにはこれまで後者が頼りになってきました。二つの文をつなげる補題(例として[beq_nat_true]や[beq_nat_false])を書くのは簡単である一方、これらの補題を使用することは、すぐに面倒になります。 *)


(** *** *)
(*
It turns out that we can get the benefits of both forms at once 
by using a construct called [sumbool]. *)

(* sumboolと呼ばれるコンストラクトを使うと、両方の形式を同時に使うことにも利便性があることが分かります。*)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(* Think of [sumbool] as being like the [boolean] type, but instead
of its values being just [true] and [false], they carry _evidence_
of truth or falsity. This means that when we [destruct] them, we
are left with the relevant evidence as a hypothesis -- just as with [or].
(In fact, the definition of [sumbool] is almost the same as for [or].
The only difference is that values of [sumbool] are declared to be in
[Set] rather than in [Prop]; this is a technical distinction 
that allows us to compute with them.) *) 
(** 単純な[true]や[false]の値としてではなく、[boolean]型と似たものとして[sumbool]をとらえると、それは真であることや偽であることの根拠を導きます。この意味は、我々が、[sumbool]を[destruct]したとき、仮説として関連性のある根拠を持ち続けられる、ということです。ちょうど[or]のように。
(実際、[sumbool]の定義は[or]とほとんど同じです。違う点はただ、[sumbool]の値が[Prop]の中よりむしろ[Set]の中で宣言されている、ということだけです。このことは、それらを使って我々がどのように計算するかについての技術的な違いにすぎません。) *)

(** *** *)

(* Here's how we can define a [sumbool] for equality on [nat]s *)
(** [nat]の等価性のために[sumbool]をどのように定義するかを示します。*)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (* WORKED IN CLASS *)
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
  
(* Read as a theorem, this says that equality on [nat]s is decidable:
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
*) 
(** 定理として見ると、これは[nat]についての等価性は決定可能であることを示しています。すなわち二つの[nat]の値が与えられたら、われわれは常に二つの値が等しいかそうでないかどちらかの根拠を提示することが出来るということです。計算機的に読むと、[eq_nat_dec]は二つの[nat]の値を引数にとり、二つの値が等しければ、[left]によって構築された、あるいは等しくないならば、[right]によって構築された[sumbool]を返却します。この結果は[match]によってテストすることが出来ます。あるいはもっといい方法として、[if-then-else]を用いてテストすることが通常の[boolean]と同じように出来ます。( この証明を[Qed]ではなく、[Defined]を用いて終らせていることに注意してください。このことで発生する唯一の違いは、証明が透明になるということです。その意味は、Coqが計算機的な解釈のために重要な縮小を行おうとしたときにその定義を使用できることです。) *)

(** *** *)
(* 
Here's a simple example illustrating the advantages of the [sumbool] form. *)
(** ここで、[sumbool]の形式の利点が分かる単純な例を挙げます *)

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

(** Compare this to the more laborious proof (in MoreCoq.v) for the 
   version of [override] defined using [beq_nat], where we had to
   use the auxiliary lemma [beq_nat_true] to convert a fact about booleans
   to a Prop. *)
(** MoreCoq_J.vにおける[beq_nat]を使った骨の折れる証明と比べてみてください。そちらでは、booleanに関する事実を命題に変換するために[beq_nat_true]の補助的な補題を用いる必要がありました。*)

(* **** Exercise: 1 star (override_shadow') *)
(** **** 練習問題: ★ (override_shadow') *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)






(* ####################################################### *)
(* * Additional Exercises *)
(** * 追加の練習問題 *)

(* **** Exercise: 3 stars (all_forallb) *)
(** **** 練習問題: ★★★ (all_forallb) *)
(* Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)
(** リストに関する属性 [all] を定義しなさい。それは、型 [X] と属性 [P : X -> Prop]をパラメータとし、 [all X P l] が「リスト [l] の全ての要素が属性 [P} を満たす」とするものです。 *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  (* FILL IN HERE *)
.

(* Recall the function [forallb], from the exercise
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

(** **** Exercise: 4 stars, advanced (filter_challenge) *)
(** **** 練習問題: ★★★★, advanced (filter_challenge) *)
(* One of the main purposes of Coq is to prove that programs match
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
課題は、この仕様をCoq の定理の形に書き直し、それを証明することです。（ヒント：まず、一つのリストが二つのリストをマージしたものとなっている、ということを示す定義を書く必要がありますが、これは帰納的な関係であって、[Fixpoint] で書くようなものではありません。）
*)
(* FILL IN HERE *)
(** [] *)

(* **** Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
(** **** 練習問題: ★★★★★, advanced, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)
(** [filter] の振る舞いに関する特性を別の切り口で表すとこうなります。「[test] の結果が [true] なる要素だけでできた、リスト [l] のすべての部分リストの中で、[filter test l] が最も長いリストである。」これを形式的に記述し、それを証明しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(* **** Exercise: 4 stars, advanced (no_repeats) *)
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
(** 値 [a] がリスト [l] の要素として少なくとも一度は現れるということを言うための、正確な方法を与えてくれます。
 
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

(* Now use [appears_in] to define a proposition [disjoint X l1 l2],
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


(* **** Exercise: 3 stars (nostutter) *)
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
 
同じ数値が連続して現れるリストを "stutters" （どもったリスト）と呼ぶことにします。述語 "[nostutter mylist]" は、 [mylist] が「どもったリスト」でないことを意味しています。[nostutter] の帰納的な定義を記述しなさい。（これは以前の練習問題に出てきた [no_repeats] という述語とは異なるものです。リスト [1,4,1] は repeats ではありますが stutter ではありません。）
*)

Inductive nostutter:  list nat -> Prop :=
 (* FILL IN HERE *)
.

(** Make sure each of these tests succeeds, but you are free
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

(* **** Exercise: 4 stars, advanced (pigeonhole principle) *)
(** **** 練習問題: ★★★★, advanced (pigeonhole principle) *)
(* The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)
(** 「鳩の巣定理（ "pigeonhole principle" ）」は、「数えるあげる」ということについての基本的な事実を提示しています。「もし [n] 個の鳩の巣に[n] 個より多い数のものを入れようとするなら、どのような入れ方をしてもいくつかの鳩の巣には必ず一つ以上のものが入ることになる。」というもので、この、数値に関する見るからに自明な事実を証明するにも、なかなか自明とは言えない手段が必要になります。我々は既にそれを知っているのですが...
	*)

(* First a pair of useful lemmas (we already proved these for lists
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
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)
(** この「鳩の巣定理」を定式化する方法を一つ挙げておきましょう。リスト [l2] が鳩の巣に貼られたラベルの一覧を、リスト [l1] はそのラベルの、アイテムへの割り当ての一覧を表しているとします。もしラベルよりも沢山のアイテムがあったならば、少なくとも二つのアイテムに同じラベルが貼られていることになります。おそらくこの証明には「排中律（ [excluded_middle] ）」が必要になるでしょう。 *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
   intros X l1. induction l1 as [|x l1'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(* FILL IN HERE *)


(* $Date: 2014-02-22 09:43:41 -0500 (Sat, 22 Feb 2014) $ *)
