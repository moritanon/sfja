(** * ProofObjects: Working with Explicit Evidence in Coq *)

Require Export MoreLogic.

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
*)
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
(** これらの証明オブジェクトは、

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

(** At any given moment, Coq has constructed a term with some
    "holes" (indicated by [?1], [?2], and so on), and it knows what
    type of evidence is needed at each hole.  *)

(**
    Each of the holes corresponds to a subgoal, and the proof is
    finished when there are no more subgoals.  At this point, the
    [Theorem] command gives a name to the evidence we've built and
    stores it in the global context. *)

(** Tactic proofs are useful and convenient, but they are not
    essential: in principle, we can always construct the required
    evidence by hand, as shown above. Then we can use [Definition] 
    (rather than [Theorem]) to give a global name directly to a 
    piece of evidence. *)

Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

(** All these different ways of building the proof lead to exactly the
    same evidence being saved in the global environment. *)

Print eight_is_beautiful.
(* ===> eight_is_beautiful    = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'.
(* ===> eight_is_beautiful'   = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful''.
(* ===> eight_is_beautiful''  = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'''.
(* ===> eight_is_beautiful''' = b_sum 3 5 b_3 b_5 : beautiful 8 *)

(** **** Exercise: 1 star (six_is_beautiful) *)
(** Give a tactic proof and a proof object showing that [6] is [beautiful]. *)

Theorem six_is_beautiful :
  beautiful 6.
Proof.
  (* FILL IN HERE *) Admitted.

Definition six_is_beautiful' : beautiful 6 :=
  (* FILL IN HERE *) admit.
(** [] *)

(** **** Exercise: 1 star (nine_is_beautiful) *)
(** Give a tactic proof and a proof object showing that [9] is [beautiful]. *)

Theorem nine_is_beautiful :
  beautiful 9.
Proof.
  (* FILL IN HERE *) Admitted.

Definition nine_is_beautiful' : beautiful 9 :=
  (* FILL IN HERE *) admit.
(** [] *)

(* ##################################################### *)
(** * Quantification, Implications and Functions *)

(** In Coq's computational universe (where we've mostly been living
    until this chapter), there are two sorts of values with arrows in
    their types: _constructors_ introduced by [Inductive]-ly defined
    data types, and _functions_.

    Similarly, in Coq's logical universe, there are two ways of giving
    evidence for an implication: constructors introduced by
    [Inductive]-ly defined propositions, and... functions!

    For example, consider this statement: *)

Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
   intros n H.
   apply b_sum.
   apply b_3.
   apply H.
Qed.

(** What is the proof object corresponding to [b_plus3]? 

    We're looking for an expression whose _type_ is [forall n,
    beautiful n -> beautiful (3+n)] -- that is, a _function_ that
    takes two arguments (one number and a piece of evidence) and
    returns a piece of evidence!  Here it is: *)

Definition b_plus3' : forall n, beautiful n -> beautiful (3+n) := 
  fun (n : nat) => fun (H : beautiful n) =>
    b_sum 3 n b_3 H.

Check b_plus3'.
(* ===> b_plus3' : forall n : nat, beautiful n -> beautiful (3+n) *)

(** Recall that [fun n => blah] means "the function that, given [n],
    yields [blah]."  Another equivalent way to write this definition is: *)

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3+n) := 
  b_sum 3 n b_3 H.

Check b_plus3''.
(* ===> b_plus3'' : forall n, beautiful n -> beautiful (3+n) *)

(** When we view the proposition being proved by [b_plus3] as a function type,
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

(** For example, consider this proposition: *)

Definition beautiful_plus3 : Prop := 
  forall n, forall (E : beautiful n), beautiful (n+3).

(** A proof term inhabiting this proposition would be a function
    with two arguments: a number [n] and some evidence [E] that [n] is
    beautiful.  But the name [E] for this evidence is not used in the
    rest of the statement of [funny_prop1], so it's a bit silly to
    bother making up a name for it.  We could write it like this
    instead, using the dummy identifier [_] in place of a real
    name: *)

Definition beautiful_plus3' : Prop := 
  forall n, forall (_ : beautiful n), beautiful (n+3).

(** Or, equivalently, we can write it in more familiar notation: *)

Definition beatiful_plus3'' : Prop :=
  forall n, beautiful n -> beautiful (n+3). 

(** In general, "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)


(** **** Exercise: 2 stars b_times2 *)

(** Give a proof object corresponding to the theorem [b_times2] from Prop.v *)

Definition b_times2': forall n, beautiful n -> beautiful (2*n) :=
  (* FILL IN HERE *) admit.
(** [] *)



(** **** Exercise: 2 stars, optional (gorgeous_plus13_po) *) 
(** Give a proof object corresponding to the theorem [gorgeous_plus13] from Prop.v *)

Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n):=
   (* FILL IN HERE *) admit.
(** [] *)




(** It is particularly revealing to look at proof objects involving the 
logical connectives that we defined with inductive propositions in Logic.v. *)

Theorem and_example : 
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
   (* Case "left". *)  apply b_0.
   (* Case "right". *)  apply b_3.  Qed.

(** Let's take a look at the proof object for the above theorem. *)

Print and_example. 
(* ===>  conj (beautiful 0) (beautiful 3) b_0 b_3
            : beautiful 0 /\ beautiful 3 *)

(** Note that the proof is of the form
    conj (beautiful 0) (beautiful 3) 
         (...pf of beautiful 3...) (...pf of beautiful 3...)
    as you'd expect, given the type of [conj]. *)

(** **** Exercise: 1 star, optional (case_proof_objects) *)
(** The [Case] tactics were commented out in the proof of
    [and_example] to avoid cluttering the proof object.  What would
    you guess the proof object will look like if we uncomment them?
    Try it and see. *)
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  split.  
    (* Case "left". *) apply HQ. 
    (* Case "right". *) apply HP.  Qed.

(** Once again, we have commented out the [Case] tactics to make the
    proof object for this theorem easier to understand. It is still
    a little complicated, but after performing some simple reduction
    steps, we can see that all that is really happening is taking apart 
    a record containing evidence for [P] and [Q] and rebuilding it in the
    opposite order: *)

Print and_commut.
(* ===>
    and_commut = 
      fun (P Q : Prop) (H : P /\ Q) =>
        (fun H0 : Q /\ P => H0)
            match H with
            | conj HP HQ => (fun (HP0 : P) (HQ0 : Q) => conj Q P HQ0 HP0) HP HQ
            end
      : forall P Q : Prop, P /\ Q -> Q /\ P *)

(** After simplifying some direct application of [fun] expressions to arguments,
we get: *)

(* ===> 
   and_commut = 
     fun (P Q : Prop) (H : P /\ Q) =>
     match H with
     | conj HP HQ => conj Q P HQ HP
     end 
     : forall P Q : Prop, P /\ Q -> Q /\ P *)



(** **** Exercise: 2 stars, optional (conj_fact) *)
(** Construct a proof object demonstrating the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  (* FILL IN HERE *) admit.
(** [] *)


(** **** Exercise: 2 stars, advanced, optional (beautiful_iff_gorgeous) *)

(** We have seen that the families of propositions [beautiful] and
    [gorgeous] actually characterize the same set of numbers.
    Prove that [beautiful n <-> gorgeous n] for all [n].  Just for
    fun, write your proof as an explicit proof object, rather than
    using tactics. (_Hint_: if you make use of previously defined
    theorems, you should only need a single line!) *)

Definition beautiful_iff_gorgeous :
  forall n, beautiful n <-> gorgeous n :=
  (* FILL IN HERE *) admit.
(** [] *)


(** **** Exercise: 2 stars, optional (or_commut'') *)
(** Try to write down an explicit proof object for [or_commut] (without
    using [Print] to peek at the ones we already defined!). *)

(* FILL IN HERE *)
(** [] *)

(** Recall that we model an existential for a property as a pair consisting of 
a witness value and a proof that the witness obeys that property. 
We can choose to construct the proof explicitly. 

For example, consider this existentially quantified proposition: *)
Check ex.

Definition some_nat_is_even : Prop := 
  ex _ ev.

(** To prove this proposition, we need to choose a particular number
    as witness -- say, 4 -- and give some evidence that that number is
    even. *)

Definition snie : some_nat_is_even := 
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).


(** **** Exercise: 2 stars, optional (ex_beautiful_Sn) *)
(** Complete the definition of the following proof object: *)

Definition p : ex _ (fun n => beautiful (S n)) :=
(* FILL IN HERE *) admit.
(** [] *)



(* ##################################################### *)
(** * Giving Explicit Arguments to Lemmas and Hypotheses *)

(** Even when we are using tactic-based proof, it can be very useful to
understand the underlying functional nature of implications and quantification. 

For example, it is often convenient to [apply] or [rewrite] 
using a lemma or hypothesis with one or more quantifiers or 
assumptions already instantiated in order to direct what
happens.  For example: *)

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


(** In this case, giving just one argument would be sufficient. *)

Lemma plus_comm_r' : forall a b c, c + (b + a) = c + (a + b).
Proof.
   intros a b c.
   rewrite (plus_comm b). 
   reflexivity.  Qed.

(** Arguments must be given in order, but wildcards (_)
may be used to skip arguments that Coq can infer.  *)

Lemma plus_comm_r'' : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros a b c.
  rewrite (plus_comm _ a).
  reflexivity. Qed.

(** The author of a lemma can choose to declare easily inferable arguments
to be implicit, just as with functions and constructors. 

  The [with] clauses we've already seen is really just a way of
  specifying selected arguments by name rather than position:  *)

Lemma plus_comm_r''' : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros a b c.
  rewrite plus_comm with (n := b). 
  reflexivity. Qed.


(** **** Exercise: 2 stars (trans_eq_example_redux) *)
(** Redo the proof of the following theorem (from MoreCoq.v) using
an [apply] of [trans_eq] but _not_ using a [with] clause. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ##################################################### *)
(** * Programming with Tactics (Optional) *)

(** If we can build proofs with explicit terms rather than
tactics, you may be wondering if we can build programs using
tactics rather than explicit terms.  Sure! *)

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

(** Notice that we terminate the [Definition] with a [.] rather than with
[:=] followed by a term.  This tells Coq to enter proof scripting mode
to build an object of type [nat -> nat].  Also, we terminate the proof
with [Defined] rather than [Qed]; this makes the definition _transparent_
so that it can be used in computation like a normally-defined function.  

This feature is mainly useful for writing functions with dependent types,
which we won't explore much further in this book.
But it does illustrate the uniformity and orthogonality of the basic ideas in Coq. *)

(* $Date: 2014-06-05 07:22:21 -0400 (Thu, 05 Jun 2014) $ *)
