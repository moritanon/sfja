(* * Lists: Working with Structured Data *)
(** * Lists_J: 構造化データと一緒に *)

Require Export Induction_J.

Module NatList.

(* ###################################################### *)
(*  * Pairs of Numbers *)
(** * 数のペア *)

(*  In an [Inductive] type definition, each constructor can take
    any number of arguments -- none (as with [true] and [O]), one (as
    with [S]), or more than one, as here: *)
(**
   [Inductive] による型定義では、各構成子は任意の個数の引数を取ることができました。
   [true] や [O] のように引数のないもの、 [S] のようにひとつのもの、また、ふたつ以上の取るものも以下のように定義することができます。
   *)

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

(*  This declaration can be read: "There is one way to construct
    a pair of numbers: by applying the constructor [pair] to two
    arguments of type [nat]." *)
(** この定義は以下のように読めます。すなわち、「数のペアを構成する方法がひとつある。それは、構成子 [pair] を [nat] 型のふたつの引数に適用することである」。*)

Check (pair 3 5).

(*  Here are two simple functions for extracting the first and
    second components of a pair.  The definitions also illustrate how
    to do pattern matching on two-argument constructors. *)
(** ここに二つのペアの一つめと二つめの要素を展開する簡単な関数があります。これら定義もまたどのように二引数のコンストラクタにパターンマッチするかを示しています。)*)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(*  Since pairs are used quite a bit, it is nice to be able to
    write them with the standard mathematical notation [(x,y)] instead
    of [pair x y].  We can tell Coq to allow this with a [Notation]
    declaration. *)
(** ペアはよく使うものなので、 [pair x y] ではなく、数学の標準的な記法で [(x, y)] と書けるとよいでしょう。このような記法を使うためには [Notation] 宣言を使います。
   *)

Notation "( x , y )" := (pair x y).

(* The new notation can be used both in expressions and in
    pattern matches (indeed, we've seen it already in the previous
    chapter -- this works because the pair notation is actually
    provided as part of the standard library): *)
(** こうして定義した新しい記法（notation）は、式だけでなくパターンマッチに使うこともできます。（実際には、前章でも見たように、ペアの記法は標準ライブラリの一部として提供されているので、これは動作します。） *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Let's try to prove a few simple facts about pairs.

    If we state things in a particular (and slightly peculiar) way, we
    can complete proofs with just reflexivity (and its built-in
    simplification): *)
(**
   それでは、数のペアに関する簡単な事実をいくつか証明してみましょう。
   
   もし、特定の(僅かに奇妙な)方法でものごとを述べておけば、単に reflexivity（と組み込みの簡約）だけで証明することができます。
   *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(*  But [reflexivity] is not enough if we state the lemma in a more
    natural way: *)
(** しかし、補題を以下のようにより自然な書き方をした場合は、反射律では足りないことに注意してください。 *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* なにも変わらない！ *)
Abort.

(* We have to expose the structure of [p] so that [simpl] can
    perform the pattern match in [fst] and [snd].  We can do this with
    [destruct].

    Notice that, unlike for [nat]s, [destruct] doesn't generate an
    extra subgoal here.  That's because [natprod]s can only be
    constructed in one way.  *)
(** [simpl] で [fst] や [snd] の中のパターンマッチを実行できるよう、 [p] の構造を明らかにする必要があります。これには [destruct] を使います。*)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(*  Notice that, unlike its behavior with [nat]s, [destruct]
    doesn't generate an extra subgoal here.  That's because [natprod]s
    can only be constructed in one way. *)
(** [nat] の場合と異なり、 [destruct] でサブゴールが増えることはありません。これは、 [natprod] の構成法がひとつしかないからです。 *)

(* **** Exercise: 1 star (snd_fst_is_swap) *)
(** **** 練習問題: ★ (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star, optional (fst_swap_is_snd) *)
(** **** 練習問題: ★, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(* * Lists of Numbers *)
(** * 数のリスト *)

(*  Generalizing the definition of pairs, we can describe the
    type of _lists_ of numbers like this: "A list is either the empty
    list or else a pair of a number and another list." *)
(** ペアの定義を少し一般化すると、数のリストは次のように表すことができます。すなわち、「リストは、空のリストであるか、または数と他のリストをペアにしたものである」。
   *)

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

(*  For example, here is a three-element list: *)
(** たとえば、次の定義は要素が三つのリストです *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(*  As with pairs, it is more convenient to write lists in
    familiar programming notation.  The following declarations
    allow us to use [::] as an infix [cons] operator and square
    brackets as an "outfix" notation for constructing lists. *)
(**
   ペアの場合と同じく、リストをプログラミング言語で馴染んだ記法で書くことができると便利でしょう。以下の宣言では [::] を中置の [cons] 演算子として使えるようにし、角括弧をリストを構成するための外置（outfix）記法として使えるようにしています。
   *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(*  It is not necessary to understand the detail of these
    declarations, but in case you are interested, here is roughly
    what's going on.  The [right associativity] annotation tells Coq
    how to parenthesize expressions involving several uses of [::] so
    that, for example, the next three declarations mean exactly the
    same thing: *)
(** これら宣言の詳細を理解する必要はありませんが、興味のある読者のために簡単に説明しておきます。
   [right associativity] アノテーションは複数の [::] を使った式にどのように括弧を付けるか指示するものです。例えば、次のみっつの宣言はすべて同じ意味に解釈されます。
   *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(*  The [at level 60] part tells Coq how to parenthesize
    expressions that involve both [::] and some other infix operator.
    For example, since we defined [+] as infix notation for the [plus]
    function at level 50,

  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

   the [+] operator will bind tighter than [::], so [1 + 2 :: [3]]
   will be parsed, as we'd expect, as [(1 + 2) :: [3]] rather than [1
   + (2 :: [3])].

   (Expressions like "[1 + 2 :: [3]]" can be a little confusing when 
   you read them in a .v file.  The inner brackets, around 3, indicate 
   a list, but the outer brackets, which are invisible in the HTML 
   rendering, are there to instruct the "coqdoc" tool that the bracketed 
   part should be displayed as Coq code rather than running text.)

   The second and third [Notation] declarations above introduce the
   standard square-bracket notation for lists; the right-hand side of
   the third one illustrates Coq's syntax for declaring n-ary
   notations and translating them to nested sequences of binary
   constructors. *)
(**
   [at level 60] の部分は [::] を他の中置演算子といっしょに使っている式にどのように括弧を付けるかを指示するものです。例えば、 [+] を [plus] に対する level 50 の中置記法として定義したので、
Notation "x + y" := (plus x y)
                    (at level 50, left associativity).
   [+] は [::] よりも強く結合し、 [1 + 2 :: [3]] は期待通り、 [1 + (2 :: [3])] ではなく [(1 + 2) :: [3]] と構文解析されます。

   ("[1 + 2 :: [3]]" のような式は、.vファイルを読むときに少し混乱させられます。内側の3を囲む括弧はリストを意味していますが、外側の括弧はHTMLレンダリン時に見えなくなりますし、coqdoc 用の命令で、角括弧内の部分をそのままのテキストではなく Coq のコードとして表示するよう指示するものです。）

   上の二番目と三番目の [Notation] 宣言は標準的なリストの記法を導入するためのものです。三番目の [Notation] の右辺は、 n 引数の記法を二項構成子の入れ子に変換する記法を定義するための Coq の構文の例です。
   *)

(*  *** Repeat *)
(** *** 繰り返し *)

(*  A number of functions are useful for manipulating lists.
    For example, the [repeat] function takes a number [n] and a
    [count] and returns a list of length [count] where every element
    is [n]. *)
(** リストを操作するために便利な関数がいくつかあります。例えば、 [repeat] 関数は数 [n] と [count] を取り、各要素が [n] で長さ [count] のリストを返します。 *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(*  *** Length *)
(** *** 長さ *)
(*  The [length] function calculates the length of a list. *)
(** [length] 関数はリストの長さを計算します。 *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* The [app] ("append") function concatenates two lists. *)
(** [app] （"append"）関数はふたつのリストを連結します。 *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(* Actually, [app] will be used a lot in some parts of what
    follows, so it is convenient to have an infix operator for it. *)
(** [app] はこの後でよく使うので、中置演算子を用意しておくと便利でしょう。 *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(*  *** Head (with default) and Tail *)
(** *** Head (デフォルトつき) と Tail *)

(*  Here are two more small examples of programming with lists.
    The [hd] function returns the first element (the "head") of the
    list, while [tl] returns everything but the first
    element (the "tail").
    Of course, the empty list has no first element, so we
    must pass a default value to be returned in that case.  *)
(** もうふたつリストを使った例を見てみましょう。 [hd] 関数はリストの最初の要素（先頭—— head）を返し、 [tl] は最初の要素を除いた全て(つまりしっぽ)を返します。空のリストには最初の要素はありませんから、その場合に返す値を引数として渡しておかなければなりません。 *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

(*  **** Exercise: 2 stars, recommended (list_funs) *)
(** **** 練習問題: ★★, recommended (list_funs) *)
(*  Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)
(** 以下の [nonzeros]、 [oddmembers]、 [countoddmembers] の定義を完成させなさい。そしてtestを見てこれらの関数が何を行なうのか理解しなさい。  *)

Fixpoint nonzeros (l:natlist) : natlist :=
  (* FILL IN HERE *) admit.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  (* FILL IN HERE *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist :=
  (* FILL IN HERE *) admit.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  (* FILL IN HERE *) Admitted.

Fixpoint countoddmembers (l:natlist) : nat :=
  (* FILL IN HERE *) admit.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  (* FILL IN HERE *) Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  (* FILL IN HERE *) Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars (alternate) *)
(** **** 練習問題: ★★★ (alternate) *)
(* Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural and elegant way of writing [alternate] will fail
    to satisfy Coq's requirement that all [Fixpoint] definitions be
    "obviously terminating."  If you find yourself in this rut, look
    for a slightly more verbose solution that considers elements of
    both lists at the same time.  (One possible solution requires
    defining a new kind of pairs, but this is not the only way.)  *)
(**
   [alternate] の定義を完成させなさい。この関数は、ふたつのリストから交互に要素を取り出しひとつに「綴じ合わせる」関数です。具体的な例は下のテストを見てください。

   注意: [alternate] の自然でエレガントな定義のひとつは、 「[Fixpoint] による定義は『明らかに停止する』ものでなければならない」という Coq の要求を満たすことができません。このパターンにはまってしまったようであれば、両方のリストの要素を同時に見ていくような少し冗長な方法を探してみてください。(一つのありうる解法は、新しい種類のペアを定義することですが、それだけが解法というわけではありません。) *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  (* FILL IN HERE *) admit.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  (* FILL IN HERE *) Admitted.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  (* FILL IN HERE *) Admitted.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  (* FILL IN HERE *) Admitted.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(* ** Bags via Lists *)
(** ** リストを使ったバッグ *)

(*  A [bag] (or [multiset]) is like a set, but each element
    can appear multiple times rather than just once.  One possible
    implementation is to represent a bag of numbers as a list. *)
(** バッグ（[bag]。または多重集合—— [multiset]）は集合のようなものですが、それぞれの要素が一度ではなく複数回現れることのできるようなものを言います。実装としてありうるのは数のバッグをリストで表現するというものでしょう。
   *)

Definition bag := natlist.

(*  **** Exercise: 3 stars (bag_functions) *)
(** **** 練習問題: ★★★ (bag_functions) *)
(*  Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)
(**
   バッグに対する [count]、 [sum]、 [add]、 [member] 関数の定義を完成させなさい。
   *)

Fixpoint count (v:nat) (s:bag) : nat :=
  (* FILL IN HERE *) admit.

(*  All these proofs can be done just by [reflexivity]. *)
(** 下の証明はすべて [reflexivity] だけでできます。 *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* FILL IN HERE *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* FILL IN HERE *) Admitted.

(*  Multiset [sum] is similar to set [union]: [sum a b] contains
    all the elements of [a] and of [b].  (Mathematicians usually
    define [union] on multisets a little bit differently, which
    is why we don't use that name for this operation.)
    For [sum] we're giving you a header that does not give explicit
    names to the arguments.  Moreover, it uses the keyword
    [Definition] instead of [Fixpoint], so even if you had names for
    the arguments, you wouldn't be able to process them recursively.
    The point of stating the question this way is to encourage you to
    think about whether [sum] can be implemented in another way --
    perhaps by using functions that have already been defined.  *)
(**
   多重集合の [sum] （直和。または非交和）は集合の [union] （和）と同じようなものです。 [sum a b] は [a] と [b] の両方の要素を持つ多重集合です。（数学者は通常、多重集合の [union] にもう少し異なる定義を与えます。それが、この関数の名前を [union] にしなかった理由です。） [sum] のヘッダには引数の名前を与えませんでした。さらに、 [Fixpoint] ではなく [Definition] を使っています。ですから、引数に名前がついていたとしても再帰的な処理はできません。問題をこのように設定したのは、 [sum] を（定義済みの関数を使うといった）別の方法で定義できないか考えさせるためです。
   *)

Definition sum : bag -> bag -> bag :=
  (* FILL IN HERE *) admit.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.

Definition add (v:nat) (s:bag) : bag :=
  (* FILL IN HERE *) admit.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.

Definition member (v:nat) (s:bag) : bool :=
  (* FILL IN HERE *) admit.

Example test_member1:             member 1 [1;4;1] = true.
 (* FILL IN HERE *) Admitted.

Example test_member2:             member 2 [1;4;1] = false.
 (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars, optional (bag_more_functions) *)
(** **** 練習問題: ★★★, optional (bag_more_functions) *)
(* Here are some more bag functions for you to practice with. *)
(** 練習として、さらにいくつかの関数を作成してください。 *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* When remove_one is applied to a bag without the number to remove,
     it should return the same bag unchanged. *)
  (* [remove_one] を削除すべき数のないバッグに適用した場合は、同じバッグを変更せずに返す *)
  (* FILL IN HERE *) admit.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  (* FILL IN HERE *) Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  (* FILL IN HERE *) Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  (* FILL IN HERE *) Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* FILL IN HERE *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  (* FILL IN HERE *) admit.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* FILL IN HERE *) Admitted.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* FILL IN HERE *) Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  (* FILL IN HERE *) admit.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 (* FILL IN HERE *) Admitted.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, recommended (bag_theorem) *)
(** **** 練習問題: ★★★, recommended (bag_theorem) *)
(*  Write down an interesting theorem [bag_theorem] about bags
    involving the functions [count] and [add], and prove it. For
    this, replace the [admit] command below with the statement of your
    theorem. Note that, since this problem is somewhat open-ended,
    it's possible that you may come up with a theorem which is true,
    but whose proof requires techniques you haven't learned yet.  Feel
    free to ask for help if you get stuck! *)
(**
   [count] や [add] を使ったバッグに関する面白い定理書き、それを証明しなさい。この問題はいわゆる自由課題で、真になることがわかっていても、証明にはまだ習っていない技を使わなければならない定理を思いついてしまうこともあります。証明に行き詰まってしまったら気軽に質問してください。*)

Theorem bag_theorem :
  (* FILL IN HERE *) admit.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(*  * Reasoning About Lists *)
(** * リストに関する推論 *)

(*  As with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification.  For
    example, the simplification performed by [reflexivity] is enough
    for this theorem... *)
(**
   数の場合と同じく、リスト処理関数についての簡単な事実はもっぱら簡約のみで証明できることがあります。たとえば、次の定理は [reflexivity] で行われる簡約だけで証明できます。
   *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(*  ... because the [[]] is substituted into the match
    "scrutinee" in the definition of [app], allowing the match itself
    to be simplified. *)
(**
   これは、 [[]] が [app] の定義のパターンマッチ部分に代入され、パターンマッチ自体が簡約できるようになるからです。
   *)

(*  Also, as with numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list. *)
(**
   またこれも数の場合と同じように、未知のリストの形（空であるかどうか）に応じた場合分けも有効です。
   *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

(*  Here, the [nil] case works because we've chosen to define
    [tl nil = nil]. Notice that the [as] annotation on the [destruct]
    tactic here introduces two names, [n] and [l'], corresponding to
    the fact that the [cons] constructor for lists takes two
    arguments (the head and tail of the list it is constructing). *)
(** ここで、 [nil] の場合がうまく行くのは、 [tl nil = nil] と定義したからです。ここでは、 [destruct] タクティックの [as] で [n] と [l'] のふたつの名前を導入しました。これは、リストの [cons] 構成子が引数をふたつ（構成するリストの頭部と尾部）取ることに対応しています。
   *)

(*  Usually, though, interesting theorems about lists require
    induction for their proofs. *)
(** ただし、リストに関する興味深い定理の証明には、帰納法が必要になるのが普通です。
   *)

(* ###################################################### *)
(* ** Micro-Sermon *)
(** ** お小言 *)

(*  Simply reading example proof scripts will not get you very far!
    It is important to work through the details of each one, using Coq
    and thinking about what each step achieves.  Otherwise it is more
    or less guaranteed that the exercises will make no sense when you
    get to them.  'Nuff said. *)
(** 単に例題の証明を読んでいるだけでは大きな進歩は望めません！ 各証明を実際に Coq で動かし、各ステップがその証明にどのようにかかわっているか考え、道筋をていねいになぞっていくことがとても大切です。そうしなければ、演習には何の意味もありません。 いいかげんしつこいと言われるかもしれませんが。*)

(* ###################################################### *)
(*  ** Induction on Lists *)
(** ** リスト上の帰納法 *)

(* Proofs by induction over datatypes like [natlist] are a
    little less familiar than standard natural number induction, but
    the idea is equally simple.  Each [Inductive] declaration defines
    a set of data values that can be built up using the declared
    constructors: a boolean can be either [true] or [false]; a number
    can be either [O] or [S] applied to another number; a list can be
    either [nil] or [cons] applied to a number and a list.

    Moreover, applications of the declared constructors to one another
    are the _only_ possible shapes that elements of an inductively
    defined set can have, and this fact directly gives rise to a way
    of reasoning about inductively defined sets: a number is either
    [O] or else it is [S] applied to some _smaller_ number; a list is
    either [nil] or else it is [cons] applied to some number and some
    _smaller_ list; etc. So, if we have in mind some proposition [P]
    that mentions a list [l] and we want to argue that [P] holds for
    _all_ lists, we can reason as follows:

      - First, show that [P] is true of [l] when [l] is [nil].

      - Then show that [P] is true of [l] when [l] is [cons n l'] for
        some number [n] and some smaller list [l'], assuming that [P]
        is true for [l'].

    Since larger lists can only be built up from smaller ones,
    eventually reaching [nil], these two arguments together establish
    the truth of [P] for all lists [l].  Here's a concrete example: *)
(**
   [natlist] のようなデータ型に対して帰納法で証明をするのは、普通の自然数に対する帰納法よりも馴染みにくさを感じたことでしょう。しかし、基本的な考え方は同じくらい簡単です。 [Inductive] 宣言では、宣言した構成子から構築できるデータ方の集合を定義しています。例えば、ブール値では [true] と [false] のいずれかであり、数では [O] か数に対する [S] のいずれか、リストであれば [nil] か数とリストに対する [cons] のいずれかです。

   さらに言えば、帰納的に定義された集合の要素になるのは、宣言した構成子を互いに適用したものだけです。このことがそのまま帰納的に定義された集合に関する推論の方法になります。すなわち、数は [O] であるか、より小さい数に [S] を適用したものであるかのいずれかです。リストは [nil] であるか、何らかの数とより小さいリストに [cons] を適用したものです。他のものも同様です。ですから、あるリスト [l] に関する命題 [P] があり、 [P] がすべてのリストに対して成り立つことを示したい場合には、次のように推論します。

      - まず、 [l] が [nil] のとき [P] が [l] について成り立つことを示す。

      - それから、 [l] が [cons n l'] であるとき、ある数 [n] とより小さいリスト [l'] に対して、 [P] が [l'] について成り立つと仮定すれば [P] が [l] についても成り立つことを示す。

     大きなリストはそれより小さなリストから作り出され、少しずつ [nil] に近付いて行きます。よって、このふたつのことからすべてのリスト [l] に関して [P] が真であることが言えます。具体的な例で説明しましょう。
     *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(*  Notice that, as when doing induction on natural numbers, the
    [as...] clause provided to the [induction] tactic gives a name to
    the induction hypothesis corresponding to the smaller list [l1']
    in the [cons] case. Once again, this Coq proof is not especially
    illuminating as a static written document -- it is easy to see
    what's going on if you are reading the proof in an interactive Coq
    session and you can see the current goal and context at each
    point, but this state is not visible in the written-down parts of
    the Coq proof.  So a natural-language proof -- one written for
    human readers -- will need to include more explicit signposts; in
    particular, it will help the reader stay oriented if we remind
    them exactly what the induction hypothesis is in the second
    case. *)
(** 自然数に関する帰納法を行うときと同じように、[as...]句 [induction]タクティックによって導出される[as...]句は、[cons]のケース中のより小さなリスト[l1']に対応する帰納仮説に名前を与えてくれます。 蒸し返すようですが、この Coq の証明はこうして単に静的なテキストとして読んでいる限り、さほど明白で分かりやすいものではありません。 Coq の証明は、 Coq を対話的に動かしながらポイントごとに「現在のゴールは何か」「コンテキストに何が出ているか」を見て、証明が今どうなっているかを読み下していくことで理解されるようになっています。しかし、このような証明の途中経過は、全てが証明結果として書き出されるわけではありません。だからこそ、人間向けの自然言語での証明には証明の筋道がわかるように証明の指針を書いておく必要があるのです。特に、読者が流れを見失わないよう、ふたつめの場合分けで使う帰納法の仮定が何だったのかわかるようにしておくのは有益なはずです。
   *)

(*  For comparison, here is an informal proof of the same theorem. *)
(** 比較のために同じ定理の非形式的な証明を書いておきます。*)

(*  _Theorem_: For all lists [l1], [l2], and [l3], 
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Proof_: By induction on [l1].

   - First, suppose [l1 = []].  We must show

       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

     which follows directly from the definition of [++].

   - Next, suppose [l1 = n::l1'], with

       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

     (the induction hypothesis). We must show

       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

     By the definition of [++], this follows from

       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

     which is immediate from the induction hypothesis.  [] *)

(**
   定理: 任意のリスト [l1]、 [l2]、 [l3] について、
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)]
     が成り立つ。

   証明: [l1] についての帰納法で証明する

   - まず、 [l1 = []] と仮定して
       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3)
     を示す。これは [++] の定義から自明である。

   - 次に [l1 = n::l1'] かつ
       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
     （帰納法の仮定）と仮定して
       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3)
     を示す。 [++] の定義から、この式は以下のように変形できる。
       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3))
     これは帰納法の仮定から直接導かれる。  [] *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(*  *** Reversing a list *)
(** *** リストの反転 *)

(*  For a slightly more involved example of inductive proof over
    lists, suppose we use [app] to define a list-reversing function
    [rev]: *)
(** リストに対する帰納的証明のもう少し入り組んだ例を見てみましょう。リストを反転させる関数[rev]を定義するために、[app]を使ってみましょう。*)


Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(*  *** Proofs about reverse *)
(** *** reverseについての証明 *)

(*  Now let's prove some theorems about our newly defined [rev].
    For something a bit more challenging than what we've seen, let's
    prove that reversing a list does not change its length.  Our first
    attempt gets stuck in the successor case... *)
(**
   新しく定義した [rev] に関する定理を証明してみましょう。ここまでの帰納的証明よりも難易度の高いものですが、リストを反転しても長さの変わらないことを証明します。下の方法では、ふたつめの場合分けで行き詰まってしまいます。
   *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    (* これはトリッキーなケースです。いつものように、簡約から始めてみましょう *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving [++], but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
     (* どうも行き詰まってしまったようです。ゴールは [++]を含む等式ですが、
       コンテキスト中にも大域環境中にも 役に立ちそうな等式はありません。 
       IHを使用してgoalを書き換えることで、少しだけ進展しますが・・・*)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
    (* これ以上は進めません *)
Abort.

(** So let's take the equation relating [++] and [length] that
    would have enabled us to make progress and prove it as a separate
    lemma. *)
(** この [++] と [length]に関する等式が成り立つことを示せれば証明が先に進むはずです。この式を取り出して別個の補題として証明してみましょう。 *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(*  Note that, to make the lemma as general as possible, we
    quantify over _all_ [natlist]s, not just those that result from an
    application of [rev].  This should seem natural, because the truth
    of the goal clearly doesn't depend on the list having been
    reversed.  Moreover, it is easier to prove the more general
    property. *)
(** 可能な限り補題を一般的なものにするために、[natlist]の全てを定量化して、[rev]の適用に起因するものだけに限定しないようにしましょう。このことは当然のように見えます。なぜなら、真のゴールは、反転したリストだけに明確に依存していません。さらに、もっと一般的な特質を証明することが簡単になります。
*)

(* Now we can complete the original proof. *)
(** これで、元々の証明ができるようになりました。 *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm.
    rewrite -> IHl'. reflexivity.  Qed.

(*  For comparison, here are _informal_ proofs of these two theorems: 

    _Theorem_: For all lists [l1] and [l2],
       [length (l1 ++ l2) = length l1 + length l2].

    _Proof_: By induction on [l1].

    - First, suppose [l1 = []].  We must show

        length ([] ++ l2) = length [] + length l2,

      which follows directly from the definitions of
      [length] and [++].

    - Next, suppose [l1 = n::l1'], with

        length (l1' ++ l2) = length l1' + length l2.

      We must show

        length ((n::l1') ++ l2) = length (n::l1') + length l2).

      This follows directly from the definitions of [length] and [++]
      together with the induction hypothesis. [] *)
(** 対比として、この二つの定理の非形式的な証明を見てみましょう

    定理: 任意の数 [n] とリスト [l] について
       [length (snoc l n) = S (length l)] が成り立つ。

    証明: [l] についての帰納法で証明する。

    - まず、 [l = []] と仮定して
        length ([] ++ l2) = length [] + length l2,
      を示す。これは [length] と [++] の定義から直接導かれる。

    - 次に、 [l = n'::l1'] かつ
        length (l1' ++ l2) = length l1' + length l2.
      と仮定して、
        length ((n::l1') ++ l2) = length (n::l1') + length l2).
      を示す。 [length] と [++] の定義から次のように変形できる。
      これは[length]と[++]の定義と帰納法の仮定から直接導くことが出来る。 [] *)

(*  _Theorem_: For all lists [l], [length (rev l) = length l].
    
    _Proof_: By induction on [l].

      - First, suppose [l = []].  We must show

          length (rev []) = length [],

        which follows directly from the definitions of [length]
        and [rev].

      - Next, suppose [l = n::l'], with

          length (rev l') = length l'.

        We must show

          length (rev (n :: l')) = length (n :: l').

        By the definition of [rev], this follows from

          length ((rev l') ++ [n]) = S (length l')

        which, by the previous lemma, is the same as

          length (rev l') + length [n] = S (length l').

        This follows directly from the induction hypothesis and the
        definition of [length]. [] *)

(** 定理: 任意のリスト [l] について [length (rev l) = length l] が成り立つ。

    証明: [l] についての帰納法で証明する。

      - まず、 [l = []] と仮定して
          length (rev []) = length []
        を示す。これは [length] と [rev] の定義から直接導かれる

      - 次に、 [l = n::l'] かつ
          length (rev l') = length l'
        と仮定して、
          length (rev (n :: l')) = length (n :: l')
        を示す。 [rev] の定義から次のように変形できる。
          length ((rev l') ++ [n]) = S (length l')
        これは、先程の補題から、次のものと同じである。
          length (rev l') + length [n] = S (length l').
        これは、帰納法の仮定と[length]の定義から明らかである。 [] *)

(*  The style of these proofs is rather longwinded and pedantic.
    After the first few, we might find it easier to follow proofs that
    give fewer details (which can easily work out in our own minds or
    on scratch paper if necessary) and just highlight the non-obvious
    steps.  In this more compressed style, the above proof might look
    like this: *)
(** こういった証明のスタイルは、長ったらしく杓子定規な感じがします。最初の何回かは別にして、それ以後は、細かいところは省略してしまって（必要であれば、頭の中や紙の上で追うのは簡単です）、自明でないところにだけ注目した方がわかりやすいでしょう。そのように省略がちに書けば、上の証明は次のようになります。
   *)

(* _Theorem_:
     For all lists [l], [length (rev l) = length l].

    _Proof_: First, observe that [length (l ++ [n]) = S (length l)]
     for any [l] (this follows by a straightforward induction on [l]).
     The main property again follows by induction on [l], using the
     observation together with the induction hypothesis in the case
     where [l = n'::l']. [] *)
(** 定理:
     任意のリスト [l] について [length (rev l) = length l] が成り立つ。

    証明: まず、任意の [l] について [length (l ++ [n]) = S (length l)]
     であることに注目する。これは [l] についての帰納法から自明である。このとき、もとの性質についても [l] についての帰納法から自明である。 [l = n'::l'] の場合については、上の性質と帰納法の仮定から導かれる。 [] *)

(*  Which style is preferable in a given situation depends on
    the sophistication of the expected audience and how similar the
    proof at hand is to ones that the audience will already be
    familiar with.  The more pedantic style is a good default for our
    present purposes. *)
(** どちらのスタイルの方が好ましいかは、読み手の証明への馴れや、彼らが今まで触れてきた証明がどちらに近いかに依ります。本書の目的としては冗長なスタイルの方が我々の学習目的には好ましいでしょう。 *)


(* ###################################################### *)
(** ** [SearchAbout] *)

(*  We've seen that proofs can make use of other theorems we've
    already proved, e.g., using [rewrite].  But in order to refer to a
    theorem, we need to know its name!  Indeed, it is often hard even
    to remember what theorems have been proven, much less what they
    are called.

    Coq's [SearchAbout] command is quite helpful with this.  Typing
    [SearchAbout foo] will cause Coq to display a list of all theorems
    involving [foo].  For example, try uncommenting the following line 
    to see a list of theorems that we have proved about [rev]: *)
(**
   これまで見てきたように、定理を証明するには既に証明した定理を使うことができます。以降では [rewrite] 以外にも、証明済みの定理を使う方法があることを紹介します。ところで、定理を使うためにはその名前を知らなければなりません! 確かに今まで何の定理を証明したかを覚えておくだけでも大変なのに、それが何という名前で呼ばれているかを覚えておくなんて無理ゲーです。

   Coq の [SearchAbout] コマンドはこのような場合にとても便利です。 [SearchAbout foo] とすると、 [foo] に関する証明がすべて表示されます。例えば、次の行のコメントを外せば、これまで [rev] に関して証明した定理が表示されます。
   *)

(* SearchAbout rev. *)

(*  Keep [SearchAbout] in mind as you do the following exercises and
    throughout the rest of the book; it can save you a lot of time!

    If you are using ProofGeneral, you can run [SearchAbout] with [C-c
    C-a C-a]. Pasting its response into your buffer can be
    accomplished with [C-c C-;]. *)
(** この本の残りの練習問題に取り組む際には、常に [SearchAbout] コマンドのことを頭の隅に置いておくといいでしょう。そうすることでずいぶん時間の節約ができるはずです。

  もし ProofGeneral を使っているのなら、 [C-c C-a C-a] とキー入力をすることで [SearchAbout] コマンドを使うことができます。その結果をエディタに貼り付けるには [C-c C-;] を使うことができます。 *)


(* ###################################################### *)
(* ** List Exercises, Part 1 *)
(** ** リストについての練習問題 Part 1 *)

(* **** Exercise: 3 stars, recommended (list_exercises) *)
(* More practice with lists. *)
(** **** 練習問題: ★★★, recommended (list_exercises) *)
(** リストについてさらに練習しましょう。 *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  (* FILL IN HERE *) Admitted.


Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.

(*  There is a short solution to the next one.  If you find yourself
    getting tangled up, step back and try to look for a simpler
    way. *)
(**
   次の問題には簡単な解法があります。こんがらがってしまったようであれば、少し戻って単純な方法を探してみましょう。
   *)

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  (* FILL IN HERE *) Admitted.


Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE *) Admitted.

(* An exercise about your implementation of [nonzeros]: *)
(** 前に書いた [nonzeros] 関数に関する練習問題です。 *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 2 stars, (beq_natlist) *)
(*  Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. *)
(** **** 練習問題: ★★, recommended (beq_natlist) *)
(** 数のリストふたつを比較し等価性を判定する関数 [beq_natlist] の定義を完成させなさい。そして、 [beq_natlist l l] が任意のリスト [l] で [true] となることを証明しなさい。 *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  (* FILL IN HERE *) admit.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
 (* FILL IN HERE *) Admitted.
Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
(* FILL IN HERE *) Admitted.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
 (* FILL IN HERE *) Admitted.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** List Exercises, Part 2 *)

(* **** Exercise: 3 stars, optional (bag_proofs) *)
(*  Here are a couple of little theorems to prove about your
    definitions about bags earlier in the file. *)
(** **** 練習問題: ★★★, optional (bag_proofs) *)
(**
   この章の前の問題のなかのbagsについてのあなたの定義を証明するための2、3の定理があります。
   *)

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(*  The following lemma about [leb] might help you in the next proof. *)
(** 以下の [leb] に関する補題は、この次の証明に使えるかもしれません。 *)

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, optional (bag_count_sum) *)
(*  Write down an interesting theorem [bag_count_sum] about bags
    involving the functions [count] and [sum], and prove it.*)
(** **** 練習問題: ★★★, optional (bag_count_sum) *)
(** バッグについて [count] と [sum] を使った定理を考え、それを証明しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(*  **** Exercise: 4 stars, advanced (rev_injective)  *)
(*  Prove that the [rev] function is injective -- that is,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

(There is a hard way and an easy way to do this.) *)
(** **** 練習問題: ★★★★, optional (rev_injective) *)
(** [rev] 関数が単射である、すなわち
    forall X (l1 l2 : list X), rev l1 = rev l2 -> l1 = l2
であることを証明しなさい。

この練習問題には簡単な解法と難しい解法があります。
*)

(* FILL IN HERE *)
(** [] *)


(* ###################################################### *)
(* * Options *)
(** * オプション *)

(*  Suppose we want to write a function that returns the [n]th
    element of some list.  If we give it type [nat -> natlist -> nat],
    then we'll have to choose some number to return when the list is
    too short... *)
(** 何かのリストの[n]番目の要素を返却する関数を書きたくなったとします。その関数に、[nat -> natlist -> nat]という型を与えた場合、リストがnに対して短すぎる場合も何か数字を選ぶ必要があります... *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* arbitrary! テキトウ！ *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

(*  This solution is not so good: If [nth_bad] returns [42], we
    can't tell whether that value actually appears on the input
    without further processing. A better alternative is to change the
    return type of [nth_bad] to include an error value as a possible
    outcome. We call this type [natoption]. *)
(** この解法はあまりよくありません: もし[nth_bad]が[42]を返却する場合、その値が実際にインプットに対応する値か分からないからです。もっと良い解法は、nth_badの型をエラーの値を出力として含むように変えることです。我々はこの型を[natoption]と呼びます。*)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(*  We can then change the above definition of [nth_bad] to
    return [None] when the list is too short and [Some a] when the
    list has enough members and [a] appears at position [n]. We call
    this new function [nth_error] to indicate that it may result in an
    error. *)
(** 上記の[nth_bad]の定義を以下のように変えます。
    listが短かすぎる場合は、[None]を返却します。
    listが十分な長さを持ち[n]番目に[a]があるとき、[Some a]を返却します。
    我々はこの新しい関数を結果の中にエラーがあるかもしれないことを示すために、[nth_error]と呼ぶことにします。

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(*  (In the HTML version, the boilerplate proofs of these
    examples are elided.  Click on a box if you want to see one.)

    This example is also an opportunity to introduce one more small
    feature of Coq's programming language: conditional
    expressions... *)
(** (HTML版では、証明のボイラープレートが省略されているかもしれません。四角をクリックすると見えるようになります。

   これを機会に、 Coq のプログラミング言語としての機能として、条件式を紹介しておきましょう。
   *)

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

(*  Coq's conditionals are exactly like those found in any other
    language, with one small generalization.  Since the boolean type
    is not built in, Coq actually allows conditional expressions over
    _any_ inductively defined type with exactly two constructors.  The
    guard is considered true if it evaluates to the first constructor
    in the [Inductive] definition and false if it evaluates to the
    second. *)
(** Coq の条件式(if式)は他の言語に見られるものとほとんど同じですが、少しだけ一般化されています。 Coq には 組み込みのブーリアン型がないため、 Coq の条件式では、実際には、構成子のふたつある任意の帰納型に対して分岐をすることができます。条件部の式が [Inductive] の定義の最初の構成子に評価された場合には真、ふたつめの構成子に評価された場合には偽と見做されます。
   *)

(*  The function below pulls the [nat] out of a [natoption], returning
    a supplied default in the [None] case. *)
(** 次の関数は、 [natoption] 型から [nat] の値を取り出し、 [None] の場合には与えられたデフォルト値を返します。
   *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(* **** Exercise: 2 stars (hd_error) *)
(* Using the same idea, fix the [hd] function from earlier so we don't
    have to pass a default element for the [nil] case.  *)
(** **** 練習問題: ★★ (hd_opt) *)
(** 同じ考え方を使って、以前定義した [hd] 関数を修正し、 [nil] の場合に返す値を渡さなくて済むようにしなさい。
   *)

Definition hd_error (l : natlist) : natoption :=
  (* FILL IN HERE *) admit.

Example test_hd_error1 : hd_error [] = None.
 (* FILL IN HERE *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 1 stars, optional (option_elim_hd) *)
(* This exercise relates your new [hd_opt] to the old [hd]. *)
(** **** 練習問題: ★, optional (option_elim_hd) *)
(** 新しい [hd_error] と古い [hd] の関係についての練習問題です。 *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End NatList.

(* ###################################################### *)
(*  * Partial Maps *)
(** * 部分マップ *)

(*  As a final illustration of how data structures can be defined in
    Coq, here is a simple _partial map_ data type, analogous to the
    map or dictionary data structures found in most programming
    languages. *)
    
    using numbers for both the keys and the
    values stored under these keys.  (That is, a dictionary represents
    a finite map from numbers to numbers.) *)

(**
データ構造がCoqにおいて、どのように定義されるかについての最後の実例として、ここで単純な _部分マップ_ データ型を宣言しましょう。
部分マップデータ型は、mapやdictionaryに似たデータ型で、たいていのプログラミング言語で用意されています。*)

(*  First, we define a new inductive datatype [id] to serve as the
    "keys" of our partial maps. *)
(** まず、新しい再帰的なデータ型[id]を定義して、われわれの部分型でkeyとして使うことにしましょう。*)

Inductive id : Type :=
  | Id : nat -> id.

(*  Internally, an [id] is just a number.  Introducing a separate type
    by wrapping each nat with the tag [Id] makes definitions more
    readable and gives us the flexibility to change representations
    later if we wish.

    We'll also need an equality test for [id]s: *)
(** 内部的に、[id]は単なる数値です。各数値をラップすることで数値と違う[Id]というタグのついた型を導入することで各定義はもっと読み易くなり、あとからの変更にも強い柔軟さを得ることが出来ます。

[id]のための同値性を見るテストがさしあたって必要になるでしょう。
*)
Definition beq_id x1 x2 :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(** **** Exercise: 1 star (beq_id_refl)  *)
Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now we define the type of partial maps: *)

Module PartialMap.
Import NatList.
  
Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.

(*  This declaration can be read: "There are two ways to construct a
    [partial_map]: either using the constructor [empty] to represent an
    empty partial map, or by applying the constructor [record] to
    a key, a value, and an existing [partial_map] to construct a
    [partial_map] with an additional key-to-value mapping." *)
(** この宣言は次のように読めます。「[partial_map] を構成する方法はふたつある。構成子 [empty] で空の辞書を表現するか、構成子 [record] をキーと値と既存の [partial_map] に適用してキーと値の対応を追加した [partial_map] を構成するかのいずれかである」。 *)

(*  The [update] function overrides the entry for a given key in a
    partial map (or adds a new entry if the given key is not already
    present). *)
(** [update]関数は、与えられたkeyに対応する部分マップのエントリを上書きします。(もしキーに対応するエントリがないなら、新しいエントリを加えます。*)
Definition update (d : partial_map)
                  (key : id) (value : nat)
                  : partial_map :=
  record key value d.

(*  Last, the [find] function searches a [partial_map] for a given
    key.  It returns [None] if the key was not found and [Some val] if
    the key was associated with [val]. If the same key is mapped to
    multiple values, [find] will return the first one it
    encounters. *)
(**  最後に、[find]関数は、[partial_map]を与えられたキーで検索します。キーが見つからなかった場合、[None]が返却されます。キーが[val]と結び付いている場合、[Some val]が返却されます。もし同じキーに複数の値がマップされている場合は、[find]は遭遇した最初のエントリを返却します。*)

Fixpoint find (key : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record k v d' => if beq_id key k
                     then Some v
                     else find key d'
  end.

(*  **** Exercise: 1 star (update_eq)  *)
(** **** 練習問題: ★ (udpate_eq) *)
Theorem update_eq :
  forall (d : partial_map) (k : id) (v: nat),
    find k (update d k v) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star (update_neq)  *)
(** **** 練習問題: ★ (udpate_neq) *)
Theorem update_neq :
  forall (d : partial_map) (m n : id) (o: nat),
    beq_id m n = false -> find m (update d n o) = find m d.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

End PartialMap.

(*  **** Exercise: 2 stars (baz_num_elts)  *)
(** **** 練習問題: ★★  (baz_num_elts) *)
(*  Consider the following inductive definition: *)
(** 次の帰納的定義について考えましょう。 *)
Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

(*  How _many_ elements does the type [baz] have?
(** [baz]型の要素はいくつあるでしょう？ *)

(* FILL IN HERE *)
*)
(** [] *)

(** $Date: 2016-05-24 14:00:08 -0400 (Tue, 24 May 2016) $ *)

(* **** Exercise: 2 stars, recommended (list_design) *)
(* Design exercise:
     - Write down a non-trivial theorem involving [cons]
       ([::]), [snoc], and [append] ([++]).
     - Prove it.
*)
(* ###################################################### *)
(** ** リストについての練習問題 (2) *)

(** **** 練習問題: ★★, recommended (list_design) *)
(** 自分で問題を考えましょう。
     - [cons] （[::]）、 [snoc]、 [append] （[++]） に関する、自明でない定理を考えて書きなさい。
     - それを証明しなさい。
*)

(* FILL IN HERE *)
(** [] *)
