(*  * ImpCEvalFun: Evaluation Function for Imp *)
(** * ImpCEvalFun: Impのための評価関数 *)

(*  We saw in the [Imp] chapter how a naive approach to defining a
    function representing evaluation for Imp runs into difficulties.
    There, we adopted the solution of changing from a functional to a
    relational definition of evaluation.  In this optional chapter, we
    consider strategies for getting the functional approach to
    work. *)
(** TODO [Imp]の章で、Impのための評価関数を素朴な方法で定義することが難しいことを見て来ました。
*)

(* #################################### *)
(*  * A Broken Evaluator *)
(** * 動かない評価関数 *)

Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith.
Require Import SfLib.
Require Import Imp.
Require Import Maps.

(*  Here was our first try at an evaluation function for commands,
    omitting [WHILE]. *)
(** 以下は [WHILE] 以外のコマンドの評価関数を得ようとした、最初の試みです。 *)

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | l ::= a1 =>
        t_update st l (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | WHILE b1 DO c1 END =>
        st  (* bogus *)
  end.

(** As we remarked in chapter [Imp], in a traditional functional
    programming language like ML or Haskell we could write the WHILE
    case as follows: *)
(** [Imp]の章で書いたように、MLやHaskellのような伝統的な関数型プログラミング言語において、WHILEの場合を次のように書くことが出来ます。

    | WHILE b1 DO c1 END => if (beval st b1) then ceval_step1 st (c1;;
        WHILE b1 DO c1 END) else st
*)
(*  Coq doesn't accept such a definition ([Error: Cannot guess
    decreasing argument of fix]) because the function we want to
    define is not guaranteed to terminate. Indeed, the changed
    [ceval_step1] function applied to the [loop] program from [Imp.v]
    would never terminate. Since Coq is not just a functional
    programming language, but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is an
    invalid(!) Coq program showing what would go wrong if Coq allowed
    non-terminating recursive functions:*)
(** Coqは、そのような定義を受け入れてくれません。([Error: Cannot gues descreasing argument of fix])我々が定義したい関数は、終了を保証できないからです。確かに、[Imp.v]の[loop]プログラムも受け入れるように変更された[ceval_step1]関数は決して終了しません。Coqは単なる関数型プログラミング言語ではなく、一貫性を持った論理であり、潜在的に終了しないどんな関数も却下される必要があります。ここに、もしCoqが終了しない再帰関数を受け入れたならば、どんな不都合なことがあるかを示す、不正な(!)Coqプログラムがあります。

     Fixpoint loop_false (n : nat) : False := loop_false n.
*)
(*  That is, propositions like [False] would become
    provable (e.g., [loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs, the full version
    of [ceval_step1] cannot be written in Coq -- at least not
    without one additional trick... *)
(** すなわち、[False]のような命題が証明可能となります。(例, [loop_false 0]は[False]の証明となります。)それは、Coqの論理的一貫性にとって厄介なものとなります。
    そのため、全ての入力について終了しないため、[cavel_step1]の完全なバージョンを書くことが出来ないのです -- 少くともある追加のトリックを使うことなしには。
*)

(* #################################### *)
(** * A Step-Indexed Evaluator *)

(*  The trick we need is to pass an _additional_ parameter to the
    evaluation function that tells it how long to run.  Informally, we
    start the evaluator with a certain amount of "gas" in its tank,
    and we allow it to run until either it terminates in the usual way
    _or_ it runs out of gas, at which point we simply stop evaluating
    and say that the final result is the empty memory.  (We could also
    say that the result is the current state at the point where the
    evaluator runs out fo gas -- it doesn't really matter because the
    result is going to be wrong in either case!) *)
(** TODO! *)
(** 次の試みでは、評価が常に停止することを保証するため、
    数の引数を追加して「ステップ指数」として用いています。*)

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_state
  | S i' =>
    match c with
      | SKIP =>
          st
      | l ::= a1 =>
          t_update st l (aeval st a1)
      | c1 ;; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

(*  _Note_: It is tempting to think that the index [i] here is
    counting the "number of steps of evaluation."  But if you look
    closely you'll see that this is not the case: for example, in the
    rule for sequencing, the same [i] is passed to both recursive
    calls.  Understanding the exact way that [i] is treated will be
    important in the proof of [ceval__ceval_step], which is given as
    an exercise below. *)
(** 注: ここでの指数 [i] は「評価のステップ数」を数えるものだろうか？
    という点が気になります。しかしよく見ると、そうではないと分かります。
    例えば、直列実行に対する規則では、2 つの再帰呼び出しに同じ [i] が渡されています。
    [i] がどのように扱われているのかを正確に理解することは、
    以下で演習問題として与えられている [ceval__ceval_step] の証明で重要となるでしょう。 *)

(*  Third try, returning an [option state] instead of just a [state]
    so that we can distinguish between normal and abnormal
    termination. *)
(** 3 つ目の試みでは、単なる [state] の代わりに [option state] を返すようにしています。
    こうすると、通常終了と異常終了を区別出来ます。*)

Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (t_update st l (aeval st a1))
      | c1 ;; c2 =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

(*  We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)
(** オプション状態に対する場合分けに繰り返し含まれている「配管」を隠すための、
    補助的なちょっとした記法を導入すると、この定義の読みやすさは改善出来ます。*)

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (t_update st l (aeval st a1))
      | c1 ;; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

(* Compute
     (test_ceval empty_state
         (X ::= ANum 2;;
          IFB BLe (AId X) (ANum 1)
            THEN Y ::= ANum 3
            ELSE Z ::= ANum 4
          FI)).
   ====>
      Some (2, 0, 4)   *)

(** **** 練習問題: ★★, (pup_to_n) *)
(*  Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].  Make sure
   your solution satisfies the test that follows. *)
(** [1] から [X] までの整数を変数 [Y] に足す (つまり [1 + 2 + ... + X]) 
    Imp プログラムを書きなさい。下に示したテストを満たすことを確認しなさい。 *)

Definition pup_to_n : com :=
  (* FILL IN HERE *) admit.

(* 
Example pup_to_n_1 :
  test_ceval (t_update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.
*)
(** [] *)

(*  **** Exercise: 2 stars, optional (peven)  *)
(** **** 練習問題: ★★, optional (peven) *)
(*  Write a [While] program that sets [Z] to [0] if [X] is even and
    sets [Z] to [1] otherwise.  Use [ceval_test] to test your
    program. *)
(** [X] が偶数だったら [Z] に [0] を、そうでなければ [Z] に [1] をセットする 
    [While] プログラムを書きなさい。テストには [ceval_test] を使いなさい。 *)

(* FILL IN HERE *)
(** [] *)

(* ################################################################ *)
(** * Equivalence of Relational and Step-Indexed Evaluation *)

(** As with arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation actually boil down
    to the same thing.  This section shows that this is the case.
    Make sure you understand the statements of the theorems and can
    follow the structure of the proofs. *)
(*  算術式とブール式で行ったように、2 つの評価の定義が本当に、
    結局のところ同じものになるのかを確認したくなるでしょう。
    この章では、それを確認します。定理の主張を理解して、
    証明の構造を追えることを確認しておいて下さい。*)


Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st \\ st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  - (* i = 0 -- contradictory *)
    intros c st st' H. inversion H.

  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* SKIP *) apply E_Skip.
      + (* ::= *) apply E_Ass. reflexivity.

      + (* ;; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Evaluation of r1 terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        * (* Otherwise -- contradiction *)
          inversion H1.

      + (* IFB *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      + (* WHILE *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileLoop with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. simpl in H1. assumption. }
         { (* r1 = None *) inversion H1. }
        * (* r = false *)
          inversion H1.
          apply E_WhileEnd.
          rewrite <- Heqr. subst. reflexivity.  Qed.

(** **** 練習問題: ★★★★, (ceval_step__ceval_inf) *)
(*  Write an informal proof of [ceval_step__ceval], following the
    usual template.  (The template for case analysis on an inductively
    defined value should look the same as for induction, except that
    there is no induction hypothesis.)  Make your proof communicate
    the main ideas to a human reader; do not simply transcribe the
    steps of the formal proof.

(* FILL IN HERE *)
[]
*)
(** いつものテンプレートにのっとって、
    [ceval_step__ceval] の形式的でない証明を書きましょう。
    (帰納的に定義された値の場合分けに対するテンプレートは、
    帰納法の仮定がないこと以外は帰納法と同じ見た目になるはずです。) 
    単に形式的な証明のステップを書き写すだけでなく、
    人間の読者に主要な考えが伝わるようにしなさい。

(* FILL IN HERE *)
[]
*)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. inversion Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by omega.
    destruct c.
    + (* SKIP *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ::= *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ;; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        inversion Hceval.

    + (* IFB *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval; assumption.
    
    + (* WHILE *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption. 
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption. 
        rewrite -> Heqst1'o. simpl. simpl in Hceval. 
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. inversion Hceval.  Qed.

(** **** 練習問題: ★★★, recommended (ceval__ceval_step)  *)
(*  Finish the following proof.  You'll need [ceval_step_more] in a
    few places, as well as some basic facts about [<=] and [plus]. *)
(** 以下の証明を完成させなさい。何度か [ceval_step_more] が必要となり、
    さらに [<=] と [plus] に関するいくつかの基本的な事実が必要となるでしょう。*)

Theorem ceval__ceval_step: forall c st st',
      c / st \\ st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem ceval_and_ceval_step_coincide: forall c st st',
      c / st \\ st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* ####################################################### *)
(*  * 	 (Simpler Proof) *)
(** *    (より単純な証明) *)

(*  Here's a slicker proof showing that the evaluation relation is
    deterministic, using the fact that the relational and step-indexed
    definition of evaluation are the same. *)
(** 以下に、より巧みな証明を示します。
    これは関係による定義と指数を利用した定義の評価が同じである事実を利用しています。*)

Theorem ceval_deterministic' : forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  omega. omega.  Qed.

(** $Date: 2016-05-26 16:17:19 -0400 (Thu, 26 May 2016) $ *)
