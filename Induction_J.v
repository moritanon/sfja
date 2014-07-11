(** * 帰納法: 帰納法による証明 *)


(** 次の行を実行すると、前章の定義を一度にインポートすることができます。 *)

Require Export Basics_J.

(** これを動かすために、[coqc]を使用して、[Basics_J.v]をコンパイルして、[Basics.vo]を生成する必要があります。(これは、.classファイルを .javaファイルから、あるいは、.oファイルを .cファイルから生成するのに似ています。

  コードをコンパイルする方法はふたつあります。

    CoqIDE:

    Basics_J.v を開き、 "Compile" メニューの "Compile Buffer" をクリックする。

    コマンドライン:

    coqc Basics_J.v を実行する。

このファイルでも Module 機能を使って数のリストやペアの定義を囲んでおきます。こうしておくことで、同じ操作を改良した（一般化した）ものに同じ名前をつけることができます。

 *)

(* ###################################################################### *)
(** * Caseへのネーミング *)

(** caseのサブゴールからサブゴールへ明示的に移動するためのコマンドがないことは、証明の過程と結果を表すスクリプトを読みにくくしていることも事実です。さらに大掛かりな証明では、caseの分析も階層化し、Coqを使って証明を進めていくことが苦痛に感じられるかもしれません（あるCaseが五つのサブゴールを持ち、残りの七つのCaseも他のCaseの内部にあるような状況を想像してみてください･･･）。インデントやコメントを上手に使うと多少は改善しますが、最もよい解決方法は"Case"タクティックを定義して使用することです。*)

(* CaseタクティックはCoqにビルトインされていませんので、自分で定義する必要があります。それがどのような仕組みで動いているかを理解する必要はありませんので、ここでは定義は跳ばして使用例から見ていくことにします。このサンプルは、Coqの機能のうちまだ解説していないstringライブラリとLtacコマンドを使用します。これらはカスタムタクティックを定義するときに使うもので、Aaron Bohannon のナイスな業績によるものです。*)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
(** Here's an example of how [Case] is used.  Step through the
   following proof and observe how the context changes. *)

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".  (* <----- here *)
    reflexivity.
  Case "b = false".  (* <---- and here *)
    rewrite <- H.
    reflexivity.
Qed.

(** Caseが行っていることは実はとても簡単です。Caseは、続けて指定されたタグ名を、今証明しようとしているゴールへのコンテキストに文字列として追加しているだけなのです。証明がサブゴールに到達し、証明されると、次のトップレベル（今しがた解決したゴールと兄弟関係にある）ゴールがアクティブになります。するとさっきCaseで指定した文字列がすでに証明を終えたcaseとしてコンテキストに現れます。これは健全性のチェックにもなります。もし今の証明が完了しておらず、コンテキストに残ったまま次のCaseタックティクを実行すると、エラーメッセージが表示されます。 

 ネストしたcaseの分析（今destructで解決しようとしているゴール自体が、他のdestructの産物であるような場合）のために、SCase("subcase")が用意されています。*)


(** **** 練習問題: ★★ (andb_true_elim2) *)
(** destructを使い、case（もしくはsubcase）を作成して、以下の証明andb_true_elim2を完成させなさい。*)

Theorem andb_true_elim2 : ∀ b c : bool,
  andb b c = true → c = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Coq上に証明の経過を記述する際、それをどのようにフォーマットするべきか、ということについてちゃんとしたルールというものはありません。行が分割され、証明の各段階が階層を持ち、それをインデントで表現するような場合は特にそうです。しかしながら、複数のサブゴールが作成された部分が明示的にCaseタクティックでマークされた場合は、それを行頭から記述することにします。そうしておけば、証明は読みやすくなり、それ以外でどんな方針のレイアウトが選ばれても、あまり問題になりません。


ここで、１行の長さをどれくらいにしておくべきか、ということにも触れておきましょう。始めたばかりのCoqユーザーは、証明全体を１行に収めようと、複数のタクティックを同じ行に書き、非常に長い行を書いてしまいがちです。よいスタイルというものは「ほどほど」のところにあります。特にあげるなら、一連の流れを１行に書くにしても1行80字程度にとどめておくべきでしょう。これ以上長くなると読むのも大変になりますし、印刷や画面表示もうまくいかない場合が多くなります。多くのエディタがこのような制限をかける機能を持っていますのでそれを使ってもいいでしょう。 *)

(* ###################################################################### *)
(** * 帰納法による証明 *)

(**  我々は先程の章で、0が加法+の左単位元（左から加えても値が値が変わらない値）であることを引数を分解し評価することで証明しました。右から加える場合でも同じように証明できるのでしょうか？ *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ･･･同じぐらい簡単、というわけにはいかないようです。reflexivityを使ってみても同じです。n + 0のn は任意の未知数であり、+の定義にあるmatchのせいで簡約できません。*) 

Proof.
  intros n.
  simpl. (* 何も起こらない! *)
Abort.

(**そして、destruct nを使い、caseごとに推論するのも難しそうです。caseごとに考えるとn = 0のときはうまくいきますが、n = S n'のほうではn'で同じように詰まってしまいます。destruct n'でさらに一歩踏み込んでみたところで、nは任意の大きい数のまま動きません。どうやらまだ来たことがないところに迷い込んでしまったようです。 *)

Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity. (* ここまでは順調... *)
  Case "n = S n'".
    simpl.       (* ...でもここでまた詰まります。 *)
Abort.

(** このような命題を証明する場合 － 実際、数値やリストや、その他の帰納的な定義を持つ型にまつわる証明の多くはそうなのですが － もっとずっと強力な推論規則が必要になります。それが「帰納法」です。 

  高校で習った帰納法の仕組みを思い出して、自然数を考えてみましょう。もしP(n)が自然数nに対する命題であるとすると、Pがどんなnに対しても成り立つことは、以下のような方法で証明できます。 

    - P(O)が成り立つことを示す;
    - どんなn'に対しても、もしP(n')が成り立つならP(S n')も成り立つことを示す;
    - これによって、P(n)がどんなnでも成り立つと結論される

Coqでは、それぞれのステップは同じですが順序は逆向きに考えます。まず、ゴールの証明である「任意のnについてP(n)が成り立つ」からはじめ、それを二つの独立したサブゴールに分割します（ここでinductionタクティックを使います）。その結果、一つ目のサブゴールはP(O)、二つ目はP(n') → P(S n')となるはずです。以下は、実際にinductionタクティックが先ほど証明しようとしていた定理にどう作用するかを示したものです。 *)

Theorem plus_0_r :forall n:nat, n + 0 = n.
Proof.
  intros n. indaction n as [| n'].
  Case "n = 0".    reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity. Qed.

(** destructのように、inductionタクティックもas...句を取り、サブゴールに導入する際の変数の名前を指定することができます。最初のブランチではnは0に置き換えられ、ゴールは0 + 0 = 0となり、簡約できる状態になります。二つ目のブランチでは、nはS n'に置き換えられ、n' + 0 = n'が前提としてコンテキストに付け加えられます。（この際、仮定にIHn'という名前がつけられます。これは「Induction Hypothesys for n'（n'についての帰納法の仮定）」というような意味です。二番目のゴールは(S n') + 0 = S n'となり、S (n' + 0) = S n'に簡約されます。ここから、帰納法の仮定n' + 0 = n'を使って証明の残りを完成させます。 *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* 講義中に動かすこと *)
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** 練習問題: ★★, recommended (basic_induction) *)

(** 次の補題を帰納法を用いて証明しなさい。これまでに証明した結果が必要になるかもしれません。*)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* FILL IN HERE *) Admitted.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** [double]についてのシンプルなこの事実を証明するために、帰納法を使いなさい。*)

(** **** 練習問題: ★★ (double_plus) *)
Lemma double_plus : forall n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★ (destruct_induction) *)
(** [destruct]と[induction]の違いを短く説明しなさい。

(* FILL IN HERE *)

*)
(** [] *)

(* ###################################################################### *)
(** * 証明の中で行う証明 *)

(** Coqでは（非形式的な数学と同様に）大きな証明は高い頻度で、後に出てきた証明が前に出ている証明を参照するような定理の列に分割されます。しかし時折、証明がいくつかの自明で雑他な事実を必要とし、それがまたトップレベルの名前をつけるほどでもなかったりします。こういう場合、状態を単純化し、すでに使われている定理の右に出現するサブ定理を証明することができれば便利です。[assert]タクティックはこれを可能にしてくれます。例えば、最初の方でやった証明[mult_0_plus]は、[plus_O_n]と名付けられた定理の証明から参照されています。[assert]を使うと[plus_O_n]の証明をこんな風に行うことができます。 *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity. Qed.

(** [assert]タクティックは、二つのサブゴールを取り込みます。最初のものは[H:]という接頭辞をつけているように、それ自身を主張するもので、Assertion [H]と呼びます。
（まず注意が必要なのは、上で使用した[destruct]や[induction]に[as]句をつけることで、[assert (0 + n = n) as H]というようにassertionに名前をつけられることです。
もう一つ、証明に出てくるassertionに、[Case]を使ってマーキングしている事も注目です。その理由は、読みやすさのため、というだけでなく、例えばCoqをインタラクティブに使っているとき、証明を進めている間にコンテキストから["Proof of assertion"]という文字列が消える瞬間を観察することで、証明の完了を知ることができます。）二つ目のゴールは、[assert]を呼び出した場合と、コンテキストに[0 + n = n] : [H]という仮定が得られることを除けば同じです。このことから、[assert]は、我々が証明しなければならない事実そのものとなるサブゴールと、その最初のサブゴールの証明がどのような値でも成り立つことを使って証明される事実となる二つ目のサブゴールを作成することが分かります。 *)

(** 実際[assert]は多くのシチュエーションで便利に使えるでしょう。例えば、[(n + m)
+ (p + q) = (m + n) + (p + q)]であることを証明するとしましょう。[=]の両側で異なるのは最初のカッコの中の[+]の両側の[n]と[m]が入れ替わっているだけで、このことは加法の交換法則([plus_comm]）があるものを別のものに書き換えることに使用できることを示しています。しかしながら、[rewrite]タクティックは「どこに適用するか」を考える必要がある場合には少々おばかさんです。ここでは[+]が3箇所で使われていますが[rewrite -> plus_comm]は一番外側（つまり中央）の[+]にしか適用されません。 *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* ここで[(n + m)]を[(m + n)]に入れ替えたいのですが、[plus_comm]でこれができるかと試してみると... *)
  rewrite -> plus_comm.
  (* うまくいきません。Coqは別のところを[rewrite]してしまいます *)
Abort.

(** [plus_comm]を、適用したいポイントに対して使用するには、まず[n + m = m + n]で始まるような補助定理（ここでは何とかしようとしている[m]と[n]を特定するため）を導き、それを望むrewriteに使用します。 *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity. Qed.

(* **** 練習問題: ★★★★ (mult_comm) *)
(** [assert]を使用して以下の証明を完成させなさい。ただしinduction（帰納法）を使用しないこと。 *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.

(** では、乗法が可換であることを証明しましょう。おそらく、補助的な定理を定義し、それを使って全体を証明することになると思います。先ほど証明した[plus_swap]が便利に使えるでしょう。 *)

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, optional (evenb_n__oddb_Sn) *)

(** 次のシンプルな事実を証明しなさい *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** * さらなる練習問題 *)

(** **** 練習問題: ★★★, optional (more_exercises) *)
(** 紙を何枚か用意して、下に続く定理が(a)簡約と書き換えだけで証明可能か、(b)[destruct]を使ったcase分割が必要になるか、(c)帰納法が必要となるか、のいずれに属すかを、紙の上だけで考えなさい。予測を紙に書いたら、実際に証明を完成させなさい。証明にはCoqを用いてかまいません。最初に紙を使ったのは「初心忘れるべからず」といった理由です。 *)

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, optional (beq_nat_refl) *)
(** 次の定理を証明しなさい。左辺を[true]と置いてあることが奇妙に感じられるかもしれません。しかし、標準ライブラリの中で定理はこのように提示されているからで、我々もそれに従います。書き換えはどちらか一方の方向に上手く動作するので、定理の記述されている方向に関係なく、定理を使う上で問題になることはありません。*)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, optional (plus_swap') *)
(** [replace]タクティックは、特定のサブタームを置き換えたいものと置き換えることができます。もう少し正確に言うと、[replace (t) with (u)]は、ゴールにある[t]という式を全て[u]にかきかえ、[t = u]というサブゴールを追加します。この機能は、通常の[rewrite]がゴールの思い通りの場所に作用してくれない場合に有効です。

[replace]タクティックを使用して[plus_swap']の証明をしなさい。ただし[plus_swap]のように[assert (n + m = m + n)]を使用しないで証明を完成させなさい。
*)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** 練習問題: ★★★ (binary_commute) *)
(** Recall the [increment] and [binary-to-unary] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that these functions commute -- that is, incrementing a binary
    number and then converting it to unary yields the same result as
    first converting it to unary and then incrementing.

    [Basics_J]の章の[binary]の練習問題で書いた[increment]と[binary-to-unary]関数を思い出してください。それらの関数が可換であること、すなわち、bin値をインクリメントしたあとに自然数に変換すること、bin値を自然数に変換したあとにインクリメントしたものとが同じ結果になることを証明しなさい。

    (Before you start working on this exercise, please copy the
    definitions from your solution to the [binary] exercise here so
    that this file can be graded on its own.  If you find yourself
    wanting to change your original definitions to make the property
    easier to prove, feel free to do so.) 

    この練習問題にとりかかる前に、このファイルはそれ自体が成績を付ける対象になるため、[binary]の練習問題のあなたの解法からここへコピーしてください。もしあなたの元々の定義を証明を簡単にするために変えたくなったら、自由に変えてください。
*)


(* FILL IN HERE *)
(** [] *)



(** **** 練習問題: ★★★★★ (binary_inverse) *)
(** この練習問題は前の問題の続きで、2進数に関するものである。前の問題で作成された定義や定理をここで用いてもよい。


(a) まず自然数を2進数に変換する関数を書きなさい。そして「任意の自然数からスタートし、それを2進数にコンバートし、それをさらに自然数にコンバートすると、スタート時の自然数に戻ることを証明しなさい。


(b) あなたはきっと、逆方向についての証明をしたほうがいいのでは、と考えているでしょう。それは、任意の2進数から始まり、それを自然数にコンバートしてから、また2進数にコンバートし直したものが、元の自然数と一致する、という証明です。しかしながら、この結果はtrueにはなりません。！！その原因を説明しなさい。


(c) 2進数を引数として取り、それを一度自然数に変換した後、また2進数に変換したものを返すnormalize関数を作成し、証明しなさい。

 もう一度言いますが、以前のあなたの定義を変更するのは自由です。もしそれがここで役に立つならば。

 *)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(** * 発展的題材 *)

(** * 形式的証明と非形式的証明 *)

(** "非形式的な証明はアルゴリズムであり、形式的な証明はコードである" *)

(** 数学的に厳格な証明を構成するとはどういうことなのか、という問題は、千年もの間哲学者を悩ませてきました。しかし少々雑な定義でよければ次のように書くこともができます。数学的な命題[P]の証明とは、それを読む（あるいは聞く）人をして、[P]がtrueであることを納得せしめる文章を書く（語る）ことである、と。このことから、証明はコミュニケーション行為であると言えるでしょう。

さて、このコミュニケーションの相手は、二種類に分けることができます。一方は、Coqのプログラムのように振る舞うような場合で、このケースでの「信用に値する」というのは、[P]が形式的論理のルールに基づく確実な論理から導かれたもので、その証明が、このチェックを行うプログラムをガイドする秘訣になっているようなものです。そんな秘訣が「形式的証明」です。

一方、読者が人間的な存在で、証明が英語などの自然言語で書かれているようなケースは「非形式的証明」であると言えます。こんなケースでの成功の条件は「あまりきちんと明示しないこと」です。とにかく、読んでいる人に納得させてしまえる証明こそが「よい証明」なのです。しかしひとつの証明を複数の読者が見るような場合、ある論点について、ある人は特定の言い回しによって核心に至るかもしれませんが、人によってはそうではないかもしれません。もっと極端な人は、ただ知ったかぶりをする割りに経験は浅い、単なる「頭でっかち」であるかもしれません。そういった人たちを押しなべて納得させる唯一の方法は、ただ骨身を惜しまず細かいところまで論じることなのです。逆にある読者はこういったことに精通しているあまり、細かいことにこだわりすぎて全体的な流れを見失う、ということもあります。多くの人が望んでいることは総論としてどうなのか、ということを知ることで、細かいことを考えていくことは面倒なものです。結局のところ、非形式的な証明でみんなを納得させる標準的な方法はなさそうです。なぜなら、非形式的な書き方で想定される読者全員を納得させる方法はないからです。しかし実際のところ、数学者は複雑な数学的事柄についてたくさんの表記規則のおかげで、証明が正しいか否かを判断するための標準的かつ公正な方法がもたらされたのです。

我々はこのコースでCoqを使用しているのですから、それだけできちんと形式化された証明に乗っていると言えます。しかしこのことは、非形式的な表現を無視していい、ということではありません。形式的証明は多くの場合有効ですが、人と人との間で考えを伝えあう際には必ずしも効率的とは言えないものです。 *)

(** 例えば、下の例は加法が結合的であることを示すものです。 *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coqはこのような証明を完璧にこなしてくれますが、上の証明は人間にとってはいささかのみこみにくいと言わざるを得ません。もしあなたがCoqに十分慣れていて、タクティックを次々と適用しながら証明を進めていき、コンテキストやゴールがどう変化していくかを頭の中だけでイメージしていくことができるようなレベルの人でも、上の証明はかなり複雑で、ほとんど理解不能に思えるかもしれません。それを横目に、数学者はサラサラとこんな風に書くでしょう。 *)

(** - 定理：任意の[n],[m],[p]について、以下が成り立つ
[[
n + (m + p) = (n + m) + p.
]]
証明：[n]について帰納法を適用する。

- まず[n = 0]と置くと、以下のようになる
[[
0 + (m + p) = (0 + m) + p.
]]
これは、[+]の定義から直接導くことができる。

- 次に[n = S n']と置き、帰納法の仮定を
[[
n' + (m + p) = (n' + m) + p.
]]
とすると、以下のような式が立つ。
[[
(S n') + (m + p) = ((S n') + m) + p.
]]
ここで、[+]の定義より、以下のように変形できる。
[[
S (n' + (m + p)) = S ((n' + m) + p),
]]
これは、直後の値について帰納法の仮定が成り立つことを示している。 [] *)

(** どちらの表現も、やっていることは基本的に同じことです。これはもちろん偶然ではなく、Coqの[induction]タクティックが、数学者が考えるのと同じ目標を、同じサブゴールとして、同じ順番で作成するように作られているだけです。しかしこの二つをよく見ると、重要な違いがあります。形式的証明は、ある部分（[reflexivity]を使っている部分など）ではより明示的ですが、それ以外のところはあまり明示的ではありません。特にあるポイントにおける証明の状態が、Coqの証明では明示されていません。一方、非形式的証明は、途中で何度も「今どのあたりで、どのようになっているか」を思い出させてくれるような書き方になっています。 *)

(** 形式的証明も、以下のように書けば構造が分かりすくなります。 *)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

(** **** Exercise: 2 stars, advanced (plus_comm_informal) *)
(** Translate your solution for [plus_comm] into an informal proof. *)

(** Theorem: Addition is commutative.

    Proof: (* FILL IN HERE *)
[]
*)

(** **** 練習問題: ★★, optional (beq_nat_refl_informal) *)
(** 次の証明を、[plus_assoc] の非形式的な証明を参考に書き換えなさい。Coqのタクティックを単に言い換えただけにならないように！

定理：true=beq_nat n n forany n.（任意のnについて、nはnと等しいという命題がtrueとなる）

Proof: (* FILL IN HERE *)
[]
*)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)
