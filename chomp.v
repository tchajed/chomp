Require Import Omega.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import RelationClasses.

Record pos :=
  mkPos { row : nat;
          col : nat }.

Notation "x & y" := (mkPos x y) (at level 50).

Inductive pos_le : pos -> pos -> Prop :=
| Pos_le : forall n m n' m',
    n <= n' ->
    m <= m' ->
    pos_le (n & m) (n' & m').

Hint Constructors pos_le.
Hint Extern 4 (_ <= _) => omega.

Ltac destruct_pos :=
  match reverse goal with
    | [ p: pos |- _ ] =>
      let n := fresh "n" in
      let m := fresh "m" in
      destruct p as [n m]
  end.

Ltac invert_pos_le :=
  match goal with
  | [ H: pos_le _ _ |- _ ] =>
    inversion H; subst; clear H
  end.

Instance pos_le_preoroder : PreOrder pos_le.
Proof.
  constructor; hnf; intros;
    repeat invert_pos_le;
    repeat destruct_pos;
    eauto.
Qed.

Definition pos_le_dec (p1 p2: pos) : {pos_le p1 p2} + {~pos_le p1 p2}.
Proof.
  repeat destruct_pos.
  destruct (le_dec n n0);
    destruct (le_dec m m0);
    try solve [ left; eauto ];
    try solve [ right; intro;
                invert_pos_le; eauto ].
Defined.

Definition Board := pos -> bool.

Definition invariant (b:Board) :=
  forall p, b p = false ->
    forall p', pos_le p p' ->
          b p' = false.

Inductive State :=
| mkState : forall (b:Board), invariant b -> State.

Theorem invariant_prop_ext : forall (b:Board)
    (H1 H2: invariant b),
    H1 = H2.
Proof.
  intros.
  extensionality p.
  extensionality Hbp.
  extensionality p'.
  extensionality Hle.
  apply (UIP_dec Bool.bool_dec).
Qed.

Implicit Type (sigma:State).
Implicit Type (b:Board).
Implicit Type (p:pos).

Definition getBoard sigma : Board :=
  let (b, _) := sigma in b.

Theorem State_eq : forall sigma sigma',
    getBoard sigma = getBoard sigma' ->
    sigma = sigma'.
Proof.
  destruct sigma, sigma'; intros; simpl in *; subst.
  pose proof (invariant_prop_ext _ i i0); subst.
  auto.
Qed.

Definition remove' (b:Board) p : Board :=
  fun p' => if pos_le_dec p p'
         then false
         else b p'.

Lemma remove_preserves_invariant : forall b p,
    invariant b ->
    invariant (remove' b p).
Proof.
  unfold invariant; intros.
  unfold remove' in *.
  destruct (pos_le_dec p p'); eauto.
  destruct (pos_le_dec p p0); eauto.
  contradiction n.
  etransitivity; eassumption.
Qed.

Definition remove (sigma:State) (p: pos) : State.
Proof.
  destruct sigma.
  apply (mkState (remove' b p)).
  auto using remove_preserves_invariant.
Defined.

Inductive move : State -> State -> Prop :=
| isMove : forall sigma sigma' p, getBoard sigma p = true ->
                     getBoard sigma' = getBoard (remove sigma p) ->
                     move sigma sigma'.

Inductive Elements b (l: list pos) : Prop :=
| ElementsAre : (forall p, b p = true ->
                      In p l) ->
                Elements b l.

Theorem sumbool_bool_eq : forall P Q (x: {P} + {Q}) (b: bool),
    (if x then true else false) = b ->
    if b then P else Q.
Proof.
  destruct x, b; congruence.
Qed.

(* rectangle with top-right corner p *)
Definition rectangle p : State.
  apply (mkState (fun p' => if pos_le_dec p' p
                         then true else false)).
  unfold invariant; intros.
  apply sumbool_bool_eq in H.
  destruct (pos_le_dec p' p); eauto.
  contradiction H.
  etransitivity; eauto.
Defined.

Inductive LoseFrom : State -> Prop :=
| AllWin : forall sigma sigma'',
    move sigma sigma'' ->
    (forall sigma', move sigma sigma' -> WinFrom sigma') ->
    LoseFrom sigma
with WinFrom : State -> Prop :=
     | NoMoves : forall sigma,
         (forall sigma', ~move sigma sigma') ->
         WinFrom sigma
     | CanForce : forall sigma sigma',
         move sigma sigma' ->
         LoseFrom sigma' ->
         WinFrom sigma.

Definition empty : State.
  apply (mkState (fun _ => false)).
  unfold invariant; intros.
  auto.
Defined.

Lemma empty_nomoves : forall sigma sigma',
    getBoard sigma = getBoard empty ->
    ~move sigma sigma'.
Proof.
  inversion 2; subst.
  rewrite H in H1.
  simpl in *; congruence.
Qed.

Theorem empty_win : forall sigma,
    getBoard sigma = getBoard empty ->
    WinFrom sigma.
Proof.
  intros.
  apply NoMoves; intros.
  apply empty_nomoves; auto.
Qed.

Theorem empty_not_lose : forall sigma,
    getBoard sigma = getBoard empty ->
    ~LoseFrom sigma.
Proof.
  inversion 2; subst.
  inversion H1; subst.
  rewrite H in H3; simpl in *; congruence.
Qed.

Ltac econstructor_with e :=
  unshelve econstructor; [ exact e | .. ].

Lemma pos_le_0 : forall p,
    pos_le p (0 & 0) ->
    p = (0 & 0).
Proof.
  intros.
  destruct_pos; invert_pos_le.
  f_equal; omega.
Qed.

Lemma remove_0_from_corner :
  getBoard (remove (rectangle (0 & 0)) (0 & 0)) =
  getBoard empty.
Proof.
  extensionality p; simpl.
  unfold remove'.
  destruct (pos_le_dec (0 & 0) p); auto.
  destruct (pos_le_dec p (0 & 0)); auto.
  apply pos_le_0 in p0; subst.
  contradict n.
  reflexivity.
Qed.

Theorem bottom_good : LoseFrom (rectangle (0 & 0)) /\
                      ~WinFrom (rectangle (0 & 0)).
Proof.
  split.
  - econstructor_with empty.
    econstructor_with (0 & 0); auto.
    rewrite remove_0_from_corner; auto.

    intros.
    inversion H; subst.
    inversion H0; subst.
    apply sumbool_bool_eq in H3.
    apply pos_le_0 in H3; subst.
    rewrite remove_0_from_corner in H1.
    apply empty_win; auto.
  - inversion 1; subst.
    apply (H0 empty).
    econstructor_with (0 & 0); auto.
    rewrite remove_0_from_corner; auto.

    Search move.
    inversion H0; subst.
    inversion H2.
    apply sumbool_bool_eq in H5.
    apply pos_le_0 in H5; subst.
    rewrite remove_0_from_corner in *.
    eapply empty_not_lose; eauto.
Qed.

(* Local Variables: *)
(* company-coq-local-symbols: (("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?')) ("sigma''" . (?σ (Br . Bl) ?' (Br . Bl) ?')) ("State" . ?Σ)) *)
(* End: *)