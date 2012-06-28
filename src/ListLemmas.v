Require Import Aux List.
Require Import Arith.
Require Import Sorting.Permutation.

Lemma NoDupSingle : forall (a : Type) (x : a),
  NoDup (x :: nil).
Proof. constructor; auto; constructor. Qed.

Lemma NoDupCons : forall (a : Type) (xs : list a) (x : a),
  NoDup (x :: xs) -> NoDup xs.
Proof.
  intros a xs x H; induction xs.
  constructor. inversion H; assumption.
Qed.    

Lemma InApp : forall (a : Type) (x : a) (xs ys : list a),
  In x (xs ++ x :: ys).
Proof.
  intros a x xs.
  induction xs.
  simpl; constructor; reflexivity.
  intros ys. right. apply IHxs.
Qed.

Lemma InApp' : forall (a : Type) (x y : a) (xs ys : list a),
  In x (xs ++ ys) -> In x (xs ++ y :: ys).
Proof.
  intros a x y xs ys H.
  generalize dependent ys.
  induction xs.
  right; assumption.
  intros ys H. destruct H as [H | H].
  rewrite H; constructor; reflexivity.
  right; apply IHxs; assumption.
Qed.

Lemma InSuper : forall (a : Type) (x : a) (xs ys : list a),
  In x xs -> In x (xs ++ ys).
Proof.
  intros a x xs ys H.
  generalize dependent ys.
  induction xs as [ | z zs].
  inversion H.
  inversion H.
  constructor; exact H0.
  destruct H as [Eq | Later].
  constructor; exact Eq.
  right. apply (IHzs); auto.
Qed.

Lemma InComm : forall (a : Type) (x : a) (xs ys : list a),
  In x (xs ++ ys) -> In x (ys ++ xs).
Proof.
  intros a x xs ys.
  generalize dependent ys.
  induction xs as [ | z zs].
  intros ys H. simpl;rewrite app_nil_r; intros; assumption.
  intros ys H. destruct H as [H | H].
  rewrite H.
  apply InApp.
  apply InApp'.
  apply IHzs.
  assumption.
Qed.

Lemma NotInComm : forall (a : Type) (x : a) (xs ys : list a),
  ~In x (xs ++ ys) -> ~In x (ys ++ xs).
Proof.
  intros a x xs ys F H.
  induction ys as [ | y ys].
  induction xs as [ | z zs]; auto.
  rewrite app_nil_r in F; simpl in *; contradiction.
  destruct H as [H | H].
  rewrite H in *; apply F, InApp; assumption.
  apply F, InApp', InComm; auto.
Qed.

Lemma NoDupAppAss : forall (a : Type) (xs ys : list a),
  NoDup (xs ++ ys) -> NoDup (ys ++ xs).
Proof.
  intros a xs ys H.
  generalize dependent xs.
  induction ys.
  intros xs H.
  rewrite app_nil_r in H; assumption.
  constructor; 
    [ apply NotInComm, NoDup_remove_2; assumption 
    | apply IHys; apply NoDup_remove_1 in H; assumption].
Qed.

Lemma NoDupPerm : forall (a : Type) (xs ys : list a),
  NoDup xs -> Permutation xs ys -> NoDup ys.
Proof.
  intros a xs ys H1 H2.
  induction H2.
  (* nil *)
  constructor.
  (* skip *)
  constructor. 
  intro F; apply (NoDup_remove_2 nil l x); auto.
  apply (Permutation_in (l:=l'));
    [ apply (Permutation_sym) | ]; auto.
  apply IHPermutation.
  inversion H1; auto.
  (* swap *)
  constructor.
  apply (NoDup_remove_2 (y :: nil) l x); auto.
  apply (NoDup_remove_1 (y :: nil) l x); auto.
  (* trans *)
  apply IHPermutation2,IHPermutation1; auto.
Qed.

Lemma PermApp : forall (a : Type) (xs ys zs : list a),
  Permutation ys zs -> Permutation (xs ++ ys) (xs ++ zs).
Proof.
  intros a xs ys zs H1.
  generalize dependent ys.
  generalize dependent zs.
  induction xs; [auto | simpl; auto].
Qed.

Lemma NoDupConsSwap : forall (a : Type) (xs : list a) (x y : a),
  NoDup (x :: y :: xs) -> NoDup (y :: x :: xs).
Proof.
  intros a xs x y H.
  apply (NoDupPerm _ (x :: y :: xs) (y :: x :: xs)).
  apply H. constructor.
Qed.

Lemma NoDupAppConsR : forall (a : Type) (xs ys : list a) (x : a),
  NoDup (xs ++ x :: ys) -> NoDup (xs ++ ys).
Proof.
  intros a xs ys x H1.
  apply NoDupAppAss.
  apply (NoDupCons _ (ys ++ xs) x).
  rewrite -> app_comm_cons.
  apply NoDupAppAss.
  apply H1.
Qed.

Lemma NoDupAppConsR' : forall (a : Type) (xs ys : list a) (x y : a),
  NoDup (x :: xs ++ y :: ys) -> NoDup (x :: xs ++ ys).
Proof.
  intros a xs ys x y H.
  rewrite -> app_comm_cons.
  apply (NoDupAppConsR _ (x :: xs) ys y).
  apply H.
Qed.

Lemma NoDupAppR : forall (a : Type) (xs ys : list a),
  NoDup (xs ++ ys) -> NoDup ys.
Proof.
  intros a xs ys H1.
  generalize dependent ys.
  induction xs as [| x xs IHxs].
  intros ys H1.
  destruct ys as [| y ys].
  apply H1.
  apply H1.
  intros ys H1.
  simpl in H1.
  apply IHxs.
  apply NoDupCons in H1; apply H1.
Qed.

Lemma NoDupAppL : forall (a : Type) (xs ys : list a),
  NoDup (xs ++ ys) -> NoDup xs.
Proof.
  intros a xs ys H.
  generalize dependent xs.
  induction ys as [| y ys IHys].
  destruct xs as [| x xs].
  intros H; apply H.
  intros H;  rewrite -> app_nil_r in H; apply H.
  intros xs H.
  apply IHys.
  apply (NoDupAppConsR _ xs ys y).
  apply H.
Qed.

Lemma FlatMapApp : forall (a b : Type) (f : a -> list b) (xs ys : list a),
  flat_map f (xs ++ ys) = flat_map f xs ++ flat_map f ys.
Proof.
  intros a b f xs.
  induction xs as [| x xs IHxs]. reflexivity.
  intros ys. simpl. rewrite -> IHxs.
  rewrite -> app_ass. reflexivity.
Qed.

Lemma NoDupApp : forall (a : Type) (xs ys : list a),
  NoDup xs -> NoDup ys -> NoDup (xs ++ ys).
Proof.
  intros a xs.
  induction xs.
  intros ys H1 H2. apply H2.
  intros ys H1 H2.
Admitted.

Lemma NoDupAppApp : forall (a : Type) (xs ys zs : list a),
  NoDup (xs ++ ys ++ zs) -> NoDup (ys ++ zs).
Proof.
  intros a xs ys zs H.
  generalize dependent ys.
  generalize dependent zs.
  induction xs as [| x xs IHxs]. simpl; intros; assumption.
  intros zs ys H. apply IHxs.
  apply (NoDupCons _ (xs ++ ys ++ zs) x). assumption.
Qed.

Lemma NoDupFlatMapCons : forall (a b : Type) (x : a) (xs : list a) (f : a -> list b),
  NoDup (flat_map f (x :: xs)) -> NoDup (flat_map f xs).
Proof.
  intros a b x xs f H.
  destruct xs as [| y ys ]. constructor.
  simpl in *.
  apply (NoDupAppApp _ (f x) (f y) (flat_map f ys)).
  apply H.
Qed.

Lemma NoDupFlatMap : forall (a b : Type) (xs ys : list a) (f : a -> list b),
  NoDup (flat_map f xs) -> Permutation xs ys -> NoDup (flat_map f ys).
Proof.
  intros a b xs ys f H1 H2.
  induction ys as [| y ys IHys].
  constructor.
  simpl.
Admitted.

Lemma NoDupFlatMapApp : forall (a b : Type) (xs ys : list a) (f : a -> list b),
  NoDup (flat_map f (xs ++ ys)) -> NoDup (flat_map f xs ++ flat_map f ys).
Proof.
  intros a b xs ys f H.
  rewrite <- FlatMapApp.
  apply H.
Qed.

Lemma NoDupAppFlatMap : forall (a b : Type) (xs ys : list a) (f : a -> list b),
  NoDup (flat_map f xs ++ flat_map f ys) -> NoDup (flat_map f (xs ++ ys)).
Proof.
  intros a b xs ys f H.
  rewrite -> FlatMapApp.
  apply H.
Qed.

Lemma NotInApp : forall (a : Type) (x : a) (xs ys : list a),
  ~In x xs -> ~In x ys -> ~In x (xs ++ ys).
Proof.
  intros a x xs ys.
  destruct xs as [ | z zs]; auto.
  intros H1 H2 F; simpl.
  apply H1.
Admitted.