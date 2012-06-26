Require Import Aux List.
Require Import StackSet.
Require Import Arith.
Require Import Sorting.Permutation.

Variable (i l a sd : Set).

Lemma focusUpDown' (s : stack a) : focusDown' (focusUp' s) = s.
  Proof.
    destruct s as [[ | l ls] c rs]; try reflexivity.
    unfold StackSet.focusUp'; simpl.
    assert (H : rev (rev rs) = rs); try apply rev_involutive.
    generalize (rev rs) as rrs, H.
    destruct rrs as [ | r rrs].
      (* Base case *)
      intro Eq; rewrite <- Eq; reflexivity.
      (* Inductive case *)
      unfold StackSet.focusDown'; simpl.
      intro Eq; rewrite rev_unit, <- Eq; reflexivity.
  Qed.

Lemma focusDownUp' (s : StackSet.stack a) : StackSet.focusUp' (StackSet.focusDown' s) = s.
  Proof.
    destruct s as [ls c [ | r rs]]; unfold StackSet.focusDown'; try reflexivity.
    simpl; f_equal.
    (* Proof that getUp is OK *)
    assert (H : rev ls = rev ls); auto.
    generalize H as Eq.
    generalize (rev ls) at 1 3 4 as rls.
    intros.
    destruct rls as [ | x xs].
      simpl; symmetry; apply revNil; rewrite Eq; reflexivity.
      simpl; rewrite rev_unit; simpl; rewrite revStep, Eq, rev_involutive; reflexivity.
    (* Proof that getFocus is OK *)
    destruct (rev ls) as [ | z zs]; simpl; try rewrite rev_unit; reflexivity.
  Qed.

Lemma modifyId (f : StackSet.stack a -> StackSet.stack a) (s : StackSet.stackSet i l a sd) : 
  (forall xs, f xs = xs) -> StackSet.modify' f s = s.
  Proof.
    intro H; destruct s.
    unfold StackSet.modify', StackSet.modify.
    destruct getCurrent; destruct getWorkspace; destruct getStack; repeat (f_equal). 
    unfold StackSet.withStack.
    simpl; f_equal; apply H; reflexivity.
  Qed.

Lemma modifyComp (f g : StackSet.stack a -> StackSet.stack a) (s : StackSet.stackSet i l a sd) : 
  StackSet.modify' f (StackSet.modify' g s) = StackSet.modify' (fun s => f (g s)) s.
  Proof.
    destruct s; unfold StackSet.modify', StackSet.modify.
    destruct getCurrent; destruct getWorkspace; destruct getStack; repeat (f_equal).
  Qed.

Theorem prop_focus_right (s : StackSet.stackSet i l a sd) : StackSet.focusDown (StackSet.focusUp s) = s.
  Proof.
    unfold StackSet.focusUp, StackSet.focusDown.
    rewrite modifyComp, modifyId; [ | intros; rewrite focusUpDown']; reflexivity.
  Qed.

Theorem prop_focus_left (s : StackSet.stackSet i l a sd) : StackSet.focusUp (StackSet.focusDown s) = s.
  Proof.
    unfold StackSet.focusUp, StackSet.focusDown.
    rewrite modifyComp, modifyId; auto; intros; rewrite focusDownUp'; reflexivity.
  Qed.

Theorem prop_swap_master_focus (x : StackSet.stackSet i l a sd) : StackSet.peek (StackSet.swapMaster x) = StackSet.peek x.
  Proof.
    destruct x; unfold StackSet.peek; unfold StackSet.swapMaster; unfold StackSet.modify'.
    destruct getCurrent; destruct getWorkspace.
    unfold StackSet.withStack; unfold StackSet.getFocus.
    destruct getStack; simpl; [ destruct s; destruct getUp | ] ; reflexivity.
  Qed.

Theorem prop_swap_left_focus (x : StackSet.stackSet i l a sd) : StackSet.peek (StackSet.swapUp x) = StackSet.peek x.
  Proof.
    destruct x; unfold StackSet.peek; unfold StackSet.swapUp; unfold StackSet.modify'.
    destruct getCurrent; destruct getWorkspace.
    unfold StackSet.withStack; unfold StackSet.getFocus.
    destruct getStack; simpl; [destruct s; destruct getUp | ]; reflexivity.
  Qed.

Theorem prop_swap_right_focus (x : StackSet.stackSet i l a sd) : StackSet.peek (StackSet.swapDown x) = StackSet.peek x.
  Proof.
    destruct x; unfold StackSet.peek; unfold StackSet.swapDown; unfold StackSet.modify'.
    destruct getCurrent; destruct getWorkspace.
    unfold StackSet.withStack; unfold StackSet.getFocus; unfold StackSet.reverseStack.
    destruct getStack; simpl; [destruct s; destruct getDown | ]; simpl; reflexivity.
  Qed.

Theorem prop_swap_master_idempotent (x : StackSet.stackSet i l a sd) : 
  StackSet.swapMaster (StackSet.swapMaster x) = StackSet.swapMaster x.
  Proof.
    destruct x; unfold StackSet.swapMaster, StackSet.modify'.
    destruct getCurrent; destruct getWorkspace.
    destruct getStack as [ stack | ]; [ | reflexivity ].
    destruct stack as [ls c rs]; simpl.
    unfold StackSet.withStack; simpl.
    repeat f_equal.
    destruct ls; auto.
  Qed.

Definition hidden_spaces (x : StackSet.stackSet i l a sd) : list (StackSet.workspace i l a) :=
  map (fun x => StackSet.getWorkspace x) (StackSet.getVisible x) ++ (StackSet.getHidden x).

Theorem prop_swap_master_local (x : StackSet.stackSet i l a sd) :
  hidden_spaces (StackSet.swapMaster x) = hidden_spaces x.
  Proof.
    destruct x.
    unfold StackSet.swapMaster, StackSet.modify', StackSet.modify, StackSet.withStack.
    destruct getCurrent; destruct getWorkspace.
    unfold hidden_spaces; reflexivity.
  Qed.

Theorem prop_swap_left_local  (x : StackSet.stackSet i l a sd) :
  hidden_spaces (StackSet.swapUp x) = hidden_spaces x.
  Proof.
    destruct x.
    unfold StackSet.swapUp, StackSet.modify', StackSet.modify, StackSet.withStack.
    destruct getCurrent; destruct getWorkspace.
    unfold hidden_spaces; reflexivity.
  Qed.

Theorem prop_swap_right_local (x : StackSet.stackSet i l a sd) :
  hidden_spaces (StackSet.swapDown x) = hidden_spaces x.
  Proof.
    destruct x.
    unfold StackSet.swapDown, StackSet.modify', StackSet.modify, StackSet.withStack.
    destruct getCurrent; destruct getWorkspace.
    unfold hidden_spaces; reflexivity.
  Qed.

Theorem prop_focus_master_local (x : StackSet.stackSet i l a sd) :
  hidden_spaces x = hidden_spaces (StackSet.focusMaster x).
  Proof.
    destruct x.
    unfold StackSet.focusMaster.
    unfold StackSet.modify', StackSet.modify.
    destruct getCurrent; destruct getWorkspace.
    unfold hidden_spaces; reflexivity.
  Qed.

Theorem prop_focusMaster_idem (x : StackSet.stackSet i l a sd) :
  StackSet.focusMaster (StackSet.focusMaster x) = StackSet.focusMaster x.
  Proof.
    destruct x.
    unfold StackSet.focusMaster.
    destruct getCurrent; destruct getWorkspace; destruct getStack; auto.
    destruct s as [ls c rs]; simpl.
    unfold StackSet.withStack.
    simpl.
    do 3 repeat f_equal.
    destruct ls as [ | l ls]; auto.
    assert (exists x, exists xs, rev ls ++ l :: nil = x :: xs).
    destruct (rev ls) as [ | y ys].
    exists l; exists nil; auto.
    exists y; exists (ys ++ l :: nil); auto.
    destruct H as [x [xs Eq]].
    (* rewrite Eq at 1. *)
  Admitted.

Fixpoint concat (a : Set) (xss : list (list a)) : list a :=
  match xss with
    | nil => nil
    | xs :: xss => xs ++ concat a xss
  end.

Definition invariant (i l a sd : Set) (s : StackSet.stackSet i l a sd) : Prop :=
  let visibles := map (fun x => getWorkspace x) (getVisible s) in
  let hiddens := getHidden s in
  let current := getWorkspace (getCurrent s) in
  let findStack := fun x => maybe nil (fun s => s :: nil) (getStack x) in
  let ts := flat_map (fun x => findStack x) (current :: visibles ++ hiddens) in
  NoDup (flat_map (fun t => getFocus t :: getUp t ++ getDown t) ts).

Implicit Arguments invariant.

Lemma NoDupSingle (x : a) : NoDup (x :: nil).
  constructor; auto; constructor.
  Qed.

Lemma NoDupCons (xs : list a) (x : a) : NoDup (x :: xs) -> NoDup xs.
  Proof.
    intro H; induction xs.
    constructor.
    inversion H; assumption.
  Qed.    

Lemma InApp (x : a) (xs ys : list a) : In x (xs ++ x :: ys).
  Proof.
    induction xs.
    simpl; constructor; reflexivity.
    right; assumption.
  Qed.

Lemma InApp' (x y : a) (xs ys : list a) : In x (xs ++ ys) -> In x (xs ++ y :: ys).
  Proof.
    intro H.
    induction xs.
    right; assumption.
    destruct H as [H | H].
    rewrite H; constructor; reflexivity.
    right; apply IHxs; assumption.
  Qed.

Lemma InSuper (x : a) (xs ys : list a) : In x xs -> In x (xs ++ ys).
  intro H.
  induction xs as [ | z zs].
  inversion H.
  inversion H.
  constructor; exact H0.
  destruct H as [Eq | Later].
  constructor; exact Eq.
  right.
  apply (IHzs); auto.
  Qed.

Lemma InComm (x : a) (xs ys : list a) : In x (xs ++ ys) -> In x (ys ++ xs).
  Proof.
    induction xs as [ | z zs].
    simpl;rewrite app_nil_r; intros; assumption.
    intro H; destruct H as [H | H].
      rewrite H.
      apply InApp.
      apply InApp'.
      apply IHzs.
      assumption.
  Qed.

Lemma NotInComm (x : a) (xs ys : list a) : ~In x (xs ++ ys) -> ~In x (ys ++ xs).
  Proof.
    intros F H.
    induction ys as [ | y ys].
    induction xs as [ | z zs]; auto.
    rewrite app_nil_r in F; simpl in *; contradiction.
    destruct H as [H | H].
    rewrite H in *; apply F, InApp; assumption.
    apply F, InApp', InComm; auto.
  Qed.

Lemma NotInApp (x : a) (xs ys : list a) : ~In x xs -> ~In x ys -> ~In x (xs ++ ys).
  destruct xs as [ | z zs]; auto.
  intros H1 H2 F; simpl.
  apply H1.  
  Admitted.

Lemma NoDupApp (xs ys : list a) (H : NoDup (xs ++ ys)) : NoDup (ys ++ xs).
  Proof.
   induction ys.
   rewrite app_nil_r in H; assumption.
   constructor; 
     [ apply NotInComm, NoDup_remove_2; assumption 
     | apply IHys; apply NoDup_remove_1 in H; assumption].
  Qed.

Lemma NoDupPerm (xs ys : list a) (H : NoDup xs) (p : Permutation xs ys)  : NoDup ys.
  Proof.
    induction p.
    (* nil *)
    constructor.
    (* skip *)
    constructor. 
    intro F; apply (NoDup_remove_2 nil l0 x); auto.
    apply (Permutation_in (l:=l'));
      [ apply (Permutation_sym) | ]; auto.
    apply IHp.
    inversion H; auto.
    (* swap *)
    constructor.
    apply (NoDup_remove_2 (y :: nil) l0 x); auto.
    apply (NoDup_remove_1 (y :: nil) l0 x); auto.
    (* trans *)
    apply IHp2,IHp1; auto.
    Qed.
 

Lemma PermApp (xs ys zs : list a):
  Permutation ys zs -> Permutation (xs ++ ys) (xs ++ zs).
Proof.
  intros H1.
  induction xs; [auto | simpl; auto].
Qed.

Lemma PermutationRotate (xs : list a) : Permutation xs (rotate xs).
  induction xs; [constructor | ].
  apply Permutation_cons_app; rewrite app_nil_r; auto.
  Qed.
  
Theorem prop_swap_master_I (s : StackSet.stackSet i l a sd) :
  invariant s -> invariant (swapMaster s).
  Proof.
    intro H; destruct s; destruct getCurrent; destruct getWorkspace; simpl.
    destruct getStack as [ | s]; auto.
    destruct s as [ls c rs]; auto.
    destruct ls as [ | l ls]; auto.
    unfold withStack; unfold invariant in *.
    apply (NoDupPerm _ _ H); clear H.
    simpl; constructor.
    do 2 (rewrite app_comm_cons; apply Permutation_app_tail).
    apply (Permutation_trans (l' := (rev ls ++ l :: nil)));
      [ apply Permutation_rev | apply PermutationRotate].
  Qed.



Theorem prop_empty_I (m : l) (wids : {wids : list i | wids <> nil}) 
  (sds : {sds : list sd | length sds <= length (proj1_sig wids) /\ sds <> nil}) 
  : invariant (new l m wids sds).
  Proof.
    destruct sds as [sds [sdsLength nonNil]]; simpl in sdsLength.
    induction sds as [ | sd sds].
    (* Base case *)
      contradiction nonNil; auto.
    (* Cons case *)
      destruct wids as [wds widsProp]; induction wds as [ | wd wds].
      (* Base case *)
        simpl in *; absurd (S (length sds) <= 0); auto with arith.
      (* Cons case *)
        simpl in *.
        unfold invariant.
        simpl.
   Admitted.

Theorem prop_view_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
  invariant s -> invariant (_view eq_nat_dec n s).
  Proof.
    unfold _view.
    case (eq_nat_dec n (currentTag s)); auto.
    case (find (fun y  => proj1_sig (beqi eq_nat_dec n (getTag (getWorkspace y))))
         (getVisible s)).
    destruct s.
  Admitted.

Theorem prop_greedyView_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
  invariant s -> invariant (_greedyView eq_nat_dec n s).
  Proof.
    unfold _greedyView.
    case (existsb (fun x => proj1_sig (beqi eq_nat_dec n (getTag x))) (getHidden s)).
    apply prop_view_I.
    case (find (fun x => proj1_sig 
                 (beqi eq_nat_dec n (getTag (getWorkspace x))))
                 (getVisible s)); auto.
    destruct s; simpl.
    destruct s; simpl.
  Admitted.

Theorem prop_focusUp_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
  invariant s -> invariant (iterate n (focusUp (i:=nat) (l:=l) (a:=a)(sd:=sd)) s).
  Proof.
    generalize s; induction n; auto; clear s.
    intros s IHs; simpl.
    cut (invariant (focusUp s)).
    intro H; apply (IHn _ H).
    unfold invariant in *.
    (* apply NoDupPerm.*)
  Admitted.

Theorem prop_focusMaster_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
  invariant s -> invariant (iterate n (focusMaster (i:=nat) (l:=l) (a:=a)(sd:=sd)) s).
  Proof.
    generalize s; induction n; auto.
    intros st IHs; simpl.
    cut (invariant (focusMaster st)).
    intro H; apply (IHn _ H).
    unfold invariant in *.
    Admitted.

      (*
Remaining QuickCheck properties that have not been verified in Coq:
        [("StackSet invariants" , mytest prop_invariant)
        ,("empty is empty"      , mytest prop_empty)
        ,("empty / current"     , mytest prop_empty_current)
        ,("empty / member"      , mytest prop_member_empty)
        ,("view sets current"   , mytest prop_view_current)
        ,("view idempotent"     , mytest prop_view_idem)
        ,("view reversible"    , mytest prop_view_reversible)
        ,("view is local"       , mytest prop_view_local)
        ,("greedyView : invariant"    , mytest prop_greedyView_I)
        ,("greedyView sets current"   , mytest prop_greedyView_current)
        ,("greedyView is safe "   ,   mytest prop_greedyView_current_id)
        ,("greedyView idempotent"     , mytest prop_greedyView_idem)
        ,("greedyView reversible"     , mytest prop_greedyView_reversible)
        ,("greedyView is local"       , mytest prop_greedyView_local)
        ,("peek/member "        , mytest prop_member_peek)
        ,("index/length"        , mytest prop_index_length)
        ,("focus left : invariant", mytest prop_focusUp_I)
        ,("focus master : invariant", mytest prop_focusMaster_I)
        ,("focus right: invariant", mytest prop_focusDown_I)
        ,("focusWindow: invariant", mytest prop_focus_I)
        ,("focus left/master"   , mytest prop_focus_left_master)
        ,("focus right/master"  , mytest prop_focus_right_master)
        ,("focus master/master"  , mytest prop_focus_master_master)
        ,("focusWindow master"  , mytest prop_focusWindow_master)
        ,("focus all left  "    , mytest prop_focus_all_l)
        ,("focus all right "    , mytest prop_focus_all_r)
        ,("focus down is local"      , mytest prop_focus_down_local)
        ,("focus up is local"      , mytest prop_focus_up_local)
        ,("focus master idemp"  , mytest prop_focusMaster_idem)
        ,("focusWindow is local", mytest prop_focusWindow_local)
        ,("focusWindow works"   , mytest prop_focusWindow_works)
        ,("focusWindow identity", mytest prop_focusWindow_identity)
        ,("findTag"           , mytest prop_findIndex)
        ,("allWindows/member"   , mytest prop_allWindowsMember)
        ,("currentTag"          , mytest prop_currentTag)
        ,("insert: invariant"   , mytest prop_insertUp_I)
        ,("insert/new"          , mytest prop_insert_empty)
        ,("insert is idempotent", mytest prop_insert_idem)
        ,("insert is reversible", mytest prop_insert_delete)
        ,("insert is local"     , mytest prop_insert_local)
        ,("insert duplicates"   , mytest prop_insert_duplicate)
        ,("insert/peek "        , mytest prop_insert_peek)
        ,("insert/size"         , mytest prop_size_insert)
        ,("delete: invariant"   , mytest prop_delete_I)
        ,("delete/empty"        , mytest prop_empty)
        ,("delete/member"       , mytest prop_delete)
        ,("delete is reversible", mytest prop_delete_insert)
        ,("delete is local"     , mytest prop_delete_local)
        ,("delete/focus"        , mytest prop_delete_focus)
        ,("delete  last/focus up", mytest prop_delete_focus_end)
        ,("delete ~last/focus down", mytest prop_delete_focus_not_end)
        ,("filter preserves order", mytest prop_filter_order)
        ,("swapMaster: invariant", mytest prop_swap_master_I)
        ,("swapUp: invariant" , mytest prop_swap_left_I)
        ,("swapDown: invariant", mytest prop_swap_right_I)
        ,("swap all left  "     , mytest prop_swap_all_l)
        ,("swap all right "     , mytest prop_swap_all_r)
        ,("shiftMaster id on focus", mytest prop_shift_master_focus)
        ,("shiftMaster is local", mytest prop_shift_master_local)
        ,("shiftMaster is idempotent", mytest prop_shift_master_idempotent)
        ,("shiftMaster preserves ordering", mytest prop_shift_master_ordering)
        ,("shift: invariant"    , mytest prop_shift_I)
        ,("shift is reversible" , mytest prop_shift_reversible)
        ,("shiftWin: invariant" , mytest prop_shift_win_I)
        ,("shiftWin is shift on focus" , mytest prop_shift_win_focus)
        ,("shiftWin fix current" , mytest prop_shift_win_fix_current)
        ,("floating is reversible" , mytest prop_float_reversible)
        ,("floating sets geometry" , mytest prop_float_geometry)
        ,("floats can be deleted", mytest prop_float_delete)
        ,("screens includes current", mytest prop_screens)
        ,("differentiate works", mytest prop_differentiate)
        ,("lookupTagOnScreen", mytest prop_lookup_current)
        ,("lookupTagOnVisbleScreen", mytest prop_lookup_visible)
        ,("screens works",      mytest prop_screens_works)
        ,("renaming works",     mytest prop_rename1)
        ,("ensure works",     mytest prop_ensure)
        ,("ensure hidden semantics",     mytest prop_ensure_append)
        ,("mapWorkspace id", mytest prop_mapWorkspaceId)
        ,("mapWorkspace inverse", mytest prop_mapWorkspaceInverse)
        ,("mapLayout id", mytest prop_mapLayoutId)
        ,("mapLayout inverse", mytest prop_mapLayoutInverse)
        ,("abort fails",            mytest prop_abort)
        ,("new fails with abort",   mytest prop_new_abort)
        ,("shiftWin identity",      mytest prop_shift_win_indentity)
        ,("tile 1 window fullsize", mytest prop_tile_fullscreen)
        ,("tiles never overlap",    mytest prop_tile_non_overlap)
        ,("split hozizontally",     mytest prop_split_hoziontal)
        ,("split verticalBy",       mytest prop_splitVertically)
        ,("pure layout tall",       mytest prop_purelayout_tall)
        ,("send shrink    tall",    mytest prop_shrink_tall)
        ,("send expand    tall",    mytest prop_expand_tall)
        ,("send incmaster tall",    mytest prop_incmaster_tall)
        ,("pure layout full",       mytest prop_purelayout_full)
        ,("send message full",      mytest prop_sendmsg_full)
        ,("describe full",          mytest prop_desc_full)
        ,("describe mirror",        mytest prop_desc_mirror)
        ,("window hints: inc",      mytest prop_resize_inc)
        ,("window hints: inc all",  mytest prop_resize_inc_extra)
        ,("window hints: max",      mytest prop_resize_max)
        ,("window hints: max all ", mytest prop_resize_max_extra)
        ]

*)