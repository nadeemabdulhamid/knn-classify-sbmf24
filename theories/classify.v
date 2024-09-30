Require Import FunInd.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Orders.
Require Import List.
Require Import SetoidList.  
Require Import PeanoNat.
Require Import Coq.Init.Nat.
Require Import kdtree.
Require Import bounding_boxes.
Require Import knn_search.
Require Import list_ot.
Require Import tactics.
Require Import Permutation.
Require Import Lia.
Require Import FMapAVL.
Require Import max_pqueue.


(* ======= Data Structure Instantiations ======= *)

Module Import FMap := FMapAVL.Make(ListOrderedType).
Import FMap.Raw.Proofs.
Definition LabelTable := (FMap.t nat). (* a dictionary mapping `datapt`s (`list nat`) to `nat` (classification labels)*)

Module MaxPQ := List_MaxPQ NatTTLB.
Module KNNS_LPQ := KNNS MaxPQ. (* instantiate the KNN search module with a PQ implementation *)
Import KNNS_LPQ.  


(* ========== Implementations =================== *)

Definition unwrap (opt : option nat) : nat :=
    match opt with
        | Some value => value
        | None => 0
    end.

Fixpoint count(vals : list nat)(num: nat) : nat:=
    match vals with
    |nil => 0
    |h :: t => if h =? num 
                then S (count t num) 
                else count t num 
    end.

Example test_count1 :
    (count (1:: 2 :: 3 :: 3 :: 3 :: nil) 3) = 3.
reflexivity. Qed.

Example test_count2 :
    (count (1:: 2 :: 3 :: 3 :: 3 :: nil) 2) = 1.
reflexivity. Qed.    

Fixpoint lookup_labels (LT : LabelTable) (keys : list datapt) : (list nat) := 
    match keys with 
        | nil => nil
        | h :: t => unwrap (find h LT) :: lookup_labels LT t
    end.


Function plurality (vals : list nat) : option nat * nat:=
  match vals with 
  | nil    => (None, 0)
  | h :: t => match (plurality t) with
             | (None, c) => let c' := (1 + count t h) in 
                 if c <? c' then (Some h, c') else (None, c)
             | (Some x, c) => let c' := (1 + count t h) in
                 if c =? c'      then (None, c)
                 else if c <? c' then (Some h, c')
                 else                 (Some x, c)
                 end
            end.

Example test_plurality : (plurality (4 :: 7 :: 2 :: 4 :: nil)) = (Some 4, 2).
reflexivity. Qed.

Example test_plurality1 : (plurality (2 :: 2 :: 5 :: 5 :: 5 :: 2 :: 2 :: nil)) = (Some 2, 4).
reflexivity. Qed.

Example test_plurality2 : (plurality (7 :: 7 :: 5 :: 5 :: 5 :: nil)) = (Some 5, 3).
reflexivity. Qed.

Compute (plurality (4 :: 7 :: 2 :: 2 :: 2 :: 2 :: 2 :: 4 :: nil)).

Example test_plurality3 : (plurality (4 :: 7 :: 2 :: 2 :: 2 :: 2 :: 2 :: 4 :: nil)) = (Some 2, 5).
reflexivity. Qed.

Example test_plurality4 : (plurality (4 :: 7 :: 2 :: 2 :: 4 :: nil)) = (None, 2).
reflexivity. Qed.


Definition classify (dist_metric : datapt -> datapt -> nat)
                    (K : nat)  (* number of neighbors *)
                    (k : nat)  (* dimensions of all points*)
                    (dataset : (list datapt))
                    (labeltable : LabelTable) 
                    (query : datapt)
                    : option nat :=  (* produces the predicted label for query *)
    let ktree := (build_kdtree k dataset) in
    let nbrs := knn_search dist_metric K k ktree query in
        fst( plurality (lookup_labels labeltable nbrs) ).
        



(* ========== Specifications =================== *)

(* `ClassesOf LT ks vs` is a proposition representing
    "LT maps the elements of ks, pairwise, to elements of vs"
*)
Inductive ClassesOf (LT : LabelTable) : list datapt -> list nat -> Prop :=
    | classesOf_nil : ClassesOf LT nil nil
    | classesOf_cons : 
        forall k v ks vs,
        MapsTo k v LT ->
        ClassesOf LT ks vs ->
        ClassesOf LT (k::ks) (v::vs).


Definition ClassesOf_alt (LT : LabelTable) (ks : list datapt) (vs : list nat) : Prop :=
    forall i k v, nth_error ks i = Some k -> nth_error vs i = Some v -> MapsTo k v LT.




(*
  `IsPlurality m ns`  is a proposition defined as what it means to say:
  "m is the plurality element of ns"  
  which is to say,
     "m is an element of ns, and the count of anything in ns (that is not
      already m) is strictly less than the count of m in ns."
*)
Definition IsPlurality (m:nat) (ns:list nat) : Prop :=
   List.In m ns
   /\ (forall m', m' = m \/ count ns m' < count ns m).




(* ==========    Tactics    =================== *)


Ltac simpl_count :=
    repeat match goal with 
    | H : context [ count (?x :: ?z) ?x ]  |- _ => simpl (count (?x :: ?z) ?y) in H at 1; replace (x =? x) with true in H;  [ | symmetry; apply Nat.eqb_eq; auto] 
    | H : context [ count (?x :: ?z) ?y ] , _ : ?x <> ?y |- _ => simpl (count (?x :: ?z) ?y) in H at 1; replace (x =? y) with false in H;  [ | symmetry; apply Nat.eqb_neq; auto]
    | H : context [ count (?x :: ?z) ?y ] , _ : ?y <> ?x |- _ => simpl (count (?x :: ?z) ?y) in H at 1; replace (x =? y) with false in H;  [ | symmetry; assert (x <> y); auto; apply Nat.eqb_neq; auto]
    | H : context [ count (?x :: ?z) ?y ] , _ : ?x = ?y |- _ => simpl (count (?x :: ?z) ?y) in H at 1; replace (x =? y) with true in H;  [ | symmetry; auto; apply Nat.eqb_eq; auto]
    | H : context [ count (?x :: ?z) ?y ] , _ : ?y = ?x |- _ => simpl (count (?x :: ?z) ?y) in H at 1; replace (x =? y) with true in H;  [ | symmetry; auto; apply Nat.eqb_eq; auto]
    | H : context [ (?x =? ?y) ], _ : ?x <> ?y |- _ => replace (x =? y) with false in H;  [ | symmetry; apply Nat.eqb_neq; auto]
    | H : context [ (?x =? ?y) ], _ : ?y <> ?x |- _ => replace (x =? y) with false in H;  [ | symmetry; assert (x <> y); auto; apply Nat.eqb_neq; auto]
    | H : ?x = ?y |- context [ count (?x :: ?z) ?y ] => simpl (count (?x :: ?z) ?y) at 1;  replace (x =? y) with true;  [ | symmetry; auto; apply Nat.eqb_eq; auto]
    |  |- context [ count (?x :: ?z) ?x ] => simpl (count (?x :: ?z) ?x) at 1;  replace (x =? x) with true;  [ | symmetry; auto; apply Nat.eqb_eq; auto]
    | H : ?x <> ?y |- context [ count (?x :: ?z) ?y ] => simpl (count (?x :: ?z) ?y) at 1;  replace (x =? y) with false;  [ | symmetry; auto; apply Nat.eqb_neq; auto]
    | H : ?y <> ?x |- context [ count (?x :: ?z) ?y ] => simpl (count (?x :: ?z) ?y) at 1;  replace (x =? y) with false;  [ | symmetry; assert (x <> y); auto; apply Nat.eqb_neq; auto]
    end.


Ltac by_plurality_ind ns :=
    (* Check plurality_ind.   <----   tells the params for each of the cases *)
    functional induction (plurality ns) using plurality_ind as 
        [ vals Hv 
        | vals n ns' Hv IHns c' Hmaj' Hcount Hlt_true 
        | vals n ns' Hv IHns c' Hmaj' Hcount Hlt_false
        | vals n ns' Hv IHns x' c' Hmaj' Hcount Heq_true
        | vals n ns' Hv IHns x' c' Hmaj' Hcount Heq_false Hlt_true
        | vals n ns' Hv IHns x' c' Hmaj' Hcount Heq_false Hlt_false 
        ]; split_andb_leb; simpl_count.



(* ==========     Proofs     =================== *)


Lemma List_Map_In_ext :
    forall (h:datapt) lst (map:LabelTable),
    (forall k, List.In k (h :: lst) -> In k map) ->
    (forall k, List.In k lst -> In k map).
Proof.
    intros.
    apply H.
    right; auto.
Qed.


(* ClassesOf is a specification for lookup_labels *)
Lemma lookup_labels_correct : forall LT ks vs,
    (forall k', List.In k' ks -> In k' LT) ->
    lookup_labels LT ks = vs -> ClassesOf LT ks vs.
Proof.
    induction ks as [ | k ks']; intros vs Hin Hlk; simpl in Hlk; subst; constructor.
    apply find_2.
    destruct (find (elt:=nat) k LT) as [ v | ] eqn:Hf ; auto.
    assert (In k LT) as Hin'; [ apply Hin; left; auto | ].
    absurd (find k LT = None); auto.
    apply find_in_iff; auto using (is_bst LT).
    apply In_alt; auto.

    apply IHks'; auto.
    eapply List_Map_In_ext; eauto.
Qed.



(*****************************************************************)
(* ASIDE - alternate specification of ClassesOf *)

Lemma ClassesOf_length : forall LT ks vs, ClassesOf LT ks vs -> length ks = length vs.
Proof.
    intros LT ks vs Hc; induction Hc; simpl; auto.
Qed.

Lemma ClassesOf_in_mapsto : 
    forall LT ks vs, 
        ClassesOf LT ks vs ->
        forall k, List.In k ks -> exists v, List.In v vs /\ MapsTo k v LT.
Proof.
    intros LT ks vs Hc; induction Hc; simpl; try tauto.  
    intros k' [ Hin | Hin ]; subst.
    exists v; split; auto.
    destruct (IHHc _ Hin) as (v', (Hv1, Hv2)).
    exists v'; split; auto.
Qed.

Lemma ClassesOf_mapsto_in : 
    forall LT ks vs, 
        ClassesOf LT ks vs ->
        forall v, List.In v vs -> exists k, List.In k ks /\ MapsTo k v LT.
Proof.
    intros LT ks vs Hc; induction Hc; simpl; try tauto.  
    intros v' [ Hin | Hin ]; subst.
    exists k; split; auto.
    destruct (IHHc _ Hin) as (k', (Hk1, Hk2)).
    exists k'; split; auto.
Qed.

Lemma ClassesOf_equiv_alt :
    forall LT ks vs, 
        ClassesOf LT ks vs ->
        ClassesOf_alt LT ks vs.
Proof.
    intros LT ks vs Hc i.
    generalize LT ks vs Hc; clear LT ks vs Hc.
    induction i.
    - intros LT ks vs Hc k v H1 H2.
      destruct ks as [ | k' ks]; inversion H1.
      destruct vs as [ | v' vs]; inversion H2.
      replace k' with k in *; replace v' with v in *; clear k' v'.
      inversion Hc; auto.
    - intros LT ks vs Hc k v H1 H2.
      destruct ks as [ | k' ks]; inversion H1.
      destruct vs as [ | v' vs]; inversion H2.
      inversion Hc; auto.
      apply IHi with ks vs; auto.
Qed.

(*****************************************************************)





Lemma plurality_in_list : 
    forall ns m c,
        plurality ns = (Some m, c)
         -> List.In m ns.
Proof.
    intros ns; by_plurality_ind ns; intros m c Hmaj; try discriminate; inversion Hmaj; 
        auto using in_eq; subst; right; eauto.
Qed.


Lemma plurality_all_le :
    forall ls mx c, plurality ls = (mx, c) -> forall m, count ls m <= c.
Proof.
    intros ns; by_plurality_ind ns; intros mx c Hmaj m; 
    inversion Hmaj; 
         auto; apply IHns with (m := m) in Hmaj' as IHm; apply IHns with (m := n) in Hmaj' as IHn;
         subst;
        repeat (compare n m; intros Hnm; subst; simpl_count; auto; try lia).
Qed.


Lemma eq_plurality_impossible : (* the plurality count cannot be a tie *)
    forall ls m' m c ,          (* between two distinct values *) 
        m' <> m -> (count ls m') = c -> (count ls m) = c ->
            forall x, plurality ls <> (Some x, c).
Proof.
    intros ns; by_plurality_ind ns; intros m' m c Hm'm Hmc' Hmc x; try discriminate.

    (* Handling the (plurality ns) = (None, c') cases: *)
    compare n m; compare n m'; intros Hnm' Hnm; subst; simpl_count; auto.

    assert (count ns' m' <= c'); try apply plurality_all_le with None; auto; lia.
    assert (count ns' m <= c'); try apply plurality_all_le with None; auto; lia.
    intros contra; inversion contra; subst;
        assert (count ns' m' <= c'); [ apply plurality_all_le with None; auto | lia ].

    (* Now the (plurality ns) = (Some x', c') cases: *)
    compare n m; compare n m'; intros Hnm' Hnm; subst; auto; simpl_count; simpl in *;
        [ assert (count ns' m' <= c'); [ apply plurality_all_le with (Some x'); auto | lia] | | ];
    repeat
     (intros contra; inversion contra as [(H2, H3)]; subst;
        assert (plurality ns' <> (Some x', c')); auto;
        apply IHns with (c := c') (x := x') (m' := m') (m := m); auto; try lia;
         [ assert (count ns' m' <= c'); [ apply plurality_all_le with (Some x'); auto | lia] |
           assert (count ns' m <= c'); [ apply plurality_all_le with (Some x'); auto | lia] ]).

    (* *)
    compare n m; compare n m'; intros Hnm' Hnm; subst; auto; simpl_count; auto; simpl in *.
    rewrite Hmc in Heq_false; intros contra; inversion contra; auto.
    rewrite <- Hmc in Heq_false; intros contra; inversion contra; subst; auto.
    rewrite <- Hmaj'; apply IHns with (m':=m') (m:=m); auto.
Qed.


Lemma plurality_some_count :
    forall ls m c, 
        plurality ls = (Some m, c) -> count ls m = c.
Proof.
    intros ns; by_plurality_ind ns; intros m c H; try discriminate;
        inversion H as [(H1, H2)]; simpl_count; subst; intuition.
    assert (n <> m);
        [ intros Habs; subst; apply IHns in Hmaj'; lia 
        | simpl_count; intuition ].
Qed.


Lemma plurality_all_lt : 
    forall ns m c,
        plurality ns = (Some m, c)
    -> forall m', 
           m' = m \/ count ns m' < count ns m.
Proof.
    induction ns as [ | n ns' IHns ]; intros m c Hm m'; try discriminate.
    apply plurality_all_le with (m := m') in Hm as HLe; auto.
    compare m' m; [ left | right ] ; auto.
    apply plurality_some_count in Hm as Hc; auto.
    rewrite Hc.
    apply Nat.lt_eq_cases in HLe; destruct HLe; auto.
    absurd(plurality (n :: ns') = (Some m, c)); auto.
    eapply eq_plurality_impossible; eauto.
Qed.


Lemma plurality_correct : 
    forall ns m c, 
    plurality ns = (Some m, c) ->
        List.In m ns /\ 
        count ns m = c /\
        (forall m', m' = m \/ count ns m' < count ns m).
Proof.
    intros ns m c Hm.
    repeat split.
    - eapply plurality_in_list; eauto.
    - eapply plurality_some_count; eauto.
    - eapply plurality_all_lt; eauto.
Qed.


Theorem plurality_is_plurality :
    forall ns m, fst(plurality ns) = Some m -> IsPlurality m ns.
Proof.
    intros; destruct (plurality ns) as [[ mx | ] c] eqn:Hmaj; try discriminate.
    apply plurality_correct in Hmaj.
    replace m with mx in *; try inversion H; auto.
    unfold IsPlurality; split_andb_leb; split; auto.
Qed.




Theorem classify_correct0 : 
    forall dist_metric,
      dist_metric_wf dist_metric ->
    forall K k data labels query c,
    0 < K -> 0 < k ->
    length data >= K ->
    (forall v' : datapt, List.In v' data -> length v' = k) ->  (* all data of dimension k *)
    classify dist_metric K k data labels query = Some c ->
    exists near far, 
        Permutation data (near ++ far) /\
        length near = K /\                       (* `near`s are the K nearest neighbors *)
        all_in_leb (dist_metric query) near far /\
        IsPlurality c (lookup_labels labels near). (* c is the plurality of all the `near` labels c*)
Proof.
    unfold classify; intros dist_metric Hdmwf K k data labels query c HK Hk Hdata Hdim Hclassify.
    assert (exists far : list datapt,
        length (knn_search dist_metric K k (build_kdtree k data) query) = min K (length data) /\
        Permutation data ((knn_search dist_metric K k (build_kdtree k data) query) ++ far) /\
        all_in_leb (dist_metric query) (knn_search dist_metric K k (build_kdtree k data) query) far); 
            [ eapply (knn_search_build_kdtree_correct dist_metric Hdmwf K k data); eauto; try lia | ].
    destruct H as (far, (Hmin, (Hperm, Hleb))).
    exists (knn_search dist_metric K k (build_kdtree k data) query), far.
    split; auto; try lia.
    split; auto; try lia.
    split; auto; try lia.
    apply plurality_is_plurality; auto.
Qed.



Theorem classify_correct : 
    forall dist_metric,
      dist_metric_wf dist_metric ->
    forall K k data labels query c,
    0 < K -> 0 < k ->
    length data >= K ->
    (forall v' : datapt, List.In v' data -> length v' = k) ->  (* all data of dimension k *)
    (forall d : datapt, List.In d data -> FMap.In d labels) -> (* every datapt has a label *)
    classify dist_metric K k data labels query = Some c ->
    exists near far classes,
        Permutation data (near ++ far) /\
        length near = K /\                       (* `near`s are the K nearest neighbors *)
        all_in_leb (dist_metric query) near far /\
        ClassesOf labels near classes /\
        IsPlurality c classes. (* c is the plurality of all the `near` labels c*)
Proof.
    unfold classify; intros dist_metric Hdmwf K k data labels query c HK Hk Hdata Hdim Hclassify.
    assert (exists far : list datapt,
        length (knn_search dist_metric K k (build_kdtree k data) query) = min K (length data) /\
        Permutation data ((knn_search dist_metric K k (build_kdtree k data) query) ++ far) /\
        all_in_leb (dist_metric query) (knn_search dist_metric K k (build_kdtree k data) query) far); 
            [ eapply (knn_search_build_kdtree_correct dist_metric Hdmwf K k data); eauto; try lia | ].
    destruct H as (far, (Hmin, (Hperm, Hleb))).
    exists (knn_search dist_metric K k (build_kdtree k data) query), far.
    exists (lookup_labels labels (knn_search dist_metric K k (build_kdtree k data) query)).
    repeat split; auto; try lia; try apply plurality_is_plurality; auto.
    apply lookup_labels_correct; auto.
        intros k' Hinknn.
        apply Hclassify.
        apply Permutation_in with (knn_search dist_metric K k (build_kdtree k data) query ++ far); auto.
        apply in_or_app; auto.
Qed.



(*
Require Extraction.
Extraction Language Scheme.

Recursive Extraction classify.
*)
