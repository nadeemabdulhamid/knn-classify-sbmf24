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
    length ks = length vs /\
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

Lemma ClassesOf_equiv_alt_1 :
    forall LT ks vs, 
        ClassesOf LT ks vs ->
        ClassesOf_alt LT ks vs.
Proof.
    intros LT ks vs Hc; split.
    apply ClassesOf_length with LT; auto.
    intros i.
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

Lemma ClassesOf_equiv_alt_2 :
    forall LT ks vs, 
        ClassesOf_alt LT ks vs ->
        ClassesOf LT ks vs.
Proof.
    induction ks as [ | k ks IHks ]; unfold ClassesOf_alt; 
        destruct vs as [ | v vs ]; simpl.
    - constructor.
    - intros (H1, H2); try discriminate.
    - intros (H1, H2); try discriminate.
    - intros (H1, H2).
      constructor.
      apply (H2 0 k v); auto.
      apply IHks.
      split; auto.
      intros i k' v' Hk' Hv'.
      apply (H2 (S i) k' v'); auto.
Qed.

Lemma ClassesOf_equiv_alt :
    forall LT ks vs, 
        ClassesOf LT ks vs <->
        ClassesOf_alt LT ks vs.
Proof.
    split.
    apply ClassesOf_equiv_alt_1.
    apply ClassesOf_equiv_alt_2.
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


Lemma plurality_none :
    forall ns cnt, plurality ns = (None, cnt) -> 
        ns = nil \/ exists m1 m2, m1 <> m2 /\ count ns m1 = cnt /\ count ns m2 = cnt /\ 
                                    (forall m', m' <> m1 -> m' <> m2 -> count ns m' <= cnt).
Proof.
    induction ns as [ | n ns Hns ]; auto.
    intros cnt Hplur.
    right.
    simpl in Hplur.
    destruct (plurality ns) as (rv, rc) eqn:Heqpl.
    destruct rv as [ v | ].
    -
        clear Hns. 
        exists v; exists n.
        destruct (rc =? S (count ns n)) eqn:Hrc.
        --
            apply EqNat.beq_nat_true_stt in Hrc.
            injection Hplur as Hplur'.
            rewrite Hplur' in *; clear Hplur' rc.
            apply plurality_some_count in Heqpl as H1.
            compare n v; intros Hnv.
            replace n with v in *; lia.
            apply plurality_all_lt with (m' := n) in Heqpl as H2.
            destruct H2; [ absurd (n=v); auto | ].
            repeat split; auto; simpl.
            replace (n =? v) with false; auto; symmetry.
            apply Nat.eqb_neq; auto.
            replace (n =? n) with true; auto; symmetry.
            apply Nat.eqb_eq; auto.
            intros m' Hm'v Hm'n.
            replace (n =? m') with false.
            rewrite <- H1.
            apply plurality_all_lt with (m' := m') in Heqpl as H2.
            destruct H2; auto; try lia.
            symmetry; apply Nat.eqb_neq; auto. 
        --
        destruct (rc <? S (count ns n)); try discriminate.
    - 
        destruct (rc <? S (count ns n)) eqn:Hlt; try discriminate.
        injection Hplur as Hplur; replace rc with cnt in *; clear Hplur rc.
        apply Nat.ltb_ge in Hlt.
        destruct (Hns cnt (eq_refl _)); clear Hns;
            [ rewrite H in *; clear H ns; simpl in *;
                injection Heqpl as Heqpl; lia | ].
        assert (count ns n < cnt) as Hlt'; try lia.
        destruct H as (m1, (m2, (H1, (H2, (H3, H4))))).
        exists m1, m2; repeat split; auto; try lia; simpl.
        destruct (n =? m1) eqn:Hnm1; try lia; rewrite Nat.eqb_eq in Hnm1; replace m1 with n in *; auto; lia.
        destruct (n =? m2) eqn:Hnm2; try lia; rewrite Nat.eqb_eq in Hnm2; replace m2 with n in *; auto; lia.
        intros m' Hm'm1 Hm'm2.
        destruct (n =? m') eqn:Hnm'.
        rewrite Nat.eqb_eq in Hnm'; rewrite Hnm' in *; lia. 
        rewrite Nat.eqb_neq in Hnm'; apply H4; auto.
Qed.


Theorem isplurality_is_plurality :
    forall ns m, IsPlurality m ns -> fst(plurality ns) = Some m.
Proof.
    intros ns m (H1, H2).
    destruct (plurality ns) as (res, cnt) eqn:Hplur.
    destruct res as [ val | ]; simpl.
    - 
        destruct (plurality_correct _ _ _ Hplur) as (Hp1, (Hp2, Hp3)).
        destruct (H2 val); auto.
        destruct (Hp3 m); auto.
        lia.
    -
        destruct (plurality_none _ _ Hplur).
        rewrite H in H1; inversion H1.
        destruct H as (m1, (m2, (Hc1, (Hc2, (Hc3, Hc4))))).
        destruct (H2 m1) as [ H | H ].
        -- 
            rewrite H in *; clear H m1.
            destruct (H2 m2) as [ H | H ].
            rewrite H in *; tauto.
            lia.
        -- 
            destruct (H2 m2) as [H' | H']  .
            rewrite H' in *; lia.
            assert (count ns m <= cnt); try lia.
            apply Hc4; auto;
                intro H0; rewrite H0 in *; lia.
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



Theorem classify_correct_some : 
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
    unfold classify; intros dist_metric Hdmwf K k data labels query c HK Hk Hdata Hdim Hlab Hclassify.
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
        apply Hlab.
        apply Permutation_in with (knn_search dist_metric K k (build_kdtree k data) query ++ far); auto.
        apply in_or_app; auto.
Qed.



(*
Require Extraction.
Extraction Language Scheme.

Recursive Extraction classify.
*)



(* ============= *)

Theorem classify_correct_none :
    forall dist_metric,
      dist_metric_wf dist_metric ->
    forall K k data labels query,
    0 < K -> 0 < k ->
    length data >= K ->
    (forall v' : datapt, List.In v' data -> length v' = k) ->  (* all data of dimension k *)
    (forall d : datapt, List.In d data -> FMap.In d labels) -> (* every datapt has a label *)
    classify dist_metric K k data labels query = None ->
    ~exists c,
        IsPlurality c (lookup_labels labels (knn_search dist_metric K k (build_kdtree k data) query)).
Proof.
    unfold classify; intros dist_metric Hdmwf K k data labels query HK Hk Hdata Hdim Hlab Hclassify.
    intros (c, Hplur).
    apply isplurality_is_plurality in Hplur.
    rewrite Hplur in Hclassify; discriminate.
Qed.



Theorem classify_correct : 
    forall dist_metric, dist_metric_wf dist_metric ->
    forall K k data labels query,
    0 < K -> 0 < k ->
    length data >= K ->
    (forall v' : datapt, List.In v' data -> length v' = k) ->
    (forall d : datapt, List.In d data -> FMap.In d labels) ->
    (exists c near far classes, classify dist_metric K k data labels query = Some c /\
        Permutation data (near ++ far) /\
        length near = K /\                       
        all_in_leb (dist_metric query) near far /\
        ClassesOf labels near classes /\
        IsPlurality c classes)
    \/
    (classify dist_metric K k data labels query = None /\
     ~exists c, IsPlurality c (lookup_labels labels 
                    (knn_search dist_metric K k 
                        (build_kdtree k data) query))).
Proof.
    intros dist_metric Hdmwf K k data labels query HK Hk Hdata Hdim Hlab.
    destruct (classify dist_metric K k data labels query) eqn:Heqn; [ left | right ].
    destruct (classify_correct_some dist_metric Hdmwf K k data labels query n HK Hk Hdata Hdim Hlab Heqn)
        as (near, (far, (classes, Hex))).
    exists n, near, far, classes; split; auto.
    split; auto.
    apply classify_correct_none; auto.
Qed.


