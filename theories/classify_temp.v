
Theorem classesof_lookup_labels :
    forall labels pts cs,
    ClassesOf labels pts cs ->
    Permutation (lookup_labels labels pts) cs.
Proof.    
    intros labels pts cs Hcs.
    induction Hcs; auto.
    simpl.
    replace (unwrap (find (elt:=nat) k labels)) with v.
    apply perm_skip; auto.
    symmetry.
    apply FMap.find_1 in H; rewrite H; auto.
Qed.


Lemma permutation_count :
    forall v cs cs', Permutation cs cs' -> count cs v = count cs' v.
Proof.
    intros v cs cs' Hperm; induction Hperm; auto; simpl.
    destruct (x =? v); auto.
    destruct (y =? v); destruct (x =? v); auto.
    rewrite IHHperm1; auto.
Qed.

Lemma permutation_isplurality :
    forall v cs cs', Permutation cs cs' -> IsPlurality v cs -> IsPlurality v cs'.
Proof.
    intros v cs cs' Hperm (Hp1, Hp2); split.
    apply Permutation_in with cs; auto.
    intros m'.
    destruct (Hp2 m'); [left | right]; auto.
    replace (count cs' m' ) with (count cs m' ); [
        replace (count cs' v ) with (count cs v ) | 
    ]; auto using permutation_count.
Qed.



Lemma eq_dec_datapt : forall x y : datapt, {x = y} + {x <> y}.
Proof.
    induction x; destruct y; auto.
    right; discriminate.
    right; discriminate.
    compare a n; intros Han.
    rewrite Han; clear Han a.
    destruct (IHx y).
    left; rewrite e; auto.
    right. intros Hn; inversion Hn; absurd (x = y); auto.
    right; intros Hn; inversion Hn; absurd (a = n); auto.
Qed.


Lemma permutation_all_in_leb :
    forall dm data (a:list datapt)  b c d,
        length a = length c ->
        Permutation data (a ++ b) ->
        Permutation data (c ++ d) ->
        all_in_leb dm a b ->
        all_in_leb dm c d ->
        Permutation a c.
Proof.
    intros.        
    rewrite (Permutation_count_occ eq_dec_datapt) in *.
    unfold all_in_leb in *.
    intros x.
    pose (H0 x) as H0x.
    pose (H1 x) as H1x.
    rewrite (count_occ_app eq_dec_datapt) in *.



Admitted.



Lemma permutation_lookup_labels :
    forall ls a b,
        Permutation a b ->
        Permutation (lookup_labels ls a) (lookup_labels ls b).
Proof.
    intros ls a b Hperm; induction Hperm; auto; simpl.
    apply perm_skip; auto.
    apply perm_swap; auto.
    apply perm_trans with (lookup_labels ls l'); auto.
Qed.


Theorem classify_correct_none : 
    forall dist_metric,
      dist_metric_wf dist_metric ->
    forall K k data labels query,
    0 < K -> 0 < k ->
    length data >= K ->
    (forall v' : datapt, List.In v' data -> length v' = k) ->  (* all data of dimension k *)
    (forall d : datapt, List.In d data -> FMap.In d labels) -> (* every datapt has a label *)
    classify dist_metric K k data labels query = None ->
    forall near far classes,
        Permutation data (near ++ far) ->
        length near = K ->
        all_in_leb (dist_metric query) near far ->
        ClassesOf labels near classes ->
        ~exists c, IsPlurality c classes.
Proof.
    unfold classify; intros dist_metric Hdmwf K k data labels query HK Hk Hdata Hdim Hlab Hclassify.
    intros near far classes H1 H2 H3 H4.
    assert (Permutation (lookup_labels labels near) classes); [ apply classesof_lookup_labels; auto | ].
    intros (c, Hc).
    assert (IsPlurality c (lookup_labels labels near)); [ apply permutation_isplurality with classes; auto | ].

    assert (0 < length data) as Hlen; try lia.
    destruct (knn_search_build_kdtree_correct dist_metric Hdmwf K k data HK Hlen Hk Hdim (build_kdtree k data) query 
            (knn_search dist_metric K k (build_kdtree k data) query) (eq_refl _) (eq_refl _))
            as (leftover, (Hk1, (Hk2, Hk3))).
    replace (min K (length data)) with K in *; try lia.
    assert (Permutation near (knn_search dist_metric K k (build_kdtree k data) query)); [ eapply permutation_all_in_leb; eauto; rewrite H2; auto | ].
    assert (Permutation (lookup_labels labels near) (lookup_labels labels (knn_search dist_metric K k (build_kdtree k data) query))); [ apply permutation_lookup_labels; auto | ].
    apply (classify_correct_none0 dist_metric Hdmwf K k data labels query HK Hk Hdata Hdim Hlab Hclassify).
    exists c.
    apply permutation_isplurality with (lookup_labels labels near); auto.
Qed.



Lemma classesof_same :
    forall labels xs cs1,
    ClassesOf labels xs cs1 -> forall cs2,
    ClassesOf labels xs cs2 ->
    cs1 = cs2.
Proof.
    intros labels xs cs1 Hc1; induction Hc1; intros cs2 Hc2.
    inversion Hc2; auto.
    inversion_clear Hc2; auto.
    apply FMap.find_1 in H, H0.
    rewrite H in H0; injection H0 as H0; rewrite H0.
    replace vs0 with vs; auto.
Qed.



Lemma classesof_perm_exists :
    forall l l',
        Permutation l l' ->
        forall labels bs,
        ClassesOf labels l bs ->
        exists cs : list nat, ClassesOf labels l' cs /\ Permutation bs cs.

Admitted.


Lemma classesof_permutation :
    forall cs es,
        Permutation es cs -> forall labels bs ds,
        ClassesOf labels es bs ->
        ClassesOf labels cs ds ->
        Permutation bs ds.
Proof.
    intros cs es Hperm; induction Hperm; auto; intros labels bs ds Hc1 Hc2.
    - 
    inversion Hc1; inversion Hc2; auto.
    - 
    inversion_clear Hc1; inversion_clear Hc2; auto.
    apply FMap.find_1 in H, H1.
    rewrite H in H1; injection H1 as H1; rewrite H1; apply perm_skip; auto.
    apply IHHperm with labels; auto.
    -
    inversion_clear Hc1; inversion_clear Hc2; auto.
    inversion_clear H0; inversion_clear H2; auto.
    apply FMap.find_1 in H, H1, H3, H0.
    rewrite H in H0; injection H0 as H0.
    rewrite H1 in H3; injection H3 as H3.
    rewrite H0, H3.
    replace vs2 with vs1.
    apply perm_swap; auto.
    eapply classesof_same; eauto.
    -
    assert (exists cs, ClassesOf labels l' cs /\ Permutation bs cs).
    eapply classesof_perm_exists; eauto.
    destruct H as (cs, (Hc3, Hc4)).
    apply perm_trans with cs; auto.
    apply (IHHperm2 labels cs); auto.
Qed.



Lemma plurality_unique_perm : 
    forall cs cs',
        Permutation cs cs' ->
        plurality cs = plurality cs'.
Proof.
    intros cs cs' Hperm; induction Hperm; auto.
    -
    simpl; rewrite IHHperm; auto.
    replace (count l' x) with (count l x); auto.
    apply permutation_count; auto.
    -
    compare x y; intros Hxy.
    replace x with y; auto.

    destruct (plurality (y :: x :: l)) as (v,c) eqn:Hpxy.
    destruct v as [ v | ].
    apply plurality_some_count in Hpxy as Hpsc.






    compare x y; intros Hxy.
    replace x with y; auto.


    simpl.
    destruct (plurality l) eqn:Hp1.
    destruct o eqn:Hp2.
    destruct (Compare_dec.lt_eq_lt_dec n (S (count l x))) as [ [Hx|Hx] | Hx];
    destruct (Compare_dec.lt_eq_lt_dec n (S (count l y))) as [ [Hy|Hy] | Hy].
    replace (n =? S (count l x)) with false.
    replace (n <? S (count l x)) with true.
    replace (n =? S (count l y)) with false.
    replace (n <? S (count l y)) with true.
    compare x y; intros xy.
    replace x with y in *.
    replace (x =? y) with true. replace (y =? x) with true.
    compare (S (count l x)) (S (S (count l y))); intros Hsxy.
    replace (S (count l x) =? S (S (count l y))) with true.
    replace (S (count l y) =? S (S (count l x))) with false.




induction cs as [ | c cs ]; intros cs' Hperm.
    apply Permutation_nil in Hperm; rewrite Hperm; auto.
    destruct cs' as [ | c' cs'].
    {
        symmetry in Hperm.
        apply Permutation_nil in Hperm; discriminate.
    }
    simpl.

Qed.


Lemma isplurality_unique_perm :
    forall cs cs',
        Permutation cs cs' ->
        forall p p',
        IsPlurality p cs ->
        IsPlurality p' cs' ->
        p = p'.
Proof.
    intros.
    apply isplurality_is_plurality in H0.
    apply isplurality_is_plurality in H1.
    rewrite (plurality_unique_perm _ _ H) in H0.
    rewrite H0 in H1; injection H1; auto.
Qed.


Theorem classify_correct : 
    forall dist_metric,
      dist_metric_wf dist_metric ->
    forall K k data labels query c,
    0 < K -> 0 < k ->
    length data >= K ->
    (forall v' : datapt, List.In v' data -> length v' = k) ->  (* all data of dimension k *)
    (forall d : datapt, List.In d data -> FMap.In d labels) -> (* every datapt has a label *)
    classify dist_metric K k data labels query = Some c <->
    exists near far classes,
        Permutation data (near ++ far) /\
        length near = K /\                       (* `near`s are the K nearest neighbors *)
        all_in_leb (dist_metric query) near far /\
        ClassesOf labels near classes /\
        IsPlurality c classes. (* c is the plurality of all the `near` labels c*)
Proof.
    intros dist_metric Hdmwf K k data labels query c HK Hk Hdata Hdim Hlab.
    split.
    intros Hclassify; eapply classify_correct_some; eauto.
    intros Hex.
    destruct (classify dist_metric K k data labels query) eqn:Heqc.
    {
        destruct Hex as (near, (far, (classes, (H1, (H2, (H3, (H4, H5))))))).
        apply classify_correct_some in Heqc; auto.
        destruct Heqc as (near', (far', (classes', (H1', (H2', (H3', (H4', H5'))))))).
        assert (Permutation near near').
        {
            eapply permutation_all_in_leb; eauto.
            rewrite <- H2 in H2'; auto.
        }
        assert (Permutation classes classes').
        eapply classesof_permutation; eauto.
        replace c with n; auto.
        symmetry; eapply isplurality_unique_perm; eauto.
    }

    {
        destruct Hex as (near, (far, (classes, (H1, (H2, (H3, (H4, H5))))))).
        absurd (exists c, IsPlurality c classes); eauto.
        eapply classify_correct_none with (K := K); eauto.
    }
Qed.



