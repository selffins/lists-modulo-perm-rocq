(** *  Lists
    Coq version of [abella-reasoning/lib/list.thm]
 *)

(** ** Contains:
    - [append_rel]
    - [rev_rel]
    - [can_append]
    - [can_rev]

    In the abella style, [append] and [rev] are relational, so we have relational [append] and [rev] as well in Coq.
 **)

From Coq Require Export Sets.Multiset.
From Coq Require Export List.
From Coq Require Import Arith.EqNat.
Export ListNotations.

Module Type Eqset_dec.
  Parameter Eqset_T : Type.
  Parameter eqA_dec : forall x y : Eqset_T, {x = y} + {x <> y}.
End Eqset_dec.

Module Type OList (ELT : Eqset_dec).

  (** ** Elements *)
  Import ELT.
  Definition o := Eqset_T.

  (** ** Append *)

  Inductive append_rel : list o -> list o -> list o -> Prop :=
  | append_nil (L : list o): append_rel [] L L
  | append_cons e J K L (H : append_rel J K L): append_rel (e :: J) K (e :: L).

  (** *** Examples *)

  Example append_rel_12_34_1234 :
    forall (o1 o2 o3 o4 : o),
    append_rel ([o1 ; o2]) ([o3 ; o4]) ([o1 ; o2 ; o3 ; o4]).
  Proof.
    intros.
    apply append_cons.
    apply append_cons.
    apply append_nil.
  Qed.

  Example append_rel_12_nil_12 :
    forall o1 o2,
    append_rel ([o1; o2]) ([]) ([o1; o2]).
  Proof.
    intros.
    apply append_cons.
    apply append_cons.
    apply append_nil.
  Qed.

  Example append_rel_12_nil_13_fail :
    forall o1 o2 o3,
      o2 <> o3 ->
    not (append_rel ([o1 ; o2]) [] ([o1 ; o3])).
  Proof.
    intros.
    unfold not.
    intros.
    inversion H0;subst.
    inversion H4.
    contradiction.
  Qed.

  (** *** Equivalence to Rocq's [append] *)

  Theorem append_append_rel :
    forall J K, append_rel J K (J ++ K).
  Proof.
    intros.
    induction J as [ | j ].
    - simpl. apply append_nil.
    - simpl. apply append_cons. apply IHJ.
  Qed.

  Theorem append_append_rel_inv :
    forall J K L, J ++ K = L -> append_rel J K L.
  Proof.
    intros;subst. apply append_append_rel.
  Qed.

  Theorem append_rel_append :
    forall J K L, append_rel J K L -> J ++ K = L.
  Proof.
    intros.
    induction H.
    - reflexivity.
    - simpl. f_equal. apply IHappend_rel.
  Qed.

  Theorem append_rel_singleton :
    forall L a, append_rel [a] L (a :: L).
  Proof.
    intros.
    apply append_cons.
    apply append_nil.
  Qed.

  (** ** Reversing a list *)

  Inductive rev_rel : list o -> list o -> Prop :=
  | rev_nil : rev_rel [] []
  | rev_cons e J L (H : exists K, rev_rel J K /\ append_rel K (e :: []) L ) : rev_rel (e :: J) L.

  Example rev_123_321 :
    forall o1 o2 o3,
    rev_rel [o1 ; o2 ; o3] [o3 ; o2 ; o1].
  Proof.
    intros.
    eapply rev_cons.
    exists [o3 ; o2].
    split.
    - eapply rev_cons.
      exists [o3].
      split.
      -- eapply rev_cons. exists []. split.
         --- apply rev_nil.
         --- apply append_nil.
      -- apply append_cons. apply append_nil.
    - apply append_cons. apply append_cons. apply append_nil.
  Qed.

  Theorem can_append_rel : forall J K, exists L, append_rel J K L.
  Proof.
    intros.
    induction J as [ | j ].
    - exists K. apply append_nil.
    - destruct IHJ as [M].
      exists (j :: M).
      apply append_cons.
      apply H.
  Qed.

  Theorem can_rev_rel : forall J, exists K, rev_rel J K.
  Proof.
    intros.
    induction J as [ | A L ].
    - exists []. apply rev_nil.
    - destruct IHL as [K].
      assert (H1 : exists L1, append_rel K [A] L1).
      {
        exists (K ++ [A]). apply append_append_rel.
      }
      destruct H1 as [L1].
      exists L1.
      apply rev_cons.
      exists K.
      split.
      -- apply H.
      -- apply H0.
  Qed.

  Theorem rev_singleton: forall a,
      rev_rel [a] [a].
  Proof.
    intros.
    apply rev_cons.
    exists []. split.
    - apply rev_nil.
    - apply append_nil.
  Qed.

  Theorem rev_cons_singleton : forall J K a,
      rev_rel J K -> rev_rel (J ++ [a]) (a :: K).
  Proof.
    intros.
    generalize dependent a. generalize dependent K.
    induction J.
    - intros. inversion H;subst. simpl. apply rev_singleton.
    - intros. inversion H;subst. destruct H3. destruct H0.
      simpl. apply rev_cons. exists (a0 :: x).
      split.
      -- apply IHJ. apply H0.
      -- apply append_cons. apply H1.
  Qed.

  Theorem rev_nil_inv : forall J,
      J = [] -> rev_rel J [].
  Proof.
    intros;subst. apply rev_nil.
  Qed.

  Theorem rev_symm : forall J K,
      rev_rel J K -> rev_rel K J.
  Proof.
    intros.
    generalize dependent K.
    induction J;intros.
    - inversion H;subst. apply rev_nil.
    - inversion H;subst. destruct H3. destruct H0.
      apply append_rel_append in H1;subst.
      apply rev_cons_singleton. apply IHJ. apply H0.
  Qed.

(** * Permutations
    -   Coq version of [abella-reasoning/lib/perm.thm]
 *)

Section Perm.

  (** ** Contains:
      [*] denotes my addition.

    - adj
    1. adj_exists
    2. *adj_cons_comm_1
    3. *adj_cons_comm_2
    4. adj_swap
    5. adj_same
    6. adj_append_1 / adj_1_append

    - perm
    7. perm_refl
    8. perm_sym
    9. perm_cons_1
    10. perm_cons_2
    11. adj_preserves_perm
    12. perm_trans_lem
    13. perm_trans
    14. adj_same_source
    15. adj_same_result
    16. adj_same_result_diff
    17. adj_same_result_diff_both
    18. perm_invert
    19. adj_perm_source
    20. adj_nil_1
    21. perm_nil_1
    22. adj_det
    23. perm_singleton

    - append and perm
    24. append_perm
    25. adj_perm
    26. adj_perm_full

    - set theoretic semantics of adj and perm
    27. adj_member
    28. member_adj
    29. member_adj_rel
    30. adj_preserves_member_lem
    31, adj_preserves_member
    32. perm_preserves_member

   *)

  (** ** Adj *)

  Inductive adj : list o -> o -> list o -> Prop :=
  | adj_hd : forall L A, adj L A (A :: L)
  | adj_tl : forall B K A L, adj K A L -> adj (B :: K) A (B :: L).

  (** Constructor database *)
  Hint Constructors append_rel : my_db.
  Hint Constructors adj : my_db.

  (** *** Examples of adj *)

  Example adj_1_23_123 :
    forall o1 o2 o3,
    adj ([o2 ; o3]) o1 ([o1 ; o2 ; o3]).
  Proof.
    intros.
    eauto with my_db.
  Qed.

  Example adj_1_23_213 :
    forall o1 o2 o3,
    adj ([o2 ; o3]) o1 ([o2 ; o1 ; o3]).
  Proof.
    intros.
    apply adj_tl.
    apply adj_hd.
  Qed.

  Theorem adj_exists : forall A L, exists M, adj L A M.
  Proof.
    intros.
    (* eauto with my_db *)
    exists (A :: L).
    apply adj_hd.
  Qed.

  Theorem adj_tl_inv : forall B K A L, adj (B :: K) A (B :: L) -> adj K A L.
  Proof.
    intros.
    inversion H; subst. (*; eauto with my_db.*)
    - apply adj_hd.
    - apply H3.
  Qed.

  Theorem adj_swap : forall A J K B L, adj J A K -> adj K B L -> exists U, adj J B U /\ adj U A L.
  Proof.
    intros. generalize dependent J.
    induction H0;intros.
    - inversion H; subst. (*; eauto with my_db. *)
      -- exists (A0 :: J).
         split.
         --- apply adj_hd.
         --- apply adj_tl. apply H.
      -- exists (A0 :: B :: K).
         split.
         --- apply adj_hd.
         --- apply adj_tl. apply H.
    - inversion H; subst. (*; eauto with my_db.
      specialize (IHadj _ H4) as [U [IHa IHb]].
      eauto with my_db. *)
      -- exists L. split. apply H0. apply adj_hd.
      -- apply IHadj in H4. destruct H4 as [X [H4a H4b]].
         exists (B :: X).
         split.
         --- apply adj_tl. apply H4a.
         --- apply adj_tl. apply H4b.
  Qed.

  Theorem adj_same : forall A L B, adj L A (B :: L) -> A = B.
  Proof.
    intros. remember (B :: L) as F.
    induction H.
    - inversion HeqF. reflexivity.
    - apply IHadj. inversion HeqF. reflexivity.
  Qed.

  Theorem adj_append_1 : forall J A K L KL,
      adj J A K ->
      append_rel K L KL ->
      exists JL, append_rel J L JL /\ adj JL A KL.
  Proof.
    intros. generalize dependent L. revert KL.
    induction H; intros.
    - inversion H0; subst; eauto with my_db.
    - inversion H0; subst.
      apply IHadj in H5 as [X [IHa IHb]].
      info_eauto with my_db.
  Qed.


  Theorem adj_1_append : forall J A K L JL,
      adj J A K ->
      append_rel J L JL ->
      exists KL, append_rel K L KL /\ adj JL A KL.
  Proof.
    intros. generalize dependent L. generalize dependent JL.
    induction H; intros.
    (* adj_hd *)
    - inversion H0; subst.
      eauto with my_db.
      -- eauto with my_db.
    (* adj_tl  *)
    - inversion H0; subst.
      apply IHadj in H5 as [KL [IHa IHb]].
      eauto with my_db.
  Qed.

  (** ** Perm *)

  Inductive perm  : list o -> list o -> Prop :=
  | perm_nil : perm nil nil
  | perm_split : forall K L A KK LL, adj KK A K ->
                                     adj LL A L ->
                                     perm KK LL ->
                                     perm K L.

  Hint Constructors perm : my_db.

  (** *** Examples of [perm] *)

  Example perm_123_321 :
    forall o1 o2 o3, perm [o1 ; o2 ; o3] [o3 ; o2 ; o1].
  Proof.
    intros. eauto 9 with my_db.
  Qed.



  (** ** [Perm] theorems *)

  Theorem perm_sym : forall K L, perm K L -> perm L K.
  Proof.
    intros.
    induction H.
    - eauto with my_db.
    - info_eauto with my_db.
  Qed.

  Theorem perm_refl : forall L, perm L L.
  Proof.
    intros.
    induction L; eauto with my_db.
  Qed.

  Hint Immediate perm_refl : my_db.

  Theorem perm_cons_1 : forall A K L,
      perm (A :: K) L ->
      exists J, adj J A L /\ perm K J.
  Proof.
    intros.
    remember (A :: K) as X.
    revert HeqX.
    revert A.
    revert K.
    induction H.
    - intros.
      discriminate.
    - intros.
      subst.
      inversion H.
      -- subst. eauto.
      -- subst.
         assert (Heq : A0 :: K = A0 :: K) by reflexivity.
         specialize (IHperm _ _ Heq).
         destruct IHperm as [J [IHa IHb]].
         destruct Heq.
         pose proof (adj_swap _ _ _ _ _ IHa H0)  as [U [H6a H6b]].
         info_eauto with my_db.
  Qed.

  Theorem perm_cons_2 : forall A K L,
      perm K (A :: L) ->
      exists J, adj J A K /\ perm J L.
  Proof.
    intros.
    apply perm_sym in H.
    eapply perm_cons_1 in H.
    destruct H as [J' [H1 H2]].
    apply perm_sym in H2.
    eauto with my_db.
  Qed.

  Theorem adj_preserves_perm : forall A JJ J KK K,
      adj JJ A J ->
      adj KK A K ->
      perm JJ KK ->
      perm J K.
  Proof.
    intros.
    eauto with my_db.
  Qed.

  (* todo: clean *)
  Theorem perm_trans : forall J K L, perm J K -> perm K L -> perm J L.
  Proof.
    intros J K. generalize dependent J.
    induction K as [ | A L1 IH]; intros.
    (* K is nil *)
    - inversion H; subst.
      -- apply H0.
      -- inversion H3; subst.
         --- inversion H2.
         --- inversion H2.
    (* K is A :: L1 *)
    - inversion H; subst.
      rename A0 into A1.
      inversion H0; subst.
      rename A0 into A2.
      inversion H2; subst.
      rename KK0 into KK1.
      rename LL0 into LL1.
      inversion H4; subst.
      -- specialize (IH KK LL1 H3 H6).
         eapply perm_split.
         apply H1. apply H5. apply IH.
      -- apply perm_cons_1 in H6.
         destruct H6 as [J1 [H6a H6b]].
         apply adj_swap with (A := A) (J := J1) in H5.
         destruct H5 as [U [H5a H5b]].
         apply adj_preserves_perm with (A := A2) (J := L1) (K := U)  in H6b as H11.
         specialize (IH _ _ H3 H11).
         eapply adj_preserves_perm. apply H1. apply H5b. apply IH.
         apply H10. apply H5a. apply H6a.
      --  apply perm_cons_2 in H3. destruct H3 as [J1 [H3a H3b]].
          apply adj_swap with (A := A) (J := J1) in H1 as H11.
          destruct H11 as [U [H11a H11b]].
          apply adj_preserves_perm with (A := A1) (J := U) (K := L1) in H3b as H12.
          apply adj_preserves_perm with (A := A2) (J := A :: L1) (K := L) in H6 as H13.
          apply perm_cons_1 in H13.
          destruct H13 as [J2 [H13a H13b]].
          apply IH with (J := U) in H13b.
          eapply adj_preserves_perm.
          (* todo: clean *)
          apply H11b.
          apply H13a.
          apply H13b.
          apply H12.
          apply H4.
          apply H5.
          apply H11a.
          apply H10.
          apply H3a.
  Qed.

  Theorem adj_same_source : forall J A K L,
      adj J A K -> adj J A L ->
      perm K L.
  Proof.
    intros.
    inversion H; inversion H0; subst; info_eauto with my_db.
  Qed.

  Theorem adj_same_result : forall J K A L,
      adj J A L ->
      adj K A L ->
      perm J K.
  Proof.
    intros. generalize dependent K.
    induction H;intros.
    - inversion H0; subst; eauto with my_db.
    - inversion H0; subst; info_eauto with my_db.
  Qed.

  Theorem adj_same_result_diff : forall J A K B L,
      adj J A L ->
      adj K B L ->
      (A = B /\ perm J K) \/
        exists KK, adj KK A K.
  Proof.
    intros. generalize dependent K. generalize dependent B.
    induction H; intros.
    - inversion H0; subst; eauto with my_db.
    - inversion H0; subst.
      -- eauto with my_db.
      -- apply IHadj in H4 as [[H4a1 H4a2] | [X H4b1]]; subst.
         --- eauto with my_db.
         --- eauto with my_db.
  Qed.

  Theorem adj_same_result_diff_both : forall J A K B L,
      adj J A L ->
      adj K B L ->
      (A = B /\ perm J K) \/
        exists JJ KK, adj JJ B J /\ adj KK A K /\ perm JJ KK.
  Proof.
    intros. generalize dependent K.
    induction H; intros.
    - inversion H0; subst.
      -- eauto with my_db.
      -- eauto 6 with my_db.
    - inversion H0;subst.
      -- eauto 6 with my_db.
      -- apply IHadj in H4 as [[IHa1 IHa2] | [X [Y [IHb1 [IHb2 IHb3]]]]].
         --- inversion IHa2; subst; eauto 6 with my_db.
         --- eauto 9 with my_db.
  Qed.

  Theorem perm_invert : forall A J K JJ KK,
      perm J K ->
      adj JJ A J ->
      adj KK A K ->
      perm JJ KK.
  Proof.
    intros A J K JJ KK H.
    generalize dependent A. generalize dependent JJ. generalize dependent KK.
    induction H.
    - intros. inversion H.
    - intros.
      pose proof (adj_same_result_diff _ _ _ _ _ H2 H).
      destruct H4 as [[H4 H4b] | H4].
      -- subst.
         pose proof (adj_same_result _ _ _ _ H3 H0).
         apply perm_sym in H4.
         eapply perm_trans. apply H4b. eapply perm_trans. apply H1. apply H4.
      -- destruct H4 as [KK2 H4].
         pose proof (adj_same_result_diff _ _ _ _ _ H3 H0).
         destruct H5 as [[H5 H5a] | [KK3 H5]].
         --- subst.
             apply perm_sym in H5a.
             pose proof (perm_trans _ _ _ H1 H5a).
             pose proof (adj_same_result _ _ _ _ H2 H).
             eapply perm_trans; eauto.
         ---
             specialize (IHperm _ _ _ H4 H5).
             pose proof (adj_swap _ _ _ _ _ H5 H0) as [U [H6 H6b]].
             pose proof (adj_swap _ _ _ _ _ H4 H) as [U1 [H7 H7b]].
             pose proof (adj_same_result _ _ _ _ H2 H7b).
             pose proof (adj_same_result _ _ _ _ H6b H3).
             pose proof (adj_preserves_perm _ _ _ _ _ H7 H6 IHperm).
             pose proof (perm_trans _ _ _ H8 H10).
             eapply perm_trans; eauto.
  Qed.

  Theorem adj_perm_result : forall J K A JJ,
      perm J K ->
      adj JJ A J ->
      (exists KK, adj KK A K /\ perm JJ KK).
  Proof.
    intros J K A JJ H.
    revert A. revert JJ.
    induction H.
    - (* perm_nil *)
      intros.
      inversion H.
    - (* perm_split *)
      intros.
      pose proof (adj_same_result_diff _ _ _ _ _ H2 H) as [[H3a H3b] | [KK1 H3alt]].
      -- subst.
         pose proof (perm_trans _ _ _ H3b H1).
         eauto.
      -- specialize (IHperm _ _ H3alt) as [KK2 [IHa IHb]].
         pose proof (adj_swap _ _ _ _ _ H3alt H) as [U [H3 H3b]].
         pose proof (adj_swap _ _ _ _ _ IHa H0) as [U1 [H4 H4b]].
         exists U1. split. auto.
         pose proof (adj_same_result _ _ _ _ H2 H3b).
         pose proof (adj_preserves_perm _ _ _ _ _ H3 H4 IHb).
         apply (perm_trans _ _ _ H5 H6); info_eauto.
  Qed.

  Theorem adj_perm_source : forall J K A L,
      perm J K ->
      adj J A L ->
      exists LL, adj K A LL /\ perm L LL.
  Proof.
    intros.
    eauto with my_db.
  Qed.

  Theorem adj_nil_1 : forall A L,
      adj nil A L -> L = A :: nil.
  Proof.
    intros. inversion H; subst. reflexivity.
  Qed.

  Theorem perm_nil_1 : forall L,
      perm nil L -> L = nil.
  Proof.
    intros.
    inversion H; subst.
    - reflexivity.
    - inversion H0.
  Qed.

  Theorem adj_det : forall A B L,
      adj L A (B :: nil) -> A = B /\ L = nil.
  Proof.
    intros.
    inversion H;subst;split.
    - reflexivity.
    - reflexivity.
    - inversion H3.
    - inversion H3.
  Qed.

  Theorem perm_singleton : forall A L,
      perm (A :: nil) L -> L = (A :: nil).
  Proof.
    intros.
    inversion H;subst.
    apply adj_det in H0 as [H0a H0b]. subst.
    apply perm_nil_1 in H2. subst.
    apply adj_nil_1 in H1.
    apply H1.
  Qed.

  (** ** [append] and [perm] theorems *)

  Theorem append_perm : forall J K L JJ KK,
      append_rel J K L ->
      perm J JJ ->
      perm K KK ->
      exists LL, append_rel JJ KK LL /\ perm L LL.
  Proof.
    intros. generalize dependent JJ. generalize dependent KK.
    induction H;intros.
    - (* append_nil *)
      inversion H0;subst.
      -- eauto with my_db.
      -- inversion H.
    - (* append_cons *)
      apply perm_cons_1 in H0 as [J2 [H0a H0b]].
      specialize (IHappend_rel _ H1 _ H0b) as [LL [H2 H2b]].
      pose proof (adj_1_append _ _ _ _ _ H0a H2) as [KL [H0aa H0ab]].
      eauto with my_db.
  Qed.

  Theorem adj_perm : forall J K JJ A,
      perm J K ->
      adj JJ A J ->
      exists KK, adj KK A K.
  Proof.
    intros. generalize dependent K.
    induction H0;intros.
    - apply perm_cons_1 in H as [X [Ha Hb]]. exists X. apply Ha.
    - apply perm_cons_1 in H as [X [Ha Hb]].
      apply IHadj in Hb as [KK'].
      pose proof (adj_swap _ _ _ _ _ H Ha) as [U [Ha1 Ha2]].
      exists U. apply Ha2.
  Qed.

  Theorem adj_perm_full : forall J K JJ A,
      perm J K ->
      adj JJ A J ->
      exists KK, adj KK A K /\ perm JJ KK.
  Proof.
    intros. generalize dependent K.
    induction H0; intros.
    - apply perm_cons_1 in H as [X [Ha Hb]]. eauto with my_db.
    - apply perm_cons_1 in H as [X [Ha Hb]].
      apply IHadj in Hb as [KK' [IHadj1 IHadj2]].
      pose proof (adj_swap _ _ _ _ _ IHadj1 Ha) as [U [Ha1 Ha2]].
      eauto with my_db.
  Qed.

  (** ** Set-theoretic semantics of [adj] *)

  (** This section connects the adj relation with the set membership relation,
      which is intuitive - [adj L A K] says [K] is [L] with [A] inserted "somewhere"
      (i.e. set membership).

     We could use [In] (from [Stdlib.Lists]) as our set membership relation, but we will instead use the [member] relation defined in the Abella standard library, which is what they used in their implementation.

     Here is how it's defined:
<<
     Type   nil     olist.
     Type   ::      o -> olist -> olist.

     Define member : o -> olist -> prop by
     member A (A :: L);
     member A (B :: L) := member A L.
>>

   *)

  Inductive member : o -> list o -> Prop :=
  | member_hd  : forall A L, member A (A :: L)
  | member_tl  : forall A B L, member A L -> member A (B :: L).

  Hint Constructors member : my_db.

  Theorem adj_member : forall J A L,
      adj J A L -> member A L.
  Proof.
    intros.
    induction H; eauto with my_db.
  Qed.

  Theorem member_adj : forall A L,
      member A L -> exists J, adj J A L.
  Proof.
    intros.
    induction H.
    - eauto with my_db.
    - destruct IHmember as [X].
      inversion H; subst; eauto with my_db.
  Qed.

  Theorem member_adj_rel : forall JJ A J B,
      adj JJ A J -> member B J ->
      A = B \/ member B JJ.
  Proof.
    intros. generalize dependent B.
    induction H;intros.
    - inversion H0; subst; auto.
    - specialize (IHadj B0).
      inversion H0; subst.
      -- right. apply member_hd.
      -- apply IHadj in H3 as [H3a | H3b]; subst.
         --- auto.
         --- eauto with my_db.
  Qed.

  Theorem adj_preserves_member_lem : forall A J B L,
      member A J -> adj J B L -> member A L.
  Proof.
    intros. generalize dependent B. generalize dependent L.
    induction H; intros; inversion H0; subst; eauto with my_db.
  Qed.

  Theorem adj_preserves_member : forall A J B L,
      member A J -> adj J B L -> member A L.
  Proof.
    intros.
    apply (adj_preserves_member_lem _ _ _ _ H H0).
  Qed.

  Theorem perm_preserves_member : forall A K L,
      perm K L ->
      member A K -> member A L.
  Proof.
    intros. generalize dependent L.
    induction H0; intros; eapply perm_cons_1 in H as [X [Ha Hb]].
    - eapply adj_member.
      apply Ha.
    - apply IHmember in Hb.
      eapply adj_preserves_member.
      apply Hb.
      apply Ha.
  Qed.

End Perm.


(** * Merge
    - Coq version of [abella-reasoning/lib/merge.thm]
 *)

(** ** Contains:

    1. merge
    2. perm_merge_1
    3. perm_merge_2
    4. perm_merge_3
    5. merge_sym
    6. merge_nil_perm
    7. merge_adj_1
    8. merge_unadj_1
    9. merge_adj_2
    10. merge_unadj_2
    11. merge_unadj_3
    12. merge_invert_1
    13. merge_invert_2
    14. merge_move_12
    15. merge_move_21
    16. add_to_merge_right
    17. add_to_merge_left
    18. merge_nil_equal
    19. merge_exists
    20. merge_head_lemma
    21. adj_implies_merge
    22. merge_assoc
    23. change_merge_order
    24. change_merge_order2
    25. merge_perm_det
    26. merge_preserves_perm_lem
    27. merge_preserves_perm
    28. merge_sub
    29. merge_to_adj
    30. merge_same_result_diff

 *)

Section Merge.

  (** ** Definition
      merge J K L : J union K equals L.
  *)

  Inductive merge : list o -> list o -> list o -> Prop :=
  | merge_nil : merge nil nil nil
  | merge_l : forall J K L A JJ LL, adj JJ A J -> adj LL A L -> merge JJ K LL ->  merge J K L
  | merge_r : forall J K L A KK LL, adj KK A K -> adj LL A L -> merge J KK LL -> merge J K L.

  Hint Constructors adj : my_db.
  Hint Constructors perm : my_db.
  Hint Constructors merge : my_db.

  Theorem perm_merge_1 : forall J K L JJ,
      merge J K L ->
      perm J JJ ->
      merge JJ K L.
  Proof.
    intros. generalize dependent JJ.
    induction H;intros.
    - apply perm_nil_1 in H0. subst. apply merge_nil.
    - pose proof  (adj_perm _ _ _ _ H2 H) as [X H3].
      pose proof (perm_invert _ _ _ _ _ H2 H H3).
      -- eapply IHmerge in H4.
         eauto with my_db.
    - apply IHmerge in H2.
      eauto with my_db.
  Qed.

  Theorem perm_merge_2 : forall J K L KK,
      merge J K L ->
      perm K KK ->
      merge J KK L.
  Proof.
    intros. generalize dependent KK.
    induction H;intros.
    - apply perm_nil_1 in H0. subst. apply merge_nil.
    - apply IHmerge in H2.
      eauto with my_db.
    - pose proof (adj_perm _ _ _ _ H2 H) as [KK2 H3].
      pose proof (perm_invert _ _ _ _ _ H2 H H3).
      apply IHmerge in H4.
      eauto with my_db.
  Qed.

  Theorem perm_merge_3 : forall J K L LL,
      merge J K L ->
      perm L LL ->
      merge J K LL.
  Proof.
    intros. generalize dependent LL.
    induction H;intros.
    - apply perm_nil_1 in H0. subst. apply merge_nil.
    - pose proof (adj_perm_result _ _ _ _ H2 H0) as [KK [H3 H4]].
      specialize (IHmerge _ H4).
      eauto with my_db.
    - pose proof (adj_perm_result _ _ _ _ H2 H0) as [KK' [H3 H4]].
      specialize (IHmerge _ H4).
      eauto with my_db.
  Qed.

  Theorem merge_sym : forall J K L,
      merge J K L ->
      merge K J L.
  Proof.
    intros.
    induction H; eauto with my_db.
  Qed.

  Theorem merge_nil_perm : forall K L,
      merge nil K L -> perm K L.
  Proof.
    intros. remember nil.
    induction H.
    - apply perm_nil.
    - subst.
      inversion H.
    - apply IHmerge in Heql as IH.
      eauto with my_db.
  Qed.

  (** *** Theorems about [merge] and [adj] *)

  Theorem merge_adj_1 : forall A JJ J K LL,
      merge JJ K LL -> adj JJ A J -> exists L, adj LL A L /\ merge J K L.
  Proof.
    intros.
    eauto with my_db.
  Qed.

  Theorem merge_unadj_1 : forall J K L JJ A,
      merge J K L -> adj JJ A J -> exists LL, adj LL A L /\ merge JJ K LL.
  Proof.
    intros.
    generalize dependent JJ. generalize dependent A.
    induction H.
    - intros. inversion H0.
    - intros.
      pose proof (adj_same_result_diff _ _ _ _ _ H2 H).
      destruct H3 as [[H3eq H3] | [KK H3]].
      subst.
      -- apply perm_sym in H3. pose proof (perm_merge_1 _ _ _ _ H1 H3).
         eauto.
      -- specialize (IHmerge _ _ H3). destruct IHmerge as [LL0 [IHa IHb]].
         pose proof (adj_swap _ _ _ _ _ IHa H0).
         pose proof (adj_swap _ _ _ _ _ H3 H). destruct H4 as [U [H4 H4b]]. destruct H5 as [U1 [H5 H5b]].
         pose proof (adj_same_result _ _ _ _ H5b H2).
         eapply perm_merge_1 in H6 as H7.
         eauto with my_db.
         eauto with my_db. (* for perm_merge_1 *)
    - intros.
      specialize (IHmerge _ _ H2) as [LL0 [IHa IHb]].
      pose proof (adj_swap _ _ _ _ _ IHa H0) as [U [H3 H3a]].
      exists U. split; eauto. econstructor; solve [ eauto ].
  Qed.

  Theorem merge_adj_2 : forall A J KK K LL,
      merge J KK LL -> adj KK A K -> exists L, adj LL A L /\ merge J K L.
  Proof.
    intros.
    eauto with my_db.
  Qed.

  Theorem merge_unadj_2 : forall J K L KK A,
      merge J K L -> adj KK A K -> exists LL, adj LL A L /\ merge J KK LL.
  Proof.
    intros.
    apply merge_sym in H.
    pose proof (merge_unadj_1 _ _ _ _ _ H H0) as [LL [H0a H0b]].
    apply merge_sym in H0b.
    eauto with my_db.
  Qed.

  Theorem merge_unadj_3 : forall J K L LL A,
      merge J K L -> adj LL A L ->
      (exists JJ, adj JJ A J /\ merge JJ K LL)
      \/ (exists KK, adj KK A K /\ merge J KK LL).
  Proof.
    intros.
    generalize dependent H0.
    revert LL.
    revert A.
    induction H.
    - (* merge_nil *)
      intros.
      inversion H0.
    - (* merge_l *)
      intros.
      pose proof (adj_same_result_diff _ _ _ _ _ H0 H2) as [[H3a H3b] | [KK H3alt]].
      -- subst.
         pose proof (perm_merge_3 _ _ _ _ H1 H3b).
         eauto.
      -- pose proof (adj_swap _ _ _ _ _ H3alt H2) as [U [H4a H4b]].
         pose proof (adj_same_result _ _ _ _ H4b H0).
         pose proof (adj_perm _ _ _ _ H3 H4a) as [KK1 H5].
         specialize (IHmerge _ _ H5).
         destruct IHmerge as [IHmerge1 | IHmerge2].
         --- destruct IHmerge1 as [JJ0 [IHmerge1a IHmerge1b]].
             pose proof (adj_swap _ _ _ _ _ IHmerge1a H) as [U1 [H6a H6b]].
             left.
             exists U1.
             split. auto.
             pose proof (adj_swap _ _ _ _ _ H5 H0) as [U2 [H7a H7b]].
             pose proof (adj_same_result _ _ _ _ H7b H2).
             eapply perm_merge_3; eauto with my_db.
         --- destruct IHmerge2 as [JJ0 [IHmerge2a IHmerge2b]].
             pose proof (adj_swap _ _ _ _ _ H5 H0) as [U1 [H6a H6b]].
             pose proof (adj_same_result _ _ _ _ H6b H2).
             epose proof (perm_merge_3 J JJ0 _ _ _ H4).
             eauto with my_db.
    - (* merge_r *)
      intros.
      pose proof (adj_same_result_diff _ _ _ _ _ H2 H0) as [[H3a H3b] | [KK0 H3alt]].
      -- subst. apply perm_sym in H3b.
         pose proof (perm_merge_3 _ _ _ _ H1 H3b).
         eauto.
      -- pose proof (adj_swap _ _ _ _ _ H3alt H0) as [U [H3 H3b]].
         pose proof (adj_same_result _ _ _ _ H3b H2).
         pose proof (adj_perm _ _ _ _ H4 H3) as [KK2 H5].
         specialize (IHmerge _ _ H3alt) as [IHmerge | IHmergealt].
         --- destruct IHmerge as [JJ [IHa IHb]].
             pose proof (adj_swap _ _ _ _ _ H5 H2) as [U1 [H6a H6b]].
             pose proof (adj_same_result _ _ _ _ H6b H0).
             left.
             exists JJ.
             split. apply IHa.
             epose proof (perm_merge_3 JJ K _ LL0 _ H4).
             apply H7.
         --- destruct IHmergealt as [KK3 [IHa IHb]].
             pose proof (adj_swap _ _ _ _ _ IHa H) as [U1 [H6 H6b]].
             right. exists U1. split.
             apply H6b.
             eapply perm_merge_3; try eauto with my_db.
             Unshelve.
             eauto with my_db.
             eauto with my_db.
  Qed.

  (** *** Consequences of merge and adj *)
  Theorem merge_invert_1 : forall A JJ J K LL L,
      merge J K L ->
      adj JJ A J ->
      adj LL A L ->
      merge JJ K LL.
  Proof.
    intros.
    pose proof (merge_unadj_1 _ _ _ _ _ H H0) as [LL1 [H2a H2b]].
    pose proof (adj_same_result _ _ _ _ H2a H1).
    apply (perm_merge_3 _ _ _ _ H2b H2).
  Qed.

  Theorem merge_invert_2 : forall A J KK K LL L,
      merge J K L ->
      adj KK A K ->
      adj LL A L ->
      merge J KK LL.
  Proof.
    intros.
    apply merge_sym in H.
    apply merge_sym.
    apply (merge_invert_1 _ _ _ _ _ _ H H0 H1).
  Qed.

  Theorem merge_move_12 : forall A JJ J KK K L,
      adj JJ A J ->
      adj KK A K ->
      merge J KK L ->
      merge JJ K L.
  Proof.
    intros.
    pose proof (merge_unadj_1 _ _ _ _ _ H1 H) as [LL [H1a H1b]].
    eauto with my_db.
  Qed.

  Theorem merge_move_21 : forall A JJ J KK K L,
      adj JJ A J ->
      adj KK A K ->
      merge JJ K L ->
      merge J KK L.
  Proof.
    intros.
    pose proof (merge_unadj_2 _ _ _ _ _ H1 H0) as [LL [H1a H1b]].
    eauto with my_db.
  Qed.

  (** ** [add_to_merge] *)

  Theorem add_to_merge_right : forall A J K KK L,
      adj KK A K ->
      merge J KK L ->
      exists M, merge J K M /\ adj L A M.
  Proof.
    eauto with my_db.
  Qed.

  Theorem add_to_merge_left : forall A J JJ K L,
      adj JJ A J ->
      merge JJ K L ->
      exists M, merge J K M /\ adj L A M.
  Proof.
    eauto with my_db.
  Qed.

  Theorem merge_nil_equal : forall L,
      merge nil L L.
  Proof.
    intros.
    induction L; eauto with my_db.
  Qed.

  Theorem merge_exists : forall J K,
    exists L, merge J K L.
  Proof.
    intros.
    induction J.
    - exists K. apply merge_nil_equal.
    - destruct IHJ as [X]. eauto with my_db.
  Qed.

  Theorem merge_head_lemma : forall L A,
      merge L (A :: nil) (A :: L).
  Proof.
    intros.
    induction L as [| Y L'].
    - apply merge_nil_equal.
    - assert (adj L' A (A :: L')) by apply adj_hd.
      pose proof (add_to_merge_left _ _ _ _ _ H IHL') as [M [IHa IHb]].
      eapply merge_r.
      -- apply adj_hd.
      -- apply adj_hd.
      -- apply merge_sym. apply merge_nil_equal.
  Qed.

  (** Note: the contrary is not true, since adj is order-sensitive *)
  Theorem adj_implies_merge : forall L J A,
      adj L A J -> merge L (A :: nil) J.
  Proof.
    intros.
    induction H.
    - apply merge_head_lemma.
    - eauto with my_db.
  Qed.

  (** *** Associativity of [merge] *)
  Theorem merge_assoc : forall J K L JK KL JKL1 JKL2,
      merge J K JK -> merge K L KL ->
      merge J KL JKL1 -> merge JK L JKL2 ->
      perm JKL1 JKL2.
  Proof.
    intros J K L JK KL JKL1 JKL2 H1.
    revert L. revert KL. revert JKL1. revert JKL2.
    induction H1; intros.
    - (* merge_nil *)
      apply merge_nil_perm in H.
      apply merge_nil_perm in H0.
      apply merge_nil_perm in H1.
      eapply perm_trans. apply perm_sym. eapply perm_trans.
      apply H. apply H0. apply H1.
    - (* merge_left *)
      pose proof (merge_unadj_1 _ _ _ _ _ H3 H) as [X [H5a H5b]].
      pose proof (merge_unadj_1 _ _ _ _ _ H4 H0) as [Y [H6a H6b]].
      (* econstructor; solve [ eauto ]. *)
      eapply perm_split.
      apply H5a.
      apply H6a.
      apply (IHmerge _ _ _ _ H2 H5b H6b).
    - (* merge_right *)
      pose proof (merge_unadj_1 _ _ _ _ _ H2 H) as [X [H5a H5b]].
      pose proof (merge_unadj_1 _ _ _ _ _ H4 H0) as [Y [H6a H6b]].
      pose proof (merge_unadj_2 _ _ _ _ _ H3 H5a) as [Z [H7a H7b]].
      (* econstructor; solve [ eauto ] *)
      eapply perm_split.
      apply H7a.
      apply H6a.
      apply (IHmerge _ _ _ _ H5b H7b H6b).
  Qed.

  Theorem change_merge_order : forall J K L JK KL JKL,
      merge JK L JKL -> merge J K JK -> merge K L KL ->
      merge J KL JKL.
  Proof.
    intros.
    pose proof (merge_exists J KL) as [L1 H2].
    pose proof (merge_assoc _ _ _ _ _ _ _ H0 H1 H2 H).
    apply (perm_merge_3 _ _ _ _ H2 H3).
  Qed.

  Theorem change_merge_order2 : forall J K JK L KL JKL,
      merge J K JK -> merge K L KL -> merge J KL JKL ->
      merge JK L JKL.
  Proof.
    intros.
    pose proof (merge_exists JK L) as [L1 H2].
    pose proof (merge_assoc _ _ _ _ _ _ _ H H0 H1 H2).
    apply perm_sym in H3.
    apply (perm_merge_3 _ _ _ _ H2 H3).
  Qed.

  Theorem merge_perm_det : forall J K L1 L2,
      merge J K L1 ->
      merge J K L2 ->
      perm L1 L2.
  Proof.
    intros J K L1 L2 H1.
    generalize dependent L2.
    induction H1; intros.
    - (* merge_nil *)
      apply merge_nil_perm. apply H.
    - (* merge_left *)
      pose proof (merge_unadj_1 _ _ _ _ _ H2 H) as [X [H3a H3b]].
      specialize (IHmerge _ H3b).
      eauto with my_db.
    - (* merge_right *)
      pose proof (merge_unadj_2 _ _ _ _ _ H2 H) as [X [H3a H3b]].
      specialize (IHmerge _ H3b).
      eauto with my_db.
  Qed.

  Theorem merge_preserves_perm : forall L LL J K,
      merge L J K ->
      merge LL J K ->
      perm L LL.
  Proof.
    intros L LL J. generalize dependent L. generalize dependent LL.
    induction J; intros.
    - (* J = [] *)
      apply merge_sym in H. apply merge_nil_perm in H.
      apply merge_sym in H0. apply merge_nil_perm in H0.
      eapply perm_trans. apply H. apply perm_sym. apply H0.
    - (* J = [a :: J] *)
      assert (adj J a (a :: J)). apply adj_hd.
      pose proof (merge_unadj_2 _ _ _ _ _ H H1) as [X [H2a H2b]].
      pose proof (merge_unadj_2 _ _ _ _ _ H0 H1) as [Y [H3a H3b]].
      pose proof (adj_same_result _ _ _ _ H2a H3a).
      pose proof (perm_merge_3 _ _ _ _ H2b H2).
      apply (IHJ _ _ _ H3 H3b).
  Qed.

  (** Apparently needs a better name *)
  Theorem merge_sub : forall J K L JK JL JKL,
      merge J K JK ->
      merge JK L JKL ->
      merge JL K JKL ->
      merge J L JL.
  Proof.
    intros.
    pose proof (merge_exists J L) as [L1 H2].
    pose proof (merge_exists K L1) as [L2 H3].
    apply merge_sym in H.
    pose proof (merge_assoc _ _ _ _ _ _ _ H H2 H3 H0).
    apply merge_sym in H3.
    pose proof (perm_merge_3 _ _ _ _ H3 H4).
    pose proof (merge_preserves_perm _ _ _ _ H5 H1).
    apply (perm_merge_3 _ _ _ _ H2 H6).
  Qed.

  Theorem merge_to_adj : forall J L A,
      merge J (A :: nil) L ->
      exists JJ, perm J JJ /\ adj JJ A L.
  Proof.
    intros.
    remember (A :: nil).
    induction H.
    - (* merge_nil*)
      discriminate.
    - (* merge_l *)
      specialize (IHmerge Heql).
      subst.
      destruct IHmerge as [JJ1 [IHa IHb]].
      pose proof (adj_swap _ _ _ _ _ IHb H0) as [U [H2a H2b]].
      eauto with my_db.
    - (* merge_r *)
      subst.
      apply adj_det in H as [Ha Hb].
      subst.
      apply merge_sym in H1.
      apply merge_nil_perm in H1.
      eauto with my_db.
  Qed.

  Theorem merge_same_result_diff : forall J A K B L,
      merge J (A :: nil) L ->
      merge K (B :: nil) L ->
      (A = B /\ perm J K) \/
        exists KK, merge KK (A :: nil) K.
  Proof.
    intros.
    apply merge_to_adj in H as [JJ [Ha Hb]].
    apply merge_to_adj in H0 as [KK [H1a H1b]].
    pose proof (adj_same_result_diff _ _ _ _ _ Hb H1b) as [[H2a H2b] | H2alt].
    subst.
    - left. split. reflexivity.
      pose proof (perm_trans _ _ _ Ha H2b).
      apply perm_sym in H1a.
      apply (perm_trans _ _ _ H H1a).
    - right.
      destruct H2alt as [X H2].
      apply adj_implies_merge in H2.
      apply perm_sym in H1a.
      exists X.
      apply (perm_merge_3 _ _ _ _ H2 H1a).
  Qed.

  (** *** Subsets via merge

  In abella,

<<
  Define subset : olist -> olist -> prop by
  subset J L := exists K, merge J K L.
>>

This doesn't seem to be a finished section in the original library.

  *)

  Inductive subset : list o -> list o -> Prop :=
  | subset_e : forall J L K, merge J K L -> subset J L.

End Merge.
End OList.
