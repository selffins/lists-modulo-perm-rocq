(** * Proof of concept: MLL using lists-modulo permutation *)
Require Import ListsModPerm.olist.

Module MLL_LMP.

  (** * Formulas *)
  Inductive formula : Set :=
  | bot
  | one
  | atom : nat -> formula
  | natom : nat -> formula
  | tens : formula -> formula -> formula
  | par : formula -> formula -> formula.

  Module ELT_DEC.
    Definition T := formula.
  End ELT_DEC.

  Declare Module LMPFormulas : OList(ELT_DEC).
  Export LMPFormulas.

  Fixpoint negation (A : formula) : formula :=
    match A with
    | bot => one
    | one => bot
    | atom v => natom v
    | natom v => atom v
    | tens A B => par (negation A) (negation B)
    | par A B => tens (negation A) (negation B)
    end.

  (** * Context representation *)
  Definition ctx := list formula.


  (** * Inference rules *)
  Inductive mll : ctx -> Prop :=
  | mll_id : forall L A, adj (natom A :: nil) (atom A) L -> mll L
  | mll_tens : forall L A B LL JJ KK J K,
      adj LL (tens A B) L ->
      merge JJ KK LL ->
      adj JJ A J -> mll J ->
      adj KK B K -> mll K -> mll L
  | mll_one : mll ([one])
  | mll_par : forall L A B LL J K,
      adj LL (par A B) L ->
      adj LL A J ->
      adj J B K ->
      mll K ->
      mll L
  | mll_bot : forall L LL,
      adj LL bot L -> mll LL -> mll L.

  Hint Constructors adj : my_db.
  Hint Constructors merge : my_db.
  Hint Constructors perm : my_db.
  Hint Immediate perm_refl : my_db.
  Hint Constructors mll : my_db.

  (** ** Example derivations *)

  (** Interesting things:
      - [mll_par] can be applied in many ways due to how [adj] works.
      If you apply [mll_par] using [eapply] (without specifying arguments), you actually end up reversing the list.
      But the hypothesis we have is in a different order (is sorted).
      So it's important to be explicit about how you want the resulting list order to be afterwards.
      (Well, that is, if you don't have the exchange theorem yet.)
      - eauto solves this easily! Power of adj.
   *)
  Example a1_par_a2_a3_par_a4_1 : forall A1 A2 A3 A4,
      mll [A1 ; A2 ; A3 ; A4] -> mll [par A1 A2; par A3 A4].
  Proof.
    intros.
    info_eauto 10 with my_db.
    Restart.
    intros.
    eapply mll_par with (K := [A1 ; A2 ; par A3 A4]).
    - apply adj_hd.
    - apply adj_hd.
    - apply adj_tl. apply adj_hd.
    - eapply mll_par with (J := [A1; A2; A3]) (K := [A1; A2; A3; A4]).
    -- apply adj_tl. apply adj_tl. apply adj_hd.
    -- apply adj_tl. apply adj_tl. apply adj_hd.
    -- apply adj_tl. apply adj_tl. apply adj_tl. apply adj_hd.
    -- apply H.
  Qed.

  (** ** Metatheorems *)
  (** *** Negation *)

  Fixpoint dual F :=
    match F with
    | atom A => natom A
    | natom A => atom A
    | tens A' B' => par (dual A') (dual B')
    | par A' B' => tens (dual A') (dual B')
    | one => bot
    | bot => one
    end.

  Inductive dual_rel : formula -> formula -> Prop :=
  | dual_atom_natom    : forall A, dual_rel (atom A) (natom A)
  | dual_one_bot : dual_rel one bot
  | dual_par_tens : forall A nA B nB, dual_rel A nA -> dual_rel B nB -> dual_rel (par A B) (tens nA nB).

  Theorem dual_sym : forall A B, dual_rel A B -> dual_rel B A.
  Admitted.

  Theorem dual_involutive : forall A, dual (dual A) = A.
  Proof.
    intros.
    induction A; try reflexivity.
    - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
    - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
  Qed.

  Theorem dual_rel_dual_1 : forall A, dual_rel A (dual A).
  Proof.
    intros.
    induction A.
    - simpl. apply dual_sym. apply dual_one_bot.
    - simpl. apply dual_one_bot.
    - simpl. apply dual_atom_natom.
    - simpl. apply dual_sym. apply dual_atom_natom.
    - simpl. apply dual_sym. apply dual_par_tens.
      -- apply dual_sym. apply IHA1.
      -- apply dual_sym. apply IHA2.
    - simpl. apply dual_par_tens.
      -- apply IHA1.
      -- apply IHA2.
  Qed.

  Theorem dual_dual_rel : forall A B, dual A = B -> dual_rel A B.
  Proof.
    intros. subst. apply dual_rel_dual_1.
  Qed.

  Theorem dual_rel_inv : forall A B, dual_rel A B -> dual A = B.
  Proof.
    intros.
    induction H.
    - reflexivity.
    - reflexivity.
    - simpl. rewrite <- IHdual_rel1.  rewrite <- IHdual_rel2. reflexivity.
  Qed.

  (** ** Identity *)
  (** eauto solves this easily! *)
  Theorem mll_identity : forall A B, dual_rel A B -> mll [A; B].
  Proof.
    intros.
    induction H; eauto 10 with my_db.
  Qed.

  (** ** Exchange *)
  Theorem mll_exchange : forall K L,
      mll K -> perm K L -> mll L.
  Proof.
    intros. generalize dependent L.
    induction H;intros.
    (* id *)
    - inversion H; subst.
      -- pose proof (perm_cons_1 _ _ _ H0) as [J [H1a H1b]].
         pose proof (perm_cons_1 _ _ _ H1b) as [J1 [H2a H2b]].
         inversion H2b; subst.
         inversion H2a; subst. eauto with my_db.
         inversion H1.
      -- pose proof (perm_cons_1 _ _ _ H0) as [J [H1a H1b]].
         apply adj_nil_1 in H5; subst.
         pose proof (perm_cons_1 _ _ _ H1b) as [J1 [H2a H2b]].
         pose proof (adj_swap _ _ _ _ _ H2a H1a) as [U [H3a H3b]].
         apply perm_nil_1 in H2b; subst. apply adj_nil_1 in H3a; subst.
         eauto with my_db.
    (* tens *)
    - assert (perm J (A :: JJ)) by eauto with my_db.
      assert (perm K (B :: KK)) by eauto with my_db.
      apply IHmll1 in H6.
      apply IHmll2 in H7.
      pose proof (adj_perm_full _ _ _ _ H5 H) as [KK1 [H8a H8b]].
      pose proof (perm_merge_3 _ _ _ _  H0 H8b).
      eauto with my_db.
    (* one *)
    - inversion H0; subst.
      inversion H; subst.
      -- apply perm_nil_1 in H2; subst. apply adj_nil_1 in H1; subst.
         apply mll_one.
      -- inversion H6.
    (* par *)
    - pose proof (adj_perm_full _ _ _ _ H3 H) as [KK [H4a H4b]].
      assert (perm J (A :: KK)) by eauto with my_db.
      assert (perm K (B :: A :: KK)) by eauto with my_db.
      apply IHmll in H5.
      eauto with my_db.
    (* bot *)
    - pose proof (adj_perm_full _ _ _ _ H1 H) as [KK [H2 H2b]].
      apply IHmll in H2b.
      info_eauto with my_db.
  Qed.

  (** Inversion theorems *)
  Theorem bot_inv : forall J L,
      mll L -> adj J bot L -> mll J.
  Proof.
    intros.
    generalize dependent J.
    induction H.
    - (* id *)
      intros. subst.
      pose proof (adj_same_result_diff _ _ _ _ _ H0 H) as [[Heq H1] | [KK H1]].
      -- discriminate.
      -- inversion H1; subst. inversion H5.
    - (* tens *)
      intros. subst.
      pose proof (adj_same_result_diff _ _ _ _ _ H5 H) as [[Heq H6] | [KK1 H6]].
      -- discriminate.
      -- pose proof (merge_unadj_3 _ _ _ _ _ H0 H6) as [[JJ1 [H7 H7b]] | [KK2 [H7 H7b]]].
         --- pose proof (adj_swap _ _ _ _ _ H7 H1) as [U [H8 H8b]].
             specialize (IHmll1 _ H8b).
             pose proof (merge_unadj_1 _ _ _ _ _ H0 H7) as [LL1 [H9 H9b]].
             pose proof (adj_swap _ _ _ _ _ H9 H) as [U1 [H10 H10b]].
             assert (mll U1) by eauto with my_db.
             pose proof (adj_same_result _ _ _ _ H10b H5).
             apply (mll_exchange _ _ H11 H12).
         --- pose proof (merge_unadj_2 _ _ _ _ _ H0 H7) as [LL1 [H8 H8b]].
             pose proof (adj_same_result _ _ _ _ H8 H6).
             pose proof (perm_merge_3 _ _ _ _ H8b H9).
             pose proof (adj_swap _ _ _ _ _ H7 H3) as [U [H11 H11b]].
             specialize (IHmll2 _ H11b).
             pose proof (adj_swap _ _ _ _ _ H6 H) as [U1 [H12 H12b]].
             assert (mll U1) by eauto with my_db.
             pose proof (adj_same_result _ _ _ _ H12b H5).
             apply (mll_exchange _ _ H13 H14).
    - (* one *)
      intros.
      inversion H0; subst.
      inversion H3.
    - (* par *)
      intros.
      pose proof (adj_same_result_diff _ _ _ _ _ H3 H) as [[Heq H4] | [KK1 H4]].
      -- discriminate.
      -- pose proof (adj_swap _ _ _ _ _ H4 H0) as [U [H5 H5b]].
         pose proof (adj_swap _ _ _ _ _ H5b H1) as [U1 [H6 H6b]].
         specialize (IHmll _ H6b).
         pose proof (adj_swap _ _ _ _ _ H4 H) as [U2 [H7 H7b]].
         assert (mll U2) by eauto with my_db.
         pose proof (adj_same_result _ _ _ _ H7b H3).
         apply (mll_exchange _ _ H8 H9).
    - (* bot *)
      intros.
      pose proof (adj_same_result _ _ _ _ H H1).
      apply (mll_exchange _ _ H0 H2).
  Qed.

  Theorem adj_sequence : forall J A K B L,
      adj J A K ->
      adj J B L ->
      exists KK LL, adj L A LL /\ adj K B KK /\ perm KK LL.
  Proof.
    intros J A K B L H.
    generalize dependent B. generalize dependent L.
    induction H; intros.
    - eauto 10 with my_db.
    - inversion H0; subst.
      -- eauto 10 with my_db.
      -- specialize (IHadj _ _ H5).
         eauto 10 with my_db.
  Qed.

  Theorem par_inv : forall L JJ A B,
      mll L -> adj JJ (par A B) L ->
      exists KK LL, adj JJ A KK /\ adj KK B LL /\ mll LL.
  Proof.
    intros LL J A B H1.
    generalize dependent A. generalize dependent B. generalize dependent J.
    induction H1; intros.
    - (* id *)
      pose proof (adj_same_result_diff _ _ _ _ _ H0 H) as [[Heq H1] | [KK1 H1]].
      -- discriminate.
      -- inversion H1; subst.
         inversion H5.
    - (* tens *)
      pose proof (adj_same_result_diff _ _ _ _ _ H3 H) as [[Heq H4] | [KK1 H4]].
      -- discriminate.
      -- pose proof (merge_unadj_3 _ _ _ _ _ H0 H4) as [[JJ1 [H5 H5b]] | [KK2 [H5 H5b]]].
         --- pose proof (adj_swap _ _ _ _ _ H5 H1) as [U [H6 H6b]].
             specialize (IHmll1 _ _ _ H6b) as [KK2 [LL1 [IH1 [IH1b IH1c]]]].
             pose proof (adj_swap _ _ _ _ _ H6 IH1) as [U1 [H7 H7b]].
             pose proof (adj_swap _ _ _ _ _ H7b IH1b) as [U2 [H8 H8b]].
             assert (merge U2 KK (A0 :: B0 :: KK1)) by eauto with my_db.
             assert (mll (tens A B :: A0 :: B0 :: KK1)) by eauto with my_db.
             pose proof (adj_swap _ _ _ _ _ H4 H) as [U3 [H11 H11b]].
             pose proof (adj_same_result _ _ _ _ H11b H3).
             pose proof (adj_perm_full _ _ _ _ H12 H11) as [KK3 [H13 H13b]].
             assert (perm (tens A B :: A0 :: B0 :: KK1) (A0 :: B0 :: J0)) by eauto 6 with my_db.
             pose proof (mll_exchange _ _ H10 H14).
             eauto 6 with my_db.
         --- pose proof (adj_swap _ _ _ _ _ H5 H2) as [U [H6 H6b]].
             specialize (IHmll2 _ _ _ H6b) as [KK3 [LL1 [IH2 [IH2b IH2c]]]].
             pose proof (adj_swap _ _ _ _ _ H6 IH2) as [U1 [H7 H7b]].
             pose proof (adj_swap _ _ _ _ _ H7b IH2b) as [U2 [H8 H8b]].
             assert (merge JJ U2 (A0 :: B0 :: KK1)) by eauto with my_db.
             assert (mll (tens A B :: A0 :: B0 :: KK1)) by eauto with my_db.
             pose proof (adj_swap _ _ _ _ _ H4 H) as [U3 [H11 H11b]].
             pose proof (adj_same_result _ _ _ _ H11b H3).
             pose proof (adj_perm_full _ _ _ _ H12 H11) as [KK4 [H13 H13b]].
             assert (perm (tens A B :: A0 :: B0 :: KK1) (A0 :: B0 :: J0)) by eauto 6 with my_db.
             pose proof (mll_exchange _ _ H10 H14).
             eauto 6 with my_db.
    - (* one *)
      intros.
      inversion H; subst. inversion H3.
    - (* par *)
      pose proof (adj_same_result_diff _ _ _ _ _ H3 H)  as [[Heq H4] | [KK H4]].
      -- inversion Heq; subst.
         assert (perm (A :: B :: J0) K) by eauto with my_db.
         apply perm_sym in H5.
         pose proof (mll_exchange _ _ H2 H5).
         eauto 6 with my_db.
      -- pose proof (adj_swap _ _ _ _ _ H4 H0) as [U [H5 H5b]].
         pose proof (adj_swap _ _ _ _ _ H5b H1) as [U1 [H6 H6b]].
         specialize (IHmll _ _ _ H6b) as [KK1 [LL1 [IH2 [IH2b IH2c]]]].
         pose proof (adj_swap _ _ _ _ _ H6 IH2) as [U2 [H7 H7b]].
         pose proof (adj_swap _ _ _ _ _ H7b IH2b) as [U3 [H8 H8b]].
         pose proof (adj_swap _ _ _ _ _ H5 H7) as [U4 [H9 H9b]].
         pose proof (adj_swap _ _ _ _ _ H9b H8) as [U5 [H10 H10b]].
         assert (mll (par A B :: U5)) by eauto with my_db.
         assert (perm (par A B :: U5) (A0 :: B0 :: J0)). {
           eapply (perm_split _ _ B0 (par A B :: U4) (A0 :: J0) _ _).
           Unshelve.
           2: eauto with my_db.
           2: eauto with my_db.
           eapply (perm_split _ _ A0 (par A B :: KK) J0 _ _).
           Unshelve.
           2: eauto with my_db. 
           2: eauto with my_db.
           pose proof (adj_swap _ _ _ _ _ H4 H) as [U6 [H12 H12b]].
           pose proof (adj_same_result _ _ _ _ H12b H3).
           eapply perm_trans; eauto.
           eauto with my_db.
         }
         pose proof (mll_exchange _ _ H11 H12).
         eauto 6 with my_db.
    - (* bot *)
      pose proof (adj_same_result_diff _ _ _ _ _ H0 H)  as [[Heq H4] | [KK H4]].
      -- discriminate.
      -- specialize (IHmll _ _ _ H4) as [KK1 [LL1 [IH2 [IH2b IH2c]]]].
         assert (mll (bot :: LL1)) by eauto with my_db.
         assert (perm (bot :: LL1) (A :: B :: J)). {
           eapply (perm_split _ _ B (bot :: KK1) (A :: J) _ _).
           Unshelve.
           2: eauto with my_db.
           2: eauto with my_db.
           eapply (perm_split _ _ A (bot :: KK) J _ _).
           Unshelve.
           2: eauto with my_db.
           2: eauto with my_db.
           pose proof (adj_swap _ _ _ _ _ H4 H) as [U [H5 H5b]].
           pose proof (adj_same_result _ _ _ _ H5b H0).
           eapply perm_trans; eauto.
           eauto with my_db.
         }
         pose proof (mll_exchange _ _ H2 H3).
         eauto 6 with my_db.
  Qed.

  Theorem mll_cut : forall A B JJ J KK K LL,
      dual_rel A B ->
      adj JJ A J -> mll J ->
      adj KK B K -> mll K ->
      merge JJ KK LL ->
      mll LL.
  Proof.
    Admitted.


End MLL_LMP.
