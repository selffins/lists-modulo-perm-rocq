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
  | rules_id : forall L A, adj (natom A :: nil) (atom A) L -> mll L
  | rules_tens : forall L A B LL JJ KK J K,
      adj LL (tens A B) L ->
      merge JJ KK LL ->
      adj JJ A J -> mll J ->
      adj KK B K -> mll K -> mll L
  | rules_one : mll ([one])
  | rules_par : forall L A B LL J K,
      adj LL (par A B) L ->
      adj LL A J ->
      adj J B K ->
      mll K ->
      mll L
  | rules_bot : forall L LL,
      adj LL bot L -> mll LL -> mll L.

  (** ** Example derivations *)

  (** Interesting things:
      - [rules_par] can be applied in many ways due to how [adj] works.
      If you apply [rules_par] using [eapply] (without specifying arguments), you actually end up reversing the list.
      But the hypothesis we have is in a different order (is sorted).
      So it's important to be explicit about how you want the resulting list order to be afterwards.
      (Well, that is, if you don't have the exchange theorem yet.)
   *)

  Example a1_par_a2_a3_par_a4_1 : forall A1 A2 A3 A4,
      mll [A1 ; A2 ; A3 ; A4] -> mll [par A1 A2; par A3 A4].
  Proof.
    intros.
    eapply rules_par with (K := [A1 ; A2 ; par A3 A4]).
    - apply adj_hd.
    - apply adj_hd.
    - apply adj_tl. apply adj_hd.
    - eapply rules_par with (J := [A1; A2; A3]) (K := [A1; A2; A3; A4]).
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

  Theorem dual_comm : forall A B, dual_rel A B -> dual_rel B A.
  Admitted.

  Theorem dual_involutive : forall A, dual (dual A) = A.
  Proof.
    intros.
    induction A;try reflexivity.
    - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
    - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
  Qed.

  Theorem dual_rel_dual_1 : forall A, dual_rel A (dual A).
  Proof.
    intros.
    induction A.
    - simpl. apply dual_comm. apply dual_one_bot.
    - simpl. apply dual_one_bot.
    - simpl. apply dual_atom_natom.
    - simpl. apply dual_comm. apply dual_atom_natom.
    - simpl. apply dual_comm. apply dual_par_tens.
      -- apply dual_comm. apply IHA1.
      -- apply dual_comm. apply IHA2.
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
  Theorem Identity : forall A B, dual_rel A B -> mll [A; B].
  Proof.
    intros.
    induction H.
    - apply rules_id with (A := A). apply adj_hd.
    - apply rules_bot with (LL := [one]).
      apply adj_tl. apply adj_hd.
      apply rules_one.
    - eapply rules_par with (A := A) (B := B) (LL := [tens nA nB]).
      -- apply adj_hd.
      -- apply adj_tl. apply adj_hd.
      -- apply adj_hd.
      -- eapply rules_tens with (A := nA) (B := nB).
         --- apply adj_tl. apply adj_hd.
         --- eapply merge_r with (A := B) (L := [B; A]).
             ---- apply adj_hd.
             ---- apply adj_hd.
             ---- eapply merge_l with (A := A).
                  ----- apply adj_hd.
                  ----- apply adj_hd.
                  ----- apply merge_nil.
         --- apply adj_tl. apply adj_hd.
         --- apply IHdual_rel1.
         --- apply adj_tl. apply adj_hd.
             --- apply IHdual_rel2.
  Qed.

  (** ** Exchange *)
  Theorem Exchange : forall K L,
      mll K -> perm K L -> mll L.
  Proof.
    intros. generalize dependent L.
    induction H;intros.
    (* id *)
    - inversion H;subst.
      -- apply perm_cons_1 in H0 as [J [H1a H1b]].
         apply perm_cons_1 in H1b as [J1 [H2a H2b]].
         inversion H2b;subst.
         --- inversion H2a;subst. eapply rules_id. apply H1a.
         --- inversion H0.
      -- apply perm_cons_1 in H0 as [J [H1a H1b]].
         apply adj_nil_1 in H5; subst.
         apply perm_cons_1 in H1b as [J1 [H2a H2b]].
         apply adj_swap with (J := J1) (A := atom A) (K := J) (B := natom A) (L := L0) in H2a as [U [H3a H3b]].
         --- apply perm_nil_1 in H2b; subst. apply adj_nil_1 in H3a; subst.
         eapply rules_id. apply H3b.
         --- apply H1a.
    (* tens *)
    - rename K into K1.
      assert (perm J (A :: JJ)). {
        eapply perm_split.
        * apply H1.
        * apply adj_hd.
        * apply perm_refl.
      }
      assert (perm K1 (B :: KK)). {
        eapply perm_split.
        * apply H3.
        * apply adj_hd.
        * apply perm_refl.
      }
      apply IHmll1 in H6.
      apply IHmll2 in H7.
      rename L into K. rename L0 into L.
      apply adj_perm_full with (J := K) (K := L) in H as [KK1 [H8a H8b]].
      -- apply perm_merge_3 with (L := LL) (LL := KK1) in H0.
         --- eapply rules_tens.
             ---- apply H8a.
             ---- apply H0.
             ---- apply H1.
             ---- apply H2.
             ---- apply H3.
             ---- apply H4.
         --- apply H8b.
      -- apply H5.
    (* one *)
    - inversion H0;subst.
      inversion H;subst.
      -- apply perm_nil_1 in H2;subst. apply adj_nil_1 in H1;subst.
         apply rules_one.
      -- inversion H6.
    (* par *)
    - rename K into K1. rename L into K. rename L0 into L.
      apply adj_perm_full with (K := L) (JJ := LL) (A := par A B) (J := K) in H as [KK [H4a H4b]].
      assert (perm J (A :: KK)). {
        eapply perm_split. apply H0. apply adj_hd. apply H4b.
      }
      assert (perm K1 (B :: A :: KK)). {
        eapply perm_split. apply H1. apply adj_hd. apply H.
      }
      apply IHmll in H4.
      eapply rules_par.
      -- apply H4a.
      -- apply adj_hd.
      -- apply adj_hd.
      -- apply H4.
      -- apply H3.
    (* bot *)
    - rename L into K. rename L0 into L.
      apply adj_perm_full with (K := L) (JJ := LL) (A := bot) (J := K) in H as [KK [H2a H2b]].
      -- apply IHmll in H2b.
         eapply rules_bot.
         --- apply H2a.
         --- apply H2b.
      -- apply H1.
  Qed.

End MLL_LMP.
