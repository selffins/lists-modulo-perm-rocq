From Coq Require Export Sets.Multiset.
From Coq Require Export List.
From Coq Require Import Arith.EqNat.
Export ListNotations.

Inductive adj : list bool -> bool -> list bool -> Prop :=
  | adj_hd : forall L A, adj L A (A :: L)
  | adj_tl : forall B K A L, adj K A L -> adj (B :: K) A (B :: L).

Inductive perm  : list bool -> list bool -> Prop :=
  | perm_nil : perm nil nil
  | perm_split : forall K L A KA LA, adj K A KA ->
                                     adj L A LA ->
                                     perm K L ->
                                     perm KA LA.

Theorem perm_refl : forall L, perm L L.
Proof.
  intros.
  induction L.
  - apply perm_nil.
  - inversion IHL;subst.
    -- eapply perm_split.
       --- assert (H : adj [] a [a]). { apply adj_hd. } apply H.
       --- assert (H : adj [] a [a]). { apply adj_hd. } apply H.
       --- apply perm_nil.
    -- eapply perm_split.
       --- apply adj_hd.
       --- apply adj_hd.
       --- apply IHL.
Qed.

  Theorem perm_sym : forall K L, perm K L -> perm L K.
  Proof.
    intros.
    induction H.
    - apply perm_nil.
    - eapply perm_split. repeat split.
      -- apply H0.
      -- apply H.
      -- apply IHperm.
  Qed.

Theorem adj_same_result : forall J K A L,
    adj J A L ->
    adj K A L ->
    perm J K.
Proof.
  (*  Induction on adj J A L and casing on adj K A L *)
  intros. generalize dependent K.
  induction H;intros.
  - inversion H0;subst.
    -- apply perm_refl.
    -- eapply perm_split.
       --- apply H3.
       --- apply adj_hd.
       --- apply perm_refl.
  - inversion H0;subst.
    -- eapply perm_split.
       --- apply adj_hd.
       --- apply H.
       --- apply perm_refl.
    -- eapply perm_split.
       --- apply adj_hd.
       --- apply adj_hd.
       --- apply IHadj in H4. apply H4.
Qed.

Theorem perm_trans : forall J K L, perm J K -> perm K L -> perm J L.
Proof.
  intros. generalize dependent L.
  induction H;intros.
  - apply H0.
  - (* Long proof, follow on paper *)
Admitted.

(* This is modified from the original file *)
Theorem adj_perm_result : forall J K A JJ KK,
    perm J K ->
    adj JJ A J ->
    adj KK A K /\ perm JJ KK.
Proof.
Admitted.

Theorem perm_cons_1 : forall C QC P Q,
  perm (C :: P) QC -> adj Q C QC -> perm P Q.
Proof.
  intros.
  inversion H.
  inversion H1.
  (* A is C *)
  - subst. apply perm_trans with (J := P) (L := Q) (K := L).
    -- apply H3.
    -- apply adj_same_result with (A := C) (L := QC).
       + apply H2.
       + apply H0.
  (* A is not C *)
  - subst. apply adj_same_result with (A := C) (L := C :: P).
    -- apply adj_hd.
    -- pose proof adj_perm_result as APR.
       destruct APR with (A := C) (J := QC) (JJ := Q) (K := C :: P) (KK := Q).
       + apply perm_sym. apply H.
       + apply H0.
       + apply H4.
Qed.
