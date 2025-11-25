From Coq Require Export Sets.Multiset.

From Coq Require Export List.
From Coq Require Import Arith.EqNat.
Export ListNotations.

(** This file is about how to translate the main relations and whether they are valid.

According to the Abella manual, a definition like

```
Define plus : nat -> nat -> nat -> prop by
  plus z     M N     ;
  plus (s M) M (s K) := plus M N K.
```

is a /definitional clause/ for the /plus/ predicate, with all the clauses separated by semi-colons.
The /head/ of each clause is the atomic formula that occurs to the left of [:=] while the formula to
the right of [:=] is the /body/.

In each clause, the capitalized identifiers are assuemd to be universally quantified.

 *)

Check nat_ind.

Theorem foo : forall n, 0 + n = n.
Proof.
  intros.
  Check nat_ind.
  induction n; auto.
Qed.

Definition o := bool.

(** * Abella code for these relations
 *)

(** 1. adj

% adj J A K : K is J with A inserted somewhere
Define adj : olist -> o -> olist -> prop by
; adj L A (A :: L) := is_o A /\ is_list L
; adj (B :: K) A (B :: L) := is_o B /\ adj K A L
.

 *)

(** 2. perm

% perm J K : J and K have the same elements
Define perm : olist -> olist -> prop by
; perm nil nil
; perm K L :=
    exists A KK LL, adj KK A K /\ adj LL A L /\ perm KK LL.

 *)

(** 3. merge

% merge J K L : J union K equals L.
Define merge : olist -> olist -> olist -> prop by
; merge nil nil nil
; merge J K L :=
    exists A JJ LL,
      adj JJ A J /\ adj LL A L /\ merge JJ K LL
; merge J K L :=
    exists A KK LL,
      adj KK A K /\ adj LL A L /\ merge J KK LL
.

 *)

(** * Directly translated abella relations


 *)
Module Direct.
  Inductive adj : list o -> o -> list o -> Prop :=
  | adj_hd : forall L A, adj L A (A :: L)
  | adj_tl : forall B K A L, adj K A L -> adj (B :: K) A (B :: L).

  Inductive perm : list o -> list o -> Prop :=
  | perm_nil : perm nil nil
  | perm_split : forall K L, (exists A KK LL, adj KK A K /\ adj LL A L /\ perm KK LL) -> perm K L.

  Inductive merge : list o -> list o -> list o -> Prop :=
  | merge_nil : merge nil nil nil
  | merge_l : forall J K L, (exists A JJ LL, adj JJ A J /\ adj LL A L /\ merge JJ K LL) -> merge J K L
  | merge_r : forall J K L, (exists A KK LL, adj KK A K /\ adj LL A L /\ merge J KK LL) -> merge J K L.

  Check adj_ind.

  (** adj's inductive principle:
```
adj_ind
     : forall P : list o -> o -> list o -> Prop,
       (forall (L : list o) (A : o), P L A (A :: L)) ->
       (forall (B : o) (K : list o) (A : o) (L : list o), adj K A L -> P K A L -> P (B :: K) A (B :: L)) ->
       forall (l : list o) (o0 : o) (l0 : list o), adj l o0 l0 -> P l o0 l0
```
  *)

  Check perm_ind.

  (** perm's inductive principle:
```
perm_ind
     : forall P : list o -> list o -> Prop,
       P [] [] ->
       (forall K L : list o, (exists (A : o) (KK LL : list o), adj KK A K /\ adj LL A L /\ perm KK LL) -> P K L) ->
       forall l l0 : list o, perm l l0 -> P l l0
``` *)

  Check merge_ind.

  (** merge's inductive principle:
```
merge_ind
     : forall P : list o -> list o -> list o -> Prop,
       P [] [] [] ->
       (forall J K L : list o,
        (exists (A : o) (JJ LL : list o), adj JJ A J /\ adj LL A L /\ merge JJ K LL) -> P J K L) ->
       (forall J K L : list o,
        (exists (A : o) (KK LL : list o), adj KK A K /\ adj LL A L /\ merge J KK LL) -> P J K L) ->
       forall l l0 l1 : list o, merge l l0 l1 -> P l l0 l1
```


```
merge_ind
     : forall P : list o -> list o -> list o -> Prop,
       P [] [] [] ->
       (forall (J K L : list o) (A : o) (JJ LL : list o),
        adj JJ A J -> adj LL A L -> merge JJ K LL -> P JJ K LL -> P J K L) ->
       (forall (J K L : list o) (A : o) (KK LL : list o),
        adj KK A K -> adj LL A L -> merge J KK LL -> P J KK LL -> P J K L) ->
       forall l l0 l1 : list o, merge l l0 l1 -> P l l0 l1
```.
   *)

End Direct.

(** * (Our modified) main relations *)
Module Modif.
  (** adj is the same as our directly translated adj *)
  Inductive adj : list o -> o -> list o -> Prop :=
  | adj_hd : forall L A, adj L A (A :: L)
  | adj_tl : forall B K A L, adj K A L -> adj (B :: K) A (B :: L).

  Inductive perm  : list o -> list o -> Prop :=
  | perm_nil : perm nil nil
  | perm_split : forall K L A KA LA, adj K A KA ->
                                     adj L A LA ->
                                     perm K L ->
                                     perm KA LA.

  Inductive merge : list o -> list o -> list o -> Prop :=
  | merge_nil : merge nil nil nil
  | merge_l : forall J K L A JJ LL, adj JJ A J -> adj LL A L -> merge JJ K LL ->  merge J K L
  | merge_r : forall J K L A KK LL, adj KK A K -> adj LL A L -> merge J KK LL -> merge J K L.

  Check adj_ind.

  (** adj's inductive principle:
```
adj_ind
     : forall P : list o -> o -> list o -> Prop,
       (forall (L : list o) (A : o), P L A (A :: L)) ->
       (forall (B : o) (K : list o) (A : o) (L : list o), adj K A L -> P K A L -> P (B :: K) A (B :: L)) ->
       forall (l : list o) (o0 : o) (l0 : list o), adj l o0 l0 -> P l o0 l0
```
  *)

  Check perm_ind.
  (** perm's inductive principle:
```
perm_ind
     : forall P : list o -> list o -> Prop,
       P [] [] ->
       (forall (K L : list o) (A : o) (KA LA : list o), adj K A KA -> adj L A LA -> perm K L -> P K L -> P KA LA) ->
       forall l l0 : list o, perm l l0 -> P l l0
```
   *)

  Check merge_ind.
  (** merge's inductive principle:

Inductive merge : list o -> list o -> list o -> Prop :=
  | merge_nil : merge nil nil nil
  | merge_l : forall J K L A JJ LL, adj JJ A J -> adj LL A L -> merge JJ K LL ->  merge J K L
  | merge_r : forall J K L A KK LL, adj KK A K -> adj LL A L -> merge J KK LL -> merge J K L.

```
merge_ind
     : forall P : list o -> list o -> list o -> Prop,
       P [] [] [] ->
       (forall (J K L : list o) (A : o) (JJ LL : list o),
        adj JJ A J -> adj LL A L -> merge JJ K LL -> P JJ K LL -> P J K L) ->
       (forall (J K L : list o) (A : o) (KK LL : list o),
        adj KK A K -> adj LL A L -> merge J KK LL -> P J KK LL -> P J K L) ->
       forall l l0 l1 : list o, merge l l0 l1 -> P l l0 l1
```.
   *)

End Modif.
