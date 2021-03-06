(* Facts about "small" types and non-accessible localizations. *)

(* ** Trim down imports later. *)
Require Import HoTT.

Require Import Conn.
Require Import misc.

(* Universe variables:  we most often use a subset of [i j k u].  We think of [Type@{i}] as containing the "small" types and [Type@{j}] the "large" types.  In some early results, there are no constraints between [i] and [j], and in others we require that [i <= j], as expected.  While the case [i = j] isn't particularly interesting, we put some effort into ensuring that it is permitted as well, as there is no semantic reason to exclude it.  The universe variable [k] should be thought of as max(i+1,j), and it is generally required to satisfy [i < k] and [j <= k].  If we assume that [i < j], then we can take [k = j], but we include [k] so that we also allow the case [i = j].  The universe variable [u] is only present because we occasionally use Univalence in [Type@{k}], so the equality types need a larger universe to live in.  Because of this, most results require [k < u].

Summary of the most common situation:  [i < k < u, j <= k], where [i] is for the small types, [j] is for the large types, [k = max(i+1,j)] and [u] is an ambient universe for Univalence.

We include universe annotations when they clarify the meaning (e.g. in [IsSmall] and when using [PropResizing]), and also when it is required in order to keep control of the universe variables. *)

(* We say that [X : Type@{j}] is small (relative to Type@{i}) if it is equivalent to a type in [Type@{i}].  We use a record to avoid an extra universe variable.  This version has no constraints on i and j.  It lands in max(i+1,j), as expected. *)
Record IsSmall@{i j | } (X : Type@{j}) :=
  { smalltype : Type@{i} ;
    equiv_smalltype : smalltype <~> X
  }.
Arguments smalltype {X} _.
Arguments equiv_smalltype {X} _.

Definition lift_issmall@{i j k | j <= k}
           (X : Type@{j})
           (sX : IsSmall@{i j} X)
  : IsSmall@{i k} X
  := Build_IsSmall X (smalltype sX) (equiv_smalltype sX).

Definition lower_issmall@{i j k | j <= k}
           (X : Type@{j})
           (sX : IsSmall@{i k} X)
  : IsSmall@{i j} X
  := Build_IsSmall X (smalltype sX) (equiv_smalltype sX).

Global Instance ishprop_issmall@{i j k | i < k, j <= k} `{Univalence} (X : Type@{j}) : IsHProp (IsSmall@{i j} X).
Proof.
  apply hprop_inhabited_contr.
  intros [Z e].
  (* [IsSmall X] is equivalent to [IsSmall Z], which is contractible since it is a based path space. *)
  rapply (istrunc_equiv_istrunc@{k k} { Y : Type@{i} & Y <~> Z } _).
  - refine (_ oE _).
    1: issig.
    apply equiv_functor_sigma_id.
    intro Y.
    exact (equiv_postcompose_equiv@{i j i k k} Y e).
Defined.

(* A type in [Type@{i}] is clearly small.  Make this a Global Instance? *)
Definition issmall_in@{i j | i <= j} (X : Type@{i}) : IsSmall@{i j} X
  := Build_IsSmall X X equiv_idmap.

(* The small types are closed under equivalence. *)
(* No constraints on i, j1 and j2. *)
Definition issmall_equiv_issmall@{i j1 j2 | } {A : Type@{j1}} {B : Type@{j2}}
           (e : A <~> B) (sA : IsSmall@{i j1} A)
  : IsSmall@{i j2} B.
Proof.
  exists (smalltype sA).
  exact (e oE (equiv_smalltype sA)).
Defined.

(* The small types are closed under dependent sums. *)
Definition sigma_closed_issmall@{i j | } {A : Type@{j}}
           (B : A -> Type@{j}) (sA : IsSmall@{i j} A)
           (sB : forall a, IsSmall@{i j} (B a))
  : IsSmall@{i j} { a : A & B a }.
Proof.
  exists { a : (smalltype sA) & (smalltype (sB (equiv_smalltype sA a))) }.
  snrapply equiv_functor_sigma'; intros; apply equiv_smalltype.
Defined.

(* If a map has small codomain and fibers, then the domain is small. *)
Definition issmall_codomain_fibers_small@{i j | } {X Y : Type@{j}}
           (f : X -> Y)
           (sY : IsSmall@{i j} Y)
           (sF : forall y : Y, IsSmall@{i j} (hfiber f y))
  : IsSmall@{i j} X.
Proof.
  rapply issmall_equiv_issmall.
  - exact (equiv_fibration_replacement f)^-1%equiv.
  - apply sigma_closed_issmall; assumption.
Defined.

(* Propositional Resizing says that every (-1)-truncated type is small. *)
(* No constraints on i and j. *)
Definition issmall_hprop@{i j | } `{PropResizing} (X : Type@{j}) (T : IsTrunc (-1) X)
  : IsSmall@{i j} X.
Proof.
  exists (resize_hprop@{j i} X).
  apply (equiv_resize_hprop X)^-1%equiv.
Defined.

(* Every contractible, i.e. (-2)-truncated type, is small. *)
Definition issmall_contr@{i j| } (X : Type@{j}) (T : IsTrunc (-2) X): IsSmall@{i j} X.
Proof.
  refine (issmall_equiv_issmall (equiv_contr_unit)^-1 _).
  apply issmall_in.
Defined.

(* This isn't yet in the paper. It lets us simplify the statement of Proposition 2.8. *)
Definition issmall_inhabited_issmall@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
           (X : Type@{j})
           (isX : X -> IsSmall@{i j} X)
  : IsSmall@{i j} X.
Proof.
  (* Since IsSmall@{i j} lives in a universe larger than [i] and we're not assuming [i <= j], we have to pass through universe [k], which we think of as max(i+1,j). *)
  apply lower_issmall.
  (* Now the goal is IsSmall@{i k} X. *)
  apply (issmall_codomain_fibers_small isX).
  - rapply issmall_hprop.
  - intro sX.
    apply sigma_closed_issmall.
    1: apply (lift_issmall _ sX).
    intro x.
    rapply issmall_contr.
Defined.

(* Locally small types. *)

(* We say that a type [X] is 0-locally small if it is small, and (n+1)-locally small if its identity types are n-small. *)
Fixpoint IsLocallySmall@{i j k | i < k, j <= k} (n : nat) (X : Type@{j}) : Type@{k}
  := match n with
    | 0%nat => IsSmall@{i j} X
    | S m => forall x y : X, IsLocallySmall m (x = y)
    end.

Definition ishprop_islocally_small@{i j k u | i < k, j <= k, k <= u, j < u} `{Univalence}
           (n : nat) (X : Type@{j})
  : IsHProp@{k} (IsLocallySmall@{i j k} n X).
Proof.
  (* We use [simple_induction] to control the universe variable. *)
  revert X; simple_induction n n IHn; exact _.
Defined.

Definition islocally_small_in@{i j k | i <= j, j <= k, i < k} (n : nat) (X : Type@{i})
  : IsLocallySmall@{i j k} n X.
Proof.
  revert X.
  induction n; intro X.
  - apply issmall_in.
  - intros x y.
    exact (IHn (x = y)).
Defined.

(* The locally small types are closed under equivalence. *)
Definition islocally_small_equiv_islocally_small@{i j1 j2 k u | i < k, j1 <= k, j2 <= k, k <= u, j1 < u, j2 < u}
           (n : nat) {A : Type@{j1}} {B : Type@{j2}}
           (e : A <~> B) (lsA : IsLocallySmall@{i j1 k} n A)
  : IsLocallySmall@{i j2 k} n B.
Proof.
  revert A B e lsA.
  simple_induction n n IHn.
  - exact @issmall_equiv_issmall@{i j1 j2}.
  - intros A B e lsA b b'.
    nrapply IHn.
    * exact (equiv_ap' (e^-1%equiv) b b')^-1%equiv.
    * apply lsA.
Defined.

Definition sigma_closed_islocally_small@{i j k u | i < k, j <= k, k <= u, j < u}
           (n : nat) {A : Type@{j}} (B : A -> Type@{j})
           (lsA : IsLocallySmall@{i j k} n A)
           (lsB : forall a, IsLocallySmall@{i j k} n (B a))
  : IsLocallySmall@{i j k} n { a : A & B a }.
Proof.
  revert A B lsA lsB.
  simple_induction n n IHn.
  - exact @sigma_closed_issmall.
  - intros A B lsA lsB x y.
    apply (islocally_small_equiv_islocally_small n (equiv_path_sigma _ x y)).
    apply IHn.
    * apply lsA.
    * intro p.
      apply lsB.
Defined.

(* If a map has locally small codomain and fibers, then the domain is locally small. *)
Definition islocally_small_codomain_fibers_locally_small@{i j k u | i < k, j <= k, k <= u, j < u}
           (n : nat)
           {X Y : Type@{j}}
           (f : X -> Y)
           (sY : IsLocallySmall@{i j k} n Y)
           (sF : forall y : Y, IsLocallySmall@{i j k} n (hfiber f y))
  : IsLocallySmall@{i j k} n X.
Proof.
  rapply islocally_small_equiv_islocally_small@{i j j k u}.
  - exact (equiv_fibration_replacement f)^-1%equiv.
  - apply sigma_closed_islocally_small; assumption.
Defined.

(* A small type is n-locally small for all n. *)
Definition islocally_small_small@{i j k u | i < k, j <= k, k <= u, j < u} (n : nat)
           (X : Type@{j}) (sX : IsSmall@{i j} X)
  : IsLocallySmall@{i j k} n X.
Proof.
  apply (islocally_small_equiv_islocally_small@{i i j k u} n (equiv_smalltype sX)).
  apply islocally_small_in.
Defined.

(* Sends a trunc_index [m] to the natural number [m+2]. *)
Fixpoint trunc_index_to_nat (m : trunc_index) : nat
:= match m with
     | minus_two => 0
     | m'.+1 => (trunc_index_to_nat m').+1
   end.

(* Under Propositional Resizing, every (n+1)-truncated type is (n+2)-locally small. This is Lemma 2.3 in the paper. *)
Definition islocally_small_trunc@{i j k u | i < k, j <= k, k <= u, j < u} `{PropResizing}
           (n : trunc_index) (X : Type@{j}) (T : IsTrunc n.+1 X)
  : IsLocallySmall@{i j k} (trunc_index_to_nat n) X.
Proof.
  revert n X T.
  rapply trunc_index_rect@{u}; cbn.
  - nrapply issmall_hprop.
  - intros n IHn X T x y.
    rapply IHn.
Defined.

(* Rijke's join construction, taken as an axiom. Egbert assumes [Funext] globally, so we assume it here. *)
(* A more detailed formulation of this is in the HoTT library, but this is all we need (and is equivalent). *)
(* This has been formalized by Valery Isaev in the Arend Standard Library available at https://github.com/JetBrains/arend-lib.  See the file Homotopy/Image.ard. *)
Definition jc_surjection@{i j k | i < k, j <= k} `{Funext} (A : Type@{i}) (X : Type@{j})
           (ls : IsLocallySmall@{i j k} 1 X)
           (f : A -> X) (s : IsSurjection@{k} f)
  : IsSmall@{i j} X.
Admitted.

(* If [f : A -> X] is n-connected, [A] is in [Type@{i}] and [X] is (n+2)-locally small, then [X] is small.  This is Proposition 2.2 from the paper. This could of course be generalized to only requiring that [A] be small. *)
Definition issmall_n_image@{i j k u | i < k, j <= k, k < u} `{Univalence}
           (n : trunc_index) {A : Type@{i}} {X : Type@{j}}
           (f : A -> X) (C : IsConnMap@{k} n f) (ls : IsLocallySmall@{i j k} (trunc_index_to_nat n) X)
  : IsSmall@{i j} X.
Proof.
  revert n A X f C ls.
  rapply trunc_index_rect@{u}.
  - intros A X f C ls.  exact ls.
  - intros n IHn A X f C ls.
    assert (IsConnMap (Tr (-1)) f) as C' by rapply minus_one_connmap_isconnmap.
    snrefine (jc_surjection A X _ f C').
    (* [f] is surjective and [IsSmall] is an [HProp], so we can assume that [x] and [y] are in the image of [f]. *)
    (* We speed up typeclass inference by providing this: *)
    pose proof (fun x y : X => ishprop_issmall (x = y)) as HP.
    intro x.
    apply (@conn_map_elim@{k i j k} (Tr (-1)) _ _ f C' _ (HP x)).
    intro b.
    revert x.
    apply (@conn_map_elim@{k i j k} (Tr (-1)) _ _ f C' _ (fun x => HP x (f b))).
    intro a.
    snrapply (IHn (a = b) _ (ap@{i j} f)).
    + srapply isconnmap_ap@{k u}.
    + apply ls.
Defined.

(* If [f : X -> Y] is (n+1)-truncated and [Y] is (n+2)-locally small, then [X] is (n+2)-locally small.  This is Lemma 2.4 from the paper. When [n] is -2, it says that a subtype of a small type is small. *)
Definition islocally_small_truncmap@{i j k u | i < k, j <= k, k <= u, j < u} `{PropResizing}
           (n : trunc_index) {X : Type@{j}} {Y : Type@{j}}
           (f : X -> Y) (T : IsTruncMap n.+1 f) (ls : IsLocallySmall@{i j k} (trunc_index_to_nat n) Y)
  : IsLocallySmall@{i j k} (trunc_index_to_nat n) X.
Proof.
  apply (islocally_small_codomain_fibers_locally_small@{i j k u} _ f).
  - exact ls.
  - intro y.
    apply islocally_small_trunc.
    apply T.
Defined.

(* This is Lemma 2.5 from the paper. *)
Definition issmall_truncmap_connected@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
           (n : trunc_index)
           {X Y : Type@{j}}
           (f : X -> Y) (T : IsTruncMap n.+1 f)
           (ls : IsLocallySmall@{i j k} (trunc_index_to_nat n) Y)
           (C : IsConnected n.+1 X)
  : IsSmall@{i j} X.
Proof.
  pose proof (x := merely_isconnected n X).
  strip_truncations.
  apply (issmall_n_image@{i j k u} n (unit_name x)).
  - apply lift_isconnmap_trunc@{j k}.
    rapply conn_point_incl@{j j j j j j j j j j j j j j j u}.
  - by rapply islocally_small_truncmap@{i j k u}.
Defined.

(* This is Theorem 2.6 from the paper. *)
Definition issmall_iff_locally_small_truncated@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
           (n : trunc_index) (X : Type@{j})
  : IsSmall@{i j} X <-> (IsLocallySmall@{i j k} (trunc_index_to_nat n) X * IsSmall@{i j} (Trunc n.+1 X)).
Proof.
  split.
  - intro sX.
    split.
    + by apply islocally_small_small@{i j k u}.
    + apply (issmall_equiv_issmall (Trunc_functor_equiv@{i j k} _ (equiv_smalltype sX))).
      apply issmall_in.
  - intros [lsX sTrX].
    apply (issmall_codomain_fibers_small (@tr n.+1 X)).
    + exact sTrX.
    + intro y.
      apply (issmall_truncmap_connected@{i j k u} n pr1).
      * rapply istruncmap_pr1.
      * exact lsX.
      * exact _.
Defined.

(* This is Corollary 2.7 from the paper. *)
Definition issmall_truncmap_small_truncation@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
           (n : trunc_index)
           {X Y : Type@{j}}
           (f : X -> Y) (T : IsTruncMap n.+1 f)
           (ls : IsLocallySmall@{i j k} (trunc_index_to_nat n) Y)
           (sTrX : IsSmall@{i j} (Trunc n.+1 X))
  : IsSmall@{i j} X.
Proof.
  apply (snd (issmall_iff_locally_small_truncated@{i j k u} n X)).
  refine (_, sTrX).
  rapply islocally_small_truncmap@{i j k u}; assumption.
Defined.
