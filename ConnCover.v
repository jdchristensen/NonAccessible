Require Import Basics Types Pointed HFiber Limits.Pullback.
Require Import Truncations.
Require Import Homotopy.Suspension.
Require Import Spaces.Spheres.
Require Import WildCat.

Require Import CORS.

Local Open Scope pointed_scope.

(** n-connected cover *)
Definition cover (n : trunc_index) (X : pType) : pType
  := @pfiber X (pTr n X) ptr.

Global Instance isconnected_cover (n : trunc_index) (X : pType)
  : IsConnected n (cover n X) := _.

(* The projection map from the n-connected cover to the type. *)
Definition cover_proj (n : trunc_index) {X : pType} : cover n X ->* X.
Proof.
  srapply Build_pMap.
  + apply pr1.
  + reflexivity.
Defined.

(* This cover projection map is n-truncated. *)
Global Instance mapinO_cover_proj (n : trunc_index) {X : pType}
  : IsTruncMap n (@cover_proj n.+1 X).
Proof.
  srapply (mapinO_pr1 n).
Defined.

(* This condition on a map [f : X ->* Y] is equivalent to the induced map X<n> ->* Y<n> being an equivalence. We also have implications [isconnequiv n f -> IsTruncMap n f] and [IsTruncMap n f -> isconnequiv n.+1 f], but neither converse is true.  In terms of homotopy groups, [isconnequiv n f] means that [f] is iso on pi_k for k >= n+1, while [IsTruncMap n f] means that [f] is iso on pi_k for k >= n+2 and is monic on pi_{n+1}.  (For explicit counterexamples to the two converse statements, consider the double-cover S^1 -> S^1, or the unique map S^1 -> Unit.)  We prove the second implication below.  For the first, we can take [A] to be S^{n+1}, from which it follows that [fmap (iterated_loops n.+1) f] is an equivalence (see [isequiv_iterated_loops_connequiv] below), which implies that [f] is n-truncated. *)
Definition isconnequiv {X Y : pType} (n : trunc_index) (f : X ->* Y)
  := forall (A : pType), IsConnected n A -> IsEquiv (fun g : A ->* X => f o* g).

(* The type of pointed maps [A ->* X] is equivalent to the fiber of the map from [A -> X] to [X] which evaluates at the base point.  We express this by composing with the inclusion [Unit -> A] of the base point. *)
Definition pointed_maps_as_fiber `{Funext} (A X : pType)
  : (A ->* X) <~> hfiber (fun g : A -> X => g o unit_name pt) (unit_name pt).
Proof.
  refine (_ oE (issig_pmap _ _)^-1%equiv).
  apply equiv_functor_sigma_id.
  intro g.
  rapply (equiv_ap (fun x => unit_name x)).
Defined.

Ltac record_equality :=
  srefine ((equiv_ap' _^-1 _ _)^-1 _); [ | issig | ];
  srapply path_sigma; simpl.

(* Put in Pullback.v. *)
Definition equiv_functor_hfiber_ispullback {A B C D : Type}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h)
           (e : IsPullback p) (b : B)
  := Build_Equiv _ _ _ (isequiv_functor_hfiber_ispullback p e b).

(* A variant in which the "bottom" map is pointed, and we take fibers over the base points. Hmm, not so useful, since in our context Coq doesn't know why things are pointed... *)
Definition equiv_functor_hfiber_ispullback'' {A C : Type} {B D : pType}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B ->* D}
           (p : k o f == g o h)
           (e : IsPullback p)
  : hfiber f pt <~> hfiber g pt.
Proof.
  refine (_ oE equiv_functor_hfiber_ispullback p e pt).
  rapply (equiv_functor_hfiber2 (h:=equiv_idmap) (k:=equiv_idmap)).
  - reflexivity.
  - apply (point_eq k).
Defined.

(* A variant in which the "bottom" map is pointed, and we take fibers over the base points. *)
Definition equiv_functor_hfiber_ispullback' {A B C D : Type}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h)
           (e : IsPullback p)
           (b : B) (d : D) (q : k b = d)
  : hfiber f b <~> hfiber g d.
Proof.
  refine (_ oE equiv_functor_hfiber_ispullback p e b).
  rapply (equiv_functor_hfiber2 (h:=equiv_idmap) (k:=equiv_idmap)).
  - reflexivity.
  - exact q.
Defined.

(* When [A] is (n+1)-connected, the inclusion of a point into [A] is n-connected, so this inclusion map is left-orthogonal to any n-truncated map.  By looking at the fibers of the canonical pullback square involving these two maps, we see that postcomposition by [f] gives an equivalence from [A ->* X] to [A ->* Y]. *)
Definition isconnequiv_truncmap `{Univalence} (n : trunc_index) {X Y : pType}
           (f : X ->* Y) `{IsTruncMap n _ _ f}
  : isconnequiv n.+1 f.
Proof.
  intros A C.
  unfold IsConnected in C.
  snapply isequiv_homotopic'.
  - (* We will write the given map as a composite of three maps.  On the ends, we have [pointed_maps_as_fiber] and its inverse.  In the middle, we use that the fibers of parallel maps in a pullback square are equivalent. *)
    refine ((pointed_maps_as_fiber A Y)^-1%equiv oE _ oE pointed_maps_as_fiber A X).
    refine (equiv_functor_hfiber_ispullback' _
             (ispullback_conn_modal (Tr n) (unit_name (point A)) f) _ _ _).
    exact (ap (fun y => unit_name y) (point_eq f)).
  - cbn.
    intro g.
    record_equality.
    + reflexivity.
    + cbn.
      pointed_reduce_pmap f.
      pointed_reduce_pmap g.
      refine ((concat_p1 _ @@ idpath) @ _).
      apply concat_Vp.
Defined.

(* BVR 6.2. *)
Definition isconnequiv_cover_proj `{Univalence} (n : trunc_index) (X : pType)
  : isconnequiv n.+1 (@cover_proj n.+1 X).
Proof.
  rapply isconnequiv_truncmap.
Defined.

(* Not used any more. *)
(* Add this to the library, after conn_point_elim. *)
Definition conn_point_elim_beta `{Univalence} (n : trunc_index) {A : pType@{u}} `{IsConnected n.+1 A}
           (P : A -> Type@{u}) `{forall a, IsTrunc n (P a)} (p0 : P (point A))
  : conn_point_elim n P p0 (point A) = p0.
Proof.
  unfold conn_point_elim.
  (* Since [Tr n (pt = pt)] is contractible, the center we chose is equal to [tr 1]. *)
  exact (ap _ (contr (tr 1))).
Defined.

(* TODO: Move elsewhere. *)
Definition pequiv_pmap_s0 `{Funext} (A : pType)
  : (psphere 0 ->** A) <~>* A.
Proof.
  snapply Build_pEquiv'.
  { snapply equiv_adjointify.
    + intro f; exact (f South).
    + intro a.
      snapply Build_pMap.
      { snapply Susp_rec.
        - exact (point _).  (* North, the basepoint of [psphere 0]. *)
        - exact a.          (* South. *)
        - contradiction. }
      reflexivity.
    + cbn; reflexivity.
    + intro f.
      rapply path_pforall.
      snapply Build_pHomotopy.
      { simpl.
        snapply Susp_ind; simpl.
        - symmetry; apply (point_eq f).
        - reflexivity.
        - contradiction. }
      simpl.
      cbn.
      symmetry; apply concat_1p. }
  reflexivity.
Defined.

(* TODO: Move elsewhere. *)
Definition pequiv_pmap_s0_nat `{Funext} (A B : pType) (f : A ->* B)
  : f o (pequiv_pmap_s0 A) == (pequiv_pmap_s0 B) o (fun g => f o* g).
Proof.
  intro x; reflexivity.
Defined.

(** If a map is a (-1)-connected-equivalence, then it is an equivalence, since the 0-sphere is (-1)-connected. *)
Definition isequiv_connequiv_minus_one `{Funext} {X Y : pType}
  (f : X ->* Y) (HE : isconnequiv minus_two.+1 f)
  : IsEquiv f.
Proof.
  napply isequiv_commsq.
  - symmetry. apply pequiv_pmap_s0_nat.
  - apply HE.  exact _.
  - exact _.
  - exact _.
Defined.

(** Taking loops shifts n down by 1. *)
Definition isconnequiv_loops `{Funext} {X Y : pType} (n : trunc_index)
           (f : X ->* Y) (HE : isconnequiv n.+1 f)
  : isconnequiv n (fmap loops f).
Proof.
  intros A C.
  napply isequiv_commsq.
  - intro g.
    apply path_pforall.
    srapply loop_susp_adjoint_nat_r.
    exact g.
  - rapply HE.  (* Typeclass resolution knows that the suspension of A is n+1 connected. *)
  - exact _.
  - exact _.
Defined.

Definition isconnequiv_iterated_loops `{Funext} {X Y : pType} (n : nat)
  (k : trunc_index) (f : X ->* Y) (HE : isconnequiv (trunc_index_inc' k n) f)
  : isconnequiv k (fmap (iterated_loops n) f).
Proof.
  revert k f HE.
  induction n; intros k f HE.
  - exact HE.
  - simpl in *.
    apply isconnequiv_loops.
    rapply IHn.
    exact HE.
Defined.

(** TODO: move elsewhere. *)
Definition trunc_index_inc'_zero (n : nat)
  : trunc_index_inc' 0 n = n.
Proof.
  induction n.
  - reflexivity.
  - refine (trunc_index_inc'_succ _ _ @ (ap _ IHn)).
Defined.

Definition isequiv_iterated_loops_connequiv `{Funext} {X Y : pType} (n : nat)
  (f : X ->* Y) (HE : isconnequiv n f)
  : IsEquiv (fmap (iterated_loops n.+1) f).
Proof.
  napply isequiv_connequiv_minus_one.
  apply isconnequiv_iterated_loops.
  refine (transport (fun k => isconnequiv k f) _ HE).
  symmetry; apply trunc_index_inc'_zero.
Defined.

Global Instance isequiv_iterated_loops_cover_proj `{Univalence}
  {n : nat} {Y : pType}
  : IsEquiv (fmap (iterated_loops n.+1) (@cover_proj n Y)).
Proof.
  rapply isequiv_iterated_loops_connequiv.
  rapply isconnequiv_cover_proj.
Defined.

