(* This is the top-level file in this development.  It uses the other files and shows that one can construct certain localizations that are not provably accessible. *)

Require Import HoTT.
(* This redundant line is so that we pick up the intended [factor1] and [factor2]. If Sets/Ordinals.v is changed, we can remove the next line. *)
Require Import HoTT.Factorization.

Require Import CORS.
Require Import Conn.
Require Import Smallness.
Require Import misc.

(* See Smallness.v for a discussion of universe variables. *)

(* If i <= j and [O] is a reflective subuniverse of [Type@{j}] such that when [X] is in [Type@{i}], [O X] is i-small, then [O] restricts to a reflective subuniverse of [Type@{i}]. This is Proposition 3.2 from the paper. *)
(* This only requires [Funext] because [O] is not assumed to unconditionally land in [HProp]s, so we can't resize the predicate defining the subuniverse unless we have [Funext].  One could also relax the requirement that the predicate lands in the universe [i]. *)
Definition restrict_O@{i j | i <= j} `{PropResizing} `{Funext}
           (O : ReflectiveSubuniverse@{j})
           (sX : forall X : Type@{i}, IsSmall@{i j} (O X))
  : ReflectiveSubuniverse@{i}.
Proof.
  snrapply Build_ReflectiveSubuniverse.
  - snrapply Build_Subuniverse.
    + exact (fun X => (smalltype@{i j} (In O X))).           (* The predicate on Type@{i}. *)
    + exact _.                                            (* It's an hprop, by [ishprop_resize_hprop]. *)
    + intros T U I f feq. cbn; cbn in I.                  (* It's replete. *)
      apply (equiv_smalltype _)^-1%equiv.
      srapply (inO_equiv_inO T f).
      apply (equiv_smalltype _).
      exact I.
  - intro X.
    snrapply Build_PreReflects.
    + exact (smalltype (O X)).                           (* The reflected type. *)
    + cbn.                                                (* It's in the new O. *)
      apply equiv_smalltype.
      srapply (inO_equiv_inO (O X) (equiv_smalltype (O X))^-1%equiv).
    + exact ((equiv_smalltype (O X))^-1%equiv o (to O X)).  (* The map from X to the reflected type. *)
  - intro X.                                              (* The universal property. *)
    snrapply Build_Reflects.
    intros Q Q_inO.
    cbn; cbn in Q_inO.
    nrapply ooextendable_compose.
    + rapply ooextendable_equiv.
    + rapply extendable_to_O'.
      exact ((equiv_smalltype _) Q_inO).
Defined.

Local Notation "n ..+2" := (trunc_index_to_nat n) (at level 2) : trunc_scope.

(* This just combines [restrict_O] and [issmall_n_image]. *)
Definition restrict_O'@{i j k u | i <= j, i < k, j <= k, k < u} `{PropResizing} `{Univalence}
           (n : trunc_index) (O : ReflectiveSubuniverse@{j})
           (C : forall X : Type@{i}, IsConnMap@{k} n (to O X))
           (L : forall X : Type@{i}, IsLocallySmall@{i j k} n..+2 (O X))
  : ReflectiveSubuniverse@{i}.
Proof.
  snrapply (restrict_O O).
  intro X.
  rapply issmall_n_image@{i j k u}.
Defined.

(* Given a family of maps, form the family with the map [S^{n+2} -> Unit] added. *)
Local Definition extended_generators@{j} (n : trunc_index)
      {I : Type@{j}} {A B : I -> Type@{j}} (f : forall i, A i -> B i)
  : LocalGenerators@{j}.
Proof.
  snrapply Build_LocalGenerators.
  - exact (sum@{j j} I Unit).
  - intros [i | u].
    + exact (A i).
    + exact (Sphere@{j} n.+2).
  - intros [i | u].
    + exact (B i).
    + exact Unit.
  - intros [i | u].
    + exact (f i).
    + exact (fun _ => tt).
Defined.

(* Being local with respect to the extended generating set is equivalent to being (n+1)-truncated and local with respect to the original family of maps. This could be generalized as in RSS Thm 3.29. *)
Definition islocal_extended_generators@{k} (n : trunc_index)
      {I : Type@{k}} {A B : I -> Type@{k}} (f : forall i, A i -> B i)
      (X : Type@{k})
  : IsLocal (extended_generators n f) X <-> IsLocal (Build_LocalGenerators _ _ _ f) X * IsTrunc n.+1 X.
Proof.
  destruct (istrunc_iff_sphere_oo_null@{k k k k k} n X)
    as [ooext_istrunc istrunc_ooext].
  split.
  - intro isLX.
    split.
    + intro a; cbn.
      exact (isLX (inl a)).
    + apply istrunc_ooext.
      rapply (@ooextendable_islocal _ _ _ (inr tt)).
  - intros [isLX isTrX].
    intros [a | b].
    + apply isLX.
    + cbn.
      apply ooext_istrunc; assumption.
Defined.

(* Given any family of n-connected maps in any universe [Type@{j}], one can localize in [Type@{i}] with respect to the extended family. This is Theorem 3.3 from the paper. Note that since localizations exist in all universes, we can remove the constraint that [i <= j]. *)
Definition nonaccessible_localization@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
           (n : trunc_index) {I : Type@{j}}
           {A B : I -> Type@{j}} (f : forall i, A i -> B i) (C : forall i, IsConnMap n (f i))
  : ReflectiveSubuniverse@{i}.
Proof.
  (* We first form the localization in a universe [k], with [i < k] and [j <= k].  Having [O] in the context helps at the end of the proof. *)
  pose (O := Loc@{k k} (extended_generators n f)).
  snrapply (restrict_O'@{i k k u} n O).
  - intro X.
    apply eta_connected_generators_connected_tr@{k k u}.
    intros [i | u].
    + cbn. apply lift_isconnmap_trunc@{j k}. apply C. 
    + cbn.
      apply conn_map_to_unit_isconnected@{k k}.
      apply isconnected_pred.
      nrapply isconnected_sn.
  - intro X.  (* All local types are (n+2)-locally small, since S^{n+2} -> Unit is a generator. *)
    apply islocallysmall_trunc.
    exact (snd (fst (islocal_extended_generators n f (O X)) _)).
Defined.

(* Here we just nail down the fact that the local objects are the n-truncated objects that are local with respect to the original family.  The only difference from [islocal_extended_generators] is that we have to handle the propositional resizing, and we state truncation in the universe [i] containing [X]. *)
Definition in_nonaccessible_localization@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
           (n : trunc_index) {I : Type@{j}}
           {A B : I -> Type@{j}} (f : forall i, A i -> B i) (C : forall i, IsConnMap n (f i))
           (X : Type@{i})
  : In (nonaccessible_localization@{i j k u} n f C) X <-> IsLocal (Build_LocalGenerators@{k} _ _ _ f) X * IsTrunc n.+1 X.
Proof.
  (* Get rid of propositional resizing on the LHS: *)
  (* cbn here shows the goal clearly, but makes the Defined slow. *)
  apply (iff_compose (iff_equiv (equiv_smalltype _))).
  apply (iff_compose (islocal_extended_generators n f X)).
  (* Change from [IsTrunc@{i}] to [IsTrunc@{k}]. *)
  nrapply iff_functor_prod.
  - split; exact idmap.
  - split; exact (@istrunc_equiv_istrunc _ _ equiv_idmap _).
Defined.

(* A special case of [nonaccessible_localization], which reproduces the Casacuberta-Scevenels-Smith result.  Associated to any family of surjective group homomorphisms, there is a localization onto the 1-types which are local with respect to the family. *)
Definition rsu_from_group_surjections@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
           (I : Type@{j}) (A B : I -> Group@{j}) (f : forall i, GroupHomomorphism (A i) (B i))
           (S : forall i, IsSurjection (f i))
  : ReflectiveSubuniverse@{i}.
Proof.
  snrapply (nonaccessible_localization@{i j k u} 0).
  4: exact (fun i => fmap pClassifyingSpace (f i)).
  intro i;
  apply isconn_map_functor_pclassifyingspace@{j u};
  apply S.
Defined.

(* If i <= j and [OFS] is a factorization system on [Type@{j}] such that when [f] is in [Type@{i}], the image is i-small, then [OFS] restricts to a factorization system on [Type@{i}]. *)
Definition restrict_OFS@{i j | i <= j} `{PropResizing} (OFS : FactorizationSystem@{j j j})
           (is : forall (X Y : Type@{i}) (f : X -> Y), IsSmall@{i j} (factor OFS f))
  : FactorizationSystem@{i i i}.
Proof.
  snrapply Build_FactorizationSystem.
  - intros X Y g; exact (smalltype@{i j} (class1 OFS g)).
  - exact _.
  - intros; simpl.
    apply (equiv_smalltype _)^-1.
    rapply class1_isequiv.
  - intros; simpl in *.
    apply (equiv_smalltype _)^-1.
    apply class1_compose; rapply (equiv_smalltype _); assumption.
  - intros X Y g; exact (smalltype@{i j} (class2 OFS g)).
  - exact _.
  - intros; simpl.
    apply (equiv_smalltype _)^-1.
    rapply class2_isequiv.
  - intros; simpl in *.
    apply (equiv_smalltype _)^-1.
    apply class2_compose; rapply (equiv_smalltype _); assumption.
  - intros X Y g.
    snrapply  Build_Factorization.
    + exact (smalltype (factor OFS g)).
    + exact ((equiv_smalltype _)^-1%equiv o (factor1 (factor OFS g))).
    + exact ((factor2 (factor OFS g)) o (equiv_smalltype _)).
    + intro x.
      refine ((ap _ _) @ _).
      * apply eisretr.
      * apply fact_factors.
    + apply (equiv_smalltype _)^-1.
      apply (class1_compose _ (factor1 _)).
      * apply inclass1.
      * rapply class1_isequiv.
    + apply (equiv_smalltype _)^-1.
      apply (class2_compose _ _ (factor2 _)).
      * apply class2_isequiv.
        (* Have to spell this out, or else Coq forces i = j for some reason: *)
        exact (equiv_isequiv (equiv_smalltype _)).
      * apply inclass2.
  - intros X Y f fact fact'.
    let T := type of fact in transparent assert (liftfact : (T -> Factorization@{j} (@class1 OFS) (@class2 OFS) f)).
    { intro facti; destruct facti.
      snrapply Build_Factorization; try assumption.
      all: apply (equiv_smalltype _); assumption. }
    destruct (path_factor OFS f (liftfact fact) (liftfact fact')).
    snrapply Build_PathFactorization; assumption.
Defined.

(* RSS Theorem 2.41, which I don't think has been formalized. *)
Definition OFS_from_family@{j} (f : LocalGenerators@{j})
  : FactorizationSystem@{j j j}.
Admitted.

(* Theorem 3.6 from the paper. The definition of OFS in the library is different from in the paper, so the proof needs to be slightly different.  In the paper, [L] is defined to be the class of maps in [Type@{i}] which are left orthogonal to [R], while here we define [L] to be the restriction of [L'] to [Type@{i}].  It follows that both definitions agree. *)
(* Unfortunately, the HoTT library is currently missing too many things for this to be fully formalized.  The notion of maps being orthogonal (the unique lifting property) has not been defined.  We also need that being right orthogonal to [S^{n+1} -> 1] implies being n-truncated (similar to istrunc_allnullhomot), and that being left orthogonal to the maps that are right orthogonal to a class of (n-1)-connected maps means you are (n-1)-connected. *)
Definition nonaccessible_OFS@{i j u} `{PropResizing} `{Univalence}
           (n : trunc_index) (I : Type@{j})
           (A B : I -> Type@{j}) (f : forall i, A i -> B i) (C : forall i, IsConnMap n (f i))
  : FactorizationSystem@{i i i}.
Proof.
  pose (OFS := OFS_from_family (extended_generators n f)).
  apply (restrict_OFS OFS).
  intros X Y g.
  snrapply (issmall_n_image n (factor1 (factor OFS g))).
  - admit.   (* Left factor is n-connected. *)
  - apply (islocallysmall_truncmap n (factor2 (factor OFS g))).
    + admit.  (* Right factor is (n+1)-truncated. *)
    + apply islocallysmall_in.
Admitted.
(* Need to add universe constraints when this is finished. *)
