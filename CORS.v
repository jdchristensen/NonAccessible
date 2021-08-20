Require Import HoTT.
(* This redundant line is so that we pick up the intended [image]. If Sets/Ordinals.v is changed, we can remove the next line. *)
Require Import HoTT.Modalities.Modality.

Require Import OFS.
Require Import Conn.

(** Lemma 3.11 from CORS says:

Definition inO_domain_map_in_R (factsys : FactorizationSystem)
           (f : LocalGenerators) (fL : forall i, class1 factsys (f i))
           {C D : Type} (Df : IsLocal f D)
           (r : C -> D) (rR : class2 factsys r)
           : IsLocal f C.

Unfortunately, the library doesn't have the unique lifting property for an OFS (RSS Lemma 1.44), and the proof is fairly long. So, I instead prove a very closely related result below, [inO_domain_mapinO]. 

Similarly, [eta_connected_generators_connected] below is closely related to CORS, Theorem 3.12. *)

(** The type of lifts in a commuting square. *)
Definition lifts {A B C D : Type}
           {c : A -> B} {m : C -> D}
           {f : A -> C} {g : B -> D} (S : m o f == g o c)
  := {h : B -> C & { H1 : h o c == f & { H2 : m o h == g & forall a, (ap m (H1 a)) @ (S a) = H2 (c a) } } }.

(** First we show that [lift(S)] is equivalent to a certain type of sections. *)

Definition equiv_lifts_sections `{Funext} {A B C D : Type}
           {c : A -> B} {m : C -> D}
           {f : A -> C} {g : B -> D} (S : m o f == g o c)
  : lifts S <~> { l : forall b : B, hfiber m (g b) & forall a, l (c a) = (f a; S a) }.
Proof.
  (* We start with two adjustments to the the codomain: *)
  refine (_ oE _).
  1: apply (equiv_functor_sigma_pb (equiv_sig_coind _ _)).
  cbn.
  equiv_via { h : B -> C & { H2 : m o h == g & forall a, (h (c a); H2 (c a)) = (f a; S a) :> {c0 : C & m c0 = g (c a)}}}.
  2: make_equiv.
  (* We strip off the outer layer: *)
  unfold lifts.
  snrapply equiv_functor_sigma_id; intro h; cbn.
  (* Rearrange the domain sigma type: *)
  refine (_ oE equiv_sigma_symm _).
  (* Strip off the outer layer: *)
  snrapply equiv_functor_sigma_id; intro H2; cbn.
  (* Apply path_sigma inside the codomain and then equiv_forall_sigma: *)
  refine (_ oE _).
  { nrapply equiv_functor_forall_id.  (* [Funext] is used here. *)
    intro a.
    apply equiv_path_sigma. }
  refine (equiv_sig_coind _ _ oE _); cbn.
  (* Strip off the outer layer: *)
  snrapply equiv_functor_sigma_id; intro H1; cbn.
  (* Handle the innermost types, focusing on the codomain: *)
  snrapply equiv_functor_forall_id; intro a; cbn.
  refine (equiv_concat_l _ _ oE _).
  1: apply transport_paths_Fl.
  refine (equiv_path_inverse _ _ oE _).
  apply equiv_moveL_Vp.
Defined.

(** This is the unique lifting property for connected and modal maps, which holds even though they don't necessarily form an OFS. *)
Definition unique_lifting_conn_modal `{Funext} (O : ReflectiveSubuniverse)
           {A B C D : Type}
           (c : A -> B) `{IsConnMap O _ _ c}
           (m : C -> D) `{MapIn O _ _ m}
           (f : A -> C) (g : B -> D) (S : m o f == g o c)
  : Contr (lifts S).
Proof.
  nrapply contr_equiv'.
  1: symmetry; apply equiv_lifts_sections.
  snrapply (contr_equiv' (hfiber (fun (l : forall b, hfiber m (g b)) => l oD c) (fun a => (f a; S a)))).
  2: { apply contr_map_isequiv.
       nrapply (isequiv_o_conn_map O).
       - assumption.
       - exact (fun b => H1 (g b)). }
  unfold hfiber.
  snrapply equiv_functor_sigma_id; intro l; cbn.
  symmetry.
  apply equiv_path_forall.
Defined.

(** If a type has unique extensions against the generators, it is local.  This is probably just repeating things to do with ooExtendableAlong... *)
Lemma islocal_unique_extension `{Funext}
      (f : LocalGenerators) (X : Type)
      (E : forall i (h : lgen_domain f i -> X), Contr { g : lgen_codomain f i -> X & g o (f i) == h })
  : IsLocal f X.
Proof.
  intro i.
  set (A := lgen_domain f i) in *.
  set (B := lgen_codomain f i) in *.
  apply (equiv_ooextendable_isequiv _ _)^-1.
  apply isequiv_contr_map.
  intro h.
  unfold hfiber.
  nrapply (@contr_equiv' _ _ _ (E i h)).
  - snrapply equiv_functor_sigma_id.
    intro g.
    rapply equiv_path_forall.
Defined.

(** And the converse. *)
Lemma unique_extension_islocal `{Funext}
      (f : LocalGenerators) (X : Type) (L : IsLocal f X)
  : forall i (h : lgen_domain f i -> X), Contr { g : lgen_codomain f i -> X & g o (f i) == h }.
Proof.
  intros i h.
  nrapply contr_equiv'.
  - nrapply equiv_functor_sigma_id.
    intro g; cbn.
    apply equiv_ap10.
  - apply contr_map_isequiv.
    rapply isequiv_ooextendable.
    apply L.
Defined.

(** A specific lemma about contractible sigma types that comes up below. *)
Lemma contr_sigma2_contr {A : Type} {B : A -> Type}
           (C : forall a (b : B a), Type)
           (s : forall a b, C a b)
           (H : Contr { a : A & { b : B a & C a b } })
  : Contr { a : A & B a }.
Proof.
  snrapply (@contr_retract _ _ H).
  - intros [a [b c]].  exact (a; b).
  - intros [a b].  exact (a; b; s a b).
  - reflexivity.
Defined.

(** A specific lemma about transporting homotopies that comes up below. *)
Lemma transport_homotopy {A B C : Type}
      (f : A -> B) (g h : B -> C) (k : A -> C)
      (K : g = h) (H : g o f == k) (a : A)
  : transport (fun w : B -> C => w o f == k) K H a = (ap10 K (f a))^ @ H a.
Proof.
  induction K; cbn.
  symmetry; apply concat_1p.
Defined.

(** Special case of the CORS result mentioned above, Lemma 3.11, for the connected/modal maps for a modality [O]. In fact, it works for any reflective subuniverse [O], even though the connected and modal maps don't form an OFS. *)
(** It might be possible to remove Funext. *)
Definition inO_domain_mapinO `{Funext} (O : ReflectiveSubuniverse)
           (f : LocalGenerators) (fL : forall i, IsConnMap O (f i))
           {C D : Type} (Df : IsLocal f D)
           (r : C -> D) (rR : MapIn O r)
  : IsLocal f C.
Proof.
  apply islocal_unique_extension.
  intros i h.
  (* Since [D] is [f]-local, [r o h] has a unique extension we'll call [k].  Extract that info. *)
  (* (We choose the order of our set and pose tactics so that later things simplify earlier things.) *)
  pose proof (UE := unique_extension_islocal f D Df i (r o h)).
  pose proof (UEcontr := @contr _ UE).
  set (UEcenter := @center _ UE) in *.
  set (k := UEcenter.1) in *.
  pose (Sr := UEcenter.2 : k o f i == r o h).
  pose (S := (fun a => (Sr a)^)).
  (* Introduce notation to make things more readable. *)
  set (A := lgen_domain f i) in *.
  set (B := lgen_codomain f i) in *.
  (* [S] gives us a commuting square, so the type of lifts is unique. We'll show that the type in our goal is a retract of the type of lifts. *)
  pose proof (UL := unique_lifting_conn_modal _ _ _ _ _ S).
  refine (contr_sigma2_contr _ _ UL).
  (* Again, more cleanup. *)
  change (forall (g : B -> C) (H1 : g o f i == h), {H2 : r o g == k & forall a : A, ap r (H1 a) @ S a = H2 (f i a)}).
  (* We have to show that any extension [g] of [h] along [f i] can be extended into a lift in the square [S]. *)
  intros g H1.
  transparent assert (S' : (r o g o f i == r o h)).
  1: exact (fun a => ap r (H1 a)).
  (* S' shows that r o g is another extension of r o h through fi, so it must equal k: *)
  pose proof (UEcontr' := (equiv_path_sigma _ _ _)^-1 (UEcontr (r o g; S'))); clear UEcontr.
  destruct UEcontr' as [contr1 contr2].
  change (k = r o g) in contr1.
  change (transport (fun k : B -> D => k o f i == r o h) contr1 Sr = S') in contr2.
  srefine (_; _).
  - symmetry.
    exact (ap10 contr1).
  - cbn beta.
    intro a.
    change (ap r (H1 a)) with (S' a).
    refine (_ @@ 1 @ _).
    1: exact ((apD10 contr2 a)^ @ transport_homotopy (f i) k (r o g) (r o h) contr1 Sr a).
    apply concat_pp_V.
Defined.

(* A sort of naturality result for [O_indpaths], stated in two ways. *)
(* This version not used. *)
Definition O_indpaths_path (O : ReflectiveSubuniverse) {P Q : Type}
           `{In O Q}
           (g h : O P -> Q)
           (p : g o (to O P) == h o (to O P))
           (x y : O P) (q : x = y)
    : (O_indpaths g h p x) @ (ap h q) = (ap g q) @ (O_indpaths g h p y).
Proof.
  induction q; cbn.
  exact (concat_p1 _ @ (concat_1p _)^).
Defined.

(* This version is used below.  Is it already in the library somewhere? *)
Definition O_indpaths_path' (O : ReflectiveSubuniverse) {P Q : Type}
           `{In O Q}
           (g h : O P -> Q)
           (p : g o (to O P) == h o (to O P))
           {x y : O P} (q : x = y)
    : (O_indpaths g h p x) = (ap g q) @ (O_indpaths g h p y) @ (ap h q)^.
Proof.
  induction q; cbn.
  exact ((concat_1p _)^ @ (concat_p1 _)^).
Defined.
    
(* If the generators of a localization are O-connected for some modality O, then the eta maps are O-connected as well.  This is a special case of CORS, Theorem 3.12, where we assume that the factorization system comes from a modality. *)
Definition eta_connected_generators_connected@{j k u | j <= k, k < u} `{Univalence}
           (O : Modality@{k})
           (f : LocalGenerators@{j}) (C : forall i, IsConnMap@{k} O (f i))
  : forall X : Type@{j}, IsConnMap@{k} O (to (Loc@{j j} f) X).
Proof.
  intro X.
  set (eta := to (Loc f) X).
  (** To prove that [eta] is [O]-connected, we factor it as [r o l], where [l] is [O]-connected by definition, and where [r] can be shown to be an equivalence. *)
  pose (fact := image@{k j j j j j j} O eta).
  set (factsave := fact).
  destruct fact as [I l r h lOconn rinO].
  snrapply (conn_map_homotopic O (r o l) eta h).
  snrapply conn_map_compose.
  1: exact lOconn.
  snrapply conn_map_isequiv@{k k j j j}.
  (** We prove some of isequiv_adjointify here, as [k] gets used in two branches. *)
  (** This is a "no typeclasses" form of [transparent assert], which is faster here: *)
  snrefine (let l' := (_ : O_reflector (Loc f) X -> I) in _).
  1: exact _.
  { (* We use [Localize_rec] rather than [O_rec], as this lets us eliminate into [I], which is in a possibly larger universe. *)
    rapply (Localize_rec@{j j k k k k} f l).
    rapply (inO_domain_mapinO@{k k k j j k j j j j j k k k k k k k k k j} _ _ _ _ r). }
  snrefine (let k := (_ : r o l' == idmap) in _).
  { apply O_indpaths. exact h. }
  snrapply (isequiv_adjointify r l' k).
  snrapply (homotopic_filler_idmap@{k k u u u} (O_factsys@{k k k k k k k k k} O) eta factsave); cbn.
  - intro x.
    exact (ap l' (h x)).
  - intro i; exact (k (r i))^.
  - simpl.
    intro x.
    refine ((_ @@ 1) @ (concat_1p (h x))).
    apply isequiv_moveL_M1.  (* This coerces to the inverse function. *)
    unfold k.
    nrefine (_ @ (O_indpaths_path' _ _ _ _ (h x))^).
    refine (_ @ concat_p_pp _ _ _).
    refine ((concat_p1 _)^ @ (_ @@ _)).
    1: symmetry; apply (ap_compose l' r (h x)).
    refine (_ @ (_^ @@ 1)).
    2: nrapply O_indpaths_beta.
    refine ((concat_pV (h x))^ @ _).
    refine (1 @@ _).
    apply ap.
    symmetry; apply ap_idmap.
Defined.

(** Special case for [n]-truncation. Because [n]-truncation is defined for all universe levels, we can change the hypothesis [C] to use the more natural universe level [j]. *)
Definition eta_connected_generators_connected_tr@{j k u | j <= k, j < u} `{Univalence}
           (n : trunc_index) (f : LocalGenerators@{j}) (C : forall i, IsConnMap@{j} n (f i))
  : forall X : Type@{j}, IsConnMap@{k} n (to (Loc@{j j} f) X).
Proof.
  intro X.
  apply lift_isconnmap_trunc@{j k}. 
  rapply eta_connected_generators_connected@{j j u}.
Defined.
