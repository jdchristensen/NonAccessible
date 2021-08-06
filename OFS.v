(* Some things about orthogonal factorization systems. *)

Require Import HoTT.
(* This redundant line is so that we pick up the intended [factor1] and [factor2]. If Sets/Ordinals.v is changed, we can remove the next line. *)
Require Import HoTT.Factorization.

Definition isequiv_in_left_and_right (F : FactorizationSystem)
           {X Y : Type} (f : X -> Y)
           (left : class1 F f) (right : class2 F f)
  : IsEquiv f.
Proof.
  transparent assert (fact1 : (Factorization (@class1 F) (@class2 F) f)).
  { snrapply (Build_Factorization Y f equiv_idmap).
    - reflexivity.
    - assumption.
    - rapply class2_isequiv. }
  transparent assert (fact2 : (Factorization (@class1 F) (@class2 F) f)).
  { snrapply (Build_Factorization X equiv_idmap f).
    - reflexivity.
    - rapply class1_isequiv.
    - assumption. }
  pose (PF := path_factor F f fact1 fact2).
  destruct PF.
  cbn in *.
  srapply isequiv_adjointify.
  - exact path_intermediate.
  - symmetry; exact path_factor2.
  - exact path_factor1.
Defined.  
(* Note that we didn't use that path_intermediate is an equivalence. *)

(** The hypotheses are almost the same as a PathFactorization between fact and fact'.  The main difference is that we do not assume that path_intermediate is an equivalence.  We also don't need [path_fact_factors]. *)
Definition isequiv_path_factorization `{Univalence} (F : FactorizationSystem)
           {X Y : Type} (f : X -> Y)
           (fact fact' : Factorization (@class1 F) (@class2 F) f)
           (path_intermediate : intermediate fact -> intermediate fact')
           (path_factor1 : path_intermediate o factor1 fact == factor1 fact')
           (path_factor2 : factor2 fact == factor2 fact' o path_intermediate)
  : IsEquiv path_intermediate.
Proof.
  nrapply (isequiv_in_left_and_right F).
  - snrapply (cancelR_class1 _ (factor1 fact)).
    + apply inclass1.
    + refine (transport (fun g => class1 F g) (path_forall _ _ path_factor1)^ _).
      apply inclass1.
  - snrapply (cancelL_class2 _ _ (factor2 fact')).
    + apply inclass2.
    + refine (transport (fun g => class2 F g) (path_forall _ _ path_factor2) _).
      apply inclass2.
Defined.

(* u u0 u1 u2 u3 |= u0 <= u < {u1,u2} <= u3.  E.g. i i j j j. *)
Definition homotopic_filler_idmap `{Univalence} (F : FactorizationSystem)
           {X Y : Type} (f : X -> Y)
           (fact : Factorization (@class1 F) (@class2 F) f)
           (path_intermediate' : intermediate fact -> intermediate fact)
           (path_factor1' : path_intermediate' o factor1 fact == factor1 fact)
           (path_factor2' : factor2 fact == factor2 fact o path_intermediate')
           (path_fact_factors' : forall a, path_factor2' (factor1 fact a)
                                                    @ ap (factor2 fact) (path_factor1' a)
                                                    @ fact_factors fact a
                                      = fact_factors fact a)
  : path_intermediate' == idmap.
Proof.
  apply ap10.
  transparent assert (eq : (intermediate fact <~> intermediate fact)).
  { snrapply (Build_Equiv _ _ path_intermediate').
    apply isequiv_path_factorization; assumption. }
  transparent assert (PF : (PathFactorization fact fact)).
  { snrapply (Build_PathFactorization _ _ eq); assumption. }
  transparent assert (PF' : (PathFactorization fact fact)).
  { snrapply (Build_PathFactorization _ _ equiv_idmap).
    1, 2: reflexivity.
    intro a. apply concat_1p. }
  nrefine (@ap _ _ equiv_fun eq equiv_idmap _).
  nrefine (@ap _ _ path_intermediate PF PF' _).
  nrapply path_contr.
  nrefine (contr_equiv' _ _).
  1: exact (equiv_path_factorization fact fact)^-1%equiv.
  nrapply contr_paths_contr.
  exact (contr_factor F f).
Defined.
