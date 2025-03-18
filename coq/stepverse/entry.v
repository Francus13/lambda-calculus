(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                     Labels                                *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.

Require Coq.Sorting.Sorted.
Require Coq.Lists.List.

Set Implicit Arguments.

Declare Scope label_scope.
Delimit Scope label_scope with label.
Open Scope label_scope.

Class EqDec (A : Type) :=  {
  eqdec : forall(a b : A), {a = b} + {a <> b}
}.

Inductive entry (A : Type) : Type := 
   | Bot    : entry A                           (* unfinished *)
   | Val    : A -> entry A                      (* returned value *)
   | Wrong  : entry A                           (* runtime error *)
   | L      : entry A -> entry A                (* inside a left choice *)
   | R      : entry A -> entry A                (* inside a right choice *)
   | Br     : entry A -> entry A -> entry A     (* sequences choices *)
.

Arguments Bot {_}.
Arguments Val {_}.
Arguments Wrong {_}.
Arguments L {_}.
Arguments R {_}.
Arguments Br {_}.

(* Trying to require entry have its type A be an instance of EqDec *)
(*
Inductive entry (A : Type) (H : EqDec A) : Type := 
   | Bot    : entry H                          (* unfinished *)
   | Val    : A -> entry H                      (* returned value *)
   | Wrong  : entry H                           (* runtime error *)
   | L      : entry H -> entry H                (* inside a left choice *)
   | R      : entry H -> entry H                (* inside a right choice *)
   | Br     : entry H -> entry H -> entry H     (* sequences choices *)
.

Arguments Bot {_} {_}.
Arguments Val {_} {_}.
Arguments Wrong {_} {_}.
Arguments L {_} {_}.
Arguments R {_} {_}.
Arguments Br {_} {_}.
*)

(* 
    The first operand of Br should only have its labels inspected, not its result. 
    This is because Br is used for either:
    1) Intersection, where the results of both operands should be the same.
    2) Sequencing, where the first result should be thrown away.
*)

Module Entry.

    (* Compares labels of the entry *)
    Fixpoint compare {A} (l m : entry A) : comparison := 
    match l , m with 
    | Bot  , Bot  => Eq
    | Bot  , _    => Lt
    | _    , Bot  => Gt

    (* These Eqs are necessary for the match 
        in the Br case to work correctly *)
    | Val v1 , Val v2 => Eq 
    | Val v , Wrong => Eq
    | Wrong , Val v => Eq
    | Wrong , Wrong => Eq
    
    | L l0 , L m0 => compare l0 m0
    | R l0 , R m0 => compare l0 m0 
    | L _  , R _  => Lt
    | R _ , L _   => Gt

    | Br l1 l2 , Br l3 l4 => 
        match compare l1 l3 with
        | Eq => compare l2 l4
        | o  => o
        end

    (* these don't matter, we only compare comparable things *)
    | L _ , _  => Lt
    | _   , L _  => Gt
    | Val v , _ => Lt
    | _   , Val v => Gt
    | Wrong , _ => Lt
    | _   , Wrong => Gt
    | Br _ _ , _ => Lt
    | _   , Br _ _ => Gt
   
    end.

    (* Denotes if it means anything to compare the entrys' labels *)
    (* NOTE: As entries are refined, the entries they are 
        comparable with strictly decrease *)
    Fixpoint comparable {A} (l1 l2 : entry A) : bool :=
    match l1 , l2 with 
    | Bot  , _    => true
    | _    , Bot  => true

    | Val v1 , Val v2 => true
    | Val v1 , Wrong => true
    | Wrong , Val v2 => true
    | Wrong , Wrong => true

    | L l0 , L m0 => comparable l0 m0
    | R l0 , R m0 => comparable l0 m0 
    | L _  , R _  => true
    | R _ , L _   => true

    | Br l1 l2 , Br l3 l4 => comparable l1 l3 &&            
                                match compare l1 l3 with
                                | Eq => comparable l2 l4
                                | _  => true
                                end

    | _ , _ => false
    end.

  Definition eqb {A} (l m : entry A) : bool := 
    match compare l m with 
    | Eq => true
    | _ => false
    end.

  Definition ltb {A} (l m : entry A) : bool := 
    match compare l m with 
    | Lt => true
    | _ => false
    end.

  Definition leb {A} (l m : entry A) : bool := 
    match compare l m with 
    | Lt => true
    | Eq => true
    | _ => false
    end.

  (* During computation, a partial result have label "Bot". However, 
     if we give the evaluator more fuel, the expression may make 
     choices, so the label will grow more structure.

          Bot ⊑ L Bot
              ⊑ L (R Bot) 
              ⊑ L (R (Bot ⋈ Bot))
              ⊑ L (R (L Bot ⋈ Bot))
              ⊑ L (R (L Bot ⋈ R Bot))
   *)
  
  Fixpoint approxb {A : Type} `{EqDec A} (l1 l2 : entry A) : bool := 
    match l1 , l2 with 
    | Bot , _  => true
    | Val v1 , Val v2 => match eqdec v1 v2 with
                        | left _ => true 
                        | right _ => false
                        end
    | Wrong, Wrong => true
    | L l0 , L l1 => approxb l0 l1 
    | R l0 , R l1 => approxb l0 l1 
    | Br l1 l2 , Br l3 l4 => approxb l1 l3 && approxb l2 l4
    | _ , _ => false
    end.


  Lemma approxb_refl {A : Type} `{EqDec A} : forall l , approxb l l = true.
  Proof. induction l; auto. 
    -
    simpl.
    destruct eqdec; auto.
    -
    simpl. rewrite IHl1. rewrite IHl2. auto. Qed.

  (* Would there be a way to prove by induction on the approxb judgment? *)
  Lemma approxb_trans {A : Type} `{EqDec A} : forall l2 l1 l3, 
      approxb l1 l2 = true -> approxb l2 l3 = true -> approxb l1 l3 = true.
  Proof. induction l2; intros l1 l3. 
    all: destruct l1; destruct l3.
    all: simpl; intros h1 h2.
    all: try done. 
    -
    destruct eqdec in h1; destruct eqdec in h2; try done.
    rewrite e; rewrite e0.
    destruct eqdec; done.
    -
    rewrite IHl2; done.
    -
    rewrite IHl2; done.
    -
    apply andb_prop in h1; move: h1 => [h1 h1'];
    apply andb_prop in h2; move: h2 => [h2 h2'].
    (* Why does done not work here? *)
    apply andb_true_intro; split; eauto.
  Qed.



  (* comparison relations *)
  Definition lt {A} (l m : entry A) : Prop := ltb l m = true.
  Definition le {A} (l m : entry A) : Prop := leb l m = true.
  Definition eq {A} (l m : entry A) : Prop := eqb l m = true.
  Definition approx {A} `{EqDec A} (l m : entry A) : Prop := approxb l m = true.

Lemma approx_refl {A : Type} `{EqDec A} : forall x, approx x x.
Proof. intros x. unfold approx. apply approxb_refl. Qed.
 
Lemma approx_trans {A : Type} `{EqDec A} : forall l2 l1 l3, 
    approx l1 l2 -> approx l2 l3 -> approx l1 l3.
    (* Why does normal apply and auto not work? *)
Proof. unfold approx. intros. eapply approxb_trans; eauto. Qed.


Lemma compare_refl {A : Type} : forall x, @compare A x x = Eq.
Proof. induction x; simpl; eauto. rewrite IHx1. rewrite IHx2. done. Qed.


Lemma compare_antisymmetry {A : Type} : 
  forall x, (forall y, (compare x y = Lt <-> @compare A y x = Gt)
      /\ (compare x y = Eq <-> @compare A y x = Eq)).
Proof. induction x; intro y.
  all: split; split; intro h.
  all: destruct y eqn:Ey; simpl in *; try done.
    (* Why do the IHs become bound here? *)
    (* How would I apply IHx in the reverse direction? *)
    (* Why does "rewrite IHx in *" do nothing? *)
  all: try (destruct (IHx e)); 
          try destruct (IHx1 e1); try destruct (IHx2 e2).
  all: try rewrite H in h; try rewrite H; auto.
  all: try rewrite H0 in h; try rewrite H0; auto.
  all: try destruct (compare x1 e1) eqn:h1; try done.
  all: destruct (compare e1 x1) eqn: h2; try done.
  (* How to just simplify to contradiction? *)
  all : destruct H0; 
    try specialize (H0 eq_refl); try specialize (H3 eq_refl);
    try discriminate.
  all : destruct H; 
    try specialize (H eq_refl); try specialize (H4 eq_refl);
    try discriminate.
 -
 rewrite H1 in h; auto.
 -
 rewrite H1; auto.
 -
 rewrite H2 in h; auto.
 -
 rewrite H2; auto.
Qed.

Lemma compare_swap_lt {A : Type} : 
forall x y : entry A, compare x y = Lt -> compare y x = Gt.
Proof. intros. pose proof (compare_antisymmetry x y) as [[? _] _].
  auto. Qed.

Lemma compare_swap_gt {A : Type} : 
forall x y : entry A, compare x y = Gt -> compare y x = Lt.
Proof. intros. pose proof (compare_antisymmetry y x) as [[_ ?] _].
  auto. Qed.

Lemma compare_swap_eq {A : Type} : 
forall x y : entry A, compare x y = Eq -> compare y x = Eq.
Proof. intros. pose proof (compare_antisymmetry x y) as [_ [? _]].
  auto. Qed.


Lemma compare_transitive_eq {A : Type} : forall y x z : entry A,
  forall o, compare x y = Eq -> compare y z = o -> compare x z = o.
Proof.
  induction y; intros x z o h1 h2.
  all: destruct x; destruct z.
  all: simpl in *; subst; auto; try done.
  destruct (compare x1 y1) eqn: c1; try discriminate.
  destruct (compare y1 z1) eqn: c2;
    try rewrite (IHy1 _ _ _ c1 c2); try done.
  destruct (compare y2 z2) eqn: c3;
    try rewrite (IHy2 _ _ _ h1 c3); try done.
Qed.


Lemma compare_transitive_same {A : Type} : forall y x z : entry A,
forall o, compare x y = o -> compare y z = o -> compare x z = o.
Proof. 
  induction y; intros x z o h1 h2.
  all: destruct x; destruct z.
  all: simpl in *; subst; auto; try done.
  destruct (compare x1 y1) eqn: c1;
  destruct (compare y1 z1) eqn: c2;
    try rewrite (IHy1 _ _ _ c1 c2); try done.
  1: rewrite (IHy2 _ _ (compare x2 y2) eq_refl h2); done.
  all: try rewrite (compare_transitive_eq _ _ _ c1 c2); try done.
  1: apply compare_swap_lt in c1.
  2: apply compare_swap_gt in c1.
  all: apply compare_swap_eq in c2.
  1: rewrite (compare_swap_gt _ _ (compare_transitive_eq _ _ _ c2 c1)).
  2: rewrite (compare_swap_lt _ _ (compare_transitive_eq _ _ _ c2 c1)).
  all: done.
Qed.



Lemma ltb_irreflexive {A : Type} : forall x : entry A, 
  not (ltb x x = true).
intros x. unfold ltb. rewrite compare_refl. done. Qed.

Lemma ltb_transitive {A : Type} : forall x y z : entry A, 
  ltb x y = true -> ltb y z = true -> ltb x z = true.
intros x y z. unfold ltb. 
destruct (compare x y) eqn:h1; intro h; try discriminate; clear h.
destruct (compare y z) eqn:h2; intro h; try discriminate; clear h.
move: (compare_transitive_same _ _ _ h1 h2) => h3. rewrite h3. done.
Qed.

Lemma lt_irreflexive {A : Type} : forall x : entry A, not (lt x x).
Proof. intros x; unfold lt. apply ltb_irreflexive. Qed.

Lemma lt_transitive {A : Type} : forall x y z : entry A, 
  lt x y -> lt y z -> lt x z.
Proof. intros x y z; unfold lt. apply ltb_transitive. Qed.
  (* What is solve and intuition?
  OLD CODE: all: try solve [intuition]. *)

Lemma leb_L {A : Type} : forall l1 l1' : entry A,
  leb (L l1) (L l1') = true <-> leb l1 l1' = true.
Proof.
  split; unfold leb; simpl.
  all: destruct (compare l1 l1') eqn:E1.
  all: try done.
Qed.
  
Lemma leb_R {A : Type} : forall l1 l1' : entry A,
  leb (R l1) (R l1') = true <->
    leb l1 l1' = true.
Proof.
  split; unfold leb; simpl.
  all: destruct (compare l1 l1') eqn:E1.
  all: try done.
Qed.

Lemma leb_Br {A : Type} : forall l1 l1' l2 l2' : entry A,
  leb (Br l1 l2) (Br l1' l2') = true <->
    ((ltb l1 l1' = true) \/ (eqb l1 l1' = true /\ leb l2 l2' = true)).
Proof.
  split.
  -  unfold leb, ltb, eqb; simpl.
     all: destruct (compare l1 l1'); destruct (compare l2 l2'); auto.
  - unfold leb, ltb, eqb; intros [h1|h1]; simpl.
    all: destruct (compare l1 l1'); destruct (compare l2 l2');
      destruct h1; auto.
Qed.

Lemma leb_def {A : Type} : forall l1 l2 : entry A,
  leb l1 l2 = true <-> ltb l1 l2 = true \/ eqb l1 l2 = true.
Proof.
  intros l1 l2; unfold leb, ltb, eqb.
  destruct (compare l1 l2).
  all: split; auto.
  intro h; destruct h; auto.
Qed.

(* Proof not done, but I'm not sure the syntactic sugar is all that useful *)
(*
  Lemma le_transitive {A : Type} :  forall y x z : entry A,
      le x y -> le y z -> le x z.
  Proof. 
    induction y; intros x z h1 h2.
    all: destruct x; destruct z; simpl; try done.
    - unfold le in *. repeat rewrite leb_L in h1, h2; rewrite leb_L. auto.
    - unfold le in *. repeat rewrite leb_R in h1, h2. rewrite leb_R. eauto.  
    - unfold le in *. rewrite leb_Br.
      repeat rewrite leb_Br in h1, h2.
      destruct h1 as [h1 | [h1' h1]];
        destruct h2 as [h2 | [h2' h2]].
      left. unfold ltb in *.
      destruct (compare x1 y1) eqn:E1; destruct (compare y1 z1) eqn:E2; 
        destruct (compare x1 z1) eqn:E3.
      all: try done.
      1, 2: move: (compare_transitive_same _ _ _ E1 E2) => h; 
        rewrite h in E3; done.
      move: (compare_transitive_same _ _ _ E1 E2) => h. rewrite h in E3. done.     
  Qed.
*)


Lemma approxb_leb {A : Type} `{EqDec A} : forall l1 l2 : entry A,
    approxb l1 l2 = true -> leb l1 l2 = true.
Proof. 
  induction l1; intros l2; destruct l2; simpl; try done.
  - rewrite leb_L; auto.
  - rewrite leb_R; auto.
  - rewrite leb_Br.
      intros h; rewrite Bool.andb_true_iff in h; destruct h.
      apply IHl1_1 in H0; apply IHl1_2 in H1.
      rewrite leb_def in H0; destruct H0; auto.
  Qed.

  Lemma approxb_le {A : Type} `{EqDec A} : forall l1 l2 : entry A,
      approxb l1 l2 = true -> le l1 l2.
  Proof. intros. unfold le. eapply approxb_leb. auto. Qed.

Lemma eqb_symmetry {A : Type} : forall l1 l2 : entry A,
  eqb l1 l2 = true -> eqb l2 l1 = true.
Proof.
  unfold eqb; intros l1 l2 h. 
  destruct (compare l1 l2) eqn: h1; try done. 
  apply compare_swap_eq in h1; rewrite h1; done.
Qed.

(*
Lemma leb_antisymmetry {A : Type} : forall l1 l2 : entry A,
  leb l1 l2 = true -> leb l2 l1 = true -> eqb l1 l2.
Proof. 
  unfold leb.
Admitted.

Lemma bot_min k : 
  Label.leb Bot k = true.
Proof. 
  destruct k; cbv; auto.
Qed.

Lemma approx_leb k k1 k2 :
  Label.leb k k1 = true -> 
  Label.approx k1 k2 -> Label.leb k k2 = true.
Proof.
  intros.
  unfold Label.approx in H0.
  apply Label.approxb_leb in H0.
  move: (@Label.le_transitive k1 k k2) => h. unfold Label.le in h. eauto.
Qed.

Lemma leb_transitive k1 k2 k3 : 
  Label.leb k1 k2 = true -> Label.leb k2 k3 = true -> Label.leb k1 k3 = true.
Admitted.

Lemma leb_swap l1 l2 : Label.leb l1 l2 = false -> Label.leb l2 l1 = true.
Proof.
  unfold Label.leb.
Admitted.
*)

End Entry.


