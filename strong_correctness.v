
Require Import Arith.   (* For natural numbers and arithmetic operations *)
Require Import ZArith.  (* Imports the integer arithmetic library *)
Require Import Lia.
Require Import Ring.
Require Import Znumtheory. (* For Z.mul_mod property *)
Require Import ssreflect.

Open Scope Z_scope. (* Allows using infix notation like `mod`, `/`, `*` for integers *)

Section NatMod.
Context (N : nat) (N_pos : (N > 0)%nat).

Lemma N_pos': 0<Z.of_nat N. Proof. lia. Qed.
Lemma N_pos'': Z.of_nat N>0. Proof. lia. Qed.
Lemma N_pos''': Z.of_nat (2*N)>0. Proof. lia. Qed.

(* FIRST DEFINITION: clear for human *)

(* DEFINITIONS OF SETS *)

(* Definition of the type representing the set {0, ..., n-1} *)
Definition Fin (n : nat) : Set :=
    { x : Z | 0 <= x < Z.of_nat n }.

(* definition useful type (sets...) *)
Definition SetN : Type := Fin N.
Definition Set2N : Type := Fin (2 * N).
Definition ScheduleType : Type := Set2N -> SetN -> SetN.

(* definition equality *)
Definition Fin_eq (n : nat) (x y : Fin n) : Prop :=
    proj1_sig x = proj1_sig y.

(* project to fin: Z -> Fin *)
Theorem modulo_lt_divisor : forall x n : Z, (n > 0) -> 0 <= (x mod n) < n.
Proof.
    intros x n Hpos.
    apply Z.mod_pos_bound.
    lia.
Qed.
Definition project_to_Fin (x : Z) : Fin N :=
    exist (fun y : Z => 0 <= y < Z.of_nat N) (x mod (Z.of_nat N)) (modulo_lt_divisor x (Z.of_nat N) (N_pos'')).
Definition project_to_Fin2 (x : Z) : Fin (2*N) :=
    exist (fun y : Z => 0 <= y < Z.of_nat (2*N)) (x mod (Z.of_nat (2*N))) (modulo_lt_divisor x (Z.of_nat (2*N)) (N_pos''')).



(* DEFINITIONS OF BIJECTION *)

Definition injective (f : ScheduleType) : Prop :=
    forall g : Set2N, forall t1 t2 : SetN, Fin_eq _ (f g t1) (f g t2) -> Fin_eq _ t1 t2.
Definition surjective (f : ScheduleType) : Prop :=
    forall g : Set2N, forall a : SetN, exists (t : SetN), Fin_eq _ (f g t) a.
Definition bijective (f : ScheduleType) : Prop :=
    injective f /\ surjective f.



(* DEFINITIONS OF NB_BY_WORKSHOP *)

(* 2 group per activity at each time *)
Definition at_least_2_by_workshop (f : ScheduleType) : Prop :=
    forall a t : SetN, exists g1 g2 : Set2N, Fin_eq _ (f g1 t) a /\ Fin_eq _ (f g2 t) a /\ ~(Fin_eq _ g1 g2).
Fixpoint cpt_group_by_act (f:ScheduleType) (g:nat) (a:SetN) (t:SetN) (cpt:Z) {struct g} : Z :=
  match g with
  | 0%nat => cpt
  | S g' => if proj1_sig (f (project_to_Fin2 (Z.of_nat g')) t) =? proj1_sig a then cpt_group_by_act f g' a t (cpt+1)
    else cpt_group_by_act f g' a t cpt
  end.
Definition exactly_2_by_workshop (f : ScheduleType) : Prop :=
    forall a t : SetN, cpt_group_by_act f (2*N) a t 0 = 2.



(* DEFINITIONS OF NO RECURING ENCOUNTER *)

(* no recuring encounter *)
Definition no_rec_enc (f : ScheduleType) : Prop :=
    forall g1 g2 : Set2N, forall t1 t2 : SetN, Fin_eq _ (f g1 t1) (f g2 t1) -> Fin_eq _ (f g1 t2) (f g2 t2) -> Fin_eq _ t1 t2 \/ Fin_eq _ g1 g2.



(* FINAL DEFINITIONS *)

(* definition for proof *)
Definition fin_eq_equality (f:ScheduleType) : Prop :=
    forall (g1 g2:Set2N) (t:SetN), Fin_eq _ g1 g2 -> Fin_eq _ (f g1 t) (f g2 t).

Definition perfect_schedule_weak (f : ScheduleType) : Prop :=
    fin_eq_equality f /\ no_rec_enc f /\ at_least_2_by_workshop f /\ injective f.
(* definition for correctness *)
Definition perfect_schedule_strong (f : ScheduleType) : Prop :=
    no_rec_enc f /\ exactly_2_by_workshop f /\ bijective f.




(* PROOF EQUIVALENCE *)

(* inj -> surj *)
(* count img reciproque : #{j<i | } *)
Fixpoint collision (f:ScheduleType) (g:Set2N) (a:SetN) (i:nat) (cpt:Z) {struct i} : Z :=
  match i with
  | 0%nat => cpt
  | S i' => if proj1_sig (f g (project_to_Fin (Z.of_nat i'))) =? proj1_sig a then collision f g a i' (cpt+1)
    else collision f g a i' cpt
  end.

Lemma collision_eq_1_to_exists: forall f : ScheduleType, forall g : Set2N, forall a : SetN, forall k: nat, collision f g a k 0 >= 1 -> exists t:Z, 0<=t<Z.of_nat k /\ proj1_sig (f g (project_to_Fin t)) = proj1_sig a.
Proof.
    intros.
    induction k.
    - exfalso. unfold collision in H. lia.
    - destruct (proj1_sig (f g (project_to_Fin (Z.of_nat k))) =? proj1_sig a) eqn:H_test.
      * exists (Z.of_nat k). lia.
      * simpl in H. rewrite H_test in H.
        apply IHk in H. destruct H. exists x. lia.
Qed.

Lemma aux_add_res: forall (f:ScheduleType) (g:Set2N) (a:SetN) (k:nat), forall (res:Z), collision f g a k res = collision f g a k 0 + res.
Proof.
    intros f g a k. induction k; intro.
    - reflexivity.
    - simpl. destruct (proj1_sig (f g (project_to_Fin (Z.of_nat k))) =? proj1_sig a) eqn:H_test; setoid_rewrite IHk; lia.
Qed.

Lemma collision_eq_2_to_exists: forall f : ScheduleType, forall g : Set2N, forall a : SetN, forall k: nat, collision f g a k 0 >= 2 -> exists t t':Z, 0 <= t' < t /\ t < Z.of_nat k /\ proj1_sig (f g (project_to_Fin t)) = proj1_sig a /\ proj1_sig (f g (project_to_Fin t')) = proj1_sig a.
Proof.
    intros.
    induction k.
    - exfalso. unfold collision in H. lia.
    - destruct (proj1_sig (f g (project_to_Fin (Z.of_nat k))) =? proj1_sig a) eqn:H_test.
      * assert (collision f g a k 0 >= 1). simpl in H. rewrite H_test in H. rewrite aux_add_res in H. lia.
        apply collision_eq_1_to_exists in H0. destruct H0.
        exists (Z.of_nat k). exists x. lia.
      * simpl in H. rewrite H_test in H.
        apply IHk in H. destruct H as [t [t' H]]. exists t. exists t'. lia.
Qed.

Lemma collision_leq_one: forall f:ScheduleType, injective f -> (forall (g:Set2N) (a:SetN), collision f g a (N) 0 <= 1).
Proof.
    intros.
    destruct (collision f g a (N) 0 <=? 1) eqn:H_dij.
    - lia.
    - exfalso.
      assert (collision f g a (N) 0 >= 2). lia. clear H_dij.
      unfold injective in H. specialize (H g).
      apply collision_eq_2_to_exists in H0. destruct H0 as [t1 [t2 [[HA HB] [HC [HD HE]]]]].
      specialize (H (project_to_Fin t1) (project_to_Fin t2)).
      unfold Fin_eq in H. rewrite HD in H. rewrite HE in H. simpl in H.
      assert (t1 mod Z.of_nat N = t2 mod Z.of_nat N). apply H. reflexivity.
      rewrite Z.mod_small in H0. lia.
      rewrite Z.mod_small in H0. lia.
      lia.
Qed.

(* sum all img reciproque : sum_a #{j<i | } *)
Fixpoint sum_collision_aux (f:ScheduleType) (g:Set2N) (a:nat) (cpt:Z) (k:nat) {struct a} : Z :=
  match a with
  | 0%nat => cpt
  | S a' => sum_collision_aux f g a' (cpt + collision f g (project_to_Fin (Z.of_nat a')) k 0) k
  end.
Fixpoint sum_collision (f:ScheduleType) (g:Set2N) (a:nat) (cpt:Z) {struct a} : Z :=
  match a with
  | 0%nat => cpt
  | S a' => sum_collision f g a' (cpt + collision f g (project_to_Fin (Z.of_nat a')) (N) 0)
  end.

Fixpoint collision' (f:ScheduleType) (g:Set2N) (a:nat) (i:nat) (cpt:Z) {struct a} : Z :=
  match a with
  | 0%nat => cpt
  | S a' => if proj1_sig (f g (project_to_Fin (Z.of_nat i))) =? Z.of_nat a' then collision' f g a' i (cpt+1)
    else collision' f g a' i cpt
  end.
Fixpoint sum_collision_aux' (f:ScheduleType) (g:Set2N) (a:nat) (i:nat) (cpt:Z) {struct i} : Z :=
  match i with
  | 0%nat => cpt
  | S i' => sum_collision_aux' f g a i' (cpt + collision' f g a i' 0)
  end.
Lemma aux_add_res': forall (f:ScheduleType) (g:Set2N) (a:nat) (t:nat), forall (res:Z), collision' f g a t res = collision' f g a t 0 + res.
Proof.
    intros f g a. induction a; intros.
    - reflexivity.
    - simpl. destruct (proj1_sig (f g (project_to_Fin (Z.of_nat t))) =? Z.of_nat a) eqn:H_test; setoid_rewrite IHa; lia.
Qed.
Lemma aux_coll_eq_one:  forall (f:ScheduleType) (g:Set2N) (t:nat), collision' f g N t 0 = 1.
Proof.
    (* collision' f g N k 0 = 1: easy to see: parcours all activity for a given time: ok: show  collision' f g N k 0 = 1 *)
    intros.
    assert (forall t:SetN, exists a:SetN, proj1_sig (f g t) = proj1_sig a). intro. exists (f g t0). reflexivity.
    assert (forall (a:nat) (res:Z), Z.of_nat a <= proj1_sig (f g (project_to_Fin (Z.of_nat t))) -> collision' f g a t res = res).
    {
        induction a.
        - reflexivity.
        - intros. simpl.
          replace (proj1_sig (f g (project_to_Fin (Z.of_nat t))) =? Z.of_nat a) with false by lia.
          apply IHa. lia.
    }

    assert (forall a:nat, Z.of_nat a = proj1_sig (f g (project_to_Fin (Z.of_nat t)))+1 -> collision' f g a t 0 = 1).
    intros. simpl.
    assert (exists a', a=S a').
    {
      destruct a.
        - exfalso. destruct (f g (project_to_Fin (Z.of_nat t))). simpl in H1. lia.
        - exists a. reflexivity.
    }
    destruct H2. rewrite H2. simpl.
    replace (proj1_sig (f g (project_to_Fin (Z.of_nat t))) =? Z.of_nat x) with true by lia.
    apply H0. lia.

    assert (forall a:nat, Z.of_nat a > proj1_sig (f g (project_to_Fin (Z.of_nat t)))+1 -> collision' f g a t 0 = 1).
    {
        induction a.
        - destruct ((f g (project_to_Fin (Z.of_nat t)))). simpl. lia.
        - destruct (Z.of_nat a >? proj1_sig (f g (project_to_Fin (Z.of_nat t))) + 1) eqn:H_init.
          + intros. simpl.
            replace (proj1_sig (f g (project_to_Fin (Z.of_nat t))) =? Z.of_nat a) with false by lia.
            apply IHa. lia.
          + intros. simpl.
            replace (proj1_sig (f g (project_to_Fin (Z.of_nat t))) =? Z.of_nat a) with false by lia.
            apply H1. lia.
    }

    assert (forall a:nat, Z.of_nat a >= proj1_sig (f g (project_to_Fin (Z.of_nat t)))+1 -> collision' f g a t 0 = 1). intro. specialize (H1 a). specialize (H2 a). lia.
    
    specialize (H3 N). apply H3.
    destruct (f g (project_to_Fin (Z.of_nat t))). simpl. lia.
Qed.
Lemma collision_sum_N': forall f:ScheduleType, forall (g:Set2N), sum_collision f g (N) 0 = Z.of_nat N.
Proof.
    intros.
    assert (forall (k:nat) (res:Z), sum_collision_aux' f g N k res = Z.of_nat k + res).
    {
        intro k. induction k.
        - reflexivity.
        - intro. cbn [sum_collision_aux']. rewrite IHk. rewrite aux_coll_eq_one. lia.
    }
    assert (forall (a i:nat) (res:Z), (0<= a<=N)%nat -> sum_collision_aux' f g a i res = sum_collision_aux f g a res i).
    {
        intro. induction a.
        - induction i.
          + reflexivity.
          + intros. simpl. replace (res+0) with res by lia. apply IHi. exact H0.
        - induction i; intros.
          + simpl. replace (res+0) with res by lia.
            specialize (IHa 0%nat res). rewrite <- IHa. reflexivity. lia.
          + destruct (proj1_sig (f g (project_to_Fin (Z.of_nat i))) =? Z.of_nat a) eqn:H_test.
            * simpl. rewrite Z.mod_small. lia. setoid_rewrite H_test.
              rewrite IHi. lia. simpl.
              setoid_rewrite <- IHa at 2. 2:lia. simpl.
              replace (res + collision' f g a i 1 + collision f g (project_to_Fin (Z.of_nat a)) i 0) with (res + collision f g (project_to_Fin (Z.of_nat a)) i 1 + collision' f g a i 0).
              2:{ setoid_rewrite aux_add_res at 1. setoid_rewrite aux_add_res' at 2. lia. }
              symmetry. apply IHa. lia.
            * simpl. rewrite Z.mod_small. lia. setoid_rewrite H_test.
              rewrite IHi. lia. simpl.
              setoid_rewrite <- IHa at 2. 2:lia. simpl.
              replace (res + collision' f g a i 0 + collision f g (project_to_Fin (Z.of_nat a)) i 0) with (res + collision f g (project_to_Fin (Z.of_nat a)) i 0 + collision' f g a i 0).
              2:{ setoid_rewrite aux_add_res at 1. setoid_rewrite aux_add_res' at 2. lia. }
              symmetry. apply IHa. lia.
    }
    assert (forall (a:nat) (res:Z), sum_collision_aux f g a res N = sum_collision f g a res).
    {
        intro. induction a.
        - reflexivity.
        - intro. unfold sum_collision_aux, sum_collision. setoid_rewrite IHa. reflexivity.
    }
    specialize (H N 0). specialize (H0 N N 0). specialize (H1 N 0). rewrite <- H1. rewrite <- H0. rewrite H. lia.
    lia.
Qed.

Lemma collision_eq_one: forall f:ScheduleType, (forall (g:Set2N), forall (a:SetN), collision f g a (N) 0 = 1) -> surjective f.
Proof.
    unfold surjective. intros.
    specialize (H g a).
    assert (collision f g a N 0 >= 1). lia.
    apply collision_eq_1_to_exists in H0. destruct H0 as [t [H1 H2]].
    exists (project_to_Fin t). exact H2.
Qed.

Lemma aux_log: forall P:SetN -> Prop, (~ exists x:SetN, ~(P x)) -> forall x:SetN, ~~(P x).
Proof.
    intros. intro.
    apply H. exists x. exact H0.
Qed.

Lemma aux_eq: forall x y:Z, ~~(x=y) -> x=y.
Proof. lia. Qed.

Lemma aux_eq_args: forall (f:ScheduleType) (g:Set2N) (a1 a2:SetN) (k:nat), Fin_eq _ a1 a2 -> forall (res:Z), collision f g a1 k res = collision f g a2 k res.
Proof.
    intros f g a1 a2 k H. induction k; intro res.
    - reflexivity.
    - simpl. rewrite IHk. rewrite IHk. unfold Fin_eq in H. rewrite H. reflexivity.
Qed.

(* injective -> bijective *)
Proposition thm_tiroirs: forall f:ScheduleType, injective f -> bijective f.
Proof.
    intros. split.
    - assumption.
    - apply collision_eq_one. intro g.
      pose proof (collision_leq_one f H g).
      pose proof (collision_sum_N' f g).
      intro a. apply aux_eq. revert a. apply aux_log. intro. destruct H2.
      assert ((collision f g x (N) 0) <= 0). pose proof (H0 x). lia.
      assert (forall a:nat, forall res:Z, (Z.of_nat a<=proj1_sig x -> sum_collision f g a res <= Z.of_nat a+res) /\ (Z.of_nat a>proj1_sig x -> sum_collision f g a res < Z.of_nat a+res)).
      {
        intro a. induction a.
        - simpl. split.
          * lia.
          * destruct x. simpl. lia.
        - intro.
          assert (sum_collision f g (S a) res = sum_collision f g a (res + collision f g (project_to_Fin (Z.of_nat (a))) (N) 0)). simpl. reflexivity.
          assert (Z.of_nat a + (res + collision f g (project_to_Fin (Z.of_nat (a))) N 0) <= Z.of_nat (S a) + res). specialize (H0 (project_to_Fin (Z.of_nat (a)))). lia.
          split.
          * intro.
            assert (sum_collision f g (S a) res <= Z.of_nat a + (res + collision f g (project_to_Fin (Z.of_nat (a))) N 0)). rewrite H4. specialize (IHa (res + collision f g (project_to_Fin (Z.of_nat (a))) N 0)). destruct IHa. apply H7. lia. (* by H6 *)
            lia.
          * intro. destruct ((Z.of_nat a) =? proj1_sig x) eqn:H_a.
            + assert (sum_collision f g (S a) res <= Z.of_nat a + (res + collision f g (project_to_Fin (Z.of_nat (a))) N 0)). rewrite H4. specialize (IHa (res + collision f g (project_to_Fin (Z.of_nat (a))) N 0)). destruct IHa. apply H7. lia. (* by H6 *)
              assert (collision f g (project_to_Fin (Z.of_nat a)) N 0 = collision f g x N 0). replace (Z.of_nat a) with (proj1_sig x) by lia. destruct x. simpl. apply aux_eq_args. unfold Fin_eq. simpl. apply Z.mod_small. exact a0.
              rewrite <- H8 in H3. lia.
            + assert (sum_collision f g (S a) res < Z.of_nat a + (res + collision f g (project_to_Fin (Z.of_nat (a))) N 0)). rewrite H4. specialize (IHa (res + collision f g (project_to_Fin (Z.of_nat (a))) N 0)). destruct IHa. apply H8. lia. (* by H6 *)
              lia. (* similar to above with S a <= x *)
      }
      assert (sum_collision f g N 0 < Z.of_nat N). specialize (H4 N 0). destruct H4. destruct x. simpl in H5. lia.
      lia.
Qed.


(* surj -> inj *)
Lemma add_res: forall (f:ScheduleType) (t a : SetN) (K:nat) (res:Z), cpt_group_by_act f K a t res = cpt_group_by_act f K a t 0 + res.
Proof.
  induction K.
  - intro. simpl. lia.
  - intro. simpl. setoid_rewrite IHK. setoid_rewrite IHK at 2. destruct (proj1_sig (f (project_to_Fin2 (Z.of_nat K)) t) =? proj1_sig a) eqn:H_test; lia.
Qed.

Lemma cpt_pos: forall (f:ScheduleType) (t a : SetN) (K:nat), cpt_group_by_act f K a t 0 >= 0.
Proof.
  induction K.
  - simpl. lia.
  - simpl. rewrite add_res. destruct (proj1_sig (f (project_to_Fin2 (Z.of_nat K)) t) =? proj1_sig a) eqn:H_test; lia.
Qed.

Lemma cpt_incease: forall (f:ScheduleType) (t a : SetN) (K1 K2:nat), (K1 <= K2)%nat -> cpt_group_by_act f K1 a t 0 <= cpt_group_by_act f K2 a t 0.
Proof.
  induction K2; intro.
  - assert (K1=0%nat). lia. rewrite H0. simpl. lia.
  - destruct (Z.of_nat K1 =? Z.of_nat (S K2)) eqn:H_test.
    * rewrite Z.eqb_eq in H_test. assert (K1 = S K2). lia. rewrite H0. lia.
    * rewrite Z.eqb_neq in H_test. assert (K1 <> S K2). lia. simpl.
      assert (cpt_group_by_act f K1 a t 0 <= cpt_group_by_act f K2 a t 0). apply IHK2. lia.
      destruct (proj1_sig (f (project_to_Fin2 (Z.of_nat K2)) t) =? proj1_sig a) eqn:H_test'.
      + setoid_rewrite add_res at 2. lia.
      + lia.
Qed.

Lemma aux_exists_1_to_cpt_geq_1: forall (f:ScheduleType) (t a : SetN) (K:nat), (exists g : nat, proj1_sig (f (project_to_Fin2 (Z.of_nat g)) t) = proj1_sig a /\ (0<=g<K)%nat) -> (cpt_group_by_act f K a t 0 >= 1).
Proof.
  unfold at_least_2_by_workshop. intros.
  destruct H as [g [H0 H1]].
  induction K.
  - exfalso. lia.
  - simpl. destruct ((Z.of_nat K =? Z.of_nat g)) eqn:H_ceil.
    + rewrite Z.eqb_eq in H_ceil. assert (K=g). lia.
      assert ((proj1_sig (f (project_to_Fin2 (Z.of_nat K)) t) =? proj1_sig a)=true). rewrite H. lia.
      rewrite H2. simpl. rewrite add_res. pose proof (cpt_pos f t a K). lia.
    + simpl. destruct (proj1_sig (f (project_to_Fin2 (Z.of_nat K)) t) =? proj1_sig a) eqn:H_test.
      * rewrite add_res. pose proof (cpt_pos f t a K). lia.
      * apply IHK.
        rewrite Z.eqb_neq in H_ceil. assert (K<>g). lia.
        lia.
Qed.

Lemma at_least_2_to_cpt_geq_2: forall f:ScheduleType, at_least_2_by_workshop f -> fin_eq_equality f -> (forall t a : SetN, cpt_group_by_act f (2*N) a t 0 >= 2).
Proof.
  unfold at_least_2_by_workshop. intros.
  specialize (H a t).
  assert (forall g:Set2N, Z.of_nat (Z.to_nat (proj1_sig g)) = (proj1_sig g)). destruct g. simpl in *. lia.
  assert (forall g:Set2N, Fin_eq N (f g t) a -> proj1_sig (f (project_to_Fin2 (Z.of_nat (Z.to_nat (proj1_sig g)))) t) = proj1_sig a).
  {
    intros.
    rewrite <- H2.
    rewrite H1.
    unfold fin_eq_equality in H0. apply H0.
    simpl. apply Z.mod_small. destruct g. simpl. lia.
  }
  assert (H_wt: forall a b : Z, a >= b -> a+1>=b+1). lia.
  destruct H as [g1 [g2 [Hg1 [Hg2 H_diff]]]].
  destruct (proj1_sig g1 <? proj1_sig g2) eqn:H_comp.
  - assert (cpt_group_by_act f (Z.to_nat (proj1_sig g2)) a t 0 >= 1). apply aux_exists_1_to_cpt_geq_1. exists (Z.to_nat (proj1_sig g1)). split. exact (H2 g1 Hg1). destruct g1. simpl in *. lia.
    assert (cpt_group_by_act f (S (Z.to_nat (proj1_sig g2))) a t 0 >= 2). simpl. rewrite (H2 g2 Hg2). replace (proj1_sig a =? proj1_sig a) with true by lia. rewrite add_res. apply H_wt in H. simpl in H. exact H.
    assert (cpt_group_by_act f (S (Z.to_nat (proj1_sig g2))) a t 0 <= cpt_group_by_act f (2 * N) a t 0). apply cpt_incease. destruct g2. simpl in *. lia.
    lia.
  - unfold Fin_eq in H_diff. assert (proj1_sig g1 > proj1_sig g2). lia.
    assert (cpt_group_by_act f (Z.to_nat (proj1_sig g1)) a t 0 >= 1). apply aux_exists_1_to_cpt_geq_1. exists (Z.to_nat (proj1_sig g2)). split. exact (H2 g2 Hg2). destruct g2. simpl in *. lia.
    assert (cpt_group_by_act f (S (Z.to_nat (proj1_sig g1))) a t 0 >= 2). simpl. rewrite (H2 g1 Hg1). replace (proj1_sig a =? proj1_sig a) with true by lia. rewrite add_res. apply H_wt in H3. simpl in H3. exact H3.
    assert (cpt_group_by_act f (S (Z.to_nat (proj1_sig g1))) a t 0 <= cpt_group_by_act f (2 * N) a t 0). apply cpt_incease. destruct g1. simpl in *. lia.
    lia.
Qed.

Fixpoint total_cpt_group (f:ScheduleType) (g:nat) (a:nat) (t:SetN) (cpt:Z) {struct a} : Z :=
  match a with
  | 0%nat => cpt
  | S a' => total_cpt_group f g a' t (cpt + cpt_group_by_act f g (project_to_Fin (Z.of_nat a')) t 0)
  end.

Fixpoint cpt_group_by_act' (f:ScheduleType) (g:Set2N) (a:nat) (t:SetN) (cpt:Z) {struct a} : Z :=
  match a with
  | 0%nat => cpt
  | S a' => if proj1_sig (f g t) =? (Z.of_nat a') then cpt_group_by_act' f g a' t (cpt+1)
    else cpt_group_by_act' f g a' t cpt
  end.

Fixpoint total_cpt_group' (f:ScheduleType) (g:nat) (a:nat) (t:SetN) (cpt:Z) {struct g} : Z :=
  match g with
  | 0%nat => cpt
  | S g' => total_cpt_group' f g' a t (cpt + cpt_group_by_act' f (project_to_Fin2 (Z.of_nat g')) a t 0)
  end.

Lemma add_res': forall (f:ScheduleType) (t: SetN) (g:Set2N) (a:nat) (res:Z), cpt_group_by_act' f g a t res = cpt_group_by_act' f g a t 0 + res.
Proof.
  induction a.
  - intro. simpl. lia.
  - intro. simpl. setoid_rewrite IHa. setoid_rewrite IHa at 2. destruct (proj1_sig (f g t) =? Z.of_nat a) eqn:H_test; lia.
Qed.

Lemma aux_cpt_grp_eq_one :forall (f:ScheduleType) (t:SetN) (g:Set2N), cpt_group_by_act' f g N t 0 = 1.
Proof.
    (* very very smilar to aux_coll_eq_one: just replace (project_to_Fin (Z.of_nat t)) with t and collision with cpt_group_by_act... *)
    intros.
    assert (forall (a:nat) (res:Z), Z.of_nat a <= proj1_sig (f g t) -> cpt_group_by_act' f g a t res = res).
    {
        induction a.
        - reflexivity.
        - intros. simpl.
          replace (proj1_sig (f g t) =? Z.of_nat a) with false by lia.
          apply IHa. lia.
    }

    assert (forall a:nat, Z.of_nat a = proj1_sig (f g t)+1 -> cpt_group_by_act' f g a t 0 = 1).
    intros. simpl.
    assert (exists a', a=S a').
    {
      destruct a.
        - exfalso. destruct (f g t). simpl in H0. lia.
        - exists a. reflexivity.
    }
    destruct H1. rewrite H1. simpl.
    replace (proj1_sig (f g t) =? Z.of_nat x) with true by lia.
    apply H. lia.

    assert (forall a:nat, Z.of_nat a > proj1_sig (f g t)+1 -> cpt_group_by_act' f g a t 0 = 1).
    {
        induction a.
        - destruct ((f g t)). simpl. lia.
        - destruct (Z.of_nat a >? proj1_sig (f g t) + 1) eqn:H_init.
          all: intros; simpl.
          all: replace (proj1_sig (f g t) =? Z.of_nat a) with false by lia.
          1: apply IHa. 2: apply H0. all: lia.
    }

    assert (Z.of_nat N >= proj1_sig (f g t)+1 -> cpt_group_by_act' f g N t 0 = 1). specialize (H1 N). specialize (H0 N). lia.
    apply H2.
    destruct (f g t). simpl. lia.
Qed.

Lemma total_cpt_eq_2N: forall f:ScheduleType, forall t : SetN, total_cpt_group f (2*N) N t 0 = 2*Z.of_nat N.
Proof.
  intros.
  assert (forall (a g:nat) (cpt:Z), (0<= a<=N)%nat -> total_cpt_group' f g a t cpt = total_cpt_group f g a t cpt).
  {
    induction a.
    - induction g; intros.
      + reflexivity.
      + simpl. rewrite IHg; try lia. simpl. ring.
    - induction g; intros.
      + simpl. rewrite <- IHa; try lia. simpl. ring.
      + simpl. replace (Z.of_nat a mod Z.of_nat N) with (Z.of_nat a). 2:{ symmetry. apply Z.mod_small. lia. }
        destruct (proj1_sig (f (project_to_Fin2 (Z.of_nat g)) t) =? Z.of_nat a) eqn:H_test.
        * rewrite <- IHa; try lia. rewrite IHg; try lia. simpl.
          rewrite IHa; try lia. f_equal; try lia.
          setoid_rewrite add_res at 2. setoid_rewrite add_res' at 1. ring.
        * rewrite <- IHa; try lia. rewrite IHg; try lia. simpl.
          rewrite IHa; try lia. f_equal; try lia.
  }
  rewrite <- H; try lia.

  pose proof (aux_cpt_grp_eq_one f t).

  assert (forall (g:nat) (cpt:Z), (0<=g<=2*N)%nat -> total_cpt_group' f g N t cpt = Z.of_nat g + cpt).
  {
    induction g; intros.
    - reflexivity.
    - cbn [total_cpt_group']. rewrite H0. rewrite IHg; lia.
  }

  specialize (H1 ((2*N)%nat) 0). lia.
Qed.

Lemma aux_eq_a_in_tot: forall (f:ScheduleType) (t a1 a2 : SetN) (g:nat) (res:Z), Fin_eq _ a1 a2 -> cpt_group_by_act f g a1 t res = cpt_group_by_act f g a2 t res.
Proof.
  induction g; intros.
  - reflexivity.
  - simpl. setoid_rewrite (IHg res H). setoid_rewrite (IHg (res+1) H). rewrite H. reflexivity.
Qed.

Lemma exceed_cpt_2N: forall f:ScheduleType, forall t a : SetN, (forall a : SetN, cpt_group_by_act f (2 * N) a t 0 >= 2) -> (cpt_group_by_act f (2 * N) a t 0 >= 3) -> total_cpt_group f (2*N) N t 0 > 2*Z.of_nat N.
Proof.
  intros.
  assert (forall a0:nat, forall res:Z, (Z.of_nat a0<=proj1_sig a -> total_cpt_group f (2*N) a0 t res >= 2*(Z.of_nat a0)+res) /\ (Z.of_nat a0>proj1_sig a -> total_cpt_group f (2*N) a0 t res > 2*(Z.of_nat a0)+res)).
  {
    intro a0. induction a0.
    - simpl. split.
      * lia.
      * destruct a. simpl. lia.
    - intro.
      split; intro; cbn [total_cpt_group]; specialize (IHa0 (res + cpt_group_by_act f (2 * N) (project_to_Fin (Z.of_nat a0)) t 0)); destruct IHa0.
      * assert (2 * Z.of_nat a0 + (res + cpt_group_by_act f (2 * N) (project_to_Fin (Z.of_nat a0)) t 0) >= 2 * Z.of_nat (S a0) + res). specialize (H (project_to_Fin (Z.of_nat a0))). lia.
        lia.
      * destruct ((Z.of_nat a0) =? proj1_sig a) eqn:H_a.
        + assert (Z.of_nat a0 = proj1_sig a). lia.
          assert (cpt_group_by_act f (2 * N) (project_to_Fin (Z.of_nat a0)) t 0 = cpt_group_by_act f (2 * N) a t 0).  rewrite H4. apply aux_eq_a_in_tot. unfold Fin_eq. simpl. apply Z.mod_small. destruct a. simpl in *. lia.
          assert (2 * Z.of_nat a0 + (res + cpt_group_by_act f (2 * N) (project_to_Fin (Z.of_nat a0)) t 0) > 2 * Z.of_nat (S a0) + res). lia.
          lia.
        + assert (2 * Z.of_nat a0 + (res + cpt_group_by_act f (2 * N) (project_to_Fin (Z.of_nat a0)) t 0) >= 2 * Z.of_nat (S a0) + res). specialize (H (project_to_Fin (Z.of_nat a0))). lia.
          lia. (* similar to above with S a <= x *)
  }
  specialize (H1 N 0). destruct H1. replace (2 * Z.of_nat N) with (2 * Z.of_nat N +0) by ring. apply H2. destruct a. simpl in *. lia.
Qed.

(* surjective -> injective *)
Proposition thm_double_tiroirs: forall f:ScheduleType, at_least_2_by_workshop f -> fin_eq_equality f -> exactly_2_by_workshop f.
Proof.
    unfold exactly_2_by_workshop. intros.
    pose proof (at_least_2_to_cpt_geq_2 f H H0 t).
    pose proof (total_cpt_eq_2N f t).
    pose proof (exceed_cpt_2N f t a H1).
    specialize (H1 a). lia.
Qed.

Proposition equivalence_weak_strong: forall f:ScheduleType, perfect_schedule_weak f -> perfect_schedule_strong f.
Proof.
    intros. destruct H as [H [H0 [H1 H2]]].
    split; try split.
    - exact H0.
    - exact (thm_double_tiroirs f H1 H).
    - exact (thm_tiroirs f H2).
Qed.






(* FIRST LEMMAS ABOUT MOD *)

Lemma rewite_N: forall x:Z, x mod Z.of_nat (2 * N) = x mod (2* (Z.of_nat N)).
Proof. lia. Qed.

(* . mod . = 0 *)
Lemma mod_to_div: forall n x : Z, n>0 -> x mod n = 0 -> exists k:Z, x = k*n.
Proof.
    intros n x Hn Hmod.
    exists (x / n).
    setoid_rewrite (Z_div_exact_2 x n) at 1; lia.
Qed.
Lemma div_to_mod: forall n x : Z, n>0 -> (exists k:Z, x = k*n) -> x mod n = 0.
Proof.
    intros n x Hn Hk.
    destruct Hk. rewrite H.
    apply Z_mod_mult; auto.
Qed.

(* . mod z = . mod z *)
Lemma rewrite_mod_to_div: forall a b z : Z, z>0 -> a mod z = b mod z -> exists k, a - b = k*z.
Proof.
    intros a b z Z_pos H.
    apply mod_to_div; try lia.
    rewrite Z.add_mod; try lia. rewrite H. rewrite <- Z.add_mod; try lia.
    replace (b+-b) with 0; try lia.
    trivial.
Qed.
Lemma rewrite_div_to_mod: forall a b z : Z, z>0 -> (exists k, a - b = k*z)  -> a mod z = b mod z.
Proof.
    intros a b z Z_pos H. destruct H.
    replace a with (x*z + b). 2:rewrite <- H. 2: ring.
    rewrite Z.add_mod; try lia.
    replace ((x * z) mod z) with 0. 2: rewrite Z_mod_mult; reflexivity.
    simpl. rewrite Z.mod_mod; lia.
Qed.

(* mult 2 in a mod equality *)
Lemma mult2_mod: forall a b z : Z, z>0 -> (a/2) mod z = (b/2) mod z -> (a-a mod 2) mod (2*z) = (b-b mod 2) mod (2*z).
Proof.
    intros a b z Z_pos H.
    assert (exists k, a/2-b/2 = k*(z)). apply rewrite_mod_to_div; try assumption.
    destruct H0.
    assert (2*(a/2-b/2) = 2*(x*(z))). f_equal. exact H0.
    assert (x * (2 * z) = 2 * (x * z)). ring.
    apply rewrite_div_to_mod; try lia.
    exists x. rewrite H2.

    rewrite Z.mul_sub_distr_l in H1.

    setoid_rewrite (Z.div_mod a 2) at 1; try lia.
    setoid_rewrite (Z.div_mod b 2) at 1; lia.
Qed.



(* ODD CASE *)

Definition f_odd : ScheduleType :=
    fun (g : Set2N) (t : SetN) =>
        let val_g := proj1_sig g in
        let val_t := proj1_sig t in
        if val_g mod 2 =? 0 then 
            project_to_Fin (val_g/2 + val_t)
        else
            project_to_Fin (val_g/2 - val_t).

Lemma mult_mod: forall a b z : Z, z>0 -> a mod 2 = 0 -> b mod 2 = 0 -> (a/2) mod z = (b/2) mod z -> a mod (2*z) = b mod (2*z).
Proof.
    intros.
    replace a with (a-a mod 2) by lia.
    replace b with (b-b mod 2) by lia.
    apply mult2_mod; assumption.
Qed.

Lemma simpl_mul_div: forall a k:Z, k>0 -> k*a/k = a.
Proof. setoid_rewrite Z.mul_comm. exact Z_div_mult. Qed.

Lemma elim_minus_mod: forall a b z: Z, z>0 -> -a mod z = -b mod z -> a mod z = b mod z.
Proof.
    intros.
    apply rewrite_div_to_mod; try assumption.
    apply rewrite_mod_to_div in H0; try assumption.
    destruct H0. exists (-x). lia.
Qed.

Lemma neg_in_mod : forall a b z:Z, z>0 -> a mod z = b mod z -> (-a) mod z = (-b) mod z.
Proof.
    intros.
    apply rewrite_div_to_mod; try assumption.
    apply rewrite_mod_to_div in H0; try assumption.
    destruct H0. exists (-x). lia.
Qed.

Lemma add_in_mod : forall x z:Z, z>0 -> (z + x) mod z = x mod z.
Proof.
  intros.
  rewrite <- Zplus_mod_idemp_l; try lia.
  rewrite Z_mod_same_full.
  simpl. reflexivity.
Qed.

Lemma Z_mod_2_is_0_or_1 : forall x : Z, x mod 2 = 0 \/ x mod 2 = 1.
Proof. intro x. pose proof (Z.mod_pos_bound x 2). lia. Qed.

Lemma H_bin_mod2 : forall x:Z, (x mod 2 =? 0) = false -> x mod 2 = 1.
Proof.
  intros.
  destruct (Z_mod_2_is_0_or_1 x).
  - exfalso. lia.
  - assumption.
Qed.

(* aux no rec odd case *)
Lemma aux_no_rec_sub_mod_eq: forall (a b c d e f z:Z), z>0 -> (a+c) mod z = (b+d) mod z -> (a+e) mod z = (b+f) mod z -> (c-e) mod z = (d-f) mod z.
Proof.
  intros.
  apply rewrite_mod_to_div in H0, H1; try lia. destruct H0, H1.
  apply rewrite_div_to_mod; try lia. exists (x-x0). lia.
Qed.

Lemma aux_no_rec_diff: forall (t1 t2:SetN), Z.of_nat N mod 2 = 1 -> (proj1_sig t1 - proj1_sig t2) mod Z.of_nat N = - (proj1_sig t1 - proj1_sig t2) mod Z.of_nat N -> proj1_sig t1 = proj1_sig t2.
Proof.
  intros t1 t2 N_odd H.
  case_eq (proj1_sig t1 - proj1_sig t2).
  * lia.
  * intros.
    rewrite (Z.mod_small (proj1_sig t1 - proj1_sig t2) (Z.of_nat N)) in H. split; try lia. destruct t1. destruct t2. simpl. lia.
    rewrite <- add_in_mod in H; try lia.
    rewrite (Z.mod_small (Z.of_nat N-(proj1_sig t1 - proj1_sig t2)) (Z.of_nat N))in H. split; try lia. destruct t1. destruct t2. simpl. lia.
    assert ((2*(proj1_sig t1 - proj1_sig t2)) mod 2 = (Z.of_nat N) mod 2). f_equal. lia.
    rewrite Z.mul_mod in H1; try lia.
    replace ((2 mod 2 * ((proj1_sig t1 - proj1_sig t2) mod 2)) mod 2) with 0 in H1 by trivial.
    rewrite N_odd in H1. exfalso. lia.
  * intros.
    rewrite <- add_in_mod in H; try lia.
    rewrite (Z.mod_small (Z.of_nat N+(proj1_sig t1 - proj1_sig t2)) (Z.of_nat N)) in H. split; try lia. destruct (t1). destruct (t2). simpl. lia.
    rewrite (Z.mod_small (-(proj1_sig t1 - proj1_sig t2)) (Z.of_nat N))in H. split; try lia. destruct (t1). destruct (t2). simpl. lia.
    assert ((2*(-proj1_sig t1 + proj1_sig t2)) mod 2 = (Z.of_nat N) mod 2). f_equal. lia.
    rewrite Z.mul_mod in H1; try lia. rewrite Z_mod_same_full in H1. simpl in H1. rewrite Zmod_0_l in H1.
    rewrite N_odd in H1. exfalso. lia.
Qed.

(* divide by 2 a _ mod (2*...) *)
Lemma mod_div2: forall x:Z, ((2 * x) mod Z.of_nat (2*N))/2  = (x mod Z.of_nat N).
Proof.
  assert (forall x y:Z, x=y*2 -> x/2 = y). intros. rewrite H.
  setoid_rewrite Z.mul_comm at 1.
  setoid_rewrite <- (Z.mul_1_r 2) at 2.
  rewrite Z.div_mul_cancel_l; try lia.
  rewrite Z.div_1_r. reflexivity.

  intro. apply H.
  rewrite Z.mod_eq; try lia. rewrite Z.mod_eq; try lia.
  replace (Z.of_nat (2 * N)) with (2*Z.of_nat (N)); try lia.
  rewrite Z.div_mul_cancel_l; try lia.
Qed.

Lemma mod_div2p1: forall x:Z, ((2 * x + 1) mod Z.of_nat (2*N))/2  = (x mod Z.of_nat N).
Proof.
  assert (forall x y:Z, y >= 0 -> x=y*2+1 -> x/2 = y).
  intros. rewrite H0.
  rewrite Z.div_add_l; try lia.
  rewrite Zdiv_small; lia.

  intro. apply H.
  - pose proof (Z_mod_lt x (Z.of_nat N)). lia.
  - 
  rewrite Z.mod_eq; try lia. rewrite Z.mod_eq; try lia.
  replace (Z.of_nat (2 * N)) with (2*Z.of_nat (N)); try lia.
  rewrite <- Zdiv_Zdiv; try lia.
  replace (2 * x + 1) with (x * 2 + 1). 2:ring.
  rewrite Z.div_add_l; try lia.
  setoid_rewrite Zdiv_small at 2; try lia.
  replace (x + 0) with x; ring.
Qed.

Lemma mod_div2_gnl: forall x:Z, (x mod Z.of_nat (2*N))/2  = (x/2 mod Z.of_nat N).
Proof.
  assert (forall x y:Z, y >= 0 -> x=y*2+x mod 2 -> x/2 = y).
  intros. rewrite H0.
  rewrite Z.div_add_l; try lia.
  assert (0 <= x mod 2 < 2). apply Z_mod_lt; try lia.
  rewrite Zdiv_small; lia.

  intro. apply H.
  - pose proof (Z_mod_lt (x/2) (Z.of_nat N)). lia.
  - 
  setoid_rewrite Z.mod_eq at 1; try lia. setoid_rewrite Z.mod_eq at 1; try lia.
  replace (Z.of_nat (2 * N)) with (2*Z.of_nat (N)); try lia.
  rewrite <- Zdiv_Zdiv; try lia.
  replace ((x mod (2 * Z.of_nat N)) mod 2) with (x mod 2). 2:{ rewrite <- Zmod_div_mod; try lia. apply Z.divide_factor_l. }
  setoid_rewrite Z.mod_eq at 1; try lia.
Qed.



Lemma aux_inj_odd: forall (a b c z:Z), z>0 -> (c+a) mod z = (c+b) mod z -> a mod z = b mod z.
Proof.
    intros.
    apply rewrite_div_to_mod; try lia.
    apply rewrite_mod_to_div in H0; try lia. destruct H0.
    exists x. lia.
Qed.

Theorem odd_case: Z.of_nat N mod 2 = 1 -> perfect_schedule_weak f_odd.
Proof.
  intro N_odd.
  split; try split; try split.
  - unfold fin_eq_equality. intros. unfold f_odd. unfold Fin_eq in H. repeat setoid_rewrite H. reflexivity.
  - unfold no_rec_enc. intros.
    destruct (proj1_sig g1 mod 2 =? 0) eqn:H_mod_g1; destruct (proj1_sig g2 mod 2 =? 0) eqn:H_mod_g2.
    + unfold f_odd in H. rewrite H_mod_g1 in H. rewrite H_mod_g2 in H.

      assert ((proj1_sig g1 / 2) mod Z.of_nat N = (proj1_sig g2 / 2) mod Z.of_nat N).
      unfold Fin_eq in H. simpl in H. apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
      apply rewrite_div_to_mod; try lia. exists x. exact H.

      assert((proj1_sig g1) mod Z.of_nat (2 * N) = (proj1_sig g2) mod Z.of_nat (2 * N)).
      setoid_rewrite rewite_N. apply mult_mod; try lia.

      rewrite (Z.mod_small (proj1_sig g1) (Z.of_nat (2*N)))in H2. destruct g1. simpl. assumption.
      rewrite (Z.mod_small (proj1_sig g2) (Z.of_nat (2*N)))in H2. destruct g2. simpl. assumption.

      right. exact H2.
    + unfold f_odd in H. rewrite H_mod_g1 in H. rewrite H_mod_g2 in H. unfold Fin_eq in H. simpl in H.
      unfold f_odd in H0. rewrite H_mod_g1 in H0. rewrite H_mod_g2 in H0. unfold Fin_eq in H0. simpl in H0.

      rewrite <- Z.add_opp_r in H, H0.
      assert (Z.of_nat N > 0). lia.
      pose proof (aux_no_rec_sub_mod_eq _ _ _ _ _ _ _ H1 H H0).

      replace (- proj1_sig t1 - - proj1_sig t2) with (-(proj1_sig t1 - proj1_sig t2)) in H2 by ring.
      left. unfold Fin_eq. exact (aux_no_rec_diff t1 t2 N_odd H2).
    + unfold f_odd in H. rewrite H_mod_g1 in H. rewrite H_mod_g2 in H. unfold Fin_eq in H. simpl in H.
      unfold f_odd in H0. rewrite H_mod_g1 in H0. rewrite H_mod_g2 in H0. unfold Fin_eq in H0. simpl in H0.

      rewrite <- Z.add_opp_r in H, H0.
      assert (Z.of_nat N > 0). lia.
      pose proof (aux_no_rec_sub_mod_eq _ _ _ _ _ _ _ H1 H H0).

      replace (- proj1_sig t1 - - proj1_sig t2) with (-(proj1_sig t1 - proj1_sig t2)) in H2 by ring.
      left. unfold Fin_eq. symmetry in H2. exact (aux_no_rec_diff t1 t2 N_odd H2).
    + unfold f_odd in H. rewrite H_mod_g1 in H. rewrite H_mod_g2 in H.

      assert ((proj1_sig g1 / 2) mod Z.of_nat N = (proj1_sig g2 / 2) mod Z.of_nat N).
      unfold Fin_eq in H. simpl in H. apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
      apply rewrite_div_to_mod; try lia. exists x. exact H.

      assert((proj1_sig g1-(proj1_sig g1 mod 2)) mod Z.of_nat (2 * N) = (proj1_sig g2-(proj1_sig g2 mod 2)) mod Z.of_nat (2 * N)).
      setoid_rewrite rewite_N. apply mult2_mod; try lia.

      apply H_bin_mod2 in H_mod_g1, H_mod_g2. rewrite H_mod_g1 in H2. rewrite H_mod_g2 in H2.

      assert (H_posx: forall x:Z, x mod 2 = 1 -> 0 <= x -> 0 <= x-1). intros. destruct x; try lia. destruct H3. trivial.

      rewrite (Z.mod_small (proj1_sig g1-1) (Z.of_nat (2*N)))in H2. destruct g1. simpl in *. specialize (H_posx x). lia.
      rewrite (Z.mod_small (proj1_sig g2-1) (Z.of_nat (2*N)))in H2. destruct g2. simpl in *. specialize (H_posx x). lia.

      right. unfold Fin_eq. lia.
  - unfold at_least_2_by_workshop. intros.
    exists (project_to_Fin2 (2 * (proj1_sig a) - 2 * (proj1_sig t))).
    exists (project_to_Fin2 (2 * (proj1_sig a) + 1 + 2 * (proj1_sig t))).
    split; try split.
    + set (K:=2 * proj1_sig a - 2 * proj1_sig t).
      unfold Fin_eq. unfold f_odd. simpl.
      
      assert (K mod 2 = 0). replace K with ((proj1_sig a - proj1_sig t)*2) by lia. apply Z_mod_mult.

      assert ((K mod Z.of_nat (N + (N + 0))) mod 2 = 0).
      replace (Z.of_nat (N + (N + 0))) with (2*(Z.of_nat N)) by lia.
      rewrite <- Zmod_div_mod; try lia.
      apply Z.divide_factor_l.

      rewrite H0. simpl.
      replace K with (2*(proj1_sig a - proj1_sig t)) by lia.
      rewrite mod_div2.
      rewrite Zplus_mod_idemp_l.
      replace (proj1_sig a - proj1_sig t + proj1_sig t) with (proj1_sig a) by ring.
      rewrite Z.mod_small; try lia. destruct a. simpl. assumption.
    + set (K:=2 * proj1_sig a + 1 + 2 * proj1_sig t).
      unfold Fin_eq. unfold f_odd. simpl.

      assert (K mod 2 = 1). replace K with (1+(proj1_sig a + proj1_sig t)*2) by lia. apply Z_mod_plus. lia.

      assert ((K mod Z.of_nat (N + (N + 0))) mod 2 = 1).
      replace (Z.of_nat (N + (N + 0))) with (2*(Z.of_nat N)) by lia.
      rewrite <- Zmod_div_mod; try lia.
      apply Z.divide_factor_l.

      rewrite H0. simpl.
      replace K with (2*(proj1_sig a + proj1_sig t)+1) by lia.
      rewrite mod_div2p1.
      rewrite Zplus_mod_idemp_l.
      replace (proj1_sig a + proj1_sig t + - proj1_sig t) with (proj1_sig a) by ring.
      rewrite Z.mod_small; try lia. destruct a. simpl. assumption.
    + unfold Fin_eq. cbn [project_to_Fin2 proj1_sig].
      rewrite Z.mod_eq; try lia.
      rewrite Z.mod_eq; lia.
  - unfold injective. intros.
    unfold Fin_eq in *.
    destruct (proj1_sig g mod 2 =? 0) eqn:H_mod_g.
    + unfold f_odd in H. rewrite H_mod_g in H. simpl in H.
      apply aux_inj_odd in H; try lia.
      rewrite (Z.mod_small (proj1_sig t1) (Z.of_nat N))in H. destruct t1. simpl. assumption.
      rewrite (Z.mod_small (proj1_sig t2) (Z.of_nat N))in H. destruct t2. simpl. assumption.
      exact H.
    + unfold f_odd in H. rewrite H_mod_g in H. simpl in H.
      apply aux_inj_odd in H; try lia.
      apply elim_minus_mod in H; try lia.
      rewrite (Z.mod_small (proj1_sig t1) (Z.of_nat N))in H. destruct t1. simpl. assumption.
      rewrite (Z.mod_small (proj1_sig t2) (Z.of_nat N))in H. destruct t2. simpl. assumption.
      exact H.
Qed.



(* DIVIDIBLE BY FOUR CASE *)

Definition f_div4 : ScheduleType :=
    fun (g : Set2N) (t : SetN) =>
        let val_g := proj1_sig g in
        let val_t := proj1_sig t in
        if val_g mod 4 =? 0 then 
            project_to_Fin (val_g/2 - val_t)
        else if val_g mod 4 =? 2 then
            project_to_Fin (val_g/2 + val_t)
        else if andb (val_g mod 4 =? 1) (val_t <? (Z.of_nat N)/2) then
            project_to_Fin (val_g/2 + val_t)
        else if val_g mod 4 =? 1 then
            project_to_Fin (val_g/2 + (Z.of_nat N)/2 - 1 - val_t)
        else if andb (val_g mod 4 =? 3) (val_t <? (Z.of_nat N)/2) then
            project_to_Fin (val_g/2 - val_t)
        else project_to_Fin (val_g/2 + (Z.of_nat N)/2 + 1 + val_t).

Lemma case_mod_4 : forall x : Z, x mod 4 = 0 \/ x mod 4 = 1 \/ x mod 4 = 2 \/ x mod 4 = 3.
Proof.
    intro.
    destruct (Z_mod_2_is_0_or_1 x); destruct (Z_mod_2_is_0_or_1 (x/2)).
    1: left.
    2: right; right; left.
    3: right; left.
    4: right; right; right.
    all: replace 4 with (2*2) by ring.
    all: rewrite Z.rem_mul_r; lia.
Qed.

Lemma aux_inj: forall x x0 x1:Z, -(Z.of_nat N) < x1 - x0 < Z.of_nat N -> (x + x0) mod Z.of_nat N = (x + x1) mod Z.of_nat N -> x0 = x1.
Proof.
  intros.
  apply rewrite_mod_to_div in H0; try lia. destruct H0. ring_simplify in H0.

  assert (H_mul_inequ: forall a b : Z, a >= 1 -> b >= 1 -> a * b >= b).
  intros. setoid_rewrite <- Z.mul_1_l at 4. apply Zmult_ge_compat_r; lia.

  case_eq x2.
  * intro. rewrite H1 in H0. simpl in H0. lia.
  * intros. exfalso.

    assert (x0 - x1 >= Z.of_nat N). rewrite H0. trivial. apply H_mul_inequ; lia.
    lia.
  * intros. exfalso.

    assert (-(x0 - x1) >= Z.of_nat N). rewrite H0. trivial. replace (- (x2 * Z.of_nat N)) with ((-x2) * Z.of_nat N); try ring. apply H_mul_inequ; lia.
    assert ((x0 - x1) <= -(Z.of_nat N)). lia.
    lia.
Qed.

Lemma div_prop_even : Z.of_nat N mod 4 = 0 -> Z.of_nat N / 2 - Z.of_nat N = - (Z.of_nat N / 2).
Proof.
  intro.
  assert (H_even: Z.of_nat N mod 2 = 0).
  apply mod_to_div in H; try lia. destruct H.
  apply div_to_mod; try lia. exists (x*2). lia.

  assert (H_of_nat_val : Z.of_nat N = 2 * (Z.of_nat N / 2) + (Z.of_nat N) mod 2).
  rewrite (Z.mod_eq (Z.of_nat N) 2); lia.
  
  rewrite H_even in H_of_nat_val.

  setoid_rewrite H_of_nat_val at 2.
  ring.
Qed.

Lemma div_prop_N_even : Z.of_nat N mod 4 = 0 -> 2*(Z.of_nat N / 2) = Z.of_nat N.
Proof. pose proof div_prop_even. lia. Qed.

Lemma elim_minus_one: forall a z:Z, z>0 -> a mod z = 0 -> (-a) mod z = 0.
Proof.
  intros.
  apply mod_to_div in H0; try lia. destruct H0.
  apply div_to_mod; try lia. exists (-x). lia.
Qed.

Lemma plus_minus_mod2: forall x:Z, x mod 2 = (-x) mod 2.
Proof.
  intro. apply rewrite_div_to_mod; try lia. exists x. lia.
Qed.

Lemma aux_at_least_2_by_wrkshp: forall x y z: Z, z > 0 -> z mod 4 = 0 -> 0 <= y < 2 -> ((2*x + y) mod (2*z)) mod 4 = 2*(x mod 2) + y.
Proof.
  intros.
  setoid_rewrite Z.mod_eq at 2; try lia. rewrite Z.add_mod; try lia.
  assert (- (2 * z * ((2 * x + y) / (2 * z))) mod 4 = 0). apply elim_minus_one; try lia. rewrite Z.mul_mod; try lia. replace (Z.of_nat (N + (N + 0))) with (2 * Z.of_nat N). 2:lia. setoid_rewrite Z.mul_mod at 2; try lia. rewrite H0. simpl. trivial.
  rewrite H2. replace ((2 * x + y) mod 4 + 0) with ((2 * x + y) mod 4). 2:ring.
  rewrite Z.mod_mod; try lia.
  assert ((2 * x + y) mod 4 = (2 * (x mod 2) + y) mod 4). apply rewrite_div_to_mod; try lia. rewrite Z.mod_eq; try lia. exists (x / 2). ring.
  rewrite H3. apply Z.mod_small.
  pose proof (Z_mod_lt x 2).
  lia.
Qed.

Lemma aux_no_rec_same_mod: forall g1 g2 : Set2N, forall x: Z, proj1_sig g1 / 2 - proj1_sig g2 / 2 = x * Z.of_nat N -> proj1_sig g1 mod 4 = proj1_sig g2 mod 4 -> Fin_eq (2 * N) g1 g2.
Proof.
  intros.
  unfold Fin_eq.

  assert (proj1_sig g1 mod 2 = proj1_sig g2 mod 2). apply rewrite_div_to_mod; try lia. apply rewrite_mod_to_div in H0; try lia. destruct H0. exists (x0*2). rewrite H0. ring.

  destruct g1. destruct g2. simpl in *.
  rewrite Z.mod_eq in H1; try lia. rewrite Z.mod_eq in H1; try lia.

  assert (x0 / 2 = x1 / 2).
  {
    destruct x.
    + lia.
    + assert (x0 / 2 - x1 / 2 < Z.of_nat N). lia.
      assert (Z.pos p * Z.of_nat N >= Z.of_nat N). setoid_rewrite <- Z.mul_1_l at 4. apply Zmult_ge_compat_r; lia.
      lia.
    + assert (x0 / 2 - x1 / 2 > - Z.of_nat N). lia.
      assert (Z.neg p * Z.of_nat N <= - Z.of_nat N). setoid_rewrite <- Z.mul_1_l at 4. rewrite <- Z.mul_opp_comm. apply Zmult_le_compat_r; lia.
      lia.
  }

  rewrite H2 in H1. lia.
Qed.

Lemma apply_mod: forall a b z: Z,  z>0 -> a = b -> a mod z = b mod z.
Proof. intros. f_equal. exact H0. Qed.
  
Lemma div_mod_by_2: forall x z : Z, z > 0 -> x mod (2*z) / 2 = (x / 2) mod z.
Proof.
  assert (forall x y:Z, y >= 0 -> x=y*2+x mod 2 -> x/2 = y).
  intros. rewrite H0.
  rewrite Z.div_add_l; try lia.
  rewrite Zmod_div. ring.

  intros. apply H.
  - pose proof (Z_mod_lt (x/2) z). lia.
  - setoid_rewrite Z.mod_eq at 1; try lia. setoid_rewrite Z.mod_eq at 1; try lia.
    rewrite <- Zdiv_Zdiv; try lia.
    replace ((x mod (2 * z)) mod 2) with (x mod 2). 2:{ rewrite <- Zmod_div_mod; try lia. apply Z.divide_factor_l. }
    setoid_rewrite Z.mod_eq at 1; try lia.
Qed.

Lemma div_sub_eq_mod_eq (x y : Z) :
  x mod 2 = y mod 2 -> x / 2 - y / 2 = (x - y) / 2.
Proof.
  intros H_mod_eq.
  assert (Hx : x = (x / 2) * 2 + (x mod 2)). rewrite Z.mod_eq; lia.
  assert (Hy : y = (y / 2) * 2 + (y mod 2)). rewrite Z.mod_eq; lia.
  rewrite <- H_mod_eq in Hy.

  replace (x - y) with (((x / 2) * 2 + (x mod 2)) - ((y / 2) * 2 + (x mod 2))) by lia.
  replace (x / 2 * 2 + x mod 2 - (y / 2 * 2 + x mod 2)) with ((x / 2  - y / 2) * 2) by ring.

  rewrite Z_div_mult; lia.
Qed.

Lemma aux_no_rec_mod_plus2: forall x y:Z, (x - y) mod 4 = 2 -> (x / 2 - y / 2) mod 2 = 0 -> False.
Proof.
  intros.
  apply mod_to_div in H0; try lia. destruct H0.
  apply (apply_mod _ _ 2) in H0; try lia. rewrite Z_mod_mult in H0.
  assert (((x - y) mod (2 * 2)) / 2 = 2/2). f_equal. replace (2*2) with 4 in H. 2:ring. exact H.
  rewrite div_mod_by_2 in H1; try lia.
  replace (2/2) with 1 in H1. 2:trivial.
  assert ((x-y) mod 2 = 0). replace 2 with (2 mod 4) in H. 2:trivial. apply rewrite_mod_to_div in H; try lia. destruct H. apply div_to_mod; try lia. exists (2*x1 + 1). lia.
  assert (x / 2 - y / 2 = (x - y) / 2). apply div_sub_eq_mod_eq. apply mod_to_div in H2; try lia. apply rewrite_div_to_mod; try lia. exact H2.
  rewrite H3 in H0.
  rewrite H0 in H1.
  discriminate H1.
Qed.

Lemma aux_sub_mod_eq: forall a b c d z : Z, z > 0 -> a mod z = b mod z -> c mod z = d mod z -> exists k, a - b - c + d = k * z.
Proof.
  intros.
  apply rewrite_mod_to_div in H0; try lia. destruct H0.
  apply rewrite_mod_to_div in H1; try lia. destruct H1.
  exists (x - x0). lia.
Qed.

Lemma aux_no_rec_bound_eq: forall x0 x1 x:Z, -2 * x0 + 2 * x1 = x * Z.of_nat N -> - Z.of_nat N < -2 * x0 + 2 * x1 < Z.of_nat N -> x0 = x1.
Proof.
  intros.
  destruct x.
  + lia.
  + assert (Z.pos p * Z.of_nat N >= Z.of_nat N). setoid_rewrite <- Z.mul_1_l at 4. apply Zmult_ge_compat_r; lia.
    lia.
  + assert (Z.neg p * Z.of_nat N <= - Z.of_nat N). setoid_rewrite <- Z.mul_1_l at 4. rewrite <- Z.mul_opp_comm. apply Zmult_le_compat_r; lia.
    lia.
Qed.

Lemma aux_no_rec_bound_eq_gnl: forall x0 x1 x:Z, x0 - x1 = x * Z.of_nat N -> - Z.of_nat N < x0 - x1 < Z.of_nat N -> x0 = x1.
Proof.
  intros.
  destruct x.
  + lia.
  + assert (Z.pos p * Z.of_nat N >= Z.of_nat N). setoid_rewrite <- Z.mul_1_l at 4. apply Zmult_ge_compat_r; lia.
    lia.
  + assert (Z.neg p * Z.of_nat N <= - Z.of_nat N). setoid_rewrite <- Z.mul_1_l at 4. rewrite <- Z.mul_opp_comm. apply Zmult_le_compat_r; lia.
    lia.
Qed.

Lemma div_small_mod4: forall x:Z, x mod 4 < 2 -> exists k, x / 2 = 2 * k.
Proof.
  intros. exists (x / 4).
  assert (x = 4* (x / 4) + x mod 4). rewrite Z.mod_eq; try lia.
  setoid_rewrite H0 at 1.
  replace (4 * (x / 4)) with ((2 * (x / 4))*2) by ring.
  rewrite Z.div_add_l; try lia.
  pose proof (Z.mod_pos_bound x 4).
  rewrite (Zdiv_small (x mod 4) 2); try lia.
Qed.

Lemma div_big_mod4: forall x:Z, x mod 4 >= 2 -> exists k, x / 2 = 2 * k + 1.
Proof.
  intros. exists (x / 4).
  assert (x = 4* (x / 4) + x mod 4). rewrite Z.mod_eq; try lia.
  setoid_rewrite H0 at 1.
  replace (4 * (x / 4)) with ((2 * (x / 4))*2) by ring.
  rewrite Z.div_add_l; try lia.
  assert (forall y, y = y/2*2 + y mod 2). intro. rewrite Z.mod_eq; try lia.
  assert (x mod 4 / 2 = 1).
  {
    pose proof (Z.mod_pos_bound x 4).
    replace (x mod 4) with (x mod 4 - 2 + 2) by ring.
    rewrite (H1 (x mod 4 - 2)).
    replace ((x mod 4 - 2) / 2 * 2 + (x mod 4 - 2) mod 2 + 2) with (((x mod 4 - 2) / 2 + 1 )* 2 + (x mod 4 - 2) mod 2) by ring.
    rewrite Z_div_plus_full_l; try lia.
    assert ((x mod 4 - 2) / 2 = 0). apply Zdiv_small. lia.
    rewrite H3. rewrite Zmod_div.
    ring.
  }
  lia.
Qed.

(* auxilary lemmas for at least 2 by workshop *)
Lemma apply_mod_2: forall a b:Z, a mod 2 <> b mod 2 -> a <> b.
Proof. intros. intro. apply H. f_equal. exact H0. Qed.
Lemma div_by_2_2N: (2 | Z.of_nat (2 * N)).
Proof. replace (Z.of_nat (2 * N)) with (2*Z.of_nat N) by lia. apply Z.divide_factor_l. Qed.
Lemma fact_2_in_mod: forall a, (2*a) mod 2 = 0.
Proof. intro. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
Lemma fact_2_p1_in_mod: forall a, (2*a+1) mod 2 = 1.
Proof. intro. replace (2*a+1) with (1+a*2) by ring. rewrite Z_mod_plus; try lia. trivial. Qed.

Theorem div4_case: Z.of_nat N mod 4 = 0 -> perfect_schedule_weak f_div4.
Proof.
  intro N_div_4.
  unfold perfect_schedule_weak.
  split; try split; try split.
  - unfold fin_eq_equality. intros. unfold f_div4. repeat rewrite H. reflexivity.
  - unfold no_rec_enc. intros.
    destruct (case_mod_4 (proj1_sig g1)) as [Hg1|Hg1_]; try destruct Hg1_ as [Hg1|Hg1_]; try destruct Hg1_ as [Hg1|Hg1];
    destruct (case_mod_4 (proj1_sig g2)) as [Hg2|Hg2_]; try destruct Hg2_ as [Hg2|Hg2_]; try destruct Hg2_ as [Hg2|Hg2].
    + unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. unfold Fin_eq in H. simpl in H.
      apply rewrite_mod_to_div in H; try lia.
      destruct H. ring_simplify in H.
      right. apply (aux_no_rec_same_mod g1 g2 x H). lia.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1; destruct (proj1_sig t2 <? (Z.of_nat N)/2) eqn:H_t2.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        destruct t1, t2. simpl in H_t1, H_t2.
        assert (0 <= x1 < Z.of_nat N / 2). lia.
        assert (- (Z.of_nat N / 2) < -x0 <= - 0). rewrite <- Z.opp_le_mono. rewrite <- Z.opp_lt_mono. lia.
        assert (0 <= Z.of_nat N - (2 * (Z.of_nat N / 2))). rewrite <- Z.mod_eq; try lia. apply modulo_lt_divisor. lia.
        assert (Z.of_nat N / 2 * 2 <= Z.of_nat N). lia.
        assert (- (Z.of_nat N) < -2 * x0 + 2 * x1 < Z.of_nat N). lia.

        unfold Fin_eq.
        cbn [proj1_sig] in *.
        left. apply (aux_no_rec_bound_eq x0 x1 x H2 H7).
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (-2 * proj1_sig t1 + (x0 * 4) / 2 - x * (x0 * 4) = 1). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
        (* in H2: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2. replace (- (Z.of_nat N / 2) + 2 * proj1_sig t2 + 1) with (1 - (Z.of_nat N / 2) + 2 * proj1_sig t2) in H2. 2:ring.

        exfalso. (* in H2: left odd right even *)
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (1 =  (x0 * 4) / 2 - 2 * proj1_sig t2 + x * (x0 * 4)). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        
        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        
        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (forall a b:Z, 1 = a/2 - b/2 - a/2 + b/2 + 1). lia.
        assert (1 = x * (x0 * 4) - proj1_sig g1 / 2 + proj1_sig g2 / 2 + (x0 * 4) / 2). rewrite <- H1. rewrite <- H.  ring_simplify. apply H2.
        replace (x0*4) with ((x0*2)*2) in H3. 2:lia. rewrite Z_div_mult in H3; try lia.

        assert (proj1_sig g1 mod 4 < 2). lia. apply div_small_mod4 in H4. destruct H4. rewrite H4 in H3.
        assert (proj1_sig g2 mod 4 < 2). lia. apply div_small_mod4 in H5. destruct H5. rewrite H5 in H3.
        lia.
        (* in H: right is even left is odd *)
    + unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. unfold Fin_eq in H. simpl in H.
      apply rewrite_mod_to_div in H; try lia.
      destruct H. ring_simplify in H.

      assert (proj1_sig g1 / 2 - 2 * proj1_sig t1 - proj1_sig g2 / 2 = (proj1_sig g1 / 2 - proj1_sig g2 / 2) + (- proj1_sig t1) * 2). ring.
      rewrite H1 in H.

      apply (apply_mod _ _ 2) in H; try lia.
      rewrite Z_mod_plus in H; try lia.
      apply mod_to_div in N_div_4; try lia. destruct N_div_4. rewrite H2 in H. replace (x * (x0 * 4)) with (x * x0 * 2 * 2) in H. 2:ring. rewrite Z_mod_mult in H.

      exfalso. apply (aux_no_rec_mod_plus2 (proj1_sig g1) (proj1_sig g2)); try lia.

      rewrite Zminus_mod. rewrite Hg1. rewrite Hg2. trivial.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1; destruct (proj1_sig t2 <? (Z.of_nat N)/2) eqn:H_t2.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        
        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        
        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4. rewrite H1 in H.
        assert (proj1_sig g1 mod 4 < 2). lia. apply div_small_mod4 in H2. destruct H2. rewrite H2 in H.
        assert (proj1_sig g2 mod 4 >= 2). lia. apply div_big_mod4 in H3. destruct H3. rewrite H3 in H.
        lia.
        (* in H: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2. replace (- (Z.of_nat N / 2) + 2 * proj1_sig t2 + 1) with (1 - (Z.of_nat N / 2) + 2 * proj1_sig t2) in H2. 2:ring.

        exfalso. (* in H2: left odd right even *)
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (1 =  -((x0 * 4) / 2) - 2 * proj1_sig t2 + x * (x0 * 4)). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (-2 * proj1_sig t1 - ((x0 * 4) / 2) - x * (x0 * 4) = 1). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
        (* in H2: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        destruct t1, t2. simpl in H_t1, H_t2.
        assert (Z.of_nat N / 2 <= x1 < Z.of_nat N). lia.
        assert (- (Z.of_nat N) < -x0 <= - (Z.of_nat N / 2)). rewrite <- Z.opp_le_mono. rewrite <- Z.opp_lt_mono. lia.
        assert (0 <= Z.of_nat N - (2 * (Z.of_nat N / 2))). rewrite <- Z.mod_eq; try lia. apply modulo_lt_divisor. lia.
        assert (Z.of_nat N / 2 * 2 = Z.of_nat N). apply mod_to_div in N_div_4; try lia. destruct N_div_4. replace (Z.of_nat N) with (2*(2*x2)) by lia. rewrite simpl_mul_div; lia.
        assert (- (Z.of_nat N) < -2 * x0 + 2 * x1 < Z.of_nat N). lia.

        unfold Fin_eq.
        cbn [proj1_sig] in *.
        left. apply (aux_no_rec_bound_eq x0 x1 (x)); try lia.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1; destruct (proj1_sig t2 <? (Z.of_nat N)/2) eqn:H_t2.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        destruct t1, t2. simpl in H_t1, H_t2.
        assert (0 <= x1 < Z.of_nat N / 2). lia.
        assert (- (Z.of_nat N / 2) < -x0 <= - 0). rewrite <- Z.opp_le_mono. rewrite <- Z.opp_lt_mono. lia.
        assert (0 <= Z.of_nat N - (2 * (Z.of_nat N / 2))). rewrite <- Z.mod_eq; try lia. apply modulo_lt_divisor. lia.
        assert (Z.of_nat N / 2 * 2 <= Z.of_nat N). lia.
        assert (- (Z.of_nat N) < -2 * x0 + 2 * x1 < Z.of_nat N). lia.

        unfold Fin_eq.
        cbn [proj1_sig] in *.
        left. apply (aux_no_rec_bound_eq x0 x1 (-x)); try lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2. replace (- (Z.of_nat N / 2) + 2 * proj1_sig t2 + 1) with (1 - (Z.of_nat N / 2) + 2 * proj1_sig t2) in H2. 2:ring.

        exfalso. (* in H2: left odd right even *)
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (1 =  (x0 * 4) / 2 - 2 * proj1_sig t1 + x * (x0 * 4)). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (-2 * proj1_sig t2 + (x0 * 4) / 2 - x * (x0 * 4) = 1). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
        (* in H2: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        
        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        
        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (forall a b:Z, a - b - a + b + 1 = 1) by lia.
        assert (proj1_sig g1 / 2 + (x0 * 4) / 2 - proj1_sig g2 / 2 - x * (x0 * 4) = 1). rewrite <- H1. rewrite <- H.  ring_simplify. apply H2.
        replace (x0*4) with ((x0*2)*2) in H3. 2:lia. rewrite Z_div_mult in H3; try lia.

        assert (proj1_sig g1 mod 4 < 2). lia. apply div_small_mod4 in H4. destruct H4. rewrite H4 in H3.
        assert (proj1_sig g2 mod 4 < 2). lia. apply div_small_mod4 in H5. destruct H5. rewrite H5 in H3.
        lia.
        (* in H: right is even left is odd *)
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        apply rewrite_mod_to_div in H; try lia.
        destruct H. ring_simplify in H.
        right. apply (aux_no_rec_same_mod g1 g2 x H). lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        apply rewrite_mod_to_div in H; try lia.
        destruct H. ring_simplify in H.
        right. apply (aux_no_rec_same_mod g1 g2 x H). lia.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1; destruct (proj1_sig t2 <? (Z.of_nat N)/2) eqn:H_t2.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        
        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        
        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4. rewrite H1 in H.
        assert (proj1_sig g1 mod 4 < 2). lia. apply div_small_mod4 in H2. destruct H2. rewrite H2 in H.
        assert (proj1_sig g2 mod 4 >= 2). lia. apply div_big_mod4 in H3. destruct H3. rewrite H3 in H.
        lia.
        (* in H: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2. replace (- (Z.of_nat N / 2) + 2 * proj1_sig t2 + 1) with (1 - (Z.of_nat N / 2) + 2 * proj1_sig t2) in H2. 2:ring.

        exfalso. (* in H2: left odd right even *)
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (1 =  ((x0 * 4) / 2) - 2 * proj1_sig t2 + x * (x0 * 4)). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (-2 * proj1_sig t1 + ((x0 * 4) / 2) - x * (x0 * 4) = 1). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
        (* in H2: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        destruct t1, t2. simpl in H_t1, H_t2.
        assert (Z.of_nat N / 2 <= x1 < Z.of_nat N). lia.
        assert (- (Z.of_nat N) < -x0 <= - (Z.of_nat N / 2)). rewrite <- Z.opp_le_mono. rewrite <- Z.opp_lt_mono. lia.
        assert (0 <= Z.of_nat N - (2 * (Z.of_nat N / 2))). rewrite <- Z.mod_eq; try lia. apply modulo_lt_divisor. lia.
        assert (Z.of_nat N / 2 * 2 = Z.of_nat N). apply mod_to_div in N_div_4; try lia. destruct N_div_4. replace (Z.of_nat N) with (2*(2*x2)) by lia. rewrite simpl_mul_div; lia.
        assert (- (Z.of_nat N) < -2 * x0 + 2 * x1 < Z.of_nat N). lia.

        unfold Fin_eq.
        cbn [proj1_sig] in *.
        left. apply (aux_no_rec_bound_eq x0 x1 (x)); try lia.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1.
      *unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        apply rewrite_mod_to_div in H; try lia.
        destruct H. ring_simplify in H.

        assert (proj1_sig g1 / 2 + 2 * proj1_sig t1 - proj1_sig g2 / 2 = (proj1_sig g1 / 2 - proj1_sig g2 / 2) + (proj1_sig t1) * 2). ring.
        rewrite H1 in H.

        apply (apply_mod _ _ 2) in H; try lia.
        rewrite Z_mod_plus in H; try lia.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4. rewrite H2 in H. replace (x * (x0 * 4)) with (x * x0 * 2 * 2) in H. 2:ring. rewrite Z_mod_mult in H.

        exfalso. apply (aux_no_rec_mod_plus2 (proj1_sig g1) (proj1_sig g2)); try lia.

        rewrite Zminus_mod. rewrite Hg1. rewrite Hg2. trivial.
      *unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        apply rewrite_mod_to_div in H; try lia.
        destruct H. ring_simplify in H.

        assert (proj1_sig g1 / 2 - 2 * proj1_sig t1 - proj1_sig g2 / 2 - 2 = (proj1_sig g1 / 2 - proj1_sig g2 / 2) + (- proj1_sig t1 - 1) * 2). ring.
        rewrite H1 in H.

        apply (apply_mod _ _ 2) in H; try lia.
        rewrite Z_mod_plus in H; try lia.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4. rewrite H2 in H. replace (x * (x0 * 4)) with (x * x0 * 2 * 2) in H. 2:ring. rewrite Z_mod_mult in H.

        exfalso. apply (aux_no_rec_mod_plus2 (proj1_sig g1) (proj1_sig g2)); try lia.

        rewrite Zminus_mod. rewrite Hg1. rewrite Hg2. trivial.
    + unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. unfold Fin_eq in H. simpl in H.
      apply rewrite_mod_to_div in H; try lia.
      destruct H. ring_simplify in H.

      assert (proj1_sig g1 / 2 + 2 * proj1_sig t1 - proj1_sig g2 / 2 = (proj1_sig g1 / 2 - proj1_sig g2 / 2) + (proj1_sig t1) * 2). ring.
      rewrite H1 in H.

      apply (apply_mod _ _ 2) in H; try lia.
      rewrite Z_mod_plus in H; try lia.
      apply mod_to_div in N_div_4; try lia. destruct N_div_4. rewrite H2 in H. replace (x * (x0 * 4)) with (x * x0 * 2 * 2) in H. 2:ring. rewrite Z_mod_mult in H.

      exfalso. apply (aux_no_rec_mod_plus2 (proj1_sig g1) (proj1_sig g2)); try lia.

      rewrite Zminus_mod. rewrite Hg1. rewrite Hg2. trivial.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1; destruct (proj1_sig t2 <? (Z.of_nat N)/2) eqn:H_t2.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        
        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        
        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4. rewrite H1 in H.
        assert (proj1_sig g2 mod 4 < 2). lia. apply div_small_mod4 in H2. destruct H2. rewrite H2 in H.
        assert (proj1_sig g1 mod 4 >= 2). lia. apply div_big_mod4 in H3. destruct H3. rewrite H3 in H.
        lia.
        (* in H: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (-2 * proj1_sig t2 + ((x0 * 4) / 2) - x * (x0 * 4) = 1). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
        (* in H2: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2. replace (- (Z.of_nat N / 2) + 2 * proj1_sig t2 + 1) with (1 - (Z.of_nat N / 2) + 2 * proj1_sig t2) in H2. 2:ring.

        exfalso. (* in H2: left odd right even *)
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (1 =  ((x0 * 4) / 2) - 2 * proj1_sig t1 + x * (x0 * 4)). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        destruct t1, t2. simpl in H_t1, H_t2.
        assert (Z.of_nat N / 2 <= x1 < Z.of_nat N). lia.
        assert (- (Z.of_nat N) < -x0 <= - (Z.of_nat N / 2)). rewrite <- Z.opp_le_mono. rewrite <- Z.opp_lt_mono. lia.
        assert (0 <= Z.of_nat N - (2 * (Z.of_nat N / 2))). rewrite <- Z.mod_eq; try lia. apply modulo_lt_divisor. lia.
        assert (Z.of_nat N / 2 * 2 = Z.of_nat N). apply mod_to_div in N_div_4; try lia. destruct N_div_4. replace (Z.of_nat N) with (2*(2*x2)) by lia. rewrite simpl_mul_div; lia.
        assert (- (Z.of_nat N) < -2 * x0 + 2 * x1 < Z.of_nat N). lia.

        unfold Fin_eq.
        cbn [proj1_sig] in *.
        left. apply (aux_no_rec_bound_eq x0 x1 (-x)); try lia.
    + unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. unfold Fin_eq in H. simpl in H.
      apply rewrite_mod_to_div in H; try lia.
      destruct H. ring_simplify in H.
      right. apply (aux_no_rec_same_mod g1 g2 x H). lia.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1; destruct (proj1_sig t2 <? (Z.of_nat N)/2) eqn:H_t2.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        destruct t1, t2. simpl in H_t1, H_t2.
        assert (0 <= x1 < Z.of_nat N / 2). lia.
        assert (- (Z.of_nat N / 2) < -x0 <= - 0). rewrite <- Z.opp_le_mono. rewrite <- Z.opp_lt_mono. lia.
        assert (0 <= Z.of_nat N - (2 * (Z.of_nat N / 2))). rewrite <- Z.mod_eq; try lia. apply modulo_lt_divisor. lia.
        assert (Z.of_nat N / 2 * 2 <= Z.of_nat N). lia.
        assert (- (Z.of_nat N) < -2 * x0 + 2 * x1 < Z.of_nat N). lia.

        unfold Fin_eq.
        cbn [proj1_sig] in *.
        left. apply (aux_no_rec_bound_eq x0 x1 (-x)); try lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2. replace (- (Z.of_nat N / 2) + 2 * proj1_sig t2 + 1) with (1 - (Z.of_nat N / 2) + 2 * proj1_sig t2) in H2. 2:ring.

        exfalso. (* in H2: left odd right even *)
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (1 =  - ((x0 * 4) / 2) - 2 * proj1_sig t1 + x * (x0 * 4)). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (-2 * proj1_sig t2 - (x0 * 4) / 2 - x * (x0 * 4) = 1). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
        (* in H2: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        
        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        
        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (forall a b:Z, -1 = a/2 - b/2 - a/2 + b/2 - 1). lia.
        assert (-1 = x * (x0 * 4) - proj1_sig g1 / 2 + proj1_sig g2 / 2 + (x0 * 4) / 2). rewrite <- H1. rewrite <- H.  ring_simplify. apply H2.
        replace (x0*4) with ((x0*2)*2) in H3. 2:lia. rewrite Z_div_mult in H3; try lia.

        assert (proj1_sig g1 mod 4 >= 2). lia. apply div_big_mod4 in H4. destruct H4. rewrite H4 in H3.
        assert (proj1_sig g2 mod 4 >= 2). lia. apply div_big_mod4 in H5. destruct H5. rewrite H5 in H3.
        lia.
        (* in H: right is even left is odd *)
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1; destruct (proj1_sig t2 <? (Z.of_nat N)/2) eqn:H_t2.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        
        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        
        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4. rewrite H1 in H.
        assert (proj1_sig g2 mod 4 < 2). lia. apply div_small_mod4 in H2. destruct H2. rewrite H2 in H.
        assert (proj1_sig g1 mod 4 >= 2). lia. apply div_big_mod4 in H3. destruct H3. rewrite H3 in H.
        lia.
        (* in H: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (-2 * proj1_sig t2 - ((x0 * 4) / 2) - x * (x0 * 4) = 1). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
        (* in H2: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2. replace (- (Z.of_nat N / 2) + 2 * proj1_sig t2 + 1) with (1 - (Z.of_nat N / 2) + 2 * proj1_sig t2) in H2. 2:ring.

        exfalso. (* in H2: left odd right even *)
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (1 =  -((x0 * 4) / 2) - 2 * proj1_sig t1 + x * (x0 * 4)). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        destruct t1, t2. simpl in H_t1, H_t2.
        assert (Z.of_nat N / 2 <= x1 < Z.of_nat N). lia.
        assert (- (Z.of_nat N) < -x0 <= - (Z.of_nat N / 2)). rewrite <- Z.opp_le_mono. rewrite <- Z.opp_lt_mono. lia.
        assert (0 <= Z.of_nat N - (2 * (Z.of_nat N / 2))). rewrite <- Z.mod_eq; try lia. apply modulo_lt_divisor. lia.
        assert (Z.of_nat N / 2 * 2 = Z.of_nat N). apply mod_to_div in N_div_4; try lia. destruct N_div_4. replace (Z.of_nat N) with (2*(2*x2)) by lia. rewrite simpl_mul_div; lia.
        assert (- (Z.of_nat N) < -2 * x0 + 2 * x1 < Z.of_nat N). lia.

        unfold Fin_eq.
        cbn [proj1_sig] in *.
        left. apply (aux_no_rec_bound_eq x0 x1 (-x)); try lia.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1.
      *unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        apply rewrite_mod_to_div in H; try lia.
        destruct H. ring_simplify in H.

        assert (proj1_sig g1 / 2 - 2 * proj1_sig t1 - proj1_sig g2 / 2 = (proj1_sig g1 / 2 - proj1_sig g2 / 2) + (- proj1_sig t1) * 2). ring.
        rewrite H1 in H.

        apply (apply_mod _ _ 2) in H; try lia.
        rewrite Z_mod_plus in H; try lia.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4. rewrite H2 in H. replace (x * (x0 * 4)) with (x * x0 * 2 * 2) in H. 2:ring. rewrite Z_mod_mult in H.

        exfalso. apply (aux_no_rec_mod_plus2 (proj1_sig g1) (proj1_sig g2)); try lia.

        rewrite Zminus_mod. rewrite Hg1. rewrite Hg2. trivial.
      *unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        apply rewrite_mod_to_div in H; try lia.
        destruct H. ring_simplify in H.

        assert (proj1_sig g1 / 2 + 2 * proj1_sig t1 - proj1_sig g2 / 2 + 2 = (proj1_sig g1 / 2 - proj1_sig g2 / 2) + (proj1_sig t1 + 1) * 2). ring.
        rewrite H1 in H.

        apply (apply_mod _ _ 2) in H; try lia.
        rewrite Z_mod_plus in H; try lia.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4. rewrite H2 in H. replace (x * (x0 * 4)) with (x * x0 * 2 * 2) in H. 2:ring. rewrite Z_mod_mult in H.

        exfalso. apply (aux_no_rec_mod_plus2 (proj1_sig g1) (proj1_sig g2)); try lia.

        rewrite Zminus_mod. rewrite Hg1. rewrite Hg2. trivial.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1; destruct (proj1_sig t2 <? (Z.of_nat N)/2) eqn:H_t2.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        destruct t1, t2. simpl in H_t1, H_t2.
        assert (0 <= x1 < Z.of_nat N / 2). lia.
        assert (- (Z.of_nat N / 2) < -x0 <= - 0). rewrite <- Z.opp_le_mono. rewrite <- Z.opp_lt_mono. lia.
        assert (0 <= Z.of_nat N - (2 * (Z.of_nat N / 2))). rewrite <- Z.mod_eq; try lia. apply modulo_lt_divisor. lia.
        assert (Z.of_nat N / 2 * 2 <= Z.of_nat N). lia.
        assert (- (Z.of_nat N) < -2 * x0 + 2 * x1 < Z.of_nat N). lia.

        unfold Fin_eq.
        cbn [proj1_sig] in *.
        left. apply (aux_no_rec_bound_eq x0 x1 x H2 H7).
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2.

        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (-2 * proj1_sig t1 - (x0 * 4) / 2 - x * (x0 * 4) = 1). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
        (* in H2: right is even left is odd *)
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        unfold f_div4 in H0. rewrite Hg1 in H0. rewrite Hg2 in H0. rewrite H_t2 in H0. unfold Fin_eq in H0. simpl in H0.
        assert (Z.of_nat N > 0). lia.
        pose proof (aux_sub_mod_eq _ _ _ _ _ H1 H H0). destruct H2. ring_simplify in H2. replace (- (Z.of_nat N / 2) + 2 * proj1_sig t2 + 1) with (1 - (Z.of_nat N / 2) + 2 * proj1_sig t2) in H2. 2:ring.

        exfalso. (* in H2: left odd right even *)
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (1 =  - ((x0 * 4) / 2) - 2 * proj1_sig t2 + x * (x0 * 4)). rewrite <- H3. lia.
        replace (x0*4) with ((x0*2)*2) in H4. 2:lia. rewrite Z_div_mult in H4; try lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        
        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        
        exfalso.
        apply mod_to_div in N_div_4; try lia. destruct N_div_4.
        assert (forall a b:Z, 1 = a/2 - b/2 - a/2 + b/2 + 1). lia.
        assert (1 = x * (x0 * 4) - proj1_sig g1 / 2 + proj1_sig g2 / 2 - (x0 * 4) / 2). rewrite <- H1. rewrite <- H.  ring_simplify. apply H2.
        replace (x0*4) with ((x0*2)*2) in H3. 2:lia. rewrite Z_div_mult in H3; try lia.

        assert (proj1_sig g1 mod 4 >= 2). lia. apply div_big_mod4 in H4. destruct H4. rewrite H4 in H3.
        assert (proj1_sig g2 mod 4 >= 2). lia. apply div_big_mod4 in H5. destruct H5. rewrite H5 in H3.
        lia.
        (* in H: right is even left is odd *)
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        apply rewrite_mod_to_div in H; try lia.
        destruct H. ring_simplify in H.
        right. apply (aux_no_rec_same_mod g1 g2 x H). lia.
      * unfold f_div4 in H. rewrite Hg1 in H. rewrite Hg2 in H. rewrite H_t1 in H. unfold Fin_eq in H. simpl in H.
        apply rewrite_mod_to_div in H; try lia.
        destruct H. ring_simplify in H.
        right. apply (aux_no_rec_same_mod g1 g2 x H). lia.
  - unfold at_least_2_by_workshop.
    intros.
    destruct (Z_mod_2_is_0_or_1 (proj1_sig a + proj1_sig t)) as [H_0|H_1]; destruct (proj1_sig t <? (Z.of_nat N)/2) eqn:H_t.
    + exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t))). exists (project_to_Fin2 (2*(proj1_sig a - proj1_sig t)+1)).
      split; try split.
      * set (g1:=project_to_Fin2 (2 * (proj1_sig a + proj1_sig t))).
        assert (proj1_sig g1 mod 4 = 0).
        {
          unfold g1. set (K:=2 * (proj1_sig a + proj1_sig t)). simpl. unfold K.
          replace (2 * (proj1_sig a + proj1_sig t)) with (2 * (proj1_sig a + proj1_sig t) + 0). 2:ring.
          replace (Z.of_nat (N + (N + 0))) with (2 * (Z.of_nat (N))). 2:lia.
          rewrite aux_at_least_2_by_wrkshp; lia.
        }
        assert (Fin_eq _ (f_div4 g1 t) (project_to_Fin ((proj1_sig g1/2 - proj1_sig t)))).
        unfold f_div4. rewrite H. unfold Fin_eq. reflexivity.

        assert (Fin_eq _ (project_to_Fin (proj1_sig g1 / 2 - proj1_sig t)) a).
        unfold Fin_eq, g1. set (A:=2 * (proj1_sig a + proj1_sig t)). simpl. unfold A.
        rewrite mod_div2. setoid_rewrite Z.add_mod at 1; try lia. rewrite Z.mod_mod; try lia. rewrite <- Z.add_mod; try lia.
        replace (proj1_sig a + proj1_sig t + - proj1_sig t) with (proj1_sig a). 2:ring.
        rewrite Z.mod_small; try lia. destruct a. simpl. assumption.

        unfold Fin_eq in H0, H1. rewrite H1 in H0.
        unfold Fin_eq. exact H0.
      * set (g1:=project_to_Fin2 (2 * (proj1_sig a - proj1_sig t) + 1)).
        assert (proj1_sig g1 mod 4 = 1).
        {
          unfold g1. set (K:=2 * (proj1_sig a - proj1_sig t) + 1). simpl. unfold K.
          replace (Z.of_nat (N + (N + 0))) with (2 * (Z.of_nat (N))). 2:lia.
          assert ((proj1_sig a - proj1_sig t) mod 2 = 0). rewrite Z.add_mod; try lia. rewrite <- plus_minus_mod2; try lia. rewrite <- Z.add_mod; lia.
          rewrite aux_at_least_2_by_wrkshp; lia.
        }
        assert (Fin_eq _ (f_div4 g1 t) (project_to_Fin ((proj1_sig g1/2 + proj1_sig t)))).
        unfold f_div4. rewrite H. rewrite H_t. unfold Fin_eq. reflexivity.

        assert (Fin_eq _ (project_to_Fin (proj1_sig g1 / 2 + proj1_sig t)) a).
        unfold Fin_eq, g1. set (A:=2 * (proj1_sig a - proj1_sig t) + 1). simpl. unfold A.
        rewrite mod_div2p1. setoid_rewrite Z.add_mod at 1; try lia. rewrite Z.mod_mod; try lia. rewrite <- Z.add_mod; try lia.
        replace (proj1_sig a - proj1_sig t + proj1_sig t) with (proj1_sig a). 2:ring.
        rewrite Z.mod_small; try lia. destruct a. simpl. assumption.

        unfold Fin_eq in H0, H1. rewrite H1 in H0.
        unfold Fin_eq. exact H0.
      * unfold Fin_eq. cbn [proj1_sig project_to_Fin2].
        intro. apply rewrite_mod_to_div in H; try lia.
        destruct H. lia.
    + exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t))). exists (project_to_Fin2 (2*(proj1_sig a - proj1_sig t) - Z.of_nat N - 1)).
      split; try split.
      * set (g1:=project_to_Fin2 (2 * (proj1_sig a + proj1_sig t))).
        assert (proj1_sig g1 mod 4 = 0).
        {
          unfold g1. set (K:=2 * (proj1_sig a + proj1_sig t)). simpl. unfold K.
          replace (2 * (proj1_sig a + proj1_sig t)) with (2 * (proj1_sig a + proj1_sig t) + 0). 2:ring.
          replace (Z.of_nat (N + (N + 0))) with (2 * (Z.of_nat (N))). 2:lia.
          rewrite aux_at_least_2_by_wrkshp; lia.
        }
        assert (Fin_eq _ (f_div4 g1 t) (project_to_Fin ((proj1_sig g1/2 - proj1_sig t)))).
        unfold f_div4. rewrite H. unfold Fin_eq. reflexivity.

        assert (Fin_eq _ (project_to_Fin (proj1_sig g1 / 2 - proj1_sig t)) a).
        unfold Fin_eq, g1. set (A:=2 * (proj1_sig a + proj1_sig t)). simpl. unfold A.
        rewrite mod_div2. setoid_rewrite Z.add_mod at 1; try lia. rewrite Z.mod_mod; try lia. rewrite <- Z.add_mod; try lia.
        replace (proj1_sig a + proj1_sig t + - proj1_sig t) with (proj1_sig a). 2:ring.
        rewrite Z.mod_small; try lia. destruct a. simpl. assumption.

        unfold Fin_eq in H0, H1. rewrite H1 in H0.
        unfold Fin_eq. exact H0.
      * set (g1:=project_to_Fin2 (2 * (proj1_sig a - proj1_sig t) - Z.of_nat N - 1)).
        assert (proj1_sig g1 mod 4 = 3).
        {
          unfold g1. set (K:=2 * (proj1_sig a - proj1_sig t) - Z.of_nat N - 1). simpl. unfold K.
          replace (Z.of_nat (N + (N + 0))) with (2 * (Z.of_nat (N))). 2:lia.
          assert ((proj1_sig a - proj1_sig t) mod 2 = 0). rewrite Z.add_mod; try lia. rewrite <- plus_minus_mod2; try lia. rewrite <- Z.add_mod; lia.
          setoid_rewrite Z.mod_eq at 2; try lia. setoid_rewrite Z.add_mod at 1; try lia. setoid_rewrite Z.add_mod at 2; try lia. setoid_rewrite Z.add_mod at 3; try lia.
          replace ((2 * (proj1_sig a - proj1_sig t)) mod 4) with 0. 2:{ symmetry. rewrite div_to_mod; try lia. apply mod_to_div in H; try lia. destruct H. exists x. lia. }
          replace (- Z.of_nat N mod 4) with 0. 2:{ symmetry. apply elim_minus_one; lia. }
          replace ((0 + 0) mod 4 + - (1) mod 4) with 3. 2:trivial.
          replace (- (2 * Z.of_nat N * ((2 * (proj1_sig a - proj1_sig t) - Z.of_nat N - 1) / (2 * Z.of_nat N))) mod 4) with 0. 2:{ symmetry. apply div_to_mod; try lia. apply mod_to_div in N_div_4; try lia. destruct N_div_4. exists (- (2 * x * ((2 * (proj1_sig a - proj1_sig t) - Z.of_nat N - 1) / (2 * Z.of_nat N)))). lia. }
          trivial.
        }
        assert (Fin_eq _ (f_div4 g1 t) (project_to_Fin ((proj1_sig g1/2 + Z.of_nat N / 2 + 1 + proj1_sig t)))).
        unfold f_div4. rewrite H. rewrite H_t. unfold Fin_eq. reflexivity.

        assert (Fin_eq _ (project_to_Fin (proj1_sig g1/2 + Z.of_nat N / 2 + 1 + proj1_sig t)) a).
        unfold Fin_eq, g1. set (A:=Z.of_nat N / 2 + proj1_sig t). set (B:=2 * (proj1_sig a - proj1_sig t) - Z.of_nat N - 1). simpl. unfold A, B.
        rewrite mod_div2_gnl. apply mod_to_div in N_div_4; try lia. destruct N_div_4. replace (2 * (proj1_sig a - proj1_sig t) - Z.of_nat N - 1) with ((proj1_sig a - proj1_sig t - 2 * x) * 2 + (-1)). 2:lia.
        rewrite (Z_div_plus_full_l); try lia.
        replace ((proj1_sig a - proj1_sig t - 2 * x + -1 / 2) mod Z.of_nat N + Z.of_nat N / 2 + 1 + proj1_sig t) with ((proj1_sig a - proj1_sig t - 2 * x + -1 / 2) mod Z.of_nat N + (Z.of_nat N / 2 + 1 + proj1_sig t)). 2:ring.
        rewrite Z.add_mod; try lia. rewrite Z.mod_mod; try lia. rewrite <- Z.add_mod; try lia.
        replace (-1/2)  with (-1). 2:trivial.
        replace (2*x) with (Z.of_nat N / 2). 2:{ rewrite H1. trivial. rewrite Zdivide_Zdiv_eq_2; replace (4) with (2*2); try lia. exact (Z.divide_factor_l 2 2). rewrite simpl_mul_div; lia. }
        replace (proj1_sig a - proj1_sig t - Z.of_nat N / 2 + -1 + (Z.of_nat N / 2 + 1 + proj1_sig t)) with (proj1_sig a). 2:lia.
        rewrite Z.mod_small; try lia. destruct a. simpl. assumption.

        unfold Fin_eq in H0, H1. rewrite H1 in H0.
        unfold Fin_eq. exact H0.
      * unfold Fin_eq. cbn [proj1_sig project_to_Fin2].
        pose proof div_by_2_2N.
        apply apply_mod_2. setoid_rewrite <- Zmod_div_mod; try lia; try assumption.
        pose proof (div_prop_N_even N_div_4).
        replace (2 * (proj1_sig a - proj1_sig t) - Z.of_nat N - 1) with (2 * (proj1_sig a - proj1_sig t - Z.of_nat N/2 - 1) +1) by lia.
        rewrite fact_2_in_mod. rewrite fact_2_p1_in_mod. lia.
    + exists (project_to_Fin2 (2*(proj1_sig a - proj1_sig t))). exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t)+1)).
      split; try split.
      * set (g1:=project_to_Fin2 (2 * (proj1_sig a - proj1_sig t))).
        assert (proj1_sig g1 mod 4 = 2).
        {
          unfold g1. set (K:=2 * (proj1_sig a - proj1_sig t)). simpl. unfold K.
          replace (2 * (proj1_sig a - proj1_sig t)) with (2 * (proj1_sig a - proj1_sig t) + 0). 2:ring.
          replace (Z.of_nat (N + (N + 0))) with (2 * (Z.of_nat (N))). 2:lia.
          assert ((proj1_sig a - proj1_sig t) mod 2 = 1). rewrite Z.add_mod; try lia. rewrite <- plus_minus_mod2; try lia. rewrite <- Z.add_mod; lia.
          rewrite aux_at_least_2_by_wrkshp; lia.
        }
        assert (Fin_eq _ (f_div4 g1 t) (project_to_Fin ((proj1_sig g1/2 + proj1_sig t)))).
        unfold f_div4. rewrite H. unfold Fin_eq. reflexivity.

        assert (Fin_eq _ (project_to_Fin (proj1_sig g1 / 2 + proj1_sig t)) a).
        unfold Fin_eq, g1. set (A:=2 * (proj1_sig a + proj1_sig t)). simpl. unfold A.
        rewrite mod_div2. setoid_rewrite Z.add_mod at 1; try lia. rewrite Z.mod_mod; try lia. rewrite <- Z.add_mod; try lia.
        replace (proj1_sig a + - proj1_sig t + proj1_sig t) with (proj1_sig a). 2:ring.
        rewrite Z.mod_small; try lia. destruct a. simpl. assumption.

        unfold Fin_eq in H0, H1. rewrite H1 in H0.
        unfold Fin_eq. exact H0.
      * set (g1:=project_to_Fin2 (2 * (proj1_sig a + proj1_sig t) + 1)).
        assert (proj1_sig g1 mod 4 = 3).
        {
          unfold g1. set (K:=2 * (proj1_sig a - proj1_sig t) + 1). simpl. unfold K.
          replace (Z.of_nat (N + (N + 0))) with (2 * (Z.of_nat (N))). 2:lia.
          rewrite aux_at_least_2_by_wrkshp; lia.
        }
        assert (Fin_eq _ (f_div4 g1 t) (project_to_Fin ((proj1_sig g1/2 - proj1_sig t)))).
        unfold f_div4. rewrite H. rewrite H_t. unfold Fin_eq. reflexivity.

        assert (Fin_eq _ (project_to_Fin (proj1_sig g1 / 2 - proj1_sig t)) a).
        unfold Fin_eq, g1. set (A:=2 * (proj1_sig a + proj1_sig t) + 1). simpl. unfold A.
        rewrite mod_div2p1. setoid_rewrite Z.add_mod at 1; try lia. rewrite Z.mod_mod; try lia. rewrite <- Z.add_mod; try lia.
        replace (proj1_sig a + proj1_sig t + - proj1_sig t) with (proj1_sig a). 2:ring.
        rewrite Z.mod_small; try lia. destruct a. simpl. assumption.

        unfold Fin_eq in H0, H1. rewrite H1 in H0.
        unfold Fin_eq. exact H0.
      * unfold Fin_eq. cbn [proj1_sig project_to_Fin2].
        intro. apply rewrite_mod_to_div in H; try lia.
        destruct H. lia.
    + exists (project_to_Fin2 (2*(proj1_sig a - proj1_sig t))). exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t) - Z.of_nat N + 3)).
      split; try split.
      * set (g1:=project_to_Fin2 (2 * (proj1_sig a - proj1_sig t))).
        assert (proj1_sig g1 mod 4 = 2).
        {
          unfold g1. set (K:=2 * (proj1_sig a - proj1_sig t)). simpl. unfold K.
          replace (2 * (proj1_sig a - proj1_sig t)) with (2 * (proj1_sig a - proj1_sig t) + 0). 2:ring.
          replace (Z.of_nat (N + (N + 0))) with (2 * (Z.of_nat (N))). 2:lia.
          assert ((proj1_sig a - proj1_sig t) mod 2 = 1). rewrite Z.add_mod; try lia. rewrite <- plus_minus_mod2; try lia. rewrite <- Z.add_mod; lia.
          rewrite aux_at_least_2_by_wrkshp; lia.
        }
        assert (Fin_eq _ (f_div4 g1 t) (project_to_Fin ((proj1_sig g1/2 + proj1_sig t)))).
        unfold f_div4. rewrite H. unfold Fin_eq. reflexivity.

        assert (Fin_eq _ (project_to_Fin (proj1_sig g1 / 2 + proj1_sig t)) a).
        unfold Fin_eq, g1. set (A:=2 * (proj1_sig a + proj1_sig t)). simpl. unfold A.
        rewrite mod_div2. setoid_rewrite Z.add_mod at 1; try lia. rewrite Z.mod_mod; try lia. rewrite <- Z.add_mod; try lia.
        replace (proj1_sig a + - proj1_sig t + proj1_sig t) with (proj1_sig a). 2:ring.
        rewrite Z.mod_small; try lia. destruct a. simpl. assumption.

        unfold Fin_eq in H0, H1. rewrite H1 in H0.
        unfold Fin_eq. exact H0.
      * set (g1:=2 * (proj1_sig a + proj1_sig t) - Z.of_nat N + 3).
        assert (proj1_sig (project_to_Fin2 g1) mod 4 = 1).
        {
          unfold g1. set (K:=2 * (proj1_sig a + proj1_sig t) - Z.of_nat N + 3). simpl. unfold K.
          replace (Z.of_nat (N + (N + 0))) with (2 * (Z.of_nat (N))). 2:lia.
          setoid_rewrite Z.mod_eq at 2; try lia. setoid_rewrite Z.add_mod at 1; try lia. setoid_rewrite Z.add_mod at 2; try lia. setoid_rewrite Z.add_mod at 3; try lia.
          replace ((2 * (proj1_sig a + proj1_sig t)) mod 4) with 2. 2:{ symmetry. replace 2 with (2 mod 4) at 2; try trivial. apply rewrite_div_to_mod; try lia. replace 1 with (1 mod 2) in H_1; try trivial. apply rewrite_mod_to_div in H_1; try lia. destruct H_1. exists x. lia. }
          replace (- Z.of_nat N mod 4) with 0. 2:{ symmetry. apply elim_minus_one; lia. }
          replace (((2 + 0) mod 4 + 3 mod 4) mod 4) with 1. 2:trivial.
          replace (- (2 * Z.of_nat N * ((2 * (proj1_sig a + proj1_sig t) - Z.of_nat N + 3) / (2 * Z.of_nat N))) mod 4) with 0. 2:{ symmetry. apply div_to_mod; try lia. apply mod_to_div in N_div_4; try lia. destruct N_div_4. exists (- (2 * x * ((2 * (proj1_sig a + proj1_sig t) - Z.of_nat N + 3) / (2 * Z.of_nat N)))). lia. }
          trivial.
        }

        unfold Fin_eq, f_div4. rewrite H. rewrite H_t. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].

        rewrite mod_div2_gnl.
        replace ((g1 / 2) mod Z.of_nat N + Z.of_nat N / 2 - 1 - proj1_sig t) with ((g1 / 2 mod Z.of_nat N) + (Z.of_nat N / 2 - 1 - proj1_sig t)) by ring.
        rewrite Zplus_mod_idemp_l.

        pose proof (div_prop_N_even N_div_4).
        replace g1 with ((proj1_sig a + proj1_sig t - Z.of_nat N/2 + 1)*2 +1) by lia.
        rewrite Z_div_plus_full_l; try lia.
        replace (1/2) with 0 by trivial.
        replace ((proj1_sig a + proj1_sig t - Z.of_nat N / 2 + 1 + 0 + (Z.of_nat N / 2 - 1 - proj1_sig t))) with (proj1_sig a) by ring.

        apply Z.mod_small. destruct a. simpl in *. assumption.
      * unfold Fin_eq. cbn [proj1_sig project_to_Fin2].
        pose proof div_by_2_2N.
        apply apply_mod_2. setoid_rewrite <- Zmod_div_mod; try lia; try assumption.
        pose proof (div_prop_N_even N_div_4).
        replace (2 * (proj1_sig a + proj1_sig t) - Z.of_nat N + 3) with (2 * (proj1_sig a + proj1_sig t - Z.of_nat N/2 + 1) +1) by lia.
        rewrite fact_2_in_mod. rewrite fact_2_p1_in_mod. lia.
  - unfold injective. (* all workshop visited - workshop visitad less than one time *)
    intros.
    destruct (case_mod_4 (proj1_sig g)) as [H_0 | [H_1 | [H_2 | H_3]]].
    + unfold f_div4 in H. rewrite H_0 in H. simpl in H.
      apply aux_inj_odd in H; try lia.
      apply elim_minus_mod in H; try lia.
      rewrite (Z.mod_small (proj1_sig t1) (Z.of_nat N))in H. destruct t1. simpl. assumption.
      rewrite (Z.mod_small (proj1_sig t2) (Z.of_nat N))in H. destruct t2. simpl. assumption.
      exact H.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1; destruct (proj1_sig t2 <? (Z.of_nat N)/2) eqn:H_t2.
      * unfold f_div4 in H. rewrite H_1 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        apply aux_inj_odd in H; try lia.
        rewrite (Z.mod_small (proj1_sig t1) (Z.of_nat N))in H. destruct t1. simpl. assumption.
        rewrite (Z.mod_small (proj1_sig t2) (Z.of_nat N))in H. destruct t2. simpl. assumption.
        exact H.
      * unfold f_div4 in H. rewrite H_1 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        destruct t1. destruct t2. unfold Fin_eq in H. simpl in *.
        assert (-Z.of_nat N < ((Z.of_nat N / 2) - 1 - x0) - x< Z.of_nat N). lia.
        apply (aux_inj (proj1_sig g / 2) _ _) in H0; try lia.
        rewrite H.
        apply rewrite_div_to_mod; try lia. exists 0.
        ring_simplify. destruct g. simpl. lia.
      * unfold f_div4 in H. rewrite H_1 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        destruct t1. destruct t2. unfold Fin_eq in H. simpl in *.
        symmetry in H.
        assert (-Z.of_nat N < ((Z.of_nat N / 2) - 1 - x) - x0< Z.of_nat N). lia.
        apply (aux_inj (proj1_sig g / 2) _ _) in H0; try lia.
        rewrite H.
        apply rewrite_div_to_mod; try lia. exists 0.
        ring_simplify. destruct g. simpl. lia.
      * unfold f_div4 in H. rewrite H_1 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        destruct t1. destruct t2. simpl in H.
        apply aux_inj in H; try lia.
        unfold Fin_eq. simpl. lia.
    + unfold f_div4 in H. rewrite H_2 in H. simpl in H.
      apply aux_inj_odd in H; try lia.
      rewrite (Z.mod_small (proj1_sig t1) (Z.of_nat N))in H. destruct t1. simpl. assumption.
      rewrite (Z.mod_small (proj1_sig t2) (Z.of_nat N))in H. destruct t2. simpl. assumption.
      exact H.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2) eqn:H_t1; destruct (proj1_sig t2 <? (Z.of_nat N)/2) eqn:H_t2.
      * unfold f_div4 in H. rewrite H_3 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        destruct t1. destruct t2. simpl in H.
        apply aux_inj in H; try lia.
        unfold Fin_eq. simpl. lia.
      * unfold f_div4 in H. rewrite H_3 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        destruct t1. destruct t2. unfold Fin_eq in H. simpl in *.
        assert (-Z.of_nat N < (- (Z.of_nat N / 2) + 1 + x0) - - x< Z.of_nat N). lia.
        apply (aux_inj (proj1_sig g / 2) (-x) _) in H0; try lia.
        rewrite Z.add_opp_r. rewrite H.
        apply rewrite_div_to_mod; try lia. exists 1.
        pose proof (div_prop_N_even N_div_4).
        ring_simplify. rewrite H1. destruct g. simpl. lia.
      * unfold f_div4 in H. rewrite H_3 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        destruct t1. destruct t2. unfold Fin_eq in H. simpl in *.
        symmetry in H.
        assert (-Z.of_nat N < (- (Z.of_nat N / 2) + 1 + x) - - x0< Z.of_nat N). lia.
        apply (aux_inj (proj1_sig g / 2) _ _) in H0; try lia.
        rewrite Z.add_opp_r. rewrite H.
        apply rewrite_div_to_mod; try lia. exists 1.
        pose proof (div_prop_N_even N_div_4).
        ring_simplify. rewrite H1. destruct g. simpl. lia.
      * unfold f_div4 in H. rewrite H_3 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        destruct t1. destruct t2. simpl in H.
        apply aux_inj in H; try lia.
        unfold Fin_eq. simpl. lia.
Qed.



(* VERY LAST CASE *)

Definition f_6 : ScheduleType :=
    fun (g : Set2N) (t : SetN) =>
        let val_g := proj1_sig g in
        let val_t := proj1_sig t in
        if val_g mod 4 =? 0 then 
            project_to_Fin (val_g/2 - val_t)

        else if andb (val_g mod 4 =? 1) (val_t <? (Z.of_nat N)/2 - 1) then
            project_to_Fin (val_g/2 + val_t)
        else if val_g mod 4 =? 1 then
            project_to_Fin (val_g/2 + (Z.of_nat N)/2 - 2 - val_t)

        else if andb (val_g mod 4 =? 2) (val_t =? Z.of_nat N - 3) then
            project_to_Fin (val_g/2 + Z.of_nat N - 2)
        else if andb (val_g mod 4 =? 2) (val_t =? Z.of_nat N - 2) then
            project_to_Fin (val_g/2 + Z.of_nat N - 1)
        else if andb (val_g mod 4 =? 2) (val_t =? Z.of_nat N - 1) then
            project_to_Fin (val_g/2 + Z.of_nat N - 3)
        else if val_g mod 4 =? 2 then
            project_to_Fin (val_g/2 + val_t)

        else if andb (val_g mod 4 =? 3) (val_t =? Z.of_nat N - 3) then
            project_to_Fin (val_g/2 + Z.of_nat N / 2)
        else if andb (val_g mod 4 =? 3) (val_t =? Z.of_nat N - 2) then
            project_to_Fin (val_g/2 + Z.of_nat N / 2 + 1)
        else if andb (val_g mod 4 =? 3) (val_t =? Z.of_nat N - 1) then
            project_to_Fin (val_g/2 + Z.of_nat N / 2 - 1)
        else if andb (val_g mod 4 =? 3) (val_t <? (Z.of_nat N)/2 - 1) then
            project_to_Fin (val_g/2 - val_t)
        else project_to_Fin (val_g/2 - (Z.of_nat N)/2 + 2 + val_t).

Lemma N_is_even: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> Z.of_nat N = 2*(Z.of_nat N / 2).
Proof.
  intro. destruct H.
  assert (H_even: Z.of_nat N mod 2 = 0).
  replace 2 with (2 mod 4) in H0 by trivial.
  apply rewrite_mod_to_div in H0; try lia. destruct H0.
  apply div_to_mod; try lia. exists (x*2+1). lia.

  assert (H_of_nat_val : Z.of_nat N = 2 * (Z.of_nat N / 2) + (Z.of_nat N) mod 2).
  rewrite (Z.mod_eq (Z.of_nat N) 2); lia.
  
  rewrite H_even in H_of_nat_val. ring_simplify in H_of_nat_val.

  exact H_of_nat_val.
Qed.

Lemma f_6_injective: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> injective f_6.
    intro H_N. unfold injective. intros.
    destruct (case_mod_4 (proj1_sig g)) as [H_0 | [H_1 | [H_2 | H_3]]].
    + unfold f_6 in H. rewrite H_0 in H. simpl in H.
      apply aux_inj_odd in H; try lia.
      apply elim_minus_mod in H; try lia.
      rewrite (Z.mod_small (proj1_sig t1) (Z.of_nat N))in H. destruct t1. simpl. assumption.
      rewrite (Z.mod_small (proj1_sig t2) (Z.of_nat N))in H. destruct t2. simpl. assumption.
      exact H.
    + destruct (proj1_sig t1 <? (Z.of_nat N)/2-1) eqn:H_t1; destruct (proj1_sig t2 <? (Z.of_nat N)/2-1) eqn:H_t2.
      * unfold f_6 in H. rewrite H_1 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        apply aux_inj_odd in H; try lia.
        rewrite (Z.mod_small (proj1_sig t1) (Z.of_nat N))in H. destruct t1. simpl. assumption.
        rewrite (Z.mod_small (proj1_sig t2) (Z.of_nat N))in H. destruct t2. simpl. assumption.
        exact H.
      * unfold f_6 in H. rewrite H_1 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        destruct t1. destruct t2. unfold Fin_eq in *. simpl in *.
        assert (-Z.of_nat N < ((Z.of_nat N / 2) - 2 - x0) - x< Z.of_nat N). lia.
        apply (aux_inj (proj1_sig g / 2) _ _) in H0; try lia.
        rewrite H.
        apply rewrite_div_to_mod; try lia. exists 0.
        ring_simplify. destruct g. simpl. lia.
      * unfold f_6 in H. rewrite H_1 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        destruct t1. destruct t2. unfold Fin_eq in H. simpl in *.
        symmetry in H.
        assert (-Z.of_nat N < ((Z.of_nat N / 2) - 2 - x) - x0< Z.of_nat N). lia.
        apply (aux_inj (proj1_sig g / 2) _ _) in H0; try lia.
        rewrite H.
        apply rewrite_div_to_mod; try lia. exists 0.
        ring_simplify. destruct g. simpl. lia.
      * unfold f_6 in H. rewrite H_1 in H. rewrite H_t1 in H. rewrite H_t2 in H. simpl in H.
        destruct t1. destruct t2. simpl in H.
        apply aux_inj in H; try lia.
        unfold Fin_eq. simpl. lia.
    + destruct (proj1_sig t1 =? Z.of_nat N - 3) eqn:H_t1; destruct (proj1_sig t2 =? Z.of_nat N - 3) eqn:H_t2.
      ++ unfold Fin_eq. lia.
      ++ destruct (proj1_sig t2 =? Z.of_nat N - 2) eqn:H_t2p; unfold f_6 in H; rewrite H_2 in H; rewrite H_t1 in H; rewrite H_t2 in H; rewrite H_t2p in H; simpl in H.
        +++ apply aux_inj in H; try lia.
        +++ destruct (proj1_sig t2 =? Z.of_nat N - 1) eqn:H_t2pp.
            ++++ apply aux_inj in H; try lia.
            ++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N - 2) with (x / 2 + (Z.of_nat N - 2)) in H by ring.
              apply aux_inj in H; try lia.
              destruct t2. simpl in *. lia.
      ++ destruct (proj1_sig t1 =? Z.of_nat N - 2) eqn:H_t1p; unfold f_6 in H; rewrite H_2 in H; rewrite H_t1 in H; rewrite H_t2 in H; rewrite H_t1p in H; simpl in H.
        +++ apply aux_inj in H; try lia.
        +++ destruct (proj1_sig t1 =? Z.of_nat N - 1) eqn:H_t1pp.
            ++++ apply aux_inj in H; try lia.
            ++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N - 2) with (x / 2 + (Z.of_nat N - 2)) in H by ring.
              apply aux_inj in H; try lia.
              destruct t1. simpl in *. lia.
      ++ destruct (proj1_sig t1 =? Z.of_nat N - 2) eqn:H_t1p; destruct (proj1_sig t2 =? Z.of_nat N - 2) eqn:H_t2p.
        +++ unfold Fin_eq. lia.
        +++ destruct (proj1_sig t2 =? Z.of_nat N - 1) eqn:H_t2pp; unfold f_6 in H; rewrite H_2 in H; rewrite H_t1 in H; rewrite H_t2 in H; rewrite H_t1p in H; rewrite H_t2p in H; rewrite H_t2pp in H; simpl in H.
          ++++ apply aux_inj in H; try lia.
          ++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N - 1) with (x / 2 + (Z.of_nat N - 1)) in H by ring.
                apply aux_inj in H; try lia.
                destruct t2. simpl in *. lia.
        +++ destruct (proj1_sig t1 =? Z.of_nat N - 1) eqn:H_t1pp; unfold f_6 in H; rewrite H_2 in H; rewrite H_t1 in H; rewrite H_t2 in H; rewrite H_t1p in H; rewrite H_t2p in H; rewrite H_t1pp in H; simpl in H.
          ++++ apply aux_inj in H; try lia.
          ++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N - 1) with (x / 2 + (Z.of_nat N - 1)) in H by ring.
                apply aux_inj in H; try lia.
                destruct t1. simpl in *. lia.
        +++ destruct (proj1_sig t1 =? Z.of_nat N - 1) eqn:H_t1pp; destruct (proj1_sig t2 =? Z.of_nat N - 1) eqn:H_t2pp; unfold f_6 in H; rewrite H_2 in H; rewrite H_t1 in H; rewrite H_t2 in H; rewrite H_t1p in H; rewrite H_t2p in H; rewrite H_t1pp in H; rewrite H_t2pp in H; simpl in H.
          ++++ unfold Fin_eq. lia.
          ++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N - 3) with (x / 2 + (Z.of_nat N - 3)) in H by ring.
                apply aux_inj in H; try lia.
                destruct t2. simpl in *. lia.
          ++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N - 3) with (x / 2 + (Z.of_nat N - 3)) in H by ring.
                apply aux_inj in H; try lia.
                destruct t1. simpl in *. lia.
          ++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N - 3) with (x / 2 + (Z.of_nat N - 3)) in H by ring.
                unfold Fin_eq. apply aux_inj in H; try lia.
                destruct t1, t2. simpl in *. lia.
    + destruct (proj1_sig t1 =? Z.of_nat N - 3) eqn:H_t1; destruct (proj1_sig t2 =? Z.of_nat N - 3) eqn:H_t2.
      ++ unfold Fin_eq. lia.
      ++ destruct (proj1_sig t2 =? Z.of_nat N - 2) eqn:H_t2p; unfold f_6 in H; rewrite H_3 in H; rewrite H_t1 in H; rewrite H_t2 in H; rewrite H_t2p in H; simpl in H.
        +++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N / 2 + 1) with (x / 2 + (Z.of_nat N / 2 + 1)) in H by ring.
          apply aux_inj in H; try lia.
        +++ destruct (proj1_sig t2 =? Z.of_nat N - 1) eqn:H_t2pp.
            ++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N / 2 - 1) with (x / 2 + (Z.of_nat N / 2 - 1)) in H by ring.
              apply aux_inj in H; try lia.
            ++++ destruct (proj1_sig t2 <? Z.of_nat N / 2 - 1) eqn:H_t2ppp.
              +++++ apply aux_inj in H; try lia.
                all: destruct t2; simpl in *; pose proof N_is_even; lia.
              +++++ destruct g. simpl in *. replace (x / 2 - Z.of_nat N / 2 + 2 + proj1_sig t2) with (x / 2 + (- (Z.of_nat N / 2) + 2 + proj1_sig t2)) in H by ring.
                apply aux_inj in H; try lia.
                2:{ destruct t2. simpl in *. pose proof N_is_even. lia. }
                destruct t2. simpl in *.
                assert (2*(Z.of_nat N / 2) = x0 + 2). lia.
                rewrite <- (N_is_even H_N) in H0. lia.
      ++ destruct (proj1_sig t1 =? Z.of_nat N - 2) eqn:H_t1p; unfold f_6 in H; rewrite H_3 in H; rewrite H_t1 in H; rewrite H_t2 in H; rewrite H_t1p in H; simpl in H.
        +++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N / 2 + 1) with (x / 2 + (Z.of_nat N / 2 + 1)) in H by ring.
          apply aux_inj in H; try lia.
        +++ destruct (proj1_sig t1 =? Z.of_nat N - 1) eqn:H_t1pp.
            ++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N / 2 - 1) with (x / 2 + (Z.of_nat N / 2 - 1)) in H by ring.
              apply aux_inj in H; try lia.
            ++++ destruct (proj1_sig t1 <? Z.of_nat N / 2 - 1) eqn:H_t2ppp.
              +++++ apply aux_inj in H; try lia.
                all: destruct t1; simpl in *; pose proof N_is_even; lia.
              +++++ destruct g. simpl in *. replace (x / 2 - Z.of_nat N / 2 + 2 + proj1_sig t1) with (x / 2 + (- (Z.of_nat N / 2) + 2 + proj1_sig t1)) in H by ring.
                apply aux_inj in H; try lia.
                2:{ destruct t1. simpl in *. pose proof N_is_even. lia. }
                destruct t1. simpl in *.
                assert (2*(Z.of_nat N / 2) = x0 + 2). lia.
                rewrite <- (N_is_even H_N) in H0. lia.
      ++ destruct (proj1_sig t1 =? Z.of_nat N - 2) eqn:H_t1p; destruct (proj1_sig t2 =? Z.of_nat N - 2) eqn:H_t2p.
        +++ unfold Fin_eq. lia.
        +++ destruct (proj1_sig t2 =? Z.of_nat N - 1) eqn:H_t2pp; unfold f_6 in H; rewrite H_3 in H; rewrite H_t1 in H; rewrite H_t2 in H; rewrite H_t1p in H; rewrite H_t2p in H; rewrite H_t2pp in H; simpl in H.
          ++++ destruct g. simpl in *.
              replace (x / 2 + Z.of_nat N / 2 - 1) with (x / 2 + (Z.of_nat N / 2 - 1)) in H by ring.
              replace (x / 2 + Z.of_nat N / 2 + 1) with (x / 2 + (Z.of_nat N / 2 + 1)) in H by ring.
              apply aux_inj in H; try lia.
          ++++ destruct (proj1_sig t2 <? Z.of_nat N / 2 - 1) eqn:H_t2ppp.
              +++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N / 2 + 1) with (x / 2 + (Z.of_nat N / 2 + 1)) in H by ring.
                apply aux_inj in H; try lia.
                all: destruct t2; simpl in *; pose proof N_is_even; lia.
              +++++ destruct g. simpl in *.
                replace (x / 2 - Z.of_nat N / 2 + 2 + proj1_sig t2) with (x / 2 + (- (Z.of_nat N / 2) + 2 + proj1_sig t2)) in H by ring.
                replace (x / 2 + Z.of_nat N / 2 + 1) with (x / 2 + (Z.of_nat N / 2 + 1)) in H by ring.
                apply aux_inj in H; try lia.
                2:{ destruct t2. simpl in *. pose proof N_is_even. lia. }
                destruct t2. simpl in *.
                assert (2*(Z.of_nat N / 2) = x0 + 1). lia.
                rewrite <- (N_is_even H_N) in H0. lia.
        +++ destruct (proj1_sig t1 =? Z.of_nat N - 1) eqn:H_t1pp; unfold f_6 in H; rewrite H_3 in H; rewrite H_t1 in H; rewrite H_t2 in H; rewrite H_t1p in H; rewrite H_t2p in H; rewrite H_t1pp in H; simpl in H.
          ++++ destruct g. simpl in *.
              replace (x / 2 + Z.of_nat N / 2 - 1) with (x / 2 + (Z.of_nat N / 2 - 1)) in H by ring.
              replace (x / 2 + Z.of_nat N / 2 + 1) with (x / 2 + (Z.of_nat N / 2 + 1)) in H by ring.
              apply aux_inj in H; try lia.
          ++++ destruct (proj1_sig t1 <? Z.of_nat N / 2 - 1) eqn:H_t2ppp.
              +++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N / 2 + 1) with (x / 2 + (Z.of_nat N / 2 + 1)) in H by ring.
                apply aux_inj in H; try lia.
                all: destruct t1; simpl in *; pose proof N_is_even; lia.
              +++++ destruct g. simpl in *.
                replace (x / 2 - Z.of_nat N / 2 + 2 + proj1_sig t1) with (x / 2 + (- (Z.of_nat N / 2) + 2 + proj1_sig t1)) in H by ring.
                replace (x / 2 + Z.of_nat N / 2 + 1) with (x / 2 + (Z.of_nat N / 2 + 1)) in H by ring.
                apply aux_inj in H; try lia.
                2:{ destruct t1. simpl in *. pose proof N_is_even. lia. }
                destruct t1. simpl in *.
                assert (2*(Z.of_nat N / 2) = x0 + 1). lia.
                rewrite <- (N_is_even H_N) in H0. lia.
        +++ destruct (proj1_sig t1 =? Z.of_nat N - 1) eqn:H_t1pp; destruct (proj1_sig t2 =? Z.of_nat N - 1) eqn:H_t2pp; unfold f_6 in H; rewrite H_3 in H; rewrite H_t1 in H; rewrite H_t2 in H; rewrite H_t1p in H; rewrite H_t2p in H; rewrite H_t1pp in H; rewrite H_t2pp in H; simpl in H.
          ++++ unfold Fin_eq. lia.
          ++++ destruct (proj1_sig t2 <? Z.of_nat N / 2 - 1) eqn:H_t2ppp.
              +++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N / 2 - 1) with (x / 2 + (Z.of_nat N / 2 - 1)) in H by ring.
                apply aux_inj in H; try lia.
                all: destruct t2; simpl in *; pose proof N_is_even; lia.
              +++++ destruct g. simpl in *.
                replace (x / 2 - Z.of_nat N / 2 + 2 + proj1_sig t2) with (x / 2 + (- (Z.of_nat N / 2) + 2 + proj1_sig t2)) in H by ring.
                replace (x / 2 + Z.of_nat N / 2 - 1) with (x / 2 + (Z.of_nat N / 2 - 1)) in H by ring.
                apply aux_inj in H; try lia.
                2:{ destruct t2. simpl in *. pose proof N_is_even. lia. }
                destruct t2. simpl in *.
                assert (2*(Z.of_nat N / 2) = x0 + 3). lia.
                rewrite <- (N_is_even H_N) in H0. lia.
          ++++ destruct (proj1_sig t1 <? Z.of_nat N / 2 - 1) eqn:H_t2ppp.
              +++++ destruct g. simpl in *. replace (x / 2 + Z.of_nat N / 2 - 1) with (x / 2 + (Z.of_nat N / 2 - 1)) in H by ring.
                apply aux_inj in H; try lia.
                all: destruct t1; simpl in *; pose proof N_is_even; lia.
              +++++ destruct g. simpl in *.
                replace (x / 2 - Z.of_nat N / 2 + 2 + proj1_sig t1) with (x / 2 + (- (Z.of_nat N / 2) + 2 + proj1_sig t1)) in H by ring.
                replace (x / 2 + Z.of_nat N / 2 - 1) with (x / 2 + (Z.of_nat N / 2 - 1)) in H by ring.
                apply aux_inj in H; try lia.
                2:{ destruct t1. simpl in *. pose proof N_is_even. lia. }
                destruct t1. simpl in *.
                assert (2*(Z.of_nat N / 2) = x0 + 3). lia.
                rewrite <- (N_is_even H_N) in H0. lia.
          ++++ destruct (proj1_sig t1 <? Z.of_nat N / 2 - 1) eqn:H_t1ppp; destruct (proj1_sig t2 <? Z.of_nat N / 2 - 1) eqn:H_t2ppp.
            +++++ unfold Fin_eq. destruct t1, t2. simpl in *. apply aux_inj in H; try lia.
            +++++ destruct g. simpl in *. replace (x / 2 - Z.of_nat N / 2 + 2 + proj1_sig t2) with (x / 2 + (- (Z.of_nat N / 2) + 2 + proj1_sig t2)) in H by ring.
              unfold Fin_eq. destruct t1, t2. simpl in *. apply aux_inj in H; try lia.
            +++++ destruct g. simpl in *. replace (x / 2 - Z.of_nat N / 2 + 2 + proj1_sig t1) with (x / 2 + (- (Z.of_nat N / 2) + 2 + proj1_sig t1)) in H by ring.
              unfold Fin_eq. destruct t1, t2. simpl in *. apply aux_inj in H; try lia.
            +++++ unfold Fin_eq. destruct t1, t2. simpl in *. apply aux_inj in H; try lia.
Qed.

Lemma four_div_2N: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (4 | Z.of_nat (2 * N)).
Proof.
  intro H_N.
  replace (Z.of_nat (2 * N)) with (2 * Z.of_nat N) by lia.
  rewrite (N_is_even H_N).
  replace (2 * (2 * (Z.of_nat N / 2))) with (4 * (Z.of_nat N / 2)) by lia.
  apply Z.divide_factor_l.
Qed.

Lemma mod2_forget_signs: forall (a b:Z), (a+b) mod 2 = (a-b) mod 2.
Proof.
  intros. apply rewrite_div_to_mod; try lia. exists b. ring.
Qed.

Lemma aux_aux_atlst2_mod0: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> proj1_sig (project_to_Fin2 ((2*(proj1_sig a + proj1_sig t)))) mod 4 = 0.
Proof.
    intros a t H_N H.
    cbn [proj1_sig project_to_Fin2].
    apply mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - apply div_to_mod; try lia. exists x. lia.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod0: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a + proj1_sig t))) t) a.
Proof.
  intros a t H_N H.
  pose proof (aux_aux_atlst2_mod0 a t H_N H).

  unfold f_6, Fin_eq. rewrite H0. cbn [Z.eqb proj1_sig project_to_Fin project_to_Fin2].
  rewrite mod_div2. rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.

Lemma aux_aux_atlst2_mod1_smallt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> proj1_sig t <? (Z.of_nat N)/2 - 1 = true -> proj1_sig (project_to_Fin2 ((2*(proj1_sig a - proj1_sig t))+1)) mod 4 = 1.
Proof.
    intros a t H_N H H0.
    cbn [proj1_sig project_to_Fin2].
    rewrite mod2_forget_signs in H. apply mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - replace (2 * (proj1_sig a - proj1_sig t) + 1) with (1+x*4) by lia.
      try rewrite Z_mod_plus; try lia. trivial.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod1_smallt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> proj1_sig t <? (Z.of_nat N)/2 - 1 = true -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a - proj1_sig t)+1)) t) a.
Proof.
  intros a t H_N H H0.
  pose proof (aux_aux_atlst2_mod1_smallt a t H_N H H0).

  unfold f_6, Fin_eq. rewrite H0. rewrite H1. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].
  rewrite mod_div2p1. rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.
Lemma aux_aux_atlst2_mod1_bigt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t <? (Z.of_nat N)/2 - 1 = false -> proj1_sig (project_to_Fin2 (2 * (proj1_sig a + proj1_sig t) + 5 - Z.of_nat N)) mod 4 = 1.
Proof.
    intros a t H_N H H0.
    cbn [proj1_sig project_to_Fin2].
    replace 1 with (1 mod 2) in H by trivial. apply rewrite_mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - replace (2 * (proj1_sig a + proj1_sig t) + 5 - Z.of_nat N) with (- (Z.of_nat N + 1) + (x+2)*4) by lia.
      try rewrite Z_mod_plus; try lia.
      destruct H_N. replace 2 with (2 mod 4) in H2 by trivial. apply rewrite_mod_to_div in H2; try lia. destruct H2.
      replace 1 with (1 mod 4) at 2 by trivial. apply rewrite_div_to_mod; try lia. exists (-x0-1). lia.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod1_bigt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t <? (Z.of_nat N)/2 - 1 = false -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a + proj1_sig t) + 5 - (Z.of_nat N))) t) a.
Proof.
  intros a t H_N H H0.
  pose proof (aux_aux_atlst2_mod1_bigt a t H_N H H0).

  unfold f_6, Fin_eq. rewrite H0. rewrite H1. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].
  setoid_rewrite (N_is_even H_N) at 3.
  replace (2 * (proj1_sig a + proj1_sig t) + 5 - 2 * (Z.of_nat N / 2)) with (2 * (proj1_sig a + proj1_sig t + 2 - (Z.of_nat N / 2))+1) by ring.
  rewrite mod_div2p1.
  replace ((proj1_sig a + proj1_sig t + 2 - Z.of_nat N / 2) mod Z.of_nat N + Z.of_nat N / 2 - 2 - proj1_sig t) with ((proj1_sig a + proj1_sig t + 2 - Z.of_nat N / 2) mod Z.of_nat N + (Z.of_nat N / 2 - 2 - proj1_sig t)) by ring.
  rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.

Lemma aux_aux_atlst2_mod2_bigggt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> proj1_sig t =? Z.of_nat N - 3 = true -> proj1_sig (project_to_Fin2 (2*(proj1_sig a) + 4 - 2*Z.of_nat N)) mod 4 = 2.
Proof.
    intros a t H_N H H0.
    cbn [proj1_sig project_to_Fin2].
    apply mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - replace 2 with (2 mod 4) at 3 by trivial. apply rewrite_div_to_mod; try lia. exists (x - Z.of_nat N + 2). lia.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod2_bigggt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> proj1_sig t =? Z.of_nat N - 3 = true -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a) + 4 - 2*Z.of_nat N)) t) a.
Proof.
  intros a t H_N H H0.
  pose proof (aux_aux_atlst2_mod2_bigggt a t H_N H H0).

  unfold f_6, Fin_eq. rewrite H0. rewrite H1. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].
  replace (2 * proj1_sig a + 4 - 2 * (Z.of_nat N)) with (2 * (proj1_sig a + 2 - (Z.of_nat N))) by ring.
  rewrite mod_div2.
  replace ((proj1_sig a + 2 - Z.of_nat N) mod Z.of_nat N + Z.of_nat N - 2) with ((proj1_sig a + 2 - Z.of_nat N) mod Z.of_nat N + (Z.of_nat N - 2)) by ring.
  rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.
Lemma aux_aux_atlst2_mod2_biggt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = true -> proj1_sig (project_to_Fin2 (2*(proj1_sig a) + 2 - 2*Z.of_nat N)) mod 4 = 2.
Proof.
    intros a t H_N H H0 H1.
    cbn [proj1_sig project_to_Fin2].
    apply mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - replace 2 with (2 mod 4) at 4 by trivial. apply rewrite_div_to_mod; try lia. exists (x - Z.of_nat N + 1). lia.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod2_biggt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = true -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a) + 2 - 2*Z.of_nat N)) t) a.
Proof.
  intros a t H_N H H0 H1.
  pose proof (aux_aux_atlst2_mod2_biggt a t H_N H H0 H1).

  unfold f_6, Fin_eq. rewrite H0. rewrite H1. rewrite H2. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].
  replace (2 * proj1_sig a + 2 - 2 * (Z.of_nat N)) with (2 * (proj1_sig a + 1 - (Z.of_nat N))) by ring.
  rewrite mod_div2.
  replace ((proj1_sig a + 1 - Z.of_nat N) mod Z.of_nat N + Z.of_nat N - 1) with ((proj1_sig a + 1 - Z.of_nat N) mod Z.of_nat N + (Z.of_nat N - 1)) by ring.
  rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.
Lemma aux_aux_atlst2_mod2_bigt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = false -> proj1_sig t =? Z.of_nat N - 1 = true -> proj1_sig (project_to_Fin2 (2*(proj1_sig a) + 6 - 2*Z.of_nat N)) mod 4 = 2.
Proof.
    intros a t H_N H H0 H1 H2.
    cbn [proj1_sig project_to_Fin2].
    replace 1 with (1 mod 2) in H by trivial. apply rewrite_mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - replace 2 with (2 mod 4) at 3 by trivial. apply rewrite_div_to_mod; try lia. exists (x - Z.of_nat N + 2). lia.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod2_bigt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = false -> proj1_sig t =? Z.of_nat N - 1 = true -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a) + 6 - 2*Z.of_nat N)) t) a.
Proof.
  intros a t H_N H H0 H1 H2.
  pose proof (aux_aux_atlst2_mod2_bigt a t H_N H H0 H1 H2).

  unfold f_6, Fin_eq. rewrite H0. rewrite H1. rewrite H2. rewrite H3. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].
  replace (2 * proj1_sig a + 6 - 2 * (Z.of_nat N)) with (2 * (proj1_sig a + 3 - (Z.of_nat N))) by ring.
  rewrite mod_div2.
  replace ((proj1_sig a + 3 - Z.of_nat N) mod Z.of_nat N + Z.of_nat N - 3) with ((proj1_sig a + 3 - Z.of_nat N) mod Z.of_nat N + (Z.of_nat N - 3)) by ring.
  rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.
Lemma aux_aux_atlst2_mod2_smallt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = false -> proj1_sig t =? Z.of_nat N - 1 = false -> proj1_sig (project_to_Fin2 (2*(proj1_sig a - proj1_sig t))) mod 4 = 2.
Proof.
    intros a t H_N H H0 H1 H2.
    cbn [proj1_sig project_to_Fin2].
    rewrite mod2_forget_signs in H. replace 1 with (1 mod 2) in H by trivial. apply rewrite_mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - replace 2 with (2 mod 4) at 2 by trivial. apply rewrite_div_to_mod; try lia. exists (x). lia.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod2_smallt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = false -> proj1_sig t =? Z.of_nat N - 1 = false -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a - proj1_sig t))) t) a.
Proof.
  intros a t H_N H H0 H1 H2.
  pose proof (aux_aux_atlst2_mod2_smallt a t H_N H H0 H1 H2).

  unfold f_6, Fin_eq. rewrite H0. rewrite H1. rewrite H2. rewrite H3. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].
  rewrite mod_div2. rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.

Lemma Np2_dividible_by_4: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> 4*((Z.of_nat N -2)/4) = Z.of_nat N - 2.
Proof.
  intro H. destruct H.
  assert ((Z.of_nat N - 2) mod 4 = 0). rewrite <- Zminus_mod_idemp_l. rewrite H0. trivial.
  rewrite Z.mod_eq in H1; try lia.
Qed.

Lemma aux_aux_atlst2_mod3_bigtttt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t =? Z.of_nat N - 3 = true -> proj1_sig (project_to_Fin2 (2*(proj1_sig a) - Z.of_nat N + 1)) mod 4 = 3.
Proof.
    intros a t H_N H H0.
    cbn [proj1_sig project_to_Fin2].
    replace 1 with (1 mod 2) in H by trivial. apply rewrite_mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - replace 3 with (3 mod 4) by trivial. apply rewrite_div_to_mod; try lia. exists (x - Z.of_nat N / 2 + 1 - (Z.of_nat N - 2)/4).
      pose proof Np2_dividible_by_4. pose proof (N_is_even H_N). lia.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod3_bigtttt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t =? Z.of_nat N - 3 = true -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a) - Z.of_nat N + 1)) t) a.
Proof.
  intros a t H_N H H0.
  pose proof (aux_aux_atlst2_mod3_bigtttt a t H_N H H0).

  unfold f_6, Fin_eq. rewrite H0. rewrite H1. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].
  setoid_rewrite (N_is_even H_N) at 2. replace (2 * proj1_sig a - 2 * (Z.of_nat N / 2) + 1) with (2 * (proj1_sig a - (Z.of_nat N / 2)) + 1) by ring.
  rewrite mod_div2p1. rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.
Lemma aux_aux_atlst2_mod3_bigttt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = true -> proj1_sig (project_to_Fin2 (2*(proj1_sig a) - Z.of_nat N - 1)) mod 4 = 3.
Proof.
    intros a t H_N H H0 H1.
    cbn [proj1_sig project_to_Fin2].
    replace 1 with (1 mod 2) in H by trivial. apply rewrite_mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - replace 3 with (3 mod 4) by trivial. apply rewrite_div_to_mod; try lia. exists (x - Z.of_nat N / 2 - (Z.of_nat N - 2)/4).
      pose proof Np2_dividible_by_4. pose proof (N_is_even H_N). lia.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod3_bigttt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = true -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a) - Z.of_nat N - 1)) t) a.
Proof.
  intros a t H_N H H0 H1.
  pose proof (aux_aux_atlst2_mod3_bigttt a t H_N H H0 H1).

  unfold f_6, Fin_eq. rewrite H0. rewrite H1. rewrite H2. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].
  setoid_rewrite (N_is_even H_N) at 2. replace (2 * proj1_sig a - 2 * (Z.of_nat N / 2) - 1) with (2 * (proj1_sig a - (Z.of_nat N / 2) - 1) + 1) by ring.
  rewrite mod_div2p1.
  replace ((proj1_sig a - Z.of_nat N / 2 - 1) mod Z.of_nat N + Z.of_nat N / 2 + 1) with ((proj1_sig a - Z.of_nat N / 2 - 1) mod Z.of_nat N + (Z.of_nat N / 2 + 1)) by ring.
  rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.
Lemma aux_aux_atlst2_mod3_bigtt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = false -> proj1_sig t =? Z.of_nat N - 1 = true -> proj1_sig (project_to_Fin2 (2*(proj1_sig a) - Z.of_nat N + 3)) mod 4 = 3.
Proof.
    intros a t H_N H H0 H1 H2.
    cbn [proj1_sig project_to_Fin2].
    apply mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - replace 3 with (3 mod 4) at 2 by trivial. apply rewrite_div_to_mod; try lia. exists (x - Z.of_nat N / 2 - (Z.of_nat N - 2)/4).
      pose proof Np2_dividible_by_4. pose proof (N_is_even H_N). lia.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod3_bigtt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = false -> proj1_sig t =? Z.of_nat N - 1 = true -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a) - Z.of_nat N + 3)) t) a.
Proof.
  intros a t H_N H H0 H1 H2.
  pose proof (aux_aux_atlst2_mod3_bigtt a t H_N H H0 H1 H2).

  unfold f_6, Fin_eq. rewrite H0. rewrite H1. rewrite H2. rewrite H3. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].
  setoid_rewrite (N_is_even H_N) at 2. replace (2 * proj1_sig a - 2 * (Z.of_nat N / 2) + 3) with (2 * (proj1_sig a - (Z.of_nat N / 2) + 1) + 1) by ring.
  rewrite mod_div2p1.
  replace ((proj1_sig a - Z.of_nat N / 2 + 1) mod Z.of_nat N + Z.of_nat N / 2 - 1) with ((proj1_sig a - Z.of_nat N / 2 + 1) mod Z.of_nat N + (Z.of_nat N / 2 - 1)) by ring.
  rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.
Lemma aux_aux_atlst2_mod3_smallt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = false -> proj1_sig t =? Z.of_nat N - 1 = false -> proj1_sig t <? (Z.of_nat N)/2 - 1 = true -> proj1_sig (project_to_Fin2 (2*(proj1_sig a + proj1_sig t)+1)) mod 4 = 3.
Proof.
    intros a t H_N H H0 H1 H2 H3.
    cbn [proj1_sig project_to_Fin2].
    replace 1 with (1 mod 2) in H by trivial. apply rewrite_mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - replace 3 with (3 mod 4) by trivial. apply rewrite_div_to_mod; try lia. exists (x).
      lia.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod3_smallt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 1 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = false -> proj1_sig t =? Z.of_nat N - 1 = false -> proj1_sig t <? (Z.of_nat N)/2 - 1 = true -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a + proj1_sig t)+1)) t) a.
Proof.
  intros a t H_N H H0 H1 H2 H3.
  pose proof (aux_aux_atlst2_mod3_smallt a t H_N H H0 H1 H2 H3).

  unfold f_6, Fin_eq. rewrite H0. rewrite H1. rewrite H2. rewrite H3. rewrite H4. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].
  rewrite mod_div2p1. rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.
Lemma aux_aux_atlst2_mod3_bigt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = false -> proj1_sig t =? Z.of_nat N - 1 = false -> proj1_sig t <? (Z.of_nat N)/2 - 1 = false -> proj1_sig (project_to_Fin2 (2*(proj1_sig a - proj1_sig t) - 3 + Z.of_nat N)) mod 4 = 3.
Proof.
    intros a t H_N H H0 H1 H2 H3.
    cbn [proj1_sig project_to_Fin2].
    rewrite mod2_forget_signs in H. apply mod_to_div in H; try lia. destruct H.
    rewrite <- Zmod_div_mod; try lia.
    - replace 3 with (3 mod 4) at 2 by trivial. apply rewrite_div_to_mod; try lia. exists (x-1+(Z.of_nat N -2)/4).
      pose proof Np2_dividible_by_4. pose proof (N_is_even H_N). lia.
    - exact (four_div_2N H_N).
Qed.
Lemma aux_atlst2_mod3_bigt: forall (a t:SetN), (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (proj1_sig a + proj1_sig t) mod 2 = 0 -> proj1_sig t =? Z.of_nat N - 3 = false -> proj1_sig t =? Z.of_nat N - 2 = false -> proj1_sig t =? Z.of_nat N - 1 = false -> proj1_sig t <? (Z.of_nat N)/2 - 1 = false -> Fin_eq _ (f_6 (project_to_Fin2 (2*(proj1_sig a - proj1_sig t) - 3 + Z.of_nat N)) t) a.
Proof.
  intros a t H_N H H0 H1 H2 H3.
  pose proof (aux_aux_atlst2_mod3_bigt a t H_N H H0 H1 H2 H3).

  unfold f_6, Fin_eq. rewrite H0. rewrite H1. rewrite H2. rewrite H3. rewrite H4. cbn [Z.eqb Pos.eqb andb proj1_sig project_to_Fin project_to_Fin2].
  setoid_rewrite (N_is_even H_N) at 3. replace (2 * (proj1_sig a - proj1_sig t) - 3 + 2 * (Z.of_nat N / 2)) with (2 * (proj1_sig a - proj1_sig t - 2 + Z.of_nat N / 2) + 1) by ring.
  rewrite mod_div2p1.
  replace ((proj1_sig a - proj1_sig t - 2 + Z.of_nat N / 2) mod Z.of_nat N - Z.of_nat N / 2 + 2 + proj1_sig t) with ((proj1_sig a - proj1_sig t - 2 + Z.of_nat N / 2) mod Z.of_nat N + (- (Z.of_nat N / 2) + 2 + proj1_sig t)) by ring.
  rewrite Zplus_mod_idemp_l.
  destruct a, t. simpl in *.
  rewrite Z.mod_small; lia.
Qed.

Lemma t_is_big: forall t:SetN, (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> proj1_sig t >= Z.of_nat N - 3 -> proj1_sig t >= (Z.of_nat N)/2 - 1.
Proof.
  intros t H_N H1.
  destruct H_N.
  assert (Z.of_nat N / 2 + 2 <= Z.of_nat N).
  {
    setoid_rewrite N_is_even at 2. 2:split; assumption.
    replace (2 * (Z.of_nat N / 2)) with (Z.of_nat N / 2 + Z.of_nat N / 2) by ring.
    apply Zplus_le_compat_l.
    replace 2 with (4/2) at 1 by trivial.
    apply Z_div_le; lia.
  }
  lia.
Qed.
Lemma apply_mod_4: forall a b:Z, a mod 4 <> b mod 4 -> a <> b.
Proof. intros. intro. apply H. f_equal. exact H0. Qed.

Lemma f_6_at_least_2_by_workshop: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> at_least_2_by_workshop f_6.
  intro H_N. unfold at_least_2_by_workshop. intros.
  destruct (Z_mod_2_is_0_or_1 (proj1_sig a + proj1_sig t)); destruct (proj1_sig t =? Z.of_nat N - 3) eqn:Ht3.
  - exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t))). exists ((project_to_Fin2 (2*(proj1_sig a) + 4 - 2*Z.of_nat N))). split; try split.
    + exact (aux_atlst2_mod0 a t H_N H).
    + exact (aux_atlst2_mod2_bigggt a t H_N H Ht3).
    + apply apply_mod_4. rewrite (aux_aux_atlst2_mod0 a t H_N H). rewrite (aux_aux_atlst2_mod2_bigggt a t H_N H Ht3). discriminate.
  - destruct (proj1_sig t =? Z.of_nat N - 2) eqn:Ht2.
    --exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t))). exists ((project_to_Fin2 (2*(proj1_sig a) + 2 - 2*Z.of_nat N))). split; try split.
      + exact (aux_atlst2_mod0 a t H_N H).
      + exact (aux_atlst2_mod2_biggt a t H_N H Ht3 Ht2).
      + apply apply_mod_4. rewrite (aux_aux_atlst2_mod0 a t H_N H). rewrite (aux_aux_atlst2_mod2_biggt a t H_N H Ht3 Ht2). discriminate.
    --destruct (proj1_sig t =? Z.of_nat N - 1) eqn:Ht1.
    --- exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t))). exists ((project_to_Fin2 (2*(proj1_sig a) - Z.of_nat N + 3))). split; try split.
      + exact (aux_atlst2_mod0 a t H_N H).
      + exact (aux_atlst2_mod3_bigtt a t H_N H Ht3 Ht2 Ht1).
      + apply apply_mod_4. rewrite (aux_aux_atlst2_mod0 a t H_N H). rewrite (aux_aux_atlst2_mod3_bigtt a t H_N H Ht3 Ht2 Ht1). discriminate.
    --- destruct (proj1_sig t <? (Z.of_nat N)/2 - 1) eqn:Ht.
    ----exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t))). exists ((project_to_Fin2 (2*(proj1_sig a - proj1_sig t)+1))). split; try split.
      + exact (aux_atlst2_mod0 a t H_N H).
      + exact (aux_atlst2_mod1_smallt a t H_N H Ht).
      + apply apply_mod_4. rewrite (aux_aux_atlst2_mod0 a t H_N H). rewrite (aux_aux_atlst2_mod1_smallt a t H_N H Ht). discriminate.
    ----exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t))). exists ((project_to_Fin2 (2*(proj1_sig a - proj1_sig t) - 3 + Z.of_nat N))). split; try split.
      + exact (aux_atlst2_mod0 a t H_N H).
      + exact (aux_atlst2_mod3_bigt a t H_N H Ht3 Ht2 Ht1 Ht).
      + apply apply_mod_4. rewrite (aux_aux_atlst2_mod0 a t H_N H). rewrite (aux_aux_atlst2_mod3_bigt a t H_N H Ht3 Ht2 Ht1 Ht). discriminate.
  - exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t) + 5 - (Z.of_nat N))). exists ((project_to_Fin2 (2*(proj1_sig a) - Z.of_nat N + 1))). split; try split.
    all: pose proof (t_is_big t H_N).
    all: assert (proj1_sig t <? (Z.of_nat N)/2 - 1 = false); try lia.
    + exact (aux_atlst2_mod1_bigt a t H_N H H1).
    + exact (aux_atlst2_mod3_bigtttt a t H_N H Ht3).
    + apply apply_mod_4. rewrite (aux_aux_atlst2_mod1_bigt a t H_N H H1). rewrite (aux_aux_atlst2_mod3_bigtttt a t H_N H Ht3). discriminate.
  - destruct (proj1_sig t =? Z.of_nat N - 2) eqn:Ht2.
    --exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t) + 5 - (Z.of_nat N))). exists ((project_to_Fin2 (2*(proj1_sig a) - Z.of_nat N - 1))). split; try split.
      all: pose proof (t_is_big t H_N).
      all: assert (proj1_sig t <? (Z.of_nat N)/2 - 1 = false); try lia.
      + exact (aux_atlst2_mod1_bigt a t H_N H H1).
      + exact (aux_atlst2_mod3_bigttt a t H_N H Ht3 Ht2).
      + apply apply_mod_4. rewrite (aux_aux_atlst2_mod1_bigt a t H_N H H1). rewrite (aux_aux_atlst2_mod3_bigttt a t H_N H Ht3 Ht2). discriminate.
    --destruct (proj1_sig t =? Z.of_nat N - 1) eqn:Ht1.
    --- exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t) + 5 - (Z.of_nat N))). exists ((project_to_Fin2 (2*(proj1_sig a) + 6 - 2*Z.of_nat N))). split; try split.
      all: pose proof (t_is_big t H_N).
      all: assert (proj1_sig t <? (Z.of_nat N)/2 - 1 = false); try lia.
      + exact (aux_atlst2_mod1_bigt a t H_N H H1).
      + exact (aux_atlst2_mod2_bigt a t H_N H Ht3 Ht2 Ht1).
      + apply apply_mod_4. rewrite (aux_aux_atlst2_mod1_bigt a t H_N H H1). rewrite (aux_aux_atlst2_mod2_bigt a t H_N H Ht3 Ht2 Ht1). discriminate.
    --- destruct (proj1_sig t <? (Z.of_nat N)/2 - 1) eqn:Ht.
    ----exists (project_to_Fin2 (2*(proj1_sig a - proj1_sig t))). exists ((project_to_Fin2 (2*(proj1_sig a + proj1_sig t)+1))). split; try split.
      + exact (aux_atlst2_mod2_smallt a t H_N H Ht3 Ht2 Ht1).
      + exact (aux_atlst2_mod3_smallt a t H_N H Ht3 Ht2 Ht1 Ht).
      + apply apply_mod_4. rewrite (aux_aux_atlst2_mod2_smallt a t H_N H Ht3 Ht2 Ht1). rewrite (aux_aux_atlst2_mod3_smallt a t H_N H Ht3 Ht2 Ht1 Ht). discriminate.
    ----exists (project_to_Fin2 (2*(proj1_sig a + proj1_sig t) + 5 - (Z.of_nat N))). exists ((project_to_Fin2 (2*(proj1_sig a - proj1_sig t)))). split; try split.
      all: pose proof (t_is_big t H_N).
      all: assert (proj1_sig t <? (Z.of_nat N)/2 - 1 = false); try lia.
      + exact (aux_atlst2_mod1_bigt a t H_N H H1).
      + exact (aux_atlst2_mod2_smallt a t H_N H Ht3 Ht2 Ht1).
      + apply apply_mod_4. rewrite (aux_aux_atlst2_mod1_bigt a t H_N H H1). rewrite (aux_aux_atlst2_mod2_smallt a t H_N H Ht3 Ht2 Ht1). discriminate.
Qed.



Lemma time_symetries: forall (f: ScheduleType),
  (forall (g1 g2 : Set2N) (t1 t2 : SetN),
  proj1_sig t1 < proj1_sig t2 -> Fin_eq N (f g1 t1) (f g2 t1) -> Fin_eq N (f g1 t2) (f g2 t2) ->
  Fin_eq (2 * N) g1 g2)
  -> no_rec_enc f.
Proof.
  unfold no_rec_enc. intros.
  destruct (Ztrichotomy (proj1_sig t1) (proj1_sig t2)) as [Hd | [Hd | Hd]].
  - right. exact (H g1 g2 t1 t2 Hd H0 H1).
  - left. exact Hd.
  - right. apply (H g1 g2 t2 t1); try assumption. lia.
Qed.
Lemma g_symetries: forall (f: ScheduleType),
  (forall (g1 g2 : Set2N) (t1 t2 : SetN),
  proj1_sig g1 mod 4 <= proj1_sig g2 mod 4 -> proj1_sig t1 < proj1_sig t2 -> Fin_eq N (f g1 t1) (f g2 t1) -> Fin_eq N (f g1 t2) (f g2 t2) ->
  Fin_eq (2 * N) g1 g2)
  -> no_rec_enc f.
Proof.
  intros. apply time_symetries. intros.
  destruct (Ztrichotomy ((proj1_sig g1) mod 4) ((proj1_sig g2) mod 4)) as [Hd | [Hd | Hd]].
  - apply (H g1 g2 t1 t2); try assumption. lia.
  - apply (H g1 g2 t1 t2); try assumption. lia.
  - symmetry. apply (H g2 g1 t1 t2); try assumption. lia. all:symmetry; assumption.
Qed.

Lemma mod4_div2: forall a b:Z, a mod 4 = b -> a/2 mod 2 = b/2.
Proof.
  intros.
  assert ((a mod 4)/2 = b/2). f_equal. exact H.
  replace 4 with (2*2) in H0 by ring.
  rewrite div_mod_by_2 in H0; lia.
Qed.
Lemma Ndiv2: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> (Z.of_nat N / 2) mod 2 = 1.
Proof.
  intro H_N. destruct H_N.
  apply mod4_div2 in H0.
  replace 1 with (2/2) by trivial.
  exact H0.
Qed.

Lemma aux_NoRecEnc_01: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> forall (g1 g2:Set2N) (t:SetN), Fin_eq N (f_6 g1 t) (f_6 g2 t) -> (proj1_sig g1) mod 4 = 0 -> (proj1_sig g2) mod 4 = 1 -> (proj1_sig t <? (Z.of_nat N)/2 - 1 = true).
Proof.
  intro H_N.
  intros. destruct (proj1_sig t <? (Z.of_nat N)/2 - 1) eqn:H_t.
  - reflexivity.
  - unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t in H. simpl in H.
    apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
    apply apply_mod_2 in H; try lia.
    apply mod4_div2 in H0, H1. replace (0/2) with 0 in H0 by trivial. replace (1/2) with 0 in H1 by trivial.
    apply mod_to_div in H0, H1; try lia. destruct H0, H1. rewrite H0. rewrite H1.
    replace (x0 * 2 - x1 * 2 - Z.of_nat N / 2 + 2) with (- (Z.of_nat N / 2) + (x0 - x1 +1)*2) by ring.
    rewrite Z_mod_plus; try lia. rewrite <- plus_minus_mod2. rewrite (Ndiv2 H_N).
    setoid_rewrite (N_is_even H_N). replace (x * (2 * (Z.of_nat N / 2))) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
    discriminate.
Qed.

Lemma aux_NoRecEnc_02: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> forall (g1 g2:Set2N) (t:SetN), Fin_eq N (f_6 g1 t) (f_6 g2 t) -> (proj1_sig g1) mod 4 = 0 -> (proj1_sig g2) mod 4 = 2 -> (proj1_sig t =? Z.of_nat N - 3 = true) \/ (proj1_sig t =? Z.of_nat N - 3 = false /\ proj1_sig t =? Z.of_nat N - 2 = true).
Proof.
  intro H_N.
  intros. destruct (proj1_sig t =? Z.of_nat N - 3) eqn:H_t3.
  - left. reflexivity.
  - destruct (proj1_sig t =? Z.of_nat N - 2) eqn:H_t2.
    + right. split; reflexivity.
    + destruct (proj1_sig t =? Z.of_nat N - 1) eqn:H_t1.
      * unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H. rewrite H_t1 in H. simpl in H.
        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        apply apply_mod_2 in H; try lia.
        apply mod4_div2 in H0, H1. replace (0/2) with 0 in H0 by trivial. replace (2/2) with (1 mod 2) in H1 by trivial.
        apply mod_to_div in H0; try lia. apply rewrite_mod_to_div in H1; try lia. destruct H0, H1. destruct g1, g2, t. simpl in *.
        replace (x2 / 2 - x4 - x3 / 2 - Z.of_nat N + 3) with (1+(x0 - Z.of_nat N - x1 + 1)*2) by lia.
        rewrite Z_mod_plus; try lia.
        setoid_rewrite (N_is_even H_N). replace (2 * (Z.of_nat N / 2) * x) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
        discriminate.
      * unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H. rewrite H_t1 in H. simpl in H.
        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        apply apply_mod_2 in H; try lia.
        apply mod4_div2 in H0, H1. replace (0/2) with 0 in H0 by trivial. replace (2/2) with (1 mod 2) in H1 by trivial.
        apply mod_to_div in H0; try lia. destruct H0. rewrite H0.
        setoid_rewrite Z.add_mod at 1; try lia. setoid_rewrite Z.add_mod at 2; try lia.
        rewrite Z_mod_mult. setoid_rewrite <- plus_minus_mod2. rewrite H1.
        replace (2 * proj1_sig t) with (proj1_sig t * 2) by ring. rewrite Z_mod_mult.
        setoid_rewrite (N_is_even H_N). replace (x * (2 * (Z.of_nat N / 2))) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
        discriminate.
Qed.

Lemma aux_NoRecEnc_03: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> forall (g1 g2:Set2N) (t:SetN), Fin_eq N (f_6 g1 t) (f_6 g2 t) -> (proj1_sig g1) mod 4 = 0 -> (proj1_sig g2) mod 4 = 3 -> (proj1_sig t <? (Z.of_nat N)/2 - 1 = false /\ proj1_sig t =? Z.of_nat N - 3 = false /\ proj1_sig t =? Z.of_nat N - 2 = false /\ proj1_sig t =? Z.of_nat N - 1 = false) \/ (proj1_sig t =? Z.of_nat N - 3 = false /\ proj1_sig t =? Z.of_nat N - 2 = false /\ proj1_sig t =? Z.of_nat N - 1 = true).
Proof.
  intro H_N.
  intros. destruct (proj1_sig t =? Z.of_nat N - 3) eqn:H_t3.
  - unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. simpl in H.
    apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
    apply apply_mod_2 in H; try lia.
    apply mod4_div2 in H0, H1. replace (0/2) with 0 in H0 by trivial. replace (3/2) with (1 mod 2) in H1 by trivial.
    apply mod_to_div in H0; try lia. apply rewrite_mod_to_div in H1; try lia. destruct H0, H1. rewrite H0. destruct t, g2. simpl in *.
    pose proof (N_is_even H_N).
    replace (x0 * 2 - x2 - x3 / 2 - Z.of_nat N / 2) with (- (Z.of_nat N / 2) + (1 + x0 - x1 - (Z.of_nat N / 2))*2) by lia.
    rewrite Z_mod_plus; try lia. rewrite <- plus_minus_mod2. rewrite (Ndiv2 H_N).
    setoid_rewrite (N_is_even H_N). replace (x * (2 * (Z.of_nat N / 2))) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
    discriminate.
  - destruct (proj1_sig t =? Z.of_nat N - 2) eqn:H_t2.
    + unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H. simpl in H.
      apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
      apply apply_mod_2 in H; try lia.
      apply mod4_div2 in H0, H1. replace (0/2) with 0 in H0 by trivial. replace (3/2) with (1 mod 2) in H1 by trivial.
      apply mod_to_div in H0; try lia. apply rewrite_mod_to_div in H1; try lia. destruct H0, H1. rewrite H0. destruct t, g2. simpl in *.
      pose proof (N_is_even H_N).
      replace (x0 * 2 - x2 - x3 / 2 - Z.of_nat N / 2 - 1) with (- (Z.of_nat N / 2) + (x0 - x1 - (Z.of_nat N / 2))*2) by lia.
      rewrite Z_mod_plus; try lia. rewrite <- plus_minus_mod2. rewrite (Ndiv2 H_N).
      setoid_rewrite (N_is_even H_N). replace (x * (2 * (Z.of_nat N / 2))) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
      discriminate.
    + destruct (proj1_sig t =? Z.of_nat N - 1) eqn:H_t1.
      ++right. repeat split; reflexivity.
      ++destruct (proj1_sig t <? Z.of_nat N / 2 - 1) eqn:H_t.
        * unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H. rewrite H_t1 in H. rewrite H_t in H. simpl in H.
          apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
          apply apply_mod_2 in H; try lia.
          apply mod4_div2 in H0, H1. replace (0/2) with 0 in H0 by trivial. replace (3/2) with 1 in H1 by trivial.
          rewrite Z.add_mod; try lia. rewrite <- plus_minus_mod2. rewrite H0. rewrite H1.
          setoid_rewrite (N_is_even H_N). replace (x * (2 * (Z.of_nat N / 2))) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
          discriminate.
        * left. repeat split; reflexivity.
Qed.

Lemma aux_NoRecEnc_12: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> forall (g1 g2:Set2N) (t:SetN), Fin_eq N (f_6 g1 t) (f_6 g2 t) -> (proj1_sig g1) mod 4 = 1 -> (proj1_sig g2) mod 4 = 2 -> (proj1_sig t <? (Z.of_nat N)/2 - 1 = false /\ proj1_sig t =? Z.of_nat N - 3 = false /\ proj1_sig t =? Z.of_nat N - 2 = false /\ proj1_sig t =? Z.of_nat N - 1 = false) \/ (proj1_sig t =? Z.of_nat N - 3 = false /\ proj1_sig t =? Z.of_nat N - 2 = false /\ proj1_sig t =? Z.of_nat N - 1 = true).
Proof.
  intro H_N.
  intros. destruct (proj1_sig t =? Z.of_nat N - 3) eqn:H_t3.
  - unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H.
    pose proof (t_is_big t H_N). assert (proj1_sig t <? (Z.of_nat N)/2 - 1 = false); try lia.
    rewrite H3 in H.  simpl in H.

    apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
    apply apply_mod_2 in H; try lia.
    apply mod4_div2 in H0, H1. replace (1/2) with 0 in H0 by trivial. replace (2/2) with (1 mod 2) in H1 by trivial.
    apply mod_to_div in H0; try lia. apply rewrite_mod_to_div in H1; try lia. destruct H0, H1. rewrite H0. destruct t, g2. simpl in *.
    replace (x0 * 2 + Z.of_nat N / 2 - x2 - x3 / 2 - Z.of_nat N) with (Z.of_nat N / 2 + (- Z.of_nat N + x0 - x1 + 1)*2) by lia.
    rewrite Z_mod_plus; try lia. rewrite (Ndiv2 H_N).
    setoid_rewrite (N_is_even H_N). replace (2 * (Z.of_nat N / 2) * x) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
    discriminate.
  - destruct (proj1_sig t =? Z.of_nat N - 2) eqn:H_t2.
    + unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H. simpl in H.
      pose proof (t_is_big t H_N). assert (proj1_sig t <? (Z.of_nat N)/2 - 1 = false); try lia.
      rewrite H3 in H.  simpl in H.

      apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
      apply apply_mod_2 in H; try lia.
      apply mod4_div2 in H0, H1. replace (1/2) with 0 in H0 by trivial. replace (2/2) with (1 mod 2) in H1 by trivial.
      apply mod_to_div in H0; try lia. apply rewrite_mod_to_div in H1; try lia. destruct H0, H1. rewrite H0. destruct t, g2. simpl in *.
      replace (x0 * 2 + Z.of_nat N / 2 - x2 - x3 / 2 - Z.of_nat N - 1) with (Z.of_nat N / 2 + (x0 - x1 - Z.of_nat N)*2) by lia.
      rewrite Z_mod_plus; try lia. rewrite (Ndiv2 H_N).
      setoid_rewrite (N_is_even H_N). replace (2 * (Z.of_nat N / 2) * x) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
      discriminate.
    + destruct (proj1_sig t =? Z.of_nat N - 1) eqn:H_t1.
      ++right. repeat split; reflexivity.
      ++destruct (proj1_sig t <? Z.of_nat N / 2 - 1) eqn:H_t.
        * unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H. rewrite H_t1 in H. rewrite H_t in H. simpl in H.
          apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
          apply apply_mod_2 in H; try lia.
          apply mod4_div2 in H0, H1. replace (1/2) with 0 in H0 by trivial. replace (2/2) with 1 in H1 by trivial.
          rewrite Z.add_mod; try lia. rewrite <- plus_minus_mod2. rewrite H0. rewrite H1.
          setoid_rewrite (N_is_even H_N). replace (x * (2 * (Z.of_nat N / 2))) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
          discriminate.
        * left. repeat split; reflexivity.
Qed.

Lemma aux_NoRecEnc_13: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> forall (g1 g2:Set2N) (t:SetN), Fin_eq N (f_6 g1 t) (f_6 g2 t) -> (proj1_sig g1) mod 4 = 1 -> (proj1_sig g2) mod 4 = 3 -> (proj1_sig t =? Z.of_nat N - 3 = true) \/ (proj1_sig t =? Z.of_nat N - 3 = false /\ proj1_sig t =? Z.of_nat N - 2 = true).
Proof.
  intro H_N.
  intros. destruct (proj1_sig t =? Z.of_nat N - 3) eqn:H_t3.
  - left. reflexivity.
  - destruct (proj1_sig t =? Z.of_nat N - 2) eqn:H_t2.
    + right. split; reflexivity.
    + destruct (proj1_sig t =? Z.of_nat N - 1) eqn:H_t1.
      ++unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H. rewrite H_t1 in H. simpl in H.
        pose proof (t_is_big t H_N). assert (proj1_sig t <? (Z.of_nat N)/2 - 1 = false); try lia.
        rewrite H3 in H.  simpl in H.

        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        apply apply_mod_2 in H; try lia.
        apply mod4_div2 in H0, H1. replace (1/2) with 0 in H0 by trivial. replace (3/2) with (1 mod 2) in H1 by trivial.
        apply mod_to_div in H0; try lia. apply rewrite_mod_to_div in H1; try lia. destruct H0, H1. rewrite H0. destruct t, g2. simpl in *.
        pose proof (N_is_even H_N).
        replace (x0 * 2 - x2 - x3 / 2 - 1) with (1 + (x0-x1-1-Z.of_nat N/2)*2) by lia.
        rewrite Z_mod_plus; try lia.
      ++destruct (proj1_sig t <? Z.of_nat N / 2 - 1) eqn:H_t.
        * unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H. rewrite H_t1 in H. rewrite H_t in H. simpl in H.
          apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
          apply apply_mod_2 in H; try lia.
          apply mod4_div2 in H0, H1. replace (1/2) with 0 in H0 by trivial. replace (3/2) with 1 in H1 by trivial.
          rewrite Z.add_mod; try lia. setoid_rewrite Z.add_mod at 2; try lia. rewrite <- plus_minus_mod2. rewrite H0. rewrite H1. replace (2 * proj1_sig t) with (proj1_sig t*2) by ring. rewrite Z_mod_mult.
          setoid_rewrite (N_is_even H_N). replace (x * (2 * (Z.of_nat N / 2))) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
          discriminate.
        * unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H. rewrite H_t1 in H. rewrite H_t in H. simpl in H.
          apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
          apply apply_mod_2 in H; try lia.
          apply mod4_div2 in H0, H1. replace (1/2) with 0 in H0 by trivial. replace (3/2) with (1 mod 2) in H1 by trivial.
          apply mod_to_div in H0; try lia. apply rewrite_mod_to_div in H1; try lia. destruct H0, H1. rewrite H0.
          assert (x0 * 2 + 2 * (Z.of_nat N / 2) - 2 * proj1_sig t - proj1_sig g2 / 2 - 4 = 1 + (x0 + Z.of_nat N / 2 - proj1_sig t - x1 - 3) * 2). lia.
          rewrite H2.
          rewrite Z_mod_plus; try lia.
          setoid_rewrite (N_is_even H_N). replace (x * (2 * (Z.of_nat N / 2))) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
          discriminate.
Qed.

Lemma aux_NoRecEnc_23: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> forall (g1 g2:Set2N) (t:SetN), Fin_eq N (f_6 g1 t) (f_6 g2 t) -> (proj1_sig g1) mod 4 = 2 -> (proj1_sig g2) mod 4 = 3 -> (proj1_sig t =? Z.of_nat N - 3 = false /\ proj1_sig t =? Z.of_nat N - 2 = false /\ proj1_sig t =? Z.of_nat N - 1 = false /\ proj1_sig t <? (Z.of_nat N)/2 - 1 = true).
Proof.
  intro H_N.
  intros. destruct (proj1_sig t =? Z.of_nat N - 3) eqn:H_t3.
  - unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H.
    apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
    apply apply_mod_2 in H; try lia.
    apply mod4_div2 in H0, H1. replace (2/2) with (1 mod 2) in H0 by trivial. replace (3/2) with (1 mod 2) in H1 by trivial.
    apply rewrite_mod_to_div in H0; try lia. apply rewrite_mod_to_div in H1; try lia. destruct H0, H1. destruct t, g1, g2. simpl in *.
    pose proof (N_is_even H_N).
    replace (x3 / 2 + Z.of_nat N - x4 / 2 - Z.of_nat N / 2 - 2) with (Z.of_nat N / 2 + (x0-x1-1)*2) by lia.
    rewrite Z_mod_plus; try lia. rewrite (Ndiv2 H_N).
    setoid_rewrite (N_is_even H_N). replace (2 * (Z.of_nat N / 2) * x) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
    discriminate.
  - destruct (proj1_sig t =? Z.of_nat N - 2) eqn:H_t2.
    + unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H.
      apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
      apply apply_mod_2 in H; try lia.
      apply mod4_div2 in H0, H1. replace (2/2) with (1 mod 2) in H0 by trivial. replace (3/2) with (1 mod 2) in H1 by trivial.
      apply rewrite_mod_to_div in H0; try lia. apply rewrite_mod_to_div in H1; try lia. destruct H0, H1. destruct t, g1, g2. simpl in *.
      pose proof (N_is_even H_N).
      replace (x3 / 2 + Z.of_nat N - x4 / 2 - Z.of_nat N / 2 - 2) with (Z.of_nat N / 2 + (x0-x1-1)*2) by lia.
      rewrite Z_mod_plus; try lia. rewrite (Ndiv2 H_N).
      setoid_rewrite (N_is_even H_N). replace (2 * (Z.of_nat N / 2) * x) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
      discriminate.
    + destruct (proj1_sig t =? Z.of_nat N - 1) eqn:H_t1.
      ++unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H. rewrite H_t1 in H.
        apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
        apply apply_mod_2 in H; try lia.
        apply mod4_div2 in H0, H1. replace (2/2) with (1 mod 2) in H0 by trivial. replace (3/2) with (1 mod 2) in H1 by trivial.
        apply rewrite_mod_to_div in H0; try lia. apply rewrite_mod_to_div in H1; try lia. destruct H0, H1. destruct t, g1, g2. simpl in *.
        pose proof (N_is_even H_N).
        replace (x3 / 2 + Z.of_nat N - x4 / 2 - Z.of_nat N / 2 - 2) with (Z.of_nat N / 2 + (x0-x1-1)*2) by lia.
        rewrite Z_mod_plus; try lia. rewrite (Ndiv2 H_N).
        setoid_rewrite (N_is_even H_N). replace (2 * (Z.of_nat N / 2) * x) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
        discriminate.
      ++destruct (proj1_sig t <? Z.of_nat N / 2 - 1) eqn:H_t.
        * repeat split; reflexivity.
        * unfold f_6, Fin_eq in H. rewrite H0 in H. rewrite H1 in H. rewrite H_t3 in H. rewrite H_t2 in H. rewrite H_t1 in H. rewrite H_t in H.
          apply rewrite_mod_to_div in H; try lia. destruct H. ring_simplify in H.
          apply apply_mod_2 in H; try lia.
          apply mod4_div2 in H0, H1. replace (2/2) with (1 mod 2) in H0 by trivial. replace (3/2) with (1 mod 2) in H1 by trivial.
          apply rewrite_mod_to_div in H0; try lia. apply rewrite_mod_to_div in H1; try lia. destruct H0, H1. destruct t, g1, g2. simpl in *.
          replace (x3 / 2 - x4 / 2 + Z.of_nat N / 2 - 2) with (Z.of_nat N / 2 + (x0-x1-1)*2) by lia.
          rewrite Z_mod_plus; try lia. rewrite (Ndiv2 H_N).
          setoid_rewrite (N_is_even H_N). replace (x * (2 * (Z.of_nat N / 2))) with ((x*(Z.of_nat N / 2))*2) by ring. rewrite Z_mod_mult.
          discriminate.
Qed.

Lemma aux_NoRec_sub_eq_eq: forall a b c d e f z:Z, z>0 -> (a+b) mod z = (c+d) mod z -> (a+e) mod z = (c+f) mod z -> exists x, b+f-d-e = x*z.
Proof.
  intros.
  apply rewrite_mod_to_div in H0; try lia. destruct H0. ring_simplify in H0.
  apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
  exists (x-x0). lia.
Qed.

Lemma div2_ineq: forall x:Z, 0 <= x < Z.of_nat (2 * N) ->  0 <= x/2 < Z.of_nat (N).
Proof.
  intros. destruct H.

  assert (0 <= x / 2 <= Z.of_nat N).
  pose proof (Z.div_le_mono 0 x 2). pose proof (Z.div_le_mono x (Z.of_nat (2 * N)) 2).
  replace (Z.of_nat (2 * N)) with (2 * Z.of_nat N) in H2 by lia. rewrite simpl_mul_div in H2; try lia.
  split.
  1: apply H1; try lia.
  1: apply H2; try lia.

  assert (x / 2 <> Z.of_nat N).
  intro. replace x with (2*(x/2) + x mod 2) in H0. 2: { rewrite Z.mod_eq; try lia. }
  rewrite H2 in H0. pose proof (modulo_lt_divisor x 2). lia.

  lia.
Qed.
Lemma eq_crit2: forall x y:Z, x mod 2 = y mod 2 -> x/2 = y/2 -> x=y.
Proof.
  intros.
  setoid_rewrite Z.mod_eq in H; lia.
Qed.
Lemma mod4_to_mod2: forall a b:Z, a mod 4 = b mod 4 -> a mod 2 = b mod 2.
Proof.
  intros.
  apply rewrite_mod_to_div in H; try lia. destruct H.
  apply rewrite_div_to_mod; try lia. exists (2*x). lia.
Qed.


Lemma f_6_no_rec_enc: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> no_rec_enc f_6.
  intro H_N. apply g_symetries. intros.
  destruct (case_mod_4 (proj1_sig g1)) as [Hg1_0 | [Hg1_1 | [Hg1_2 | Hg1_3]]]; destruct (case_mod_4 (proj1_sig g2)) as [Hg2_0 | [Hg2_1 | [Hg2_2 | Hg2_3]]].
  - (* same mod *)
    unfold f_6, Fin_eq in H1. rewrite Hg1_0 in H1. rewrite Hg2_0 in H1. simpl in H1.
    unfold f_6, Fin_eq in H2. rewrite Hg1_0 in H2. rewrite Hg2_0 in H2. simpl in H2.

    apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
    apply aux_no_rec_bound_eq_gnl in H1.
    2:{ destruct g1, g2. cbn [proj1_sig] in *. apply div2_ineq in a, a0. lia. }
    apply eq_crit2; try assumption.
    apply mod4_to_mod2. lia.
  - pose proof (aux_NoRecEnc_01 H_N g1 g2 t1 H1 Hg1_0 Hg2_1).
    pose proof (aux_NoRecEnc_01 H_N g1 g2 t2 H2 Hg1_0 Hg2_1).
    unfold f_6, Fin_eq in H1. rewrite Hg1_0 in H1. rewrite Hg2_1 in H1. rewrite H3 in H1. simpl in H1.
    unfold f_6, Fin_eq in H2. rewrite Hg1_0 in H2. rewrite Hg2_1 in H2. rewrite H4 in H2. simpl in H2.

    assert (Z.of_nat N > 0). lia.
    pose proof (aux_NoRec_sub_eq_eq _ _ _ _ _ _ _ H5 H1 H2).
    destruct H6. ring_simplify in H6.
    apply aux_no_rec_bound_eq in H6.
    2:{ pose proof (N_is_even H_N). destruct t1, t2. cbn [proj1_sig] in *. lia. }
    lia.
  - pose proof (aux_NoRecEnc_02 H_N g1 g2 t1 H1 Hg1_0 Hg2_2).
    pose proof (aux_NoRecEnc_02 H_N g1 g2 t2 H2 Hg1_0 Hg2_2).
    destruct H3; destruct H4.
    + lia. (* time symetry *)
    + destruct H4 as [H4 H4'].
      unfold f_6, Fin_eq in H1. rewrite Hg1_0 in H1. rewrite Hg2_2 in H1. rewrite H3 in H1. simpl in H1.
      unfold f_6, Fin_eq in H2. rewrite Hg1_0 in H2. rewrite Hg2_2 in H2. rewrite H4 in H2. rewrite H4' in H2. simpl in H2.

      assert (Z.of_nat N > 0). lia.
      pose proof (aux_NoRec_sub_eq_eq _ _ _ _ _ _ _ H5 H1 H2).
      destruct H6. ring_simplify in H6. replace (- proj1_sig t1 + proj1_sig t2 + 1) with (2-0) in H6 by lia.
      apply aux_no_rec_bound_eq_gnl in H6.
      2:{ lia. }
      lia.
    + lia. (* time symetry *)
    + lia. (* time symetry *)
  - pose proof (aux_NoRecEnc_03 H_N g1 g2 t1 H1 Hg1_0 Hg2_3).
    pose proof (aux_NoRecEnc_03 H_N g1 g2 t2 H2 Hg1_0 Hg2_3).
    destruct H3; destruct H4.
    + destruct H3 as [Ht1_0 [Ht1_3 [Ht1_2 Ht1_1]]]. destruct H4 as [Ht2_0 [Ht2_3 [Ht2_2 Ht2_1]]].
      unfold f_6, Fin_eq in H1. rewrite Hg1_0 in H1. rewrite Hg2_3 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. rewrite Ht1_1 in H1. rewrite Ht1_0 in H1. simpl in H1.
      unfold f_6, Fin_eq in H2. rewrite Hg1_0 in H2. rewrite Hg2_3 in H2. rewrite Ht2_3 in H2. rewrite Ht2_2 in H2. rewrite Ht2_1 in H2. rewrite Ht2_0 in H2. simpl in H2.

      assert (Z.of_nat N > 0). lia.
      pose proof (aux_NoRec_sub_eq_eq _ _ _ _ _ _ _ H3 H1 H2).
      destruct H4. ring_simplify in H4.
      apply aux_no_rec_bound_eq in H4.
      2:{ pose proof (N_is_even H_N). destruct t1, t2. cbn [proj1_sig] in *. lia. }
      lia.
    + destruct H3 as [Ht1_0 [Ht1_3 [Ht1_2 Ht1_1]]]. destruct H4 as [Ht2_3 [Ht2_2 Ht2_1]].
      unfold f_6, Fin_eq in H1. rewrite Hg1_0 in H1. rewrite Hg2_3 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. rewrite Ht1_1 in H1. rewrite Ht1_0 in H1. simpl in H1.
      unfold f_6, Fin_eq in H2. rewrite Hg1_0 in H2. rewrite Hg2_3 in H2. rewrite Ht2_3 in H2. rewrite Ht2_2 in H2. rewrite Ht2_1 in H2. simpl in H2.

      assert (Z.of_nat N > 0). lia.
      apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
      apply rewrite_mod_to_div in H2; try lia. destruct H2. ring_simplify in H2.
      pose proof (N_is_even H_N).
      assert (Z.of_nat N - 2 * proj1_sig t1 - 4 = (x - x0 - 1) * Z.of_nat N). lia.

      apply aux_no_rec_bound_eq_gnl in H5.
      2:{ pose proof (N_is_even H_N). destruct t1. cbn [proj1_sig] in *. lia. }
      lia.
    + destruct t2. simpl in *. lia. (* time symetry *)
    + lia. (* time symetry *)

  - lia. (* g symetry *)
  - (* same mod *)
    destruct (proj1_sig t1 <? Z.of_nat N / 2 - 1) eqn:H_t1.
    * unfold f_6, Fin_eq in H1. rewrite Hg1_1 in H1. rewrite Hg2_1 in H1. rewrite H_t1 in H1. simpl in H1.

      apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
      apply aux_no_rec_bound_eq_gnl in H1.
      2:{ destruct g1, g2. cbn [proj1_sig] in *. destruct H2. apply div2_ineq in a, a0. lia. }
      apply eq_crit2; try assumption.
      apply mod4_to_mod2. lia.
    * unfold f_6, Fin_eq in H1. rewrite Hg1_1 in H1. rewrite Hg2_1 in H1. rewrite H_t1 in H1. simpl in H1.

      apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
      apply aux_no_rec_bound_eq_gnl in H1.
      2:{ destruct g1, g2. cbn [proj1_sig] in *. destruct H2. apply div2_ineq in a, a0. lia. }
      apply eq_crit2; try assumption.
      apply mod4_to_mod2. lia.
  - pose proof (aux_NoRecEnc_12 H_N g1 g2 t1 H1 Hg1_1 Hg2_2).
    pose proof (aux_NoRecEnc_12 H_N g1 g2 t2 H2 Hg1_1 Hg2_2).
    destruct H3; destruct H4.
    + destruct H3 as [Ht1_0 [Ht1_3 [Ht1_2 Ht1_1]]]. destruct H4 as [Ht2_0 [Ht2_3 [Ht2_2 Ht2_1]]].
      unfold f_6, Fin_eq in H1. rewrite Hg1_1 in H1. rewrite Hg2_2 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. rewrite Ht1_1 in H1. rewrite Ht1_0 in H1. simpl in H1.
      unfold f_6, Fin_eq in H2. rewrite Hg1_1 in H2. rewrite Hg2_2 in H2. rewrite Ht2_3 in H2. rewrite Ht2_2 in H2. rewrite Ht2_1 in H2. rewrite Ht2_0 in H2.  simpl in H2.

      assert (Z.of_nat N > 0). lia.
      pose proof (aux_NoRec_sub_eq_eq _ _ _ _ _ _ _ H3 H1 H2).
      destruct H4. ring_simplify in H4.
      apply aux_no_rec_bound_eq in H4.
      2:{ pose proof (N_is_even H_N). destruct t1, t2. cbn [proj1_sig] in *. lia. }
      lia.
    + destruct H3 as [Ht1_0 [Ht1_3 [Ht1_2 Ht1_1]]]. destruct H4 as [Ht2_3 [Ht2_2 Ht2_1]].
      unfold f_6, Fin_eq in H1. rewrite Hg1_1 in H1. rewrite Hg2_2 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. rewrite Ht1_1 in H1. rewrite Ht1_0 in H1. simpl in H1.
      unfold f_6, Fin_eq in H2. rewrite Hg1_1 in H2. rewrite Hg2_2 in H2. rewrite Ht2_3 in H2. rewrite Ht2_2 in H2. rewrite Ht2_1 in H2. simpl in H2.
      assert (Ht2_0: (proj1_sig t2 <? Z.of_nat N / 2 - 1) = false). destruct t2. simpl in *. lia. rewrite Ht2_0 in H2.

      assert (Z.of_nat N > 0). lia.
      apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
      apply rewrite_mod_to_div in H2; try lia. destruct H2. ring_simplify in H2.
      pose proof (N_is_even H_N).
      assert (Z.of_nat N - 2 * proj1_sig t1 - 4 = (x - x0 - 1) * Z.of_nat N). lia.

      apply aux_no_rec_bound_eq_gnl in H5.
      2:{ pose proof (N_is_even H_N). destruct t1. cbn [proj1_sig] in *. lia. }
      lia.
    + destruct t2. simpl in *. lia. (* time symetry *)
    + lia. (* time symetry *)
  - pose proof (aux_NoRecEnc_13 H_N g1 g2 t1 H1 Hg1_1 Hg2_3).
    pose proof (aux_NoRecEnc_13 H_N g1 g2 t2 H2 Hg1_1 Hg2_3).
    destruct H3; destruct H4.
    + lia. (* time symetry *)
    + destruct H4 as [H4 H4'].
      unfold f_6, Fin_eq in H1. rewrite Hg1_1 in H1. rewrite Hg2_3 in H1. rewrite H3 in H1.
      unfold f_6, Fin_eq in H2. rewrite Hg1_1 in H2. rewrite Hg2_3 in H2. rewrite H4 in H2. rewrite H4' in H2.
      assert (H_t1_big:proj1_sig t1 <? Z.of_nat N / 2 - 1 = false). pose proof (t_is_big t1 H_N). lia. rewrite H_t1_big in H1.
      assert (H_t2_big:proj1_sig t2 <? Z.of_nat N / 2 - 1 = false). pose proof (t_is_big t2 H_N). lia. rewrite H_t2_big in H2.
      simpl in H1. simpl in H2.

      assert (Z.of_nat N > 0). lia.
      assert (H1':(proj1_sig g1 / 2 + Z.of_nat N / 2 - 2 - proj1_sig t1) mod Z.of_nat N = (proj1_sig g2 / 2 + Z.of_nat N / 2 + 0) mod Z.of_nat N). rewrite Z.add_0_r. exact H1.
      pose proof (aux_NoRec_sub_eq_eq _ _ _ _ _ _ _ H5 H1' H2).
      destruct H6. ring_simplify in H6. replace (- proj1_sig t1 + proj1_sig t2 + 1) with (2-0) in H6 by lia.
      apply aux_no_rec_bound_eq_gnl in H6.
      2:{ lia. }
      lia.
    + lia. (* time symetry *)
    + lia. (* time symetry *)

  - lia. (* g symetry *)
  - lia. (* g symetry *)
  - (* same mod *)
    destruct (proj1_sig t1 =? Z.of_nat N - 3) eqn:Ht1_3.
    + unfold f_6, Fin_eq in H1. rewrite Hg1_2 in H1. rewrite Hg2_2 in H1. rewrite Ht1_3 in H1. simpl in H1.

      apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1. rewrite Z.mul_comm in H1.
      apply aux_no_rec_bound_eq_gnl in H1.
      2:{ destruct g1, g2. cbn [proj1_sig] in *. destruct H2. apply div2_ineq in a, a0. lia. }
      apply eq_crit2; try assumption.
      apply mod4_to_mod2. lia.
    + destruct (proj1_sig t1 =? Z.of_nat N - 2) eqn:Ht1_2.
      ++unfold f_6, Fin_eq in H1. rewrite Hg1_2 in H1. rewrite Hg2_2 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. simpl in H1.

        apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1. rewrite Z.mul_comm in H1.
        apply aux_no_rec_bound_eq_gnl in H1.
        2:{ destruct g1, g2. cbn [proj1_sig] in *. destruct H2. apply div2_ineq in a, a0. lia. }
        apply eq_crit2; try assumption.
        apply mod4_to_mod2. lia.
      ++destruct (proj1_sig t1 =? Z.of_nat N - 1) eqn:Ht1_1.
        * unfold f_6, Fin_eq in H1. rewrite Hg1_2 in H1. rewrite Hg2_2 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. rewrite Ht1_1 in H1. simpl in H1.

          apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1. rewrite Z.mul_comm in H1.
          apply aux_no_rec_bound_eq_gnl in H1.
          2:{ destruct g1, g2. cbn [proj1_sig] in *. destruct H2. apply div2_ineq in a, a0. lia. }
          apply eq_crit2; try assumption.
          apply mod4_to_mod2. lia.
        * unfold f_6, Fin_eq in H1. rewrite Hg1_2 in H1. rewrite Hg2_2 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. rewrite Ht1_1 in H1. simpl in H1.

          apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
          apply aux_no_rec_bound_eq_gnl in H1.
          2:{ destruct g1, g2. cbn [proj1_sig] in *. destruct H2. apply div2_ineq in a, a0. lia. }
          apply eq_crit2; try assumption.
          apply mod4_to_mod2. lia.
  - pose proof (aux_NoRecEnc_23 H_N g1 g2 t1 H1 Hg1_2 Hg2_3). destruct H3 as [Ht1_3 [Ht1_2 [Ht1_1 Ht1_0]]].
    pose proof (aux_NoRecEnc_23 H_N g1 g2 t2 H2 Hg1_2 Hg2_3). destruct H3 as [Ht2_3 [Ht2_2 [Ht2_1 Ht2_0]]].
    unfold f_6, Fin_eq in H1. rewrite Hg1_2 in H1. rewrite Hg2_3 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. rewrite Ht1_1 in H1. rewrite Ht1_0 in H1. simpl in H1.
    unfold f_6, Fin_eq in H2. rewrite Hg1_2 in H2. rewrite Hg2_3 in H2. rewrite Ht2_3 in H2. rewrite Ht2_2 in H2. rewrite Ht2_1 in H2. rewrite Ht2_0 in H2. simpl in H2.

    assert (Z.of_nat N > 0). lia.
    pose proof (aux_NoRec_sub_eq_eq _ _ _ _ _ _ _ H3 H1 H2).
    destruct H4. ring_simplify in H4.
    apply aux_no_rec_bound_eq_gnl in H4.
    2:{ pose proof (N_is_even H_N). destruct t1, t2. cbn [proj1_sig] in *. lia. }
    lia.

  - lia. (* g symetry *)
  - lia. (* g symetry *)
  - lia. (* g symetry *)
  - (* same mod *)
    destruct (proj1_sig t1 =? Z.of_nat N - 3) eqn:Ht1_3.
    + unfold f_6, Fin_eq in H1. rewrite Hg1_3 in H1. rewrite Hg2_3 in H1. rewrite Ht1_3 in H1. simpl in H1.

      apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
      apply aux_no_rec_bound_eq_gnl in H1.
      2:{ destruct g1, g2. cbn [proj1_sig] in *. destruct H2. apply div2_ineq in a, a0. lia. }
      apply eq_crit2; try assumption.
      apply mod4_to_mod2. lia.
    + destruct (proj1_sig t1 =? Z.of_nat N - 2) eqn:Ht1_2.
      ++unfold f_6, Fin_eq in H1. rewrite Hg1_3 in H1. rewrite Hg2_3 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. simpl in H1.

        apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
        apply aux_no_rec_bound_eq_gnl in H1.
        2:{ destruct g1, g2. cbn [proj1_sig] in *. destruct H2. apply div2_ineq in a, a0. lia. }
        apply eq_crit2; try assumption.
        apply mod4_to_mod2. lia.
      ++destruct (proj1_sig t1 =? Z.of_nat N - 1) eqn:Ht1_1.
        * unfold f_6, Fin_eq in H1. rewrite Hg1_3 in H1. rewrite Hg2_3 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. rewrite Ht1_1 in H1. simpl in H1.

          apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
          apply aux_no_rec_bound_eq_gnl in H1.
          2:{ destruct g1, g2. cbn [proj1_sig] in *. destruct H2. apply div2_ineq in a, a0. lia. }
          apply eq_crit2; try assumption.
          apply mod4_to_mod2. lia.
        * destruct (proj1_sig t1 <? Z.of_nat N / 2 - 1) eqn:Ht1.
          **unfold f_6, Fin_eq in H1. rewrite Hg1_3 in H1. rewrite Hg2_3 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. rewrite Ht1_1 in H1. rewrite Ht1 in H1. simpl in H1.

            apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
            apply aux_no_rec_bound_eq_gnl in H1.
            2:{ destruct g1, g2. cbn [proj1_sig] in *. destruct H2. apply div2_ineq in a, a0. lia. }
            apply eq_crit2; try assumption.
            apply mod4_to_mod2. lia.
          **unfold f_6, Fin_eq in H1. rewrite Hg1_3 in H1. rewrite Hg2_3 in H1. rewrite Ht1_3 in H1. rewrite Ht1_2 in H1. rewrite Ht1_1 in H1. rewrite Ht1 in H1. simpl in H1.

            apply rewrite_mod_to_div in H1; try lia. destruct H1. ring_simplify in H1.
            apply aux_no_rec_bound_eq_gnl in H1.
            2:{ destruct g1, g2. cbn [proj1_sig] in *. destruct H2. apply div2_ineq in a, a0. lia. }
            apply eq_crit2; try assumption.
            apply mod4_to_mod2. lia.
Qed.



Theorem div4p2_case: (Z.of_nat N >= 6 /\ Z.of_nat N mod 4 = 2) -> perfect_schedule_weak f_6.
Proof.
  intro H_N.
  unfold perfect_schedule_weak.
  split; try split; try split.
  - unfold fin_eq_equality. intros. unfold f_6. repeat rewrite H. reflexivity.
  - exact (f_6_no_rec_enc H_N).
  - exact (f_6_at_least_2_by_workshop H_N).
  - exact (f_6_injective H_N).
Qed.




(* FINAL RESULT *)

Theorem solution_exist_when_N_is_not_2: (N<>0)%nat -> (N<>2)%nat -> exists (f:ScheduleType), perfect_schedule_strong f.
Proof.
  intros. destruct (case_mod_4 (Z.of_nat N)) as [H_0 | [H_1 | [H_2 | H_3]]].
  - exists f_div4. apply equivalence_weak_strong. apply div4_case. exact H_0.
  - exists f_odd. apply equivalence_weak_strong. apply odd_case.
    replace 1 with (1 mod 4) in H_1 by trivial. apply rewrite_mod_to_div in H_1; try lia. destruct H_1.
    replace 1 with (1 mod 2) by trivial. apply rewrite_div_to_mod; try lia. exists (2*x). lia.
  - exists f_6. apply equivalence_weak_strong. apply div4p2_case. split; try assumption.
    replace 2 with (2 mod 4) in H_2 by trivial. apply rewrite_mod_to_div in H_2; try lia. destruct H_2. lia.
  - exists f_odd. apply equivalence_weak_strong. apply odd_case.
    replace 3 with (3 mod 4) in H_3 by trivial. apply rewrite_mod_to_div in H_3; try lia. destruct H_3.
    replace 1 with (1 mod 2) by trivial. apply rewrite_div_to_mod; try lia. exists (2*x+1). lia.
Qed.



End NatMod.
