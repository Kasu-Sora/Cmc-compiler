Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_core_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint cm_region_generations_unique regions : Prop := match regions with []=>True | r::rest=>(forall other,In other rest -> cm_region_gen other<>cm_region_gen r) /\ cm_region_generations_unique rest end.
Lemma cm_global_regions_generation_bounds p gs index r : In r (cm_global_regions p gs index) -> 1+index<=cm_region_gen r<1+index+Zlength gs.
Proof.
 revert index; induction gs as [|g gs IH]; intros index IN; [contradiction|].
 cbn [cm_global_regions] in IN; rewrite Zlength_cons; destruct IN as [<-|IN].
 - cbn [cm_region_gen]; unfold cm_global_generation; pose proof (ListLib.General.Length.Zlength_nonneg gs); lia.
 - specialize (IH (index+1) IN); lia.
Qed.
Lemma cm_string_regions_generation_bounds p ss index r : In r (cm_string_regions p ss index) -> 1+Zlength (cm_program_globals p)+index<=cm_region_gen r<1+Zlength (cm_program_globals p)+index+Zlength ss.
Proof.
 revert index; induction ss as [|s ss IH]; intros index IN; [contradiction|].
 cbn [cm_string_regions] in IN; rewrite Zlength_cons; destruct IN as [<-|IN].
 - cbn [cm_region_gen]; unfold cm_string_generation; pose proof (ListLib.General.Length.Zlength_nonneg ss); lia.
 - specialize (IH (index+1) IN); lia.
Qed.
Lemma cm_global_regions_generations_unique p gs index : cm_region_generations_unique (cm_global_regions p gs index).
Proof.
 revert index; induction gs; intro index; [exact I|]; split; [|apply IHgs].
 intros r IN; pose proof (cm_global_regions_generation_bounds _ _ _ _ IN); cbn [cm_region_gen]; unfold cm_global_generation; lia.
Qed.
Lemma cm_string_regions_generations_unique p ss index : cm_region_generations_unique (cm_string_regions p ss index).
Proof.
 revert index; induction ss; intro index; [exact I|]; split; [|apply IHss].
 intros r IN; pose proof (cm_string_regions_generation_bounds _ _ _ _ IN); cbn [cm_region_gen]; unfold cm_string_generation; lia.
Qed.
Lemma cm_region_generations_unique_append xs ys : cm_region_generations_unique xs -> cm_region_generations_unique ys -> (forall x y,In x xs -> In y ys -> cm_region_gen x<>cm_region_gen y) -> cm_region_generations_unique (xs++ys).
Proof.
 induction xs as [|r rs IH]; intros X Y SEP; [exact Y|]; destruct X as [R RS]; split.
 - intros other IN; apply in_app_iff in IN; destruct IN as [IN|IN]; [now apply R|intro E; exact (SEP r other (or_introl eq_refl) IN (eq_sym E))].
 - apply IH; [exact RS|exact Y|intros x y IX IY; exact (SEP x y (or_intror IX) IY)].
Qed.
Lemma cm_static_regions_generations_unique p : cm_region_generations_unique (cm_static_regions p).
Proof.
 unfold cm_static_regions; apply cm_region_generations_unique_append; [apply cm_global_regions_generations_unique|apply cm_string_regions_generations_unique|].
 intros x y X Y; pose proof (cm_global_regions_generation_bounds _ _ _ _ X); pose proof (cm_string_regions_generation_bounds _ _ _ _ Y); lia.
Qed.
Lemma cm_region_base_member_unique regions r : cm_region_generations_unique regions -> In r regions -> cm_region_base regions (cm_region_gen r)=cm_region_base_field r.
Proof.
 induction regions as [|a rs IH]; intros U IN; [contradiction|]; destruct U as [SEP U]; cbn [cm_region_base]; destruct IN as [<-|IN].
 - now rewrite Z.eqb_refl.
 - assert (NE:cm_region_gen a=?cm_region_gen r=false) by (apply Z.eqb_neq; intro E; apply (SEP r IN); symmetry; exact E).
   rewrite NE; now apply IH.
Qed.
Lemma cm_static_region_base_member p r : In r (cm_static_regions p) -> cm_region_base (cm_static_regions p) (cm_region_gen r)=cm_region_base_field r.
Proof. intro IN; apply cm_region_base_member_unique; [apply cm_static_regions_generations_unique|exact IN]. Qed.
Lemma cm_typed_globals_nonnegative policy p : cm_typed_program policy p -> Forall (fun g=>0<=cm_global_size (cm_program_structs p) g) (cm_program_globals p).
Proof.
 intros [_ [WG _]]; apply Forall_forall; intros g IN.
 apply In_nth with (d:=cm_default_global) in IN; destruct IN as [i [B <-]].
 assert (BI:0<=Z.of_nat i<Zlength (cm_program_globals p)) by (rewrite Zlength_correct; lia).
 specialize (WG (Z.of_nat i) BI); unfold cm_global_at in WG; rewrite Nat2Z.id in WG; unfold cm_global_wf in WG; intuition lia.
Qed.
Lemma cm_globals_size_nonnegative_from_members structs gs : Forall (fun g=>0<=cm_global_size structs g) gs -> 0<=cm_globals_size structs gs.
Proof. intro H; induction H; cbn [cm_globals_size]; lia. Qed.
Lemma cm_strings_size_nonnegative ss : 0<=cm_strings_size ss.
Proof. induction ss as [|a ss IH]; [change (0<=0); lia|]. change (0<=cm_rep_string_size a+cm_strings_size ss). unfold cm_rep_string_size,cm_rep_string_length; pose proof (ListLib.General.Length.Zlength_nonneg (cm_string_bytes a)); lia. Qed.
Lemma cm_globals_prefix_cell_bounds_nat structs gs i : Forall (fun g=>0<=cm_global_size structs g) gs -> (i<length gs)%nat ->
 0<=cm_globals_prefix structs gs (Z.of_nat i) /\ cm_globals_prefix structs gs (Z.of_nat i)+cm_global_size structs (nth i gs cm_default_global)<=cm_globals_size structs gs.
Proof.
 revert i; induction gs as [|g gs IH]; intros i ALL B; [cbn in B; lia|]; inversion ALL as [|? ? G T]; subst.
 destruct i as [|i].
 - cbn [cm_globals_prefix nth Z.of_nat Z.eqb cm_globals_size]; pose proof (cm_globals_size_nonnegative_from_members _ _ T); lia.
 - assert (NZ:(Z.of_nat (S i)=?0)=false) by (apply Z.eqb_neq; lia).
   cbn [cm_globals_prefix]; rewrite NZ; replace (Z.of_nat (S i)-1) with (Z.of_nat i) by lia.
   specialize (IH i T ltac:(cbn in B; lia)); cbn [nth cm_globals_size]; lia.
Qed.
Lemma cm_strings_prefix_cell_bounds_nat ss i : (i<length ss)%nat ->
 0<=cm_strings_prefix ss (Z.of_nat i) /\ cm_strings_prefix ss (Z.of_nat i)+Zlength (cm_string_bytes (nth i ss (CMStringD [])))+1<=cm_strings_size ss.
Proof.
 revert i; induction ss as [|s ss IH]; intros i B; [cbn in B; lia|]. destruct i as [|i].
 - change (0<=0 /\ 0+Zlength (cm_string_bytes s)+1<=Zlength (cm_string_bytes s)+1+cm_strings_size ss); pose proof (cm_strings_size_nonnegative ss); lia.
 - assert (NZ:(Z.of_nat (S i)=?0)=false) by (apply Z.eqb_neq; lia).
   change (0<=cm_rep_strings_prefix (s::ss) (Z.of_nat (S i)) /\ cm_rep_strings_prefix (s::ss) (Z.of_nat (S i))+Zlength (cm_string_bytes (nth i ss (CMStringD [])))+1<=cm_rep_strings_size (s::ss)).
   cbn [cm_rep_strings_prefix]; rewrite NZ; replace (Z.of_nat (S i)-1) with (Z.of_nat i) by lia.
   specialize (IH i ltac:(cbn in B; lia)); unfold cm_strings_prefix,cm_strings_size in IH; unfold cm_rep_strings_size at 1; fold cm_rep_strings_size; unfold cm_rep_string_size,cm_rep_string_length; pose proof (ListLib.General.Length.Zlength_nonneg (cm_string_bytes s)); lia.
Qed.
Lemma cm_global_region_member_index_nat p gs start r : In r (cm_global_regions p gs start) -> exists i:nat,(i<length gs)%nat /\ r=CMRegion (cm_global_generation (start+Z.of_nat i)) (cm_global_address p (start+Z.of_nat i)) 0 (cm_global_size (cm_program_structs p) (nth i gs cm_default_global)) true true.
Proof.
 revert start; induction gs as [|g gs IH]; intros start IN; [contradiction|]; destruct IN as [<-|IN].
 - exists 0%nat; split; [cbn; lia|now rewrite Z.add_0_r].
 - destruct (IH (start+1) IN) as [i [B E]]; exists (S i); split; [cbn; lia|]. cbn [nth]; replace (start+Z.of_nat (S i)) with (start+1+Z.of_nat i) by lia; exact E.
Qed.
Lemma cm_string_region_member_index_nat p ss start r : In r (cm_string_regions p ss start) -> exists i:nat,(i<length ss)%nat /\ r=CMRegion (cm_string_generation p (start+Z.of_nat i)) (cm_string_address p (start+Z.of_nat i)) 0 (Zlength (cm_string_bytes (nth i ss (CMStringD [])))+1) false true.
Proof.
 revert start; induction ss as [|s ss IH]; intros start IN; [contradiction|]; destruct IN as [<-|IN].
 - exists 0%nat; split; [cbn; lia|now rewrite Z.add_0_r].
 - destruct (IH (start+1) IN) as [i [B E]]; exists (S i); split; [cbn; lia|]. cbn [nth]; replace (start+Z.of_nat (S i)) with (start+1+Z.of_nat i) by lia; exact E.
Qed.
Theorem cm_typed_static_regions_layout policy p : cm_typed_program policy p -> cm_static_regions_layout p (cm_static_regions p).
Proof.
 intro WF; pose proof (cm_typed_globals_nonnegative _ _ WF) as G; intros r IN LIVE; rewrite (cm_static_region_base_member _ _ IN).
 unfold cm_static_regions in IN; apply in_app_iff in IN; destruct IN as [IN|IN].
 - destruct (cm_global_region_member_index_nat _ _ _ _ IN) as [i [B ->]]; rewrite Z.add_0_l; cbn [cm_region_lo cm_region_hi cm_region_base_field].
   pose proof (cm_globals_prefix_cell_bounds_nat _ _ i G B) as [L U]; pose proof (cm_strings_size_nonnegative (cm_program_strings p)) as S.
   assert (N:0<=cm_global_size (cm_program_structs p) (nth i (cm_program_globals p) cm_default_global)) by (apply Forall_forall with (x:=nth i (cm_program_globals p) cm_default_global) in G; [exact G|now apply nth_In]).
   unfold cm_global_address,cm_static_size; repeat split; lia.
 - destruct (cm_string_region_member_index_nat _ _ _ _ IN) as [i [B ->]]; rewrite Z.add_0_l; cbn [cm_region_lo cm_region_hi cm_region_base_field].
   pose proof (cm_strings_prefix_cell_bounds_nat _ i B) as [L U]; pose proof (cm_globals_size_nonnegative_from_members _ _ G) as GS.
   pose proof (ListLib.General.Length.Zlength_nonneg (cm_string_bytes (nth i (cm_program_strings p) (CMStringD [])))) as N.
   unfold cm_string_address,cm_static_size; repeat split; lia.
Qed.
