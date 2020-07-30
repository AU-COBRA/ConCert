(** Proofs of correctness *)

From MetaCoq Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICWcbvEval PCUICTyping.

From ConCert Require Import CustomTactics MyEnv
     EnvSubst Ast EvalE PCUICFacts  PCUICTranslate
     PCUICCorrectnessAux Wf Misc.


From Coq Require Import String List.

Import ListNotations ssrbool Basics Lia.
Import NamelessSubst.

Local Set Keyed Unification.

(** Soundness (In the paper: Theorem 1) *)
Theorem expr_to_term_sound (n : nat) (ρ : env val) Σ1 Σ2
        (e1 e2 : expr) (v : val) :
  genv_ok Σ1 ->
  env_ok Σ1 ρ ->
  eval(n, Σ1, ρ, e1) = Ok v ->
  e1.[exprs ρ] = e2 ->
  iclosed_n 0 e2 = true ->
  Σ2 |- t⟦e2⟧Σ1 ⇓ t⟦of_val_i v⟧Σ1.
Proof.
  revert dependent v.
  revert dependent ρ.
  revert dependent e2.
  revert dependent e1.
  induction n.
  - intros;tryfalse.
  - intros e1 e2 ρ v Hgeok Hρ_ok He Henv Hc;destruct e1.
    + (* eRel *) simpl in *. autounfold with facts in *. simpl in *.
      destruct (lookup_i ρ n0) as [v1| ] eqn:Hlookup;tryfalse; simpl in He;inversion He;subst.
      destruct (Nat.ltb n0 (length ρ)) eqn:Hn0.
      * destruct (inst_env_i_in _ _ Hn0) as [v2 HH].
        destruct HH as [H1 H2].
        assert (v = v2) by congruence. subst.
        assert (ge_val_ok Σ1 v2) by (apply val_ok_ge_val_ok;eapply All_lookup_i;eauto).
        rewrite H2.
        eapply PcbvCurr.value_final; eapply Wcbv_of_value_value; eauto with hints.
        eapply All_lookup_i;eauto.
      * specialize (lookup_i_length_false _ _ Hn0) as Hnone;tryfalse.
    + (* eVar *) simpl;tryfalse.
    + (* eLambda *)
      subst. simpl in *.
      destruct (eval_type_i 0 ρ t) eqn:Hty;tryfalse;simpl in *.
      destruct (valid_env ρ 1 e1) eqn:He1;tryfalse. inv_andb Hc.
      inversion He;subst;simpl;eauto with hints.
      erewrite eval_type_i_subst_env;eauto.
      rewrite subst_env_ty_closed_n_eq with (n:=0) (m:=0);eauto with hints.
    + simpl in *. destruct (valid_env ρ 1 e1) eqn:He1;tryfalse.
      inversion He. subst;clear He.
      simpl. constructor;eauto.
    + (* eLetIn *)
      subst;simpl in *.
      unfold is_true in *;
        repeat rewrite  Bool.andb_true_iff in *.
      destruct Hc as [[? ?] ?].
      destruct (eval (n, Σ1, ρ, e1_1)) eqn:He1;tryfalse.
      destruct (eval_type_i 0 ρ t) eqn:Ht0;tryfalse. inversion He;subst;clear He.
      assert (He11 : Σ2 |- t⟦ e1_1 .[ exprs ρ] ⟧ Σ1 ⇓  t⟦ of_val_i v0 ⟧ Σ1)
        by (eauto with hints).
      assert (ty_expr_env_ok (exprs ρ) 0 e1_1) by (eapply eval_ty_expr_env_ok;eauto with hints).

      assert (iclosed_n #|exprs ρ # [e ~> of_val_i v0]| e1_2 = true).
      { simpl. eapply subst_env_iclosed_n_inv with (n:=1);eauto with hints. }

      assert (ty_expr_env_ok (exprs ρ # [e ~> of_val_i v0]) 0 e1_2).
      { change (exprs ρ # [e ~> of_val_i v0]) with (exprs (ρ # [e ~> v0])).
        eapply eval_ty_expr_env_ok;eauto with hints. simpl.
        replace #|ρ| with (#|exprs ρ|) by apply map_length.
        eapply subst_env_iclosed_n_inv with (n:=1);eauto with hints. }

      assert (val_ok Σ1 v0) by (eapply eval_val_ok;eauto with hints).
      assert (He12 : Σ2 |- t⟦ e1_2 .[exprs ((e, v0) :: ρ)] ⟧ Σ1 ⇓ t⟦ of_val_i v ⟧ Σ1).
      { eapply IHn with (ρ:=((e, v0) :: ρ));simpl;eauto 6 with hints. }
      simpl in *. unfold subst_env_i in *.
      econstructor;eauto. unfold subst1.
      erewrite <- subst_term_subst_env_par_rec in He12 by eauto with hints.
      erewrite <- subst_term_subst_env_par_rec;eauto with hints.
      rewrite PCUICCSubst.closed_subst by (apply expr_closed_term_closed;auto;eapply of_value_closed;eauto).
      now rewrite <- subst_app_simpl.
      now eapply ty_expr_env_ok_app_rec with (n:=0) (ρ1:=[(e,of_val_i v0)]).
    + (* eApp *)
      autounfold with facts in *. subst; cbn in *.
      destruct (expr_eval_general _ _ _ _ e1_2) eqn:He2;tryfalse.
      destruct (expr_eval_general _ _ _ _ e1_1) eqn:He1;tryfalse.
      apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
      assert (Hneq1 : [t⟦ inst_env_i ρ e1_2 ⟧ Σ1] <> []) by easy.
      destruct v1;tryfalse.
      * (* application evaluates to a constructor *)
        inversion_clear He. simpl_vars_to_apps. subst. simpl in *.
        rename e into n0.
        change (tApp (t⟦ vars_to_apps (eConstr i n0) (map of_val_i l) ⟧ Σ1) (t⟦ of_val_i v0 ⟧ Σ1))
          with (mkApps (t⟦ vars_to_apps (eConstr i n0) (map of_val_i l) ⟧ Σ1) [t⟦ of_val_i v0 ⟧ Σ1]).

        eapply PcbvCurr.eval_app_cong;eauto with hints.
        change (vars_to_apps (eConstr i n0) (map of_val_i l)) with (of_val_i (vConstr i n0 l)).
        eapply IHn;eauto with hints.
      * destruct c.
        ** (* the closure corresponds to lambda *)
          simpl in *. rename e0 into n0.
          simpl in *.
          assert (Hv0 : Σ2|- t⟦e1_2 .[ exprs ρ]⟧ Σ1 ⇓ t⟦ of_val_i v0 ⟧ Σ1)
            by eauto.
          assert (Hv0_ok : val_ok Σ1 v0) by (eapply eval_val_ok;eauto with hints).
          assert (Hlam_ok : val_ok Σ1 (vClos e n0 cmLam t t0 e1)) by
             (eapply eval_val_ok with(e:=e1_1);eauto with hints).
          inversion Hlam_ok;subst.
          assert (He_ok1 : env_ok Σ1 (e # [n0 ~> v0])) by now constructor.
          assert
           (Hlam : Σ2 |- t⟦e1_1 .[ exprs ρ]⟧ Σ1 ⇓ t⟦ of_val_i (vClos e n0 cmLam t t0 e1) ⟧ Σ1) by
              (eapply IHn with (ρ:=ρ);eauto).
          assert (AllEnv (fun e1 : expr => iclosed_n 0 e1 = true) (exprs e)).
           { inversion He_ok1. subst.
             apply All_map. unfold compose. simpl.
             eapply (All_impl (P := fun x => val_ok Σ1 (snd x)));eauto.
             intros a ?; destruct a; simpl;eauto with hints. }
           assert (iclosed_n 1 (e1 .[ exprs e] 1) = true)
            by eauto with hints.
           assert (ty_expr_env_ok [(n0, of_val_i v0)] 0 (e1.[exprs e]1)).
           { eapply ty_expr_env_ok_subst_env;eauto;simpl.
             change (exprs e # [n0 ~> of_val_i v0]) with (exprs (e # [n0 ~> v0])).
             eapply eval_ty_expr_env_ok;eauto. }

           assert (Hsubst : Σ2 |- (t⟦e1.[exprs e]1⟧Σ1){0 := t⟦of_val_i v0⟧Σ1} ⇓ t⟦of_val_i v⟧ Σ1).
           { rewrite subst_term_subst_env with (nm:=n0); eauto 8 with hints. }

           simpl in *.
           eapply PcbvCurr.eval_beta;eauto.
           rewrite PCUICCSubst.closed_subst
             by (apply expr_closed_term_closed;auto;
                 eapply of_value_closed;eauto);eauto.
        ** (* the closure corresponds to fix *)
          simpl in *. rename e into ρ'. rename e0 into n0.
          destruct v0;tryfalse.
          simpl in *.
          remember (t⟦e1_1.[exprs ρ] ⟧ Σ1) as tm1.
          remember (t⟦ e1_2.[exprs ρ] ⟧ Σ1) as tm2.
          assert (Hfix : Σ2 |- tm1 ⇓ t⟦ of_val_i (vClos ρ' n0 (cmFix _) t t0 e1) ⟧ Σ1)
            by (subst;eauto with hints).

          change (tApp tm1 tm2) with (mkApps tm1 [tm2]).
          simpl in Hfix.
          assert (Hok_ctor: val_ok Σ1 (vConstr i _ l)) by
              (eapply eval_val_ok with (e:=e1_2);eauto 8 with hints).
          inversion Hok_ctor as [ | | | ?????  HresC |];subst;clear Hok_ctor;eauto.
          assert (Hconstr : is_constructor 0 [t⟦ of_val_i (vConstr i e l) ⟧ Σ1]).
          { simpl. rewrite <- mkApps_vars_to_apps. cbn.
            unfold isConstruct_app.
            rewrite decompose_app_mkApps; now rewrite HresC. }
          eapply PcbvCurr.eval_fix with (av:=t⟦of_val_i (vConstr i e l)⟧Σ1) (argsv:=[]) (narg:=0);
            subst;eauto with hints;try reflexivity.
          cbn. remember (tFix _ _) as tfix.
          assert (Hok_ctor: val_ok Σ1 (vConstr i _ l)) by eauto 8 with hints.
          assert (Hok_fix : val_ok Σ1 ((vClos ρ' n0 (cmFix e2) t t0 e1))) by
              (eapply eval_val_ok with (ρ:=ρ)(e:=e1_1);eauto with hints).
          assert (tfix = t⟦eFix e2 n0 t t0 (e1.[exprs ρ']2)⟧ Σ1).
          { simpl. inversion Hok_fix;subst. subst.
            repeat rewrite subst_env_i_ty_closed_eq;eauto with hints. }
          assert (closed tfix).
          { rewrite H. apply expr_closed_term_closed;auto.
            inversion Hok_fix;subst.
            simpl. repeat split_andb;eauto with hints. }
          repeat rewrite PCUICCSubst.closed_subst by auto.
          rewrite simpl_subst_k by auto.
          clear Heqtfix. subst tfix.
          inversion Hok_fix;subst.

          remember (eFix _ _ _ _ _) as efix.

          assert (Hexprs : AllEnv (fun e => iclosed_n 0 e = true) (exprs ρ')).
          { apply All_map.
            eapply (All_impl (P := fun v => val_ok Σ1 (snd v)));try assumption;
              intros a ?;destruct a;cbv;eauto with hints. }

          eapply PcbvCurr.eval_beta;eauto with hints.
          eapply PcbvCurr.value_final.
          eapply Wcbv_value_vars_to_apps;eauto with hints.
          now eapply All_value_of_val.
          assert (All (fun v0 : val => iclosed_n 0 (of_val_i v0) = true) l).
          { eapply All_impl. apply X. intros.
            eapply of_value_closed;eauto with hints. }

          remember (vars_to_apps _ _) as args.
          assert (ty_expr_env_ok (nil # [e2 ~> efix] # [n0 ~> args]) 0 (e1.[ exprs ρ']2)).
          { subst.
            eapply ty_expr_env_ok_subst_env.
            assert (H : ty_expr_env_ok (exprs ((n0, vConstr i e l) :: (e2, vClos ρ' n0 (cmFix e2) t t0 e1) :: ρ'))  0 e1) by (eapply eval_ty_expr_env_ok;eauto).
            cbn in H. repeat rewrite subst_env_i_ty_closed_0_eq in H by auto. easy.
            now eapply closed_exprs. }
          assert (closed t⟦ args ⟧ Σ1).
          {subst;apply expr_closed_term_closed;auto.
           apply vars_to_apps_iclosed_n;eauto. }
          rewrite PCUICCSubst.closed_subst by auto.
          assert (AllEnv (iclosed_n 0) [(n0, args); (e2, efix)]).
          { subst;repeat constructor;unfold compose;simpl.
            now eapply vars_to_apps_iclosed_n. repeat split_andb;eauto with hints. }

          rewrite <- subst_app_simpl. simpl.

          erewrite subst_term_subst_env_2 with (nm1:=n0) (nm2:=e2) by eauto with hints.

          remember ((n0,_) :: (e2,_) :: ρ') as ρ''.
          eapply IHn with (ρ:=ρ''); subst;eauto with hints.
          rewrite <- subst_env_compose_2;
            (simpl; eauto using vars_to_apps_iclosed_n with hints).
          cbn.
          now repeat rewrite subst_env_i_ty_closed_0_eq by auto.
          repeat split_andb;eauto with hints.
      * rename e0 into n0.
        assert (Hv0 : Σ2 |- t⟦e1_2 .[ exprs ρ]⟧ Σ1 ⇓ t⟦ of_val_i v0 ⟧ Σ1)
          by eauto with hints.
        assert (Hv0_ok : val_ok Σ1 v0) by eauto 8 with hints.
        assert (Hlam_ok : val_ok Σ1 (vTyClos e n0 e1))
          by eauto 8 with hints.
        inversion Hlam_ok;subst.
        assert (He_ok1 : env_ok Σ1 (e # [n0 ~> v0])) by now constructor.
        assert
         (Hlam : Σ2 |- t⟦e1_1 .[ exprs ρ]⟧ Σ1 ⇓ t⟦ of_val_i (vTyClos e n0 e1) ⟧ Σ1) by
            (eapply IHn with (ρ:=ρ);eauto).
        assert (AllEnv (fun e1 : expr => iclosed_n 0 e1 = true) (exprs e)).
         { inversion He_ok1. subst.
           apply All_map. unfold compose. simpl.
           eapply (All_impl (P := fun x => val_ok Σ1 (snd x)));eauto.
           intros a ?; destruct a; simpl;eauto with hints. }
         assert (iclosed_n 1 (e1 .[ exprs e] 1) = true)
          by eauto with hints.
         assert (ty_expr_env_ok [(n0, of_val_i v0)] 0 (e1.[exprs e]1)).
         { eapply ty_expr_env_ok_subst_env;eauto;simpl.
           change (exprs e # [n0 ~> of_val_i v0]) with (exprs (e # [n0 ~> v0])).
           eapply eval_ty_expr_env_ok;eauto. }

         assert (Hsubst : Σ2 |- (t⟦e1.[exprs e]1⟧Σ1){0 := t⟦of_val_i v0⟧Σ1} ⇓ t⟦of_val_i v⟧ Σ1).
         { rewrite subst_term_subst_env with (nm:=n0); eauto 8 with hints. }

         simpl in *.
         eapply PcbvCurr.eval_beta;eauto.
         now rewrite PCUICCSubst.closed_subst by (apply expr_closed_term_closed;auto;eapply of_value_closed;eauto).
    + (* eConstr *)
      rename e into n0.
      cbn in He. destruct (resolve_constr Σ1 i n0) eqn:Hres;tryfalse.
      inversion He;subst;clear He.
      simpl in *. rewrite Hres in *. eauto with hints.
    + (* eConst *)
      (* The traslation does not support constants yet *)
      inversion He.
    + (* eCase *)
      unfold expr_eval_i in He. destruct p.
      (* dealing with the interpreter *)
      simpl in He.
      unfold is_true in Hc;subst;simpl in Hc;repeat rewrite  Bool.andb_true_iff in *.
      destruct Hc as [[[Hce1 ?] ?] HH].
      destruct (forallb _ l) eqn:Hl;tryfalse.
      destruct (eval_type_i _ _ t) eqn:Ht0;tryfalse;simpl in *.
      destruct (monad_utils.monad_map) eqn:Hmm;tryfalse.
      destruct (expr_eval_general _ _ _ _ e1) eqn:He1;tryfalse.
      destruct v0;tryfalse.
      destruct (string_dec _ _) eqn:Hi;tryfalse;subst.
      unfold resolve_constr in *. simpl.
      destruct (resolve_inductive _ _) eqn:HresI;tryfalse.
      destruct (lookup_with_ind _ _) eqn:Hfind_i;tryfalse.
      destruct p as [nparams cs]. destruct p0 as [i ci].  simpl in *.
      rewrite map_length.
      destruct (Nat.eqb nparams #|l0|) eqn:Hnparams;tryfalse.
      assert (HresC: resolve_constr Σ1 i0 e = Some (nparams,i, ci)).
      { unfold resolve_constr. rewrite HresI. rewrite Hfind_i. reflexivity. }

      destruct (match_pat _ _ _ _) eqn:Hpat;tryfalse.

      (* dealing with the translation and the evaluation in PCUIC *)
      *  assert (IH' : Σ2 |- t⟦ e1 .[ exprs ρ] ⟧ Σ1 ⇓ t⟦ of_val_i (vConstr i0 e l2) ⟧ Σ1) by
            eauto with hints.
        simpl in IH'.
        destruct p as [nm tys].
        rewrite map_map.
        erewrite <- mkApps_vars_to_apps_constr in IH' by eauto.
        simpl in IH'.
        eapply PcbvCurr.eval_iota;eauto.
        unfold iota_red in *. simpl in *.
        rewrite <- nth_default_eq in *.
        unfold nth_default in *.
        rewrite map_map.
        destruct (nth_error _) eqn:Hnth;remember ((fun (x : pat * expr) => _)) as f in Hnth.
        ** (* destruct p as [i ci0];simpl in *. *)
           specialize (lookup_ind_nth_error _ _ _ _ Hfind_i) as Hnth_eq.
           rewrite nth_error_map in Hnth_eq. destruct (nth_error cs i) eqn:Nci0;tryfalse.
           2 : { rewrite Nci0 in *;tryfalse. }
           erewrite map_nth_error in Hnth by eauto.
           inversion Hnth as [H1']. clear Hnth.
           rewrite Nci0 in Hnth_eq. simpl in Hnth_eq. inversion Hnth_eq. subst e.

           unfold trans_branch.

           (* Exploiting the fact that pattern-matching succeeds *)
           apply pat_match_succeeds in Hpat.
           destruct Hpat as [pt [Hfnd [Hci [Hl0 Hl2]]]].
           assert (
               Hfind : find (fun x => (pName (fst x) =? c.1)) (map f l) =
                     Some (f (pt, tys))).
           { eapply find_map with (p1 := fun x => (pName (fst x) =? c.1));auto.
             intros a;destruct a. subst f. cbn. reflexivity. }
           specialize (find_forallb_map _ Hfnd HH) as Hce1'. simpl in Hce1'.
           rewrite Hfind. subst f. cbn in *.
           assert (Hci' : #|ci| = #|pVars pt|) by lia.
           rewrite H3. rewrite Hci'. rewrite PeanoNat.Nat.eqb_refl.
           clear Hfind.

           subst. replace ((#|pVars pt| + 0)) with (#|pVars pt|) in * by lia.
           assert (Hok_constr: val_ok Σ1 (vConstr i0 c.1 l2)) by eauto 8 with hints.
           inversion Hok_constr;subst;clear Hok_constr.
           rewrite pat_to_lam_rev.
           apply pat_to_lam_app_par;eauto with hints.
           *** apply All_skipn.
               apply All_map.
               now eapply All_value_of_val.
           *** apply All_forallb;eauto.
               apply All_skipn.
               apply All_map.
               now eapply All_term_closed_of_val.
           *** rewrite rev_length. rewrite combine_length.
               rewrite map_length. rewrite Hci'.
               rewrite PeanoNat.Nat.eqb_eq in Hnparams.
               rewrite skipn_length. rewrite map_length.
               lia.
           *** rewrite PeanoNat.Nat.eqb_eq in Hnparams.
               assert (Hlen_pl0 :
                         #|pVars pt| = #|combine (rev (pVars pt)) (rev l2)|)
                 by (rewrite combine_length; repeat rewrite rev_length; lia).

               assert (#|pVars pt| = #|skipn nparams l2|) by (rewrite skipn_length;lia).
               rewrite <- map_skipn.
               rewrite <- map_rev.
               remember (fun x : val => t⟦ _ ⟧ _) as f.
               remember (fun x : string * expr => t⟦ snd x ⟧ Σ1) as g.
               remember (t⟦ tys .[_] _⟧ _) as te3.
               assert (Hmap : map f (rev (skipn nparams l2)) =
                       map g (map (fun_prod id of_val_i)(rev (combine (pVars pt) (skipn nparams l2))))).
               { rewrite map_map.
                 subst g;simpl.
                 rewrite <- combine_rev by auto.
                 change (fun x : name * val => t⟦ of_val_i (snd x) ⟧ Σ1) with
                  (fun x : name * val => ((expr_to_pcuic Σ1) ∘ of_val_i) (snd x)).
                 rewrite <- map_map with (g:=(expr_to_term Σ1) ∘ of_val_i)
                                        (f:=snd).
                 rewrite map_combine_snd. now subst.
                 now repeat rewrite rev_length. }
               rewrite Hmap. subst g te3.
               rewrite subst_term_subst_env_par;eauto with hints.
               eapply IHn with (ρ:=(rev (combine (pVars pt) (skipn nparams l2)) ++ ρ)%list);
                 eauto with hints.
               ****  eapply All_app_inv;eauto. apply All_rev.
                     eapply All_env_ok;eauto with hints. now apply All_skipn.
               ****
                     (* rewrite <- combine_rev by (subst;auto). *)
                     unfold fun_prod,id.
                     rewrite map_app. subst nparams.
                     remember (rev (combine (pVars pt) (skipn #|l0| l2))) as l_rev.
                     assert (Hlrev : #|pVars pt| = #|exprs l_rev|).
                     { subst. rewrite map_length.
                       rewrite rev_length. rewrite combine_length.
                       rewrite skipn_length;lia. }
                     rewrite Hlrev.
                     symmetry. eapply subst_env_swap_app with (n:=0);
                                 eauto with hints.
                     apply All_map. subst.
                     apply All_rev. unfold compose. simpl.
                     apply All_snd_combine with (p:=(iclosed_n 0) ∘ of_val_i).
                     unfold compose.
                     eapply All_expr_iclosed_of_val;try apply All_skipn;eauto.
               **** rewrite <- combine_rev by auto.
                    rewrite map_combine_snd_funprod.
                    eapply subst_env_iclosed_0;eauto with hints.
                    remember ((combine (rev (pVars pt)) (map of_val_i (rev (skipn _ l2))))) as l_comb.
                    assert (Hlen : #|l_comb| = #|pVars pt|).
                    { subst. rewrite combine_length. rewrite map_length.
                      repeat rewrite rev_length. rewrite skipn_length;lia.  }
                    rewrite <- Hlen.
                    eapply ty_expr_env_ok_subst_env with (k:=0).
                    assert (Hcomb : exprs (rev (combine (pVars pt) (skipn nparams l2))) = l_comb).
                    { subst. repeat rewrite map_rev.  rewrite combine_rev.
                      apply f_equal. now rewrite  map_combine_snd_funprod.
                      rewrite map_length. rewrite skipn_length;lia. }
                    rewrite <- Hcomb. rewrite <- map_app.
                    subst nparams. eapply eval_ty_expr_env_ok;eauto with hints.
                    rewrite app_length.
                    replace (#|rev (combine (pVars pt) (skipn #|l0| l2))|) with #|pVars pt| by
                        (rewrite rev_length, combine_length, skipn_length;lia).
                    replace #|ρ| with #|exprs ρ| by apply map_length. eauto with hints.

                    eapply closed_exprs;eauto.

                    eapply All_snd_combine with (p:=iclosed_n 0);eauto with hints.
                    apply All_map. apply All_rev.
                    eapply All_expr_iclosed_of_val;eauto using All_skipn.

                    rewrite combine_length. rewrite map_length.
                    repeat rewrite rev_length. rewrite skipn_length by lia.
                    replace (min #|pVars pt| (#|l2| - nparams)) with #|pVars pt| by lia.
                    eauto with hints.

               **** rewrite <- combine_rev by auto.
                    rewrite map_combine_snd_funprod.
                    remember ((combine (rev (pVars pt)) (map of_val_i (rev (skipn _ l2))))) as l_comb.
                    assert (Hlen : #|l_comb| = #|pVars pt|).
                    { subst. rewrite combine_length. rewrite map_length.
                      repeat rewrite rev_length. rewrite skipn_length;lia.  }
                    rewrite <- Hlen.
                    eapply ty_expr_env_ok_subst_env with (k:=0).
                    assert (Hcomb : exprs (rev (combine (pVars pt) (skipn nparams l2))) = l_comb).
                    { subst. repeat rewrite map_rev.  rewrite combine_rev.
                      apply f_equal. now rewrite  map_combine_snd_funprod.
                      rewrite map_length. rewrite skipn_length;lia. }
                    rewrite <- Hcomb. rewrite <- map_app.
                    subst nparams. eapply eval_ty_expr_env_ok;eauto with hints.
                    rewrite app_length.
                    replace (#|rev (combine (pVars pt) (skipn #|l0| l2))|) with #|pVars pt| by
                        (rewrite rev_length, combine_length, skipn_length;lia).
                    replace #|ρ| with #|exprs ρ| by apply map_length. eauto with hints.
                    eapply closed_exprs;eauto.
               **** rewrite map_length. subst nparams.
                    replace (#|rev (combine (pVars pt) (skipn #|l0| l2))|) with #|pVars pt| by
                        (rewrite rev_length, combine_length, skipn_length;lia).
                    eauto with hints.
               ****  apply All_map. subst.
                     apply All_rev. unfold compose. simpl.
                     apply All_snd_combine with (p:=(iclosed_n 0) ∘ of_val_i).
                     unfold compose.
                     eapply All_expr_iclosed_of_val;try apply All_skipn;eauto.
        ** specialize (lookup_ind_nth_error _ _ _ _ Hfind_i) as Hnth_eq.
           rewrite nth_error_map in Hnth_eq.
           rewrite nth_error_map in Hnth.
           destruct (nth_error _ _) eqn:Nci0;tryfalse.
    + (* eFix *)
      simpl in *.
      destruct (valid_env _ _ _);tryfalse.
      destruct (eval_type_i 0 ρ t) eqn:Ht0;tryfalse.
      destruct (eval_type_i 0 ρ t0) eqn:Ht1;tryfalse.
      cbn in *. inversion He.
      subst;simpl. repeat erewrite eval_type_i_subst_env by eauto.
      repeat rewrite subst_env_i_ty_closed_eq by eauto 8 with hints.
      constructor;auto.
    + (* eTy *)
      simpl in *.
      destruct (eval_type_i 0 ρ t) eqn:Ht0;tryfalse;simpl in *.
      inversion He;subst;clear He. simpl.
      erewrite eval_type_i_subst_env by eauto.
      eapply Wcvb_type_to_term_eval;eauto with hints.
      eapply closed_exprs;eauto.
Qed.

(** ** Soundness for closed epxressions (In the paper: Corollary 2)*)
Corollary expr_to_term_sound_closed (n : nat) Σ1 Σ2
          (e : expr) (v : val) :
  genv_ok Σ1 ->
  eval(n, Σ1, [], e) = Ok v ->
  iclosed_n 0 e = true ->
  Σ2 |- t⟦e⟧Σ1 ⇓ t⟦of_val_i v⟧Σ1.
Proof.
  intros.
  eapply expr_to_term_sound;eauto with hints.
  simpl. symmetry. eapply subst_env_i_empty.
Qed.

Definition terminates_expr Σ1 (e : expr) : Prop :=
  exists n v, eval(n, Σ1, [], e) = Ok v.

(** ** Adequacy for terminating programs (In the paper: Theorem 3) *)
Theorem adequacy_terminating Σ1 Σ2
        (e : expr) (t : term) :
  genv_ok Σ1 ->
  terminates_expr Σ1 e ->
  Σ2 |- t⟦e⟧Σ1 ⇓ t ->
  iclosed_n 0 e = true ->
  exists v, t = t⟦of_val_i v⟧Σ1.
Proof.
  intros Hgok Hterm Hcvb Hclosed.
  destruct Hterm as (n & v &?).
  assert (Hcbv1 : Σ2 |- t⟦ e ⟧Σ1 ⇓ t⟦ of_val_i v ⟧ Σ1)
    by (eapply expr_to_term_sound_closed;eauto).
  exists v. eapply PcbvCurr.eval_deterministic;eauto.
Qed.
