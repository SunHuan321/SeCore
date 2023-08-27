theory Ann_PiCore_RG_IFS
  imports Ann_PiCore_IFS Ann_PiCore_RG_Prop
begin

(*declare [[show_types]]*)
locale RG_InfoFlow = InfoFlow C0 step interference vpeq obs dome
  for C0  ::  "('l,'k,'s) pesconf"
  and step :: "('l,'k,'s,'d) action \<Rightarrow> (('l,'k,'s) pesconf \<times> ('l,'k,'s) pesconf) set"
  and interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
  and vpeq ::  "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<sim>_\<sim> _)" [70,69,70] 60)
  and obs ::  "'s \<Rightarrow> 'd \<Rightarrow> 'o" (infixl "\<guillemotright>"  55)
  and dome :: "'s \<Rightarrow> 'k \<Rightarrow> ('l,'k,'s) event \<Rightarrow> 'd"
  +
  fixes pesf :: "('l,'k,'s) rgformula_par"
  fixes s0 :: "'s"
  fixes x0 :: "('l,'k,'s) x"
  fixes evtrgfs :: "('l,'k,'s) event \<Rightarrow> 's rgformula option" (*a set of events and their rg conditions*)
  fixes spec_of_parsys :: "('l,'k,'s) paresys"
  assumes C0_ParSys: "C0 = (paresys_spec pesf, s0, x0)"
    and   spec_of_parsys: "spec_of_parsys = paresys_spec pesf"
    and   all_evts_are_basic: "\<forall>ef\<in>all_evts pesf. is_basicevt (E\<^sub>e ef)"
    and   parsys_sat_rg: "\<turnstile> pesf SAT [{s0}, {}, UNIV, UNIV]"
    and   evt_in_parsys_in_evtrgfs: "\<forall>erg\<in>all_evts pesf. the (evtrgfs (E\<^sub>e erg)) = snd erg" 
begin

definition locally_respect_event :: " bool"
  where "locally_respect_event \<equiv> \<forall>ef s k l x u i. ef\<in>all_evts pesf \<longrightarrow> l \<in> cpts_of_ev (E\<^sub>e ef) s x \<longrightarrow> 
        Suc i < length l \<longrightarrow>  (\<exists>t. l!i -et-t\<rightarrow> l!(Suc i)) \<longrightarrow> ann_preserves_e (l!i) \<longrightarrow> 
        ((dome (gets_e (l!i)) k (E\<^sub>e ef)) \<setminus>\<leadsto> u) \<longrightarrow> (gets_e (l!i)) \<sim>u\<sim> (gets_e (l!(Suc i)))"

definition locally_respect_event_guar :: "bool" where
  "locally_respect_event_guar \<equiv> \<forall>ef u s1 s2 k. ef\<in>all_evts pesf \<and> (s1,s2) \<in> Guar\<^sub>e ef \<longrightarrow> 
                                    ((dome s1 k (E\<^sub>e ef)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"


lemma cpt_is_run: 
  "\<forall>c C1 C2. c\<in>cpts_pes \<and> c!0 = C1 \<and> last c = C2 \<and> (\<forall>j. Suc j < length c \<longrightarrow> \<not>(c!j-pese\<rightarrow>c!Suc j)) 
            \<longrightarrow> (\<exists>as.  (C1,C2) \<in> run as \<and> Suc (length as) = length c \<and>
                       (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)) )"
  proof -
  {
    fix C2 c
    assume a0: "(c::('l,'k,'s) pesconfs)\<in>cpts_pes"
    then have "\<forall>C1. c!0 = C1 \<and> last c = C2 \<and> (\<forall>j. Suc j < length c \<longrightarrow> \<not>(c!j-pese\<rightarrow>c!Suc j)) 
            \<longrightarrow> (\<exists>as.  (C1,C2) \<in> run as \<and> Suc (length as) = length c \<and>
                       (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)) )"
      proof(induct c)
        case (CptsPesOne)
        show ?case by simp
      next
        case (CptsPesEnv)
        show ?case using nth_Cons_Suc pesetran.intros by force 
      next
        case (CptsPesComp pes1 s x ct pes2 t y xs)
        assume b0: "(pes1, s, x) -pes-ct\<rightarrow> (pes2, t, y)"
          and  b1: "(pes2, t, y) # xs \<in> cpts_pes"
          and  b2[rule_format]: "\<forall>C1. ((pes2, t, y) # xs) ! 0 = C1 \<and>
                       last ((pes2, t, y) # xs) = C2 \<and>
                       (\<forall>j. Suc j < length ((pes2, t, y) # xs) \<longrightarrow>
                            (((pes2, t, y) # xs) ! j, ((pes2, t, y) # xs) ! Suc j) \<notin> pesetran) \<longrightarrow>
                       (\<exists>as. (C1, C2) \<in> run as \<and>
                             Suc (length as) = length ((pes2, t, y) # xs) \<and>
                             (\<forall>j. Suc j < length ((pes2, t, y) # xs) \<longrightarrow>
                                  ((pes2, t, y) # xs) ! j -pes-actk (as ! j)\<rightarrow> ((pes2, t, y) # xs) ! Suc j))"
        then show ?case 
          proof -
          {
            fix C1
            assume c0: "((pes1, s, x) # (pes2, t, y) # xs) ! 0 = C1"
              and  c1: "last ((pes1, s, x) # (pes2, t, y) # xs) = C2"
              and  c2: "(\<forall>j. Suc j < length ((pes1, s, x) # (pes2, t, y) # xs) \<longrightarrow>
              (((pes1, s, x) # (pes2, t, y) # xs) ! j, ((pes1, s, x) # (pes2, t, y) # xs) ! Suc j) \<notin> pesetran)"
            then have c3: "C1 = (pes1, s, x)" by simp
            let ?C1 = "(pes2, t, y)"
            have "((pes2, t, y) # xs) ! 0 = ?C1" by simp
            moreover
            from c1 have "last ((pes2, t, y) # xs) = C2" by simp
            moreover
            from c2 have "\<forall>j. Suc j < length ((pes2, t, y) # xs) \<longrightarrow>
                            (((pes2, t, y) # xs) ! j, ((pes2, t, y) # xs) ! Suc j) \<notin> pesetran"
               using Suc_mono length_Cons nth_Cons_Suc by auto 
            ultimately have "\<exists>as. (?C1, C2) \<in> run as \<and>
                             Suc (length as) = length ((pes2, t, y) # xs) \<and>
                             (\<forall>j. Suc j < length ((pes2, t, y) # xs) \<longrightarrow>
                                  ((pes2, t, y) # xs) ! j -pes-actk (as ! j)\<rightarrow> ((pes2, t, y) # xs) ! Suc j)"
              using b2[of ?C1] by simp
            then obtain as where c4: "(?C1, C2) \<in> run as \<and>
                             Suc (length as) = length ((pes2, t, y) # xs) \<and>
                             (\<forall>j. Suc j < length ((pes2, t, y) # xs) \<longrightarrow>
                                  ((pes2, t, y) # xs) ! j -pes-actk (as ! j)\<rightarrow> ((pes2, t, y) # xs) ! Suc j)"
              by auto
            obtain tr and k where "ct = tr\<sharp>k" using get_actk_def
              by (metis actk.cases) 
            
            then have "\<exists>as. (C1, C2) \<in> run as \<and>
               Suc (length as) = length ((pes1, s, x) # (pes2, t, y) # xs) \<and>
               (\<forall>j. Suc j < length ((pes1, s, x) # (pes2, t, y) # xs) \<longrightarrow>
                    ((pes1, s, x) # (pes2, t, y) # xs) !
                    j -pes-actk (as ! j)\<rightarrow> ((pes1, s, x) # (pes2, t, y) # xs) ! Suc j)"
              proof(induct tr)
                case (Cmd cmd)
                assume d0: "ct = Cmd cmd\<sharp>k"
                obtain a1 where d1: "actk (a1::('l,'k,'s,'d) action) = ((Cmd cmd)\<sharp>k) \<and> eventof a1 = (getx C1) k 
                                          \<and> dome (gets C1) k (eventof a1) = domain a1"
                  using action.select_convs(1) by fastforce 
                then obtain as1 where d2: "as1 = a1#as" by simp
                with d0 d1 b0 c3 c4 have "(C1, C2) \<in> run as1" using run_def step_def
                  using case_prod_conv mem_Collect_eq run_Cons by fastforce
                moreover
                from d2 c4 have "Suc (length as1) = length ((pes1, s, x) # (pes2, t, y) # xs)"
                  by auto
                moreover
                from c4 b0 d0 d1 d2 have "\<forall>j. Suc j < length ((pes1, s, x) # (pes2, t, y) # xs) \<longrightarrow>
                    ((pes1, s, x) # (pes2, t, y) # xs) !
                    j -pes-actk (as1 ! j)\<rightarrow> ((pes1, s, x) # (pes2, t, y) # xs) ! Suc j"
                  using c3 calculation(2) diff_Suc_1 length_Suc_conv less_Suc_eq_0_disj 
                    nat.discI not0_implies_Suc nth_Cons' by auto 
                ultimately show ?case by auto
              next
                case (EvtEnt ev)
                assume d0: "ct = EvtEnt ev\<sharp>k"
                obtain a1 where d1: "actk (a1::('l,'k,'s,'d) action) = ((EvtEnt ev)\<sharp>k) \<and> eventof a1 = ev 
                                          \<and> dome (gets C1) k ev = domain a1"
                  using action.select_convs(1) by fastforce 
                then obtain as1 where d2: "as1 = a1#as" by simp
                with d0 d1 b0 c3 c4 have "(C1, C2) \<in> run as1" using run_def step_def
                  using case_prod_conv mem_Collect_eq run_Cons by fastforce
                moreover
                from d2 c4 have "Suc (length as1) = length ((pes1, s, x) # (pes2, t, y) # xs)"
                  by auto
                moreover
                from c4 b0 d0 d1 d2 have "\<forall>j. Suc j < length ((pes1, s, x) # (pes2, t, y) # xs) \<longrightarrow>
                    ((pes1, s, x) # (pes2, t, y) # xs) !
                    j -pes-actk (as1 ! j)\<rightarrow> ((pes1, s, x) # (pes2, t, y) # xs) ! Suc j"
                  using c3 calculation(2) diff_Suc_1 length_Suc_conv less_Suc_eq_0_disj 
                    nat.discI not0_implies_Suc nth_Cons' by auto 
                ultimately show ?case by auto
              qed
          }
          then show ?thesis by auto
          qed
      qed
  }
  then show ?thesis by auto
  qed

lemma run_is_cpt: "\<forall>C1 C2 as. (C1,C2) \<in> run as \<longrightarrow> 
            (\<exists>c. c\<in>cpts_pes \<and> c!0 = C1 \<and> last c = C2 \<and> Suc (length as) = length c \<and>
                 (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)) )" 
  proof -
  {
    fix C2 as 
    have "\<forall>C1. (C1,C2) \<in> run as \<longrightarrow> (\<exists>c. c\<in>cpts_pes \<and> c!0 = C1 \<and> last c = C2 \<and> Suc (length as) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)))"
      proof(induct as)
        case Nil
        show ?case
          proof -
          {
            fix C1
            assume a0: "(C1, C2) \<in> run []"
            then have b1: "C1 = C2" by (simp add:run_def)
            then have "[C1]\<in>cpts_pes" by (metis cpts_pes.CptsPesOne prod_cases3) 
            moreover
            have "[C1]!0 = C1" by simp
            moreover
            from b1 have "last [C1] = C2" by simp
            ultimately have "(\<exists>c. c \<in> cpts_pes \<and> c ! 0 = C1 \<and> last c = C2 \<and> Suc (length []) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk ([]!j))\<rightarrow>c!Suc j)))" by auto
          }
          then show ?thesis by blast
          qed
      next
        case (Cons b bs)
        assume a0: "\<forall>C1. (C1, C2) \<in> run bs \<longrightarrow> (\<exists>c. c \<in> cpts_pes \<and> c ! 0 = C1 \<and> last c = C2 \<and> Suc (length bs) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (bs!j))\<rightarrow>c!Suc j)))"
        then show ?case
          proof -
          {
            fix C1
            assume b0: "(C1, C2) \<in> run (b # bs)"
            then have "\<exists>R. (C1,R) \<in> step b \<and> (R,C2) \<in> run bs"
              by (simp add:run_def)
            then obtain R where b1: "(C1,R) \<in> step b \<and> (R,C2) \<in> run bs" by auto
            with a0 have "\<exists>c. c \<in> cpts_pes \<and> c ! 0 = R \<and> last c = C2 \<and> Suc (length bs) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (bs!j))\<rightarrow>c!Suc j))" by blast
            then obtain c where b2: "c \<in> cpts_pes \<and> c ! 0 = R \<and> last c = C2 \<and> Suc (length bs) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (bs!j))\<rightarrow>c!Suc j))" by auto
            then obtain c' where b3: "c=R#c'"
              by (metis cpts_pes_not_empty hd_conv_nth list.exhaust list.sel(1)) 
            from b1 have b4: "C1 -pes-(actk b)\<rightarrow> R" by (simp add:step_def)
            with b2 b3 have b5: "(C1#c) \<in> cpts_pes" 
              using pestran_cpts_pes by meson 
            from b2 have b6: "(C1#c)!0 = C1 \<and> last (C1#c) = C2 \<and> Suc (length (b#bs)) = length (C1#c)" by auto
            with b2 b4 have "\<forall>j. Suc j < length (C1#c) \<longrightarrow> ((C1#c)!j-pes-(actk ((b # bs)!j))\<rightarrow>(C1#c)!Suc j)"
              by (smt Suc_inject Suc_less_eq2 Suc_pred length_Cons neq0_conv nth_Cons' nth_Cons_Suc)
            with b5 b6 have "\<exists>c. c \<in> cpts_pes \<and> Suc (length (b # bs)) = length c \<and>
              c ! 0 = C1 \<and> last c = C2 \<and> (\<forall>j. Suc j < length c \<longrightarrow> c ! j -pes-actk ((b # bs) ! j)\<rightarrow> c ! Suc j)" 
              by auto
          }
          then show ?thesis by blast
          qed
      qed
  }
  then show ?thesis by auto
  qed


lemma reachable_impl_cpts: "reachable C1 C2 \<Longrightarrow> \<exists>c. c\<in>cpts_pes \<and> c!0 = C1 \<and> last c = C2" 
  proof -
    assume "reachable C1 C2"
    then have "\<exists>as. (C1,C2) \<in> run as" by (simp add:reachable_def)
    then obtain as where a1: "(C1,C2) \<in> run as" by auto
    then show ?thesis using run_is_cpt by blast
  qed

lemma reachable0_impl_cpts: "reachable0 C \<Longrightarrow> \<exists>c. c\<in>cpts_pes \<and> c!0 = C0 \<and> last c = C"
  using reachable_impl_cpts reachable0_def by simp


lemma rg_lr_imp_lr: "locally_respect_event \<Longrightarrow> locally_respect"
  proof -
    assume p0: "locally_respect_event"
    then have p1: " \<forall>ef s k l x u i. ef\<in>all_evts pesf \<longrightarrow> l \<in> cpts_of_ev (E\<^sub>e ef) s x \<longrightarrow> 
        Suc i < length l \<longrightarrow>  (\<exists>t. l!i -et-t\<rightarrow> l!(Suc i)) \<longrightarrow> ann_preserves_e (l!i) \<longrightarrow> 
        ((dome (gets_e (l!i)) k (E\<^sub>e ef)) \<setminus>\<leadsto> u) \<longrightarrow> (gets_e (l!i)) \<sim>u\<sim> (gets_e (l!(Suc i)))"
      by (simp add:locally_respect_event_def)
    show ?thesis
      proof -
      {
        fix a u C
        assume a0: "reachable0 C"
          and  a1: "(domain (a::('l,'k,'s,'d) action)) \<setminus>\<leadsto> u"
        have "\<forall> C'. (C'\<in>nextc C a) \<longrightarrow> (C \<sim>.u.\<sim> C')"
          proof -
          {
            fix C'
            assume b0: "C'\<in>nextc C a"
            then have b1: "(C,C')\<in>step a" by (simp add:nextc_def)
            then have b2: "(C -pes-(actk a)\<rightarrow> C') \<and>
                            ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C) k e = domain a) \<or>
                             (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C) k \<and> dome (gets C) k (eventof a) = domain a))"
              by (simp add:step_def)
            obtain act_k and e and d where b3: "a = \<lparr>actk = act_k,eventof = e, domain=d\<rparr>"
              using action.cases by blast 
            with b2 have b4: "(C -pes-act_k\<rightarrow> C') \<and> 
                              ((\<exists>e k. act_k = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C) k e = domain a) \<or>
                             (\<exists>c k. act_k = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C) k \<and> dome (gets C) k (eventof a) = domain a))"
              by simp
            obtain act and k where b5: "act_k = act\<sharp>k"
              by (metis actk.cases get_actk_def) 
            obtain pes1 and s1 and x1 where b6: "C = (pes1,s1,x1)" using prod_cases3 by blast 
            obtain pes2 and s2 and x2 where b7: "C' = (pes2,s2,x2)" using prod_cases3 by blast
            from b4 b5 b6 b7 have "\<exists>es'. ((pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es', s2, x2)) \<and> pes2 = pes1(k:=es')" 
              using pestran_estran by force
            then obtain es' where b8: "((pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es', s2, x2)) \<and> pes2 = pes1(k:=es')" by auto

            from b5 have "C \<sim>.u.\<sim> C'"
              proof(induct act)
                case (Cmd x) 
                assume c0: "act_k = Cmd x\<sharp>k"
                from a0 have "\<exists>as. (C0,C) \<in> run as" by (simp add:reachable0_def reachable_def)
                then obtain as where "(C0,C) \<in> run as" by auto
                then have "(\<exists>c. c\<in>cpts_pes \<and> c!0 = C0 \<and> last c = C \<and> Suc (length as) = length c \<and>
                              (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)) )"
                  using run_is_cpt by blast
                then obtain c where c1: "c\<in>cpts_pes \<and> c!0 = C0 \<and> last c = C \<and> Suc (length as) = length c \<and>
                              (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j))" by auto
                with b1 have c2: "c@[C']\<in>cpts_pes" using cpts_pes_onemore step_def
                  by (metis (no_types, lifting) b4 cpts_pes_not_empty last_conv_nth)
                with c1 have c3: "c @ [C'] \<in> cpts_of_pes (paresys_spec pesf) s0 x0" 
                  using cpts_of_pes_def[of "paresys_spec pesf" s0 x0] C0_ParSys
                  by (smt cpts_pes_not_empty length_greater_0_conv mem_Collect_eq nth_append) 
                moreover
                from c1 have c4: "(c @ [C']) ! (length (c @ [C']) - 2) = C"
                  by (metis (no_types, hide_lams) Suc_1 cpts_pes_not_empty diff_Suc_Suc 
                      hd_Cons_tl last_conv_nth length_Cons length_append_singleton length_tl lessI nth_append)
                moreover
                have c5: "(c @ [C']) ! (length (c @ [C']) - 1) = C'" by simp
                moreover
                from b1 c1 have c50: "\<forall>j. Suc j < length (c @ [C']) \<longrightarrow> 
                        ((c @ [C'])!j-pes-(actk ((as@[a])!j))\<rightarrow>(c @ [C'])!Suc j)"
                   by (smt Suc_1 Suc_lessI Suc_less_eq action.simps(1) b3 b4 c4 
                     diff_Suc_1 diff_Suc_Suc length_append_singleton nth_append nth_append_length) 


end