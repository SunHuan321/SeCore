theory Ann_PiCore_RG_IFS 
  imports Ann_PiCore_IFS Ann_PiCore_RG_Prop Ann_PiCore_Hoare
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

lemma K1: "l \<in> cpts_of_pes (paresys_spec pesf) s0 x0 \<Longrightarrow> l \<in> preserves_pes"
  sorry


definition seteq :: "'s set \<Rightarrow> 'd \<Rightarrow> 's set \<Rightarrow> bool" ("(_ \<approx>_\<approx> _)" [70,71] 60)
   where "seteq P u Q \<equiv> \<forall>s t. s \<in> P \<and> t \<in> Q \<longrightarrow> s \<sim>u\<sim> t"

inductive sc_p :: "'s ann_prog \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool"
    ("\<turnstile>\<^sub>s\<^sub>c _ sat\<^sub>p _" [60] 45)
where
  Basic: "\<lbrakk>\<forall>s1 s2 k u. s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> (dome s1 k ev) \<leadsto> u \<and> s1 \<sim>(dome s1 k ev)\<sim> s2 
           \<longrightarrow> f s1 \<sim>u\<sim> f s2\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnBasic r f sat\<^sub>p ev"
| Seq: "\<lbrakk> \<turnstile>\<^sub>s\<^sub>c P sat\<^sub>p ev;  \<turnstile>\<^sub>s\<^sub>c Q sat\<^sub>p ev\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnSeq P Q sat\<^sub>p ev"
| Cond: "\<lbrakk> \<turnstile>\<^sub>s\<^sub>c P1 sat\<^sub>p ev;  \<turnstile>\<^sub>s\<^sub>c P2 sat\<^sub>p ev \<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnCond r b P1 P2 sat\<^sub>p ev"
| While: "\<lbrakk> \<turnstile>\<^sub>s\<^sub>c P sat\<^sub>p ev \<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnWhile r b P sat\<^sub>p ev"
| Await: "\<lbrakk>\<forall>s1 s2 k u. s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> (dome s1 k ev) \<leadsto> u \<and> s1 \<sim>(dome s1 k ev)\<sim> s2 \<and>
           \<turnstile> P sat\<^sub>p [{s1}, {}, UNIV, Q1] \<and>  \<turnstile> P sat\<^sub>p [{s2}, {}, UNIV, Q2] \<longrightarrow> 
           (\<forall>t1 t2. t1 \<in> Q1 \<and> t2 \<in> Q2 \<longrightarrow> t1 \<sim>u\<sim> t2)\<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnAwait r b P sat\<^sub>p ev"
| Nondt: "\<lbrakk>\<forall>s1 s2 k u.  s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> (dome s1 k ev) \<leadsto> u \<and> s1 \<sim>(dome s1 k ev)\<sim> s2 \<longrightarrow>
           (\<forall>t1 t2. (s1, t1) \<in> f \<and> (s2, t2) \<in> f \<longrightarrow> t1 \<sim>u\<sim> t2) \<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnNondt r f sat\<^sub>p ev"

lemma "(None, s) -c\<rightarrow> (P, t) \<Longrightarrow> False"
  apply (erule ptran.cases, simp_all)
  done

definition step_consistent_p :: "'s ann_prog option set \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool"
  where "step_consistent_p \<S> ev \<equiv> \<forall>P P1' P2' s1 s2  s1' s2' k u. P \<in> \<S> \<longrightarrow> 
          (ann_preserves_p P s1 \<and> ann_preserves_p P s2 \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1 k ev) \<leadsto> u 
          \<longrightarrow> s1 \<sim>(dome s1 k ev)\<sim> s2) \<and> (P, s1) -c\<rightarrow> (P1', s1') \<and> (P, s2) -c\<rightarrow> (P2', s2') 
          \<longrightarrow> s1' \<sim>u\<sim> s2') \<and> (ann_preserves_p P s1 \<and> (P, s1) -c\<rightarrow> (P1', s1') \<longrightarrow> P1' \<in> \<S>)"

lemma " \<forall>s1 s2 k u. s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> dome s1 k ev \<leadsto> u \<and> s1 \<sim>dome s1 k ev\<sim> s2 \<longrightarrow> f s1 \<sim>u\<sim> f s2 \<Longrightarrow> \<exists>\<S>. Some (AnnBasic r f) \<in> \<S> \<and> step_consistent_p \<S> ev"
  sorry















lemma sc_p_sound : " \<turnstile>\<^sub>s\<^sub>c P sat\<^sub>p ev \<Longrightarrow> \<exists>\<S>. Some P \<in> \<S> \<and> step_consistent_p \<S> ev"
  sorry

definition locally_respect_event :: "bool" where
  "locally_respect_event \<equiv> \<forall>ef u s1 s2 k. ef\<in>all_evts pesf \<and> (s1,s2) \<in> Guar\<^sub>e ef \<longrightarrow> 
                                    ((dome s1 k (E\<^sub>e ef)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"


definition step_consistent_events :: "('l, 'k, 's) event set \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool" where
  "step_consistent_events \<S> ev \<equiv> \<forall>e e1' e2' s1 s2 x1 x2 s1' s2' x1' x2' k u t. e \<in> \<S> \<longrightarrow> 
  (ann_preserves_e e s1 \<and> ann_preserves_e e s2 \<and> s1 \<sim>u\<sim> s2 \<and> 
  ((dome s1 k ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 k ev)\<sim> s2) \<and> 
  (e, s1, x1) -et-t\<rightarrow> (e1', s1', x1') \<and> (e, s2, x2) -et-t\<rightarrow> (e2', s2', x2') \<longrightarrow>
   s1' \<sim>u\<sim> s2') \<and> (ann_preserves_e e s1 \<and> (e, s1, x1) -et-t\<rightarrow> (e1', s1', x1') \<longrightarrow> e1' \<in> \<S>)"

definition step_consistent_event :: "bool" where
  "step_consistent_event \<equiv> \<forall>ef. ef\<in>all_evts pesf  \<longrightarrow> (\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> step_consistent_events \<S> (E\<^sub>e ef))"


lemma consistent_next_event : "\<lbrakk>getspc_e c \<in> \<S> ; step_consistent_events \<S> ev; ann_preserves_e (getspc_e c) (gets_e c); 
                               \<exists>t. c -et-t\<rightarrow> c'\<rbrakk>  \<Longrightarrow> getspc_e c' \<in> \<S>"
  apply (case_tac "c", case_tac c', simp add: step_consistent_events_def getspc_e_def gets_e_def)
  by blast

lemma consistent_next_state : "\<lbrakk>e \<in> \<S> \<and> step_consistent_events \<S> ev; ann_preserves_e e s1; ann_preserves_e e s2;
                                s1 \<sim>u\<sim> s2; (dome s1 k ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 k ev)\<sim> s2; 
                                (e, s1, x1) -et-t\<rightarrow> (e1', s1', x1'); (e, s2, x2) -et-t\<rightarrow> (e2', s2', x2')\<rbrakk> 
                              \<Longrightarrow> s1' \<sim>u\<sim> s2'"
  apply (simp add: step_consistent_events_def, clarify)
  by blast

lemma step_consistent_forall : "\<lbrakk>e \<in> \<S> ; step_consistent_events \<S> ev; el \<in> cpts_ev; getspc_e (el!0) = e; el \<in> preserves_e;
        i < length el\<rbrakk> \<Longrightarrow> getspc_e (el ! i) \<in> \<S>"
  apply (induct i, simp add: cpts_of_ev_def getspc_e_def)
  apply (case_tac "getspc_e (el ! i) = getspc_e (el ! Suc i)", simp)
  apply (rule_tac c = "el ! i" in consistent_next_event, simp_all)
  apply (simp add: preserves_e_def)
  using cpts_of_ev_def notran_confeqi by fastforce




lemma K3: "\<lbrakk>ev = BasicEvent e;  \<turnstile>\<^sub>s\<^sub>c body e sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. ev \<in> \<S> \<and> step_consistent_events \<S> ev"
  sorry



(*
definition locally_respect :: "bool" where
  "locally_respect \<equiv> \<forall>a u C. (reachable0 C) \<longrightarrow> ((domain a) \<setminus>\<leadsto> u) \<longrightarrow> 
                              (\<forall> C'. (C'\<in>nextc C a) \<longrightarrow> (C \<sim>.u.\<sim> C'))"                    

definition step_consistent :: "bool" where
  "step_consistent \<equiv> \<forall>a u C1 C2. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow>  (C1 \<sim>.u.\<sim> C2) 
                         \<and> ( ((domain a) \<leadsto> u) \<longrightarrow> (C1 \<sim>.(domain a).\<sim> C2) ) \<longrightarrow> 
                         (\<forall> C1' C2'. (C1'\<in>nextc C1 a) \<and> (C2'\<in>nextc C2 a) \<longrightarrow> (C1' \<sim>.u.\<sim> C2'))"
*)


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




lemma rg_sc_imp_sc: "step_consistent_event \<Longrightarrow> step_consistent"
proof-
  assume p0: "step_consistent_event"
  then have p1: "\<forall>ef. ef\<in>all_evts pesf  \<longrightarrow> (\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> step_consistent_events \<S> (E\<^sub>e ef))"
    by (simp add: step_consistent_event_def)
  show ?thesis
  proof-
    {
      fix a u C1 C2
      assume a0: "(reachable0 C1) \<and> (reachable0 C2)"
      and    a1: "(C1 \<sim>.u.\<sim> C2) \<and> (((domain (a::('l,'k,'s,'d) action)) \<leadsto> u) \<longrightarrow> (C1 \<sim>.(domain a).\<sim> C2))"
      have "\<forall>C1' C2'. (C1'\<in>nextc C1 a) \<and> (C2'\<in>nextc C2 a) \<longrightarrow> (C1' \<sim>.u.\<sim> C2')"
      proof-
        {
          fix C1' C2'
          assume b0: "(C1'\<in>nextc C1 a) \<and> (C2'\<in>nextc C2 a)"
          obtain act_k and e and d where b3: "a = \<lparr>actk = act_k,eventof = e, domain=d\<rparr>"
            using action.cases by blast 
          obtain act and k where b5: "act_k = act\<sharp>k"
            by (metis actk.cases get_actk_def)

          from b0 have b1: "(C1, C1') \<in> step a" by (simp add: nextc_def)
          then have b2: "(C1 -pes-(actk a)\<rightarrow> C1') \<and>
                         ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C1) k e = domain a) \<or>
                         (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C1) k \<and> dome (gets C1) k (eventof a) = domain a))"
            by (simp add: step_def)
          with b3 have b4: "(C1 -pes-act_k\<rightarrow> C1') \<and> 
                            ((\<exists>e k. act_k = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C1) k e = domain a) \<or>
                            (\<exists>c k. act_k = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C1) k \<and> dome (gets C1) k (eventof a) = domain a))"
            by simp

          from b0 have b6: "(C2,C2')\<in>step a" by (simp add:nextc_def)
          then have "(C2 -pes-(actk a)\<rightarrow> C2') \<and>
                     ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C2) k e = domain a) \<or>
                     (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C2) k \<and> dome (gets C2) k (eventof a) = domain a))"
            by (simp add:step_def)
          with b3 have b7: "(C2 -pes-act_k\<rightarrow> C2') \<and> 
                            ((\<exists>e k. act_k = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C2) k e = domain a) \<or>
                            (\<exists>c k. act_k = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C2) k \<and> dome (gets C2) k (eventof a) = domain a))"
            by simp
          obtain pes1 and s1 and x1 where b8: "C1 = (pes1,s1,x1)" using prod_cases3 by blast 
          obtain pes1' and s1' and x1' where b9: "C1' = (pes1',s1',x1')" using prod_cases3 by blast
          obtain pes2 and s2 and x2 where b10: "C2 = (pes2,s2,x2)" using prod_cases3 by blast
          obtain pes2' and s2' and x2' where b11: "C2' = (pes2',s2',x2')" using prod_cases3 by blast
          from b4 b5 b8 b9 have "\<exists>es'. ((pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es', s1', x1')) \<and> pes1' = pes1(k:=es')" 
            using pestran_estran [of pes1 s1 x1 act k pes1' s1' x1'] by simp
          then obtain es1' where b12: "((pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es1', s1', x1')) \<and> pes1' = pes1(k:=es1')" by auto
          from b5 b7 b10 b11 have "\<exists>es'. ((pes2 k, s2, x2) -es-(act\<sharp>k)\<rightarrow> (es', s2', x2')) \<and> pes2' = pes2(k:=es')" 
            using pestran_estran [of pes2 s2 x2 act k pes2' s2' x2'] by simp
          then obtain es2' where b13: "((pes2 k, s2, x2) -es-(act\<sharp>k)\<rightarrow> (es2', s2', x2')) \<and> pes2' = pes2(k:=es2')"
            by auto

          from b5 have "C1' \<sim>.u.\<sim> C2'"
          proof(induct act)
            case (Cmd c)
            assume c0: "act_k = Cmd c\<sharp>k"

            from a0 have "\<exists>as. (C0, C1) \<in> run as" by (simp add: reachable0_def reachable_def)
            then obtain as1 where "(C0, C1) \<in> run as1" by auto
            then have "(\<exists>c. c\<in>cpts_pes \<and> c!0 = C0 \<and> last c = C1 \<and> Suc (length as1) = length c \<and>
                              (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as1!j))\<rightarrow>c!Suc j)) )"
              using run_is_cpt by blast
            then obtain c1 where c1: "c1\<in>cpts_pes \<and> c1!0 = C0 \<and> last c1 = C1 \<and> Suc (length as1) = length c1 \<and>
                (\<forall>j. Suc j < length c1 \<longrightarrow> (c1!j-pes-(actk (as1!j))\<rightarrow>c1!Suc j))" by auto
            with b1 have c2: "c1@[C1']\<in>cpts_pes" using cpts_pes_onemore step_def
              by (metis (no_types, lifting) b4 cpts_pes_not_empty last_conv_nth)
            with c1 have c3: "c1 @ [C1'] \<in> cpts_of_pes (paresys_spec pesf) s0 x0" 
              using cpts_of_pes_def[of "paresys_spec pesf" s0 x0] C0_ParSys
              by (smt cpts_pes_not_empty length_greater_0_conv mem_Collect_eq nth_append)
            moreover
            from c1 have c4: "(c1 @ [C1']) ! (length (c1 @ [C1']) - 2) = C1"
              by (metis Suc_1 diff_Suc_1 diff_Suc_Suc last_conv_nth length_0_conv length_append_singleton 
                  lessI nat.distinct(1) nth_append)
              
            moreover
            have c5: "(c1 @ [C1']) ! (length (c1 @ [C1']) - 1) = C1'" by simp
            moreover
            from b1 c1 have c50: "\<forall>j. Suc j < length (c1 @ [C1']) \<longrightarrow> 
             ((c1 @ [C1'])!j-pes-(actk ((as1@[a])!j))\<rightarrow>(c1 @ [C1'])!Suc j)"
              by (smt Suc_1 Suc_lessI Suc_less_eq action.simps(1) b3 b4 c4 diff_Suc_1 
                  diff_Suc_Suc length_append_singleton nth_append nth_append_length) 

            from a0 have "\<exists>as. (C0,C2) \<in> run as" by (simp add:reachable0_def reachable_def)
            then obtain as2 where "(C0,C2) \<in> run as2" by auto
            then have "(\<exists>c. c\<in>cpts_pes \<and> c!0 = C0 \<and> last c = C2 \<and> Suc (length as2) = length c \<and>
                        (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as2!j))\<rightarrow>c!Suc j)) )"
              using run_is_cpt by blast
            then obtain c2 where c7: "c2\<in>cpts_pes \<and> c2!0 = C0 \<and> last c2 = C2 \<and> Suc (length as2) = length c2 \<and>
                     (\<forall>j. Suc j < length c2 \<longrightarrow> (c2!j-pes-(actk (as2!j))\<rightarrow>c2!Suc j))" by auto
            with b6 have c8: "c2@[C2']\<in>cpts_pes" using cpts_pes_onemore step_def
              by (metis (no_types, lifting) b7 cpts_pes_not_empty last_conv_nth)
            with c7 have c9: "c2 @ [C2'] \<in> cpts_of_pes (paresys_spec pesf) s0 x0" 
              using cpts_of_pes_def[of "paresys_spec pesf" s0 x0] C0_ParSys
              by (smt cpts_pes_not_empty length_greater_0_conv mem_Collect_eq nth_append) 
            moreover
            from c7 have c10: "(c2 @ [C2']) ! (length (c2 @ [C2']) - 2) = C2"
              by (metis Suc_1 diff_Suc_1 diff_Suc_Suc last_conv_nth length_0_conv length_append_singleton 
                  lessI nat.distinct(1) nth_append)
            moreover
            have c11: "(c2 @ [C2']) ! (length (c2 @ [C2']) - 1) = C2'" by simp
            moreover
            from b1 c7 have c12: "\<forall>j. Suc j < length (c2 @ [C2']) \<longrightarrow> 
              ((c2 @ [C2'])!j-pes-(actk ((as2@[a])!j))\<rightarrow>(c2 @ [C2'])!Suc j)"
              by (smt Suc_1 Suc_lessI Suc_less_eq action.simps(1) b3 b7 c10 diff_Suc_1 
                 diff_Suc_Suc length_append_singleton nth_append nth_append_length) 


            from c3 c50 have c51: "\<forall>k i. Suc i < length (c1 @ [C1']) \<longrightarrow>
                      (\<exists>ca. (c1 @ [C1']) ! i -pes-Cmd ca\<sharp>k\<rightarrow> (c1 @ [C1']) ! Suc i) \<longrightarrow>
                      (\<exists>ef\<in>all_evts pesf. getx ((c1 @ [C1']) ! i) k = fst ef) " 
              using all_evts_are_basic cur_evt_in_specevts [of "c1@[C1']" pesf] by (metis E\<^sub>e_def)
            moreover
            from b1 b3 c0 have c52: "C1-pes-Cmd c\<sharp>k\<rightarrow>C1'" using step_def by simp
            from c9 c12 have c61: "\<forall>k i. Suc i < length (c2 @ [C2']) \<longrightarrow>
                      (\<exists>ca. (c2 @ [C2']) ! i -pes-Cmd ca\<sharp>k\<rightarrow> (c2 @ [C2']) ! Suc i) \<longrightarrow>
                      (\<exists>ef\<in>all_evts pesf. getx ((c2 @ [C2']) ! i) k = fst ef) " 
              using all_evts_are_basic cur_evt_in_specevts [of "c2@[C2']" pesf] by (metis E\<^sub>e_def)
            moreover
            from b6 b3 c0 have c62: "C2-pes-Cmd c\<sharp>k\<rightarrow>C2'" using step_def by simp

            ultimately have "(\<exists>ef\<in>all_evts pesf. getx C1 k = fst ef)"
              using c1 c4 c5
            proof-
              have f1: "\<forall>k n. \<not> Suc n < length (c1 @ [C1']) \<or>
                        (\<forall>ca. ((c1 @ [C1']) ! n, Cmd ca\<sharp>k, (c1 @ [C1']) ! Suc n) \<notin> pestran) \<or> 
                        (\<exists>p. p \<in> all_evts pesf \<and> fst p = getx ((c1 @ [C1']) ! n) k)"
                by (metis c51)
              from c1 have f2: "\<forall>ps. c1 ! length as1 = (c1 @ ps) ! length as1" 
                by (metis (no_types) c1 lessI nth_append)
              have "c1 ! length as1 = C1"
                by (metis (no_types) append_Nil c1 diff_Suc_1 id_take_nth_drop last_length 
                    length_Cons take_0 zero_less_Suc)
              then show ?thesis
                using f2 f1 by (metis c52 c1 c5 diff_Suc_1 length_append_singleton lessI)
            qed

            then obtain ef where c12: "ef\<in>all_evts pesf \<and> getx C1 k = E\<^sub>e ef" 
              by (metis E\<^sub>e_def)
            from c0 have c12_1: "\<not>(\<exists>e k. act_k = EvtEnt e\<sharp>k)"
              by (simp add: get_actk_def) 
            with b3 b4 c0 have c13: "\<exists>x k. act_k = Cmd c\<sharp>k \<and> eventof a = getx C1 k \<and> dome (gets C1) k (eventof a) = domain a"
              by (metis actk.iffs get_actk_def)
            with a1 b3 c0 have c14: "eventof a = getx C1 k \<and> dome (gets C1) k (eventof a) = domain a"
              by (metis actk.ext_inject get_actk_def)

            have c15: "eventof a = (getx C2) k \<and> dome (gets C2) k (eventof a) = domain a"
            proof -
              from b7 c12_1 have "\<exists>c k. act_k = Cmd c\<sharp>k \<and> eventof a = getx C2 k 
                    \<and> dome (gets C2) k (eventof a) = domain a" by auto
              then obtain c' and k' where "act_k = Cmd c'\<sharp>k' \<and> eventof a = getx C2 k' 
                    \<and> dome (gets C2) k' (eventof a) = domain a" by auto
              with c0 c14 show ?thesis by (metis actk.iffs get_actk_def)
            qed

            let ?pes = "paresys_spec pesf"
            let ?i = "length (c1 @ [C1']) - 2"
            have "\<exists>\<S>. AnonyEvent c \<in> \<S> \<and> step_consistent_events \<S> (E\<^sub>e ef)"
            proof-
              {
                have "\<exists>el j.  getspc_e (el!0) = getx C1 k \<and> j < length el \<and> 
                     el!j = rm_evtsys1 ((getspc C1 k), gets C1, getx C1) \<and> el \<in> cpts_ev \<and> el \<in> preserves_e"
                  using act_cptpes_sat_e_sim[rule_format, of pesf "{s0}" UNIV s0 evtrgfs "c1 @ [C1']"
                        x0 ?i k] parsys_sat_rg all_evts_are_basic evt_in_parsys_in_evtrgfs c1 c3 c4 c5 c50 c52
                  by (smt One_nat_def Suc_1 Suc_diff_Suc Suc_less_eq diff_less insertI1 
                      length_append_singleton zero_less_Suc)
                then obtain el and j where e0: "getspc_e (el!0) = getx C1 k \<and> j < length el \<and> 
                     el!j = rm_evtsys1 ((getspc C1 k), gets C1, getx C1) \<and> el \<in> cpts_ev \<and> el \<in> preserves_e"
                  by auto
                with c12 have c120: "getspc_e (el!0) = E\<^sub>e ef \<and> j < length el \<and> el!j = rm_evtsys1 ((getspc C1 k), gets C1, getx C1) 
                               \<and> el \<in> cpts_ev \<and> el \<in> preserves_e" by simp
                with c12 p1 have "\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> step_consistent_events \<S> (E\<^sub>e ef)" by blast
                then obtain \<S> where e1: "(E\<^sub>e ef) \<in> \<S> \<and> step_consistent_events \<S> (E\<^sub>e ef)" by auto

                from b5 b8 b12 c0 have "\<exists>es. getspc C1 k = EvtSeq (AnonyEvent c) es"
                  by (metis evtseq_cmd_tran_anonyevt fst_conv getspc_def)
                then obtain es where "getspc C1 k = EvtSeq (AnonyEvent c) es" by auto
                with e0 b8 have e2: "el!j = (AnonyEvent c, s1, x1)" 
                  using rm_evtsys1_def 
                  by (metis EvtSeqrm esconf_trip fst_conv gets_def getx_def snd_conv)
                with e0 e1 e2 c120 have "AnonyEvent c \<in> \<S>"
                  using step_consistent_forall[of "E\<^sub>e ef" \<S> "E\<^sub>e ef" el j]
                  by (metis getspc_e_def fstI)
                with e1 show ?thesis by auto
              }
            qed
      
        then obtain \<S> where d0: "AnonyEvent c \<in> \<S> \<and> step_consistent_events \<S> (E\<^sub>e ef)" by auto

        have d1: "ann_preserves_e (AnonyEvent c) s1"
        proof-     
          {
            from c3 have "c1 @ [C1'] \<in> preserves_pes" by (simp add: K1)
            with c4 b8 have "ann_preserves_pes pes1 s1"
              apply (simp add: preserves_pes_def)
              apply (erule_tac x = "?i" in allE)
              by (simp add: getspc_def gets_def)
            then have f0 : "ann_preserves_es (pes1 k) s1"
              by (simp add: ann_preserves_pes_def)
            from b8 c52 have "\<exists>es. pes1 k = EvtSeq (AnonyEvent c) es"
              using b12 b5 c0 evtseq_cmd_tran_anonyevt by fastforce
            then obtain es where "pes1 k = EvtSeq (AnonyEvent c) es" by auto
            with f0 have "ann_preserves_e (AnonyEvent c) s1"
              by (simp add: ann_preserves_es_def)
          }
          then show ?thesis by auto
        qed

        let ?j = "length (c2 @ [C2']) - 2"
        have d2: "ann_preserves_e (AnonyEvent c) s2"
        proof-     
          {
            from c9 have "c2 @ [C2'] \<in> preserves_pes" by (simp add: K1)
            with c10 b10 have "ann_preserves_pes pes2 s2"
              apply (simp add: preserves_pes_def)
              apply (erule_tac x = "?j" in allE)
              by (simp add: getspc_def gets_def)
            then have f0 : "ann_preserves_es (pes2 k) s2"
              by (simp add: ann_preserves_pes_def)
            from b10 c62 have "\<exists>es. pes2 k = EvtSeq (AnonyEvent c) es"
              using b13 b5 c0 evtseq_cmd_tran_anonyevt by fastforce
            then obtain es where "pes2 k = EvtSeq (AnonyEvent c) es" by auto
            with f0 have "ann_preserves_e (AnonyEvent c) s2"
              by (simp add: ann_preserves_es_def)
          }
          then show ?thesis by auto
        qed

        from b8 b9 c52 have "\<exists>e1. (AnonyEvent c, s1, x1) -et-Cmd c\<sharp>k\<rightarrow> (e1, s1', x1')"
          by (simp add:  pes_cmd_tran_anonyevt1)
        then obtain e1 where d3 : "(AnonyEvent c, s1, x1) -et-Cmd c\<sharp>k\<rightarrow> (e1, s1', x1')"by auto

        from b10 b11 c62 have "\<exists>e2. (AnonyEvent c, s2, x2) -et-Cmd c\<sharp>k\<rightarrow> (e2, s2', x2')"
          by (simp add:  pes_cmd_tran_anonyevt1)
        then obtain e2 where d4: "(AnonyEvent c, s2, x2) -et-Cmd c\<sharp>k\<rightarrow> (e2, s2', x2')" by auto

        from c14 a1 b3 b8 b10 c12 have d5: "(dome s1 k (E\<^sub>e ef)) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 k (E\<^sub>e ef))\<sim> s2" 
          using gets_def E\<^sub>e_def vpeqc_def by (metis fst_conv snd_conv) 

        from a1 b8 b10 have d5 : "s1 \<sim>u\<sim> s2"
          by (simp add: gets_def vpeqc_def)

        from c14 a1 b3 b8 b10 c12 have d6: "(dome s1 k (E\<^sub>e ef)) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 k (E\<^sub>e ef))\<sim> s2" 
          using gets_def E\<^sub>e_def vpeqc_def by (metis fst_conv snd_conv) 

        with d0 d1 d2 d3 d4 d5 have "s1' \<sim>u\<sim> s2'"
          by (drule_tac k = k in consistent_next_state, simp_all)

        then show ?case by (simp add: b11 b9 gets_def vpeqc_def)
          next
            case (EvtEnt x)
            from b12 have r1: "s1 = s1'" using entevt_notchgstate
              by (metis EvtEnt.prems b5 evtent_is_basicevt)
            from b13 have r2: "s2 = s2'" using entevt_notchgstate
              by (metis EvtEnt.prems b5 evtent_is_basicevt) 
            from a1 b8 b9 b10 b11 r1 r2 show ?case using gets_def vpeqc_def vpeq_reflexive
              by (metis fst_conv snd_conv)
          qed
        }
        then show ?thesis by auto qed
    }
    then show ?thesis using step_consistent_def by blast
  qed
qed



end