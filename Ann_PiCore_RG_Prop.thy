section \<open>Rely-guarantee Reasoning\<close>

theory Ann_PiCore_RG_Prop
  imports Ann_PiCore_Hoare
begin

fun all_evts_es :: "('l,'k,'s) rgformula_ess \<Rightarrow> ('l,'k,'s) rgformula_e set" 
  where all_evts_es_seq: "all_evts_es (rgf_EvtSeq e es) = insert e (all_evts_es (fst es))" |
        all_evts_es_esys: "all_evts_es (rgf_EvtSys es) = es"

fun all_evts_esspec :: "('l,'k,'s) esys \<Rightarrow> ('l,'k,'s) event set" 
  where "all_evts_esspec (EvtSeq e es) = insert e (all_evts_esspec es)" |
        "all_evts_esspec (EvtSys es) = es"

fun all_basicevts_es :: "('l,'k,'s) esys \<Rightarrow> ('l,'k,'s) event set" 
  where "all_basicevts_es (EvtSeq e es) = (if is_basicevt e then 
                                            insert e (all_basicevts_es es) 
                                           else all_basicevts_es es) " |
        "all_basicevts_es (EvtSys es) = {x. x\<in>es \<and> is_basicevt x}"

definition all_evts :: "('l,'k,'s) rgformula_par \<Rightarrow> ('l,'k,'s) rgformula_e set"
  where "all_evts parsys \<equiv> \<Union>k. all_evts_es (fst (parsys k))"

definition all_basicevts :: "('l,'k,'s) paresys \<Rightarrow> ('l,'k,'s) event set"
  where "all_basicevts parsys \<equiv> \<Union>k. all_basicevts_es (parsys k)"

lemma all_evts_same: "Domain (all_evts_es rgfes) = all_evts_esspec (evtsys_spec rgfes)"
  apply(induct rgfes)
  using "all_evts_esspec.simps" "all_evts_es.simps" "evtsys_spec.simps"
   E\<^sub>e_def eq_fst_iff fsts.intros apply fastforce 
  using "all_evts_esspec.simps" "all_evts_es.simps" "evtsys_spec.simps"
   E\<^sub>e_def fsts.intros apply force
  done

lemma allbasicevts_es_blto_allevts: "all_basicevts_es esys \<subseteq> all_evts_esspec esys"
  apply(induct esys)
  apply auto[1]
  by auto  
  
lemma allevts_es_blto_allevts: "\<forall>k. all_evts_esspec (evtsys_spec (fst (pesrgf k))) \<subseteq> Domain (all_evts pesrgf)"
  proof -
  {
    fix k
    have "all_evts_esspec (evtsys_spec (fst (pesrgf k))) = Domain (all_evts_es (fst (pesrgf k)))" 
      using all_evts_same by auto
    moreover
    have "all_evts_es (fst (pesrgf k)) \<subseteq> all_evts pesrgf" 
      using all_evts_def UNIV_I UN_upper by blast 
    ultimately have "all_evts_esspec (evtsys_spec (fst (pesrgf k))) \<subseteq> Domain (all_evts pesrgf)"
      by auto
  }
  then show ?thesis by auto
qed


lemma etran_nchg_curevt:
  "c \<propto> cs \<Longrightarrow> \<forall>k i. Suc i < length (cs k) \<and> (\<exists>actk. c!i-pes-actk\<rightarrow>c!Suc i) 
                \<and> (cs k ! i -ese\<rightarrow> cs k ! Suc i) 
                \<longrightarrow> getx_es (cs k ! i) k = getx_es (cs k ! Suc i) k"
  proof -
    assume p0: "c \<propto> cs"
    {
      fix k i
      assume a0: "Suc i < length (cs k)"
        and  a1: "\<exists>actk. c!i-pes-actk\<rightarrow>c!Suc i"
        and  a2: "cs k ! i -ese\<rightarrow> cs k ! Suc i"
      from p0 have a3: "\<forall>k. length c = length (cs k)" 
        using conjoin_def[of c cs] same_length_def[of c cs] by simp
      from a1 have "\<not>(c!i-pese\<rightarrow>c!Suc i)" using pes_tran_not_etran1 by blast
      with p0 a0 a1 a3 have "\<exists>t k. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<and>
                          (\<forall>k t. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i)))"
        using conjoin_def[of c cs] compat_tran_def[of c cs] by auto
      then obtain t1 and k1 where a4: "(c!i -pes-(t1\<sharp>k1)\<rightarrow> c!Suc i) \<and>
                          (\<forall>k t. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i)))" by auto
      from p0 a0 a3 have a5: "getx_es (cs k ! i) = getx_es (cs k1 ! i) 
                            \<and> getx_es (cs k ! Suc i) = getx_es (cs k1 ! Suc i)" 
        using conjoin_def[of c cs] same_state_def[of c cs] same_spec_def[of c cs] by auto
      from a2 a4 have a6: "k \<noteq> k1" using es_tran_not_etran1 by blast
      from a4 have "getx_es (cs k ! i) k = getx_es (cs k ! Suc i) k"
        proof(induct t1)
          case (Cmd x) 
          then show ?case 
            using cmd_ines_nchg_x2[of "cs k1 ! i" x k1 "cs k1 ! Suc i"] a5 by auto
        next
          case (EvtEnt x)
          then show ?case
            using a5 a6 entevt_ines_notchg_otherx2[of "cs k1 ! i" x k1 "cs k1 ! Suc i"] by auto
        qed
            
    }
    then show ?thesis by auto
  qed

lemma compt_notevtent_iscmd:
  "c \<propto> cs \<Longrightarrow> \<forall>k i. Suc i < length (cs k) \<and> (\<exists>actk. c!i-pes-actk\<rightarrow>c!Suc i) 
                \<and> (\<not> (\<exists>e. cs k ! i -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc i)) 
                \<longrightarrow> (\<exists>cmd. cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i) \<or> cs k ! i -ese\<rightarrow> cs k ! Suc i"
  proof -
    assume p0: "c \<propto> cs"
    {
      fix k i
      assume a0: "Suc i < length (cs k)"
        and  a1: "\<exists>actk. c!i-pes-actk\<rightarrow>c!Suc i"
        and  a2: "\<not> (\<exists>e. cs k ! i -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc i)"
      from p0 have a3: "\<forall>k. length c = length (cs k)" 
        using conjoin_def[of c cs] same_length_def[of c cs] by simp
      from a1 have "\<not>(c!i-pese\<rightarrow>c!Suc i)" using pes_tran_not_etran1 by blast
      with p0 a0 a1 a3 have "\<exists>t k. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<and>
                          (\<forall>k t. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i)))"
        using conjoin_def[of c cs] compat_tran_def[of c cs] by auto
      then obtain t1 and k1 where a4: "(c!i -pes-(t1\<sharp>k1)\<rightarrow> c!Suc i) \<and>
                          (\<forall>k t. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i)))" by auto
      have "(\<exists>cmd. cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i) \<or> cs k ! i -ese\<rightarrow> cs k ! Suc i"
        proof(cases "k = k1")
          assume b0: "k = k1"
          with a2 a4 have "\<exists>cmd. cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i" 
            proof(induct t1)
              case (Cmd x) then show ?case by auto
            next
              case (EvtEnt x) then show ?case by auto
            qed
          then show ?thesis by auto
        next
          assume b0: "k \<noteq> k1"
          with a4 have "cs k ! i -ese\<rightarrow> cs k ! Suc i" by auto
          then show ?thesis by simp
        qed
    }
    then show ?thesis by auto
  qed

lemma evtent_impl_curevt_in_cpts_es[rule_format]:
  "\<lbrakk>c \<propto> cs; \<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c!j-pes-actk\<rightarrow>c!Suc j)\<rbrakk>
      \<Longrightarrow> \<forall>k i. Suc i < length (cs k) \<and> ((cs k)!i -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc i)) 
                \<longrightarrow> (\<forall>j. j > Suc i \<and> Suc j < length (cs k) 
                        \<and> (\<forall>m. m > i \<and> m < j \<longrightarrow> \<not>(\<exists>e. (cs k)!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc m)))
                        \<longrightarrow> (\<forall>m. m > i \<and> m \<le> j \<longrightarrow> getx_es ((cs k)!m) k = e))"
  proof -
    assume p1: "c \<propto> cs"
      and  p3: "\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c!j-pes-actk\<rightarrow>c!Suc j)"
    from p1 p3 have "\<forall>i k. Suc i < length (cs k) \<and> (\<exists>actk. c ! i -pes-actk\<rightarrow> c ! Suc i) 
                          \<and> \<not> (\<exists>e. cs k ! i -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc i) 
                                \<longrightarrow> (\<exists>cmd. cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i) \<or> cs k ! i -ese\<rightarrow> cs k ! Suc i"
                              using compt_notevtent_iscmd [of c cs] by auto
    then have p5: "\<And>i k. Suc i < length (cs k) \<and> (\<exists>actk. c ! i -pes-actk\<rightarrow> c ! Suc i) 
                        \<and> \<not> (\<exists>e. cs k ! i -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc i) 
                                \<Longrightarrow> (\<exists>cmd. cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i) 
                                    \<or> cs k ! i -ese\<rightarrow> cs k ! Suc i" by auto
    from p1 have "\<forall>k i. Suc i < length (cs k) \<and> (\<exists>actk. c ! i -pes-actk\<rightarrow> c ! Suc i) 
                        \<and> cs k ! i -ese\<rightarrow> cs k ! Suc i \<longrightarrow>
                        getx_es (cs k ! i) k = getx_es (cs k ! Suc i) k" 
       using etran_nchg_curevt [of c cs] by simp
    then have p6: "\<And>i k. Suc i < length (cs k) \<and> (\<exists>actk. c ! i -pes-actk\<rightarrow> c ! Suc i) 
                        \<and> cs k ! i -ese\<rightarrow> cs k ! Suc i \<Longrightarrow>
                        getx_es (cs k ! i) k = getx_es (cs k ! Suc i) k" by auto
    then show ?thesis
      proof -
      {
        fix k i
        assume a0: "Suc i < length (cs k) \<and> ((cs k)!i -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc i))"
        then obtain es1 and s1 and x1 where a01: "(cs k)!i = (es1,s1,x1)"
          using prod_cases3 by blast 
        from a0 obtain es2 and s2 and x2 where a02: "(cs k)!Suc i = (es2,s2,x2)"
          using prod_cases3 by blast 
        from p1 have a2: "\<forall>k. length c = length (cs k)" using conjoin_def[of c cs] same_length_def[of c cs] by simp
        from a0 have "\<forall>j. j > Suc i \<and> Suc j < length (cs k) 
                        \<and> (\<forall>m. m > i \<and> m < j \<longrightarrow> \<not>(\<exists>e. (cs k)!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc m)))
                        \<longrightarrow> (\<forall>m. m > i \<and> m \<le> j \<longrightarrow> getx_es ((cs k)!m) k = e)"
          proof-
          {
            fix j
            assume b0: "j > Suc i \<and> Suc j < length (cs k)"
              and  b1: "\<forall>m. m > i \<and> m < j \<longrightarrow> \<not>(\<exists>e. (cs k)!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc m))"
            then have "\<forall>m. m > i \<and> m \<le> j \<longrightarrow> getx_es ((cs k)!m) k = e"
              proof(induct j)
                case 0 show ?case by simp
              next
                case (Suc sj)
                assume c0: "Suc i < sj \<and> Suc sj < length (cs k) \<Longrightarrow>
                                (\<forall>m. i < m \<and> m < sj \<longrightarrow> \<not> (\<exists>e. cs k ! m -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc m)) \<Longrightarrow>
                                (\<forall>m. i < m \<and> m \<le> sj \<longrightarrow> getx_es (cs k ! m) k = e)"
                  and  c1: "Suc i < Suc sj \<and> Suc (Suc sj) < length (cs k)"
                  and  c2: "\<forall>m. i < m \<and> m < Suc sj \<longrightarrow> \<not> (\<exists>e. cs k ! m -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc m)"
                show ?case 
                  proof(cases "Suc i = sj")
                    assume d0: "Suc i = sj"
                    then show ?thesis 
                      proof-
                      {
                        fix m
                        assume e0: "i < m \<and> m \<le> Suc sj"
                        from a0 have e1: "getx_es (cs k ! Suc i) k = e" 
                          using entevt_ines_chg_selfx2[of "cs k ! i" e k "cs k ! Suc i"] by simp
                        have "getx_es (cs k ! m) k = e"
                          proof(cases "m = Suc i")
                            assume f0: "m = Suc i"
                            with e1 show ?thesis by simp
                          next
                            assume "m \<noteq> Suc i"
                            with d0 e0 have f0: "m = Suc (Suc i)" by auto
                            with c2 d0 have f1: "\<not> (\<exists>e. cs k ! Suc i -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc (Suc i))"
                              by auto
                            from p3 a2 b0 have "\<exists>actk. c ! Suc i -pes-actk\<rightarrow> c ! Suc (Suc i)" by auto
                            with p3 b0 f1 have "(\<exists>cmd. cs k ! Suc i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc (Suc i)) \<or>
                                      cs k ! Suc i -ese\<rightarrow> cs k ! Suc (Suc i)" using p5 [of "Suc i" k] by auto
                            then show ?thesis 
                              proof 
                                assume "\<exists>cmd. cs k ! Suc i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc (Suc i)"
                                then obtain cmd where g0: "cs k ! Suc i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc (Suc i)" by auto
                                with e1 f0 have "getx_es (cs k ! Suc (Suc i)) k = e" 
                                  using cmd_ines_nchg_x2 [of "cs k ! Suc i" cmd k "cs k ! Suc (Suc i)"] by simp
                                with f0 show ?thesis by simp
                              next
                                assume g0: "cs k ! Suc i -ese\<rightarrow> cs k ! Suc (Suc i)"
                                from p3 a2 b0 have g1: "\<exists>actk. c ! Suc i -pes-actk\<rightarrow> c ! Suc (Suc i)" by auto
                                from b0 e1 f0 g0 g1 show ?thesis using p6 [of "Suc i" k] by auto
                              qed
                          qed
                      }
                      then show ?thesis by auto qed
                  next
                    assume d0: "Suc i \<noteq> sj"
                    with c1 have d1: "Suc i < sj" by auto
                    with c0 c1 c2 have d2: "\<forall>m. i < m \<and> m \<le> sj \<longrightarrow> getx_es (cs k ! m) k = e" by auto
                    then show ?thesis
                      proof -
                      {
                        fix m
                        assume e0: "i < m \<and> m \<le> Suc sj"
                        have " getx_es (cs k ! m) k = e"
                          proof(cases "i < m \<and> m < Suc sj")
                            assume f0: "i < m \<and> m < Suc sj"
                            with d2 show ?thesis by auto
                          next
                            assume f0: "\<not>(i < m \<and> m < Suc sj)"
                            with e0 have f1: "m = Suc sj" by simp
                            from d1 d2 have f2: "getx_es (cs k ! sj) k = e" by auto
                            from f1 c1 c2 have f3: "\<not> (\<exists>e. cs k ! sj -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc sj)"
                              by auto
                            from c2 d1 have "\<not> (\<exists>e. cs k ! sj -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc sj)" by auto
                            from p3 a2 c1 have "\<exists>actk. c ! sj -pes-actk\<rightarrow> c ! Suc sj" by auto
                            with p3 b0 c1 f1 f3 have "(\<exists>cmd. cs k ! sj -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc sj) \<or>
                                      cs k ! sj -ese\<rightarrow> cs k ! Suc sj" using p5 [of sj k] by auto
                            then show ?thesis
                              proof
                                assume "(\<exists>cmd. cs k ! sj -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc sj)"
                                then obtain cmd where g0: "cs k !sj -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc sj" by auto
                                with f2 have "getx_es (cs k ! Suc sj) k = e" 
                                  using cmd_ines_nchg_x2 [of "cs k ! sj" cmd k "cs k ! Suc sj"] by simp
                                with f1 show ?thesis by simp
                              next
                                assume g0: "cs k ! sj -ese\<rightarrow> cs k ! Suc sj"
                                from p3 a2 c1 have g1: "\<exists>actk. c ! sj -pes-actk\<rightarrow> c ! Suc sj" by auto
                                from b0 c1 f1 f2 g0 g1 show ?thesis using p6 [of sj k] by auto 
                              qed
                          qed
                      } 
                      then show ?thesis by auto qed
                  qed
              qed
          }
          then show ?thesis by auto qed
      }
      then show ?thesis by auto qed
  qed

lemma evtent_impl_curevt_in_cpts_es1[rule_format]:
  "\<lbrakk>c \<propto> cs; \<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c!j-pes-actk\<rightarrow>c!Suc j)\<rbrakk> 
      \<Longrightarrow> \<forall>k i. Suc i < length (cs k) \<and> ((cs k)!i -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc i)) 
                \<longrightarrow> (\<forall>j. j \<ge> Suc i \<and> Suc j \<le> length (cs k) 
                        \<and> (\<forall>m. m > i \<and> m < j \<longrightarrow> \<not>(\<exists>e. (cs k)!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc m)))
                        \<longrightarrow> (\<forall>m. m > i \<and> m \<le> j \<longrightarrow> getx_es ((cs k)!m) k = e))"
  proof -
    assume p1: "c \<propto> cs"
      and  p3: "\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c!j-pes-actk\<rightarrow>c!Suc j)"
    from p1 p3 have "\<forall>i k. Suc i < length (cs k) \<and> (\<exists>actk. c ! i -pes-actk\<rightarrow> c ! Suc i) 
                          \<and> \<not> (\<exists>e. cs k ! i -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc i) 
                                \<longrightarrow> (\<exists>cmd. cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i) \<or> cs k ! i -ese\<rightarrow> cs k ! Suc i"
                              using compt_notevtent_iscmd [of c cs] by auto
    then have p5: "\<And>i k. Suc i < length (cs k) \<and> (\<exists>actk. c ! i -pes-actk\<rightarrow> c ! Suc i) 
                        \<and> \<not> (\<exists>e. cs k ! i -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc i) 
                                \<Longrightarrow> (\<exists>cmd. cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i) 
                                    \<or> cs k ! i -ese\<rightarrow> cs k ! Suc i" by auto
    from p1 have "\<forall>k i. Suc i < length (cs k) \<and> (\<exists>actk. c ! i -pes-actk\<rightarrow> c ! Suc i) 
                        \<and> cs k ! i -ese\<rightarrow> cs k ! Suc i \<longrightarrow>
                        getx_es (cs k ! i) k = getx_es (cs k ! Suc i) k" 
       using etran_nchg_curevt [of c cs] by simp
    then have p6: "\<And>i k. Suc i < length (cs k) \<and> (\<exists>actk. c ! i -pes-actk\<rightarrow> c ! Suc i) 
                        \<and> cs k ! i -ese\<rightarrow> cs k ! Suc i \<Longrightarrow>
                        getx_es (cs k ! i) k = getx_es (cs k ! Suc i) k" by auto
    then show ?thesis
      proof -
      {
        fix k i
        assume a0: "Suc i < length (cs k) \<and> ((cs k)!i -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc i))"
        then obtain es1 and s1 and x1 where a01: "(cs k)!i = (es1,s1,x1)"
          using prod_cases3 by blast 
        from a0 obtain es2 and s2 and x2 where a02: "(cs k)!Suc i = (es2,s2,x2)"
          using prod_cases3 by blast 
        from p1 have a2: "\<forall>k. length c = length (cs k)" using conjoin_def[of c cs] same_length_def[of c cs] by simp
        from a0 have "\<forall>j. j \<ge> Suc i \<and> Suc j \<le> length (cs k) 
                        \<and> (\<forall>m. m > i \<and> m < j \<longrightarrow> \<not>(\<exists>e. (cs k)!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc m)))
                        \<longrightarrow> (\<forall>m. m > i \<and> m \<le> j \<longrightarrow> getx_es ((cs k)!m) k = e)"
          proof-
          {
            fix j
            assume b0: "j \<ge> Suc i \<and> Suc j \<le> length (cs k)"
              and  b1: "\<forall>m. m > i \<and> m < j \<longrightarrow> \<not>(\<exists>e. (cs k)!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc m))"
            then have "\<forall>m. m > i \<and> m \<le> j \<longrightarrow> getx_es ((cs k)!m) k = e"
              proof(induct j)
                case 0 show ?case by simp
              next
                case (Suc sj)
                assume c0: "Suc i \<le> sj \<and> Suc sj \<le> length (cs k) \<Longrightarrow>
                                (\<forall>m. i < m \<and> m < sj \<longrightarrow> \<not> (\<exists>e. cs k ! m -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc m)) \<Longrightarrow>
                                (\<forall>m. i < m \<and> m \<le> sj \<longrightarrow> getx_es (cs k ! m) k = e)"
                  and  c1: "Suc i \<le> Suc sj \<and> Suc (Suc sj) \<le> length (cs k)"
                  and  c2: "\<forall>m. i < m \<and> m < Suc sj \<longrightarrow> \<not> (\<exists>e. cs k ! m -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc m)"
                show ?case 
                  proof(cases "Suc i = Suc sj")
                    assume d0: "Suc i = Suc sj"
                    then show ?thesis 
                      proof-
                      {
                        fix m
                        assume e0: "i < m \<and> m \<le> Suc sj"
                        from a0 have e1: "getx_es (cs k ! Suc i) k = e" 
                          using entevt_ines_chg_selfx2[of "cs k ! i" e k "cs k ! Suc i"] by simp
                        have "getx_es (cs k ! m) k = e"
                          proof(cases "m = Suc i")
                            assume f0: "m = Suc i"
                            with e1 show ?thesis by simp
                          next
                            assume "m \<noteq> Suc i"
                            with d0 e0 have f0: "m = Suc (Suc i)" by auto
                            with c2 d0 have f1: "\<not> (\<exists>e. cs k ! Suc i -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc (Suc i))"
                              using Suc_n_not_le_n e0 by blast
                            from p3 a2 b0 have "\<exists>actk. c ! Suc i -pes-actk\<rightarrow> c ! Suc (Suc i)"
                              using Suc_le_lessD c1 d0 Suc_n_not_le_n e0 f0 by blast
                            with p3 b0 f1 have "(\<exists>cmd. cs k ! Suc i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc (Suc i)) \<or>
                                      cs k ! Suc i -ese\<rightarrow> cs k ! Suc (Suc i)" using p5 [of "Suc i" k]
                                        using Suc_le_eq c1 d0 Suc_n_not_le_n e0 f0 by blast
                            then show ?thesis 
                              proof 
                                assume "\<exists>cmd. cs k ! Suc i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc (Suc i)"
                                then obtain cmd where g0: "cs k ! Suc i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc (Suc i)" by auto
                                with e1 f0 have "getx_es (cs k ! Suc (Suc i)) k = e" 
                                  using cmd_ines_nchg_x2 [of "cs k ! Suc i" cmd k "cs k ! Suc (Suc i)"] by simp
                                with f0 show ?thesis by simp
                              next
                                assume g0: "cs k ! Suc i -ese\<rightarrow> cs k ! Suc (Suc i)"
                                from p3 a2 b0 have g1: "\<exists>actk. c ! Suc i -pes-actk\<rightarrow> c ! Suc (Suc i)"
                                  using \<open>\<exists>actk. c ! Suc i -pes-actk\<rightarrow> c ! Suc (Suc i)\<close> by blast
                                from b0 e1 f0 g0 g1 show ?thesis using p6 [of "Suc i" k]
                                  Suc_n_not_le_n d0 e0 by blast
                              qed
                          qed
                      }
                      then show ?thesis by auto qed
                  next
                    assume d0: "Suc i \<noteq> Suc sj"
                    with c1 have d1: "Suc i < Suc sj" by auto
                    with c0 c1 c2 have d2: "\<forall>m. i < m \<and> m \<le> sj \<longrightarrow> getx_es (cs k ! m) k = e" by auto
                    then show ?thesis
                      proof -
                      {
                        fix m
                        assume e0: "i < m \<and> m \<le> Suc sj"
                        have " getx_es (cs k ! m) k = e"
                          proof(cases "i < m \<and> m < Suc sj")
                            assume f0: "i < m \<and> m < Suc sj"
                            with d2 show ?thesis by auto
                          next
                            assume f0: "\<not>(i < m \<and> m < Suc sj)"
                            with e0 have f1: "m = Suc sj" by simp
                            from d1 d2 have f2: "getx_es (cs k ! sj) k = e" by auto
                            from f1 c1 c2 have f3: "\<not> (\<exists>e. cs k ! sj -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc sj)"
                              using Suc_less_SucD d1 lessI by blast
                            from c2 d1 have "\<not> (\<exists>e. cs k ! sj -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc sj)" by auto
                            from p3 a2 c1 have "\<exists>actk. c ! sj -pes-actk\<rightarrow> c ! Suc sj" by auto
                            with p3 b0 c1 f1 f3 have "(\<exists>cmd. cs k ! sj -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc sj) \<or>
                                      cs k ! sj -ese\<rightarrow> cs k ! Suc sj" using p5 [of sj k] by auto
                            then show ?thesis
                              proof
                                assume "(\<exists>cmd. cs k ! sj -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc sj)"
                                then obtain cmd where g0: "cs k !sj -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc sj" by auto
                                with f2 have "getx_es (cs k ! Suc sj) k = e" 
                                  using cmd_ines_nchg_x2 [of "cs k ! sj" cmd k "cs k ! Suc sj"] by simp
                                with f1 show ?thesis by simp
                              next
                                assume g0: "cs k ! sj -ese\<rightarrow> cs k ! Suc sj"
                                from p3 a2 c1 have g1: "\<exists>actk. c ! sj -pes-actk\<rightarrow> c ! Suc sj" by auto
                                from b0 c1 f1 f2 g0 g1 show ?thesis using p6 [of sj k] by auto 
                              qed
                          qed
                      } 
                      then show ?thesis by auto qed
                  qed
              qed
          }
          then show ?thesis by auto qed
      }
      then show ?thesis by auto qed
  qed

lemma evtent_impl_curevt_in_cpts_es2[rule_format]:
  "\<lbrakk>c \<propto> cs; \<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c!j-pes-actk\<rightarrow>c!Suc j)\<rbrakk>
      \<Longrightarrow> \<forall>k i. Suc i < length (cs k) \<and> ((cs k)!i -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc i)) 
                \<longrightarrow> (\<forall>j. j > i \<and> Suc j < length (cs k) 
                        \<and> (\<forall>m. m > i \<and> m < j \<longrightarrow> \<not>(\<exists>e. (cs k)!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc m)))
                        \<longrightarrow> (\<forall>m. m > i \<and> m \<le> j \<longrightarrow> getx_es ((cs k)!m) k = e))"
  proof -
    assume p1: "c \<propto> cs"
      and  p3: "\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c!j-pes-actk\<rightarrow>c!Suc j)"
    then show ?thesis
      proof -
      {
        fix k i
        assume a0: "Suc i < length (cs k) \<and> ((cs k)!i -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc i))"
        then have "\<forall>j. j > i \<and> Suc j < length (cs k) 
                        \<and> (\<forall>m. m > i \<and> m < j \<longrightarrow> \<not>(\<exists>e. (cs k)!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc m)))
                        \<longrightarrow> (\<forall>m. m > i \<and> m \<le> j \<longrightarrow> getx_es ((cs k)!m) k = e)"
          proof -
          {
            fix j
            assume b0: "j > i \<and> Suc j < length (cs k)"
              and  b1: "\<forall>m. m > i \<and> m < j \<longrightarrow> \<not>(\<exists>e. (cs k)!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> (cs k)!(Suc m))"
            then have "\<forall>m. m > i \<and> m \<le> j \<longrightarrow> getx_es ((cs k)!m) k = e"
              proof(cases "j = Suc i")
                assume c0: "j = Suc i"
                then show ?thesis by (metis a0 entevt_ines_chg_selfx2 le_SucE not_less) 
              next
                assume c0: "j \<noteq> Suc i"
                with b0 have "j > Suc i" by simp
                with p1 p3 a0 b0 b1 show ?thesis using evtent_impl_curevt_in_cpts_es[of c cs i k e j] by auto
              qed
          }
          then show ?thesis by auto
          qed
      }
      then show ?thesis by auto
      qed
    qed


lemma anonyevtseq_and_noet_impl_allanonyevtseq_bef: 
  "esl \<in> cpts_es \<Longrightarrow>
    \<forall>m < length esl. (\<exists>e es. getspc_es (esl!m) = EvtSeq e es \<and> is_anonyevt e) 
                      \<longrightarrow> (\<forall>i < m. \<not> (\<exists>e k. esl ! i -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc i)) 
                      \<longrightarrow> (\<forall>i < m. \<exists>e es. getspc_es (esl!i) = EvtSeq e es \<and> is_anonyevt e)" 
  proof -
    assume p0: "esl \<in> cpts_es"
    {
      fix m
      assume a0: "m < length esl"
        and  a1: "\<exists>e es. getspc_es (esl!m) = EvtSeq e es \<and> is_anonyevt e"
        and  a2: "\<forall>i < m. \<not> (\<exists>e k. esl ! i -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc i)"
      then have "\<forall>i < m. \<exists>e es. getspc_es (esl!i) = EvtSeq e es \<and> is_anonyevt e"
        proof(induct m)
          case 0 then show ?case by simp
        next
          case (Suc n)
          assume b0: "n < length esl \<Longrightarrow>
                      \<exists>e es. getspc_es (esl ! n) = EvtSeq e es \<and> is_anonyevt e \<Longrightarrow>
                      \<forall>i < n. \<not> (\<exists>e k. esl ! i -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc i) \<Longrightarrow>
                      \<forall>i < n. \<exists>e es. getspc_es (esl ! i) = EvtSeq e es \<and> is_anonyevt e"
            and  b1: "Suc n < length esl"
            and  b2: "\<exists>e es. getspc_es (esl ! Suc n) = EvtSeq e es \<and> is_anonyevt e"
            and  b3: "\<forall>i < Suc n. \<not> (\<exists>e k. esl ! i -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc i)"
          then show ?case 
            proof(cases "n = 0")
              assume c0: "n = 0"
              with b3 have "\<not> (\<exists>e k. esl ! 0 -es-EvtEnt e\<sharp>k\<rightarrow> esl ! 1)" by auto
              with p0 b1 c0 have "esl ! 0 -ese\<rightarrow> esl ! 1 \<or> (\<exists>c k. esl ! 0 -es-Cmd c\<sharp>k\<rightarrow> esl ! 1)"
                using notevtent_cptses_isenvorcmd[of esl] by auto
              then have "\<exists>e es. getspc_es (esl ! 0) = EvtSeq e es \<and> is_anonyevt e"
                proof
                  assume d0: "esl ! 0 -ese\<rightarrow> esl ! 1"
                  with b2 c0 show ?thesis using esetran_eqconf1[of "esl ! 0" "esl ! 1"] by simp
                next
                  assume d0: "\<exists>c k. esl ! 0 -es-Cmd c\<sharp>k\<rightarrow> esl ! 1"
                  then obtain c and k where "esl ! 0 -es-Cmd c\<sharp>k\<rightarrow> esl ! 1" by auto
                  then show ?thesis using cmd_enable_impl_anonyevt2[of "esl ! 0" c k "esl ! 1"] by auto
                qed
              with c0 show ?thesis by auto
            next
              assume "n \<noteq> 0"
              then have c0: "n > 0" by auto
              from b1 b3 have b4: "\<not> (\<exists>e k. esl ! n -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc n)" by auto
              moreover
              from p0 b1 have "drop n esl\<in>cpts_es" using cpts_es_dropi2[of esl n] by simp
              moreover
              from b1 have "2 \<le> length (drop n esl)" by simp
              moreover
              from b1 have "drop n esl ! 0 = esl ! n" by auto
              moreover
              from b1 c0 have "drop n esl ! 1 = esl ! Suc n" by auto
              ultimately have "esl ! n -ese\<rightarrow> esl ! Suc n \<or> (\<exists>c k. esl ! n -es-Cmd c\<sharp>k\<rightarrow> esl ! Suc n)" 
                using notevtent_cptses_isenvorcmd[of "drop n esl"] by auto
              then show ?case
                proof
                  assume d0: "esl ! n -ese\<rightarrow> esl ! Suc n"
                  with b2 c0 have d1: "\<exists>e es. getspc_es (esl ! n) = EvtSeq e es \<and> is_anonyevt e" 
                    using esetran_eqconf1[of "esl ! n" "esl ! Suc n"] by auto
                  with b0 b1 b2 b3 have "\<forall>i < n. \<exists>e es. getspc_es (esl ! i) = EvtSeq e es \<and> is_anonyevt e"
                    by auto
                  with d1 show ?thesis by (simp add: less_Suc_eq) 
                next
                  assume d0: "\<exists>c k. esl ! n -es-Cmd c\<sharp>k\<rightarrow> esl ! Suc n"
                  then obtain c1 and k1 where "esl ! n -es-Cmd c1\<sharp>k1\<rightarrow> esl ! Suc n" by auto
                  then have d1: "\<exists>e e' es1. getspc_es (esl ! n) = EvtSeq e es1 \<and> e = AnonyEvent e'" 
                    using cmd_enable_impl_anonyevt2[of "(esl ! n)" c1 k1 "esl ! Suc n"] by simp
                  with b0 b1 b2 b3 have "\<forall>i < n. \<exists>e es. getspc_es (esl ! i) = EvtSeq e es \<and> is_anonyevt e"
                    by auto
                  with d1 show ?thesis using is_anonyevt.simps(1) less_Suc_eq by auto 
                qed
            qed
        qed 
    }
    then show ?thesis by auto
  qed

lemma anonyevtseq_and_noet_impl_allanonyevtseq_bef3: 
  "\<lbrakk>c \<propto> cs; cs k \<in> cpts_es; m < length (cs k)\<rbrakk> \<Longrightarrow>
    (\<exists>e es. getspc_es ((cs k)!m) = EvtSeq e es \<and> is_anonyevt e) 
                      \<longrightarrow> (\<forall>i < m. \<not> (\<exists>e. (cs k) ! i -es-EvtEnt e\<sharp>k\<rightarrow> (cs k) ! Suc i)) 
                      \<longrightarrow> (\<forall>i < m. \<exists>e es. getspc_es ((cs k)!i) = EvtSeq e es \<and> is_anonyevt e)" 
  proof -
    assume p0: "(cs k) \<in> cpts_es"
      and  p1: "c \<propto> cs"
      and  p2: "m < length (cs k)"
    {
      assume a1: "\<exists>e es. getspc_es ((cs k)!m) = EvtSeq e es \<and> is_anonyevt e"
        and  a2: "\<forall>i < m. \<not> (\<exists>e. (cs k) ! i -es-EvtEnt e\<sharp>k\<rightarrow> (cs k) ! Suc i)"
      with p2 have "\<forall>i < m. \<exists>e es. getspc_es ((cs k)!i) = EvtSeq e es \<and> is_anonyevt e"
        proof(induct m)
          case 0 then show ?case by simp
        next
          case (Suc n)
          assume b0: "n < length (cs k) \<Longrightarrow>
                      \<exists>e es. getspc_es ((cs k) ! n) = EvtSeq e es \<and> is_anonyevt e \<Longrightarrow>
                      \<forall>i < n. \<not> (\<exists>e. (cs k) ! i -es-EvtEnt e\<sharp>k\<rightarrow> (cs k) ! Suc i) \<Longrightarrow>
                      \<forall>i < n. \<exists>e es. getspc_es ((cs k) ! i) = EvtSeq e es \<and> is_anonyevt e"
            and  b1: "Suc n < length (cs k)"
            and  b2: "\<exists>e es. getspc_es ((cs k) ! Suc n) = EvtSeq e es \<and> is_anonyevt e"
            and  b3: "\<forall>i < Suc n. \<not> (\<exists>e. (cs k) ! i -es-EvtEnt e\<sharp>k\<rightarrow> (cs k) ! Suc i)"
          then show ?case 
            proof(cases "n = 0")
              assume c0: "n = 0"
              with b3 have "\<not> (\<exists>e. (cs k) ! 0 -es-EvtEnt e\<sharp>k\<rightarrow> (cs k) ! 1)" by auto
              with p0 p1 b1 c0 have "(cs k) ! 0 -ese\<rightarrow> (cs k) ! 1 \<or> (\<exists>c. (cs k) ! 0 -es-Cmd c\<sharp>k\<rightarrow> (cs k) ! 1)"
                using acts_in_conjoin_cpts by (metis One_nat_def) 
              then have "\<exists>e es. getspc_es ((cs k) ! 0) = EvtSeq e es \<and> is_anonyevt e"
                proof
                  assume d0: "(cs k) ! 0 -ese\<rightarrow> (cs k) ! 1"
                  with b2 c0 show ?thesis using esetran_eqconf1[of "(cs k) ! 0" "(cs k) ! 1"] by simp
                next
                  assume d0: "\<exists>c. (cs k) ! 0 -es-Cmd c\<sharp>k\<rightarrow> (cs k) ! 1"
                  then obtain c and k where "(cs k) ! 0 -es-Cmd c\<sharp>k\<rightarrow> (cs k) ! 1" by auto
                  then show ?thesis using cmd_enable_impl_anonyevt2[of "(cs k) ! 0" c k "(cs k) ! 1"]
                    by (metis cmd_enable_impl_anonyevt2 d0 is_anonyevt.simps(1)) 
                qed
              with c0 show ?thesis by auto
            next
              assume "n \<noteq> 0"
              then have c0: "n > 0" by auto
              from b1 b3 have b4: "\<not> (\<exists>e. (cs k) ! n -es-EvtEnt e\<sharp>k\<rightarrow> (cs k) ! Suc n)" by auto
              with p1 b1 have "(cs k) ! n -ese\<rightarrow> (cs k) ! Suc n \<or> (\<exists>c. (cs k) ! n -es-Cmd c\<sharp>k\<rightarrow> (cs k) ! Suc n)"
                using acts_in_conjoin_cpts by fastforce 
              then show ?case
                proof
                  assume d0: "(cs k) ! n -ese\<rightarrow> (cs k) ! Suc n"
                  with b2 c0 have d1: "\<exists>e es. getspc_es ((cs k) ! n) = EvtSeq e es \<and> is_anonyevt e" 
                    using esetran_eqconf1[of "(cs k) ! n" "(cs k) ! Suc n"] by auto
                  with b0 b1 b2 b3 have "\<forall>i < n. \<exists>e es. getspc_es ((cs k) ! i) = EvtSeq e es \<and> is_anonyevt e"
                    by auto
                  with d1 show ?thesis by (simp add: less_Suc_eq) 
                next
                  assume d0: "\<exists>c. (cs k) ! n -es-Cmd c\<sharp>k\<rightarrow> (cs k) ! Suc n"
                  then obtain c1 where "(cs k) ! n -es-Cmd c1\<sharp>k\<rightarrow> (cs k) ! Suc n" by auto
                  then have d1: "\<exists>e e' es1. getspc_es ((cs k) ! n) = EvtSeq e es1 \<and> e = AnonyEvent e'" 
                    using cmd_enable_impl_anonyevt2[of "((cs k) ! n)" c1 k "(cs k) ! Suc n"] by simp
                  with b0 b1 b2 b3 have "\<forall>i < n. \<exists>e es. getspc_es ((cs k) ! i) = EvtSeq e es \<and> is_anonyevt e"
                    by auto
                  with d1 show ?thesis using is_anonyevt.simps(1) less_Suc_eq by auto 
                qed
            qed
        qed 
    }
    then show ?thesis by auto
  qed

lemma evtseq_noesys_allevtseq: "\<lbrakk>esl\<in>cpts_es; esl = (EvtSeq ev esys, s, x) # esl1; 
        (\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> esys)\<rbrakk>
        \<Longrightarrow> (\<forall>i < length esl. \<exists>e'. getspc_es (esl ! i) = EvtSeq e' esys)"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSeq ev esys, s, x) # esl1"
      and  p2: "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> esys"
    {
      fix i
      assume a0: "i < length esl"
      then have "\<exists>e'. getspc_es (esl ! i) = EvtSeq e' esys"
        proof(induct i)
          case 0 
          from p1 show ?case using getspc_es_def fst_conv nth_Cons_0 by fastforce 
        next
          case (Suc ii)
          assume b0: "ii < length esl \<Longrightarrow> \<exists>e'. getspc_es (esl ! ii) = EvtSeq e' esys"
            and  b1: "Suc ii < length esl"
          then obtain e' where "getspc_es (esl ! ii) = EvtSeq e' esys" by auto
          with p0 have "getspc_es (esl!Suc ii) = esys \<or> (\<exists>e. getspc_es (esl!Suc ii) = EvtSeq e esys)"
            using evtseq_next_in_cpts[of esl e' esys] b1 by auto
          with p2 b1 show ?case by auto
        qed
    }
    then show ?thesis by auto
  qed

lemma evtseq_noesys_allevtseq2: "\<lbrakk>esl\<in>cpts_es; esl = (EvtSeq ev esys, s, x) # esl1; \<not> is_basicevt ev;
        (\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> esys)\<rbrakk>
        \<Longrightarrow> (\<forall>i < length esl. \<exists>e'. \<not> is_basicevt e' \<and> getspc_es (esl ! i) = EvtSeq e' esys)"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSeq ev esys, s, x) # esl1"
      and  p2: "\<not> is_basicevt ev"
      and  p3: "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> esys"
    {
      fix i
      assume a0: "i < length esl"
      then have "\<exists>e'. \<not> is_basicevt e' \<and> getspc_es (esl ! i) = EvtSeq e' esys"
        proof(induct i)
          case 0 
          with p1 p2 show ?case using getspc_es_def fst_conv nth_Cons_0 by fastforce 
        next
          case (Suc ii)
          assume b0: "ii < length esl \<Longrightarrow> \<exists>e'. \<not> is_basicevt e' \<and> getspc_es (esl ! ii) = EvtSeq e' esys"
            and  b1: "Suc ii < length esl"
          then have b2: "\<exists>e'. \<not> is_basicevt e' \<and> getspc_es (esl ! ii) = EvtSeq e' esys" by auto
          then obtain e' where b3: "\<not> is_basicevt e' \<and> getspc_es (esl ! ii) = EvtSeq e' esys" by auto
          from b1 b2 have "getspc_es (esl!Suc ii) = esys \<or> (\<exists>e. getspc_es (esl!Suc ii) = EvtSeq e esys)" 
            using evtseq_next_in_cpts [of esl] p0 by blast 
          with p3 b1 have "\<exists>e. getspc_es (esl!Suc ii) = EvtSeq e esys" by auto
          then obtain e where b4: "getspc_es (esl!Suc ii) = EvtSeq e esys" by auto
          with p0 b2 have "\<not> is_basicevt e" 
            proof -
            {
              assume c0: "is_basicevt e"
              then obtain be where "e = BasicEvent be" by (metis event.exhaust is_basicevt.simps(1)) 
              with p0 b1 b3 b4 have "getspc_es (esl ! ii) = EvtSeq (BasicEvent be) esys" 
                using only_envtran_to_basicevt[of esl esys be] by fastforce
              with b3 c0 have "False" using is_basicevt_def by auto
            }
            then show ?thesis by auto
            qed
          with b4 show ?case by simp
        qed
    }
    then show ?thesis by auto
  qed

lemma evtseq_evtent_befaft: "\<lbrakk>esl\<in>cpts_es; esl = (EvtSeq ev esys, s, x) # esl1; 
        (\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> esys);
        (\<exists>e k. m <length esl - 1 \<and> esl ! m -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc m)\<rbrakk> \<Longrightarrow> 
         is_basicevt ev \<and> (\<forall>i. i \<le> m \<longrightarrow> getspc_es (esl ! i) = EvtSeq ev esys) 
         \<and> (\<forall>i. i > m \<and> i < length esl \<longrightarrow> (\<exists>e'. \<not> is_basicevt e' \<and> getspc_es (esl ! i) = EvtSeq e' esys))"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSeq ev esys, s, x) # esl1"
      and  p2: "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> esys"
      and  p3: "\<exists>e k. m <length esl - 1 \<and> esl ! m -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc m"
    then have a0: "\<forall>i < length esl. \<exists>e'. getspc_es (esl ! i) = EvtSeq e' esys"
      using evtseq_noesys_allevtseq[of esl ev esys s x esl1] by simp
    from p3 obtain e and k where a1: "m <length esl - 1 \<and> esl ! m -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc m" by auto
    with a0 obtain e' where a2: "getspc_es (esl ! m) = EvtSeq e' esys"
      using length_Cons length_tl less_SucI list.sel(3) p1 by fastforce 
    with a0 a1 have a3: "e = e' \<and> (\<exists>e''. e' = BasicEvent e'')" 
      using evtent_is_basicevt_inevtseq2[of "esl ! m" e k "esl ! Suc m" e' esys] by auto
    then obtain be where a4: "e' = BasicEvent be" by auto
    then have a5: "\<forall>i. i \<le> m \<longrightarrow> getspc_es ((drop (m - i) esl) ! 0) = EvtSeq e esys"
      proof-
      {
        fix i
        assume b0: "i \<le> m"
        then have "getspc_es ((drop (m - i) esl) ! 0) = EvtSeq e esys"
          proof(induct i)
            case 0 
            with a1 a2 a3 show ?case by auto
          next
            case (Suc ii)
            assume c0: "ii \<le> m \<Longrightarrow> getspc_es (drop (m - ii) esl ! 0) = EvtSeq e esys"
              and  c1: "Suc ii \<le> m"
            from p0 have "\<forall>i. Suc i < length esl \<and>
                  (\<exists>e. getspc_es (esl ! i) = EvtSeq e esys) \<and> getspc_es (esl ! Suc i) = EvtSeq (BasicEvent be) esys \<longrightarrow>
                  getspc_es (esl ! i) = EvtSeq (BasicEvent be) esys" 
               using only_envtran_to_basicevt[of esl esys be] by simp
            then have c01: "\<And>i. Suc i < length esl \<and>
                  (\<exists>e. getspc_es (esl ! i) = EvtSeq e esys) \<and> getspc_es (esl ! Suc i) = EvtSeq (BasicEvent be) esys \<longrightarrow>
                  getspc_es (esl ! i) = EvtSeq (BasicEvent be) esys" by simp
            from c0 c1 have c2: "getspc_es (drop (m - ii) esl ! 0) = EvtSeq e esys" by simp
            moreover
            from a1 c1 have "drop (m - Suc ii) esl ! 0 = esl ! (m - Suc ii)" by force
            moreover
            from a1 c1 have "drop (m - ii) esl ! 0 = esl ! (m - ii)" by force
            moreover
            from a0 a1 c1 have "(\<exists>e. getspc_es (esl ! (m - Suc ii)) = EvtSeq e esys)" by auto
            ultimately show ?case using p0 a0 a1 a3 a4 c0 c1 c01[of "(m - Suc ii)"]
              Suc_diff_Suc Suc_le_lessD length_Cons length_tl less_SucI less_imp_diff_less 
              list.sel(3) p1 by auto
          qed
      }
      then show ?thesis by auto 
      qed
    then have "getspc_es (esl ! 0) = EvtSeq e esys" by auto
    with p1 have a51: "ev =  e" using getspc_es_def by (metis esys.inject(1) fst_conv nth_Cons_0) 
    with a5 have r1: "\<forall>i. i \<le> m \<longrightarrow> getspc_es (esl ! i) = EvtSeq ev esys"
      by (metis (no_types, lifting) Cons_nth_drop_Suc a1 diff_diff_cancel diff_le_self 
        le_less_trans length_Cons length_tl less_SucI list.sel(3) nth_Cons_0 p1) 
    
    let ?esl = "drop (Suc m) esl"
    from p0 p1 a1 have a6: "?esl\<in>cpts_es" 
      using Suc_mono cpts_es_dropi length_Cons length_tl list.sel(3) by fastforce 
    from a1 obtain esc1 and s1 and x1 and esc2 and s2 and x2 
      where a7: "esl ! m = (esc1,s1,x1) \<and> esl ! Suc m = (esc2,s2,x2) \<and> (esc1,s1,x1) -es-EvtEnt e\<sharp>k\<rightarrow> (esc2,s2,x2)"
      using prod_cases3 by metis 
    from a7 have "\<exists>e. \<not> is_basicevt e \<and> getspc_es (?esl!0) = EvtSeq e esys" 
      apply(simp add:is_basicevt_def)
      apply(rule estran.cases)
      apply auto
      apply (metis a2 esys.simps(4) fst_conv getspc_es_def) 
      using get_actk_def apply (smt Cons_nth_drop_Suc Suc_mono a1 a2 a3 ent_spec2' 
        esys.inject(1) event.simps(7) fst_conv getspc_es_def length_Cons length_tl list.sel(3) nth_Cons_0 p1) 
      by (metis (no_types, lifting) Suc_leI Suc_le_mono a1 a2 esys.inject(1) fst_conv 
          getspc_es_def length_Cons length_tl list.sel(3) p1 p2)
    then obtain e1 and s3 and x3 where a7: "\<not> is_basicevt e1 \<and> ?esl!0 = (EvtSeq e1 esys,s3,x3)"
      by (metis fst_conv getspc_es_def surj_pair) 
    from p2 have "\<forall>i. Suc i \<le> length ?esl \<longrightarrow> getspc_es (?esl ! i) \<noteq> esys" by auto
    with p2 a6 a7 have a8: "\<forall>i < length ?esl. \<exists>e'. \<not> is_basicevt e' \<and> getspc_es (?esl ! i) = EvtSeq e' esys"
      using evtseq_noesys_allevtseq2[of ?esl e1 esys s3 x3] by (metis (no_types, lifting) 
        Cons_nth_drop_Suc Suc_mono a1 length_Cons length_tl list.sel(3) nth_Cons_0 p1)
    then have "\<forall>i. i > m \<and> i < length esl \<longrightarrow> (\<exists>e'. \<not> is_basicevt e' \<and> getspc_es (esl ! i) = EvtSeq e' esys)" 
      proof -
      {
        fix i
        assume b0: "i > m \<and> i < length esl"
        with a1 have "esl ! i = ?esl ! (i - Suc m)" by auto
        from b0 have "i - Suc m \<ge> 0" by auto
        moreover
        from b0 have "i - Suc m < length ?esl" by auto
        ultimately have "\<exists>e'. \<not> is_basicevt e' \<and> getspc_es (?esl ! (i - Suc m)) = EvtSeq e' esys" using a8 by auto
      }
      then show ?thesis by auto
      qed

    with a1 a3 a4 a51 r1 show ?thesis by auto
  qed

lemma evtsys_allevtseqorevtsys: 
  "\<lbrakk>esl\<in>cpts_es; esl = (EvtSys es, s, x) # esl1\<rbrakk>
        \<Longrightarrow> (\<forall>i < length esl. getspc_es (esl ! i) = EvtSys es 
                              \<or> (\<exists>e'. is_anonyevt e' \<and> getspc_es (esl ! i) = EvtSeq e' (EvtSys es)))"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSys es, s, x) # esl1"
    {
      fix i
      assume a0: "i < length esl"
      then have "getspc_es (esl ! i) = EvtSys es \<or> 
                (\<exists>e'. is_anonyevt e' \<and> getspc_es (esl ! i) = EvtSeq e' (EvtSys es))"
        proof(induct i)
          case 0 then show ?case using p1 getspc_es_def fst_conv nth_Cons_0 by force 
        next
          case (Suc ii)
          assume b0: "ii < length esl \<Longrightarrow> getspc_es (esl ! ii) = EvtSys es \<or> 
            (\<exists>e'. is_anonyevt e' \<and> getspc_es (esl ! ii) = EvtSeq e' (EvtSys es))"
            and  b1: "Suc ii < length esl"
          from a0 obtain esc1 and s1 and x1 where b2: "esl ! ii = (esc1,s1,x1)"
            using prod_cases3 by blast  
          from a0 obtain esc2 and s2 and x2 where b3: "esl ! Suc ii = (esc2,s2,x2)"
            using prod_cases3 by blast  
          from p0 b1 b2 b3 have b4: "(esc1,s1,x1) -ese\<rightarrow> (esc2,s2,x2) \<or> (\<exists>et. (esc1,s1,x1) -es-et\<rightarrow> (esc2,s2,x2))" 
                using incpts_es_impl_evnorcomptran[of esl] by auto
          from b0 b1 have "getspc_es (esl ! ii) = EvtSys es \<or> 
            (\<exists>e'. is_anonyevt e' \<and> getspc_es (esl ! ii) = EvtSeq e' (EvtSys es))"
            by auto
          then show ?case
            proof
              assume c0: "getspc_es (esl ! ii) = EvtSys es"
              with b2 have c1: "esc1 = EvtSys es" using getspc_es_def by (metis fst_conv) 
              from b4 have "esc2 = EvtSys es \<or> (\<exists>e'. is_anonyevt e' \<and> esc2 = EvtSeq e' (EvtSys es))" 
                proof
                  assume "(esc1,s1,x1) -ese\<rightarrow> (esc2,s2,x2)"
                  then have "esc1 = esc2" by (simp add: esetran_eqconf) 
                  with c1 show ?thesis by simp
                next
                  assume "\<exists>et. (esc1,s1,x1) -es-et\<rightarrow> (esc2,s2,x2)"
                  then obtain et where "(esc1,s1,x1) -es-et\<rightarrow> (esc2,s2,x2)" by auto
                  with c1 have "\<exists>e'. is_anonyevt e' \<and> esc2 = EvtSeq e' (EvtSys es)" 
                    apply(clarsimp simp:is_anonyevt_def)
                    apply(rule estran.cases)
                    apply(simp add:get_actk_def)+
                    apply(rule etran.cases)
                    apply simp+
                    done
                  then show ?thesis by auto
                qed
              with b2 b3 show ?thesis using getspc_es_def fst_conv by fastforce 
            next
              assume c0: "\<exists>e'. is_anonyevt e' \<and> getspc_es (esl ! ii) = EvtSeq e' (EvtSys es)"
              then obtain e' where c2: "is_anonyevt e' \<and> getspc_es (esl ! ii) = EvtSeq e' (EvtSys es)" by auto
              with b2 have c1: "esc1 = EvtSeq e' (EvtSys es)" using getspc_es_def by (metis fst_conv) 
              from b4 have "esc2 =EvtSys es \<or> (\<exists>e'. is_anonyevt e' \<and> esc2 = EvtSeq e' (EvtSys es))" 
                proof
                  assume d0:"(esc1,s1,x1) -ese\<rightarrow> (esc2,s2,x2)"
                  then have "esc1 = esc2" by (simp add: esetran_eqconf) 
                  with c1 c2 d0 show ?thesis by auto
                next
                  assume "\<exists>et. (esc1,s1,x1) -es-et\<rightarrow> (esc2,s2,x2)"
                  then obtain et where "(esc1,s1,x1) -es-et\<rightarrow> (esc2,s2,x2)" by auto
                  with c1 c2 show ?thesis 
                    apply(clarsimp simp:is_anonyevt_def)
                    apply(rule estran.cases)
                    apply(simp add:get_actk_def)+
                    apply(rule etran.cases)
                    apply simp+
                    done
                qed 
              with b2 b3 show ?thesis using getspc_es_def fst_conv by fastforce 
            qed
        qed
    }
    then show ?thesis by auto
  qed

lemma evtsys_befevtent_isevtsys: 
  "\<lbrakk>esl\<in>cpts_es; esl = (EvtSys es, s, x) # esl1\<rbrakk>
        \<Longrightarrow> \<forall>i. Suc i < length esl \<and> (\<exists>e k. esl ! i -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc i) \<longrightarrow> getspc_es (esl!i) = EvtSys es"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSys es, s, x) # esl1"
    {
      fix i
      assume a0: "Suc i < length esl"
        and  a1: "(\<exists>e k. esl ! i -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc i)"
      with p0 p1 have a00: "getspc_es (esl ! i) = EvtSys es \<or> (\<exists>e'. is_anonyevt e' \<and> getspc_es (esl ! i) = EvtSeq e' (EvtSys es))"
        using evtsys_allevtseqorevtsys[of esl es s x esl1] by auto
      from a0 obtain esc1 and s1 and x1 where a2: "esl ! i = (esc1,s1,x1)"
        using prod_cases3 by blast  
      from a0 obtain esc2 and s2 and x2 where a3: "esl ! Suc i = (esc2,s2,x2)"
        using prod_cases3 by blast 
      from a1 a2 a3 obtain e and k where a4: "(esc1,s1,x1)-es-EvtEnt e\<sharp>k\<rightarrow>(esc2,s2,x2)" by auto
      from a00 a2 have a5: "esc1 = EvtSys es \<or> (\<exists>e'. is_anonyevt e' \<and> esc1 = EvtSeq e' (EvtSys es))" 
        using getspc_es_def by (metis fst_conv) 
      with a4 have "\<not>(\<exists>e'. is_anonyevt e' \<and> esc1 = EvtSeq e' (EvtSys es))" 
        apply(simp add:get_actk_def is_anonyevt_def)
        apply(rule estran.cases)
        apply simp+
        apply(rule etran.cases)
        apply(simp add:get_actk_def)+
        apply(rule etran.cases)
        apply(simp add:get_actk_def)+
        done
      with a5 have "esc1 = EvtSys es" by simp
      with a2 have "getspc_es (esl!i) = EvtSys es" using getspc_es_def by (metis fst_conv)
    }
    then show ?thesis by auto
  qed

lemma allentev_isin_basicevts:
    "\<forall>esl esc s x esl1 e k. esl\<in>cpts_es \<and> esl = (esc,s,x)#esl1 \<longrightarrow>
          (\<forall>m<length esl - 1. (esl ! m -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc m) \<longrightarrow> e\<in>all_basicevts_es esc)"
  proof -
  {
    fix esc
    have "\<forall>esl s x esl1 e k. esl\<in>cpts_es \<and> esl = (esc,s,x)#esl1 \<longrightarrow>
          (\<forall>m<length esl - 1. (esl ! m -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc m) \<longrightarrow> e\<in>all_basicevts_es esc)"
      proof(induct esc)
        case (EvtSeq ev esys)
        assume a0: "\<forall>esl s x esl1 e k.
                     esl \<in> cpts_es \<and> esl = (esys, s, x) # esl1 \<longrightarrow>
                     (\<forall>i<length esl - 1. (esl ! i -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc i) \<longrightarrow> e \<in> all_basicevts_es esys)"
        then have a1: "\<And>esl s x esl1 e k.
                     esl \<in> cpts_es \<and> esl = (esys, s, x) # esl1 \<Longrightarrow>
                     (\<forall>i<length esl - 1. (esl ! i -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc i) \<longrightarrow> e \<in> all_basicevts_es esys)" by auto
        {
          fix esl s x esl1 e k
          assume b0: "esl \<in> cpts_es \<and> esl = (EvtSeq ev esys, s, x) # esl1"
          {
            fix m
            assume c0: "m<length esl - 1"
              and  c1: "esl ! m -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc m"
            have "e \<in> all_basicevts_es (EvtSeq ev esys)"
              proof(cases "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> esys")
                assume d0: "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> esys"
                with b0 c0 c1 have d1: "is_basicevt ev \<and> (\<forall>i. i \<le> m \<longrightarrow> getspc_es (esl ! i) = EvtSeq ev esys)"
                  using evtseq_evtent_befaft[of esl ev esys s x esl1 m] by auto
                then have "getspc_es (esl ! m) = EvtSeq ev esys" by simp
                with c1 have "e = ev" using evtent_is_basicevt_inevtseq2 by fastforce 
                with d1 show ?thesis using all_basicevts_es.simps(1)
                  by (simp add: insertI1) 
              next
                assume d0: "\<not>(\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> esys)"
                then have "\<exists>m. Suc m \<le> length esl \<and> getspc_es (esl ! m) = esys" by auto
                then obtain m1 where d1: "Suc m1 \<le> length esl \<and> getspc_es (esl ! m1) = esys" by auto
                then have "\<exists>i. i \<le> m1 \<and> getspc_es (esl ! i) = esys" by auto
                with b0 d1 have d2: "\<exists>i. (i \<le> m1 \<and> getspc_es (esl ! i) = esys) 
                                    \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) \<noteq> esys)"
                  using evtseq_fst_finish[of esl ev esys m1] getspc_es_def fst_conv nth_Cons' by force 
                then obtain n where d3: "(n \<le> m1 \<and> getspc_es (esl ! n) = esys) 
                                          \<and> (\<forall>j. j < n \<longrightarrow> getspc_es (esl ! j) \<noteq> esys)"
                  by auto
                from b0 d3 have "n \<noteq> 0" by (metis (no_types, lifting) Groups.add_ac(2) 
                    Suc_n_not_le_n add.right_neutral add_Suc_right esys.size(3) fst_conv 
                    getspc_es_def le_add1 nth_Cons')
                then have d4:"n > 0" by simp
                
                show ?thesis
                  proof(cases "m < n")
                    assume e0: "m < n"
                    let ?esl0 = "take n esl"
                    from d1 d3 d4 have e1: "?esl0 \<in> cpts_es"
                      by (metis (no_types, lifting) Suc_le_lessD Suc_pred' b0 cpts_es_take less_trans)
                    
                    from b0 d1 d3 d4 obtain esl2 where e2: "?esl0 = (EvtSeq ev esys, s, x) # esl2"
                      by (simp add: take_Cons') 
                     
                    from d1 d3 d4 have e3: "\<forall>i. Suc i \<le> length ?esl0 \<longrightarrow> getspc_es (?esl0 ! i) \<noteq> esys"
                      by (simp add: drop_take leD le_less_linear not_less_eq)
                    
                    have e4: "Suc m \<noteq> n"
                      proof -
                      {
                        assume f0: "Suc m = n"
                        from d1 d3 d4 e0 have "m < length ?esl0" by auto
                        with d1 d3 e0 e1 e2 e3 have "\<exists>e'. getspc_es (?esl0 ! m) = EvtSeq e' esys"
                          using evtseq_noesys_allevtseq[of ?esl0 ev esys s x esl2] by simp
                        then obtain e' where "getspc_es (?esl0 ! m) = EvtSeq e' esys" by auto
                        then obtain s' and x' where f1: "?esl0 ! m = (EvtSeq e' esys, s',x')" 
                          using getspc_es_def by (metis fst_conv surj_pair)
                        moreover
                        from d3 obtain s'' and x'' where f2:"esl ! n = (esys,s'',x'')" 
                          using getspc_es_def by (metis fst_conv surj_pair)
                        moreover
                        from d1 d3 e0 have "?esl0 ! m = esl ! m" by auto
                        moreover
                        with c1 have f4:"?esl0 ! m -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc m" by simp
                        ultimately have f3:"(EvtSeq e' esys, s',x')-es-EvtEnt e\<sharp>k\<rightarrow>(esys,s'',x'')" using f0 by simp
                        then have False
                          apply(rule estran.cases)
                          apply(simp add:get_actk_def)
                          apply(rule etran.cases)
                          apply(simp add:get_actk_def)+
                          apply (metis f3 ent_spec2' event.inject(1) evtseq_tran_0_exist_etran 
                            noevtent_notran option.distinct(1))
                          by (metis f2 f4 f1 ent_spec2' event.inject(1) evtent_is_basicevt_inevtseq f0 option.simps(3))
                      } then show ?thesis by auto   
                      qed
                    
                    from c1 e0 d1 d3 d4 e4 have e5: "?esl0 ! m -es-EvtEnt e\<sharp>k\<rightarrow> ?esl0 ! Suc m"
                      by (simp add: Suc_lessI) 
                    from d1 d3 d4 e0 e4 have "m < length ?esl0 - 1" by auto
                    with b0 c0 c1 e1 e2 e3 e4 e5 have d1: "is_basicevt ev \<and> (\<forall>i. i \<le> m \<longrightarrow> getspc_es (esl ! i) = EvtSeq ev esys)"
                      using evtseq_evtent_befaft[of ?esl0 ev esys s x esl2 m]
                      by (smt diff_diff_cancel e0 less_imp_diff_less nth_take) 
                    then have "getspc_es (esl ! m) = EvtSeq ev esys" by simp
                    with c1 have "e = ev" using evtent_is_basicevt_inevtseq2 by fastforce 
                    with d1 show ?thesis using all_basicevts_es.simps(1)
                      by (simp add: insertI1)
                  next
                    assume "\<not>m < n"
                    then have e0: "m \<ge> n" by auto
                    let ?esl0 = "drop n esl"
                    from c0 e0 have "?esl0 \<in> cpts_es" using b0 cpts_es_dropi2 length_Cons 
                      length_tl less_SucI list.sel(3) by fastforce 
                    moreover
                    from d1 d3 obtain s' and x' and esl1 where "?esl0 = (esys,s',x')#esl1"
                      by (metis (no_types, hide_lams) Cons_nth_drop_Suc getspc_es_def 
                        less_le_trans not_less_eq old.prod.exhaust prod.sel(1)) 
                    moreover
                    from d1 d3 d0 c0 e0 have "m - n <length ?esl0 - 1" by auto 
                    moreover
                    from d1 d3 d0 c0 e0 have "esl ! m = ?esl0 ! (m - n)" by auto
                    moreover
                    from d1 d3 d0 c0 e0 have "esl ! Suc m = ?esl0 ! Suc (m - n)" by auto
                    ultimately have "e \<in> all_basicevts_es esys" 
                      using c1 d1 d3 e0 a1[of ?esl0 s' x' esl1 e k] by auto
                    then show ?thesis using all_basicevts_es.simps by simp
                  qed
              qed
          }
        }
        then show ?case by auto
      next
        case (EvtSys es)
        {
          fix esl s x esl1 e k
          assume b0: "esl \<in> cpts_es \<and> esl = (EvtSys es, s, x) # esl1"
          {
            fix m
            assume c0: "m<length esl - 1"
              and  c1: "esl ! m -es-EvtEnt e\<sharp>k\<rightarrow> esl ! Suc m"
            with b0 have c00: "getspc_es (esl!m) = EvtSys es"
              using evtsys_befevtent_isevtsys[of esl es s x esl1] 
              Suc_mono length_Cons length_tl list.sel(3) by auto 
            from c0 obtain esc1 and s1 and x1 where c2: "esl ! m = (esc1,s1,x1)"
              using prod_cases3 by blast  
            from c0 obtain esc2 and s2 and x2 where c3: "esl ! Suc m = (esc2,s2,x2)"
              using prod_cases3 by blast 
            from c1 c2 c3 have c4: "(esc1,s1,x1)-es-EvtEnt e\<sharp>k\<rightarrow>(esc2,s2,x2)" by auto
            with c00 c2 c3 have c5: "\<exists>i\<in>es. i = e" 
              using evtsysent_evtent2[of es s1 x1 e k esc2 s2 x2] getspc_es_def
                by (metis fst_conv)  
            from c4 have "is_basicevt e" 
              using evtent_is_basicevt[of esc1 s1 x1 e k esc2 s2 x2] is_basicevt.simps by auto
            with c5 have "e \<in> all_basicevts_es (EvtSys es)" using "all_basicevts_es.simps" by auto
          }
        }
        then show ?case by auto
      qed
  }
  then show ?thesis by fastforce 
qed

lemma cmd_impl_evtent_before:
  "\<lbrakk>c \<propto> cs; cs k\<in>cpts_of_es esc s x; \<forall>ef\<in>all_evts_esspec esc. is_basicevt ef\<rbrakk>
    \<Longrightarrow> \<forall>i. Suc i < length (cs k) \<longrightarrow> (\<exists>cmd. (cs k)!i -es-((Cmd cmd)\<sharp>k)\<rightarrow> (cs k)!(Suc i)) 
            \<longrightarrow> (\<exists>m. m < i \<and> (\<exists>e. (cs k)!m -es-(EvtEnt e\<sharp>k)\<rightarrow> (cs k)!(Suc m)))" 
  proof -
    assume p0: "c \<propto> cs"
      and  p1: "cs k\<in>cpts_of_es esc s x"
      and  p2: "\<forall>ef\<in>all_evts_esspec esc. is_basicevt ef"
    let ?esl = "cs k"
    from p1 have p01: "?esl \<in> cpts_es \<and> ?esl ! 0 = (esc,s,x)" by (simp add:cpts_of_es_def)
    {
      fix i
      assume a0: "Suc i < length ?esl"
        and  a1: "\<exists>cmd. ?esl!i -es-((Cmd cmd)\<sharp>k)\<rightarrow> ?esl!(Suc i)"
      
      then obtain cmd where a2: "?esl!i -es-((Cmd cmd)\<sharp>k)\<rightarrow> ?esl!(Suc i)" by auto
      then obtain esc1 and s1 and x1 and esc2 and s2 and x2 where a3:
        "?esl!i = (esc1,s1,x1) \<and> ?esl!Suc i = (esc2,s2,x2)"
        by (meson prod_cases3) 
      with a2 have a4: "\<exists>e' es. esc1 = EvtSeq e' es \<and> is_anonyevt e'" 
        using cmd_enable_impl_anonyevt[of esc1 s1 x1 cmd k esc2 s2 x2] is_anonyevt.simps by auto
      from p01 p2 a3 a4 have a5: "i \<noteq> 0" by (metis all_evts_esspec.simps(1) anonyevt_isnot_basic fst_conv insertI1) 
      have "\<exists>m. m < i \<and> (\<exists>e. ?esl!m -es-(EvtEnt e\<sharp>k)\<rightarrow> ?esl!(Suc m))" 
        proof-
        {
          assume b0: "\<not>(\<exists>m. m < i \<and> (\<exists>e. ?esl!m -es-(EvtEnt e\<sharp>k)\<rightarrow> ?esl!(Suc m)))"
          then have b1: "\<forall>j. j < i \<longrightarrow> \<not>(\<exists>e. ?esl!j -es-(EvtEnt e\<sharp>k)\<rightarrow> ?esl!(Suc j))" by auto
          with p0 p01 a0 a1 a3 a4 have "\<forall>j < i. \<exists>e es. getspc_es (?esl!j) = EvtSeq e es \<and> is_anonyevt e" 
            using anonyevtseq_and_noet_impl_allanonyevtseq_bef3[of c cs k i] getspc_es_def
              by (metis Suc_lessD fst_conv)
          with a5 have "\<exists>e es. getspc_es (?esl!0) = EvtSeq e es \<and> is_anonyevt e" by simp
          with p01 p1 p2 have False by (metis all_evts_esspec.simps(1) anonyevt_isnot_basic 
              getspc_es_def insertI1 prod.sel(1))
        }
        then show ?thesis by blast
        qed
    }
    then show ?thesis by blast
  qed

lemma cmd_impl_evtent_before_and_cmds:
  "\<lbrakk>c \<propto> cs; cs k\<in>cpts_of_es esc s x; \<forall>ef\<in>all_evts_esspec esc. is_basicevt ef\<rbrakk>
    \<Longrightarrow> \<forall>i. Suc i < length (cs k) \<longrightarrow> (\<exists>cmd. (cs k)!i -es-((Cmd cmd)\<sharp>k)\<rightarrow> (cs k)!(Suc i)) 
            \<longrightarrow> (\<exists>m. m < i \<and> (\<exists>e. (cs k)!m -es-(EvtEnt e\<sharp>k)\<rightarrow> (cs k)!(Suc m))
                      \<and> (\<forall>j. j > m \<and> j < i \<longrightarrow> \<not>(\<exists>e. (cs k)!j -es-(EvtEnt e\<sharp>k)\<rightarrow> (cs k)!(Suc j))))" 
  proof -
    assume p0: "c \<propto> cs"
      and  p1: "cs k\<in>cpts_of_es esc s x"
      and  p2: "\<forall>ef\<in>all_evts_esspec esc. is_basicevt ef"
    let ?esl = "cs k"
    from p1 have p01: "?esl \<in> cpts_es \<and> ?esl ! 0 = (esc,s,x)" by (simp add:cpts_of_es_def)
    {
      fix i
      assume a0: "Suc i < length ?esl"
        and  a1: "\<exists>cmd. ?esl!i -es-((Cmd cmd)\<sharp>k)\<rightarrow> ?esl!(Suc i)"
      from p0 p1 p2 a0 a1 have "\<exists>m. m < i \<and> (\<exists>e. ?esl!m -es-(EvtEnt e\<sharp>k)\<rightarrow> ?esl!(Suc m))"
        using cmd_impl_evtent_before[of c cs k esc s x] by auto
      then obtain m where a2: "m < i \<and> (\<exists>e. ?esl!m -es-(EvtEnt e\<sharp>k)\<rightarrow> ?esl!(Suc m))" by auto
      with a0 have "\<exists>m. m < i \<and> (\<exists>e. ?esl!m -es-(EvtEnt e\<sharp>k)\<rightarrow> ?esl!(Suc m))
                    \<and> (\<forall>j. j > m \<and> j < i \<longrightarrow> \<not>(\<exists>e. ?esl!j -es-(EvtEnt e\<sharp>k)\<rightarrow> ?esl!(Suc j)))"
        proof(induct i)
          case 0 then show ?case by simp
        next
          case (Suc ii)
          assume b0: "Suc ii < length ?esl \<Longrightarrow>
                      m < ii \<and> (\<exists>e. ?esl ! m -es-EvtEnt e\<sharp>k\<rightarrow> ?esl ! Suc m) \<Longrightarrow>
                      \<exists>m<ii. (\<exists>e. ?esl ! m -es-EvtEnt e\<sharp>k\<rightarrow> ?esl ! Suc m) \<and>
                             (\<forall>j. m < j \<and> j < ii \<longrightarrow> \<not> (\<exists>e. ?esl ! j -es-EvtEnt e\<sharp>k\<rightarrow> ?esl ! Suc j))"
            and  b1: "Suc (Suc ii) < length ?esl"
            and  b2: "m < Suc ii \<and> (\<exists>e. ?esl ! m -es-EvtEnt e\<sharp>k\<rightarrow> ?esl ! Suc m)"
          then show ?case
            proof(cases "m = ii")
              assume c0: "m = ii"
              with b2 show ?case using not_less_eq by auto 
            next
              assume "m \<noteq> ii"
              with b2 have c0: "m < ii" by simp
              with b0 b1 b2 have c1: "\<exists>m<ii. (\<exists>e. ?esl ! m -es-EvtEnt e\<sharp>k\<rightarrow> ?esl ! Suc m) \<and>
                             (\<forall>j. m < j \<and> j < ii \<longrightarrow> \<not> (\<exists>e. ?esl ! j -es-EvtEnt e\<sharp>k\<rightarrow> ?esl ! Suc j))" by auto
              then obtain m1 where c2: "m1<ii \<and> (\<exists>e. ?esl ! m1 -es-EvtEnt e\<sharp>k\<rightarrow> ?esl ! Suc m1) \<and>
                             (\<forall>j. m1 < j \<and> j < ii \<longrightarrow> \<not> (\<exists>e. ?esl ! j -es-EvtEnt e\<sharp>k\<rightarrow> ?esl ! Suc j))" by auto
              show ?case
                proof(cases "\<exists>e. ?esl ! ii -es-EvtEnt e\<sharp>k\<rightarrow> ?esl ! Suc ii")
                  assume d0: "\<exists>e. ?esl ! ii -es-EvtEnt e\<sharp>k\<rightarrow> ?esl ! Suc ii"
                  then show ?thesis using lessI not_less_eq by auto 
                next
                  assume d0: "\<not> (\<exists>e. ?esl ! ii -es-EvtEnt e\<sharp>k\<rightarrow> ?esl ! Suc ii)"
                  with c2 show ?thesis by (metis less_Suc_eq) 
                qed
            qed
        qed
    }
    then show ?thesis by blast
  qed

lemma cur_evt_in_cpts_es:
  "\<lbrakk>c\<in>cpts_of_pes (paresys_spec pesrgf) s x; c \<propto> cs; 
    (\<forall>k. (cs k) \<in> cpts_of_es (evtsys_spec (fst (pesrgf k))) s x); 
    \<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c!j-pes-actk\<rightarrow>c!Suc j); 
    \<forall>ef\<in>all_evts pesrgf. is_basicevt (E\<^sub>e ef)\<rbrakk>
      \<Longrightarrow> \<forall>k i. Suc i < length (cs k) \<longrightarrow> (\<exists>cmd. (cs k)!i -es-((Cmd cmd)\<sharp>k)\<rightarrow> (cs k)!(Suc i)) 
                \<longrightarrow> (\<exists>ef\<in>all_evts_es (fst (pesrgf k)). getx_es ((cs k)!i) k = E\<^sub>e ef)"
  proof -
    assume p0: "c\<in>cpts_of_pes (paresys_spec pesrgf) s x"
      and  p1: "c \<propto> cs"
      and  p2: "(\<forall>k. (cs k) \<in> cpts_of_es (evtsys_spec (fst (pesrgf k))) s x)"
      and  p3: "\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c!j-pes-actk\<rightarrow>c!Suc j)"
      and  p4: "\<forall>ef\<in>all_evts pesrgf. is_basicevt (E\<^sub>e ef)"
    {
      fix k i
      assume a0: "Suc i < length (cs k)"
        and  a1: "\<exists>cmd. (cs k)!i -es-((Cmd cmd)\<sharp>k)\<rightarrow> (cs k)!(Suc i)"
      from p4 have a2: "\<forall>ef\<in>all_evts_esspec (evtsys_spec (fst (pesrgf k))). is_basicevt ef"
        using allevts_es_blto_allevts[of pesrgf]
        by (metis (no_types, hide_lams) DomainE E\<^sub>e_def prod.sel(1) subsetCE) 
      from p2 have a3: "cs k \<in> cpts_of_es (evtsys_spec (fst (pesrgf k))) s x" by simp
      with p1 a0 a1 a2 a3 have "(\<exists>m. m < i \<and> (\<exists>e. cs k!m -es-(EvtEnt e\<sharp>k)\<rightarrow> cs k!(Suc m))
                    \<and> (\<forall>j. j > m \<and> j < i \<longrightarrow> \<not>(\<exists>e. cs k!j -es-(EvtEnt e\<sharp>k)\<rightarrow> cs k!(Suc j))))"
        using cmd_impl_evtent_before_and_cmds[of c cs k "evtsys_spec (fst (pesrgf k))" s x] by auto
      then obtain m and e where a4: "m < i \<and> (cs k!m -es-(EvtEnt e\<sharp>k)\<rightarrow> cs k!(Suc m))
                    \<and> (\<forall>j. j > m \<and> j < i \<longrightarrow> \<not>(\<exists>e. cs k!j -es-(EvtEnt e\<sharp>k)\<rightarrow> cs k!(Suc j)))" by auto
      with p1 p3 a0 have a5: "\<forall>j. j > m \<and> j \<le> i \<longrightarrow> getx_es ((cs k)!j) k = e" 
        using evtent_impl_curevt_in_cpts_es[of c cs m k e i]
        by (smt Suc_lessD Suc_lessI entevt_ines_chg_selfx2 less_trans_Suc not_less) 
      with a4 have a6: "getx_es ((cs k)!i) k = e" by auto
      from a3 have "cs k \<in> cpts_es \<and> (\<exists>esl1. cs k = (evtsys_spec (fst (pesrgf k)), s, x)#esl1)"
        using cpts_of_es_def by (smt a0 hd_Cons_tl list.size(3) mem_Collect_eq not_less0 nth_Cons_0) 
      with a0 a4 have "e\<in>all_basicevts_es (evtsys_spec (fst (pesrgf k)))" 
        using allentev_isin_basicevts by (smt Suc_lessE diff_Suc_1 le_less_trans less_imp_le_nat) 
      with a6 have "\<exists>ef\<in>all_evts_es (fst (pesrgf k)). getx_es ((cs k)!i) k = E\<^sub>e ef"
        using allbasicevts_es_blto_allevts[of "evtsys_spec (fst (pesrgf k))"] 
          by (metis (no_types, hide_lams) DomainE E\<^sub>e_def all_evts_same fst_conv set_mp) 
    }
    then show ?thesis by auto
  qed

lemma cur_evt_in_specevts: 
    "\<lbrakk>pesl\<in>cpts_of_pes (paresys_spec pesf) s x; 
      \<forall>j. Suc j < length pesl \<longrightarrow> (\<exists>actk. pesl!j-pes-actk\<rightarrow>pesl!Suc j);
      \<forall>ef\<in>all_evts pesf. is_basicevt (E\<^sub>e ef)\<rbrakk> \<Longrightarrow>
        (\<forall>k i. Suc i < length pesl \<longrightarrow> (\<exists>c. (pesl!i -pes-((Cmd c)\<sharp>k)\<rightarrow> pesl!(Suc i)))
            \<longrightarrow> (\<exists>ef\<in>all_evts pesf. getx (pesl!i) k = E\<^sub>e ef) )" 
  proof -
    assume p0: "pesl\<in>cpts_of_pes (paresys_spec pesf) s x"
      and  p1: "\<forall>j. Suc j < length pesl \<longrightarrow> (\<exists>actk. pesl!j-pes-actk\<rightarrow>pesl!Suc j)"
      and  p2: "\<forall>ef\<in>all_evts pesf. is_basicevt (E\<^sub>e ef)"
    then have "\<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es ((paresys_spec pesf) k) s x) \<and> pesl \<propto> cs"
      using par_evtsys_semantics_comp[of "paresys_spec pesf" s x] by auto
    then obtain cs where a1: "(\<forall>k. (cs k) \<in> cpts_of_es ((paresys_spec pesf) k) s x) \<and> pesl \<propto> cs" by auto
    then have a2: "\<forall>k. length pesl = length (cs k)" by (simp add:conjoin_def same_length_def)
    from a1 have a3: "\<forall>k j. j < length pesl \<longrightarrow> getx (pesl!j) = getx_es ((cs k)!j)"
      by (simp add:conjoin_def same_state_def)
    {
      fix k i
      assume b0: "Suc i < length pesl"
        and  b1: "\<exists>c. (pesl!i -pes-((Cmd c)\<sharp>k)\<rightarrow> pesl!(Suc i))"
      then obtain c where b2: "pesl!i -pes-((Cmd c)\<sharp>k)\<rightarrow> pesl!(Suc i)" by auto
      from a1 have b3: "compat_tran pesl cs" by (simp add:conjoin_def)
      with b0 have b4: "\<exists>t k. (pesl!i -pes-(t\<sharp>k)\<rightarrow> pesl!Suc i) \<and>
                          (\<forall>k t. (pesl!i -pes-(t\<sharp>k)\<rightarrow> pesl!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i)))
                          \<or>
                          (((pesl!i) -pese\<rightarrow> (pesl!Suc i)) \<and> (\<forall>k. (((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i))))"
        using compat_tran_def[of pesl cs] by auto

      from b2 have "\<exists>t k1. k1 = k \<and> t = Cmd c \<and> pesl ! i -pes-t\<sharp>k\<rightarrow> pesl ! Suc i" by simp
      
      then have "\<not>(pesl ! i -pese\<rightarrow> pesl ! Suc i)" by (simp add: pes_tran_not_etran1) 
      with b4 have "\<exists>t k. (pesl!i -pes-(t\<sharp>k)\<rightarrow> pesl!Suc i) \<and>
                          (\<forall>k t. (pesl!i -pes-(t\<sharp>k)\<rightarrow> pesl!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i)))" by simp
      then obtain t and k1 where b5: "(pesl!i -pes-(t\<sharp>k1)\<rightarrow> pesl!Suc i) \<and>
                          (\<forall>k t. (pesl!i -pes-(t\<sharp>k)\<rightarrow> pesl!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i)))" by auto
      have "cs k ! i -es-((Cmd c)\<sharp>k)\<rightarrow> cs k!(Suc i)" using b2 b5 by auto
      with p0 p1 p2 a1 a2 b0 b1 have "\<exists>ef\<in>all_evts_es (fst (pesf k)). getx_es ((cs k)!i) k = E\<^sub>e ef"
        using cur_evt_in_cpts_es[of pesl pesf s x cs] by (metis paresys_spec_def) 
      then obtain ef where "ef\<in>all_evts_es (fst (pesf k)) \<and> getx_es ((cs k)!i) k = E\<^sub>e ef" by auto
      moreover
      have "all_evts_es (fst (pesf k)) \<subseteq> all_evts pesf" using all_evts_def by auto
      moreover
      from a2 a3 b0 have "getx_es ((cs k)!i) k = getx (pesl!i) k" by auto
      ultimately have "\<exists>ef\<in>all_evts pesf. getx (pesl!i) k = E\<^sub>e ef" by auto
    }
    then show ?thesis by auto
  qed

lemma drop_take_ln: "\<lbrakk>l1 = drop i (take j l); length l1 > n\<rbrakk> \<Longrightarrow> j > i + n"
  by (metis add.commute add_lessD1 leI length_drop length_take less_diff_conv 
    less_imp_add_positive min.absorb2 nat_le_linear take_all) 
   
lemma drop_take_eq: "\<lbrakk>l1 = drop i (take j l); j \<le> length l; length l1 = n; n > 0\<rbrakk> \<Longrightarrow> j = i + n"
  by simp 

lemma drop_take_sametrace[rule_format]: "\<lbrakk>l1 = drop i (take j l)\<rbrakk> \<Longrightarrow> \<forall>m < length l1. l1 ! m = l ! (i + m)"
  by (simp add: less_imp_le_nat)




lemma act_cpts_evtsys_sat_guar_curevt_gen0_new2[rule_format]:
  "\<lbrakk>\<turnstile> (esspc::('l,'k,'s) rgformula_ess) sat\<^sub>s [pre, rely, guar, post]\<rbrakk>
      \<Longrightarrow> \<forall>c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd. 
            Pre k \<subseteq> pre \<and> Rely k \<subseteq> rely \<and> guar \<subseteq> Guar k \<and> post \<subseteq> Post k \<longrightarrow>
            c\<in>cpts_of_pes pes s x \<and> c \<propto> cs \<and> c\<in>assume_pes(pre1, rely1) \<longrightarrow>
           (\<forall>k. (cs k) \<in> cpts_of_es (pes k) s x)  \<longrightarrow> 
           (\<forall>k. (cs k)\<in>commit_es(Guar k, Post k)) \<longrightarrow>
           (\<forall>k. pre1 \<subseteq> Pre k) \<longrightarrow>
           (\<forall>k. rely1 \<subseteq> Rely k) \<longrightarrow>
           (\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k) \<longrightarrow>
           evtsys_spec esspc = EvtSys es \<and>  EvtSys es = getspc_es (cs k!0) \<longrightarrow>
           (\<forall>e\<in>all_evts_es esspc. is_basicevt (E\<^sub>e e)) \<longrightarrow>
           (\<forall>e\<in>all_evts_es esspc. the (evtrgfs (E\<^sub>e e)) = snd e) \<longrightarrow>
           (\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c!j-pes-actk\<rightarrow>c!Suc j)) \<longrightarrow>
          (\<forall>i. Suc i < length (cs k) \<and> ((cs k)!i -es-((Cmd cmd)\<sharp>k)\<rightarrow> (cs k)!(Suc i)) 
                \<longrightarrow> (gets_es ((cs k)!i), gets_es ((cs k)!(Suc i)))\<in>Guar\<^sub>f (the (evtrgfs (getx_es ((cs k)!i) k))))"
  apply(rule rghoare_es.induct[of esspc pre rely guar post]) 
  apply simp
  apply simp
  proof -
  {
    fix esf prea relya guara posta
    assume p0: " \<turnstile> (esspc::('l,'k,'s) rgformula_ess) sat\<^sub>s [pre, rely, guar, post]"
      and  b5: "\<forall>ef\<in>(esf::('l,'k,'s) rgformula_e set). \<turnstile> E\<^sub>e ef sat\<^sub>e [Pre\<^sub>e ef, Rely\<^sub>e ef, Guar\<^sub>e ef, Post\<^sub>e ef]"
      and  b6: "\<forall>ef\<in>esf. prea \<subseteq> Pre\<^sub>e ef"
      and  b7: "\<forall>ef\<in>esf. relya \<subseteq> Rely\<^sub>e ef"
      and  b8: "\<forall>ef\<in>esf. Guar\<^sub>e ef \<subseteq> guara"
      and  b9: "\<forall>ef\<in>esf. Post\<^sub>e ef \<subseteq> posta"
      and  b10: "\<forall>ef1 ef2. ef1 \<in> esf \<and> ef2 \<in> esf \<longrightarrow> Post\<^sub>e ef1 \<subseteq> Pre\<^sub>e ef2"
      and  b11: "stable prea relya"
      and  b12: "\<forall>s. (s, s) \<in> guara"
    {
      fix c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd
      assume b1: "Pre k \<subseteq> prea"
         and b2: "Rely k \<subseteq> relya"
         and b3: "guara \<subseteq> Guar k"
         and b4: "posta \<subseteq> Post k"
         and p0: "c \<in> cpts_of_pes pes s x"
         and p1: "c \<propto> cs"
         and p8: "c \<in> assume_pes (pre1, rely1)"
         and p2: "(\<forall>k. cs k \<in> cpts_of_es (pes k) s x)"
         and p3: "\<forall>k. (cs k)\<in>commit_es(Guar k, Post k)"
         and a5: "(\<forall>k. pre1 \<subseteq> Pre k)"
         and a6: "(\<forall>k. rely1 \<subseteq> Rely k)"
         and p4: "(\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k)"
         and a0: "evtsys_spec (rgf_EvtSys esf) = EvtSys es \<and> EvtSys es = getspc_es (cs k ! 0) 
                  \<and> (\<forall>e\<in>all_evts_es (rgf_EvtSys esf). is_basicevt (E\<^sub>e e))
                  \<and> (\<forall>e\<in>all_evts_es (rgf_EvtSys esf). the (evtrgfs (E\<^sub>e e)) = snd e)"
         and p6: "(\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c ! j -pes-actk\<rightarrow> c ! Suc j))"
      then have p30: "(\<forall>k. cs k \<in> assume_es (Pre k, Rely k))" 
        using conjoin_comm_imp_rely[of pre1 Pre rely1 Rely Guar cs Post c pes s x] by auto
      with p3 have p31: "(\<forall>k. cs k \<in> commit_es (Guar k, Post k))"
        by (meson IntI contra_subsetD cpts_of_es_def es_validity_def p2) 

      from p1 have p11: "\<forall>k. length (cs k) = length c" by (simp add:conjoin_def same_length_def)
      from p2 have p12: "\<forall>k. cs k \<in> cpts_es" using cpts_of_es_def mem_Collect_eq by fastforce 
      with p11 have "c \<noteq> Nil" using cpts_es_not_empty length_0_conv by auto 
      then have p13: "length c > 0" by auto

      let ?esl = "cs k"
      let ?esys = "EvtSys es"
      
      from p1 p2 a0 have a8: "?esl \<in> cpts_es \<and> ?esl!0 = (EvtSys es,s,x)"
        by (simp add: cpts_of_es_def eq_fst_iff getspc_es_def) 

      then obtain esll where a81: "?esl = (EvtSys es,s,x)#esll"
        by (metis hd_Cons_tl length_greater_0_conv nth_Cons_0 p11 p13) 

      {
        fix i
        assume a3: "Suc i < length (cs k)"
          and  a4: "cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i"
        have "(gets_es (cs k ! i), gets_es (cs k ! Suc i)) \<in> Guar\<^sub>f (the (evtrgfs (getx_es (cs k ! i) k)))"
          proof(cases "\<forall>i. Suc i \<le> length ?esl \<longrightarrow> getspc_es (?esl ! i) = EvtSys es")
              assume c0: "\<forall>i. Suc i \<le> length ?esl \<longrightarrow> getspc_es (?esl ! i) = EvtSys es"
              with a3 have "getspc_es (?esl ! i) = EvtSys es \<and> getspc_es (?esl ! Suc i) = EvtSys es"
                by auto
              with a4 show ?thesis using evtsys_not_eq_in_tran_aux1 by fastforce 
            next
              assume c0: "\<not>(\<forall>i. Suc i \<le> length ?esl \<longrightarrow> getspc_es (?esl ! i) = EvtSys es)"
              then obtain m where c1: "Suc m \<le> length ?esl \<and> getspc_es (?esl ! m) \<noteq> EvtSys es" 
                by auto
              from a8 have c2: "getspc_es (?esl!0) = EvtSys es" by (simp add:getspc_es_def)
              from c1 have "\<exists>i. i \<le> m \<and> getspc_es (?esl ! i) \<noteq> EvtSys es" by auto
              with a8 c1 c2 have "\<exists>i. (i < m \<and> getspc_es (?esl ! i) = EvtSys es 
                        \<and> getspc_es (?esl ! Suc i) \<noteq> EvtSys es) 
                        \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (?esl ! j) = EvtSys es)" 
                using evtsys_fst_ent by blast
              then obtain n where c3: "(n < m \<and> getspc_es (?esl ! n) = EvtSys es 
                        \<and> getspc_es (?esl ! Suc n) \<noteq> EvtSys es) 
                        \<and> (\<forall>j. j < n \<longrightarrow> getspc_es (?esl ! j) = EvtSys es)" by auto
              have c4: "i \<ge> n" 
                proof -
                {
                  assume d0: "i < n"
                  with c3 have "getspc_es (?esl ! i) = EvtSys es" by simp
                  moreover from c3 d0 have "getspc_es (?esl ! Suc i) = EvtSys es"
                    using Suc_lessI by blast 
                  ultimately have "\<not>(\<exists>t. ?esl!i -es-t\<rightarrow> ?esl!Suc i)" 
                    using evtsys_not_eq_in_tran getspc_es_def by (metis surjective_pairing)
                  with a4 have False by simp
                }
                then show ?thesis using leI by auto 
                qed
              
              let ?esl1 = "drop n ?esl"
              let ?eslh = "take (Suc n) ?esl"
              from c1 c3 have c5: "length ?esl1 \<ge> 2"
                by (metis One_nat_def Suc_eq_plus1_left Suc_le_eq length_drop 
                    less_diff_conv less_trans_Suc numeral_2_eq_2)
              from c1 c3 have c6: "getspc_es (?esl1!0) = EvtSys es \<and> getspc_es (?esl1!1) \<noteq> EvtSys es"
                by force

              from a3 a8 c1 c3 c4 have c7: "?esl1 \<in> cpts_es" using cpts_es_dropi
                  by (metis (no_types, lifting) drop_0 dual_order.strict_trans 
                      le_0_eq le_SucE le_imp_less_Suc zero_induct) 
              from c5 c6 c7 have "\<exists>s x ev s1 x1 xs. 
                ?esl1 = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
                  using fst_esys_snd_eseq_exist by blast
              then obtain s0 and x0 and e and s1 and x1 and xs where c8:
                  "?esl1 = (EvtSys es, s0, x0) # (EvtSeq e (EvtSys es), s1,x1) # xs" by auto
              with c3 have c3_1: "(\<forall>j\<le>n. getspc_es (cs k ! j) = EvtSys es)" using getspc_es_def
                using antisym_conv2 by blast 
              let ?elst = "tl (parse_es_cpts_i2 ?esl1 es [[]])"
              from c8 c7 have c9: "concat ?elst = ?esl1" using parse_es_cpts_i2_concat3 by metis 
              
              from a0 have c13: "es = Domain esf" using evtsys_spec_evtsys by auto
              from b5 have c14: "\<forall>i\<in>esf. \<Turnstile> E\<^sub>e i sat\<^sub>e [Pre\<^sub>e i, Rely\<^sub>e i, Guar\<^sub>e i, Post\<^sub>e i]"
                by (simp add: rgsound_e)

              let ?RG = "\<lambda>e. SOME rg. (e,rg)\<in>esf" 
              from c13 have c131: "\<forall>e\<in>es. \<exists>ef\<in>esf. ?RG e = snd ef" by (metis Domain.cases snd_conv someI) 
          
              let ?Pre = "pre_rgf \<circ> ?RG"
              let ?Rely = "rely_rgf \<circ> ?RG"
              let ?Guar = "guar_rgf \<circ> ?RG"
              let ?Post = "post_rgf \<circ> ?RG"

              from c13 c14 have c16: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [?Pre ef, ?Rely ef, ?Guar ef, ?Post ef]" 
                by (metis (mono_tags, lifting) Domain.cases E\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def 
                    Pre\<^sub>e_def Rely\<^sub>e_def comp_apply fst_conv snd_conv someI_ex) 
              moreover
              from b1 b6 have c17: "\<forall>j\<in>es. prea \<subseteq> ?Pre j" using Pre\<^sub>e_def c131 comp_def by metis 
              moreover
              from b2 b7 have c18: "\<forall>j\<in>es. Rely k \<subseteq> ?Rely j" using Rely\<^sub>e_def c131 comp_def by (metis subsetCE subsetI) 
              moreover
              from b3 b8 have c19: "\<forall>j\<in>es. ?Guar j \<subseteq> Guar k" using Guar\<^sub>e_def c131 comp_def by (metis subsetCE subsetI)
              moreover
              from b4 b9 have c20: "\<forall>j\<in>es. ?Post j \<subseteq> Post k" using c131 comp_def
                by (metis Post\<^sub>e_def contra_subsetD subsetI) 
              moreover
              from b5 b10 have c21: "\<forall>ef1 ef2. ef1 \<in> es \<and> ef2 \<in> es \<longrightarrow> ?Post ef1 \<subseteq> ?Pre ef2"
                by (metis Post\<^sub>e_def Pre\<^sub>e_def c131 comp_apply) 
              moreover
              from c1 c3_1 p30 have c24: "?esl1\<in>assume_es (prea, Rely k)"
                proof(cases "n = 0")
                  assume d0: "n = 0"
                  from b1 p30 have "?esl\<in>assume_es(prea,Rely k)" 
                    using assume_es_imp[of "Pre k" prea "Rely k" "Rely k" ?esl] by blast
                  with d0 show ?thesis by auto
                next
                  assume d0: "n \<noteq> 0"
                  from b1 b2 p30 have "?esl\<in>assume_es(prea,relya)" 
                    using assume_es_imp[of "Pre k" prea "Rely k" relya ?esl] by blast
                  then have "?eslh \<in> assume_es(prea,relya)" 
                    using assume_es_take_n[of "Suc n" ?esl prea relya] d0 c1 c3 by auto
                  moreover
                  from c3 have "\<forall>i<length ?eslh. getspc_es (?eslh!i) = EvtSys es"
                    proof -
                      from c3 have "\<forall>i. Suc i<length ?eslh \<longrightarrow> getspc_es (?eslh!i) = EvtSys es"
                        using Suc_le_lessD length_take less_antisym less_imp_le_nat 
                        min.bounded_iff nth_take by auto 
                      moreover
                      from c3 have "getspc_es (last ?eslh) = EvtSys es"
                        by (metis (no_types, lifting) a3 c4 dual_order.strict_trans 
                          getspc_es_def last_snoc le_imp_less_Suc take_Suc_conv_app_nth) 
                      ultimately show ?thesis
                        by (metis Suc_lessI diff_Suc_1 last_conv_nth 
                          length_greater_0_conv nat.distinct(1) p11 p13 take_eq_Nil) 
                    qed
                  ultimately have "\<forall>i<length ?eslh. gets_es (?eslh!i) \<in> prea" 
                    using b11 pre_trans[of ?eslh prea relya "EvtSys es"] by blast
                  moreover
                  from c1 c3 have d1: "Suc n \<le> length ?esl" by auto
                  moreover
                  then have "n < length ?eslh" by auto
                  ultimately have "gets_es (?eslh ! n) \<in> prea" by simp
                  moreover
                  from d1 have "?eslh ! n = ?esl1 ! 0" by (simp add: c8 nth_via_drop) 
                  ultimately have "gets_es (?esl ! n) \<in> prea" by simp
                  with p30 d1 show ?thesis using assume_es_drop_n[of n ?esl "Pre k" "Rely k" prea] by auto
                qed
              ultimately 
              have ri[rule_format]: "\<forall>i. Suc i < length ?elst \<longrightarrow> 
                          (\<exists>m\<in>es. ?elst!i@[(?elst!Suc i)!0]\<in>commit_es(?Guar m,?Post m)
                              \<and> gets_es ((?elst!Suc i)!0) \<in> ?Post m
                            \<and> (\<exists>k. (?elst!i@[(?elst!Suc i)!0])!0-es-(EvtEnt m)\<sharp>k\<rightarrow>(?elst!i@[(?elst!Suc i)!0])!1))"
                  using EventSys_sound_aux_i[of es ?Pre ?Rely ?Guar ?Post
                      "prea" "Rely k" "Guar k" "Post k" ?esl1 s0 x0 e s1 x1 xs ?elst]
                      c7 c8 by force

              from c16 c17 c18 c19 c20 c21 c24
              have ri_forall[rule_format]: 
                "\<forall>i. Suc i < length ?elst \<longrightarrow> 
                    (\<forall>ei\<in>es. (\<exists>k. (?elst!i@[(?elst!Suc i)!0])!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>(?elst!i@[(?elst!Suc i)!0])!1) 
                                  \<longrightarrow> ?elst!i@[(?elst!Suc i)!0]\<in>commit_es(?Guar ei,?Post ei)
                                    \<and> gets_es ((?elst!Suc i)!0) \<in> ?Post ei)"
                  using EventSys_sound_aux_i_forall[of es ?Pre ?Rely ?Guar ?Post
                      "prea" "Rely k" "Guar k" "Post k" ?esl1 s0 x0 e s1 x1 xs ?elst] 
                      c7 c8 by simp
                      

              from c16 c17 c18 c19 c20 c21 b10 c7 c8 c24
              have rl_forall: "\<forall>ei\<in>es. (\<exists>k. (last ?elst)!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>(last ?elst)!1)
                            \<longrightarrow> last ?elst\<in>commit_es(?Guar ei,?Post ei)"
                  using EventSys_sound_aux_last_forall[of es ?Pre ?Rely ?Guar ?Post
                      "prea" "Rely k" "Guar k" "Post k" ?esl1 s0 x0 e s1 x1 xs ?elst] by simp
                      

              from c16 c17 c18 c19 c20 c21 b10 c7 c8 c24
              have rl: "\<exists>m\<in>es. last ?elst\<in>commit_es(?Guar m,?Post m) 
                        \<and> (\<exists>k. (last ?elst)!0-es-(EvtEnt m)\<sharp>k\<rightarrow>(last ?elst)!1)"
                  using EventSys_sound_aux_last[of es ?Pre ?Rely ?Guar ?Post
                      "prea" "Rely k" "Guar k" "Post k" ?esl1 s0 x0 e s1 x1 xs ?elst] by simp
                      

              from c8 c7 have no_mident[rule_format]: "\<forall>i. i < length ?elst \<longrightarrow> 
                             \<not>(\<exists>j. j > 0 \<and> Suc j < length (?elst!i) \<and> 
                             getspc_es (?elst!i!j) = EvtSys es \<and> getspc_es (?elst!i!Suc j) \<noteq> EvtSys es)"
                 using parse_es_cpts_i2_noent_mid[of ?esl1 es s0 x0 e s1 x1 xs "parse_es_cpts_i2 ?esl1 es [[]]"]
                  by simp

              from c8 c7 have no_mident_i[rule_format]: "\<forall>i. Suc i < length ?elst \<longrightarrow> 
                             \<not>(\<exists>j. j > 0 \<and> Suc j < length (?elst!i@[?elst!Suc i!0]) \<and> 
                             getspc_es ((?elst!i@[?elst!Suc i!0])!j) = EvtSys es \<and> getspc_es ((?elst!i@[?elst!Suc i!0])!Suc j) \<noteq> EvtSys es)"
                 by (metis parse_es_cpts_i2_noent_mid_i)
              

              have in_cpts_i[rule_format]: "\<forall>i. Suc i < length ?elst \<longrightarrow> (?elst!i)@[?elst!Suc i!0] \<in>cpts_es"
                using parse_es_cpts_i2_in_cptes_i[of ?esl1 es s0 x0 e s1 x1 xs ?elst] c7 c8
                  by simp
              
              have in_cpts_last: "last ?elst \<in>cpts_es"
                using parse_es_cpts_i2_in_cptes_last[of ?esl1 es s0 x0 e s1 x1 xs ?elst] c7 c8
                  by simp

              then have in_cpts_last1: "?elst ! (length ?elst - 1) \<in> cpts_es"
                by (metis c7 c9 concat.simps(1) cpts_es_not_empty last_conv_nth) 
                
              from c5 c8 c7 have len_start_elst[rule_format]: 
                "\<forall>i<length ?elst. length (?elst!i) \<ge> 2 \<and> getspc_es (?elst!i!0) = EvtSys es 
                                  \<and> getspc_es (?elst!i!1) \<noteq> EvtSys es" 
                using parse_es_cpts_i2_start_aux[of ?esl1 es s0 x0 e s1 x1 xs "parse_es_cpts_i2 ?esl1 es [[]]"]
                  by fastforce

              then have c30: "\<forall>i. Suc i < length ?esl1 
                      \<longrightarrow> (\<exists>k j. (Suc k < length ?elst \<and> Suc j < length (?elst!k@[(?elst!Suc k)!0]) \<and> 
                                  ?esl1!i = (?elst!k@[(?elst!Suc k)!0])!j \<and> ?esl1!Suc i = (?elst!k@[(?elst!Suc k)!0])!Suc j) 
                              \<or> (Suc k = length ?elst \<and> Suc j < length (?elst!k) \<and> 
                                  ?esl1!i = ?elst!k!j \<and> ?esl1!Suc i = ?elst!k!Suc j))" 
                  using c9 concat_list_lemma[of ?esl1 ?elst] by fastforce
              
              from p12 a3 have c33[rule_format]: "\<forall>i. i < length ?esl 
                \<longrightarrow> getspc_es (?esl!i) = EvtSys es \<or> (\<exists>e. getspc_es (?esl!i) = EvtSeq e (EvtSys es) \<and> is_anonyevt e)"
                using evtsys_all_es_in_cpts_anony[of ?esl es]
                  c2 gr0I gr_implies_not0 by blast 

              from a3 c4 have c34: "?esl!i = ?esl1!(i - n)"
                using Suc_lessD add_diff_inverse_nat leD less_imp_le_nat nth_drop by auto 
              from a3 c4 have c340: "?esl!Suc i = ?esl1!(Suc (i - n))"
                using Suc_lessD add_diff_inverse_nat leD less_imp_le_nat nth_drop by auto 
              from a3 c4 have "Suc (i - n) < length ?esl1"
                by (simp add: Suc_diff_le diff_less_mono le_SucI) 
              with c30 have "\<exists>k j. (Suc k < length ?elst \<and> Suc j < length (?elst!k@[(?elst!Suc k)!0]) \<and> 
                                  ?esl1!(i - n) = (?elst!k@[(?elst!Suc k)!0])!j \<and> ?esl1!Suc (i - n) = (?elst!k@[(?elst!Suc k)!0])!Suc j) 
                              \<or> (Suc k = length ?elst \<and> Suc j < length (?elst!k) \<and> 
                                  ?esl1!(i - n) = ?elst!k!j \<and> ?esl1!Suc (i - n) = ?elst!k!Suc j)"
                  by auto
              then obtain kk and j where c35: "(Suc kk < length ?elst \<and> Suc j < length (?elst!kk@[(?elst!Suc kk)!0]) \<and> 
                                  ?esl1!(i - n) = (?elst!kk@[(?elst!Suc kk)!0])!j \<and> ?esl1!Suc (i - n) = (?elst!kk@[(?elst!Suc kk)!0])!Suc j) 
                              \<or> (Suc kk = length ?elst \<and> Suc j < length (?elst!kk) \<and> 
                                  ?esl1!(i - n) = ?elst!kk!j \<and> ?esl1!Suc (i - n) = ?elst!kk!Suc j)"
                 by auto
              let ?elstk = "?elst!kk@[(?elst!Suc kk)!0]"
              have c36: "length ?elstk > 2" using len_start_elst[of kk] c35
                by (metis Suc_lessD le_imp_less_Suc length_append_singleton lessI)

              let ?elstl = "?elst!kk"
              have c37: "length ?elstl \<ge> 2" using len_start_elst[of kk] c35
                by (metis Suc_lessD lessI)

              from c35 have c38: "Suc kk \<le> length ?elst" using less_or_eq_imp_le by blast 

              from c38 have "\<not>(\<exists>j. j > 0 \<and> Suc j < length (?elst!kk) \<and> 
                         getspc_es (?elst!kk!j) = EvtSys es \<and> getspc_es (?elst!kk!Suc j) \<noteq> EvtSys es)" 
                 using no_mident by auto
              then have d1: "\<forall>j. j > 0 \<and> Suc j < length (?elst!kk) \<longrightarrow> getspc_es ((?elst!kk) ! j) = EvtSys es 
                      \<longrightarrow> getspc_es ((?elst!kk) ! Suc j) = EvtSys es" using noevtent_inmid_eq by auto

              have d43: "length ?esl = n + length ?esl1"
                    using \<open>Suc (i - n) < length (drop n (cs k))\<close> by auto 

              from c35 show ?thesis
                proof
                  assume d0: "(Suc kk < length ?elst \<and> Suc j < length ?elstk \<and> 
                             ?esl1!(i - n) = ?elstk!j \<and> ?esl1!Suc (i - n) = ?elstk!Suc j)"
                  
                  have d01: "j \<noteq> 0"
                    proof
                      assume e0: "j = 0"
                      with len_start_elst[of kk] have e1: "getspc_es (?elstk!j) = EvtSys es 
                            \<and> getspc_es (?elstk!Suc j) \<noteq> EvtSys es"
                         by (metis (no_types, hide_lams) One_nat_def Suc_1 Suc_le_lessD c34 d0 less_imp_le_nat nth_append)
                      moreover
                      from a4 have "\<not>(\<exists>ess. getspc_es (?esl ! i) = EvtSys ess)" 
                        using cmd_enable_impl_notesys2[of "?esl ! i" cmd k "?esl ! Suc i"] by simp
                      moreover
                      from d0 have "?esl!i = ?elstk!j"
                        by (simp add: c34) 
                      ultimately show False by simp
                    qed

                  
                  have d1_1: "\<forall>ii. ii > 0 \<and> Suc ii < length ?elstk 
                        \<longrightarrow> \<not>(\<exists>e. (?elstk!ii) -es-((EvtEnt e)\<sharp>k)\<rightarrow> (?elstk!(Suc ii)))"
                    proof -
                    {
                      fix ii
                      assume e0: "ii > 0 \<and> Suc ii < length ?elstk"
                      have "\<not>(\<exists>e. (?elstk!ii) -es-((EvtEnt e)\<sharp>k)\<rightarrow> (?elstk!(Suc ii)))"
                        proof(cases "getspc_es (?elstk!ii) = EvtSys es")
                          assume f0: "getspc_es (?elstk!ii) = EvtSys es"
                          with d1 d0 have "getspc_es (?elstk!(Suc ii)) = EvtSys es"
                            by (smt Suc_lessI Suc_less_eq c7 c8 e0 length_append_singleton 
                              nth_append nth_append_length parse_es_cpts_i2_start_aux) 
                          with f0 show ?thesis
                            using evtsys_not_eq_in_tran_aux1 by fastforce 
                        next
                          assume f0: "getspc_es (?elstk!ii) \<noteq> EvtSys es"
                          from d0 e0 in_cpts_i[of kk] have f1: "?elstk \<in> cpts_es" by simp
                          moreover
                          from d0 f1 len_start_elst[of kk] have 
                            "length ?elstk > 0 \<and> getspc_es (?elstk!0) = EvtSys es" 
                            by (metis (no_types, lifting) Suc_lessD cpts_es_not_empty length_greater_0_conv 
                                list.size(3) not_numeral_le_zero nth_append)
                          ultimately have "\<exists>e. getspc_es (?elstk!ii) = EvtSeq e (EvtSys es) 
                                            \<and> is_anonyevt e" 
                            using evtsys_all_es_in_cpts_anony[of ?elstk es] e0 f0 Suc_lessD by blast 
                          then show ?thesis using incpts_es_eseq_not_evtent[of ?elstk ii] 
                            in_cpts_i[of kk] d0 e0 by blast
                        qed
                    }
                    then show ?thesis by auto
                    qed

                  have d2: "getspc_es (?elstk!0) = EvtSys es \<and> getspc_es (?elstk!1) \<noteq> EvtSys es"
                    using len_start_elst[of 0] by (metis (no_types, hide_lams) One_nat_def 
                      Suc_1 Suc_le_lessD Suc_lessD d0 len_start_elst nth_append) 

                  from c9 d0 len_start_elst 
                    have "\<exists>si ti. si = length (concat (take kk ?elst)) \<and> ti = Suc (length (concat (take (Suc kk) ?elst))) \<and>
                      si \<le> length ?esl1 \<and> ti < length ?esl1 \<and> si < ti \<and> drop si (take ti ?esl1) = ?elstk"
                    using concat_list_lemma_withnextfst3[of ?esl1 ?elst kk]
                      Suc_1 Suc_le_lessD by presburger
                  then obtain si and ti where d4: "si = length (concat (take kk ?elst)) 
                      \<and> ti = Suc (length (concat (take (Suc kk) ?elst))) 
                      \<and> si \<le> length ?esl1 \<and> ti < length ?esl1 
                      \<and> si < ti \<and> drop si (take ti ?esl1) = ?elstk" by auto
                  then have d42: "si + (length ?elstk) = ti" 
                    using drop_take_eq[of ?elstk si ti ?esl1 "length ?elstk"] c36
                      by (metis cpts_es_not_empty d0 in_cpts_i length_greater_0_conv less_imp_le_nat) 

                  from d4 have "ti < length ?esl1" by simp
                  with d43 have d41: "n + ti < length ?esl" by simp

                  from d4 have d5: "?elstk = drop (si+n) (take (ti+n) ?esl)"
                    by (metis (no_types, lifting) drop_drop take_drop)
                  then have d6: "?elstk!0 = ?esl!(si+n)" 
                    by (metis (no_types, lifting) Nat.add_0_right 
                        append_is_Nil_conv append_take_drop_id drop_eq_Nil 
                        leI nat_le_linear not_Cons_self2 nth_append nth_drop)
                  
                  from d5 have "?elstk!1 = drop (si+n) (take (ti+n) ?esl) ! 1" by simp
                  moreover
                  from d0 d5 have "drop (si+n) (take (ti+n) ?esl) ! 1 = ?esl!(Suc (si+n))"
                    by (metis add.commute add_lessD1 drop_take_sametrace plus_1_eq_Suc)
                  ultimately have d7: "?elstk!1 = ?esl!(Suc (si+n))" by simp

                  
                  from c36 d4 have d71: "ti > si + 2" using drop_take_ln[of ?elstk si ti ?esl1 2] by fastforce
                  with c1 c3 d4 have d72: "Suc (si+n) < length ?esl"
                    proof -
                      have "si + 2 < length (cs k) - n"
                        using \<open>ti < length (drop n (cs k))\<close> d71 by auto 
                      then have "Suc (Suc (si + n)) < length (cs k)"
                        by linarith
                      then show ?thesis
                        by (metis Suc_le_lessD order.strict_implies_order)
                    qed

                  with p1 d2 d6 d7 have "\<exists>e. ?esl!(si+n) -es-((EvtEnt e)\<sharp>k)\<rightarrow> ?esl!(Suc (si+n))"
                    using entevt_in_conjoin_cpts[of c cs "si+n" k es] by simp
                  then obtain ente where d8: "?esl!(si+n) -es-((EvtEnt ente)\<sharp>k)\<rightarrow> ?esl!(Suc (si+n))" by auto
                  with d2 d6 have "\<exists>ei\<in>es. ente = ei" 
                    using evtsysent_evtent3[of "?esl!(si+n)" ente k "?esl!(Suc (si+n))" es] by auto
                  then obtain ei where d9: "ei\<in>es \<and> ente = ei" by auto

                  from ri_forall[of kk ei] d0 d6 d7 d8 d9 
                    have d10: "?elstk \<in> commit_es(?Guar ei,?Post ei)" by auto
                  
                  from d0 have d11: "cs k ! i = ?elstk ! j" by (simp add: c34)
                  moreover
                  from d0 have d12: "cs k ! Suc i = ?elstk ! Suc j" by (simp add: c340)
                  ultimately have d13: "?elstk ! j -es-Cmd cmd\<sharp>k\<rightarrow> ?elstk ! Suc j" using a4 by auto

                  have d14: "(gets_es (?elstk ! j), gets_es (?elstk ! Suc j)) \<in> ?Guar ei"
                    proof -
                      from d10 have "\<forall>i. Suc i<length ?elstk \<longrightarrow> 
                              (\<exists>t. ?elstk!i -es-t\<rightarrow> ?elstk!(Suc i)) \<longrightarrow> 
                                  (gets_es (?elstk!i), gets_es (?elstk!Suc i)) \<in> ?Guar ei"
                        by (simp add:commit_es_def)
                      with d0 d13 show ?thesis by auto
                    qed

                  with d11 d12 have d15: "(gets_es (cs k ! i), gets_es (cs k ! Suc i)) \<in> ?Guar ei" 
                    by simp


                  from d0 no_mident_i[of kk] have "\<not>(\<exists>m. m > 0 \<and> Suc m < length ?elstk \<and> 
                             getspc_es (?elstk!m) = EvtSys es \<and> getspc_es (?elstk!Suc m) \<noteq> EvtSys es)"
                    by simp
                  then have d16[rule_format]: "\<forall>m. m > 0 \<and> Suc m < length ?elstk 
                      \<longrightarrow> \<not>(getspc_es (?elstk!m) = EvtSys es \<and> getspc_es (?elstk!Suc m) \<noteq> EvtSys es)"
                    by auto
                  have d17: "\<forall>m. m > (si + n) \<and> m < ti + n - 1 \<longrightarrow> 
                             \<not>(getspc_es (?esl!m) = EvtSys es \<and> getspc_es (?esl!Suc m) \<noteq> EvtSys es)"
                    proof -
                    {
                      fix m
                      assume e0: "m > (si + n) \<and> m < ti + n - 1"
                      then have e1: "m - (n+si) > 0" by auto
                      moreover
                      have e2: "Suc (m - (n+si)) < length ?elstk" 
                        proof -
                          from e0 have "m - (n + si) < ti - si - 1" by auto
                          then have "Suc (m - (n + si)) < ti - si" by auto
                          with d42 show ?thesis by auto
                        qed
                      ultimately have "\<not>(getspc_es (?elstk!(m-(n+si))) = EvtSys es 
                          \<and> getspc_es (?elstk!Suc (m-(n+si))) \<noteq> EvtSys es)"
                        using d16[of "m - (n+si)"] by simp
                      moreover
                      from e1 e2 d5 have "?esl!m = ?elstk!(m - (n+si))"
                        using drop_take_sametrace[of ?elstk "si+n" "ti+n" ?esl "m - (n+si)"] by auto
                      moreover
                      from e1 e2 d5 have "?esl!Suc m = ?elstk!Suc (m - (n+si))"
                        using drop_take_sametrace[of ?elstk "si+n" "ti+n" ?esl "Suc (m - (n+si))"] by auto
                      ultimately have "\<not>(getspc_es (?esl!m) = EvtSys es \<and> getspc_es (?esl!Suc m) \<noteq> EvtSys es)"
                        by simp
                    }
                    then show ?thesis by auto
                    qed
                  have d18: "\<forall>m. m > (si + n) \<and> m < ti + n - 1 \<longrightarrow> 
                             \<not>(\<exists>e. ?esl!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> ?esl!Suc m)"
                    proof -
                    {
                      fix m
                      assume e0: "m > (si + n) \<and> m < ti + n - 1"
                      with d17 have "\<not>(getspc_es (?esl!m) = EvtSys es \<and> getspc_es (?esl!Suc m) \<noteq> EvtSys es)" 
                        by auto
                      with p1 a8 a81 d41 e0 have "\<not>(\<exists>e. ?esl!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> ?esl!Suc m)" 
                        using notentevt_in_conjoin_cpts[of c cs m k es] evtsys_allevtseqorevtsys[of ?esl es s x esll]
                          by auto
                    }
                    then show ?thesis by auto
                    qed
                  
                  from d71 have "Suc (si + n) < ti + n - 1"
                    using Suc_eq_plus1 add.assoc add_2_eq_Suc add_diff_cancel_right' less_diff_conv by linarith
                  moreover
                  from d41 have "Suc (ti + n - 1) < length (cs k)" using calculation d41 by linarith
                  ultimately 
                  have d19[rule_format]:"\<forall>m. m > (si + n) \<and> m \<le> (ti + n - 1) \<longrightarrow> getx_es ((cs k)!m) k = ente" 
                    using evtent_impl_curevt_in_cpts_es[of c cs "si + n" k ente "ti + n - 1"]
                       d18 p1 p6 d8 d41 d71 d72 by auto
                  from d0 d42 have "si + n + j \<le> ti + n - 1" by auto
                  with d19[of "si + n + j"] d01 have "getx_es ((cs k)!(si + n + j)) k = ente" by auto
                  with d11 d5 have "getx_es ((cs k)!i) k = ente"
                    by (metis Suc_lessD d0 drop_take_sametrace) 
                  moreover
                  from a0 have "the (evtrgfs (ei)) = (?RG ei)" 
                    using all_evts_es_esys d9 c13 c131 by (metis Domain.cases E\<^sub>e_def prod.sel(1) snd_conv someI_ex) 
                  moreover
                  from d9 c13 c131 have "?Guar ei = Guar\<^sub>f (?RG ei)" by (simp add: Guar\<^sub>f_def)
                  ultimately show ?thesis using d15 d9 by simp
                next
                  assume d0: "Suc kk = length ?elst \<and> Suc j < length ?elstl \<and> 
                              ?esl1!(i - n) = ?elstl!j \<and> ?esl1!Suc (i - n) = ?elstl!Suc j"
                  have d01: "j \<noteq> 0"
                    proof
                      assume e0: "j = 0"
                      with len_start_elst[of kk] have e1: "getspc_es (?elstl!j) = EvtSys es 
                            \<and> getspc_es (?elstl!Suc j) \<noteq> EvtSys es"
                         using One_nat_def d0 lessI by fastforce
                      moreover
                      from a4 have "\<not>(\<exists>ess. getspc_es (?esl ! i) = EvtSys ess)" 
                        using cmd_enable_impl_notesys2[of "?esl ! i" cmd k "?esl ! Suc i"] by simp
                      moreover
                      from d0 have "?esl!i = ?elstl!j"
                        by (simp add: c34) 
                      ultimately show False by simp
                    qed

                  
                  have d1_1: "\<forall>ii. ii > 0 \<and> Suc ii < length ?elstl 
                        \<longrightarrow> \<not>(\<exists>e. (?elstl!ii) -es-((EvtEnt e)\<sharp>k)\<rightarrow> (?elstl!(Suc ii)))"
                    proof -
                    {
                      fix ii
                      assume e0: "ii > 0 \<and> Suc ii < length ?elstl"
                      have "\<not>(\<exists>e. (?elstl!ii) -es-((EvtEnt e)\<sharp>k)\<rightarrow> (?elstl!(Suc ii)))"
                        proof(cases "getspc_es (?elstl!ii) = EvtSys es")
                          assume f0: "getspc_es (?elstl!ii) = EvtSys es"
                          with d1 d0 have "getspc_es (?elstl!(Suc ii)) = EvtSys es"
                            by (smt Suc_lessI Suc_less_eq c7 c8 e0 length_append_singleton 
                              nth_append nth_append_length parse_es_cpts_i2_start_aux) 
                          with f0 show ?thesis
                            using evtsys_not_eq_in_tran_aux1 by fastforce 
                        next
                          assume f0: "getspc_es (?elstl!ii) \<noteq> EvtSys es"
                          from d0 have f1: "Suc kk = length ?elst" by simp
                          with in_cpts_last1 have f2: "?elstl \<in> cpts_es"
                            by (metis diff_Suc_1) 
                          moreover
                          from f1 len_start_elst[of kk] have 
                            "length ?elstl > 0 \<and> getspc_es (?elstl!0) = EvtSys es"
                              using Suc_le_lessD c38 d0 gr_implies_not0 by blast 
                          ultimately have "\<exists>e. getspc_es (?elstl!ii) = EvtSeq e (EvtSys es) 
                                            \<and> is_anonyevt e" 
                            using evtsys_all_es_in_cpts_anony[of ?elstl es] e0 f0 Suc_lessD by blast 
                          then show ?thesis using incpts_es_eseq_not_evtent[of ?elstl ii] 
                            in_cpts_last1 f2 d0 e0 by blast
                        qed
                    }
                    then show ?thesis by auto
                    qed

                  from d0 have d2: "getspc_es (?elstl!0) = EvtSys es \<and> getspc_es (?elstl!1) \<noteq> EvtSys es"
                    using len_start_elst[of kk] by auto

                  from c9 d0 len_start_elst[of kk]
                    have "\<exists>si ti. si = length (concat (take kk ?elst)) \<and> ti = length (concat (take (Suc kk) ?elst)) \<and>
                      si \<le> length ?esl1 \<and> ti \<le> length ?esl1 \<and> si < ti \<and> drop si (take ti ?esl1) = ?elstl"
                    using concat_list_lemma3[of ?esl1 ?elst kk]
                      using Suc_1 Suc_le_lessD c38 by presburger

                  then obtain si and ti where d4: "si = length (concat (take kk ?elst)) 
                      \<and> ti = length (concat (take (Suc kk) ?elst)) 
                      \<and> si \<le> length ?esl1 \<and> ti \<le> length ?esl1 \<and> si < ti 
                      \<and> drop si (take ti ?esl1) = ?elstl" by auto
                  then have d42: "si + (length ?elstl) = ti" 
                    using drop_take_eq[of ?elstl si ti ?esl1 "length ?elstl"] c37
                      by (metis d0 gr_implies_not0 not_gr0)

                  from d0 d4 have "ti = length ?esl1" by (simp add: c38 c9)
                  with d43 have d41: "n + ti = length ?esl" by simp

                  from d4 have d5: "?elstl = drop (si+n) (take (ti+n) ?esl)"
                    by (metis (no_types, lifting) drop_drop take_drop)
                  then have d6: "?elstl!0 = ?esl!(si+n)"
                    by (metis Cons_nth_drop_Suc \<open>ti = length (drop n (cs k))\<close> d4 
                      drop_drop drop_eq_Nil linorder_not_less nth_Cons_0 take_all) 
                  
                  from d5 have "?elstl!1 = drop (si+n) (take (ti+n) ?esl) ! 1" by simp
                  moreover
                  from d0 d5 have "drop (si+n) (take (ti+n) ?esl) ! 1 = ?esl!(Suc (si+n))"
                    by (simp add: drop_take_sametrace)

                  ultimately have d7: "?elstl!1 = ?esl!(Suc (si+n))" by simp

                  from c37 d4 have d71: "ti > si + 2" using drop_take_ln[of ?elstl si ti ?esl1 2]
                    by (metis Suc_inject d0 d01 le_eq_less_or_eq less_2_cases nat.distinct(1)) 
                  with c1 c3 d4 have d72: "Suc (si+n) < length ?esl"
                    using Suc_leI Suc_n_not_le_n add.commute add_2_eq_Suc' add_Suc_right
                      d41 leI le_antisym less_trans_Suc nat_add_left_cancel_less 
                      nat_le_linear not_less by linarith

                  with p1 d2 d6 d7 have "\<exists>e. ?esl!(si+n) -es-((EvtEnt e)\<sharp>k)\<rightarrow> ?esl!(Suc (si+n))"
                    using entevt_in_conjoin_cpts[of c cs "si+n" k es] by simp
                  then obtain ente where d8: "?esl!(si+n) -es-((EvtEnt ente)\<sharp>k)\<rightarrow> ?esl!(Suc (si+n))" by auto
                  with d2 d6 have "\<exists>ei\<in>es. ente = ei" 
                    using evtsysent_evtent3[of "?esl!(si+n)" ente k "?esl!(Suc (si+n))" es] by auto
                  then obtain ei where d9: "ei\<in>es \<and> ente = ei" by auto

                  from d0 d6 d7 d8 d9 
                    have d10: "?elstl \<in> commit_es(?Guar ei,?Post ei)"
                      by (metis c7 c9 concat.simps(1) cpts_es_not_empty diff_Suc_1 last_conv_nth rl_forall)
                  
                  from d0 have d11: "cs k ! i = ?elstl ! j" by (simp add: c34)
                  moreover
                  from d0 have d12: "cs k ! Suc i = ?elstl ! Suc j" by (simp add: c340)
                  ultimately have d13: "?elstl ! j -es-Cmd cmd\<sharp>k\<rightarrow> ?elstl ! Suc j" using a4 by auto

                  have d14: "(gets_es (?elstl ! j), gets_es (?elstl ! Suc j)) \<in> ?Guar ei"
                    proof -
                      from d10 have "\<forall>i. Suc i<length ?elstl \<longrightarrow> 
                              (\<exists>t. ?elstl!i -es-t\<rightarrow> ?elstl!(Suc i)) \<longrightarrow> 
                                  (gets_es (?elstl!i), gets_es (?elstl!Suc i)) \<in> ?Guar ei"
                        by (simp add:commit_es_def)
                      with d0 d13 show ?thesis by auto
                    qed

                  with d11 d12 have d15: "(gets_es (cs k ! i), gets_es (cs k ! Suc i)) \<in> ?Guar ei" 
                    by simp

                  from d0 no_mident[of kk] have "\<not>(\<exists>m. m > 0 \<and> Suc m < length ?elstl \<and> 
                             getspc_es (?elstl!m) = EvtSys es \<and> getspc_es (?elstl!Suc m) \<noteq> EvtSys es)"
                    by simp
                  then have d16[rule_format]: "\<forall>m. m > 0 \<and> Suc m < length ?elstl 
                      \<longrightarrow> \<not>(getspc_es (?elstl!m) = EvtSys es \<and> getspc_es (?elstl!Suc m) \<noteq> EvtSys es)"
                    by auto
                  have d17: "\<forall>m. m > (si + n) \<and> m < ti + n - 1 \<longrightarrow> 
                             \<not>(getspc_es (?esl!m) = EvtSys es \<and> getspc_es (?esl!Suc m) \<noteq> EvtSys es)"
                    proof -
                    {
                      fix m
                      assume e0: "m > (si + n) \<and> m < ti + n - 1"
                      then have e1: "m - (n+si) > 0" by auto
                      moreover
                      have e2: "Suc (m - (n+si)) < length ?elstl" 
                        proof -
                          from e0 have "m - (n + si) < ti - si - 1" by auto
                          then have "Suc (m - (n + si)) < ti - si" by auto
                          with d42 show ?thesis by auto
                        qed
                      ultimately have "\<not>(getspc_es (?elstl!(m-(n+si))) = EvtSys es 
                          \<and> getspc_es (?elstl!Suc (m-(n+si))) \<noteq> EvtSys es)"
                        using d16[of "m - (n+si)"] by simp
                      moreover
                      from e1 e2 d5 have "?esl!m = ?elstl!(m - (n+si))"
                        using drop_take_sametrace[of ?elstl "si+n" "ti+n" ?esl "m - (n+si)"] by auto
                      moreover
                      from e1 e2 d5 have "?esl!Suc m = ?elstl!Suc (m - (n+si))"
                        using drop_take_sametrace[of ?elstl "si+n" "ti+n" ?esl "Suc (m - (n+si))"] by auto
                      ultimately have "\<not>(getspc_es (?esl!m) = EvtSys es \<and> getspc_es (?esl!Suc m) \<noteq> EvtSys es)"
                        by simp
                    }
                    then show ?thesis by auto
                    qed

                  have d18: "\<forall>m. m > (si + n) \<and> m < ti + n - 1 \<longrightarrow> 
                             \<not>(\<exists>e. ?esl!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> ?esl!Suc m)"
                    proof -
                    {
                      fix m
                      assume e0: "m > (si + n) \<and> m < ti + n - 1"
                      with d17 have "\<not>(getspc_es (?esl!m) = EvtSys es \<and> getspc_es (?esl!Suc m) \<noteq> EvtSys es)" 
                        by auto
                      with p1 a8 a81 d41 e0 have "\<not>(\<exists>e. ?esl!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> ?esl!Suc m)" 
                        using notentevt_in_conjoin_cpts[of c cs m k es] evtsys_allevtseqorevtsys[of ?esl es s x esll]
                          by auto
                    }
                    then show ?thesis by auto
                    qed
                  
                  from d71 have "Suc (si + n) < ti + n - 1"
                    using Suc_eq_plus1 add.assoc add_2_eq_Suc add_diff_cancel_right' less_diff_conv by linarith
                  moreover
                  from d41 have "Suc (ti + n - 1) = length (cs k)" using calculation d41 by linarith
                  ultimately 
                  have d19[rule_format]:"\<forall>m. m > (si + n) \<and> m \<le> (ti + n - 1) \<longrightarrow> getx_es ((cs k)!m) k = ente" 
                    using evtent_impl_curevt_in_cpts_es1[of c cs "si + n" k ente "ti + n - 1"]
                       d18 p1 p6 d8 d41 d71 d72 by auto
                  from d0 d42 have "si + n + j \<le> ti + n - 1" by auto
                  with d19[of "si + n + j"] d01 have "getx_es ((cs k)!(si + n + j)) k = ente" by auto
                  with d11 d5 have "getx_es ((cs k)!i) k = ente"
                    by (metis Suc_lessD d0 drop_take_sametrace) 
                  moreover
                  from a0 have "the (evtrgfs (ei)) = (?RG ei)" 
                    using all_evts_es_esys d9 c13 c131 by (metis Domain.cases E\<^sub>e_def prod.sel(1) snd_conv someI_ex) 
                  moreover
                  from d9 c13 c131 have "?Guar ei = Guar\<^sub>f (?RG ei)" by (simp add: Guar\<^sub>f_def)
                  ultimately show ?thesis using d15 d9 by simp
                qed
            qed
      }
      then have "\<forall>i. Suc i < length (cs k) \<and> cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i \<longrightarrow>
               (gets_es (cs k ! i), gets_es (cs k ! Suc i)) \<in> Guar\<^sub>f (the (evtrgfs (getx_es (cs k ! i) k)))" by auto
    }
    then show "\<forall>c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd.
          Pre k \<subseteq> prea \<and> Rely k \<subseteq> relya \<and> guara \<subseteq> Guar k \<and> posta \<subseteq> Post k \<longrightarrow>
          c \<in> cpts_of_pes pes s x \<and> c \<propto> cs \<and> c \<in> assume_pes (pre1, rely1) \<longrightarrow>
          (\<forall>k. cs k \<in> cpts_of_es (pes k) s x) \<longrightarrow>
          (\<forall>k. (cs k)\<in>commit_es(Guar k, Post k)) \<longrightarrow>
          (\<forall>k. pre1 \<subseteq> Pre k) \<longrightarrow>
          (\<forall>k. rely1 \<subseteq> Rely k) \<longrightarrow>
          (\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k) \<longrightarrow>
          evtsys_spec (rgf_EvtSys esf) = EvtSys es \<and> EvtSys es = getspc_es (cs k ! 0) \<longrightarrow>
          (\<forall>e\<in>all_evts_es (rgf_EvtSys esf). is_basicevt (E\<^sub>e e)) \<longrightarrow>
          (\<forall>e\<in>all_evts_es (rgf_EvtSys esf). the (evtrgfs (E\<^sub>e e)) = snd e) \<longrightarrow>
          (\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c ! j -pes-actk\<rightarrow> c ! Suc j)) \<longrightarrow>
          (\<forall>i. Suc i < length (cs k) \<and> cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i \<longrightarrow>
               (gets_es (cs k ! i), gets_es (cs k ! Suc i)) \<in> Guar\<^sub>f (the (evtrgfs (getx_es (cs k ! i) k))))" by fastforce
  }
  next
  {
    fix prea pre' relya rely' guar' guara post' posta esys
    assume p0: "\<turnstile> (esspc::('l,'k,'s) rgformula_ess) sat\<^sub>s [pre, rely, guar, post]"
       and p1: "prea \<subseteq> pre'"
       and p2: "relya \<subseteq> rely'"
       and p3: "guar' \<subseteq> guara"
       and p4: "post' \<subseteq> posta"
       and p5: "\<turnstile> esys sat\<^sub>s [pre', rely', guar', post']"
       and p6[rule_format]: "\<forall>c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd.
          Pre k \<subseteq> pre' \<and> Rely k \<subseteq> rely' \<and> guar' \<subseteq> Guar k \<and> post' \<subseteq> Post k \<longrightarrow>
          c \<in> cpts_of_pes pes s x \<and> c \<propto> cs \<and> c \<in> assume_pes (pre1, rely1) \<longrightarrow>
          (\<forall>k. cs k \<in> cpts_of_es (pes k) s x) \<longrightarrow>
          (\<forall>k. (cs k)\<in>commit_es(Guar k, Post k)) \<longrightarrow>
          (\<forall>k. pre1 \<subseteq> Pre k) \<longrightarrow>
          (\<forall>k. rely1 \<subseteq> Rely k) \<longrightarrow>
          (\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k) \<longrightarrow>
          evtsys_spec esys = EvtSys es \<and> EvtSys es = getspc_es (cs k ! 0) \<longrightarrow>
          (\<forall>e\<in>all_evts_es esys. is_basicevt (E\<^sub>e e)) \<longrightarrow>
          (\<forall>e\<in>all_evts_es esys. the (evtrgfs (E\<^sub>e e)) = snd e) \<longrightarrow>
          (\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c ! j -pes-actk\<rightarrow> c ! Suc j)) \<longrightarrow>
          (\<forall>i. Suc i < length (cs k) \<and> cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i \<longrightarrow>
               (gets_es (cs k ! i), gets_es (cs k ! Suc i)) \<in> Guar\<^sub>f (the (evtrgfs (getx_es (cs k ! i) k))))"
     {
       fix c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd
       assume a0: "Pre k \<subseteq> prea \<and> Rely k \<subseteq> relya \<and> guara \<subseteq> Guar k \<and> posta \<subseteq> Post k"
         and a1: "c \<in> cpts_of_pes pes s x \<and> c \<propto> cs \<and> c \<in> assume_pes (pre1, rely1)"
         and a2: "(\<forall>k. cs k \<in> cpts_of_es (pes k) s x)"
         and a3: "\<forall>k. (cs k)\<in>commit_es(Guar k, Post k)"
         and a5: "(\<forall>k. pre1 \<subseteq> Pre k)"
         and a6: "(\<forall>k. rely1 \<subseteq> Rely k)"
         and a7: "(\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k)"
         and a8: "evtsys_spec esys = EvtSys es \<and> EvtSys es = getspc_es (cs k ! 0)"
         and a9: "(\<forall>e\<in>all_evts_es esys. is_basicevt (E\<^sub>e e))"
         and a10: "(\<forall>e\<in>all_evts_es esys. the (evtrgfs (E\<^sub>e e)) = snd e)"
         and a11: "(\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c ! j -pes-actk\<rightarrow> c ! Suc j))"
       from a0 p1 p2 p3 p4 have "Pre k \<subseteq> pre' \<and> Rely k \<subseteq> rely' \<and> guar' \<subseteq> Guar k \<and> post' \<subseteq> Post k" by auto
       with a1 a2 a3 a5 a6 a7 a8 a9 a10 a11 p1 p2 p3 p4 p6[of Pre k Rely Guar Post c pes s x cs pre1 rely1] 
        have "\<forall>i. Suc i < length (cs k) \<and> cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i \<longrightarrow>
               (gets_es (cs k ! i), gets_es (cs k ! Suc i)) \<in> Guar\<^sub>f (the (evtrgfs (getx_es (cs k ! i) k)))" by force
     }
     then show "\<forall>c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd.
          Pre k \<subseteq> prea \<and> Rely k \<subseteq> relya \<and> guara \<subseteq> Guar k \<and> posta \<subseteq> Post k \<longrightarrow>
          c \<in> cpts_of_pes pes s x \<and> c \<propto> cs \<and> c \<in> assume_pes (pre1, rely1) \<longrightarrow>
          (\<forall>k. cs k \<in> cpts_of_es (pes k) s x) \<longrightarrow>
          (\<forall>k. (cs k)\<in>commit_es(Guar k, Post k)) \<longrightarrow>
          (\<forall>k. pre1 \<subseteq> Pre k) \<longrightarrow>
          (\<forall>k. rely1 \<subseteq> Rely k) \<longrightarrow>
          (\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k) \<longrightarrow>
          evtsys_spec esys = EvtSys es \<and> EvtSys es = getspc_es (cs k ! 0) \<longrightarrow>
          (\<forall>e\<in>all_evts_es esys. is_basicevt (E\<^sub>e e)) \<longrightarrow>
          (\<forall>e\<in>all_evts_es esys. the (evtrgfs (E\<^sub>e e)) = snd e) \<longrightarrow>
          (\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c ! j -pes-actk\<rightarrow> c ! Suc j)) \<longrightarrow>
          (\<forall>i. Suc i < length (cs k) \<and> cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i \<longrightarrow>
               (gets_es (cs k ! i), gets_es (cs k ! Suc i)) \<in> Guar\<^sub>f (the (evtrgfs (getx_es (cs k ! i) k))))" by fastforce
     
  }
qed


lemma rm_evtsys_preserves: "elst \<in> preserves_es \<Longrightarrow> rm_evtsys elst \<in> preserves_e"
  apply (simp add: preserves_es_def preserves_e_def, clarify)
  apply (erule_tac x = i in allE, erule impE)
   apply (simp add: rm_evtsys_def)
  apply (case_tac "getspc_es (elst ! i)")
   apply (simp add: ann_preserves_es_def rm_evtsys_def rm_evtsys1_def gets_e_def gets_es_def getspc_e_def)
  apply (simp add: rm_evtsys_def rm_evtsys1_def getspc_e_def)
  done


lemma act_cpts_evtsys_sat_e_sim[rule_format]:
  "\<lbrakk>\<turnstile> (esspc::('l,'k,'s) rgformula_ess) sat\<^sub>s [pre, rely, guar, post]\<rbrakk>
      \<Longrightarrow> \<forall>c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd. 
            Pre k \<subseteq> pre \<and> Rely k \<subseteq> rely \<and> guar \<subseteq> Guar k \<and> post \<subseteq> Post k \<longrightarrow>
            c\<in>cpts_of_pes pes s x \<and> c \<propto> cs \<and> c\<in>assume_pes(pre1, rely1) \<longrightarrow>
           (\<forall>k. (cs k) \<in> cpts_of_es (pes k) s x)  \<longrightarrow> 
           (\<forall>k. (cs k)\<in> commit_es(Guar k, Post k)) \<longrightarrow>
           (\<forall>k. pre1 \<subseteq> Pre k) \<longrightarrow>
           (\<forall>k. rely1 \<subseteq> Rely k) \<longrightarrow>
           (\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k) \<longrightarrow>
           evtsys_spec esspc = EvtSys es \<and>  EvtSys es = getspc_es (cs k!0) \<longrightarrow>
           (\<forall>e\<in>all_evts_es esspc. is_basicevt (E\<^sub>e e)) \<longrightarrow>
           (\<forall>e\<in>all_evts_es esspc. the (evtrgfs (E\<^sub>e e)) = snd e) \<longrightarrow>
           (\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c!j-pes-actk\<rightarrow>c!Suc j)) \<longrightarrow>
          (\<forall>i. Suc i < length (cs k) \<and> ((cs k)!i -es-((Cmd cmd)\<sharp>k)\<rightarrow> (cs k)!(Suc i)) 
          \<longrightarrow>  (\<exists>el j. getspc_e (el!0) = getx_es ((cs k)!i) k \<and> j < length el \<and> el!j = rm_evtsys1 ((cs k)!i)   
               \<and> el \<in> cpts_ev \<and> el \<in> preserves_e))"
  apply(rule rghoare_es.induct[of esspc pre rely guar post]) 
     apply simp
    apply simp
proof-
  {
    fix esf prea relya guara posta
    assume p0: " \<turnstile> (esspc::('l,'k,'s) rgformula_ess) sat\<^sub>s [pre, rely, guar, post]"
      and  b5: "\<forall>ef\<in>(esf::('l,'k,'s) rgformula_e set). \<turnstile> E\<^sub>e ef sat\<^sub>e [Pre\<^sub>e ef, Rely\<^sub>e ef, Guar\<^sub>e ef, Post\<^sub>e ef]"
      and  b6: "\<forall>ef\<in>esf. prea \<subseteq> Pre\<^sub>e ef"
      and  b7: "\<forall>ef\<in>esf. relya \<subseteq> Rely\<^sub>e ef"
      and  b8: "\<forall>ef\<in>esf. Guar\<^sub>e ef \<subseteq> guara"
      and  b9: "\<forall>ef\<in>esf. Post\<^sub>e ef \<subseteq> posta"
      and  b10: "\<forall>ef1 ef2. ef1 \<in> esf \<and> ef2 \<in> esf \<longrightarrow> Post\<^sub>e ef1 \<subseteq> Pre\<^sub>e ef2"
      and  b11: "stable prea relya"
      and  b12: "\<forall>s. (s, s) \<in> guara"
    {
      fix c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd
      assume b1: "Pre k \<subseteq> prea"
         and b2: "Rely k \<subseteq> relya"
         and b3: "guara \<subseteq> Guar k"
         and b4: "posta \<subseteq> Post k"
         and p0: "c \<in> cpts_of_pes pes s x"
         and p1: "c \<propto> cs"
         and p8: "c \<in> assume_pes (pre1, rely1)"
         and p2: "(\<forall>k. cs k \<in> cpts_of_es (pes k) s x)"
         and p3: "\<forall>k. (cs k)\<in>commit_es(Guar k, Post k)"
         and a5: "(\<forall>k. pre1 \<subseteq> Pre k)"
         and a6: "(\<forall>k. rely1 \<subseteq> Rely k)"
         and p4: "(\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k)"
         and a0: "evtsys_spec (rgf_EvtSys esf) = EvtSys es \<and> EvtSys es = getspc_es (cs k ! 0) 
                  \<and> (\<forall>e\<in>all_evts_es (rgf_EvtSys esf). is_basicevt (E\<^sub>e e))
                  \<and> (\<forall>e\<in>all_evts_es (rgf_EvtSys esf). the (evtrgfs (E\<^sub>e e)) = snd e)"
         and p6: "(\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c ! j -pes-actk\<rightarrow> c ! Suc j))"
      then have p30: "(\<forall>k. cs k \<in> assume_es (Pre k, Rely k))" 
        using conjoin_comm_imp_rely[of pre1 Pre rely1 Rely Guar cs Post c pes s x] by auto
      with p3 have p31: "(\<forall>k. cs k \<in> commit_es (Guar k, Post k))"
        by (meson IntI contra_subsetD cpts_of_es_def es_validity_def p2)

      from p1 have p11: "\<forall>k. length (cs k) = length c" by (simp add:conjoin_def same_length_def)
      from p2 have p12: "\<forall>k. cs k \<in> cpts_es" using cpts_of_es_def mem_Collect_eq by fastforce 
      with p11 have "c \<noteq> Nil" using cpts_es_not_empty length_0_conv by auto 
      then have p13: "length c > 0" by auto

      let ?esl = "cs k"
      let ?esys = "EvtSys es"
      
      from p1 p2 a0 have a8: "?esl \<in> cpts_es \<and> ?esl!0 = (EvtSys es,s,x)"
        by (simp add: cpts_of_es_def eq_fst_iff getspc_es_def) 

      then obtain esll where a81: "?esl = (EvtSys es,s,x)#esll"
        by (metis hd_Cons_tl length_greater_0_conv nth_Cons_0 p11 p13) 

      from p1 have a9: "\<forall>i. Suc i < length ?esl \<longrightarrow> (?esl!i) -ese\<rightarrow> (?esl! Suc i) 
        \<or> (\<exists>e. (?esl!i) -es-(EvtEnt e\<sharp>k)\<rightarrow> (?esl! Suc i))
        \<or> (\<exists>c. (?esl!i) -es-(Cmd c\<sharp>k)\<rightarrow> (?esl ! Suc i))"
        by (meson acts_in_conjoin_cpts)

      {
        fix i
        assume a3: "Suc i < length (cs k)"
          and  a4: "cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i"
        have "\<exists>el j. getspc_e (el!0) = getx_es ((cs k)!i) k \<and> j < length el \<and> el!j = rm_evtsys1 ((cs k)!i)   
               \<and> el \<in> cpts_ev \<and> el \<in> preserves_e"
          proof(cases "\<forall>i. Suc i \<le> length ?esl \<longrightarrow> getspc_es (?esl ! i) = EvtSys es")
              assume c0: "\<forall>i. Suc i \<le> length ?esl \<longrightarrow> getspc_es (?esl ! i) = EvtSys es"
              with a3 have "getspc_es (?esl ! i) = EvtSys es \<and> getspc_es (?esl ! Suc i) = EvtSys es"
                by auto
              with a4 show ?thesis by (metis evtsys_not_eq_in_tran_aux1)
            next
              assume c0: "\<not>(\<forall>i. Suc i \<le> length ?esl \<longrightarrow> getspc_es (?esl ! i) = EvtSys es)"
              then obtain m where c1: "Suc m \<le> length ?esl \<and> getspc_es (?esl ! m) \<noteq> EvtSys es" 
                by auto
              from a8 have c2: "getspc_es (?esl!0) = EvtSys es" by (simp add:getspc_es_def)
              from c1 have "\<exists>i. i \<le> m \<and> getspc_es (?esl ! i) \<noteq> EvtSys es" by auto
              with a8 c1 c2 have "\<exists>i. (i < m \<and> getspc_es (?esl ! i) = EvtSys es 
                        \<and> getspc_es (?esl ! Suc i) \<noteq> EvtSys es) 
                        \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (?esl ! j) = EvtSys es)" 
                using evtsys_fst_ent by blast
              then obtain n where c3: "(n < m \<and> getspc_es (?esl ! n) = EvtSys es 
                        \<and> getspc_es (?esl ! Suc n) \<noteq> EvtSys es) 
                        \<and> (\<forall>j. j < n \<longrightarrow> getspc_es (?esl ! j) = EvtSys es)" by auto
              have c4: "i \<ge> n" 
                proof -
                {
                  assume d0: "i < n"
                  with c3 have "getspc_es (?esl ! i) = EvtSys es" by simp
                  moreover from c3 d0 have "getspc_es (?esl ! Suc i) = EvtSys es"
                    using Suc_lessI by blast 
                  ultimately have "\<not>(\<exists>t. ?esl!i -es-t\<rightarrow> ?esl!Suc i)" 
                    using evtsys_not_eq_in_tran getspc_es_def by (metis surjective_pairing)
                  with a4 have False by simp
                }
                then show ?thesis using leI by auto 
              qed

              let ?esl1 = "drop n ?esl"
              let ?eslh = "take (Suc n) ?esl"
              from c1 c3 have c5: "length ?esl1 \<ge> 2"
                by (metis One_nat_def Suc_eq_plus1_left Suc_le_eq length_drop 
                    less_diff_conv less_trans_Suc numeral_2_eq_2)
              from c1 c3 have c6: "getspc_es (?esl1!0) = EvtSys es \<and> getspc_es (?esl1!1) \<noteq> EvtSys es"
                by force

              from a3 a8 c1 c3 c4 have c7: "?esl1 \<in> cpts_es" using cpts_es_dropi
                  by (metis (no_types, lifting) drop_0 dual_order.strict_trans 
                      le_0_eq le_SucE le_imp_less_Suc zero_induct) 
              from c5 c6 c7 have "\<exists>s x ev s1 x1 xs. 
                ?esl1 = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
                  using fst_esys_snd_eseq_exist by blast
              then obtain s0 and x0 and e and s1 and x1 and xs where c8:
                  "?esl1 = (EvtSys es, s0, x0) # (EvtSeq e (EvtSys es), s1,x1) # xs" by auto
              with c3 have c3_1: "(\<forall>j\<le>n. getspc_es (cs k ! j) = EvtSys es)" using getspc_es_def
                using antisym_conv2 by blast 
              let ?elst = "tl (parse_es_cpts_i2 ?esl1 es [[]])"
              from c8 c7 have c9: "concat ?elst = ?esl1" using parse_es_cpts_i2_concat3 by metis 
              from a3 a8 c1 c3 c4 have c7: "?esl1 \<in> cpts_es" using cpts_es_dropi
                  by (metis (no_types, lifting) drop_0 dual_order.strict_trans 
                      le_0_eq le_SucE le_imp_less_Suc zero_induct) 
              from c5 c6 c7 have "\<exists>s x ev s1 x1 xs. 
                ?esl1 = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
                  using fst_esys_snd_eseq_exist by blast
              then obtain s0 and x0 and e and s1 and x1 and xs where c8:
                  "?esl1 = (EvtSys es, s0, x0) # (EvtSeq e (EvtSys es), s1,x1) # xs" by auto
              with c3 have c3_1: "(\<forall>j\<le>n. getspc_es (cs k ! j) = EvtSys es)" using getspc_es_def
                using antisym_conv2 by blast 
              let ?elst = "tl (parse_es_cpts_i2 ?esl1 es [[]])"
              from c8 c7 have c9: "concat ?elst = ?esl1" using parse_es_cpts_i2_concat3 by metis 
              
              from a0 have c13: "es = Domain esf" using evtsys_spec_evtsys by auto
              from b5 have c14: "\<forall>i\<in>esf. \<Turnstile> E\<^sub>e i sat\<^sub>e [Pre\<^sub>e i, Rely\<^sub>e i, Guar\<^sub>e i, Post\<^sub>e i]"
                by (simp add: rgsound_e)

              let ?RG = "\<lambda>e. SOME rg. (e,rg)\<in>esf" 
              from c13 have c131: "\<forall>e\<in>es. \<exists>ef\<in>esf. ?RG e = snd ef" by (metis Domain.cases snd_conv someI) 
          
              let ?Pre = "pre_rgf \<circ> ?RG"
              let ?Rely = "rely_rgf \<circ> ?RG"
              let ?Guar = "guar_rgf \<circ> ?RG"
              let ?Post = "post_rgf \<circ> ?RG"

              from c13 c14 have c16: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [?Pre ef, ?Rely ef, ?Guar ef, ?Post ef]" 
                by (metis (mono_tags, lifting) Domain.cases E\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def 
                    Pre\<^sub>e_def Rely\<^sub>e_def comp_apply fst_conv snd_conv someI_ex) 
              moreover
              from b1 b6 have c17: "\<forall>j\<in>es. prea \<subseteq> ?Pre j" using Pre\<^sub>e_def c131 comp_def by metis 
              moreover
              from b2 b7 have c18: "\<forall>j\<in>es. Rely k \<subseteq> ?Rely j" using Rely\<^sub>e_def c131 comp_def by (metis subsetCE subsetI) 
              moreover
              from b3 b8 have c19: "\<forall>j\<in>es. ?Guar j \<subseteq> Guar k" using Guar\<^sub>e_def c131 comp_def by (metis subsetCE subsetI)
              moreover
              from b4 b9 have c20: "\<forall>j\<in>es. ?Post j \<subseteq> Post k" using c131 comp_def
                by (metis Post\<^sub>e_def contra_subsetD subsetI) 
              moreover
              from b5 b10 have c21: "\<forall>ef1 ef2. ef1 \<in> es \<and> ef2 \<in> es \<longrightarrow> ?Post ef1 \<subseteq> ?Pre ef2"
                by (metis Post\<^sub>e_def Pre\<^sub>e_def c131 comp_apply) 
              moreover
              from c1 c3_1 p30 have c24: "?esl1\<in>assume_es (prea, Rely k)"
              proof(cases "n = 0")
                assume d0: "n = 0"
                from b1 p30 have "?esl\<in>assume_es(prea,Rely k)" 
                  using assume_es_imp[of "Pre k" prea "Rely k" "Rely k" ?esl] by blast
                with d0 show ?thesis by auto
              next
                assume d0: "n \<noteq> 0"
                from b1 b2 p30 have "?esl\<in>assume_es(prea,relya)" 
                  using assume_es_imp[of "Pre k" prea "Rely k" relya ?esl] by blast
                then have "?eslh \<in> assume_es(prea,relya)" 
                  using assume_es_take_n[of "Suc n" ?esl prea relya] d0 c1 c3 by auto
                moreover
                from c3 have "\<forall>i<length ?eslh. getspc_es (?eslh!i) = EvtSys es"
                proof -
                  from c3 have "\<forall>i. Suc i<length ?eslh \<longrightarrow> getspc_es (?eslh!i) = EvtSys es"
                    using Suc_le_lessD length_take less_antisym less_imp_le_nat min.bounded_iff nth_take by auto 
                  moreover
                  from c3 have "getspc_es (last ?eslh) = EvtSys es"
                    by (metis (no_types, lifting) a3 c4 dual_order.strict_trans getspc_es_def 
                        last_snoc le_imp_less_Suc take_Suc_conv_app_nth) 
                  ultimately show ?thesis
                    by (metis Suc_lessI diff_Suc_1 last_conv_nth length_greater_0_conv nat.distinct(1) p11 p13 take_eq_Nil) 
                qed
                ultimately have "\<forall>i<length ?eslh. gets_es (?eslh!i) \<in> prea" 
                  using b11 pre_trans[of ?eslh prea relya "EvtSys es"] by blast
                moreover
                from c1 c3 have d1: "Suc n \<le> length ?esl" by auto
                moreover
                then have "n < length ?eslh" by auto
                ultimately have "gets_es (?eslh ! n) \<in> prea" by simp
                moreover
                from d1 have "?eslh ! n = ?esl1 ! 0" by (simp add: c8 nth_via_drop)
                ultimately have "gets_es (?esl ! n) \<in> prea" by simp
                with p30 d1 show ?thesis using assume_es_drop_n[of n ?esl "Pre k" "Rely k" prea] by auto
              qed
              ultimately have rl [rule_format]: "\<forall>i. i < length ?elst \<longrightarrow> ?elst ! i \<in> preserves_es"
                using EventSys_sound_aux_i_preserve[of es ?Pre ?Rely ?Guar ?Post
                      "prea" "Rely k" "Guar k" "Post k" ?esl1 s0 x0 e s1 x1 xs ?elst] c7 c8 by force

              from c8 c7 have no_mident_i[rule_format]: "\<forall>i. i < length ?elst \<longrightarrow> 
                             \<not>(\<exists>j. j > 0 \<and> Suc j < length (?elst!i) \<and> getspc_es (?elst!i!j) = EvtSys es 
                             \<and> getspc_es (?elst!i!Suc j) \<noteq> EvtSys es)"
                using parse_es_cpts_i2_noent_mid[of ?esl1 es s0 x0 e s1 x1 xs "parse_es_cpts_i2 ?esl1 es [[]]"]
                by simp

              from c7 c8 have in_cpts[rule_format]: "\<forall>i. i < length ?elst \<longrightarrow> ?elst ! i \<in> cpts_es"
                using parse_es_cpts_i2_in_cptes[of ?esl1 es s0 x0 e s1 x1 xs ?elst] by blast

              from c5 c8 c7 have len_start_elst[rule_format]: 
                "\<forall>i<length ?elst. length (?elst!i) \<ge> 2 \<and> getspc_es (?elst!i!0) = EvtSys es 
                                  \<and> getspc_es (?elst!i!1) \<noteq> EvtSys es" 
                using parse_es_cpts_i2_start_aux[of ?esl1 es s0 x0 e s1 x1 xs "parse_es_cpts_i2 ?esl1 es [[]]"]
                by fastforce

              from c9 have c30: "\<forall>i. i < length ?esl1 \<longrightarrow> (\<exists>k j. k < length ?elst \<and> j < length (?elst ! k)
                              \<and> ?esl1!i = ?elst!k!j)"
                by (metis concat_list_lemma_i)


              from p12 a3 have c33[rule_format]: "\<forall>i. i < length ?esl 
                \<longrightarrow> getspc_es (?esl!i) = EvtSys es \<or> (\<exists>e. getspc_es (?esl!i) = EvtSeq e (EvtSys es) \<and> is_anonyevt e)"
                using evtsys_all_es_in_cpts_anony[of ?esl es]
                  c2 gr0I gr_implies_not0 by blast 

              from a3 c4 have c34: "?esl!i = ?esl1!(i - n)"
                using Suc_lessD add_diff_inverse_nat leD less_imp_le_nat nth_drop by auto 
              from a3 c4 have c340: "?esl!Suc i = ?esl1!(Suc (i - n))"
                using Suc_lessD add_diff_inverse_nat leD less_imp_le_nat nth_drop by auto 
              from a3 c4 have "Suc (i - n) < length ?esl1"
                by (simp add: Suc_diff_le diff_less_mono le_SucI) 
              with c30 have "\<exists>k j. k < length ?elst \<and> j < length (?elst ! k) \<and> ?esl1!(i-n) = ?elst!k!j"
                by auto
              then obtain kk and j where c35 : "kk < length ?elst \<and> j < length (?elst ! kk) \<and> ?esl1!(i-n) = ?elst!kk!j"
                by auto

              then have c36: "\<not>(\<exists>j. j > 0 \<and> Suc j < length (?elst!kk) \<and>  getspc_es (?elst!kk!j) = EvtSys es \<and> getspc_es (?elst!kk!Suc j) \<noteq> EvtSys es)"
                using no_mident_i by blast

              let ?elstl = "?elst!kk"

              from c35 have d0: "?elstl \<in> cpts_es" using in_cpts by auto
              from c35 have d1: "length ?elstl \<ge> 2 \<and> getspc_es (?elstl!0) = EvtSys es  \<and> getspc_es (?elstl!1) \<noteq> EvtSys es"
                using len_start_elst by blast

              have d01: "j \<noteq> 0"
              proof
                assume e0: "j = 0"
                with len_start_elst[of kk] have e1: "getspc_es (?elstl!j) = EvtSys es 
                            \<and> getspc_es (?elstl!Suc j) \<noteq> EvtSys es"
                  using One_nat_def d1 by presburger
                moreover
                from a4 have "\<not>(\<exists>ess. getspc_es (?esl ! i) = EvtSys ess)" 
                  using cmd_enable_impl_notesys2[of "?esl ! i" cmd k "?esl ! Suc i"] by simp
                moreover
                from d0 have "?esl!i = ?elstl!j"
                  by (simp add: c34 c35)
                ultimately show False by simp
              qed


              have d1_1: "\<forall>ii. ii > 0 \<and> Suc ii < length ?elstl \<longrightarrow> \<not>(\<exists>e. (?elstl!ii) -es-((EvtEnt e)\<sharp>k)\<rightarrow> (?elstl!(Suc ii)))"
              proof-
                {
                  fix ii
                  assume e0: "ii > 0 \<and> Suc ii < length ?elstl"
                  have "\<not>(\<exists>e. (?elstl!ii) -es-((EvtEnt e)\<sharp>k)\<rightarrow> (?elstl!(Suc ii)))"
                  proof(cases "getspc_es (?elstl!ii) = EvtSys es")
                    assume f0: "getspc_es (?elstl!ii) = EvtSys es"
                    with c36 e0 have "getspc_es (?elstl! Suc ii) = EvtSys es" by blast
                    with f0 show ?thesis
                      using evtsys_not_eq_in_tran_aux1 by fastforce
                  next
                    assume f0: "getspc_es (?elstl!ii) \<noteq> EvtSys es"
                    from d1 have "length ?elstl > 0 \<and> getspc_es (?elstl!0) = EvtSys es" by auto
                    with c35 d0 have  "\<forall>i<length ?elstl. getspc_es (?elstl!i) = EvtSys es \<or> (\<exists>e. getspc_es (?elstl!i) = EvtSeq e (EvtSys es) \<and> is_anonyevt e)"
                      using evtsys_all_es_in_cpts_anony[of ?elstl es]  by blast
                    with e0 have "getspc_es (?elstl!ii) = EvtSys es \<or> (\<exists>e. getspc_es (?elstl!ii) = EvtSeq e (EvtSys es) \<and> is_anonyevt e)"
                      using Suc_lessD by blast
                    with f0 show ?thesis using d0 e0 incpts_es_eseq_not_evtent by blast
                  qed
                }
                then show ?thesis by auto
              qed


               from c9 d0 len_start_elst[of kk]  have "\<exists>si ti. si = length (concat (take kk ?elst)) \<and> 
               ti = length (concat (take (Suc kk) ?elst)) \<and> si \<le> length ?esl1 \<and> ti \<le> length ?esl1 
               \<and> si < ti \<and> drop si (take ti ?esl1) = ?elstl"
                 using concat_list_lemma3[of ?esl1 ?elst kk] Suc_1 Suc_le_lessD c35 by presburger
               then obtain si and ti where d3: "si = length (concat (take kk ?elst)) 
                                            \<and>   ti = length (concat (take (Suc kk) ?elst)) 
                                            \<and>   si \<le> length ?esl1 \<and> ti \<le> length ?esl1 
                                            \<and>   si < ti \<and> drop si (take ti ?esl1) = ?elstl" by auto
               then have d32: "si + (length ?elstl) = ti" 
                 by (metis c35 drop_take_eq gr_implies_not0 length_0_conv length_greater_0_conv) 

               with d1 have d31 : "ti \<ge> si + 2" by linarith
               from d3 have "ti \<le> length ?esl1" by blast
               then have d33: "n + ti \<le> length ?esl" 
                 using a3 c4 by auto

               from d31 have d4: "Suc (si + n) < length ?esl"
                 by (metis Suc_1 Suc_eq_plus1 Suc_le_lessD add_Suc add_Suc_right d3 le_trans length_drop less_diff_conv)

               from d3 have d5: "?elstl = drop (si + n) (take (ti+n) ?esl)"
                 by (simp add: d3 take_drop)

               then have d6: "?elstl!0 = ?esl!(si + n)"
                 by (metis (no_types, lifting) Nat.add_0_right add.commute c8 d3 d32 drop_eq_Nil 
                    drop_take_sametrace less_add_same_cancel1 list.distinct(1) nat_le_linear nth_drop)

               from d5 have "?elstl!1 = drop (si+n) (take (ti+n) ?esl) ! 1" by simp
               moreover
               from d5 have "drop (si+n) (take (ti+n) ?esl) ! 1 = ?esl!(Suc (si+n))"
                 by (metis Suc_1 Suc_eq_plus1 Suc_le_lessD d1 drop_take_sametrace)
               moreover have d7: "?elstl!1 = ?esl!(Suc (si+n))" 
                 using calculation(1) calculation(2) by auto
               ultimately have d71: "?elstl!j = ?esl!(si+n +j)" 
                 using c35 d5 drop_take_sametrace by blast

               with p1 d1 d4 d6 d7 have "\<exists>e. ?esl!(si+n) -es-((EvtEnt e)\<sharp>k)\<rightarrow> ?esl!(Suc (si+n))"
                    using entevt_in_conjoin_cpts[of c cs "si+n" k es] by simp
                  then obtain ente where d8: "?esl!(si+n) -es-((EvtEnt ente)\<sharp>k)\<rightarrow> ?esl!(Suc (si+n))" by auto
                  with d1 d6 have "\<exists>ei\<in>es. ente = ei" 
                    using evtsysent_evtent3[of "?esl!(si+n)" ente k "?esl!(Suc (si+n))" es] by auto
                  then obtain ei where d9: "ei\<in>es \<and> ente = ei" by auto

               from c36[rule_format] have d10: "\<forall>m. m > 0 \<and> Suc m < length ?elstl \<longrightarrow> 
                    \<not>(getspc_es (?elstl!m) = EvtSys es \<and> getspc_es (?elstl!Suc m) \<noteq> EvtSys es)"
                 by auto



               have d11: "\<forall>m. m > (si + n) \<and> m < ti + n - 1 \<longrightarrow> 
                             \<not>(getspc_es (?esl!m) = EvtSys es \<and> getspc_es (?esl!Suc m) \<noteq> EvtSys es)"
               proof-
                 {
                   fix m
                   assume e0: "m > (si + n) \<and> m < ti + n - 1"
                   then have e1: "m - (n + si) > 0" by auto
                   moreover
                   have e2: "Suc (m - (n+si)) < length ?elstl" 
                   proof-
                     from e0 have "m - (n + si) < ti - si - 1" by auto
                     then have "Suc (m - (n + si)) < ti - si" by auto
                     with d32 show ?thesis by auto
                   qed
                   ultimately have "\<not>(getspc_es (?elstl!(m-(n+si))) = EvtSys es 
                                 \<and> getspc_es (?elstl!Suc (m-(n+si))) \<noteq> EvtSys es)"
                     using d10 by blast
                   from e1 e2 d5 have "?esl!m = ?elstl!(m - (n+si))"
                     using drop_take_sametrace[of ?elstl "si+n" "ti+n" ?esl "m - (n+si)"] by auto
                   moreover
                   from e1 e2 d5 have "?esl!Suc m = ?elstl!Suc (m - (n+si))"
                     using drop_take_sametrace[of ?elstl "si+n" "ti+n" ?esl "Suc (m - (n+si))"] by auto
                   ultimately have "\<not>(getspc_es (?esl!m) = EvtSys es \<and> getspc_es (?esl!Suc m) \<noteq> EvtSys es)"
                     using d10 e1 e2 by auto
                 }
                 then show ?thesis by auto
               qed

               have d11: "\<forall>m. m > (si + n) \<and> m < ti + n - 1 \<longrightarrow> \<not>(\<exists>e. ?esl!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> ?esl!Suc m)"
               proof-
                 {
                   fix m
                   assume e0: "m > (si + n) \<and> m < ti + n - 1"
                   with d11 have "\<not>(getspc_es (?esl!m) = EvtSys es \<and> getspc_es (?esl!Suc m) \<noteq> EvtSys es)" 
                        by auto
                      with p1 a8 a81 d33  e0 have "\<not>(\<exists>e. ?esl!m -es-((EvtEnt e)\<sharp>k)\<rightarrow> ?esl!Suc m)" 
                        using notentevt_in_conjoin_cpts[of c cs m k es] evtsys_allevtseqorevtsys[of ?esl es s x esll]
                          by auto         
                      }
                      then show ?thesis by auto
                    qed

                    have d12[rule_format]:"\<forall>m. m > (si + n) \<and> m \<le> (ti + n - 1) \<longrightarrow> getx_es ((cs k)!m) k = ente" 
                      using evtent_impl_curevt_in_cpts_es1[of c cs "si + n" k ente "ti + n - 1"]
                          d11 p1 p6 d8 d33 by auto
                    from c35 d32 have "si + n + j \<le> ti + n - 1" by linarith
                    with d01 d12[of "si + n + j"] have "getx_es ((cs k)!(si + n + j)) k = ente"
                      by auto
                    with c34 c35 d5 have d13: "getx_es ((cs k)!i) k = ente"    
                      using drop_take_sametrace by fastforce

                    from a0 d9 have "is_basicevt ente" 
                      by (metis Domain_iff E\<^sub>e_def all_evts_es.simps(2) c13 prod.sel(1))
                    then have "\<exists>ev. ente = BasicEvent ev" 
                      by (metis event.exhaust is_basicevt.simps(1))
                    then obtain ev where d14: "ente = BasicEvent ev" by auto
                    
                    let ?ss = "gets_es (?elstl!0)"
                    let ?xx = "getx_es (?elstl!0)"
                    let ?ss1 = "gets_es (?elstl!1)"
                    let ?xx1 = "getx_es (?elstl!1)"

                    from d1 have d15: "?elstl!0 = ((EvtSys es), ?ss, ?xx)" by (simp add: esconf_trip)
                    from d6 d7 d8 have "?elstl!0 -es-EvtEnt ente\<sharp>k\<rightarrow> ?elstl!1" by auto
                    with d1 d4 d6 d7 d15 have "\<exists>ev1. getspc_es (?elstl!1) = EvtSeq ev1 (EvtSys es)"
                      using evtsys_next_in_cpts p12 by auto
                    then obtain e1 where "getspc_es (?elstl!1) = EvtSeq e1 (EvtSys es)" by auto
                    then have d16: "?elstl!1 = (EvtSeq e1 (EvtSys es), ?ss1, ?xx1)" by (simp add: esconf_trip)

                    with d0 d1 d15 have "\<exists>xs. ?elstl = (EvtSys es, ?ss, ?xx) # (EvtSeq e1 (EvtSys es), ?ss1,?xx1) # xs"
                      using  fst_esys_snd_eseq_exist by fastforce
                    then obtain xs where d17: "?elstl = (EvtSys es, ?ss, ?xx) # (EvtSeq e1 (EvtSys es), ?ss1,?xx1) # xs"
                      by auto

                    from d6 d7 d8 d14 d15 d16 have d18 : "(EvtSys es, ?ss, ?xx) -es-EvtEnt (BasicEvent ev)\<sharp>k\<rightarrow> (EvtSeq e1 (EvtSys es), ?ss1,?xx1)"
                      by auto

                    let ?elstl1 = "(EvtSeq e1 (EvtSys es), ?ss1, ?xx1) # xs"
                    let ?el = "(BasicEvent ev, ?ss, ?xx) # rm_evtsys ?elstl1"

                    from d13 d14 have d19: "getspc_e (?el!0) = getx_es (cs k ! i) k"
                      by (simp add: getspc_e_def)


                    from c34 c35 d01 d17 have  "?elstl1!(j-1) = (cs k) ! i"
                      by (metis (no_types, lifting) nth_Cons')
                    with c35 d01 d17 have  "j-1 < length ?elstl1 \<and> ?elstl1!(j-1) = (cs k) ! i"
                      by (metis (no_types, lifting) Suc_less_SucD add_diff_inverse_nat length_Cons less_one plus_1_eq_Suc)
                    then have d20: "j < length ?el \<and> ?el ! j = rm_evtsys1 ((cs k) ! i)"
                    proof-
                      assume e0: "j-1 < length ?elstl1 \<and> ?elstl1!(j-1) = (cs k) ! i"
                      then have "j -1  < length (rm_evtsys ?elstl1)"
                        by (simp add: rm_evtsys_def)
                      then have e1: "j < length ?el" by simp
                      with d01 have e2: "?el!j = (rm_evtsys ?elstl1) ! (j - 1)" by simp
                      from e0 have "(rm_evtsys ?elstl1) ! (j - 1) = rm_evtsys1 (?elstl1 ! (j - 1))"
                        by (metis (no_types, lifting) rm_evtsys_def  nth_map)
                      with e0 e2 have "?el!j = rm_evtsys1 ((cs k)!i)" by auto
                      with e1 show ?thesis by auto
                    qed


                    from d0 d17 d18 c36 have d21: "?el \<in> cpts_ev"
                      using rm_evtsys_in_cptse[of ?elstl es ?ss ?xx e1 ?ss1 ?xx1 xs ev] by blast

                    from c35 rl[of kk] have " ?elstl \<in> preserves_es" by blast
                    with d17 have "(EvtSeq e1 (EvtSys es), ?ss1,?xx1) # xs \<in> preserves_es"  
                      using preserves_es_append1[of ?elstl "[(EvtSys es, ?ss, ?xx)]" 
                            "?elstl1"] by auto
                    then have d220: "rm_evtsys ?elstl1 \<in> preserves_e"
                      using rm_evtsys_preserves by blast
                    have "[(BasicEvent ev, ?ss, ?xx)] \<in> preserves_e"
                      by (simp add: preserves_e_def getspc_e_def)
                    with d220 have d22 : "?el \<in> preserves_e"
                      using preserves_e_append[of ?el "[(BasicEvent ev, ?ss, ?xx)]" "rm_evtsys ?elstl1"]
                      by simp
                    with d19 d20 d21  show ?thesis by blast
                  qed
                }
                then have "\<forall>i. Suc i < length (cs k) \<and> ((cs k)!i -es-((Cmd cmd)\<sharp>k)\<rightarrow> (cs k)!(Suc i)) 
          \<longrightarrow>  (\<exists>el j. getspc_e (el!0) = getx_es ((cs k)!i) k \<and> j < length el \<and> el!j = rm_evtsys1 ((cs k)!i)   
               \<and> el \<in> cpts_ev \<and> el \<in> preserves_e)" by auto
              }
              then show "       \<forall>c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd.
          Pre k \<subseteq> prea \<and> Rely k \<subseteq> relya \<and> guara \<subseteq> Guar k \<and> posta \<subseteq> Post k \<longrightarrow>
          c \<in> cpts_of_pes pes s x \<and> c \<propto> cs \<and> c \<in> assume_pes (pre1, rely1) \<longrightarrow>
          (\<forall>k. cs k \<in> cpts_of_es (pes k) s x) \<longrightarrow>
          (\<forall>k. cs k \<in> commit_es (Guar k, Post k)) \<longrightarrow>
          (\<forall>k. pre1 \<subseteq> Pre k) \<longrightarrow>
          (\<forall>k. rely1 \<subseteq> Rely k) \<longrightarrow>
          (\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k) \<longrightarrow>
          evtsys_spec (rgf_EvtSys esf) = EvtSys es \<and> EvtSys es = getspc_es (cs k ! 0) \<longrightarrow>
          (\<forall>e\<in>all_evts_es (rgf_EvtSys esf). is_basicevt (E\<^sub>e e)) \<longrightarrow>
          (\<forall>e\<in>all_evts_es (rgf_EvtSys esf). the (evtrgfs (E\<^sub>e e)) = snd e) \<longrightarrow>
          (\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c ! j -pes-actk\<rightarrow> c ! Suc j)) \<longrightarrow> 
          (\<forall>i. Suc i < length (cs k) \<and> cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i \<longrightarrow> 
          (\<exists>el j. getspc_e (el!0) = getx_es ((cs k)!i) k \<and> j < length el \<and> el!j = rm_evtsys1 ((cs k)!i)   
               \<and> el \<in> cpts_ev \<and> el \<in> preserves_e))" by fastforce
            }
          next
            {
              fix prea pre' relya rely' guar' guara post' posta esys
              assume p0: "\<turnstile> (esspc::('l,'k,'s) rgformula_ess) sat\<^sub>s [pre, rely, guar, post]"
                 and p1: "prea \<subseteq> pre'"
                 and p2: "relya \<subseteq> rely'"
                 and p3: "guar' \<subseteq> guara"
                 and p4: "post' \<subseteq> posta"
                 and p5: "\<turnstile> esys sat\<^sub>s [pre', rely', guar', post']"
                 and p6[rule_format]: "\<forall>c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd.
          Pre k \<subseteq> pre' \<and> Rely k \<subseteq> rely' \<and> guar' \<subseteq> Guar k \<and> post' \<subseteq> Post k \<longrightarrow>
          c \<in> cpts_of_pes pes s x \<and> c \<propto> cs \<and> c \<in> assume_pes (pre1, rely1) \<longrightarrow>
          (\<forall>k. cs k \<in> cpts_of_es (pes k) s x) \<longrightarrow>
          (\<forall>k. cs k \<in> commit_es (Guar k, Post k)) \<longrightarrow>
          (\<forall>k. pre1 \<subseteq> Pre k) \<longrightarrow>
          (\<forall>k. rely1 \<subseteq> Rely k) \<longrightarrow>
          (\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k) \<longrightarrow>
          evtsys_spec esys = EvtSys es \<and> EvtSys es = getspc_es (cs k ! 0) \<longrightarrow>
          (\<forall>e\<in>all_evts_es esys. is_basicevt (E\<^sub>e e)) \<longrightarrow>
          (\<forall>e\<in>all_evts_es esys. the (evtrgfs (E\<^sub>e e)) = snd e) \<longrightarrow>
          (\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c ! j -pes-actk\<rightarrow> c ! Suc j)) \<longrightarrow> (\<forall>i. Suc i < length (cs k) \<and> 
          cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i \<longrightarrow> (\<exists>el j. getspc_e (el!0) = getx_es ((cs k)!i) k \<and>
          j < length el \<and> el!j = rm_evtsys1 ((cs k)!i) \<and> el \<in> cpts_ev \<and> el \<in> preserves_e))"
              {
                fix c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd
                assume a0: "Pre k \<subseteq> prea \<and> Rely k \<subseteq> relya \<and> guara \<subseteq> Guar k \<and> posta \<subseteq> Post k"
                   and a1: "c \<in> cpts_of_pes pes s x \<and> c \<propto> cs \<and> c \<in> assume_pes (pre1, rely1)"
                   and a2: "(\<forall>k. cs k \<in> cpts_of_es (pes k) s x)"
                   and a3: "\<forall>k. (cs k)\<in>commit_es(Guar k, Post k)"
                   and a5: "(\<forall>k. pre1 \<subseteq> Pre k)"
                   and a6: "(\<forall>k. rely1 \<subseteq> Rely k)"
                   and a7: "(\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k)"
                   and a8: "evtsys_spec esys = EvtSys es \<and> EvtSys es = getspc_es (cs k ! 0)"
                   and a9: "(\<forall>e\<in>all_evts_es esys. is_basicevt (E\<^sub>e e))"
                   and a10: "(\<forall>e\<in>all_evts_es esys. the (evtrgfs (E\<^sub>e e)) = snd e)"
                   and a11: "(\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c ! j -pes-actk\<rightarrow> c ! Suc j))"
                from a0 p1 p2 p3 p4 have "Pre k \<subseteq> pre' \<and> Rely k \<subseteq> rely' \<and> guar' \<subseteq> Guar k \<and> post' \<subseteq> Post k" by auto
                with a1 a2 a3 a5 a6 a7 a8 a9 a10 a11 p1 p2 p3 p4 p6[of Pre k Rely Guar Post c pes s x cs pre1 rely1]
                have "\<forall>i. Suc i < length (cs k) \<and> cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i \<longrightarrow> 
                (\<exists>el j. getspc_e (el!0) = getx_es ((cs k)!i) k \<and> j < length el \<and> el!j = rm_evtsys1 ((cs k)!i)   
               \<and> el \<in> cpts_ev \<and> el \<in> preserves_e)" by force

              }
              then show "       \<forall>c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd.
          Pre k \<subseteq> prea \<and> Rely k \<subseteq> relya \<and> guara \<subseteq> Guar k \<and> posta \<subseteq> Post k \<longrightarrow>
          c \<in> cpts_of_pes pes s x \<and> c \<propto> cs \<and> c \<in> assume_pes (pre1, rely1) \<longrightarrow>
          (\<forall>k. cs k \<in> cpts_of_es (pes k) s x) \<longrightarrow>
          (\<forall>k. cs k \<in> commit_es (Guar k, Post k)) \<longrightarrow>
          (\<forall>k. pre1 \<subseteq> Pre k) \<longrightarrow>
          (\<forall>k. rely1 \<subseteq> Rely k) \<longrightarrow>
          (\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k) \<longrightarrow>
          evtsys_spec esys = EvtSys es \<and> EvtSys es = getspc_es (cs k ! 0) \<longrightarrow>
          (\<forall>e\<in>all_evts_es esys. is_basicevt (E\<^sub>e e)) \<longrightarrow>
          (\<forall>e\<in>all_evts_es esys. the (evtrgfs (E\<^sub>e e)) = snd e) \<longrightarrow>
          (\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c ! j -pes-actk\<rightarrow> c ! Suc j)) \<longrightarrow> (\<forall>i. Suc i < length (cs k) 
          \<and> cs k ! i -es-Cmd cmd\<sharp>k\<rightarrow> cs k ! Suc i \<longrightarrow> (\<exists>el j. getspc_e (el!0) = getx_es ((cs k)!i) k \<and> 
          j < length el \<and> el!j = rm_evtsys1 ((cs k)!i) \<and> el \<in> cpts_ev \<and> el \<in> preserves_e))" by fastforce
            }
          
          qed

lemma act_cptpes_sat_e_sim: 
  "\<lbrakk>\<turnstile> (pesf::('l,'k,'s) rgformula_par) SAT [pre, {}, UNIV, post]\<rbrakk> \<Longrightarrow> 
      s0\<in>pre \<longrightarrow>
      (\<forall>ef\<in>all_evts pesf. is_basicevt (E\<^sub>e ef)) \<longrightarrow>
      (\<forall>erg\<in>all_evts pesf. the (evtrgfs (E\<^sub>e erg)) = snd erg) \<longrightarrow>
      pesl\<in>cpts_of_pes (paresys_spec pesf) s0 x0 \<longrightarrow> 
      (\<forall>j. Suc j < length pesl \<longrightarrow> (\<exists>actk. pesl!j-pes-actk\<rightarrow>pesl!Suc j)) \<longrightarrow> pesl \<propto> cs \<longrightarrow>
      (\<forall>k i. Suc i <length pesl \<longrightarrow> (\<exists>c. (pesl!i -pes-((Cmd c)\<sharp>k)\<rightarrow> pesl!(Suc i)))
          \<longrightarrow> (\<exists>el j. getspc_e (el!0) = getx_es ((cs k)!i) k \<and> j < length el \<and> el!j = rm_evtsys1 ((cs k)!i)   
               \<and> el \<in> cpts_ev \<and> el \<in> preserves_e))"
  apply(rule rghoare_pes.induct[of pesf pre "{}" UNIV post]) 
    apply simp
   prefer 2
   apply blast
  sorry


end


(*
lemma act_cpts_evtsys_sat_e_sim[rule_format]:
  "\<lbrakk>\<turnstile> (esspc::('l,'k,'s) rgformula_ess) sat\<^sub>s [pre, rely, guar, post]\<rbrakk>
      \<Longrightarrow> \<forall>c pes s x cs pre1 rely1 Pre Rely Guar Post k cmd. 
            Pre k \<subseteq> pre \<and> Rely k \<subseteq> rely \<and> guar \<subseteq> Guar k \<and> post \<subseteq> Post k \<longrightarrow>
            c\<in>cpts_of_pes pes s x \<and> c \<propto> cs \<and> c\<in>assume_pes(pre1, rely1) \<longrightarrow>
           (\<forall>k. (cs k) \<in> cpts_of_es (pes k) s x)  \<longrightarrow> 
           (\<forall>k. (cs k)\<in> commit_es(Guar k, Post k)) \<longrightarrow>
           (\<forall>k. pre1 \<subseteq> Pre k) \<longrightarrow>
           (\<forall>k. rely1 \<subseteq> Rely k) \<longrightarrow>
           (\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k) \<longrightarrow>
           evtsys_spec esspc = EvtSys es \<and>  EvtSys es = getspc_es (cs k!0) \<longrightarrow>
           (\<forall>e\<in>all_evts_es esspc. is_basicevt (E\<^sub>e e)) \<longrightarrow>
           (\<forall>e\<in>all_evts_es esspc. the (evtrgfs (E\<^sub>e e)) = snd e) \<longrightarrow>
           (\<forall>j. Suc j < length c \<longrightarrow> (\<exists>actk. c!j-pes-actk\<rightarrow>c!Suc j)) \<longrightarrow>
          (\<forall>i. Suc i < length (cs k) \<and> ((cs k)!i -es-((Cmd cmd)\<sharp>k)\<rightarrow> (cs k)!(Suc i)) 
          \<longrightarrow>  (\<exists>el s x j.  j < i \<and> el = ((getx_es ((cs k)!i) k), s, x) 
              # rm_evtsys (drop j (take (Suc i) (cs k))) \<and> el \<in> cpts_ev \<and> el \<in> preserves_e))"
*)
(*
lemma act_cptpes_sat_e_sim: 
  "\<lbrakk>\<turnstile> (pesf::('l,'k,'s) rgformula_par) SAT [pre, {}, UNIV, post]\<rbrakk> \<Longrightarrow> 
      s0\<in>pre \<longrightarrow>
      (\<forall>ef\<in>all_evts pesf. is_basicevt (E\<^sub>e ef)) \<longrightarrow>
      (\<forall>erg\<in>all_evts pesf. the (evtrgfs (E\<^sub>e erg)) = snd erg) \<longrightarrow>
      pesl\<in>cpts_of_pes (paresys_spec pesf) s0 x0 \<longrightarrow> 
      (\<forall>j. Suc j < length pesl \<longrightarrow> (\<exists>actk. pesl!j-pes-actk\<rightarrow>pesl!Suc j)) \<longrightarrow> pesl \<propto> cs \<longrightarrow>
      (\<forall>k i. Suc i <length pesl \<longrightarrow> (\<exists>c. (pesl!i -pes-((Cmd c)\<sharp>k)\<rightarrow> pesl!(Suc i)))
          \<longrightarrow> (\<exists>el ef s x j. ef \<in> all_evts pesf \<and> j < i \<and> el = ((E\<^sub>e ef), s, x) 
              # rm_evtsys (drop j (take (Suc i) (cs k))) \<and> el \<in> cpts_ev \<and> el \<in> preserves_e))"
  sorry
*) 