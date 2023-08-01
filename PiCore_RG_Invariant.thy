(*
Created by Yongwang Zhao (ywzhao@ntu.edu.sg, zhaoyw@buaa.edu.cn)
School of Computer Engineering, Nanyang Technological University, Singapore
and School of Computer Science & Engineering, Beihang University, China
*)

section \<open>Rely-guarantee-based Safety Reasoning\<close>

theory PiCore_RG_Invariant
imports PiCore_RG_Prop 
begin

type_synonym 's invariant = "'s set"

definition no_environment :: "('l,'k,'s) pesconfs \<Rightarrow> bool"
  where "no_environment pesl \<equiv> (\<forall>j. Suc j < length pesl \<longrightarrow> (\<exists>actk. pesl!j-pes-actk\<rightarrow>pesl!Suc j))"

definition invariant_of_pares::"('l,'k,'s) paresys \<Rightarrow> 's set \<Rightarrow> 's invariant \<Rightarrow> bool"
  where "invariant_of_pares pares init invar \<equiv> 
          \<forall>s0 x0 pesl. s0\<in>init \<and> pesl\<in>cpts_of_pes pares s0 x0 \<and> no_environment pesl
                          \<longrightarrow> (\<forall>i<length pesl. gets (pesl!i) \<in> invar)"

theorem invariant_theorem:
  assumes parsys_sat_rg: "\<turnstile> pesf SAT [init, {}, UNIV, UNIV]"
    and   all_evts_are_basic: "\<forall>ef\<in>all_evts pesf. is_basicevt (E\<^sub>e ef)"
    and   evt_in_parsys_in_evtrgfs: "\<forall>erg\<in>all_evts pesf. the (evtrgfs (E\<^sub>e erg)) = snd erg" 
    and   stb_invar: "\<forall>ef\<in>all_evts pesf. stable invar (Guar\<^sub>e ef)"
    and   init_in_invar: "init\<subseteq>invar"
  shows "invariant_of_pares (paresys_spec pesf) init invar"
  proof -
  {
    fix s0 x0 pesl
    assume a0: "s0\<in>init"
      and  a1: "pesl\<in>cpts_of_pes (paresys_spec pesf) s0 x0"
      and  "no_environment pesl"
    then have a2: "\<forall>j. Suc j < length pesl \<longrightarrow> (\<exists>actk. pesl!j-pes-actk\<rightarrow>pesl!Suc j)" by (simp add:no_environment_def)
    from a1 have a3: "pesl!0 = (paresys_spec pesf, s0, x0) \<and> pesl\<in>cpts_pes" by (simp add:cpts_of_pes_def)

    {
      fix i
      assume b0: "i<length pesl"
      then have "gets (pesl!i) \<in> invar"
        proof(induct i)
          case 0 
          with a3 have "gets (pesl!0) = s0" by (simp add:gets_def)
          with a0 init_in_invar show ?case by auto
        next
          case (Suc ni)
          assume c0: "ni < length pesl \<Longrightarrow> gets (pesl ! ni) \<in> invar"
            and  c1: "Suc ni < length pesl"
          then have c2: "gets (pesl ! ni) \<in> invar" by auto
          from a3 c1 have "pesl ! ni -pese\<rightarrow> pesl ! Suc ni \<or> (\<exists>et. pesl ! ni -pes-et\<rightarrow> pesl ! Suc ni)"
            using incpts_pes_impl_evnorcomptran by blast
          then show ?case
            proof
              assume d0: "pesl ! ni -pese\<rightarrow> pesl ! Suc ni"
              then show ?thesis using a2 c1 pes_tran_not_etran1 by blast
            next
              assume "\<exists>et. pesl ! ni -pes-et\<rightarrow> pesl ! Suc ni"
              then obtain et where d0: "pesl ! ni -pes-et\<rightarrow> pesl ! Suc ni" by auto
              then obtain act and k where d1: "et = act\<sharp>k" using get_actk_def by (metis actk.cases)
              then show ?thesis
                proof(induct act)
                  case (Cmd x)
                  assume e0: "et = Cmd x\<sharp>k"
                  have e1: "(gets (pesl!ni),gets (pesl!Suc ni))\<in> Guar\<^sub>f (the (evtrgfs (getx (pesl!ni) k)))" 
                    using act_cptpes_sat_guar_curevt_new2[of pesf init UNIV s0 evtrgfs pesl x0] 
                      parsys_sat_rg a0 all_evts_are_basic evt_in_parsys_in_evtrgfs a1 a2 c1 d0 e0 by auto
                  
                  have "\<exists>ef\<in>all_evts pesf. getx (pesl!ni) k = E\<^sub>e ef" 
                    using cur_evt_in_specevts[of pesl pesf s0 x0] a1 a2 all_evts_are_basic c1 d0 e0 by auto
                  then obtain ef where e2: "ef\<in>all_evts pesf \<and> getx (pesl!ni) k = E\<^sub>e ef" by auto
                  with e1 have "(gets (pesl!ni),gets (pesl!Suc ni))\<in>Guar\<^sub>e ef" using evt_in_parsys_in_evtrgfs
                    by (simp add: Guar\<^sub>e_def Guar\<^sub>f_def)
                  with stb_invar e2 c2 show ?case by (meson stable_def) 
                next
                  case (EvtEnt x)
                  assume e0: "et = EvtEnt x\<sharp>k"
                  with c2 d0 show ?case using evtent_in_pes_notchgstate2[of "pesl ! ni" x k "pesl ! Suc ni"] by simp
                qed
            qed
        qed
    }
  }
  then show ?thesis using invariant_of_pares_def by blast
  qed

end