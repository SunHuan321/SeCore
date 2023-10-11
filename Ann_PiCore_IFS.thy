theory Ann_PiCore_IFS
  imports Ann_PiCore_Semantics
begin

subsection \<open>Information Flow Security Definition\<close>

(*identifying an action: the action type, its event, the execution core, and its execution domain*)
record ('l,'k,'s,'d) action = 
        actk :: "('l,'k,'s) actk"
        eventof :: "('l,'k,'s) event"
        domain ::  "'d"
(*
primrec dom_helper :: "('s \<Rightarrow> 'k \<Rightarrow> ('l,'k,'s) event \<Rightarrow> 'd) \<Rightarrow> 's \<Rightarrow> ('l,'k,'s) x 
                        \<Rightarrow> ('l,'k,'s) act \<Rightarrow> 'k \<Rightarrow> 'd" where
  dom_Comp:   "dom_helper dome s x (Cmd c) k = dome s k (x k)" |
  dom_EnvEnt: "dom_helper dome s x (EvtEnt e) k = dome s k e"
*)

locale InfoFlow = 
  fixes C0  ::  "('l,'k,'s) pesconf"
  fixes step :: "('l,'k,'s,'d) action \<Rightarrow> (('l,'k,'s) pesconf \<times> ('l,'k,'s) pesconf) set"
  fixes interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
  fixes vpeq ::  "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<sim>_\<sim> _)" [70,69,70] 60)
  fixes obs ::  "'s \<Rightarrow> 'd \<Rightarrow> 'o" (infixl "\<guillemotright>"  55)
  fixes dome :: "'s \<Rightarrow> 'k \<Rightarrow> ('l,'k,'s) event \<Rightarrow> 'd"
  assumes vpeq_transitive : "\<forall> a b c u. (a \<sim> u \<sim> b) \<and> (b \<sim> u \<sim> c) \<longrightarrow> (a \<sim> u \<sim> c)"
    and   vpeq_symmetric : "\<forall> a b u. (a \<sim> u \<sim> b) \<longrightarrow> (b \<sim> u \<sim> a)"
    and   vpeq_reflexive : "\<forall> a u. (a \<sim> u \<sim> a)"
    and   step_def : "step a \<equiv> {(P,Q). (P -pes-(actk a)\<rightarrow> Q) \<and> 
                                        ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                                              \<and> dome (gets P) k e = domain a) \<or>
                                        (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx P) k 
                                          \<and> dome (gets P) k (eventof a) = domain a))}"
    (*and   step_def : "step a \<equiv> {(P,Q). (P -pes-(actk a)\<rightarrow> Q) \<and> (*domc dome P (actk a)*) 
                                dom_helper dome (gets P) (getx P) (Act (actk a)) (K (actk a)) = domain a}"*)
begin

definition noninterf :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<setminus>\<leadsto> _)" [70,71] 60)
 where "u \<setminus>\<leadsto> v \<equiv> \<not> (u \<leadsto> v)"

(*
primrec dom' :: "'s \<Rightarrow> ('l,'k,'s) x \<Rightarrow> ('l,'k,'s) act \<Rightarrow> 'k \<Rightarrow> 'd" where
  dom_Comp:   "dom' s x (Cmd c) k = dome s k (x k)" |
  dom_EnvEnt: "dom' s x (EvtEnt e) k = dome s k e"

definition dom :: "'s \<Rightarrow> ('l,'k,'s) x \<Rightarrow> ('l,'k,'s) actk \<Rightarrow> 'd" where
  "dom s x a \<equiv> dom' s x (Act a) (K a)"

definition domc :: "('l,'k,'s) pesconf \<Rightarrow> ('l,'k,'s) actk \<Rightarrow> 'd"
  where "domc C a \<equiv> dom (gets C) (getx C) a"

definition step :: "('l,'k,'s,'d) action \<Rightarrow> (('l,'k,'s) pesconf \<times> ('l,'k,'s) pesconf) set" where
  "step a \<equiv> {(P,Q). (P -p-(actk a)\<rightarrow> Q) \<and> domc P (actk a) = domain a}"
*)

definition vpeqc :: "('l,'k,'s) pesconf \<Rightarrow> 'd \<Rightarrow> ('l,'k,'s) pesconf \<Rightarrow> bool" ("(_ \<sim>._.\<sim> _)" [70,71] 60)
   where "vpeqc C1 u C2 \<equiv> (gets C1) \<sim>u\<sim> (gets C2)"

lemma vpeqc_transitive: "\<forall> a b c u. (a \<sim>.u.\<sim> b) \<and> (b \<sim>.u.\<sim> c) \<longrightarrow> (a \<sim>.u.\<sim> c)"
  using vpeq_transitive vpeqc_def by blast

lemma vpeqc_symmetric: "\<forall> a b u. (a \<sim>.u.\<sim> b) \<longrightarrow> (b \<sim>.u.\<sim> a)"
  using vpeq_symmetric vpeqc_def by blast

lemma vpeqc_reflexive: "\<forall> a u. (a \<sim>.u.\<sim> a)"
  by (simp add: vpeq_reflexive vpeqc_def)

definition ivpeq :: "'s \<Rightarrow> 'd set \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<approx> _ \<approx> _)" [70,71] 60)
    where "ivpeq s D t \<equiv> \<forall> d \<in> D. (s \<sim> d \<sim> t)"

definition ivpeqc :: "('l,'k,'s) pesconf \<Rightarrow> 'd set \<Rightarrow> ('l,'k,'s) pesconf \<Rightarrow> bool" ("(_ \<approx>._.\<approx> _)" [70,71] 60)
    where "ivpeqc C1 D C2 \<equiv> \<forall> d \<in> D. (C1 \<sim>.d.\<sim> C2)"

(*
definition step :: "('l,'k,'s,'d) action \<Rightarrow> (('l,'k,'s) pesconf \<times> ('l,'k,'s) pesconf) set" where
  "step a \<equiv> {(P,Q). (P -p-(actk a)\<rightarrow> Q) \<and> domc P (actk a) = domain a}"
*)

(*the next configuration set of executing an action from one configuration*)
definition nextc :: "('l,'k,'s) pesconf \<Rightarrow> ('l,'k,'s,'d) action \<Rightarrow>  ('l,'k,'s) pesconf set" where
  "nextc P a \<equiv> {Q. (P,Q)\<in>step a}"

definition stepable :: "('l,'k,'s) pesconf \<Rightarrow> bool" where
  "stepable C \<equiv> \<exists>a C'. (C,C')\<in>step a"
      

primrec run :: "('l,'k,'s,'d) action list \<Rightarrow> (('l,'k,'s) pesconf \<times> ('l,'k,'s) pesconf) set" where
  run_Nil:  "run [] = Id " |
  run_Cons: "run (a#as) = {(P,Q). (\<exists>R. (P,R) \<in> step a \<and> (R,Q) \<in> run as)}"


(* only require that there is at least one executable path*)
definition runnable :: "('l,'k,'s) pesconf \<Rightarrow> ('l,'k,'s,'d) action list \<Rightarrow> bool" ("(_ \<^bsub> _)" [70,70] 60)
  where "runnable C as \<equiv> \<exists>C'. (C,C') \<in> run as"

lemma runnable_empty : "runnable C []"
  by (metis IdI run_Nil runnable_def)  

lemma run_trans : "\<forall>C T V as bs. (C,T)\<in>run as \<and> (T,V)\<in>run bs \<longrightarrow> (C,V)\<in>run (as@bs)"
  proof -
  {
    fix T V as bs
    have "\<forall>C. (C,T)\<in>run as \<and> (T,V)\<in>run bs \<longrightarrow> (C,V)\<in>run (as@bs)"
      proof(induct as)
        case Nil show ?case by simp
      next
        case (Cons c cs)
        assume a0: "\<forall>C. (C, T) \<in> run cs \<and> (T, V) \<in> run bs \<longrightarrow> (C, V) \<in> run (cs @ bs)"
        show ?case
          proof-
          {
            fix C
            have "(C, T) \<in> run (c # cs) \<and> (T, V) \<in> run bs \<longrightarrow> (C, V) \<in> run ((c # cs) @ bs) "
              proof
                assume b0: "(C, T) \<in> run (c # cs) \<and> (T, V) \<in> run bs"
                (*assume b1: "(T, V) \<in> run bs"*)
                from b0 obtain C' where b2: "(C,C')\<in>step c \<and> (C',T)\<in>run cs" by auto
                with a0 b0 have "(C',V)\<in>run (cs@bs)" by blast
                with b2 show "(C, V) \<in> run ((c # cs) @ bs)"
                  by (metis (mono_tags, lifting) CollectI append_Cons case_prodI run_Cons) 
              qed
          }
          then show ?thesis by auto
          qed
      qed
  }
  then show ?thesis by auto
  qed

definition reachable :: "('l,'k,'s) pesconf \<Rightarrow> ('l,'k,'s) pesconf \<Rightarrow> bool" ("(_ \<hookrightarrow> _)" [70,71] 60) where
  "reachable C1 C2 \<equiv>  (\<exists>as. (C1,C2) \<in> run as)"

definition reachable0 :: "('l,'k,'s) pesconf \<Rightarrow> bool"  where
  "reachable0 C \<equiv> reachable C0 C"

lemma reachableC0 : "reachable0 C0"
  by (metis IdI reachable0_def reachable_def run_Nil)

lemma reachable_self : "reachable C C"
  by (metis IdI reachable_def run_Nil)
  
lemma reachable_step : "(C,C')\<in>step a \<Longrightarrow> reachable C C'"
  proof-
    assume a0: "(C,C')\<in>step a"
    then have "(C,C')\<in>run [a]"
      by (metis (mono_tags, lifting) IdI case_prod_conv mem_Collect_eq run_Cons run_Nil)
    then show ?thesis using reachable_def by blast 
  qed

lemma reachable_trans : "\<lbrakk>reachable C T; reachable T V\<rbrakk> \<Longrightarrow> reachable C V"
  proof-
    assume a0: "reachable C T"
    assume a1: "reachable T V"
    from a0 have "C = T \<or> (\<exists>as. (C,T)\<in>run as)" using reachable_def by simp
    then show ?thesis
      proof
        assume b0: "C = T"
        show ?thesis 
          proof -
            from a1 have "T = V \<or> (\<exists>as. (T,V)\<in>run as)" using reachable_def by simp
            then show ?thesis
              proof
                assume c0: "T=V"
                with a0 show ?thesis by simp
              next
                assume c0: "(\<exists>as. (T,V)\<in>run as)"
                then show ?thesis by (simp add: a1 b0) 
              qed
          qed
      next
        assume b0: "\<exists>as. (C,T)\<in>run as"
        show ?thesis
          proof -
            from a1 have "T = V \<or> (\<exists>as. (T,V)\<in>run as)" using reachable_def by simp
            then show ?thesis
              proof
                assume c0: "T=V"
                then show ?thesis using a0 by auto 
              next
                assume c0: "(\<exists>as. (T,V)\<in>run as)"
                from b0 obtain as where d0: "(C,T)\<in>run as" by auto
                from c0 obtain bs where d1: "(T,V)\<in>run bs" by auto
                then show ?thesis using d0 reachable_def run_trans by blast 
              qed
          qed
      qed
  qed

lemma reachableStep : "\<lbrakk>reachable0 C; (C,C')\<in>step a\<rbrakk> \<Longrightarrow> reachable0 C'"
  proof -
    assume a0: "reachable0 C"
    assume a1: "(C,C')\<in>step a"
    from a0 have "(C = C0) \<or> (\<exists>as. (C0,C) \<in> run as)" unfolding reachable0_def reachable_def by auto
    then show "reachable0 C'"
      proof
        assume b0: "C = C0"
        show "reachable0 C'"
          using a1 b0 reachable0_def reachable_step by auto 
      next
        assume b0: "\<exists>as. (C0,C) \<in> run as"
        show "reachable0 C'"
          using a0 a1 reachable0_def reachable_step reachable_trans by blast 
      qed
  qed

lemma reachable0_reach : "\<lbrakk>reachable0 C; reachable C C'\<rbrakk> \<Longrightarrow> reachable0 C'"
  using reachable0_def reachable_trans by blast
  
primrec sources :: "('l,'k,'s,'d) action list \<Rightarrow> 'd \<Rightarrow> 'd set" where
  sources_Nil:  "sources [] u = {u}" |
  sources_Cons: "sources (a#as) u = (sources as u) \<union> {w. w = domain a \<and> (\<exists>v. (w \<leadsto> v) \<and> v \<in> sources as u)}"
declare sources_Nil [simp del]     
declare sources_Cons [simp del]

primrec ipurge :: "('l,'k,'s,'d) action list \<Rightarrow> 'd \<Rightarrow> ('l,'k,'s,'d) action list" where
  ipurge_Nil:   "ipurge [] u = []" |
  ipurge_Cons:  "ipurge (a#as) u = (if  domain a \<in> sources (a#as) u then
                                          a # ipurge as u
                                       else
                                          ipurge as u
                                      )"

lemma sources_ipurge: "sources (ipurge as u) u = sources as u"
  proof -
    have "\<forall>as u. sources (ipurge as u) u = sources as u"
      proof -
      {
        fix as
        have "\<forall>u. sources (ipurge as u) u = sources as u"
          proof(induct as)
            case Nil show ?case by simp
          next
            case (Cons b bs)
            assume a0: "\<forall>u. sources (ipurge bs u) u = sources bs u"
            show ?case
            proof -
            {
              fix u
              have "sources (ipurge (b # bs) u) u = sources (b # bs) u"
                proof(cases "domain b\<in>sources (b#bs) u")
                  assume b0: "domain b\<in>sources (b#bs) u"
                  then have b1: "ipurge (b # bs) u = b # ipurge bs u"
                    by (simp add: sources_Cons) 
                  from a0 have b2: "sources (ipurge bs u) u = sources bs u" by simp
                  from b1 have b3: "sources (ipurge (b # bs) u) u = sources (b # ipurge bs u) u" by simp
                  with b0 b2 have b4: "sources (ipurge (b # bs) u) u = {domain b} \<union> sources (ipurge bs u) u"
                    using sources_Cons by auto 
                  from b0 have b5: "sources (b # bs) u = {domain b} \<union> sources bs u" using sources_Cons by auto 
                  then show ?thesis using a0 b4 by auto 
                next
                  assume b0: "\<not> domain b\<in>sources (b#bs) u"
                  then have b1: "sources (ipurge (b # bs) u) u = sources (ipurge bs u) u" using sources_Cons by auto 
                  from b0 have b2: "sources (b # bs) u = sources bs u" using sources_Cons by auto 
                  with a0 b1 show ?thesis by auto
                qed
            }
            then show ?thesis by auto
            qed
        qed
      }
      then show ?thesis by auto
      qed
    then show ?thesis by auto
    qed

lemma ipurge_eq: "ipurge as u = ipurge (ipurge as u) u"
  proof -
    have "\<forall>as u. ipurge as u = ipurge (ipurge as u) u"
      proof -
      {
        fix as
        have "\<forall>u. ipurge as u = ipurge (ipurge as u) u"
          proof(induct as)
            case Nil show ?case by simp
          next
            case (Cons b bs)
            assume a0: "\<forall>u. ipurge bs u = ipurge (ipurge bs u) u"
            show ?case
            proof -
            {
              fix u
              have "ipurge (b # bs) u = ipurge (ipurge (b # bs) u) u "
                proof(cases "domain b\<in>sources (b#bs) u")
                  assume b0: "domain b\<in>sources (b#bs) u"
                  then have b1: "ipurge (b # bs) u = b # ipurge bs u" by simp
                  then have b2: "ipurge (ipurge (b # bs) u) u = ipurge (b # ipurge bs u) u" by simp
                  have b3: "sources (b#bs) u = sources (b#ipurge bs u) u" using sources_ipurge by (metis b1) 
                  with b1 b2 show ?thesis using a0 by auto 
                next
                  assume b0: "\<not> domain b\<in>sources (b#bs) u"
                  then have b1: "ipurge (b # bs) u = ipurge bs u" by simp
                  then have b2: "ipurge (ipurge (b # bs) u) u = ipurge (ipurge bs u) u" by simp
                  with b1 show ?thesis  using a0 by auto 
                qed
            }
            then show ?thesis by auto
            qed
          qed
      }
      then show ?thesis by auto
      qed
    then show ?thesis by auto
  qed

definition exec_equiv :: "('l,'k,'s) pesconf \<Rightarrow> ('l,'k,'s,'d) action list \<Rightarrow> 'd \<Rightarrow> ('l,'k,'s) pesconf \<Rightarrow> 
           ('l,'k,'s,'d) action list \<Rightarrow> bool" ("(_ \<lhd> _ \<simeq> _ \<simeq> _ \<lhd> _)" [80,80,80,80,80] 75)
    where "exec_equiv S as u T bs \<equiv> \<forall>S' T'. ((S,S')\<in> run as \<and> (T,T')\<in> run bs) \<longrightarrow>  (gets S' \<guillemotright> u = gets T' \<guillemotright> u)"

lemma exec_equiv_sym : "(S \<lhd> as \<simeq> u \<simeq> T \<lhd> bs) \<Longrightarrow> (T \<lhd> bs \<simeq> u \<simeq> S \<lhd> as)"
  by (metis exec_equiv_def)

(*exec_equiv is transitive if runnable*)
lemma exec_equiv_trans : "\<lbrakk>runnable T bs; (S \<lhd> as \<simeq> u \<simeq> T \<lhd> bs); (T \<lhd> bs \<simeq> u \<simeq> V \<lhd> cs)\<rbrakk> \<Longrightarrow> (S \<lhd> as \<simeq> u \<simeq> V \<lhd> cs)"
proof - 
  assume a0: "S \<lhd> as \<simeq> u \<simeq> T \<lhd> bs"
  assume a1: "T \<lhd> bs \<simeq> u \<simeq> V \<lhd> cs"
  assume a2: "runnable T bs"
  have g: "S \<lhd> as \<simeq> u \<simeq> V \<lhd> cs"
    proof - 
    {
      fix a aa b ab ac ba
      assume b0: "(S, a, aa, b) \<in> run as"
      assume b1: "(V, ab, ac, ba) \<in> run cs"
      have "aa \<guillemotright> u = ac \<guillemotright> u"
        proof -
          from a0 b0 have c0: "\<forall>T'. ((T,T') \<in> run bs) \<longrightarrow> (aa \<guillemotright> u = gets T' \<guillemotright> u)"
            using exec_equiv_def gets_def by (metis fst_conv snd_conv) 
          from a1 b1 have c1: "\<forall>T'. ((T,T') \<in> run bs) \<longrightarrow> (ac \<guillemotright> u = gets T' \<guillemotright> u)"
            using exec_equiv_def gets_def by (metis fst_conv snd_conv) 
          with c0 show ?thesis using a2 runnable_def by fastforce 
        qed
    }
    then show ?thesis using exec_equiv_def gets_def using a0 a1 a2 runnable_def by metis 
    qed
  then show ?thesis by auto
qed

lemma exec_equiv_notr: "\<not>runnable C as \<Longrightarrow> (C \<lhd> as \<simeq> u \<simeq> D \<lhd> bs)"
  by (simp add: exec_equiv_def runnable_def) 

lemma exec_equiv_leftI:
   "\<lbrakk>reachable0 C; \<forall> C'\<in>nextc C a. (C' \<lhd> as \<simeq> u \<simeq> D \<lhd> bs)\<rbrakk> \<Longrightarrow> (C \<lhd> (a # as) \<simeq> u \<simeq> D \<lhd> bs)"
  proof -
    assume a0: "reachable0 C"
    assume a1: "\<forall> C'\<in>nextc C a. (C' \<lhd> as \<simeq> u \<simeq> D \<lhd> bs)"
    have "\<forall>S' T'. (C, S') \<in> run (a # as) \<and> (D, T') \<in> run bs \<longrightarrow> gets S' \<guillemotright> u = gets T' \<guillemotright> u" 
      proof -
      {
        fix S' T'
        assume b0: "(C, S') \<in> run (a # as) \<and> (D, T') \<in> run bs"
        then obtain C' where b1: "C'\<in>nextc C a \<and> (C',S')\<in>run as"
          using nextc_def step_def by fastforce 
        with a1 have b2: "(C' \<lhd> as \<simeq> u \<simeq> D \<lhd> bs)" by simp
        with b0 b1 have "gets S' \<guillemotright> u = gets T' \<guillemotright> u" using exec_equiv_def by blast 
      }
      then show ?thesis by auto
      qed
    then show ?thesis using exec_equiv_def by simp 
  qed

lemma exec_equiv_both:
   "\<lbrakk>reachable0 C1; reachable0 C2; \<forall> C1' C2'. C1'\<in>nextc C1 a \<and> C2'\<in>nextc C2 b\<longrightarrow> (C1' \<lhd> as \<simeq> u \<simeq> C2' \<lhd> bs)\<rbrakk> 
      \<Longrightarrow> C1 \<lhd> (a # as) \<simeq> u \<simeq> C2 \<lhd> (b # bs)"
  proof -
    assume a0: "reachable0 C1"
    assume a1: "reachable0 C2"
    assume a2: "\<forall> C1' C2'. C1'\<in>nextc C1 a \<and> C2'\<in>nextc C2 b\<longrightarrow> (C1' \<lhd> as \<simeq> u \<simeq> C2' \<lhd> bs)"
    have "\<forall>S' T'. (C1, S') \<in> run (a # as) \<and> (C2, T') \<in> run (b # bs) \<longrightarrow> gets S' \<guillemotright> u = gets T' \<guillemotright> u"
      proof -
      {
        fix S' T'
        assume b0: "(C1, S') \<in> run (a # as) \<and> (C2, T') \<in> run (b # bs)"
        then obtain C1' where b1: "C1'\<in>nextc C1 a \<and> (C1',S')\<in>run as" 
          using nextc_def step_def by fastforce 
        from b0 obtain C2' where b2: "C2'\<in>nextc C2 b \<and> (C2',T')\<in>run bs"
           using nextc_def step_def by fastforce 
        with a2 b1 have b3: "(C1' \<lhd> as \<simeq> u \<simeq> C2' \<lhd> bs)" by blast
        with b0 b1 b2 have "gets S' \<guillemotright> u = gets T' \<guillemotright> u" using exec_equiv_def by blast 
      }
      then show ?thesis by auto
      qed
    then show ?thesis using exec_equiv_def by simp 
  qed

(* Rushby's noninterference*)
definition noninterference0 :: "bool"
  where "noninterference0 \<equiv> \<forall>u as. (C0 \<lhd> as \<simeq> u \<simeq> C0 \<lhd> (ipurge as u))"

(* reachable state version of Rushby's noninterference*)
definition noninterference0_r :: "bool"
  where "noninterference0_r \<equiv> \<forall>u as C. reachable0 C \<longrightarrow> (C \<lhd> as \<simeq> u \<simeq> C \<lhd> (ipurge as u))"

(* Oheimb's nondeterministic version of noninterference *)
(* It is the same as Oheimb's strong noninterference*)
definition noninterference1 :: "bool" where
  "noninterference1 \<equiv> \<forall>u as bs. (ipurge as u = ipurge bs u)  \<longrightarrow> (C0 \<lhd> as \<simeq> u \<simeq> C0 \<lhd> bs)"

(* reachable state version of Oheimb's strong noninterference *)
definition noninterference1_r :: "bool"
      where "noninterference1_r \<equiv> \<forall>u as bs C. reachable0 C \<longrightarrow> ipurge as u = ipurge bs u \<longrightarrow> (C \<lhd> as \<simeq> u \<simeq> C \<lhd> bs)"

(* Oheimb's nonleakage. The Murray's nonleakage is the same *)
definition nonleakage :: "bool" where
  "nonleakage \<equiv> \<forall>as C1 C2 u. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> (C1 \<approx>.(sources as u).\<approx> C2) 
                                 \<longrightarrow> (C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> as)"

(* Oheimb's noninfluence *)
definition noninfluence0 ::"bool" where
  "noninfluence0 \<equiv> \<forall> u as C1 C2 . (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> (C1 \<approx>.(sources as u).\<approx> C2) 
                                \<longrightarrow> (C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> (ipurge as u))"

(* Murray's noninfluence (without the scheduler) *)
(* replacing ``ipurge bs {C1} u'' by ``ipurge bs {C2} u'' yields and equivalent property as stated in Murray's paper*)
definition noninfluence1 :: "bool" where
  "noninfluence1 \<equiv> \<forall>as bs C1 C2 u. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> (C1 \<approx>.(sources as u).\<approx> C2)
                                 \<longrightarrow> ipurge as u = ipurge bs u \<longrightarrow> (C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> bs)"


subsection \<open>A Infererence Framework of Information Flow Security Properties\<close>
(*
   \<Midarrow>\<Midarrow>\<Midarrow> unwinding conditions
   \<parallel>             \<parallel>
   \<parallel>             \<parallel>(UnwindingTheorem_noninfluence0)
   \<parallel>             \<parallel>
   \<parallel>             \<Down>
   \<parallel>      noninfluence0  \<Midarrow>\<Midarrow>(lm7)\<Longrightarrow>  noninterference0_r  \<Midarrow>\<Midarrow>(lm1)\<Longrightarrow>  noninterference0
   \<parallel>             \<Up>                           \<Up>                              \<Up>
   \<parallel>(UT_nonlk)   \<parallel>(lm8)                      \<parallel>(lm9)                         \<parallel>(lm10)
   \<parallel>             \<parallel>                           \<parallel>                              \<parallel>
   \<parallel>             \<parallel>                           \<parallel>                              \<parallel>
   \<parallel>      noninfluence1  \<Midarrow>\<Midarrow>(lm6)\<Longrightarrow>  noninterference1_r  \<Midarrow>\<Midarrow>(lm2)\<Longrightarrow>  noninterference1
   \<parallel>             \<parallel>
   \<parallel>             \<parallel>(lm5)
   \<parallel>             \<parallel>
   \<parallel>             \<Down>
   \<parallel>\<Midarrow>\<Midarrow>\<Midarrow>\<Longrightarrow>  nonleakage

*)

lemma lm1: "noninterference0_r \<Longrightarrow> noninterference0"
  using noninterference0_def noninterference0_r_def reachableC0 by blast

lemma lm2: "noninterference1_r \<Longrightarrow> noninterference1"
  using noninterference1_def noninterference1_r_def reachableC0 by blast

(*
lemma lm3: "noninterference0 \<Longrightarrow> noninterference1" sorry (*exec_equiv is not transitive, so this is not satisfied*)


lemma lm4: "noninterference0_r \<Longrightarrow> noninterference1_r" sorry (*exec_equiv is not transitive, so this is not satisfied*)
*)

lemma lm5: "noninfluence1 \<Longrightarrow> nonleakage" 
  using noninfluence1_def nonleakage_def by blast

(*lemma lm11: "noninfluence0 \<Longrightarrow> nonleakage" *)

lemma lm6: "noninfluence1 \<Longrightarrow> noninterference1_r" 
  using ivpeqc_def noninfluence1_def noninterference1_r_def vpeqc_reflexive by blast

lemma lm7: "noninfluence0 \<Longrightarrow> noninterference0_r"
  using ivpeqc_def noninfluence0_def noninterference0_r_def vpeqc_reflexive by blast

lemma lm8: "noninfluence1 \<Longrightarrow> noninfluence0"
  using ipurge_eq noninfluence0_def noninfluence1_def by blast 
  
lemma lm9: "noninterference1_r \<Longrightarrow> noninterference0_r"
  using ipurge_eq noninterference0_r_def noninterference1_r_def by blast

lemma lm10: "noninterference1 \<Longrightarrow> noninterference0"
  using ipurge_eq noninterference0_def noninterference1_def by blast
  
subsection \<open>Unwinding Conditions\<close>
(*
definition observed_consistent1 :: "bool" where (*dont know why ``Additional type variable(s) in specification of "observed_consistent1": 'k, 'l, 'p''*)
 "observed_consistent1 \<equiv> (\<forall> C1 C2 u. ((C1 \<sim>.u.\<sim> C2) \<longrightarrow> (gets C1) \<guillemotright> u  = (gets C2) \<guillemotright> u))"
*)
definition observed_consistent :: "bool" where
 "observed_consistent \<equiv> (\<forall> s t u. ((s \<sim> u \<sim> t) \<longrightarrow> s \<guillemotright> u  = t \<guillemotright> u))"

definition locally_respect :: "bool" where
  "locally_respect \<equiv> \<forall>a u C. (reachable0 C) \<longrightarrow> ((domain a) \<setminus>\<leadsto> u) \<longrightarrow> 
                              (\<forall> C'. (C'\<in>nextc C a) \<longrightarrow> (C \<sim>.u.\<sim> C'))"

definition weak_step_consistent :: "bool" where
  "weak_step_consistent \<equiv> \<forall>a u C1 C2. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow>  (C1 \<sim>.u.\<sim> C2)
                         \<and> ((domain a) \<leadsto> u) \<and> (C1 \<sim>.(domain a).\<sim> C2)  \<longrightarrow>
                         (\<forall> C1' C2'. (C1'\<in>nextc C1 a) \<and> (C2'\<in>nextc C2 a) \<longrightarrow> (C1' \<sim>.u.\<sim> C2'))"


definition step_consistent :: "bool" where
  "step_consistent \<equiv> \<forall>a u C1 C2. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow>  (C1 \<sim>.u.\<sim> C2) 
                         \<and> ( ((domain a) \<leadsto> u) \<longrightarrow> (C1 \<sim>.(domain a).\<sim> C2) ) \<longrightarrow> 
                         (\<forall> C1' C2'. (C1'\<in>nextc C1 a) \<and> (C2'\<in>nextc C2 a) \<longrightarrow> (C1' \<sim>.u.\<sim> C2'))"

definition step_consistent2 :: "bool" where
  "step_consistent2 \<equiv> \<forall>a u C1 C2. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow>  (C1 \<sim>.u.\<sim> C2) 
                         \<and> ( ((domain a) \<leadsto> u) \<and> (domain a) \<noteq> u \<longrightarrow> (C1 \<sim>.(domain a).\<sim> C2) ) \<longrightarrow> 
                         (\<forall> C1' C2'. (C1'\<in>nextc C1 a) \<and> (C2'\<in>nextc C2 a) \<longrightarrow> (C1' \<sim>.u.\<sim> C2'))"

definition step_consistent3 :: "bool" where
  "step_consistent3 \<equiv> \<forall>a u C1 C2. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow>  (C1 \<sim>.u.\<sim> C2) 
                         \<and> ( (domain a) = u  ) \<longrightarrow> 
                         (\<forall> C1' C2'. (C1'\<in>nextc C1 a) \<and> (C2'\<in>nextc C2 a) \<longrightarrow> (C1' \<sim>.u.\<sim> C2'))"

subsection \<open>Unwinding Theorem\<close>
  
lemma step_cons_impl_weak : "step_consistent \<Longrightarrow> weak_step_consistent"
  using step_consistent_def weak_step_consistent_def by blast 


lemma sources_unwinding_step:
    "\<lbrakk>C1 \<approx>.(sources (a#as) d).\<approx> C2; step_consistent; C1'\<in>nextc C1 a; C2'\<in>nextc C2 a;
       reachable0 C1; reachable0 C2\<rbrakk>  \<Longrightarrow> C1' \<approx>.(sources as d).\<approx> C2'"
   proof -
    assume a0: "C1 \<approx>.(sources (a#as) d).\<approx> C2"
    assume a1: "step_consistent"
    assume a2: "C1'\<in>nextc C1 a"
    assume a3: "C2'\<in>nextc C2 a"
    assume a4: "reachable0 C1"
    assume a5: "reachable0 C2"
    have a7: "(sources as d) \<subseteq> (sources (a#as) d)" by (simp add: sources_Cons) 
    have "\<forall>u. u\<in>(sources as d) \<longrightarrow> C1' \<sim>.u.\<sim> C2'"
      proof -
      {
        fix u
        assume b0: "u\<in>(sources as d)"
        from a7 b0 have b1: "u \<in> (sources (a#as) d)" by auto
        then have "C1' \<sim>.u.\<sim> C2'"
          proof(cases "domain a \<leadsto> u")
            assume c0: "domain a \<leadsto> u"
            show ?thesis
              proof -
                have d0: "C1 \<sim>.(domain a).\<sim> C2" using a0 b0 c0 ivpeqc_def sources_Cons by auto 
                then have "C1' \<sim>.u.\<sim> C2'" using a0 a1 a2 a3 a4 a5 b1 c0 ivpeqc_def 
                  step_cons_impl_weak weak_step_consistent_def by blast 
                then show ?thesis by auto
              qed
          next
            assume c0: "\<not> (domain a \<leadsto> u)"
            show ?thesis using a0 a1 a2 a3 a4 a5 b1 c0 ivpeqc_def step_consistent_def by blast 
          qed
      }
      then show ?thesis by auto
      qed

    then show ?thesis by (simp add: ivpeqc_def) 
  qed

lemma sources_preserved_left:
  "\<lbrakk>locally_respect; reachable0 C1; reachable0 C2; C1'\<in>nextc C1 a;
    domain a \<notin> sources (a#as) u; C1 \<approx>.(sources (a#as) u).\<approx> C2\<rbrakk> \<Longrightarrow> C1' \<approx>.(sources as u).\<approx> C2"
  proof -
    assume a1: "locally_respect"
    assume a2: "reachable0 C1"
    assume a3: "reachable0 C2"
    assume a4: "C1'\<in>nextc C1 a"
    assume a5: "domain a \<notin> sources (a#as) u"
    assume a6: "C1 \<approx>.(sources (a#as) u).\<approx> C2"
    show "C1' \<approx>.(sources as u).\<approx> C2" 
    proof(clarsimp simp: ivpeqc_def) 
      fix d
      assume b0: "d \<in> sources as u"
      then have b1: "domain a \<setminus>\<leadsto> d" using CollectI a5 noninterf_def sources_Cons by auto 
      from a6 b0 have b2: "C1 \<sim>.d.\<sim> C2" by (simp add: ivpeqc_def sources_Cons) 
      with b1 show "C1' \<sim>.d.\<sim> C2" using a1 a2 a4 locally_respect_def vpeqc_symmetric vpeqc_transitive by blast

    qed
  qed


theorem UnwindingTheorem_noninfluence0:
    assumes p1: observed_consistent
    and     p2: locally_respect
    and     p3: step_consistent
  shows noninfluence0
  proof(subst noninfluence0_def)
    show "\<forall> u as C1 C2 . (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> (C1 \<approx>.(sources as u).\<approx> C2) 
                                \<longrightarrow> (C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> (ipurge as u))"
      proof-
      {
        fix as
        have "\<forall>u C1 C2. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> (C1 \<approx>.(sources as u).\<approx> C2) 
                                \<longrightarrow> (C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> (ipurge as u))"
          proof(induct as)
          case Nil show ?case  
            proof -
            {
              fix u C1 C2
              assume a0:"reachable0 C1 \<and> reachable0 C2"
              assume a1:"C1 \<approx>.sources [] u.\<approx> C2"
              have a2:"C1 \<sim>.u.\<sim> C2" using a1 ivpeqc_def sources_Nil by auto 
              have a3:"ipurge [] u = []" by simp
              from a2 have "C1 \<lhd> [] \<simeq> u \<simeq> C2 \<lhd> []" unfolding exec_equiv_def
                using observed_consistent_def p1 vpeqc_def by fastforce
              with a3 have "C1 \<lhd> [] \<simeq> u \<simeq> C2 \<lhd> ipurge [] u" by auto
            }
            then show ?thesis by auto
            qed
          next
          case (Cons b bs)
            assume a0:"\<forall>u C1 C2. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> 
               (C1 \<approx>.(sources bs u).\<approx> C2) \<longrightarrow> (C1 \<lhd> bs \<simeq> u \<simeq> C2 \<lhd> (ipurge bs u))"
            show ?case 
              proof-
              {
                fix u C1 C2
                assume b0:"reachable0 C1"
                assume b1:"reachable0 C2"
                assume b2:"C1 \<approx>.sources (b # bs) u.\<approx> C2"
                have " C1 \<lhd> (b # bs) \<simeq> u \<simeq> C2 \<lhd> ipurge (b # bs) u"
                  proof(cases "domain b\<in>sources (b # bs) u")
                    assume d0: "domain b\<in>sources (b # bs) u" 
                    then have d1: "ipurge (b # bs) u = b # ipurge bs u" by simp
                    have "\<forall>C1' C2'. C1'\<in>nextc C1 b \<and> C2'\<in>nextc C2 b \<longrightarrow> (C1' \<lhd> bs \<simeq> u \<simeq> C2' \<lhd> (ipurge bs u))"
                      by (metis CollectD Cons.hyps b0 b1 b2 nextc_def p3 reachableStep sources_unwinding_step) 
                    then show ?thesis using b0 b1 d1 exec_equiv_both by auto 
                  next
                    assume d0: "\<not> domain b\<in>sources (b # bs) u"
                    then have d1: "ipurge (b # bs) u = ipurge bs u" by simp
                    have "\<forall>C1'. C1'\<in>nextc C1 b  \<longrightarrow> (C1' \<lhd> bs \<simeq> u \<simeq> C2 \<lhd> (ipurge bs u))"
                      by (metis CollectD a0 b0 b1 b2 d0 nextc_def p2 reachableStep sources_preserved_left)
                    then show ?thesis by (metis b0 d1 exec_equiv_leftI) 
                  qed
              }
              then show ?thesis by auto
              qed
          qed
      }
      then show ?thesis by auto
      qed
  qed

(*
theorem UnwindingTheorem_noninfluence1:
    assumes p1: observed_consistent
    and     p2: locally_respect
    and     p3: step_consistent
  shows g:noninfluence1
  proof(subst noninfluence1_def)
    show "\<forall>as bs C1 C2 u. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> (C1 \<approx>.(sources as u).\<approx> C2) 
              \<longrightarrow> ipurge as u = ipurge bs u \<longrightarrow> C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> bs"
      proof -
      {
        fix as bs C1 C2 u
        assume a0: "(reachable0 C1) \<and> (reachable0 C2)"
          and  a1: "(C1 \<approx>.(sources as u).\<approx> C2)"
          and  a2: "ipurge as u = ipurge bs u"
        then have a3: "sources as u = sources bs u" using sources_ipurge by metis
        from p1 p2 p3 a0 a1 a2 have a4: "(C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> (ipurge as u))" 
          using UnwindingTheorem_noninfluence0 noninfluence0_def by blast
        
        from p1 p2 p3 a0 a1 a2 a3 have "(C1 \<lhd> bs \<simeq> u \<simeq> C2 \<lhd> (ipurge bs u))" 
          using UnwindingTheorem_noninfluence0 noninfluence0_def by fastforce 
        
        with a2 a4 have "C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> bs" sorry
      }
      then show ?thesis by auto
      qed
  qed

theorem UnwindingTheorem_noninfluence1:
    assumes p1: observed_consistent
    and     p2: locally_respect
    and     p3: step_consistent
  shows g:noninfluence1
  proof(subst noninfluence1_def)
    show "\<forall>as bs C1 C2 u. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> (C1 \<approx>.(sources as u).\<approx> C2) 
              \<longrightarrow> ipurge as u = ipurge bs u \<longrightarrow> C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> bs"
      proof -
      {
        fix as 
        have "\<forall>bs C1 C2 u. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> (C1 \<approx>.(sources as u).\<approx> C2) 
              \<longrightarrow> ipurge as u = ipurge bs u \<longrightarrow> C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> bs"
          proof(induct as)
            case Nil show ?case
              proof -
              {
                fix bs C1 C2 u
                assume a0: "reachable0 C1 \<and> reachable0 C2"
                  and  a1: "C1 \<approx>.sources [] u.\<approx> C2"
                  and  a2: "ipurge [] u = ipurge bs u"

                have a3:"C1 \<sim>.u.\<sim> C2" using a1 ivpeqc_def sources_Nil by auto 
                have a4:"ipurge [] u = []" by simp
                from a3 have "C1 \<lhd> [] \<simeq> u \<simeq> C2 \<lhd> []" unfolding exec_equiv_def
                  using observed_consistent_def p1 vpeqc_def by fastforce
                with a4 have "C1 \<lhd> [] \<simeq> u \<simeq> C2 \<lhd> ipurge [] u" by auto

                with a2 have "C1 \<lhd> [] \<simeq> u \<simeq> C2 \<lhd> bs"
                  by (metis InfoFlow.exec_equiv_trans InfoFlow_axioms 
                    UnwindingTheorem_noninfluence0 a0 a4 exec_equiv_sym 
                    lm7 noninterference0_r_def p1 p2 p3 runnable_empty) 
              }
              then show ?thesis by auto
              qed
          next
            case (Cons c cs)
            assume a0: "\<forall>bs C1 C2 u. reachable0 C1 \<and> reachable0 C2 
                          \<longrightarrow> (C1 \<approx>.sources cs u.\<approx> C2) \<longrightarrow> ipurge cs u = ipurge bs u 
                          \<longrightarrow> C1 \<lhd> cs \<simeq> u \<simeq> C2 \<lhd> bs"
            show ?case
              proof -
              {
                fix bs C1 C2 u
                assume b0: "reachable0 C1"
                  and  b1: "reachable0 C2"
                  and  b2: "C1 \<approx>.sources (c # cs) u.\<approx> C2"
                  and  b3: "ipurge (c # cs) u = ipurge bs u"
                then have "sources (c # cs) u = sources bs u"
                  using sources_ipurge by metis
                then have "C1 \<lhd> (c # cs) \<simeq> u \<simeq> C2 \<lhd> bs" 
                  proof(cases "domain c\<in>sources (c # cs) u")
                    assume d0: "domain c\<in>sources (c # cs) u" 
                    then have d1: "ipurge (c # cs) u = c # ipurge cs u" by simp
                    have "\<forall>C1'. C1'\<in>nextc C1 c 
                          \<longrightarrow> (C1' \<lhd> cs \<simeq> u \<simeq> C2 \<lhd> bs)" sorry
                    then show ?thesis using b0 exec_equiv_leftI by blast
                  next
                    assume d0: "\<not> domain c\<in>sources (c # cs) u"
                    then have d1: "ipurge (c # cs) u = ipurge cs u" by simp
                    have "\<forall>C1'. C1'\<in>nextc C1 c  \<longrightarrow> (C1' \<lhd> cs \<simeq> u \<simeq> C2 \<lhd> bs)"
                      by (metis InfoFlow.nextc_def InfoFlow.sources_preserved_left 
                        InfoFlow_axioms a0 b0 b1 b2 b3 d0 d1 mem_Collect_eq p2 reachableStep) 
                    then show ?thesis using b0 exec_equiv_leftI by blast 
                  qed
              }
              then show ?thesis by auto
              qed
          qed
       }
      then show ?thesis by auto
      qed
  qed
*)

theorem UnwindingTheorem_nonleakage:
    assumes p1: observed_consistent
    and     p2: locally_respect
    and     p3: step_consistent 
  shows nonleakage
  proof(subst nonleakage_def)
    show "\<forall>as C1 C2 u. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> (C1 \<approx>.(sources as u).\<approx> C2) 
                                 \<longrightarrow> (C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> as)"
      proof -
      {
        fix as
        have "\<forall>C1 C2 u. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> (C1 \<approx>.(sources as u).\<approx> C2) 
                                 \<longrightarrow> (C1 \<lhd> as \<simeq> u \<simeq> C2 \<lhd> as)"
          proof(induct as)
            case Nil 
            show ?case 
              proof -
              {
                fix C1 C2 u
                assume a0: "C1 \<approx>.(sources [] u).\<approx> C2"
                then have a1: "(C1 \<sim>.u.\<sim> C2)" 
                  by (simp add: ivpeqc_def sources_Nil) 
                then have "C1 \<lhd> [] \<simeq> u \<simeq> C2 \<lhd> []"  unfolding exec_equiv_def
                   using observed_consistent_def p1 vpeqc_def by fastforce
              }
              then show ?thesis by auto
              qed
          next
            case (Cons b bs)
            assume a0: "\<forall>C1 C2 u. (reachable0 C1) \<and> (reachable0 C2) \<longrightarrow> (C1 \<approx>.(sources bs u).\<approx> C2) 
                                 \<longrightarrow> (C1 \<lhd> bs \<simeq> u \<simeq> C2 \<lhd> bs)"
            show ?case
              proof -
              {
                fix C1 C2 u
                assume b0: "(reachable0 C1) \<and> (reachable0 C2)"
                assume b1: "C1 \<approx>.(sources (b#bs) u).\<approx> C2"
                have "\<forall>C1' C2'. C1'\<in>nextc C1 b \<and> C2'\<in>nextc C2 b \<longrightarrow> (C1' \<lhd> bs \<simeq> u \<simeq> C2' \<lhd> bs)"
                          by (metis CollectD Cons.hyps b0 b1 b0 nextc_def p3 reachableStep sources_unwinding_step) 
                then have "C1 \<lhd> (b # bs) \<simeq> u \<simeq> C2 \<lhd> (b # bs)" using b0 b1 exec_equiv_both by auto 
              }
              then show ?thesis by auto
              qed
          qed
      }
      then show ?thesis by auto
      qed
    qed

end (*end of locale InfoFlow*)

end