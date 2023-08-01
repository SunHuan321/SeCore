(*
Created by:
Yongwang Zhao (ywzhao@ntu.edu.sg, zhaoyw@buaa.edu.cn)
School of Computer Engineering, Nanyang Technological University, Singapore
and School of Computer Science & Engineering, Beihang University, China

David Sanan (sanan@ntu.edu.sg)
School of Computer Engineering, Nanyang Technological University, Singapore
*)

section \<open>Formal specification of ARINC653 Multicore Separation Kernel\<close>

theory ARINC653_MultiCore_Spec_Invar_Await
imports PiCore_Syntax PiCore_RG_Invariant
begin

typedecl Part
typedecl Sched
typedecl Message 
typedecl Port
typedecl Core

datatype Domain = P Part | S Sched 

type_synonym Que = "Message set" 

typedecl SampChannel

record Config = c2s :: "Core \<Rightarrow> Sched"
                p2s :: "Part \<Rightarrow> Sched set"
                p2p :: "Port \<Rightarrow> Part"
                scsrc :: "SampChannel \<Rightarrow> Port"
                scdests :: "SampChannel \<Rightarrow> Port set"                                
                core_id:: "Core \<Rightarrow> nat"

axiomatization conf::Config 
  where bij_c2s: "bij (c2s conf)" and
        surj_p2c: "surj (p2s conf)" and
        scdests_not_emp: "\<forall>sc. (scdests conf) sc \<noteq> {}" and
        port_disj: "range (scsrc conf) \<inter> (\<Union> range (scdests conf)) = {}" and 
        no_disconn_port: "\<forall>p. p\<in>range (scsrc conf) \<or> p\<in>\<Union> range (scdests conf)" and
        no_same_source: "inj (scsrc conf)" and  
        no_same_dest: "(\<forall>ch1 ch2. ch1\<noteq>ch2 \<longrightarrow> 
                         ((scdests conf) ch1 \<inter> (scdests conf) ch2) = {}) " and
        no_core_zero: "\<forall>c. (core_id conf) c \<noteq> 0 \<and> inj (core_id conf)" and
        bij_p2p: "inj (p2p conf)"

lemma inj_surj_c2s: "inj (c2s conf) \<and> surj (c2s conf)"
  using bij_c2s by (simp add: bij_def) 

definition gsch :: "Config \<Rightarrow> Core \<Rightarrow> Sched"
  where "gsch cfg k \<equiv> (c2s cfg) k"

definition is_src_sampport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_src_sampport sc p \<equiv> (p\<in>range (scsrc sc))"

definition is_dest_sampport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_dest_sampport sc p \<equiv> (p\<in>\<Union> range (scdests sc))"

definition is_sampport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_sampport sc p \<equiv> is_src_sampport sc p \<or> is_dest_sampport sc p"

definition port_of_part :: "Config \<Rightarrow> Port \<Rightarrow> Part \<Rightarrow> bool"
  where "port_of_part sc po pa \<equiv> ((p2p sc) po = pa)"

definition ch_srcsampport :: "Config \<Rightarrow> Port \<Rightarrow> SampChannel"
  where "ch_srcsampport sc p \<equiv> SOME c. (scsrc sc) c = p"

definition ch_destsampport :: "Config \<Rightarrow> Port \<Rightarrow> SampChannel"
  where "ch_destsampport sc p \<equiv> SOME c. p\<in>((scdests sc) c)"

lemma same_dest_sampport:
  "(scdests conf) c1 = p1 \<Longrightarrow>
   (scdests conf) c2 = p2 \<Longrightarrow>
   p1 \<inter> p2 \<noteq> {} \<Longrightarrow>
   c1 = c2 "
using no_same_dest
by (meson inj_eq)

lemma same_src_sampport:
  "(scsrc conf) c1 = p1 \<Longrightarrow>
   (scsrc conf) c2 = p2 \<Longrightarrow>
   p1 = p2 \<Longrightarrow>
   c1 = c2 "
using no_same_source
by (meson inj_eq)

lemma not_dest_src_samp:
  "p1 \<in> (scdests conf) c1  \<Longrightarrow>
   (scsrc conf) c2 = p2 \<Longrightarrow>
   p1=p2 \<Longrightarrow>
   G "
using port_disj
by (simp add: UnionI disjoint_iff_not_equal rangeI)

definition par_ports :: "Config \<Rightarrow> Part \<Rightarrow> Port set"
where "par_ports sc pa \<equiv> {p. port_of_part sc p pa}"

lemma "pa\<noteq>pb \<Longrightarrow> par_ports conf pa \<inter> par_ports conf pb = {}"
  using bij_p2p unfolding par_ports_def port_of_part_def 
  by auto


definition par_sampling_ports :: "Config \<Rightarrow> Port set \<Rightarrow> Port set"
where "par_sampling_ports sc ps \<equiv> {p.  (is_sampport sc) p \<and> p\<in>ps}"

definition par_dest_sampling_ports :: "Config \<Rightarrow> Port set \<Rightarrow> Port set"
where "par_dest_sampling_ports sc ps \<equiv> {p.  (is_dest_sampport sc) p \<and> p\<in>ps}"

definition par_src_sampling_ports :: "Config \<Rightarrow> Port set \<Rightarrow> Port set"
where "par_src_sampling_ports sc ps \<equiv> {p.  (is_src_sampport sc) p \<and> p\<in>ps}"

definition par_sampchan::"Config \<Rightarrow> Part \<Rightarrow> SampChannel set"
where "par_sampchan sc pa \<equiv> (ch_srcsampport sc) ` (par_src_sampling_ports sc (par_ports sc pa)) \<union>
                            (ch_destsampport sc) `(par_dest_sampling_ports sc (par_ports sc pa))"


definition ch_conn :: "Config \<Rightarrow> Part \<Rightarrow> Part \<Rightarrow> bool"
  where "ch_conn cfg p1 p2 \<equiv> (\<exists>sch p. (p2p cfg) ((scsrc cfg) sch) = p1 
                                      \<and> p \<in> (scdests cfg) sch \<and> (p2p cfg) p = p2)
                            (*\<or> (\<exists>qch. (p2p cfg) ((qcsrc cfg) qch) = p1 
                                      \<and> (p2p cfg) ((qcdest cfg) qch) = p2)*)"

record State = cur :: "Sched \<Rightarrow> Part"
               schan :: "SampChannel \<rightharpoonup> Message"
               sclock :: "SampChannel \<Rightarrow> bool"
               (* qchan :: "QueChannel \<Rightarrow> Que"
               (*sclock :: "SampChannel \<Rightarrow> Core option"*)  (*True: it is available*)
               (* sclock :: "SampChannel \<Rightarrow> nat" *)
               qclock :: "QueChannel \<Rightarrow> nat" *)
               (*vark :: Core*)

definition cur_part::"(State) invariant"
  where "cur_part \<equiv> \<lbrace> \<forall>sched. sched\<in>(p2s conf) (\<acute>cur sched) \<rbrace>"

datatype EL = Core_InitE | ScheduleE | Write_Sampling_MessageE |  Read_Sampling_MessageE
              | Get_Sampling_Port_StatusE | Send_Queuing_MessageE | Receive_Queuing_MessageE
              | Get_Queuing_Port_StatusE

datatype parameter = Nat nat | Str string | Q Que | Pt Port | Msg Message

type_synonym EventLabel = "EL \<times> (parameter list \<times> Core)" 

definition get_evt_label :: "EL \<Rightarrow> parameter list \<Rightarrow> Core \<Rightarrow> EventLabel" ("_ _@@_" [0,0,0] 20)
  where "get_evt_label el ps k \<equiv> (el,(ps,k))"

definition Core_Init :: "Core \<Rightarrow> (EventLabel, Core, State) event" 
  where "Core_Init k\<equiv> 
    EVENT Core_InitE []@@k WHERE
      True
    THEN 
      SKIP 
    END"

definition System_Init :: "Config \<Rightarrow> (State \<times> (EventLabel, Core, State) x)"
  where "System_Init cfg \<equiv> (\<lparr>cur=(\<lambda>c. SOME p. c\<in>(p2s cfg) p ),
                            schan = (\<lambda>c. None),
                            sclock = (\<lambda>c. True)
                            (* qchan = (\<lambda>c. {}), *)
                            (* sclock = (\<lambda>c. 0),*)
                            (* qclock = (\<lambda>c. 0) *) \<rparr>, 
                            (\<lambda>k. Core_Init k))"

definition Schedule :: "Core \<Rightarrow> (EventLabel, Core, State) event" 
  where "Schedule k \<equiv> 
    EVENT ScheduleE []@@k WHERE
      True
    THEN 
      \<acute>cur := \<acute>cur((c2s conf) k := SOME p. (c2s conf) k \<in>(p2s conf) p ) 
    END"
                                           
definition Write_Sampling_Message :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> (EventLabel, Core, State) event" 
  where "Write_Sampling_Message k p m \<equiv> 
    EVENT Write_Sampling_MessageE [Pt p, Msg m]@@k WHERE
      is_src_sampport conf p           (*constrains on parameters*)
       \<and> port_of_part conf p (\<acute>cur (gsch conf k))
    THEN   
      AWAIT (\<acute>sclock (ch_srcsampport conf p)) THEN 
        \<acute>sclock := \<acute>sclock (ch_srcsampport conf p := False)
      END;;    
      \<acute>schan := \<acute>schan (ch_srcsampport conf p := Some m);;
      \<acute>sclock := \<acute>sclock (ch_srcsampport conf p := True)
    END"

definition Read_Sampling_Message :: "Core \<Rightarrow> Port \<Rightarrow> (EventLabel, Core, State) event" 
  where "Read_Sampling_Message k p \<equiv> 
    EVENT Read_Sampling_MessageE [Pt p]@@k WHERE
      is_dest_sampport conf p           (*constrains on parameters*)
        \<and> port_of_part conf p (\<acute>cur (gsch conf k))      (*guard of states*)
    THEN 
      AWAIT (\<acute>sclock (ch_srcsampport conf p)) THEN 
        \<acute>sclock := \<acute>sclock (ch_srcsampport conf p := False)
      END;;    
      SKIP;;
      \<acute>sclock := \<acute>sclock (ch_srcsampport conf p := True)
    END"

definition Core_Init_RGCond :: "(State) rgformula"
  where "Core_Init_RGCond  \<equiv> RG[\<lbrace>True\<rbrace>,UNIV,Id,\<lbrace>True\<rbrace>]"


definition Schedule_RGCond :: "Core \<Rightarrow> (State) rgformula"
  where "Schedule_RGCond k \<equiv> 
   (RG[\<lbrace>True\<rbrace>,
       \<lbrace>True\<rbrace>, 
       (\<lbrace>\<ordfeminine>cur (c2s conf k) = (SOME p. (c2s conf) k \<in>(p2s conf) p)
          \<and> (\<forall>c. c\<noteq> k \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))\<rbrace> \<union> Id),
       \<lbrace>True\<rbrace>])"

definition Write_Sampling_Message_RGCond :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> (State) rgformula"
  where "Write_Sampling_Message_RGCond k p m \<equiv> (
            RG[\<lbrace>True\<rbrace>,
               \<lbrace>\<ordfeminine>cur (c2s conf k)= \<ordmasculine>cur (c2s conf k)\<rbrace>, 
               (\<lbrace>\<ordfeminine>cur= \<ordmasculine>cur\<rbrace>\<union>Id),
               \<lbrace>True\<rbrace>])"

definition Read_Sampling_Message_RGCond :: "Core \<Rightarrow> Port \<Rightarrow> (State) rgformula"
  where "Read_Sampling_Message_RGCond k p \<equiv> 
     RG[\<lbrace>True\<rbrace>,
        \<lbrace>\<ordfeminine>cur (c2s conf k)= \<ordmasculine>cur (c2s conf k)\<rbrace>,
        (\<lbrace>\<ordfeminine>cur= \<ordmasculine>cur\<rbrace>\<union>Id),
        \<lbrace>True\<rbrace>]"

definition Core_Init_RGF :: "Core \<Rightarrow> (EventLabel, Core, State) rgformula_e"
  where "Core_Init_RGF k \<equiv> (Core_Init k, Core_Init_RGCond)"

definition Schedule_RGF :: "Core \<Rightarrow> (EventLabel, Core, State) rgformula_e"
  where "Schedule_RGF k \<equiv> (Schedule k, Schedule_RGCond k)"

definition Write_Sampling_Message_RGF :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> (EventLabel, Core, State) rgformula_e"
  where "Write_Sampling_Message_RGF k p m \<equiv> (Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)"

definition Read_Sampling_Message_RGF :: "Core \<Rightarrow> Port \<Rightarrow> (EventLabel, Core, State) rgformula_e"
  where "Read_Sampling_Message_RGF k p  \<equiv> (Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)"

definition EvtSys1_on_Core_RGF :: "Core \<Rightarrow> (EventLabel, Core, State) rgformula_es"
  where "EvtSys1_on_Core_RGF k \<equiv> 
            (rgf_EvtSys ({Schedule_RGF k} \<union>
                          (\<Union>(p, m). {Write_Sampling_Message_RGF k p m}) \<union>
                          (\<Union>p.{Read_Sampling_Message_RGF k p})),
               RG[\<lbrace>True\<rbrace>,
                  \<lbrace>\<ordfeminine>cur (c2s conf k)= \<ordmasculine>cur (c2s conf k)\<rbrace>,
                  (\<lbrace>\<ordfeminine>cur= \<ordmasculine>cur \<or> \<ordfeminine>cur (c2s conf k) = (SOME p. (c2s conf) k \<in>(p2s conf) p)
                                \<and> (\<forall>c. c\<noteq> k \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))\<rbrace>\<union>Id),
                  \<lbrace>True\<rbrace>])"


definition EvtSys_on_Core_RGF :: "Core \<Rightarrow> (EventLabel, Core, State) rgformula_es"
  where "EvtSys_on_Core_RGF k  \<equiv> 
          (rgf_EvtSeq (Core_Init_RGF k) (EvtSys1_on_Core_RGF k),
           RG[\<lbrace>True\<rbrace>,
              \<lbrace>\<ordfeminine>cur (c2s conf k)= \<ordmasculine>cur (c2s conf k)\<rbrace>,
              (\<lbrace>\<ordfeminine>cur= \<ordmasculine>cur \<or> \<ordfeminine>cur (c2s conf k) = (SOME p. (c2s conf) k \<in>(p2s conf) p)
                                \<and> (\<forall>c. c\<noteq> k \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))\<rbrace>\<union>Id),
              \<lbrace>True\<rbrace>])"

definition ARINCXKernel_Spec :: "(EventLabel, Core, State) rgformula_par"
  where "ARINCXKernel_Spec \<equiv> (\<lambda>k. EvtSys_on_Core_RGF k)"

axiomatization s0 where s0_init: "s0 \<equiv> fst (System_Init conf)"
axiomatization x0 where x0_init: "x0 \<equiv> snd (System_Init conf)"
axiomatization C0 where C0_init: "C0 = (paresys_spec ARINCXKernel_Spec, s0, x0)"


lemma neq_coreinit: "k1\<noteq>k2 \<Longrightarrow> Core_Init k1\<noteq>Core_Init k2" 
  by (simp add:Core_Init_def get_evt_label_def)

lemma neq_schedule: "k1\<noteq>k2 \<Longrightarrow> Schedule k1\<noteq>Schedule k2" 
  by (simp add:Schedule_def get_evt_label_def)

lemma neq_wrt_samp: "(k1\<noteq>k2 \<or> p1\<noteq>p2 \<or> m1\<noteq>m2) \<Longrightarrow> Write_Sampling_Message k1 p1 m1 \<noteq> Write_Sampling_Message k2 p2 m2" 
  apply (clarsimp, simp add:Write_Sampling_Message_def) 
  by (simp add:get_evt_label_def)

lemma neq_rd_samp: "(k1\<noteq>k2 \<or> p1\<noteq>p2) \<Longrightarrow> Read_Sampling_Message k1 p1 \<noteq> Read_Sampling_Message k2 p2" 
  apply (clarsimp, simp add:Read_Sampling_Message_def) 
  by (simp add:get_evt_label_def)

lemma neq_coreinit_sched: "Core_Init k1 \<noteq> Schedule k2"
  by (simp add:Schedule_def Core_Init_def get_evt_label_def)

lemma neq_coreinit_wrtsamp: "Core_Init k1 \<noteq> Write_Sampling_Message k2 p m"
  by (simp add:Write_Sampling_Message_def Core_Init_def get_evt_label_def)

lemma neq_coreinit_rdsamp: "Core_Init k1 \<noteq> Read_Sampling_Message k2 p"
  by (simp add:Read_Sampling_Message_def Core_Init_def get_evt_label_def)

lemma neq_sched_wrtsamp: "Schedule k1 \<noteq> Write_Sampling_Message k2 p m"
  by (simp add:Write_Sampling_Message_def Schedule_def get_evt_label_def)

lemma neq_sched_rdsamp: "Schedule k1 \<noteq> Read_Sampling_Message k2 p"
  by (simp add:Read_Sampling_Message_def Schedule_def get_evt_label_def)

lemma neq_wrtsamp_rdsamp: "Write_Sampling_Message k1 p1 m \<noteq> Read_Sampling_Message k2 p2"
  by (simp add:Read_Sampling_Message_def Write_Sampling_Message_def get_evt_label_def)

definition evtrgfset :: "((EventLabel, Core, State) event \<times> (State rgformula)) set"
  where "evtrgfset \<equiv> (\<Union>k.{(Core_Init k, Core_Init_RGCond)})
                  \<union> (\<Union>k.{(Schedule k, Schedule_RGCond k)})
                  \<union> (\<Union>(k, p, m).{(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})
                  \<union> (\<Union>(k, p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"

lemma evtrgfset_eq_allevts_ARINCSpec: "all_evts ARINCXKernel_Spec = evtrgfset"
  proof -
    have "all_evts ARINCXKernel_Spec = (\<Union>k. all_evts_es (fst (ARINCXKernel_Spec k)))" 
      by (simp add:all_evts_def)
    then have "all_evts ARINCXKernel_Spec = (\<Union>k. all_evts_es (fst (EvtSys_on_Core_RGF k)))"
      by (simp add:ARINCXKernel_Spec_def)
    then have "all_evts ARINCXKernel_Spec = (\<Union>k. all_evts_es (rgf_EvtSeq (Core_Init_RGF k) (EvtSys1_on_Core_RGF k)))"
      by (simp add:EvtSys_on_Core_RGF_def)
    then have "all_evts ARINCXKernel_Spec = (\<Union>k. {Core_Init_RGF k} \<union> (all_evts_es (fst (EvtSys1_on_Core_RGF k))))"
      by simp
    then have "all_evts ARINCXKernel_Spec = (\<Union>k. {Core_Init_RGF k} \<union>
                                                  ({Schedule_RGF k} \<union>
                                                  (\<Union>(p, m). {Write_Sampling_Message_RGF k p m}) \<union>
                                                  (\<Union>p.{Read_Sampling_Message_RGF k p}))
                                             )"
      by (simp add:Core_Init_RGF_def EvtSys1_on_Core_RGF_def)
    then have "all_evts ARINCXKernel_Spec = (\<Union>k. {(Core_Init k, Core_Init_RGCond)} \<union>
                                                  {(Schedule k, Schedule_RGCond k)} \<union>
                                                  (\<Union>(p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)}) \<union>
                                                  (\<Union>p.{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})
                                             )"
      by (simp add: Core_Init_RGF_def Schedule_RGF_def Write_Sampling_Message_RGF_def Read_Sampling_Message_RGF_def)
    moreover
    have "(\<Union>k. {(Core_Init k, Core_Init_RGCond)} \<union>
                {(Schedule k, Schedule_RGCond k)} \<union>
                (\<Union>(p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)}) \<union>
                (\<Union>p.{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})
           ) = 
           (\<Union>k. {(Core_Init k, Core_Init_RGCond)}) \<union>
           (\<Union>k. {(Schedule k, Schedule_RGCond k)}) \<union>
           (\<Union>k. (\<Union>(p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})) \<union>
           (\<Union>k. (\<Union>p.{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)}))"
      by blast
    moreover
    have "(\<Union>k. (\<Union>(p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)}))
          = (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})" by blast
    moreover
    have "(\<Union>k. (\<Union>p.{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)}))
          = (\<Union>(k,p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})" by blast
    ultimately show ?thesis using evtrgfset_def by simp
  qed

definition evtrgffun :: "(EventLabel, Core, State) event \<Rightarrow> (State rgformula) option"
  where "evtrgffun \<equiv> (\<lambda>e. Some (SOME rg. (e, rg)\<in>evtrgfset))"

lemma evtrgffun_exist: "\<forall>e\<in>Domain evtrgfset. \<exists>ef\<in>evtrgfset. E\<^sub>e ef = e \<and> evtrgffun e = Some (snd ef)"
  by (metis Domain_iff E\<^sub>e_def evtrgffun_def fst_conv snd_conv someI_ex)

lemma diff_e_in_evtrgfset: "\<forall>ef1 ef2. ef1\<in>evtrgfset \<and> ef2\<in>evtrgfset \<and> ef1\<noteq>ef2 \<longrightarrow> E\<^sub>e ef1 \<noteq> E\<^sub>e ef2"
  proof -
  {
    fix ef1 ef2
    assume a0: "ef1\<in>evtrgfset \<and> ef2\<in>evtrgfset \<and> ef1\<noteq>ef2"
    then have a1: "ef1\<in>(\<Union>k.{(Core_Init k, Core_Init_RGCond)})
               \<or> ef1\<in>(\<Union>k.{(Schedule k, Schedule_RGCond k)})
               \<or> ef1\<in>(\<Union>(k, p, m).{(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})
               \<or> ef1\<in>(\<Union>(k, p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})" 
      using evtrgfset_def by blast
      
    from a0 have a2: "ef2\<in>(\<Union>k.{(Core_Init k, Core_Init_RGCond)})
               \<or> ef2\<in>(\<Union>k.{(Schedule k, Schedule_RGCond k)})
               \<or> ef2\<in>(\<Union>(k, p, m).{(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})
               \<or> ef2\<in>(\<Union>(k, p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})" 
      using evtrgfset_def by blast

    from a1 have "E\<^sub>e ef1 \<noteq> E\<^sub>e ef2"
      proof
        assume "ef1\<in>(\<Union>k.{(Core_Init k, Core_Init_RGCond)})"
        then obtain k where b0: "ef1 = (Core_Init k, Core_Init_RGCond)" by auto
        from a2 show ?thesis
          proof
            assume c0: "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond)})"
            then obtain k1 where "ef2 = (Core_Init k1, Core_Init_RGCond)" by auto
            with a0 b0 show ?thesis using neq_coreinit by (simp add:E\<^sub>e_def)
          next
            assume c0: "ef2 \<in> (\<Union>k. {(Schedule k, Schedule_RGCond k)}) \<or>
                        ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)}) \<or>
                        ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
            then show ?thesis 
              proof
                assume "ef2 \<in> (\<Union>k. {(Schedule k, Schedule_RGCond k)})"
                then obtain k1 where "ef2 = (Schedule k1, Schedule_RGCond k1)" by auto
                with a0 b0 show ?thesis using neq_coreinit_sched by (simp add:E\<^sub>e_def)
              next
                assume "ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)}) \<or>
                        ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                then show ?thesis
                  proof
                    assume "ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})"
                    then obtain k1 and p and m where "ef2 = (Write_Sampling_Message k1 p m, Write_Sampling_Message_RGCond k1 p m)"
                      by auto
                    with a0 b0 show ?thesis using neq_coreinit_wrtsamp by (simp add:E\<^sub>e_def)
                  next
                    assume "ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                    then obtain k1 and p where "ef2 = (Read_Sampling_Message k1 p, Read_Sampling_Message_RGCond k1 p)" 
                      by auto
                    with a0 b0 show ?thesis using neq_coreinit_rdsamp by (simp add:E\<^sub>e_def)
                  qed
              qed
          qed
      next
        assume "ef1\<in>(\<Union>k.{(Schedule k, Schedule_RGCond k)})
               \<or> ef1\<in>(\<Union>(k, p, m).{(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})
               \<or> ef1\<in>(\<Union>(k, p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
        then show ?thesis
          proof
            assume "ef1\<in>(\<Union>k.{(Schedule k, Schedule_RGCond k)})"
            then obtain k where b0: "ef1 = (Schedule k, Schedule_RGCond k)" by auto
            from a2 show ?thesis
              proof
                assume c0: "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond)})"
                then obtain k1 where "ef2 = (Core_Init k1, Core_Init_RGCond)" by auto
                with a0 b0 show ?thesis using neq_coreinit_sched E\<^sub>e_def by (metis fst_conv) 
              next
                assume c0: "ef2 \<in> (\<Union>k. {(Schedule k, Schedule_RGCond k)}) \<or>
                            ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)}) \<or>
                            ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                then show ?thesis 
                  proof
                    assume "ef2 \<in> (\<Union>k. {(Schedule k, Schedule_RGCond k)})"
                    then obtain k1 where "ef2 = (Schedule k1, Schedule_RGCond k1)" by auto
                    with a0 b0 show ?thesis using neq_schedule E\<^sub>e_def by (metis fst_conv)
                  next
                    assume "ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)}) \<or>
                            ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                    then show ?thesis
                      proof
                        assume "ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})"
                        then obtain k1 and p and m where "ef2 = (Write_Sampling_Message k1 p m, Write_Sampling_Message_RGCond k1 p m)"
                          by auto
                        with a0 b0 show ?thesis using neq_sched_wrtsamp by (simp add:E\<^sub>e_def)
                      next
                        assume "ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                        then obtain k1 and p where "ef2 = (Read_Sampling_Message k1 p, Read_Sampling_Message_RGCond k1 p)" 
                          by auto
                        with a0 b0 show ?thesis using neq_sched_rdsamp by (simp add:E\<^sub>e_def)
                      qed
                  qed
              qed
          next
            assume "ef1\<in>(\<Union>(k, p, m).{(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})
                  \<or> ef1\<in>(\<Union>(k, p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
            then show ?thesis
              proof
                assume "ef1\<in>(\<Union>(k, p, m).{(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})"
                then obtain k and p and m where b0: 
                  "ef1 = (Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)" by auto
                from a2 show ?thesis
                  proof
                    assume c0: "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond)})"
                    then obtain k1 where "ef2 = (Core_Init k1, Core_Init_RGCond)" by auto
                    with a0 b0 show ?thesis using neq_coreinit_wrtsamp E\<^sub>e_def by (metis fst_conv) 
                  next
                    assume c0: "ef2 \<in> (\<Union>k. {(Schedule k, Schedule_RGCond k)}) \<or>
                                ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)}) \<or>
                                ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                    then show ?thesis 
                      proof
                        assume "ef2 \<in> (\<Union>k. {(Schedule k, Schedule_RGCond k)})"
                        then obtain k1 where "ef2 = (Schedule k1, Schedule_RGCond k1)" by auto
                        with a0 b0 show ?thesis using neq_sched_wrtsamp E\<^sub>e_def by (metis fst_conv)
                      next
                        assume "ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)}) \<or>
                                ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                        then show ?thesis
                          proof
                            assume "ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})"
                            then obtain k1 and p1 and m1 where "ef2 = (Write_Sampling_Message k1 p1 m1, Write_Sampling_Message_RGCond k1 p1 m1)"
                              by auto
                            with a0 b0 show ?thesis using neq_wrt_samp E\<^sub>e_def by (metis fst_conv)
                          next
                            assume "ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                            then obtain k1 and p1 where "ef2 = (Read_Sampling_Message k1 p1, Read_Sampling_Message_RGCond k1 p1)" 
                              by auto
                            with a0 b0 show ?thesis using neq_wrtsamp_rdsamp E\<^sub>e_def by (metis fst_conv)
                          qed
                      qed
                  qed
              next
                assume "ef1\<in>(\<Union>(k, p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                then obtain k and p where b0: 
                  "ef1 = (Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)" by auto
                from a2 show ?thesis
                  proof
                    assume c0: "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond)})"
                    then obtain k1 where "ef2 = (Core_Init k1, Core_Init_RGCond)" by auto
                    with a0 b0 show ?thesis using neq_coreinit_rdsamp E\<^sub>e_def by (metis fst_conv) 
                  next
                    assume c0: "ef2 \<in> (\<Union>k. {(Schedule k, Schedule_RGCond k)}) \<or>
                                ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)}) \<or>
                                ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                    then show ?thesis 
                      proof
                        assume "ef2 \<in> (\<Union>k. {(Schedule k, Schedule_RGCond k)})"
                        then obtain k1 where "ef2 = (Schedule k1, Schedule_RGCond k1)" by auto
                        with a0 b0 show ?thesis using neq_sched_rdsamp E\<^sub>e_def by (metis fst_conv)
                      next
                        assume "ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)}) \<or>
                                ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                        then show ?thesis
                          proof
                            assume "ef2 \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})"
                            then obtain k1 and p1 and m1 where "ef2 = (Write_Sampling_Message k1 p1 m1, Write_Sampling_Message_RGCond k1 p1 m1)"
                              by auto
                            with a0 b0 show ?thesis using neq_wrtsamp_rdsamp E\<^sub>e_def by (metis fst_conv)
                          next
                            assume "ef2 \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})"
                            then obtain k1 and p1 where "ef2 = (Read_Sampling_Message k1 p1, Read_Sampling_Message_RGCond k1 p1)" 
                              by auto
                            with a0 b0 show ?thesis using neq_rd_samp E\<^sub>e_def by (metis fst_conv)
                          qed
                      qed
                  qed
              qed
          qed
      qed
  }
  then show ?thesis by auto
  qed

lemma evtrgfset_func: "\<forall>ef\<in>evtrgfset. evtrgffun (E\<^sub>e ef) = Some (snd ef)" 
  proof -
  {
    fix ef
    assume a0: "ef\<in>evtrgfset"
    then have "E\<^sub>e ef\<in>Domain evtrgfset" by (metis Domain_iff E\<^sub>e_def surjective_pairing) 
    then obtain ef1 where a1: "ef1\<in>evtrgfset \<and> E\<^sub>e ef1 = E\<^sub>e ef \<and> evtrgffun (E\<^sub>e ef) = Some (snd ef1)" 
      using evtrgffun_exist[rule_format,of "E\<^sub>e ef"] by auto
    have "evtrgffun (E\<^sub>e ef) = Some (snd ef)"
      proof(cases "ef1 = ef")
        assume "ef1 = ef"
        with a1 show ?thesis by simp
      next
        assume b0: "ef1\<noteq>ef"
        with diff_e_in_evtrgfset a0 a1 have "E\<^sub>e ef1 \<noteq> E\<^sub>e ef" by blast
        with a1 show ?thesis by simp
      qed
  }
  then show ?thesis by auto
  qed

lemma all_basic_evts_arinc_help: "\<forall>k. ef\<in>all_evts_es (fst (ARINCXKernel_Spec k)) \<longrightarrow> is_basicevt (E\<^sub>e ef)"
  proof -
  {
    fix k
    assume p0: "ef\<in>all_evts_es (fst (ARINCXKernel_Spec k))" 
    then have "ef\<in>all_evts_es (fst (EvtSys_on_Core_RGF k))" by (simp add:ARINCXKernel_Spec_def)
    then have "ef\<in>insert (Core_Init_RGF k) (all_evts_es (fst (EvtSys1_on_Core_RGF k)))" 
      by (simp add:EvtSys_on_Core_RGF_def)
    then have "ef = (Core_Init_RGF k) \<or> ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGF k))" by auto
    then have "is_basicevt (E\<^sub>e ef)"
      proof
        assume a0: "ef = Core_Init_RGF k"
        then show ?thesis 
          using Core_Init_RGF_def Core_Init_def by (metis E\<^sub>e_def fst_conv is_basicevt.simps(2)) 
      next
        assume a1: "ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGF k))"
        then have "ef\<in>{Schedule_RGF k} \<union>
                      {ef. \<exists>p m. ef = Write_Sampling_Message_RGF k p m} \<union>
                      {ef. \<exists>p. ef = Read_Sampling_Message_RGF k p}" 
          using all_evts_es_esys EvtSys1_on_Core_RGF_def by auto
        then have "ef\<in>{Schedule_RGF k} 
                  \<or> ef\<in>{ef. \<exists>p m. ef = Write_Sampling_Message_RGF k p m} 
                  \<or> ef\<in>{ef. \<exists>p. ef = Read_Sampling_Message_RGF k p}" by auto
        then show ?thesis
          proof
            assume "ef\<in>{Schedule_RGF k}"
            then show ?thesis by (simp add: E\<^sub>e_def Schedule_RGF_def Schedule_def) 
          next
            assume "ef\<in>{ef. \<exists>p m. ef = Write_Sampling_Message_RGF k p m}
                    \<or> ef\<in>{ef. \<exists>p. ef = Read_Sampling_Message_RGF k p}"
            then show ?thesis 
              proof
                assume "ef\<in>{ef. \<exists>p m. ef = Write_Sampling_Message_RGF k p m}"
                then have "\<exists>p m. ef = Write_Sampling_Message_RGF k p m" by auto
                then obtain p and m where "ef = Write_Sampling_Message_RGF k p m" by auto
                then show ?thesis by (simp add: E\<^sub>e_def Write_Sampling_Message_RGF_def Write_Sampling_Message_def)
              next
                assume "ef\<in>{ef. \<exists>p. ef = Read_Sampling_Message_RGF k p}"
                then have "\<exists>p. ef = Read_Sampling_Message_RGF k p" by auto
                then obtain p where "ef = Read_Sampling_Message_RGF k p" by auto
                then show ?thesis by (simp add: E\<^sub>e_def Read_Sampling_Message_RGF_def Read_Sampling_Message_def) 
              qed
          qed
      qed
  }
  then show ?thesis by auto
  qed

lemma all_basic_evts_arinc: "\<forall>ef\<in>all_evts ARINCXKernel_Spec. is_basicevt (E\<^sub>e ef)" 
  using all_evts_def[of ARINCXKernel_Spec] all_basic_evts_arinc_help by auto

lemma bsc_evts_rgfs: "\<forall>erg\<in>all_evts (ARINCXKernel_Spec). (evtrgffun (E\<^sub>e erg))  = Some (snd erg)"
  using evtrgfset_func evtrgfset_eq_allevts_ARINCSpec by simp

definition Evt_sat_RG:: "(EventLabel, Core, State) event \<Rightarrow> (State) rgformula \<Rightarrow> bool" ("(_\<turnstile>_)" [60,60] 61)
  where "Evt_sat_RG e rg \<equiv> \<turnstile> e sat\<^sub>e [Pre\<^sub>f rg, Rely\<^sub>f rg, Guar\<^sub>f rg, Post\<^sub>f rg]"

lemma Core_Init_SatRG: "\<forall>k. Core_Init k \<turnstile> Core_Init_RGCond"
  apply(simp add:Evt_sat_RG_def)
  apply(rule allI)
  apply(simp add:Core_Init_def)
  apply(rule BasicEvt)
    apply(simp add:body_def Skip_def)
    apply(rule Basic)
    apply(simp add:Core_Init_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def getrgformula_def)+
    apply auto[1] 
  apply(simp add:Core_Init_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def Rely\<^sub>f_def getrgformula_def guard_def stable_def)
  apply(simp add:Core_Init_RGCond_def Post\<^sub>f_def Rely\<^sub>f_def getrgformula_def stable_def)
  apply(simp add:stable_def Core_Init_RGCond_def getrgformula_def Pre\<^sub>f_def)
  apply(simp add:Core_Init_RGCond_def Guar\<^sub>f_def getrgformula_def stable_def)
  done

lemma Sched_SatRG_help1: "{(s, t). t = s\<lparr>cur := (cur s)(c2s conf k := SOME p. c2s conf k \<in> p2s conf p)\<rparr>}
         \<subseteq> \<lbrace>(\<forall>c. c \<noteq> k \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur (c2s conf c))\<rbrace>" using inj_surj_c2s
  by (simp add: Collect_mono case_prod_beta' inj_eq) 

lemma Sched_SatRG: "\<forall>k. Schedule k \<turnstile> Schedule_RGCond k"
  apply(simp add:Evt_sat_RG_def)  
  apply(rule allI)
  apply(simp add:Schedule_def)
  apply(rule BasicEvt)
    apply(simp add:body_def guard_def)
    apply(rule Basic)
    apply(simp add:Schedule_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
    apply(simp add:Schedule_RGCond_def Pre\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
    using Sched_SatRG_help1 apply fastforce
    apply(simp add:stable_def Schedule_RGCond_def getrgformula_def Pre\<^sub>f_def)
    apply(simp add:stable_def Schedule_RGCond_def getrgformula_def Post\<^sub>f_def)
    apply(simp add:stable_def Schedule_RGCond_def getrgformula_def Pre\<^sub>f_def)
    by (simp add:Schedule_RGCond_def getrgformula_def Guar\<^sub>f_def)

lemma Write_Sampling_Message_SatRG_help: 
  "{(s, t). s \<in> pre_rgf (RG[UNIV,\<lbrace>\<ordfeminine>cur (c2s conf k) = \<ordmasculine>cur (c2s conf k)\<rbrace>,(\<lbrace>\<ordfeminine>cur = \<ordmasculine>cur\<rbrace> \<union> Id),UNIV]) 
          \<and> is_src_sampport conf p \<and> port_of_part conf p (cur s (gsch conf k)) 
          \<and> t = s\<lparr>schan := schan s(ch_srcsampport conf p \<mapsto> m)\<rparr>} 
   \<subseteq> guar_rgf (RG[UNIV,\<lbrace>\<ordfeminine>cur (c2s conf k) = \<ordmasculine>cur (c2s conf k)\<rbrace>,(\<lbrace>\<ordfeminine>cur = \<ordmasculine>cur\<rbrace> \<union> Id),UNIV])"
  proof -
    have "{(s, t). s \<in> UNIV \<and> is_src_sampport conf p \<and> port_of_part conf p (cur s (gsch conf k)) 
          \<and> t = s\<lparr>schan := schan s(ch_srcsampport conf p \<mapsto> m)\<rparr>} 
          \<subseteq> (\<lbrace>\<ordfeminine>cur = \<ordmasculine>cur\<rbrace> \<union> Id)" by auto
    moreover
    have "pre_rgf (RG[UNIV,\<lbrace>\<ordfeminine>cur (c2s conf k) = \<ordmasculine>cur (c2s conf k)\<rbrace>,(\<lbrace>\<ordfeminine>cur = \<ordmasculine>cur\<rbrace> \<union> Id),UNIV]) = UNIV" 
      using getrgformula_def by (metis (no_types, lifting) rgformula.select_convs(1)) 
    moreover
    have "guar_rgf (RG[UNIV,\<lbrace>\<ordfeminine>cur (c2s conf k) = \<ordmasculine>cur (c2s conf k)\<rbrace>,(\<lbrace>\<ordfeminine>cur = \<ordmasculine>cur\<rbrace> \<union> Id),UNIV]) = (\<lbrace>\<ordfeminine>cur = \<ordmasculine>cur\<rbrace> \<union> Id)"
      using getrgformula_def by (metis (no_types, lifting) rgformula.select_convs(3)) 
    ultimately show ?thesis by auto
  qed

lemma Write_Sampling_Message_SatRG: 
  "\<forall>k p m. Write_Sampling_Message k p m \<turnstile> Write_Sampling_Message_RGCond k p m"
  apply(simp add:Evt_sat_RG_def)
  apply(rule allI)+
  apply(simp add:Write_Sampling_Message_def)
  apply(rule BasicEvt)
  apply(simp add:body_def guard_def)
  apply(rule Seq) apply(rule Seq) apply(rule Await)
  apply(simp add:Write_Sampling_Message_RGCond_def Pre\<^sub>f_def Rely\<^sub>f_def getrgformula_def stable_def)
  apply (simp add: gsch_def)
  prefer 2
  apply(rule allI)
  apply(rule Basic)
  prefer 2 apply simp
  prefer 2 apply(simp add:stable_def)
  prefer 2 apply(simp add:stable_def)
  prefer 3 apply(rule Basic)
  

  apply(simp add:Write_Sampling_Message_RGCond_def Rely\<^sub>f_def getrgformula_def stable_def)

  apply(rule Basic)
  apply(simp add:Write_Sampling_Message_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  apply(simp add:Write_Sampling_Message_RGCond_def Pre\<^sub>f_def Guar\<^sub>f_def)
  using Write_Sampling_Message_SatRG_help apply fastforce
  apply(simp add:stable_def Write_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>f_def Rely\<^sub>f_def gsch_def)
  apply(simp add:stable_def Write_Sampling_Message_RGCond_def getrgformula_def Post\<^sub>f_def)
  apply(simp add:stable_def Write_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>f_def Rely\<^sub>f_def)
  by (simp add:Write_Sampling_Message_RGCond_def getrgformula_def Guar\<^sub>f_def)
  
  
lemma Read_Sampling_Message_SatRG: "\<forall>k p. Read_Sampling_Message k p \<turnstile> Read_Sampling_Message_RGCond k p"
  apply(simp add:Evt_sat_RG_def)
  apply(rule allI)+ 
  apply(simp add:Read_Sampling_Message_def)
  apply(rule BasicEvt)
  apply(simp add:body_def guard_def Skip_def)
  apply(rule Basic)
  apply(simp add:Read_Sampling_Message_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def getrgformula_def)+
  apply auto[1] 
  apply(simp add:Read_Sampling_Message_RGCond_def Pre\<^sub>f_def Rely\<^sub>f_def getrgformula_def stable_def gsch_def)
  apply(simp add:Read_Sampling_Message_RGCond_def Post\<^sub>f_def Rely\<^sub>f_def getrgformula_def stable_def)
  apply(simp add:stable_def Read_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>f_def Rely\<^sub>f_def)
  by (simp add:Read_Sampling_Message_RGCond_def getrgformula_def Guar\<^sub>f_def)

lemma EvtSys1_on_core_SatRG: 
  "\<forall>k. \<turnstile> fst (EvtSys1_on_Core_RGF k) sat\<^sub>s 
              [Pre\<^sub>f (snd (EvtSys1_on_Core_RGF k)), 
               Rely\<^sub>f (snd (EvtSys1_on_Core_RGF k)), 
               Guar\<^sub>f (snd (EvtSys1_on_Core_RGF k)), 
               Post\<^sub>f (snd (EvtSys1_on_Core_RGF k))]"
  apply(rule allI)
  apply(simp add:EvtSys1_on_Core_RGF_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def getrgformula_def)
  apply(rule EvtSys_h)
  apply(clarify)
  apply(case_tac "(a,b)\<in> {(Schedule_RGF k)}")
  using Sched_SatRG Schedule_RGF_def Evt_sat_RG_def E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def 
    Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def snd_conv fst_conv apply (metis singletonD) 
  apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
  apply(clarify)
  using Write_Sampling_Message_SatRG Write_Sampling_Message_RGF_def E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def 
    Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def snd_conv fst_conv Evt_sat_RG_def
  apply (smt Abs_unit_cases empty_iff singletonD)  
  apply(case_tac "(a,b)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
  apply(clarify)
  using Read_Sampling_Message_SatRG Read_Sampling_Message_RGF_def E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def 
    Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def snd_conv fst_conv Evt_sat_RG_def
  apply (smt Abs_unit_cases empty_iff singletonD)  
  apply blast
  
  apply(clarify)
  apply(case_tac "(a,b)\<in> {(Schedule_RGF k)}")
  apply(simp add:Schedule_RGF_def Schedule_RGCond_def Pre\<^sub>e_def getrgformula_def)
  apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
  apply clarify
  apply(simp add:Write_Sampling_Message_RGF_def Write_Sampling_Message_RGCond_def Pre\<^sub>e_def getrgformula_def)
  apply(case_tac "(a,b)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
  apply(clarify)
  apply(simp add:Read_Sampling_Message_RGF_def Read_Sampling_Message_RGCond_def Pre\<^sub>e_def getrgformula_def)
  apply blast
  
  apply(clarify)
  apply(case_tac "(a,b)\<in> {(Schedule_RGF k)}")
  apply(simp add:Schedule_RGF_def Schedule_RGCond_def Rely\<^sub>e_def getrgformula_def)
  apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
  apply clarify
  apply(simp add:Write_Sampling_Message_RGF_def Write_Sampling_Message_RGCond_def Rely\<^sub>e_def getrgformula_def)
  apply(case_tac "(a,b)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
  apply(clarify)
  apply(simp add:Read_Sampling_Message_RGF_def Read_Sampling_Message_RGCond_def Rely\<^sub>e_def getrgformula_def)
  apply blast
  
  apply(clarify)
  apply(case_tac "(a,b)\<in> {(Schedule_RGF k)}")
  apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Guar\<^sub>e_def) apply auto[1] 
  apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
  apply(simp add:Write_Sampling_Message_RGF_def Write_Sampling_Message_RGCond_def getrgformula_def Guar\<^sub>e_def)
  apply(case_tac "(a,b)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
  apply(simp add:Read_Sampling_Message_RGF_def Read_Sampling_Message_RGCond_def getrgformula_def Guar\<^sub>e_def)
  apply blast
  
  apply(clarify)
  apply(case_tac "(a,b)\<in> {(Schedule_RGF k)}")
  apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Guar\<^sub>e_def)
  apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
  apply(simp add:Write_Sampling_Message_RGF_def Write_Sampling_Message_RGCond_def getrgformula_def Guar\<^sub>e_def)
  apply(case_tac "(a,b)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
  apply(simp add:Read_Sampling_Message_RGF_def Read_Sampling_Message_RGCond_def getrgformula_def Guar\<^sub>e_def)
  apply blast

  apply(clarify)
  apply(case_tac "(a,b)\<in> {(Schedule_RGF k)}")
    apply(case_tac "(aa,ba)\<in> {(Schedule_RGF k)}")
    apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Pre\<^sub>e_def)
    apply(case_tac "(aa,ba)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
    apply(simp add:Write_Sampling_Message_RGF_def Write_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
    apply(case_tac "(aa,ba)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
    apply(simp add:Read_Sampling_Message_RGF_def Read_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
    apply blast
  apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
    apply(case_tac "(aa,ba)\<in> {(Schedule_RGF k)}")
    apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Pre\<^sub>e_def)
    apply(case_tac "(aa,ba)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
    apply(simp add:Write_Sampling_Message_RGF_def Write_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
    apply(case_tac "(aa,ba)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
    apply(simp add:Read_Sampling_Message_RGF_def Read_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
    apply blast
  apply(case_tac "(a,b)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
    apply(case_tac "(aa,ba)\<in> {(Schedule_RGF k)}")
    apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Pre\<^sub>e_def)
    apply(case_tac "(aa,ba)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
    apply(simp add:Write_Sampling_Message_RGF_def Write_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
    apply(case_tac "(aa,ba)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
    apply(simp add:Read_Sampling_Message_RGF_def Read_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
    apply blast
  apply blast
  apply (simp add:stable_def)
  by simp

lemma EvtSys_on_core_SatRG: 
  "\<forall>k. \<turnstile> fst (EvtSys_on_Core_RGF k) sat\<^sub>s 
              [Pre\<^sub>f (snd (EvtSys_on_Core_RGF k)), 
               Rely\<^sub>f (snd (EvtSys_on_Core_RGF k)), 
               Guar\<^sub>f (snd (EvtSys_on_Core_RGF k)), 
               Post\<^sub>f (snd (EvtSys_on_Core_RGF k))]"
  apply(rule allI)
  apply(simp add:EvtSys_on_Core_RGF_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def getrgformula_def)
  apply(rule EvtSeq_h)
  apply(simp add:E\<^sub>e_def Core_Init_RGF_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def)
  using Core_Init_SatRG getrgformula_def apply (simp add: Evt_sat_RG_def Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def) 
  using EvtSys1_on_core_SatRG apply simp
  apply(simp add:Core_Init_RGF_def Core_Init_RGCond_def Pre\<^sub>e_def getrgformula_def)
  apply(simp add:EvtSys1_on_Core_RGF_def Post\<^sub>f_def getrgformula_def)
  apply(simp add:Core_Init_RGF_def Core_Init_RGCond_def Rely\<^sub>e_def getrgformula_def)
  apply(simp add:EvtSys1_on_Core_RGF_def Rely\<^sub>f_def getrgformula_def)
  apply(simp add:Core_Init_RGF_def Core_Init_RGCond_def Guar\<^sub>e_def getrgformula_def)
  apply(simp add:EvtSys1_on_Core_RGF_def Core_Init_RGCond_def Guar\<^sub>f_def getrgformula_def)
  by (simp add:EvtSys1_on_Core_RGF_def Core_Init_RGF_def Core_Init_RGCond_def Post\<^sub>e_def Pre\<^sub>f_def getrgformula_def)

lemma spec_sat_rg: "\<turnstile> ARINCXKernel_Spec SAT [{s0}, {}, UNIV, UNIV]"
  apply (rule ParallelESys)
  apply(simp add:ARINCXKernel_Spec_def) using EvtSys_on_core_SatRG
    apply (simp add: Guar\<^sub>e\<^sub>s_def Guar\<^sub>f_def Post\<^sub>e\<^sub>s_def Post\<^sub>f_def Pre\<^sub>e\<^sub>s_def Pre\<^sub>f_def Rely\<^sub>e\<^sub>s_def Rely\<^sub>f_def) 
  apply(simp add:ARINCXKernel_Spec_def EvtSys_on_Core_RGF_def Pre\<^sub>e\<^sub>s_def getrgformula_def)
  apply simp
  apply(rule allI)+
  apply(simp add:ARINCXKernel_Spec_def EvtSys_on_Core_RGF_def Guar\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def getrgformula_def)
  apply (simp add: Collect_mono Id_fstsnd_eq)
  apply simp+
  done

lemma init_sat_inv: "{s0}\<subseteq>cur_part" 
  apply(simp add:s0_init System_Init_def cur_part_def)
  by (metis UNIV_I exE_some imageE surj_p2c)


lemma stb_guar_sched: "stable cur_part ((\<lbrace>\<ordfeminine>cur (c2s conf x) = (SOME p. c2s conf x \<in> p2s conf p) \<and>
                         (\<forall>c. c \<noteq> x \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur (c2s conf c))\<rbrace>)\<union>Id)"
  apply(simp add:stable_def cur_part_def)
  apply(rule allI)
  apply(rule impI)
  apply(rule allI)
  apply(rule conjI)
  apply(rule impI)
  apply(rule allI)
  apply (metis (no_types, lifting) UNIV_I imageE inj_surj_c2s someI2_ex)
  by auto

lemma stb_guar_wrtsamp: "stable cur_part (\<lbrace>\<ordfeminine>cur= \<ordmasculine>cur\<rbrace>\<union>Id)"
  by (simp add:stable_def cur_part_def)
  
lemma evts_stb_invar: "\<forall>ef\<in>evtrgfset. stable cur_part (Guar\<^sub>e ef)"
  unfolding evtrgfset_def
  apply(clarify)
  apply(case_tac "(a, b) \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond)})")
  apply(simp add:Core_Init_RGCond_def Guar\<^sub>e_def getrgformula_def stable_def)
  apply(case_tac "(a, b) \<in> (\<Union>k. {(Schedule k, Schedule_RGCond k)})")
  apply(simp add:Schedule_RGCond_def Guar\<^sub>e_def getrgformula_def)
  using stb_guar_sched rgformula.select_convs(3) apply auto[1] 
  apply(case_tac "(a, b) \<in> (\<Union>(k, p, m). {(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})")
  apply(simp add:Write_Sampling_Message_RGCond_def Guar\<^sub>e_def getrgformula_def) 
  using stb_guar_wrtsamp rgformula.select_convs(3) apply auto[1] 
  apply(case_tac "(a, b) \<in> (\<Union>(k, p). {(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})")
  apply(simp add:Read_Sampling_Message_RGCond_def Guar\<^sub>e_def getrgformula_def)
  using stb_guar_wrtsamp rgformula.select_convs(3) apply auto[1] 
  by blast

theorem ARINC_invariant_theorem:
  "ParES_sat_invar (paresys_spec ARINCXKernel_Spec) {s0} cur_part"
  using invariant_theorem[of ARINCXKernel_Spec "{s0}" evtrgffun cur_part]
    spec_sat_rg evts_stb_invar evtrgfset_eq_allevts_ARINCSpec 
    all_basic_evts_arinc evts_stb_invar init_sat_inv bsc_evts_rgfs by auto

end