section \<open>Formal specification of ARINC653 Multicore Separation Kernel\<close>

theory ARINC653_MultiCore
imports Ann_PiCore_Syntax Ann_PiCore_RG_IFS
begin

subsection \<open>functional specification\<close>
typedecl Part
typedecl Sched
typedecl Message 
typedecl Port
typedecl Core

typedecl SampChannel

datatype Domain = P Part | S Sched | F 

record Config = c2s :: "Core \<Rightarrow> Sched"
                p2s :: "Part \<Rightarrow> Sched set"
                p2p :: "Port \<Rightarrow> Part"
                scsrc :: "SampChannel \<Rightarrow> Port"
                scdests :: "SampChannel \<Rightarrow> Port set"

axiomatization conf::Config 
  where bij_c2s: "bij (c2s conf)" and
        surj_p2c: "surj (p2s conf)" and
        scdests_not_emp: "\<forall>sc. (scdests conf) sc \<noteq> {}" and
        port_disj: "range (scsrc conf) \<inter> (\<Union> (range (scdests conf))) = {}" and 
        no_disconn_port: "\<forall>p. p\<in>range (scsrc conf) \<or> p\<in>\<Union> (range (scdests conf))" and
        no_same_source: "inj (scsrc conf)" and  
        no_same_dest: "(\<forall>ch1 ch2. ch1\<noteq>ch2 \<longrightarrow> 
                         ((scdests conf) ch1 \<inter> (scdests conf) ch2) = {}) " and
        bij_p2p: "inj (p2p conf)"

definition gsch :: "Config \<Rightarrow> Core \<Rightarrow> Sched"
  where "gsch cfg k \<equiv> (c2s cfg) k"

definition is_src_sampport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_src_sampport sc p \<equiv> (p\<in>range (scsrc sc))"

definition is_dest_sampport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_dest_sampport sc p \<equiv> (p\<in>\<Union> (range (scdests sc)))"

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
  using no_same_dest by (meson inj_eq)

lemma same_src_sampport:
  "(scsrc conf) c1 = p1 \<Longrightarrow>
   (scsrc conf) c2 = p2 \<Longrightarrow>
   p1 = p2 \<Longrightarrow>
   c1 = c2 "
  using no_same_source by (meson inj_eq)

definition par_ports :: "Config \<Rightarrow> Part \<Rightarrow> Port set"
  where "par_ports sc pa \<equiv> {p. port_of_part sc p pa}"

lemma "pa\<noteq>pb \<Longrightarrow> par_ports conf pa \<inter> par_ports conf pb = {}"
  using bij_p2p unfolding par_ports_def port_of_part_def by auto

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
                                      \<and> p \<in> (scdests cfg) sch \<and> (p2p cfg) p = p2)"

primrec ch_conn2 :: "Config \<Rightarrow> Domain \<Rightarrow> Domain \<Rightarrow> bool"
  where "ch_conn2 cfg (P p1) d2 = (case d2 of
                                    (P p2) \<Rightarrow> ch_conn cfg p1 p2 |
                                    (S s2) \<Rightarrow> False |
                                      F  \<Rightarrow> False)" |                                     
        "ch_conn2 cfg (S p1) d2 = False" |
        "ch_conn2 cfg F d2 = False"

primrec part_on_core :: "Config \<Rightarrow> Domain \<Rightarrow> Domain \<Rightarrow> bool"
  where "part_on_core cfg (P d1) d2 = (case d2 of
                                        P d22 \<Rightarrow> False |
                                        S d22 \<Rightarrow> d22 \<in>((p2s cfg) d1) |
                                        F \<Rightarrow> False )" |
        "part_on_core cfg (S d1) d2 = False" |
        "part_on_core cfg F d2 = False"


datatype PartMode = IDLE | READY | RUN

record State = cur :: "Sched \<Rightarrow> Part"
               schan :: "SampChannel \<rightharpoonup> Message"
               recv :: "Part \<rightharpoonup> Message"

datatype EL = Core_InitE | ScheduleE | Write_Sampling_MessageE |  Read_Sampling_MessageE

datatype parameter = Port Port | Message Message | Partition Part

type_synonym EventLabel = "EL \<times> (parameter list \<times> Core)" 

definition get_evt_label :: "EL \<Rightarrow> parameter list \<Rightarrow> Core \<Rightarrow> EventLabel" ("_ _ \<rhd> _" [0,0,0] 20)
  where "get_evt_label el ps k \<equiv> (el,(ps,k))"

definition Core_Init :: "Core \<Rightarrow> (EventLabel, Core, State) event" 
  where "Core_Init k \<equiv> 
    EVENT Core_InitE [] \<rhd> k 
    WHERE
      True
    THEN 
      \<lbrace>True\<rbrace> SKIP 
    END"


definition System_Init :: "Config \<Rightarrow> (State \<times> (EventLabel, Core, State) x)"
  where "System_Init cfg \<equiv> (\<lparr>cur = (\<lambda>c. SOME p. c\<in>(p2s cfg) p),
                            schan = (\<lambda>c. None),
                            recv = (\<lambda>c. None)\<rparr>, 
                            (\<lambda>k. Core_Init k))"

definition Schedule :: "Core  \<Rightarrow> (EventLabel, Core, State) event" 
  where "Schedule k  \<equiv> 
    EVENT ScheduleE [] \<rhd> k 
    WHERE True
    THEN 
      \<lbrace>True\<rbrace> \<acute>cur := \<acute>cur((c2s conf) k := SOME p. (c2s conf) k \<in>(p2s conf) p) 
    END"

definition Write_Sampling_Message :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> (EventLabel, Core, State) event" 
  where "Write_Sampling_Message k p m \<equiv> 
    EVENT Write_Sampling_MessageE [Port p, Message m] \<rhd> k 
    WHERE
      is_src_sampport conf p
      \<and> port_of_part conf p (\<acute>cur (gsch conf k))
    THEN
      \<lbrace>is_src_sampport conf p \<and> port_of_part conf p (\<acute>cur (gsch conf k))\<rbrace> 
      \<acute>schan := \<acute>schan (ch_srcsampport conf p := Some m)
    END"

definition Read_Sampling_Message :: "Core \<Rightarrow> Port \<Rightarrow> (EventLabel, Core, State) event" 
  where "Read_Sampling_Message k p \<equiv> 
    EVENT Read_Sampling_MessageE [Port p] \<rhd> k 
    WHERE
      is_dest_sampport conf p 
      \<and> port_of_part conf p (\<acute>cur (gsch conf k))
    THEN
      \<lbrace>is_dest_sampport conf p \<and> port_of_part conf p (\<acute>cur (gsch conf k))\<rbrace> 
      \<acute>recv := \<acute>recv ((p2p conf p) := (\<acute>schan (ch_destsampport conf p)))
    END"

definition Core_Init_RGCond :: " (State) rgformula"
  where "Core_Init_RGCond  \<equiv> RG[\<lbrace>True\<rbrace>,UNIV,Id,\<lbrace>True\<rbrace>]"

definition Schedule_RGCond :: "Core  \<Rightarrow> (State) rgformula"
  where "Schedule_RGCond k  \<equiv> 
   (RG[\<lbrace>True\<rbrace>,
       \<lbrace>True\<rbrace>, 
       (\<lbrace>\<ordfeminine>schan= \<ordmasculine>schan \<and> \<ordfeminine>recv = \<ordmasculine>recv \<and> \<ordfeminine>cur (c2s conf k) = (SOME p. (c2s conf) k \<in>(p2s conf) p)
          \<and> (\<forall>c. c \<noteq> k \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))\<rbrace> \<union> Id),
       \<lbrace>True\<rbrace>])"

definition Write_Sampling_Message_RGCond :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> (State) rgformula"
  where "Write_Sampling_Message_RGCond k p m \<equiv> (
            RG[\<lbrace>True\<rbrace>,
               \<lbrace>\<ordfeminine>cur (c2s conf k)= \<ordmasculine>cur (c2s conf k)\<rbrace>, 
               (\<lbrace>\<ordfeminine>cur = \<ordmasculine>cur \<and> \<ordfeminine>recv = \<ordmasculine>recv \<and> 
                (is_src_sampport conf p \<and> port_of_part conf p (\<ordmasculine>cur (c2s conf k)) \<longrightarrow>
                 (\<forall>ch. ch \<noteq> ch_srcsampport conf p \<longrightarrow> \<ordfeminine>schan ch = \<ordmasculine>schan ch)) \<and> 
                 (\<not> (is_src_sampport conf p \<and> port_of_part conf p (\<ordmasculine>cur (c2s conf k))) \<longrightarrow> 
                  \<ordfeminine>schan  = \<ordmasculine>schan)\<rbrace>),
               \<lbrace>True\<rbrace>])"

definition Read_Sampling_Message_RGCond :: "Core \<Rightarrow> Port \<Rightarrow> (State) rgformula"
  where "Read_Sampling_Message_RGCond k p \<equiv> 
     RG[\<lbrace>True\<rbrace>,
        \<lbrace>\<ordfeminine>cur (c2s conf k)= \<ordmasculine>cur (c2s conf k)\<rbrace>,
        (\<lbrace>\<ordfeminine>cur= \<ordmasculine>cur \<and> \<ordfeminine>schan = \<ordmasculine>schan \<and> (\<forall>x. x \<noteq> \<ordmasculine>cur (gsch conf k) \<longrightarrow> \<ordfeminine>recv x = \<ordmasculine>recv x)\<rbrace>),
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
                                \<and> (\<forall>c. c\<noteq> k \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))\<rbrace>),
                  \<lbrace>True\<rbrace>])"

definition EvtSys_on_Core_RGF :: "Core \<Rightarrow> (EventLabel, Core, State) rgformula_es"
  where "EvtSys_on_Core_RGF k  \<equiv> 
          (rgf_EvtSeq (Core_Init_RGF k) (EvtSys1_on_Core_RGF k),
           RG[\<lbrace>True\<rbrace>,
              \<lbrace>\<ordfeminine>cur (c2s conf k)= \<ordmasculine>cur (c2s conf k)\<rbrace>,
              (\<lbrace>\<ordfeminine>cur= \<ordmasculine>cur \<or> \<ordfeminine>cur (c2s conf k) = (SOME p. (c2s conf) k \<in>(p2s conf) p)
                                \<and> (\<forall>c. c\<noteq> k \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))\<rbrace>),
              \<lbrace>True\<rbrace>])"

definition ARINCXKernel_Spec :: "(EventLabel, Core, State) rgformula_par"
  where "ARINCXKernel_Spec \<equiv> (\<lambda>k. EvtSys_on_Core_RGF k)"

definition Evt_sat_RG:: "(EventLabel, Core, State) event \<Rightarrow> (State) rgformula \<Rightarrow> bool" ("(_\<turnstile>_)" [60,60] 61)
  where "Evt_sat_RG e rg \<equiv> \<turnstile> e sat\<^sub>e [Pre\<^sub>f rg, Rely\<^sub>f rg, Guar\<^sub>f rg, Post\<^sub>f rg]"

lemma Core_Init_SatRG: "\<forall>k. Core_Init k \<turnstile> Core_Init_RGCond"
  apply(simp add:Evt_sat_RG_def)
  apply(rule allI)
  apply(simp add:Core_Init_def)
  apply(rule BasicEvt)
    apply(simp add:body_def)
    apply(rule Basic)
    apply(simp add:Core_Init_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def getrgformula_def)+
    apply auto[1] 
  apply(simp add:Core_Init_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def Rely\<^sub>f_def getrgformula_def guard_def stable_def)
  apply(simp add:Core_Init_RGCond_def Post\<^sub>f_def Rely\<^sub>f_def getrgformula_def stable_def)
  apply(simp add:stable_def Core_Init_RGCond_def getrgformula_def Pre\<^sub>f_def)
  apply(simp add:Core_Init_RGCond_def Guar\<^sub>f_def getrgformula_def stable_def)
  done

lemma inj_surj_c2s: "inj (c2s conf) \<and> surj (c2s conf)"
  using bij_c2s by (simp add: bij_def) 

lemma Sched_SatRG_help1: "{(s, t). t = s\<lparr>cur := (cur s)(c2s conf k := SOME p. c2s conf k \<in> p2s conf p)\<rparr>}
         \<subseteq> \<lbrace>(\<forall>c. c \<noteq> k \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur (c2s conf c))\<rbrace>" 
  using inj_surj_c2s by (simp add: Collect_mono case_prod_beta' inj_eq)

lemma Sched_SatRG: "\<forall>k. Schedule k \<turnstile> Schedule_RGCond k"
  apply(simp add:Evt_sat_RG_def)  
  apply(rule allI)
  apply(simp add:Schedule_def)
  apply(rule BasicEvt)
    apply(simp add:body_def guard_def)
    apply(rule Basic, simp)
       apply(simp add:Schedule_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
      apply(simp add:Schedule_RGCond_def Pre\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  using Sched_SatRG_help1 apply fastforce
     apply(simp add:stable_def Schedule_RGCond_def getrgformula_def Pre\<^sub>f_def)
    apply(simp add:stable_def Schedule_RGCond_def getrgformula_def Post\<^sub>f_def)
   apply(simp add:stable_def Schedule_RGCond_def getrgformula_def Pre\<^sub>f_def)
  by (simp add:Schedule_RGCond_def getrgformula_def Guar\<^sub>f_def)

lemma Write_Sampling_Message_SatRG: 
  "\<forall>k p m. Write_Sampling_Message k p m \<turnstile> Write_Sampling_Message_RGCond k p m"
  apply(simp add:Evt_sat_RG_def)
  apply(rule allI)+
  apply(simp add:Write_Sampling_Message_def)
  apply(rule BasicEvt)
    apply(simp add:body_def guard_def)
    apply(rule Basic)
        apply(simp add:Write_Sampling_Message_RGCond_def Pre\<^sub>f_def getrgformula_def)
       apply(simp add:Write_Sampling_Message_RGCond_def Post\<^sub>f_def getrgformula_def)
      apply (simp add: Write_Sampling_Message_RGCond_def Guar\<^sub>f_def getrgformula_def)
  using gsch_def apply force
     apply(simp add:stable_def Write_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>f_def Rely\<^sub>f_def gsch_def)
    apply(simp add:stable_def Write_Sampling_Message_RGCond_def getrgformula_def Post\<^sub>f_def)
   apply(simp add:stable_def Write_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>f_def Rely\<^sub>f_def)
  by (simp add:Write_Sampling_Message_RGCond_def getrgformula_def Guar\<^sub>f_def)

lemma Read_Sampling_Message_SatRG: "\<forall>k p. Read_Sampling_Message k p \<turnstile> Read_Sampling_Message_RGCond k p"
  apply(simp add:Evt_sat_RG_def)
  apply(rule allI)+ 
  apply(simp add:Read_Sampling_Message_def)
  apply(rule BasicEvt)
    apply(simp add:body_def guard_def)
    apply (rule Basic)
        apply(simp add: Read_Sampling_Message_RGCond_def Rely\<^sub>f_def getrgformula_def stable_def gsch_def)
       apply(simp add: Read_Sampling_Message_RGCond_def Post\<^sub>f_def Rely\<^sub>f_def getrgformula_def stable_def gsch_def)
      apply(simp add: Read_Sampling_Message_RGCond_def Guar\<^sub>f_def getrgformula_def gsch_def)
  using port_of_part_def apply force
     apply (simp add: stable_def Read_Sampling_Message_RGCond_def Rely\<^sub>f_def getrgformula_def gsch_def)
    apply (simp add: stable_def Read_Sampling_Message_RGCond_def Rely\<^sub>f_def Post\<^sub>f_def getrgformula_def gsch_def)
   apply (simp add: stable_def Read_Sampling_Message_RGCond_def Rely\<^sub>f_def Pre\<^sub>f_def getrgformula_def gsch_def)
  by (simp add: Read_Sampling_Message_RGCond_def getrgformula_def Guar\<^sub>f_def)

lemma pre_all_true : "ef \<in> insert (Schedule_RGF k) ((\<Union>(p, m). {Write_Sampling_Message_RGF k p m}) 
      \<union> (\<Union>p. {Read_Sampling_Message_RGF k p})) \<Longrightarrow> Pre\<^sub>e ef = \<lbrace>True\<rbrace>"
  apply (case_tac "ef \<in> {(Schedule_RGF k)}")
   apply (simp add: Schedule_RGF_def getrgformula_def Schedule_RGCond_def Pre\<^sub>e_def)
  apply(case_tac " ef \<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
   apply (simp add: Write_Sampling_Message_RGF_def getrgformula_def Write_Sampling_Message_RGCond_def Pre\<^sub>e_def)
   apply force
  apply (simp add: Read_Sampling_Message_RGF_def getrgformula_def Read_Sampling_Message_RGCond_def Pre\<^sub>e_def)
  by force

lemma post_all_true : "ef \<in> insert (Schedule_RGF k) ((\<Union>(p, m). {Write_Sampling_Message_RGF k p m}) 
      \<union> (\<Union>p. {Read_Sampling_Message_RGF k p})) \<Longrightarrow> Post\<^sub>e ef = \<lbrace>True\<rbrace>"
  apply (case_tac "ef \<in> {(Schedule_RGF k)}")
   apply (simp add: Schedule_RGF_def getrgformula_def Schedule_RGCond_def Post\<^sub>e_def)
  apply(case_tac " ef \<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
   apply (simp add: Write_Sampling_Message_RGF_def getrgformula_def Write_Sampling_Message_RGCond_def Post\<^sub>e_def)
   apply force
  apply (simp add: Read_Sampling_Message_RGF_def getrgformula_def Read_Sampling_Message_RGCond_def Post\<^sub>e_def)
  by force


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
       apply force
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
     apply(case_tac "(a,b)\<in> {(Schedule_RGF k)}")
      apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Pre\<^sub>e_def)
     apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
      apply(simp add:Write_Sampling_Message_RGF_def Write_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
     apply(case_tac "(a,b)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
      apply(simp add:Read_Sampling_Message_RGF_def Read_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
     apply blast
    apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
     apply(case_tac "(a,b)\<in> {(Schedule_RGF k)}")
      apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Pre\<^sub>e_def)
     apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
      apply(simp add:Write_Sampling_Message_RGF_def Write_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
     apply(case_tac "(a,b)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
      apply(simp add:Read_Sampling_Message_RGF_def Read_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
     apply blast
    apply(case_tac "(a,b)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
     apply(case_tac "(a,b)\<in> {(Schedule_RGF k)}")
      apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Pre\<^sub>e_def)
     apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Write_Sampling_Message_RGF k p m})")
      apply(simp add:Write_Sampling_Message_RGF_def Write_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
     apply(case_tac "(a,b)\<in>(\<Union>p. {Read_Sampling_Message_RGF k p})")
      apply(simp add:Read_Sampling_Message_RGF_def Read_Sampling_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)
     apply blast
     apply blast
  using pre_all_true apply force
   apply (simp add: Ann_PiCore_Hoare.stable_def)
  by force


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
    apply auto[1]
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


axiomatization s0 where s0_init: "s0 \<equiv> fst (System_Init conf)"
axiomatization x0 where x0_init: "x0 \<equiv> snd (System_Init conf)"
axiomatization C0 where C0_init: "C0 = (paresys_spec ARINCXKernel_Spec, s0, x0)"

definition domevt :: "State \<Rightarrow> Core \<Rightarrow> (EventLabel, Core, State) event \<Rightarrow> Domain"
  where "domevt s k e \<equiv>  (if (\<exists>p m. e = Write_Sampling_Message k p m )\<or>                             
                             (\<exists>p. e = Read_Sampling_Message k p) then
                              P  ((cur s) (gsch conf k))
                          else if e = Schedule k then S (gsch conf k)
                          else F)" 

definition exec_step :: "(EventLabel, Core, State, Domain) action \<Rightarrow> 
 ((EventLabel, Core, State) pesconf \<times> (EventLabel, Core, State) pesconf) set"
  where "exec_step a \<equiv> {(P,Q). (P -pes-(actk a)\<rightarrow> Q) \<and> 
                                        ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                                              \<and> domevt (gets P) k e = domain a) \<or>
                                        (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx P) k 
                                          \<and> domevt (gets P) k (eventof a) = domain a))}"

definition interf :: "Domain \<Rightarrow> Domain \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
  where "interf d1 d2 \<equiv> if d1 = d2 then True
                         else if part_on_core conf d2 d1 then True
                         else if ch_conn2 conf d1 d2 then True
                         else if d1 = F \<or> d2 = F then True
                         else False"

definition noninterf1 :: "Domain \<Rightarrow> Domain \<Rightarrow> bool" ("(_ \<setminus>\<leadsto> _)" [70,71] 60)
  where "u \<setminus>\<leadsto> v \<equiv> \<not> (u \<leadsto> v)"


definition state_obs_sched :: "State \<Rightarrow> Sched \<Rightarrow> State"
  where "state_obs_sched s d \<equiv> s0\<lparr>cur:=(cur s0) (d:=(cur s) d)\<rparr>"


definition schan_obs_part :: "State \<Rightarrow> Part \<Rightarrow> (SampChannel \<rightharpoonup> Message)"
  where "schan_obs_part s p \<equiv> (schan s) |` (par_sampchan conf p)  "

definition state_obs_part :: "State \<Rightarrow> Part \<Rightarrow> State"
  where "state_obs_part s p \<equiv> s0\<lparr>schan := schan_obs_part s p, 
                                 recv := (recv s0) (p := (recv s) p)\<rparr>"

primrec state_obs :: "State \<Rightarrow> Domain \<Rightarrow> State"
  where "state_obs s (P p) = state_obs_part s p" |
        "state_obs s (S p) = state_obs_sched s p"|
        "state_obs s F = s0"

lemma ch_destsampport_same : "\<lbrakk>schan_obs_part s1 d = schan_obs_part s2 d; port_of_part conf p d; 
      is_dest_sampport conf p\<rbrakk> \<Longrightarrow> schan s1 (ch_destsampport conf p) = schan s2 (ch_destsampport conf p)"
  apply (simp add: schan_obs_part_def par_dest_sampling_ports_def par_ports_def par_sampchan_def)
  by (metis (mono_tags, lifting) Un_iff imageI mem_Collect_eq restrict_in)

definition state_equiv :: "State \<Rightarrow> Domain \<Rightarrow> State \<Rightarrow> bool" ("(_ \<sim>_\<sim> _)" [70,69,70] 60)
  where "state_equiv s d t \<equiv> state_obs s d = state_obs t d"

lemma state_equiv_transitive: "\<lbrakk>s \<sim> d \<sim> t; t \<sim> d \<sim> r\<rbrakk> \<Longrightarrow> s \<sim> d \<sim> r"
  by (simp add:state_equiv_def)
    
lemma state_equiv_symmetric : "s \<sim> d \<sim> t \<Longrightarrow> t \<sim> d \<sim> s"
  by (simp add:state_equiv_def)

lemma state_equiv_reflexive : "s \<sim> d \<sim> s"
  by (simp add:state_equiv_def)


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
      by auto
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
  apply(rule allI)+
  apply(case_tac "ef1\<in>(\<Union>k.{(Core_Init k, Core_Init_RGCond)})")
    apply(case_tac "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond)})")
    apply(clarify) using neq_coreinit_sched apply (simp add: E\<^sub>e_def) 
    apply(case_tac "ef2 \<in> (\<Union>k.{(Schedule k, Schedule_RGCond k)})")
    apply(clarify) using neq_coreinit_sched apply (simp add:E\<^sub>e_def)
    apply(case_tac "ef2 \<in> (\<Union>(k, p, m).{(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})")
    apply(clarify) using neq_coreinit_wrtsamp apply (simp add:E\<^sub>e_def)
    apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})")
    apply(clarify) using neq_coreinit_rdsamp apply (simp add:E\<^sub>e_def)
    using evtrgfset_def apply blast
  apply(case_tac "ef1 \<in> (\<Union>k.{(Schedule k, Schedule_RGCond k)})")
    apply(case_tac "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond)})")
    apply(clarify) using neq_coreinit_sched apply (metis E\<^sub>e_def fst_conv)
    apply(case_tac "ef2 \<in> (\<Union>k.{(Schedule k, Schedule_RGCond k)})")
    apply(clarify) using neq_schedule apply (metis E\<^sub>e_def fst_conv)
    apply(case_tac "ef2 \<in> (\<Union>(k, p, m).{(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})")
    apply(clarify) using neq_sched_wrtsamp apply (simp add: E\<^sub>e_def)
    apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})")
    apply(clarify) using neq_sched_rdsamp apply (simp add: E\<^sub>e_def)
    apply(simp add: evtrgfset_def)
  apply(case_tac "ef1 \<in> (\<Union>(k, p, m).{(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})")
     apply(case_tac "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond)})")
    apply(clarify) using neq_coreinit_wrtsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
    apply(case_tac "ef2 \<in> (\<Union>k.{(Schedule k, Schedule_RGCond k)})")
    apply(clarify) using neq_sched_wrtsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
    apply(case_tac "ef2 \<in> (\<Union>(k, p, m).{(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})")
    apply(clarify) using neq_wrt_samp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
    apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})")
    apply(clarify) using neq_wrtsamp_rdsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
    apply(simp add: evtrgfset_def)
  apply(case_tac "ef1 \<in> (\<Union>(k, p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})")
    apply(case_tac "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond)})")
    apply(clarify) using neq_coreinit_rdsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
    apply(case_tac "ef2 \<in> (\<Union>k.{(Schedule k, Schedule_RGCond k)})")
    apply(clarify) using neq_sched_rdsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
    apply(case_tac "ef2 \<in> (\<Union>(k, p, m).{(Write_Sampling_Message k p m, Write_Sampling_Message_RGCond k p m)})")
    apply(clarify) using neq_wrtsamp_rdsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
    apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Read_Sampling_Message k p, Read_Sampling_Message_RGCond k p)})")
    apply(clarify) using neq_rd_samp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
    by(simp add: evtrgfset_def)+

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

interpretation RG_InfoFlow C0 exec_step interf state_equiv state_obs domevt 
  ARINCXKernel_Spec s0 x0 evtrgffun "paresys_spec ARINCXKernel_Spec"
    using state_equiv_transitive state_equiv_reflexive state_equiv_symmetric exec_step_def 
      C0_init all_basic_evts_arinc bsc_evts_rgfs spec_sat_rg
    InfoFlow.intro[of state_equiv exec_step domevt]
    RG_InfoFlow.intro[of exec_step state_equiv domevt C0 ARINCXKernel_Spec 
                        s0 x0 evtrgffun "paresys_spec ARINCXKernel_Spec"]
    RG_InfoFlow_axioms.intro[of C0 ARINCXKernel_Spec s0 x0 "paresys_spec ARINCXKernel_Spec" evtrgffun]  
    by (metis (no_types, lifting) option.sel)

lemma s0_update_help: "\<lbrakk>schan1 = schan2; recv1 = recv2 \<rbrakk> \<Longrightarrow> 
                      s0\<lparr> schan := schan1, recv := recv1\<rparr> = s0\<lparr> schan := schan2, recv := recv2\<rparr>"
  by blast

lemma Core_Init_sat_SCE: "\<exists>\<S>. Core_Init k \<in> \<S> \<and> step_consistent_e \<S> (Core_Init k)"
  apply (rule sc_e_Basic, simp add: Core_Init_def)
  by (simp add: body_def  sc_p.Basic)

lemma Schedule_sat_SCE: "\<exists>\<S>. Schedule k \<in> \<S> \<and> step_consistent_e \<S> (Schedule k)"
  apply (rule sc_e_Basic, simp add: Schedule_def)
  apply (simp add: body_def)
  apply (rule sc_p.Basic, clarsimp)
  apply (case_tac u)
   apply (simp add: state_equiv_def state_obs_part_def schan_obs_part_def)
   apply ( simp add: state_equiv_def state_obs_sched_def)
  by ( simp add: state_equiv_def)

lemma Read_Sampling_sat_SCE: "\<exists>\<S>. Read_Sampling_Message k p \<in> \<S> \<and> step_consistent_e \<S> (Read_Sampling_Message k p)"
  apply (rule sc_e_Basic, simp add: Read_Sampling_Message_def)
  apply (simp add: body_def)
  apply (rule sc_p.Basic, clarsimp)
  apply (case_tac u)
  apply (case_tac "ka = k", simp)
    apply (case_tac "x1 = (cur s1) (gsch conf k)")
     apply (erule impE)
      apply (metis domevt_def interf_def) 
     apply (simp add: state_equiv_def state_obs_part_def schan_obs_part_def, clarify)
     apply (rule s0_update_help)
      apply (simp add: System_Init_def s0_init)
     apply (metis (no_types, lifting) State.ext_inject State.update_convs(2) State.update_convs(3) 
            System_Init_def ch_destsampport_same prod.sel(1) s0_init schan_obs_part_def)
    apply (simp add: port_of_part_def schan_obs_part_def state_equiv_def state_obs_part_def)
   apply (simp add: state_equiv_def state_obs_part_def schan_obs_part_def, clarify)
   apply (rule s0_update_help, simp add: System_Init_def s0_init)
   apply (metis (no_types, lifting) State.ext_inject State.update_convs(2) State.update_convs(3) 
      System_Init_def ch_destsampport_same port_of_part_def prod.sel(1) s0_init schan_obs_part_def)
  apply (simp add: state_equiv_def state_obs_sched_def)
  by ( simp add: state_equiv_def)

lemma Write_Sampling_sat_SCE: "\<exists>\<S>. Write_Sampling_Message k p m \<in> \<S> \<and> step_consistent_e \<S> (Write_Sampling_Message k p m)"
  apply (rule sc_e_Basic, simp add: Write_Sampling_Message_def)
  apply (simp add: body_def)
  apply (rule sc_p.Basic, clarsimp)
  apply (case_tac u)
   apply (simp add: state_equiv_def state_obs_part_def schan_obs_part_def, clarify)
   apply (rule s0_update_help)
    apply (metis (no_types, lifting) State.ext_inject State.update_convs(2) State.update_convs(3) 
       System_Init_def fun_upd_restrict_conv prod.sel(1) s0_init)
   apply (simp add: System_Init_def s0_init)
   apply (simp add: state_equiv_def state_obs_sched_def)
  by ( simp add: state_equiv_def)

lemma Core_Init_sat_LRE: 
  "\<forall>u s1 s2 x. (s1,s2) \<in> Guar\<^sub>f Core_Init_RGCond 
                \<longrightarrow> ((domevt s1 k (Core_Init x)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
  apply (simp add: Core_Init_RGCond_def Guar\<^sub>f_def getrgformula_def, clarsimp)
  apply (case_tac u, simp add: vpeq_reflexive)
  using vpeq_reflexive apply force
  by ( simp add: state_equiv_def)


lemma Schedule_sat_LRE: 
  "\<forall>u s1 s2 x. (s1,s2) \<in> Guar\<^sub>f (Schedule_RGCond x) 
                \<longrightarrow> ((domevt s1 k (Schedule x)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
  apply (simp add: Schedule_RGCond_def Guar\<^sub>f_def getrgformula_def, clarsimp)
  apply (case_tac "x = k")
  apply (case_tac u, simp add: vpeq_reflexive, clarsimp)
   apply (simp add: state_equiv_def state_obs_part_def)
  using schan_obs_part_def apply presburger
  apply (simp add: vpeq_reflexive, clarsimp)
  apply (simp add: state_equiv_def state_obs_sched_def)
    apply (simp add: domevt_def gsch_def neq_sched_rdsamp neq_sched_wrtsamp)
    apply (metis (mono_tags, lifting) inj_surj_c2s interf_def noninterf1_def surj_def)
  using state_equiv_def state_obs.simps(3) apply presburger
  using domevt_def interf_def neq_sched_rdsamp neq_sched_wrtsamp neq_schedule noninterf1_def by presburger


lemma Read_Sampling_sat_LRE:
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f (Read_Sampling_Message_RGCond x p) 
                \<longrightarrow> ((domevt s1 k (Read_Sampling_Message x p)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
  apply (simp add: Read_Sampling_Message_RGCond_def Guar\<^sub>f_def getrgformula_def, clarsimp)
  apply (case_tac "x = k")
  apply (case_tac u, simp add: vpeq_reflexive, clarsimp)
   apply (case_tac "x1 = (cur s1) (gsch conf x)")
    apply (metis domevt_def interf_def noninterf1_def)
   apply (simp add: state_equiv_def state_obs_part_def)
   apply (rule s0_update_help, simp add: schan_obs_part_def)
   apply blast
    apply (simp add: state_equiv_def state_obs_sched_def)
  using state_equiv_def state_obs.simps(3) apply presburger
  by (metis domevt_def interf_def neq_rd_samp neq_sched_rdsamp neq_wrtsamp_rdsamp noninterf1_def)

lemma Write_Sampling_sat_LRE1:
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f (Write_Sampling_Message_RGCond k p m) 
                \<longrightarrow> ((domevt s1 k (Write_Sampling_Message k p m)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
proof-
  {
    fix u s1 s2 k
    assume a0: "(s1,s2) \<in> Guar\<^sub>f (Write_Sampling_Message_RGCond k p m)"
       and a1: "domevt s1 k (Write_Sampling_Message k p m) \<setminus>\<leadsto> u"
    then have eq: "cur s2 = cur s1 \<and> recv s2 = recv s1 \<and> 
    (is_src_sampport conf p \<and> port_of_part conf p ((cur s1) (c2s conf k)) \<longrightarrow>
    (\<forall>ch. ch \<noteq> (ch_srcsampport conf p) \<longrightarrow> (schan s1) ch = (schan s2) ch)) \<and> 
    (\<not> (is_src_sampport conf p \<and> port_of_part conf p ((cur s1) (c2s conf k))) \<longrightarrow>
    schan s1 = schan s2)"
      using a0 unfolding Write_Sampling_Message_RGCond_def Guar\<^sub>f_def getrgformula_def 
      by auto
    then have "s1 \<sim>u\<sim> s2"
    proof-
      {
        assume pre_cond: "is_src_sampport conf p \<and> port_of_part conf p ((cur s1) (c2s conf k))"
        have "domevt s1 k (Write_Sampling_Message k p m) = P ((cur s1) (c2s conf k))"
          by (metis domevt_def gsch_def)
      then have non_inter:"P ((cur s1) (c2s conf k)) \<noteq> u \<and> 
              \<not>(part_on_core conf u (P ((cur s1) (c2s conf k)) )) \<and> 
              \<not>ch_conn2 conf (P ((cur s1) (c2s conf k))) u" 
        by (metis a1 interf_def noninterf1_def)
      then have "(u = F \<or> (\<exists>d1. u = S d1)) \<or> (\<exists>d1. u=P d1)"
        by (metis Domain.exhaust)
      then have ?thesis
      proof
        assume "u = F \<or> (\<exists>d1. u = S d1)"
        thus ?thesis
          using eq state_equiv_def state_obs_sched_def by force
      next
        assume u:"\<exists>d1. u=P d1"
        then obtain d1 where u:"u=P d1" by auto
        then have d1_not_cur_core:"d1 \<noteq> ((cur s1) (c2s conf k))"
          using non_inter by blast
        then have "(\<exists>d1. u= S d1) \<or> \<not>ch_conn conf ((cur s1) (c2s conf k)) d1"
          using non_inter u by auto
        thus ?thesis
        proof
          assume "\<exists>d1. u = S d1" thus ?thesis using u by auto
        next
          assume a0:"\<not>ch_conn conf ((cur s1) (c2s conf k)) d1"   
          then have a0:"(\<forall>sch p. (p2p conf (scsrc conf sch) = cur s1 (c2s conf k)) \<longrightarrow> 
                  \<not>(p \<in> scdests conf sch \<and> p2p conf p = d1))"
            unfolding ch_conn_def by auto
          obtain ch where  eq_schan:"ch =(ch_srcsampport conf p) \<and>  
            (\<forall>ch'. (ch'\<noteq>ch \<longrightarrow> (schan s2) ch' = (schan s1) ch'))"
            using eq by fastforce
          have "ch \<notin>(par_sampchan conf d1)"
          proof 
            assume ch_par:"ch \<in> (par_sampchan conf d1)"
            then have "ch \<in> (ch_srcsampport conf) ` (par_src_sampling_ports conf (par_ports conf d1)) \<or>
                    ch \<in> (ch_destsampport conf) `(par_dest_sampling_ports conf (par_ports conf d1))"
              using a0 unfolding par_sampchan_def by auto  
            then show False
              unfolding par_sampchan_def ch_srcsampport_def
              using  a0 d1_not_cur_core pre_cond eq_schan  ch_par port_disj scdests_not_emp no_disconn_port  
                    no_same_source no_same_dest bij_p2p    
              unfolding  ch_srcsampport_def par_src_sampling_ports_def par_ports_def port_of_part_def
                  is_src_sampport_def par_dest_sampling_ports_def is_dest_sampport_def
                  image_def ch_destsampport_def par_sampchan_def gsch_def 
              apply auto
               apply (metis (mono_tags))
              by (metis (mono_tags, lifting))
          qed
          then have "\<forall>ch \<in>(par_sampchan conf d1). (schan s2) ch = (schan s1) ch" 
            using eq_schan by force 
          then have "schan_obs_part s1 d1 = schan_obs_part s2 d1" 
            unfolding  schan_obs_part_def restrict_map_def by auto
          then have "state_obs_part s1 d1 = state_obs_part s2 d1"  
            unfolding state_obs_part_def
            using eq by auto      
          thus ?thesis using u unfolding state_equiv_def by auto  
        qed        
      qed
    } note l=this
     {assume "\<not> is_src_sampport conf p \<and> port_of_part conf p ((cur s1) (c2s conf k))"
      then have "cur s2= cur s1 \<and> schan s2 = schan s1"
        using eq by auto
      then have "s1 = s2" 
        by (simp add: eq)
      then have "s1 \<sim>u\<sim> s2" 
        unfolding state_equiv_def by auto
    } 
    thus ?thesis using eq l 
      by (metis State.surjective old.unit.exhaust vpeq_reflexive)
  qed
}thus ?thesis by auto
qed

lemma Write_Sampling_sat_LRE:
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f (Write_Sampling_Message_RGCond x p m) 
                \<longrightarrow> ((domevt s1 k (Write_Sampling_Message x p m)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
  apply (clarsimp, case_tac "x = k")
  using Write_Sampling_sat_LRE1 apply blast
  by (metis domevt_def interf_def neq_sched_wrtsamp neq_wrt_samp neq_wrtsamp_rdsamp noninterf1_def)

lemma uwce_LRE_help: "\<forall>x. ef \<in> all_evts_es (fst (ARINCXKernel_Spec x)) \<and> (s1,s2) \<in> Guar\<^sub>e ef \<longrightarrow> 
                                    ((domevt s1 k (E\<^sub>e ef)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
  proof -
  {
    fix x
    assume p0: "ef\<in>all_evts_es (fst (ARINCXKernel_Spec x))" 
    then have "ef\<in>all_evts_es (fst (EvtSys_on_Core_RGF x))" by (simp add:ARINCXKernel_Spec_def)
    then have "ef\<in>insert (Core_Init_RGF x) (all_evts_es (fst (EvtSys1_on_Core_RGF x)))" 
      by (simp add:EvtSys_on_Core_RGF_def)
    then have "ef = (Core_Init_RGF x) \<or> ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGF x))" by auto
    then have "(s1,s2) \<in> Guar\<^sub>e ef \<longrightarrow> ((domevt s1 k (E\<^sub>e ef)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
      proof
        assume a0: "ef = Core_Init_RGF x"
        then show ?thesis
          by (simp add: Core_Init_RGF_def Core_Init_sat_LRE E\<^sub>e_def Guar\<^sub>e_def Guar\<^sub>f_def)          
      next
        assume a1: "ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGF x))"
        then have "ef\<in>{Schedule_RGF x} \<union>
                      {ef. \<exists>p m. ef = Write_Sampling_Message_RGF x p m} \<union>
                      {ef. \<exists>p. ef = Read_Sampling_Message_RGF x p}" 
          using all_evts_es_esys EvtSys1_on_Core_RGF_def by auto
        then have "ef\<in>{Schedule_RGF x} 
                  \<or> ef\<in>{ef. \<exists>p m. ef = Write_Sampling_Message_RGF x p m} 
                  \<or> ef\<in>{ef. \<exists>p. ef = Read_Sampling_Message_RGF x p}" by auto
        then show ?thesis
          proof
            assume "ef\<in>{Schedule_RGF x}"
            then show ?thesis 
              by (simp add: E\<^sub>e_def Guar\<^sub>e_def Guar\<^sub>f_def Schedule_RGF_def Schedule_sat_LRE) 
          next
            assume "ef\<in>{ef. \<exists>p m. ef = Write_Sampling_Message_RGF x p m}
                    \<or> ef\<in>{ef. \<exists>p. ef = Read_Sampling_Message_RGF x p}"
            then show ?thesis 
              proof
                assume "ef\<in>{ef. \<exists>p m. ef = Write_Sampling_Message_RGF x p m}"
                then have "\<exists>p m. ef = Write_Sampling_Message_RGF x p m" by auto
                then obtain p and m where "ef = Write_Sampling_Message_RGF x p m" by auto
                then show ?thesis 
                  by (simp add: E\<^sub>e_def Guar\<^sub>e_def Guar\<^sub>f_def Write_Sampling_Message_RGF_def Write_Sampling_sat_LRE)
              next
                assume "ef\<in>{ef. \<exists>p. ef = Read_Sampling_Message_RGF x p}"
                then have "\<exists>p. ef = Read_Sampling_Message_RGF x p" by auto
                then obtain p where "ef = Read_Sampling_Message_RGF x p" by auto
                then show ?thesis 
                  by (simp add: E\<^sub>e_def Guar\<^sub>e_def Guar\<^sub>f_def Read_Sampling_Message_RGF_def Read_Sampling_sat_LRE)
              qed
          qed
      qed
  }
  then show ?thesis by auto
qed


lemma uwce_SCE_help: "\<forall>k. ef \<in> all_evts_es (fst (ARINCXKernel_Spec k)) \<longrightarrow> (\<exists>\<S>. E\<^sub>e ef \<in> \<S> \<and> step_consistent_e \<S> (E\<^sub>e ef))"
  proof -
  {
    fix k
    assume p0: "ef\<in>all_evts_es (fst (ARINCXKernel_Spec k))" 
    then have "ef\<in>all_evts_es (fst (EvtSys_on_Core_RGF k))" by (simp add:ARINCXKernel_Spec_def)
    then have "ef\<in>insert (Core_Init_RGF k) (all_evts_es (fst (EvtSys1_on_Core_RGF k)))" 
      by (simp add:EvtSys_on_Core_RGF_def)
    then have "ef = (Core_Init_RGF k) \<or> ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGF k))" by auto
    then have "\<exists>\<S>. E\<^sub>e ef \<in> \<S> \<and> step_consistent_e \<S> (E\<^sub>e ef)"
      proof
        assume a0: "ef = Core_Init_RGF k"
        then show ?thesis 
          by (simp add: Core_Init_RGF_def Core_Init_sat_SCE E\<^sub>e_def)  
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
            then show ?thesis 
              by (simp add: E\<^sub>e_def Schedule_RGF_def Schedule_sat_SCE) 
          next
            assume "ef\<in>{ef. \<exists>p m. ef = Write_Sampling_Message_RGF k p m}
                    \<or> ef\<in>{ef. \<exists>p. ef = Read_Sampling_Message_RGF k p}"
            then show ?thesis 
              proof
                assume "ef\<in>{ef. \<exists>p m. ef = Write_Sampling_Message_RGF k p m}"
                then have "\<exists>p m. ef = Write_Sampling_Message_RGF k p m" by auto
                then obtain p and m where "ef = Write_Sampling_Message_RGF k p m" by auto
                then show ?thesis 
                  by (simp add: E\<^sub>e_def Write_Sampling_Message_RGF_def Write_Sampling_sat_SCE)
              next
                assume "ef\<in>{ef. \<exists>p. ef = Read_Sampling_Message_RGF k p}"
                then have "\<exists>p. ef = Read_Sampling_Message_RGF k p" by auto
                then obtain p where "ef = Read_Sampling_Message_RGF k p" by auto
                then show ?thesis 
                  by (simp add: E\<^sub>e_def Read_Sampling_Message_RGF_def Read_Sampling_sat_SCE)
              qed
          qed
      qed
  }
  then show ?thesis by auto
qed

theorem uwc_oc: "observed_consistent"
  apply(simp add:observed_consistent_def)
  by(simp add:state_equiv_def)


theorem uwce_LRE: "locally_respect_events_guar"
  apply (simp add: locally_respect_events_guar_def all_evts_def, clarify)
  using all_evts_def[of ARINCXKernel_Spec] uwce_LRE_help 
  using noninterf1_def noninterf_def by blast
                                               

theorem uwce_SCE: "step_consistent_events"
  apply (simp add: step_consistent_events_def)
  using all_evts_def[of ARINCXKernel_Spec] uwce_SCE_help by auto


theorem "noninfluence0"
  using uwc_oc uwce_LRE uwce_SCE UnwindingTheoremE_noninfluence0_guar by simp

theorem "nonleakage"
  using UnwindingTheorem_nonleakage rg_lr_guar_imp_lr rg_sc_imp_sc uwc_oc uwce_LRE uwce_SCE by blast


end