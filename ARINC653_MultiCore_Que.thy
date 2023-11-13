theory ARINC653_MultiCore_Que
  imports Ann_PiCore_Syntax Ann_PiCore_RG_IFS
begin

subsection \<open>functional specification\<close>

type_synonym max_buffer_size = nat
type_synonym buffer_size = nat

typedecl Part
typedecl Sched
typedecl Message 
typedecl Port
typedecl Core

typedecl QChannel

record Config = c2s :: "Core \<Rightarrow> Sched"
                p2s :: "Part \<Rightarrow> Sched"
                p2p :: "Port \<Rightarrow> Part"
                chsrc :: "QChannel \<Rightarrow> Port"
                chdest :: "QChannel \<Rightarrow> Port"  
                chmax :: "QChannel \<Rightarrow> nat"
  
axiomatization conf::Config 
  where bij_c2s: "bij (c2s conf)" 
(*
    and surj_p2c: "surj (p2s conf)" 
    and portsrc_disj: "\<forall>c1 c2. c1 \<noteq> c2 \<longrightarrow> (chsrc conf) c1 \<noteq> (chsrc conf) c2" 
    and portdest_disj: "\<forall>c1 c2. c1 \<noteq> c2 \<longrightarrow> (chdest conf) c1 \<noteq> (chdest conf) c2" 
*)

lemma inj_surj_c2s: "inj (c2s conf) \<and> surj (c2s conf)"
  using bij_c2s by (simp add: bij_def) 

definition is_src_qport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_src_qport sc p \<equiv> (p\<in>range (chsrc sc))"

definition is_dest_qport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_dest_qport sc p \<equiv> (p\<in>range (chdest sc))"

definition port_of_part :: "Config \<Rightarrow> Port \<Rightarrow> Part \<Rightarrow> bool"
  where "port_of_part sc po pa \<equiv> ((p2p sc) po = pa)"

definition ch_srcqport :: "Config \<Rightarrow> Port \<Rightarrow> QChannel"
  where "ch_srcqport sc p \<equiv> SOME c. (chsrc sc) c = p"

definition ch_destqport :: "Config \<Rightarrow> Port \<Rightarrow> QChannel"
  where "ch_destqport sc p \<equiv> SOME c. (chdest sc) c = p"

datatype PartMode = IDLE | READY | RUN

record State = cur :: "Sched \<Rightarrow> Part option"
               qbuf :: "QChannel \<Rightarrow> Message list"
               qbufsize :: "QChannel \<Rightarrow> nat"
               partst :: "Part \<Rightarrow> PartMode"

datatype EL = Core_InitE | ScheduleE | Send_Que_MessageE |  Recv_Que_MessageE

datatype parameter = Port Port | Message Message | Partition Part

type_synonym EventLabel = "EL \<times> (parameter list \<times> Core)" 

definition get_evt_label :: "EL \<Rightarrow> parameter list \<Rightarrow> Core \<Rightarrow> EventLabel" ("_ _ \<rhd> _" [0,0,0] 20)
  where "get_evt_label el ps k \<equiv> (el,(ps,k))"

definition get_evt_core :: "(EventLabel, Core, State) event \<Rightarrow> Core"
  where "get_evt_core ev =  snd (snd (the (label_e ev)))"

definition get_evt_el :: "(EventLabel, Core, State) event \<Rightarrow> EL"
  where "get_evt_el ev =  fst (the (label_e ev))"

definition Core_Init :: "Core \<Rightarrow> (EventLabel, Core, State) event" 
  where "Core_Init k \<equiv> 
    EVENT Core_InitE [] \<rhd> k 
    THEN 
      \<lbrace>\<forall>p. p2s conf p = c2s conf k \<longrightarrow> \<acute>partst p = IDLE\<rbrace>
      \<acute>partst := (\<lambda>p. if p2s conf p = c2s conf k \<and> \<acute>partst p = IDLE then READY else \<acute>partst p) 
    END"

definition System_Init :: "Config \<Rightarrow> (State \<times> (EventLabel, Core, State) x)"
  where "System_Init cfg \<equiv> (\<lparr>cur=(\<lambda>c. None ),
                            qbuf = (\<lambda>c. []),
                            qbufsize = (\<lambda>c. 0),
                            partst = (\<lambda>p. IDLE)\<rparr>, 
                            (\<lambda>k. Core_Init k))"

definition Schedule :: "Core \<Rightarrow> Part \<Rightarrow> (EventLabel, Core, State) event" 
  where "Schedule k p \<equiv> 
    EVENT ScheduleE [Partition p] \<rhd> k 
    WHERE
      p2s conf p = c2s conf k \<and> (\<acute>partst p \<noteq> IDLE) \<and> (\<acute>cur((c2s conf) k) = None 
          \<or> p2s conf (the (\<acute>cur((c2s conf) k))) = c2s conf k)
    THEN 
      \<lbrace>p2s conf p = c2s conf k \<and> (\<acute>partst p \<noteq> IDLE) \<and> (\<acute>cur((c2s conf) k) = None \<or> p2s conf (the (\<acute>cur((c2s conf) k))) = c2s conf k)\<rbrace> 
        IF (\<acute>cur((c2s conf) k) \<noteq> None) THEN 
        \<lbrace>p2s conf p = c2s conf k  \<and> p2s conf (the (\<acute>cur((c2s conf) k))) = c2s conf k\<rbrace> 
              ATOMIC
          \<lbrace>True\<rbrace> \<acute>partst := \<acute>partst(the (\<acute>cur ((c2s conf) k)) := READY);;
          \<lbrace>True\<rbrace> \<acute>cur := \<acute>cur((c2s conf) k := None)
               END
            FI;;
      
      (\<lbrace>p2s conf p = c2s conf k \<and> \<acute>cur(c2s conf k) = None \<rbrace>
         ATOMIC
        \<lbrace>True\<rbrace> \<acute>cur := \<acute>cur((c2s conf) k := Some p);;
        \<lbrace>True\<rbrace> \<acute>partst := \<acute>partst(p := RUN)
        END)

    END"


definition Send_Que_Message :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> (EventLabel, Core, State) event" 
  where "Send_Que_Message k p m \<equiv> 
    EVENT Send_Que_MessageE [Port p, Message m] \<rhd> k 
    WHERE
      is_src_qport conf p
      \<and> \<acute>cur ((c2s conf) k) \<noteq> None
      \<and> port_of_part conf p (the (\<acute>cur ((c2s conf) k)))
    THEN
     \<lbrace>is_src_qport conf p \<and> \<acute>cur ((c2s conf) k) \<noteq> None \<and> port_of_part conf p (the (\<acute>cur ((c2s conf) k)))\<rbrace> 
     ATOMIC
     \<lbrace>True\<rbrace> IF \<acute>qbufsize (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
     \<lbrace>True\<rbrace> \<acute>qbuf := \<acute>qbuf (ch_srcqport conf p := \<acute>qbuf (ch_srcqport conf p) @ [m]);;
     \<lbrace>True\<rbrace> \<acute>qbufsize := \<acute>qbufsize (ch_srcqport conf p := \<acute>qbufsize (ch_srcqport conf p) + 1)
            FI
      END
    END"


definition Recv_Que_Message :: "Core \<Rightarrow> Port \<Rightarrow> (EventLabel, Core, State) event" 
  where "Recv_Que_Message k p \<equiv> 
    EVENT Recv_Que_MessageE [Port p] \<rhd> k 
    WHERE
      is_dest_qport conf p 
      \<and> \<acute>cur ((c2s conf) k) \<noteq> None
      \<and> port_of_part conf p (the (\<acute>cur ((c2s conf) k)))
    THEN 
        \<lbrace>is_dest_qport conf p  \<and> \<acute>cur ((c2s conf) k) \<noteq> None \<and> port_of_part conf p (the (\<acute>cur ((c2s conf) k))) \<rbrace>
        AWAIT \<acute>qbufsize (ch_destqport conf p) > 0 THEN 
          \<lbrace>True\<rbrace> \<acute>qbuf := \<acute>qbuf (ch_destqport conf p := tl (\<acute>qbuf (ch_destqport conf p)));;
          \<lbrace>True\<rbrace> \<acute>qbufsize := \<acute>qbufsize (ch_destqport conf p := \<acute>qbufsize (ch_destqport conf p) - 1)
        END
    END"

subsection \<open>Rely-guarantee condition of events\<close>

abbreviation "core_init_pre k \<equiv> \<lbrace>\<forall>p. p2s conf p = c2s conf k \<longrightarrow> \<acute>partst p = IDLE\<rbrace>"
abbreviation "core_init_rely k \<equiv> \<lbrace>(\<forall>p. p2s conf p = c2s conf k \<longrightarrow> \<ordfeminine>partst p = \<ordmasculine>partst p)\<rbrace>"
abbreviation "core_init_guar k \<equiv> \<lbrace>\<ordfeminine>cur= \<ordmasculine>cur \<and> \<ordfeminine>qbuf= \<ordmasculine>qbuf \<and> \<ordfeminine>qbufsize= \<ordmasculine>qbufsize 
            \<and> (\<forall>p. p2s conf p = c2s conf k \<longrightarrow> \<ordmasculine>partst p = IDLE \<and> \<ordfeminine>partst p = READY)
            \<and> (\<forall>c p. c \<noteq> k \<and> p2s conf p = c2s conf c \<longrightarrow> \<ordfeminine>partst  p = \<ordmasculine>partst p)\<rbrace> \<union> Id"
abbreviation "core_init_post \<equiv> \<lbrace>True\<rbrace>"

definition Core_Init_RGCond :: " Core \<Rightarrow> (State) rgformula"
  where "Core_Init_RGCond  k \<equiv> RG[core_init_pre k, core_init_rely k, core_init_guar k, core_init_post]"

abbreviation "schedule_pre \<equiv> \<lbrace>True\<rbrace>"
abbreviation "schedule_rely k \<equiv> \<lbrace>\<ordfeminine>cur (c2s conf k) = \<ordmasculine>cur  (c2s conf k) \<and>
              (\<forall>p. p2s conf p = c2s conf k \<longrightarrow> \<ordfeminine>partst  p = \<ordmasculine>partst p)\<rbrace>"

abbreviation "schedule_guar k p \<equiv> 
  \<lbrace>(\<ordfeminine>cur = \<ordmasculine>cur(c2s conf k := Some p) \<and> \<ordfeminine>partst = \<ordmasculine>partst(the (\<ordfeminine>cur(c2s conf k)) := RUN) 
   \<and> p2s conf p = c2s conf k \<or> (\<ordfeminine>cur = \<ordmasculine>cur(c2s conf k := None) 
   \<and> \<ordfeminine>partst = \<ordmasculine>partst(the (\<ordmasculine>cur (c2s conf k)) := READY)))
   \<and> (\<forall>c. c \<noteq> k \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))
   \<and> (\<forall>p. p2s conf p \<noteq> c2s conf k \<longrightarrow> \<ordfeminine>partst  p = \<ordmasculine>partst p )
   \<and> \<ordfeminine>qbuf= \<ordmasculine>qbuf  \<and> \<ordfeminine>qbufsize= \<ordmasculine>qbufsize\<rbrace> \<union> Id"

abbreviation "schedule_post \<equiv> \<lbrace>True\<rbrace>"

definition Schedule_RGCond :: "Core \<Rightarrow> Part \<Rightarrow>(State) rgformula"
  where "Schedule_RGCond k p \<equiv> RG[schedule_pre, schedule_rely k, schedule_guar k p, schedule_post]"

abbreviation "snd_recv_pre \<equiv> \<lbrace>True\<rbrace>"
abbreviation "snd_recv_rely k \<equiv> \<lbrace>\<ordfeminine>cur (c2s conf k) = \<ordmasculine>cur  (c2s conf k)\<rbrace>"
abbreviation "snd_send_guar k p \<equiv> 
    \<lbrace>\<ordfeminine>cur = \<ordmasculine>cur \<and> \<ordfeminine>partst = \<ordmasculine>partst \<and> (\<ordmasculine>qbufsize (ch_srcqport conf p) = length (\<ordmasculine>qbuf (ch_srcqport conf p))
      \<longrightarrow> \<ordfeminine>qbufsize (ch_srcqport conf p) = length (\<ordfeminine>qbuf (ch_srcqport conf p))) \<and>
    ((is_src_qport conf p \<and> \<ordmasculine>cur ((c2s conf) k) \<noteq> None \<and> port_of_part conf p (the (\<ordmasculine>cur ((c2s conf) k)))) \<longrightarrow>
    (\<forall>c. c \<noteq> ch_srcqport conf p \<longrightarrow> \<ordfeminine>qbuf c = \<ordmasculine>qbuf c \<and> \<ordfeminine>qbufsize c = \<ordmasculine>qbufsize c)) \<and> 
    ((\<not>(is_src_qport conf p \<and> \<ordmasculine>cur ((c2s conf) k) \<noteq> None \<and> port_of_part conf p (the (\<ordmasculine>cur ((c2s conf) k)))))
    \<longrightarrow> (\<ordfeminine>qbuf  = \<ordmasculine>qbuf  \<and> \<ordfeminine>qbufsize  = \<ordmasculine>qbufsize))\<rbrace>"


abbreviation "snd_recv_guar k p \<equiv> 
    \<lbrace>\<ordfeminine>cur = \<ordmasculine>cur \<and> \<ordfeminine>partst = \<ordmasculine>partst \<and>  (\<ordmasculine>qbufsize (ch_destqport conf p) = length (\<ordmasculine>qbuf (ch_destqport conf p))
      \<longrightarrow> \<ordfeminine>qbufsize (ch_destqport conf p) = length (\<ordfeminine>qbuf (ch_destqport conf p))) \<and>
    ((is_dest_qport conf p \<and> \<ordmasculine>cur ((c2s conf) k) \<noteq> None \<and> port_of_part conf p (the (\<ordmasculine>cur ((c2s conf) k)))) \<longrightarrow>
    (\<forall>c. c \<noteq> ch_destqport conf p \<longrightarrow> \<ordfeminine>qbuf c = \<ordmasculine>qbuf c \<and> \<ordfeminine>qbufsize c = \<ordmasculine>qbufsize c)) \<and> 
    ((\<not>(is_dest_qport conf p \<and> \<ordmasculine>cur ((c2s conf) k) \<noteq> None \<and> port_of_part conf p (the (\<ordmasculine>cur ((c2s conf) k)))))
    \<longrightarrow> (\<ordfeminine>qbuf  = \<ordmasculine>qbuf  \<and> \<ordfeminine>qbufsize  = \<ordmasculine>qbufsize))\<rbrace>"

abbreviation "snd_recv_post \<equiv> \<lbrace>True\<rbrace>"

definition Send_Que_Message_RGCond :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> (State) rgformula"
  where "Send_Que_Message_RGCond k p m \<equiv> RG[snd_recv_pre, snd_recv_rely k, snd_send_guar k p, snd_recv_post]"

definition Recv_Que_Message_RGCond :: "Core \<Rightarrow> Port \<Rightarrow> (State) rgformula"
  where "Recv_Que_Message_RGCond k p \<equiv> RG[snd_recv_pre, snd_recv_rely k, snd_recv_guar k p, snd_recv_post]"

definition Core_Init_RGF :: "Core \<Rightarrow> (EventLabel, Core, State) rgformula_e"
  where "Core_Init_RGF k \<equiv> (Core_Init k, Core_Init_RGCond k)"

definition Schedule_RGF :: "Core \<Rightarrow> Part \<Rightarrow> (EventLabel, Core, State) rgformula_e"
  where "Schedule_RGF k p \<equiv> (Schedule k p, Schedule_RGCond k p)"

definition Send_Que_Message_RGF :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> (EventLabel, Core, State) rgformula_e"
  where "Send_Que_Message_RGF k p m \<equiv> (Send_Que_Message k p m, Send_Que_Message_RGCond k p m)"

definition Recv_Que_Message_RGF :: "Core \<Rightarrow> Port \<Rightarrow> (EventLabel, Core, State) rgformula_e"
  where "Recv_Que_Message_RGF k p  \<equiv> (Recv_Que_Message k p, Recv_Que_Message_RGCond k p)"

definition EvtSys1_on_Core_RGF :: "Core \<Rightarrow> (EventLabel, Core, State) rgformula_es"
  where "EvtSys1_on_Core_RGF k \<equiv> 
            (rgf_EvtSys (\<Union>p.{Schedule_RGF k p} \<union>
                          (\<Union>(p, m). {Send_Que_Message_RGF k p m}) \<union>
                          (\<Union>p.{Recv_Que_Message_RGF k p})),
               RG[\<lbrace>True\<rbrace>,\<lbrace>\<ordfeminine>cur (c2s conf k) = \<ordmasculine>cur  (c2s conf k) \<and> 
                  (\<forall>p. p2s conf p = c2s conf k \<longrightarrow> \<ordfeminine>partst  p = \<ordmasculine>partst p)\<rbrace>,
                  ((\<Union>p. schedule_guar k p) \<union> (\<Union>p. snd_send_guar k p) \<union> 
                  (\<Union>p. snd_recv_guar k p) \<union> Id), \<lbrace>True\<rbrace>])"

definition EvtSys_on_Core_RGF :: "Core \<Rightarrow> (EventLabel, Core, State) rgformula_es"
  where "EvtSys_on_Core_RGF k  \<equiv> 
          (rgf_EvtSeq (Core_Init_RGF k) (EvtSys1_on_Core_RGF k),
           RG[core_init_pre k,
              schedule_rely k,
              ((\<Union>p. schedule_guar k p) \<union> (\<Union>p. snd_send_guar k p) \<union> 
              (\<Union>p. snd_recv_guar k p) \<union> Id \<union> (core_init_guar k)), \<lbrace>True\<rbrace>])"

definition ARINCXKernel_Spec :: "(EventLabel, Core, State) rgformula_par"
  where "ARINCXKernel_Spec \<equiv> (\<lambda>k. EvtSys_on_Core_RGF k)"


axiomatization s0 where s0_init: "s0 \<equiv> fst (System_Init conf)"
axiomatization x0 where x0_init: "x0 \<equiv> snd (System_Init conf)"
axiomatization C0 where C0_init: "C0 = (paresys_spec ARINCXKernel_Spec, s0, x0)"

subsection \<open>Functional correctness by rely guarantee proof\<close>

definition Evt_sat_RG:: "(EventLabel, Core, State) event \<Rightarrow> (State) rgformula \<Rightarrow> bool" ("(_\<turnstile>_)" [60,60] 61)
  where "Evt_sat_RG e rg \<equiv> \<turnstile> e sat\<^sub>e [Pre\<^sub>f rg, Rely\<^sub>f rg, Guar\<^sub>f rg, Post\<^sub>f rg]"


lemma Core_Init_SatRG: "\<forall>k. (Core_Init k) \<turnstile> Core_Init_RGCond k"
  apply(simp add:Evt_sat_RG_def)
  apply(rule allI)
  apply(simp add:Core_Init_def)
  apply(rule BasicEvt)
    apply(simp add:body_def Core_Init_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def  Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
    apply(rule Basic, simp, simp)
      apply auto
  using inj_surj_c2s injI surj_def apply (simp add: inj_eq)
     apply(simp add:stable_def)+
     apply(simp add:guard_def stable_def)
    apply (simp add: stable_def)
   apply(simp add:Core_Init_RGCond_def Pre\<^sub>f_def Rely\<^sub>f_def getrgformula_def stable_def)
  apply(simp add:Core_Init_RGCond_def Pre\<^sub>f_def Guar\<^sub>f_def  getrgformula_def stable_def)
  done


lemma Sched_SatRG_h1:
    " \<turnstile>\<lbrace>True \<rbrace>\<acute>partst := \<acute>partst(the (\<acute>cur (c2s conf k)) := READY);;
       \<lbrace>True \<rbrace> \<acute>cur := \<acute>cur (c2s conf k := None) sat\<^sub>p 
       [\<lbrace>p2s conf p = c2s conf k \<and> \<acute>partst p \<noteq> IDLE \<and> (\<acute>cur (c2s conf k) = None 
        \<or> p2s conf (the (\<acute>cur (c2s conf k))) = c2s conf k)\<rbrace> \<inter> \<lbrace>\<exists>y. \<acute>cur (c2s conf k) = Some y\<rbrace> \<inter> {V}, 
        {(s, t).s = t}, UNIV, 
        \<lbrace>(\<acute>cur = (cur V)(c2s conf k \<mapsto> p) \<and> \<acute>partst = (partst V)(the (\<acute>cur (c2s conf k)) := RUN) \<and> 
        p2s conf p = c2s conf k \<or> \<acute>cur = (cur V)(c2s conf k := None) \<and> \<acute>partst = (partst V)(the (cur V (c2s conf k)) := READY)) \<and>
        (\<forall>c. c \<noteq> k \<longrightarrow> \<acute>cur (c2s conf c) = cur V (c2s conf c)) \<and> (\<forall>p. p2s conf p \<noteq> c2s conf k 
        \<longrightarrow> \<acute>partst p = partst V p) \<and> \<acute>qbuf = qbuf V \<and> \<acute>qbufsize = qbufsize V \<or>\<acute>((=) V)\<rbrace> \<inter>
        \<lbrace>p2s conf p = c2s conf k \<and> \<acute>cur (c2s conf k) = None\<rbrace>]"
  apply(case_tac "p2s conf p = c2s conf k \<and> partst V p \<noteq> IDLE \<and> ((cur V) (c2s conf k) = None
        \<or> p2s conf (the ((cur V) (c2s conf k))) = c2s conf k) \<and> (\<exists>y. (cur V) (c2s conf k) = Some y)")
   apply simp
   apply(rule Seq[where mid="{s. s = V \<lparr> partst := (partst V) (the ((cur V) (c2s conf k)) := READY)\<rparr>
                              \<and> p2s conf p = c2s conf k}"])
    apply simp
    apply (rule Basic, simp)
       apply auto[1]
      apply(simp add:stable_def)+
   apply (rule Basic, simp, simp)
      apply(rule disjI1)
      apply (rule conjI)
  using inj_surj_c2s injI surj_def apply (simp add: inj_eq)
      apply (rule impI)
     apply(case_tac "cur V (c2s conf k) = None", simp)
  using inj_surj_c2s injI surj_def apply (simp add: inj_eq)
     apply simp
    apply (simp add: stable_def)
   apply (simp add: stable_def, clarify)
   apply (intro conjI)
       apply auto[1]
      apply blast
     apply blast
    apply blast
   apply blast
  apply(rule Seq[where mid="{}"])
   apply (rule Basic)
       apply (simp add: stable_def)+
  apply (rule Basic)
      apply (simp add: stable_def)+
  apply auto[1]
  done

lemma Sched_SatRG_h2: "\<turnstile> \<lbrace>True \<rbrace> \<acute>cur := \<acute>cur(c2s conf k \<mapsto> p) ;;
                         \<lbrace>True \<rbrace> \<acute>partst := \<acute>partst (p := RUN)
      sat\<^sub>p [\<lbrace>p2s conf p = c2s conf k \<and> \<acute>cur (c2s conf k) = None\<rbrace> \<inter> {V},  {(s, t). s = t}, UNIV, 
           \<lbrace>(\<acute>cur = (cur V)(c2s conf k \<mapsto> p) \<and> \<acute>partst = (partst V)(the (\<acute>cur (c2s conf k)) := RUN) 
           \<and> p2s conf p = c2s conf k \<or> \<acute>cur = (cur V)(c2s conf k := None) \<and> 
             \<acute>partst = (partst V)(the (cur V (c2s conf k)) := READY)) \<and> 
              (\<forall>c. c \<noteq> k \<longrightarrow> \<acute>cur (c2s conf c) = cur V (c2s conf c)) \<and> 
              (\<forall>p. p2s conf p \<noteq> c2s conf k \<longrightarrow> \<acute>partst p = partst V p) \<and> \<acute>qbuf = qbuf V 
              \<and> \<acute>qbufsize = qbufsize V \<or> \<acute>((=) V)\<rbrace>]"
  apply(case_tac "p2s conf p = c2s conf k \<and> (cur V) (c2s conf k) = None", simp)
   apply(rule Seq[where mid="{s. s = V \<lparr> cur := (cur V) (c2s conf k := Some p)\<rparr>}"])
    apply (rule Basic)
        apply (simp add: stable_def)+
   apply (rule Basic, simp, simp)
  using inj_surj_c2s injI surj_def apply (simp add: inj_eq)
     apply(simp add:stable_def)+
  apply(rule Seq[where mid="{}"])
   apply (rule Basic, simp)
      apply(simp add:stable_def)+
  apply (rule Basic, simp)
     apply (simp add: stable_def)+
  done

lemma Sched_SatRG: " (Schedule k p) \<turnstile> Schedule_RGCond k p"
  apply(simp add:Evt_sat_RG_def) 
  apply(simp add:Schedule_def)
  apply(rule BasicEvt) 
    apply(simp add:body_def Schedule_RGCond_def guard_def Pre\<^sub>f_def  Post\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
    apply(rule Seq[where mid="\<lbrace>p2s conf p = c2s conf k \<and> \<acute>cur(c2s conf k) = None\<rbrace>"])
     apply(rule Cond, simp)
        apply(simp add: stable_def)
       apply(rule Await)
          apply force
         apply(simp add: stable_def)+
  using Sched_SatRG_h1 apply auto[1]
      apply (rule Basic)
          apply auto[1]
         apply auto[1]
        apply (clarsimp)
       apply (simp add: stable_def)+
    apply (rule Await, simp)
      apply (simp add: stable_def)+
    apply (rule allI)
  using Sched_SatRG_h2 apply auto[1]
   apply(simp add: stable_def Schedule_RGCond_def Pre\<^sub>f_def  Post\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  apply(simp add: Schedule_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  done

lemma Send_Que_Message_SatRG_h1: "\<turnstile> \<lbrace>True \<rbrace> \<acute>qbuf := \<acute>qbuf(ch_srcqport conf p := \<acute>qbuf (ch_srcqport conf p) @ [m]) ;;
                                    \<lbrace>True \<rbrace> \<acute>qbufsize := \<acute>qbufsize (ch_srcqport conf p := Suc (\<acute>qbufsize (ch_srcqport conf p)))
                sat\<^sub>p [\<lbrace>is_src_qport conf p \<and> (\<exists>y. \<acute>cur (c2s conf k) = Some y) \<and> 
                      port_of_part conf p (the (\<acute>cur (c2s conf k)))\<rbrace> \<inter> {V} \<inter>
                      \<lbrace>\<acute>qbufsize (ch_srcqport conf p) < chmax conf (ch_srcqport conf p)\<rbrace>, 
                      {(s, t). s = t}, UNIV, \<lbrace>\<acute>cur = cur V \<and> \<acute>partst = partst V \<and> 
                      (qbufsize V (ch_srcqport conf p) = length (qbuf V (ch_srcqport conf p)) \<longrightarrow> 
                      \<acute>qbufsize (ch_srcqport conf p) = length (\<acute>qbuf (ch_srcqport conf p))) \<and>
                       (is_src_qport conf p \<and> (\<exists>y. cur V (c2s conf k) = Some y) \<and> 
                       port_of_part conf p (the (cur V (c2s conf k))) \<longrightarrow> (\<forall>c. c \<noteq> ch_srcqport conf p 
                       \<longrightarrow> \<acute>qbuf c = qbuf V c \<and> \<acute>qbufsize c = qbufsize V c)) \<and> ((is_src_qport conf p 
                      \<longrightarrow> cur V (c2s conf k) = None \<or> \<not> port_of_part conf p (the (cur V (c2s conf k)))) 
                      \<longrightarrow> \<acute>qbuf = qbuf V \<and> \<acute>qbufsize = qbufsize V)\<rbrace>]"
  apply(case_tac "is_src_qport conf p \<and> (\<exists>y. (cur V) ((c2s conf) k) = Some y) 
       \<and> port_of_part conf p (the ((cur V) ((c2s conf) k))) 
      \<and> (qbufsize V) (ch_srcqport conf p) < chmax conf (ch_srcqport conf p)")
   apply simp
   apply(rule Seq[where mid="{s. s = V\<lparr>qbuf := (qbuf V)(ch_srcqport conf p := (qbuf V) (ch_srcqport conf p) @ [m])\<rparr>}"])
    apply(rule Basic)
        apply auto[1]
       apply(simp add: stable_def)+
   apply(rule Basic, simp)
       apply auto[1]
      apply(simp add: stable_def)+
  apply(rule Seq[where mid="{}"])
   apply(rule Basic, simp)
      apply(simp add:stable_def)+
      apply fastforce
     apply simp
    apply (simp add: stable_def)+
  apply(rule Basic)
      apply(simp add:stable_def)+
  done

lemma Send_Que_Message_SatRG: 
  " Send_Que_Message k p m \<turnstile> Send_Que_Message_RGCond k p m"
  apply(simp add:Evt_sat_RG_def)
  apply(simp add:Send_Que_Message_def)
  apply(rule BasicEvt)
    apply(simp add:body_def Send_Que_Message_RGCond_def guard_def Pre\<^sub>f_def Post\<^sub>f_def Rely\<^sub>f_def 
         Guar\<^sub>f_def getrgformula_def)
    apply(rule Await)
       apply(simp add: stable_def)+
    apply(rule allI)
    apply (rule Cond, simp)
       apply (simp add: stable_def)
  using Send_Que_Message_SatRG_h1 apply auto[1]
     apply (rule Basic)
         apply blast
        apply force
       apply simp
      apply (simp add: stable_def)+
   apply(simp add: stable_def Send_Que_Message_RGCond_def Pre\<^sub>f_def Rely\<^sub>f_def getrgformula_def)
  apply(simp add: Send_Que_Message_RGCond_def Guar\<^sub>f_def getrgformula_def)
  done

lemma Recv_Que_Message_SatRG_h1: "\<turnstile> \<lbrace>True\<rbrace> \<acute>qbuf := \<acute>qbuf(ch_destqport conf p := tl (\<acute>qbuf (ch_destqport conf p)));;
                         \<lbrace>True \<rbrace>\<acute>qbufsize := \<acute>qbufsize (ch_destqport conf p := \<acute>qbufsize (ch_destqport conf p) - Suc 0)
            sat\<^sub>p [\<lbrace>is_dest_qport conf p \<and> (\<exists>y. \<acute>cur (c2s conf k) = Some y) \<and> port_of_part conf p (the (\<acute>cur (c2s conf k)))\<rbrace> 
            \<inter> \<lbrace>0 < \<acute>qbufsize (ch_destqport conf p)\<rbrace> \<inter> {V}, {(s, t). s = t}, UNIV, 
            \<lbrace>\<acute>cur = cur V \<and> \<acute>partst = partst V \<and> (qbufsize V (ch_destqport conf p) = length (qbuf V (ch_destqport conf p)) 
            \<longrightarrow> \<acute>qbufsize (ch_destqport conf p) = length (\<acute>qbuf (ch_destqport conf p))) \<and>
            (is_dest_qport conf p \<and> (\<exists>y. cur V (c2s conf k) = Some y) \<and> port_of_part conf p (the (cur V (c2s conf k))) 
            \<longrightarrow> (\<forall>c. c \<noteq> ch_destqport conf p \<longrightarrow> \<acute>qbuf c = qbuf V c \<and> \<acute>qbufsize c = qbufsize V c)) \<and>
            ((is_dest_qport conf p \<longrightarrow> cur V (c2s conf k) = None \<or> \<not> port_of_part conf p (the (cur V (c2s conf k)))) 
            \<longrightarrow> \<acute>qbuf = qbuf V \<and> \<acute>qbufsize = qbufsize V)\<rbrace>]"
  apply(case_tac "is_dest_qport conf p \<and> (\<exists>y. (cur V) ((c2s conf) k) = Some y) 
                  \<and> port_of_part conf p (the ((cur V) ((c2s conf) k)))\<and> 0 < (qbufsize V) (ch_destqport conf p)")
   apply simp
   apply(rule Seq[where mid="{s. s = V\<lparr>qbuf := (qbuf V)(ch_destqport conf p := tl ((qbuf V) (ch_destqport conf p)))\<rparr>}"])
    apply(rule Basic)
        apply auto[1]
       apply auto[1]
      apply blast
     apply(simp add: stable_def)+
   apply(rule Basic, simp)
      apply auto[1]
     apply(simp add: stable_def)+
  apply(rule Seq[where mid="{}"])
   apply(rule Basic)
       apply(simp add:stable_def)+
  apply(rule Basic, simp)
     apply(simp add:stable_def)+
  done

lemma Recv_Que_Message_SatRG: " Recv_Que_Message k p \<turnstile> Recv_Que_Message_RGCond k p"
  apply(simp add:Evt_sat_RG_def)
  apply(simp add:Recv_Que_Message_def)
  apply(rule BasicEvt)
    apply(simp add:body_def Recv_Que_Message_RGCond_def guard_def Pre\<^sub>f_def Post\<^sub>f_def Rely\<^sub>f_def
          Guar\<^sub>f_def getrgformula_def)
    apply(rule Await)
       apply(simp add: stable_def)+
    apply(rule allI)
  using Recv_Que_Message_SatRG_h1 apply fastforce
  apply(simp add: stable_def Recv_Que_Message_RGCond_def Pre\<^sub>f_def Rely\<^sub>f_def getrgformula_def)
  apply(simp add: Recv_Que_Message_RGCond_def Guar\<^sub>f_def getrgformula_def)
  done

lemma EvtSys1_on_core_SatRG: 
  "\<forall>k. \<turnstile> fst (EvtSys1_on_Core_RGF k) sat\<^sub>s 
       [Pre\<^sub>f (snd (EvtSys1_on_Core_RGF k)), 
       Rely\<^sub>f (snd (EvtSys1_on_Core_RGF k)), 
       Guar\<^sub>f (snd (EvtSys1_on_Core_RGF k)), 
        Post\<^sub>f (snd (EvtSys1_on_Core_RGF k))]"
  apply (rule allI)
  apply(simp add:EvtSys1_on_Core_RGF_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def getrgformula_def)
  apply (rule EvtSys_h)
                    
  apply(clarify)
  apply(case_tac "(a,b)\<in> {(Schedule_RGF k x)}")
  using Sched_SatRG Schedule_RGF_def Evt_sat_RG_def E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def 
    Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def snd_conv fst_conv apply (metis singletonD)
  apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Send_Que_Message_RGF k p m})")
  apply(clarify)
  using Send_Que_Message_SatRG Send_Que_Message_RGF_def E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def 
    Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def snd_conv fst_conv Evt_sat_RG_def apply metis
  apply(case_tac "(a,b)\<in>(\<Union>p. {Recv_Que_Message_RGF k p})")
  apply(clarify)
  using Recv_Que_Message_SatRG Recv_Que_Message_RGF_def E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def 
    Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def snd_conv fst_conv Evt_sat_RG_def apply metis
  apply blast

  apply(clarify)
  apply(case_tac "(a,b)\<in> {(Schedule_RGF k x)}")
  apply(simp add:Schedule_RGF_def Schedule_RGCond_def Pre\<^sub>e_def getrgformula_def)
  apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Send_Que_Message_RGF k p m})")
  apply clarify
  apply(simp add:Send_Que_Message_RGF_def Send_Que_Message_RGCond_def Pre\<^sub>e_def getrgformula_def)
  apply(case_tac "(a,b)\<in>(\<Union>p. {Recv_Que_Message_RGF k p})")
  apply(clarify)
  apply(simp add:Recv_Que_Message_RGF_def Recv_Que_Message_RGCond_def Pre\<^sub>e_def getrgformula_def)
  apply blast

  apply(clarify)
  apply(case_tac "(a,b)\<in> {(Schedule_RGF k x)}")
  apply(simp add:Schedule_RGF_def Schedule_RGCond_def Rely\<^sub>e_def getrgformula_def) 
  apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Send_Que_Message_RGF k p m})")
  apply clarify
  apply(simp add:Send_Que_Message_RGF_def Send_Que_Message_RGCond_def Rely\<^sub>e_def getrgformula_def)
  apply(case_tac "(a,b)\<in>(\<Union>p. {Recv_Que_Message_RGF k p})")
  apply(clarify)
  apply(simp add:Recv_Que_Message_RGF_def Recv_Que_Message_RGCond_def Rely\<^sub>e_def getrgformula_def)
  apply blast

  apply(clarify)
  apply(case_tac "(a,b)\<in> {(Schedule_RGF k x)}")
  apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Guar\<^sub>e_def) 
  apply auto[1] 
  apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Send_Que_Message_RGF k p m})")
  apply(simp add:Send_Que_Message_RGF_def Send_Que_Message_RGCond_def getrgformula_def Guar\<^sub>e_def, clarify)
  apply auto[1]
  apply(case_tac "(a,b)\<in>(\<Union>p. {Recv_Que_Message_RGF k p})")
  apply(simp add:Recv_Que_Message_RGF_def Recv_Que_Message_RGCond_def getrgformula_def Guar\<^sub>e_def) 
  apply auto[1] 
  apply blast
  
  apply simp

  apply(clarify)
  apply(case_tac "(a,b)\<in> {(Schedule_RGF k xa)}")
  apply(case_tac "(aa,ba)\<in> {(Schedule_RGF k xb)}")
  apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Pre\<^sub>e_def)
  apply(case_tac "(aa,ba)\<in>(\<Union>(p, m). {Send_Que_Message_RGF k p m})")
  apply(simp add:Send_Que_Message_RGF_def Send_Que_Message_RGCond_def getrgformula_def Pre\<^sub>e_def)  
  apply auto[1] 
  apply(case_tac "(aa,ba)\<in>(\<Union>p. {Recv_Que_Message_RGF k p})")
  apply(simp add:Recv_Que_Message_RGF_def Recv_Que_Message_RGCond_def getrgformula_def Pre\<^sub>e_def) 
  apply auto[1] 
  apply blast

  apply(case_tac "(a,b)\<in>(\<Union>(p, m). {Send_Que_Message_RGF k p m})")
  apply(case_tac "(aa,ba)\<in> {(Schedule_RGF k xb)}")
  apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Pre\<^sub>e_def)
  apply(case_tac "(aa,ba)\<in>(\<Union>(p, m). {Send_Que_Message_RGF k p m})")
  apply(simp add:Send_Que_Message_RGF_def Send_Que_Message_RGCond_def getrgformula_def Pre\<^sub>e_def) 
  apply auto[1] 
  apply(case_tac "(aa,ba)\<in>(\<Union>p. {Recv_Que_Message_RGF k p})")
  apply(simp add:Recv_Que_Message_RGF_def Recv_Que_Message_RGCond_def getrgformula_def Pre\<^sub>e_def) 
  apply auto[1] 
  apply blast
  apply(case_tac "(a,b)\<in>(\<Union>p. {Recv_Que_Message_RGF k p})")
  apply(case_tac "(aa,ba)\<in> {(Schedule_RGF k xb)}")
  apply(simp add:Schedule_RGF_def Schedule_RGCond_def getrgformula_def Pre\<^sub>e_def)
  apply(case_tac "(aa,ba)\<in>(\<Union>(p, m). {Send_Que_Message_RGF k p m})")
  apply(simp add:Send_Que_Message_RGF_def Send_Que_Message_RGCond_def getrgformula_def Pre\<^sub>e_def) 
  apply auto[1] 
  apply(case_tac "(aa,ba)\<in>(\<Union>p. {Recv_Que_Message_RGF k p})")
  apply(simp add:Recv_Que_Message_RGF_def Recv_Que_Message_RGCond_def getrgformula_def Pre\<^sub>e_def) 
  apply auto[1] 
  apply blast
  apply blast
  apply (simp add:stable_def)
  by simp



lemma EvtSys_on_core_SatRG: 
  "\<forall>k.  \<turnstile> fst (EvtSys_on_Core_RGF k) sat\<^sub>s 
          [Pre\<^sub>f (snd (EvtSys_on_Core_RGF k)), 
           Rely\<^sub>f (snd (EvtSys_on_Core_RGF k)), 
           Guar\<^sub>f (snd (EvtSys_on_Core_RGF k)), 
           Post\<^sub>f (snd (EvtSys_on_Core_RGF k))]"
  apply(rule allI)
  apply(simp add:EvtSys_on_Core_RGF_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def getrgformula_def)
  apply(rule EvtSeq_h)
          apply(simp add:E\<^sub>e_def Core_Init_RGF_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def)
          apply (metis Core_Init_SatRG Evt_sat_RG_def Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def) 
  using EvtSys1_on_core_SatRG apply fastforce
        apply(simp add:Core_Init_RGF_def Core_Init_RGCond_def Pre\<^sub>e_def getrgformula_def) 
       apply(simp add:EvtSys1_on_Core_RGF_def Post\<^sub>f_def getrgformula_def)
      apply(simp add:Core_Init_RGF_def Core_Init_RGCond_def Rely\<^sub>e_def getrgformula_def) 
      apply auto[1]
     apply(simp add:EvtSys1_on_Core_RGF_def Rely\<^sub>f_def getrgformula_def Core_Init_RGF_def)
    apply(simp add:Core_Init_RGF_def Core_Init_RGCond_def Guar\<^sub>e_def Guar\<^sub>f_def getrgformula_def EvtSys1_on_Core_RGF_def)
   apply(simp add:EvtSys1_on_Core_RGF_def Core_Init_RGCond_def Guar\<^sub>f_def getrgformula_def)
  by (simp add:EvtSys1_on_Core_RGF_def Core_Init_RGF_def Core_Init_RGCond_def Post\<^sub>e_def Pre\<^sub>f_def getrgformula_def)

lemma spec_sat_rg: " \<turnstile> ARINCXKernel_Spec SAT [{s0}, {}, UNIV, UNIV]"
  apply (rule ParallelESys)
       apply(simp add:ARINCXKernel_Spec_def Guar\<^sub>e\<^sub>s_def Guar\<^sub>f_def Post\<^sub>e\<^sub>s_def Post\<^sub>f_def Pre\<^sub>e\<^sub>s_def 
            Pre\<^sub>f_def Rely\<^sub>e\<^sub>s_def Rely\<^sub>f_def)
       apply (metis EvtSys_on_core_SatRG Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def)
      apply(simp add:ARINCXKernel_Spec_def EvtSys_on_Core_RGF_def Pre\<^sub>e\<^sub>s_def getrgformula_def 
            System_Init_def s0_init)
     apply simp
    apply clarsimp
  apply(simp add:ARINCXKernel_Spec_def EvtSys_on_Core_RGF_def Guar\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def getrgformula_def)  
    apply auto[1]
      apply (simp add: inj_eq inj_surj_c2s)
     apply (metis inj_eq inj_surj_c2s)
    apply metis
   apply simp+
  done


subsection \<open>Security Specification\<close>

datatype Domain = P Part | S Sched | F 


definition domevt :: "State  \<Rightarrow> (EventLabel, Core, State) event \<Rightarrow> Domain"
  where "domevt s e \<equiv> let c = get_evt_core e in (let el = get_evt_el e in  
                         (if (el = Send_Que_MessageE \<or> el = Recv_Que_MessageE) 
                              \<and> (cur s) (c2s conf c) \<noteq> None
                              then P (the ((cur s) (c2s conf c)))
                          else if (el = Core_InitE \<or> el = ScheduleE) then S (c2s conf c)
                          else F))" 

primrec part_on_core :: "Config \<Rightarrow> Domain \<Rightarrow> Domain \<Rightarrow> bool"
  where "part_on_core cfg (P d1) d2 = (case d2 of
                                        P d22 \<Rightarrow> False |
                                        S d22 \<Rightarrow> d22 = ((p2s cfg) d1) |
                                        F \<Rightarrow> False )" |
        "part_on_core cfg (S d1) d2 = False" |
        "part_on_core cfg F d2 = False"

definition ch_conn :: "Config \<Rightarrow> Part \<Rightarrow> Part \<Rightarrow> bool"
  where "ch_conn cfg p1 p2 \<equiv> (\<exists>ch. (p2p cfg) ((chsrc cfg) ch) = p1 \<and> (p2p cfg) ((chdest cfg) ch) = p2)"

primrec ch_conn2 :: "Config \<Rightarrow> Domain \<Rightarrow> Domain \<Rightarrow> bool"
  where "ch_conn2 cfg (P p1) d2 = (case d2 of
                                    (P p2) \<Rightarrow> ch_conn cfg p1 p2 |
                                    (S s2) \<Rightarrow> False |
                                      F  \<Rightarrow> False)" |                                     
        "ch_conn2 cfg (S p1) d2 = False" |
        "ch_conn2 cfg F d2 = False"

definition interf :: "Domain \<Rightarrow> Domain \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
  where "interf d1 d2 \<equiv> if d1 = d2 then True
                         else if part_on_core conf d2 d1 then True
                         else if ch_conn2 conf d1 d2 then True
                         else False"

definition noninterf1 :: "Domain \<Rightarrow> Domain \<Rightarrow> bool" ("(_ \<setminus>\<leadsto> _)" [70,71] 60)
  where "u \<setminus>\<leadsto> v \<equiv> \<not> (u \<leadsto> v)"

definition state_obs_sched :: "State \<Rightarrow> Sched \<Rightarrow> State"
  where "state_obs_sched s d \<equiv> s0\<lparr>cur:=(cur s0) (d := (cur s) d)\<rparr>"

definition obs_cap_part :: "State \<Rightarrow> Part  \<Rightarrow> (QChannel \<Rightarrow> nat)"
  where "obs_cap_part s p  \<equiv> \<lambda>c. if (p2p conf) ((chdest conf) c) = p then qbufsize s c else qbufsize s0 c"

lemma obs_cap_equiv : "\<lbrakk>\<forall>c. p2p conf (chdest conf c) = x1 \<longrightarrow> qbufsize s1 c = qbufsize s2 c\<rbrakk> 
                        \<Longrightarrow>  obs_cap_part s2 x1 = obs_cap_part s1 x1"
  apply (simp add: obs_cap_part_def)
  by force

lemma obs_cap_equiv1 : "qbufsize s1 = qbufsize s2 \<Longrightarrow> obs_cap_part s1 p = obs_cap_part s2 p"
  using obs_cap_equiv by force

definition state_obs_part :: "State \<Rightarrow> Part \<Rightarrow> State"
  where "state_obs_part s p \<equiv> s0\<lparr>partst := (partst s0) (p := (partst s) p), 
                                 qbufsize := obs_cap_part s p\<rparr>"

primrec state_obs :: "State \<Rightarrow> Domain \<Rightarrow> State"
  where "state_obs s (P p) = state_obs_part s p" |
        "state_obs s (S p) = state_obs_sched s p"|
        "state_obs s F = s0"

definition state_equiv :: "State \<Rightarrow> Domain \<Rightarrow> State \<Rightarrow> bool" ("(_ \<sim>_\<sim> _)" [70,69,70] 60)
  where "state_equiv s d t \<equiv> state_obs s d = state_obs t d"

lemma state_equiv_transitive: "\<lbrakk>s \<sim> d \<sim> t; t \<sim> d \<sim> r\<rbrakk> \<Longrightarrow> s \<sim> d \<sim> r"
  by (simp add:state_equiv_def)
    
lemma state_equiv_symmetric : "s \<sim> d \<sim> t \<Longrightarrow> t \<sim> d \<sim> s"
  by (simp add:state_equiv_def)

lemma state_equiv_reflexive : "s \<sim> d \<sim> s"
  by (simp add:state_equiv_def)

definition exec_step :: "(EventLabel, Core, State, Domain) action \<Rightarrow> 
 ((EventLabel, Core, State) pesconf \<times> (EventLabel, Core, State) pesconf) set"
  where "exec_step a \<equiv> {(P,Q). (P -pes-(actk a)\<rightarrow> Q) \<and>((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                         \<and> domevt (gets P) e = domain a) \<or> (\<exists>c k. actk a = ((Cmd c)\<sharp>k) 
                         \<and> eventof a = (getx P) k \<and> domevt (gets P) (eventof a) = domain a))}"


subsection \<open>Instantiate the Security Model\<close>

lemma neq_coreinit: "k1\<noteq>k2 \<Longrightarrow> Core_Init k1\<noteq>Core_Init k2" 
  by (simp add:Core_Init_def get_evt_label_def)

lemma neq_schedule: " k1 \<noteq> k2 \<or> p1 \<noteq> p2 \<Longrightarrow> Schedule k1 p1 \<noteq>Schedule k2 p2" 
  by (simp add:Schedule_def get_evt_label_def)

lemma neq_wrt_samp: " k1\<noteq>k2 \<or> p1\<noteq>p2 \<or> m1\<noteq>m2 \<Longrightarrow> Send_Que_Message k1 p1 m1 \<noteq> Send_Que_Message k2 p2 m2" 
  by (clarsimp, simp add: Send_Que_Message_def get_evt_label_def)

lemma neq_rd_samp: "k1\<noteq>k2 \<or> p1\<noteq>p2 \<Longrightarrow> Recv_Que_Message k1 p1 \<noteq> Recv_Que_Message k2 p2" 
  by (clarsimp, simp add: Recv_Que_Message_def get_evt_label_def)

lemma neq_coreinit_sched: "Core_Init k1 \<noteq> Schedule k2 p"
  by (simp add:Schedule_def Core_Init_def get_evt_label_def)

lemma neq_coreinit_wrtsamp: "Core_Init k1 \<noteq> Send_Que_Message k2 p m"
  by (simp add:Send_Que_Message_def Core_Init_def get_evt_label_def)

lemma neq_coreinit_rdsamp: "Core_Init k1 \<noteq> Recv_Que_Message k2 p"
  by (simp add:Recv_Que_Message_def Core_Init_def get_evt_label_def)

lemma neq_sched_wrtsamp: "Schedule k1 p1 \<noteq> Send_Que_Message k2 p2 m"
  by (simp add:Send_Que_Message_def Schedule_def get_evt_label_def)

lemma neq_sched_rdsamp: "Schedule k1 p1 \<noteq> Recv_Que_Message k2 p2"
  by (simp add:Recv_Que_Message_def Schedule_def get_evt_label_def)

lemma neq_wrtsamp_rdsamp: "Send_Que_Message k1 p1 m \<noteq> Recv_Que_Message k2 p2"
  by (simp add:Recv_Que_Message_def Send_Que_Message_def get_evt_label_def)

definition evtrgfset :: "((EventLabel, Core, State) event \<times> (State rgformula)) set"
  where "evtrgfset \<equiv> (\<Union>k.{(Core_Init k, Core_Init_RGCond k)})
                   \<union> (\<Union>(k, p).{(Schedule k p, Schedule_RGCond k p)})
                   \<union> (\<Union>(k, p, m).{(Send_Que_Message k p m, Send_Que_Message_RGCond k p m)})
                   \<union> (\<Union>(k, p).{(Recv_Que_Message k p, Recv_Que_Message_RGCond k p)})"

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
                                                  (\<Union>p. {Schedule_RGF k p} \<union>
                                                  (\<Union>(p, m). {Send_Que_Message_RGF k p m}) \<union>
                                                  (\<Union>p.{Recv_Que_Message_RGF k p})))"
      by (simp add:Core_Init_RGF_def EvtSys1_on_Core_RGF_def)
    then have "all_evts ARINCXKernel_Spec = (\<Union>k. {(Core_Init k, Core_Init_RGCond k)} \<union>
                                                  (\<Union>p. {(Schedule k p, Schedule_RGCond k p)} \<union>
                                                  (\<Union>(p, m). {(Send_Que_Message k p m, Send_Que_Message_RGCond k p m)}) \<union>
                                                  (\<Union>p.{(Recv_Que_Message k p, Recv_Que_Message_RGCond k p)})))"
      by (simp add: Core_Init_RGF_def Schedule_RGF_def Send_Que_Message_RGF_def Recv_Que_Message_RGF_def)
    moreover
    have "(\<Union>k. {(Core_Init k, Core_Init_RGCond k)} \<union>
          (\<Union>p. {(Schedule k p, Schedule_RGCond k p)} \<union>
          (\<Union>(p, m). {(Send_Que_Message k p m, Send_Que_Message_RGCond k p m)}) \<union>
          (\<Union>p.{(Recv_Que_Message k p, Recv_Que_Message_RGCond k p)}))) = 
          (\<Union>k. {(Core_Init k, Core_Init_RGCond k)}) \<union>
          (\<Union>k. (\<Union>p.{(Schedule k p, Schedule_RGCond k p)})) \<union>
          (\<Union>k. (\<Union>(p, m). {(Send_Que_Message k p m, Send_Que_Message_RGCond k p m)})) \<union>
          (\<Union>k. (\<Union>p.{(Recv_Que_Message k p, Recv_Que_Message_RGCond k p)}))"
      by auto
    moreover
    have "(\<Union>k. (\<Union>p.{(Schedule k p, Schedule_RGCond k p)}))
          = (\<Union>(k,p).{(Schedule k p, Schedule_RGCond k p)})" by blast
    moreover
    have "(\<Union>k. (\<Union>(p, m). {(Send_Que_Message k p m, Send_Que_Message_RGCond k p m)}))
          = (\<Union>(k, p, m). {(Send_Que_Message k p m, Send_Que_Message_RGCond k p m)})" by blast
    moreover
    have "(\<Union>k. (\<Union>p.{(Recv_Que_Message k p, Recv_Que_Message_RGCond k p)}))
          = (\<Union>(k,p).{(Recv_Que_Message k p, Recv_Que_Message_RGCond k p)})" by blast
    ultimately show ?thesis using evtrgfset_def by presburger
  qed

definition evtrgffun :: "(EventLabel, Core, State) event \<Rightarrow> (State rgformula) option"
  where "evtrgffun \<equiv> (\<lambda>e. Some (SOME rg. (e, rg)\<in>evtrgfset))"

lemma evtrgffun_exist: "\<forall>e\<in>Domain evtrgfset. \<exists>ef\<in>evtrgfset. E\<^sub>e ef = e \<and> evtrgffun e = Some (snd ef)"
  by (metis Domain_iff E\<^sub>e_def evtrgffun_def fst_conv snd_conv someI_ex)

lemma diff_e_in_evtrgfset: "\<forall>ef1 ef2. ef1\<in>evtrgfset \<and> ef2\<in>evtrgfset \<and> ef1\<noteq>ef2 \<longrightarrow> E\<^sub>e ef1 \<noteq> E\<^sub>e ef2"
  apply(rule allI)+
  apply(case_tac "ef1\<in>(\<Union>k.{(Core_Init k, Core_Init_RGCond k)})")
   apply(case_tac "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond k)})")
    apply (metis (no_types, lifting) E\<^sub>e_def UN_E neq_coreinit prod.sel(1) singletonD)
   apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Schedule k p, Schedule_RGCond k p)})")
    apply(clarify) using neq_coreinit_sched apply (simp add:E\<^sub>e_def)
   apply(case_tac "ef2 \<in> (\<Union>(k, p, m).{(Send_Que_Message k p m, Send_Que_Message_RGCond k p m)})")
    apply(clarify) using neq_coreinit_wrtsamp apply (simp add:E\<^sub>e_def)
   apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Recv_Que_Message k p, Recv_Que_Message_RGCond k p)})")
    apply(clarify) using neq_coreinit_rdsamp apply (simp add:E\<^sub>e_def)
  using evtrgfset_def apply blast
  apply(case_tac "ef1 \<in> (\<Union>(k, p).{(Schedule k p, Schedule_RGCond k p)})")
   apply(case_tac "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond k)})")
    apply(clarify) using neq_coreinit_sched apply (metis E\<^sub>e_def fst_conv)
  apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Schedule k p, Schedule_RGCond k p)})")
  apply(clarify) using neq_schedule apply (metis E\<^sub>e_def fst_conv)
  apply(case_tac "ef2 \<in> (\<Union>(k, p, m).{(Send_Que_Message k p m, Send_Que_Message_RGCond k p m)})")
  apply(clarify) using neq_sched_wrtsamp apply (simp add: E\<^sub>e_def)
  apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Recv_Que_Message k p, Recv_Que_Message_RGCond k p)})")
  apply(clarify) using neq_sched_rdsamp apply (simp add: E\<^sub>e_def)
   apply(simp add: evtrgfset_def)
  apply(case_tac "ef1 \<in> (\<Union>(k, p, m).{(Send_Que_Message k p m, Send_Que_Message_RGCond k p m)})")
   apply(case_tac "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond k)})")
    apply(clarify) using neq_coreinit_wrtsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
   apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Schedule k p, Schedule_RGCond k p)})")
    apply(clarify) using neq_sched_wrtsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
   apply(case_tac "ef2 \<in> (\<Union>(k, p, m).{(Send_Que_Message k p m, Send_Que_Message_RGCond k p m)})")
    apply(clarify) using neq_wrt_samp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
   apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Recv_Que_Message k p, Recv_Que_Message_RGCond k p)})")
    apply(clarify) using neq_wrtsamp_rdsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
   apply(simp add: evtrgfset_def)
  apply(case_tac "ef1 \<in> (\<Union>(k, p).{(Recv_Que_Message k p, Recv_Que_Message_RGCond k p)})")
   apply(case_tac "ef2 \<in> (\<Union>k. {(Core_Init k, Core_Init_RGCond k)})")
    apply(clarify) using neq_coreinit_rdsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
   apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Schedule k p, Schedule_RGCond k p)})")
    apply(clarify) using neq_sched_rdsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
   apply(case_tac "ef2 \<in> (\<Union>(k, p, m).{(Send_Que_Message k p m, Send_Que_Message_RGCond k p m)})")
  apply(clarify) using neq_wrtsamp_rdsamp apply (metis (no_types, opaque_lifting) E\<^sub>e_def prod.sel(1))
  apply(case_tac "ef2 \<in> (\<Union>(k, p).{(Recv_Que_Message k p, Recv_Que_Message_RGCond k p)})")
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
          using Core_Init_RGF_def Core_Init_def by (simp add: E\<^sub>e_def)
      next
        assume a1: "ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGF k))"
        then have "ef\<in>{ef. \<exists>p. ef = Schedule_RGF k p} \<union>
                      {ef. \<exists>p m. ef = Send_Que_Message_RGF k p m} \<union>
                      {ef. \<exists>p. ef = Recv_Que_Message_RGF k p}" 
          using all_evts_es_esys EvtSys1_on_Core_RGF_def by auto
        then have "ef\<in>{ef. \<exists>p. ef = Schedule_RGF k p} 
                  \<or> ef\<in>{ef. \<exists>p m. ef = Send_Que_Message_RGF k p m} 
                  \<or> ef\<in>{ef. \<exists>p. ef = Recv_Que_Message_RGF k p}" by auto
        then show ?thesis
          proof
            assume "ef\<in>{ef. \<exists>p. ef = Schedule_RGF k p}"
            then have  "\<exists>p. ef = Schedule_RGF k p" by auto
            then obtain p where "ef = Schedule_RGF k p" by auto
            then show ?thesis by (simp add: E\<^sub>e_def Schedule_RGF_def Schedule_def)
          next
            assume "ef\<in>{ef. \<exists>p m. ef = Send_Que_Message_RGF k p m}
                    \<or> ef\<in>{ef. \<exists>p. ef = Recv_Que_Message_RGF k p}"
            then show ?thesis 
              proof
                assume "ef\<in>{ef. \<exists>p m. ef = Send_Que_Message_RGF k p m}"
                then have "\<exists>p m. ef = Send_Que_Message_RGF k p m" by auto
                then obtain p and m where "ef = Send_Que_Message_RGF k p m" by auto
                then show ?thesis by (simp add: E\<^sub>e_def Send_Que_Message_RGF_def Send_Que_Message_def)
              next
                assume "ef\<in>{ef. \<exists>p. ef = Recv_Que_Message_RGF k p}"
                then have "\<exists>p. ef = Recv_Que_Message_RGF k p" by auto
                then obtain p where "ef = Recv_Que_Message_RGF k p" by auto
                then show ?thesis by (simp add: E\<^sub>e_def Recv_Que_Message_RGF_def Recv_Que_Message_def) 
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

subsection \<open>Proof of Events satisfy the UCs \<close>

lemma s0_update_help: "\<lbrakk>partst1 = partst2; qbufsize1 = qbufsize2 \<rbrakk> \<Longrightarrow> 
                      s0\<lparr> partst := partst1, qbufsize := qbufsize1 \<rparr> = s0\<lparr> partst := partst2, qbufsize := qbufsize2\<rparr>"
  by blast

lemma Core_Init_sat_LRE: 
  "\<forall>u s1 s2 x. (s1,s2) \<in> Guar\<^sub>f (Core_Init_RGCond x)
                \<longrightarrow> ((domevt s1 (Core_Init x)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
  apply (simp add: Core_Init_RGCond_def Guar\<^sub>f_def getrgformula_def, clarsimp)
  apply (simp add: domevt_def get_evt_core_def Core_Init_def label_def get_evt_el_def get_evt_label_def)
  apply (case_tac u, clarify)
    apply (case_tac "p2s conf x1 = c2s conf x")
     apply (simp add: interf_def noninterf1_def)
    apply (simp add: state_equiv_def state_obs_part_def, clarify)
    apply (rule s0_update_help)
     apply (metis bij_c2s bij_pointE)
  using obs_cap_equiv apply presburger
   apply (simp add: vpeq_reflexive state_equiv_def state_obs_sched_def)
  by (simp add: state_equiv_def)

lemma Schedule_sat_LRE: 
  "\<forall>u s1 s2 x p. (s1,s2) \<in> Guar\<^sub>f (Schedule_RGCond x p) 
                \<longrightarrow> ((domevt s1 (Schedule x p)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
  apply (simp add: Schedule_RGCond_def Guar\<^sub>f_def getrgformula_def vpeq_reflexive, clarsimp)
  apply (simp add: domevt_def get_evt_core_def Schedule_def label_def get_evt_el_def get_evt_label_def)
  apply (case_tac u)
    apply (simp add: state_equiv_def state_obs_part_def, clarsimp)
    apply (rule s0_update_help)
     apply (case_tac "p2s conf x1 = c2s conf x")
      apply (simp add: interf_def noninterf1_def)
     apply presburger
  using obs_cap_part_def apply presburger
   apply (simp add: state_equiv_def state_obs_sched_def)
   apply (metis fun_upd_other interf_def noninterf1_def)
  using state_equiv_def by auto[1]


lemma ch_chonn_help1 : "\<lbrakk>port_of_part conf p y; c = ch_srcqport conf p; is_src_qport conf p; y \<noteq> p2p conf (chdest conf c)\<rbrakk> 
   \<Longrightarrow> ch_conn conf y (p2p conf (chdest conf c))"
  apply (simp add: ch_conn_def, rule_tac x = c in exI)
  apply (simp add: port_of_part_def is_src_qport_def image_def ch_srcqport_def)
  by (metis (mono_tags, lifting) someI2)

lemma ch_chonn_help2 : "\<lbrakk>port_of_part conf p y; is_src_qport conf p; y \<noteq> p2p conf (chdest conf c); P y \<setminus>\<leadsto> P (p2p conf (chdest conf c))\<rbrakk>
          \<Longrightarrow> c \<noteq> ch_srcqport conf p"
  using ch_chonn_help1 interf_def noninterf1_def by fastforce

lemma Send_Que_sat_LRE:
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f (Send_Que_Message_RGCond x p m) 
                \<longrightarrow> ((domevt s1 (Send_Que_Message x p m)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
  apply (simp add: Send_Que_Message_RGCond_def Guar\<^sub>f_def getrgformula_def, clarsimp)
  apply (simp add: domevt_def get_evt_core_def Send_Que_Message_def label_def get_evt_el_def get_evt_label_def)
  apply (case_tac "(cur s1) (c2s conf x) = None")
  apply (metis State.surjective old.unit.exhaust vpeq_reflexive)
  apply (case_tac u, clarsimp)
    apply (case_tac "is_src_qport conf p \<and> port_of_part conf p y", simp)
     apply (metis ch_chonn_help2 interf_def noninterf1_def obs_cap_equiv state_equiv_def state_obs.simps(1) state_obs_part_def)
    apply (simp add: state_equiv_def state_obs_def)
    apply (metis State.surjective old.unit.exhaust)
   apply (simp add: state_equiv_def state_obs_sched_def)
  using state_equiv_def state_obs.simps(3) by presburger

lemma Recv_Que_sat_LRE:
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f (Recv_Que_Message_RGCond x p) 
                \<longrightarrow> ((domevt s1 (Recv_Que_Message x p)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
  apply (simp add: Recv_Que_Message_RGCond_def Guar\<^sub>f_def getrgformula_def, clarsimp)
  apply (simp add: domevt_def get_evt_core_def Recv_Que_Message_def label_def get_evt_el_def get_evt_label_def)
  apply (case_tac "(cur s1) (c2s conf x) = None")
   apply (metis State.surjective old.unit.exhaust vpeq_reflexive)
  apply (case_tac u)
    apply (case_tac "x1 = the ((cur s1) (c2s conf x))")
  using interf_def noninterf1_def apply force
    apply (simp add: state_equiv_def  state_obs_part_def)
    apply (rule s0_update_help)
     apply blast
    apply (rule obs_cap_equiv, clarsimp)
    apply (case_tac "is_dest_qport conf p \<and> port_of_part conf p y", simp)
     apply (drule_tac a = c in all_impD)
      apply (simp add: ch_destqport_def is_dest_qport_def port_of_part_def image_def)
      apply (metis (mono_tags, lifting)  someI)
     apply blast
    apply presburger
   apply (simp add: state_equiv_def state_obs_sched_def)
  using state_equiv_def state_obs.simps(3) by presburger


lemma uwce_LRE_help: "\<forall>x. ef \<in> all_evts_es (fst (ARINCXKernel_Spec x)) \<and> (s1,s2) \<in> Guar\<^sub>e ef \<longrightarrow> 
                                    ((domevt s1 (E\<^sub>e ef)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
  proof -
  {
    fix x
    assume p0: "ef\<in>all_evts_es (fst (ARINCXKernel_Spec x))" 
    then have "ef\<in>all_evts_es (fst (EvtSys_on_Core_RGF x))" by (simp add:ARINCXKernel_Spec_def)
    then have "ef\<in>insert (Core_Init_RGF x) (all_evts_es (fst (EvtSys1_on_Core_RGF x)))" 
      by (simp add:EvtSys_on_Core_RGF_def)
    then have "ef = (Core_Init_RGF x) \<or> ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGF x))" by auto
    then have "(s1,s2) \<in> Guar\<^sub>e ef \<longrightarrow> ((domevt s1 (E\<^sub>e ef)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
      proof
        assume a0: "ef = Core_Init_RGF x"
        then show ?thesis
          by (simp add: Core_Init_RGF_def Core_Init_sat_LRE E\<^sub>e_def Guar\<^sub>e_def Guar\<^sub>f_def)          
      next
        assume a1: "ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGF x))"
        then have "ef\<in>{ef. \<exists>p. ef = Schedule_RGF x p} \<union>
                      {ef. \<exists>p m. ef = Send_Que_Message_RGF x p m} \<union>
                      {ef. \<exists>p. ef = Recv_Que_Message_RGF x p}" 
          using all_evts_es_esys EvtSys1_on_Core_RGF_def by auto
        then have "ef\<in>{ef. \<exists>p. ef = Schedule_RGF x p} 
                  \<or> ef\<in>{ef. \<exists>p m. ef = Send_Que_Message_RGF x p m} 
                  \<or> ef\<in>{ef. \<exists>p. ef = Recv_Que_Message_RGF x p}" by auto
        then show ?thesis
          proof
            assume "ef\<in>{ef. \<exists>p. ef = Schedule_RGF x p}"
            then have "\<exists>p. ef = Schedule_RGF x p" by auto
            then obtain p where "ef = Schedule_RGF x p" by auto
            then show ?thesis 
              by (simp add: E\<^sub>e_def Guar\<^sub>e_def Guar\<^sub>f_def Schedule_RGF_def Schedule_sat_LRE) 
          next
            assume "ef\<in>{ef. \<exists>p m. ef = Send_Que_Message_RGF x p m}
                    \<or> ef\<in>{ef. \<exists>p. ef = Recv_Que_Message_RGF x p}"
            then show ?thesis 
              proof
                assume "ef\<in>{ef. \<exists>p m. ef = Send_Que_Message_RGF x p m}"
                then have "\<exists>p m. ef = Send_Que_Message_RGF x p m" by auto
                then obtain p and m where "ef = Send_Que_Message_RGF x p m" by auto
                then show ?thesis 
                  by (simp add: E\<^sub>e_def Guar\<^sub>e_def Guar\<^sub>f_def Send_Que_Message_RGF_def Send_Que_sat_LRE)
              next
                assume "ef\<in>{ef. \<exists>p. ef = Recv_Que_Message_RGF x p}"
                then have "\<exists>p. ef = Recv_Que_Message_RGF x p" by auto
                then obtain p where "ef = Recv_Que_Message_RGF x p" by auto
                then show ?thesis 
                  by (simp add: E\<^sub>e_def Guar\<^sub>e_def Guar\<^sub>f_def Recv_Que_Message_RGF_def Recv_Que_sat_LRE)
              qed
          qed
      qed
  }
  then show ?thesis by auto
qed


lemma Core_Init_sat_SCE: "\<exists>\<S>. Core_Init k \<in> \<S> \<and> step_consistent_e \<S> (Core_Init k)"
  apply (rule sc_e_Basic, simp add: Core_Init_def)
  apply (simp add: body_def sc_p.Basic)
  apply (rule sc_p.Basic, clarsimp)
  apply (case_tac u)
    apply (simp add: state_equiv_def state_obs_part_def)
    apply (simp add: System_Init_def s0_init)
    apply (metis (no_types, lifting) State.select_convs(3) State.surjective  State.update_convs(4) obs_cap_equiv1)
  using state_equiv_def state_obs_sched_def apply auto[1]
  using state_equiv_def state_obs.simps(3) apply presburger
  done

lemma Schedule_sat_SCE_h1: " 
        \<turnstile>\<lbrace>True \<rbrace>\<acute>partst := \<acute>partst(the (\<acute>cur (c2s conf k)) := READY);;
         \<lbrace>True \<rbrace> \<acute>cur := \<acute>cur (c2s conf k := None) sat\<^sub>p 
        [\<lbrace>p2s conf p = c2s conf k \<and> p2s conf (the (\<acute>cur (c2s conf k))) = c2s conf k\<rbrace> \<inter> {V}, 
         {(s, t). s = t}, UNIV, \<lbrace>\<acute>qbuf = qbuf V \<and> \<acute>qbufsize = qbufsize V \<and> \<acute>cur = (cur V)(c2s conf k := None) 
        \<and> \<acute>partst = (partst V)(the (cur V (c2s conf k)) := READY) \<and> (\<forall>p. p2s conf p \<noteq> c2s conf k \<longrightarrow> \<acute>partst p = partst V p)\<rbrace>]"
  apply (case_tac "p2s conf p = c2s conf k \<and> p2s conf (the ((cur V) (c2s conf k))) = c2s conf k ")
   apply simp
   apply(rule rghoare_p.Seq[where mid="{s. s = V \<lparr> partst := (partst V) (the ((cur V) (c2s conf k)) := READY)\<rparr>
         \<and> p2s conf p = c2s conf k}"])
    apply (rule rghoare_p.Basic, simp)
       apply force
      apply simp
     apply (simp add: stable_def)+
  apply (rule rghoare_p.Basic, simp, simp, simp)
    apply (simp add: stable_def, simp add: stable_def)
  apply(rule rghoare_p.Seq[where mid="{}"])
   apply (rule rghoare_p.Basic)
       apply (simp add: stable_def)+
  apply (rule rghoare_p.Basic, simp_all)
   apply (simp add: stable_def)+
  by force

lemma Schedule_sat_SCE_h2: "\<turnstile> \<lbrace>True \<rbrace> \<acute>cur := \<acute>cur(c2s conf k \<mapsto> p) ;;
                         \<lbrace>True \<rbrace> \<acute>partst := \<acute>partst (p := RUN)
      sat\<^sub>p [\<lbrace>p2s conf p = c2s conf k \<and> \<acute>cur (c2s conf k) = None\<rbrace> \<inter>  {V}, {(s, t). s = t}, UNIV, 
            \<lbrace>\<acute>qbuf = qbuf V \<and> \<acute>qbufsize = qbufsize V \<and> \<acute>cur = (cur V)(c2s conf k \<mapsto> p) \<and> 
             \<acute>partst = (partst V)(the (\<acute>cur (c2s conf k)) := RUN) \<and> (\<forall>p. p2s conf p \<noteq> c2s conf k 
             \<longrightarrow> \<acute>partst p = partst V p)\<rbrace>]"
  apply(case_tac "p2s conf p = c2s conf k \<and> (cur V) (c2s conf k) = None", simp)
   apply(rule rghoare_p.Seq[where mid="{s. s = V \<lparr> cur := (cur V) (c2s conf k := Some p)\<rparr>}"])
    apply (rule rghoare_p.Basic)
        apply (simp add: stable_def)+
   apply (rule rghoare_p.Basic, simp, simp)
  using inj_surj_c2s injI surj_def apply (simp add: inj_eq)
    apply(simp add:stable_def)+
  apply(rule rghoare_p.Seq[where mid="{}"])
   apply (rule rghoare_p.Basic, simp)
      apply(simp add:stable_def)+
  apply (rule rghoare_p.Basic, simp)
     apply (simp add: stable_def)+
  by force

lemma Schedule_sat_SCE: "\<exists>\<S>. Schedule k p \<in> \<S> \<and> step_consistent_e \<S> (Schedule k p)"
  apply (rule sc_e_Basic, simp add: Schedule_def)
  apply (simp add: body_def)
  apply (rule sc_p.Seq)
   apply (rule sc_p.Cond)
    apply (rule_tac pre = "\<lbrace>p2s conf p = c2s conf k \<and> p2s conf (the (\<acute>cur (c2s conf k))) = c2s conf k\<rbrace>" 
          and rely = Id and post = "\<lbrace>True\<rbrace>" and guar = "\<lbrace>\<ordfeminine>qbuf = \<ordmasculine>qbuf \<and> \<ordfeminine>qbufsize = \<ordmasculine>qbufsize \<and> 
          \<ordfeminine>cur = \<ordmasculine>cur(c2s conf k := None) \<and> \<ordfeminine>partst = \<ordmasculine>partst(the (\<ordmasculine>cur (c2s conf k)) := READY) \<and> 
          (\<forall>p. p2s conf p \<noteq> c2s conf k \<longrightarrow> \<ordfeminine>partst  p = \<ordmasculine>partst p )\<rbrace>" in sc_p.Await)
      apply (rule rghoare_p.Await, clarsimp)
        apply (simp add: stable_def)+
      apply (rule allI)
  using Schedule_sat_SCE_h1 apply auto[1]
     apply simp
    apply (simp add: domevt_def get_evt_core_def Schedule_def label_def get_evt_el_def get_evt_label_def, clarify)
     apply (case_tac u)
      apply (case_tac "p2s conf x1 = c2s conf k")
       apply (simp add: interf_def state_equiv_def state_obs_sched_def state_obs_part_def s0_init System_Init_def)
        apply (smt (verit, best) State.ext_inject State.update_convs(1) State.update_convs(3) State.update_convs(4) 
              fst_conv fun_upd_other fun_upd_same obs_cap_equiv1)
      apply (metis obs_cap_equiv1 state_equiv_def state_obs.simps(1) state_obs_part_def)
     apply (simp add: System_Init_def s0_init state_equiv_def state_obs_sched_def)
  using state_equiv_def state_obs.simps(3) apply presburger
   apply (rule sc_p.Basic, simp)
    apply (rule_tac pre = "\<lbrace>p2s conf p = c2s conf k \<and> \<acute>cur (c2s conf k) = None\<rbrace>" 
          and rely = Id and post = "\<lbrace>True\<rbrace>" and guar = "\<lbrace>\<ordfeminine>qbuf = \<ordmasculine>qbuf \<and> \<ordfeminine>qbufsize = \<ordmasculine>qbufsize \<and>  
          \<ordfeminine>cur = \<ordmasculine>cur(c2s conf k := Some p) \<and> \<ordfeminine>partst = \<ordmasculine>partst(the (\<ordfeminine>cur(c2s conf k)) := RUN) \<and> 
          (\<forall>p. p2s conf p \<noteq> c2s conf k \<longrightarrow> \<ordfeminine>partst  p = \<ordmasculine>partst p)\<rbrace>" in sc_p.Await)
    apply (rule rghoare_p.Await, simp)
      apply (simp add: stable_def)+
    apply (rule allI)
  using Schedule_sat_SCE_h2 apply auto[1]
    apply simp
   apply (simp add: domevt_def get_evt_core_def Schedule_def label_def get_evt_el_def get_evt_label_def, clarify)
   apply (case_tac u)
     apply (case_tac "p2s conf x1 = c2s conf k")
      apply (simp add: interf_def state_equiv_def state_obs_sched_def state_obs_part_def s0_init System_Init_def)
      apply (smt (verit, best) State.ext_inject State.update_convs(1) State.update_convs(3) State.update_convs(4) 
              fst_conv fun_upd_other fun_upd_same obs_cap_equiv1)
     apply (metis obs_cap_equiv1 state_equiv_def state_obs.simps(1) state_obs_part_def)
    apply (simp add: System_Init_def s0_init state_equiv_def state_obs_sched_def)
  using state_equiv_def state_obs.simps(3) by presburger

lemma Send_Que_sat_SCE_h1: "\<turnstile> \<lbrace>True \<rbrace> \<acute>qbuf := \<acute>qbuf(ch_srcqport conf p := \<acute>qbuf (ch_srcqport conf p) @ [m]) ;;
                              \<lbrace>True \<rbrace> \<acute>qbufsize := \<acute>qbufsize (ch_srcqport conf p := Suc (\<acute>qbufsize (ch_srcqport conf p)))
     sat\<^sub>p [\<lbrace>is_src_qport conf p \<and> (\<exists>y. \<acute>cur (c2s conf k) = Some y) \<and> port_of_part conf p (the (\<acute>cur (c2s conf k)))\<rbrace> 
            \<inter> {V} \<inter> \<lbrace>\<acute>qbufsize (ch_srcqport conf p) < chmax conf (ch_srcqport conf p)\<rbrace>, 
            {(s, t). s = t}, UNIV, \<lbrace>\<acute>cur = cur V \<and> \<acute>partst = partst V \<and> (is_src_qport conf p \<and> 
            (\<exists>y. cur V (c2s conf k) = Some y) \<and> port_of_part conf p (the (cur V (c2s conf k))) \<longrightarrow>
            (\<forall>c. c \<noteq> ch_srcqport conf p \<longrightarrow> \<acute>qbuf c = qbuf V c \<and> \<acute>qbufsize c = qbufsize V c) \<and>
            (qbufsize V (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) \<longrightarrow> 
            \<acute>qbufsize (ch_srcqport conf p) = Suc (qbufsize V (ch_srcqport conf p))) \<and>
            (chmax conf (ch_srcqport conf p) \<le> qbufsize V (ch_srcqport conf p) \<longrightarrow> 
            \<acute>qbuf = qbuf V \<and> \<acute>qbufsize = qbufsize V)) \<and> ((is_src_qport conf p \<longrightarrow> cur V (c2s conf k) = None 
            \<or> \<not> port_of_part conf p (the (cur V (c2s conf k)))) \<longrightarrow> \<acute>qbuf = qbuf V \<and> \<acute>qbufsize = qbufsize V)\<rbrace>]"
  apply(case_tac "is_src_qport conf p \<and> (\<exists>y. (cur V) ((c2s conf) k) = Some y) \<and> port_of_part conf p 
      (the ((cur V) ((c2s conf) k)))\<and> (qbufsize V) (ch_srcqport conf p) < chmax conf (ch_srcqport conf p)")
   apply simp
   apply(rule rghoare_p.Seq[where mid="{s. s = V\<lparr>qbuf := (qbuf V)(ch_srcqport conf p := (qbuf V) (ch_srcqport conf p) @ [m])\<rparr>}"])
    apply(rule rghoare_p.Basic)
        apply auto[1]
       apply(simp add: stable_def)+
   apply(rule rghoare_p.Basic, simp)
      apply auto[1]
     apply(simp add: stable_def)+
  apply(rule rghoare_p.Seq[where mid="{}"])
   apply(rule rghoare_p.Basic, simp)
      apply(simp add:stable_def)+
      apply fastforce
     apply simp
    apply (simp add: stable_def)+
  apply(rule rghoare_p.Basic)
      apply(simp add:stable_def)+
  done


lemma Send_Que_sat_SCE: "\<exists>\<S>. Send_Que_Message k p m \<in> \<S> \<and> step_consistent_e \<S> (Send_Que_Message k p m)"
  apply (rule sc_e_Basic, simp add: Send_Que_Message_def)
  apply (simp add: body_def)
  apply (rule_tac pre = "\<lbrace>is_src_qport conf p \<and> (\<exists>y. \<acute>cur (c2s conf k) = Some y) \<and> port_of_part conf p (the (\<acute>cur (c2s conf k)))\<rbrace>" 
          and rely = Id and post = "\<lbrace>True\<rbrace>" and guar = "\<lbrace>\<ordfeminine>cur = \<ordmasculine>cur \<and> \<ordfeminine>partst = \<ordmasculine>partst \<and> 
          ((is_src_qport conf p \<and> \<ordmasculine>cur ((c2s conf) k) \<noteq> None \<and> port_of_part conf p (the (\<ordmasculine>cur ((c2s conf) k)))) 
          \<longrightarrow> (\<forall>c. c \<noteq> ch_srcqport conf p \<longrightarrow> \<ordfeminine>qbuf c = \<ordmasculine>qbuf c \<and> \<ordfeminine>qbufsize c = \<ordmasculine>qbufsize c) \<and> 
          (\<ordmasculine>qbufsize (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) \<longrightarrow> 
          \<ordfeminine>qbufsize (ch_srcqport conf p) = \<ordmasculine>qbufsize (ch_srcqport conf p) + 1) \<and>
          (\<ordmasculine>qbufsize (ch_srcqport conf p) \<ge> chmax conf (ch_srcqport conf p) \<longrightarrow> 
          \<ordfeminine>qbuf = \<ordmasculine>qbuf \<and> \<ordfeminine>qbufsize  = \<ordmasculine>qbufsize)) \<and> ((\<not>(is_src_qport conf p \<and> 
          \<ordmasculine>cur ((c2s conf) k) \<noteq> None \<and> port_of_part conf p (the (\<ordmasculine>cur ((c2s conf) k)))))\<longrightarrow> 
          (\<ordfeminine>qbuf  = \<ordmasculine>qbuf  \<and> \<ordfeminine>qbufsize  = \<ordmasculine>qbufsize))\<rbrace>" in sc_p.Await)
    apply (rule rghoare_p.Await, simp)
      apply (simp add: stable_def)+
    apply (rule allI)
    apply (rule rghoare_p.Cond, simp, simp add: stable_def)
  using Send_Que_sat_SCE_h1 apply auto[1]
     apply (rule rghoare_p.Basic)
         apply blast
        apply auto[1]
       apply simp
      apply (simp add: stable_def)+
  apply (simp add: domevt_def get_evt_core_def Send_Que_Message_def label_def get_evt_el_def get_evt_label_def, clarify)
  apply (case_tac u)
    apply (simp add: state_equiv_def state_obs_part_def)
    apply (rule s0_update_help)
     apply (smt (z3) State.ext_inject State.surjective State.update_convs(3) State.update_convs(4))
    apply (rule obs_cap_equiv, clarsimp)
    apply (subgoal_tac "qbufsize s1 c = qbufsize s2 c")
     apply (case_tac "c = ch_srcqport conf p")
      apply (erule impE)
       apply (metis ch_chonn_help2 interf_def noninterf1_def)
      apply (case_tac "qbufsize s1 c < chmax conf (ch_srcqport conf p)", simp)
      apply (case_tac "qbufsize s2 c < chmax conf (ch_srcqport conf p)")
       apply linarith
      apply (metis linorder_not_le)
     apply presburger
    apply (metis (no_types, lifting) State.ext_inject State.surjective State.update_convs(3) obs_cap_part_def)
   apply (simp add: state_equiv_def state_obs_sched_def)
  using state_equiv_def state_obs.simps(3) by presburger

lemma Recv_Que_sat_SCE_h1: "\<turnstile> \<lbrace>True\<rbrace> \<acute>qbuf := \<acute>qbuf(ch_destqport conf p := tl (\<acute>qbuf (ch_destqport conf p)));;
                         \<lbrace>True \<rbrace>\<acute>qbufsize := \<acute>qbufsize (ch_destqport conf p := \<acute>qbufsize (ch_destqport conf p) - Suc 0)
  sat\<^sub>p [\<lbrace>is_dest_qport conf p \<and> (\<exists>y. \<acute>cur (c2s conf k) = Some y) \<and> port_of_part conf p (the (\<acute>cur (c2s conf k)))\<rbrace> 
        \<inter> \<lbrace>0 < \<acute>qbufsize (ch_destqport conf p)\<rbrace> \<inter> {V}, {(s, t). s = t}, UNIV, \<lbrace>\<acute>cur = cur V \<and>
       \<acute>partst = partst V \<and> (is_dest_qport conf p \<and> (\<exists>y. cur V (c2s conf k) = Some y) \<and> 
        port_of_part conf p (the (cur V (c2s conf k))) \<longrightarrow> (\<forall>c. c \<noteq> ch_destqport conf p \<longrightarrow> 
        \<acute>qbuf c = qbuf V c \<and> \<acute>qbufsize c = qbufsize V c) \<and> (0 < qbufsize V (ch_destqport conf p) \<longrightarrow> 
        \<acute>qbufsize (ch_destqport conf p) = qbufsize V (ch_destqport conf p) - Suc 0) \<and> 
         (qbufsize V (ch_destqport conf p) = 0 \<longrightarrow> \<acute>qbuf = qbuf V \<and> \<acute>qbufsize = qbufsize V)) \<and>
         ((is_dest_qport conf p \<longrightarrow> cur V (c2s conf k) = None \<or> \<not> port_of_part conf p (the (cur V (c2s conf k)))) 
          \<longrightarrow> \<acute>qbuf = qbuf V \<and> \<acute>qbufsize = qbufsize V)\<rbrace>]"
  apply(case_tac "is_dest_qport conf p \<and> (\<exists>y. (cur V) ((c2s conf) k) = Some y) \<and> 
        port_of_part conf p (the ((cur V) ((c2s conf) k))) \<and> 0 < (qbufsize V) (ch_destqport conf p)")
   apply simp
   apply(rule rghoare_p.Seq[where mid="{s. s = V\<lparr>qbuf := (qbuf V)(ch_destqport conf p := tl ((qbuf V) (ch_destqport conf p)))\<rparr>}"])
    apply(rule rghoare_p.Basic)
        apply auto[1]
       apply auto[1]
      apply blast
  apply(simp add: stable_def)+
   apply(rule rghoare_p.Basic, simp)
      apply auto[1]
  apply(simp add: stable_def)+
  apply(rule rghoare_p.Seq[where mid="{}"])
   apply(rule rghoare_p.Basic)
       apply(simp add:stable_def)+
  apply(rule rghoare_p.Basic, simp)
     apply(simp add:stable_def)+
  done

lemma Recv_Que_sat_SCE: "\<exists>\<S>. Recv_Que_Message k p \<in> \<S> \<and> step_consistent_e \<S> (Recv_Que_Message k p)"
  apply (rule sc_e_Basic, simp add: Recv_Que_Message_def)
  apply (simp add: body_def)
  apply (rule_tac pre = "\<lbrace>is_dest_qport conf p \<and> (\<exists>y. \<acute>cur (c2s conf k) = Some y) \<and> port_of_part conf p (the (\<acute>cur (c2s conf k)))\<rbrace>" 
          and rely = Id and post = "\<lbrace>True\<rbrace>" and guar = "\<lbrace>\<ordfeminine>cur = \<ordmasculine>cur \<and> \<ordfeminine>partst = \<ordmasculine>partst \<and> 
          ((is_dest_qport conf p \<and> \<ordmasculine>cur ((c2s conf) k) \<noteq> None \<and> port_of_part conf p (the (\<ordmasculine>cur ((c2s conf) k)))) 
          \<longrightarrow> (\<forall>c. c \<noteq> ch_destqport conf p \<longrightarrow> \<ordfeminine>qbuf c = \<ordmasculine>qbuf c \<and> \<ordfeminine>qbufsize c = \<ordmasculine>qbufsize c) \<and> 
          (\<ordmasculine>qbufsize (ch_destqport conf p) > 0 \<longrightarrow> \<ordfeminine>qbufsize (ch_destqport conf p) = \<ordmasculine>qbufsize (ch_destqport conf p) - 1) \<and>
          (\<ordmasculine>qbufsize (ch_destqport conf p) = 0 \<longrightarrow> \<ordfeminine>qbuf = \<ordmasculine>qbuf \<and> \<ordfeminine>qbufsize  = \<ordmasculine>qbufsize)) 
          \<and> ((\<not>(is_dest_qport conf p \<and> \<ordmasculine>cur ((c2s conf) k) \<noteq> None \<and> port_of_part conf p (the (\<ordmasculine>cur ((c2s conf) k)))))
          \<longrightarrow> (\<ordfeminine>qbuf  = \<ordmasculine>qbuf  \<and> \<ordfeminine>qbufsize  = \<ordmasculine>qbufsize))\<rbrace>" in sc_p.Await)
    apply (rule rghoare_p.Await, simp)
      apply (simp add: stable_def)+
    apply (rule allI)
  using Recv_Que_sat_SCE_h1 apply auto[1]
   apply simp
  apply (simp add: domevt_def get_evt_core_def Recv_Que_Message_def label_def get_evt_el_def get_evt_label_def, clarify)
  apply (case_tac u)
    apply (simp add: state_equiv_def state_obs_part_def)
    apply (rule s0_update_help)
     apply (smt (z3) State.ext_inject State.surjective State.update_convs(3) State.update_convs(4))
    apply (rule obs_cap_equiv, clarsimp)
  apply (subgoal_tac "qbufsize s1 c = qbufsize s2 c")
     apply (metis bot_nat_0.not_eq_extremum)
    apply (metis (no_types, lifting) State.ext_inject State.surjective State.update_convs(3) obs_cap_part_def)
   apply (simp add: state_equiv_def state_obs_sched_def)
  using state_equiv_def state_obs.simps(3) by presburger

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
        then have "ef\<in>{ef. \<exists>p. ef = Schedule_RGF k p} \<union>
                      {ef. \<exists>p m. ef = Send_Que_Message_RGF k p m} \<union>
                      {ef. \<exists>p. ef = Recv_Que_Message_RGF k p}" 
          using all_evts_es_esys EvtSys1_on_Core_RGF_def by auto
        then have "ef\<in>{ef. \<exists>p. ef = Schedule_RGF k p} 
                  \<or> ef\<in>{ef. \<exists>p m. ef = Send_Que_Message_RGF k p m} 
                  \<or> ef\<in>{ef. \<exists>p. ef = Recv_Que_Message_RGF k p}" by auto
        then show ?thesis
          proof
            assume "ef\<in>{ef. \<exists>p. ef = Schedule_RGF k p}"
            then have "\<exists>p. ef = Schedule_RGF k p" by auto
            then obtain p where "ef = Schedule_RGF k p" by auto
            then show ?thesis 
              by (simp add: E\<^sub>e_def Schedule_RGF_def Schedule_sat_SCE) 
          next
            assume "ef\<in>{ef. \<exists>p m. ef = Send_Que_Message_RGF k p m}
                    \<or> ef\<in>{ef. \<exists>p. ef = Recv_Que_Message_RGF k p}"
            then show ?thesis 
              proof
                assume "ef\<in>{ef. \<exists>p m. ef = Send_Que_Message_RGF k p m}"
                then have "\<exists>p m. ef = Send_Que_Message_RGF k p m" by auto
                then obtain p and m where "ef = Send_Que_Message_RGF k p m" by auto
                then show ?thesis 
                  by (simp add: E\<^sub>e_def Send_Que_Message_RGF_def Send_Que_sat_SCE)
              next
                assume "ef\<in>{ef. \<exists>p. ef = Recv_Que_Message_RGF k p}"
                then have "\<exists>p. ef = Recv_Que_Message_RGF k p" by auto
                then obtain p where "ef = Recv_Que_Message_RGF k p" by auto
                then show ?thesis 
                  by (simp add: E\<^sub>e_def Recv_Que_Message_RGF_def Recv_Que_sat_SCE)
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