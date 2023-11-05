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

typedecl QChannel

datatype Domain = P Part | S Sched 

record Config = c2s :: "Core \<Rightarrow> Sched"
                p2s :: "Part \<Rightarrow> Sched set"
                p2p :: "Port \<Rightarrow> Part"
                chsrc :: "QChannel \<Rightarrow> Port"
                chdest :: "QChannel \<Rightarrow> Port"  
                chmax :: "QChannel \<Rightarrow> nat"
  
axiomatization conf::Config 
  where bij_c2s: "bij (c2s conf)" 
    and portsrc_disj: "\<forall>c1 c2. c1 \<noteq> c2 \<longrightarrow> (chsrc conf) c1 \<noteq> (chsrc conf) c2" 
    and portdest_disj: "\<forall>c1 c2. c1 \<noteq> c2 \<longrightarrow> (chdest conf) c1 \<noteq> (chdest conf) c2" 
    and portsrcdest_disj: "\<forall>c1 c2. (chsrc conf) c1 \<noteq> (chdest conf) c2"

lemma inj_surj_c2s: "inj (c2s conf) \<and> surj (c2s conf)"
  using bij_c2s by (simp add: bij_def) 


definition gsch :: "Config \<Rightarrow> Core \<Rightarrow> Sched"
  where "gsch cfg k \<equiv> (c2s cfg) k"

definition port_of_part :: "Config \<Rightarrow> Port \<Rightarrow> Part \<Rightarrow> bool"
  where "port_of_part sc po pa \<equiv> ((p2p sc) po = pa)"

definition par_ports :: "Config \<Rightarrow> Part \<Rightarrow> Port set"
  where "par_ports sc pa \<equiv> {p. port_of_part sc p pa}"

definition is_src_qport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_src_qport sc p \<equiv> (p\<in>range (chsrc sc))"

definition is_dest_qport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_dest_qport sc p \<equiv> (p\<in>range (chdest sc))"

definition ch_srcqport :: "Config \<Rightarrow> Port \<Rightarrow> QChannel"
  where "ch_srcqport sc p \<equiv> SOME c. (chsrc sc) c = p"

definition ch_destqport :: "Config \<Rightarrow> Port \<Rightarrow> QChannel"
  where "ch_destqport sc p \<equiv> SOME c. (chdest sc) c = p"

definition par_src_qports :: "Config \<Rightarrow> Port set \<Rightarrow> Port set"
where "par_src_qports sc ps \<equiv>  {p.  (is_src_qport sc) p \<and> p\<in>ps}"

definition par_dest_qports :: "Config \<Rightarrow> Port set \<Rightarrow> Port set"
  where "par_dest_qports sc ps \<equiv>  {p.  (is_dest_qport sc) p \<and> p\<in>ps}"

definition par_qchan :: "Config \<Rightarrow> Part \<Rightarrow> QChannel set"
  where "par_qchan sc pa \<equiv> (ch_srcqport sc) ` (par_src_qports sc (par_ports sc pa)) \<union> 
                           (ch_destqport sc) ` (par_dest_qports sc (par_ports sc pa))"

datatype PartMode = IDLE | READY | RUN

definition ch_conn :: "Config \<Rightarrow> Part \<Rightarrow> Part \<Rightarrow> bool"
  where "ch_conn cfg p1 p2 \<equiv> (\<exists>sch. (p2p cfg) ((chsrc cfg) sch) = p1 
                                      \<and> (p2p cfg) ((chdest cfg) sch) = p2)"

primrec ch_conn2 :: "Config \<Rightarrow> Domain \<Rightarrow> Domain \<Rightarrow> bool"
  where "ch_conn2 cfg (P p1) d2 = (case d2 of
                                    (P p2) \<Rightarrow> ch_conn cfg p1 p2 |
                                    (S s2) \<Rightarrow> False)" |
        "ch_conn2 cfg (S p1) d2 = False"

primrec part_on_core :: "Config \<Rightarrow> Domain \<Rightarrow> Domain \<Rightarrow> bool"
  where "part_on_core cfg (P d1) d2 = (case d2 of
                                        P d22 \<Rightarrow> False |
                                        S d22 \<Rightarrow> d22 \<in>((p2s cfg) d1))" |
        "part_on_core cfg (S d1) d2 = False"

record State = cur :: "Sched \<Rightarrow> Part option"
               qbuf :: "QChannel \<Rightarrow> Message list"
               qbufsize :: "QChannel \<Rightarrow> nat"
               partst :: "Part \<Rightarrow> PartMode"

datatype EL = Core_InitE | ScheduleE | Send_Que_MessageE |  Recv_Que_MessageE

datatype parameter = Port Port | Message Message | Partition Part

type_synonym EventLabel = "EL \<times> (parameter list \<times> Core)" 

definition get_evt_label :: "EL \<Rightarrow> parameter list \<Rightarrow> Core \<Rightarrow> EventLabel" ("_ _ \<rhd> _" [0,0,0] 20)
  where "get_evt_label el ps k \<equiv> (el,(ps,k))"

abbreviation "core_init_pre k \<equiv> \<lbrace>\<forall>p. c2s conf k \<in> p2s conf p \<longrightarrow> \<acute>partst p = IDLE\<rbrace>"
abbreviation "core_init_rely k \<equiv> \<lbrace>(\<forall>p. c2s conf k \<in> p2s conf p \<longrightarrow> \<ordfeminine>partst p = \<ordmasculine>partst p)\<rbrace>"
abbreviation "core_init_guar k \<equiv> \<lbrace>\<ordfeminine>cur= \<ordmasculine>cur \<and> \<ordfeminine>qbuf= \<ordmasculine>qbuf \<and> \<ordfeminine>qbufsize= \<ordmasculine>qbufsize 
            \<and> (\<forall>p. c2s conf k \<in> p2s conf p \<longrightarrow> \<ordmasculine>partst p = IDLE \<and> \<ordfeminine>partst p = READY)
            \<and> (\<forall>c p. c \<noteq> k \<and> c2s conf c \<in> p2s conf p \<longrightarrow> \<ordfeminine>partst  p = \<ordmasculine>partst p)\<rbrace> \<union> Id"



definition Core_Init :: "Core \<Rightarrow> (EventLabel, Core, State) event" 
  where "Core_Init k \<equiv> 
    EVENT Core_InitE [] \<rhd> k 
    WHERE
      True
    THEN 
      \<lbrace>True\<rbrace> SKIP 
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
       c2s conf k \<in> p2s conf p
      \<and> (\<acute>partst p \<noteq> IDLE)
      \<and> (\<acute>cur((c2s conf) k) = None 
          \<or> c2s conf k \<in> p2s conf (the (\<acute>cur((c2s conf) k))))
    THEN 
      \<lbrace>True\<rbrace> IF (\<acute>cur((c2s conf) k) \<noteq> None) THEN 
        \<lbrace>True\<rbrace> ATOMIC
          \<lbrace>True\<rbrace> \<acute>partst := \<acute>partst(the (\<acute>cur ((c2s conf) k)) := READY);;
          \<lbrace>True\<rbrace> \<acute>cur := \<acute>cur((c2s conf) k := None)
               END
      FI;; 
     (\<lbrace>True\<rbrace> ATOMIC
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
      \<lbrace>is_src_qport conf p \<and> (\<exists>y. \<acute>cur ((c2s conf) k) = Some y) 
      \<and> port_of_part conf p (the (\<acute>cur ((c2s conf) k)))\<rbrace> 
      AWAIT \<acute>qbufsize (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
        \<lbrace>is_src_qport conf p \<and> (\<exists>y. \<acute>cur ((c2s conf) k) = Some y) \<and> 
        port_of_part conf p (the (\<acute>cur ((c2s conf) k)))\<rbrace> \<inter> \<lbrace>\<acute>qbufsize (ch_srcqport conf p) 
        < chmax conf (ch_srcqport conf p)\<rbrace> 
        \<acute>qbuf := \<acute>qbuf (ch_srcqport conf p := \<acute>qbuf (ch_srcqport conf p) @ [m]);;
        \<lbrace>True\<rbrace> \<acute>qbufsize := \<acute>qbufsize (ch_srcqport conf p := \<acute>qbufsize (ch_srcqport conf p) + 1)
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
      \<lbrace>True\<rbrace> AWAIT \<acute>qbufsize (ch_srcqport conf p) > 0 THEN 
        \<lbrace>True\<rbrace> \<acute>qbuf := \<acute>qbuf (ch_srcqport conf p := tl (\<acute>qbuf (ch_srcqport conf p)));;
        \<lbrace>True\<rbrace> \<acute>qbufsize := \<acute>qbufsize (ch_srcqport conf p := \<acute>qbufsize (ch_srcqport conf p) - 1)
      END
    END"

definition domevt :: "State \<Rightarrow> Core \<Rightarrow> (EventLabel, Core, State) event \<Rightarrow> Domain"
  where "domevt s k e \<equiv>  
                         (if (\<exists>p m. e = Send_Que_Message k p m )\<or>                             
                             (\<exists>p. e = Recv_Que_Message k p) then
                              P (the ((cur s) (gsch conf k)))
                         else S (gsch conf k))"  (*for convenience, we also consider domain of other(undefined) event as the sched*)

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
                         else False"

definition noninterf1 :: "Domain \<Rightarrow> Domain \<Rightarrow> bool" ("(_ \<setminus>\<leadsto> _)" [70,71] 60)
  where "u \<setminus>\<leadsto> v \<equiv> \<not> (u \<leadsto> v)"

axiomatization s0 where s0_init: "s0 \<equiv> fst (System_Init conf)"

definition state_obs_sched :: "State \<Rightarrow> Sched \<Rightarrow> State"
  where "state_obs_sched s d \<equiv> s0\<lparr>cur:=(cur s0) (d:=(cur s) d)\<rparr>"

definition state_obs_part :: "State \<Rightarrow> Part \<Rightarrow> State"
  where "state_obs_part s p \<equiv> s0\<lparr>partst:=(partst s0) (p:=(partst s) p)\<rparr> "

definition qbuf_obs_part :: "State \<Rightarrow> Part \<Rightarrow> (QChannel \<Rightarrow> Message list)"
  where "q_obs_part s p \<equiv> (qbuf s) |` (par_qchan conf p)"

primrec state_obs :: "State \<Rightarrow> Domain \<Rightarrow> State"
  where "state_obs s (P p) = state_obs_part s p" |
        "state_obs s (S p) = state_obs_sched s p"

definition state_equiv :: "State \<Rightarrow> Domain \<Rightarrow> State \<Rightarrow> bool" ("(_ \<sim>_\<sim> _)" [70,69,70] 60)
  where "state_equiv s d t \<equiv> state_obs s d = state_obs t d"

lemma state_equiv_transitive: "\<lbrakk>s \<sim> d \<sim> t; t \<sim> d \<sim> r\<rbrakk> \<Longrightarrow> s \<sim> d \<sim> r"
  by (simp add:state_equiv_def)
    
lemma state_equiv_symmetric : "s \<sim> d \<sim> t \<Longrightarrow> t \<sim> d \<sim> s"
  by (simp add:state_equiv_def)

lemma state_equiv_reflexive : "s \<sim> d \<sim> s"
  by (simp add:state_equiv_def)





end