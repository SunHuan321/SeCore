(*
Created by:
Yongwang Zhao (ywzhao@ntu.edu.sg, zhaoyw@buaa.edu.cn)
School of Computer Engineering, Nanyang Technological University, Singapore
and School of Computer Science & Engineering, Beihang University, China

David Sanan (sanan@ntu.edu.sg)
School of Computer Engineering, Nanyang Technological University, Singapore
*)

section \<open>Formal specification of ARINC653 Multicore Separation Kernel\<close>

theory ARINC653_MultiCore_Spec
imports PiCore_Syntax PiCore_RG_IFS
begin

typedecl Part
typedecl Sched
typedecl Message 
typedecl Port
datatype Core = Core0 | Core1


datatype Domain = P Part | S Sched 

type_synonym Que = "Message set" 

typedecl SampChannel


record Config = c2s :: "Core \<Rightarrow> Sched"
                p2s :: "Part \<Rightarrow> Sched set"
                p2p :: "Port \<Rightarrow> Part"
                scsrc :: "SampChannel \<Rightarrow> Port"
                scdests :: "SampChannel \<Rightarrow> Port set"                                
                core_id::"Core \<Rightarrow> nat"

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

definition gsch :: "Config \<Rightarrow> Core \<Rightarrow> Sched"
  where "gsch cfg k \<equiv> (c2s cfg) k"

definition is_src_sampport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_src_sampport sc p \<equiv> (p\<in>range (scsrc sc))"

definition is_dest_sampport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_dest_sampport sc p \<equiv> (p\<in>\<Union> range (scdests sc))"

definition is_sampport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_sampport sc p \<equiv> is_src_sampport sc p \<or> is_dest_sampport sc p"
(*
definition is_src_queport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_src_queport sc p \<equiv> (p\<in>range (qcsrc sc))"

definition is_dest_queport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_dest_queport sc p \<equiv> (p\<in>range (qcdest sc))"

definition is_queport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_queport sc p \<equiv> is_src_queport sc p \<or> is_dest_queport sc p"

lemma only_src_queport: 
 "is_src_queport conf p \<Longrightarrow> \<not>is_dest_queport conf p \<and> \<not>is_src_sampport conf p \<and>
                          \<not>is_dest_sampport conf p"
unfolding is_src_queport_def is_dest_queport_def is_src_sampport_def
          is_dest_sampport_def
using port_disj
by (metis IntI empty_iff)

lemma only_dest_queport: 
 "is_dest_queport conf p \<Longrightarrow> \<not>is_src_queport conf p \<and> \<not>is_src_sampport conf p \<and>
                          \<not>is_dest_sampport conf p"
unfolding is_src_queport_def is_dest_queport_def is_src_sampport_def
          is_dest_sampport_def
using port_disj
by (metis IntI empty_iff)

lemma only_src_sampport: 
 "is_src_sampport conf p \<Longrightarrow> \<not>is_dest_queport conf p \<and> \<not>is_src_queport conf p \<and>
                          \<not>is_dest_sampport conf p"
unfolding is_src_queport_def is_dest_queport_def is_src_sampport_def
          is_dest_sampport_def
using port_disj
by (metis IntI empty_iff)

lemma only_dest_sampport: 
 "is_dest_sampport conf p \<Longrightarrow> \<not>is_src_queport conf p \<and> \<not>is_src_sampport conf p \<and>
                          \<not>is_dest_queport conf p"
unfolding is_src_queport_def is_dest_queport_def is_src_sampport_def
          is_dest_sampport_def
using port_disj
by (metis IntI empty_iff)
*)
definition port_of_part :: "Config \<Rightarrow> Port \<Rightarrow> Part \<Rightarrow> bool"
  where "port_of_part sc po pa \<equiv> ((p2p sc) po = pa)"

definition ch_srcsampport :: "Config \<Rightarrow> Port \<Rightarrow> SampChannel"
  where "ch_srcsampport sc p \<equiv> SOME c. (scsrc sc) c = p"


definition ch_destsampport :: "Config \<Rightarrow> Port \<Rightarrow> SampChannel"
  where "ch_destsampport sc p \<equiv> SOME c. p\<in>((scdests sc) c)"
(*
definition ch_srcqueport :: "Config \<Rightarrow> Port \<Rightarrow> QueChannel"
  where "ch_srcqueport sc p \<equiv> SOME c. (qcsrc sc) c = p"

definition ch_destqueport :: "Config \<Rightarrow> Port \<Rightarrow> QueChannel"
  where "ch_destqueport sc p \<equiv> SOME c. (qcdest sc) c = p"

lemma same_dest_queport:
  "(qcdest conf) c1 = p1 \<Longrightarrow>
   (qcdest conf) c2 = p2 \<Longrightarrow>
   p1=p2 \<Longrightarrow>
   c1 = c2 "
using no_same_dest
by (meson inj_eq)
*)

lemma same_dest_sampport:
  "(scdests conf) c1 = p1 \<Longrightarrow>
   (scdests conf) c2 = p2 \<Longrightarrow>
   p1 \<inter> p2 \<noteq> {} \<Longrightarrow>
   c1 = c2 "
using no_same_dest
by (meson inj_eq)
(* 
lemma same_src_queport:
  "(qcsrc conf) c1 = p1 \<Longrightarrow>
   (qcsrc conf) c2 = p2 \<Longrightarrow>
   p1=p2 \<Longrightarrow>
   c1 = c2 "
using no_same_source
by (meson inj_eq)
*)
lemma same_src_sampport:
  "(scsrc conf) c1 = p1 \<Longrightarrow>
   (scsrc conf) c2 = p2 \<Longrightarrow>
   p1 = p2 \<Longrightarrow>
   c1 = c2 "
using no_same_source
by (meson inj_eq)

(*lemma not_dest_src_que:
  "(qcdest conf) c1 = p1 \<Longrightarrow>
   (qcsrc conf) c2 = p2 \<Longrightarrow>
   p1=p2 \<Longrightarrow>
   G "
using port_disj
using disjoint_iff_not_equal rangeI by blast
*)

lemma not_dest_src_samp:
  "p1 \<in> (scdests conf) c1  \<Longrightarrow>
   (scsrc conf) c2 = p2 \<Longrightarrow>
   p1=p2 \<Longrightarrow>
   G "
using port_disj
by (simp add: UnionI disjoint_iff_not_equal rangeI)

(*lemma not_dest_src_que_samp:
  "(qcdest conf) c1 = p1 \<Longrightarrow>
   (scsrc conf) c2 = p2 \<Longrightarrow>
   p1=p2 \<Longrightarrow>
   G "
using port_disj
using disjoint_iff_not_equal rangeI
by metis *)

(* lemma not_src_dest_que_samp:
  "(qcsrc conf) c1 = p1 \<Longrightarrow>
   p2 \<in> (scdests conf) c2 \<Longrightarrow>
   p1=p2 \<Longrightarrow>
   G "
proof -
  assume a1: "qcsrc conf c1 = p1"
  assume a2: "p2 \<in> scdests conf c2"
  assume "p1 = p2"
  then have False
    using a2 a1 by (meson Union_iff disjoint_iff_not_equal port_disj rangeI)
  then show ?thesis
    by metis
qed *)

(* lemma not_src_src_samp_que:
  "(scsrc conf) c1 = p1 \<Longrightarrow>
   (qcsrc conf) c2 = p2 \<Longrightarrow>
   p1=p2 \<Longrightarrow>
   G "
using port_disj
using disjoint_iff_not_equal rangeI
by metis *)

(* lemma not_dest_dest_que_samp:
  "(qcdest conf) c1 = p1 \<Longrightarrow>
   p2 \<in> (scdests conf) c2 \<Longrightarrow>
   p1=p2 \<Longrightarrow>
   G "
using port_disj
using disjoint_iff_not_equal rangeI
using UnionI by blast
*)

definition par_ports :: "Config \<Rightarrow> Part \<Rightarrow> Port set"
where "par_ports sc pa \<equiv> {p. port_of_part sc p pa}"

lemma "pa\<noteq>pb \<Longrightarrow> par_ports conf pa \<inter> par_ports conf pb = {}"
  using bij_p2p unfolding par_ports_def port_of_part_def 
  by auto


definition par_sampling_ports :: "Config \<Rightarrow> Port set \<Rightarrow> Port set"
where "par_sampling_ports sc ps \<equiv> {p.  (is_sampport sc) p \<and> p\<in>ps}"

(*definition par_queuing_ports :: "Config \<Rightarrow> Port set \<Rightarrow> Port set"
where "par_queuing_ports sc ps \<equiv>  {p.  (is_queport sc) p \<and> p\<in>ps}"
*)

definition par_dest_sampling_ports :: "Config \<Rightarrow> Port set \<Rightarrow> Port set"
where "par_dest_sampling_ports sc ps \<equiv> {p.  (is_dest_sampport sc) p \<and> p\<in>ps}"

definition par_src_sampling_ports :: "Config \<Rightarrow> Port set \<Rightarrow> Port set"
where "par_src_sampling_ports sc ps \<equiv> {p.  (is_src_sampport sc) p \<and> p\<in>ps}"

(*definition par_dest_queuing_ports :: "Config \<Rightarrow> Port set \<Rightarrow> Port set"
where "par_dest_queuing_ports sc ps \<equiv>  {p.  (is_dest_queport sc) p \<and> p\<in>ps}"
*)

(*definition par_src_queuing_ports :: "Config \<Rightarrow> Port set \<Rightarrow> Port set"
where "par_src_queuing_ports sc ps \<equiv>  {p.  (is_src_queport sc) p \<and> p\<in>ps}"
*)

(* definition par_quechan::"Config \<Rightarrow> Part \<Rightarrow> QueChannel set"
where "par_quechan sc pa \<equiv> (ch_srcqueport sc) ` (par_src_queuing_ports sc (par_ports sc pa)) \<union>
                           (ch_destqueport sc) ` (par_dest_queuing_ports sc (par_ports sc pa))"
*)

definition par_sampchan::"Config \<Rightarrow> Part \<Rightarrow> SampChannel set"
where "par_sampchan sc pa \<equiv> (ch_srcsampport sc) ` (par_src_sampling_ports sc (par_ports sc pa)) \<union>
                            (ch_destsampport sc) `(par_dest_sampling_ports sc (par_ports sc pa))"


definition ch_conn :: "Config \<Rightarrow> Part \<Rightarrow> Part \<Rightarrow> bool"
  where "ch_conn cfg p1 p2 \<equiv> (\<exists>sch p. (p2p cfg) ((scsrc cfg) sch) = p1 
                                      \<and> p \<in> (scdests cfg) sch \<and> (p2p cfg) p = p2)
                            (*\<or> (\<exists>qch. (p2p cfg) ((qcsrc cfg) qch) = p1 
                                      \<and> (p2p cfg) ((qcdest cfg) qch) = p2)*)"

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

record State = cur :: "Sched \<Rightarrow> Part"
               schan :: "SampChannel \<rightharpoonup> Message"
               (* qchan :: "QueChannel \<Rightarrow> Que"
               (*sclock :: "SampChannel \<Rightarrow> Core option"*)  (*True: it is available*)
               (* sclock :: "SampChannel \<Rightarrow> nat" *)
               qclock :: "QueChannel \<Rightarrow> nat" *)
               (*vark :: Core*)

(* definition gsclock :: "State \<Rightarrow> SampChannel \<Rightarrow> nat"
  where "gsclock s sc \<equiv> (sclock s) sc" *)

(* definition gqclock :: "State \<Rightarrow> QueChannel \<Rightarrow> nat"
  where "gqclock s qc \<equiv> (qclock s) qc" *)

datatype EL = Core_InitE | ScheduleE0 |ScheduleE1 | Write_Sampling_MessageE0 |  Write_Sampling_MessageE1 | 
              Read_Sampling_MessageE0 | Read_Sampling_MessageE1
              | Get_Sampling_Port_StatusE | Send_Queuing_MessageE | Receive_Queuing_MessageE
              | Get_Queuing_Port_StatusE

datatype par = Nat nat | Str string | Q Que | Pt Port | Msg Message
datatype parN = NAT | STRI | QUE | PORT | MSG

primrec gNat :: "par \<Rightarrow> nat option"
  where "gNat (Nat n) = Some n" 

primrec gStr :: "par \<Rightarrow> string option"
  where "gStr (Str n) = Some n" 

primrec gPort :: "par \<Rightarrow> Port option"
  where gPortNor: "gPort (Pt n) = Some n" 

primrec gMsg :: "par \<Rightarrow> Message option"
  where "gMsg (Msg n) = Some n" 

primrec MT:: "par \<Rightarrow> parN \<Rightarrow> bool" 
  where "MT (Nat _) ptn = (if ptn = NAT  then True else False)" |
        "MT (Str _) ptn = (if ptn = STRI  then True else False)" |
        "MT (Q _)   ptn = (if ptn = QUE  then True else False)" |
        "MT (Pt _)  ptn = (if ptn = PORT then True else False)" |
        "MT (Msg _) ptn = (if ptn = MSG  then True else False)" 

lemma MT_Nat:"MT u NAT \<Longrightarrow> \<exists>x. u = Nat x"
by (metis MT.simps(2) MT.simps(3) MT.simps(4) MT.simps(5) 
    par.exhaust parN.distinct(2) parN.distinct(4) parN.distinct(6) parN.distinct(8))

lemma MT_Str: "MT u STRI \<Longrightarrow> \<exists>x. u = Str x"
by (metis MT.simps(1) MT.simps(3) MT.simps(4) MT.simps(5) par.exhaust 
            parN.distinct(1) parN.distinct(12) parN.distinct(14) parN.simps(10))

lemma MT_Q:"MT u QUE \<Longrightarrow> \<exists>x. u = Q x"
by (metis MT.simps(1) MT.simps(2) MT.simps(4) MT.simps(5) 
    par.exhaust parN.distinct(16) parN.distinct(18) parN.distinct(4) parN.distinct(9))


lemma MT_Pt: "MT u PORT \<Longrightarrow> \<exists>x. u = Pt x"
by (metis MT.simps(1) MT.simps(2) MT.simps(3) MT.simps(5) 
    par.exhaust parN.distinct(12) parN.distinct(16) parN.distinct(20) parN.distinct(5))

lemma MT_Msg: "MT u MSG \<Longrightarrow> \<exists>x. u = Msg x"
by (metis MT.simps(1) MT.simps(2) MT.simps(3) MT.simps(4) par.exhaust 
   parN.distinct(14) parN.distinct(18) parN.distinct(20) parN.distinct(8))


primrec WF:: "par list \<Rightarrow> parN list \<Rightarrow> bool" ("(_typeof_)" [70,71] 60)
  where "WF [] bs = (if bs = [] then True else False)" |
        "WF (a#as) bs = ((length (a#as) = length bs) \<and> MT a (bs!0) \<and> WF as (tl bs))"

lemma same_length_WF:" ps typeof pt  \<Longrightarrow> length ps = length pt"
proof (induct ps)
  case Nil thus ?case
    using WF.simps(1) length_0_conv by fastforce 
next 
  case (Cons a as) thus ?case by auto
qed

lemma typeof_MT:
  assumes a0:"ps typeof pt" and 
          a1:"i< length ps" 
  shows "MT (ps!i) (pt!i)"
using a0 a1
proof (induct ps arbitrary: i pt)
  case Nil thus ?case by auto
next
  case (Cons ps1 psl)     
  thus ?case 
  proof (cases i)
    case 0 thus ?thesis using Cons by auto
  next
    case (Suc n)   
      obtain pt1 ptl where pt:"pt = pt1#ptl" 
        by (metis PiCore_Semantics.nth_tl Cons(2) same_length_WF length_0_conv list.simps(3))
      have f1: "n < length psl"
        by (metis Cons.prems(2) Suc Suc_less_SucD length_Cons)
      then have "MT (psl!n) (ptl!n)" using Cons pt by auto
      thus ?thesis using Cons Suc pt by fastforce
  qed 
qed



definition Core_Init :: "Core \<Rightarrow> (EL, par list, Core, State) event" 
  where "Core_Init k\<equiv> 
    EVENT Core_InitE ps@k WHERE 
      True
    THEN 
      SKIP 
    END"

(*
definition Core_Init :: "(EL, par list, Core, State) event" 
  where "Core_Init \<equiv> BasicEvent (Evt,(\<lambda>(ps, k). 
            (\<lbrace>True\<rbrace>, 
              (*event body*)
             SKIP
            )))"
*)

definition System_Init :: "Config \<Rightarrow> (State \<times> (EL, par list, Core, State) x)"
  where "System_Init cfg \<equiv> (\<lparr>cur=(\<lambda>c. SOME p. c\<in>(p2s cfg) p ),
                            schan = (\<lambda>c. None)
                            (* qchan = (\<lambda>c. {}), *)
                            (* sclock = (\<lambda>c. 0),*)
                            (* qclock = (\<lambda>c. 0) *) \<rparr>, 
                            (\<lambda>k. Core_Init k))"

(*
definition Schedule :: "(EL, par list, Core, State) event" 
  where "Schedule \<equiv> BasicEvent (Evt,(\<lambda>(ps, k). 
            (\<lbrace> ps typeof []                                  (*parameter type*)
              \<rbrace>, 
              (*event body*) (*need change to using Spec (nondeterministic) *)
             \<acute>cur := \<acute>cur((c2s conf) k := SOME p. (p2s conf) p = (c2s conf) k)
            )))"
*)

definition Schedulek0 :: "Core \<Rightarrow> (EL, par list, Core, State) event" 
  where "Schedulek0 k \<equiv> 
    EVENT ScheduleE0 ps@k1 WHERE 
      ps typeof []
    THEN 
      \<acute>cur := \<acute>cur((c2s conf) Core0 := SOME p. (c2s conf) Core0 \<in>(p2s conf) p ) 
    END"

definition Schedulek1 :: "Core \<Rightarrow> (EL, par list, Core, State) event" 
  where "Schedulek1 k \<equiv> 
    EVENT ScheduleE1 ps@k1 WHERE 
      ps typeof []
    THEN 
      \<acute>cur := \<acute>cur((c2s conf) Core1 := SOME p. (c2s conf) Core1 \<in>(p2s conf) p ) 
    END"

(*
definition Write_Sampling_Message :: "(EL, par list, Core, State) event" 
  where "Write_Sampling_Message \<equiv> BasicEvent (Evt,(\<lambda>(ps, k). 
            (\<lbrace> ps typeof [PORT,MSG]                                  (*parameter type*)
              \<and> is_src_sampport conf (the (gPort (ps!0)))           (*constrains on parameters*)
              \<and> port_of_part conf (the (gPort (ps!0))) (\<acute>cur (gsch conf k))     (*guard of states*)
             \<rbrace>, 
             (*event body*)
             AWAIT (\<acute>sclock (ch_srcsampport conf (the (gPort (ps!0))))) THEN 
                \<acute>sclock := \<acute>sclock (ch_srcsampport conf (the (gPort (ps!0))) := False)
             END;;
             \<acute>schan := \<acute>schan (ch_srcsampport conf (the (gPort (ps!0))) := Some ((the (gMsg (ps!1)))));;
             \<acute>sclock := \<acute>sclock (ch_srcsampport conf (the (gPort (ps!0))) := True)
            )))"
*)                                                                
definition Write_Sampling_Messagek0 :: "Core \<Rightarrow> (EL, par list, Core, State) event" 
  where "Write_Sampling_Messagek0 k \<equiv> 
    EVENT Write_Sampling_MessageE0 ps@k1 WHERE 
       ps typeof [PORT,MSG]                                  (*parameter type*)
       \<and> is_src_sampport conf (the (gPort (ps!0)))           (*constrains on parameters*)
       \<and> port_of_part conf (the (gPort (ps!0))) (\<acute>cur (gsch conf Core0))
       \<and> k = Core0 
    THEN       
      \<acute>schan := \<acute>schan (ch_srcsampport conf (the (gPort (ps!0))) := Some ((the (gMsg (ps!1)))))      
    END"

definition Write_Sampling_Messagek1 :: "Core \<Rightarrow> (EL, par list, Core, State) event" 
  where "Write_Sampling_Messagek1 k \<equiv> 
    EVENT Write_Sampling_MessageE1 ps@k1 WHERE 
       ps typeof [PORT,MSG]                                  (*parameter type*)
       \<and> is_src_sampport conf (the (gPort (ps!0)))           (*constrains on parameters*)
       \<and> port_of_part conf (the (gPort (ps!0))) (\<acute>cur (gsch conf Core1))
       \<and> k = Core1 
    THEN       
      \<acute>schan := \<acute>schan (ch_srcsampport conf (the (gPort (ps!0))) := Some ((the (gMsg (ps!1)))))      
    END"

lemma unique_srcsampport:"\<exists>!c. (ch_srcsampport conf p) =c"
by auto

lemma other_chan_eq:
  "ch =(ch_srcsampport conf p) \<Longrightarrow>
   s\<lparr>schan := (schan s) (ch:= x) \<rparr> = y \<Longrightarrow>
   ch' \<noteq> ch \<Longrightarrow>
   (schan y) ch' = (schan s) ch'"
by auto
(*
definition Read_Sampling_Message :: "(EL, par list, Core, State) event" 
  where "Read_Sampling_Message \<equiv> BasicEvent (Evt,(\<lambda>(ps, k). 
            (\<lbrace> ps typeof [PORT]                                       (*parameter type*)
              \<and> is_dest_sampport conf (the (gPort (ps!0)))           (*constrains on parameters*)
              \<and> port_of_part conf (the (gPort (ps!0))) (\<acute>cur (gsch conf k))      (*guard of states*)
             \<rbrace>, 
             (*event body*)
             AWAIT (\<acute>sclock (ch_srcsampport conf (the (gPort (ps!0))))) THEN 
               \<acute>sclock := \<acute>sclock (ch_srcsampport conf (the (gPort (ps!0))) := False)
             END;;
              (*read msg here*)
             \<acute>sclock := \<acute>sclock (ch_srcsampport conf (the (gPort (ps!0))) := True)
            )))"
*)
definition Read_Sampling_Messagek0 :: "Core \<Rightarrow> (EL, par list, Core, State) event" 
  where "Read_Sampling_Messagek0 k \<equiv> 
    EVENT Read_Sampling_MessageE0 ps@k1 WHERE 
      ps typeof [PORT]                                       (*parameter type*)
        \<and> is_dest_sampport conf (the (gPort (ps!0)))           (*constrains on parameters*)
        \<and> port_of_part conf (the (gPort (ps!0))) (\<acute>cur (gsch conf Core0))      (*guard of states*)
    THEN 
     SKIP
    END"

definition Read_Sampling_Messagek1 :: "Core \<Rightarrow> (EL, par list, Core, State) event" 
  where "Read_Sampling_Messagek1 k \<equiv> 
    EVENT Read_Sampling_MessageE1 ps@k1 WHERE 
      ps typeof [PORT]                                       (*parameter type*)
        \<and> is_dest_sampport conf (the (gPort (ps!0)))           (*constrains on parameters*)
        \<and> port_of_part conf (the (gPort (ps!0))) (\<acute>cur (gsch conf Core1))      (*guard of states*)
    THEN 
     SKIP
    END"

(*
definition Get_Sampling_Port_Status :: "(EL, par list, Core, State) event" 
  where "Get_Sampling_Port_Status \<equiv> BasicEvent (Evt,(\<lambda>(ps, k). 
            (\<lbrace> ps typeof [PORT]                                       (*parameter type*)
               \<and> is_sampport conf (the (gPort (ps!0)))           (*constrains on parameters*)
               \<and> port_of_part conf (the (gPort (ps!0))) (\<acute>cur (gsch conf k))      (*guard of states*)
             \<rbrace>, 
             (*event body*)
             SKIP
            )))"
*)

(*
definition Send_Queuing_Message :: "(EL, par list, Core, State) event" 
  where "Send_Queuing_Message \<equiv> BasicEvent (Evt,(\<lambda>(ps, k). 
            (\<lbrace> ps typeof [PORT,MSG]                                       (*parameter type*)
              \<and> is_src_queport conf (the (gPort (ps!0)))           (*constrains on parameters*)
              \<and> port_of_part conf (the (gPort (ps!0))) (\<acute>cur (gsch conf k))      (*guard of states*)
             \<rbrace>, 
             (*event body*)
             AWAIT (\<acute>qclock (ch_srcqueport conf (the (gPort (ps!0))))) THEN 
               \<acute>qclock := \<acute>qclock (ch_srcqueport conf (the (gPort (ps!0))) := False)
             END;;
             IF card (\<acute>qchan (ch_srcqueport conf (the (gPort (ps!0))))) 
                  < (qmax conf) (ch_srcqueport conf (the (gPort (ps!0)))) THEN
                \<acute>qchan := \<acute>qchan (ch_srcqueport conf (the (gPort (ps!0))) 
                                  := insert (the (gMsg (ps!1))) (\<acute>qchan (ch_srcqueport conf (the (gPort (ps!0))))))
             ELSE 
                SKIP
             FI;;
             \<acute>qclock := \<acute>qclock (ch_srcqueport conf (the (gPort (ps!0))) := True)
            )))"
*)

(*
definition Receive_Queuing_Message :: "(EL, par list, Core, State) event" 
  where "Receive_Queuing_Message \<equiv> BasicEvent (Evt,(\<lambda>(ps, k). 
            (\<lbrace> ps typeof [PORT]                                       (*parameter type*)
              \<and> is_dest_queport conf (the (gPort (ps!0)))           (*constrains on parameters*)
              \<and> port_of_part conf (the (gPort (ps!0))) (\<acute>cur (gsch conf k))      (*guard of states*)
             \<rbrace>, 
             (*event body*)
             AWAIT (\<acute>qclock (ch_destqueport conf (the (gPort (ps!0))))) THEN 
               \<acute>qclock := \<acute>qclock (ch_destqueport conf (the (gPort (ps!0))) := False)
             END;;
             IF card (\<acute>qchan (ch_destqueport conf (the (gPort (ps!0))))) > 0 THEN
                \<acute>qchan := \<acute>qchan (ch_destqueport conf (the (gPort (ps!0))) 
                                := \<acute>qchan (ch_destqueport conf (the (gPort (ps!0)))) 
                                    - {SOME m. m\<in>\<acute>qchan (ch_destqueport conf (the (gPort (ps!0))))})
             ELSE 
                SKIP
             FI;;
             \<acute>qclock := \<acute>qclock (ch_destqueport conf (the (gPort (ps!0))) := True)
             
            )))"
*)


(*
definition Get_Queuing_Port_Status :: "(EL, par list, Core, State) event" 
  where "Get_Queuing_Port_Status \<equiv> BasicEvent (Evt,(\<lambda>(ps, k). 
            (\<lbrace> ps typeof [PORT]                                       (*parameter type*)
               \<and> is_queport conf (the (gPort (ps!0)))           (*constrains on parameters*)
               \<and> port_of_part conf (the (gPort (ps!0))) (\<acute>cur (gsch conf k))      (*guard of states*)
             \<rbrace>, 
             (*event body*)
             SKIP
            )))"

*)

definition Core_Init_RGCond :: " (State) rgformula"
  where "Core_Init_RGCond  \<equiv> RG[\<lbrace>True\<rbrace>,UNIV,Id,\<lbrace>True\<rbrace>]"

definition Core_Init_RGF :: "Core \<Rightarrow> (EL, par list, Core, State) rgformula_e"
  where "Core_Init_RGF k \<equiv> (Core_Init k, Core_Init_RGCond)"



definition Schedule_RGCondC0 :: "(State) rgformula"
  where "Schedule_RGCondC0 \<equiv> 
   (RG[\<lbrace>True\<rbrace>,\<lbrace>\<ordfeminine>cur (c2s conf Core0) = \<ordmasculine>cur (c2s conf Core0)\<rbrace>,                              
       (\<lbrace>\<ordfeminine>schan= \<ordmasculine>schan
          \<and> (\<forall>c. c\<noteq> Core0 \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))\<rbrace>),
        \<lbrace>True\<rbrace>])"

definition Write_Sampling_Message_RGCondC0 :: "(State) rgformula"
  where "Write_Sampling_Message_RGCondC0 \<equiv> (
            RG[\<lbrace>True\<rbrace>,
            \<lbrace>\<ordfeminine>cur (c2s conf Core0)= \<ordmasculine>cur (c2s conf Core0)\<rbrace>,           
            \<lbrace>\<ordfeminine>cur= \<ordmasculine>cur \<and>
             (\<exists>ps. ((ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (\<ordmasculine>cur (gsch conf Core0))) \<longrightarrow>
                       (\<exists>!ch. ch =(ch_srcsampport conf (the (gPort (ps!0)))) \<and> 
                       (\<forall>ch'. (ch'\<noteq>ch \<longrightarrow> (\<ordfeminine>schan) ch' = (\<ordmasculine>schan) ch')))) \<and>
                   (\<not>(ps typeof [PORT,MSG]                              
                   \<and> is_src_sampport conf (the (gPort (ps!0)))          
                   \<and> port_of_part conf (the (gPort (ps!0))) (\<ordfeminine>cur (gsch conf Core0))) \<longrightarrow>
                   (\<ordfeminine>schan) = (\<ordmasculine>schan))) \<rbrace>,
            \<lbrace>True\<rbrace>])"

definition Read_Sampling_Message_RGCondC0 :: "(State) rgformula"
  where "Read_Sampling_Message_RGCondC0 \<equiv> 
     RG[\<lbrace>True\<rbrace>,
    \<lbrace>\<ordfeminine>cur (c2s conf Core0)= \<ordmasculine>cur (c2s conf Core0)\<rbrace>,
    \<lbrace>\<ordfeminine>cur= \<ordmasculine>cur \<and> \<ordfeminine>schan= \<ordmasculine>schan\<rbrace>,
    \<lbrace>True\<rbrace>]"


definition Schedule_RGFC0 :: "Core \<Rightarrow> (EL, par list, Core, State) rgformula_e"
  where "Schedule_RGFC0 k \<equiv> (Schedulek0 k, Schedule_RGCondC0 )"


definition Write_Sampling_Message_RGFC0 :: "(EL, par list, Core, State) rgformula_e"
  where "Write_Sampling_Message_RGFC0 \<equiv> ((Write_Sampling_Messagek0 Core0, Write_Sampling_Message_RGCondC0))"

definition Read_Sampling_Message_RGFC0 :: "(EL, par list, Core, State) rgformula_e"
  where "Read_Sampling_Message_RGFC0  \<equiv> (Read_Sampling_Messagek0 Core0, Read_Sampling_Message_RGCondC0)"



definition Schedule_RGCondC1 :: "(State) rgformula"
  where "Schedule_RGCondC1 \<equiv>(RG[\<lbrace>True\<rbrace>,\<lbrace>\<ordfeminine>cur (c2s conf Core1) = \<ordmasculine>cur (c2s conf Core1)\<rbrace>,                             
                              (\<lbrace>\<ordfeminine>schan= \<ordmasculine>schan \<and> 
                                 (\<forall>c. c\<noteq> Core1 \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))\<rbrace>),
                              \<lbrace>True\<rbrace>])"

definition Schedule_RGFC1 :: "Core \<Rightarrow> (EL, par list, Core, State) rgformula_e"
  where "Schedule_RGFC1 k \<equiv> (Schedulek1 k, Schedule_RGCondC1)"




definition Write_Sampling_Message_RGCondC1 :: "(State) rgformula"
  where "Write_Sampling_Message_RGCondC1 \<equiv> (
            RG[\<lbrace>True\<rbrace>,
            \<lbrace>\<ordfeminine>cur (c2s conf Core1)= \<ordmasculine>cur (c2s conf Core1)\<rbrace>,           
            \<lbrace> \<ordfeminine>cur= \<ordmasculine>cur \<and>
             (\<exists>ps. ((ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (\<ordmasculine>cur (gsch conf Core1))) \<longrightarrow>
                       (\<exists>!ch. ch =(ch_srcsampport conf (the (gPort (ps!0)))) \<and> 
                       (\<forall>ch'. (ch'\<noteq>ch \<longrightarrow> (\<ordfeminine>schan) ch' = (\<ordmasculine>schan) ch')))) \<and>
                   (\<not>(ps typeof [PORT,MSG]                              
                   \<and> is_src_sampport conf (the (gPort (ps!0)))          
                   \<and> port_of_part conf (the (gPort (ps!0))) (\<ordfeminine>cur (gsch conf Core1))) \<longrightarrow>
                   (\<ordfeminine>schan) = (\<ordmasculine>schan))) \<rbrace>,
            \<lbrace>True\<rbrace>])"

definition Write_Sampling_Message_RGFC1 :: "(EL, par list, Core, State) rgformula_e"
  where "Write_Sampling_Message_RGFC1 \<equiv> ((Write_Sampling_Messagek1 Core1, Write_Sampling_Message_RGCondC1))"


definition Read_Sampling_Message_RGCondC1 :: "(State) rgformula"
  where "Read_Sampling_Message_RGCondC1 \<equiv> 
     RG[\<lbrace>True\<rbrace>,
    \<lbrace>\<ordfeminine>cur (c2s conf Core1)= \<ordmasculine>cur (c2s conf Core1)\<rbrace>,
    \<lbrace>\<ordfeminine>cur= \<ordmasculine>cur \<and> \<ordfeminine>schan= \<ordmasculine>schan \<rbrace>,
    \<lbrace>True\<rbrace>]"

definition Read_Sampling_Message_RGFC1 :: "(EL, par list, Core, State) rgformula_e"
  where "Read_Sampling_Message_RGFC1 \<equiv> (Read_Sampling_Messagek1 Core1, Read_Sampling_Message_RGCondC1)"


definition EvtSys1_on_Core_RGFC1 :: "(EL, par list, Core, State) rgformula_es"
  where "EvtSys1_on_Core_RGFC1 \<equiv> (rgf_EvtSys ([Schedule_RGFC1 Core1 ,
                                              Write_Sampling_Message_RGFC1 ,
                                              Read_Sampling_Message_RGFC1]),
               RG[\<lbrace>True\<rbrace>,\<lbrace>\<ordfeminine>cur (c2s conf Core1)= \<ordmasculine>cur (c2s conf Core1)\<rbrace>,
                  (\<lbrace>(\<ordfeminine>cur= \<ordmasculine>cur \<or> (\<forall>c. c\<noteq> Core1 \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))) \<and>    
                     (\<ordfeminine>schan= \<ordmasculine>schan \<or> (\<exists>ps. ((ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (\<ordmasculine>cur (gsch conf Core1))) \<longrightarrow>
                       (\<exists>!ch. ch =(ch_srcsampport conf (the (gPort (ps!0)))) \<and> 
                       (\<forall>ch'. (ch'\<noteq>ch \<longrightarrow> (\<ordfeminine>schan) ch' = (\<ordmasculine>schan) ch')))) \<and>
                   (\<not>(ps typeof [PORT,MSG]                              
                   \<and> is_src_sampport conf (the (gPort (ps!0)))          
                   \<and> port_of_part conf (the (gPort (ps!0))) (\<ordfeminine>cur (gsch conf Core1))) \<longrightarrow>
                   (\<ordfeminine>schan) = (\<ordmasculine>schan)))) \<rbrace> ),
                  \<lbrace>True\<rbrace>])"

definition EvtSys1_on_Core_RGFC0 :: "(EL, par list, Core, State) rgformula_es"
  where "EvtSys1_on_Core_RGFC0 \<equiv> (rgf_EvtSys ([Schedule_RGFC0 Core0 ,
                                              Write_Sampling_Message_RGFC0,
                                              Read_Sampling_Message_RGFC0]),
               RG[\<lbrace>True\<rbrace>,\<lbrace>\<ordfeminine>cur (c2s conf Core0)= \<ordmasculine>cur (c2s conf Core0)\<rbrace>,
                  (\<lbrace>(\<ordfeminine>cur= \<ordmasculine>cur \<or> (\<forall>c. c\<noteq> Core0 \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))) \<and>    
                     (\<ordfeminine>schan= \<ordmasculine>schan \<or> (\<exists>ps. ((ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (\<ordmasculine>cur (gsch conf Core0))) \<longrightarrow>
                       (\<exists>!ch. ch =(ch_srcsampport conf (the (gPort (ps!0)))) \<and> 
                       (\<forall>ch'. (ch'\<noteq>ch \<longrightarrow> (\<ordfeminine>schan) ch' = (\<ordmasculine>schan) ch')))) \<and>
                   (\<not>(ps typeof [PORT,MSG]                              
                   \<and> is_src_sampport conf (the (gPort (ps!0)))          
                   \<and> port_of_part conf (the (gPort (ps!0))) (\<ordfeminine>cur (gsch conf Core0))) \<longrightarrow>
                   (\<ordfeminine>schan) = (\<ordmasculine>schan)))) \<rbrace> ),
                  \<lbrace>True\<rbrace>])"

definition EvtSys_on_Core_RGFC1 :: " (EL, par list, Core, State) rgformula_es"
  where "EvtSys_on_Core_RGFC1  \<equiv> 
          (rgf_EvtSeq (Core_Init_RGF Core1) (EvtSys1_on_Core_RGFC1),
            RG[\<lbrace>True\<rbrace>,\<lbrace>\<ordfeminine>cur (c2s conf Core1)= \<ordmasculine>cur (c2s conf Core1)\<rbrace>,
                  (\<lbrace>(\<ordfeminine>cur= \<ordmasculine>cur \<or> (\<forall>c. c\<noteq> Core1 \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))) \<and>    
                     (\<ordfeminine>schan= \<ordmasculine>schan \<or> (\<exists>ps. ((ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (\<ordmasculine>cur (gsch conf Core1))) \<longrightarrow>
                       (\<exists>!ch. ch =(ch_srcsampport conf (the (gPort (ps!0)))) \<and> 
                       (\<forall>ch'. (ch'\<noteq>ch \<longrightarrow> (\<ordfeminine>schan) ch' = (\<ordmasculine>schan) ch')))) \<and>
                   (\<not>(ps typeof [PORT,MSG]                              
                   \<and> is_src_sampport conf (the (gPort (ps!0)))          
                   \<and> port_of_part conf (the (gPort (ps!0))) (\<ordfeminine>cur (gsch conf Core1))) \<longrightarrow>
                   (\<ordfeminine>schan) = (\<ordmasculine>schan)))) \<rbrace> ),
                  \<lbrace>True\<rbrace>])"

definition EvtSys_on_Core_RGFC0 :: " (EL, par list, Core, State) rgformula_es"
  where "EvtSys_on_Core_RGFC0  \<equiv> 
          (rgf_EvtSeq (Core_Init_RGF Core0) (EvtSys1_on_Core_RGFC0),
          RG[\<lbrace>True\<rbrace>,\<lbrace>\<ordfeminine>cur (c2s conf Core0)= \<ordmasculine>cur (c2s conf Core0)\<rbrace>,
                  (\<lbrace>(\<ordfeminine>cur= \<ordmasculine>cur \<or> (\<forall>c. c\<noteq> Core0 \<longrightarrow> \<ordfeminine>cur (c2s conf c) = \<ordmasculine>cur  (c2s conf c))) \<and>    
                     (\<ordfeminine>schan= \<ordmasculine>schan \<or> (\<exists>ps. ((ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (\<ordmasculine>cur (gsch conf Core0))) \<longrightarrow>
                       (\<exists>!ch. ch =(ch_srcsampport conf (the (gPort (ps!0)))) \<and> 
                       (\<forall>ch'. (ch'\<noteq>ch \<longrightarrow> (\<ordfeminine>schan) ch' = (\<ordmasculine>schan) ch')))) \<and>
                   (\<not>(ps typeof [PORT,MSG]                              
                   \<and> is_src_sampport conf (the (gPort (ps!0)))          
                   \<and> port_of_part conf (the (gPort (ps!0))) (\<ordfeminine>cur (gsch conf Core0))) \<longrightarrow>
                   (\<ordfeminine>schan) = (\<ordmasculine>schan)))) \<rbrace> ),
                  \<lbrace>True\<rbrace>])"

definition ARINCXKernel_Spec :: "(EL, par list, Core, State) rgformula_par"
  where "ARINCXKernel_Spec \<equiv> (\<lambda>k. if k = Core0 then EvtSys_on_Core_RGFC0 
                                   else EvtSys_on_Core_RGFC1)"

axiomatization s0 where s0_init: "s0 \<equiv> fst (System_Init conf)"
axiomatization x0 where x0_init: "x0 \<equiv> snd (System_Init conf)"
axiomatization C0 where C0_init: "C0 = (paresys_spec ARINCXKernel_Spec, s0, x0)"

definition evtrgfs :: "(EL, par list, Core, State) event \<Rightarrow> (State rgformula) option"
  where "evtrgfs \<equiv> map_of [(Core_Init Core0, Core_Init_RGCond), 
                           (Schedulek0 Core0, Schedule_RGCondC0),
                           (Write_Sampling_Messagek0 Core0, Write_Sampling_Message_RGCondC0),
                           (Read_Sampling_Messagek0 Core0, Read_Sampling_Message_RGCondC0),                           
                           (Core_Init Core1, Core_Init_RGCond), 
                           (Schedulek1 Core1, Schedule_RGCondC1),
                           (Write_Sampling_Messagek1 Core1, Write_Sampling_Message_RGCondC1),
                           (Read_Sampling_Messagek1 Core1, Read_Sampling_Message_RGCondC1)]"

definition domevt :: "State \<Rightarrow> Core \<Rightarrow> (EL, par list, Core, State) event \<Rightarrow> Domain"
  where "domevt s k e \<equiv>  
                         (if e = Write_Sampling_Messagek0 k \<or>                             
                             e = Read_Sampling_Messagek0 k then
                              P ((cur s) (gsch conf Core0))
                         else if e = Write_Sampling_Messagek1 k \<or>                               
                             e = Read_Sampling_Messagek1 k then
                              P ((cur s) (gsch conf Core1))
                         else if e = Schedulek0 k then 
                             S (gsch conf Core0)
                         else if  e = Schedulek1 k then
                             S (gsch conf Core1)
                         else if e = Core_Init k then
                              S (gsch conf k)
                         else S (gsch conf k))"  (*for convenience, we also consider domain of other(undefined) event as the sched*)

definition exec_step :: "(EL, par list, Core, State, Domain) action 
      \<Rightarrow> ((EL, par list, Core, State) pesconf \<times> (EL, par list, Core, State) pesconf) set"
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

definition sub_fun_sta :: "('a\<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> ('a\<Rightarrow> 'b)"
where 
"sub_fun_sta f s c \<equiv>  (\<lambda>x. if x \<in> s then f x else c)"

definition state_obs_sched :: "State \<Rightarrow> Sched \<Rightarrow> State"
  where "state_obs_sched s d \<equiv> s0\<lparr>cur:=(cur s0) (d:=(cur s) d)\<rparr>"

definition schan_obs_part :: "State \<Rightarrow> Part \<Rightarrow> (SampChannel \<rightharpoonup> Message)"
  where "schan_obs_part s p \<equiv> (schan s) |` (par_sampchan conf p)  "

(* definition qchan_obs_part :: "State \<Rightarrow> Part \<Rightarrow> (QueChannel \<Rightarrow> Que)"
  where "qchan_obs_part s p \<equiv> sub_fun_sta (qchan s) (par_quechan conf p) {}" *)

(* definition qclock_obs_part ::"State \<Rightarrow> Part \<Rightarrow> (QueChannel \<Rightarrow> nat)"
 where "qclock_obs_part s p \<equiv> sub_fun_sta (qclock s) (par_quechan conf p) 0" *)

definition state_obs_part :: "State \<Rightarrow> Part \<Rightarrow> State" 
  where "state_obs_part s p \<equiv> s0\<lparr>schan:=schan_obs_part s p\<rparr>"



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
                                               
lemma all_basic_evts_arinc_help: "\<forall>k. ef\<in>all_evts_es (fst (ARINCXKernel_Spec k)) \<longrightarrow> is_basicevt (E\<^sub>e ef)"
  proof -
  {
    fix k
    assume p0: "ef\<in>all_evts_es (fst (ARINCXKernel_Spec k))"
    have "is_basicevt (E\<^sub>e ef)"  
    proof (cases k)
      assume a0:"k=Core0"
      then have "ef\<in>insert (Core_Init_RGF k) (all_evts_es (fst (EvtSys1_on_Core_RGFC0)))"
      using ARINCXKernel_Spec_def EvtSys_on_Core_RGFC0_def 
        all_evts_es_seq[of "Core_Init_RGF k" "EvtSys1_on_Core_RGFC0"] a0
        by (metis (no_types, lifting) fst_conv p0)        
      then have "ef = (Core_Init_RGF k) \<or> ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGFC0))" by auto
      then have "is_basicevt (E\<^sub>e ef)"
      proof
        assume a0: "ef = Core_Init_RGF k"
        then show ?thesis 
          using Core_Init_RGF_def Core_Init_def 
            by (metis E\<^sub>e_def fst_conv is_basicevt.simps(2)) 
       next
        assume a1: "ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGFC0))"
        then show ?thesis
          using all_evts_es_esys[of "[Schedule_RGFC0 k,
                                      Write_Sampling_Message_RGFC0,
                                      Read_Sampling_Message_RGFC0]"] 
            Schedule_RGFC0_def Schedulek0_def a0
            Write_Sampling_Message_RGFC0_def Write_Sampling_Messagek0_def
            Read_Sampling_Message_RGFC0_def Read_Sampling_Messagek0_def
            by (metis (no_types, lifting) E\<^sub>e_def EvtSys1_on_Core_RGFC0_def 
                empty_iff fst_conv insert_iff is_basicevt.simps(2) list.set(1) list.simps(15)) 
       qed
       thus ?thesis using a0 by auto
    next
      assume a0:"k=Core1"
      then have "ef\<in>insert (Core_Init_RGF k) (all_evts_es (fst (EvtSys1_on_Core_RGFC1)))"
      using ARINCXKernel_Spec_def EvtSys_on_Core_RGFC1_def 
        all_evts_es_seq[of "Core_Init_RGF k" "EvtSys1_on_Core_RGFC1"] a0
        by (metis (no_types, lifting) Core.distinct(1) fst_conv p0)        
      then have "ef = (Core_Init_RGF k) \<or> ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGFC1))" by auto
      then have "is_basicevt (E\<^sub>e ef)"
      proof
        assume a0: "ef = Core_Init_RGF k"
        then show ?thesis 
          using Core_Init_RGF_def Core_Init_def 
            by (metis E\<^sub>e_def fst_conv is_basicevt.simps(2)) 
       next
        assume a1: "ef\<in>all_evts_es (fst (EvtSys1_on_Core_RGFC1))"
        then show ?thesis
          using all_evts_es_esys[of "[Schedule_RGFC1 k,
                                      Write_Sampling_Message_RGFC1,
                                      Read_Sampling_Message_RGFC1]"] 
            Schedule_RGFC1_def Schedulek1_def a0
            Write_Sampling_Message_RGFC1_def Write_Sampling_Messagek1_def
            Read_Sampling_Message_RGFC1_def Read_Sampling_Messagek1_def            
              by (metis (no_types, lifting) E\<^sub>e_def EvtSys1_on_Core_RGFC1_def 
                empty_iff fst_conv insert_iff is_basicevt.simps(2) list.set(1) list.simps(15)) 
       qed
       thus ?thesis using a0 by auto
   qed
  }
  then show ?thesis by auto
qed

lemma all_basic_evts_arinc: "\<forall>ef\<in>all_evts ARINCXKernel_Spec. is_basicevt (E\<^sub>e ef)" 
  using all_evts_def[of ARINCXKernel_Spec] all_basic_evts_arinc_help by auto


lemma bsc_evts_rgfs_help: 
  "\<forall>k erg. erg\<in>all_evts_es (fst (ARINCXKernel_Spec k)) \<longrightarrow> the (evtrgfs (E\<^sub>e erg))  = (snd erg)"
  proof -
  {
    fix k erg
    assume p0: "erg\<in>all_evts_es (fst (ARINCXKernel_Spec k))"
    have "the (evtrgfs (E\<^sub>e erg))  = (snd erg)"
    proof (cases k)
      assume k:"k=Core0"
      then have "erg\<in>insert (Core_Init_RGF k) (all_evts_es (fst (EvtSys1_on_Core_RGFC0)))"
      using ARINCXKernel_Spec_def EvtSys_on_Core_RGFC0_def 
        all_evts_es_seq[of "Core_Init_RGF k" "EvtSys1_on_Core_RGFC0"]
        by (metis (no_types, lifting) fst_conv p0)        
      then have "erg = (Core_Init_RGF k) \<or> erg\<in>all_evts_es (fst (EvtSys1_on_Core_RGFC0))" by auto
      then show ?thesis
      proof
        assume a0: "erg = Core_Init_RGF k"
        have "evtrgfs (Core_Init k) = Some Core_Init_RGCond"
          by (simp add: k evtrgfs_def)               
        with a0 show ?thesis 
          using Core_Init_RGF_def E\<^sub>e_def
            by (metis fst_conv option.sel snd_conv) 
      next
        assume a0: "erg\<in>all_evts_es (fst (EvtSys1_on_Core_RGFC0))"
        moreover
        have "all_evts_es (fst (EvtSys1_on_Core_RGFC0)) = {Schedule_RGFC0 k,
                                      Write_Sampling_Message_RGFC0,
                                      Read_Sampling_Message_RGFC0}"
          using all_evts_es_esys by (simp add: k EvtSys1_on_Core_RGFC0_def) 
        moreover
        have "evtrgfs (Schedulek0 k) = Some Schedule_RGCondC0"           
          unfolding  evtrgfs_def Schedulek0_def Core_Init_def k
          by auto
        moreover
        have "evtrgfs (Write_Sampling_Messagek0 k) = Some (Write_Sampling_Message_RGCondC0)"          
          by (simp add: k Write_Sampling_Messagek0_def Core_Init_def Schedulek0_def evtrgfs_def)
        moreover
        have "evtrgfs (Read_Sampling_Messagek0 k) = Some Read_Sampling_Message_RGCondC0"
          by (simp add: k Write_Sampling_Messagek0_def Core_Init_def Schedulek0_def 
                        Read_Sampling_Messagek0_def evtrgfs_def)           
        ultimately show ?thesis
          by (smt k E\<^sub>e_def  
              Read_Sampling_Message_RGFC0_def  Schedule_RGCondC0_def 
              Schedule_RGFC0_def Write_Sampling_Message_RGFC0_def
              fst_conv insert_iff option.sel singletonD snd_conv)
      qed
  next
      assume k:"k=Core1"
      then have "erg\<in>insert (Core_Init_RGF k) (all_evts_es (fst (EvtSys1_on_Core_RGFC1)))"
      using ARINCXKernel_Spec_def EvtSys_on_Core_RGFC0_def 
        all_evts_es_seq[of "Core_Init_RGF k" "EvtSys1_on_Core_RGFC1"]
       by (metis (no_types, lifting) Core.distinct(1) EvtSys_on_Core_RGFC1_def fst_conv p0)        
      then have "erg = (Core_Init_RGF k) \<or> erg\<in>all_evts_es (fst (EvtSys1_on_Core_RGFC1))" by auto
      then show ?thesis
      proof
        assume a0: "erg = Core_Init_RGF k"
        have "evtrgfs (Core_Init k) = Some Core_Init_RGCond"
          unfolding evtrgfs_def using k
          by (simp add: Core_Init_def)                                 
        with a0 show ?thesis 
          using Core_Init_RGF_def E\<^sub>e_def
            by (metis fst_conv option.sel snd_conv) 
      next
        assume a0: "erg\<in>all_evts_es (fst (EvtSys1_on_Core_RGFC1))"
        moreover
        have "all_evts_es (fst (EvtSys1_on_Core_RGFC1)) = {Schedule_RGFC1 k,
                                      Write_Sampling_Message_RGFC1,
                                      Read_Sampling_Message_RGFC1}"
          using all_evts_es_esys by (simp add: k EvtSys1_on_Core_RGFC1_def) 
        moreover
        have "evtrgfs (Schedulek1 k) = Some Schedule_RGCondC1"   
          using k        
          unfolding  Write_Sampling_Messagek0_def  Core_Init_def Schedulek0_def Schedulek1_def
                     Read_Sampling_Messagek0_def  evtrgfs_def Schedule_RGCondC1_def Schedule_RGCondC0_def
          by auto
        moreover
        have "evtrgfs (Write_Sampling_Messagek1 k) = Some (Write_Sampling_Message_RGCondC1)" 
          using k 
          unfolding evtrgfs_def getrgformula_def
                    Write_Sampling_Messagek0_def Write_Sampling_Messagek1_def  Core_Init_def 
                    Schedulek0_def Schedulek1_def
                    Read_Sampling_Messagek0_def   
          by auto
        moreover
        have "evtrgfs (Read_Sampling_Messagek1 k) = Some Read_Sampling_Message_RGCondC1"
         using k 
          unfolding evtrgfs_def getrgformula_def  Schedulek0_def  Schedulek1_def
                    Write_Sampling_Messagek0_def Write_Sampling_Messagek1_def  Core_Init_def 
                    Read_Sampling_Messagek0_def Read_Sampling_Messagek1_def
         by auto  
                  
        ultimately show ?thesis         
          by (smt k E\<^sub>e_def  
              Read_Sampling_Message_RGFC1_def   
               Schedule_RGCondC1_def 
              Schedule_RGFC1_def  Write_Sampling_Message_RGFC1_def
              fst_conv insert_iff option.sel singletonD snd_conv)
      qed
  qed
  }
  then show ?thesis by auto
  qed

lemma bsc_evts_rgfs: "\<forall>erg\<in>all_evts (ARINCXKernel_Spec). the (evtrgfs (E\<^sub>e erg))   = snd erg"
  using all_evts_def[of ARINCXKernel_Spec] bsc_evts_rgfs_help  by auto

definition Evt_sat_RG:: "(EL, par list, Core, State) event \<Rightarrow> (State) rgformula \<Rightarrow> bool" ("(_\<turnstile>_)" [60,60] 61)
  where "Evt_sat_RG e rg \<equiv> \<turnstile> e sat\<^sub>e [Pre\<^sub>f rg, Rely\<^sub>f rg, Guar\<^sub>f rg, Post\<^sub>f rg]"


(*lemma "\<turnstile> Core_Init sat\<^sub>e [Pre\<^sub>f Core_Init_RGCond, Rely\<^sub>f Core_Init_RGCond, Guar\<^sub>f Core_Init_RGCond, Post\<^sub>f Core_Init_RGCond]"*)
lemma Core_Init_SatRG: "\<forall>k. Core_Init k \<turnstile> Core_Init_RGCond"
  apply(simp add:Evt_sat_RG_def)
  apply(simp add:Core_Init_def)
  apply(rule BasicEvt)
    apply(simp add:get_evtp_def Skip_def)
    apply(rule allI)+
    apply(rule Basic)
    apply(simp add:get_evtg_def) 
    apply(simp add:Core_Init_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def getrgformula_def) 
    apply(simp add:Core_Init_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def getrgformula_def get_evtg_def)
    apply auto[1] 
  apply(simp add:Core_Init_RGCond_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def Rely\<^sub>f_def getrgformula_def get_evtg_def stable_def)
  apply(simp add:Core_Init_RGCond_def Post\<^sub>f_def Rely\<^sub>f_def getrgformula_def stable_def)
  apply(simp add:stable_def Core_Init_RGCond_def getrgformula_def Pre\<^sub>f_def)
  apply(simp add:Core_Init_RGCond_def Guar\<^sub>f_def getrgformula_def stable_def)
  done
  
lemma Schedk0_SatRG: "\<forall>k. Schedulek0 k \<turnstile> Schedule_RGCondC0"
  apply(simp add:Evt_sat_RG_def Schedulek0_def)  
  apply(rule BasicEvt)
  apply(simp add:get_evtp_def get_evtg_def)
  apply(rule allI)+
  apply(rule conjI)
  apply(rule impI)  
  apply(rule Basic)      
  using bij_c2s apply (auto simp add:injD Schedule_RGCondC0_def Guar\<^sub>f_def Pre\<^sub>f_def getrgformula_def Post\<^sub>f_def)[2]
  using bij_is_inj range_ex1_eq apply fastforce  
  apply(simp add:stable_def Schedule_RGCondC0_def getrgformula_def Rely\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def)+  
  apply(rule impI)
  apply(rule Basic)  
  apply(simp add:Schedule_RGCondC0_def Guar\<^sub>f_def Pre\<^sub>f_def getrgformula_def)+
  apply blast
  by (simp add:stable_def Schedule_RGCondC0_def getrgformula_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def)+

lemma Schedk1_SatRG: "\<forall>k. Schedulek1 k \<turnstile> Schedule_RGCondC1"
  apply(simp add:Evt_sat_RG_def Schedulek1_def)  
  apply(rule BasicEvt)
  apply(simp add:get_evtp_def get_evtg_def)
  apply(rule allI)+
  apply(rule conjI)
  apply(rule impI)  
  apply(rule Basic)    
  using bij_c2s apply (auto simp add:injD Schedule_RGCondC1_def Guar\<^sub>f_def Pre\<^sub>f_def getrgformula_def Post\<^sub>f_def)[2]    
  using bij_is_inj range_ex1_eq apply fastforce
  apply(simp add:stable_def Schedule_RGCondC1_def getrgformula_def Rely\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def)+  
  apply(rule impI)
  apply(rule Basic)  
  apply(simp add:Schedule_RGCondC1_def Guar\<^sub>f_def Pre\<^sub>f_def getrgformula_def)+
  apply blast
  by(simp add:stable_def Schedule_RGCondC1_def getrgformula_def Pre\<^sub>f_def Post\<^sub>f_def Guar\<^sub>f_def)+ 


lemma Writek1_SatRG: "\<forall>k. Write_Sampling_Messagek1 k \<turnstile> Write_Sampling_Message_RGCondC1"
  apply(simp add:Evt_sat_RG_def)
  apply(rule allI)+ 
  apply(simp add:Write_Sampling_Messagek1_def)
  apply(rule BasicEvt)
  apply(simp add:get_evtp_def get_evtg_def)
  apply(rule allI)+ 
  apply (simp add: Write_Sampling_Message_RGCondC1_def getrgformula_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def)
  apply (rule Basic)
  apply auto     
by  (simp add:stable_def gsch_def Write_Sampling_Message_RGCondC1_def 
             getrgformula_def Guar\<^sub>f_def  Pre\<^sub>f_def Rely\<^sub>f_def)+
  
lemma Writek0_SatRG: "\<forall>k. Write_Sampling_Messagek0 k \<turnstile> Write_Sampling_Message_RGCondC0"
  apply(simp add:Evt_sat_RG_def)
  apply(rule allI)+ 
  apply(simp add:Write_Sampling_Messagek0_def)
  apply(rule BasicEvt)
  apply(simp add:get_evtp_def get_evtg_def)
  apply(rule allI)+ 
  apply (simp add: Write_Sampling_Message_RGCondC0_def getrgformula_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def)
  apply (rule Basic)
  apply auto     
by  (simp add:stable_def gsch_def Write_Sampling_Message_RGCondC0_def 
             getrgformula_def Guar\<^sub>f_def  Pre\<^sub>f_def Rely\<^sub>f_def)+
  
lemma Readk0_SatRG: "\<forall>k. Read_Sampling_Messagek0 k \<turnstile> Read_Sampling_Message_RGCondC0"
  apply(simp add:Evt_sat_RG_def)
  apply(rule allI)+ 
  apply(simp add:Read_Sampling_Messagek0_def)
  apply(rule BasicEvt)
  apply(simp add:get_evtp_def get_evtg_def)
  apply(rule allI)+ 
  apply (simp add: Read_Sampling_Message_RGCondC0_def getrgformula_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def Skip_def)   
  apply (rule Basic)
  apply auto     
by  (simp add:stable_def gsch_def Read_Sampling_Message_RGCondC0_def 
             getrgformula_def Guar\<^sub>f_def  Pre\<^sub>f_def Rely\<^sub>f_def)+

lemma Readk1_SatRG: "\<forall>k. Read_Sampling_Messagek1 k \<turnstile> Read_Sampling_Message_RGCondC1"
  apply(simp add:Evt_sat_RG_def)
  apply(rule allI)+ 
  apply(simp add:Read_Sampling_Messagek1_def)
  apply(rule BasicEvt)
  apply(simp add:get_evtp_def get_evtg_def)
  apply(rule allI)+ 
  apply (simp add: Read_Sampling_Message_RGCondC0_def getrgformula_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def Skip_def)   
  apply (rule Basic)
  apply auto     
by  (simp add:stable_def gsch_def Read_Sampling_Message_RGCondC1_def 
             getrgformula_def Guar\<^sub>f_def  Pre\<^sub>f_def Rely\<^sub>f_def)+

lemma Readk0_SatRG1:"\<forall>i<length [Schedule_RGFC0 Core0, Write_Sampling_Message_RGFC0, Read_Sampling_Message_RGFC0].
       \<turnstile> E\<^sub>e ([Schedule_RGFC0 Core0, Write_Sampling_Message_RGFC0, Read_Sampling_Message_RGFC0] !
               i) sat\<^sub>e [Pre\<^sub>e ([Schedule_RGFC0 Core0, Write_Sampling_Message_RGFC0,
                                 Read_Sampling_Message_RGFC0] !
                                i), Rely\<^sub>e
                                     ([Schedule_RGFC0 Core0, Write_Sampling_Message_RGFC0,
                                       Read_Sampling_Message_RGFC0] !
                                      i), Guar\<^sub>e
                                           ([Schedule_RGFC0 Core0, Write_Sampling_Message_RGFC0,
                                             Read_Sampling_Message_RGFC0] !
                                            i), Post\<^sub>e
                                                 ([Schedule_RGFC0 Core0, Write_Sampling_Message_RGFC0,
Read_Sampling_Message_RGFC0] !
                                                  i)]"
unfolding E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def 
    Schedule_RGFC0_def Write_Sampling_Message_RGFC0_def Read_Sampling_Message_RGFC0_def
    using Schedk0_SatRG Writek0_SatRG Readk0_SatRG unfolding Evt_sat_RG_def 
      Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def using less_Suc_eq_0_disj by auto  




lemma sat_s_0:" \<turnstile> fst EvtSys1_on_Core_RGFC0 sat\<^sub>s 
              [Pre\<^sub>f (snd EvtSys1_on_Core_RGFC0), 
               Rely\<^sub>f (snd EvtSys1_on_Core_RGFC0), 
               Guar\<^sub>f (snd EvtSys1_on_Core_RGFC0), Post\<^sub>f (snd EvtSys1_on_Core_RGFC0)]"
  apply (simp add:EvtSys1_on_Core_RGFC0_def)
  apply (rule EvtSys_h)
  apply (simp add: Readk0_SatRG1)
  
  unfolding getrgformula_def Pre\<^sub>f_def Pre\<^sub>e_def Schedule_RGFC0_def Rely\<^sub>f_def Rely\<^sub>e_def 
    Guar\<^sub>f_def Guar\<^sub>e_def Post\<^sub>f_def Post\<^sub>e_def
    Schedule_RGCondC0_def Write_Sampling_Message_RGFC0_def Write_Sampling_Message_RGCondC0_def 
    Read_Sampling_Message_RGFC0_def Read_Sampling_Message_RGCondC0_def 
    using less_Suc_eq_0_disj list.size(3) mem_Collect_eq nth_Cons' 
         rgformula.select_convs(1,2) set_eq_subset snd_conv top_set_def 
    apply fastforce
    apply (fastforce simp add:less_Suc_eq )+
by(auto simp add:stable_def)


lemma Readk1_SatRG1:"\<forall>i<length [Schedule_RGFC1 Core1, Write_Sampling_Message_RGFC1, Read_Sampling_Message_RGFC1].
       \<turnstile> E\<^sub>e ([Schedule_RGFC1 Core1, Write_Sampling_Message_RGFC1, Read_Sampling_Message_RGFC1] !
               i) sat\<^sub>e [Pre\<^sub>e ([Schedule_RGFC1 Core1, Write_Sampling_Message_RGFC1, Read_Sampling_Message_RGFC1] !
                                i), Rely\<^sub>e ([Schedule_RGFC1 Core1, Write_Sampling_Message_RGFC1, Read_Sampling_Message_RGFC1] !
                                            i), Guar\<^sub>e ([Schedule_RGFC1 Core1, Write_Sampling_Message_RGFC1, Read_Sampling_Message_RGFC1] !
                                                        i), Post\<^sub>e ([Schedule_RGFC1 Core1, Write_Sampling_Message_RGFC1,
                                                                     Read_Sampling_Message_RGFC1] !
                                                                    i)]"
  unfolding E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def 
    Schedule_RGFC1_def Write_Sampling_Message_RGFC1_def Read_Sampling_Message_RGFC1_def
    using Schedk1_SatRG Writek1_SatRG Readk1_SatRG unfolding Evt_sat_RG_def 
      Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def
using less_Suc_eq_0_disj by auto

                                            
lemma sat_s_1: "\<turnstile> fst EvtSys1_on_Core_RGFC1 sat\<^sub>s [Pre\<^sub>f (snd
  EvtSys1_on_Core_RGFC1), Rely\<^sub>f
                           (snd EvtSys1_on_Core_RGFC1), Guar\<^sub>f
      (snd EvtSys1_on_Core_RGFC1), Post\<^sub>f (snd EvtSys1_on_Core_RGFC1)]"
apply (simp add:EvtSys1_on_Core_RGFC1_def)
  apply (rule EvtSys_h)
  apply (simp add: Readk1_SatRG1)
  
  unfolding getrgformula_def Pre\<^sub>f_def Pre\<^sub>e_def Schedule_RGFC1_def Rely\<^sub>f_def Rely\<^sub>e_def 
    Guar\<^sub>f_def Guar\<^sub>e_def Post\<^sub>f_def Post\<^sub>e_def
    Schedule_RGCondC1_def Write_Sampling_Message_RGFC1_def Write_Sampling_Message_RGCondC1_def 
    Read_Sampling_Message_RGFC1_def Read_Sampling_Message_RGCondC1_def 
    using less_Suc_eq_0_disj list.size(3) mem_Collect_eq nth_Cons' 
         rgformula.select_convs(1,2) set_eq_subset snd_conv top_set_def 
  apply fastforce
  apply (fastforce simp add:less_Suc_eq )+
by(auto simp add:stable_def)

lemma spec_sat_rg: "\<turnstile> ARINCXKernel_Spec SAT [{s0}, {}, UNIV, UNIV]"
  apply (rule ParallelESys)
  prefer 5
  apply simp
  prefer 5
  apply simp
  apply (rule allI)+
  apply (case_tac "k=Core0")
  apply (auto simp add: ARINCXKernel_Spec_def EvtSys_on_Core_RGFC0_def EvtSys_on_Core_RGFC1_def)
  apply (rule EvtSeq_h)
  using Core_Init_SatRG Evt_sat_RG_def Core_Init_RGF_def
    Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def
  apply (metis E\<^sub>e_def Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def fst_conv snd_conv)
  apply (simp add:sat_s_0)
  unfolding Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def getrgformula_def Core_Init_RGF_def Core_Init_RGCond_def 
    apply auto[1]
  unfolding Post\<^sub>e\<^sub>s_def Post\<^sub>f_def EvtSys1_on_Core_RGFC0_def getrgformula_def apply auto[1]
  unfolding Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def  getrgformula_def apply auto[1]
  unfolding Rely\<^sub>f_def apply auto[1]
  unfolding Guar\<^sub>e_def Guar\<^sub>e\<^sub>s_def apply auto[1]
  unfolding Guar\<^sub>f_def apply auto[1]
  unfolding Post\<^sub>e_def Pre\<^sub>f_def apply auto[1]
  apply (subgoal_tac "k=Core1")
  prefer 2 using Core.exhaust apply auto[1] 
  apply (rule EvtSeq_h)
  using Core_Init_SatRG Evt_sat_RG_def Core_Init_RGF_def
    Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def
  apply (metis Core_Init_RGCond_def E\<^sub>e_def Guar\<^sub>f_def Post\<^sub>f_def Pre\<^sub>f_def Rely\<^sub>f_def fst_conv getrgformula_def snd_conv)
  apply (simp add:sat_s_1)
  unfolding Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def getrgformula_def Core_Init_RGF_def Core_Init_RGCond_def 
    apply auto[1]
  unfolding Post\<^sub>e\<^sub>s_def Post\<^sub>f_def EvtSys1_on_Core_RGFC1_def getrgformula_def apply auto[1]
  unfolding Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def  getrgformula_def apply auto[1]
  unfolding Rely\<^sub>f_def apply auto[1]
  unfolding Guar\<^sub>e_def Guar\<^sub>e\<^sub>s_def apply auto[1]
  unfolding Guar\<^sub>f_def apply auto[1]
  unfolding Post\<^sub>e_def Pre\<^sub>f_def apply auto[1]
  using bij_c2s apply auto
  by (metis (full_types) Core.exhaust)+
  
  
 

interpretation RG_InfoFlow C0 exec_step interf state_equiv state_obs domevt 
  ARINCXKernel_Spec s0 x0 evtrgfs "paresys_spec ARINCXKernel_Spec"
    using state_equiv_transitive state_equiv_reflexive state_equiv_symmetric exec_step_def 
      C0_init all_basic_evts_arinc bsc_evts_rgfs spec_sat_rg
    InfoFlow.intro[of state_equiv exec_step domevt]
    RG_InfoFlow.intro[of exec_step state_equiv domevt C0 ARINCXKernel_Spec 
                        s0 x0 evtrgfs "paresys_spec ARINCXKernel_Spec"]
    RG_InfoFlow_axioms.intro[of C0 ARINCXKernel_Spec s0 x0 "paresys_spec ARINCXKernel_Spec" evtrgfs] 
      by blast

lemma Core_Init_sat_LRE: 
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f Core_Init_RGCond 
                \<longrightarrow> ((domevt s1 k (Core_Init k)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
proof -
  {fix u s1 s2 k
  assume a0:"(s1,s2) \<in> Guar\<^sub>f Core_Init_RGCond"
  then have "s1 = s2" 
    unfolding Core_Init_RGCond_def Guar\<^sub>f_def getrgformula_def Id_def by auto
  then have "s1 \<sim>u\<sim> s2" unfolding state_equiv_def by auto
  } 
  thus ?thesis by auto
qed  
 
lemma schedulers: 
 assumes a0:"u=S d" and
         a1:"S ((c2s conf) k) \<noteq> u"
 shows "\<exists>!k1. d=((c2s conf) k1) \<and> k1\<noteq>k"
using bij_c2s a0 a1
by (metis bij_pointE)

lemma Schedule0_sat_LRE: 
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f Schedule_RGCondC0
                \<longrightarrow> ((domevt s1 k (Schedulek0 k)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
proof-
  {fix u s1 s2 k
   assume a0:"(s1,s2) \<in> Guar\<^sub>f Schedule_RGCondC0" and
          a1:"(domevt s1 k (Schedulek0 k)) \<setminus>\<leadsto> u"     
   then have eq:"schan s1 = schan s2 \<and>
                (cur s1 (c2s conf Core1) = cur s2  (c2s conf Core1))"
   using a0 unfolding Schedule_RGCondC0_def Guar\<^sub>f_def getrgformula_def Id_def by auto
   have "domevt s1 k (Schedulek0 k) = S ((c2s conf) Core0)" 
     unfolding domevt_def gsch_def Schedulek0_def  Read_Sampling_Messagek1_def
               Write_Sampling_Messagek0_def Write_Sampling_Messagek1_def Read_Sampling_Messagek0_def
     by auto
   then have non_inter:"S ((c2s conf) Core0)\<noteq> u \<and> 
              \<not>(part_on_core conf u (S ((c2s conf) Core0)) ) \<and> 
              \<not>ch_conn2 conf (S ((c2s conf) Core0)) u" 
     using a1 unfolding noninterf1_def interf_def
     by presburger
   then have "(\<exists>d1. u = S d1) \<or> (\<exists>d1. u=P d1 \<and> (c2s conf) Core0 \<notin> ((p2s conf) d1))"
   using non_inter part_on_core.simps
     by (metis Domain.simps(6) Domain.exhaust)    
   then have "s1 \<sim>u\<sim> s2" 
   proof
     assume "(\<exists>d1. u = S d1)" 
     then obtain d1 where a0:"u=S d1" by auto
     then have "\<exists>!k1. d1=((c2s conf) k1) \<and> k1\<noteq>Core0"
       using schedulers non_inter by auto
     then have u:"u=S ((c2s conf) Core1)" using  a0 Core.exhaust by auto
     thus ?thesis using eq unfolding state_equiv_def using state_obs_sched_def 
       by auto
   next 
     assume "(\<exists>d1. u=P d1 \<and> (c2s conf) Core0 \<notin> ((p2s conf) d1))"
     then obtain d1 where a0:"u=P d1 \<and> (c2s conf) Core0 \<notin> ((p2s conf) d1)" by auto
     then have "state_obs_part s1 d1 = state_obs_part s2 d1" 
       unfolding state_obs_part_def schan_obs_part_def 
       using eq by auto
     thus ?thesis  using a0
        unfolding state_equiv_def by auto        
   qed
  } thus ?thesis by auto
qed

lemma Schedule1_sat_LRE:           
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f Schedule_RGCondC1
                \<longrightarrow> ((domevt s1 k (Schedulek1 k)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
proof-
  {fix u s1 s2 k
   assume a0:"(s1,s2) \<in> Guar\<^sub>f Schedule_RGCondC1" and
          a1:"(domevt s1 k (Schedulek1 k)) \<setminus>\<leadsto> u"     
   then have eq:"schan s1 = schan s2 \<and>
                (cur s1 (c2s conf Core0) = cur s2  (c2s conf Core0))"
   using a0 unfolding Schedule_RGCondC1_def Guar\<^sub>f_def getrgformula_def Id_def by auto
   have "domevt s1 k (Schedulek1 k) = S ((c2s conf) Core1)" 
     unfolding domevt_def gsch_def Schedulek1_def  Read_Sampling_Messagek0_def
               Write_Sampling_Messagek1_def Write_Sampling_Messagek0_def Read_Sampling_Messagek1_def
              Schedulek0_def
     by auto
   then have non_inter:"S ((c2s conf) Core1)\<noteq> u \<and> 
              \<not>(part_on_core conf u (S ((c2s conf) Core1)) ) \<and> 
              \<not>ch_conn2 conf (S ((c2s conf) Core1)) u" 
     using a1 unfolding noninterf1_def interf_def
     by presburger
   then have "(\<exists>d1. u = S d1) \<or> (\<exists>d1. u=P d1 \<and> (c2s conf) Core1 \<notin> ((p2s conf) d1))"
   using non_inter part_on_core.simps
     by (metis Domain.simps(6) Domain.exhaust)    
   then have "s1 \<sim>u\<sim> s2" 
   proof
     assume "(\<exists>d1. u = S d1)" 
     then obtain d1 where a0:"u=S d1" by auto
     then have "\<exists>!k1. d1=((c2s conf) k1) \<and> k1\<noteq>Core1"
       using schedulers non_inter by auto
     then have u:"u=S ((c2s conf) Core0)" using  a0 Core.exhaust by auto
     thus ?thesis using eq unfolding state_equiv_def using state_obs_sched_def 
       by auto
   next 
     assume "(\<exists>d1. u=P d1 \<and> (c2s conf) Core1 \<notin> ((p2s conf) d1))"
     then obtain d1 where a0:"u=P d1 \<and> (c2s conf) Core1 \<notin> ((p2s conf) d1)" by auto
     then have "state_obs_part s1 d1 = state_obs_part s2 d1" 
       unfolding state_obs_part_def schan_obs_part_def 
       using eq by auto
     thus ?thesis  using a0
        unfolding state_equiv_def by auto        
   qed
  } thus ?thesis by auto
qed

lemma Read_Sampling_Message0_sat_LRE: 
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC0 
                \<longrightarrow> ((domevt s1 k (Read_Sampling_Messagek0 k)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
proof-
 {fix u s1 s2 k
  assume a0:"(s1,s2) \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC0" and
         a1:"(domevt s1 k (Read_Sampling_Messagek0 k)) \<setminus>\<leadsto> u"
  have "s1=s2" 
  using a0 unfolding Read_Sampling_Message_RGCondC0_def Guar\<^sub>f_def getrgformula_def
    by auto
  then  have "s1 \<sim>u\<sim> s2" 
    unfolding state_equiv_def by auto
 } thus ?thesis by auto
qed
  

lemma Read_Sampling_Message1_sat_LRE: 
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC1 
                \<longrightarrow> ((domevt s1 k (Read_Sampling_Messagek1 k)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
proof-
 {fix u s1 s2 k
  assume a0:"(s1,s2) \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC1" and
         a1:"(domevt s1 k (Read_Sampling_Messagek1 k)) \<setminus>\<leadsto> u"
  have "s1=s2" 
  using a0 unfolding Read_Sampling_Message_RGCondC1_def Guar\<^sub>f_def getrgformula_def
    by auto
  then  have "s1 \<sim>u\<sim> s2" 
    unfolding state_equiv_def by auto
 } thus ?thesis by auto
qed

lemma Write_Sampling_Message1_sat_LRE: 
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f Write_Sampling_Message_RGCondC0 
                \<longrightarrow> ((domevt s1 k (Write_Sampling_Messagek0 k)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
proof-
  {fix u s1 s2 k
   assume a0:"(s1,s2) \<in> Guar\<^sub>f Write_Sampling_Message_RGCondC0" and
         a1:"(domevt s1 k (Write_Sampling_Messagek0 k)) \<setminus>\<leadsto> u"
   then obtain ps where eq:"cur s2= cur s1 \<and>
                 (((ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (cur s1 (gsch conf Core0))) \<longrightarrow>
                       (\<exists>!ch. ch =(ch_srcsampport conf (the (gPort (ps!0)))) \<and> 
                       (\<forall>ch'. (ch'\<noteq>ch \<longrightarrow> (schan s2) ch' = (schan s1) ch')))) \<and>
                   (\<not>(ps typeof [PORT,MSG]                              
                   \<and> is_src_sampport conf (the (gPort (ps!0)))          
                   \<and> port_of_part conf (the (gPort (ps!0))) (cur s2 (gsch conf Core0))) \<longrightarrow>
                   (schan s2) = (schan s1)))"
    using a0 unfolding Write_Sampling_Message_RGCondC0_def Guar\<^sub>f_def getrgformula_def  
     by auto
   then have "s1 \<sim>u\<sim> s2"
   proof -
     {assume pre_cond:"(ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (cur s1 (gsch conf Core0)))"      
      then obtain p where ps0_pt:"(the (gPort (ps!0))) = p" 
        using MT_Pt typeof_MT by fastforce
      then have pre_cond:
        "(ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf p \<and> 
                     port_of_part conf p (cur s1 (gsch conf Core0)))"
        using pre_cond by auto
      have "domevt s1 k (Write_Sampling_Messagek0 k) = P ((cur s1) (c2s conf Core0))"
      unfolding domevt_def gsch_def Schedulek0_def  Read_Sampling_Messagek1_def
               Write_Sampling_Messagek0_def Write_Sampling_Messagek1_def Read_Sampling_Messagek0_def
        by auto
      then have non_inter:"P ((cur s1) (c2s conf Core0))\<noteq> u \<and> 
              \<not>(part_on_core conf u (P ((cur s1) (c2s conf Core0)) )) \<and> 
              \<not>ch_conn2 conf (P ((cur s1) (c2s conf Core0))) u" 
      using a1 unfolding noninterf1_def interf_def
        by presburger    
      then have "(\<exists>d1. u = S d1) \<or> (\<exists>d1. u=P d1)"
        using non_inter part_on_core.simps
        by (metis Domain.exhaust)             
      then have ?thesis
      proof
        assume "\<exists>d1. u = S d1"
        thus ?thesis using eq 
          unfolding state_equiv_def using state_obs_sched_def by auto
      next
        assume u:"\<exists>d1. u=P d1"
        then obtain d1 where u:"u=P d1" by auto
        then have d1_not_cur_core:"d1 \<noteq> ((cur s1) (c2s conf Core0))" 
          using non_inter by auto
        then have "(\<exists>d1. u= S d1) \<or>  \<not>ch_conn conf ((cur s1) (c2s conf Core0)) d1"  
          using non_inter u a0 ch_conn2.simps by auto
        thus ?thesis
        proof
          assume "\<exists>d1. u = S d1" thus ?thesis using u by auto
        next
          assume a0:"\<not>ch_conn conf ((cur s1) (c2s conf Core0)) d1"       
          then have a0:"(\<forall>sch p. (p2p conf (scsrc conf sch) = cur s1 (c2s conf Core0)) \<longrightarrow> 
                  \<not>(p \<in> scdests conf sch \<and> p2p conf p = d1))"
            unfolding ch_conn_def
            by auto
          obtain ch  where 
            eq_schan:"ch =(ch_srcsampport conf p) \<and>  
            (\<forall>ch'. (ch'\<noteq>ch \<longrightarrow> (schan s2) ch' = (schan s1) ch'))"
              using eq pre_cond ps0_pt by auto
          have "ch \<notin>(par_sampchan conf d1)" 
          proof 
            assume ch_par:"ch \<in> (par_sampchan conf d1)"
            then have "ch \<in> (ch_srcsampport conf) ` (par_src_sampling_ports conf (par_ports conf d1)) \<or>
                    ch \<in> (ch_destsampport conf) `(par_dest_sampling_ports conf (par_ports conf d1))"
              using a0 unfolding par_sampchan_def by auto            
            then show False
              unfolding par_sampchan_def ch_srcsampport_def
              using  a0 d1_not_cur_core pre_cond eq_schan ps0_pt ch_par port_disj scdests_not_emp no_disconn_port  no_same_source no_same_dest bij_p2p    
              unfolding  ch_srcsampport_def par_src_sampling_ports_def par_ports_def port_of_part_def
                  is_src_sampport_def par_dest_sampling_ports_def is_dest_sampport_def
                  image_def ch_destsampport_def par_sampchan_def gsch_def 
              apply auto 
              by (metis (mono_tags, lifting) someI_ex)+
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
     {assume "\<not>(ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (cur s2 (gsch conf Core0)))"
      then have "cur s2= cur s1 \<and> schan s2 = schan s1"
        using eq by auto
      then have "s1 = s2" by auto
       then  have "s1 \<sim>u\<sim> s2" 
       unfolding state_equiv_def by auto
     } 
     thus ?thesis using eq l by auto
   qed
  } thus ?thesis by auto
qed

lemma Write_Sampling_Message2_sat_LRE: 
  "\<forall>u s1 s2 k. (s1,s2) \<in> Guar\<^sub>f Write_Sampling_Message_RGCondC1 
                \<longrightarrow> ((domevt s1 k (Write_Sampling_Messagek1 k)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
proof-
  {fix u s1 s2 k
   assume a0:"(s1,s2) \<in> Guar\<^sub>f Write_Sampling_Message_RGCondC1" and
         a1:"(domevt s1 k (Write_Sampling_Messagek1 k)) \<setminus>\<leadsto> u"
   then obtain ps where eq:" cur s2= cur s1 \<and>
                 (((ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (cur s1 (gsch conf Core1))) \<longrightarrow>
                       (\<exists>!ch. ch =(ch_srcsampport conf (the (gPort (ps!0)))) \<and> 
                       (\<forall>ch'. (ch'\<noteq>ch \<longrightarrow> (schan s2) ch' = (schan s1) ch')))) \<and>
                   (\<not>(ps typeof [PORT,MSG]                              
                   \<and> is_src_sampport conf (the (gPort (ps!0)))          
                   \<and> port_of_part conf (the (gPort (ps!0))) (cur s2 (gsch conf Core1))) \<longrightarrow>
                   (schan s2) = (schan s1)))"
    using a0 unfolding Write_Sampling_Message_RGCondC1_def Guar\<^sub>f_def getrgformula_def  
     by auto
   then have "s1 \<sim>u\<sim> s2"
   proof -
     {assume pre_cond:"(ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (cur s1 (gsch conf Core1)))"      
      then obtain p where ps0_pt:"(the (gPort (ps!0))) = p" 
        using MT_Pt typeof_MT by fastforce
      then have pre_cond:
        "(ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf p \<and> 
                     port_of_part conf p (cur s1 (gsch conf Core1)))"
        using pre_cond by auto
      have "domevt s1 k (Write_Sampling_Messagek1 k) = P ((cur s1) (c2s conf Core1))"
      unfolding domevt_def gsch_def Schedulek1_def Schedulek0_def  Read_Sampling_Messagek1_def
               Write_Sampling_Messagek0_def Write_Sampling_Messagek1_def Read_Sampling_Messagek0_def
        by auto
      then have non_inter:"P ((cur s1) (c2s conf Core1))\<noteq> u \<and> 
              \<not>(part_on_core conf u (P ((cur s1) (c2s conf Core1)) )) \<and> 
              \<not>ch_conn2 conf (P ((cur s1) (c2s conf Core1))) u" 
      using a1 unfolding noninterf1_def interf_def
        by presburger    
      then have "(\<exists>d1. u = S d1) \<or> (\<exists>d1. u=P d1)"
        using non_inter part_on_core.simps
        by (metis Domain.exhaust)             
      then have ?thesis
      proof
        assume "\<exists>d1. u = S d1"
        thus ?thesis using eq 
          unfolding state_equiv_def using state_obs_sched_def by auto
      next
        assume u:"\<exists>d1. u=P d1"
        then obtain d1 where u:"u=P d1" by auto
        then have d1_not_cur_core:"d1 \<noteq> ((cur s1) (c2s conf Core1))" 
          using non_inter by auto
        then have "(\<exists>d1. u= S d1) \<or>  \<not>ch_conn conf ((cur s1) (c2s conf Core1)) d1"  
          using non_inter u a0 ch_conn2.simps by auto
        thus ?thesis
        proof
          assume "\<exists>d1. u = S d1" thus ?thesis using u by auto
        next
          assume a0:"\<not>ch_conn conf ((cur s1) (c2s conf Core1)) d1"       
          then have a0:"(\<forall>sch p. (p2p conf (scsrc conf sch) = cur s1 (c2s conf Core1)) \<longrightarrow> 
                  \<not>(p \<in> scdests conf sch \<and> p2p conf p = d1))"
            unfolding ch_conn_def
            by auto
          obtain ch  where 
            eq_schan:"ch =(ch_srcsampport conf p) \<and>  
            (\<forall>ch'. (ch'\<noteq>ch \<longrightarrow> (schan s2) ch' = (schan s1) ch'))"
              using eq pre_cond ps0_pt by auto
          have "ch \<notin>(par_sampchan conf d1)" 
          proof 
            assume ch_par:"ch \<in> (par_sampchan conf d1)"
            then have "ch \<in> (ch_srcsampport conf) ` (par_src_sampling_ports conf (par_ports conf d1)) \<or>
                    ch \<in> (ch_destsampport conf) `(par_dest_sampling_ports conf (par_ports conf d1))"
              using a0 unfolding par_sampchan_def by auto            
            then show False
              unfolding par_sampchan_def ch_srcsampport_def
              using  a0 d1_not_cur_core pre_cond eq_schan ps0_pt ch_par port_disj scdests_not_emp no_disconn_port  no_same_source no_same_dest bij_p2p    
              unfolding  ch_srcsampport_def par_src_sampling_ports_def par_ports_def port_of_part_def
                  is_src_sampport_def par_dest_sampling_ports_def is_dest_sampport_def
                  image_def ch_destsampport_def par_sampchan_def gsch_def 
              apply auto 
              by (metis (mono_tags, lifting) someI_ex)+
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
     {assume "\<not>(ps typeof [PORT,MSG] \<and> 
                     is_src_sampport conf (the (gPort (ps!0))) \<and> 
                     port_of_part conf (the (gPort (ps!0))) (cur s2 (gsch conf Core1)))"
      then have "cur s2= cur s1 \<and> schan s2 = schan s1"
        using eq by auto
      then have "s1 = s2" by auto
       then  have "s1 \<sim>u\<sim> s2" 
       unfolding state_equiv_def by auto
     } 
     thus ?thesis using eq l by auto
   qed
  } thus ?thesis by auto
qed



lemma Core_Init_sat_SCE: 
  "\<forall>u s1 s2 k. s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (Core_Init k)) \<leadsto> u \<longrightarrow> s1 \<sim>(domevt s1 k (Core_Init k))\<sim> s2)
               \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>f Core_Init_RGCond \<and> (s2,s2') \<in> Guar\<^sub>f Core_Init_RGCond 
                              \<longrightarrow> s1' \<sim>u\<sim> s2')"
proof -
 { fix u s1 s2 k s1' s2'
  assume a0: "s1 \<sim>u\<sim> s2 \<and> 
            ((domevt s1 k (Core_Init k)) \<leadsto> u \<longrightarrow> s1 \<sim>(domevt s1 k (Core_Init k))\<sim> s2)" 
  assume a1: "(s1,s1') \<in> Guar\<^sub>f Core_Init_RGCond \<and> (s2,s2') \<in> Guar\<^sub>f Core_Init_RGCond"
  then have "s1 = s1'" and "s2=s2'"
    unfolding Core_Init_RGCond_def Guar\<^sub>f_def getrgformula_def Id_def by auto
  then have "s1'\<sim>u\<sim> s2'" using a0 
    by (simp add: state_equiv_def)
 } thus ?thesis by blast
qed 

lemma eq_s1_s2_u_sch: "s1 \<sim>u\<sim> s2 \<Longrightarrow> u = S p \<Longrightarrow> cur s1 p = cur s2 p"
using state_obs.simps  state_equiv_def  state_obs_sched_def
by (metis (no_types, lifting) State.select_convs(1) State.update_convs(1) System_Init_def fstI fun_upd_eqD s0_init)


lemma eq_s1_s2_u_par:"s1 \<sim>u\<sim> s2 \<Longrightarrow> u = P p \<Longrightarrow> \<forall>ch\<in> par_sampchan conf p. schan s1 ch = schan s2 ch"
using state_obs.simps
unfolding state_equiv_def  state_obs_part_def schan_obs_part_def
proof -
  assume a1: "u = P p"
  assume a2: "state_obs s1 u = state_obs s2 u"
  assume a3: "\<And>s p. state_obs s (P p) = s0 \<lparr>schan := schan s |` par_sampchan conf p\<rparr>"
  { fix ss :: SampChannel
    have "\<And>f. schan (schan_update f s0) = f Map.empty"
      by (simp add: System_Init_def s0_init)
    then have "ss \<notin> par_sampchan conf p \<or> schan s2 ss = schan s1 ss"
      using a3 a2 a1 by (metis (no_types) restrict_in) }
  then show ?thesis
    by auto
qed



lemma Schedule0_sat_SCE: 
  "\<forall>u s1 s2 k. s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (Schedulek0 k)) \<leadsto> u \<longrightarrow> s1 \<sim>(domevt s1 k (Schedulek0 k))\<sim> s2) \<and>
               s1 \<in> Pre\<^sub>f Schedule_RGCondC0 \<and> s2 \<in> Pre\<^sub>f Schedule_RGCondC0 
               \<longrightarrow> (\<forall>s1' s2'. s1' \<in> Post\<^sub>f Schedule_RGCondC0 \<and> s2' \<in> Post\<^sub>f Schedule_RGCondC0 
                              \<longrightarrow> s1' \<sim>u\<sim> s2')"
proof-
{ fix u s1 s2 k s1' s2'
  assume a0: "s1 \<sim>u\<sim> s2 \<and> 
            ((domevt s1 k (Schedulek0 k)) \<leadsto> u \<longrightarrow> 
               s1 \<sim>(domevt s1 k (Schedulek0 k))\<sim> s2)" 
  assume a1: "(s1,s1') \<in> Guar\<^sub>f Schedule_RGCondC0 \<and> 
              (s2,s2') \<in> Guar\<^sub>f Schedule_RGCondC0"
  then have eq_s1:"schan s1 = schan s1' \<and> (cur s1 (c2s conf Core1) = cur s1'  (c2s conf Core1))" and
            eq_s2:"schan s2 = schan s2' \<and> (cur s2 (c2s conf Core1) = cur s2'  (c2s conf Core1))"
    unfolding Schedule_RGCondC0_def Guar\<^sub>f_def 
              getrgformula_def Id_def by auto  
  have dom:"domevt s1 k (Schedulek0 k) = S ((c2s conf) Core0)" 
   unfolding domevt_def gsch_def Schedulek1_def  Read_Sampling_Messagek0_def
             Write_Sampling_Messagek1_def Write_Sampling_Messagek0_def Read_Sampling_Messagek1_def
            Schedulek0_def
   by auto
  have "s1'\<sim>u\<sim> s2'" 
  proof (cases "S ((c2s conf) Core0) \<leadsto> u")
    case True   
    then have eq_s1_s2_sch0:"s1 \<sim> S ((c2s conf) Core0)\<sim> s2" using a0 dom by auto
    have "S ((c2s conf) Core0) = u \<or>
               part_on_core conf u (S ((c2s conf) Core0)) \<or>
               ch_conn2 conf (S ((c2s conf) Core0)) u"
      using True unfolding interf_def by meson 
    { assume u:"u = S ((c2s conf) Core0)" 
      then have "cur s1 ((c2s conf) Core0) = cur s2 ((c2s conf) Core0)"
        using a0 state_obs.simps eq_s1_s2_u_sch[of s1 u s2 "((c2s conf) Core0)"]  by auto
      then have "cur s1' ((c2s conf) Core0) = cur s2' ((c2s conf) Core0)"
        using  eq_s1 eq_s2 sorry
      then have ?thesis using eq_s1 eq_s2  state_obs.simps  u
        unfolding state_obs_sched_def state_equiv_def 
    }
    thus ?thesis sorry
  next
    case False    
    have non_inter:"S ((c2s conf) Core0)\<noteq> u \<and> 
              \<not>(part_on_core conf u (S ((c2s conf) Core0)) ) \<and> 
              \<not>ch_conn2 conf (S ((c2s conf) Core0)) u" 
    using False
    unfolding interf_def by presburger
   then have "(\<exists>d1. u = S d1) \<or> (\<exists>d1. u=P d1 \<and> (c2s conf) Core0 \<notin> ((p2s conf) d1))"
   using non_inter part_on_core.simps
     by (metis Domain.simps(6) Domain.exhaust)
   then show ?thesis
   proof 
     assume "(\<exists>d1. u = S d1)" 
     then obtain d1 where us:"u=S d1" by auto
     then have "\<exists>!k1. d1=((c2s conf) k1) \<and> k1\<noteq>Core0"
       using schedulers non_inter by auto
     then have u:"u=S ((c2s conf) Core1)" using  us Core.exhaust by auto
     moreover have " cur s1' (c2s conf Core1) =  cur s2' (c2s conf Core1)"      
       using a0 u eq_s1_s2_u_sch  eq_s1 eq_s2 by auto    
     thus ?thesis unfolding state_equiv_def  using u state_obs_sched_def by auto
   next 
     assume "(\<exists>d1. u=P d1 \<and> (c2s conf) Core0 \<notin> ((p2s conf) d1))"
     then obtain d1 where uP:"u=P d1 \<and> (c2s conf) Core0 \<notin> ((p2s conf) d1)" by auto
     then have "state_obs_part s1 d1 = state_obs_part s2 d1" 
       using a0 state_obs.simps
       unfolding state_obs_part_def schan_obs_part_def 
                 state_equiv_def by auto
     thus ?thesis  using a0 eq_s1 eq_s2 state_obs.simps
        unfolding state_equiv_def state_obs_part_def
        by (simp add: System_Init_def fstI s0_init schan_obs_part_def uP)              
   qed
 qed
 } thus ?thesis by blast
qed 

lemma Schedule1_sat_SCE: 
  "\<forall>u s1 s2 k. s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (Schedulek1 k)) \<leadsto> u \<longrightarrow> s1 \<sim>(domevt s1 k (Schedulek1 k))\<sim> s2)
               \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>f Schedule_RGCondC1 \<and> (s2,s2') \<in> Guar\<^sub>f Schedule_RGCondC1
                              \<longrightarrow> s1' \<sim>u\<sim> s2')"
  sorry


lemma Read_Sampling_Message0_sat_SCE: 
  "\<forall>u s1 s2 k. s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (Read_Sampling_Messagek0 k)) \<leadsto> u 
                              \<longrightarrow> s1 \<sim>(domevt s1 k (Read_Sampling_Messagek0 k))\<sim> s2)
               \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC0 
                               \<and> (s2,s2') \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC0
                                \<longrightarrow> s1' \<sim>u\<sim> s2')"
  proof -
{ fix u s1 s2 k s1' s2'
  assume a0: "s1 \<sim>u\<sim> s2 \<and> 
            ((domevt s1 k (Read_Sampling_Messagek0 k)) \<leadsto> u \<longrightarrow> 
               s1 \<sim>(domevt s1 k (Read_Sampling_Messagek0 k))\<sim> s2)" 
  assume a1: "(s1,s1') \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC0 \<and> 
              (s2,s2') \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC0"
  then have "s1 = s1'" and "s2=s2'"
    unfolding Read_Sampling_Message_RGCondC0_def Guar\<^sub>f_def 
              getrgformula_def Id_def by auto
  then have "s1'\<sim>u\<sim> s2'" using a0 
    by (simp add: state_equiv_def)
 } thus ?thesis by blast
qed 

lemma Read_Sampling_Message1_sat_SCE: 
  "\<forall>u s1 s2 k. s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (Read_Sampling_Messagek1 k)) \<leadsto> u 
                              \<longrightarrow> s1 \<sim>(domevt s1 k (Read_Sampling_Messagek1 k))\<sim> s2)
               \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC1 
                               \<and> (s2,s2') \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC1
                                \<longrightarrow> s1' \<sim>u\<sim> s2')"
  proof -
 { fix u s1 s2 k s1' s2'
  assume a0: "s1 \<sim>u\<sim> s2 \<and> 
            ((domevt s1 k (Read_Sampling_Messagek1 k)) \<leadsto> u \<longrightarrow> s1 \<sim>(domevt s1 k (Read_Sampling_Messagek1 k))\<sim> s2)" 
  assume a1: "(s1,s1') \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC1 \<and> 
              (s2,s2') \<in> Guar\<^sub>f Read_Sampling_Message_RGCondC1"
  then have "s1 = s1'" and "s2=s2'"
    unfolding Read_Sampling_Message_RGCondC1_def Guar\<^sub>f_def getrgformula_def Id_def by auto
  then have "s1'\<sim>u\<sim> s2'" using a0 
    by (simp add: state_equiv_def)
 } thus ?thesis by blast
qed 

lemma Write_Sampling_Message0_sat_SCE: 
  "\<forall>u s1 s2 k. s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (Write_Sampling_Messagek0 k)) \<leadsto> u 
                              \<longrightarrow> s1 \<sim>(domevt s1 k (Write_Sampling_Messagek0 k))\<sim> s2)
               \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>f Write_Sampling_Message_RGCondC0 
                              \<and> (s2,s2') \<in> Guar\<^sub>f Write_Sampling_Message_RGCondC0 
                                \<longrightarrow> s1' \<sim>u\<sim> s2')"
  sorry

lemma Write_Sampling_Message1_sat_SCE: 
  "\<forall>u s1 s2 k. s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (Write_Sampling_Messagek1 k)) \<leadsto> u 
                              \<longrightarrow> s1 \<sim>(domevt s1 k (Write_Sampling_Messagek1 k))\<sim> s2)
               \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>f Write_Sampling_Message_RGCondC1 
                              \<and> (s2,s2') \<in> Guar\<^sub>f Write_Sampling_Message_RGCondC1
                                \<longrightarrow> s1' \<sim>u\<sim> s2')"
  sorry



theorem uwc_oc: "observed_consistent"
  apply(simp add:observed_consistent_def)
  by(simp add:state_equiv_def)


theorem uwce_LRE: "locally_respect_event"
  proof -
    have "\<forall>ef u s1 s2 k. ef\<in>all_evts ARINCXKernel_Spec \<and> (s1,s2) \<in> Guar\<^sub>e ef \<longrightarrow> 
                           ((domevt s1 k (E\<^sub>e ef)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)"
      proof -
      {
        fix ef u s1 s2 k
        assume a0: "ef\<in>all_evts ARINCXKernel_Spec \<and> (s1,s2) \<in> Guar\<^sub>e ef"
        then have "ef\<in>insert Core_Init_RGF (all_evts_es (fst EvtSys1_on_Core_RGF))"
          using all_evts_def[of ARINCXKernel_Spec] ARINCXKernel_Spec_def EvtSys_on_Core_RGF_def 
            all_evts_es_seq[of Core_Init_RGF EvtSys1_on_Core_RGF]
              by (metis (no_types, lifting) UN_E fst_conv) 
        then have "ef = Core_Init_RGF \<or> ef\<in>all_evts_es (fst EvtSys1_on_Core_RGF)" by auto
        then have "(domevt s1 k (E\<^sub>e ef)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2"
          proof
            assume b0: "ef = Core_Init_RGF"
            have "evtrgfs (Core_Init) = Some Core_Init_RGCond"
              by (simp add: evtrgfs_def) 
            with a0 b0 show ?thesis 
              using Core_Init_RGF_def E\<^sub>e_def Core_Init_sat_LRE
                by (metis Guar\<^sub>e_def Guar\<^sub>f_def fst_conv snd_conv)
          next
            assume b0: "ef\<in>all_evts_es (fst EvtSys1_on_Core_RGF)"
            moreover
            have "all_evts_es (fst EvtSys1_on_Core_RGF) = {Schedule_RGF,
                                      Write_Sampling_Message_RGF,
                                      Read_Sampling_Message_RGF,
                                      Get_Sampling_Port_Status_RGF,
                                      Send_Queuing_Message_RGF,
                                      Receive_Queuing_Message_RGF,
                                      Get_Queuing_Port_Status_RGF}"
              using all_evts_es_esys by (simp add: EvtSys1_on_Core_RGF_def) 
            moreover
            have "(s1,s2) \<in> Guar\<^sub>e Schedule_RGF \<longrightarrow> 
                    domevt s1 k (E\<^sub>e Schedule_RGF) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2"
              using Schedule_sat_LRE Schedule_RGF_def Guar\<^sub>e_def Guar\<^sub>f_def E\<^sub>e_def
                by (metis fst_conv snd_conv) 
            moreover
            have "(s1,s2) \<in> Guar\<^sub>e Write_Sampling_Message_RGF \<longrightarrow> 
                    domevt s1 k (E\<^sub>e Write_Sampling_Message_RGF) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2"
              using Write_Sampling_Message_sat_LRE Write_Sampling_Message_RGF_def Guar\<^sub>e_def 
                Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
            moreover
            have "(s1,s2) \<in> Guar\<^sub>e Read_Sampling_Message_RGF \<longrightarrow> 
                    domevt s1 k (E\<^sub>e Read_Sampling_Message_RGF) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2"
              using Read_Sampling_Message_sat_LRE Read_Sampling_Message_RGF_def Guar\<^sub>e_def 
                Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
            moreover
            have "(s1,s2) \<in> Guar\<^sub>e Get_Sampling_Port_Status_RGF \<longrightarrow> 
                    domevt s1 k (E\<^sub>e Get_Sampling_Port_Status_RGF) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2"
              using Get_Sampling_Port_Status_sat_LRE Get_Sampling_Port_Status_RGF_def Guar\<^sub>e_def 
                Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
            moreover
            have "(s1,s2) \<in> Guar\<^sub>e Send_Queuing_Message_RGF \<longrightarrow> 
                    domevt s1 k (E\<^sub>e Send_Queuing_Message_RGF) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2"
              using Send_Queuing_Message_sat_LRE Send_Queuing_Message_RGF_def Guar\<^sub>e_def 
                Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
            moreover
            have "(s1,s2) \<in> Guar\<^sub>e Receive_Queuing_Message_RGF \<longrightarrow> 
                    domevt s1 k (E\<^sub>e Receive_Queuing_Message_RGF) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2"
              using Receive_Queuing_Message_sat_LRE Receive_Queuing_Message_RGF_def Guar\<^sub>e_def 
                Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
            moreover
            have "(s1,s2) \<in> Guar\<^sub>e Get_Queuing_Port_Status_RGF \<longrightarrow> 
                    domevt s1 k (E\<^sub>e Get_Queuing_Port_Status_RGF) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2"
              using Get_Queuing_Port_Status_sat_LRE Get_Queuing_Port_Status_RGF_def Guar\<^sub>e_def
                Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
            ultimately show ?thesis using a0 insert_iff singletonD by auto 
          qed
      }
      then show ?thesis by auto
      qed

    then show ?thesis using locally_respect_event_def
      noninterf1_def noninterf_def by auto 
  qed

theorem uwce_SCE: "step_consistent_event"
  proof -
    have "\<forall>ef u s1 s2 k. ef\<in>all_evts ARINCXKernel_Spec  
                \<longrightarrow> s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (E\<^sub>e ef)) \<leadsto> u \<longrightarrow> s1 \<sim>(domevt s1 k (E\<^sub>e ef))\<sim> s2)
                \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>e ef \<and> (s2,s2') \<in> Guar\<^sub>e ef \<longrightarrow> s1' \<sim>u\<sim> s2')"
      proof -
      {
        fix ef u s1 s2 k
        assume a0: "ef\<in>all_evts ARINCXKernel_Spec"
          and  a1: "s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (E\<^sub>e ef)) \<leadsto> u \<longrightarrow> s1 \<sim>(domevt s1 k (E\<^sub>e ef))\<sim> s2)"
        then have "ef\<in>insert Core_Init_RGF (all_evts_es (fst EvtSys1_on_Core_RGF))"
          using all_evts_def[of ARINCXKernel_Spec] ARINCXKernel_Spec_def EvtSys_on_Core_RGF_def 
            all_evts_es_seq[of Core_Init_RGF EvtSys1_on_Core_RGF]
              by (metis (no_types, lifting) UN_E fst_conv) 
        then have "ef = Core_Init_RGF \<or> ef\<in>all_evts_es (fst EvtSys1_on_Core_RGF)" by auto
        then have "\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>e ef \<and> (s2,s2') \<in> Guar\<^sub>e ef \<longrightarrow> s1' \<sim>u\<sim> s2'"
          proof
            assume b0: "ef = Core_Init_RGF"
            have "evtrgfs (Core_Init) = Some Core_Init_RGCond"
              by (simp add: evtrgfs_def) 
            with a0 a1 b0 show ?thesis 
              using Core_Init_RGF_def E\<^sub>e_def Core_Init_sat_SCE
                by (metis Guar\<^sub>e_def Guar\<^sub>f_def fst_conv snd_conv)
          next
            assume b0: "ef\<in>all_evts_es (fst EvtSys1_on_Core_RGF)"
            moreover
            have "all_evts_es (fst EvtSys1_on_Core_RGF) = {Schedule_RGF,
                                      Write_Sampling_Message_RGF,
                                      Read_Sampling_Message_RGF,
                                      Get_Sampling_Port_Status_RGF,
                                      Send_Queuing_Message_RGF,
                                      Receive_Queuing_Message_RGF,
                                      Get_Queuing_Port_Status_RGF}"
              using all_evts_es_esys by (simp add: EvtSys1_on_Core_RGF_def) 
            moreover
            have "s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (E\<^sub>e Schedule_RGF)) \<leadsto> u 
                  \<longrightarrow> s1 \<sim>(domevt s1 k (E\<^sub>e Schedule_RGF))\<sim> s2)
                  \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>e Schedule_RGF \<and> (s2,s2') \<in> Guar\<^sub>e Schedule_RGF 
                              \<longrightarrow> s1' \<sim>u\<sim> s2')"
              using Schedule_sat_SCE Schedule_RGF_def Guar\<^sub>e_def Guar\<^sub>f_def E\<^sub>e_def
                by (metis fst_conv snd_conv) 
            moreover
            have "s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (E\<^sub>e Write_Sampling_Message_RGF)) \<leadsto> u 
                  \<longrightarrow> s1 \<sim>(domevt s1 k (E\<^sub>e Write_Sampling_Message_RGF))\<sim> s2)
                  \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>e Write_Sampling_Message_RGF 
                                  \<and> (s2,s2') \<in> Guar\<^sub>e Write_Sampling_Message_RGF 
                                  \<longrightarrow> s1' \<sim>u\<sim> s2')"
              using Write_Sampling_Message_sat_SCE Write_Sampling_Message_RGF_def 
                Guar\<^sub>e_def Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
            moreover
            have "s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (E\<^sub>e Read_Sampling_Message_RGF)) \<leadsto> u 
                  \<longrightarrow> s1 \<sim>(domevt s1 k (E\<^sub>e Read_Sampling_Message_RGF))\<sim> s2)
                  \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>e Read_Sampling_Message_RGF 
                                  \<and> (s2,s2') \<in> Guar\<^sub>e Read_Sampling_Message_RGF 
                                  \<longrightarrow> s1' \<sim>u\<sim> s2')"
              using Read_Sampling_Message_sat_SCE Read_Sampling_Message_RGF_def 
                Guar\<^sub>e_def Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
             moreover
            have "s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (E\<^sub>e Get_Sampling_Port_Status_RGF)) \<leadsto> u 
                  \<longrightarrow> s1 \<sim>(domevt s1 k (E\<^sub>e Get_Sampling_Port_Status_RGF))\<sim> s2)
                  \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>e Get_Sampling_Port_Status_RGF 
                                  \<and> (s2,s2') \<in> Guar\<^sub>e Get_Sampling_Port_Status_RGF 
                                    \<longrightarrow> s1' \<sim>u\<sim> s2')"
              using Get_Sampling_Port_Status_sat_SCE Get_Sampling_Port_Status_RGF_def 
                Guar\<^sub>e_def Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
            moreover
            have "s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (E\<^sub>e Send_Queuing_Message_RGF)) \<leadsto> u 
                  \<longrightarrow> s1 \<sim>(domevt s1 k (E\<^sub>e Send_Queuing_Message_RGF))\<sim> s2)
                  \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>e Send_Queuing_Message_RGF 
                                  \<and> (s2,s2') \<in> Guar\<^sub>e Send_Queuing_Message_RGF 
                                    \<longrightarrow> s1' \<sim>u\<sim> s2')"
              using Send_Queuing_Message_sat_SCE Send_Queuing_Message_RGF_def 
                Guar\<^sub>e_def Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
            moreover
            have "s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (E\<^sub>e Receive_Queuing_Message_RGF)) \<leadsto> u 
                  \<longrightarrow> s1 \<sim>(domevt s1 k (E\<^sub>e Receive_Queuing_Message_RGF))\<sim> s2)
                  \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>e Receive_Queuing_Message_RGF 
                                  \<and> (s2,s2') \<in> Guar\<^sub>e Receive_Queuing_Message_RGF 
                                    \<longrightarrow> s1' \<sim>u\<sim> s2')"
              using Receive_Queuing_Message_sat_SCE Receive_Queuing_Message_RGF_def 
                Guar\<^sub>e_def Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
             moreover
            have "s1 \<sim>u\<sim> s2 \<and> ((domevt s1 k (E\<^sub>e Get_Queuing_Port_Status_RGF)) \<leadsto> u 
                  \<longrightarrow> s1 \<sim>(domevt s1 k (E\<^sub>e Get_Queuing_Port_Status_RGF))\<sim> s2)
                  \<longrightarrow> (\<forall>s1' s2'. (s1,s1') \<in> Guar\<^sub>e Get_Queuing_Port_Status_RGF 
                                  \<and> (s2,s2') \<in> Guar\<^sub>e Get_Queuing_Port_Status_RGF 
                                    \<longrightarrow> s1' \<sim>u\<sim> s2')"
              using Get_Queuing_Port_Status_sat_SCE Get_Queuing_Port_Status_RGF_def 
                Guar\<^sub>e_def Guar\<^sub>f_def E\<^sub>e_def by (metis fst_conv snd_conv) 
            ultimately show ?thesis using a0 a1 insert_iff singletonD by smt
          qed
      }
      then show ?thesis by blast
      qed

    then show ?thesis using step_consistent_event_def
      noninterf1_def noninterf_def by blast
  qed

theorem "noninfluence0"
  using uwc_oc uwce_LRE uwce_SCE UnwindingTheoremE_noninfluence0 by simp

theorem "nonleakage"
  using uwc_oc uwce_LRE uwce_SCE UnwindingTheoremE_nonleakage by simp


end