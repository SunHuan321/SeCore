(*
Created by Yongwang Zhao (ywzhao@ntu.edu.sg, zhaoyw@buaa.edu.cn)
School of Computer Engineering, Nanyang Technological University, Singapore
and School of Computer Science & Engineering, Beihang University, China
*)


section \<open>Abstract Syntax of PiCore Language\<close>

theory PiCore_Language imports Main begin

type_synonym 's bexp = "'s set"

type_synonym 's guard = "'s set"

datatype 's prog =
    Basic "'s \<Rightarrow>'s"
  | Seq "'s prog" "'s prog"
  | Cond "'s bexp" "'s prog" "'s prog"
  | While "'s bexp" "'s prog"
  | Await "'s bexp" "'s prog"
  | Nondt "('s \<times> 's) set"

type_synonym ('l,'s) event' = "'l \<times> ('s guard \<times> 's prog)"

definition guard :: "('l,'s) event' \<Rightarrow> 's guard" where
  "guard ev \<equiv> fst (snd ev)"

definition body :: "('l,'s) event' \<Rightarrow> 's prog" where
  "body ev \<equiv> snd (snd ev)"

datatype ('l,'k,'s) event =
      AnonyEvent "('s prog) option" 
    | BasicEvent "('l,'s) event'" 

datatype ('l,'k,'s) esys = 
      EvtSeq "('l,'k,'s) event" "('l,'k,'s) esys"
    | EvtSys "('l,'k,'s) event set" 

type_synonym ('l,'k,'s) paresys = "'k \<Rightarrow> ('l,'k,'s) esys"

section \<open>Some Lemmas of Abstract Syntax\<close>

primrec is_basicevt :: "('l,'k,'s) event \<Rightarrow> bool"
  where "is_basicevt (AnonyEvent _) = False" |
        "is_basicevt (BasicEvent _) = True"

primrec is_anonyevt :: "('l,'k,'s) event \<Rightarrow> bool"
  where "is_anonyevt (AnonyEvent _) = True" |
        "is_anonyevt (BasicEvent _) = False"

lemma basicevt_isnot_anony: "is_basicevt e \<Longrightarrow> \<not> is_anonyevt e"
  by (metis event.exhaust is_anonyevt.simps(2) is_basicevt.simps(1)) 

lemma anonyevt_isnot_basic: "is_anonyevt e \<Longrightarrow> \<not> is_basicevt e"
  using basicevt_isnot_anony by auto

lemma evtseq_ne_es: "EvtSeq e es \<noteq> es"
  apply(induct es)
  apply auto[1]
  by simp

end