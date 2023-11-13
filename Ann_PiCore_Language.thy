section \<open>Abstract Syntax of PiCore Language\<close>

theory Ann_PiCore_Language imports Main begin

type_synonym 's bexp = "'s set"
type_synonym 's guard = "'s set"
type_synonym 's assn = "'s set"

datatype 's ann_prog =
    AnnBasic "('s assn)" "'s \<Rightarrow>'s"
  | AnnSeq "'s ann_prog" "'s ann_prog"
  | AnnCond "('s assn)" "'s bexp" "'s ann_prog" "'s ann_prog"
  | AnnWhile "('s assn)" "'s bexp" "'s ann_prog"
  | AnnAwait "('s assn)" "'s bexp" "'s ann_prog"
  | AnnNondt "('s assn)" "('s \<times> 's) set"

primrec ann_pre ::"'s ann_prog \<Rightarrow> 's assn"  where
  "ann_pre (AnnBasic r f) = r"
| "ann_pre (AnnSeq c1 c2) = ann_pre c1"
| "ann_pre (AnnCond r b c1 c2) = r"
| "ann_pre (AnnWhile r b c) = r"
| "ann_pre (AnnAwait r b c) = r"
| "ann_pre (AnnNondt r f) = r"

type_synonym ('l,'s) event' = "'l \<times> ('s guard \<times> 's ann_prog)"

definition label :: "('l,'s) event' \<Rightarrow> 'l" where 
  "label ev \<equiv> fst ev"

definition guard :: "('l,'s) event' \<Rightarrow> 's guard" where
  "guard ev \<equiv> fst (snd ev)"

definition body :: "('l,'s) event' \<Rightarrow> 's ann_prog" where
  "body ev \<equiv> snd (snd ev)"

datatype ('l,'k,'s) event =
      AnonyEvent "('s ann_prog) option" 
    | BasicEvent "(('l,'s) event')" 


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

primrec label_e :: "('l,'k,'s) event \<Rightarrow> 'l option"
  where "label_e (AnonyEvent _) = None" |
        "label_e (BasicEvent ev) = Some (label ev)"

primrec body_e :: "('l,'k,'s) event \<Rightarrow> 's ann_prog option"
  where "body_e (AnonyEvent P) = None" |
        "body_e (BasicEvent ev) = Some (body ev)"


lemma basicevt_isnot_anony: "is_basicevt e \<Longrightarrow> \<not> is_anonyevt e"
  by (metis event.exhaust is_anonyevt.simps(2) is_basicevt.simps(1)) 

lemma anonyevt_isnot_basic: "is_anonyevt e \<Longrightarrow> \<not> is_basicevt e"
  using basicevt_isnot_anony by auto

lemma evtseq_ne_es: "EvtSeq e es \<noteq> es"
  apply(induct es)
  apply auto[1]
  by simp

end