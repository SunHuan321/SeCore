section \<open>Small-step Operational Semantics of PiCore Language\<close>

theory Ann_PiCore_Semantics
imports Ann_PiCore_Language
begin

subsection \<open>Datatypes for Semantics\<close>

datatype cmd = CMP
datatype ('l,'k,'s) act = 
      Cmd "'s ann_prog option"      
    | EvtEnt "('l,'k,'s) event" 

record ('l,'k,'s) actk =  Act  :: "('l,'k,'s) act" 
                              K   :: "'k"

definition get_actk :: "('l,'k,'s) act \<Rightarrow> 'k \<Rightarrow> ('l,'k,'s) actk" ("_\<sharp>_" [91,91] 90)
  where "get_actk a k \<equiv> \<lparr>Act=a, K=k\<rparr>"

type_synonym ('l,'k,'s) x = "'k \<Rightarrow> ('l,'k,'s) event" 

type_synonym 's pconf = "(('s ann_prog) option) \<times> 's"

definition getspc_p :: "'s pconf \<Rightarrow> ('s ann_prog) option" where
  "getspc_p conf \<equiv> fst conf"

definition gets_p :: "'s pconf \<Rightarrow> 's" where
  "gets_p conf \<equiv> snd conf"

type_synonym ('l,'k,'s) econf = "(('l,'k,'s) event) \<times> ('s \<times> (('l,'k,'s) x) )"

definition getspc_e :: "('l,'k,'s) econf \<Rightarrow> ('l,'k,'s) event" where
  "getspc_e conf \<equiv> fst conf"

definition gets_e :: "('l,'k,'s) econf \<Rightarrow> 's" where
  "gets_e conf \<equiv> fst (snd conf)"

definition getx_e :: "('l,'k,'s) econf \<Rightarrow> ('l,'k,'s) x" where
  "getx_e conf \<equiv> snd (snd conf)"

type_synonym ('l,'k,'s) esconf = "(('l,'k,'s) esys) \<times> ('s \<times> (('l,'k,'s) x) )"

definition getspc_es :: "('l,'k,'s) esconf \<Rightarrow> ('l,'k,'s) esys" where
  "getspc_es conf \<equiv> fst conf"

definition gets_es :: "('l,'k,'s) esconf \<Rightarrow> 's" where
  "gets_es conf \<equiv> fst (snd conf)"

definition getx_es :: "('l,'k,'s) esconf \<Rightarrow> ('l,'k,'s) x" where
  "getx_es conf \<equiv> snd (snd conf)"

type_synonym ('l,'k,'s) pesconf = "(('l,'k,'s) paresys) \<times> ('s \<times> (('l,'k,'s) x) )"

definition getspc :: "('l,'k,'s) pesconf \<Rightarrow> ('l,'k,'s) paresys" where
  "getspc conf \<equiv> fst conf"

definition gets :: "('l,'k,'s) pesconf \<Rightarrow> 's" where
  "gets conf \<equiv> fst (snd conf)"

definition getx :: "('l,'k,'s) pesconf \<Rightarrow> ('l,'k,'s) x" where
  "getx conf \<equiv> snd (snd conf)"

definition getact :: "('l,'k,'s) actk \<Rightarrow> ('l,'k,'s) act" where
  "getact a \<equiv> Act a"

definition getk :: "('l,'k,'s) actk \<Rightarrow> 'k" where
  "getk a \<equiv> K a"

primrec is_Cmd_act :: "('l,'k,'s) act \<Rightarrow> bool"
  where "is_Cmd_act (Cmd _) = True" |
        "is_Cmd_act (EvtEnt _) = False"

definition is_Cmd_actk :: "('l,'k,'s) actk \<Rightarrow> bool" where
  "is_Cmd_actk a \<equiv> is_Cmd_act (getact a)"

subsection \<open>Semantics of Programs\<close>

inductive_set
  ptran :: "('s pconf \<times> 's pconf) set"
  and ptran' :: "'s pconf \<Rightarrow> 's pconf \<Rightarrow> bool"   ("_ -c\<rightarrow> _" [81,81] 80)
  and ptrans :: "'s pconf \<Rightarrow> 's pconf \<Rightarrow> bool"   ("_ -c*\<rightarrow> _" [81,81] 80)
where
  "P -c\<rightarrow> Q \<equiv> (P,Q) \<in> ptran"
| "P -c*\<rightarrow> Q \<equiv> (P,Q) \<in>ptran^*" 

| Basic:  "(Some (AnnBasic r f), s) -c\<rightarrow> (None, f s)"
| Seq1:   "(Some P0, s) -c\<rightarrow> (None, t) \<Longrightarrow> (Some (AnnSeq P0 P1), s) -c\<rightarrow> (Some P1, t)"
| Seq2:    "(Some P0, s) -c\<rightarrow> (Some P2, t) \<Longrightarrow> (Some(AnnSeq P0 P1), s) -c\<rightarrow> (Some(AnnSeq P2 P1), t)"
| CondT:  "s\<in>b  \<Longrightarrow> (Some(AnnCond r b P1 P2), s) -c\<rightarrow> (Some P1, s)"
| CondF:  "s\<notin>b \<Longrightarrow> (Some(AnnCond r b P1 P2), s) -c\<rightarrow> (Some P2, s)"
| WhileF: "s\<notin>b \<Longrightarrow> (Some(AnnWhile r b P), s) -c\<rightarrow> (None, s)"
| WhileT: "s\<in>b  \<Longrightarrow> (Some(AnnWhile r b P), s) -c\<rightarrow> (Some(AnnSeq P (AnnWhile r b P)), s)"
| Await:  "\<lbrakk>s\<in>b; (Some P, s) -c*\<rightarrow> (None, t)\<rbrakk> \<Longrightarrow> (Some(AnnAwait r b P), s) -c\<rightarrow> (None, t)" 
| Nondt:  "(s,t)\<in>f \<Longrightarrow> (Some(AnnNondt r f), s) -c\<rightarrow> (None, t)"

monos "rtrancl_mono"

subsection \<open>Semantics of Events\<close>

inductive_set
  etran :: "(('l,'k,'s) econf \<times> ('l,'k,'s) actk \<times> ('l,'k,'s) econf) set"
  and etran' :: "('l,'k,'s) econf \<Rightarrow> ('l,'k,'s) actk \<Rightarrow> ('l,'k,'s) econf \<Rightarrow> bool"   ("_ -et-_\<rightarrow> _" [81,81,81] 80)
where
  "P -et-t\<rightarrow> Q \<equiv> (P,t,Q) \<in> etran"
| AnonyEvent: "(P, s) -c\<rightarrow> (Q, t) \<Longrightarrow> (AnonyEvent P, s, x) -et-(Cmd P)\<sharp>k\<rightarrow> (AnonyEvent Q, t, x)"
| EventEntry: "\<lbrakk>P = body e; s \<in> guard e; x' = x(k:= BasicEvent e)\<rbrakk> 
                \<Longrightarrow> (BasicEvent e, s, x) -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> ((AnonyEvent (Some P)), s, x')"

subsection \<open>Semantics of Event Systems\<close>

inductive_set
  estran :: "(('l,'k,'s) esconf \<times> ('l,'k,'s) actk \<times> ('l,'k,'s) esconf) set"
  and estran' :: "('l,'k,'s) esconf \<Rightarrow> ('l,'k,'s) actk \<Rightarrow> ('l,'k,'s) esconf \<Rightarrow> bool"  
        ("_ -es-_\<rightarrow> _" [81,81] 80)
where
  "P -es-t\<rightarrow> Q \<equiv> (P,t,Q) \<in> estran"
| EvtOccur: "\<lbrakk>evt\<in> evts; (evt, (s, x)) -et-(EvtEnt evt)\<sharp>k\<rightarrow> (e, (s, x')) \<rbrakk> 
              \<Longrightarrow> (EvtSys evts, (s, x)) -es-(EvtEnt evt)\<sharp>k\<rightarrow> (EvtSeq e (EvtSys evts), (s, x'))"
| EvtSeq1:  "\<lbrakk>(e, s, x) -et-act\<sharp>k\<rightarrow> (e', s', x); e' \<noteq> AnonyEvent None\<rbrakk> 
              \<Longrightarrow> (EvtSeq e es, s, x) -es-act\<sharp>k\<rightarrow> (EvtSeq e' es, s', x)"
| EvtSeq2:  "\<lbrakk>(e, s, x) -et-act\<sharp>k\<rightarrow> (e', s', x); e' = AnonyEvent None\<rbrakk> 
              \<Longrightarrow> (EvtSeq e es, s, x) -es-act\<sharp>k\<rightarrow> (es, s', x)"

subsection \<open>Semantics of Parallel Event Systems\<close>

inductive_set
  pestran :: "(('l,'k,'s) pesconf \<times> ('l,'k,'s) actk \<times> ('l,'k,'s) pesconf) set"
  and pestran' :: "('l,'k,'s) pesconf \<Rightarrow> ('l,'k,'s) actk 
                      \<Rightarrow> ('l,'k,'s) pesconf \<Rightarrow> bool"  ("_ -pes-_\<rightarrow> _" [70,70] 60)
where
  "P -pes-t\<rightarrow> Q \<equiv> (P,t,Q) \<in> pestran"
| ParES:  "(pes(k), (s, x)) -es-(a\<sharp>k)\<rightarrow> (es', (s', x')) \<Longrightarrow> (pes, (s, x)) -pes-(a\<sharp>k)\<rightarrow> (pes(k:=es'), (s', x'))"

subsection \<open>Lemmas\<close>
subsubsection \<open>programs\<close>
lemma list_eq_if [rule_format]: 
  "\<forall>ys. xs=ys \<longrightarrow> (length xs = length ys) \<longrightarrow> (\<forall>i<length xs. xs!i=ys!i)"
  by (induct xs) auto

lemma list_eq: "(length xs = length ys \<and> (\<forall>i<length xs. xs!i=ys!i)) = (xs=ys)"
apply(rule iffI)
 apply clarify
 apply(erule nth_equalityI)
 apply simp+
done

lemma nth_tl: "\<lbrakk> ys!0=a; ys\<noteq>[] \<rbrakk> \<Longrightarrow> ys=(a#(tl ys))"
  by (cases ys) simp_all

lemma nth_tl_if [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P ys \<longrightarrow> P (a#(tl ys))"
  by (induct ys) simp_all

lemma nth_tl_onlyif [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P (a#(tl ys)) \<longrightarrow> P ys"
  by (induct ys) simp_all

lemma seq_not_eq1: "AnnSeq c1 c2\<noteq>c1"
  by (induct c1) auto

lemma seq_not_eq2: "AnnSeq c1 c2\<noteq>c2"
  by (induct c2) auto

lemma if_not_eq1: "AnnCond r b c1 c2 \<noteq>c1"
  by (induct c1) auto

lemma if_not_eq2: "AnnCond r b c1 c2\<noteq>c2"
  by (induct c2) auto

lemmas seq_and_if_not_eq [simp] = seq_not_eq1 seq_not_eq2 
seq_not_eq1 [THEN not_sym] seq_not_eq2 [THEN not_sym] 
if_not_eq1 if_not_eq2 if_not_eq1 [THEN not_sym] if_not_eq2 [THEN not_sym]

lemma prog_not_eq_in_ctran_aux:
  assumes c: "(P,s) -c\<rightarrow> (Q,t)"
  shows "P\<noteq>Q" using c
  by (induct x1 \<equiv> "(P,s)" x2 \<equiv> "(Q,t)" arbitrary: P s Q t) auto

lemma prog_not_eq_in_ctran [simp]: "\<not> (P,s) -c\<rightarrow> (P,t)"
apply clarify
apply(drule prog_not_eq_in_ctran_aux)
apply simp
done

subsubsection \<open>Events\<close>
lemma ent_spec1: "(ev, s, x) -et-(EvtEnt be)\<sharp>k\<rightarrow> (e2, s1, x1) \<Longrightarrow> ev = be" 
  apply(rule etran.cases)
  apply(simp)
  apply(simp add:get_actk_def)
  apply(simp add:get_actk_def)
  done

lemma ent_spec: "ec1 -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> ec2 \<Longrightarrow> getspc_e ec1 = BasicEvent ev"
  by (metis ent_spec1 getspc_e_def prod.collapse) 

lemma ent_spec2': "(ev, s, x) -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (e2, s1, x1) 
                    \<Longrightarrow> s \<in> guard e \<and> s = s1
                                \<and> e2 = AnonyEvent (Some (body e)) \<and> x1 = x (k := BasicEvent e)"
  apply(rule etran.cases)
  apply(simp)
  apply(simp add:get_actk_def)+
  done

lemma ent_spec2: "ec1 -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> ec2 
                    \<Longrightarrow> gets_e ec1 \<in> guard ev \<and> gets_e ec1 = gets_e ec2
                                \<and> getspc_e ec2 = AnonyEvent (Some (body ev)) \<and> getx_e ec2 = (getx_e ec1) (k := BasicEvent ev)"
  using getspc_e_def getx_e_def gets_e_def ent_spec2' by (metis surjective_pairing) 

lemma no_tran2basic0: "(e1, s, x) -et-t\<rightarrow> (e2, s1, x1) \<Longrightarrow> \<not>(\<exists>e. e2 = BasicEvent e)"
  apply(rule etran.cases)
  apply(simp)+
  done

lemma no_tran2basic: "\<not>(\<exists>t ec1. ec1 -et-t\<rightarrow> (BasicEvent ev, s, x))"
  using no_tran2basic0 by (metis prod.collapse) 

lemma noevtent_notran0: "(BasicEvent e, s, x) -et-(a\<sharp>k)\<rightarrow> (e2, s1, x1) \<Longrightarrow> a = EvtEnt (BasicEvent e)"
  apply(rule etran.cases)
  apply(simp)+
  apply(simp add:get_actk_def)
  done

lemma noevtent_notran: "ec1 = (BasicEvent e, s, x) \<Longrightarrow> \<not> (\<exists>k. ec1 -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> ec2) 
                        \<Longrightarrow> \<not> (ec1 -et-t\<rightarrow> ec2)"
  proof -
    assume p0: "ec1 = (BasicEvent e, s, x)" and
           p1: "\<not> (\<exists>k. ec1 -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> ec2)"
    then show "\<not> (ec1 -et-t\<rightarrow> ec2)"
      proof -
      {
        assume a0: "ec1 -et-t\<rightarrow> ec2"
        with p0 have a1: "getact t = EvtEnt (BasicEvent e)"  using getact_def noevtent_notran0 get_actk_def
          by (metis cases prod_cases3 select_convs(1))
        from a0 obtain k where "k = getk t" by auto
        with p1 a0 a1 have "ec1 -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> ec2" using get_actk_def getact_def 
          by (metis cases select_convs(1))
        with p1 have False by auto
      }
      then show ?thesis by auto
      qed
  qed


lemma evt_not_eq_in_tran_aux:"(P,s,x) -et-et\<rightarrow> (Q,t,y) \<Longrightarrow> P \<noteq> Q"
  apply(erule etran.cases)
  apply (simp add: prog_not_eq_in_ctran_aux)
  by simp
  

lemma evt_not_eq_in_tran [simp]: "\<not> (P,s,x) -et-et\<rightarrow> (P,t,y)"
apply clarify
apply(drule evt_not_eq_in_tran_aux)
apply simp
done

lemma evt_not_eq_in_tran2 [simp]: "\<not>(\<exists>et. (P,s,x) -et-et\<rightarrow> (P,t,y))" by simp

subsubsection \<open>Event Systems\<close>

lemma esconf_trip: "\<lbrakk>gets_es c = s; getspc_es c = spc; getx_es c = x\<rbrakk> \<Longrightarrow> c = (spc,s,x)"
  by (metis gets_es_def getspc_es_def getx_es_def prod.collapse)

lemma evtseq_tran_evtseq: 
  "\<lbrakk>(EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es2, t1, y1); es2 \<noteq> es\<rbrakk> \<Longrightarrow> \<exists>e. es2 = EvtSeq e es"
  apply(rule estran.cases)
  apply(simp)+
  done

lemma evtseq_tran_evtseq_anony: 
  "\<lbrakk>(EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es2, t1, y1); es2 \<noteq> es\<rbrakk> \<Longrightarrow> \<exists>e. es2 = EvtSeq e es \<and> is_anonyevt e"
  apply(rule estran.cases)
  apply(simp)+
  apply (metis event.exhaust is_anonyevt.simps(1) no_tran2basic0)
  by simp 

lemma evtseq_tran_evtsys: 
  "\<lbrakk>(EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es2, t1, y1); \<not>(\<exists>e. es2 = EvtSeq e es)\<rbrakk> \<Longrightarrow> es2 = es"
  apply(rule estran.cases)
  apply(simp)+
  done

lemma evtseq_tran_exist_etran: 
  "(EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (EvtSeq e2 es, t1, y1) \<Longrightarrow> \<exists>t. (e1, s1, x1) -et-t\<rightarrow> (e2, t1, y1)"
  apply(rule estran.cases)
  apply(simp)+
  apply blast
  by (metis add.right_neutral add_Suc_right esys.inject(1) esys.size(3) lessI not_less_eq trans_less_add2)

lemma evtseq_tran_0_exist_etran: 
  "(EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es, t1, y1) \<Longrightarrow> \<exists>t. (e1, s1, x1) -et-t\<rightarrow> (AnonyEvent (None), t1, y1)"
  apply(rule estran.cases)
     apply(simp)+
  apply (simp add: evtseq_ne_es)
  by blast
  

lemma notrans_to_basicevt_insameesys: 
  "\<lbrakk>(es1, s1, x1) -es-et\<rightarrow> (es2, s2, x2); \<exists>e. es1 = EvtSeq e esys\<rbrakk> \<Longrightarrow> \<not>(\<exists>e. es2 = EvtSeq (BasicEvent e) esys)"
  apply(rule estran.cases)
  apply simp
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
     apply (simp add: get_actk_def)+
  by (metis evtseq_ne_es)
  
lemma evtseq_tran_sys_or_seq:
  "(EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es2, t1, y1) \<Longrightarrow> es2 = es \<or> (\<exists>e. es2 = EvtSeq e es)"
  by (meson evtseq_tran_evtseq)

lemma evtseq_tran_sys_or_seq_anony:
  "(EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es2, t1, y1) \<Longrightarrow> es2 = es \<or> (\<exists>e. es2 = EvtSeq e es \<and> is_anonyevt e)"
  by (meson evtseq_tran_evtseq_anony)

lemma evtseq_no_evtent:
  "\<lbrakk>(EvtSeq e1 es, s1, x1) -es-t\<sharp>k\<rightarrow> (es2, s2, x2);is_anonyevt e1\<rbrakk> \<Longrightarrow> \<not>(\<exists>e. t = EvtEnt e)"
  apply(rule estran.cases)
  apply(simp)+
  apply(rule etran.cases)
  apply(simp add:get_actk_def)+
  apply(rule etran.cases)
  apply(simp add:get_actk_def)+
  done

lemma evtseq_no_evtent2:
  "\<lbrakk>esc1 -es-t\<sharp>k\<rightarrow> esc2; getspc_es esc1 = EvtSeq e esys; is_anonyevt e\<rbrakk> \<Longrightarrow> \<not>(\<exists>e. t = EvtEnt e)"
  proof -
    assume p0: "esc1 -es-t\<sharp>k\<rightarrow> esc2"
      and  p1: "getspc_es esc1 = EvtSeq e esys"
      and  p2: "is_anonyevt e"
    then obtain es1 and s1 and x1 where a1: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    from p0 obtain es2 and s2 and x2 where a2: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    from p1 a1 have "es1 = EvtSeq e esys" by (simp add:getspc_es_def)
    with p0 p2 a1 a2 show ?thesis using evtseq_no_evtent[of e esys s1 x1 t k es2 s2 x2]
      by simp
  qed

lemma esys_not_eseq: "getspc_es esc = EvtSys es \<Longrightarrow> \<not>(\<exists>e esys. getspc_es esc = EvtSeq e esys)"
  by(simp add:getspc_es_def)
  
lemma eseq_not_esys: "getspc_es esc = EvtSeq e esys \<Longrightarrow> \<not>(\<exists>es. getspc_es esc = EvtSys es)"
  by(simp add:getspc_es_def)

lemma evtent_is_basicevt: "(es, s, x) -es-EvtEnt e\<sharp>k\<rightarrow> (es', s', x') \<Longrightarrow> \<exists>e'. e = BasicEvent e'"
  apply(rule estran.cases)
  apply(simp add:get_actk_def)+
  apply(rule etran.cases)
  apply(simp add:get_actk_def)+
  apply(rule etran.cases)
  apply simp+
  apply(rule etran.cases)
  apply simp+
  apply auto[1]
  apply (metis ent_spec1 event.exhaust evtseq_no_evtent get_actk_def is_anonyevt.simps(1))+  
  done
  
lemma evtent_is_basicevt_inevtseq: "\<lbrakk>(EvtSeq e es,s1,x1) -es-EvtEnt e1\<sharp>k\<rightarrow> (esc2,s2,x2)\<rbrakk> 
    \<Longrightarrow> e = e1 \<and> (\<exists>e'. e = BasicEvent e')"
  apply(rule estran.cases)
  apply(simp add:get_actk_def)
  apply(rule etran.cases)
  apply(simp add:get_actk_def)+
  apply(rule etran.cases)
  apply(simp add:get_actk_def)+
  apply(rule etran.cases)
  apply(simp add:get_actk_def)+
  apply auto[1]
  by (metis ent_spec1 esys.inject(1) evtent_is_basicevt get_actk_def)
  
lemma evtent_is_basicevt_inevtseq2: "\<lbrakk>esc1 -es-EvtEnt e1\<sharp>k\<rightarrow> esc2; getspc_es esc1 = EvtSeq e es\<rbrakk> 
    \<Longrightarrow> e = e1 \<and> (\<exists>e'. e = BasicEvent e')"
  proof -
    assume p0: "esc1 -es-EvtEnt e1\<sharp>k\<rightarrow> esc2"
      and  p1: "getspc_es esc1 = EvtSeq e es"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately show ?thesis 
      using p0 p1 evtent_is_basicevt_inevtseq[of e es s1 x1 e1 k es2 s2 x2] getspc_es_def[of esc1] by auto
  qed

lemma evtsysent_evtent0: "(EvtSys es, s, x) -es-t\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1) \<Longrightarrow>
        s = s1 \<and> (\<exists>evt e. evt \<in> es \<and> evt = BasicEvent e \<and> Act t = EvtEnt (BasicEvent e) \<and>
            (BasicEvent e, s, x) -et-t\<rightarrow> (ev, s1, x1))"
  apply(rule estran.cases)
  apply(simp)
  prefer 2
  apply(simp)
  prefer 2
  apply(simp)
  apply(rule etran.cases)
  apply(simp)
  apply(simp add:get_actk_def)
  apply(rule conjI)
  apply(simp)
  using get_actk_def by (metis esys.inject(1) esys.inject(2) select_convs(1))

lemma evtsysent_evtent: "(EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1) \<Longrightarrow>
        s = s1 \<and> BasicEvent e \<in> es \<and> (BasicEvent e, s, x) -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (ev, s1, x1)"
  apply(rule estran.cases)
  apply(simp)+
  apply (metis ent_spec1)
  apply(simp)+
  done

lemma evtsysent_evtent2: "(EvtSys es, s, x) -es-(EvtEnt ev)\<sharp>k\<rightarrow> (esc2, s1,x1) \<Longrightarrow>
        s = s1 \<and> (ev\<in>es)"
  apply(rule estran.cases)
  apply(simp)+
  apply (metis ent_spec1)
  apply(simp)+
  done

lemma evtsysent_evtent3: "\<lbrakk>esc1 -es-(EvtEnt ev)\<sharp>k\<rightarrow> esc2; getspc_es esc1 = EvtSys es\<rbrakk> \<Longrightarrow>
        (ev\<in>es)"
  proof -
    assume p0: "esc1 -es-(EvtEnt ev)\<sharp>k\<rightarrow> esc2"
      and  p1: "getspc_es esc1 = EvtSys es"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    from p1 a0 have "es1 = EvtSys es" by (simp add:getspc_es_def)
    with a0 a1 p0 show ?thesis using evtsysent_evtent2[of es s1 x1 ev k es2 s2 x2] by simp
  qed


lemma evtsys_evtent: "(EvtSys es, s, x) -es-t\<rightarrow> (es2, s1,x1) \<Longrightarrow> \<exists>e. es2 = EvtSeq e (EvtSys es)"
  apply(rule estran.cases)
  apply(simp)+
  done

lemma act_in_es_notchgstate: "\<lbrakk>(es, s, x) -es-(Cmd c)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> \<Longrightarrow> x = x'"
  apply(rule estran.cases)
  by (simp add: get_actk_def)+

lemma cmd_enable_impl_anonyevt: 
    "\<lbrakk>(es, s, x) -es-(Cmd c)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> 
        \<Longrightarrow> \<exists>e e' es1. es = EvtSeq e es1 \<and> e = AnonyEvent e'"
  apply(rule estran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  done

lemma cmd_enable_impl_notesys: 
    "\<lbrakk>(es, s, x) -es-(Cmd c)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> 
        \<Longrightarrow> \<not>(\<exists>ess. es = EvtSys ess)"
  apply(rule estran.cases)
  apply (simp add: get_actk_def)+
  done

lemma cmd_enable_impl_notesys2: 
    "\<lbrakk>esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2\<rbrakk> 
        \<Longrightarrow> \<not>(\<exists>ess. getspc_es esc1 = EvtSys ess)"
  proof -
    assume p0: "esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately show ?thesis using p0 cmd_enable_impl_notesys[of es1 s1 x1 c k es2 s2 x2] getspc_es_def[of esc1]
      by simp
  qed

lemma cmd_enable_impl_anonyevt2: 
    "\<lbrakk>esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2\<rbrakk> 
        \<Longrightarrow> \<exists>e e' es1. getspc_es esc1 = EvtSeq e es1 \<and> e = AnonyEvent e'"
  proof -
    assume p0: "esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately show ?thesis using p0 cmd_enable_impl_anonyevt[of es1 s1 x1 c k es2 s2 x2] getspc_es_def[of esc1]
      by simp
  qed

lemma entevt_notchgstate: "\<lbrakk>(es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> \<Longrightarrow> s = s'"
  apply(rule estran.cases)
  apply(simp)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply auto
  using ent_spec2' get_actk_def by metis 

lemma entevt_ines_notchg_otherx: "\<lbrakk>(es, s, x) -es-(EvtEnt e)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> \<Longrightarrow> (\<forall>k'. k'\<noteq>k \<longrightarrow> x k' = x' k')"
  apply(rule estran.cases)
  apply(simp)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  done

lemma entevt_ines_notchg_otherx2: "\<lbrakk>esc1 -es-(EvtEnt e)\<sharp>k\<rightarrow> esc2\<rbrakk> 
          \<Longrightarrow> (\<forall>k'. k'\<noteq>k \<longrightarrow> (getx_es esc1) k' = (getx_es esc2) k')"
  proof -
    assume p0: "esc1 -es-(EvtEnt e)\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately have "\<forall>k'. k'\<noteq>k \<longrightarrow> x1 k' = x2 k'" 
      using entevt_ines_notchg_otherx[of es1 s1 x1 e k es2 s2 x2] p0 by simp
    with a0 a1 show ?thesis using getx_es_def by (metis snd_conv) 
  qed

lemma cmd_ines_nchg_x: "\<lbrakk>(es, s, x) -es-(Cmd c)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> \<Longrightarrow> (\<forall>k. x' k = x k)"
  apply(rule estran.cases)
  apply(simp)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  done

lemma cmd_ines_nchg_x2: "\<lbrakk>esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2\<rbrakk> \<Longrightarrow> (\<forall>k. (getx_es esc2) k = (getx_es esc1) k)" 
  proof -
    assume p0: "esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately have "\<forall>k. x1 k = x2 k" using cmd_ines_nchg_x [of es1 s1 x1 c k es2 s2 x2] p0 by simp
    with a0 a1 show ?thesis using getx_es_def by (metis snd_conv) 
  qed

lemma entevt_ines_chg_selfx: "\<lbrakk>(es, s, x) -es-(EvtEnt e)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> \<Longrightarrow> x' k = e"
  apply(rule estran.cases)
  apply(simp)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply (simp add: fun_upd_idem_iff)
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  done

lemma entevt_ines_chg_selfx2: "\<lbrakk>esc1 -es-(EvtEnt e)\<sharp>k\<rightarrow> esc2\<rbrakk> \<Longrightarrow> (getx_es esc2) k = e" 
  proof -
    assume p0: "esc1 -es-(EvtEnt e)\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately have "x2 k = e" using entevt_ines_chg_selfx p0 by auto
    with a1 show ?thesis using getx_es_def by (metis snd_conv) 
  qed

lemma estran_impl_evtentorcmd: "\<lbrakk>(es, s, x) -es-t\<rightarrow> (es', s', x')\<rbrakk> 
  \<Longrightarrow> (\<exists>e k. (es, s, x) -es-EvtEnt e\<sharp>k\<rightarrow> (es', s', x')) \<or> (\<exists>c k. (es, s, x) -es-Cmd c\<sharp>k\<rightarrow> (es', s', x'))" 
  apply(rule estran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply auto
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply auto
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  done

lemma estran_impl_evtentorcmd': "\<lbrakk>(es, s, x) -es-t\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> 
  \<Longrightarrow> (\<exists>e. (es, s, x) -es-EvtEnt e\<sharp>k\<rightarrow> (es', s', x')) \<or> (\<exists>c. (es, s, x) -es-Cmd c\<sharp>k\<rightarrow> (es', s', x'))" 
  apply(rule estran.cases)
  apply simp
  apply (metis get_actk_def iffs)
  apply(rule etran.cases)
  apply simp
  apply (metis get_actk_def iffs)
  apply (metis get_actk_def iffs)
  apply(rule etran.cases)
  apply simp
  apply (metis get_actk_def iffs)
  apply (metis get_actk_def iffs)
  done

lemma estran_impl_evtentorcmd2: "\<lbrakk>esc1 -es-t\<rightarrow> esc2\<rbrakk> 
  \<Longrightarrow> (\<exists>e k. esc1 -es-EvtEnt e\<sharp>k\<rightarrow> esc2) \<or> (\<exists>c k. esc1 -es-Cmd c\<sharp>k\<rightarrow> esc2)" 
  proof -
    assume p0: "esc1 -es-t\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately show ?thesis using p0 estran_impl_evtentorcmd[of es1 s1 x1 t es2 s2 x2] by simp 
  qed

lemma estran_impl_evtentorcmd2': "\<lbrakk>esc1 -es-t\<sharp>k\<rightarrow> esc2\<rbrakk> 
  \<Longrightarrow> (\<exists>e. esc1 -es-EvtEnt e\<sharp>k\<rightarrow> esc2) \<or> (\<exists>c. esc1 -es-Cmd c\<sharp>k\<rightarrow> esc2)" 
  proof -
    assume p0: "esc1 -es-t\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately show ?thesis using p0 estran_impl_evtentorcmd'[of es1 s1 x1 t k es2 s2 x2] by simp 
  qed

  
subsubsection \<open>Parallel Event Systems\<close>

lemma pesconf_trip: "\<lbrakk>gets c = s; getspc c = spc; getx c = x\<rbrakk> \<Longrightarrow> c = (spc,s,x)"
  by (metis gets_def getspc_def getx_def prod.collapse)

lemma pestran_estran: "\<lbrakk>(pes, s, x) -pes-(a\<sharp>k)\<rightarrow> (pes', s', x')\<rbrakk> \<Longrightarrow> 
              \<exists>es'. ((pes k, s, x) -es-(a\<sharp>k)\<rightarrow> (es', s', x')) \<and> pes' = pes(k:=es')"
  apply(rule pestran.cases)
  apply(simp)
  apply(simp add:get_actk_def)
  by auto

lemma act_in_pes_notchgstate: "\<lbrakk>(pes, s, x) -pes-(Cmd c)\<sharp>k\<rightarrow> (pes', s', x')\<rbrakk> \<Longrightarrow> x = x'"
  apply(rule pestran.cases)
  apply (simp add: get_actk_def)+
  apply(rule estran.cases)
  apply (simp add: get_actk_def)+
  done

lemma evtent_in_pes_notchgstate: "\<lbrakk>(pes, s, x) -pes-(EvtEnt e)\<sharp>k\<rightarrow> (pes', s', x')\<rbrakk> \<Longrightarrow> s = s'"
  apply(rule pestran.cases)
  apply (simp add: get_actk_def)+
  apply(rule estran.cases)
  apply (simp add: get_actk_def)+
  apply (metis entevt_notchgstate evtent_is_basicevt get_actk_def)
  by (metis entevt_notchgstate evtent_is_basicevt get_actk_def)
  
lemma evtent_in_pes_notchgstate2: "\<lbrakk>esc1 -pes-(EvtEnt e)\<sharp>k\<rightarrow> esc2\<rbrakk> \<Longrightarrow> gets esc1 = gets esc2"
  using evtent_in_pes_notchgstate by (metis pesconf_trip) 

end