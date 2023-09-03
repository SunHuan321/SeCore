section \<open>The Proof System of PiCore\<close>

theory Ann_PiCore_Hoare
imports Ann_PiCore_Validity
begin

subsection \<open>Proof System for Programs\<close>

declare Un_subset_iff [simp del] sup.bounded_iff [simp del]

definition stable :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
  "stable \<equiv> \<lambda>f g. (\<forall>x y. x \<in> f \<longrightarrow> (x, y) \<in> g \<longrightarrow> y \<in> f)"

inductive rghoare_p :: "['s ann_prog, 's set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
    ("\<turnstile> _ sat\<^sub>p [_, _, _, _]" [60,0,0,0,0] 45)
where
  Basic: "\<lbrakk> pre \<subseteq> r; r \<subseteq> {s. f s \<in> post}; {(s,t). s \<in> r \<and> (t=f s)} \<subseteq> guar;
            stable r rely; stable post rely\<rbrakk>
           \<Longrightarrow> \<turnstile> AnnBasic r f sat\<^sub>p [pre, rely, guar, post]"
| Seq: "\<lbrakk> \<turnstile> P sat\<^sub>p [pre, rely, guar, mid]; \<turnstile> Q sat\<^sub>p [mid, rely, guar, post] \<rbrakk>
           \<Longrightarrow> \<turnstile> AnnSeq P Q sat\<^sub>p [pre, rely, guar, post]"
| Cond: "\<lbrakk> pre \<subseteq> r;  stable r rely; \<turnstile> P1 sat\<^sub>p [r \<inter> b, rely, guar, post];
           \<turnstile> P2 sat\<^sub>p [r \<inter> -b, rely, guar, post]; \<forall>s. (s,s)\<in>guar \<rbrakk>
          \<Longrightarrow> \<turnstile> AnnCond r b P1 P2 sat\<^sub>p [pre, rely, guar, post]"
| While: "\<lbrakk> pre \<subseteq> r; stable r rely; (r \<inter> -b) \<subseteq> post; stable post rely;
            \<turnstile> P sat\<^sub>p [r \<inter> b, rely, guar, r]; \<forall>s. (s,s)\<in>guar \<rbrakk>
          \<Longrightarrow> \<turnstile> AnnWhile r b P sat\<^sub>p [pre, rely, guar, post]"
| Await: "\<lbrakk>  pre \<subseteq> r; stable r rely; stable post rely;
            \<forall>V. \<turnstile> P sat\<^sub>p [r \<inter> b \<inter> {V}, {(s, t). s = t},
                UNIV, {s. (V, s) \<in> guar} \<inter> post] \<rbrakk>
           \<Longrightarrow> \<turnstile> AnnAwait r b P sat\<^sub>p [pre, rely, guar, post]"
| Nondt: "\<lbrakk>pre \<subseteq> r; stable r rely;
           r \<subseteq> {s. (\<forall>t. (s,t) \<in> f \<longrightarrow> t \<in> post) \<and> (\<exists>t. (s,t) \<in> f)}; 
            {(s,t). s \<in> r \<and> (s,t)\<in>f} \<subseteq> guar;  stable post rely\<rbrakk>
           \<Longrightarrow> \<turnstile> AnnNondt r f sat\<^sub>p [pre, rely, guar, post]"
| Conseq: "\<lbrakk> pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
             \<turnstile> P sat\<^sub>p [pre', rely', guar', post'] \<rbrakk>
            \<Longrightarrow> \<turnstile> P sat\<^sub>p [pre, rely, guar, post]"

subsection \<open>Rely-guarantee Condition\<close>

record 's rgformula =
    pre_rgf :: "'s set"
    rely_rgf :: "('s \<times> 's) set"
    guar_rgf :: "('s \<times> 's) set"
    post_rgf :: "'s set"    

definition getrgformula :: 
    "'s set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> 's rgformula" ("RG[_,_,_,_]" [91,91,91,91] 90)
      where "getrgformula pre r g pst \<equiv> \<lparr>pre_rgf = pre, rely_rgf = r, guar_rgf = g, post_rgf = pst\<rparr>"

definition Pre\<^sub>f :: "'s rgformula \<Rightarrow> 's set"
  where "Pre\<^sub>f rg = pre_rgf rg"

definition Rely\<^sub>f :: "'s rgformula \<Rightarrow> ('s \<times> 's) set"
  where "Rely\<^sub>f rg = rely_rgf rg"

definition Guar\<^sub>f :: "'s rgformula \<Rightarrow> ('s \<times> 's) set"
  where "Guar\<^sub>f rg = guar_rgf rg"

definition Post\<^sub>f :: "'s rgformula \<Rightarrow> 's set"
  where "Post\<^sub>f rg = post_rgf rg"

type_synonym ('l,'k,'s) rgformula_e = "('l,'k,'s) event \<times> 's rgformula"


datatype ('l,'k,'s) rgformula_ess = 
      rgf_EvtSeq "('l,'k,'s) rgformula_e" "('l,'k,'s) rgformula_ess \<times> 's rgformula"
    | rgf_EvtSys "('l,'k,'s) rgformula_e set"

type_synonym ('l,'k,'s) rgformula_es =
  "('l,'k,'s) rgformula_ess \<times> 's rgformula"

type_synonym ('l,'k,'s) rgformula_par =
  "'k \<Rightarrow> ('l,'k,'s) rgformula_es"

definition E\<^sub>e :: "('l,'k,'s) rgformula_e \<Rightarrow> ('l,'k,'s) event"
  where "E\<^sub>e rg = fst rg"

definition Pre\<^sub>e :: "('l,'k,'s) rgformula_e \<Rightarrow> 's set"
  where "Pre\<^sub>e rg = pre_rgf (snd rg)"

definition Rely\<^sub>e :: "('l,'k,'s) rgformula_e \<Rightarrow> ('s \<times> 's) set"
  where "Rely\<^sub>e rg = rely_rgf (snd rg)"

definition Guar\<^sub>e :: "('l,'k,'s) rgformula_e \<Rightarrow> ('s \<times> 's) set"
  where "Guar\<^sub>e rg = guar_rgf (snd rg)"

definition Post\<^sub>e :: "('l,'k,'s) rgformula_e \<Rightarrow> 's set"
  where "Post\<^sub>e  rg = post_rgf (snd rg)"


definition Pre\<^sub>e\<^sub>s :: "('l,'k,'s) rgformula_es \<Rightarrow> 's set"
  where "Pre\<^sub>e\<^sub>s rg = pre_rgf (snd rg)"

definition Rely\<^sub>e\<^sub>s :: "('l,'k,'s) rgformula_es \<Rightarrow> ('s \<times> 's) set"
  where "Rely\<^sub>e\<^sub>s rg = rely_rgf (snd rg)"

definition Guar\<^sub>e\<^sub>s :: "('l,'k,'s) rgformula_es \<Rightarrow> ('s \<times> 's) set"
  where "Guar\<^sub>e\<^sub>s rg = guar_rgf (snd rg)"

definition Post\<^sub>e\<^sub>s :: "('l,'k,'s) rgformula_es \<Rightarrow> 's set"
  where "Post\<^sub>e\<^sub>s  rg = post_rgf (snd rg)"

fun evtsys_spec :: "('l,'k,'s) rgformula_ess \<Rightarrow> ('l,'k,'s) esys" where
  evtsys_spec_evtseq: "evtsys_spec (rgf_EvtSeq ef esf) = EvtSeq (E\<^sub>e ef) (evtsys_spec (fst esf))" |
  evtsys_spec_evtsys: "evtsys_spec (rgf_EvtSys esf) = EvtSys (Domain esf)"

definition paresys_spec :: "('l,'k,'s) rgformula_par \<Rightarrow> ('l,'k,'s) paresys"
  where "paresys_spec pesf \<equiv> \<lambda>k. evtsys_spec (fst (pesf k))"

subsection \<open>Proof System for Events\<close>

inductive rghoare_e :: "[('l,'k,'s) event, 's set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
    ("\<turnstile> _ sat\<^sub>e [_, _, _, _]" [60,0,0,0,0] 45)
where
  AnonyEvt: " \<turnstile> P sat\<^sub>p [pre, rely, guar, post] \<Longrightarrow> \<turnstile> AnonyEvent (Some P) sat\<^sub>e [pre, rely, guar, post]"

| BasicEvt: "\<lbrakk> \<turnstile> body ev sat\<^sub>p [pre\<inter>(guard ev), rely, guar, post]; 
          stable pre rely; \<forall>s. (s, s)\<in>guar\<rbrakk> \<Longrightarrow> \<turnstile> BasicEvent ev sat\<^sub>e [pre, rely, guar, post]"

| Evt_conseq: "\<lbrakk> pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
                       \<turnstile> ev sat\<^sub>e [pre', rely', guar', post'] \<rbrakk>
                      \<Longrightarrow> \<turnstile> ev sat\<^sub>e [pre, rely, guar, post]"


subsection \<open>Proof System for Event Systems\<close>
inductive rghoare_es :: "[('l,'k,'s) rgformula_ess, 's set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
    ("\<turnstile> _ sat\<^sub>s [_, _, _, _]" [60,0,0,0,0] 45)
where
  EvtSeq_h: "\<lbrakk> \<turnstile> E\<^sub>e ef sat\<^sub>e [Pre\<^sub>e ef, Rely\<^sub>e ef, Guar\<^sub>e ef, Post\<^sub>e ef]; 
              \<turnstile> fst esf sat\<^sub>s [Pre\<^sub>f (snd esf), Rely\<^sub>f (snd esf), Guar\<^sub>f (snd esf), Post\<^sub>f (snd esf)]; 
              pre = Pre\<^sub>e ef; post = Post\<^sub>f (snd esf);
              rely \<subseteq> Rely\<^sub>e ef; rely \<subseteq>Rely\<^sub>f (snd esf); 
              Guar\<^sub>e ef \<subseteq> guar; Guar\<^sub>f (snd esf) \<subseteq> guar; 
              Post\<^sub>e ef \<subseteq> Pre\<^sub>f (snd esf)\<rbrakk> 
              \<Longrightarrow> \<turnstile> (rgf_EvtSeq ef esf) sat\<^sub>s [pre, rely, guar, post]"

| EvtSys_h: "\<lbrakk>\<forall>ef\<in> esf. \<turnstile> E\<^sub>e ef sat\<^sub>e [Pre\<^sub>e ef, Rely\<^sub>e ef, Guar\<^sub>e ef, Post\<^sub>e ef];
             \<forall>ef\<in> esf. pre \<subseteq> Pre\<^sub>e ef;  \<forall>ef\<in> esf. rely \<subseteq> Rely\<^sub>e ef;
             \<forall>ef\<in> esf. Guar\<^sub>e ef \<subseteq> guar; \<forall>ef\<in> esf. Post\<^sub>e ef \<subseteq> post;
             \<forall>ef1 ef2. ef1\<in> esf \<and> ef2\<in> esf \<longrightarrow> Post\<^sub>e ef1 \<subseteq> Pre\<^sub>e ef2;
             stable pre rely; \<forall>s. (s, s)\<in>guar\<rbrakk>
             \<Longrightarrow> \<turnstile> rgf_EvtSys esf sat\<^sub>s [pre, rely, guar, post]"

| EvtSys_conseq: "\<lbrakk> pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
                       \<turnstile> esys sat\<^sub>s [pre', rely', guar', post'] \<rbrakk>
                      \<Longrightarrow> \<turnstile> esys sat\<^sub>s [pre, rely, guar, post]"

subsection \<open>Proof System for Parallel Event Systems\<close>
inductive rghoare_pes :: "[('l,'k,'s) rgformula_par, 's set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
          ("\<turnstile> _ SAT [_, _, _, _]" [60,0,0,0,0] 45) 
where
  ParallelESys: "\<lbrakk>\<forall>k. \<turnstile> fst (pesf k) sat\<^sub>s [Pre\<^sub>e\<^sub>s (pesf k), Rely\<^sub>e\<^sub>s (pesf k), Guar\<^sub>e\<^sub>s (pesf k), Post\<^sub>e\<^sub>s (pesf k)]; 
                  \<forall>k. pre \<subseteq> Pre\<^sub>e\<^sub>s (pesf k); 
                  \<forall>k. rely \<subseteq> Rely\<^sub>e\<^sub>s (pesf k); 
                  \<forall>k j. j\<noteq>k \<longrightarrow>  Guar\<^sub>e\<^sub>s (pesf j) \<subseteq> Rely\<^sub>e\<^sub>s (pesf k);
                  \<forall>k. Guar\<^sub>e\<^sub>s (pesf k) \<subseteq> guar;
                  \<forall>k. Post\<^sub>e\<^sub>s (pesf k) \<subseteq> post\<rbrakk> 
              \<Longrightarrow> \<turnstile> pesf SAT [pre, rely, guar, post]"

| ParallelESys_conseq: "\<lbrakk> pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
                       \<turnstile> pesf SAT [pre', rely', guar', post'] \<rbrakk>
                      \<Longrightarrow> \<turnstile> pesf SAT [pre, rely, guar, post]"

section \<open>Soundness\<close>

subsection \<open>Some previous lemmas\<close>

subsubsection \<open>program\<close>
lemma tl_of_assum_in_assum:
  "(P, s) # (P, t) # xs \<in> assume_p (pre, rely) \<Longrightarrow> stable pre rely
  \<Longrightarrow> (P, t) # xs \<in> assume_p (pre, rely)"
apply(simp add:assume_p_def)
apply clarify
apply(rule conjI)
 apply(erule_tac x=0 in allE)
 apply(simp (no_asm_use)only:stable_def)
 apply(erule allE,erule allE,erule impE,assumption,erule mp)
 apply(simp add:EnvP)
apply(simp add:getspc_p_def gets_p_def)
apply clarify
apply (fastforce)
done

lemma etran_in_comm:
  "(P, t) # xs \<in> commit_p(guar, post) \<Longrightarrow> (P, s) # (P, t) # xs \<in> commit_p(guar, post)"
apply(simp add:commit_p_def)
apply(simp add:getspc_p_def gets_p_def)
apply clarify
apply(case_tac i,fastforce+)
done

lemma ctran_in_comm:
  "\<lbrakk>(t, s) \<in> guar; t \<in> ann_pre_p P ; (Q, s) # xs \<in> commit_p(guar, post)\<rbrakk>
  \<Longrightarrow> (P, t) # (Q, s) # xs \<in> commit_p(guar, post)"
  apply(simp add:commit_p_def)
  apply(simp add:getspc_p_def gets_p_def)
  apply clarify
  apply(case_tac i, simp)
  by auto

lemma takecptn_is_cptn [rule_format, elim!]:
  "\<forall>j. c \<in> cpts_p \<longrightarrow> take (Suc j) c \<in> cpts_p"
apply(induct "c")
 apply(force elim: cpts_p.cases)
apply clarify
apply(case_tac j)
 apply simp
 apply(rule CptsPOne)
apply simp
apply(force intro:cpts_p.intros elim:cpts_p.cases)
done

lemma dropcptn_is_cptn [rule_format,elim!]:
  "\<forall>j<length c. c \<in> cpts_p \<longrightarrow> drop j c \<in> cpts_p"
apply(induct "c")
 apply(force elim: cpts_p.cases)
apply clarify
apply(case_tac j,simp+)
apply(erule cpts_p.cases)
  apply simp
 apply force
apply force
done

lemma segcptn_is_cptn: "\<lbrakk>l \<in> cpts_p; n < length l; m < n\<rbrakk> 
                    \<Longrightarrow> take (n - m + 1) (drop m l) \<in> cpts_p"
  by (metis Suc_eq_plus1 dropcptn_is_cptn dual_order.strict_trans takecptn_is_cptn)

lemma tl_of_cptn_is_cptn: "\<lbrakk>x # xs \<in> cpts_p; xs \<noteq> []\<rbrakk> \<Longrightarrow> xs  \<in> cpts_p"
apply(subgoal_tac "1 < length (x # xs)")
 apply(drule dropcptn_is_cptn,simp+)
done

lemma notran_p_confeq0: "\<lbrakk>l \<in> cpts_p; Suc 0 < length l; \<not> (l ! 0 -c\<rightarrow> l ! 1)\<rbrakk>
                      \<Longrightarrow> getspc_p (l ! 0) = getspc_p (l ! 1)"
  apply(simp)
  apply(rule cpts_p.cases)
  apply(simp)+
  apply(simp add:getspc_p_def)+
  done

lemma petran_eqconf: "(p1, s1) -pe\<rightarrow> (p2, s2) \<Longrightarrow> p1 = p2"
  apply(rule petran.cases)
  apply(simp)+
  done

lemma notran_p_confeqi: "\<lbrakk>l \<in> cpts_p; Suc i < length l; \<not> (l ! i -c\<rightarrow> l ! Suc i)\<rbrakk>
                      \<Longrightarrow> getspc_p (l ! i) = getspc_p (l ! (Suc i))"
  proof -
    assume p0: "l \<in> cpts_p" and
           p1: "Suc i < length l" and
           p2: "\<not> (l ! i -c\<rightarrow> l ! Suc i)"
    have "\<forall>l i. l \<in> cpts_p \<and>  Suc i < length l \<and> \<not> (l ! i -c\<rightarrow> l ! Suc i)
                \<longrightarrow> getspc_p (l ! i) = getspc_p (l ! (Suc i))"
      proof -
      {
        fix l i
        assume a0: "l \<in> cpts_p \<and> Suc i < length l \<and> \<not> (l ! i -c\<rightarrow> l ! Suc i)"
        then have "getspc_p (l ! i) = getspc_p (l ! (Suc i))"
          proof(induct i)
            case 0 show ?case by (simp add: "0.prems" notran_p_confeq0) 
          next
            case (Suc j)
            let ?subel = "drop (Suc j) l"
            assume b0: "l \<in> cpts_p \<and> Suc (Suc j) < length l \<and> \<not> (l ! Suc j -c\<rightarrow> l ! Suc (Suc j))"            
            then have b1: "?subel \<in> cpts_p" by (simp add: Suc_lessD b0 dropcptn_is_cptn) 
            from b0 have b2: "Suc 0 < length ?subel" by auto 
            from b0 have b3: "\<not> (?subel ! 0 -c\<rightarrow> ?subel ! 1)" by auto
            with b1 b2 have b3: "getspc_p (?subel ! 0) = getspc_p (?subel ! 1)"
              using notran_p_confeq0 by blast
            then show ?case
              by (metis Cons_nth_drop_Suc One_nat_def Suc_lessD b0 nth_Cons_0 nth_Cons_Suc) 
          qed
      }
      then show ?thesis by auto
    qed
    with p0 p1 p2 show ?thesis by auto
  qed

lemma notran_p_confeqi1: "\<lbrakk>l \<in> cpts_p; \<forall>i. Suc i < length l \<longrightarrow> \<not> (l ! i -c\<rightarrow> l ! Suc i); j < length l\<rbrakk>
                      \<Longrightarrow> getspc_p (l ! 0) = getspc_p (l ! j)"
  apply (induct j, simp)
  apply clarsimp
  apply (erule_tac x = j in allE)
  using notran_p_confeqi by blast

lemma notran_p_seg_aux : "\<lbrakk>take (n - m + 1) (drop m l) \<in> cpts_p; m < n; n < length l; \<forall>i. i \<ge> m \<and> i < n \<longrightarrow> 
        \<not> (l ! i -c\<rightarrow> l ! Suc i)\<rbrakk> \<Longrightarrow>  getspc_p (l ! m) = getspc_p (l ! n)"
  apply (drule_tac j = "n - m" in notran_p_confeqi1, simp_all)
  by (simp add: less_diff_conv)

lemma notran_seg_take: "\<lbrakk>l \<in> cpts_p; m < n; n < length l; \<forall>i. i \<ge> m \<and> i < n \<longrightarrow> 
                          \<not> (l ! i -c\<rightarrow> l ! Suc i)\<rbrakk> \<Longrightarrow> getspc_p (l ! m) = getspc_p (l ! n)"
  apply (rule notran_p_seg_aux, simp_all)
  by (metis Suc_eq_plus1 segcptn_is_cptn)
 
lemma not_ctran_None [rule_format]:
  "\<forall>s. (None, s)#xs \<in> cpts_p \<longrightarrow> (\<forall>i<length xs. ((None, s)#xs)!i -pe\<rightarrow> xs!i)"
apply(induct xs,simp+)
apply clarify
apply(erule cpts_p.cases,simp)
 apply simp
 apply(case_tac i,simp)
  apply(rule EnvP)
 apply simp
apply(force elim:ptran.cases)
  done

lemma cptn_not_empty [simp]:"[] \<notin> cpts_p"
apply(force elim:cpts_p.cases)
done

lemma etran_or_ctran [rule_format]:
  "\<forall>m i. x\<in>cpts_p \<longrightarrow> m \<le> length x
   \<longrightarrow> (\<forall>i. Suc i < m \<longrightarrow> \<not> x!i -c\<rightarrow> x!Suc i) \<longrightarrow> Suc i < m
   \<longrightarrow> x!i -pe\<rightarrow> x!Suc i"
apply(induct x,simp)
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp)
  apply(rule EnvP)
 apply simp
 apply(erule_tac x="m - 1" in allE)
 apply(case_tac m,simp,simp)
 apply(subgoal_tac "(\<forall>i. Suc i < nata \<longrightarrow> (((P, t) # xs) ! i, xs ! i) \<notin> ptran)")
  apply force
 apply clarify
 apply(erule_tac x="Suc ia" in allE,simp)
apply(erule_tac x="0" and P="\<lambda>j. H j \<longrightarrow> (J j) \<notin> ptran" for H J in allE,simp)
done

lemma etran_or_ctran2 [rule_format]:
  "\<forall>i. Suc i<length x \<longrightarrow> x\<in>cpts_p \<longrightarrow> (x!i -c\<rightarrow> x!Suc i \<longrightarrow> \<not> x!i -pe\<rightarrow> x!Suc i)
  \<or> (x!i -pe\<rightarrow> x!Suc i \<longrightarrow> \<not> x!i -c\<rightarrow> x!Suc i)"
apply(induct x)
 apply simp
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp+)
apply(case_tac i,simp)
 apply(force elim:petran.cases)
apply simp
done

lemma etran_or_ctran2_disjI1:
  "\<lbrakk> x\<in>cpts_p; Suc i<length x; x!i -c\<rightarrow> x!Suc i\<rbrakk> \<Longrightarrow> \<not> x!i -pe\<rightarrow> x!Suc i"
by(drule etran_or_ctran2,simp_all)

lemma etran_or_ctran2_disjI2:
  "\<lbrakk> x\<in>cpts_p; Suc i<length x; x!i -pe\<rightarrow> x!Suc i\<rbrakk> \<Longrightarrow> \<not> x!i -c\<rightarrow> x!Suc i"
by(drule etran_or_ctran2,simp_all)


lemma not_ctran_None2 [rule_format]:
  "\<lbrakk> (None, s) # xs \<in>cpts_p; i<length xs\<rbrakk> \<Longrightarrow> \<not> ((None, s) # xs) ! i -c\<rightarrow> xs ! i"
apply(frule not_ctran_None,simp)
apply(case_tac i,simp)
 apply(force elim:petranE)
apply simp
apply(rule etran_or_ctran2_disjI2,simp_all)
apply(force intro:tl_of_cptn_is_cptn)
done

lemma not_ctran_None3 [rule_format]:
  "\<lbrakk> (None, s) # xs \<in>cpts_p; i<length xs\<rbrakk> \<Longrightarrow> getspc_p (xs ! i) = None "
  apply (induct i, simp)
   apply (drule_tac i = 0 in not_ctran_None, simp)
   apply (metis fstI getspc_p_def nth_Cons_0 petranE)
  apply (subgoal_tac "getspc_p (xs ! i) = None")
   apply (drule_tac i = "Suc i" in not_ctran_None, simp)
   apply (metis fstI getspc_p_def nth_Cons_Suc petranE)
  using Suc_lessD by blast

lemma not_ctran_None3' [rule_format]:
  "\<lbrakk>xs \<in>cpts_p; i<length xs; getspc_p (xs ! 0) = None\<rbrakk> \<Longrightarrow> getspc_p (xs ! i) = None"
  apply (case_tac xs, simp)
  apply (case_tac a)
  apply (case_tac aa)
   apply (simp add: cpts_p.CptsPEnv not_ctran_None3)
  by (simp add: getspc_p_def)

lemma not_ctran_Finish [rule_format]:
  "\<lbrakk>xs \<in> cpts_p; i<length xs; getspc_p (xs ! i) = None; j \<ge> i; j < length xs\<rbrakk> 
    \<Longrightarrow> getspc_p (xs ! j) = None"
proof-
  assume a1: "xs \<in> cpts_p"
    and  a2: "i < length xs"
    and  a3: "getspc_p (xs ! i) = None"
    and  a4: "j \<ge> i"
    and  a5: "j < length xs"
  from a1 a2 have "drop i xs \<in> cpts_p" by (simp add: dropcptn_is_cptn)
  with a2 a3 a4 a5 show ?thesis
    by (drule_tac xs = "drop i xs" and i = "j - i" in not_ctran_None3', simp_all)
qed

lemma Ex_first_occurrence [rule_format]: "P (n::nat) \<longrightarrow> (\<exists>m. P m \<and> (\<forall>i<m. \<not> P i))"
apply(rule nat_less_induct)
apply clarify
apply(case_tac "\<forall>m. m<n \<longrightarrow> \<not> P m")
apply auto
done

lemma stability [rule_format]:
  "\<forall>j k. x \<in> cpts_p \<longrightarrow> stable p rely \<longrightarrow> j\<le>k \<longrightarrow> k<length x \<longrightarrow> snd(x!j)\<in>p  \<longrightarrow>
  (\<forall>i. (Suc i)<length x \<longrightarrow>
          (x!i -pe\<rightarrow> x!(Suc i)) \<longrightarrow> (snd(x!i), snd(x!(Suc i))) \<in> rely) \<longrightarrow>
  (\<forall>i. j\<le>i \<and> i<k \<longrightarrow> x!i -pe\<rightarrow> x!Suc i) \<longrightarrow> snd(x!k)\<in>p \<and> fst(x!j)=fst(x!k)"
apply(induct x)
 apply clarify
 apply(force elim:cpts_p.cases)
apply clarify
apply(erule cpts_p.cases,simp)
 apply simp
 apply(case_tac k,simp,simp)
 apply(case_tac j,simp)
  apply(erule_tac x=0 in allE)
  apply(erule_tac x="nat" and P="\<lambda>j. (0\<le>j) \<longrightarrow> (J j)" for J in allE,simp)
  apply(subgoal_tac "t\<in>p")
   apply(subgoal_tac "(\<forall>i. i < length xs \<longrightarrow> ((P, t) # xs) ! i -pe\<rightarrow> xs ! i \<longrightarrow> (snd (((P, t) # xs) ! i), snd (xs ! i)) \<in> rely)")
    apply clarify
    apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>petran" for H J in allE,simp)
   apply clarify
   apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j) \<longrightarrow> (T j)\<in>rely" for H J T in allE,simp)
  apply(erule_tac x=0 and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>petran \<longrightarrow> T j" for H J T in allE,simp)
  apply(simp(no_asm_use) only:stable_def)
  apply(erule_tac x=s in allE)
  apply(erule_tac x=t in allE)
  apply simp
  apply(erule mp)
  apply(erule mp)
  apply(rule EnvP)
 apply simp
 apply(erule_tac x="nata" in allE)
 apply(erule_tac x="nat" and P="\<lambda>j. (s\<le>j) \<longrightarrow> (J j)" for s J in allE,simp)
 apply(subgoal_tac "(\<forall>i. i < length xs \<longrightarrow> ((P, t) # xs) ! i -pe\<rightarrow> xs ! i \<longrightarrow> (snd (((P, t) # xs) ! i), snd (xs ! i)) \<in> rely)")
  apply clarify
  apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>petran" for H J in allE,simp)
 apply clarify
 apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j) \<longrightarrow> (T j)\<in>rely" for H J T in allE,simp)
apply(case_tac k,simp,simp)
apply(case_tac j)
 apply(erule_tac x=0 and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>petran" for H J in allE,simp)
 apply(erule petran.cases,simp)
apply(erule_tac x="nata" in allE)
apply(erule_tac x="nat" and P="\<lambda>j. (s\<le>j) \<longrightarrow> (J j)" for s J in allE,simp)
apply(subgoal_tac "(\<forall>i. i < length xs \<longrightarrow> ((Q, t) # xs) ! i -pe\<rightarrow> xs ! i \<longrightarrow> (snd (((Q, t) # xs) ! i), snd (xs ! i)) \<in> rely)")
 apply clarify
 apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>petran" for H J in allE,simp)
apply clarify
apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j) \<longrightarrow> (T j)\<in>rely" for H J T in allE,simp)
  done

subsubsection \<open>event\<close>

lemma assume_e_imp: "\<lbrakk>pre1\<subseteq>pre; rely1\<subseteq>rely; c\<in>assume_e(pre1,rely1)\<rbrakk> \<Longrightarrow> c\<in>assume_e(pre,rely)"
  proof -
    assume p0: "pre1\<subseteq>pre"
      and  p1: "rely1\<subseteq>rely"
      and  p3: "c\<in>assume_e(pre1,rely1)"
    then have a0: "gets_e (c!0) \<in> pre1 \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -ee\<rightarrow> c!(Suc i) \<longrightarrow> (gets_e (c!i), gets_e (c!Suc i)) \<in> rely1)"
      by (simp add:assume_e_def)
    show ?thesis
      proof(simp add:assume_e_def,rule conjI)
        from p0 a0 show "gets_e (c ! 0) \<in> pre" by auto
      next
        from p1 a0 show "\<forall>i. Suc i < length c \<longrightarrow> c ! i -ee\<rightarrow> c ! Suc i 
                            \<longrightarrow> (gets_e (c ! i), gets_e (c ! Suc i)) \<in> rely"
          by auto
      qed
  qed

lemma commit_e_imp: "\<lbrakk>guar1\<subseteq>guar; post1\<subseteq>post; c\<in>commit_e(guar1,post1)\<rbrakk> \<Longrightarrow> c\<in>commit_e(guar,post)"
  proof -
    assume p0: "guar1\<subseteq>guar"
      and  p1: "post1\<subseteq>post"
      and  p3: "c\<in>commit_e(guar1,post1)"
    then have a0: "(\<forall>i. Suc i<length c \<longrightarrow> 
               (\<exists>t. c!i -et-t\<rightarrow> c!(Suc i)) \<longrightarrow> (gets_e (c!i), gets_e (c!Suc i)) \<in> guar1) \<and> 
               (getspc_e (last c) = AnonyEvent (None) \<longrightarrow> gets_e (last c) \<in> post1)"
      by (simp add:commit_e_def)
    show ?thesis
      proof(simp add:commit_e_def)
        from p0 p1 a0 show "(\<forall>i. Suc i < length c \<longrightarrow> (\<exists>t. c ! i -et-t\<rightarrow> c ! Suc i) 
                            \<longrightarrow> (gets_e (c ! i), gets_e (c ! Suc i)) \<in> guar) \<and> 
               (getspc_e (last c) = AnonyEvent (None) \<longrightarrow> gets_e (last c) \<in> post)"
          by auto
      qed
  qed

subsubsection \<open>event system\<close>

lemma assume_es_imp: "\<lbrakk>pre1\<subseteq>pre; rely1\<subseteq>rely; c\<in>assume_es(pre1,rely1)\<rbrakk> \<Longrightarrow> c\<in>assume_es(pre,rely)"
  proof -
    assume p0: "pre1\<subseteq>pre"
      and  p1: "rely1\<subseteq>rely"
      and  p3: "c\<in>assume_es(pre1,rely1)"
    then have a0: "gets_es (c!0) \<in> pre1 \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -ese\<rightarrow> c!(Suc i) \<longrightarrow> (gets_es (c!i), gets_es (c!Suc i)) \<in> rely1)"
      by (simp add:assume_es_def)
    show ?thesis
      proof(simp add:assume_es_def,rule conjI)
        from p0 a0 show "gets_es (c ! 0) \<in> pre" by auto
      next
        from p1 a0 show "\<forall>i. Suc i < length c \<longrightarrow> c ! i -ese\<rightarrow> c ! Suc i 
                            \<longrightarrow> (gets_es (c ! i), gets_es (c ! Suc i)) \<in> rely"
          by auto
      qed
  qed

lemma commit_es_imp: "\<lbrakk>guar1\<subseteq>guar; post1\<subseteq>post; c\<in>commit_es(guar1,post1)\<rbrakk> \<Longrightarrow> c\<in>commit_es(guar,post)"
  proof -
    assume p0: "guar1\<subseteq>guar"
      and  p1: "post1\<subseteq>post"
      and  p3: "c\<in>commit_es(guar1,post1)"
    then have a0: "\<forall>i. Suc i<length c \<longrightarrow> 
               (\<exists>t. c!i -es-t\<rightarrow> c!(Suc i)) \<longrightarrow> (gets_es (c!i), gets_es (c!Suc i)) \<in> guar1"
      by (simp add:commit_es_def)
    show ?thesis
      proof(simp add:commit_es_def)
        from p0 a0 show "\<forall>i. Suc i < length c \<longrightarrow> (\<exists>t. c ! i -es-t\<rightarrow> c ! Suc i) 
                            \<longrightarrow> (gets_es (c ! i), gets_es (c ! Suc i)) \<in> guar"
          by auto
      qed
  qed

lemma concat_i_lm[rule_format]: "\<forall>ls l. concat ls = l \<and> (\<forall>i<length ls. ls!i \<noteq> [])\<longrightarrow> (\<forall>i. Suc i < length ls \<longrightarrow> 
                      (\<exists>m n. m \<le> length l \<and> n \<le> length l \<and> m \<le> n \<and> ls!i@[(ls!Suc i)!0] = take (n - m) (drop m l)))"
  proof -
  {
    fix ls
    have "\<forall>l. concat ls = l \<and> (\<forall>i<length ls. ls!i \<noteq> [])\<longrightarrow> (\<forall>i. Suc i < length ls \<longrightarrow> 
                      (\<exists>m n. m \<le> length l \<and> n \<le> length l \<and> m \<le> n \<and> ls!i@[(ls!Suc i)!0] = take (n - m) (drop m l)))"
    proof(induct ls)
      case Nil show ?case by simp
    next
      case (Cons x xs)
      assume a0: "\<forall>l. concat xs = l \<and> (\<forall>i<length xs. xs ! i \<noteq> []) \<longrightarrow>
                        (\<forall>i. Suc i < length xs \<longrightarrow> (\<exists>m n. m \<le> length l \<and> n \<le> length l \<and> 
                                m \<le> n \<and> xs ! i @ [xs ! Suc i ! 0] = take (n - m) (drop m l)))"
      show ?case 
        proof -
        {
          fix l
          assume b0: "concat (x # xs) = l"
            and  b1: "\<forall>i<length (x # xs). (x # xs) ! i \<noteq> []"
          let ?l' = "concat xs"
          from b0 have b2: "l = x@?l'" by simp
          have "\<forall>i. Suc i < length (x # xs) \<longrightarrow> (\<exists>m n. m \<le> length l \<and> n \<le> length l \<and> 
                        m \<le> n \<and> (x # xs) ! i @ [(x # xs) ! Suc i ! 0] = take (n - m) (drop m l))" 
            proof -
            {
              fix i
              assume c0: "Suc i < length (x # xs)"
              then have c1: "length xs > 0" by auto
              have "\<exists>m n. m \<le> length l \<and> n \<le> length l \<and> m \<le> n \<and> 
                        (x # xs) ! i @ [(x # xs) ! Suc i ! 0] = take (n - m) (drop m l)"
                proof(cases "i = 0")
                  assume d0: "i = 0"
                  from b1 c1 have d1: "(x # xs) ! 1 \<noteq> []" by (metis One_nat_def c0 d0) 
                  with b0 have d2: "x @ [xs!0 ! 0] = take (length x + 1) (drop 0 l)"
                    by (smt Cons_nth_drop_Suc Nil_is_append_conv One_nat_def append_eq_conv_conj 
                      c0 concat.simps(2) d0 drop_0 drop_Suc_Cons length_greater_0_conv 
                      nth_Cons_Suc nth_append self_append_conv2 take_0 take_Suc_conv_app_nth take_add)
                  then have d3: "(x # xs) ! 0 @ [(x # xs) ! 1 ! 0] = take (length x + 1) (drop 0 l)"
                    by simp 
                  moreover
                  have "0 \<le> length l" using calculation by auto 
                  moreover
                  from b0 d1 have "length x + 1 \<le> length l"
                    by (metis Suc_eq_plus1 d2 drop_0 length_append_singleton linear take_all) 
                  ultimately show ?thesis using d0 by force 
                next
                  assume d0: "i \<noteq> 0"
                  moreover
                  from b1 have d1: "\<forall>i<length xs. xs ! i \<noteq> []" by auto
                  moreover
                  from c0 have "Suc (i - 1) < length xs" using d0 by auto 
                  ultimately have "\<exists>m n. m \<le> length ?l' \<and> n \<le> length ?l' \<and> 
                                m \<le> n \<and> xs ! (i - 1) @ [xs ! Suc (i - 1) ! 0] = take (n - m) (drop m ?l')" 
                     using a0 d0 by blast
                  then obtain m and n where d2: "m \<le> length ?l' \<and> n \<le> length ?l' \<and> 
                                m \<le> n \<and> xs ! (i - 1) @ [xs ! Suc (i - 1) ! 0] = take (n - m) (drop m ?l')"
                     by auto
                  let ?m' = "m + length x"
                  let ?n' = "n + length x"
                  from b0 d2 have "?m' \<le> length l" by auto
                  moreover
                  from b0 d2 have "?n' \<le> length l" by auto
                  moreover 
                  from d2 have "?m' \<le> ?n'" by auto
                  moreover
                  have "(x # xs) ! i @ [(x # xs) ! Suc i ! 0] = take (?n' - ?m') (drop ?m' l)"
                    using b2 d0 d2 by auto
                  ultimately have "?m' \<le> length l \<and> ?n' \<le> length l \<and> ?m' \<le> ?n' \<and> 
                          (x # xs) ! i @ [(x # xs) ! Suc i ! 0] = take (?n' - ?m') (drop ?m' l)" by simp
                  then show ?thesis by blast
                qed
            }
            then show ?thesis by auto
            qed
        }
        then show ?thesis by auto
        qed
    qed
  }
  then show ?thesis by blast
qed

lemma concat_i_lm1[rule_format]: "\<forall>ls l. concat ls = l \<and> (\<forall>i<length ls. ls!i \<noteq> [])\<longrightarrow> (\<forall>i. i < length ls \<longrightarrow> 
         (\<exists>m n. m \<le> length l \<and> n \<le> length l \<and> m \<le> n \<and> ls!i = take (n - m) (drop m l)))"
proof -
  {
    fix ls
    have "\<forall>l. concat ls = l \<and> (\<forall>i<length ls. ls!i \<noteq> [])\<longrightarrow> (\<forall>i. i < length ls \<longrightarrow> 
        (\<exists>m n. m \<le> length l \<and> n \<le> length l \<and> m \<le> n \<and> ls!i = take (n - m) (drop m l)))"
    proof(induct ls)
      case Nil show ?case by simp
    next
      case (Cons x xs)
      assume a0: "\<forall>l. concat xs = l \<and> (\<forall>i<length xs. xs ! i \<noteq> []) \<longrightarrow> (\<forall>i. i < length xs \<longrightarrow> 
      (\<exists>m n. m \<le> length l \<and> n \<le> length l \<and>  m \<le> n  \<and> xs ! i  = take (n - m) (drop m l)))"
      show ?case 
        proof -
        {
          fix l
          assume b0: "concat (x # xs) = l"
            and  b1: "\<forall>i<length (x # xs). (x # xs) ! i \<noteq> []"
          let ?l' = "concat xs"
          from b0 have b2: "l = x@?l'" by simp
          have "(\<forall>i<length (x # xs). \<exists>m n. m \<le> length l \<and> n \<le> length l \<and> m \<le> n \<and> (x # xs) ! i = take (n - m) (drop m l))" 
            proof -
            {
              fix i
              assume c0: "i < length (x # xs)"
              have "\<exists>m n. m \<le> length l \<and> n \<le> length l \<and> m \<le> n \<and> (x # xs) ! i  = take (n - m) (drop m l)"
                proof(cases "i = 0")
                  assume d0: "i = 0"
                  then have d1 : "x \<noteq> []" using b1 by auto
                  with b0 have d2 : "x = take (length x) (drop 0 l)" by auto
                  then show ?thesis 
                    by (metis d0 drop0 drop_take le0 leI less_or_eq_imp_le nth_Cons_0 take_all)
                next
                  assume d0: "i \<noteq> 0"
                  moreover
                  from b1 have d1: "\<forall>i<length xs. xs ! i \<noteq> []" by auto
                  moreover
                  from c0 have " i - 1 < length xs" using d0 by auto 
                  ultimately have "\<exists>m n. m \<le> length ?l' \<and> n \<le> length ?l' \<and> 
                                m \<le> n \<and> xs ! (i - 1)  = take (n - m) (drop m ?l')" 
                    using a0 d1 by blast
                  then obtain m and n where d2: "m \<le> length ?l' \<and> n \<le> length ?l' \<and> 
                                m \<le> n \<and> xs ! (i - 1) = take (n - m) (drop m ?l')"
                     by auto
                  let ?m' = "m + length x"
                  let ?n' = "n + length x"
                  from b0 d2 have "?m' \<le> length l" by auto
                  moreover
                  from b0 d2 have "?n' \<le> length l" by auto
                  moreover 
                  from d2 have "?m' \<le> ?n'" by auto
                  moreover
                  have "(x # xs) ! i  = take (?n' - ?m') (drop ?m' l)"
                    using b2 d0 d2 by auto
                  ultimately have "?m' \<le> length l \<and> ?n' \<le> length l \<and> ?m' \<le> ?n' \<and> 
                          (x # xs) ! i  = take (?n' - ?m') (drop ?m' l)" by simp
                  then show ?thesis by blast
                qed
            }
            then show ?thesis by auto
            qed
        }
        then show ?thesis by auto
        qed
    qed
  }
  then show ?thesis by blast
qed


lemma concat_last_lm: "\<forall>ls l. concat ls = l \<and> length ls > 0 \<longrightarrow> 
                      (\<exists>m . m \<le> length l \<and> last ls = drop m l)"
  proof 
    fix ls
    show "\<forall>l. concat ls = l \<and> length ls > 0 \<longrightarrow> 
                      (\<exists>m . m \<le> length l \<and> last ls = drop m l)"
      proof(induct ls)
        case Nil show ?case by simp
      next
        case (Cons x xs)
        assume a0: "\<forall>l. concat xs = l \<and> 0 < length xs \<longrightarrow> (\<exists>m\<le>length l. last xs = drop m l)"
        show ?case 
          proof -
          {
            fix l
            assume b0: "concat (x # xs) = l"
              and  b1: "0 < length (x # xs)"
            let ?l' = "concat xs"
            have "\<exists>m\<le>length l. last (x # xs) = drop m l"
              proof(cases "xs = []")
                assume c0: "xs = []"
                then show ?thesis using b0 by auto 
              next
                assume c0: "xs \<noteq> []"
                then have c1: "length xs > 0" by auto
                with a0 have "\<exists>m\<le>length ?l'. last xs = drop m ?l'" by auto
                then obtain m where c2: "m\<le>length ?l' \<and> last xs = drop m ?l'" by auto
                with b0 show ?thesis
                  by (metis append_eq_conv_conj c0 concat.simps(2) 
                      drop_all drop_drop last.simps nat_le_linear) 
              qed
          }
          then show ?thesis by auto
          qed
      qed
  qed

lemma concat_equiv: "\<lbrakk>l \<noteq> []; l = concat lt; \<forall>i<length lt. length (lt!i) \<ge> 2\<rbrakk> \<Longrightarrow> 
          \<forall>i. i \<le> length l \<longrightarrow> (\<exists>k j. k < length lt \<and> j \<le> length (lt!k) \<and> 
                  drop i l = (drop j (lt!k)) @ concat (drop (Suc k) lt) )"
  proof -
    assume p0: "l = concat lt"
      and  p1: "\<forall>i<length lt. length (lt!i) \<ge> 2"
      and  p3: "l \<noteq> []"
    then have p4: "lt \<noteq> []" using concat.simps(1) by blast 
    show ?thesis
      proof -
      {
        fix i
        assume a0: "i \<le> length l"
        from a0 have "\<exists>k j. k < length lt \<and> j \<le> length (lt!k) \<and> 
                  drop i l = (drop j (lt!k)) @ concat (drop (Suc k) lt)"
          proof(induct i)
            case 0
            assume b0: "0 \<le> length l"
            have "drop 0 l = drop 0 (lt ! 0) @ concat (drop (Suc 0) lt)"
              by (metis concat.simps(2) drop_0 drop_Suc_Cons list.exhaust nth_Cons_0 p0 p4)
            then show ?case using p4 by blast 
          next
            case (Suc m)
            assume b0: "m \<le> length l \<Longrightarrow> \<exists>k j. k < length lt \<and> j \<le> length (lt ! k) \<and> 
                          drop m l = drop j (lt ! k) @ concat (drop (Suc k) lt)"
              and  b1: "Suc m \<le> length l"
            then have "\<exists>k j. k < length lt \<and> j \<le> length (lt ! k) \<and> 
                          drop m l = drop j (lt ! k) @ concat (drop (Suc k) lt)"
              by auto
            then obtain k and j where b2: "k < length lt \<and> j \<le> length (lt ! k) \<and> 
                          drop m l = drop j (lt ! k) @ concat (drop (Suc k) lt)" by auto
            show ?case
              proof(cases "j = length (lt!k)")
                assume c0: "j = length (lt!k)"
                with b2 have c1: "drop m l = concat (drop (Suc k) lt)" by simp
                from b1 have "drop m l \<noteq> []" by simp
                with c1 have c2: "drop (Suc k) lt \<noteq> []" by auto
                then obtain lt1 and lts where c3: "drop (Suc k) lt = lt1#lts"
                  by (meson neq_Nil_conv)
                then have c4: "drop (Suc (Suc k)) lt = lts" by (metis drop_Suc list.sel(3) tl_drop) 
                moreover
                from c3 have c5: "lt!Suc k = lt1" by (simp add: nth_via_drop) 
                ultimately have "drop (Suc m) l = drop 1 lt1 @ concat lts" using c1 c3
                  by (metis One_nat_def Suc_leI Suc_lessI b2 concat.simps(2) 
                    drop_0 drop_Suc drop_all list.distinct(1) list.size(3) 
                    not_less_eq_eq numeral_2_eq_2 p1 tl_append2 tl_drop zero_less_Suc) 
                with c4 c5  have "drop (Suc m) l = drop 1 (lt!Suc k) @ concat (drop (Suc (Suc k)) lt)" by simp
                then show ?thesis by (metis One_nat_def Suc_leD Suc_leI Suc_lessI c2 b2 drop_all numeral_2_eq_2 p1) 
              next
                assume c0: "j \<noteq> length (lt!k)"
                with b2 have c1: "j < length (lt!k)" by auto
                with b2 have "drop (Suc m) l = drop (Suc j) (lt ! k) @ concat (drop (Suc k) lt)"
                  by (metis c0 drop_Suc drop_eq_Nil le_antisym tl_append2 tl_drop) 
                then show ?thesis using Suc_leI c1 b2 by blast 
              qed
          qed
      }
      then show ?thesis by auto
      qed
  qed

lemma rely_take_rely: "\<forall>i. Suc i<length l \<longrightarrow> l!i -ese\<rightarrow> l!(Suc i) 
        \<longrightarrow> (gets_es (l!i), gets_es (l!Suc i)) \<in> rely \<Longrightarrow> 
        \<forall>m subl. m \<le> length l \<and> subl = take m l \<longrightarrow> (\<forall>i. Suc i<length subl \<longrightarrow> subl!i -ese\<rightarrow> subl!(Suc i) 
        \<longrightarrow> (gets_es (subl!i), gets_es (subl!Suc i)) \<in> rely)" 
  proof -
    assume p0: "\<forall>i. Suc i<length l \<longrightarrow> l!i -ese\<rightarrow> l!(Suc i) 
        \<longrightarrow> (gets_es (l!i), gets_es (l!Suc i)) \<in> rely"
    show ?thesis
      proof -
      {
        fix m
        have "\<forall>subl. m \<le> length l \<and> subl = take m l \<longrightarrow> (\<forall>i. Suc i<length subl \<longrightarrow> subl!i -ese\<rightarrow> subl!(Suc i) 
        \<longrightarrow> (gets_es (subl!i), gets_es (subl!Suc i)) \<in> rely)"        
          proof(induct m)
            case 0 show ?case by simp
          next
            case (Suc n)
            assume a0: "\<forall>subl. n \<le> length l \<and> subl = take n l \<longrightarrow>
                          (\<forall>i. Suc i < length subl \<longrightarrow> subl ! i -ese\<rightarrow> subl ! Suc i \<longrightarrow> 
                              (gets_es (subl ! i), gets_es (subl ! Suc i)) \<in> rely)"
            show ?case
              proof -
              {
                fix subl
                assume b0: "Suc n \<le> length l"
                  and  b1: "subl = take (Suc n) l"
                with a0 have "\<forall>i. Suc i < length subl \<longrightarrow> subl ! i -ese\<rightarrow> subl ! Suc i \<longrightarrow> 
                              (gets_es (subl ! i), gets_es (subl ! Suc i)) \<in> rely"
                   using p0 by auto 
              }
              then show ?thesis by auto
              qed
          qed
      }
      then show ?thesis by auto
      qed
  qed

lemma rely_drop_rely: "\<forall>i. Suc i<length l \<longrightarrow> l!i -ese\<rightarrow> l!(Suc i) 
        \<longrightarrow> (gets_es (l!i), gets_es (l!Suc i)) \<in> rely \<Longrightarrow> 
        \<forall>m subl. m \<le> length l \<and> subl = drop m l \<longrightarrow> (\<forall>i. Suc i<length subl \<longrightarrow> subl!i -ese\<rightarrow> subl!(Suc i) 
        \<longrightarrow> (gets_es (subl!i), gets_es (subl!Suc i)) \<in> rely)" 
  proof -
    assume p0: "\<forall>i. Suc i<length l \<longrightarrow> l!i -ese\<rightarrow> l!(Suc i) 
        \<longrightarrow> (gets_es (l!i), gets_es (l!Suc i)) \<in> rely"
    show ?thesis
      proof -
      {
        fix m
        have "\<forall>subl. m \<le> length l \<and> subl = drop m l \<longrightarrow> (\<forall>i. Suc i<length subl \<longrightarrow> subl!i -ese\<rightarrow> subl!(Suc i) 
        \<longrightarrow> (gets_es (subl!i), gets_es (subl!Suc i)) \<in> rely)"        
          proof(induct m)
            case 0 show ?case by (simp add: p0) 
          next
            case (Suc n)
            assume a0: "\<forall>subl. n \<le> length l \<and> subl = drop n l \<longrightarrow>
                          (\<forall>i. Suc i < length subl \<longrightarrow> subl ! i -ese\<rightarrow> subl ! Suc i \<longrightarrow> 
                              (gets_es (subl ! i), gets_es (subl ! Suc i)) \<in> rely)"
            show ?case
              proof -
              {
                fix subl
                assume b0: "Suc n \<le> length l"
                  and  b1: "subl = drop (Suc n) l"
                with a0 have "\<forall>i. Suc i < length subl \<longrightarrow> subl ! i -ese\<rightarrow> subl ! Suc i \<longrightarrow> 
                              (gets_es (subl ! i), gets_es (subl ! Suc i)) \<in> rely"
                   using p0 by auto 
              }
              then show ?thesis by auto
              qed
          qed
      }
      then show ?thesis by auto
      qed
  qed

lemma rely_takedrop_rely: "\<lbrakk>\<forall>i. Suc i<length l \<longrightarrow> l!i -ese\<rightarrow> l!(Suc i) 
        \<longrightarrow> (gets_es (l!i), gets_es (l!Suc i)) \<in> rely; 
        \<exists>m n. m \<le> length l \<and> n \<le> length l \<and> m \<le> n \<and> subl = take (n - m) (drop m l)\<rbrakk> \<Longrightarrow> 
        \<forall>i. Suc i<length subl \<longrightarrow> subl!i -ese\<rightarrow> subl!(Suc i) 
        \<longrightarrow> (gets_es (subl!i), gets_es (subl!Suc i)) \<in> rely" 
  proof -
    assume p1: "\<forall>i. Suc i<length l \<longrightarrow> l!i -ese\<rightarrow> l!(Suc i) 
        \<longrightarrow> (gets_es (l!i), gets_es (l!Suc i)) \<in> rely"
      and  p3: "\<exists>m n. m \<le> length l \<and> n \<le> length l \<and> m \<le> n \<and> subl = take (n - m) (drop m l)"

    from p3 obtain m and n where a0: "m \<le> length l \<and> n \<le> length l \<and> m \<le> n \<and> subl = take (n - m) (drop m l)" 
      by auto
    let ?subl1 = "drop m l"
    have a1: "\<forall>i. Suc i<length ?subl1 \<longrightarrow> ?subl1!i -ese\<rightarrow> ?subl1!(Suc i) 
        \<longrightarrow> (gets_es (?subl1!i), gets_es (?subl1!Suc i)) \<in> rely"
      using a0 p1 rely_drop_rely by blast 
    show ?thesis using a0 a1 by auto 
  qed


lemma pre_trans: "\<lbrakk>esl \<in> assume_es(pre, rely); \<forall>i<length esl. getspc_es (esl!i) = es; stable pre rely\<rbrakk>
        \<Longrightarrow> \<forall>i<length esl. gets_es (esl!i) \<in> pre"
  proof -
    assume p0: "esl \<in> assume_es(pre, rely)"
      and  p2: "\<forall>i<length esl. getspc_es (esl!i) = es"
      and  p3: "stable pre rely"
    then show ?thesis
      proof -
      {
        fix i
        assume a0: "i<length esl"
        then have "gets_es (esl!i) \<in> pre"
          proof(induct i)
            case 0 from p0 show ?case by (simp add:assume_es_def)
          next
            case (Suc j)
            assume b0: "j < length esl \<Longrightarrow> gets_es (esl ! j) \<in> pre"
              and  b1: "Suc j < length esl"
            then have b2: "gets_es (esl ! j) \<in> pre" by auto

            from p2 b1 have "getspc_es (esl ! j) = es" by auto
            moreover
            from p2 b1 have "getspc_es (esl ! Suc j) = es" by auto
            ultimately have "esl ! j -ese\<rightarrow> esl ! Suc j" by (simp add: eqconf_esetran) 
            with p0 b1 have "(gets_es (esl!j), gets_es (esl!Suc j)) \<in> rely" by (simp add:assume_es_def)
            with p3 b2 show ?case by (simp add:stable_def)
          qed
      }
      then show ?thesis by auto
      qed
  qed

lemma pre_trans_assume_es: 
  "\<lbrakk>esl \<in> assume_es(pre, rely); n < length esl; 
    \<forall>j. j \<le> n \<longrightarrow> getspc_es (esl ! j) = es; stable pre rely\<rbrakk>
        \<Longrightarrow> drop n esl \<in> assume_es(pre, rely)"
  proof -
    assume p0: "esl \<in> assume_es(pre, rely)"
      and  p2: "\<forall>j. j \<le> n \<longrightarrow> getspc_es (esl ! j) = es"
      and  p3: "stable pre rely"
      and  p4: "n < length esl"
    then show ?thesis
      proof(cases "n = 0")
        assume "n = 0" with p0 show ?thesis by auto
      next
        assume "n \<noteq> 0"
        then have a0: "n > 0" by simp
        let ?esl = "drop n esl"
        let ?esl1 = "take (Suc n) esl"
        from p0 a0 p4 have "?esl1\<in>assume_es(pre, rely)"
          using assume_es_take_n[of "Suc n" esl pre rely] by simp
        moreover
        from p2 a0 have "\<forall>i<length ?esl1. getspc_es (?esl1 ! i) = es" by simp
        ultimately
        have "\<forall>i<length ?esl1. gets_es (?esl1!i) \<in> pre" 
          using pre_trans[of "take (Suc n) esl" pre rely es] p3 by simp
        with a0 p4 have "gets_es (?esl!0)\<in>pre"
          using Cons_nth_drop_Suc Suc_leI length_take lessI less_or_eq_imp_le 
          min.absorb2 nth_Cons_0 nth_append_length take_Suc_conv_app_nth by auto 
        moreover
        have "\<forall>i. Suc i<length ?esl \<longrightarrow> 
               ?esl!i -ese\<rightarrow> ?esl!(Suc i) \<longrightarrow> (gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> rely"
          proof -
          {
            fix i
            assume b0: "Suc i<length ?esl"
              and  b1: "?esl!i -ese\<rightarrow> ?esl!(Suc i)"
            from p0 have "\<forall>i. Suc i<length esl \<longrightarrow> 
               esl!i -ese\<rightarrow> esl!(Suc i) \<longrightarrow> (gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely"
               by (simp add:assume_es_def)
            with p4 a0 b0 b1 have "(gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> rely"
              using less_imp_le_nat rely_drop_rely by auto 
          }
          then show ?thesis by auto
          qed
        ultimately show ?thesis by (simp add:assume_es_def) 
      qed
  qed

subsubsection \<open>parallel event system\<close>


subsection \<open>State trace equivalence\<close>
subsubsection \<open>trace equivalence of program and anonymous event\<close>

definition lift_progs :: "('s pconfs) \<Rightarrow> ('l,'k,'s) x \<Rightarrow> ('l,'k,'s) econfs"
  where "lift_progs pcfs x \<equiv> map (\<lambda>c. (AnonyEvent (fst c), snd c, x)) pcfs"

lemma equiv_prog_lift0 : "p\<in>cpts_p \<Longrightarrow> lift_progs p x \<in> cpts_of_ev (AnonyEvent (getspc_p (p!0))) (gets_p (p!0)) x"
  proof-
    assume a0: "p\<in>cpts_p"
    have "\<forall>p s x. p\<in>cpts_p \<longrightarrow> lift_progs p x \<in> cpts_of_ev (AnonyEvent (getspc_p (p!0))) (gets_p (p!0)) x"
      proof -
      {
        fix p s x
        assume b0: "p\<in>cpts_p"
        then have "lift_progs p x \<in> cpts_of_ev (AnonyEvent (getspc_p (p!0))) (gets_p (p!0)) x" 
          proof(induct p)
            case (CptsPOne P' s')
            have c0:"lift_progs [(P', s')] x ! 0 = ((AnonyEvent (getspc_p ([(P', s')]!0))), (gets_p ([(P', s')]!0)), x)" 
              by (simp add: lift_progs_def getspc_p_def gets_p_def) 
            have c1:"lift_progs [(P', s')] x \<in> cpts_ev" 
              by (simp add: cpts_ev.CptsEvOne lift_progs_def) 
            with c0 show ?case by (simp add: cpts_of_ev_def) 
          next
            case (CptsPEnv P' t' xs' s')
            assume c0: "(P', t') # xs' \<in> cpts_p" and
                   c1: "lift_progs ((P', t') # xs') x \<in> cpts_of_ev (AnonyEvent (getspc_p (((P', t') # xs') ! 0))) (gets_p (((P', t') # xs') ! 0)) x"
            have c2: "lift_progs ((P', s') # (P', t') # xs') x ! 0 = 
                ((AnonyEvent (getspc_p (((P', s') # (P', t') # xs') ! 0))), (gets_p (((P', s') # (P', t') # xs') ! 0)), x)"
                 by (simp add: lift_progs_def getspc_p_def gets_p_def) 
            have c3: "lift_progs ((P', s') # (P', t') # xs') x = (AnonyEvent P', s', x) # lift_progs ((P', t') # xs') x"
              by (simp add: lift_progs_def) 
            from c1 have c5: "lift_progs ((P', t') # xs') x \<in> cpts_ev"
              by (simp add: cpts_of_ev_def) 
            with c3 have c4: "lift_progs ((P', s') # (P', t') # xs') x \<in> cpts_ev"
              by (simp add: cpts_ev.CptsEvEnv lift_progs_def) 
            with c2 show ?case using cpts_of_ev_def by fastforce 
          next
            case (CptsPComp P' s' Q' t' xs')
            assume c0: "(P', s') -c\<rightarrow> (Q', t')" and
                   c1: "(Q', t') # xs' \<in> cpts_p" and
                   c2: "lift_progs ((Q', t') # xs') x \<in> cpts_of_ev (AnonyEvent (getspc_p (((Q', t') # xs') ! 0))) (gets_p (((Q', t') # xs') ! 0)) x"
            have c3: "lift_progs ((P', s') # (Q', t') # xs') x ! 0 =
                      ((AnonyEvent (getspc_p (((P', s') # (Q', t') # xs') ! 0))), (gets_p (((P', s') # (Q', t') # xs') ! 0)), x)"
                by (simp add: lift_progs_def getspc_p_def gets_p_def) 
            have c4: "lift_progs ((P', s') # (Q', t') # xs') x = (AnonyEvent P', s', x) # lift_progs ((Q', t') # xs') x"
              by (simp add: lift_progs_def) 
            from c2 have c5: "lift_progs ((Q', t') # xs') x \<in> cpts_ev"
              by (simp add: cpts_of_ev_def) 
            from c0 have c6: "(AnonyEvent P', s', x) -et-(Cmd P')\<sharp>k\<rightarrow> (AnonyEvent Q', t', x)" 
              by (simp add: etran.AnonyEvent)
            with c6 c5 c4 have c7: "lift_progs ((P', s') # (Q', t') # xs') x \<in> cpts_ev"
              by (simp add: cpts_ev.CptsEvComp lift_progs_def)
 
            with c3 show ?case using cpts_of_ev_def by fastforce 
          qed
      }
      then show ?thesis by auto
      qed

    with a0 show ?thesis by auto
  qed


lemma equiv_prog_lift : "p\<in>cpts_of_p P s \<Longrightarrow> lift_progs p x \<in> cpts_of_ev (AnonyEvent P) s x"
  proof -
    assume a0: "p\<in>cpts_of_p P s"
    then have a1: "p\<in>cpts_p" by (simp add: cpts_of_p_def)
    from a0 have a2: "p!0=(P,s)" by (simp add: cpts_of_p_def)
    with a1 show ?thesis using equiv_prog_lift0 getspc_p_def gets_p_def
      by (metis fst_conv snd_conv) 
  qed

primrec lower_anonyevt0 :: "('l,'k,'s) event \<Rightarrow> 's \<Rightarrow> 's pconf"
  where AnonyEv: "lower_anonyevt0 (AnonyEvent p) s = (p, s)" |
        BasicEv: "lower_anonyevt0 (BasicEvent p) s = (None, s)"

definition lower_anonyevt1 :: "('l,'k,'s) econf  \<Rightarrow> 's pconf"
  where "lower_anonyevt1 ec \<equiv> lower_anonyevt0 (getspc_e ec) (gets_e ec) " 

definition lower_evts :: "('l,'k,'s) econfs \<Rightarrow> ('s pconfs)"
  where "lower_evts ecfs \<equiv> map lower_anonyevt1 ecfs"

lemma lower_anonyevt_s : "getspc_e e = AnonyEvent P \<Longrightarrow> gets_p (lower_anonyevt1 e) = gets_e e"
  by (simp add: gets_p_def lower_anonyevt1_def)
  
lemma equiv_lower_evts0 : "\<lbrakk>\<exists>P. getspc_e (es ! 0) = AnonyEvent P; es \<in> cpts_ev\<rbrakk> \<Longrightarrow> lower_evts es \<in>cpts_p"
proof-
    assume a0: "es \<in> cpts_ev" and a1: "\<exists>P. getspc_e (es ! 0) = AnonyEvent P"
    have "\<forall>es P. getspc_e (es ! 0) = AnonyEvent P \<and> es \<in> cpts_ev \<longrightarrow> lower_evts es \<in>cpts_p"
      proof -
      {
        fix es
        assume b0: "\<exists>P. getspc_e (es ! 0) = AnonyEvent P" and
               b1: "es \<in> cpts_ev"
        from b1 b0 have "lower_evts es \<in>cpts_p"
          proof(induct es)
            case (CptsEvOne e' s' x') 
            assume c0: "\<exists>P. getspc_e ([(e', s', x')] ! 0) = AnonyEvent P"  
            then obtain P where "getspc_e ([(e', s', x')] ! 0) = AnonyEvent P" by auto
            then have c1: "e' = AnonyEvent P" by (simp add:getspc_e_def)
            then have c2: "lower_anonyevt1 (e', s', x') = (P, s')"
              by (simp add: gets_e_def getspc_e_def lower_anonyevt1_def)
            then have c2: "lower_evts [(e', s', x')] = [(P, s')]"
              by (simp add: lower_evts_def)  
            then show ?case by (simp add: cpts_of_p_def cpts_p.CptsPOne) 
          next
            case (CptsEvEnv e' t' x' xs' s' y')
            assume c0: " (e', t', x') # xs' \<in> cpts_ev" and
                   c1: "\<exists>P. getspc_e (((e', t', x') # xs') ! 0) = AnonyEvent P \<Longrightarrow> lower_evts ((e', t', x') # xs') \<in> cpts_p" and
                   c2: "\<exists>P. getspc_e (((e', s', y') # (e', t', x') # xs') ! 0) = AnonyEvent P"
            let ?ob = "lower_evts ((e', s', y') # (e', t', x') # xs')"
            from c2 obtain P where c_:"getspc_e (((e', s', y') # (e', t', x') # xs') ! 0) = AnonyEvent P" by auto
            then have c3: "?ob ! 0 = (P, s')" 
              by (simp add: lower_evts_def lower_anonyevt1_def lower_anonyevt0_def gets_e_def getspc_e_def) 
            
            from c_ have c5: "(e', s', y') = (AnonyEvent P, s', y')" by (simp add:getspc_e_def)
            then have c4: "e' = AnonyEvent P" by simp
            with c1 have c6: "lower_evts ((e', t', x') # xs') \<in> cpts_p" by (simp add:getspc_e_def)
            from c5 have c7: "?ob = (P, s') # lower_evts ((e', t', x') # xs')"
              by (metis (no_types, lifting) c3 list.simps(9) lower_evts_def nth_Cons_0) 
            from c4 have c8: "lower_evts ((e', t', x') # xs') = (P, t') # lower_evts xs'" 
              by (simp add:lower_evts_def lower_anonyevt1_def lower_anonyevt0_def gets_e_def getspc_e_def) 
            with c6 c7 show ?case by (simp add: cpts_p.CptsPEnv) 
          next
            case (CptsEvComp e1 s1 x1 et e2 t1 y1 xs1)
            assume c0: "(e1, s1, x1) -et-et\<rightarrow> (e2, t1, y1)" and
                   c1: "(e2, t1, y1) # xs1 \<in> cpts_ev" and
                   c2: "\<exists>P. getspc_e (((e2, t1, y1) # xs1) ! 0) = AnonyEvent P 
                        \<Longrightarrow> lower_evts ((e2, t1, y1) # xs1) \<in> cpts_p" and
                   c3: "\<exists>P. getspc_e (((e1, s1, x1) # (e2, t1, y1) # xs1) ! 0) = AnonyEvent P"
            from c3 obtain P where c_:"getspc_e (((e1, s1, x1) # (e2, t1, y1) # xs1) ! 0) = AnonyEvent P" by auto
            then have c4: "e1 = AnonyEvent P" by (simp add:getspc_e_def)
            with c0 have "\<exists>Q. e2 = AnonyEvent Q"
              apply(clarify)
              apply(rule etran.cases)
              apply(simp_all)+
              done
            then obtain Q where c5: "e2 = AnonyEvent Q" by auto
            with c2 have c6:"lower_evts ((e2, t1, y1) # xs1) \<in> cpts_p" by (simp add: getspc_e_def) 
            have c7: "lower_evts ((e1, s1, x1) # (e2, t1, y1) # xs1) = 
                  (lower_anonyevt1 (e1, s1, x1)) # lower_evts ((e2, t1, y1) # xs1)"
              by (simp add: lower_evts_def) 
            have c7_: "lower_evts ((e2, t1, y1) # xs1) = lower_anonyevt1 (e2, t1, y1) # lower_evts xs1" 
              by (simp add: lower_evts_def)
            with c6 have c8: "lower_anonyevt1 (e2, t1, y1) # lower_evts xs1 \<in> cpts_p" by simp
            from c4 have c9: "lower_anonyevt1 (e1, s1, x1) = (P, s1)" 
              by (simp add: gets_e_def getspc_e_def lower_anonyevt1_def) 
            from c5 have c10: "lower_anonyevt1 (e2, t1, y1) = (Q, t1)" 
              by (simp add: gets_e_def getspc_e_def lower_anonyevt1_def) 
            from c0 c4 c5 have c11: "(AnonyEvent P, s1, x1) -et-et\<rightarrow> (AnonyEvent Q, t1, y1)" by simp
            then have "(P, s1) -c\<rightarrow> (Q, t1)" 
              apply(rule etran.cases)
              apply(simp_all)
              done
            with c8 c9 c10 have "lower_anonyevt1 (e1, s1, x1) # lower_anonyevt1 (e2, t1, y1) # lower_evts xs1 \<in> cpts_p"
              using CptsPComp by simp
            with c7 c7_ show ?case by simp
          qed
      }
      then show ?thesis by auto
      qed
    with a0 a1 show ?thesis by blast 
  qed

lemma equiv_lower_evts : "es \<in> cpts_of_ev (AnonyEvent P) s x \<Longrightarrow> lower_evts es \<in>cpts_of_p P s"
  proof -
    assume a0: "es \<in> cpts_of_ev (AnonyEvent P) s x"
    then have a1: "es!0=(AnonyEvent P,(s,x)) \<and> es \<in> cpts_ev" by (simp add: cpts_of_ev_def)
    then have a2: "getspc_e (es ! 0) = AnonyEvent P" by (simp add:getspc_e_def)
    with a1 have a3: "lower_evts es \<in>cpts_p" using equiv_lower_evts0
      by (simp add: equiv_lower_evts0) 
    have a4: "lower_evts es ! 0 = lower_anonyevt1 (es ! 0)"
      by (metis a3 cptn_not_empty list.simps(8) list.size(3) lower_evts_def neq0_conv not_less0 nth_equalityI nth_map) 
    from a1 have a5: "lower_anonyevt1 (es ! 0) = (P,s)" 
      by (simp add: gets_e_def getspc_e_def lower_anonyevt1_def) 
    with a4 have a6: "lower_evts es ! 0 = (P,s)" by simp
    with a3 show ?thesis by (simp add:cpts_of_p_def)
  qed

subsubsection \<open>trace between of basic and anonymous events\<close>

lemma evtent_in_cpts1: "el \<in> cpts_ev \<and> el ! 0 = (BasicEvent ev, s, x) \<Longrightarrow> 
      Suc i < length el \<and> el ! i -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc i) \<Longrightarrow> 
      (\<forall>j. Suc j \<le> i \<longrightarrow> getspc_e (el ! j) = BasicEvent ev \<and> el ! j -ee\<rightarrow> el ! (Suc j))"
  proof -
    assume p0: "el \<in> cpts_ev \<and> el ! 0 = (BasicEvent ev, s, x)"
    assume p1: "Suc i < length el \<and> el ! i -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc i)"
    from p0 have p01: "el \<in> cpts_ev" and
                 p02: "el ! 0 = (BasicEvent ev, s, x)" by auto
    from p1 have p3: "getspc_e (el ! i) = BasicEvent ev" by (meson ent_spec) 
    show "\<forall>j. Suc j \<le> i \<longrightarrow> getspc_e (el ! j) = BasicEvent ev \<and> el ! j -ee\<rightarrow> el ! (Suc j)"
      proof -
      {
        fix j
        assume a0: "Suc j \<le> i"
        have "\<forall>k. k < i \<longrightarrow> getspc_e (el ! (i -k -1)) = BasicEvent ev \<and> el ! (i -k -1)-ee\<rightarrow> el ! (i - k)"
          proof -
          {
            fix k
            assume "k < i"
            then have "getspc_e (el ! (i -k -1)) = BasicEvent ev \<and> el ! (i -k -1)-ee\<rightarrow> el ! (i - k)"
              proof(induct k)
                case 0 
                from p3 have b0: "\<not>(\<exists>t ec1. ec1-et-t\<rightarrow>(el ! i))" 
                  using no_tran2basic getspc_e_def by (metis prod.collapse)
                with p1 p01 have b1: "getspc_e (el ! (i - 1)) = getspc_e (el ! i)" using notran_confeqi
                  by (metis "0.prems" Suc_diff_1 Suc_lessD) 
                with p3 show ?case by (simp add: eqconf_eetran) 
              next
                case (Suc m)
                assume b0: "m < i \<Longrightarrow> getspc_e (el ! (i - m - 1)) = BasicEvent ev 
                                    \<and> el ! (i - m - 1) -ee\<rightarrow> el ! (i - m)" and
                       b1: "Suc m < i"
                then have b2: "getspc_e (el ! (i - m - 1)) = BasicEvent ev" and
                          b3: "el ! (i - m - 1) -ee\<rightarrow> el ! (i - m)"
                            using Suc_lessD apply blast
                            using Suc_lessD b0 b1 by blast
                have b4: "Suc m = m + 1" by auto
                with b2 have "\<not>(\<exists>t ec1. ec1-et-t\<rightarrow>(el ! (i - Suc m))) " 
                  using no_tran2basic getspc_e_def by (metis diff_diff_left prod.collapse)  
                with p1 p02 have b5: "getspc_e (el ! ((i - Suc m - 1))) = getspc_e (el ! (i - Suc m))" 
                  using notran_confeqi by (smt Suc_diff_1 Suc_lessD b1 diff_less less_trans p01 
                                          zero_less_Suc zero_less_diff) 
                with b2 b4 have b6: "getspc_e (el ! ((i - Suc m - 1))) = BasicEvent ev"
                  by (metis diff_diff_left) 
                from b5 have "el ! (i - Suc m - 1) -ee\<rightarrow> el ! (i - Suc m)" using eqconf_eetran by simp
                with b6 show ?case by simp
              qed
          }
          then show ?thesis by auto
          qed
            
      }
      then show ?thesis by (metis (no_types, lifting) Suc_le_lessD diff_Suc_1 diff_Suc_less 
                            diff_diff_cancel gr_implies_not0 less_antisym zero_less_Suc) 
      qed
  qed

lemma evtent_in_cpts2: "el \<in> cpts_ev \<and> el ! 0 = (BasicEvent ev, s, x) \<Longrightarrow> 
      Suc i < length el \<and> el ! i -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc i) \<Longrightarrow> 
      (gets_e (el ! i) \<in> guard ev \<and> drop (Suc i) el \<in> 
          cpts_of_ev (AnonyEvent (Some (body ev))) (gets_e (el ! (Suc i))) ((getx_e (el ! i)) (k := BasicEvent ev)) )"
  proof -
    assume p0: "el \<in> cpts_ev \<and> el ! 0 = (BasicEvent ev, s, x)"
    assume p1: "Suc i < length el \<and> el ! i -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc i)"
    then have a2: "gets_e (el ! i) \<in> guard ev \<and> gets_e (el ! i) = gets_e (el ! (Suc i))
                            \<and> getspc_e (el ! (Suc i)) = AnonyEvent (Some (body ev))
                            \<and> getx_e (el ! (Suc i)) = (getx_e (el ! i)) (k := BasicEvent ev)"
      by (meson ent_spec2) 
    
    from p1 have "(drop (Suc i) el)!0 = el ! (Suc i)" by auto
    with a2 have a3: "(drop (Suc i) el)!0 = (AnonyEvent (Some (body ev)),(gets_e (el ! (Suc i)), 
                                          (getx_e (el ! i)) (k := BasicEvent ev) ))" 
       using gets_e_def getspc_e_def getx_e_def by (metis prod.collapse)
    have a4: "drop (Suc i) el \<in> cpts_ev" by (simp add: cpts_ev_subi p0 p1) 
    with a2 a3 show "gets_e (el ! i) \<in> guard ev \<and> drop (Suc i) el \<in> 
          cpts_of_ev (AnonyEvent (Some (body ev))) (gets_e (el ! (Suc i))) ((getx_e (el ! i)) (k := BasicEvent ev))"
       by (metis (mono_tags, lifting) CollectI cpts_of_ev_def) 
      
  qed


lemma no_evtent_in_cpts: "el \<in> cpts_ev \<Longrightarrow> el ! 0 = (BasicEvent ev, s, x) \<Longrightarrow> 
      (\<not> (\<exists>i k. Suc i < length el \<and> el ! i -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc i)) ) \<Longrightarrow> 
      (\<forall>j. Suc j < length el \<longrightarrow> getspc_e (el ! j) = BasicEvent ev 
                                \<and> el ! j -ee\<rightarrow> el ! (Suc j)
                                \<and> getspc_e (el ! (Suc j)) = BasicEvent ev)" 
  proof -  
    assume p0: "el \<in> cpts_ev" and
           p1: "el ! 0 = (BasicEvent ev, s, x)" and
           p2: "\<not> (\<exists>i k. Suc i < length el \<and> el ! i -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc i))"
    show ?thesis 
      proof -
      {
        fix j
        assume "Suc j < length el"
        then have "getspc_e (el ! j) = BasicEvent ev \<and> el ! j -ee\<rightarrow> el ! (Suc j) 
                  \<and> getspc_e (el ! (Suc j)) = BasicEvent ev"
          proof(induct j)
            case 0
            assume a0: "Suc 0 < length el"
            from p1 have a00: "getspc_e (el ! 0) = BasicEvent ev" by (simp add:getspc_e_def)
            from a0 p2 have "\<not> (\<exists>k. el ! 0 -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc 0))" by simp
            with p0 p1 have "\<not> (\<exists>t. el ! 0 -et-t\<rightarrow> el ! (Suc 0))" by (metis noevtent_notran) 
            with p0 a0 have a1: "getspc_e (el ! 0) = getspc_e (el ! (Suc 0))"
              using notran_confeqi by blast 

            with a00 have a2: "getspc_e (el ! (Suc 0)) = BasicEvent ev" by simp
            from a1 have "el ! 0 -ee\<rightarrow> el ! Suc 0" using getspc_e_def eetran.EnvE
                  by (metis eq_fst_iff)
            then show ?case by (simp add: a00 a2)  
          next
            case (Suc m)
            assume a0: "Suc m < length el \<Longrightarrow> getspc_e (el ! m) = BasicEvent ev \<and> el ! m -ee\<rightarrow> el ! Suc m
                        \<and> getspc_e (el ! Suc m) = BasicEvent ev"
            assume a1: "Suc (Suc m) < length el"
            with a0 have a2: "getspc_e (el ! m) = BasicEvent ev \<and> el ! m -ee\<rightarrow> el ! Suc m" by simp
            then have a3: "getspc_e (el ! Suc m) = BasicEvent ev" using getspc_e_def by (metis eetranE fstI)
            
            then have a4: "\<exists>s x. el ! Suc m = (BasicEvent ev, s, x)" unfolding getspc_e_def
              by (metis fst_conv surj_pair) 
            from a0 a1 p2 have "\<not> (\<exists>k. el ! (Suc m) -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc (Suc m) ))" by simp
            with a4 have a5: "\<not> (\<exists>t. el ! (Suc m) -et-t\<rightarrow> el ! (Suc (Suc m)))"
              using noevtent_notran by metis

            
            with p0 a0 a1 have a6: "getspc_e (el ! (Suc m)) = getspc_e (el ! (Suc (Suc m)))"
              using notran_confeqi by blast 
            with a3 have a7: "getspc_e (el ! (Suc (Suc m))) = BasicEvent ev" by simp
            from a6 have "el ! Suc m -ee\<rightarrow> el ! Suc (Suc m)" using getspc_e_def eetran.EnvE
                  by (metis eq_fst_iff)

            with a3 a7 show ?case by simp
          qed
      }
      then show ?thesis by auto
      qed
  qed
  
subsubsection \<open>trace between of event and event system\<close>

primrec rm_evtsys0 :: "('l,'k,'s) esys \<Rightarrow> 's \<Rightarrow> ('l,'k,'s) x \<Rightarrow> ('l,'k,'s) econf"
  where EvtSeqrm: "rm_evtsys0 (EvtSeq e es) s x= (e, s, x)" |
        EvtSysrm: "rm_evtsys0 (EvtSys es) s x= (AnonyEvent None, s, x)"

definition rm_evtsys1 :: "('l,'k,'s) esconf \<Rightarrow> ('l,'k,'s) econf"
  where "rm_evtsys1 esc \<equiv> rm_evtsys0 (getspc_es esc) (gets_es esc) (getx_es esc)" 

definition rm_evtsys :: "('l,'k,'s) esconfs \<Rightarrow> ('l,'k,'s) econfs"
  where "rm_evtsys escfs \<equiv> map rm_evtsys1 escfs"

definition e_eqv_einevtseq :: "('l,'k,'s) esconfs \<Rightarrow> ('l,'k,'s) econfs \<Rightarrow> ('l,'k,'s) esys \<Rightarrow> bool" 
  where "e_eqv_einevtseq esl el es \<equiv> length esl = length el \<and> 
            (\<forall>i. Suc i \<le> length el \<longrightarrow> gets_e (el ! i) = gets_es (esl ! i) \<and>
                                       getx_e (el ! i) = getx_es (esl ! i) \<and>
                                       getspc_es (esl ! i) = EvtSeq (getspc_e (el ! i)) es)"

lemma e_eqv_einevtseq_s : "\<lbrakk>e_eqv_einevtseq esl el es; gets_e e1 = gets_es es1; getx_e e1 = getx_es es1;
                            getspc_es es1 = EvtSeq (getspc_e e1) es\<rbrakk> \<Longrightarrow> e_eqv_einevtseq (es1 # esl) (e1 # el) es"
  proof -
    assume p0: "e_eqv_einevtseq esl el es"
      and  p1: "gets_e e1 = gets_es es1"
      and  p2: "getx_e e1 = getx_es es1"
      and  p3: "getspc_es es1 = EvtSeq (getspc_e e1) es"
    let ?el' = "e1 # el"
    let ?esl' = "es1 # esl"
    from p0 have a1: "length esl = length el" by (simp add: e_eqv_einevtseq_def)
    from p0 have a2: "\<forall>i. Suc i \<le> length el \<longrightarrow> gets_e (el ! i) = gets_es (esl ! i) \<and>
                                                 getx_e (el ! i) = getx_es (esl ! i) \<and>
                                                 getspc_es (esl ! i) = EvtSeq (getspc_e (el ! i)) es" 
      by (simp add: e_eqv_einevtseq_def)
    from a1 have "length (es1 # esl) = length (e1 # el)" by simp
    moreover have "\<forall>i. Suc i \<le> length ?el' \<longrightarrow> gets_e (?el' ! i) = gets_es (?esl' ! i) \<and>
                                       getx_e (?el' ! i) = getx_es (?esl' ! i) \<and>
                                       getspc_es (?esl' ! i) = EvtSeq (getspc_e (?el' ! i)) es"
      by (simp add: a2 nth_Cons' p1 p2 p3) 
    ultimately show "e_eqv_einevtseq ?esl' ?el' es" by (simp add:e_eqv_einevtseq_def)
  qed
       
definition same_s_x:: "('l,'k,'s) esconfs \<Rightarrow> ('l,'k,'s) econfs \<Rightarrow> bool" 
  where "same_s_x esl el \<equiv> length esl = length el \<and> 
            (\<forall>i. Suc i \<le> length el \<longrightarrow> gets_e (el ! i) = gets_es (esl ! i) \<and>
                                       getx_e (el ! i) = getx_es (esl ! i))"

lemma rm_evtsys_same_sx: "same_s_x esl (rm_evtsys esl)"
  proof(induct esl)
    case Nil 
    show ?case by (simp add:rm_evtsys_def same_s_x_def)
  next
    case (Cons ec1 esl1)
    assume a0: "same_s_x esl1 (rm_evtsys esl1)"
    have a1: "rm_evtsys (ec1 # esl1) = rm_evtsys1 ec1 # rm_evtsys esl1" by (simp add:rm_evtsys_def)
    obtain es and s and x where a2: "ec1 = (es, s, x)" using prod_cases3 by blast 
    then show ?case 
      proof(induct es)
        case (EvtSeq x1 es1)
        assume b0: "ec1 = (EvtSeq x1 es1, s, x)"
        then have b1: "rm_evtsys1 ec1 # rm_evtsys esl1 = (x1, s, x) # rm_evtsys esl1"
          by (simp add:rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
        have "length (ec1 # esl1) = length (rm_evtsys (ec1 # esl1))" by (simp add: rm_evtsys_def) 
        moreover have "\<forall>i. Suc i \<le> length (rm_evtsys (ec1 # esl1)) \<longrightarrow> 
                            gets_e ((rm_evtsys (ec1 # esl1)) ! i) = gets_es ((ec1 # esl1) ! i) 
                          \<and> getx_e ((rm_evtsys (ec1 # esl1)) ! i) = getx_es ((ec1 # esl1) ! i)"
          proof -
          {
            fix i
            assume c0: "Suc i \<le> length (rm_evtsys (ec1 # esl1))"
            have "gets_e ((rm_evtsys (ec1 # esl1)) ! i) = gets_es ((ec1 # esl1) ! i) 
                          \<and> getx_e ((rm_evtsys (ec1 # esl1)) ! i) = getx_es ((ec1 # esl1) ! i)" 
              proof(cases "i = 0")
                assume d0: "i = 0"
                with a0 a1 b0 b1 show ?thesis using gets_e_def gets_es_def getx_e_def getx_es_def 
                  by (metis nth_Cons_0 snd_conv)
              next
                assume d0: "i \<noteq> 0"
                then have "(rm_evtsys (ec1 # esl1)) ! i = (rm_evtsys esl1) ! (i - 1)"
                  by (simp add: a1) 
                moreover have "(ec1 # esl1) ! i = esl1 ! (i - 1)"
                  by (simp add: d0 nth_Cons')
                ultimately show ?thesis using a0 c0 d0 same_s_x_def
                  by (metis (no_types, lifting) Suc_diff_1 Suc_leI Suc_le_lessD 
                      Suc_less_eq a1 length_Cons neq0_conv)
              qed
          }
          then show ?thesis by auto
          qed

        ultimately show ?case using same_s_x_def by blast
      next
        case (EvtSys xa)
        assume b0: "ec1 = (EvtSys xa, s, x)"
        then have b1: "rm_evtsys1 ec1 # rm_evtsys esl1 = (AnonyEvent None, s, x) # rm_evtsys esl1"
          by (simp add:rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
        have "length (ec1 # esl1) = length (rm_evtsys (ec1 # esl1))" by (simp add: rm_evtsys_def) 
        moreover have "\<forall>i. Suc i \<le> length (rm_evtsys (ec1 # esl1)) \<longrightarrow> 
                            gets_e ((rm_evtsys (ec1 # esl1)) ! i) = gets_es ((ec1 # esl1) ! i) 
                          \<and> getx_e ((rm_evtsys (ec1 # esl1)) ! i) = getx_es ((ec1 # esl1) ! i)"
          proof -
          {
            fix i
            assume c0: "Suc i \<le> length (rm_evtsys (ec1 # esl1))"
            have "gets_e ((rm_evtsys (ec1 # esl1)) ! i) = gets_es ((ec1 # esl1) ! i) 
                          \<and> getx_e ((rm_evtsys (ec1 # esl1)) ! i) = getx_es ((ec1 # esl1) ! i)" 
              proof(cases "i = 0")
                assume d0: "i = 0"
                with a0 a1 b0 b1 show ?thesis using gets_e_def gets_es_def getx_e_def getx_es_def 
                  by (metis nth_Cons_0 snd_conv)
              next
                assume d0: "i \<noteq> 0"
                then have "(rm_evtsys (ec1 # esl1)) ! i = (rm_evtsys esl1) ! (i - 1)"
                  by (simp add: a1) 
                moreover have "(ec1 # esl1) ! i = esl1 ! (i - 1)"
                  by (simp add: d0 nth_Cons')
                ultimately show ?thesis using a0 c0 d0 same_s_x_def
                  by (metis (no_types, lifting) Suc_diff_1 Suc_leI Suc_le_lessD 
                      Suc_less_eq a1 length_Cons neq0_conv)
              qed
          }
          then show ?thesis by auto
          qed
        ultimately show ?case using same_s_x_def by blast
      qed
  qed

definition e_sim_es:: "('l,'k,'s) esconfs \<Rightarrow> ('l,'k,'s) econfs 
                          \<Rightarrow> ('l,'k,'s) event set \<Rightarrow> ('l,'s) event' \<Rightarrow> bool" 
  where "e_sim_es esl el es e \<equiv> length esl = length el \<and> getspc_es (esl!0) = EvtSys es \<and>
                                getspc_e (el!0) = BasicEvent e \<and>
                                (\<forall>i. i < length el \<longrightarrow> gets_e (el ! i) = gets_es (esl ! i) \<and>
                                                        getx_e (el ! i) = getx_es (esl ! i)) \<and>
                                (\<forall>i. i > 0 \<and> i < length el \<longrightarrow> 
                                    (getspc_es (esl!i) = EvtSys es \<and> getspc_e (el!i) = AnonyEvent None) 
                                      \<or> (getspc_es (esl!i) = EvtSeq (getspc_e (el!i)) (EvtSys es))
                                 )"


subsection \<open>Soundness of Programs\<close>

subsubsection\<open>Soundness of the Rule of Consequence\<close>

lemma Conseq_sound:
  "\<lbrakk>pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
  \<Turnstile> P sat\<^sub>p [pre', rely', guar', post']\<rbrakk>
  \<Longrightarrow> \<Turnstile> P sat\<^sub>p [pre, rely, guar, post]"
  apply (simp add: prog_validity_def)
  apply clarify
  apply(erule_tac x=s in allE)
  apply (rule conjI)
   apply clarify
   apply (simp add: assume_p_def commit_p_def)
   apply(drule_tac c=x in subsetD)
    apply force
   apply force
  apply clarify
  apply (simp add: assume_p_def commit_p_def)
  apply(drule_tac c=x in subsetD)
   apply force
  apply force
  done


lemma Conseq_sound_r:
  "\<lbrakk> pre \<subseteq> r; stable r rely; \<Turnstile> P sat\<^sub>p [r, rely, guar, post]\<rbrakk>
  \<Longrightarrow>  \<Turnstile> P sat\<^sub>p [pre, rely, guar, post]"
  by (rule Conseq_sound, simp_all)

subsubsection \<open>Soundness of the Basic rule\<close>

lemma unique_ctran_Basic [rule_format]:
  "\<forall>s i. x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnBasic r f), s) \<longrightarrow>
  Suc i<length x \<longrightarrow> x!i -c\<rightarrow> x!Suc i \<longrightarrow>
  (\<forall>j. Suc j<length x \<longrightarrow> i\<noteq>j \<longrightarrow> x!j -pe\<rightarrow> x!Suc j)"
apply(induct x,simp)
apply simp
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp+)
 apply clarify
 apply(case_tac j,simp)
  apply(rule EnvP)
 apply simp
apply clarify
apply simp
apply(case_tac i)
 apply(case_tac j,simp,simp)
 apply(erule ptran.cases,simp_all)
 apply(force elim: not_ctran_None)
apply(ind_cases "((Some (AnnBasic r f), sa), Q, t) \<in> ptran" for sa Q t)
apply simp
apply(drule_tac i=nat in not_ctran_None,simp)
apply(erule petranE,simp)
done

lemma exists_ctran_Basic_None [rule_format]:
  "\<forall>s i. x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnBasic r f), s)
  \<longrightarrow> i<length x \<longrightarrow> fst(x!i)=None \<longrightarrow> (\<exists>j<i. x!j -c\<rightarrow> x!Suc j)"
apply(induct x,simp)
apply simp
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp,simp)
 apply(erule_tac x=nat in allE,simp)
 apply clarify
 apply(rule_tac x="Suc j" in exI,simp,simp)
apply clarify
apply(case_tac i,simp,simp)
apply(rule_tac x=0 in exI,simp)
  done

lemma Basic_sound:
  " \<lbrakk> pre \<subseteq> r; r \<subseteq> {s. f s \<in> post}; {(s,t). s \<in> r \<and> (t=f s)} \<subseteq> guar;
            stable r rely; stable post rely\<rbrakk>
  \<Longrightarrow> \<Turnstile> AnnBasic r f sat\<^sub>p [pre, rely, guar, post]"
  apply (rule Conseq_sound_r, simp_all)
  apply(unfold prog_validity_def)
  apply clarify
  apply (rule IntI)
   apply(simp add:commit_p_def)
   apply(simp add:getspc_p_def gets_p_def)
   apply(rule conjI, clarify)
    apply(simp add:cpts_of_p_def assume_p_def gets_p_def)
    apply clarify
    apply(frule_tac j=0 and k=i and p= r in stability)
          apply simp_all
      apply(erule_tac x=ia in allE,simp)
     apply(erule_tac i=i and f=f in unique_ctran_Basic,simp_all)
    apply(erule subsetD,simp)
    apply(case_tac "x!i")
    apply clarify
    apply(drule_tac s="Some (AnnBasic r f)" in sym,simp)
    apply(thin_tac "\<forall>j. H j" for H)
    apply(force elim:ptran.cases)
   apply clarify
   apply(simp add:cpts_of_p_def)
   apply clarify
   apply(frule_tac i="length x - 1" and f=f in exists_ctran_Basic_None,simp+)
     apply(case_tac x,simp+)
    apply(rule last_fst_esp,simp add:last_length)
    apply (case_tac x,simp+)
   apply(simp add:assume_p_def gets_p_def)
   apply clarify
   apply(frule_tac j=0 and k="j" and p=r in stability)
         apply simp_all
     apply(erule_tac x=i in allE,simp)
    apply(erule_tac i=j and f=f in unique_ctran_Basic,simp_all)
   apply(case_tac "x!j")
   apply clarify
   apply simp
   apply(drule_tac s="Some (AnnBasic r f)" in sym,simp)
   apply(case_tac "x!Suc j",simp)
   apply(rule ptran.cases,simp)
           apply(simp_all)
   apply(drule_tac c=sa in subsetD,simp)
   apply clarify
   apply(frule_tac j="Suc j" and k="length x - 1" and p=post in stability,simp_all)
     apply(case_tac x,simp+)
    apply(erule_tac x=i in allE)
    apply(erule_tac i=j and f=f in unique_ctran_Basic,simp_all)
     apply arith+
   apply(case_tac x)
    apply(simp add:last_length)+
  apply (case_tac "\<exists>i. Suc i < length x \<and> (x!i) -c\<rightarrow> (x!(Suc i))")
   apply (simp add: preserves_p_def cpts_of_p_def assume_p_def gets_p_def)
   apply clarify
   apply (case_tac "ia \<le> i")
    apply(frule_tac j=0 and k=ia and p= r in stability, simp_all)
      apply blast
  using unique_ctran_Basic apply fastforce
    apply (case_tac "x!ia")
    apply (simp add: getspc_p_def, clarsimp)
   apply(frule_tac j=0 and k=i and p= r in stability, simp_all)
     apply blast
    apply(erule_tac i=i and f=f in unique_ctran_Basic,simp_all)
   apply (case_tac "x ! Suc i")
   apply (erule ptran.cases, simp_all)
   apply (drule_tac i = "Suc i" and j = ia in not_ctran_Finish, simp_all)
   apply (simp add: getspc_p_def)
  apply (simp add: preserves_p_def cpts_of_p_def assume_p_def gets_p_def)
  apply clarify 
  apply(frule_tac j=0 and k=i and p= r in stability, simp_all)
    apply blast
   apply (drule_tac m = "length x" and i = "ia" in etran_or_ctran, simp_all)
  apply (case_tac "x!i")
  apply (simp add: getspc_p_def, clarsimp)
  done
 
subsubsection\<open>Soundness of the Await rule\<close>

lemma unique_ctran_Await [rule_format]:
  "\<forall>s i. x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnAwait r b c), s) \<longrightarrow>
  Suc i<length x \<longrightarrow> x!i -c\<rightarrow> x!Suc i \<longrightarrow>
  (\<forall>j. Suc j<length x \<longrightarrow> i\<noteq>j \<longrightarrow> x!j -pe\<rightarrow> x!Suc j)"
apply(induct x,simp+)
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp+)
 apply clarify
 apply(case_tac j,simp)
  apply(rule EnvP)
 apply simp
apply clarify
apply simp
apply(case_tac i)
 apply(case_tac j,simp,simp)
 apply(erule ptran.cases,simp_all)
 apply(force elim: not_ctran_None)
apply(ind_cases "((Some (AnnAwait r b c), sa), Q, t) \<in> ptran" for sa Q t,simp)
apply(drule_tac i=nat in not_ctran_None,simp)
apply(erule petranE,simp)
done

lemma exists_ctran_Await_None [rule_format]:
  "\<forall>s i.  x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnAwait r b c), s)
  \<longrightarrow> i<length x \<longrightarrow> fst(x!i)=None \<longrightarrow> (\<exists>j<i. x!j -c\<rightarrow> x!Suc j)"
apply(induct x,simp+)
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp+)
 apply(erule_tac x=nat in allE,simp)
 apply clarify
 apply(rule_tac x="Suc j" in exI,simp,simp)
apply clarify
apply(case_tac i,simp,simp)
apply(rule_tac x=0 in exI,simp)
done

lemma Star_imp_cptn:
  "(P, s) -c*\<rightarrow> (R, t) \<Longrightarrow> \<exists>l \<in> cpts_of_p P s. (last l)=(R, t)
  \<and> (\<forall>i. Suc i<length l \<longrightarrow> l!i -c\<rightarrow> l!Suc i)"
apply (erule converse_rtrancl_induct2)
 apply(rule_tac x="[(R,t)]" in bexI)
  apply simp
 apply(simp add:cpts_of_p_def)
 apply(rule CptsPOne)
apply clarify
apply(rule_tac x="(a, b)#l" in bexI)
 apply (rule conjI)
  apply(case_tac l,simp add:cpts_of_p_def)
  apply(simp add:last_length)
 apply clarify
apply(case_tac i,simp)
apply(simp add:cpts_of_p_def)
apply force
apply(simp add:cpts_of_p_def)
 apply(case_tac l)
 apply(force elim:cpts_p.cases)
apply simp
apply(erule CptsPComp)
apply clarify
done

lemma Await_sound:
  "\<lbrakk>pre \<subseteq> r; stable r rely; stable post rely;
   \<forall>V. \<turnstile> P sat\<^sub>p [r \<inter> b \<inter> {s. s = V}, {(s, t). s = t},
                 UNIV, {s. (V, s) \<in> guar} \<inter> post] \<and>
   \<Turnstile> P sat\<^sub>p [r \<inter> b \<inter> {s. s = V}, {(s, t). s = t},
                 UNIV, {s. (V, s) \<in> guar} \<inter> post]\<rbrakk>
   \<Longrightarrow> \<Turnstile> AnnAwait r b P sat\<^sub>p [pre, rely, guar, post]"
  apply (rule Conseq_sound_r, simp_all)
  apply(unfold prog_validity_def)
  apply clarify
  apply (rule IntI)
   apply(simp add:commit_p_def)
   apply(rule conjI, clarify)
    apply(simp add:cpts_of_p_def assume_p_def gets_p_def getspc_p_def)
    apply clarify
    apply(frule_tac j=0 and k=i and p= r in stability,simp_all)
      apply(erule_tac x=ia in allE,simp)
     apply(subgoal_tac "x\<in> cpts_of_p (Some(AnnAwait r b P)) s")
      apply(erule_tac i=i in unique_ctran_Await,force,simp_all)
     apply(simp add:cpts_of_p_def)
(*here starts the different part.*)
    apply(erule ptran.cases,simp_all)
    apply(drule Star_imp_cptn)
    apply clarify
    apply(erule_tac x=sa in allE)
    apply clarify
    apply(erule_tac x=sa in allE)
    apply auto[1]
    apply(drule_tac c=l in subsetD)
     apply (simp add:cpts_of_p_def)
     apply clarify
     apply(erule_tac x=ia and P="\<lambda>i. H i \<longrightarrow> (J i, I i)\<in>ptran" for H J I in allE,simp)
     apply(erule petranE,simp)
    apply simp
   apply clarify
   apply (simp add:gets_p_def getspc_p_def)
   apply(simp add:cpts_of_p_def)
   apply clarify
   apply(frule_tac i="length x - 1" in exists_ctran_Await_None,force)
     apply (case_tac x,simp+)
    apply(rule last_fst_esp,simp add:last_length)
    apply(case_tac x, simp+)
   apply clarify
   apply(simp add:assume_p_def gets_p_def getspc_p_def)
   apply clarify
   apply(frule_tac j=0 and k="j" and p= r and rely = rely in stability,simp_all)
    apply(erule_tac i=j in unique_ctran_Await,force,simp_all)
   apply(case_tac "x!j")
   apply clarify
   apply simp
   apply(drule_tac s="Some (AnnAwait r b P)" in sym,simp)
   apply(case_tac "x!Suc j",simp)
   apply(rule ptran.cases,simp)
           apply(simp_all)
   apply(drule Star_imp_cptn)
   apply clarify
   apply(erule_tac x=sa in allE)
   apply clarify
   apply(erule_tac x=sa in allE)
   apply auto[1]
   apply(drule_tac c=l in subsetD)
    apply (simp add:cpts_of_p_def)
    apply clarify
    apply(erule_tac x=i and P="\<lambda>i. H i \<longrightarrow> (J i, I i)\<in>ptran" for H J I in allE,simp)
    apply(erule petranE,simp)
   apply simp
   apply clarify
   apply(frule_tac j="Suc j" and k="length x - 1" and p=post in stability,simp_all)
     apply(case_tac x,simp+)
    apply(erule_tac x=i in allE)
    apply(erule_tac i=j in unique_ctran_Await,force,simp_all)
     apply arith+
   apply(case_tac x)
    apply(simp add:last_length)+
  apply (case_tac "\<exists>i. Suc i < length x \<and> (x!i) -c\<rightarrow> (x!(Suc i))")
   apply (simp add: preserves_p_def cpts_of_p_def assume_p_def gets_p_def)
   apply clarify
   apply (case_tac "ia \<le> i")
    apply(frule_tac j=0 and k=ia and p= r in stability, simp_all)
      apply blast
  using unique_ctran_Await apply fastforce
    apply (case_tac "x!ia")
    apply (simp add: getspc_p_def, clarsimp)
   apply(frule_tac j=0 and k=i and p= r in stability, simp_all)
     apply blast
    apply(erule_tac i=i in unique_ctran_Await,simp_all)
   apply (case_tac "x ! Suc i")
   apply (erule ptran.cases, simp_all)
   apply (drule_tac i = "Suc i" and j = ia in not_ctran_Finish, simp_all)
   apply (simp add: getspc_p_def)
  apply (simp add: preserves_p_def cpts_of_p_def assume_p_def gets_p_def)
  apply clarify 
  apply(frule_tac j=0 and k=i and p= r in stability, simp_all)
    apply blast
   apply (drule_tac m = "length x" and i = "ia" in etran_or_ctran, simp_all)
  apply (case_tac "x!i")
  apply (simp add: getspc_p_def, clarsimp)
  done


subsubsection\<open>Soundness of the Conditional rule\<close>
lemma all_impD : "\<lbrakk>\<forall>a. P a \<longrightarrow> Q a ; P a \<rbrakk> \<Longrightarrow> Q a"
  by simp

lemma all_imp2D : "\<lbrakk>\<forall>a. P a \<longrightarrow> Q a \<longrightarrow> R a; P a; Q a\<rbrakk> \<Longrightarrow> R a"
  by simp

lemma Cond_sound:
  "\<lbrakk> pre \<subseteq> r;  stable r rely; \<Turnstile> P1 sat\<^sub>p [r \<inter> b, rely, guar, post];
     \<Turnstile> P2 sat\<^sub>p [r \<inter> -b, rely, guar, post]; \<forall>s. (s,s)\<in>guar \<rbrakk>
    \<Longrightarrow> \<Turnstile> AnnCond r b P1 P2 sat\<^sub>p [pre, rely, guar, post]"
  apply (rule Conseq_sound_r, simp_all)
  apply(unfold prog_validity_def)
  apply clarify
  apply (rule IntI)
   apply(simp add:cpts_of_p_def commit_p_def)
   apply(simp add:getspc_p_def gets_p_def)
   apply(case_tac "\<exists>i. Suc i<length x \<and> x!i -c\<rightarrow> x!Suc i")
    prefer 2
    apply simp
    apply clarify
   apply(frule_tac j="0" and k="length x - 1" and p= r in stability,simp+)
       apply(case_tac x,simp+)
      apply(simp add:assume_p_def gets_p_def)
     apply(simp add:assume_p_def gets_p_def)
    apply(erule_tac m="length x" in etran_or_ctran,simp+)
    apply(case_tac x, (simp add:last_length)+)
   apply(erule exE)
   apply(drule_tac n=i and P="\<lambda>i. H i \<and> (J i, I i) \<in> ptran" for H J I in Ex_first_occurrence)
  apply clarify
  apply (simp add:assume_p_def gets_p_def)
  apply(frule_tac j=0 and k="m" and p= "r" in stability,simp+)
   apply(erule_tac m="Suc m" in etran_or_ctran,simp+)
  apply(erule ptran.cases,simp_all)
    apply(erule_tac x="sa" in allE)
    apply clarify
    apply(drule_tac c="drop (Suc m) x" in subsetD)
    apply simp
    apply clarify
   apply simp
   apply clarify
    apply(case_tac "i\<le>m")
     apply(drule le_imp_less_or_eq)
     apply(erule_tac x=i in allE, erule impE, assumption)
     apply (metis (no_types, lifting) le_neq_implies_less snd_conv)
    apply simp
    apply(erule_tac x="i - (Suc m)" and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> (I j)\<in>guar" for H J I in allE)
    apply(subgoal_tac "(Suc m)+(i - Suc m) \<le> length x")
     apply(subgoal_tac "(Suc m)+Suc (i - Suc m) \<le> length x")
      apply(rotate_tac -2)
      apply simp
     apply arith
    apply arith
   apply(case_tac "length (drop (Suc m) x)",simp)
   apply(erule_tac x="sa" in allE)
   back
   apply clarify
   apply(drule_tac c="drop (Suc m) x" in subsetD,simp)
    apply clarsimp
   apply clarsimp
   apply(case_tac "i\<le>m")
    apply(drule le_imp_less_or_eq)
    apply(erule disjE)
     apply(erule_tac x=i in allE, erule impE, assumption)
     apply (metis (no_types, hide_lams) le_neq_implies_less snd_conv)
    apply (metis (no_types, lifting) le_neq_implies_less snd_conv)
   apply(erule_tac x="i - (Suc m)" and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> (I j)\<in>guar" for H J I in allE)
   apply(subgoal_tac "(Suc m)+(i - Suc m) \<le> length x")
    apply(subgoal_tac "(Suc m)+Suc (i - Suc m) \<le> length x")
     apply(rotate_tac -2)
     apply simp
    apply arith
   apply arith
  apply(simp add:cpts_of_p_def preserves_p_def getspc_p_def gets_p_def)
  apply(case_tac "\<exists>i. Suc i<length x \<and> x!i -c\<rightarrow> x!Suc i")
   prefer 2
  apply clarsimp
   apply(frule_tac j="0" and k="i" and p= r in stability,simp+)
      apply(simp add:assume_p_def gets_p_def)
     apply(simp add:assume_p_def gets_p_def)
    apply(erule_tac m="length x" in etran_or_ctran,simp+)
   apply (case_tac "x!i")
   apply (simp add: getspc_p_def, clarsimp)
  apply(erule exE, simp add: assume_p_def gets_p_def)
  apply(drule_tac n=i and P="\<lambda>i. H i \<and> (J i, I i) \<in> ptran" for H J I in Ex_first_occurrence)
  apply clarify
  apply (case_tac " ia < m")
   apply(frule_tac j="0" and k= "ia" and p= r in stability,simp+)
    apply (drule_tac m = "m" and i = "ib" in etran_or_ctran, simp_all)
   apply (case_tac "x!ia")
   apply (simp add: gets_p_def, clarsimp)
  apply(frule_tac j="0" and k= "m" and p= r in stability,simp+)
   apply(erule_tac m="Suc m" in etran_or_ctran,simp+)
  apply (case_tac "ia = m")
   apply (case_tac "x!m")
   apply (simp add: gets_p_def, clarsimp)
  apply(erule ptran.cases,simp_all)
   apply (erule_tac x = sa in allE)
   apply auto[1]
   apply(drule_tac c="drop (Suc m) x" in subsetD)
  back
    apply clarsimp
    apply (simp add: dropcptn_is_cptn)
   apply clarsimp
   apply (erule_tac x = "ia - Suc m" in allE)
   back
   back
   apply (erule impE, simp, simp)
  apply (erule_tac x = sa in allE)
  back
  apply auto[1]
  apply(drule_tac c="drop (Suc m) x" in subsetD)
   back
   apply clarsimp
   apply (simp add: dropcptn_is_cptn)
  apply clarsimp
  apply (erule_tac x = "ia - Suc m" in allE)
  back
  back
  apply (erule impE, simp, simp)
  done

subsubsection\<open>Soundness of the Sequential rule\<close>

inductive_cases Seq_cases [elim!]: "(Some (Seq P Q), s) -c\<rightarrow> t"

lemma last_lift_not_None: "fst ((lift Q) ((x#xs)!(length xs))) \<noteq> None"
apply(subgoal_tac "length xs<length (x # xs)")
 apply(drule_tac Q=Q in  lift_nth)
 apply(erule ssubst)
 apply (simp add:lift_def)
 apply(case_tac "(x # xs) ! length xs",simp)
apply simp
  done

lemma Seq_sound1 [rule_format]:
  "x\<in> cpt_p_mod \<Longrightarrow> \<forall>s P. x !0=(Some (AnnSeq P Q), s) \<longrightarrow>
  (\<forall>i<length x. fst(x!i)\<noteq>Some Q) \<longrightarrow>
  (\<exists>xs\<in> cpts_of_p (Some P) s. x=map (lift Q) xs)"
apply(erule cpt_p_mod.induct)
apply(unfold cpts_of_p_def)
apply safe
apply simp_all
    apply(simp add:lift_def)
    apply(rule_tac x="[(Some Pa, sa)]" in exI,simp add:CptsPOne)
   apply(subgoal_tac "(\<forall>i < Suc (length xs). fst (((Some (AnnSeq Pa Q), t) # xs) ! i) \<noteq> Some Q)")
    apply clarify
    apply(rule_tac x="(Some Pa, sa) #(Some Pa, t) # zs" in exI,simp)
    apply(rule conjI,erule CptsPEnv)
    apply(simp (no_asm_use) add:lift_def)
   apply clarify
   apply(erule_tac x="Suc i" in allE, simp)
 apply(rule_tac x="(Some P, sa) # xs" in exI, simp add:cpts_iff_cpt_p_mod lift_def)
apply(erule_tac x="length xs" in allE, simp)
apply(simp only:Cons_lift_append)
apply(subgoal_tac "length xs < length ((Some P, sa) # xs)")
 apply(simp only :nth_append length_map last_length nth_map)
 apply(case_tac "last((Some P, sa) # xs)")
 apply(simp add:lift_def)
apply simp
  done

lemma Seq_sound2 [rule_format]:
  "x \<in> cpts_p \<Longrightarrow> \<forall>s P i. x!0=(Some (AnnSeq P Q), s) \<longrightarrow> i<length x
  \<longrightarrow> fst(x!i)=Some Q \<longrightarrow>
  (\<forall>j<i. fst(x!j)\<noteq>(Some Q)) \<longrightarrow>
  (\<exists>xs ys. xs \<in> cpts_of_p (Some P) s \<and> length xs=Suc i
   \<and> ys \<in> cpts_of_p (Some Q) (snd(xs !i)) \<and> x=(map (lift Q) xs)@tl ys)"
apply(erule cpts_p.induct)
apply(unfold cpts_of_p_def)
apply safe
apply simp_all
 apply(case_tac i,simp+)
 apply(erule allE,erule impE,assumption,simp)
 apply clarify
 apply(subgoal_tac "(\<forall>j < nat. fst (((Some (AnnSeq Pa Q), t) # xs) ! j) \<noteq> Some Q)",clarify)
  prefer 2
  apply force
 apply(case_tac xsa,simp,simp)
 apply(rename_tac list)
 apply(rule_tac x="(Some Pa, sa) #(Some Pa, t) # list" in exI,simp)
 apply(rule conjI,erule CptsPEnv)
 apply(simp (no_asm_use) add:lift_def)
 apply(rule_tac x=ys in exI,simp)
apply(ind_cases "((Some (AnnSeq Pa Q), sa), t) \<in> ptran" for Pa sa t)
 apply simp
 apply(rule_tac x="(Some Pa, sa)#[(None, ta)]" in exI,simp)
 apply(rule conjI)
  apply(drule_tac xs="[]" in CptsPComp,force simp add:CptsPOne,simp)
 apply(case_tac i, simp+)
 apply(case_tac nat,simp+)
 apply(rule_tac x="(Some Q,ta)#xs" in exI,simp add:lift_def)
   apply(case_tac nat,simp+)
  using nth_Cons_Suc apply auto[1]
apply(case_tac i, simp+)
apply(case_tac nat,simp+)
apply(erule_tac x="Suc nata" in allE,simp)
apply clarify
apply(subgoal_tac "(\<forall>j<Suc nata. fst (((Some (AnnSeq P2 Q), ta) # xs) ! j) \<noteq> Some Q)",clarify)
 prefer 2
   apply clarify
  apply (metis (full_types) Suc_less_eq nth_Cons_Suc)
apply(rule_tac x="(Some Pa, sa)#(Some P2, ta)#(tl xsa)" in exI,simp)
apply(rule conjI,erule CptsPComp)
apply(rule nth_tl_if,force,simp+)
apply(rule_tac x=ys in exI,simp)
  apply(rule conjI)
  apply (simp add: List.nth_tl)
apply(rule conjI,simp add:lift_def)
apply(subgoal_tac "lift Q (Some P2, ta) =(Some (AnnSeq P2 Q), ta)")
 apply(simp add:Cons_lift del:list.map)
 apply(rule nth_tl_if)
   apply force
  apply simp+
apply(simp add:lift_def)
done


lemma last_lift_not_None2: "fst ((lift Q) (last (x#xs))) \<noteq> None"
apply(simp only:last_length [THEN sym])
apply(subgoal_tac "length xs<length (x # xs)")
 apply(drule_tac Q=Q in  lift_nth)
 apply(erule ssubst)
 apply (simp add:lift_def)
 apply(case_tac "(x # xs) ! length xs",simp)
apply simp
  done

lemma ann_preserves_pre : "\<forall>s. cpts_of_p (Some P) s \<inter> assume_p (pre, rely) \<subseteq> preserves_p \<Longrightarrow> pre \<subseteq> (ann_pre P)"
  apply (simp add: cpts_of_p_def assume_p_def)
  apply clarify
  apply (erule_tac x = x in allE)
  apply (drule_tac c= "[(Some P, x)]" in subsetD)
   apply (simp add: gets_p_def  cpts_p.CptsPOne)
  by (simp add: preserves_p_def getspc_p_def gets_p_def)

lemma preserves_p_append : "\<lbrakk> l = xs @ ys; xs \<in> preserves_p; ys \<in> preserves_p \<rbrakk> \<Longrightarrow> l \<in> preserves_p"
  by (simp add: preserves_p_def nth_append)

lemma lift_step : "lift Q (xs ! i) -c\<rightarrow> lift Q (xs ! Suc i) \<Longrightarrow> fst (xs ! i) \<noteq> None \<Longrightarrow> xs ! i -c\<rightarrow> xs ! Suc i"
proof-
  assume a1: "lift Q (xs ! i) -c\<rightarrow> lift Q (xs ! Suc i)"
  and    a2: "fst (xs ! i) \<noteq> None"
  then have "\<exists>P s. xs ! i = (Some P, s)" by (metis eq_fst_iff not_None_eq)
  then obtain P and s where b1 : "xs ! i = (Some P, s)"  by auto
  then show ?thesis
  proof(induct "fst (xs ! (Suc i))")
    case None
    then have "\<exists>t. xs ! (Suc i) = (None, t)"  by (metis prod.collapse)
    then obtain t where b2: "xs ! (Suc i) = (None, t)" by auto
    then have "(Some (AnnSeq P Q), s) -c\<rightarrow> (Some Q, t)"
      using a1 b1 by (simp add: lift_def)
    with b1 and b2 show ?case
      apply simp
      by (erule ptran.cases, simp_all)
  next
    case (Some R)
    then have "\<exists>t. xs ! (Suc i) = (Some R, t)"  by (metis prod.collapse)
    then obtain R and t where b3: "xs ! (Suc i) = (Some R, t)" by auto
    then have "(Some (AnnSeq P Q), s) -c\<rightarrow> (Some (AnnSeq R Q), t)"
      using a1 b1 by (simp add: lift_def)
      with b1 and b3 show ?case
        apply simp
        by (erule ptran.cases, simp_all)
    qed
  qed

lemma Seq_sound:
  "\<lbrakk>\<Turnstile> P sat\<^sub>p [pre, rely, guar, mid]; \<Turnstile> Q sat\<^sub>p [mid, rely, guar, post]\<rbrakk>
  \<Longrightarrow> \<Turnstile> AnnSeq P Q sat\<^sub>p [pre, rely, guar, post]"
  apply(unfold prog_validity_def)
  apply clarify
  apply(case_tac "\<exists>i<length x. fst(x!i)=Some Q")
   prefer 2
   apply (simp add:cpts_of_p_def cpts_iff_cpt_p_mod)
   apply clarify
   apply(frule_tac Seq_sound1,force)
    apply force
    apply clarify
   apply(erule_tac x=s in allE,simp)
   apply auto[1]
    apply(drule_tac c=xs in subsetD,simp add:cpts_of_p_def cpts_iff_cpt_p_mod)
     apply(simp add:assume_p_def gets_p_def)
     apply clarify
     apply(erule_tac P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE,erule impE, assumption)
     apply(simp add:snd_lift)
     apply(erule mp)
     apply(force elim:petranE intro:EnvP simp add:lift_def)
    apply(simp add:commit_p_def)
    apply(rule conjI)
     apply clarify
     apply(erule_tac P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE,erule impE, assumption)
     apply(simp add:snd_lift getspc_p_def gets_p_def)
     apply(case_tac "(xs!i)")
     apply(case_tac "(xs! Suc i)")
     apply(case_tac "fst(xs!i)")
      apply(erule_tac x=i in allE, simp add:lift_def)
     apply(case_tac "fst(xs!Suc i)")
      apply (metis (no_types, lifting)  One_nat_def add.right_neutral add_Suc_right diff_Suc_1 
      last_lift length_greater_0_conv length_map lift_nth  list.size(3) list.size(4) nth_Cons_0 zero_less_Suc)
     apply (force simp add: lift_def)
    apply(case_tac xs,simp add:cpts_of_p_def)
    apply clarify
    apply (simp del:list.map)
    apply (rename_tac list)
    apply(subgoal_tac "(map (lift Q) ((a, b) # list))\<noteq>[]")
     apply(drule last_conv_nth)
     apply (simp del:list.map)
     apply(simp add:getspc_p_def gets_p_def)
     apply(simp only:last_lift_not_None)
    apply simp
   apply(drule_tac c=xs in subsetD,simp add:cpts_of_p_def cpts_iff_cpt_p_mod)
    back
    apply(simp add:assume_p_def gets_p_def)
    apply clarify
    apply(erule_tac P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE,erule impE, assumption)
    apply(simp add:snd_lift)
    apply(erule mp)
    apply(force elim:petranE intro:EnvP simp add:lift_def)
   apply (simp add: preserves_p_def, clarsimp)
   apply (case_tac "xs!i")
   apply (case_tac "a")
    apply (simp add: getspc_p_def gets_p_def lift_def)
    apply (rule_tac A = mid in set_mp)
     apply (rule_tac rely = rely in ann_preserves_pre)
     apply auto[1]
    apply(drule_tac c="take (Suc i) xs" in subsetD,simp add:cpts_of_p_def cpts_iff_cpt_p_mod)
     apply (rule conjI)
      apply auto[1]
     apply(simp add:assume_p_def gets_p_def)
     apply auto[1]
    apply (simp add: commit_p_def gets_p_def getspc_p_def take_Suc_conv_app_nth)
   apply (simp add: lift_def getspc_p_def gets_p_def)
   apply auto[1]
(*@{text "\<exists>i<length x. fst (x ! i) = Some Q"}*)
   apply(erule exE)
   apply(drule_tac n=i and P="\<lambda>i. i < length x \<and> fst (x ! i) = Some Q" in Ex_first_occurrence)
   apply clarify
   apply (simp add:cpts_of_p_def)
   apply clarify
   apply(frule_tac i=m in Seq_sound2,force)
      apply simp+
  apply clarify
  apply (rule conjI)
   apply(simp add:commit_p_def)
   apply(erule_tac x=s in allE)
   apply clarify
   apply(drule_tac c=xs in subsetD,simp)
    apply(case_tac "xs=[]",simp)
    apply(simp add:cpts_of_p_def assume_p_def nth_append gets_p_def getspc_p_def)
    apply clarify
    apply(erule_tac x=i in allE)
    back
    apply(simp add:snd_lift)
    apply(erule mp)
    apply(force elim:petranE intro:EnvP simp add:lift_def)
   apply clarsimp
   apply(erule_tac x="snd(xs!m)" in allE)
   apply(simp add:getspc_p_def gets_p_def)
   apply clarify
   apply(drule_tac c=ys in subsetD)
    back
    apply (simp add:cpts_of_p_def assume_p_def)
    apply(case_tac "xs\<noteq>[]")
     apply(drule last_conv_nth,simp)
     apply(rule conjI)
      apply(simp add:gets_p_def)
      apply(case_tac "xs!m")
      apply(case_tac "fst(xs!m)", simp)
      apply(simp add:lift_def nth_append)
     apply clarify 
     apply(simp add:gets_p_def)
     apply(erule_tac x="m+i" in allE)
     back
     back
     apply(case_tac ys,(simp add:nth_append)+)
     apply (case_tac i, (simp add:snd_lift)+)
  
      apply(erule mp)
      apply(case_tac "xs!m")
      apply(force elim:etran.cases intro:EnvP simp add:lift_def)
     apply simp
    apply simp
   apply clarify
   apply(rule conjI,clarify)
    apply(case_tac "i<m",simp add:nth_append)
     apply(simp add:snd_lift)
     apply(erule allE, erule impE, assumption, erule mp)
     apply(case_tac "(xs ! i)")
     apply(case_tac "(xs ! Suc i)")
     apply (case_tac "fst (xs!i)")
      apply (erule_tac x = i in allE, simp add: lift_def)
     apply (rule lift_step, simp, simp)
    apply(erule_tac x="i-m" in allE)
    back
    back
    apply(subgoal_tac "Suc (i - m) < length ys",simp)
     prefer 2
     apply arith
 apply(simp add:nth_append snd_lift)
 apply(rule conjI,clarify)
  apply(subgoal_tac "i=m")
   prefer 2
   apply arith
     apply clarify
     apply(simp add:cpts_of_p_def)
     apply(rule tl_zero)
       apply(erule mp)
       apply(case_tac "lift Q (xs!m)",simp add:snd_lift)
       apply(case_tac "xs!m",case_tac "fst(xs!m)",simp add:lift_def snd_lift)
        apply(case_tac ys,simp+)
       apply(simp add:lift_def)
      apply simp
     apply force
    apply clarify
    apply(rule tl_zero)
      apply(rule tl_zero)
        apply (subgoal_tac "i-m=Suc(i-Suc m)")
         apply simp
         apply(erule mp)
         apply(case_tac ys,simp+)
      apply force
     apply arith
    apply force
   apply clarify
   apply(case_tac "(map (lift Q) xs @ tl ys)\<noteq>[]")
    apply(drule last_conv_nth)
    apply(simp add: snd_lift nth_append)
    apply(rule conjI,clarify)
     apply(case_tac ys,simp+)
    apply clarify
    apply(case_tac ys,simp+)
  apply (rule_tac xs = "map (lift Q) (take m xs)" and ys = "lift Q (xs ! m) # tl ys" in preserves_p_append)
    apply (rule_tac s = "(map (lift Q) (take m xs) @ [lift Q (xs ! m)]) @ tl ys" in trans)
     apply (metis (no_types, lifting) append_eq_append_conv_if length_map lessI nth_map take_Suc_conv_app_nth take_map)
    apply simp
   apply (simp add: preserves_p_def, clarify)
   apply (erule_tac x = s in allE, drule conjunct2) 
   apply(drule_tac c=xs in subsetD, simp add: assume_p_def gets_p_def cpts_of_p_def)
    apply clarify
    apply(erule_tac x = ia and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE, erule impE)
     apply linarith
    apply (simp add: nth_append, erule impE)
     apply(force elim:petranE intro:EnvP simp add:lift_def)
    apply (simp add: snd_lift)
   apply (case_tac "xs ! i")
   apply (case_tac "fst (xs ! i)")
    apply (erule_tac x = "i" in allE, simp add: nth_append)
    apply (simp add: lift_def getspc_p_def gets_p_def, clarify)
   apply (simp add: getspc_p_def gets_p_def lift_def)
   apply (metis ann_preserves_p.simps(2) fst_conv less_SucI snd_conv)
   apply (case_tac "xs ! m")
  apply (case_tac "fst (xs ! m)")
   prefer 2
   apply (simp add: nth_append lift_def)
  apply (erule_tac x = s in allE, drule conjunct1)
  apply(drule_tac c=xs in subsetD, simp add: assume_p_def gets_p_def cpts_of_p_def)
   apply clarify
   apply(erule_tac x = i and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE, erule impE)
    apply linarith
   apply (simp add: nth_append, erule impE)
    apply(force elim:petranE intro:EnvP simp add:lift_def)
   apply (simp add: snd_lift)
  apply (erule_tac x = b in allE, drule conjunct2)
  apply (drule_tac c = "lift Q (xs ! m) # tl ys" in subsetD)
   apply (simp add: cpts_of_p_def lift_def)
   apply (rule conjI)
    apply (metis Ann_PiCore_Semantics.nth_tl cptn_not_empty)
   apply (simp add: assume_p_def gets_p_def)
   apply (rule conjI)
    apply (simp add: commit_p_def)
    apply (metis Zero_not_Suc diff_Suc_1 fst_conv gets_p_def getspc_p_def last_conv_nth length_0_conv snd_conv)
   apply clarify
   apply(erule_tac x = "i + m" and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE, erule impE)
    apply simp
   apply (case_tac i, simp add: nth_append)
   apply (simp add: nth_append)
  by simp

subsubsection\<open>Soundness of the While rule\<close>

lemma last_append[rule_format]:
  "\<forall>xs. ys\<noteq>[] \<longrightarrow> ((xs@ys)!(length (xs@ys) - (Suc 0)))=(ys!(length ys - (Suc 0)))"
apply(induct ys)
 apply simp
apply clarify
apply (simp add:nth_append)
done

lemma assum_after_body:
  "\<lbrakk> \<Turnstile> P sat\<^sub>p [pre \<inter> b, rely, guar, pre];
  (Some P, s) # xs \<in> cpt_p_mod; fst (last ((Some P, s) # xs)) = None; s \<in> b;
  (Some (AnnWhile r b P), s) # (Some (AnnSeq P (AnnWhile r b P)), s) #
   map (lift (AnnWhile r b P)) xs @ ys \<in> assume_p (pre, rely)\<rbrakk>
  \<Longrightarrow> (Some (AnnWhile r b P), snd (last ((Some P, s) # xs))) # ys \<in> assume_p (pre, rely)"
  apply(simp add:assume_p_def prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod gets_p_def)
  apply clarify
  apply(erule_tac x=s in allE)
  apply clarify
   apply(drule_tac c="(Some P, s) # xs" in subsetD,simp)
   apply clarify
   apply(erule_tac x="Suc i" in allE)
   apply simp
   apply(simp add:Cons_lift_append nth_append snd_lift del:list.map)
   apply(erule mp)
   apply(erule petranE,simp)
   apply(case_tac "fst(((Some P, s) # xs) ! i)")
    apply(force intro:EnvP simp add:lift_def)
   apply(force intro:EnvP simp add:lift_def)
  apply(rule conjI)
   apply clarify
   apply(simp add:commit_p_def last_length)
  apply clarify
  apply(rule conjI)
   apply(simp add:commit_p_def getspc_p_def gets_p_def)
  apply clarify
  apply(erule_tac x="Suc(length xs + i)" in allE,simp)
  apply(case_tac i, simp add:nth_append Cons_lift_append snd_lift last_conv_nth lift_def split_def)
  apply(simp add:Cons_lift_append nth_append snd_lift)
  done

lemma lift_assume : "map (lift P) l \<in> assume_p (pre, rely) \<Longrightarrow> l \<in> cpts_p \<Longrightarrow> l \<in> assume_p (pre, rely)"
  apply (simp add: assume_p_def gets_p_def getspc_p_def)
  apply (rule conjI)
   apply (metis cptn_not_empty length_greater_0_conv nth_map snd_lift)
  apply clarify
  apply(erule_tac x="i" in allE,simp add:snd_lift del:list.map)
  apply(case_tac "fst(l!i)")
  apply (erule mp)
  apply(erule petranE,simp add:lift_def)
   apply (rule EnvP)
  apply(erule petranE,simp add:lift_def)
  by (simp add: petran.intros)


lemma While_sound_aux [rule_format]:
  "\<lbrakk> r \<inter> - b \<subseteq> post; \<Turnstile> P sat\<^sub>p [r \<inter> b, rely, guar, r]; \<forall>s. (s, s) \<in> guar;
   stable r rely;  stable post rely; x \<in> cpt_p_mod \<rbrakk>
  \<Longrightarrow>  \<forall>s xs. x=(Some(AnnWhile r b P),s)#xs \<longrightarrow> x\<in>assume_p(r, rely) \<longrightarrow> x \<in> commit_p (guar, post)"
  apply(erule cpt_p_mod.induct)
          apply safe
      apply (simp_all del:last.simps)
(*5 subgoals left*)
      apply(simp add:commit_p_def getspc_p_def gets_p_def)
(*4 subgoals left*)
     apply(rule etran_in_comm)
     apply(erule mp)
     apply(erule tl_of_assum_in_assum,simp)
(*While-None*)
    apply(simp add:commit_p_def)
    apply(simp add:cpts_iff_cpt_p_mod [THEN sym])
    apply(rule conjI,clarify)
     apply (rule conjI, clarify)
       apply(force simp add:assume_p_def getspc_p_def gets_p_def)
      apply (simp add: ann_preserves_p_def assume_p_def getspc_p_def gets_p_def)
     apply(force simp add:assume_p_def getspc_p_def gets_p_def)
    apply(simp add: getspc_p_def gets_p_def)
    apply clarify
    apply(rule conjI, clarify)
      apply(case_tac i,simp,simp)
     apply(force simp add:not_ctran_None2)
    apply(subgoal_tac "\<forall>i. Suc i < length ((None, sa) # xs) \<longrightarrow> (((None, sa) # xs) ! i, ((None, sa) # xs) ! Suc i)\<in> petran")
     prefer 2
     apply clarify
     apply(rule_tac m="length ((None, sa) # xs)" in etran_or_ctran,simp+)
      apply(erule not_ctran_None2,simp)
     apply simp+
    apply(frule_tac j="0" and k="length ((None, sa) # xs) - 1" and p=post in stability,simp+)
       apply(force simp add:assume_p_def subsetD gets_p_def)
      apply(simp add:assume_p_def)
      apply clarify
      apply(erule_tac x="i" in allE,simp)
      apply (simp add:gets_p_def)
      apply(erule_tac x="Suc i" in allE,simp)
     apply simp
    apply clarify
    apply (simp add:last_length)
(*WhileOne*)
   apply(thin_tac "P = AnnWhile r b P \<longrightarrow> Q" for Q)
   apply(rule ctran_in_comm, simp)
    apply(simp add: assume_p_def gets_p_def)
   apply(simp add:Cons_lift del:list.map)
   apply(simp add:commit_p_def del:list.map)
   apply(rule conjI, clarify)
    apply(case_tac "fst(((Some P, sa) # xs) ! i)")
     apply(case_tac "((Some P, sa) # xs) ! i")
     apply (simp add:lift_def)
     apply(ind_cases "(Some (AnnWhile r b P), ba) -c\<rightarrow> t" for ba t)
      apply (simp add:gets_p_def)
     apply (simp add:gets_p_def)
    apply(simp add:snd_lift gets_p_def del:list.map)
    apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
    apply(erule_tac x=sa in allE)
    apply(drule_tac c="(Some P, sa) # xs" in subsetD)
     apply (simp add:assume_p_def gets_p_def del:list.map)
     apply clarify
     apply(erule_tac x="Suc ia" in allE,simp add:snd_lift del:list.map)
     apply(erule mp)
     apply(case_tac "fst(((Some P, sa) # xs) ! ia)")
      apply(erule petranE,simp add:lift_def)
      apply(rule EnvP)
     apply(erule petranE,simp add:lift_def)
     apply(rule EnvP)
    apply (simp add:commit_p_def getspc_p_def gets_p_def del:list.map)
    apply clarify
    apply(erule allE,erule impE,assumption)
    apply(case_tac "((Some P, sa) # xs) ! i")
    apply(case_tac "xs!i")
    apply(simp add:lift_def)
    apply(case_tac "fst(xs!i)")
     apply force
    apply force
(*last=None*)
   apply(subgoal_tac "(map (lift (AnnWhile r b P)) ((Some P, sa) # xs))\<noteq>[]")
    apply(drule last_conv_nth)
    apply (simp add:getspc_p_def gets_p_def del:list.map)
    apply (metis last.simps last_length last_lift_not_None)
   apply simp
(*WhileMore*)                                                              
  apply(thin_tac "P = AnnWhile r b P \<longrightarrow> Q" for Q)
  apply(rule ctran_in_comm,simp del:last.simps)
(*metiendo la hipotesis antes de dividir la conclusion.*)
   apply(subgoal_tac "(Some (AnnWhile r b P), snd (last ((Some P, sa) # xs))) # ys \<in> assume_p (r, rely)")
    apply (simp del:last.simps)
   apply(erule assum_after_body)
      apply (simp del:last.simps)+
(*lo de antes.*)
  apply(simp add:commit_p_def getspc_p_def gets_p_def del:list.map last.simps)
  apply(rule conjI, clarify)
   apply(simp only:Cons_lift_append)
   apply(case_tac "i<length xs")
    apply(simp add:nth_append del:list.map last.simps)
    apply(case_tac "fst(((Some P, sa) # xs) ! i)")
     apply(case_tac "((Some P, sa) # xs) ! i")
     apply (simp add:lift_def del:last.simps)
     apply(ind_cases "(Some (AnnWhile r b P), ba) -c\<rightarrow> t" for ba t)
      apply simp
     apply simp
    apply(simp add:snd_lift del:list.map last.simps)
    apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
    apply(erule_tac x=sa in allE)
    apply(drule_tac c="(Some P, sa) # xs" in subsetD)
     apply (simp add:assume_p_def getspc_p_def gets_p_def del:list.map last.simps)
     apply clarify
     apply(erule_tac x="Suc ia" in allE,simp add:nth_append snd_lift del:list.map last.simps, erule mp)
     apply(case_tac "fst(((Some P, sa) # xs) ! ia)")
      apply(erule petranE,simp add:lift_def)
      apply(rule EnvP)
     apply(erule petranE,simp add:lift_def)
     apply(rule EnvP)
    apply (simp add:commit_p_def getspc_p_def gets_p_def del:list.map)
    apply clarify
    apply(erule allE,erule impE,assumption)
    apply(case_tac "((Some P, sa) # xs) ! i")
    apply(case_tac "xs!i")
    apply(simp add:lift_def)
    apply(case_tac "fst(xs!i)")
     apply force
    apply force
(*@{text "i \<ge> length xs"}*)
    apply(subgoal_tac "i-length xs <length ys")
     prefer 2
    apply arith
   apply(case_tac "i=length xs")
     apply (simp add:nth_append snd_lift del:list.map last.simps)
     apply(simp add:last_length del:last.simps)
     apply(case_tac "last((Some P, sa) # xs)")
    apply(simp add:lift_def del:last.simps)
    apply auto[1]
(*@{text "i>length xs"}*)
   apply(case_tac "i-length xs")
    apply arith
   apply(simp add:nth_append del:list.map last.simps)
   apply(rotate_tac -3)
   apply(subgoal_tac "i- Suc (length xs)=nat")
    prefer 2
    apply arith
   apply (metis (no_types, lifting) Cons_lift_append List.nth_tl Suc_lessD assum_after_body list.sel(3))
(*last=None*)
  apply clarify
  apply(case_tac ys)
   apply(simp add:Cons_lift del:list.map last.simps)
   apply(subgoal_tac "(map (lift (AnnWhile r b P)) ((Some P, sa) # xs))\<noteq>[]")
    apply(drule last_conv_nth)
    apply (simp del:list.map)
    apply(simp only:last_lift_not_None)
   apply simp
  apply(subgoal_tac "((Some (AnnSeq P (AnnWhile r b P)), sa) # map (lift (AnnWhile r b P)) xs @ ys)\<noteq>[]")
   apply(drule last_conv_nth)
   apply (simp del:list.map last.simps)
   apply(simp add:nth_append del:last.simps)
   apply(rename_tac a list)
   apply(subgoal_tac "((Some (AnnWhile r b P), snd (last ((Some P, sa) # xs))) # a # list)\<noteq>[]")
    apply(drule last_conv_nth)
    apply (metis assum_after_body last_length length_Cons nth_Cons_Suc)
   apply simp
  apply simp
  done

lemma lift_assume_p : "map (lift Q) l \<in> assume_p (r, rely) \<Longrightarrow> l \<in> assume_p (r, rely)"
  apply (simp add: assume_p_def)
  apply (rule conjI)
   apply (metis gets_p_def length_0_conv list.simps(8) neq0_conv nth_map snd_lift)
  apply clarify
  apply (case_tac "l ! i")
  apply (case_tac "a")
   apply (erule_tac x = i in allE)
   apply(erule petranE,simp add:lift_def gets_p_def getspc_p_def)
  apply (simp add: petran.intros)
  apply(erule petranE,simp add:lift_def gets_p_def getspc_p_def)
  using petran.intros by fastforce

lemma While_sound_aux1 [rule_format]:
  "\<lbrakk> r \<inter> - b \<subseteq> post; \<Turnstile> P sat\<^sub>p [r \<inter> b, rely, guar, r]; \<forall>s. (s, s) \<in> guar;
   stable r rely;  stable post rely; x \<in> cpt_p_mod \<rbrakk>
  \<Longrightarrow>  \<forall>s xs. x=(Some(AnnWhile r b P),s)#xs \<longrightarrow> x\<in>assume_p(r, rely) \<longrightarrow> x \<in> preserves_p"
  apply(erule cpt_p_mod.induct)
          apply safe
      apply (simp_all del:last.simps)
(*5 subgoals left*)
      apply(simp add:preserves_p_def assume_p_def getspc_p_def gets_p_def)
(*4 subgoals left*)
  apply (rule_tac xs = "[(Some (AnnWhile r b P), sa)]" and ys = "(Some (AnnWhile r b P), t) # xs"
         in preserves_p_append, simp)
  apply (simp add: assume_p_def preserves_p_def gets_p_def getspc_p_def)
     apply (erule impE, simp add: assume_p_def gets_p_def)
      apply (clarify, rule conjI)
       apply (erule_tac x = "0" in allE, simp add: petran.intros stable_def)
      apply auto[1]
     apply simp
(*While-None*)
    apply (rule_tac xs = "[(Some (AnnWhile r b P), sa)]" and ys = "(None, sa) # xs" in preserves_p_append, simp)
     apply (simp add: preserves_p_def assume_p_def gets_p_def getspc_p_def)
    apply (simp add: preserves_p_def, clarify)
    apply (subgoal_tac "getspc_p (((None, sa) # xs) ! i) = None", simp)
    apply (rule not_ctran_None3', simp_all del: last.simps)
  using cpts_if_cpt_p_mod apply blast
    apply (simp add: getspc_p_def)
(*WhileOne*)
   apply(thin_tac "P = AnnWhile r b P \<longrightarrow> Q" for Q)
   apply(simp add:Cons_lift del:list.map)
  apply (rule_tac xs = "[(Some (AnnWhile r b P), sa)]" and ys = "map (lift (AnnWhile r b P)) ((Some P, sa) # xs)"
          in preserves_p_append, simp)
    apply (simp add: preserves_p_def assume_p_def gets_p_def getspc_p_def)
   apply (subgoal_tac "(Some P, sa) # xs \<in> assume_p (r, rely)")
   apply (simp add: preserves_p_def del: list.map, clarify)
   apply(case_tac "fst(((Some P, sa) # xs) ! i)")
    apply(case_tac "((Some P, sa) # xs) ! i")
    apply (simp add: getspc_p_def lift_def gets_p_def del: list.map)
    apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
    apply (erule_tac x = "sa" in allE, simp del: list.map)
    apply (drule conjunct1)
    apply (drule_tac c = "take (Suc i) ((Some P, sa) # xs)" in subsetD)
      apply (simp add:assume_p_def gets_p_def del:list.map take_Suc_Cons)
  using cpts_if_cpt_p_mod cpts_onlyif_cpt_p_mod takecptn_is_cptn apply blast
     apply clarify
    apply (simp add: commit_p_def del: take_Suc_Cons)
    apply (drule conjunct2)
    apply (erule impE, simp add: getspc_p_def del: take_Suc_Cons)
     apply (metis fst_conv last_snoc length_Cons take_Suc_conv_app_nth)
    apply (simp add: gets_p_def del: take_Suc_Cons)
    apply (metis last_snoc length_Cons snd_conv take_Suc_conv_app_nth)
   apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
   apply (erule_tac x = "sa" in allE, simp del: list.map)
   apply (drule conjunct2)
   apply(drule_tac c="(Some P, sa) # xs" in subsetD)
    apply (simp add:assume_p_def gets_p_def del:list.map)
   apply (simp add: preserves_p_def del: list.map)
   apply (erule_tac x = "i" in allE, simp del: list.map)
   apply(case_tac "((Some P, sa) # xs) ! i")
    apply (simp add: getspc_p_def gets_p_def lift_def del: list.map)
   apply (rule_tac Q = "(AnnWhile r b P)" in lift_assume_p)
   apply (simp add: assume_p_def gets_p_def)
   apply (rule conjI, simp add: lift_def)
   apply clarify
   apply (erule_tac x = "Suc i" in allE, erule impE, simp)
   apply (erule impE, simp, simp)
(*WhileMore*)
  apply(thin_tac "P = AnnWhile r b P \<longrightarrow> Q" for Q)
  apply(subgoal_tac "(Some (AnnWhile r b P), snd (last ((Some P, sa) # xs))) # ys \<in> assume_p (r, rely)")
   apply (simp del:last.simps)
   prefer 2
   apply(erule assum_after_body)
      apply (simp del:last.simps)+
  apply (rule_tac xs = "[(Some (AnnWhile r b P), sa)]" and ys = "(Some (AnnSeq P (AnnWhile r b P)), sa) 
        # map (lift (AnnWhile r b P)) xs @ ys" in preserves_p_append, simp)
   apply (simp add: assume_p_def preserves_p_def gets_p_def getspc_p_def)
  apply (rule_tac xs = "(Some (AnnSeq P (AnnWhile r b P)), sa) # map (lift (AnnWhile r b P)) xs" 
        and ys = " ys" in preserves_p_append, simp)
   apply (simp only: Cons_lift)
   apply (subgoal_tac " map (lift (AnnWhile r b P)) ((Some P, sa) # xs) \<in> assume_p (r, rely)")
    prefer 2
    apply (simp add: assume_p_def gets_p_def getspc_p_def del: last.simps list.map)
    apply (rule conjI, simp add: lift_def)
    apply clarify
    apply (erule_tac x = "Suc i" and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE)
    apply (erule impE)
     apply linarith
    apply (erule impE)
     apply (metis (no_types, lifting) Cons_lift_append length_Cons length_map less_SucI nth_Cons_Suc nth_append nth_map)
    apply (metis (no_types, lifting) Cons_lift_append le_imp_less_Suc length_Cons length_map less_imp_le nth_Cons_Suc nth_append nth_map)
   apply (subgoal_tac "(Some P, sa) # xs \<in> assume_p (r, rely)")
    apply (simp only: preserves_p_def, clarify)
    apply (case_tac "((Some P, sa) # xs) ! i")
    apply (case_tac "a")
     apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
     apply (erule_tac x = "sa" in allE, simp del: list.map)
     apply (drule conjunct1)
     apply (drule_tac c = "take (Suc i) ((Some P, sa) # xs)" in subsetD)
      apply (simp add:assume_p_def gets_p_def del:list.map take_Suc_Cons last.simps)
      apply clarify
      apply (meson cpts_if_cpt_p_mod cpts_onlyif_cpt_p_mod takecptn_is_cptn)
     apply clarify
     apply (simp add: commit_p_def getspc_p_def gets_p_def lift_def del: take_Suc_Cons last.simps)
     apply (drule conjunct2)
     apply (metis (no_types, lifting) fst_conv last_snoc length_Cons snd_conv take_Suc_conv_app_nth)
    apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
    apply (erule_tac x = "sa" in allE, simp del: list.map take_Suc_Cons last.simps)
    apply (drule conjunct2)
    apply (drule_tac c = "(Some P, sa) # xs" in subsetD)
     apply (simp add:assume_p_def gets_p_def del:list.map take_Suc_Cons last.simps)
    apply (simp add: preserves_p_def getspc_p_def gets_p_def lift_def del: list.map take_Suc_Cons last.simps)
    apply (erule_tac x = i in allE, simp add: lift_def del: list.map take_Suc_Cons last.simps)
  using lift_assume_p apply blast
  apply (simp add: preserves_p_def)
  apply clarify
  apply (erule_tac x = "Suc i" in allE, simp)
  done

lemma While_sound:
  "\<lbrakk> pre \<subseteq> r; stable r rely; r \<inter> - b \<subseteq> post; stable post rely;
    \<Turnstile> P sat\<^sub>p [r \<inter> b, rely, guar, r]; \<forall>s. (s,s)\<in>guar\<rbrakk>
  \<Longrightarrow> \<Turnstile> AnnWhile r b P sat\<^sub>p [pre, rely, guar, post]"
  apply(unfold prog_validity_def)
  apply clarify
  apply (rule IntI)
   apply(erule_tac xs="tl x" in While_sound_aux)
         apply(simp add:prog_validity_def)
        apply force
       apply simp_all
     apply(simp add:cpts_iff_cpt_p_mod cpts_of_p_def)
    apply(simp add:cpts_of_p_def)
    apply clarify
    apply(rule nth_equalityI)
     apply simp_all
     apply(case_tac x,simp+)
    apply clarify
    apply(case_tac i,simp+)
    apply(case_tac x,simp+)
   apply (simp add: assume_p_def)
   apply blast
   apply(erule_tac xs="tl x" in While_sound_aux1)
         apply(simp add:prog_validity_def)
        apply force
       apply simp_all
     apply(simp add:cpts_iff_cpt_p_mod cpts_of_p_def)
    apply(simp add:cpts_of_p_def)
    apply clarify
    apply(rule nth_equalityI)
     apply simp_all
     apply(case_tac x,simp+)
    apply clarify
    apply(case_tac i,simp+)
    apply(case_tac x,simp+)
   apply (simp add: assume_p_def)
  apply blast
  done


lemma unique_ctran_Nondt [rule_format]:
  "\<forall>s i. x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnNondt r f), s) \<longrightarrow>
  Suc i<length x \<longrightarrow> x!i -c\<rightarrow> x!Suc i \<longrightarrow>
  (\<forall>j. Suc j<length x \<longrightarrow> i\<noteq>j \<longrightarrow> x!j -pe\<rightarrow> x!Suc j)"
apply(induct x,simp)
apply simp
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp+)
 apply clarify
 apply(case_tac j,simp)
  apply(rule EnvP)
 apply simp
apply clarify
apply simp
apply(case_tac i)
 apply(case_tac j,simp,simp)
 apply(erule ptran.cases,simp_all)
 apply(force elim: not_ctran_None)
apply(ind_cases "((Some (AnnNondt r f), sa), Q, t) \<in> ptran" for sa Q t)
apply simp
apply(drule_tac i=nat in not_ctran_None,simp)
apply(erule petranE,simp)
done

lemma exists_ctran_Nondt_None [rule_format]:
  "\<forall>s i. x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnNondt r f), s)
  \<longrightarrow> i<length x \<longrightarrow> fst(x!i)=None \<longrightarrow> (\<exists>j<i. x!j -c\<rightarrow> x!Suc j)"
apply(induct x,simp)
apply simp
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp,simp)
 apply(erule_tac x=nat in allE,simp)
 apply clarify
 apply(rule_tac x="Suc j" in exI,simp,simp)
apply clarify
apply(case_tac i,simp,simp)
apply(rule_tac x=0 in exI,simp)
done

lemma Nondt_sound:
  "\<lbrakk>pre \<subseteq> r; stable r rely; r \<subseteq> {s. (\<forall>t. (s,t) \<in> f \<longrightarrow> t \<in> post) \<and> (\<exists>t. (s,t) \<in> f)}; 
            {(s,t). s \<in> r \<and> (s,t)\<in>f} \<subseteq> guar;  stable post rely\<rbrakk>
           \<Longrightarrow> \<Turnstile> AnnNondt r f sat\<^sub>p [pre, rely, guar, post]"
  apply (rule Conseq_sound_r, simp_all)
  apply(unfold prog_validity_def)
  apply clarify
  apply (rule IntI)
   apply(simp add:commit_p_def)
   apply(simp add:getspc_p_def gets_p_def)
   apply(rule conjI, clarify)
    apply(simp add:cpts_of_p_def assume_p_def gets_p_def)
    apply clarify
    apply(frule_tac j=0 and k=i and p= r in stability)
          apply simp_all
      apply(erule_tac x=ia in allE,simp)
     apply(erule_tac i=i and r=r in unique_ctran_Nondt,simp_all)
    apply(erule subsetD,simp)
    apply(case_tac "x!i")
    apply clarify
    apply(drule_tac s="Some (AnnNondt r f)" in sym,simp)
    apply(thin_tac "\<forall>j. H j" for H)
    apply(force elim:ptran.cases)
   apply clarify
   apply(simp add:cpts_of_p_def)
   apply clarify
   apply(frule_tac i="length x - 1" and r=r and f = f in exists_ctran_Nondt_None,simp+)
     apply(case_tac x,simp+)
    apply(rule last_fst_esp,simp add:last_length)
    apply (case_tac x,simp+)
   apply(simp add:assume_p_def gets_p_def)
   apply clarify
   apply(frule_tac j=0 and k="j" and p=r in stability)
         apply simp_all
     apply(erule_tac x=i in allE,simp)
    apply(erule_tac i=j and r=r in unique_ctran_Nondt,simp_all)
   apply(case_tac "x!j")
   apply clarify
   apply simp
   apply(drule_tac s="Some (AnnNondt r f)" in sym,simp)
   apply(case_tac "x!Suc j",simp)
   apply(rule ptran.cases,simp)
           apply(simp_all)
   apply(drule_tac c=sa in subsetD,simp)
   apply clarify
   apply(frule_tac j="Suc j" and k="length x - 1" and p=post in stability,simp_all)
     apply(case_tac x,simp+)
    apply(erule_tac x=i in allE)
    apply(erule_tac i=j and r=r in unique_ctran_Nondt, simp_all)
     apply arith+
   apply(case_tac x)
    apply(simp add:last_length)+
  apply (case_tac "\<exists>i. Suc i < length x \<and> (x!i) -c\<rightarrow> (x!(Suc i))")
   apply (simp add: preserves_p_def cpts_of_p_def assume_p_def gets_p_def)
   apply clarify
   apply (case_tac "ia \<le> i")
    apply(frule_tac j=0 and k=ia and p= r in stability, simp_all)
      apply blast
  using unique_ctran_Nondt apply fastforce
    apply (case_tac "x!ia")
    apply (simp add: getspc_p_def, clarsimp)
   apply(frule_tac j=0 and k=i and p= r in stability, simp_all)
     apply blast
    apply(erule_tac i=i and f=f in unique_ctran_Nondt,simp_all)
   apply (case_tac "x ! Suc i")
   apply (erule ptran.cases, simp_all)
   apply (drule_tac i = "Suc i" and j = ia in not_ctran_Finish, simp_all)
   apply (simp add: getspc_p_def)
  apply (simp add: preserves_p_def cpts_of_p_def assume_p_def gets_p_def)
  apply clarify 
  apply(frule_tac j=0 and k=i and p= r in stability, simp_all)
    apply blast
   apply (drule_tac m = "length x" and i = "ia" in etran_or_ctran, simp_all)
  apply (case_tac "x!i")
  apply (simp add: getspc_p_def, clarsimp)
  done


subsubsection \<open>Soundness of the system for programs\<close>

theorem rgsound_p:
  "\<turnstile> P sat\<^sub>p [pre, rely, guar, post] \<Longrightarrow> \<Turnstile> P sat\<^sub>p [pre, rely, guar, post]"
  apply(erule rghoare_p.induct)
        apply(force elim:Basic_sound)
       apply(force elim:Seq_sound)
      apply(force elim:Cond_sound)
     apply(force elim:While_sound)
    apply(force elim:Await_sound)
   apply(force elim:Nondt_sound)
  apply(erule Conseq_sound,simp+)
  done
                                      
subsection \<open>Soundness of Events\<close>

lemma anony_cfgs0 : "\<lbrakk>\<exists>P. getspc_e (es ! 0) = AnonyEvent P; es \<in> cpts_ev\<rbrakk> 
                      \<Longrightarrow> \<forall>i. (i < length es \<longrightarrow> (\<exists>Q. getspc_e (es!i) = AnonyEvent Q) )"
  proof -
    assume a0: "es \<in> cpts_ev" and a1: "\<exists>P. getspc_e (es ! 0) = AnonyEvent P"
    from a0 a1 show "\<forall>i. (i < length es \<longrightarrow> (\<exists>Q. getspc_e (es!i) = AnonyEvent Q) )"
      proof(induct es)
        case (CptsEvOne e s x)
        assume b0: "\<exists>P. getspc_e ([(e, s, x)] ! 0) = AnonyEvent P"
        show ?case using b0 by auto 
      next
        case (CptsEvEnv e' t' x' xs' s' y')
        assume b0: "(e', t', x') # xs' \<in> cpts_ev" and
               b1: "\<exists>P. getspc_e (((e', t', x') # xs') ! 0) = AnonyEvent P \<Longrightarrow>
                    \<forall>i<length ((e', t', x') # xs'). \<exists>Q. getspc_e (((e', t', x') # xs') ! i) = AnonyEvent Q" and
               b2: "\<exists>P. getspc_e (((e', s', y') # (e', t', x') # xs') ! 0) = AnonyEvent P"
        from b2 obtain P1 where b3: "getspc_e (((e', s', y') # (e', t', x') # xs') ! 0) = AnonyEvent P1" by auto
        then have b4: "e' = AnonyEvent P1" by (simp add: getspc_e_def)
        with b1 have "\<forall>i<length ((e', t', x') # xs'). \<exists>Q. getspc_e (((e', t', x') # xs') ! i) = AnonyEvent Q"  
          by (simp add: getspc_e_def)
        with b4 show ?case by (metis (no_types, hide_lams) Ex_list_of_length b3 gr0_conv_Suc 
                        length_Cons length_tl list.sel(3) not_less_eq nth_non_equal_first_eq)
      next
        case (CptsEvComp e1 s1 x1 et e2 t1 y1 xs1)
        assume b0: "(e1, s1, x1) -et-et\<rightarrow> (e2, t1, y1)" and
               b1: "(e2, t1, y1) # xs1 \<in> cpts_ev" and
               b2: "\<exists>P. getspc_e (((e2, t1, y1) # xs1) ! 0) = AnonyEvent P \<Longrightarrow>
                    \<forall>i<length ((e2, t1, y1) # xs1). \<exists>Q. getspc_e (((e2, t1, y1) # xs1) ! i) = AnonyEvent Q" and
               b3: "\<exists>P. getspc_e (((e1, s1, x1) # (e2, t1, y1) # xs1) ! 0) = AnonyEvent P"
        from b3 obtain P1 where b4: "getspc_e (((e1, s1, x1) # (e2, t1, y1) # xs1) ! 0) = AnonyEvent P1" by auto
        then have b5: "e1 = AnonyEvent P1" by (simp add: getspc_e_def)
        with b0 have "\<exists>Q. e2 = AnonyEvent Q"
              apply(clarify)
              apply(rule etran.cases)
              apply(simp_all)+
              done
        then have "\<exists>P. getspc_e (((e2, t1, y1) # xs1) ! 0) = AnonyEvent P" by (simp add:getspc_e_def)
        with b2 have b6: "\<forall>i<length ((e2, t1, y1) # xs1). \<exists>Q. getspc_e (((e2, t1, y1) # xs1) ! i) = AnonyEvent Q" by auto
        with b5 show ?case by (metis (no_types, hide_lams) Ex_list_of_length b3 gr0_conv_Suc 
                        length_Cons length_tl list.sel(3) not_less_eq nth_non_equal_first_eq)
      qed
    qed

lemma anony_cfgs : "es \<in> cpts_of_ev (AnonyEvent P) s x  \<Longrightarrow> \<forall>i. (i < length es \<longrightarrow> (\<exists>Q. getspc_e (es!i) = AnonyEvent Q) )"
  proof -
    assume a0: "es \<in> cpts_of_ev (AnonyEvent P) s x"
    then have a1: "es!0=(AnonyEvent P,(s,x)) \<and> es \<in> cpts_ev" by (simp add:cpts_of_ev_def)
    then have "\<exists>P. getspc_e (es ! 0) = AnonyEvent P" by (simp add:getspc_e_def)
    with a1 show ?thesis using anony_cfgs0 by blast
  qed

lemma AnonyEvt_sound: "\<Turnstile> P sat\<^sub>p [pre, rely, guar, post] \<Longrightarrow> \<Turnstile> AnonyEvent (Some P) sat\<^sub>e [pre, rely, guar, post]"
  proof -
    assume a0: "\<Turnstile> P sat\<^sub>p [pre, rely, guar, post]"
    then have a1: "\<forall>s. cpts_of_p (Some P) s \<inter> assume_p (pre, rely) \<subseteq> commit_p (guar, post) \<inter> preserves_p" 
      unfolding prog_validity_def cpts_of_p_def by simp
    then have "\<forall>s x. (cpts_of_ev (AnonyEvent (Some P)) s x) \<inter> assume_e (pre, rely) 
                      \<subseteq> commit_e (guar, post) \<inter> preserves_e"
      proof -
      {
        fix s x
        have "\<forall>el. el\<in>(cpts_of_ev (AnonyEvent (Some P)) s x) \<inter> assume_e (pre, rely) \<longrightarrow> el\<in> commit_e (guar, post) \<inter> preserves_e"
          proof -
          {
            fix el
            assume b0: "el\<in>(cpts_of_ev (AnonyEvent (Some P)) s x) \<inter> assume_e (pre, rely)"
            then obtain pl where b1: "pl = lower_evts el" by simp
            with b0 have b2: "pl \<in> cpts_of_p (Some P) s" using equiv_lower_evts by auto 
            from b0 have b3: "el!0=(AnonyEvent (Some P),(s,x))" and b4: "el \<in> cpts_ev" 
              by (simp add:cpts_of_ev_def)+
            from b0 have b5: "el \<in> assume_e (pre, rely)" by simp
            have b6: "gets_p (pl!0) \<in> pre" 
              proof -
                from b5 have c0: "gets_e (el!0) \<in> pre" by (simp add:assume_e_def)
                from b2 b3 have c1: "gets_p (pl!0) = gets_e (el!0)" by (simp add:cpts_of_p_def gets_p_def gets_e_def)
                with c0 show ?thesis by simp
              qed

            have b7: "\<forall>i. Suc i<length pl \<longrightarrow> 
               pl!i -pe\<rightarrow> pl!(Suc i) \<longrightarrow> (gets_p (pl!i), gets_p (pl!Suc i)) \<in> rely"
              proof -
              {
                fix i
                assume c0: "Suc i<length pl" and c1: "pl!i -pe\<rightarrow> pl!(Suc i)"
                from b1 c0 have c2: "Suc i < length el" by (simp add:lower_evts_def)
                from c1 have c3: "getspc_p (pl!i) = getspc_p (pl!(Suc i))" using getspc_p_def
                  by (metis fst_conv petranE) 
                from b1 have c4: "lower_anonyevt1 (el!i) = pl!i"
                  by (simp add: Suc_lessD c2 lower_evts_def) 
                from b1 have c5: "lower_anonyevt1 (el!Suc i) = pl!Suc i" 
                  by (simp add: Suc_lessD c2 lower_evts_def) 
                
                from b0 c2 have c7: "\<exists>Q. getspc_e (el!i) = AnonyEvent Q"
                  by (meson Int_iff Suc_lessD anony_cfgs) 
                then obtain Q1 where c71: "getspc_e (el!i) = AnonyEvent Q1" by auto
                from b0 c2 have c8: "\<exists>Q. getspc_e (el ! (Suc i)) = AnonyEvent Q"
                  by (meson Int_iff anony_cfgs)
                then obtain Q2 where c81: "getspc_e (el ! (Suc i)) = AnonyEvent Q2" by auto
                from c4 c71 have c9: "getspc_p (pl ! i) = Q1" 
                        using lower_anonyevt1_def AnonyEv getspc_p_def by (metis fst_conv) 
                from c5 c81 have c10: "getspc_p (pl ! (Suc i)) = Q2" 
                        using lower_anonyevt1_def AnonyEv getspc_p_def by (metis fst_conv) 
                with c3 c9 have c11: "Q1 = Q2" by simp
                
                from c4 c71 have c61: "gets_p (pl!i) = gets_e (el!i)" 
                  using lower_anonyevt1_def AnonyEv gets_p_def by (metis snd_conv)

                from c5 c81 have c62: "gets_p (pl! (Suc i)) = gets_e (el! (Suc i))" 
                  using lower_anonyevt1_def AnonyEv gets_p_def by (metis snd_conv)

                from c71 c81 c11 have c12: "getspc_e (el!i) = getspc_e (el!(Suc i))" by simp
                then have c13: "el!i -ee\<rightarrow> el!(Suc i)" using eetran.EnvE getspc_e_def
                  by (metis prod.collapse) 
                from b5 c2 have "(\<forall>i. Suc i < length el \<longrightarrow> el ! i -ee\<rightarrow> el ! Suc i 
                      \<longrightarrow> (gets_e (el ! i), gets_e (el ! Suc i)) \<in> rely)" by (simp add:assume_e_def)
                with c2 c13 have "(gets_e (el!i), gets_e (el!Suc i)) \<in> rely" by auto

                with c61 c62 have "(gets_p (pl!i), gets_p (pl!Suc i)) \<in> rely" by simp
              }
              then show ?thesis by auto
              qed

            with b6 have b8: "pl \<in> assume_p (pre, rely)" by (simp add:assume_p_def)

            with a1 b2 have b9: "pl \<in> commit_p (guar, post) \<inter> preserves_p" by auto
            then have b10: "(\<forall>i. Suc i<length el \<longrightarrow> 
               (\<exists>t. el!i -et-t\<rightarrow> el!(Suc i)) \<longrightarrow> (gets_e (el!i), gets_e (el!Suc i)) \<in> guar)"
               proof -
               {
                 fix i
                 assume c0: "Suc i<length el"
                 assume c1: "\<exists>t. el!i -et-t\<rightarrow> el!(Suc i)"
                 from b1 c0 have c2: "Suc i < length pl" by (simp add:lower_evts_def)
                 
                 from b1 have c3: "lower_anonyevt1 (el!i) = pl!i"
                  by (simp add: Suc_lessD c0 lower_evts_def) 
                from b1 have c4: "lower_anonyevt1 (el!Suc i) = pl!Suc i" 
                  by (simp add: Suc_lessD c0 lower_evts_def) 
                from b0 c0 have c7: "\<exists>Q. getspc_e (el!i) = AnonyEvent Q"
                  by (meson Int_iff Suc_lessD anony_cfgs) 
                 then obtain Q1 where c71: "getspc_e (el!i) = AnonyEvent Q1" by auto
                 from b0 c0 have c8: "\<exists>Q. getspc_e (el ! (Suc i)) = AnonyEvent Q"
                  by (meson Int_iff anony_cfgs)
                 then obtain Q2 where c81: "getspc_e (el! (Suc i)) = AnonyEvent Q2" by auto

                 have c5: "pl!i -c\<rightarrow> pl!(Suc i)"
                  proof -
                    from c1 obtain t where d0: "el!i -et-t\<rightarrow> el!(Suc i)" by auto
                    obtain s1 and x1 where d1: "s1 = gets_e (el ! i) \<and> x1 = getx_e (el ! i)" by simp
                    obtain s2 and x2 where d2: "s2 = gets_e (el ! (Suc i)) \<and> x2 = getx_e (el ! (Suc i))" by simp
                    with d1 c71 c81 have d21: "el ! i = (AnonyEvent Q1, s1, x1) 
                                           \<and> el ! (Suc i) = (AnonyEvent Q2, s2, x2)" 
                         using gets_e_def getx_e_def getspc_e_def by (metis prod.collapse) 
                    with d0 have d3: "(AnonyEvent Q1, s1, x1) -et-t\<rightarrow> (AnonyEvent Q2, s2, x2)" by simp
                    then have "\<exists>k. t = ((Cmd Q1)\<sharp>k)"
                      apply(rule etran.cases)
                      apply simp_all
                      by auto
                    then obtain k where "t = ((Cmd Q1)\<sharp>k)" by auto
                    with d3 have d4: "(Q1,s1) -c\<rightarrow> (Q2, s2)" 
                      apply(clarify)
                      apply(rule etran.cases)
                      apply simp_all+
                      done
                    from c3 d21 have d5: "pl!i = (Q1,s1)" by (simp add:lower_anonyevt1_def getspc_e_def gets_e_def)
                    from c4 d21 have d6: "pl! (Suc i) = (Q2,s2)" by (simp add:lower_anonyevt1_def getspc_e_def gets_e_def)
                    with d4 d5 show ?thesis by simp 
                  qed
                 with b9 c2 have c6: "(gets_p (pl!i), gets_p (pl!Suc i)) \<in> guar" by (simp add:commit_p_def)

                 
                 from c3 c71 have c9: "gets_e (el!i) = gets_p (pl!i)" using lower_anonyevt_s by fastforce
                 from c4 c81 have c10: "gets_e (el!Suc i) = gets_p (pl!Suc i)" using lower_anonyevt_s by fastforce
                 from c6 c9 c10 have  "(gets_e (el!i), gets_e (el!Suc i)) \<in> guar" by simp
               }
               then show ?thesis by auto
               qed

            have b11: "(getspc_e (last el) = AnonyEvent (None) \<longrightarrow> gets_e (last el) \<in> post)"
              proof 
                assume c0: "getspc_e (last el) = AnonyEvent (None)"
                from b1 have c1: "last pl = lower_anonyevt1 (last el)"
                  by (metis (no_types, lifting) CollectD b2 cptn_not_empty cpts_of_p_def 
                      last_map length_greater_0_conv length_map lower_evts_def) 
                from b9 have c2: "getspc_p (last pl) = None \<longrightarrow> gets_p (last pl) \<in> post" by (simp add:commit_p_def)
                from c0 c1 have c3: "getspc_p (last pl) = None" 
                  by (simp add: getspc_p_def lower_anonyevt1_def)
                with c2 have c4: "gets_p (last pl) \<in> post" by auto
                from c0 c1 have "gets_p (last pl) = gets_e (last el)" 
                  by (simp add: getspc_p_def lower_anonyevt1_def gets_p_def)
                with c4 show "gets_e (last el) \<in> post" by simp
              qed

              have b12: " \<forall>i<length el. ann_preserves_e (getspc_e (el ! i)) (gets_e (el ! i))"
              proof-
                {
                fix i
                assume e0: "i < length el"
                with b1 have e1: "i < length pl" by (simp add:lower_evts_def)

                from b1 have e2: "lower_anonyevt1 (el!i) = pl!i"
                  by (simp add: Suc_lessD e0 lower_evts_def)
                from b0 e0 have "\<exists>Q s x. el!i = (AnonyEvent Q, s, x)"
                  by (metis Int_iff anony_cfgs getspc_e_def prod.collapse)
                then obtain Q s x where e3 : "el!i = (AnonyEvent Q, s, x)"  by auto
                then have e4: "pl!i = (Q, s)" 
                  by (metis e2 gets_e_def getspc_e_def lower_anonyevt0.simps(1) lower_anonyevt1_def prod.sel(1) prod.sel(2))
                with b9 have "ann_preserves_p Q s" 
                  apply (simp add: preserves_p_def)
                  by (metis e1 fst_conv gets_p_def getspc_p_def snd_conv)
                with e3 have "ann_preserves_e (getspc_e (el ! i)) (gets_e (el ! i))"
                  by (simp add: getspc_e_def gets_e_def)
              }
              then show ?thesis by auto
              qed

              with b10 b11 have "el \<in> commit_e (guar, post) \<inter> preserves_e" 
                by (simp add: commit_e_def preserves_e_def)
          }
          then show ?thesis by auto
          qed

        then have "(cpts_of_ev (AnonyEvent (Some P)) s x) \<inter> assume_e (pre, rely) \<subseteq> commit_e (guar, post) \<inter> preserves_e" by auto
      }
      then show ?thesis by auto
      qed
    then show ?thesis by (simp add: evt_validity_def) 
  qed

lemma BasicEvt_sound: 
    "\<lbrakk> \<Turnstile> (body ev) sat\<^sub>p [pre \<inter> (guard ev), rely, guar, post]; 
        stable pre rely; \<forall>s. (s, s)\<in>guar\<rbrakk> 
     \<Longrightarrow> \<Turnstile> ((BasicEvent ev)::('l,'k,'s) event) sat\<^sub>e [pre, rely, guar, post]"
  proof -
    assume p0: "\<Turnstile> (body ev) sat\<^sub>p [pre \<inter> (guard ev), rely, guar, post]"
    assume p1: "\<forall>s. (s, s)\<in>guar"
    assume p2: "stable pre rely"
    have "\<forall>s x. (cpts_of_ev ((BasicEvent ev)::('l,'k,'s) event) s x) \<inter> assume_e (pre, rely) 
                      \<subseteq> commit_e (guar, post) \<inter> preserves_e"
      proof -
      {
        fix s x
        have "\<forall>el. el\<in>(cpts_of_ev (BasicEvent ev) s x) \<inter> assume_e (pre, rely) \<longrightarrow> el\<in> commit_e (guar, post) \<inter> preserves_e"
          proof -
          {
            fix el
            assume b0: "el\<in>(cpts_of_ev (BasicEvent ev) s x) \<inter> assume_e (pre, rely)"
            then have b0_1: "el\<in>(cpts_of_ev (BasicEvent ev) s x)" and
                      b0_2: "el \<in> assume_e (pre, rely)" by auto
            from b0_1 have b1: "el ! 0 = (BasicEvent ev, (s, x))" and
                           b2: "el \<in> cpts_ev" by (simp add:cpts_of_ev_def)+
            from b0_2 have b3: "gets_e (el!0) \<in> pre" and
                           b4: "(\<forall>i. Suc i<length el \<longrightarrow> el!i -ee\<rightarrow> el!(Suc i) \<longrightarrow> 
                                (gets_e (el!i), gets_e (el!Suc i)) \<in> rely)" by (simp add: assume_e_def)+
            have "el\<in> commit_e (guar, post) \<inter> preserves_e"
              proof(cases "\<exists>i k. Suc i < length el \<and> el ! i -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc i)")
                assume c0: "\<exists>i k. Suc i < length el \<and> el ! i -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc i)"
                then obtain m and k where c1: "Suc m < length el \<and> el ! m -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc m)"
                  by auto
                with b1 b2 have c2: "\<forall>j. Suc j \<le> m \<longrightarrow> getspc_e (el ! j) = BasicEvent ev \<and> el ! j -ee\<rightarrow> el ! (Suc j)"
                  by (meson evtent_in_cpts1) 
                from b1 b2 c1 have c4: "gets_e (el ! m) \<in> guard ev" and
                        c6: "drop (Suc m) el \<in> cpts_of_ev (AnonyEvent (Some (body ev))) (gets_e (el ! (Suc m))) ((getx_e (el ! m)) (k := BasicEvent ev))" 
                        using evtent_in_cpts2[of el ev s x m k] by auto
                
                from p0[rule_format] c4 have c7: "\<Turnstile> ((AnonyEvent (Some (body ev)))::('l,'k,'s) event) 
                                sat\<^sub>e [pre \<inter> (guard ev), rely, guar, post]"
                  by (simp add: AnonyEvt_sound) 

                from b4 c1 c2 have c8:"\<forall>j. Suc j \<le> m \<longrightarrow> (gets_e (el ! j), gets_e (el ! (Suc j))) \<in> rely" by auto
                with p2 b3 have c9: "\<forall>j. j \<le> m \<longrightarrow> gets_e (el ! j) \<in> pre" 
                  proof -
                  {
                    fix j
                    assume d0: "j \<le> m"
                    then have "gets_e (el ! j) \<in> pre"
                      proof(induct j)
                        case 0 show ?case by (simp add: b3)
                      next
                        case (Suc jj)
                        assume e0: "Suc jj \<le> m"
                        assume e1: "jj \<le> m \<Longrightarrow> gets_e (el ! jj) \<in> pre"
                        from e0 c8 have "(gets_e (el ! jj), gets_e (el ! (Suc jj))) \<in> rely" by auto
                        with p2 e0 e1 show ?case by (meson Suc_leD stable_def)
                      qed
                  }
                  then show ?thesis by auto
                qed

                from c1 have c10: "gets_e (el ! m) = gets_e (el ! (Suc m))" by (meson ent_spec2)
                with c9 have c11: "gets_e (el ! (Suc m)) \<in> pre" by auto
                from c7 have c12: "\<forall>s x. (cpts_of_ev ((AnonyEvent (Some (body ev)))::('l,'k,'s) event) s x) \<inter> 
                    assume_e(pre \<inter> (guard ev), rely) \<subseteq> commit_e(guar, post)" by (simp add:evt_validity_def)
                

                have "drop (Suc m) el \<in> assume_e(pre \<inter> (guard ev), rely)"
                  proof -
                    from c11 have d1: "gets_e (drop (Suc m) el ! 0) \<in> pre" using c1 by auto 
                    from c4 c10 have d2: "gets_e (drop (Suc m) el ! 0) \<in> guard ev"
                      using c1 by auto 
                    from b4 have d3: "\<forall>i. Suc i < length el - Suc m \<longrightarrow>
                             el ! Suc (m + i) -ee\<rightarrow> el ! Suc (Suc (m + i)) \<longrightarrow> 
                             (gets_e (el ! Suc (m + i)), gets_e (el ! Suc (Suc (m + i)))) \<in> rely"
                        by simp
                    with d1 d2 show ?thesis by (simp add:assume_e_def)
                  qed

                with c6 c12 have c13: "drop (Suc m) el \<in> commit_e(guar, post) \<inter> preserves_e" 
                  by (meson AnonyEvt_sound IntI contra_subsetD evt_validity_def p0)
               

                have c14: "\<forall>i. Suc i < length el \<longrightarrow> (\<exists>t. el ! i -et-t\<rightarrow> el ! Suc i) 
                    \<longrightarrow> (gets_e (el ! i), gets_e (el ! Suc i)) \<in> guar"
                  proof -
                  {
                    fix i 
                    assume d0: "Suc i < length el" and
                           d1: "(\<exists>t. el ! i -et-t\<rightarrow> el ! Suc i)"
                    then have "(gets_e (el ! i), gets_e (el ! Suc i)) \<in> guar"
                      proof(cases "Suc i \<le> m")
                        assume e0: "Suc i \<le> m"
                        with c2 have "el ! i -ee\<rightarrow> el ! (Suc i)" by auto
                        then have "\<not>(\<exists>t. el ! i -et-t\<rightarrow> el ! Suc i)"
                          by (metis eetranE evt_not_eq_in_tran prod.collapse) 
                        with d1 show ?thesis by simp
                      next
                        assume e0: "\<not> Suc i \<le> m"
                        then have e1: "Suc i > m" by auto
                        show ?thesis
                          proof(cases "Suc i = m + 1")
                            assume f0: "Suc i = m + 1"
                            then have f1: "i = m" by auto
                            with c1 have "el ! i -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc i)" by simp
                            then have "gets_e (el ! i) = gets_e (el ! (Suc i))" by (meson ent_spec2)
                            with p1 show ?thesis by auto
                          next
                            assume f0: "\<not> Suc i = m + 1"
                            with e1 have f1: "Suc i > Suc m" by auto
                            from c13 have f2: "\<forall>i. Suc i < length (drop (Suc m) el) \<longrightarrow> 
                                    (\<exists>t. (drop (Suc m) el) ! i -et-t\<rightarrow> (drop (Suc m) el) ! Suc i) \<longrightarrow> 
                                    (gets_e ((drop (Suc m) el) ! i), gets_e ((drop (Suc m) el) ! Suc i)) \<in> guar"
                                    by (simp add:commit_e_def)
                            with d0 d1 f1 have "(gets_e (drop (Suc m) el ! (i - Suc m)), gets_e (drop (Suc m) el ! Suc (i - Suc m))) \<in> guar"
                              proof -
                                from d0 f1 have g0: "Suc (i - Suc m) < length (drop (Suc m) el)" by auto
                                from d1 f1 have "(\<exists>t. drop (Suc m) el ! (i - Suc m) -et-t\<rightarrow> drop (Suc m) el ! Suc (i - Suc m))"
                                  using d0 by auto
                                with g0 f2 show ?thesis by simp
                              qed
                              then show ?thesis
                                by (smt Suc_diff_Suc Suc_less_SucD add_Suc 
                                   add_diff_cancel_left' c1 e1 f1 less_imp_Suc_add 
                                   less_imp_le_nat nth_drop)
                          qed
                      qed
                   }
                  then show ?thesis by auto
                  qed


                from c13 have c15: " getspc_e (last el) = AnonyEvent None \<longrightarrow> gets_e (last el) \<in> post"
                  proof -
                    from c1 have "last (drop (Suc m) el) = last el" by simp
                    with c13 show ?thesis by (simp add:commit_e_def)
                  qed

                  have c16: "\<forall>i<length el. ann_preserves_e (getspc_e (el ! i)) (gets_e (el ! i))"
                  proof-
                    {
                      fix i
                      assume d0: "i < length el"
                      then have "ann_preserves_e (getspc_e (el ! i)) (gets_e (el ! i))"
                      proof(cases "i \<le> m")
                        assume e0: "i \<le> m"
                        with c2 have "getspc_e (el ! i) = BasicEvent ev"
                          by (metis Suc_leI c1 ent_spec le_neq_implies_less)
                        then show ?thesis by (simp add: ann_preserves_e_def)
                      next
                        assume f0: "\<not> i \<le> m"
                        then have "i > m" by auto
                        then have f1 : "el ! i = (drop (Suc m) el) ! (i - Suc m)"
                          using c1 by auto
                        from d0 f0 have f2 : "i - Suc m < length (drop (Suc m) el)"
                          by (simp add: Suc_leI \<open>m < i\<close> diff_less_mono)
                        from c13 have "drop (Suc m) el \<in> preserves_e" by auto
                        with f2 have "ann_preserves_e (getspc_e ((drop (Suc m) el) ! (i - Suc m))) 
                                      (gets_e ((drop (Suc m) el) ! (i - Suc m)))"
                          by (simp add: preserves_e_def)
                        with f1 show ?thesis by auto
                      qed
                      }
                      then show ?thesis by auto
                    qed
                    with c14 c15 show ?thesis by (simp add:commit_e_def preserves_e_def)


                  next
                    assume c0: "\<not> (\<exists>i k. Suc i < length el \<and> el ! i -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc i) )"
                    with b1 b2 have c1: "\<forall>j. Suc j < length el \<longrightarrow> getspc_e (el ! j) = BasicEvent ev 
                                        \<and> el ! j -ee\<rightarrow> el ! (Suc j)
                                        \<and> getspc_e (el ! (Suc j)) = BasicEvent ev"
                      using no_evtent_in_cpts by simp
                    then have c2: "(\<forall>i. Suc i<length el \<longrightarrow> (\<exists>t. el!i -et-t\<rightarrow> el!(Suc i)) 
                                   \<longrightarrow> (gets_e (el!i), gets_e (el!Suc i)) \<in> guar)"
                    proof -
                      {
                        fix i
                        assume "Suc i<length el"
                      and  d0: "\<exists>t. el!i -et-t\<rightarrow> el!(Suc i)"
                        with c1 have "el ! i -ee\<rightarrow> el ! Suc i" by auto
                        then have "\<not> (\<exists>t. el!i -et-t\<rightarrow> el!(Suc i))"
                          by (metis eetranE evt_not_eq_in_tran2 prod.collapse) 
                        with d0 have False by simp
                      }
                      then show ?thesis by auto
                    qed
                    from b1 b2 have "el \<noteq> []" using cpts_e_not_empty by auto
                    with b1 b2 obtain els where "el = (BasicEvent ev, s, x) # els"
                      by (metis hd_Cons_tl hd_conv_nth) 
                    then have "getspc_e (last el) = BasicEvent ev"
                    proof(induct els)
                      case Nil
                      assume "el = [(BasicEvent ev, s, x)]"
                      then have "last el = (BasicEvent ev, s, x)" by simp
                      then show ?case by (simp add:getspc_e_def)
                    next
                      case (Cons els1 elsr)
                      assume d0: "el = (BasicEvent ev, s, x) # els1 # elsr"
                      then have d1: "length el > 1" by simp
                      with d0 obtain mm where d2: "Suc mm = length el" by simp
                      with d1 obtain jj where d3: "Suc jj = mm" using d0 by auto 
                      with d2 have d4: "last el = el ! mm" by (metis last.simps last_length nth_Cons_Suc) 
                      with c1 have "getspc_e (el ! (Suc jj)) = BasicEvent ev" using d2 d3 by auto 
                      with d3 d4 show ?case by simp
                    qed

                    then have c3: "getspc_e (last el) = AnonyEvent (None) \<longrightarrow> gets_e (last el) \<in> post" by simp

                    from c1 have c4: "\<forall>i<length el. ann_preserves_e (getspc_e (el ! i)) (gets_e (el ! i))"
                    proof-
                      {
                        fix i
                        assume "i < length el"
                        then have "getspc_e (el ! i ) = BasicEvent ev"
                          by (metis Suc_lessI \<open>el \<noteq> []\<close> \<open>getspc_e (last el) = BasicEvent ev\<close> c1 diff_Suc_1 last_conv_nth)
                        then have "ann_preserves_e (getspc_e (el ! i)) (gets_e (el ! i))"
                          by (simp add: ann_preserves_e_def)
                      }
                      then show ?thesis by auto
                    qed

                with c2 c3 show ?thesis by (simp add:commit_e_def preserves_e_def)
              qed
          }
          then show ?thesis by auto
          qed
      }
      then show ?thesis by auto
      qed
    then show ?thesis by (simp add: evt_validity_def) 
  qed


lemma ev_seq_sound: 
      "\<lbrakk>pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
        \<Turnstile> ev sat\<^sub>e [pre', rely', guar', post']\<rbrakk> 
    \<Longrightarrow> \<Turnstile> ev sat\<^sub>e [pre, rely, guar, post]"
  proof -
    assume p0: "pre \<subseteq> pre'"
      and  p1: "rely \<subseteq> rely'"
      and  p2: "guar' \<subseteq> guar"
      and  p3: "post' \<subseteq> post"
      and  p4: "\<Turnstile> ev sat\<^sub>e [pre', rely', guar', post']"
    from p4 have p5: "\<forall>s x. (cpts_of_ev ev s x) \<inter> assume_e(pre', rely') \<subseteq> commit_e(guar', post') \<inter> preserves_e"
      by (simp add: evt_validity_def)
    have "\<forall>s x. (cpts_of_ev ev s x) \<inter> assume_e(pre, rely) \<subseteq> commit_e(guar, post) \<inter> preserves_e"
      proof -
      {
        fix c s x
        assume a0: "c\<in>(cpts_of_ev ev s x) \<inter> assume_e(pre, rely)"
        then have "c\<in>(cpts_of_ev ev s x) \<and> c\<in>assume_e(pre, rely)" by simp
        with p0 p1 have "c\<in>(cpts_of_ev ev s x) \<and> c\<in>assume_e(pre', rely')"
          using assume_e_imp[of pre pre' rely rely' c] by simp
        with p5 have "c\<in>commit_e(guar', post') \<inter> preserves_e" by auto
        with p2 p3 have "c\<in>commit_e(guar, post) \<inter> preserves_e" 
          using commit_e_imp[of guar' guar post' post c] by simp
      }
      then show ?thesis by auto
      qed
    then show ?thesis by (simp add:evt_validity_def)
  qed

theorem rgsound_e:
  "\<turnstile> Evt sat\<^sub>e [pre, rely, guar, post] \<Longrightarrow> \<Turnstile> Evt sat\<^sub>e [pre, rely, guar, post]"
  apply(erule rghoare_e.induct)
    apply (simp add: AnonyEvt_sound rgsound_p)
   apply (meson BasicEvt_sound rgsound_p)
  apply (simp add: ev_seq_sound rgsound_p)
  done



subsection \<open>Soundness of Event Systems\<close>

lemma evtseq_nfin_samelower: "\<lbrakk>esl \<in> cpts_of_es (EvtSeq e es) s x; \<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> es\<rbrakk> 
        \<Longrightarrow> (\<exists>el. (el \<in> cpts_of_ev e s x \<and> length esl = length el \<and> e_eqv_einevtseq esl el es))"
  proof -
    assume p0: "esl \<in> cpts_of_es (EvtSeq e es) s x"
      and  p1: "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> es"
    from p0 have p01: "esl ! 0 = (EvtSeq e es, s, x) \<and> esl \<in> cpts_es" by (simp add: cpts_of_es_def) 
    then have p01_1: "esl ! 0 = (EvtSeq e es, s, x)" by simp
    then have p2: "\<exists>e. getspc_es (esl ! 0) = EvtSeq e es" by (simp add:getspc_es_def)
    from p01 have p01_2: "esl \<in> cpts_es" by simp
    let ?el = "rm_evtsys esl"
    have a1: "length esl = length ?el" by (simp add: rm_evtsys_def) 
    moreover have "?el \<in> cpts_of_ev e s x"
      proof -
        from p01_2 p1 p2 have b1: "?el \<in> cpts_ev"
          proof(induct esl)
            case (CptsEsOne es1 s1 x1)
            assume c0: "\<exists>e. getspc_es ([(es1, s1, x1)] ! 0) = EvtSeq e es"
            then obtain e1 where c1: "getspc_es ([(es1, s1, x1)] ! 0) = EvtSeq e1 es" by auto
            then have "es1 = EvtSeq e1 es" by (simp add:getspc_es_def)
            then have "rm_evtsys1 (es1, s1, x1) = (e1, s1, x1)" 
              by (simp add: gets_es_def getspc_es_def rm_evtsys1_def getx_es_def) 
            then have "rm_evtsys [(es1, s1, x1)] = [(e1, s1, x1)]" by (simp add:rm_evtsys_def)
            then show ?case by (simp add: cpts_ev.CptsEvOne) 
          next
            case (CptsEsEnv es1 t1 x1 xs1 s1 y1)
            assume c0: "(es1, t1, x1) # xs1 \<in> cpts_es"
              and  c1: "\<forall>i. Suc i \<le> length ((es1, t1, x1) # xs1) \<longrightarrow> getspc_es (((es1, t1, x1) # xs1) ! i) \<noteq> es
                            \<Longrightarrow>\<exists>e. getspc_es (((es1, t1, x1) # xs1) ! 0) = EvtSeq e es 
                            \<Longrightarrow> rm_evtsys ((es1, t1, x1) # xs1) \<in> cpts_ev"
              and  c11: "\<forall>i. Suc i \<le> length ((es1, s1, y1) # (es1, t1, x1) # xs1) 
                                  \<longrightarrow> getspc_es (((es1, s1, y1) # (es1, t1, x1) # xs1) ! i) \<noteq> es"
              and  c2: "\<exists>e. getspc_es (((es1, s1, y1) # (es1, t1, x1) # xs1) ! 0) = EvtSeq e es"
              from c2 obtain e1 where c3: "getspc_es (((es1, s1, y1) # (es1, t1, x1) # xs1) ! 0) = EvtSeq e1 es" by auto
              then have c4: "es1 = EvtSeq e1 es" by (simp add:getspc_es_def)
              from c11 have "\<forall>i. Suc i \<le> length ((es1, t1, x1) # xs1) \<longrightarrow> getspc_es (((es1, t1, x1) # xs1) ! i) \<noteq> es"
                by auto
              with c1 c4 have c5: "rm_evtsys ((es1, t1, x1) # xs1) \<in> cpts_ev"  by (simp add:getspc_es_def)
              have c6: "rm_evtsys ((es1, t1, x1) # xs1) = (rm_evtsys1 (es1, t1, x1)) # (rm_evtsys xs1)"
                by (simp add: rm_evtsys_def) 
              have c7: "rm_evtsys ((es1, s1, y1) # (es1, t1, x1) # xs1) = 
                  (rm_evtsys1 (es1, s1, y1)) # (rm_evtsys1 (es1, t1, x1)) # (rm_evtsys xs1)" 
                  by (simp add: rm_evtsys_def) 
              from c4 have c8: "rm_evtsys1 (es1, s1, y1) = (e1, s1, y1)" 
                by (simp add: gets_es_def getspc_es_def rm_evtsys1_def getx_es_def)
              from c4 have c9: "rm_evtsys1 (es1, t1, x1) = (e1, t1, x1)" 
                by (simp add: gets_es_def getspc_es_def rm_evtsys1_def getx_es_def)
              have c10: "rm_evtsys ((es1, s1, y1) # (es1, t1, x1) # xs1) = (e1, s1, y1) # (e1, t1, x1) # rm_evtsys xs1"
                by (simp add: c7 c8 c9)
              have "rm_evtsys ((es1, t1, x1) # xs1) = (e1, t1, x1) # rm_evtsys xs1"
                by (simp add: c6 c9) 
              with c5 c10 show ?case by (simp add: cpts_ev.CptsEvEnv) 
          next
            case (CptsEsComp es1 s1 x1 et es2 t1 y1 xs1)
            assume c0: "(es1, s1, x1) -es-et\<rightarrow> (es2, t1, y1)"
              and  c1: "(es2, t1, y1) # xs1 \<in> cpts_es"
              and  c2: "\<forall>i. Suc i \<le> length ((es2, t1, y1) # xs1) \<longrightarrow> getspc_es (((es2, t1, y1) # xs1) ! i) \<noteq> es
                            \<Longrightarrow> \<exists>e. getspc_es (((es2, t1, y1) # xs1) ! 0) = EvtSeq e es 
                            \<Longrightarrow> rm_evtsys ((es2, t1, y1) # xs1) \<in> cpts_ev"
              and  c3: "\<forall>i. Suc i \<le> length ((es1, s1, x1) # (es2, t1, y1) # xs1)
                              \<longrightarrow> getspc_es (((es1, s1, x1) # (es2, t1, y1) # xs1) ! i) \<noteq> es"
              and  c4: "\<exists>e. getspc_es (((es1, s1, x1) # (es2, t1, y1) # xs1) ! 0) = EvtSeq e es"
              from c4 obtain e1 where c41: "getspc_es (((es1, s1, x1) # (es2, t1, y1) # xs1) ! 0) = EvtSeq e1 es"
                by auto
              then have c5: "es1 = EvtSeq e1 es" by (simp add:getspc_es_def)
              from c3 have "getspc_es (es2, t1, y1) \<noteq> es" by auto 
              then have c6: "es2 \<noteq> es" by (simp add:getspc_es_def)
              
              with c0 c5 have "\<exists>e2. es2 = EvtSeq e2 es" by (meson evtseq_tran_evtsys) 
              then obtain e2 where c7: "es2 = EvtSeq e2 es" by auto
              with c0 c5 have "\<exists>t. (e1,s1,x1) -et-t\<rightarrow> (e2,t1,y1)" by (simp add: evtseq_tran_exist_etran)
              then obtain t where c71: "(e1,s1,x1) -et-t\<rightarrow> (e2,t1,y1)" by auto
              have c8: "rm_evtsys ((es1, s1, x1) # (es2, t1, y1) # xs1) = 
                  (rm_evtsys1 (es1, s1, x1)) # (rm_evtsys1 (es2, t1, y1)) # (rm_evtsys xs1)" 
                  by (simp add: rm_evtsys_def) 
              have c9: "rm_evtsys ((es2, t1, y1) # xs1) = rm_evtsys1 (es2, t1, y1) # (rm_evtsys xs1)" 
                  by (simp add: rm_evtsys_def) 

              from c3 have c10: "\<forall>i. Suc i \<le> length ((es2, t1, y1) # xs1) \<longrightarrow> getspc_es (((es2, t1, y1) # xs1) ! i) \<noteq> es"
                by auto
              from c7 have "\<exists>e. getspc_es (((es2, t1, y1) # xs1) ! 0) = EvtSeq e es" 
                by (simp add:getspc_es_def)
              with c2 c10 have c11: "rm_evtsys ((es2, t1, y1) # xs1) \<in> cpts_ev" by auto
              from c5 have c12: "rm_evtsys1 (es1, s1, x1) = (e1, s1, x1)" 
                by (simp add: gets_es_def getspc_es_def rm_evtsys1_def getx_es_def)
              from c7 have c13: "rm_evtsys1 (es2, t1, y1) = (e2, t1, y1)" 
                by (simp add: gets_es_def getspc_es_def rm_evtsys1_def getx_es_def)
              with c71 c8 c9 c11 c12 show ?case using cpts_ev.CptsEvComp by fastforce 
          qed
        moreover have "?el ! 0=(e,(s,x))"
          proof -
            from p01 have "rm_evtsys1 (esl ! 0) = (e, s, x)" 
              by (simp add: gets_es_def getspc_es_def getx_es_def rm_evtsys1_def) 
            moreover from a1 b1 have "?el ! 0 = rm_evtsys1 (esl ! 0)" using rm_evtsys_def
              by (metis cpts_e_not_empty length_greater_0_conv nth_map) 
            ultimately show ?thesis by simp
          qed
        ultimately have "?el ! 0=(e,(s,x)) \<and> ?el \<in> cpts_ev" by auto
        then show ?thesis by (simp add: cpts_of_ev_def) 
      qed
    moreover from p01_2 p1 p2 have "e_eqv_einevtseq esl ?el es"
      proof(induct esl)
        case (CptsEsOne es1 s1 x1)
        assume a0: "\<exists>e. getspc_es ([(es1, s1, x1)] ! 0) = EvtSeq e es"
        then obtain e1 where a1: "getspc_es ([(es1, s1, x1)] ! 0) = EvtSeq e1 es" by auto
        then have "es1 = EvtSeq e1 es" by (simp add:getspc_es_def)
        then have "rm_evtsys1 (es1, s1, x1) = (e1, s1, x1)" 
          by (simp add: gets_es_def getspc_es_def rm_evtsys1_def getx_es_def)
        then have a2: "rm_evtsys [(es1, s1, x1)] = [(e1, s1, x1)]" by (simp add:rm_evtsys_def)
        show ?case 
          proof(simp add:e_eqv_einevtseq_def, rule conjI)
            show b0: "Suc 0 = length (rm_evtsys [(es1, s1, x1)])" by (simp add: a2) 
            moreover
            from a2 have "gets_e (rm_evtsys [(es1, s1, x1)] ! 0) = gets_es ([(es1, s1, x1)] ! 0)" 
              by (simp add: gets_es_def rm_evtsys1_def gets_e_def)
            moreover
            from a2 have "getx_e (rm_evtsys [(es1, s1, x1)] ! 0) = getx_es ([(es1, s1, x1)] ! 0)"
              by (simp add: getx_es_def rm_evtsys1_def getx_e_def)
            moreover
            from a2 have "getspc_es ([(es1, s1, x1)] ! 0) = EvtSeq (getspc_e (rm_evtsys [(es1, s1, x1)] ! 0)) es"
              using getspc_es_def getspc_e_def by (metis a1 fst_conv nth_Cons_0)
            ultimately show "\<forall>i. Suc i \<le> length (rm_evtsys [(es1, s1, x1)]) \<longrightarrow>
                      gets_e (rm_evtsys [(es1, s1, x1)] ! i) = gets_es ([(es1, s1, x1)] ! i) \<and>
                      getx_e (rm_evtsys [(es1, s1, x1)] ! i) = getx_es ([(es1, s1, x1)] ! i) \<and>
                      getspc_es ([(es1, s1, x1)] ! i) = EvtSeq (getspc_e (rm_evtsys [(es1, s1, x1)] ! i)) es"
                      by (metis One_nat_def Suc_le_lessD less_one)
          qed
      next
        case (CptsEsEnv es1 t1 x1 xs1 s1 y1)
        assume a0: "(es1, t1, x1) # xs1 \<in> cpts_es"
          and  a1: "\<forall>i. Suc i \<le> length ((es1, t1, x1) # xs1) \<longrightarrow> getspc_es (((es1, t1, x1) # xs1) ! i) \<noteq> es \<Longrightarrow>
                    \<exists>e. getspc_es (((es1, t1, x1) # xs1) ! 0) = EvtSeq e es \<Longrightarrow>
                    e_eqv_einevtseq ((es1, t1, x1) # xs1) (rm_evtsys ((es1, t1, x1) # xs1)) es"
          and  a2: "\<forall>i. Suc i \<le> length ((es1, s1, y1) # (es1, t1, x1) # xs1) 
                      \<longrightarrow> getspc_es (((es1, s1, y1) # (es1, t1, x1) # xs1) ! i) \<noteq> es"
          and  a3: "\<exists>e. getspc_es (((es1, s1, y1) # (es1, t1, x1) # xs1) ! 0) = EvtSeq e es"
        from a2 have a4: "\<forall>i. Suc i \<le> length ((es1, t1, x1) # xs1) \<longrightarrow> getspc_es (((es1, t1, x1) # xs1) ! i) \<noteq> es"
          by auto
        from a3 obtain e1 where a5: "es1 = EvtSeq e1 es" using getspc_es_def by (metis fst_conv nth_Cons_0)
        then have "\<exists>e. getspc_es (((es1, t1, x1) # xs1) ! 0) = EvtSeq e es" 
          using getspc_es_def by (simp add: getspc_es_def) 
        with a1 a4 have a6: "e_eqv_einevtseq ((es1, t1, x1) # xs1) (rm_evtsys ((es1, t1, x1) # xs1)) es" by simp
        from a5 have a7: "rm_evtsys1 (es1, s1, y1) = (e1, s1, y1)" 
          by (simp add: gets_es_def getspc_es_def rm_evtsys1_def getx_es_def)
        have "rm_evtsys ((es1, s1, y1) # (es1, t1, x1) # xs1) = 
          rm_evtsys1 (es1, s1, y1) # rm_evtsys ((es1, t1, x1) # xs1)" by (simp add: rm_evtsys_def) 
        with a6 a7 show ?case using gets_e_def gets_es_def getx_e_def getx_es_def 
          getspc_es_def getspc_e_def e_eqv_einevtseq_s by (metis a5 fst_conv snd_conv)
      next
        case (CptsEsComp es1 s1 x1 et es2 t1 y1 xs1)
        assume a0: "(es1, s1, x1) -es-et\<rightarrow> (es2, t1, y1)"
          and  a1: "(es2, t1, y1) # xs1 \<in> cpts_es"
          and  a2: "\<forall>i. Suc i \<le> length ((es2, t1, y1) # xs1) \<longrightarrow> getspc_es (((es2, t1, y1) # xs1) ! i) \<noteq> es \<Longrightarrow>
                      \<exists>e. getspc_es (((es2, t1, y1) # xs1) ! 0) = EvtSeq e es \<Longrightarrow>
                      e_eqv_einevtseq ((es2, t1, y1) # xs1) (rm_evtsys ((es2, t1, y1) # xs1)) es"
          and  a3: "\<forall>i. Suc i \<le> length ((es1, s1, x1) # (es2, t1, y1) # xs1) 
                      \<longrightarrow> getspc_es (((es1, s1, x1) # (es2, t1, y1) # xs1) ! i) \<noteq> es"
          and  a4: "\<exists>e. getspc_es (((es1, s1, x1) # (es2, t1, y1) # xs1) ! 0) = EvtSeq e es"
        from a3 have a5: "\<forall>i. Suc i \<le> length ((es2, t1, y1) # xs1) \<longrightarrow> getspc_es (((es2, t1, y1) # xs1) ! i) \<noteq> es"
          by auto
        from a4 obtain e1 where a6: "es1 = EvtSeq e1 es" using getspc_es_def by (metis fst_conv nth_Cons_0)
        from a3 have "getspc_es (es2, t1, y1) \<noteq> es" by auto
        then have a7: "es2 \<noteq> es" by (simp add:getspc_es_def)
        with a0 a6 have "\<exists>e2. es2 = EvtSeq e2 es" by (meson evtseq_tran_evtsys) 
        then obtain e2 where a8: "es2 = EvtSeq e2 es" by auto
        then have a9: "\<exists>e. getspc_es (((es2, t1, y1) # xs1) ! 0) = EvtSeq e es" by (simp add:getspc_es_def)
        with a2 a5 have a10: "e_eqv_einevtseq ((es2, t1, y1) # xs1) (rm_evtsys ((es2, t1, y1) # xs1)) es" by simp
        have a11: "rm_evtsys ((es1, s1, x1) # (es2, t1, y1) # xs1) = rm_evtsys1 (es1, s1, x1) # rm_evtsys ((es2, t1, y1) # xs1)"
          by (simp add:rm_evtsys_def)
        from a6 have a12: "rm_evtsys1 (es1, s1, x1) = (e1, s1, x1)" 
          by (simp add: gets_es_def getspc_es_def rm_evtsys1_def getx_es_def)
        with a6 a11 a10 show ?case using gets_e_def gets_es_def getx_e_def getx_es_def 
          getspc_es_def getspc_e_def e_eqv_einevtseq_s by (metis fst_conv snd_conv)
      qed

    ultimately have "?el \<in> cpts_of_ev e s x \<and> length esl = length ?el \<and> e_eqv_einevtseq esl ?el es" by auto
    then show ?thesis by auto
  qed

lemma evtseq_fst_finish: 
  "\<lbrakk>esl \<in> cpts_es; getspc_es (esl ! 0) = EvtSeq e es; Suc m \<le> length esl; 
     \<exists>i. i \<le> m \<and> getspc_es (esl ! i) = es\<rbrakk> \<Longrightarrow> 
      \<exists>i. (i \<le> m \<and> getspc_es (esl ! i) = es) \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) \<noteq> es)" 
  proof -
    assume p0: "esl \<in> cpts_es"
      and  p1: "getspc_es (esl ! 0) = EvtSeq e es"
      and  p2: "Suc m \<le> length esl"
      and  p3: "\<exists>i. i \<le> m \<and> getspc_es (esl ! i) = es"
    have "\<forall>m. esl \<in> cpts_es \<and> getspc_es (esl ! 0) = EvtSeq e es \<and> Suc m \<le> length esl \<and> 
              (\<exists>i. i \<le> m \<and> getspc_es (esl ! i) = es) \<longrightarrow>
          (\<exists>i. (i \<le> m \<and> getspc_es (esl ! i) = es) \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) \<noteq> es) )"
      proof - 
      {
        fix m
        assume a0: "esl \<in> cpts_es"
          and  a1: "getspc_es (esl ! 0) = EvtSeq e es"
          and  a2: "Suc m \<le> length esl"
          and  a3: "(\<exists>i. i \<le> m \<and> getspc_es (esl ! i) = es)"
        then have "\<exists>i. (i \<le> m \<and> getspc_es (esl ! i) = es) \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) \<noteq> es)"
          proof(induct m)
            case 0 show ?case using "0.prems"(4) by auto 
          next
            case (Suc n)
            assume b0: "esl \<in> cpts_es \<Longrightarrow>
                        getspc_es (esl ! 0) = EvtSeq e es \<Longrightarrow>
                        Suc n \<le> length esl \<Longrightarrow>
                        \<exists>i\<le>n. getspc_es (esl ! i) = es \<Longrightarrow> 
                        \<exists>i. (i \<le> n \<and> getspc_es (esl ! i) = es) \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) \<noteq> es)"
              and  b1: "esl \<in> cpts_es"
              and  b2: "getspc_es (esl ! 0) = EvtSeq e es"
              and  b3: "Suc (Suc n) \<le> length esl"
              and  b4: "\<exists>i\<le>Suc n. getspc_es (esl ! i) = es"
            show ?case
              proof(cases "\<exists>i\<le>n. getspc_es (esl ! i) = es")
                assume c0: "\<exists>i\<le>n. getspc_es (esl ! i) = es"
                with b0 b1 b2 b3 have "\<exists>i. (i \<le> n \<and> getspc_es (esl ! i) = es) \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) \<noteq> es)"
                  using Suc_leD by blast
                then show ?case using le_Suc_eq by blast
              next
                assume c0: "\<not> (\<exists>i\<le>n. getspc_es (esl ! i) = es)"
                with b4 have "getspc_es (esl ! (Suc n)) = es" using le_SucE by auto 
                moreover from c0 have "\<forall>j. j < Suc n \<longrightarrow> getspc_es (esl ! j) \<noteq> es" by auto
                ultimately show ?case by blast
              qed
          qed
      }
      then show ?thesis by auto
      qed

    then show ?thesis using p0 p1 p2 p3 by blast
  qed

lemma EventSeq_sound : 
    "\<lbrakk> \<Turnstile> e sat\<^sub>e [pre, rely1, guar1, post1]; \<Turnstile> es sat\<^sub>s [pre2, rely2, guar2, post]; 
      rely \<subseteq> rely1; rely \<subseteq> rely2; guar1 \<subseteq> guar; guar2 \<subseteq> guar; post1 \<subseteq> pre2\<rbrakk> 
      \<Longrightarrow> \<Turnstile> EvtSeq e es sat\<^sub>s [pre, rely, guar, post]"
  proof -
    assume p0: "\<Turnstile> e sat\<^sub>e [pre, rely1, guar1, post1]"
      and  p1: "\<Turnstile> es sat\<^sub>s [pre2, rely2, guar2, post]"
      and  p2: "rely \<subseteq> rely1"
      and  p3: "rely \<subseteq> rely2"
      and  p4: "guar1 \<subseteq> guar"
      and  p5: "guar2 \<subseteq> guar"
      and  p6: "post1 \<subseteq> pre2"
    then have "\<forall>s x. (cpts_of_es (EvtSeq e es) s x) \<inter> assume_es(pre, rely) \<subseteq> commit_es(guar, post) \<inter> preserves_es"
      proof -
      {
        fix s x
        have "\<forall>esl. esl\<in>(cpts_of_es (EvtSeq e es) s x) \<inter> assume_es (pre, rely) \<longrightarrow> esl\<in> commit_es (guar, post) \<inter> preserves_es"
          proof -
          {
            fix esl
            assume a0: "esl \<in> (cpts_of_es (EvtSeq e es) s x) \<inter> assume_es (pre, rely)"
            then have a01: "esl \<in> cpts_of_es (EvtSeq e es) s x" by simp
            from a0 have a02: "esl \<in> assume_es (pre, rely)" by auto
 
            from a01 have a01_1: "esl ! 0 = (EvtSeq e es, s, x)" by (simp add: cpts_of_es_def) 
            from a01 have a01_2: "esl \<in> cpts_es" by (simp add: cpts_of_es_def) 

            have "esl\<in> commit_es (guar, post) \<inter> preserves_es"
              proof(cases "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> es")
                assume b0: "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> es"
                with a01 have "\<exists>el. (el \<in> cpts_of_ev e s x \<and> length esl = length el \<and> e_eqv_einevtseq esl el es)"
                  by (simp add: evtseq_nfin_samelower)
                then obtain el where b1: "el \<in> cpts_of_ev e s x \<and> length esl = length el \<and> e_eqv_einevtseq esl el es"
                  by auto
                have "el \<in> assume_e (pre, rely1)"
                  proof(simp add:assume_e_def, rule conjI)
                    from a02 have c0: "gets_es (esl ! 0) \<in> pre" by (simp add:assume_es_def)
                    moreover
                    from b1 have "gets_e (el ! 0) = s" by (simp add:cpts_of_ev_def gets_e_def)
                    moreover
                    from a01_1 have "gets_es (esl ! 0) = s" by (simp add:cpts_of_ev_def gets_es_def)
                    ultimately show "gets_e (el ! 0) \<in> pre" by simp
                  next
                    show "\<forall>i. Suc i < length el \<longrightarrow> el ! i -ee\<rightarrow> el ! Suc i \<longrightarrow> 
                            (gets_e (el ! i), gets_e (el ! Suc i)) \<in> rely1 "
                      proof -
                      {
                        fix i
                        assume c0:"Suc i < length el"
                          and  c1: "el ! i -ee\<rightarrow> el ! Suc i"
                        then have c2: "getspc_e (el ! i) = getspc_e (el ! Suc i)"
                          by (simp add: eetran_eqconf1) 
                        moreover from b1 c0 have "getspc_es (esl ! i) = EvtSeq (getspc_e (el ! i)) es"
                          by (simp add: e_eqv_einevtseq_def) 
                        moreover from b1 c0 have "getspc_es (esl ! Suc i) = EvtSeq (getspc_e (el ! Suc i)) es"
                          by (simp add: e_eqv_einevtseq_def) 
                        ultimately have c3: "getspc_es (esl ! i) = getspc_es (esl ! Suc i)" by simp

                        then have "esl ! i -ese\<rightarrow> esl ! Suc i" by (simp add: eqconf_esetran) 
                        with a02 b1 c0 have "(gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely"
                          by (simp add: assume_es_def)
                        moreover have "gets_es (esl!i) = gets_e (el ! i)"
                          by (metis b1 c0 e_eqv_einevtseq_def less_imp_le_nat) 
                        moreover have "gets_es (esl!Suc i) = gets_e (el ! Suc i)"
                          by (metis Suc_le_eq b1 c0 e_eqv_einevtseq_def)
                        ultimately have "(gets_e (el ! i), gets_e (el ! Suc i)) \<in> rely" by simp

                        with p2 have "(gets_e (el ! i), gets_e (el ! Suc i)) \<in> rely1" by auto
                      }
                      then show ?thesis by auto
                      qed
                  qed
                with p0 b1 have b2 : "el \<in> commit_e(guar1, post1) \<inter> preserves_e"
                  by (meson IntI contra_subsetD evt_validity_def)
                then have "\<forall>i. Suc i<length el \<longrightarrow> (\<exists>t. el!i -et-t\<rightarrow> el!(Suc i)) 
                        \<longrightarrow> (gets_e (el!i), gets_e (el!Suc i)) \<in> guar1" by (simp add:commit_e_def)
                with p4 have b3: "\<forall>i. Suc i<length el \<longrightarrow> (\<exists>t. el!i -et-t\<rightarrow> el!(Suc i)) 
                        \<longrightarrow> (gets_e (el!i), gets_e (el!Suc i)) \<in> guar" by auto

                then have b4 : "esl \<in> commit_es (guar, post)"
                  proof(simp add:commit_es_def)
                    show "\<forall>i. Suc i < length esl \<longrightarrow> (\<exists>t. esl ! i -es-t\<rightarrow> esl ! Suc i) 
                              \<longrightarrow> (gets_es (esl ! i), gets_es (esl ! Suc i)) \<in> guar"
                      proof -
                      {
                        fix i
                        assume c0: "Suc i < length esl"
                          and  c1: "(\<exists>t. esl ! i -es-t\<rightarrow> esl ! Suc i)"
                        with b1 have c2: "getspc_es (esl ! i) = EvtSeq (getspc_e (el ! i)) es" 
                          by (simp add: e_eqv_einevtseq_def) 
                        
                        from b1 c0 have c3: "getspc_es (esl ! Suc i) = EvtSeq (getspc_e (el ! Suc i)) es" 
                          by (simp add: e_eqv_einevtseq_def) 
                        from c1 have "getspc_es (esl ! i) \<noteq> getspc_es (esl ! Suc i)" 
                          using evtsys_not_eq_in_tran_aux getspc_es_def by (metis surjective_pairing) 
                        with c2 c3 have "getspc_e (el ! i) \<noteq> getspc_e (el ! Suc i)" by simp
                        then have "\<exists>t. (el ! i) -et-t\<rightarrow> (el ! Suc i)"
                          using b1 c0 cpts_of_ev_def notran_confeqi by fastforce 
                        with b3 have "(gets_e (el!i), gets_e (el!Suc i)) \<in> guar"
                          using b1 c0 by auto 
                        moreover have "gets_e (el!i) = gets_es (esl ! i)"
                          using b1 c0 e_eqv_einevtseq_def less_imp_le by fastforce 
                        moreover have "gets_e (el!Suc i) = gets_es (esl ! Suc i)"
                          using Suc_leI b1 c0 e_eqv_einevtseq_def by fastforce 
                        ultimately have "(gets_es (esl ! i), gets_es (esl ! Suc i)) \<in> guar" by simp
                      }
                      then show ?thesis by auto
                      qed
                    qed

                    from b2 have "el \<in> preserves_e" by auto
                    then have b5: "\<forall>i. i < length el \<longrightarrow> ann_preserves_e (getspc_e (el!i)) (gets_e (el!i))"
                      by (simp add: preserves_e_def)

                    then have b6: "esl \<in> preserves_es"
                    proof(simp add: preserves_es_def)
                      show "\<forall>i<length esl. ann_preserves_es (getspc_es (esl ! i)) (gets_es (esl ! i))"
                      proof-
                        {
                          fix i
                          assume c0 : "i < length esl"
                          with b1 have c1: "getspc_es (esl ! i) = EvtSeq (getspc_e (el ! i)) es" 
                            by (simp add: e_eqv_einevtseq_def)
                          with c0 b1 have c2: "gets_es (esl ! i) = gets_e (el ! i)"
                            by (simp add: e_eqv_einevtseq_def)
                          from b1 b5 c0 have c3: "ann_preserves_e (getspc_e (el!i)) (gets_e (el!i))"
                            by auto
                          with c1 c2 have "ann_preserves_es (getspc_es (esl ! i)) (gets_es (esl ! i))"
                            by simp
                        }
                        then show ?thesis by auto
                      qed
                    qed

                    with b4 show ?thesis by (simp add: preserves_es_def commit_es_def)
                  next
                    assume b0: "\<not> (\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) \<noteq> es)"
                    from a01_1 have b00: "getspc_es (esl ! 0) = EvtSeq e es" by (simp add:getspc_es_def)
                    from b0 have "\<exists>m. Suc m \<le> length esl \<and> getspc_es (esl ! m) = es" by auto
                    then obtain m where b1: "Suc m \<le> length esl \<and> getspc_es (esl ! m) = es" by auto
                    then have "\<exists>i. i \<le> m \<and> getspc_es (esl ! i) = es" by auto
                    with a01_1 a01_2 b00 b1 have b2: "\<exists>i. (i \<le> m \<and> getspc_es (esl ! i) = es) \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) \<noteq> es)"
                      using evtseq_fst_finish by blast
                    then obtain n where b3: "(n \<le> m \<and> getspc_es (esl ! n) = es) \<and> (\<forall>j. j < n \<longrightarrow> getspc_es (esl ! j) \<noteq> es)"
                      by auto
                    with b00 have b41: "n \<noteq> 0" by (metis (no_types, hide_lams) add.commute add.right_neutral 
                                   add_Suc dual_order.irrefl esys.size(3) le_add1 le_imp_less_Suc)

                    then have b4: "n > 0" by auto
                    then obtain esl0 where b5: "esl0 = take n esl" by simp
                    then have b5_1: "length esl0 = n" using b1 b3 less_le_trans by auto 
                    obtain esl1 where b6: "esl1 = drop n esl" by simp
                    with b5 have b7: "esl0 @ esl1 = esl" by simp
                    from a01_2 b1 b3 b4 b5 have b8: "esl0 \<in> cpts_es"
                      by (metis (no_types, lifting) Suc_diff_1 Suc_le_lessD cpts_es_take less_trans)
                    from a01_2 b1 b3 b4 b5 b6 have b9: "esl1 \<in> cpts_es"
                      by (metis (no_types, lifting) Suc_diff_1 Suc_le_lessD cpts_es_dropi le_neq_implies_less less_trans)
                    have b10: "esl0 ! 0 = (EvtSeq e es, s, x)" by (simp add: a01_1 b4 b5) 
                    have b11: "getspc_es (esl1 ! 0) = es" using b1 b3 b6 by auto 

                    from b3 b5 have b11_1: "\<forall>i. i < length esl0 \<longrightarrow> getspc_es (esl0 ! i) \<noteq> es" by auto
                    moreover from b8 b10 have "esl0 \<in> cpts_of_es (EvtSeq e es) s x" by (simp add:cpts_of_es_def)
                    ultimately have b12: "\<exists>el. (el \<in> cpts_of_ev e s x \<and> length esl0 = length el \<and> e_eqv_einevtseq esl0 el es)"
                      by (simp add: evtseq_nfin_samelower)
                    then obtain el where b12_1: "el \<in> cpts_of_ev e s x \<and> length esl0 = length el \<and> e_eqv_einevtseq esl0 el es"
                      by auto
                    then have b12_2: "el \<in> cpts_ev" by (simp add:cpts_of_ev_def)

                    from a02 have b13: "gets_es (esl!0) \<in> pre \<and> (\<forall>i. Suc i<length esl \<longrightarrow> 
                                    esl!i -ese\<rightarrow> esl!(Suc i) \<longrightarrow> (gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely)"
                      by (simp add:assume_es_def)
                    have b14: "esl0 \<in> assume_es (pre, rely)"
                    proof(simp add:assume_es_def, rule conjI)
                      show "gets_es (esl0 ! 0) \<in> pre" using a01_1 b10 b13 by auto 
                  next
                    from b5 b13 show "\<forall>i. Suc i < length esl0 \<longrightarrow> esl0 ! i -ese\<rightarrow> esl0 ! Suc i 
                            \<longrightarrow> (gets_es (esl0 ! i), gets_es (esl0 ! Suc i)) \<in> rely" by auto
                  qed
                  with p2 have b15: "esl0 \<in> assume_es (pre, rely1)"
                    by (simp add: assume_es_def subset_iff)
                
                
                  have b16: "el \<in> assume_e (pre, rely1)"
                  proof(simp add:assume_e_def, rule conjI)
                    from a02 have c0: "gets_es (esl ! 0) \<in> pre" by (simp add:assume_es_def)
                    moreover
                    from b12_1 have "gets_e (el ! 0) = s" by (simp add:cpts_of_ev_def gets_e_def)
                    moreover
                    from a01_1 have "gets_es (esl ! 0) = s" by (simp add:cpts_of_ev_def gets_es_def)
                    ultimately show "gets_e (el ! 0) \<in> pre" by simp
                  next
                    show "\<forall>i. Suc i < length el \<longrightarrow> el ! i -ee\<rightarrow> el ! Suc i \<longrightarrow> 
                            (gets_e (el ! i), gets_e (el ! Suc i)) \<in> rely1 "
                    proof -
                      {
                        fix i
                        assume c0:"Suc i < length el"
                          and  c1: "el ! i -ee\<rightarrow> el ! Suc i"
                        then have c2: "getspc_e (el ! i) = getspc_e (el ! Suc i)"
                          by (simp add: eetran_eqconf1) 
                        moreover from b12_1 c0 have "getspc_es (esl0 ! i) = EvtSeq (getspc_e (el ! i)) es"
                          by (simp add: e_eqv_einevtseq_def) 
                        moreover from b12_1 c0 have "getspc_es (esl0 ! Suc i) = EvtSeq (getspc_e (el ! Suc i)) es"
                          by (simp add: e_eqv_einevtseq_def) 
                        ultimately have c3: "getspc_es (esl0 ! i) = getspc_es (esl0 ! Suc i)" by simp

                        then have c4: "esl0 ! i -ese\<rightarrow> esl0 ! Suc i" by (simp add: eqconf_esetran) 
                        with b14 b12_1 c0 have "(gets_es (esl0!i), gets_es (esl0!Suc i)) \<in> rely" 
                        proof -
                          from b14 have "\<forall>i. Suc i<length esl0 \<longrightarrow> esl0!i -ese\<rightarrow> esl0!(Suc i) 
                                      \<longrightarrow> (gets_es (esl0!i), gets_es (esl0!Suc i)) \<in> rely" 
                            by (simp add:assume_es_def)
                          with b12_1 c0 c4 show ?thesis by simp
                          qed

                          moreover have "gets_es (esl0!i) = gets_e (el ! i)"
                            by (metis b12_1 c0 e_eqv_einevtseq_def less_imp_le_nat)
                          moreover have "gets_es (esl0!Suc i) = gets_e (el ! Suc i)"
                            using b12_1 c0 by (simp add: b12_1 c0 e_eqv_einevtseq_def Suc_leI)
                          ultimately have "(gets_e (el ! i), gets_e (el ! Suc i)) \<in> rely" by simp

                          with p2 have "(gets_e (el ! i), gets_e (el ! Suc i)) \<in> rely1" by auto
                        }
                        then show ?thesis by auto
                      qed
                    qed

                    have b17: "el \<in> commit_e(guar1, post1) \<inter> preserves_e"
                      using b12_1 b16 evt_validity_def p0 by fastforce
                    then have b18: "\<forall>i. Suc i<length el \<longrightarrow> (\<exists>t. el!i -et-t\<rightarrow> el!(Suc i)) 
                        \<longrightarrow> (gets_e (el!i), gets_e (el!Suc i)) \<in> guar1" by (simp add:commit_e_def)
                    with p4 have b19: "\<forall>i. Suc i<length el \<longrightarrow> (\<exists>t. el!i -et-t\<rightarrow> el!(Suc i)) 
                        \<longrightarrow> (gets_e (el!i), gets_e (el!Suc i)) \<in> guar" by auto

                    from b17 have b20: "\<forall>i. i < length el \<longrightarrow> ann_preserves_e (getspc_e (el!i)) (gets_e (el!i))"
                      by (simp add: preserves_e_def)

                    from b11 have "\<exists>sn xn. esl1 ! 0 = (es, sn, xn)" using getspc_es_def
                      by (metis fst_conv surj_pair)
                    then obtain sn and xn where b13: "esl1 ! 0 = (es, sn, xn)" by auto
                    with b9 have "esl1 \<in> cpts_of_es es sn xn" by (simp add:cpts_of_es_def)

                    have b21 : "esl1 \<in> cpts_of_es es sn xn \<inter> assume_es (pre2, rely2)"
                    proof-
                      {
                        from b5_1 b12_1 have d1: "getspc_es (esl0 ! (n-1)) = EvtSeq (getspc_e (el ! (n-1))) es"
                          by (simp add: b12_1 e_eqv_einevtseq_def b4) 
                        with b5 have d1_1: "getspc_es (esl ! (n-1)) = EvtSeq (getspc_e (el ! (n-1))) es"
                          by (simp add: b4) 
                        then have "\<exists>sn1 xn1. esl ! (n-1) = (EvtSeq (getspc_e (el ! (n-1))) es, sn1, xn1)" 
                          using getspc_es_def by (metis fst_conv surj_pair) 
                        then obtain sn1 and xn1 where d2: "esl ! (n-1) = (EvtSeq (getspc_e (el ! (n-1))) es, sn1, xn1)"
                          by auto

                      from b4 b5 b5_1 b12_1 have "gets_e (el ! (n -1) ) = gets_es (esl0 ! (n -1)) \<and>
                          getx_e (el ! (n -1)) = getx_es (esl0 ! (n -1))" by (simp add:e_eqv_einevtseq_def)
                      with b5 d2 have d3: "el ! (n -1) = (getspc_e (el ! (n-1)), sn1, xn1)"
                        using gets_e_def gets_es_def getx_e_def getx_es_def getspc_e_def 
                        by (metis Suc_diff_1 b4 lessI nth_take prod.collapse snd_conv)

                      from b13 have d4: "esl ! n = (es, sn, xn)" using b6 
                        by (metis b3 b5_1 b7 cancel_comm_monoid_add_class.diff_cancel nth_append)

                      from a01_2 b1 b3 have d5: "drop (n-1) esl \<in> cpts_es" using cpts_es_dropi
                        by (metis (no_types, hide_lams) Suc_diff_1 Suc_le_lessD b5 b5_1 
                              drop_0 less_or_eq_imp_le neq0_conv not_le take_all zero_less_diff) 
                      with d2 d4 have d6: "\<exists>est. esl ! (n-1) -es-est\<rightarrow> esl ! n" 
                        by (metis (no_types, lifting) One_nat_def Suc_le_lessD Suc_pred a01_2 
                            b3 b4 b6 b9 cpts_es_not_empty d1_1 diff_less esetran.cases
                            incpts_es_impl_evnorcomptran le_numeral_extra(4) length_drop 
                            length_greater_0_conv zero_less_diff)
                      with d2 have d7: "\<exists>t. (getspc_e (el ! (n-1)), sn1, xn1) -et-t\<rightarrow>(AnonyEvent (None),sn, xn)"
                        using evtseq_tran_0_exist_etran using d4 by fastforce 
                      with b4 b5_1 b12_1 b12_2 d3 have d8:"el @ [(AnonyEvent (None),sn, xn)] \<in> cpts_ev" 
                        using cpts_ev_onemore by fastforce
                      let ?el1 = "el @ [(AnonyEvent (None),sn, xn)]"

                      from d8 have d9: "?el1 \<in> cpts_of_ev e s x"
                        by (metis (no_types, lifting) append_Cons b12_1 b3 b4 b5_1 
                              cpts_of_ev_def list.size(3) mem_Collect_eq neq_Nil_conv nth_Cons_0)

                      from d8 have d9: "?el1 \<in> cpts_of_ev e s x"
                        by (metis (no_types, lifting) append_Cons b12_1 b3 b4 b5_1 
                          cpts_of_ev_def list.size(3) mem_Collect_eq neq_Nil_conv nth_Cons_0)
                      moreover from b16 d7 have "?el1 \<in> assume_e (pre, rely1)"
                      proof -
                        have "gets_e (?el1!0) \<in> pre"
                        proof -
                          from b16 have "gets_e (el!0) \<in> pre" by (simp add:assume_e_def)
                          then show ?thesis by (metis b12_1 b4 b5_1 nth_append)
                        qed
                        moreover
                            have "\<forall>i. Suc i<length ?el1 \<longrightarrow>  ?el1!i -ee\<rightarrow> ?el1!(Suc i) \<longrightarrow> 
                                  (gets_e (?el1!i), gets_e (?el1!Suc i)) \<in> rely1"
                            proof -
                              {
                                fix i
                                assume e0: "Suc i<length ?el1"
                                  and  e1: "?el1!i -ee\<rightarrow> ?el1!(Suc i)"
                                from b16 have e2: "\<forall>i. Suc i<length el \<longrightarrow>  el!i -ee\<rightarrow> el!(Suc i) \<longrightarrow> 
                                  (gets_e (el!i), gets_e (el!Suc i)) \<in> rely1" by (simp add:assume_e_def)
                                have "(gets_e (?el1!i), gets_e (?el1!Suc i)) \<in> rely1"
                                  proof(cases "Suc i < length ?el1 - 1")
                                    assume f0: "Suc i < length ?el1 - 1"
                                    with e0 e2 show ?thesis by (metis (no_types, lifting) Suc_diff_1 
                                        Suc_less_eq Suc_mono e1 length_append_singleton nth_append zero_less_Suc) 
                                  next
                                    assume "\<not> (Suc i < length ?el1 - 1)"
                                    then have f0: "Suc i \<ge> length ?el1 - 1" by simp
                                    with e0 have f1: "Suc i = length ?el1 - 1" by simp
                                    then have f2: "?el1!(Suc i) = (AnonyEvent None, sn, xn)" by simp
                                    from f1 have f3: "?el1!i = (getspc_e (el ! (n-1)), sn1, xn1)"
                                      by (metis b12_1 b5_1 d3 diff_Suc_1 length_append_singleton lessI nth_append) 
                                    
                                    with d7 f2 have "getspc_e (?el1!i) \<noteq> getspc_e (?el1!(Suc i))"
                                      using evt_not_eq_in_tran_aux by (metis e1 eetran.cases)
                                    moreover from e1 have "getspc_e (?el1!i) = getspc_e (?el1!(Suc i))" 
                                      using eetran_eqconf1 by blast
                                    ultimately show ?thesis by simp
                                  qed
                                }
                                then show ?thesis by auto
                              qed
                              ultimately show ?thesis by (simp add:assume_e_def)
                            qed
                            ultimately have d10: "?el1 \<in> commit_e(guar1, post1)"
                              using evt_validity_def p0 by fastforce
                          
                            have d11: "getspc_e (last ?el1) = AnonyEvent (None)" by (simp add:getspc_e_def)
                            with d10 have d12: "gets_e (last ?el1) \<in> post1" by (simp add: commit_e_def)
                            from d12 have "sn \<in> post1" by (simp add:gets_e_def)

                            from d4 have g2: "esl1 ! 0 = (es, sn, xn)" by (simp add: b13)
                            with b9 have d13: "esl1 \<in> cpts_of_es es sn xn" by (simp add:cpts_of_es_def)

                            with g2 p6 have d14: "gets_es (esl1 ! 0) \<in> pre2" 
                              using gets_es_def 
                              by (metis \<open>sn \<in> post1\<close> contra_subsetD fst_conv snd_conv) 
                                have "\<forall>i. Suc i < length esl1 \<longrightarrow> esl1 ! i -ese\<rightarrow> esl1 ! Suc i 
                                  \<longrightarrow> (gets_es (esl1 ! i), gets_es (esl1 ! Suc i)) \<in> rely2"
                                  proof -
                                  {
                                    fix i
                                    assume h0: "Suc i < length esl1"
                                      and  h1: "esl1 ! i -ese\<rightarrow> esl1 ! Suc i"
                                    have h2: "esl1 ! i = esl ! (n + i)" using b5_1 b7 by auto
                                    have h3: "esl1 ! Suc i = esl ! (n + Suc i)"
                                      by (metis b5_1 b7 nth_append_length_plus) 
                                    with h1 h2 have h4: "esl ! (n + i) -ese\<rightarrow> esl ! (n + Suc i)" by simp
                                    have "Suc (n + i) < length esl" using b5_1 b7 h0 by auto 
                                    with a02 h4 have "(gets_es (esl ! (n + i)), gets_es (esl ! (n + Suc i))) \<in> rely"
                                      by (simp add:assume_es_def)
                                    with h2 h3 have "(gets_es (esl1 ! i), gets_es (esl1 ! Suc i)) \<in> rely" by simp
                                      
                                    then have "(gets_es (esl1 ! i), gets_es (esl1 ! Suc i)) \<in> rely2"
                                      using p3 by auto 
                                  }
                                  then show ?thesis by auto
                                qed
                                with d13 d14 show ?thesis by (simp add: assume_es_def)
                              }
                            qed


                            have b22 : "\<forall>i. Suc i<length esl \<longrightarrow> (\<exists>t. esl!i -es-t\<rightarrow> esl!(Suc i)) 
                                      \<longrightarrow> (gets_es (esl!i), gets_es (esl!Suc i)) \<in> guar"
                            proof -
                              {
                                fix i
                                assume c0: "Suc i<length esl"
                                  and  c1: "\<exists>t. esl!i -es-t\<rightarrow> esl!(Suc i)"
                                have "(gets_es (esl!i), gets_es (esl!Suc i)) \<in> guar"
                                proof(cases "Suc i < n")
                                  assume d0: "Suc i < n"
                        
                                  with b5 b5_1 b12_1 c0 c1 have d1: "getspc_es (esl0 ! i) = EvtSeq (getspc_e (el ! i)) es" 
                                    using e_eqv_einevtseq_def by (metis less_imp_le_nat) 
                        
                                  with b5 b5_1 b12_1 c0 c1 have d2: "getspc_es (esl0 ! Suc i) = EvtSeq (getspc_e (el ! Suc i)) es" 
                                    using e_eqv_einevtseq_def by (metis Suc_le_eq d0) 
                        
                                  from c1 have d3: "getspc_es (esl ! i) \<noteq> getspc_es (esl ! Suc i)" 
                                    using evtsys_not_eq_in_tran_aux getspc_es_def by (metis surjective_pairing) 

                                  with d1 d2 have "getspc_e (el ! i) \<noteq> getspc_e (el ! Suc i)"
                                    by (simp add: Suc_lessD b5 d0) 
                                  then have "\<exists>t. (el ! i) -et-t\<rightarrow> (el ! Suc i)"
                                    using b12_1 b5_1 cpts_of_ev_def d0 notran_confeqi by fastforce 
 
                                  with b19 have "(gets_e (el!i), gets_e (el!Suc i)) \<in> guar"
                                    using b12_1 b5_1 d0 by auto
                                  moreover have "gets_e (el!i) = gets_es (esl0 ! i)"
                                    using b12_1 b5_1 d0 e_eqv_einevtseq_def less_imp_le_nat by fastforce 
                                  moreover have "gets_e (el!Suc i) = gets_es (esl0 ! Suc i)"
                                    using Suc_leI b12_1 b5_1 d0 e_eqv_einevtseq_def less_imp_le_nat by fastforce 
                                  ultimately have "(gets_es (esl0 ! i), gets_es (esl0 ! Suc i)) \<in> guar" by simp

                                  then show ?thesis by (simp add: Suc_lessD b5 d0)
                                next
                                  assume d0: "\<not> (Suc i < n)"
                          from b5_1 b12_1 have d1: "getspc_es (esl0 ! (n-1)) = EvtSeq (getspc_e (el ! (n-1))) es"
                            by (simp add: b12_1 e_eqv_einevtseq_def b4) 
                          with b5 have d1_1: "getspc_es (esl ! (n-1)) = EvtSeq (getspc_e (el ! (n-1))) es"
                            by (simp add: b4) 
                          then have "\<exists>sn1 xn1. esl ! (n-1) = (EvtSeq (getspc_e (el ! (n-1))) es, sn1, xn1)" 
                            using getspc_es_def by (metis fst_conv surj_pair) 
                          then obtain sn1 and xn1 where d2: "esl ! (n-1) = (EvtSeq (getspc_e (el ! (n-1))) es, sn1, xn1)"
                            by auto

                          from b4 b5 b5_1 b12_1 have "gets_e (el ! (n -1) ) = gets_es (esl0 ! (n -1)) \<and>
                                       getx_e (el ! (n -1)) = getx_es (esl0 ! (n -1))" by (simp add:e_eqv_einevtseq_def)
                          with b5 d2 have d3: "el ! (n -1) = (getspc_e (el ! (n-1)), sn1, xn1)" 
                            using gets_e_def gets_es_def getx_e_def getx_es_def getspc_e_def 
                            by (metis Suc_diff_1 b4 lessI nth_take prod.collapse snd_conv)

                          from b13 have d4: "esl ! n = (es, sn, xn)" using b6 c0 d0 by auto 

                          from a01_2 b1 b3 have d5: "drop (n-1) esl \<in> cpts_es" using cpts_es_dropi
                            by (metis (no_types, hide_lams) Suc_diff_1 Suc_le_lessD b5 b5_1 
                              drop_0 less_or_eq_imp_le neq0_conv not_le take_all zero_less_diff)
                          with d2 d4 have d6: "\<exists>est. esl ! (n-1) -es-est\<rightarrow> esl ! n" 
                            by (metis (no_types, lifting) One_nat_def Suc_le_lessD Suc_pred a01_2 
                            b3 b4 b6 b9 cpts_es_not_empty d1_1 diff_less esetran.cases 
                            incpts_es_impl_evnorcomptran le_numeral_extra(4) length_drop 
                            length_greater_0_conv zero_less_diff)
                          with d2 have d7: "\<exists>t. (getspc_e (el ! (n-1)), sn1, xn1) -et-t\<rightarrow>(AnonyEvent (None),sn, xn)"
                            using evtseq_tran_0_exist_etran using d4 by fastforce 
                          with b4 b5_1 b12_1 b12_2 d3 have d8:"el @ [(AnonyEvent (None),sn, xn)] \<in> cpts_ev" 
                            using cpts_ev_onemore by fastforce
                          let ?el1 = "el @ [(AnonyEvent (None),sn, xn)]"
                        
                          from d8 have d9: "?el1 \<in> cpts_of_ev e s x"
                            by (metis (no_types, lifting) append_Cons b12_1 b3 b4 b5_1 
                              cpts_of_ev_def list.size(3) mem_Collect_eq neq_Nil_conv nth_Cons_0)
                          moreover from b16 d7 have "?el1 \<in> assume_e (pre, rely1)"
                          proof -
                            have "gets_e (?el1!0) \<in> pre"
                            proof -
                              from b16 have "gets_e (el!0) \<in> pre" by (simp add:assume_e_def)
                              then show ?thesis by (metis b12_1 b4 b5_1 nth_append) 
                            qed
                            moreover
                            have "\<forall>i. Suc i<length ?el1 \<longrightarrow>  ?el1!i -ee\<rightarrow> ?el1!(Suc i) \<longrightarrow> 
                                  (gets_e (?el1!i), gets_e (?el1!Suc i)) \<in> rely1"
                            proof -
                              {
                                fix i
                                assume e0: "Suc i<length ?el1"
                                  and  e1: "?el1!i -ee\<rightarrow> ?el1!(Suc i)"
                                from b16 have e2: "\<forall>i. Suc i<length el \<longrightarrow>  el!i -ee\<rightarrow> el!(Suc i) \<longrightarrow> 
                                  (gets_e (el!i), gets_e (el!Suc i)) \<in> rely1" by (simp add:assume_e_def)
                                have "(gets_e (?el1!i), gets_e (?el1!Suc i)) \<in> rely1"
                                  proof(cases "Suc i < length ?el1 - 1")
                                    assume f0: "Suc i < length ?el1 - 1"
                                    with e0 e2 show ?thesis by (metis (no_types, lifting) Suc_diff_1 
                                        Suc_less_eq Suc_mono e1 length_append_singleton nth_append zero_less_Suc) 
                                  next
                                    assume "\<not> (Suc i < length ?el1 - 1)"
                                    then have f0: "Suc i \<ge> length ?el1 - 1" by simp
                                    with e0 have f1: "Suc i = length ?el1 - 1" by simp
                                    then have f2: "?el1!(Suc i) = (AnonyEvent None, sn, xn)" by simp
                                    from f1 have f3: "?el1!i = (getspc_e (el ! (n-1)), sn1, xn1)"
                                      by (metis b12_1 b5_1 d3 diff_Suc_1 length_append_singleton lessI nth_append) 
                                    
                                    with d7 f2 have "getspc_e (?el1!i) \<noteq> getspc_e (?el1!(Suc i))"
                                      using evt_not_eq_in_tran_aux by (metis e1 eetran.cases)
                                    moreover from e1 have "getspc_e (?el1!i) = getspc_e (?el1!(Suc i))" 
                                      using eetran_eqconf1 by blast
                                    ultimately show ?thesis by simp
                                  qed
                              }
                              then show ?thesis by auto
                              qed
                              
                              ultimately show ?thesis by (simp add:assume_e_def)
                            qed
                            ultimately have d10: "?el1 \<in> commit_e(guar1, post1)"
                              using evt_validity_def p0 by fastforce
                          
                            have d11: "getspc_e (last ?el1) = AnonyEvent (None)" by (simp add:getspc_e_def)
                            with d10 have d12: "gets_e (last ?el1) \<in> post1" by (simp add: commit_e_def)
                        
                            show ?thesis
                            proof(cases "Suc i = n")
                              assume g0: "Suc i = n"
                              from d10 have "(\<forall>i. Suc i<length ?el1 \<longrightarrow> (\<exists>t. ?el1!i -et-t\<rightarrow> ?el1!(Suc i)) 
                                \<longrightarrow> (gets_e (?el1!i), gets_e (?el1!Suc i)) \<in> guar1)" by (simp add: commit_e_def)
                              with d7 have g1: "(gets_e (?el1!i), gets_e (?el1!Suc i)) \<in> guar1"
                                by (metis (no_types, lifting) b12_1 b5_1 d3 diff_Suc_1 
                                g0 length_append_singleton lessI nth_append nth_append_length) 
                              moreover have "?el1!(Suc i) = (AnonyEvent None, sn, xn)"
                                using b12_1 b5_1 g0 by auto 
                              moreover from g0 b5_1 b12_1 have "?el1!i = (getspc_e (el ! (n-1)), sn1, xn1)"
                                by (metis b12_1 b5_1 d3 diff_Suc_1 lessI nth_append) 
                              ultimately have "(sn1,sn) \<in> guar1" by (simp add:gets_e_def)
                              with p4 have "(sn1,sn) \<in> guar" by auto
                              with d4 d2 have "(gets_es (esl ! (n - 1)), gets_es (esl ! Suc (n - 1))) \<in> guar" 
                                by (simp add: gets_es_def b4) 
                              then show ?thesis using g0 by auto 
                            next
                              assume "Suc i \<noteq> n"
                              then have g1: "Suc i > n"
                                using d0 linorder_neqE_nat by blast 
                                from b21 have g2: "esl1 \<in> commit_es (guar2,post)"
                                  by (meson contra_subsetD es_validity_def le_inf_iff p1)
                            
                                have g3: "esl ! i = esl1 ! (i - n)"
                                  by (metis b5_1 b7 g1 not_less_eq nth_append) 
                                have g4: "esl ! Suc i = esl1 ! (Suc i - n)"
                                  by (metis b5_1 b7 d0 nth_append)

                                have g5: "Suc (i - n) < length esl1" using b6 c0 g1 by auto
                                from g2 have "\<forall>i. Suc i<length esl1 \<longrightarrow> (\<exists>t. esl1!i -es-t\<rightarrow> esl1!(Suc i)) 
                                \<longrightarrow> (gets_es (esl1!i), gets_es (esl1!Suc i)) \<in> guar2" by (simp add:commit_es_def)
                                with g5 have "(gets_es (esl1!(i - n)), gets_es (esl1!(Suc i - n))) \<in> guar2"
                                  using Suc_diff_Suc c1 g1 g3 g4 by fastforce
                                with g3 g4 have "(gets_es (esl ! i), gets_es (esl ! Suc i)) \<in> guar2" by simp

                                then show ?thesis using p5 by auto 
                              qed
                            qed
                          }
                          then show ?thesis by auto
                        qed

                        have b23 : "\<forall>i. i < length esl \<longrightarrow> ann_preserves_es (getspc_es (esl!i)) (gets_es (esl!i))"
                        proof-
                          {
                            fix i
                            assume c0: "i < length esl"
                            have "ann_preserves_es (getspc_es (esl!i)) (gets_es (esl!i))"
                            proof(cases "i < n")
                              assume d0: "i < n"
                              with b5 b5_1 b12_1 c0 have d1: "getspc_es (esl0 ! i) = EvtSeq (getspc_e (el ! i)) es"
                                by (metis Suc_leI e_eqv_einevtseq_def)
                              moreover have d2: " gets_es (esl0 ! i) = gets_e (el!i)"
                                by (metis Suc_leI b12_1 b5_1 d0 e_eqv_einevtseq_def)
                              from b20 c0 have "ann_preserves_e (getspc_e (el!i)) (gets_e (el!i))"
                                using b12_1 b5_1 d0 by auto
                              with d1 d2 d0 show ?thesis by (simp add: b5)
                            next
                              assume d0: "\<not> i < n"
                              then have d1: "esl ! i = esl1 ! (i - n)"
                                by (metis b5_1 b7 nth_append)
                              from c0 have d2: "i - n < length esl1"
                                by (simp add: add.commute add_diff_inverse_nat b6 d0 less_diff_conv)
                              from b21 have "esl1 \<in> preserves_es"
                                by (meson contra_subsetD es_validity_def le_inf_iff p1)
                              with d2 have "ann_preserves_es (getspc_es (esl1 ! (i - n))) (gets_es (esl1 ! (i - n)))"
                                by (simp add: preserves_es_def)
                              with d1 show ?thesis by simp
                            qed
                          }
                          then show ?thesis by auto
                        qed

                        with b22 show ?thesis by (simp add:commit_es_def preserves_es_def)
                      qed
                    }
                    then show ?thesis by auto
                  qed
                }
                then show ?thesis by auto
              qed

              then show ?thesis by (simp add: es_validity_def) 
            qed


primrec parse_es_cpts_i2 :: "('l,'k,'s) esconfs \<Rightarrow>('l,'k,'s) event set \<Rightarrow> 
                             (('l,'k,'s) esconfs) list \<Rightarrow> (('l,'k,'s) esconfs) list"
  where "parse_es_cpts_i2 [] es rlst = rlst" |
        "parse_es_cpts_i2 (x#xs) es rlst = 
            (if getspc_es x = EvtSys es \<and> length xs > 0 
                \<and> (getspc_es (xs!0) \<noteq> EvtSys es) then
               parse_es_cpts_i2 xs es (rlst@[[x]])
             else
               parse_es_cpts_i2 xs es (list_update rlst (length rlst - 1) (last rlst @ [x])) )"

lemma concat_list_lemma_take_n [rule_format]: 
  "\<lbrakk>esl = concat lst; i \<le> length lst\<rbrakk> \<Longrightarrow> 
      \<exists>k. k \<le> length esl \<and> take k esl = concat (take i lst)"
  proof -
    assume p0: "esl = concat lst"
      and  p1: "i \<le> length lst"
    then show ?thesis
      proof(induct i)
        case 0
        have "concat (take 0 lst) = take 0 esl" by simp
        then show ?case by auto
      next
        case (Suc ii)
        assume a0: "esl = concat lst \<Longrightarrow> ii \<le> length lst 
                    \<Longrightarrow> \<exists>k\<le>length esl. take k esl = concat (take ii lst)"
          and  a1: "esl = concat lst"
          and  a2: "Suc ii \<le> length lst"
        then have "\<exists>k\<le>length esl. take k esl = concat (take ii lst)"
          using Suc_leD by blast 
        then obtain k where a3: "k\<le>length esl \<and> take k esl = concat (take ii lst)"
          by auto
        from a2 have a4: "concat (take (Suc ii) lst) = concat (take ii lst) @ lst!ii"
          by (simp add: take_Suc_conv_app_nth)
        with a3 have "concat (take (Suc ii) lst) = take (k + length (lst!ii)) esl"
          by (metis Cons_nth_drop_Suc Suc_le_lessD a2 append_eq_conv_conj 
            append_take_drop_id concat.simps(2) concat_append p0 take_add) 
        then show ?case by (metis nat_le_linear take_all) 
      qed
  qed

lemma concat_list_lemma_take_n2 [rule_format]: 
  "\<lbrakk>esl = concat lst; i \<le> length lst\<rbrakk> \<Longrightarrow> 
      \<exists>k. k \<le> length esl \<and> k = length (concat (take i lst)) \<and> take k esl = concat (take i lst)"
  proof -
    assume p0: "esl = concat lst"
      and  p1: "i \<le> length lst"
    then show ?thesis
      proof(induct i)
        case 0
        have "concat (take 0 lst) = take 0 esl" by simp
        then show ?case by auto
      next
        case (Suc ii)
        assume a0: "esl = concat lst \<Longrightarrow> ii \<le> length lst 
                    \<Longrightarrow> \<exists>k\<le>length esl. k = length (concat (take ii lst)) 
                        \<and> take k esl = concat (take ii lst)"
          and  a1: "esl = concat lst"
          and  a2: "Suc ii \<le> length lst"
        then have "\<exists>k\<le>length esl. k = length (concat (take ii lst)) 
                      \<and> take k esl = concat (take ii lst)"
          using Suc_leD by blast 
        then obtain k where a3: "k\<le>length esl \<and> k = length (concat (take ii lst)) 
                                \<and> take k esl = concat (take ii lst)"
          by auto
        from a2 have a4: "concat (take (Suc ii) lst) = concat (take ii lst) @ lst!ii"
          by (simp add: take_Suc_conv_app_nth)
        with a3 have "concat (take (Suc ii) lst) = take (k + length (lst!ii)) esl"
          by (metis Cons_nth_drop_Suc Suc_le_lessD a2 append_eq_conv_conj 
            append_take_drop_id concat.simps(2) concat_append p0 take_add) 
        then show ?case by (metis a2 concat_list_lemma_take_n length_take min.absorb2 p0)
      qed
  qed

lemma concat_list_lemma [rule_format]: 
  "\<forall>esl lst. esl = concat lst \<and> (\<forall>i<length lst. length (lst!i) > 0)\<longrightarrow> 
        (\<forall>i. Suc i < length esl 
          \<longrightarrow> (\<exists>k j. Suc k < length lst \<and> Suc j < length (lst!k@[lst!(Suc k)!0]) 
                      \<and> esl!i = (lst!k@[lst!(Suc k)!0])!j \<and> esl!Suc i = (lst!k@[lst!(Suc k)!0])!Suc j
                  \<or> Suc k = length lst \<and> Suc j < length (lst!k) \<and> esl!i = lst!k!j \<and> esl!Suc i = lst!k!Suc j))"
  proof -
  {
    fix lst
    have "\<forall>esl. esl = concat lst \<and> (\<forall>i<length lst. length (lst!i) > 0)\<longrightarrow> 
        (\<forall>i. Suc i < length esl 
          \<longrightarrow> (\<exists>k j. Suc k < length lst \<and> Suc j < length (lst!k@[lst!(Suc k)!0]) 
                      \<and> esl!i = (lst!k@[lst!(Suc k)!0])!j \<and> esl!Suc i = (lst!k@[lst!(Suc k)!0])!Suc j
                  \<or> Suc k = length lst \<and> Suc j < length (lst!k) \<and> esl!i = lst!k!j \<and> esl!Suc i = lst!k!Suc j))"
      proof(induct lst)
        case Nil then show ?case by simp
      next
        case (Cons l lt)
        assume a0: "\<forall>esl. esl = concat lt \<and> (\<forall>i<length lt. 0 < length (lt ! i)) \<longrightarrow>
        (\<forall>i. Suc i < length esl \<longrightarrow>
             (\<exists>k j. Suc k < length lt \<and>
                    Suc j < length (lt ! k @ [lt ! Suc k ! 0]) \<and>
                    esl ! i = (lt ! k @ [lt ! Suc k ! 0]) ! j \<and> esl ! Suc i = (lt ! k @ [lt ! Suc k ! 0]) ! Suc j \<or>
                    Suc k = length lt \<and> Suc j < length (lt ! k) \<and> esl ! i = lt ! k ! j \<and> esl ! Suc i = lt ! k ! Suc j))"
        {
          fix esl
          assume b0: "esl = concat (l # lt)"
            and  b1: "\<forall>i<length (l # lt). 0 < length ((l # lt) ! i)"

          {
            fix i
            assume c0: "Suc i < length esl"
            then have "\<exists>k j. Suc k < length (l # lt) \<and>
                    Suc j < length ((l # lt) ! k @ [(l # lt) ! Suc k ! 0]) \<and>
                    esl ! i = ((l # lt) ! k @ [(l # lt) ! Suc k ! 0]) ! j \<and>
                    esl ! Suc i = ((l # lt) ! k @ [(l # lt) ! Suc k ! 0]) ! Suc j \<or>
                    Suc k = length (l # lt) \<and>
                    Suc j < length ((l # lt) ! k) \<and> esl ! i = (l # lt) ! k ! j \<and> esl ! Suc i = (l # lt) ! k ! Suc j"
              proof(cases "lt = []")
                assume d0: "lt = []"
                with b0 have "esl = l" by auto
                with b0 c0 have "Suc 0 = length (l # []) \<and>
                    Suc i < length ((l # []) ! 0) \<and> esl ! i = (l # []) ! 0 ! i \<and> esl ! Suc i = (l # []) ! 0 ! Suc i"
                    by simp
                with d0 show ?thesis by auto
              next
                assume d0: "lt \<noteq> []"
                then show ?thesis
                  proof(cases "Suc i < length (l@[(l # lt) ! Suc 0!0])")
                    assume e0: "Suc i < length (l@[(l # lt) ! Suc 0!0])"
                    with b0 b1 show ?thesis
                      by (smt Cons_nth_drop_Suc Suc_lessE Suc_lessI Suc_mono 
                        cancel_comm_monoid_add_class.diff_cancel concat.simps(2) 
                        d0 diff_Suc_1 drop_0 drop_Suc_Cons length_Cons length_append_singleton 
                        length_greater_0_conv nth_Cons_0 nth_append) 
                  next
                    assume e00: "\<not>(Suc i < length (l@[(l # lt) ! Suc 0!0]))"
                    then have e0: "Suc i \<ge> length (l@[(l # lt) ! Suc 0!0])" by simp
                    from b0 have "\<exists>esl1. esl = l@esl1 \<and> esl1 = concat lt" by simp
                    then obtain esl1 where e1: "esl = l@esl1 \<and> esl1 = concat lt" by auto
                    with a0 b1 have e2: "\<forall>i. Suc i < length esl1 \<longrightarrow>
                       (\<exists>k j. Suc k < length lt \<and>
                              Suc j < length (lt ! k @ [lt ! Suc k ! 0]) \<and>
                              esl1 ! i = (lt ! k @ [lt ! Suc k ! 0]) ! j \<and> esl1 ! Suc i = (lt ! k @ [lt ! Suc k ! 0]) ! Suc j \<or>
                              Suc k = length lt \<and> Suc j < length (lt ! k) \<and> esl1 ! i = lt ! k ! j \<and> esl1 ! Suc i = lt ! k ! Suc j)"
                      by auto
                    from c0 e0 e00 e1 have e3: "esl!i = esl1!(i-length l)"
                      by (simp add: length_append_singleton nth_append) 
                    from c0 e0 e00 e1 have e4: "esl!Suc i = esl1!(Suc i - length l)"
                      by (simp add: length_append_singleton less_Suc_eq nth_append)
                    from c0 e0 e00 e1 have e5: "Suc (i-length l) < length esl1"
                      using Suc_le_mono add.commute le_SucI length_append 
                      length_append_singleton less_diff_conv2 by auto 
                    with e2 have "\<exists>k j. Suc k < length lt \<and>
                              Suc j < length (lt ! k @ [lt ! Suc k ! 0]) \<and>
                              esl1 ! (i-length l) = (lt ! k @ [lt ! Suc k ! 0]) ! j \<and> esl1 ! Suc (i-length l) = (lt ! k @ [lt ! Suc k ! 0]) ! Suc j \<or>
                              Suc k = length lt \<and> Suc j < length (lt ! k) \<and> esl1 ! (i-length l) = lt ! k ! j \<and> esl1 ! Suc (i-length l) = lt ! k ! Suc j"
                      by auto
                    then obtain k and j where "Suc k < length lt \<and>
                              Suc j < length (lt ! k @ [lt ! Suc k ! 0]) \<and>
                              esl1 ! (i-length l) = (lt ! k @ [lt ! Suc k ! 0]) ! j \<and> esl1 ! Suc (i-length l) = (lt ! k @ [lt ! Suc k ! 0]) ! Suc j \<or>
                              Suc k = length lt \<and> Suc j < length (lt ! k) \<and> esl1 ! (i-length l) = lt ! k ! j \<and> esl1 ! Suc (i-length l) = lt ! k ! Suc j"
                      by auto
                    
                    with c0 e0 e1 show ?thesis
                      by (smt Suc_diff_le Suc_le_mono Suc_mono e3 e4 length_Cons 
                        length_append_singleton nat_neq_iff nth_Cons_Suc) 
                  qed
              qed
          }
        }
        then show ?case by auto
      qed
  }
  then show ?thesis by blast
  qed

lemma concat_list_lemma2 [rule_format]: 
  "\<forall>esl lst. esl = concat lst \<longrightarrow>
        (\<forall>i < length lst. (take (length (lst!i)) (drop (length (concat (take i lst))) esl) = lst ! i))"
  proof -
  {
    fix lst
    have "\<forall>esl. esl = concat lst \<longrightarrow>
        (\<forall>i < length lst. (take (length (lst!i)) (drop (length (concat (take i lst))) esl) = lst ! i))"
      proof(induct lst)
        case Nil then show ?case by simp
      next
        case (Cons l lt)
        assume a0[rule_format]: " \<forall>esl. esl = concat lt \<longrightarrow> 
                            (\<forall>i<length lt. take (length (lt ! i)) (drop (length (concat (take i lt))) esl) = lt ! i)"
        {
          fix esl
          assume b0: "esl = concat (l # lt)"
          let ?esl = "concat lt"
          from b0 have b1: "esl = l @ ?esl" by auto
          {
            fix i
            assume c0: "i<length (l # lt)"
            have "take (length ((l # lt) ! i)) (drop (length (concat (take i (l # lt)))) esl) = (l # lt) ! i"
              proof(cases "i = 0")
                assume d0: "i = 0"
                then show ?thesis by (simp add: b0 d0)
              next
                assume d0: "i \<noteq> 0"
                with c0 have "take (length (lt ! (i-1))) (drop (length (concat (take (i-1) lt))) ?esl) = lt ! (i-1)"
                  using a0[of ?esl "i-1"] by (metis One_nat_def leI less_Suc0 less_diff_conv2 list.size(4)) 
                moreover
                from d0 c0 have "lt ! (i - 1) = (l # lt) ! i" by (simp add: nth_Cons')
                moreover
                from b0 b1 d0 c0 have "drop (length (concat (take (i-1) lt))) ?esl 
                                = drop (length (concat (take i (l # lt)))) esl"
                  by (metis append_eq_conv_conj append_take_drop_id concat_append drop_Cons') 
                ultimately show ?thesis by simp
              qed
          }
        }
        then show ?case by auto
      qed
  }
  then show ?thesis by auto
  qed
        
lemma concat_list_lemma3 [rule_format]: 
  "\<lbrakk>esl = concat lst; i < length lst; length (lst!i) > 1\<rbrakk> \<Longrightarrow> 
      \<exists>k j. k = length (concat (take i lst)) \<and> j = length (concat (take (Suc i) lst)) \<and> 
            k \<le> length esl \<and> j \<le> length esl \<and> k < j \<and> drop k (take j esl) = lst ! i"
  proof -
    assume p0: "esl = concat lst"
      and  p1: "i < length lst"
      and  p2: "length (lst!i) > 1"
    then have a1: "take (length (lst!i)) (drop (length (concat (take i lst))) esl) = lst ! i"
      using concat_list_lemma2 by auto
    let ?k = "length (concat (take i lst))"
    let ?j = "length (concat (take (Suc i) lst))"
    from p0 p1 p2 have a10: "drop ?k (take ?j esl) = lst ! i"
      proof -
        have "length (lst ! i) + length (concat (take i lst)) = length (concat (take (Suc i) lst))"
          by (simp add: p1 take_Suc_conv_app_nth)
        then show ?thesis
          by (metis (full_types) a1 take_drop)
      qed 
    have a2: "?j - ?k = length (lst!i)" by (simp add: p1 take_Suc_conv_app_nth)
    have a3: "?j = ?k + length (lst!i)" by (simp add: p1 take_Suc_conv_app_nth)
    moreover
    from p0 p1 have "?k \<le> length esl"
      by (metis append_eq_conv_conj append_take_drop_id concat_append nat_le_linear take_all) 
    moreover
    from p0 p1 have "?j \<le> length esl"
      by (metis append_eq_conv_conj append_take_drop_id concat_append nat_le_linear take_all)
    moreover
    from a3 p2 have "?k < ?j" using a2 diff_is_0_eq leI not_less0 by linarith
    ultimately have "?k \<le> length esl \<and> ?j \<le> length esl \<and> ?k < ?j \<and> drop ?k (take ?j esl) = lst ! i"
      using a10 by simp
    then show ?thesis by blast
  qed

lemma concat_list_lemma_withnextfst: 
  "\<lbrakk>esl = concat lst; Suc i < length lst; length (lst!Suc i) > 0\<rbrakk> \<Longrightarrow> 
      \<exists>k j. k \<le> length esl \<and> j \<le> length esl \<and> k < j \<and> drop k (take j esl) = lst!i @ [lst!Suc i!0]"
  proof -
    assume p0: "esl = concat lst"
      and  p1: "Suc i < length lst"
      and  p2: "length (lst!Suc i) > 0"
    then have "\<exists>k. k \<le> length esl \<and> take k esl = concat (take (Suc (Suc i)) lst)"
      using concat_list_lemma_take_n[of esl lst "Suc (Suc i)"] by simp
    then obtain k where a1: "k \<le> length esl \<and> take k esl = concat (take (Suc (Suc i)) lst)" by auto

    from p0 p1 p2 have "\<exists>k. k \<le> length esl \<and> take k esl = concat (take (Suc i) lst)" 
      using concat_list_lemma_take_n[of esl lst "Suc i"] by simp 
    then obtain k2 where a2: "k2 \<le> length esl \<and> take k2 esl = concat (take (Suc i) lst)" by auto

    with p0 have a5: "concat (take (Suc i) lst) @ [lst!Suc i!0] = take (Suc k2) esl"
      by (metis (no_types, lifting) Cons_nth_drop_Suc append_eq_conv_conj 
        append_take_drop_id concat_list_lemma2 drop_eq_Nil length_greater_0_conv 
        less_eq_Suc_le not_less_eq_eq nth_Cons_0 nth_take p1 p2 take_Suc_conv_app_nth take_eq_Nil)
    then have a3: "concat (take i lst)@lst!i@[lst!Suc i!0] = take (Suc k2) esl"
      by (metis (no_types, lifting) Suc_lessD append_Nil2 append_eq_appendI 
        concat.simps(1) concat.simps(2) concat_append p1 take_Suc_conv_app_nth) 
    
    from p0 p1 p2 have "\<exists>k. k \<le> length esl \<and> take k esl = concat (take i lst)" 
      using concat_list_lemma_take_n[of esl lst i] by simp 
    then obtain k1 where a4: "k1 \<le> length esl \<and> take k1 esl = concat (take i lst)" by auto
    
    from a3 a4 have "drop k1 (take (Suc k2) esl) = lst!i@[lst!Suc i!0]"
      by (metis append_eq_conv_conj length_take min.absorb2) 
    then show ?thesis using a2 a4 a5
      by (metis Nil_is_append_conv drop_eq_Nil leI length_take 
        min.absorb2 nat_le_linear not_Cons_self2 take_all)
  qed

lemma concat_list_lemma_withnextfst2: 
  "\<lbrakk>esl = concat lst; Suc i < length lst; length (lst!Suc i) > 0\<rbrakk> \<Longrightarrow> 
      \<exists>k j. k = length (concat (take i lst)) \<and> j = Suc (length (concat (take (Suc i) lst))) \<and>
      k \<le> length esl \<and> j \<le> length esl \<and> k < j \<and> drop k (take j esl) = lst!i @ [lst!Suc i!0]"
  proof -
    assume p0: "esl = concat lst"
      and  p1: "Suc i < length lst"
      and  p2: "length (lst!Suc i) > 0"
    then have "\<exists>k. k \<le> length esl \<and> k = length (concat (take (Suc (Suc i)) lst)) 
      \<and> take k esl = concat (take (Suc (Suc i)) lst)"
      using concat_list_lemma_take_n2[of esl lst "Suc (Suc i)"] by simp
    then obtain k where a1: "k \<le> length esl \<and> k = length (concat (take (Suc (Suc i)) lst)) 
         \<and> take k esl = concat (take (Suc (Suc i)) lst)" by auto

    from p0 p1 p2 have "\<exists>k. k \<le> length esl \<and> k = length (concat (take (Suc i) lst)) 
      \<and> take k esl = concat (take (Suc i) lst)" 
      using concat_list_lemma_take_n2[of esl lst "Suc i"] by simp 
    then obtain k2 where a2: "k2 \<le> length esl \<and> k2 = length (concat (take (Suc i) lst)) 
      \<and> take k2 esl = concat (take (Suc i) lst)" by auto

    with p0 have a5: "concat (take (Suc i) lst) @ [lst!Suc i!0] = take (Suc k2) esl"
      by (metis (no_types, lifting) Cons_nth_drop_Suc append_eq_conv_conj 
        append_take_drop_id concat_list_lemma2 drop_eq_Nil length_greater_0_conv 
        less_eq_Suc_le not_less_eq_eq nth_Cons_0 nth_take p1 p2 take_Suc_conv_app_nth take_eq_Nil)
    then have a3: "concat (take i lst)@lst!i@[lst!Suc i!0] = take (Suc k2) esl"
      by (metis (no_types, lifting) Suc_lessD append_Nil2 append_eq_appendI 
        concat.simps(1) concat.simps(2) concat_append p1 take_Suc_conv_app_nth)

    from p0 p1 p2 have "\<exists>k. k \<le> length esl \<and> k = length (concat (take i lst)) 
      \<and> take k esl = concat (take i lst)" 
      using concat_list_lemma_take_n2[of esl lst i] by simp 
    then obtain k1 where a4: "k1 \<le> length esl \<and> k1 = length (concat (take i lst)) 
      \<and> take k1 esl = concat (take i lst)" by auto

    from a3 a4 have "drop k1 (take (Suc k2) esl) = lst!i@[lst!Suc i!0]"
      by (metis append_eq_conv_conj length_take) 

    with a2 a4 a5 show ?thesis by (metis (no_types, lifting) Nil_is_append_conv 
        drop_eq_Nil leI length_append_singleton less_or_eq_imp_le not_Cons_self2 take_all) 
  qed

lemma concat_list_lemma_withnextfst3: 
  "\<lbrakk>esl = concat lst; Suc i < length lst; length (lst!Suc i) > 1\<rbrakk> \<Longrightarrow> 
      \<exists>k j. k = length (concat (take i lst)) \<and> j = Suc (length (concat (take (Suc i) lst))) \<and>
      k \<le> length esl \<and> j < length esl \<and> k < j \<and> drop k (take j esl) = lst!i @ [lst!Suc i!0]"
  proof -
    assume p0: "esl = concat lst"
      and  p1: "Suc i < length lst"
      and  p2: "length (lst!Suc i) > 1"
    then have "\<exists>k. k \<le> length esl \<and> k = length (concat (take (Suc (Suc i)) lst)) 
      \<and> take k esl = concat (take (Suc (Suc i)) lst)"
      using concat_list_lemma_take_n2[of esl lst "Suc (Suc i)"] by simp
    then obtain k where a1: "k \<le> length esl \<and> k = length (concat (take (Suc (Suc i)) lst)) 
         \<and> take k esl = concat (take (Suc (Suc i)) lst)" by auto

    from p0 p1 p2 have "\<exists>k. k \<le> length esl \<and> k = length (concat (take (Suc i) lst)) 
      \<and> take k esl = concat (take (Suc i) lst)" 
      using concat_list_lemma_take_n2[of esl lst "Suc i"] by simp 
    then obtain k2 where a2: "k2 \<le> length esl \<and> k2 = length (concat (take (Suc i) lst)) 
      \<and> take k2 esl = concat (take (Suc i) lst)" by auto

    with p0 have a5: "concat (take (Suc i) lst) @ [lst!Suc i!0] = take (Suc k2) esl"
      by (metis One_nat_def Suc_lessD Suc_n_not_le_n append_Nil2 append_take_drop_id 
        concat_list_lemma2 concat_list_lemma_withnextfst2 hd_conv_nth 
        le_neq_implies_less nth_take p1 p2 take_hd_drop)
      
    then have a3: "concat (take i lst)@lst!i@[lst!Suc i!0] = take (Suc k2) esl"
      by (metis (no_types, lifting) Suc_lessD append_Nil2 append_eq_appendI 
        concat.simps(1) concat.simps(2) concat_append p1 take_Suc_conv_app_nth)

    from p0 p1 p2 have "\<exists>k. k \<le> length esl \<and> k = length (concat (take i lst)) 
      \<and> take k esl = concat (take i lst)" 
      using concat_list_lemma_take_n2[of esl lst i] by simp 
    then obtain k1 where a4: "k1 \<le> length esl \<and> k1 = length (concat (take i lst)) 
      \<and> take k1 esl = concat (take i lst)" by auto

    from a3 a4 have "drop k1 (take (Suc k2) esl) = lst!i@[lst!Suc i!0]"
      by (metis append_eq_conv_conj length_take) 

    with a2 a4 a5 show ?thesis
      by (smt One_nat_def append_eq_conv_conj concat_list_lemma2 concat_list_lemma_withnextfst2 
        leI length_Cons less_trans list.size(3) nat_neq_iff p0 p1 p2 take_all zero_less_one) 
  qed

lemma parse_es_cpts_i2_concat: 
      "\<forall>esl rlst es. esl\<in>cpts_es \<and> (rlst::(('l,'k,'s) esconfs) list) \<noteq> [] 
                      \<longrightarrow> concat (parse_es_cpts_i2 esl es rlst) = concat rlst @ esl"
  proof -
  {
    fix esl
    have "\<forall>rlst es. esl\<in>cpts_es \<and> (rlst::(('l,'k,'s) esconfs) list) \<noteq> [] \<longrightarrow> concat (parse_es_cpts_i2 esl es rlst) = concat rlst @ esl"
      proof(induct esl)
        case Nil show ?case by simp
      next
        case (Cons esc esl1)
        assume a0: "\<forall>rlst es. esl1 \<in> cpts_es \<and> rlst \<noteq> [] \<longrightarrow> concat (parse_es_cpts_i2 esl1 es rlst) = concat rlst @ esl1"
        then show ?case 
          proof -
          {
            fix rlst es
            assume b0: "esc # esl1 \<in> cpts_es \<and> (rlst::(('l,'k,'s) esconfs) list) \<noteq> []"
            have "concat (parse_es_cpts_i2 (esc # esl1) es rlst) = concat rlst @ (esc # esl1)"
              proof(cases "getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es")
                assume c0: "getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es"
                then have c1: "parse_es_cpts_i2 (esc # esl1) es rlst = parse_es_cpts_i2 esl1 es (rlst@[[esc]])"
                  by simp
                from b0 have c2: "rlst@[[esc]] \<noteq> []" by simp
                from b0 c0 have "esl1 \<in> cpts_es" using cpts_es_dropi by force
                with a0 c2 have c3: "concat (parse_es_cpts_i2 esl1 es (rlst@[[esc]])) =  concat (rlst@[[esc]]) @ esl1" by simp
                have "concat rlst @ (esc # esl1) = concat (rlst@[[esc]]) @ esl1" by auto
                with c1 c3 show ?thesis by presburger 
              next
                assume c0: "\<not>(getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es)"
                then have c1: "parse_es_cpts_i2 (esc # esl1) es rlst = 
                                parse_es_cpts_i2 esl1 es (list_update rlst (length rlst - 1) (last rlst @ [esc]))" by auto
                show ?thesis
                  proof(cases "esl1 = []")
                    assume d0: "esl1 = []"
                    then have d1: "parse_es_cpts_i2 (esc # []) es rlst = 
                                parse_es_cpts_i2 [] es (list_update rlst (length rlst - 1) (last rlst @ [esc]))" by simp
                    have d2: "parse_es_cpts_i2 [] es (list_update rlst (length rlst - 1) (last rlst @ [esc])) = 
                            list_update rlst (length rlst - 1) (last rlst @ [esc])" by simp
                    from b0 have "concat (list_update rlst (length rlst - 1) (last rlst @ [esc])) = concat rlst @ esc # []"
                      by (metis (no_types, lifting) append_assoc append_butlast_last_id 
                            append_self_conv concat.simps(2) concat_append length_butlast list_update_length) 
                    with d0 d1 d2 show ?thesis by simp
                  next
                    assume d0: "\<not>(esl1 = [])"
                    then have "length esl1 > 0" by simp
                    with b0 have d1: "esl1 \<in> cpts_es" using cpts_es_dropi by force
                    from b0 have "list_update rlst (length rlst - 1) (last rlst @ [esc]) \<noteq> []" by simp
                    with a0 d1 have d2: "concat (parse_es_cpts_i2 esl1 es (list_update rlst (length rlst - 1) (last rlst @ [esc]))) =
                                    concat (list_update rlst (length rlst - 1) (last rlst @ [esc])) @ esl1" by auto
                    from b0 have d3: "concat rlst @ (esc # esl1) = concat (list_update rlst (length rlst - 1) (last rlst @ [esc])) @ esl1"
                      by (metis (no_types, lifting) Cons_eq_appendI append_assoc append_butlast_last_id 
                            concat.simps(2) concat_append length_butlast list_update_length self_append_conv2)
                    
                    with c1 d2 show ?thesis by simp
                  qed
              qed
          }
          then show ?thesis by auto
          qed
      qed
  }
  then show ?thesis by auto
  qed

lemma parse_es_cpts_i2_concat1: 
      "esl\<in>cpts_es \<Longrightarrow> concat (parse_es_cpts_i2 esl es [[]]) = esl"
  by (simp add: parse_es_cpts_i2_concat)

lemma parse_es_cpts_i2_lst0:
    "\<forall>esl l1 l2 es. esl\<in>cpts_es \<and> (l2::(('l,'k,'s) esconfs) list) \<noteq> [] 
                    \<longrightarrow> parse_es_cpts_i2 esl es (l1@l2) = l1@(parse_es_cpts_i2 esl es l2)"
  proof -
  {
    fix esl
    have "\<forall>l1 l2 es. esl\<in>cpts_es \<and> (l2::(('l,'k,'s) esconfs) list) \<noteq> [] 
                      \<longrightarrow> parse_es_cpts_i2 esl es (l1@l2) = l1@(parse_es_cpts_i2 esl es l2)"
      proof(induct esl)
        case Nil show ?case by simp
      next
        case (Cons esc esl1)
        assume a0: "\<forall>l1 l2 es. esl1 \<in> cpts_es \<and> (l2::(('l,'k,'s) esconfs) list) \<noteq> [] 
                                \<longrightarrow> parse_es_cpts_i2 esl1 es (l1 @l2) = l1 @ parse_es_cpts_i2 esl1 es l2"
        show ?case 
          proof -
          {
            fix l1 l2 es
            assume b0: "esc # esl1 \<in> cpts_es"
              and  b1: "(l2::(('l,'k,'s) esconfs) list) \<noteq> []"
            have "parse_es_cpts_i2 (esc # esl1) es (l1 @ l2) = l1 @ parse_es_cpts_i2 (esc # esl1) es l2"
              proof(cases "esl1 = []")
                assume c0: "esl1 = []"
                then have "parse_es_cpts_i2 (esc # []) es (l1 @ l2) =
                            parse_es_cpts_i2 [] es (list_update (l1 @ l2) (length (l1 @ l2) - 1) (last (l1 @ l2) @ [esc]))"
                  by simp 
                then have c1: "parse_es_cpts_i2 (esc # []) es (l1 @ l2) = 
                            list_update (l1 @ l2) (length (l1 @ l2) - 1) (last (l1 @ l2) @ [esc])" 
                  by simp
                with b1 have c2: "parse_es_cpts_i2 (esc # []) es (l1 @ l2) = 
                                l1 @ (list_update l2 (length l2 - 1) (last l2 @ [esc]))"
                   by (smt append1_eq_conv append_assoc append_butlast_last_id 
                      append_is_Nil_conv length_butlast list_update_length)
                have "l1 @ parse_es_cpts_i2 (esc # []) es l2 = 
                        l1 @ parse_es_cpts_i2 [] es (list_update l2 (length l2 - 1) (last l2 @ [esc]))" by simp
                then have "l1 @ parse_es_cpts_i2 (esc # []) es l2 = 
                            l1 @ (list_update l2 (length l2 - 1) (last l2 @ [esc]))" by simp
                with c0 c2 show ?thesis by simp
              next
                assume c0: "\<not>(esl1 = [])" 
                with b0 have c1: "esl1 \<in> cpts_es" using cpts_es_dropi by force
                show ?thesis
                  proof(cases "getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es")
                    assume d0: "getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es"
                    then have d1:"parse_es_cpts_i2 (esc # esl1) es (l1 @ l2) =
                                    parse_es_cpts_i2 esl1 es (l1 @ l2@[[esc]])" by simp
                    from a0 c1 have d2: "parse_es_cpts_i2 esl1 es (l1 @ l2@[[esc]]) =
                                    l1 @ parse_es_cpts_i2 esl1 es (l2@[[esc]])" by simp
                    from d0 have d3: "l1 @ parse_es_cpts_i2 (esc # esl1) es l2 =
                                    l1 @ parse_es_cpts_i2 esl1 es (l2@[[esc]])" by simp
                    with d1 d2 show ?thesis by simp
                  next
                    assume d0: "\<not>(getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es)"
                    then have d1: "parse_es_cpts_i2 (esc # esl1) es (l1 @ l2) =
                                    parse_es_cpts_i2 esl1 es (list_update (l1 @ l2) (length (l1 @ l2) - 1) 
                                                                (last (l1 @ l2) @ [esc]))" by auto
                    with b1 have d2: "parse_es_cpts_i2 (esc # esl1) es (l1 @ l2) =
                                    parse_es_cpts_i2 esl1 es (l1 @ list_update l2 (length l2 - 1) (last l2 @ [esc]) )"
                      by (smt append1_eq_conv append_assoc append_butlast_last_id 
                              append_is_Nil_conv length_butlast list_update_length)
                    with a0 b1 c1 have d3: "parse_es_cpts_i2 (esc # esl1) es (l1 @ l2) =
                                    l1 @ parse_es_cpts_i2 esl1 es (list_update l2 (length l2 - 1) (last l2 @ [esc]) )"
                        by auto
                    from d0 have "l1 @ parse_es_cpts_i2 (esc # esl1) es l2 = 
                                  l1 @ parse_es_cpts_i2 esl1 es (list_update l2 (length l2 - 1) (last l2 @ [esc]))" 
                        by auto
                    with d3 show ?thesis by simp
                  qed
              qed
          }
          then show ?thesis by auto
          qed
      qed
  }
  then show ?thesis by auto
  qed

lemma parse_es_cpts_i2_lst:
    "\<forall>esl l1 l2 es. esl\<in>cpts_es \<and> (l2::(('l,'k,'s) esconfs) list) \<noteq> [] 
                    \<longrightarrow> parse_es_cpts_i2 esl es ([l1]@l2) = [l1]@(parse_es_cpts_i2 esl es l2)"
  using parse_es_cpts_i2_lst0 by blast


lemma parse_es_cpts_i2_fst: "\<forall>esl elst rlst es l. esl\<in>cpts_es \<and> rlst = [l] \<and> elst = parse_es_cpts_i2 esl es rlst 
                                                  \<longrightarrow> (\<exists>i\<le>length (elst!0). take i (elst!0) = l)" 
  proof -
  {
    fix esl
    have "\<forall>elst rlst es l. esl\<in>cpts_es \<and> rlst = [l] \<and> elst = parse_es_cpts_i2 esl es rlst 
                            \<longrightarrow> (\<exists>i\<le>length (elst!0). take i (elst!0) = l)"
      proof(induct esl)
        case Nil show ?case by simp
      next
        case (Cons esc esl1)
        assume a0: "\<forall>elst rlst es l. esl1 \<in> cpts_es \<and> rlst = [l] \<and> elst = parse_es_cpts_i2 esl1 es rlst 
                                    \<longrightarrow> (\<exists>i\<le>length (elst ! 0). take i (elst ! 0) = l)"
        show ?case
          proof -
          {
            fix elst rlst es l
            assume b0: "esc # esl1 \<in> cpts_es"
              and  b1: "rlst = [l]"
              and  b2: "elst = parse_es_cpts_i2 (esc # esl1) es rlst"
            have "\<exists>i\<le>length (elst ! 0). take i (elst ! 0) = l"
              proof(cases "esl1 = []")
                assume c0: "esl1 = []"
                with b2 have c1: "elst = parse_es_cpts_i2 [] es (list_update rlst (length rlst - 1) (last rlst @ [esc]))"
                  by simp
                then have "elst = list_update rlst (length rlst - 1) (last rlst @ [esc])" by simp
                with b1 have c2: "elst = [l@[esc]]" by simp
                then show ?thesis by (metis butlast_conv_take butlast_snoc linear nth_Cons_0 take_all) 
              next
                assume c0: "\<not>(esl1 = [])"
                with b0 have c1: "esl1 \<in> cpts_es" using cpts_es_dropi by force
                from c0 obtain esl2 and ec1 where c2: "esl1 = ec1 # esl2"
                  by (meson neq_Nil_conv) 
                show ?thesis 
                  proof(cases "getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es")
                    assume d0: "getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es"
                    with c2 have d01: "getspc_es ec1 \<noteq> EvtSys es" by simp
                    from d0 have d1: "parse_es_cpts_i2 (esc # esl1) es rlst = parse_es_cpts_i2 esl1 es (rlst@[[esc]])"
                      by simp
                    with b1 b2 have d2: "elst = parse_es_cpts_i2 esl1 es ([l]@[[esc]])" by simp
                    from c1 have "parse_es_cpts_i2 esl1 es ([l]@[[esc]]) = [l]@parse_es_cpts_i2 esl1 es ([[esc]])"
                      using parse_es_cpts_i2_lst by auto
                    with d2 have "elst = [l] @ parse_es_cpts_i2 esl1 es ([[esc]])" by simp
                    then show ?thesis by auto
                  next
                    assume d0: "\<not>(getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es)"
                    then have d1: "parse_es_cpts_i2 (esc # esl1) es rlst = 
                                parse_es_cpts_i2 esl1 es (list_update rlst (length rlst - 1) (last rlst @ [esc]))" by auto
                    with b2 have d2: "elst = parse_es_cpts_i2 esl1 es (list_update rlst (length rlst - 1) (last rlst @ [esc]))"
                      by simp
                    with b1 have "elst = parse_es_cpts_i2 esl1 es ([l @ [esc]])" by simp
                    with a0 c1 have "\<exists>i\<le>length (elst ! 0). take i (elst ! 0) = l @ [esc]" by simp
                    then obtain i where "i\<le>length (elst ! 0) \<and> take i (elst ! 0) = l @ [esc]" by auto
                    then show ?thesis by (metis (no_types, lifting) butlast_snoc butlast_take diff_le_self dual_order.trans) 
                  qed
              qed
          }
          then show ?thesis by auto
          qed
      qed
  }
  then show ?thesis by blast
  qed


lemma parse_es_cpts_i2_start_withlen [simp]:
    "\<forall>esl elst rlst es l. esl\<in>cpts_es \<and> rlst \<noteq> [] \<and> elst = parse_es_cpts_i2 esl es rlst \<longrightarrow>
                        (\<forall>i. i \<ge> length rlst \<and> i < length elst \<longrightarrow> 
                            length (elst!i) \<ge> 2 \<and> getspc_es (elst!i!0) = EvtSys es \<and> getspc_es (elst!i!1) \<noteq> EvtSys es)"
  proof -
  {
    fix esl
    have "\<forall>elst rlst es l. esl\<in>cpts_es \<and> rlst \<noteq> [] \<and> elst = parse_es_cpts_i2 esl es rlst \<longrightarrow>
                        (\<forall>i. i \<ge> length rlst \<and> i < length elst \<longrightarrow> 
                            length (elst!i) \<ge> 2 \<and> getspc_es (elst!i!0) = EvtSys es \<and> getspc_es (elst!i!1) \<noteq> EvtSys es)"
      proof(induct esl)
        case Nil show ?case by simp
      next
        case (Cons esc esl1)
        assume a0: "\<forall>elst rlst es l. esl1 \<in> cpts_es \<and> rlst \<noteq> [] \<and> elst = parse_es_cpts_i2 esl1 es rlst \<longrightarrow>
                                    (\<forall>i. i \<ge> length rlst \<and> i < length elst \<longrightarrow> 
                                         length (elst!i) \<ge> 2 \<and> getspc_es (elst ! i ! 0) = EvtSys es 
                                          \<and> getspc_es (elst ! i ! 1) \<noteq> EvtSys es)"
        then show ?case 
          proof -
          {
            fix elst rlst es l
            assume b0: "esc # esl1 \<in> cpts_es"
              and  b1: "rlst \<noteq> []"
              and  b2: "elst = parse_es_cpts_i2 (esc # esl1) es rlst"
            have "\<forall>i. i \<ge> length rlst \<and> i < length elst \<longrightarrow> length (elst!i) \<ge> 2 \<and> getspc_es (elst ! i ! 0) = EvtSys es 
                                                \<and> getspc_es (elst ! i ! 1) \<noteq> EvtSys es"
              proof(cases "esl1 = []")
                assume c0: "esl1 = []"
                then have c1: "parse_es_cpts_i2 (esc # []) es rlst = 
                            parse_es_cpts_i2 [] es (list_update rlst (length rlst - 1) (last rlst @ [esc]))" by simp
                have c2: "parse_es_cpts_i2 [] es (list_update rlst (length rlst - 1) (last rlst @ [esc]))
                      = list_update rlst (length rlst - 1) (last rlst @ [esc])" by simp
                with b2 c0 c1 have "elst = list_update rlst (length rlst - 1) (last rlst @ [esc])" by simp
                with b1 show ?thesis by auto
              next
                assume c0: "\<not>(esl1 = [])"
                with b0 have c1: "esl1 \<in> cpts_es" using cpts_es_dropi by force
                from c0 obtain esl2 and ec1 where c2: "esl1 = ec1 # esl2"
                  by (meson neq_Nil_conv) 
                show ?thesis
                  proof(cases "getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es")
                    assume d0: "getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es"
                    with c2 have d01: "getspc_es ec1 \<noteq> EvtSys es" by simp
                    from d0 have d1: "parse_es_cpts_i2 (esc # esl1) es rlst = parse_es_cpts_i2 esl1 es (rlst@[[esc]])"
                      by simp
                    with b1 b2 have d2: "elst = parse_es_cpts_i2 esl1 es (rlst@[[esc]])" by simp
                    from c1 have d4: "parse_es_cpts_i2 esl1 es (rlst@[[esc]]) = rlst@parse_es_cpts_i2 esl1 es ([[esc]])"
                      using parse_es_cpts_i2_lst0 by auto
                    with d2 have d3: "elst = rlst @ parse_es_cpts_i2 esl1 es ([[esc]])" by simp
                    show ?thesis
                      proof(cases "esl2 = []")
                        assume e0: "esl2 = []"
                        with c2 have e1: "elst = rlst @ parse_es_cpts_i2 [] es 
                                        (list_update [[esc]] (length [[esc]] - 1) (last [[esc]] @ [ec1]))"
                           using b2 d1 by auto 
                        then have "elst = rlst @ (list_update [[esc]] (length [[esc]] - 1) (last [[esc]] @ [ec1]))"
                          by simp
                        then have "elst = rlst @ ([[esc] @ [ec1]])" by simp
                        with d0 d01 show ?thesis using leD le_eq_less_or_eq by auto
                      next
                        assume e0: "\<not>(esl2 = [])"
                        
                        let ?elst2 = "parse_es_cpts_i2 esl1 es ([[esc]])"
                        from a0 c1 have e1: "\<forall>i. i \<ge> 1 \<and> i < length ?elst2 \<longrightarrow> 
                                             length (?elst2!i) \<ge> 2 \<and> getspc_es (?elst2 ! i ! 0) = EvtSys es 
                                             \<and> getspc_es (?elst2 ! i ! 1) \<noteq> EvtSys es"
                           by (metis One_nat_def length_Cons list.distinct(2) list.size(3)) 
                           
                        from c2 d01 d3 have "elst = rlst @ parse_es_cpts_i2 esl2 es 
                                                      (list_update [[esc]] (length [[esc]] - 1) (last [[esc]] @ [ec1]))" by simp
                        then have e2: "elst = rlst @ parse_es_cpts_i2 esl2 es [[esc]@[ec1]]" by simp
                        with d3 have e3: "?elst2 = parse_es_cpts_i2 esl2 es [[esc]@[ec1]]" by simp
                        from c1 c2 e0 have "esl2\<in>cpts_es" using cpts_es_dropi by force
                        with e3 have e4: "\<exists>i\<le>length (?elst2!0). take i (?elst2!0) = [esc]@[ec1]" 
                          using parse_es_cpts_i2_fst by blast
                        with d0 d01 e1 e2 e3 show ?thesis
                          proof -
                          {
                            fix i
                            assume f0: "length rlst \<le> i \<and> i < length elst"
                            have "length (elst ! i) \<ge> 2 \<and> getspc_es (elst ! i ! 0) = EvtSys es 
                                    \<and> getspc_es (elst ! i ! 1) \<noteq> EvtSys es"
                              proof(cases "length rlst = i")
                                assume g0: "length rlst = i"
                                then have "elst ! i = ?elst2!0" by (simp add: e2 e3 nth_append) 
                                with e4 show ?thesis
                                  by (metis (no_types, lifting) One_nat_def Suc_1 butlast_snoc 
                                      butlast_take c2 d0 diff_Suc_1 length_Cons length_append_singleton 
                                      length_take lessI list.size(3) min.absorb2 nth_Cons_0 
                                      nth_append_length nth_take)  
                              next
                                assume g0: "\<not> (length rlst = i)"
                                with f0 have "length rlst < i \<and> i < length elst" by simp
                                with e1 show ?thesis by (metis Nil_is_append_conv Suc_leI a0 b1 
                                    c1 d4 e2 e3 length_append_singleton) 
                              qed
                          }
                          then show ?thesis by auto
                          qed
                      qed
                  next
                    assume d0: "\<not>(getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es)"
                    then have d1: "parse_es_cpts_i2 (esc # esl1) es rlst = 
                                parse_es_cpts_i2 esl1 es (list_update rlst (length rlst - 1) (last rlst @ [esc]))" by auto
                    with b2 have d2: "elst = parse_es_cpts_i2 esl1 es (list_update rlst (length rlst - 1) (last rlst @ [esc]))"
                      by simp
                    with a0 c1 show ?thesis using b1 by (metis length_list_update list_update_nonempty) 
                  qed
              qed
          }
          then show ?thesis by blast
          qed
      qed
  }
  then show ?thesis by blast
qed

lemma parse_es_cpts_i2_start_withlen0 [simp]:
    "\<lbrakk>esl\<in>cpts_es; rlst \<noteq> []; elst = parse_es_cpts_i2 esl es rlst\<rbrakk> \<Longrightarrow>
          \<forall>i. i \<ge> length rlst \<and> i < length elst \<longrightarrow> length (elst!i) \<ge> 2 
            \<and> getspc_es (elst!i!0) = EvtSys es \<and> getspc_es (elst!i!1) \<noteq> EvtSys es"
  using parse_es_cpts_i2_start_withlen by fastforce

lemma parse_es_cpts_i2_fstempty: "\<lbrakk>esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs; esl\<in>cpts_es;
        rlst = parse_es_cpts_i2 esl es [[]]\<rbrakk> \<Longrightarrow> rlst!0 =[]"
  proof -
    assume p0: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p1: "esl\<in>cpts_es"
      and  p2: "rlst = parse_es_cpts_i2 esl es [[]]"
    then have "rlst = parse_es_cpts_i2 ((EvtSeq e (EvtSys es), s1,x1) # xs) es ([[]]@[[(EvtSys es, s, x)]])"
      by (simp add:getspc_es_def)
    moreover from p0 p1 have "(EvtSeq e (EvtSys es), s1,x1) # xs \<in> cpts_es" 
      using cpts_es_dropi by force
    ultimately have "rlst = [[]]@ parse_es_cpts_i2 ((EvtSeq e (EvtSys es), s1,x1) # xs) es ([[(EvtSys es, s, x)]])"
      using parse_es_cpts_i2_lst0 by blast
    then show ?thesis by simp
  qed


lemma parse_es_cpts_i2_concat3: "\<lbrakk>esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs; esl\<in>cpts_es;
        rlst = parse_es_cpts_i2 esl es [[]]\<rbrakk> \<Longrightarrow> concat (tl rlst) = esl"
  using parse_es_cpts_i2_concat1 parse_es_cpts_i2_fstempty 
   by (smt append_Nil concat.simps(1) concat.simps(2) hd_Cons_tl list.distinct(1) nth_Cons_0)

lemma parse_es_cpts_i2_noent_mid0:
    "\<forall>esl elst l es. esl\<in>cpts_es \<and> elst = parse_es_cpts_i2 esl es [l] \<longrightarrow>
                        \<not>(length l > 1 \<and> getspc_es (last l) = EvtSys es \<and> getspc_es (esl!0) \<noteq> EvtSys es) \<longrightarrow>
                        \<not>(\<exists>j. j > 0 \<and> Suc j < length l \<and> 
                             getspc_es (l!j) = EvtSys es \<and> getspc_es (l!Suc j) \<noteq> EvtSys es) \<longrightarrow>
                        (\<forall>i. i < length elst \<longrightarrow> \<not>(\<exists>j. j > 0 \<and> Suc j < length (elst!i) \<and> 
                             getspc_es (elst!i!j) = EvtSys es \<and> getspc_es (elst!i!Suc j) \<noteq> EvtSys es))"
  proof -
  {
    fix esl
    have "\<forall>elst l es. esl\<in>cpts_es \<and> elst = parse_es_cpts_i2 esl es [l] \<longrightarrow>
                        \<not>(length l > 1 \<and> getspc_es (last l) = EvtSys es \<and> getspc_es (esl!0) \<noteq> EvtSys es) \<longrightarrow>
                        \<not>(\<exists>j. j > 0 \<and> Suc j < length l \<and> 
                             getspc_es (l!j) = EvtSys es \<and> getspc_es (l!Suc j) \<noteq> EvtSys es) \<longrightarrow>
                        (\<forall>i. i < length elst \<longrightarrow> \<not>(\<exists>j. j > 0 \<and> Suc j < length (elst!i) \<and> 
                             getspc_es (elst!i!j) = EvtSys es \<and> getspc_es (elst!i!Suc j) \<noteq> EvtSys es))"
      proof(induct esl)
        case Nil show ?case by simp
      next
        case (Cons esc esl1)
        assume a0: "\<forall>elst l es. esl1\<in>cpts_es \<and> elst = parse_es_cpts_i2 esl1 es [l] \<longrightarrow>
                        \<not>(length l > 1 \<and> getspc_es (last l) = EvtSys es \<and> getspc_es (esl1!0) \<noteq> EvtSys es) \<longrightarrow>
                        \<not>(\<exists>j. j > 0 \<and> Suc j < length l \<and> 
                             getspc_es (l!j) = EvtSys es \<and> getspc_es (l!Suc j) \<noteq> EvtSys es) \<longrightarrow>
                        (\<forall>i. i < length elst \<longrightarrow> \<not>(\<exists>j. j > 0 \<and> Suc j < length (elst!i) \<and> 
                             getspc_es (elst!i!j) = EvtSys es \<and> getspc_es (elst!i!Suc j) \<noteq> EvtSys es))"
        then show ?case 
          proof -
          {
            fix elst l es
            assume b0: "esc # esl1 \<in> cpts_es"
              and  b1: "elst = parse_es_cpts_i2 (esc # esl1) es [l]"
              and  b2: "\<not> (length l > 1 \<and> getspc_es (last l) = EvtSys es \<and> getspc_es ((esc # esl1) ! 0) \<noteq> EvtSys es)"
              and  b3: "\<not> (\<exists>j>0. Suc j < length l \<and> getspc_es (l ! j) = EvtSys es \<and> getspc_es (l ! Suc j) \<noteq> EvtSys es)"
            have "(\<forall>i. i < length elst \<longrightarrow> \<not> (\<exists>j>0. Suc j < length (elst ! i) \<and>
                    getspc_es (elst ! i ! j) = EvtSys es \<and> getspc_es (elst ! i ! Suc j) \<noteq> EvtSys es))"
              proof(cases "esl1 = []")
                assume c0: "esl1 = []"
                then have c1: "parse_es_cpts_i2 (esc # []) es [l] = 
                            parse_es_cpts_i2 [] es (list_update [l] (length [l] - 1) (last [l] @ [esc]))" by simp
                have c2: "parse_es_cpts_i2 [] es (list_update [l] (length [l] - 1) (last [l] @ [esc]))
                      = list_update [l] (length [l] - 1) (last [l] @ [esc])" by simp
                with b1 c0 c1 have "elst = list_update [l] (length [l] - 1) (last [l] @ [esc])" by simp
                then have "elst = [l @ [esc]]" by simp
                with b2 b3 show ?thesis by (smt Suc_eq_plus1_left Suc_lessD Suc_lessI diff_Suc_1 
                  dual_order.strict_trans last_conv_nth length_Cons length_append_singleton 
                  less_antisym less_one list.size(3) nat_neq_iff nth_Cons_0 nth_append nth_append_length)
                  
              next
                assume c0: "\<not>(esl1 = [])"
                with b0 have c1: "esl1 \<in> cpts_es" using cpts_es_dropi by force
                from c0 obtain esl2 and ec1 where c2: "esl1 = ec1 # esl2"
                  by (meson neq_Nil_conv) 
                show ?thesis
                  proof(cases "getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es")
                    assume d0: "getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es"
                    with c2 have d01: "getspc_es ec1 \<noteq> EvtSys es" by simp
                    from d0 have d1: "parse_es_cpts_i2 (esc # esl1) es [l] = parse_es_cpts_i2 esl1 es ([l]@[[esc]])"
                      by simp
                    with b1 b2 have d2: "elst = parse_es_cpts_i2 esl1 es ([l]@[[esc]])" by simp
                    from c1 have d4: "parse_es_cpts_i2 esl1 es ([l]@[[esc]]) = [l]@parse_es_cpts_i2 esl1 es ([[esc]])"
                      using parse_es_cpts_i2_lst0 by blast
                    with d2 have d3: "elst = [l] @ parse_es_cpts_i2 esl1 es ([[esc]])" by simp
                    let ?elst1 = "parse_es_cpts_i2 esl1 es ([[esc]])"
                    have "\<not>(length [esc] > 1 \<and> getspc_es (last [esc]) = EvtSys es \<and> getspc_es (esl1!0) \<noteq> EvtSys es)"
                      by simp
                    moreover have "\<not>(\<exists>j. j > 0 \<and> Suc j < length [esc] \<and> 
                             getspc_es ([esc]!j) = EvtSys es \<and> getspc_es ([esc]!Suc j) \<noteq> EvtSys es)" by simp                    
                    ultimately have "\<forall>i. i < length ?elst1 \<longrightarrow> \<not>(\<exists>j. j > 0 \<and> Suc j < length (?elst1!i) \<and> 
                             getspc_es (?elst1!i!j) = EvtSys es \<and> getspc_es (?elst1!i!Suc j) \<noteq> EvtSys es)"
                       using a0 c1 by simp
                    with b3 d3 show ?thesis by (smt Nil_is_append_conv Nitpick.size_list_simp(2) 
                        One_nat_def Suc_diff_Suc Suc_less_eq append_Cons append_Nil 
                        diff_Suc_1 diff_Suc_Suc list.sel(3) not_gr0 nth_Cons') 
                  next
                    assume d0: "\<not>(getspc_es esc = EvtSys es \<and> length esl1 > 0 \<and> getspc_es (esl1!0) \<noteq> EvtSys es)"
                    then have "parse_es_cpts_i2 (esc # esl1) es [l] = 
                                parse_es_cpts_i2 esl1 es (list_update [l] (length [l] - 1) (last [l] @ [esc])) "
                                by auto
                    with b1 have d1: "elst = parse_es_cpts_i2 esl1 es ([l@[esc]])" by simp
                    show ?thesis
                      proof(cases "length esl1 = 0")
                        assume e0: "length esl1 = 0"
                        then have e1: "esl1 = []" by simp
                        with d1 have "elst = [l@[esc]]" by simp
                        with b2 show ?thesis using e1 c0 by linarith 
                      next
                        assume e0: "\<not>(length esl1 = 0)"
                        then have "length esl1 > 0" by simp
                        with d0 have e1: "\<not>(getspc_es esc = EvtSys es \<and> getspc_es (esl1!0) \<noteq> EvtSys es)" by simp
                        then have "\<not> (1 < length (l@[esc]) \<and> getspc_es (last (l@[esc])) = EvtSys es 
                                    \<and> getspc_es (esl1 ! 0) \<noteq> EvtSys es)" by auto
                        moreover from b2 b3 have "\<not> (\<exists>j>0. Suc j < length (l@[esc]) \<and> getspc_es ((l@[esc]) ! j) = EvtSys es \<and> 
                                getspc_es ((l@[esc]) ! Suc j) \<noteq> EvtSys es)"
                          by (metis (no_types, hide_lams) Suc_neq_Zero diff_Suc_1 last_conv_nth 
                            length_append_singleton less_antisym list.size(3) not_gr0 not_less_eq 
                            nth_Cons_0 nth_append zero_less_diff)
                        ultimately show ?thesis using a0 d1 c1 by blast
                      qed
                  qed
              qed
          }
          then show ?thesis by auto
          qed
      qed
  }
  then show ?thesis by blast
  qed

lemma parse_es_cpts_i2_noent_mid:
    "\<lbrakk>esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs; esl\<in>cpts_es; 
      elst = parse_es_cpts_i2 esl es [[]]\<rbrakk> \<Longrightarrow>  \<forall>i. i < length (tl elst) \<longrightarrow> 
                             \<not>(\<exists>j. j > 0 \<and> Suc j < length ((tl elst)!i) \<and> 
                             getspc_es ((tl elst)!i!j) = EvtSys es \<and> getspc_es ((tl elst)!i!Suc j) \<noteq> EvtSys es)"
  proof -
    assume p0: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p1: "esl\<in>cpts_es"
      and  p2: "elst = parse_es_cpts_i2 esl es [[]]"
    then have "\<not>(length [] > 1 \<and> getspc_es (last []) = EvtSys es \<and> getspc_es (esl!0) \<noteq> EvtSys es)" by simp
    moreover have "\<not>(\<exists>j. j > 0 \<and> Suc j < length [] \<and> 
                      getspc_es ([]!j) = EvtSys es \<and> getspc_es ([]!Suc j) \<noteq> EvtSys es)" by simp
    ultimately have "\<forall>i. i < length elst \<longrightarrow> \<not>(\<exists>j. j > 0 \<and> Suc j < length (elst!i) \<and> 
                             getspc_es (elst!i!j) = EvtSys es \<and> getspc_es (elst!i!Suc j) \<noteq> EvtSys es)"
      using p1 p2 parse_es_cpts_i2_noent_mid0 by blast
    then show ?thesis by (metis (no_types, lifting) List.nth_tl Nitpick.size_list_simp(2) Suc_mono list.sel(2)) 
  qed



lemma parse_es_cpts_i2_start_aux: "\<lbrakk>esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs; esl\<in>cpts_es;
        elst = parse_es_cpts_i2 esl es [[]]\<rbrakk> \<Longrightarrow> 
        \<forall>i. i < length (tl elst) \<longrightarrow> length ((tl elst)!i) \<ge> 2  \<and> 
            getspc_es ((tl elst)!i!0) = EvtSys es \<and> getspc_es ((tl elst)!i!1) \<noteq> EvtSys es"
  proof -
    assume p0: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p1: "esl\<in>cpts_es"
      and  p2: "elst = parse_es_cpts_i2 esl es [[]]"
    from p1 p2 have a0: "\<forall>i. i \<ge> length [[]] \<and> i < length elst \<longrightarrow> length (elst!i) \<ge> 2  \<and> 
            getspc_es (elst!i!0) = EvtSys es \<and> getspc_es (elst!i!1) \<noteq> EvtSys es"
      by (metis length_Cons list.distinct(2) list.size(3) parse_es_cpts_i2_start_withlen0) 

    then show ?thesis 
      proof -
      {
        fix i
        assume b0: "i < length (tl elst)"
        from a0 b0 have "length (tl elst ! i) \<ge> 2" 
          by (metis List.nth_tl Nil_tl Nitpick.size_list_simp(2) One_nat_def 
              Suc_eq_plus1_left Suc_less_eq le_add1 length_Cons less_nat_zero_code)
        moreover from a0 b0 have "getspc_es (elst!Suc i!0) = EvtSys es \<and> getspc_es (elst!Suc i!1) \<noteq> EvtSys es"
          by force 
        moreover from b0 have "(tl elst)!i = elst!Suc i" by (simp add: List.nth_tl)
        ultimately have "length (tl elst ! i) \<ge> 2 \<and> getspc_es ((tl elst)!i!0) = EvtSys es 
          \<and> getspc_es ((tl elst)!i!1) \<noteq> EvtSys es" by simp
      }
      then show ?thesis by auto
      qed
  qed    

lemma parse_es_cpts_i2_noent_mid_i:
    "\<lbrakk>esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs; esl\<in>cpts_es; 
      elst = tl (parse_es_cpts_i2 esl es [[]]); Suc i < length elst; esl1 = elst!i@[elst!Suc i!0]\<rbrakk> \<Longrightarrow>  
        \<not>(\<exists>j. j > 0 \<and> Suc j < length esl1 \<and> 
              getspc_es (esl1!j) = EvtSys es \<and> getspc_es (esl1!Suc j) \<noteq> EvtSys es)"
  proof -
    assume p0: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p1: "esl\<in>cpts_es"
      and  p2: "elst = tl (parse_es_cpts_i2 esl es [[]])"
      and  p3: "Suc i < length elst"
      and  p4: "esl1 = elst!i@[elst!Suc i!0]"
    let ?esl2 = "elst!i"
    from p0 p1 p2 p3 have "\<not>(\<exists>j. j > 0 \<and> Suc j < length ?esl2 \<and> 
              getspc_es (?esl2!j) = EvtSys es \<and> getspc_es (?esl2!Suc j) \<noteq> EvtSys es)"
      using parse_es_cpts_i2_noent_mid[of esl es s x e s1 x1 xs elst]
        by (meson Suc_lessD parse_es_cpts_i2_noent_mid) 
    moreover
    from p0 p1 p2 p3 have "getspc_es (elst!Suc i!0) = EvtSys es"
      using parse_es_cpts_i2_start_aux[of esl es s x e s1 x1 xs 
          "parse_es_cpts_i2 esl es [[]]"] by blast 
    ultimately show ?thesis by (simp add: nth_append p4) 
  qed

lemma parse_es_cpts_i2_drop_cptes: 
  "\<lbrakk>esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs; esl\<in>cpts_es;
        elst = tl (parse_es_cpts_i2 esl es [[]])\<rbrakk> \<Longrightarrow> 
        \<forall>i. i < length elst \<longrightarrow> concat (drop i elst)\<in>cpts_es"
  proof -
    assume p0: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p1: "esl\<in>cpts_es"
      and  p2: "elst = tl (parse_es_cpts_i2 esl es [[]])"
    then have a1: "concat elst = esl" using parse_es_cpts_i2_concat3 by metis 
    {
      fix i
      assume b0: "i < length elst"
      then have "concat (drop i elst)\<in>cpts_es"
        proof(induct i)
          case 0 with p1 a1 show ?case by auto
        next
          case (Suc j)
          assume c0: "j < length elst \<Longrightarrow> concat (drop j elst) \<in> cpts_es"
            and  c1: "Suc j < length elst"
          then have c2: "concat (drop (Suc j) elst) = drop (length (elst!j)) (concat (drop j elst))"
            by (metis Cons_nth_drop_Suc Suc_lessD append_eq_conv_conj concat.simps(2))
          from c0 c1 have "concat (drop j elst) \<in> cpts_es" by simp
          with c1 c2 show ?case 
            using cpts_es_dropi2[of "concat (drop j elst)" "length (elst ! j)"]
            by (smt List.nth_tl Suc_leI Suc_lessE concat_last_lm diff_Suc_1 drop.simps(1) 
              last_conv_nth last_drop le_less_trans length_0_conv length_Cons length_drop 
              length_greater_0_conv length_tl lessI numeral_2_eq_2 p1 p2 parse_es_cpts_i2_start_withlen0 
              zero_less_diff) 
        qed
    }
    then show ?thesis by auto
  qed

lemma parse_es_cpts_i2_in_cptes_i: 
  "\<lbrakk>esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs; esl\<in>cpts_es;
        elst = tl (parse_es_cpts_i2 esl es [[]])\<rbrakk> \<Longrightarrow> 
        \<forall>i. Suc i < length elst \<longrightarrow> (elst!i)@[elst!Suc i!0] \<in>cpts_es"
  proof -
    assume p0: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p1: "esl\<in>cpts_es"
      and  p2: "elst = tl (parse_es_cpts_i2 esl es [[]])"
    then have p3: "concat elst = esl" using parse_es_cpts_i2_concat3 by metis 
    from p0 p1 p2 have p4: "\<forall>i. i < length elst \<longrightarrow> length (elst!i) \<ge> 2" 
      using parse_es_cpts_i2_start_aux[of esl es s x e s1 x1 xs "parse_es_cpts_i2 esl es [[]]"] 
        by simp

    {
      fix i
      assume a0: "Suc i < length elst"
      have "(elst!i)@[elst!Suc i!0] \<in>cpts_es"
        proof(cases "i = 0")
          assume b0: "i = 0"
          with a0 p4 have b1: "length (elst!1) \<ge> 2" by auto
          from p3 a0 have "esl = (elst!0) @ concat (drop 1 elst)"
            by (metis Cons_nth_drop_Suc One_nat_def Suc_lessD b0 concat.simps(2) drop_0)  
          with a0 have "esl = (elst!0) @ ((elst!1) @ concat (drop 2 elst))"
            by (metis Cons_nth_drop_Suc One_nat_def Suc_1 b0 concat.simps(2)) 
          with a0 b0 b1 have "take ((length (elst ! 0)) + 1) esl = (elst ! 0) @ [elst!Suc 0!0]"
            by (smt Cons_nth_drop_Suc Nil_is_append_conv One_nat_def Suc_1 Suc_le_lessD 
                append.simps(1) append.simps(2) append_eq_conv_conj drop_0 length_greater_0_conv 
                list.size(3) not_less0 nth_Cons_0 take_0 take_Suc_conv_app_nth take_add) 
          with p1 b0 show ?thesis using cpts_es_take[of esl "length (elst ! 0)"]
            by (metis One_nat_def Suc_lessD add.right_neutral add_Suc_right le_less_linear take_all)
        next
          assume "i\<noteq>0"
          then have b0: "i > 0" by simp
          let ?elst = "drop (i - 1) elst"
          let ?esl = "concat ?elst"
          from a0 b0 have b01: "length ?elst > 2" by simp
          from a0 p4 b0 have b1: "length (?elst!1) \<ge> 2" by auto
          from p0 p1 p2 a0 b1 have b2: "?esl\<in>cpts_es" 
            using parse_es_cpts_i2_drop_cptes[of esl es s x e s1 x1 xs elst]
              One_nat_def Suc_lessD Suc_pred b0 by presburger
          from p3 a0 have b3: "?esl = (?elst!0) @ concat (drop 1 ?elst)"
            by (metis Cons_nth_drop_Suc One_nat_def Suc_lessD Suc_pred b0 
                concat.simps(2) drop_0 length_drop zero_less_diff) 
          with a0 have "?esl = (?elst!0) @ ((?elst!1) @ concat (drop 2 ?elst))"
            by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_1 
                Suc_leI Suc_lessD b0 concat.simps(2) diff_diff_cancel diff_le_self 
                diff_less_mono length_drop) 
          with b0 b01 b1 have "take ((length (?elst ! 0)) + 1) ?esl = (?elst ! 0) @ [?elst!1!0]"
            by (smt Cons_nth_drop_Suc Nil_is_append_conv One_nat_def append.simps(2) 
                append_eq_conv_conj drop_0 length_greater_0_conv list.size(3) not_numeral_le_zero 
                nth_Cons_0 take_0 take_Suc_conv_app_nth take_add)
          with b2 show ?thesis using cpts_es_take[of ?esl "length (?elst ! 0)"]
            by (smt Nil_is_append_conv a0 concat_i_lm cpts_es_seg2 list.size(3) not_Cons_self2 
              not_numeral_le_zero p0 p1 p2 p3 parse_es_cpts_i2_start_aux) 
        qed
    }
    then show ?thesis by auto
  qed
  

lemma parse_es_cpts_i2_in_cptes_last: 
  "\<lbrakk>esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs; esl\<in>cpts_es;
        elst = tl (parse_es_cpts_i2 esl es [[]])\<rbrakk> \<Longrightarrow> 
        last elst \<in>cpts_es"
  proof -
    assume p0: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p1: "esl\<in>cpts_es"
      and  p2: "elst = tl (parse_es_cpts_i2 esl es [[]])"
    then have "\<forall>i. i < length elst \<longrightarrow> concat (drop i elst)\<in>cpts_es"
      using parse_es_cpts_i2_drop_cptes[of esl es s x e s1 x1 xs elst] by fastforce
    then show ?thesis
      by (metis (no_types, lifting) append_butlast_last_id append_eq_conv_conj 
          concat.simps(1) concat.simps(2) diff_less length_butlast length_greater_0_conv 
          less_one list.simps(3) p0 p1 p2 parse_es_cpts_i2_concat3 self_append_conv) 
  qed

lemma evtsys_fst_ent: 
      "\<lbrakk>esl \<in> cpts_es; getspc_es (esl ! 0) = EvtSys es; Suc m \<le> length esl; \<exists>i. i \<le> m \<and> getspc_es (esl ! i) \<noteq> EvtSys es\<rbrakk> 
        \<Longrightarrow> \<exists>i. (i < m \<and> getspc_es (esl ! i) = EvtSys es \<and> getspc_es (esl ! Suc i) \<noteq> EvtSys es) 
                \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) = EvtSys es)" 
  proof -
    assume p0: "esl \<in> cpts_es"
      and  p1: "getspc_es (esl ! 0) = EvtSys es"
      and  p2: "Suc m \<le> length esl"
      and  p3: "\<exists>i. i \<le> m \<and> getspc_es (esl ! i) \<noteq> EvtSys es"
    have "\<forall>m. esl \<in> cpts_es \<and> getspc_es (esl ! 0) = EvtSys es \<and> Suc m \<le> length esl 
                   \<and> (\<exists>i. i \<le> m \<and> getspc_es (esl ! i) \<noteq> EvtSys es)  
             \<longrightarrow> (\<exists>i. (i < m \<and> getspc_es (esl ! i) = EvtSys es \<and> getspc_es (esl ! Suc i) \<noteq> EvtSys es) 
                \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) = EvtSys es))"
      proof - 
      {
        fix m
        assume a0: "esl \<in> cpts_es"
          and  a1: "getspc_es (esl ! 0) = EvtSys es"
          and  a2: "Suc m \<le> length esl"
          and  a3: "\<exists>i. i \<le> m \<and> getspc_es (esl ! i) \<noteq> EvtSys es"
        then have "\<exists>i. (i < m \<and> getspc_es (esl ! i) = EvtSys es 
                        \<and> getspc_es (esl ! Suc i) \<noteq> EvtSys es) 
                        \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) = EvtSys es)"
          proof(induct m)
            case 0 show ?case using "0.prems"(4) p1 by auto 
          next
            case (Suc n)
            assume b0: "esl \<in> cpts_es \<Longrightarrow>
                        getspc_es (esl ! 0) = EvtSys es \<Longrightarrow>
                        Suc n \<le> length esl \<Longrightarrow>
                        \<exists>i\<le>n. getspc_es (esl ! i) \<noteq> EvtSys es \<Longrightarrow>
                        \<exists>i. (i < n \<and> getspc_es (esl ! i) = EvtSys es 
                            \<and> getspc_es (esl ! Suc i) \<noteq> EvtSys es) 
                            \<and> (\<forall>j<i. getspc_es (esl ! j) = EvtSys es)"
              and  b1: "esl \<in> cpts_es"
              and  b2: "getspc_es (esl ! 0) = EvtSys es"
              and  b3: "Suc (Suc n) \<le> length esl"
              and  b4: "\<exists>i\<le>Suc n. getspc_es (esl ! i) \<noteq> EvtSys es"
            show ?case 
              proof(cases "\<exists>i\<le>n. getspc_es (esl ! i) \<noteq> EvtSys es")
                assume c0: "\<exists>i\<le>n. getspc_es (esl ! i) \<noteq> EvtSys es"
                with b0 b1 b2 b3 have "\<exists>i. (i < n \<and> getspc_es (esl ! i) = EvtSys es 
                            \<and> getspc_es (esl ! Suc i) \<noteq> EvtSys es) 
                            \<and> (\<forall>j<i. getspc_es (esl ! j) = EvtSys es)" by simp
                then show ?thesis using less_Suc_eq by auto
              next
                assume c0: "\<not>(\<exists>i\<le>n. getspc_es (esl ! i) \<noteq> EvtSys es)"
                with b4 have "getspc_es (esl ! Suc n) \<noteq> EvtSys es"
                  using le_SucE by auto
                moreover from c0 have "\<forall>j<n. getspc_es (esl ! j) = EvtSys es" by auto
                moreover from c0 have "getspc_es (esl ! n) = EvtSys es" by auto
                ultimately show ?thesis by blast
              qed
        qed
      }
      then show ?thesis by auto
      qed

    then show ?thesis using p0 p1 p2 p3 by blast
  qed


lemma rm_evtsys_in_cptse0: 
    "\<lbrakk>esl\<in>cpts_es; length esl > 0; \<exists>e. getspc_es (esl!0) = EvtSeq e (EvtSys es);
      \<not>(\<exists>j. Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es) \<rbrakk>
       \<Longrightarrow> rm_evtsys esl \<in> cpts_ev"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "length esl > 0"
      and  p2: "\<exists>e. getspc_es (esl!0) = EvtSeq e (EvtSys es)"
      and  p3: "\<not>(\<exists>j. Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
    have "\<forall>esl e es .esl\<in>cpts_es \<and> length esl > 0 \<and> (\<exists>e. getspc_es (esl!0) = EvtSeq e (EvtSys es)) \<and>
      \<not>(\<exists>j. Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es) 
       \<longrightarrow> rm_evtsys esl \<in> cpts_ev"
      proof -
      {
        fix esl e es
        assume a0: "esl\<in>cpts_es"
          and  a1: "length esl > 0"
          and  a2: "\<exists>e. getspc_es (esl!0) = EvtSeq e (EvtSys es)"
          and  a3: "\<not>(\<exists>j. Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
        from a0 a1 a2 a3 have "rm_evtsys esl \<in> cpts_ev"
          proof(induct esl)
            case (CptsEsOne es1 s x)
            show ?case 
              proof(induct es1)
                case (EvtSeq x1 es1)
                have "rm_evtsys [(EvtSeq x1 es1, s, x)] = [(x1, s, x)]" 
                  by (simp add:rm_evtsys_def rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
                then show ?case by (simp add: cpts_ev.CptsEvOne)
              next
                case (EvtSys xa)
                have "rm_evtsys [(EvtSys xa, s, x)] = [(AnonyEvent None, s, x)]"
                  by (simp add:rm_evtsys_def rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
                then show ?case by (simp add: cpts_ev.CptsEvOne)
              qed
          next
            case (CptsEsEnv es1 t x xs s y)
            assume b0: "(es1, t, x) # xs \<in> cpts_es"
              and  b1: "0 < length ((es1, t, x) # xs) \<Longrightarrow>
                          \<exists>e. getspc_es (((es1, t, x) # xs) ! 0) = EvtSeq e (EvtSys es) \<Longrightarrow>
                          \<not> (\<exists>j. Suc j < length ((es1, t, x) # xs) \<and>
                          getspc_es (((es1, t, x) # xs) ! j) = EvtSys es \<and> 
                          getspc_es (((es1, t, x) # xs) ! Suc j) \<noteq> EvtSys es) \<Longrightarrow>
                            rm_evtsys ((es1, t, x) # xs) \<in> cpts_ev"
              and  b2: "0 < length ((es1, s, y) # (es1, t, x) # xs)"
              and  b3: "\<exists>e. getspc_es (((es1, s, y) # (es1, t, x) # xs) ! 0) = EvtSeq e (EvtSys es)"
              and  b4: "\<not> (\<exists>j. Suc j < length ((es1, s, y) # (es1, t, x) # xs) \<and>
                                getspc_es (((es1, s, y) # (es1, t, x) # xs) ! j) = EvtSys es \<and>
                                getspc_es (((es1, s, y) # (es1, t, x) # xs) ! Suc j) \<noteq> EvtSys es)"
            from b4 have "\<not> (\<exists>j. Suc j < length ((es1, t, x) # xs) \<and>
                                getspc_es (((es1, t, x) # xs) ! j) = EvtSys es \<and> 
                                getspc_es (((es1, t, x) # xs) ! Suc j) \<noteq> EvtSys es)" by force
            moreover have "\<exists>e. getspc_es (((es1, t, x) # xs) ! 0) = EvtSeq e (EvtSys es)"
              proof -
                from b3 obtain e where "getspc_es (((es1, s, y) # (es1, t, x) # xs) ! 0) = EvtSeq e (EvtSys es)"
                  by auto
                then have "es1 = EvtSeq e (EvtSys es)" by (simp add:getspc_es_def)
                then show ?thesis by (simp add:getspc_es_def)
              qed
            ultimately have "rm_evtsys ((es1, t, x) # xs) \<in> cpts_ev" using b1 b3 by blast
            then have b4: "rm_evtsys1 (es1, t, x) # rm_evtsys xs \<in> cpts_ev" by (simp add:rm_evtsys_def)
            have b5: "rm_evtsys ((es1, s, y) # (es1, t, x) # xs) = 
                    rm_evtsys1 (es1, s, y) # rm_evtsys1 (es1, t, x) # rm_evtsys xs" 
                by (simp add:rm_evtsys_def)
            from b4 show ?case 
              proof(induct es1)
                case(EvtSeq x1 es2)
                assume c0: "rm_evtsys1 (EvtSeq x1 es2, t, x) # rm_evtsys xs \<in> cpts_ev"
                have "rm_evtsys ((EvtSeq x1 es2, s, y) # (EvtSeq x1 es2, t, x) # xs) = 
                        (x1,s,y) # (x1, t, x) # rm_evtsys xs" 
                   by (simp add:rm_evtsys_def rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
                moreover from c0 have "(x1, t, x) # rm_evtsys xs \<in> cpts_ev" 
                  by (simp add:rm_evtsys_def rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
                ultimately show ?case by (simp add: cpts_ev.CptsEvEnv)
              next
                case (EvtSys xa)
                assume c0: "rm_evtsys1 (EvtSys xa, t, x) # rm_evtsys xs \<in> cpts_ev"
                have "rm_evtsys ((EvtSys xa, s, y) # (EvtSys xa, t, x) # xs) = 
                        (AnonyEvent None, s, y) # (AnonyEvent None, t, x) # rm_evtsys xs" 
                   by (simp add:rm_evtsys_def rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
                moreover from c0 have "(AnonyEvent None,t, x) # rm_evtsys xs \<in> cpts_ev"
                  by (simp add:rm_evtsys_def rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
                ultimately show ?case by (simp add: cpts_ev.CptsEvEnv)
              qed
          next
            case (CptsEsComp e1 s1 x1 et e2 t1 y1 xs1)
            assume b0: "(e1, s1, x1) -es-et\<rightarrow> (e2, t1, y1)"
              and  b1: "(e2, t1, y1) # xs1 \<in> cpts_es"
              and  b2: "0 < length ((e2, t1, y1) # xs1) \<Longrightarrow>
                          \<exists>e. getspc_es (((e2, t1, y1) # xs1) ! 0) = EvtSeq e (EvtSys es) \<Longrightarrow>
                          \<not> (\<exists>j. Suc j < length ((e2, t1, y1) # xs1) \<and>
                                  getspc_es (((e2, t1, y1) # xs1) ! j) = EvtSys es \<and> 
                                  getspc_es (((e2, t1, y1) # xs1) ! Suc j) \<noteq> EvtSys es) \<Longrightarrow>
                                    rm_evtsys ((e2, t1, y1) # xs1) \<in> cpts_ev"
              and  b3: "0 < length ((e1, s1, x1) # (e2, t1, y1) # xs1)"
              and  b4: "\<exists>e. getspc_es (((e1, s1, x1) # (e2, t1, y1) # xs1) ! 0) = EvtSeq e (EvtSys es)"
              and  b5: "\<not> (\<exists>j. Suc j < length ((e1, s1, x1) # (e2, t1, y1) # xs1) \<and>
                                getspc_es (((e1, s1, x1) # (e2, t1, y1) # xs1) ! j) = EvtSys es \<and>
                                getspc_es (((e1, s1, x1) # (e2, t1, y1) # xs1) ! Suc j) \<noteq> EvtSys es)"
            have b6: "rm_evtsys ((e1, s1, x1) # (e2, t1, y1) # xs1) = 
                        rm_evtsys1 (e1, s1, x1) # rm_evtsys1 (e2, t1, y1) # rm_evtsys xs1" 
                by (simp add:rm_evtsys_def)
            from b4 obtain e' where "getspc_es (((e1, s1, x1) # (e2, t1, y1) # xs1) ! 0) = EvtSeq e' (EvtSys es)"
              by auto
            then have b7: "e1 = EvtSeq e' (EvtSys es)" by (simp add:getspc_es_def)
            show ?case
              proof(cases "\<exists>e. e2 = EvtSeq e (EvtSys es)")
                assume c0: "\<exists>e. e2 = EvtSeq e (EvtSys es)"
                then obtain e where c1: "e2 = EvtSeq e (EvtSys es)" by auto
                then have c2: "\<exists>e. getspc_es (((e2, t1, y1) # xs1) ! 0) = EvtSeq e (EvtSys es)" 
                  by (simp add:getspc_es_def)
                moreover from b5 have "\<not> (\<exists>j. Suc j < length ((e2, t1, y1) # xs1) \<and>
                                  getspc_es (((e2, t1, y1) # xs1) ! j) = EvtSys es \<and> 
                                  getspc_es (((e2, t1, y1) # xs1) ! Suc j) \<noteq> EvtSys es)" by force
                ultimately have c3: "rm_evtsys ((e2, t1, y1) # xs1) \<in> cpts_ev" using b2 by blast
                then have c5: "rm_evtsys1 (e2, t1, y1) # rm_evtsys xs1 \<in> cpts_ev" by (simp add:rm_evtsys_def)
                
                from b0 c1 b7 have "\<exists>t. (e', s1, x1) -et-t\<rightarrow> (e, t1, y1)" 
                  using evtseq_tran_exist_etran by simp
                then obtain t where c8: "(e', s1, x1) -et-t\<rightarrow> (e, t1, y1)" by auto
                from b7 have "rm_evtsys1 (e1, s1, x1) = (e', s1, x1)" 
                  by (simp add:rm_evtsys_def rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
                moreover from c1 have "rm_evtsys1 (e2, t1, y1) = (e, t1, y1)"
                  by (simp add:rm_evtsys_def rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
                ultimately show ?thesis using b6 c8 c5 using cpts_ev.CptsEvComp by fastforce 
              next
                assume c0: "\<not>(\<exists>e. e2 = EvtSeq e (EvtSys es))"
                with b0 b7 have c1: "e2 = EvtSys es" by (meson evtseq_tran_evtseq) 
                then have c11: "rm_evtsys1 (e2, t1, y1) # rm_evtsys xs1 \<in> cpts_ev"
                  proof -
                    from b5 have d0: "\<not> (\<exists>j. Suc j < length ((e2, t1, y1) # xs1) \<and>
                            getspc_es (((e2, t1, y1) # xs1) ! j) = EvtSys es \<and>
                            getspc_es (((e2, t1, y1) # xs1) ! Suc j) \<noteq> EvtSys es)" by force
                    have d00: "\<forall>j. j < length xs1 \<longrightarrow> getspc_es (xs1!j) = EvtSys es"
                      proof -
                      {
                        fix j
                        assume e0: "j < length xs1"
                        then have "getspc_es (xs1!j) = EvtSys es"
                          proof(induct j)
                            case 0 from b1 c1 d0 show ?case 
                              using getspc_es_def by (metis One_nat_def e0 fst_conv length_Cons 
                                          less_one not_less_eq nth_Cons_0 nth_Cons_Suc) 
                          next
                            case (Suc m)
                            assume f0: "m < length xs1 \<Longrightarrow> getspc_es (xs1 ! m) = EvtSys es"
                              and  f1: "Suc m < length xs1"
                            with d0 show ?case by auto
                          qed
                      }
                      then show ?thesis by auto
                      qed
                    then have d1: "\<forall>j. j < length (rm_evtsys xs1) \<longrightarrow> getspc_e ((rm_evtsys xs1)!j) = AnonyEvent None" 
                       by (simp add:rm_evtsys_def rm_evtsys1_def getspc_es_def gets_es_def getx_es_def getspc_e_def)
                    from c1 have d2: "rm_evtsys1 (e2, t1, y1) = (AnonyEvent None, t1, y1)" 
                      by (simp add:rm_evtsys1_def getspc_es_def gets_es_def getx_es_def getspc_e_def)
                    with d1 have "\<forall>i. i < length (rm_evtsys1 (e2, t1, y1) # rm_evtsys xs1) \<longrightarrow>
                                      getspc_e ((rm_evtsys1 (e2, t1, y1) # rm_evtsys xs1)!i) = AnonyEvent None"
                      using getspc_e_def less_Suc_eq_0_disj by force 
                    moreover have "length (rm_evtsys1 (e2, t1, y1) # rm_evtsys xs1) > 0" by simp
                    ultimately show ?thesis using cpts_ev_same by blast

                  qed
                from b7 have c2: "rm_evtsys1 (e1, s1, x1) = (e', s1, x1)" 
                  by (simp add:rm_evtsys_def rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
                from c1 have c3: "rm_evtsys1 (e2, t1, y1) = (AnonyEvent None, t1, y1)" 
                  by (simp add:rm_evtsys_def rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
                from b0 b7 c1 have "\<exists>t. (e', s1, x1) -et-t\<rightarrow> (AnonyEvent None, t1, y1)" 
                  using evtseq_tran_0_exist_etran by simp
                then obtain t where "(e', s1, x1) -et-t\<rightarrow> (AnonyEvent None, t1, y1)" by auto
                with b6 c2 c3 c11 show ?thesis using cpts_ev.CptsEvComp by fastforce 
              qed
          qed
      }
      then show ?thesis by auto
      qed
    with p0 p1 p2 p3 show ?thesis by force
  qed



lemma rm_evtsys_in_cptse: 
    "\<lbrakk>esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs;
      (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1);
      \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es);
      el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs) \<rbrakk> \<Longrightarrow> 
      el \<in> cpts_ev"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
      and  p2: "(EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      and  p3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es 
                      \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  p4: "el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"
    let ?esl1 = "(EvtSeq ev (EvtSys es), s1,x1) # xs"
    from p0 p1 have a1: "?esl1 \<in> cpts_es" using cpts_es_dropi by force
    moreover have a2: "length ?esl1 > 0" by simp
    moreover have a3: "\<exists>e. getspc_es (?esl1 ! 0) = EvtSeq e (EvtSys es)" by (simp add:getspc_es_def)
    moreover from p1 p3 have a4: "\<not> (\<exists>j. Suc j < length ?esl1 \<and> getspc_es (?esl1 ! j) = EvtSys es 
            \<and> getspc_es (?esl1 ! Suc j) \<noteq> EvtSys es)" by force
    ultimately have "?esl1 \<in> cpts_es" using rm_evtsys_in_cptse0 by blast
    
    with a1 a2 a3 a4 have a5: "rm_evtsys ?esl1 \<in> cpts_ev" using rm_evtsys_in_cptse0 by blast
    have "rm_evtsys ?esl1 = rm_evtsys1 (EvtSeq ev (EvtSys es), s1,x1) # rm_evtsys xs" 
      by (simp add:rm_evtsys_def)
    then have a6: "rm_evtsys ?esl1 = (ev,s1,x1) # rm_evtsys xs" 
      by (simp add:rm_evtsys1_def getspc_es_def gets_es_def getx_es_def)
    from p2 have "(BasicEvent e, s, x) -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (ev, s1, x1)" 
      using evtsysent_evtent[of es s x e k ev s1 x1] by auto
    with p4 a6 show ?thesis using a5 cpts_ev.CptsEvComp by fastforce 
  qed

lemma fstent_nomident_e_sim_es_aux:
    "\<lbrakk>esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs;
      \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es);
      el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs); el\<in>cpts_ev\<rbrakk> \<Longrightarrow>
        \<forall>i. i > 0 \<and> i < length el \<longrightarrow> 
              (getspc_es (esl!i) = EvtSys es \<and> getspc_e (el!i) = AnonyEvent None) 
                \<or> (getspc_es (esl!i) = EvtSeq (getspc_e (el!i)) (EvtSys es))"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
      and  p2: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es 
                  \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  p3: "el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"
      and  p4: "el\<in>cpts_ev"
    let ?el1 = "rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"
    let ?esl1 = "(EvtSeq ev (EvtSys es), s1,x1) # xs"
    have a1: "length ?esl1 = length ?el1" using rm_evtsys_same_sx same_s_x_def by blast
    from p0 p1 have a2: "?esl1\<in>cpts_es" using cpts_es_dropi by force 
    from p2 have p2_1: "\<forall>j. j > 0 \<and> Suc j < length esl \<longrightarrow> 
          getspc_es (esl ! j) = EvtSys es \<longrightarrow> getspc_es (esl ! Suc j) = EvtSys es"
      using noevtent_inmid_eq by auto
    have "\<forall>i. i < length ?el1 \<longrightarrow> 
          (getspc_es (?esl1!i) = EvtSys es \<and> getspc_e (?el1!i) = AnonyEvent None) 
                \<or> (getspc_es (?esl1!i) = EvtSeq (getspc_e (?el1!i)) (EvtSys es))"
      proof -
      {
        fix i
        assume b0: "i < length ?el1"
        then have "(getspc_es (?esl1!i) = EvtSys es \<and> getspc_e (?el1!i) = AnonyEvent None) 
                \<or> (getspc_es (?esl1!i) = EvtSeq (getspc_e (?el1!i)) (EvtSys es))"
          proof(induct i)
            case 0 
            have "getspc_es (?esl1!0) = EvtSeq (getspc_e (?el1!0)) (EvtSys es)" 
              using getspc_es_def getspc_e_def rm_evtsys_def rm_evtsys1_def gets_es_def getx_es_def EvtSeqrm 
              by (smt fstI length_greater_0_conv list.distinct(2) nth_Cons_0 nth_map)
            then show ?case by simp
          next
            case (Suc j)
            assume c0: "j < length ?el1 \<Longrightarrow> getspc_es (?esl1 ! j) = EvtSys es \<and>
                        getspc_e (?el1 ! j) = AnonyEvent None \<or>
                        getspc_es (?esl1 ! j) =
                        EvtSeq (getspc_e (?el1 ! j)) (EvtSys es)"
              and  c1: "Suc j < length ?el1"
            then have c2: "getspc_es (?esl1 ! j) = EvtSys es \<and>
                        getspc_e (?el1 ! j) = AnonyEvent None \<or>
                        getspc_es (?esl1 ! j) =
                        EvtSeq (getspc_e (?el1 ! j)) (EvtSys es)" by simp
            show ?case
              proof(cases "getspc_es (?esl1 ! j) = EvtSys es \<and>
                        getspc_e (?el1 ! j) = AnonyEvent None")
                assume d0: "getspc_es (?esl1 ! j) = EvtSys es \<and>
                        getspc_e (?el1 ! j) = AnonyEvent None"
                with p1 p2_1 a1 have d1: "getspc_es (?esl1 ! Suc j) = EvtSys es"
                  proof -
                    from p1 d0 have "getspc_es (esl ! Suc j) = EvtSys es" by simp
                    moreover 
                    from p1 c1 have "0 < Suc j \<and> Suc (Suc j) < length esl"
                      using a1 by auto 
                    ultimately have "getspc_es (esl ! Suc (Suc j)) = EvtSys es" 
                      using p2_1 by simp
                    with p1 show ?thesis by simp
                  qed
                with a1 c1 have d2: "getspc_e (?el1 ! Suc j) = AnonyEvent None" 
                  using getspc_es_def getspc_e_def rm_evtsys_def rm_evtsys1_def 
                    gets_es_def getx_es_def EvtSysrm by (smt fst_conv nth_map)
                with d1 show ?case by simp
              next
                assume "\<not>(getspc_es (?esl1 ! j) = EvtSys es \<and>
                        getspc_e (?el1 ! j) = AnonyEvent None)"
                with c2 have d0: "getspc_es (?esl1 ! j) =
                        EvtSeq (getspc_e (?el1 ! j)) (EvtSys es)"
                   by simp
                obtain e and s1 and x1 where d1: "?el1 ! j = (e,s1,x1)"
                  using prod_cases3 by blast 
                with d0 have d2: "?esl1 ! j = (EvtSeq e (EvtSys es),s1,x1)" 
                  proof -
                    have e1: "same_s_x ?esl1 ?el1" using rm_evtsys_same_sx by blast
                    from d0 d1 have "getspc_es (?esl1 ! j) = EvtSeq e (EvtSys es)" 
                      by (simp add:getspc_es_def getspc_e_def)
                    moreover
                    from e1 have "gets_e (?el1 ! j) = gets_es (?esl1 ! j)"
                      by (simp add: Suc.prems less_or_eq_imp_le same_s_x_def) 
                    moreover
                    from e1 have "getx_e (?el1 ! j) = getx_es (?esl1 ! j)"
                      by (simp add: Suc.prems less_or_eq_imp_le same_s_x_def)
                    ultimately show ?thesis 
                      using d1 getspc_es_def gets_es_def getx_es_def gets_e_def getx_e_def 
                        by (metis prod.collapse snd_conv)
                  qed
                then show ?case
                  proof(cases "getspc_es (?esl1 ! Suc j) = EvtSys es")
                    assume e0: "getspc_es (?esl1 ! Suc j) = EvtSys es"
                    then obtain s2 and x2 where e1: "?esl1 ! Suc j = (EvtSys es, s2,x2)" 
                      using getspc_es_def by (metis fst_conv surj_pair) 
                    then have e2: "?el1 ! Suc j = (AnonyEvent None, s2,x2)" 
                      using getspc_es_def rm_evtsys_def rm_evtsys1_def 
                        gets_es_def getx_es_def EvtSysrm by (metis Suc.prems a1 fst_conv nth_map snd_conv)
                    with e1 have "getspc_es (?esl1 ! Suc j) = EvtSys es \<and>
                        getspc_e (?el1 ! Suc j) = AnonyEvent None"
                      using getspc_es_def getspc_e_def by (metis fst_conv)
                    then show ?thesis by simp
                  next
                    assume e0: "getspc_es (?esl1 ! Suc j) \<noteq> EvtSys es"
                    with a1 a2 c1 d2 have "\<exists>e1. getspc_es (?esl1 ! Suc j) = EvtSeq e1 (EvtSys es)" 
                      using evtseq_next_in_cpts getspc_es_def by fastforce 
                    then obtain e1 where e1:"getspc_es (?esl1 ! Suc j) = EvtSeq e1 (EvtSys es)" by auto
                    with a1 c1 have "getspc_e (?el1 ! Suc j) = e1" 
                      using getspc_es_def getspc_e_def rm_evtsys_def rm_evtsys1_def 
                        gets_es_def getx_es_def EvtSeqrm by (smt fstI nth_map)
                    with e1 have "getspc_es (?esl1 ! Suc j) =
                                EvtSeq (getspc_e (?el1 ! Suc j)) (EvtSys es)" by simp
                    then show ?thesis by simp
                  qed
              qed
          qed
      }
      then show ?thesis by auto
      qed
    with p1 p2 p3 p4 show ?thesis by (metis (no_types, lifting) Suc_diff_1 
              Suc_less_SucD length_Cons nth_Cons_pos) 
  qed


lemma fstent_nomident_e_sim_es:
    "\<lbrakk>esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs;
      \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)\<rbrakk> \<Longrightarrow>
      \<exists>el e s x. el\<in>cpts_of_ev (BasicEvent e) s x \<and> e_sim_es esl el es e"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
      and  p3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es 
                    \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
    from p1 have "\<exists>t. (EvtSys es, s, x) -es-t\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      apply(induct esl)
      apply(simp)
      by (metis esys.distinct(1) exist_estran p0 p1)
    then obtain t where a1: "(EvtSys es, s, x) -es-t\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)" by auto
    then have "\<exists>evt e. evt \<in> es \<and> evt = BasicEvent e \<and> Act t = EvtEnt (BasicEvent e) \<and>
            (BasicEvent e, s, x) -et-t\<rightarrow> (ev, s1, x1)" using evtsysent_evtent0 by fastforce
    then obtain evt and e where a2: "evt \<in> es \<and> evt = BasicEvent e \<and> Act t = EvtEnt (BasicEvent e) \<and>
            (BasicEvent e, s, x) -et-t\<rightarrow> (ev, s1, x1)" by auto
    let ?esl1 = "(EvtSeq ev (EvtSys es), s1,x1) # xs"
    let ?el = "(BasicEvent e, s, x) # rm_evtsys ?esl1" 
    let ?el1 = "rm_evtsys ?esl1"
    have a5: "?el = (BasicEvent e, s, x) # ?el1" by simp
    from p1 have a3: "esl = (EvtSys es, s, x) # ?esl1" by simp
    from a2 obtain at and ak where "(BasicEvent e, s, x) -et-(at\<sharp>ak)\<rightarrow> (ev, s1, x1)" 
      using get_actk_def by (metis actk.cases)
    with p0 p1 p3 a1 a2 have a4: "?el \<in> cpts_ev" 
      using rm_evtsys_in_cptse [of esl es s x ev s1 x1 xs] 
        by (metis estran.EvtOccur evtsysent_evtent0 noevtent_notran0)
    moreover have "e_sim_es esl ?el es e" 
      proof -
        from a3 have b1: "length esl = length ?el" by (simp add:rm_evtsys_def)
        moreover 
        from p1 have b2: "getspc_es (esl ! 0) = EvtSys es" by (simp add:getspc_es_def)
        moreover 
        have b3: "getspc_e (?el ! 0) = BasicEvent e" by (simp add:getspc_e_def)
        moreover 
        from a3 b1 have b4: "\<forall>i. i < length ?el \<longrightarrow> 
                  gets_e (?el ! i) = gets_es (esl ! i) \<and>
                  getx_e (?el ! i) = getx_es (esl ! i)"
          proof -
            have c1: "same_s_x ?esl1 (rm_evtsys ?esl1)" using rm_evtsys_same_sx by auto
            show ?thesis 
              proof -
              {
                fix i
                have "i < length ?el \<longrightarrow> 
                  gets_e (?el ! i) = gets_es (esl ! i) \<and>
                  getx_e (?el ! i) = getx_es (esl ! i)"
                  proof(cases "i = 0")
                    assume "i = 0" 
                    with p1 show ?thesis using gets_e_def getx_e_def gets_es_def 
                        getx_es_def by (metis nth_Cons_0 snd_conv)
                  next
                    assume "i\<noteq>0"
                    with p1 p3 a3 c1 show ?thesis by (simp add: same_s_x_def) 
                  qed
              }
              then show ?thesis by auto
              qed
          qed
        moreover 
        have "\<forall>i. i > 0 \<and> i < length ?el \<longrightarrow> 
                  (getspc_es (esl!i) = EvtSys es \<and> getspc_e (?el!i) = AnonyEvent None) 
                    \<or> (getspc_es (esl!i) = EvtSeq (getspc_e (?el!i)) (EvtSys es))"
          using p0 p1 p3 a4  by (meson fstent_nomident_e_sim_es_aux)
        ultimately show ?thesis by (simp add:e_sim_es_def)
      qed
    ultimately show ?thesis using cpts_of_ev_def by (smt mem_Collect_eq nth_Cons') 
  qed

lemma fstent_nomident_e_sim_es2:
    "\<lbrakk>esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs;
      (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1);
      \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es);
      el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs); el\<in>cpts_ev\<rbrakk> \<Longrightarrow>
      e_sim_es esl el es e"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
      and  p2: "(EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      and  p3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es 
                    \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  p4: "el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"
      and  p5: "el\<in>cpts_ev"
    from p2 have a2: "(BasicEvent e, s, x) -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (ev, s1, x1)" 
      using evtsysent_evtent[of es s x e k ev s1 x1] by auto
    let ?esl1 = "(EvtSeq ev (EvtSys es), s1,x1) # xs"
    let ?el = "(BasicEvent e, s, x) # rm_evtsys ?esl1" 
    let ?el1 = "rm_evtsys ?esl1"
    have a5: "?el = (BasicEvent e, s, x) # ?el1" by simp
    from p1 have a3: "esl = (EvtSys es, s, x) # ?esl1" by simp
    from p0 p1 p2 p3 p4 a2 have a4: "?el \<in> cpts_ev" 
      using rm_evtsys_in_cptse by metis
    show ?thesis 
      proof -
        from a3 have b1: "length esl = length ?el" by (simp add:rm_evtsys_def)
        moreover 
        from p1 have b2: "getspc_es (esl ! 0) = EvtSys es" by (simp add:getspc_es_def)
        moreover 
        have b3: "getspc_e (?el ! 0) = BasicEvent e" by (simp add:getspc_e_def)
        moreover 
        from a3 b1 have b4: "\<forall>i. i < length ?el \<longrightarrow> 
                  gets_e (?el ! i) = gets_es (esl ! i) \<and>
                  getx_e (?el ! i) = getx_es (esl ! i)"
          proof -
            have c1: "same_s_x ?esl1 (rm_evtsys ?esl1)" using rm_evtsys_same_sx by auto
            show ?thesis 
              proof -
              {
                fix i
                have "i < length ?el \<longrightarrow> 
                  gets_e (?el ! i) = gets_es (esl ! i) \<and>
                  getx_e (?el ! i) = getx_es (esl ! i)"
                  proof(cases "i = 0")
                    assume "i = 0" 
                    with p1 show ?thesis using gets_e_def getx_e_def gets_es_def 
                        getx_es_def by (metis nth_Cons_0 snd_conv)
                  next
                    assume "i\<noteq>0"
                    with p1 p3 a3 c1 show ?thesis by (simp add: same_s_x_def) 
                  qed
              }
              then show ?thesis by auto
              qed
          qed
        moreover 
        have "\<forall>i. i > 0 \<and> i < length ?el \<longrightarrow> 
                  (getspc_es (esl!i) = EvtSys es \<and> getspc_e (?el!i) = AnonyEvent None) 
                    \<or> (getspc_es (esl!i) = EvtSeq (getspc_e (?el!i)) (EvtSys es))"
          using p0 p1 p3 a4  by (meson fstent_nomident_e_sim_es_aux)
        ultimately show ?thesis using e_sim_es_def using p4 by blast 
      qed
    
  qed

lemma e_sim_es_same_assume: 
  "\<lbrakk>esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs;
      (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1);
      \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es);
      el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs); 
      e_sim_es esl el es e; esl\<in>assume_es(pre,rely)\<rbrakk>
      \<Longrightarrow> el\<in>assume_e(pre,rely)"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
      and  p2: "(EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      and  p3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es 
                    \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  p4: "el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)" 
      and  a1: "e_sim_es esl el es e"
      and  b0: "esl\<in>assume_es(pre,rely)"
    from p3 have p3_1: "\<forall>j. j > 0 \<and> Suc j < length esl \<longrightarrow> getspc_es (esl ! j) = EvtSys es 
          \<longrightarrow> getspc_es (esl ! Suc j) = EvtSys es" using noevtent_inmid_eq by auto

    let ?esl1 = "(EvtSeq ev (EvtSys es), s1,x1) # xs"
    let ?el1 = "rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"
    from p4 have a2: "el = (BasicEvent e, s, x) # (ev,s1,x1) # rm_evtsys xs" 
      by (simp add: gets_es_def getspc_es_def getx_es_def rm_evtsys1_def rm_evtsys_def) 
    from p1 a2 have a3: "length esl = length el" by (simp add:rm_evtsys_def)
    
    from b0 have b1: "gets_es (esl!0) \<in> pre \<and> (\<forall>i. Suc i<length esl \<longrightarrow> 
           esl!i -ese\<rightarrow> esl!(Suc i) \<longrightarrow> (gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely)"
      by (simp add:assume_es_def)
    then show ?thesis
      proof -
        from p1 p4 b1 have "gets_e (el!0) \<in> pre" using gets_es_def gets_e_def 
          by (metis nth_Cons_0 snd_conv)
        moreover
        have "\<forall>i. Suc i<length el \<longrightarrow> el!i -ee\<rightarrow> el!(Suc i) 
                \<longrightarrow> (gets_e (el!i), gets_e (el!Suc i)) \<in> rely"
          proof -
          {
            fix i
            assume c0: "Suc i<length el"
              and  c1: "el!i -ee\<rightarrow> el!(Suc i)"
            with a2 have "\<not>(el!0 -ee\<rightarrow> el!1)"
                by (metis One_nat_def eetran.simps evtsysent_evtent0 
                    no_tran2basic0 nth_Cons_0 nth_Cons_Suc p2) 
            with c1 have c2: "i \<noteq> 0" by (metis One_nat_def)
            with a1 have c3: "(getspc_es (esl!i) = EvtSys es \<and> getspc_e (el!i) = AnonyEvent None) 
                                  \<or> (getspc_es (esl!i) = EvtSeq (getspc_e (el!i)) (EvtSys es))"
               using e_sim_es_def Suc_lessD c0 by blast
            from c1 have c4: "getspc_e (el!i) = getspc_e (el!Suc i)"
              by (simp add: eetran_eqconf1) 
            from a1 c0 a3 have c5: "gets_es (esl!i) = gets_e (el!i) 
                              \<and> gets_es (esl!Suc i) = gets_e (el!Suc i)" by (simp add:e_sim_es_def)
            from a1 c0 a3 have c6: 
                        "(getspc_es (esl!Suc i) = EvtSys es \<and> getspc_e (el!Suc i) = AnonyEvent None) 
                         \<or> (getspc_es (esl!Suc i) = EvtSeq (getspc_e (el!Suc i)) (EvtSys es))"
               using e_sim_es_def by blast
            have "(gets_e (el!i), gets_e (el!Suc i)) \<in> rely"
              proof(cases "getspc_es (esl!i) = EvtSys es \<and> getspc_e (el!i) = AnonyEvent None")
                assume d0: "getspc_es (esl!i) = EvtSys es \<and> getspc_e (el!i) = AnonyEvent None"
                with c2 p3_1 c0 a3 have "getspc_es (esl!Suc i) = EvtSys es" by auto
                with d0 have "esl!i -ese\<rightarrow> esl!Suc i" by (simp add: eqconf_esetran) 
                with b1 c0 a3 have "(gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely" by auto
                then show ?thesis using c5 by simp
              next
                assume "\<not>(getspc_es (esl!i) = EvtSys es \<and> getspc_e (el!i) = AnonyEvent None)"
                with c3 have d0: "getspc_es (esl!i) = EvtSeq (getspc_e (el!i)) (EvtSys es)"
                  by simp
                let ?ei = "getspc_e (el!i)"
                show ?thesis
                  proof(cases "?ei = AnonyEvent None")
                    assume e0: "?ei = AnonyEvent None"
                    with c1 have e1: "getspc_e (el!Suc i) = AnonyEvent None"
                      using eetran_eqconf1 by fastforce 
                    show ?thesis
                      proof(cases "getspc_es (esl!Suc i) = EvtSys es \<and> getspc_e (el!Suc i) = AnonyEvent None")
                        assume f0: "getspc_es (esl!Suc i) = EvtSys es \<and> getspc_e (el!Suc i) = AnonyEvent None"
                        with d0 have "getspc_e (el!i) \<noteq> AnonyEvent None" 
                          proof -
                            let ?esl' = "drop i esl"
                            from p0 have "?esl'\<in>cpts_es"
                              by (metis Suc_lessD a3 c0 c2 cpts_es_dropi old.nat.exhaust) 
                            moreover
                            from c0 a3 have "length ?esl' > 1"
                              by auto
                            moreover
                            from d0 have "getspc_es (?esl'!0) = EvtSeq (getspc_e (el!i)) (EvtSys es)"
                              using a3 c0 by auto
                            moreover
                            from f0 have "getspc_es (?esl'!1) = EvtSys es"
                              using a3 c0 by fastforce 
                            ultimately show ?thesis using not_anonyevt_none_in_evtseq1 by blast
                          qed
                        with e0 show ?thesis by simp
                      next
                        assume "\<not>(getspc_es (esl!Suc i) = EvtSys es \<and> getspc_e (el!Suc i) = AnonyEvent None)"
                        with c6 have f0: "getspc_es (esl!Suc i) = EvtSeq (getspc_e (el!Suc i)) (EvtSys es)"
                          by simp
                        with c4 have "getspc_es (esl!Suc i) = EvtSeq (getspc_e (el!i)) (EvtSys es)" by simp
                        with d0 have "getspc_es (esl!Suc i) = getspc_es (esl!i)" by simp
                        then have "esl!i -ese\<rightarrow> esl!Suc i" by (simp add: eqconf_esetran) 
                        with b1 have "(gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely"
                          by (simp add: a3 c0) 
                        with c5 show ?thesis by simp
                      qed
                  next
                    assume e0: "?ei \<noteq> AnonyEvent None"
                    with c4 c6 have "getspc_es (esl!Suc i) = EvtSeq (getspc_e (el!Suc i)) (EvtSys es)" 
                      by simp
                    with c4 d0 have "getspc_es (esl!Suc i) = getspc_es (esl!i)" by simp
                    then have "esl!i -ese\<rightarrow> esl!Suc i" by (simp add: eqconf_esetran) 
                    with b1 have "(gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely"
                      by (simp add: a3 c0) 
                    with c5 show ?thesis by simp
                  qed
              qed
          }
          then show ?thesis by auto
          qed
        ultimately show ?thesis by (simp add:assume_e_def)
      qed
    qed

lemma e_sim_es_same_commit: 
  "\<lbrakk>esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs;
      (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1);
      \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es);
      el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs); 
      e_sim_es esl el es e; el\<in>commit_e(guar,post)\<rbrakk>
      \<Longrightarrow> esl\<in>commit_es(guar,post)"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
      and  p2: "(EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      and  p3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es 
                    \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  p4: "el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)" 
      and  a1: "e_sim_es esl el es e"
      and  b3: "el\<in>commit_e(guar,post)"
    from p3 have p3_1: "\<forall>j. j > 0 \<and> Suc j < length esl \<longrightarrow> getspc_es (esl ! j) = EvtSys es 
          \<longrightarrow> getspc_es (esl ! Suc j) = EvtSys es" using noevtent_inmid_eq by auto
    from p0 p1 p2 p3 p4 have a0: "el \<in> cpts_ev" using rm_evtsys_in_cptse by metis
    let ?esl1 = "(EvtSeq ev (EvtSys es), s1,x1) # xs"
    let ?el1 = "rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"
    from p4 have a2: "el = (BasicEvent e, s, x) # (ev,s1,x1) # rm_evtsys xs" 
      by (simp add: gets_es_def getspc_es_def getx_es_def rm_evtsys1_def rm_evtsys_def) 
    from p1 a2 have a3: "length esl = length el" by (simp add:rm_evtsys_def)

    from b3 have b4: "\<forall>i. Suc i<length el \<longrightarrow> 
               (\<exists>t. el!i -et-t\<rightarrow> el!(Suc i)) \<longrightarrow> (gets_e (el!i), gets_e (el!Suc i)) \<in> guar" 
               by (simp add:commit_e_def)
    then show "esl\<in>commit_es(guar,post)" 
      proof -
        have "\<forall>i. Suc i<length esl \<longrightarrow> (\<exists>t. esl!i -es-t\<rightarrow> esl!(Suc i)) 
              \<longrightarrow> (gets_es (esl!i), gets_es (esl!Suc i)) \<in> guar"
          proof -
          {
            fix i
            assume c0: "Suc i<length esl"
              and  c1: "\<exists>t. esl!i -es-t\<rightarrow> esl!(Suc i)"
            
            have "(gets_es (esl!i), gets_es (esl!Suc i)) \<in> guar"
              proof(cases "i = 0")
                assume d0: "i = 0"
                from p2 have "(BasicEvent e, s, x) -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (ev, s1, x1)"
                  using evtsysent_evtent by fastforce
                with a2 b4 have "(s, s1) \<in> guar" using gets_e_def
                  by (metis a3 c0 d0 fst_conv nth_Cons_0 nth_Cons_Suc snd_conv)
                with p1 show ?thesis by (simp add: gets_es_def d0)
              next
                assume d0: "i \<noteq> 0"
                then show ?thesis
                  proof(cases "getspc_es (esl!i) = EvtSys es")
                    assume e0: "getspc_es (esl!i) = EvtSys es"
                    with p3_1 c0 d0 have e1: "getspc_es (esl!Suc i) = EvtSys es" by simp
                    from c1 obtain t where "esl ! i -es-t\<rightarrow> esl ! Suc i" by auto
                    then have "getspc_es (esl!i) \<noteq> getspc_es (esl!Suc i)" 
                      using evtsys_not_eq_in_tran_aux1 by blast
                    with e0 e1 show ?thesis by simp
                  next
                    assume e0: "getspc_es (esl!i) \<noteq> EvtSys es"
                    from p0 p1 c0 have "getspc_es (esl!i) = EvtSys es \<or> 
                        (\<exists>e. getspc_es (esl!i) = EvtSeq e (EvtSys es))" 
                      using evtsys_all_es_in_cpts getspc_es_def
                      by (metis Suc_lessD fst_conv length_Cons nth_Cons_0 zero_less_Suc) 
                    with e0 have "\<exists>e. getspc_es (esl!i) = EvtSeq e (EvtSys es)" by simp
                    then obtain e where e1: "getspc_es (esl!i) = EvtSeq e (EvtSys es)" by auto
                    from p0 p1 c0 have e0_1: "getspc_es (esl!Suc i) = EvtSys es \<or> 
                        (\<exists>e. getspc_es (esl!Suc i) = EvtSeq e (EvtSys es))" 
                      using evtsys_all_es_in_cpts getspc_es_def 
                      by (metis fst_conv length_greater_0_conv list.distinct(1) nth_Cons_0)

                    obtain esi and si and xi and esi' and si' and xi' 
                      where e2: "esl!i = (esi,si,xi) \<and> esl!(Suc i) = (esi',si',xi')"
                      by (metis prod.collapse)
                    with c1 obtain t where e3: "(esi,si,xi) -es-t\<rightarrow> (esi',si',xi')" by auto
                    
                    from e0_1 show ?thesis
                      proof
                        assume f0: "getspc_es (esl!Suc i) = EvtSys es"
                        with e1 e2 e3 have "\<exists>t. (e, si, xi) -et-t\<rightarrow> (AnonyEvent (None), si',xi')"
                          by (simp add: evtseq_tran_0_exist_etran getspc_es_def) 
                        then obtain et where f1: "(e, si, xi) -et-et\<rightarrow> (AnonyEvent (None), si',xi')"
                          by auto
                        from p1 p4 a3 c0 d0 e1 e2 have f2:"el!i = (e, si, xi)"
                          using getspc_es_def getspc_e_def rm_evtsys_def rm_evtsys1_def 
                            gets_es_def getx_es_def EvtSeqrm
                            by (smt Suc_lessD fst_conv less_Suc_eq_0_disj list.simps(9) nth_Cons_Suc nth_map snd_conv)
                        moreover
                        from p1 p4 a3 c0 d0 e2 f0 have f3:"el!Suc i = (AnonyEvent (None), si',xi')"
                          using getspc_es_def getspc_e_def rm_evtsys_def rm_evtsys1_def 
                            gets_es_def getx_es_def EvtSysrm
                            by (smt List.nth_tl Suc_lessE diff_Suc_1 fst_conv 
                              length_tl list.sel(3) nth_map snd_conv)
                        ultimately have "(si,si')\<in>guar" using b4 f1 a3 c0 gets_e_def
                          by (metis fst_conv snd_conv)

                        with e2 show ?thesis by (simp add:gets_es_def)
                      next
                        assume f0: "\<exists>e. getspc_es (esl!Suc i) = EvtSeq e (EvtSys es)"
                        then obtain e' where f1: "getspc_es (esl!Suc i) = EvtSeq e' (EvtSys es)"
                          by auto
                        with e1 e2 e3 have "\<exists>t. (e, si, xi) -et-t\<rightarrow> (e', si', xi')" 
                          by (simp add: evtseq_tran_exist_etran getspc_es_def) 
                        moreover
                        from p1 p4 a3 c0 d0 e1 e2 have f2:"el!i = (e, si, xi)"
                          using getspc_es_def getspc_e_def rm_evtsys_def rm_evtsys1_def 
                            gets_es_def getx_es_def EvtSeqrm
                            by (smt Suc_lessD fst_conv less_Suc_eq_0_disj list.simps(9) nth_Cons_Suc nth_map snd_conv)
                        moreover
                        from p1 p4 a3 c0 d0 e2 f1 have f3:"el!Suc i = (e', si',xi')"
                          using getspc_es_def getspc_e_def rm_evtsys_def rm_evtsys1_def 
                            gets_es_def getx_es_def EvtSeqrm
                            by (smt Suc_lessD fst_conv less_Suc_eq_0_disj list.simps(9) nth_Cons_Suc nth_map snd_conv)
                        ultimately have "(si,si')\<in>guar" using b4 f1 a3 c0 gets_e_def
                          by (metis fst_conv snd_conv)

                        with e2 show ?thesis by (simp add:gets_es_def)
                      qed
                  qed
              qed
          }
          then show ?thesis by auto
          qed
        then show ?thesis by (simp add:commit_es_def)
      qed
  qed

lemma e_sim_es_same_preserve: 
  "\<lbrakk>esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs;
      (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1);
      \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es);
      el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs); 
      e_sim_es esl el es e; el\<in> preserves_e\<rbrakk>
      \<Longrightarrow> esl\<in> preserves_es"
proof -
  assume p0: "esl\<in>cpts_es"
    and  p1: "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
    and  p2: "(EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
    and  p3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es 
                    \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
    and  p4: "el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)" 
    and  a1: "e_sim_es esl el es e"
    and  b3: "el\<in>preserves_e"
    from p3 have p3_1: "\<forall>j. j > 0 \<and> Suc j < length esl \<longrightarrow> getspc_es (esl ! j) = EvtSys es 
          \<longrightarrow> getspc_es (esl ! Suc j) = EvtSys es" using noevtent_inmid_eq by auto
    from p0 p1 p2 p3 p4 have a0: "el \<in> cpts_ev" using rm_evtsys_in_cptse by metis
    let ?esl1 = "(EvtSeq ev (EvtSys es), s1,x1) # xs"
    let ?el1 = "rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"
    from p4 have a2: "el = (BasicEvent e, s, x) # (ev,s1,x1) # rm_evtsys xs" 
      by (simp add: gets_es_def getspc_es_def getx_es_def rm_evtsys1_def rm_evtsys_def) 
    from p1 a2 have a3: "length esl = length el" by (simp add:rm_evtsys_def)

    from b3 have b4: "\<forall>i. i<length el \<longrightarrow> ann_preserves_e (getspc_e (el!i)) (gets_e (el!i))" 
               by (simp add:preserves_e_def)
             then show "esl\<in>preserves_es" 
             proof -
               have "\<forall>i. i<length esl \<longrightarrow> ann_preserves_es (getspc_es (esl!i)) (gets_es (esl!i))"
               proof -
                 {
                   fix i
                   assume c0: "i<length esl"
            
                   have "ann_preserves_es (getspc_es (esl!i)) (gets_es (esl!i))"
                   proof(cases "i = 0")
                     assume d0: "i = 0"
                     from p1 d0 have "esl!i = (EvtSys es, s, x)" by simp
                     then show ?thesis by (simp add: getspc_es_def)
                   next
                     assume d0: "i \<noteq> 0"
                     then show ?thesis
                     proof(cases "getspc_es (esl!i) = EvtSys es")
                       assume e0: "getspc_es (esl!i) = EvtSys es"
                       then show ?thesis by (simp add: getspc_es_def)
                     next
                       assume e0: "getspc_es (esl!i) \<noteq> EvtSys es"
                       from p0 p1 c0 have "getspc_es (esl!i) = EvtSys es \<or> 
                        (\<exists>e. getspc_es (esl!i) = EvtSeq e (EvtSys es))" 
                         using evtsys_all_es_in_cpts getspc_es_def
                         by (metis fst_conv length_Cons nth_Cons_0 zero_less_Suc) 
                       with e0 have "\<exists>e. getspc_es (esl!i) = EvtSeq e (EvtSys es)" by simp
                       then obtain e where e1: "getspc_es (esl!i) = EvtSeq e (EvtSys es)" by auto

                       obtain esi and si and xi  where e2: "esl!i = (esi,si,xi)"
                         by (metis prod.collapse)
                    
                       with p1 p4 a3 c0 d0 e1 have f1 : "el!i = (e, si, xi)"
                         using getspc_es_def getspc_e_def rm_evtsys_def rm_evtsys1_def gets_es_def getx_es_def EvtSeqrm
                         by (smt Suc_lessD fst_conv less_Suc_eq_0_disj list.simps(9) nth_Cons_Suc nth_map snd_conv)
                       with a3 b4 c0  have "ann_preserves_e e si"
                         by (metis gets_e_def getspc_e_def prod.sel(1) prod.sel(2))
                       with e1 e2 f1 show ?thesis
                         by (simp add: gets_es_def)                     
                     qed
                   qed
                 }
          then show ?thesis by auto
        qed
        then show ?thesis by (simp add:preserves_es_def)
      qed
    qed

lemma rm_evtsys_assum_comm: 
    "\<lbrakk>esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs;
      (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1);
      \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es);
      el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs); 
      el\<in>assume_e(pre,rely) \<longrightarrow> el\<in>commit_e(guar,post) \<rbrakk>
      \<Longrightarrow> esl\<in>assume_es(pre,rely) \<longrightarrow> esl\<in>commit_es(guar,post)" 
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
      and  p2: "(EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      and  p3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es 
                    \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  p4: "el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)" 
      and  p5: "el\<in>assume_e(pre,rely) \<longrightarrow> el\<in>commit_e(guar,post)"
    from p3 have p3_1: "\<forall>j. j > 0 \<and> Suc j < length esl \<longrightarrow> getspc_es (esl ! j) = EvtSys es 
          \<longrightarrow> getspc_es (esl ! Suc j) = EvtSys es" using noevtent_inmid_eq by auto
    from p0 p1 p2 p3 p4 have a0: "el \<in> cpts_ev" using rm_evtsys_in_cptse by metis
    let ?esl1 = "(EvtSeq ev (EvtSys es), s1,x1) # xs"
    let ?el1 = "rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"
    from p0 p1 p2 p3 p4 a0 have a1: "e_sim_es esl el es e" 
      using fstent_nomident_e_sim_es2 by metis
    from p4 have a2: "el = (BasicEvent e, s, x) # (ev,s1,x1) # rm_evtsys xs" 
      by (simp add: gets_es_def getspc_es_def getx_es_def rm_evtsys1_def rm_evtsys_def) 
    from p1 a2 have a3: "length esl = length el" by (simp add:rm_evtsys_def)
    show ?thesis
      proof 
        assume b0: "esl\<in>assume_es(pre,rely)"
        with p0 p1 p2 p3 p4 a1 have b2: "el\<in>assume_e(pre,rely)" using e_sim_es_same_assume by metis
        with p5 have b3: "el\<in>commit_e(guar,post)" by simp
        with p0 p1 p2 p3 p4 a1 show "esl\<in>commit_es(guar,post)" using e_sim_es_same_commit by metis
      qed
  qed


lemma rm_evtsys_assum_preserve: 
    "\<lbrakk>esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs;
      (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1);
      \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es);
      el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs); 
      el\<in>assume_e(pre,rely) \<longrightarrow> el\<in> preserves_e \<rbrakk>
      \<Longrightarrow> esl\<in>assume_es(pre,rely) \<longrightarrow> esl\<in> preserves_es" 
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
      and  p2: "(EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      and  p3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es 
                    \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  p4: "el = (BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)" 
      and  p5: "el\<in>assume_e(pre,rely) \<longrightarrow> el\<in> preserves_e"
    from p3 have p3_1: "\<forall>j. j > 0 \<and> Suc j < length esl \<longrightarrow> getspc_es (esl ! j) = EvtSys es 
          \<longrightarrow> getspc_es (esl ! Suc j) = EvtSys es" using noevtent_inmid_eq by auto
    from p0 p1 p2 p3 p4 have a0: "el \<in> cpts_ev" using rm_evtsys_in_cptse by metis
    let ?esl1 = "(EvtSeq ev (EvtSys es), s1,x1) # xs"
    let ?el1 = "rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"
    from p0 p1 p2 p3 p4 a0 have a1: "e_sim_es esl el es e" 
      using fstent_nomident_e_sim_es2 by metis
    from p4 have a2: "el = (BasicEvent e, s, x) # (ev,s1,x1) # rm_evtsys xs" 
      by (simp add: gets_es_def getspc_es_def getx_es_def rm_evtsys1_def rm_evtsys_def) 
    from p1 a2 have a3: "length esl = length el" by (simp add:rm_evtsys_def)
    show ?thesis
      proof 
        assume b0: "esl\<in>assume_es(pre,rely)"
        with p0 p1 p2 p3 p4 a1 have b2: "el\<in>assume_e(pre,rely)" using e_sim_es_same_assume by metis
        with p5 have b3: "el\<in> preserves_e" by simp
        with p0 p1 p2 p3 p4 a1 show "esl\<in> preserves_es" using e_sim_es_same_preserve by metis
      qed
    qed

lemma EventSys_sound_aux1: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     esl\<in>cpts_es;length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es;
     \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)\<rbrakk>
      \<Longrightarrow> \<exists>m\<in>es. (esl\<in>assume_es(Pre m,Rely m) \<longrightarrow> esl\<in>commit_es(Guar m,Post m)) 
                          \<and> (\<exists>k. esl!0-es-(EvtEnt m)\<sharp>k\<rightarrow>esl!1)"
  proof -
    assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  a0: "length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es"
      and  c41: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  c1: "esl\<in>cpts_es"

    from a0 c1 have c2: "\<exists>s x ev s1 x1 xs. esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
      by (simp add:fst_esys_snd_eseq_exist)
    then obtain s and x and ev and s1 and x1 and xs where c3:
      "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs" by auto
    with c1 have "\<exists>e k. (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      using fst_esys_snd_eseq_exist_evtent2 by fastforce
    then obtain e and k where c4: 
      "(EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      by auto
    let ?el = "(BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"
    
    from c1 c3 c4 c41 have c5: "?el \<in> cpts_ev" using rm_evtsys_in_cptse by metis
    from c4 have "\<exists>ei\<in>es. ei = BasicEvent e" using evtsysent_evtent by metis
    then obtain ei where c6: "ei\<in>es \<and> ei = BasicEvent e" by auto
    from c3 c4 c6 have c61: "esl!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>esl!1" by simp
    have c8: "?el\<in>assume_e(Pre ei, Rely ei) \<longrightarrow> ?el\<in>commit_e(Guar ei,Post ei)" 
      proof 
        assume d0: "?el\<in>assume_e(Pre ei, Rely ei)"
        moreover
        from p0 c6 have d1: "\<Turnstile> ei sat\<^sub>e [Pre ei, Rely ei, Guar ei, Post ei]" by auto
        moreover
        from c5 have "?el\<in>cpts_of_ev (BasicEvent e) s x" by (simp add:cpts_of_ev_def)
        ultimately show "?el\<in>commit_e(Guar ei,Post ei)" using evt_validity_def c6
          by fastforce 
      qed
    with c1 c3 c4 c41 have c7: "esl\<in>assume_es(Pre ei, Rely ei) \<longrightarrow> esl\<in>commit_es(Guar ei,Post ei)"
      using rm_evtsys_assum_comm by metis
    then show ?thesis using c6 c61 by blast
  qed         

lemma EventSys_sound_aux1_preserve: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     esl\<in>cpts_es;length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es;
     \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)\<rbrakk>
      \<Longrightarrow> \<exists>m\<in>es. (esl\<in>assume_es(Pre m,Rely m) \<longrightarrow> esl\<in> preserves_es)"
  proof -
    assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  a0: "length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es"
      and  c41: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  c1: "esl\<in>cpts_es"

    from a0 c1 have c2: "\<exists>s x ev s1 x1 xs. esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
      by (simp add:fst_esys_snd_eseq_exist)
    then obtain s and x and ev and s1 and x1 and xs where c3:
      "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs" by auto
    with c1 have "\<exists>e k. (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      using fst_esys_snd_eseq_exist_evtent2 by fastforce
    then obtain e and k where c4: 
      "(EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      by auto
    let ?el = "(BasicEvent e, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"
    
    from c1 c3 c4 c41 have c5: "?el \<in> cpts_ev" using rm_evtsys_in_cptse by metis
    from c4 have "\<exists>ei\<in>es. ei = BasicEvent e" using evtsysent_evtent by metis
    then obtain ei where c6: "ei\<in>es \<and> ei = BasicEvent e" by auto
    from c3 c4 c6 have c61: "esl!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>esl!1" by simp
    have c8: "?el\<in>assume_e(Pre ei, Rely ei) \<longrightarrow> ?el\<in> preserves_e" 
      proof 
        assume d0: "?el\<in>assume_e(Pre ei, Rely ei)"
        moreover
        from p0 c6 have d1: "\<Turnstile> ei sat\<^sub>e [Pre ei, Rely ei, Guar ei, Post ei]" by auto
        moreover
        from c5 have "?el\<in>cpts_of_ev (BasicEvent e) s x" by (simp add:cpts_of_ev_def)
        ultimately show "?el\<in> preserves_e" using evt_validity_def c6
          by fastforce 
      qed
    with c1 c3 c4 c41 have c7: "esl\<in>assume_es(Pre ei, Rely ei) \<longrightarrow> esl\<in> preserves_es"
      using rm_evtsys_assum_preserve by metis
    then show ?thesis using c6 c61 by blast
  qed    

lemma EventSys_sound_aux1_forall: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     esl\<in>cpts_es;length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es;
     \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)\<rbrakk>
      \<Longrightarrow> \<forall>m\<in>es. (\<exists>k. esl!0-es-(EvtEnt m)\<sharp>k\<rightarrow>esl!1) 
                          \<longrightarrow> (esl\<in>assume_es(Pre m,Rely m) \<longrightarrow> esl\<in>commit_es(Guar m,Post m))"
  proof -
    assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  a0: "length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es"
      and  c41: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  c1: "esl\<in>cpts_es"
    then show ?thesis
      proof -
      {
        fix m
        assume c01: "m\<in>es"
          and  c02: "\<exists>k. esl!0-es-(EvtEnt m)\<sharp>k\<rightarrow>esl!1"
        from a0 c1 have c2: "\<exists>s x ev s1 x1 xs. esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
          by (simp add:fst_esys_snd_eseq_exist)
        then obtain s and x and ev and s1 and x1 and xs where c3:
          "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs" by auto
        with c02 have "\<exists>k. (EvtSys es, s, x) -es-(EvtEnt m)\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)" by simp
        then obtain k where c4: "(EvtSys es, s, x) -es-(EvtEnt m)\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)" by auto
        then have "\<exists>e. m = BasicEvent e" by (meson evtent_is_basicevt) 
        then obtain e where c40: "m = BasicEvent e" by auto
        let ?el = "(m, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"    
        from c1 c3 c4 c40 c41 have c5: "?el \<in> cpts_ev" using rm_evtsys_in_cptse by metis

        from c3 c4 c40 have c61: "esl!0-es-(EvtEnt m)\<sharp>k\<rightarrow>esl!1" by simp
        have c8: "?el\<in>assume_e(Pre m, Rely m) \<longrightarrow> ?el\<in>commit_e(Guar m,Post m)" 
          proof 
            assume d0: "?el\<in>assume_e(Pre m, Rely m)"
            moreover
            from p0 c01 c40 have d1: "\<Turnstile> m sat\<^sub>e [Pre m, Rely m, Guar m, Post m]" by auto
            moreover
            from c5 c40 have "?el\<in>cpts_of_ev (BasicEvent e) s x" by (simp add:cpts_of_ev_def)
            ultimately show "?el\<in>commit_e(Guar m,Post m)" using evt_validity_def c40
              by fastforce 
          qed
        with c1 c3 c4 c40 c41 have c7: "esl\<in>assume_es(Pre m, Rely m) \<longrightarrow> esl\<in>commit_es(Guar m,Post m)"
          using rm_evtsys_assum_comm by metis
      }
      then show ?thesis by auto
      qed
  qed

lemma EventSys_sound_aux1_forall_preserve: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     esl\<in>cpts_es;length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es;
     \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)\<rbrakk>
      \<Longrightarrow> \<forall>m\<in>es. (\<exists>k. esl!0-es-(EvtEnt m)\<sharp>k\<rightarrow>esl!1) 
                          \<longrightarrow> (esl\<in>assume_es(Pre m,Rely m) \<longrightarrow> esl\<in> preserves_es)"
  proof -
    assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  a0: "length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es"
      and  c41: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  c1: "esl\<in>cpts_es"
    then show ?thesis
      proof -
      {
        fix m
        assume c01: "m\<in>es"
          and  c02: "\<exists>k. esl!0-es-(EvtEnt m)\<sharp>k\<rightarrow>esl!1"
        from a0 c1 have c2: "\<exists>s x ev s1 x1 xs. esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
          by (simp add:fst_esys_snd_eseq_exist)
        then obtain s and x and ev and s1 and x1 and xs where c3:
          "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs" by auto
        with c02 have "\<exists>k. (EvtSys es, s, x) -es-(EvtEnt m)\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)" by simp
        then obtain k where c4: "(EvtSys es, s, x) -es-(EvtEnt m)\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)" by auto
        then have "\<exists>e. m = BasicEvent e" by (meson evtent_is_basicevt) 
        then obtain e where c40: "m = BasicEvent e" by auto
        let ?el = "(m, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"    
        from c1 c3 c4 c40 c41 have c5: "?el \<in> cpts_ev" using rm_evtsys_in_cptse by metis

        from c3 c4 c40 have c61: "esl!0-es-(EvtEnt m)\<sharp>k\<rightarrow>esl!1" by simp
        have c8: "?el\<in>assume_e(Pre m, Rely m) \<longrightarrow> ?el\<in> preserves_e" 
          proof 
            assume d0: "?el\<in>assume_e(Pre m, Rely m)"
            moreover
            from p0 c01 c40 have d1: "\<Turnstile> m sat\<^sub>e [Pre m, Rely m, Guar m, Post m]" by auto
            moreover
            from c5 c40 have "?el\<in>cpts_of_ev (BasicEvent e) s x" by (simp add:cpts_of_ev_def)
            ultimately show "?el\<in> preserves_e" using evt_validity_def c40
              by fastforce 
          qed
        with c1 c3 c4 c40 c41 have c7: "esl\<in>assume_es(Pre m, Rely m) \<longrightarrow> esl\<in>preserves_es"
          using rm_evtsys_assum_preserve by metis
      }
      then show ?thesis by auto
      qed
    qed

lemma EventSys_sound_seg_aux0_exist: 
    "\<lbrakk>esl\<in>cpts_es;length esl \<ge> 2; getspc_es (esl!0) = EvtSys es; getspc_es (esl!1) \<noteq> EvtSys es\<rbrakk>
      \<Longrightarrow> \<exists>m\<in>es. (\<exists>k. esl!0-es-(EvtEnt m)\<sharp>k\<rightarrow>esl!1)"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "length esl \<ge> 2"
      and  p2: "getspc_es (esl!0) = EvtSys es"
      and  p3: "getspc_es (esl!1) \<noteq> EvtSys es"
    then have a1: "\<exists>s x ev s1 x1 xs. esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
      by (simp add:fst_esys_snd_eseq_exist)
    then obtain s and x and ev and s1 and x1 and xs where a2:
      "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs" by auto
    with p0 a1 have "\<exists>e k. (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      using fst_esys_snd_eseq_exist_evtent2 by fastforce
    then obtain e and k where a3: 
      "(EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
      by auto
    from a3 have "\<exists>i\<in>es. i = BasicEvent e" using evtsysent_evtent by metis
    then obtain ei where c6: "ei\<in> es \<and> ei = BasicEvent e" by auto
    then show ?thesis using One_nat_def a2 a3 nth_Cons_0 nth_Cons_Suc by force 
  qed

lemma EventSys_sound_seg_aux0_forall: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     esl\<in>cpts_es;length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es;
     getspc_es (last esl) = EvtSys es;
     \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)\<rbrakk>
      \<Longrightarrow> \<forall>ei\<in>es. (\<exists>k. esl!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>esl!1) 
                              \<longrightarrow> (esl\<in>assume_es(Pre ei,Rely ei) \<longrightarrow> esl\<in>commit_es(Guar ei,Post ei)
                                    \<and> gets_es (last esl) \<in> Post ei)"
  proof -
    assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  a0: "length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es"
      and  p6: "getspc_es (last esl) = EvtSys es"
      and  c41: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  c1: "esl\<in>cpts_es"
    then show ?thesis
      proof-
      {
        fix ei
        assume c01: "ei\<in>es"
          and  c02: "\<exists>k. esl!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>esl!1"        

        from a0 c1 have c2: "\<exists>s x ev s1 x1 xs. esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
          by (simp add:fst_esys_snd_eseq_exist)
        then obtain s and x and ev and s1 and x1 and xs where c3:
          "esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs" by auto
        with c02 have "\<exists>k. (EvtSys es, s, x) -es-(EvtEnt ei)\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)" by simp
        then obtain k where c4: "(EvtSys es, s, x) -es-(EvtEnt ei)\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)" by auto
        then have "\<exists>e. ei = BasicEvent e" by (meson evtent_is_basicevt) 
        then obtain e where c6: "ei = BasicEvent e" by auto
        let ?el = "(ei, s, x) # rm_evtsys ((EvtSeq ev (EvtSys es), s1,x1) # xs)"    
        from c1 c3 c4 c6 c41 have c5: "?el \<in> cpts_ev" using rm_evtsys_in_cptse by metis


        from c3 c4 c6 have c61: "esl!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>esl!1" by simp
        have c8: "?el\<in>assume_e(Pre ei, Rely ei) \<longrightarrow> ?el\<in>commit_e(Guar ei,Post ei)" 
          proof 
            assume d0: "?el\<in>assume_e(Pre ei, Rely ei)"
            moreover
            from p0 c01 c6 have d1: "\<Turnstile> ei sat\<^sub>e [Pre ei, Rely ei, Guar ei, Post ei]" by auto
            moreover
            from c5 c6 have "?el\<in>cpts_of_ev (BasicEvent e) s x" by (simp add:cpts_of_ev_def)
            ultimately show "?el\<in>commit_e(Guar ei,Post ei)" using evt_validity_def c6
              by fastforce 
          qed
        with c1 c3 c4 c41 c6 have c7: "esl\<in>assume_es(Pre ei, Rely ei) \<longrightarrow> esl\<in>commit_es(Guar ei,Post ei)"
          using rm_evtsys_assum_comm by metis
        moreover 
        have "esl\<in>assume_es(Pre ei, Rely ei) \<longrightarrow> gets_es (last esl) \<in> Post ei"
          proof 
            assume d0: "esl\<in>assume_es(Pre ei, Rely ei)"
            from c1 c3 c4 c41 c5 c6 have d2: "e_sim_es esl ?el es e" using fstent_nomident_e_sim_es2 by metis
            with c1 c3 c4 c41 c5 c6 d0 have d3: "?el\<in>assume_e(Pre ei, Rely ei)" 
              using e_sim_es_same_assume by metis
            with c8 have d1: "?el\<in>commit_e(Guar ei,Post ei)" by auto
    
            have d4: "getspc_e (last ?el) = AnonyEvent None"
              proof -
                from a0 d2 have e1: "length ?el = length esl" by (simp add: e_sim_es_def) 
                with d2 have "\<forall>i. i > 0 \<and> i < length ?el \<longrightarrow> 
                                        (getspc_es (esl!i) = EvtSys es \<and> getspc_e (?el!i) = AnonyEvent None) 
                                          \<or> (getspc_es (esl!i) = EvtSeq (getspc_e (?el!i)) (EvtSys es))"
                  by (simp add: e_sim_es_def) 
                with a0 e1 have "(getspc_es (last esl) = EvtSys es \<and> getspc_e (last ?el) = AnonyEvent None) 
                                          \<or> (getspc_es (last esl) = EvtSeq (getspc_e (last ?el)) (EvtSys es))"
                  by (metis (no_types, hide_lams) c3 last_length length_Cons length_tl lessI list.sel(3) zero_less_Suc)
                with p6 show ?thesis by simp
              qed
            with d1 have "gets_e (last ?el) \<in> Post ei" by (simp add: commit_e_def)
            moreover
            from a0 d2 have "gets_e (last ?el) = gets_es (last esl)" using e_sim_es_def
              proof -
                from a0 d2 have e1: "length ?el = length esl" by (simp add: e_sim_es_def)
                with d2 have "\<forall>i. i < length ?el \<longrightarrow> gets_e (?el ! i) = gets_es (esl ! i) \<and>
                                                            getx_e (?el ! i) = getx_es (esl ! i)"
                  by (simp add: e_sim_es_def) 
                with a0 e1 show ?thesis by (metis (no_types, hide_lams) c3 last_length 
                        length_Cons length_tl lessI list.sel(3)) 
              qed
            ultimately show "gets_es (last esl) \<in> Post ei" by simp
          qed

        ultimately have "(esl\<in>assume_es(Pre ei,Rely ei) \<longrightarrow> esl\<in>commit_es(Guar ei,Post ei)
                                    \<and> gets_es (last esl) \<in> Post ei)" by simp
      }
      then show ?thesis by auto
      qed
    qed

lemma EventSys_sound_seg_aux0: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     esl\<in>cpts_es;length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es;
     getspc_es (last esl) = EvtSys es;
     \<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)\<rbrakk>
      \<Longrightarrow> \<exists>m\<in>es. (esl\<in>assume_es(Pre m,Rely m) \<longrightarrow> esl\<in>commit_es(Guar m,Post m)
                                \<and> gets_es (last esl) \<in> Post m)
                        \<and> (\<exists>k. esl!0-es-(EvtEnt m)\<sharp>k\<rightarrow>esl!1)"
  proof -
    assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  p1: "length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es"
      and  p2: "getspc_es (last esl) = EvtSys es"
      and  p3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl!j) = EvtSys es \<and> getspc_es (esl!Suc j) \<noteq> EvtSys es)"
      and  p4: "esl\<in>cpts_es"
    then have "\<exists>m\<in>es. (\<exists>k. esl!0-es-(EvtEnt m)\<sharp>k\<rightarrow>esl!1)" 
      using EventSys_sound_seg_aux0_exist[of esl es] by simp
    then obtain m where a1: "m\<in> es \<and> (\<exists>k. esl!0-es-(EvtEnt m)\<sharp>k\<rightarrow>esl!1)" by auto
    with p0 p1 p2 p3 p4 have "(esl\<in>assume_es(Pre m,Rely m) \<longrightarrow> esl\<in>commit_es(Guar m,Post m)
                                \<and> gets_es (last esl) \<in> Post m)" 
      using EventSys_sound_seg_aux0_forall [of es Pre Rely Guar Post esl] by simp
    with a1 show ?thesis by auto
  qed


lemma EventSys_sound_aux_i_forall: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     \<forall>ef\<in>es. pre \<subseteq> Pre ef;  \<forall>ef\<in>es. rely \<subseteq> Rely ef;
     \<forall>ef\<in>es. Guar ef \<subseteq> guar; \<forall>ef\<in>es. Post ef \<subseteq> post;
     \<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2;
     esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs;
     esl\<in>assume_es(pre,rely);
     elst = tl (parse_es_cpts_i2 esl es [[]])\<rbrakk>
      \<Longrightarrow> \<forall>i. Suc i < length elst \<longrightarrow> 
                (\<forall>ei\<in>es. (\<exists>k. (elst!i@[(elst!Suc i)!0])!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>(elst!i@[(elst!Suc i)!0])!1) 
                                  \<longrightarrow> elst!i@[(elst!Suc i)!0]\<in>commit_es(Guar ei,Post ei)
                                      \<and> gets_es ((elst!Suc i)!0) \<in> Post ei)"
  proof -
    assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  p1: "\<forall>ef\<in>es. pre \<subseteq> Pre ef"
      and  p2: "\<forall>ef\<in>es. rely \<subseteq> Rely ef"
      and  p3: "\<forall>ef\<in>es. Guar ef \<subseteq> guar"
      and  p4: "\<forall>ef\<in>es. Post ef \<subseteq> post"
      and  p5[rule_format]: "\<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2"
      and  p8: "esl\<in>cpts_es"
      and  p9: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p10: "esl\<in>assume_es(pre,rely)"
      and  p11: "elst = tl (parse_es_cpts_i2 esl es [[]])"
    from p9 p8 p11 have a0[rule_format]: "\<forall>i. i < length elst \<longrightarrow> length (elst!i) \<ge> 2 \<and>
                  getspc_es (elst!i!0) = EvtSys es \<and> getspc_es (elst!i!1) \<noteq> EvtSys es"
      using parse_es_cpts_i2_start_aux by metis
    from p9 p8 p11 have a1: "\<forall>i. i < length elst \<longrightarrow> 
                 \<not>(\<exists>j. j > 0 \<and> Suc j < length (elst!i) \<and> 
                 getspc_es (elst!i!j) = EvtSys es \<and> getspc_es (elst!i!Suc j) \<noteq> EvtSys es)"
      using parse_es_cpts_i2_noent_mid by metis
    from p9 p8 p11 have a2: "concat elst = esl" using parse_es_cpts_i2_concat3 by metis
    show ?thesis
      proof -
      {
        fix i
        assume b0: "Suc i < length elst"
        then have "\<forall>ei\<in>es. (\<exists>k. (elst!i@[(elst!Suc i)!0])!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>(elst!i@[(elst!Suc i)!0])!1) 
                                  \<longrightarrow> elst!i@[(elst!Suc i)!0]\<in>commit_es(Guar ei,Post ei)
                                      \<and> gets_es ((elst!Suc i)!0) \<in> Post ei"
              proof(induct i)
                case 0
                assume c0: "Suc 0 < length elst" 
                let ?els = "elst ! 0 @ [elst ! Suc 0 ! 0]"
                have c1: "?els \<in> cpts_es"
                  proof -
                    from a0 have c11: "\<forall>i<length elst. elst ! i \<noteq> []"
                      using list.size(3) not_numeral_le_zero by force
                    with a2 c0 have "\<exists>m n. m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n \<and> ?els = take (n - m) (drop m esl)"
                      using concat_i_lm by blast
                    then obtain m and n where d1: "m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n 
                          \<and> ?els = take (n - m) (drop m esl)" by auto
                    have "?els \<noteq> []" by simp
                    with p8 d1 show ?thesis by (simp add: cpts_es_seg2) 
                    qed
                
                have c2: "getspc_es (last ?els) = EvtSys es" by (simp add: a0 c0) 
                have c3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length ?els \<and> getspc_es (?els!j) = EvtSys es 
                  \<and> getspc_es (?els!Suc j) \<noteq> EvtSys es)" 
                  proof -
                    from a0 have "getspc_es (elst ! Suc 0 ! 0) = EvtSys es" using c0 by blast
                    with a1 show ?thesis by (metis (no_types, lifting) Suc_leI Suc_lessD 
                      Suc_lessE c0 diff_Suc_1 diff_is_0_eq' length_append_singleton nth_Cons_0 nth_append) 
                  qed
                from a0 have c4: "2 \<le> length ?els \<and> getspc_es (?els ! 0) = EvtSys es \<and> getspc_es (?els ! 1) \<noteq> EvtSys es"
                  by (metis (no_types, hide_lams) Suc_1 Suc_eq_plus1_left Suc_le_lessD 
                      Suc_lessD add.right_neutral c0 length_append_singleton not_less nth_append)
                with p0 c1 c2 c3 have c5: "\<forall>ei\<in>es. (\<exists>k. ?els!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>?els!1) 
                              \<longrightarrow> (?els\<in>assume_es(Pre ei,Rely ei) \<longrightarrow> ?els\<in>commit_es(Guar ei,Post ei)
                                    \<and> gets_es (last ?els) \<in> Post ei)"
                  using EventSys_sound_seg_aux0_forall[of es Pre Rely Guar Post ?els] by auto
                
                from p10 a2 have "?els\<in>assume_es(pre,rely)"
                  proof -
                    from a0 have d1: "\<forall>i<length elst. elst ! i \<noteq> []" 
                      using list.size(3) not_numeral_le_zero by force
                    with a2 c0 have "\<exists>m n. m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n \<and> ?els = take (n - m) (drop m esl)"
                      using concat_i_lm by blast
                    moreover
                    from p10 have "\<forall>i. Suc i<length esl \<longrightarrow> esl!i -ese\<rightarrow> esl!(Suc i) \<longrightarrow> 
                        (gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely" by (simp add:assume_es_def)
                    ultimately have "\<forall>i. Suc i<length ?els \<longrightarrow> ?els!i -ese\<rightarrow> ?els!(Suc i) \<longrightarrow> 
                        (gets_es (?els!i), gets_es (?els!Suc i)) \<in> rely"
                        using rely_takedrop_rely by blast
                    moreover
                    have "gets_es (?els!0) \<in> pre"
                      proof -
                        from a2 have "?els!0 = esl!0"
                          by (metis (no_types, lifting) Suc_lessD d1 
                              c0 concat.simps(2) cpts_es_not_empty hd_append2 
                              length_greater_0_conv list.collapse nth_Cons_0 p8 snoc_eq_iff_butlast)
                        moreover
                        from p10 have "gets_es (esl!0) \<in> pre" by (simp add:assume_es_def)
                        ultimately show ?thesis by simp
                      qed
                    ultimately show ?thesis by (simp add:assume_es_def)
                  qed
    
                with p1 p2 c5 have "\<forall>ei\<in>es. ?els\<in>assume_es(Pre ei, Rely ei)" using assume_es_imp
                  by metis
                with c5 show ?case by auto
              next
                case (Suc j)
                let ?elstjj = "elst ! j @ [elst ! Suc j ! 0]"
                let ?els = "elst ! Suc j @ [elst ! Suc (Suc j) ! 0]"
                assume c01: "Suc j < length elst 
                            \<Longrightarrow> \<forall>ei\<in>es. (\<exists>k. ?elstjj ! 0 -es-EvtEnt ei\<sharp>k\<rightarrow> ?elstjj ! 1) \<longrightarrow>
                             ?elstjj \<in> commit_es (Guar ei, Post ei) \<and> gets_es (elst ! Suc j ! 0) \<in> Post ei"
                 and   c02: "Suc (Suc j) < length elst"
                then show ?case
                  proof-
                  {
                    fix ei
                    assume d0: "ei\<in>es"
                      and  d1: "\<exists>k. ?els ! 0 -es-EvtEnt ei\<sharp>k\<rightarrow> ?els ! 1"

                    from c02 a0[of j] have "\<exists>m\<in>es. (\<exists>k. ?elstjj!0-es-(EvtEnt m)\<sharp>k\<rightarrow>?elstjj!1)"
                      using EventSys_sound_seg_aux0_exist[of ?elstjj es] p8 p9 p11
                        by (smt One_nat_def Suc_1 Suc_le_lessD Suc_lessD le_SucI length_append_singleton 
                          nth_append parse_es_cpts_i2_in_cptes_i) 
    
                    then obtain ei' where c03: "ei'\<in>es \<and> (\<exists>k. ?elstjj!0-es-(EvtEnt ei')\<sharp>k\<rightarrow>?elstjj!1)"
                      by auto
                    with c01 c02 have c04: "?elstjj \<in> commit_es (Guar ei', Post ei') 
                                        \<and> gets_es (elst ! Suc j ! 0) \<in> Post ei'"
                      by auto
    
                    have c1: "?els \<in> cpts_es"
                      proof -
                        from a0 have c11: "\<forall>i<length elst. elst ! i \<noteq> []" 
                          using list.size(3) not_numeral_le_zero by force
                        with a2 c02 have "\<exists>m n. m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n \<and> ?els = take (n - m) (drop m esl)"
                          using concat_i_lm by blast
                        then obtain m and n where d1: "m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n 
                              \<and> ?els = take (n - m) (drop m esl)" by auto
                        have "?els \<noteq> []" by simp
                        with p8 d1 show ?thesis by (simp add: cpts_es_seg2) 
                        qed
                    
                    have c2: "getspc_es (last ?els) = EvtSys es" by (simp add: a0 c02) 
                    have c3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length ?els \<and> getspc_es (?els!j) = EvtSys es 
                      \<and> getspc_es (?els!Suc j) \<noteq> EvtSys es)" 
                      proof -
                        from a0 have "getspc_es (elst ! Suc (Suc j) ! 0) = EvtSys es" using c02 by blast
                        with a1 show ?thesis by (metis (no_types, lifting) Suc_leI Suc_lessD 
                          Suc_lessE c02 diff_Suc_1 diff_is_0_eq' length_append_singleton nth_Cons_0 nth_append) 
                      qed
                    from a0 have c4: "2 \<le> length ?els \<and> getspc_es (?els ! 0) = EvtSys es \<and> getspc_es (?els ! 1) \<noteq> EvtSys es"
                      by (metis (no_types, hide_lams) Suc_1 Suc_eq_plus1_left Suc_le_lessD 
                          Suc_lessD add.right_neutral c02 length_append_singleton not_less nth_append)
        
                    with p0 c1 c2 c3 d0 d1 have c5: "(?els\<in>assume_es(Pre ei,Rely ei) \<longrightarrow> ?els\<in>commit_es(Guar ei,Post ei)
                                \<and> gets_es (last ?els) \<in> Post ei)" 
                      using EventSys_sound_seg_aux0_forall[of es Pre Rely Guar Post ?els] by blast
                    from p10 a2 have "?els\<in>assume_es(Pre ei,rely)"
                      proof -
                        from a0 have d1: "\<forall>i<length elst. elst ! i \<noteq> []"
                          using list.size(3) not_numeral_le_zero by force
                        with a2 c02 have "\<exists>m n. m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n \<and> ?els = take (n - m) (drop m esl)"
                          using concat_i_lm by blast
                        moreover
                        from p10 have "\<forall>i. Suc i<length esl \<longrightarrow> esl!i -ese\<rightarrow> esl!(Suc i) \<longrightarrow> 
                            (gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely" by (simp add:assume_es_def)
                        ultimately have "\<forall>i. Suc i<length ?els \<longrightarrow> ?els!i -ese\<rightarrow> ?els!(Suc i) \<longrightarrow> 
                            (gets_es (?els!i), gets_es (?els!Suc i)) \<in> rely"
                            using rely_takedrop_rely by blast
                        moreover
                        have "gets_es (?els!0) \<in> Pre ei"
                          proof -
                            from p5[of ei' ei] d0 c03 c04 have "gets_es (elst ! Suc j ! 0) \<in> Pre ei"
                               by blast 
                            then show ?thesis by (simp add: Suc_lessD c02 d1 nth_append) 
                          qed
                        ultimately show ?thesis by (simp add:assume_es_def)
                      qed
        
                    with p2 have "?els\<in>assume_es(Pre ei, Rely ei)" 
                      using assume_es_imp[of "Pre ei" "Pre ei" rely "Rely ei"]
                       d0 order_refl by auto
                      
                    with c5 have c6: "?els\<in>commit_es(Guar ei,Post ei) \<and> gets_es (last ?els) \<in> Post ei" by simp
                  }
                  then show ?thesis by auto
                  qed
              qed
      }
      then show ?thesis by auto
      qed
  qed


lemma EventSys_sound_aux_i: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     \<forall>ef\<in>es. pre \<subseteq> Pre ef;  \<forall>ef\<in>es. rely \<subseteq> Rely ef;
     \<forall>ef\<in>es. Guar ef \<subseteq> guar; \<forall>ef\<in>es. Post ef \<subseteq> post;
     \<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2;
     esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs;
     esl\<in>assume_es(pre,rely);
     elst = tl (parse_es_cpts_i2 esl es [[]])\<rbrakk>
      \<Longrightarrow> \<forall>i. Suc i < length elst \<longrightarrow> 
                (\<exists>m\<in>es. elst!i@[(elst!Suc i)!0]\<in>commit_es(Guar m,Post m)
                                \<and> gets_es ((elst!Suc i)!0) \<in> Post m
                \<and> (\<exists>k. (elst!i@[(elst!Suc i)!0])!0-es-(EvtEnt m)\<sharp>k\<rightarrow>(elst!i@[(elst!Suc i)!0])!1))"
  proof -
    assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  p1: "\<forall>ef\<in>es. pre \<subseteq> Pre ef"
      and  p2: "\<forall>ef\<in>es. rely \<subseteq> Rely ef"
      and  p3: "\<forall>ef\<in>es. Guar ef \<subseteq> guar"
      and  p4: "\<forall>ef\<in>es. Post ef \<subseteq> post"
      and  p5: "\<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2"
      and  p8: "esl\<in>cpts_es"
      and  p9: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p10: "esl\<in>assume_es(pre,rely)"
      and  p11: "elst = tl (parse_es_cpts_i2 esl es [[]])"
    from p9 p8 p11 have a0[rule_format]: "\<forall>i. i < length elst \<longrightarrow> length (elst!i) \<ge> 2 \<and>
                  getspc_es (elst!i!0) = EvtSys es \<and> getspc_es (elst!i!1) \<noteq> EvtSys es"
      using parse_es_cpts_i2_start_aux by metis
    from p9 p8 p11 have a1: "\<forall>i. i < length elst \<longrightarrow> 
                 \<not>(\<exists>j. j > 0 \<and> Suc j < length (elst!i) \<and> 
                 getspc_es (elst!i!j) = EvtSys es \<and> getspc_es (elst!i!Suc j) \<noteq> EvtSys es)"
      using parse_es_cpts_i2_noent_mid by metis
    from p9 p8 p11 have a2: "concat elst = esl" using parse_es_cpts_i2_concat3 by metis
    show ?thesis
      proof -
      {
        fix i
        assume b0: "Suc i < length elst"
        with a0[of i] have "\<exists>m\<in>es. (\<exists>k. elst!i!0-es-(EvtEnt m)\<sharp>k\<rightarrow>elst!i!1)" 
          using EventSys_sound_seg_aux0_exist[of "elst!i@[(elst!Suc i)!0]" es] 
            parse_es_cpts_i2_in_cptes_i[of esl es s x e s1 x1 xs elst]
            by (smt Suc_1 Suc_le_lessD Suc_lessD le_SucI length_append_singleton 
              length_greater_0_conv list.size(3) not_numeral_le_zero nth_append p11 p8 p9) 
        then obtain m where b1: "m\<in>es \<and> (\<exists>k. elst!i!0-es-(EvtEnt m)\<sharp>k\<rightarrow>elst!i!1)" by auto
        with p0 p1 p2 p3 p4 p5 p8 p9 p10 p11 b0
        have b2[rule_format]: "\<forall>i. Suc i < length elst \<longrightarrow> (\<forall>ei\<in>es.
            (\<exists>k. (elst ! i @ [elst ! Suc i ! 0]) ! 0 -es-EvtEnt ei\<sharp>k\<rightarrow> (elst ! i @ [elst ! Suc i ! 0]) ! 1) \<longrightarrow>
            elst ! i @ [elst ! Suc i ! 0] \<in> commit_es (Guar ei, Post ei) \<and> gets_es (elst ! Suc i ! 0) \<in> Post ei)"
          using EventSys_sound_aux_i_forall[of es Pre Rely Guar Post pre rely guar post esl s x e s1 x1 xs elst] 
            by fastforce
        from b0 b1 b2[of i m] have "elst!i@[(elst!Suc i)!0]\<in>commit_es(Guar m,Post m)
                 \<and> gets_es ((elst!Suc i)!0) \<in> Post m"
           by (metis (no_types, lifting) Suc_1 Suc_le_lessD Suc_lessD a0 length_greater_0_conv 
              list.size(3) not_numeral_le_zero nth_append) 
        with b1 have "\<exists>m\<in>es. elst!i@[(elst!Suc i)!0]\<in>commit_es(Guar m,Post m)
                  \<and> gets_es ((elst!Suc i)!0) \<in> Post m 
                  \<and> (\<exists>k. (elst!i@[(elst!Suc i)!0])!0-es-(EvtEnt m)\<sharp>k\<rightarrow>(elst!i@[(elst!Suc i)!0])!1)"
           by (smt One_nat_def Suc_lessD a0 b0 lessI less_le_trans nth_append numeral_2_eq_2) 

      }
      then show ?thesis by auto
      qed
    qed


lemma EventSys_sound_aux_last_forall: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     \<forall>ef\<in>es. pre \<subseteq> Pre ef;  \<forall>ef\<in>es. rely \<subseteq> Rely ef;
     \<forall>ef\<in>es. Guar ef \<subseteq> guar; \<forall>ef\<in>es. Post ef \<subseteq> post;
     \<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2;
     esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs;
     esl\<in>assume_es(pre,rely);
     elst = tl (parse_es_cpts_i2 esl es [[]])\<rbrakk>
      \<Longrightarrow> \<forall>ei\<in>es. (\<exists>k. (last elst)!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>(last elst)!1) 
                           \<longrightarrow> last elst\<in>commit_es(Guar ei,Post ei)"
  proof -
    assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  p1: "\<forall>ef\<in>es. pre \<subseteq> Pre ef"
      and  p2: "\<forall>ef\<in>es. rely \<subseteq> Rely ef"
      and  p3: "\<forall>ef\<in>es. Guar ef \<subseteq> guar"
      and  p4: "\<forall>ef\<in>es. Post ef \<subseteq> post"
      and  p5: "\<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2"
      and  p8: "esl\<in>cpts_es"
      and  p9: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p10: "esl\<in>assume_es(pre,rely)"
      and  p11: "elst = tl (parse_es_cpts_i2 esl es [[]])"
    from p9 p8 p11 have a0[rule_format]: "\<forall>i. i < length elst \<longrightarrow> length (elst!i) \<ge> 2 \<and>
                  getspc_es (elst!i!0) = EvtSys es \<and> getspc_es (elst!i!1) \<noteq> EvtSys es"
      using parse_es_cpts_i2_start_aux by metis
    from p9 p8 p11 have a1: "\<forall>i. i < length elst \<longrightarrow> 
                 \<not>(\<exists>j. j > 0 \<and> Suc j < length (elst!i) \<and> 
                 getspc_es (elst!i!j) = EvtSys es \<and> getspc_es (elst!i!Suc j) \<noteq> EvtSys es)"
      using parse_es_cpts_i2_noent_mid by metis
    from p9 p8 p11 have a2: "concat elst = esl" using parse_es_cpts_i2_concat3 by metis
    with p9  have a3: "elst \<noteq> []" by auto
    show ?thesis
    proof -
    {
      fix ei
      assume a01: "ei\<in>es"
        and  a02: "\<exists>k. (last elst)!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>(last elst)!1"
      have "last elst\<in>commit_es(Guar ei,Post ei)"
      proof(cases "length elst = 1")
        assume b0: "length elst = 1"
        from a2 b0 have b1: "last elst = esl"
          by (metis (no_types, lifting) One_nat_def a3 append_butlast_last_id append_self_conv2 concat.simps(1) concat.simps(2) diff_Suc_1 length_0_conv length_butlast self_append_conv) 
        let ?els = "elst ! 0"
        from p8 a2 b0 have c1: "?els \<in> cpts_es" using b1 a3 last_conv_nth by fastforce 
        
        from a1 b0 have c3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length ?els \<and> getspc_es (?els!j) = EvtSys es 
          \<and> getspc_es (?els!Suc j) \<noteq> EvtSys es)" by simp 
        from a0 b0 have c4: "2 \<le> length ?els \<and> getspc_es (?els ! 0) = EvtSys es \<and> getspc_es (?els ! 1) \<noteq> EvtSys es"
          by simp
        
        with p0 c1 c3 have c5: "\<forall>m\<in>es. (\<exists>k. ?els!0-es-(EvtEnt m)\<sharp>k\<rightarrow>?els!1) 
                          \<longrightarrow> (?els\<in>assume_es(Pre m,Rely m) \<longrightarrow> ?els\<in>commit_es(Guar m,Post m))"
          using EventSys_sound_aux1_forall[of es Pre Rely Guar Post ?els] by fastforce

        from p10 a2 have "?els\<in>assume_es(pre,rely)"
          proof -
            
            from a2 b0 have "\<exists>m n. m \<le> length esl \<and> last elst = (drop m esl)"
              using concat_last_lm using b1 by auto 
            moreover
            from p10 have "\<forall>i. Suc i<length esl \<longrightarrow> esl!i -ese\<rightarrow> esl!(Suc i) \<longrightarrow> 
                (gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely" by (simp add:assume_es_def)
            ultimately have "\<forall>i. Suc i<length ?els \<longrightarrow> ?els!i -ese\<rightarrow> ?els!(Suc i) \<longrightarrow> 
                (gets_es (?els!i), gets_es (?els!Suc i)) \<in> rely"
                using a3 b0 b1 last_conv_nth by force
            moreover
            have "gets_es (?els!0) \<in> pre"
              proof -
                from a2 have "?els!0 = esl!0"
                  using a3 b0 b1 last_conv_nth by fastforce
                moreover
                from p10 have "gets_es (esl!0) \<in> pre" by (simp add:assume_es_def)
                ultimately show ?thesis by simp
              qed
            ultimately show ?thesis by (simp add:assume_es_def)
          qed

        with p1 p2 a01 have "?els\<in>assume_es(Pre ei, Rely ei)" 
          using assume_es_imp[of pre "Pre ei" rely "Rely ei" "elst ! 0"] by simp
        with a01 a02 c5 have c6: "?els\<in>commit_es(Guar ei,Post ei)"
          by (simp add: a3 b0 last_conv_nth) 
        with c5 show ?thesis using a3 b0 last_conv_nth by (metis One_nat_def diff_Suc_1) 
      next
        assume "length elst \<noteq> 1"
        with a3 have b0: "length elst > 1" by (simp add: Suc_lessI) 
        let ?els = "last elst"
        from p8 a2 b0 have c1: "?els \<in> cpts_es" 
          proof -
            from a2 b0 have "\<exists>m . m \<le> length esl \<and> ?els = drop m esl"
              by (simp add: concat_last_lm a3) 

            then obtain m where d1: "m \<le> length esl \<and> ?els = drop m esl" by auto
            with a0 have "m < length esl"
              by (metis One_nat_def a3 diff_less drop_all last_conv_nth le_less_linear 
                  length_greater_0_conv list.size(3) not_less_eq not_numeral_le_zero) 
            with p8 d1 show ?thesis using cpts_es_dropi
              by (metis drop_0 le_0_eq le_SucE zero_induct) 
          qed

        from a1 b0 have c3: "\<not>(\<exists>j. j > 0 \<and> Suc j < length ?els \<and> getspc_es (?els!j) = EvtSys es 
          \<and> getspc_es (?els!Suc j) \<noteq> EvtSys es)"
            by (metis One_nat_def Suc_lessD a3 diff_less last_conv_nth zero_less_one)  
        from a0 b0 have c4: "2 \<le> length ?els \<and> getspc_es (?els ! 0) = EvtSys es \<and> getspc_es (?els ! 1) \<noteq> EvtSys es"
          by (simp add: a3 last_conv_nth)
          
        with p0 c1 c3 have c5: "\<forall>m\<in>es. (\<exists>k. ?els!0-es-(EvtEnt m)\<sharp>k\<rightarrow>?els!1) 
                          \<longrightarrow> (?els\<in>assume_es(Pre m,Rely m) \<longrightarrow> ?els\<in>commit_es(Guar m,Post m))"
          using EventSys_sound_aux1_forall[of es Pre Rely Guar Post ?els] by fastforce

        from p10 a2 have c6: "?els\<in>assume_es(Pre ei,rely)"
          proof -
            from a2 b0 have "\<exists>m . m \<le> length esl \<and> ?els = drop m esl"
              by (simp add: concat_last_lm a3) 
            moreover
            from p10 have "\<forall>i. Suc i<length esl \<longrightarrow> esl!i -ese\<rightarrow> esl!(Suc i) \<longrightarrow> 
                (gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely" by (simp add:assume_es_def)
            ultimately have "\<forall>i. Suc i<length ?els \<longrightarrow> ?els!i -ese\<rightarrow> ?els!(Suc i) \<longrightarrow> 
                (gets_es (?els!i), gets_es (?els!Suc i)) \<in> rely"
                using a3 b0 last_conv_nth by force
            moreover
            have "gets_es (?els!0) \<in> Pre ei"
              proof -
                from p0 p1 p2 p3 p4 p5 p8 p9 p10 p11
                have c1[rule_format]: "\<forall>i. Suc i < length elst \<longrightarrow> 
                (\<forall>ei\<in>es. (\<exists>k. (elst!i@[(elst!Suc i)!0])!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>(elst!i@[(elst!Suc i)!0])!1) 
                                  \<longrightarrow> elst!i@[(elst!Suc i)!0]\<in>commit_es(Guar ei,Post ei)
                                      \<and> gets_es ((elst!Suc i)!0) \<in> Post ei)" 
                   using EventSys_sound_aux_i_forall[of es Pre Rely Guar Post pre rely guar 
                          post esl s x e s1 x1 xs elst] by blast
                let ?els1 = "elst!(length elst - 2)@[(elst!(length elst - 1))!0]"
                have d1: "?els1 \<in> cpts_es"
                  proof -
                    from a0 have c11: "\<forall>i<length elst. elst ! i \<noteq> []"
                      using list.size(3) not_numeral_le_zero by force
                    with a2 b0 have "\<exists>m n. m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n \<and> ?els1 = take (n - m) (drop m esl)"
                      using concat_i_lm[of elst esl "length elst - 2"]
                        by (metis (no_types, lifting) Suc_1 Suc_diff_1 
                            Suc_diff_Suc a3 length_greater_0_conv lessI) 
                    then obtain m and n where d1: "m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n 
                          \<and> ?els1 = take (n - m) (drop m esl)" by auto
                    have "?els1 \<noteq> []" by simp
                    with p8 d1 show ?thesis by (simp add: cpts_es_seg2) 
                    qed
                moreover
                have "length ?els1 > 2" using a0[of "length elst - 2"]
                  by (simp add: a3) 
                moreover
                have "getspc_es (?els1 ! 0) = EvtSys es \<and> getspc_es (?els1 ! 1) \<noteq> EvtSys es"
                  using a0[of "length elst - 2"] by (metis (no_types, lifting) One_nat_def 
                      Suc_lessD Suc_less_SucD b0 calculation(2) diff_less 
                      length_append_singleton nth_append numeral_2_eq_2 zero_less_numeral)  
                ultimately have "\<exists>m\<in>es. (\<exists>k. ?els1!0-es-(EvtEnt m)\<sharp>k\<rightarrow>?els1!1)"
                  using EventSys_sound_seg_aux0_exist[of ?els1 es] by simp
                then obtain m where d2: "m\<in>es \<and> (\<exists>k. ?els1!0-es-(EvtEnt m)\<sharp>k\<rightarrow>?els1!1)"
                  by auto
                then have "gets_es (elst ! (length elst - 1) ! 0) \<in> Post m" 
                  using c1[of "length elst - 2" m] by (metis (no_types, lifting) One_nat_def 
                    Suc_diff_Suc Suc_lessD b0 diff_less le_imp_less_Suc le_numeral_extra(3) numeral_2_eq_2)
              
                then have "gets_es (last elst ! 0) \<in> Post m"
                  by (simp add: a3 last_conv_nth) 
                with p5 a01 d2 show ?thesis by auto
              qed
            ultimately show ?thesis by (simp add:assume_es_def)
          qed
        moreover 
        from p1 p2 have "rely \<subseteq> Rely ei" by (simp add: a01)  
        ultimately have "?els\<in>assume_es(Pre ei, Rely ei)" 
          using assume_es_imp by blast 
        with c5 have c6: "?els\<in>commit_es(Guar ei,Post ei)" using a01 a02 by blast 
        
        with c5 show ?thesis using a3 b0 last_conv_nth by blast
      qed
    }
    then show ?thesis by auto qed
  qed

lemma EventSys_sound_aux_last:                                                                   
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     \<forall>ef\<in>es. pre \<subseteq> Pre ef;  \<forall>ef\<in>es. rely \<subseteq> Rely ef;
     \<forall>ef\<in>es. Guar ef \<subseteq> guar; \<forall>ef\<in>es. Post ef \<subseteq> post;
     \<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2;
     esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs;
     esl\<in>assume_es(pre,rely);
     elst = tl (parse_es_cpts_i2 esl es [[]])\<rbrakk>
      \<Longrightarrow> \<exists>m\<in>es. last elst\<in>commit_es(Guar m,Post m) 
                        \<and> (\<exists>k. (last elst)!0-es-(EvtEnt m)\<sharp>k\<rightarrow>(last elst)!1)"
  proof -
    assume  p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  p1: "\<forall>ef\<in>es. pre \<subseteq> Pre ef"
      and  p2: "\<forall>ef\<in>es. rely \<subseteq> Rely ef"
      and  p3: "\<forall>ef\<in>es. Guar ef \<subseteq> guar"
      and  p4: "\<forall>ef\<in>es. Post ef \<subseteq> post"
      and  p5: "\<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2"
      and  p8: "esl\<in>cpts_es"
      and  p9: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p10: "esl\<in>assume_es(pre,rely)"
      and  p11: "elst = tl (parse_es_cpts_i2 esl es [[]])"
    from p9 p8 p11 have a0[rule_format]: "\<forall>i. i < length elst \<longrightarrow> length (elst!i) \<ge> 2 \<and>
                  getspc_es (elst!i!0) = EvtSys es \<and> getspc_es (elst!i!1) \<noteq> EvtSys es"
      using parse_es_cpts_i2_start_aux by metis
    from p9 p8 p11 have a1: "\<forall>i. i < length elst \<longrightarrow> 
                 \<not>(\<exists>j. j > 0 \<and> Suc j < length (elst!i) \<and> 
                 getspc_es (elst!i!j) = EvtSys es \<and> getspc_es (elst!i!Suc j) \<noteq> EvtSys es)"
      using parse_es_cpts_i2_noent_mid by metis
    from p9 p8 p11 have a2: "concat elst = esl" using parse_es_cpts_i2_concat3 by metis
    with p9  have a3: "elst \<noteq> []" by auto
    from p8 p9 p11 a0[of "length elst - 1"] have "\<exists>m\<in>es. (\<exists>k. last elst!0-es-(EvtEnt m)\<sharp>k\<rightarrow>last elst!1)" 
      using EventSys_sound_seg_aux0_exist[of "last elst" es] 
        parse_es_cpts_i2_in_cptes_last[of esl es s x e s1 x1 xs elst]
        by (metis a3 diff_less last_conv_nth length_greater_0_conv less_one)
    then obtain m where b1: "m\<in>es \<and> (\<exists>k. last elst!0-es-(EvtEnt m)\<sharp>k\<rightarrow>last elst!1)" by auto
    with p0 p1 p2 p3 p4 p5 p8 p9 p10 p11
    have "last elst\<in>commit_es(Guar m,Post m)"
      using EventSys_sound_aux_last_forall[of es Pre Rely Guar Post pre 
        rely guar post esl s x e s1 x1 xs elst] by blast
    with b1 show ?thesis by auto
  qed

lemma EventSys_sound_aux_i_preserve: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     \<forall>ef\<in>es. pre \<subseteq> Pre ef;  \<forall>ef\<in>es. rely \<subseteq> Rely ef;
     \<forall>ef\<in>es. Guar ef \<subseteq> guar; \<forall>ef\<in>es. Post ef \<subseteq> post;
     \<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2;
     esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs;
     esl\<in>assume_es(pre,rely);
     elst = tl (parse_es_cpts_i2 esl es [[]]); i < length elst\<rbrakk> \<Longrightarrow> 
     elst ! i \<in> preserves_es"
proof -
  assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
    and  p1: "\<forall>ef\<in>es. pre \<subseteq> Pre ef"
    and  p2: "\<forall>ef\<in>es. rely \<subseteq> Rely ef"
    and  p3: "\<forall>ef\<in>es. Guar ef \<subseteq> guar"
    and  p4: "\<forall>ef\<in>es. Post ef \<subseteq> post"
    and  p5[rule_format]: "\<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2"
    and  p8: "esl\<in>cpts_es"
    and  p9: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
    and  p10: "esl\<in>assume_es(pre,rely)"
    and  p11: "elst = tl (parse_es_cpts_i2 esl es [[]])"
    and p12: "i < length elst"
  from p9 p8 p11 have a0[rule_format]: "\<forall>i. i < length elst \<longrightarrow> length (elst!i) \<ge> 2 \<and>
                  getspc_es (elst!i!0) = EvtSys es \<and> getspc_es (elst!i!1) \<noteq> EvtSys es"
    using parse_es_cpts_i2_start_aux by metis
  from p9 p8 p11 have a1: "\<forall>i. i < length elst \<longrightarrow> \<not>(\<exists>j. j > 0 \<and> Suc j < length (elst!i) \<and> 
            getspc_es (elst!i!j) = EvtSys es \<and> getspc_es (elst!i!Suc j) \<noteq> EvtSys es)"
    using parse_es_cpts_i2_noent_mid by metis
  from p9 p8 p11 have a2: "concat elst = esl" using parse_es_cpts_i2_concat3 by metis
  show ?thesis
  proof-
    {
      assume b0: " i < length elst"
      then have "elst ! i \<in> preserves_es"
      proof (induct i)
        case 0
        let ?els = "elst ! 0 "
        have c1: "?els \<in> cpts_es"
        proof -
          from a0 have c11: "\<forall>i<length elst. elst ! i \<noteq> []"
            using list.size(3) not_numeral_le_zero by force
             with a2 "0.prems" have "\<exists>m n. m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n \<and> ?els = take (n - m) (drop m esl)"
               using concat_i_lm1 by blast
             then obtain m and n where d1: "m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n
                          \<and> ?els = take (n - m) (drop m esl)" by auto
             have "?els \<noteq> []" using "0.prems" c11 by blast
             with p8 d1 show ?thesis by (simp add: cpts_es_seg2) 
           qed
           have c2: "\<not>(\<exists>j. j > 0 \<and> Suc j < length ?els \<and> getspc_es (?els!j) = EvtSys es 
                     \<and> getspc_es (?els!Suc j) \<noteq> EvtSys es)" 
           proof -
             from a0 have "getspc_es (elst ! 0 ! 0) = EvtSys es" using "0.prems" by blast
             with a1 show ?thesis  using "0.prems" by blast
           qed
           from a0 have c3: "2 \<le> length ?els \<and> getspc_es (?els ! 0) = EvtSys es \<and> getspc_es (?els ! 1) \<noteq> EvtSys es"
             using "0.prems" by blast
           with p0 c1 c2  have c4: "\<forall>ei\<in>es. (\<exists>k. ?els!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>?els!1) 
               \<longrightarrow> (?els\<in>assume_es(Pre ei,Rely ei) \<longrightarrow> ?els \<in> preserves_es)"
             using EventSys_sound_aux1_forall_preserve[of es Pre Rely Guar Post ?els] by auto

           from p10 a2 have "?els\<in>assume_es(pre,rely)"
           proof -
             from a0 have d1: "\<forall>i<length elst. elst ! i \<noteq> []" 
               using list.size(3) not_numeral_le_zero by force
             with a2 "0.prems" have "\<exists>m n. m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n \<and> ?els = take (n - m) (drop m esl)"
               using concat_i_lm1 by blast
             moreover
             from p10 have "\<forall>i. Suc i<length esl \<longrightarrow> esl!i -ese\<rightarrow> esl!(Suc i) \<longrightarrow> 
                  (gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely" by (simp add:assume_es_def)
             ultimately have "\<forall>i. Suc i<length ?els \<longrightarrow> ?els!i -ese\<rightarrow> ?els!(Suc i) \<longrightarrow> 
               (gets_es (?els!i), gets_es (?els!Suc i)) \<in> rely"
               using rely_takedrop_rely by blast
             moreover
             have "gets_es (?els!0) \<in> pre"
             proof -
               from a2 "0.prems" have "?els!0 = esl!0"
                 by (metis (no_types, lifting) d1 concat.simps(2) cpts_es_not_empty 
                     hd_append2 length_greater_0_conv list.collapse nth_Cons_0 p8 )
               moreover
               from p10 have "gets_es (esl!0) \<in> pre" by (simp add:assume_es_def)
               ultimately show ?thesis by simp
             qed
             ultimately show ?thesis by (simp add:assume_es_def)
           qed

           with p1 p2 c4 have "\<forall>ei\<in>es. ?els\<in>assume_es(Pre ei, Rely ei)" using assume_es_imp
             by metis

           with c1 c3 c4 show ?case using EventSys_sound_seg_aux0_exist by blast
         next
           case (Suc j)
           let ?els = "elst ! (Suc j)"
           have c21 : "?els \<in> cpts_es"
           proof-
             from a0 have c11: "\<forall>i<length elst. elst ! i \<noteq> []"
            using list.size(3) not_numeral_le_zero by force
          with a2  have "\<exists>m n. m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n \<and> ?els = take (n - m) (drop m esl)"
               using concat_i_lm1 Suc.prems by blast
             then obtain m and n where d1: "m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n
                          \<and> ?els = take (n - m) (drop m esl)" by auto
             have "?els \<noteq> []" using Suc.prems c11 by blast
             with p8 d1 show ?thesis by (simp add: cpts_es_seg2) 
           qed
           have c22: "\<not>(\<exists>j. j > 0 \<and> Suc j < length ?els \<and> getspc_es (?els!j) = EvtSys es 
                     \<and> getspc_es (?els!Suc j) \<noteq> EvtSys es)" 
           proof -
             from a0 have "getspc_es (elst ! 0 ! 0) = EvtSys es" using Suc.prems by fastforce
             with a1 show ?thesis  using Suc.prems by blast
           qed
           from a0 have c23: "2 \<le> length ?els \<and> getspc_es (?els ! 0) = EvtSys es \<and> getspc_es (?els ! 1) \<noteq> EvtSys es"
             using Suc.prems by blast
           with p0 c21 c22 have c23: "\<forall>ei\<in>es. (\<exists>k. ?els!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>?els!1) 
               \<longrightarrow> (?els\<in>assume_es(Pre ei,Rely ei) \<longrightarrow> ?els \<in> preserves_es)"
             using EventSys_sound_aux1_forall_preserve[of es Pre Rely Guar Post ?els] by auto

           have "\<exists>m\<in>es. (\<exists>k. ?els!0-es-(EvtEnt m)\<sharp>k\<rightarrow>?els!1)"
             using EventSys_sound_seg_aux0_exist Suc.prems a0 c21 by blast
           then obtain ei where c24: "ei \<in> es \<and> (\<exists>k. ?els!0-es-(EvtEnt ei)\<sharp>k\<rightarrow>?els!1)" by blast


           with p10 a2 have "?els\<in> assume_es(Pre ei, Rely ei)"
           proof -
             from a0 have d21: "\<forall>i<length elst. elst ! i \<noteq> []" 
               using list.size(3) not_numeral_le_zero by force
             with a2 Suc.prems have "\<exists>m n. m \<le> length esl \<and> n \<le> length esl \<and> m \<le> n \<and> ?els = take (n - m) (drop m esl)"
               using concat_i_lm1 by blast
             moreover
             from p10 have "\<forall>i. Suc i<length esl \<longrightarrow> esl!i -ese\<rightarrow> esl!(Suc i) \<longrightarrow> 
                  (gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely" by (simp add:assume_es_def)
             then have "\<forall>i. Suc i<length ?els \<longrightarrow> ?els!i -ese\<rightarrow> ?els!(Suc i) \<longrightarrow> 
               (gets_es (?els!i), gets_es (?els!Suc i)) \<in> rely"
               using rely_takedrop_rely calculation by blast
             ultimately have "\<forall>i. Suc i<length ?els \<longrightarrow> ?els!i -ese\<rightarrow> ?els!(Suc i) \<longrightarrow> 
               (gets_es (?els!i), gets_es (?els!Suc i)) \<in> Rely ei"
               using c24 p2 by blast
             moreover
             have "gets_es (?els!0) \<in> Pre ei"
             proof-
               from p0 p1 p2 p3 p4 p5 p8 p9 p10 p11 have "\<forall>i. Suc i < length elst \<longrightarrow> 
                (\<exists>m\<in>es. elst!i@[(elst!Suc i)!0]\<in>commit_es(Guar m,Post m)
                                \<and> gets_es ((elst!Suc i)!0) \<in> Post m
                \<and> (\<exists>k. (elst!i@[(elst!Suc i)!0])!0-es-(EvtEnt m)\<sharp>k\<rightarrow>(elst!i@[(elst!Suc i)!0])!1))"
                 using EventSys_sound_aux_i [of es Pre Rely Guar Post pre rely guar post esl s x e s1 x1 xs elst]
                 by auto[1]
               then have "\<exists>m \<in> es. gets_es ((elst!Suc j)!0) \<in> Post m"
                 using Suc.prems by auto
               then have "gets_es ((elst!Suc j)!0) \<in> Pre ei"
                 by (meson c24 contra_subsetD p5)
               then show ?thesis by simp
             qed

             ultimately show ?thesis by (simp add:assume_es_def)
           qed

           with c21 c23 c24 show ?case by blast
         qed
       }
       with p12 show ?thesis by auto
     qed
   qed


lemma EventSys_sound_0: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     \<forall>ef\<in>es. pre \<subseteq> Pre ef;  \<forall>ef\<in>es. rely \<subseteq> Rely ef;
     \<forall>ef\<in>es. Guar ef \<subseteq> guar; \<forall>ef\<in>es. Post ef \<subseteq> post;
     \<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2;
     stable pre rely; \<forall>s. (s, s)\<in>guar;
     esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs;
     esl\<in>assume_es(pre,rely)\<rbrakk>
      \<Longrightarrow> \<forall>i. Suc i<length esl \<longrightarrow> (\<exists>t. esl!i -es-t\<rightarrow> esl!(Suc i)) \<longrightarrow> 
                          (gets_es (esl!i), gets_es (esl!Suc i)) \<in> guar"
  proof -
    assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  p1: "\<forall>ef\<in>es. pre \<subseteq> Pre ef"
      and  p2: "\<forall>ef\<in>es. rely \<subseteq> Rely ef"
      and  p3: "\<forall>ef\<in>es. Guar ef \<subseteq> guar"
      and  p4: "\<forall>ef\<in>es. Post ef \<subseteq> post"
      and  p5: "\<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2"
      and  p6: "stable pre rely"
      and  p7: "\<forall>s. (s, s)\<in>guar"
      and  p8: "esl\<in>cpts_es"
      and  p9: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p10: "esl\<in>assume_es(pre,rely)"
    let ?elst = "tl (parse_es_cpts_i2 esl es [[]])"
    from p9 p8 have a0: "concat ?elst = esl" using parse_es_cpts_i2_concat3 by metis  

    from p9 p8 have a1: "\<forall>i. i < length ?elst \<longrightarrow> length (?elst!i) \<ge> 2 \<and>
                  getspc_es (?elst!i!0) = EvtSys es \<and> getspc_es (?elst!i!1) \<noteq> EvtSys es"
      using parse_es_cpts_i2_start_aux by metis

    from p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    have "\<forall>i. Suc i < length ?elst \<longrightarrow> 
                (\<exists>m\<in>es. ?elst!i@[(?elst!Suc i)!0]\<in>commit_es(Guar m,Post m)
                                \<and> gets_es ((?elst!Suc i)!0) \<in> Post m)"
      using EventSys_sound_aux_i 
        [of es Pre Rely Guar Post pre rely guar post esl s x e s1 x1 xs ?elst] by blast
    then have a2: "\<forall>i. Suc i < length ?elst \<longrightarrow> 
                (\<exists>m\<in>es. ?elst!i@[(?elst!Suc i)!0]\<in>commit_es(Guar m,Post m))" by auto

    from p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    have a3: "\<exists>m\<in>es. last ?elst\<in>commit_es(Guar m,Post m)"
      using EventSys_sound_aux_last
        [of es Pre Rely Guar Post pre rely guar post esl s x e s1 x1 xs ?elst] by blast
    then obtain m where a4: "m\<in>es \<and> last ?elst\<in>commit_es(Guar m,Post m)" by auto
    show ?thesis 
      proof -
      {
        fix i
        assume b0: "Suc i < length esl"
          and  b1: "\<exists>t. esl ! i -es-t\<rightarrow> esl ! Suc i"
        from p9 have b01: "esl \<noteq> []" by simp
        moreover
        from a1 have b3: "\<forall>i<length ?elst. length (?elst!i) \<ge> 2" by simp
        ultimately have "\<exists>k j. k < length ?elst \<and> j \<le> length (?elst!k) \<and> 
                  drop i esl = (drop j (?elst!k)) @ concat (drop (Suc k) ?elst)"
          using concat_equiv [of esl ?elst] a0 b0 by auto
        then obtain k and j where b2: "k < length ?elst \<and> j \<le> length (?elst!k) \<and> 
                  drop i esl = (drop j (?elst!k)) @ concat (drop (Suc k) ?elst)" by auto
        have "(gets_es (esl!i), gets_es (esl!Suc i)) \<in> guar"
          proof(cases "k = length ?elst - 1")
            assume c0: "k = length ?elst - 1"
            with b2 have c1: "drop i esl = drop j (last ?elst)"
              by (metis (no_types, lifting) Nitpick.size_list_simp(2) Suc_leI b01 
                  a0 concat.simps(1) drop_all last_conv_nth length_tl self_append_conv)
            with b0 b01 have c2: "drop j (last ?elst) \<noteq> []" by auto
            with b2 c0 have c3: "j < length (last ?elst)" by auto
            with c1 have c4: "esl ! i = (last ?elst) ! j"
              by (metis Suc_lessD b0 hd_drop_conv_nth) 
            from c1 c3 have c5: "esl ! Suc i = (last ?elst) ! Suc j"
              by (metis Cons_nth_drop_Suc Suc_lessD b0 list.sel(3) nth_via_drop) 
            from a4 have "\<forall>i. Suc i<length (last ?elst) \<longrightarrow> (\<exists>t. (last ?elst)!i -es-t\<rightarrow> (last ?elst)!(Suc i)) 
                  \<longrightarrow> (gets_es ((last ?elst)!i), gets_es ((last ?elst)!Suc i)) \<in> Guar m" 
              by (simp add: commit_es_def)
            with b1 c3 c4 c5 have "(gets_es (esl ! i), gets_es (esl ! Suc i)) \<in> Guar m"
              by (metis Cons_nth_drop_Suc b0 c1 length_drop list.sel(3) zero_less_diff) 
            with p3 a4 show ?thesis by auto
          next
            assume c00: "k \<noteq> length ?elst - 1"
            with b2 have c0: "k < length ?elst - 1" by auto
            show ?thesis
              proof(cases "j = length (?elst!k)")
                assume d0: "j = length (?elst!k)"
                with b2 have d1: "drop i esl = concat (drop (Suc k) ?elst)" by auto
                from b3 c0 have d2: "length (?elst ! (Suc k)) \<ge> 2" by auto
                from c0 have "concat (drop (Suc k) ?elst) = ?elst ! (Suc k) @ concat (drop (Suc (Suc k)) ?elst)"
                  by (metis (no_types, hide_lams) Cons_nth_drop_Suc List.nth_tl concat.simps(2) drop_Suc length_tl)
                with d1 have d3: "drop i esl = ?elst ! (Suc k) @ concat (drop (Suc (Suc k)) ?elst)" by simp
                with b0 c0 d2 have d4: "esl ! i = ?elst ! (Suc k) ! 0"
                  by (metis (no_types, hide_lams) Cons_nth_drop_Suc One_nat_def Suc_1 
                      less_or_eq_imp_le not_less not_less_eq_eq nth_Cons_0 nth_append)
                  
                from b0 c0 d2 d3 have d5: "esl ! Suc i = ?elst ! (Suc k) ! 1"
                  by (metis (no_types, hide_lams) Cons_nth_drop_Suc One_nat_def 
                    Suc_1 Suc_le_lessD Suc_lessD nth_Cons_0 nth_Cons_Suc nth_append) 
                from c0 have "Suc k < length ?elst" by auto
                show ?thesis
                  proof(cases "Suc k = length ?elst - 1")
                    assume e0: "Suc k = length ?elst - 1"
                    with d4 have e1: "esl ! i = (last ?elst) ! 0"
                      by (metis a0 b01 concat.simps(1) last_conv_nth) 
                    from e0 d4 have e2: "esl ! Suc i = (last ?elst) ! 1"
                      by (metis a0 b01 concat.simps(1) d5 last_conv_nth) 
                    from a4 have "\<forall>i. Suc i<length (last ?elst) \<longrightarrow> (\<exists>t. (last ?elst)!i -es-t\<rightarrow> (last ?elst)!(Suc i)) 
                          \<longrightarrow> (gets_es ((last ?elst)!i), gets_es ((last ?elst)!Suc i)) \<in> Guar m" 
                      by (simp add: commit_es_def)
                    with b1 e1 e2 have "(gets_es (esl ! i), gets_es (esl ! Suc i)) \<in> Guar m"
                      by (metis One_nat_def Suc_1 Suc_le_lessD a0 b01 concat.simps(1) d2 e0 last_conv_nth)
                    with p3 a4 show ?thesis by auto
                  next
                    assume "Suc k \<noteq> length ?elst - 1"
                    with c0 have e0: "Suc k < length ?elst - 1" by auto
                    let ?els' = "?elst!(Suc k)@[(?elst!Suc (Suc k))!0]"
                    from e0 have "Suc (Suc k) < length ?elst" by auto
                    with a2 have "\<exists>m\<in>es. ?els'\<in>commit_es(Guar m,Post m)"
                      by blast
                    then obtain m where e1: "m\<in>es \<and> ?els'\<in>commit_es(Guar m,Post m)"
                      by auto
                    then have e2: "\<forall>i. Suc i<length ?els' \<longrightarrow> (\<exists>t. ?els'!i -es-t\<rightarrow> ?els'!(Suc i)) 
                                  \<longrightarrow> (gets_es (?els'!i), gets_es (?els'!Suc i)) \<in> Guar m"
                      by (simp add: commit_es_def)
                    from d4 have e3: "esl ! i = ?els' ! 0"
                      by (metis (no_types, lifting) Suc_le_eq d2 dual_order.strict_trans lessI nth_append numeral_2_eq_2)
                    from d5 have e4: "esl ! Suc i = ?els' ! 1"
                      by (metis (no_types, lifting) Suc_1 Suc_le_lessD d2 nth_append) 
                    from b1 e3 e4 have e5: "\<exists>t. ?els'!0 -es-t\<rightarrow> ?els'!1" by simp
                    have "length ?els' > 1" using d2 by auto 
                    with e2 e5 have "(gets_es (?els'!0), gets_es (?els'!1)) \<in> Guar m" by simp
                    with e3 e4 have "(gets_es (esl ! i), gets_es (esl ! Suc i)) \<in> Guar m" by simp
                    with p3 e1 show ?thesis by auto
                  qed
              next
                assume d00: "j \<noteq> length (?elst!k)"
                with b2 have d0: "j < length (?elst!k)" by auto
                with b2 have d1: "esl ! i = (?elst!k) ! j"
                  by (metis (no_types, lifting) Cons_nth_drop_Suc Suc_lessD append_Cons b0 list.inject) 
                from b0 b2 d0 have d2: "drop (Suc i) esl = (drop (Suc j) (?elst!k)) @ concat (drop (Suc k) ?elst)"
                  by (metis (no_types, lifting) d00 drop_Suc drop_eq_Nil le_antisym tl_append2 tl_drop)
                show ?thesis
                  proof(cases "j = length (?elst!k) - 1")
                    assume e0: "j = length (?elst!k) - 1"
                    let ?els' = "?elst!k@[(?elst!(Suc k))!0]"
                    from d1 d0 have e1: "esl ! i = last (?elst!k)"
                      by (metis e0 gr_implies_not0 last_conv_nth length_0_conv) 
                    
                    from b2 e0 have e2: "drop (Suc i) esl = concat (drop (Suc k) ?elst)"
                      by (simp add: d2) 
                    with c0 have e3: "drop (Suc i) esl = ?elst!Suc k @ concat (drop (Suc (Suc k)) ?elst)"
                      by (metis Cons_nth_drop_Suc Suc_lessI c00 b2 concat.simps(2) diff_Suc_1)
                    from b3 c0 have "length (?elst ! (Suc k)) \<ge> 2" by auto
                    with e3 have e4: "esl ! Suc i = ?elst!(Suc k)!0"
                      by (metis (no_types, lifting) One_nat_def Suc_1 Suc_leD 
                        Suc_n_not_le_n b0 hd_append2 hd_conv_nth hd_drop_conv_nth list.size(3)) 
                    with e0 have e5: "esl ! Suc i = ?els' ! Suc j"
                      by (metis Suc_pred' d0 gr_implies_not0 linorder_neqE_nat nth_append_length) 
                    from e0 e1 have e6: "esl ! i = ?els' ! j"
                      by (metis (no_types, lifting) d0 d1 nth_append) 
                    
                    from c0 a2 have "\<exists>m\<in>es. ?els'\<in>commit_es(Guar m,Post m)"
                      by simp
                    then obtain m where e7: "m\<in>es \<and> 
                          ?els'\<in>commit_es(Guar m,Post m)"
                      by auto
                    then have e8: "\<forall>i. Suc i<length ?els' \<longrightarrow> (\<exists>t. ?els'!i -es-t\<rightarrow> ?els'!(Suc i)) 
                                  \<longrightarrow> (gets_es (?els'!i), gets_es (?els'!Suc i)) \<in> Guar m"
                      by (simp add: commit_es_def)
                    
                    from b1 e5 e6 have e9: "\<exists>t. ?els'!j -es-t\<rightarrow> ?els'!Suc j" by simp
                    have "Suc j < length ?els'" using e0 d0 by auto 
                    with e8 e9 have "(gets_es (?els'!j), gets_es (?els'!Suc j)) \<in> Guar m" by simp
                    with e5 e6 have "(gets_es (esl ! i), gets_es (esl ! Suc i)) \<in> Guar m" by simp
                    with p3 e7 show ?thesis by auto

                  next
                    assume e0: "j \<noteq> length (?elst!k) - 1"
                    with d0 have e00: "j < length (?elst!k) - 1" by auto
                    with b0 d2 have e1: "esl ! Suc i = (?elst!k) ! Suc j"
                      by (metis (no_types, lifting) List.nth_tl Suc_diff_Suc drop_Suc 
                          drop_eq_Nil hd_conv_nth hd_drop_conv_nth leD length_drop length_tl nth_append zero_less_Suc) 
                    
                    let ?els' = "?elst!k@[(?elst!(Suc k))!0]"
                    from c0 a2 have "\<exists>m\<in>es. ?els'\<in>commit_es(Guar m,Post m)"
                      by simp
                    then obtain m where e2: "m\<in>es \<and> ?els'\<in>commit_es(Guar m,Post m)"
                      by auto
                    then have e3: "\<forall>i. Suc i<length ?els' \<longrightarrow> (\<exists>t. ?els'!i -es-t\<rightarrow> ?els'!(Suc i)) 
                                  \<longrightarrow> (gets_es (?els'!i), gets_es (?els'!Suc i)) \<in> Guar m"
                      by (simp add: commit_es_def)
                    from d1 e00 have e4: "esl ! i = ?els' ! j"
                      by (simp add: d0 nth_append) 
                    from e1 e00 have e5: "esl ! Suc i = ?els' ! Suc j"
                      by (simp add: Suc_lessI nth_append) 
                    from b1 e5 e4 have e6: "\<exists>t. ?els'!j -es-t\<rightarrow> ?els'!Suc j" by simp
                    have "Suc j < length ?els'" using e00 by auto 
                    with e3 e4 e6 have "(gets_es (?els'!j), gets_es (?els'!Suc j)) \<in> Guar m" by simp
                    with e4 e5 have "(gets_es (esl ! i), gets_es (esl ! Suc i)) \<in> Guar m" by simp
                    with p3 e2 show ?thesis by auto
                  qed    
              qed
          qed
      }
      then show ?thesis by auto
      qed

  qed  

lemma preserves_es_append : "\<lbrakk> l = xs @ ys; xs \<in> preserves_es; ys \<in> preserves_es \<rbrakk> \<Longrightarrow> l \<in> preserves_es"
  by (simp add: preserves_es_def nth_append)

lemma preserves_es_append1 : "\<lbrakk>l \<in> preserves_es; l = xs @ ys \<rbrakk> \<Longrightarrow> xs \<in> preserves_es \<and> ys \<in> preserves_es"
  apply (simp add: preserves_es_def)
  apply (rule conjI, clarify)
   apply (metis nth_append trans_less_add1)
  apply clarify
  apply (erule_tac x = "length xs + i" in allE, simp add: nth_append)
  done

lemma concat_preserve : "\<lbrakk>\<forall>i. i < length elst \<longrightarrow> elst ! i \<in> preserves_es; concat elst = esl \<rbrakk>
                          \<Longrightarrow> esl \<in> preserves_es"
  apply (induct elst arbitrary: esl, simp add: preserves_es_def)
  apply (rule_tac xs = a and ys = "concat elst" in preserves_es_append, simp)
   apply auto[1]
  by fastforce


lemma EventSys_sound_0_preserve: 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     \<forall>ef\<in>es. pre \<subseteq> Pre ef;  \<forall>ef\<in>es. rely \<subseteq> Rely ef;
     \<forall>ef\<in>es. Guar ef \<subseteq> guar; \<forall>ef\<in>es. Post ef \<subseteq> post;
     \<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2;
     stable pre rely; \<forall>s. (s, s)\<in>guar;
     esl\<in>cpts_es; esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs;
     esl\<in>assume_es(pre,rely)\<rbrakk>
      \<Longrightarrow> esl \<in> preserves_es"
proof -
  assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  p1: "\<forall>ef\<in>es. pre \<subseteq> Pre ef"
      and  p2: "\<forall>ef\<in>es. rely \<subseteq> Rely ef"
      and  p3: "\<forall>ef\<in>es. Guar ef \<subseteq> guar"
      and  p4: "\<forall>ef\<in>es. Post ef \<subseteq> post"
      and  p5: "\<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2"
      and  p6: "stable pre rely"
      and  p7: "\<forall>s. (s, s)\<in>guar"
      and  p8: "esl\<in>cpts_es"
      and  p9: "esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs"
      and  p10: "esl\<in>assume_es(pre,rely)"
  let ?elst = "tl (parse_es_cpts_i2 esl es [[]])"
  from p9 p8 have a0: "concat ?elst = esl" using parse_es_cpts_i2_concat3 by metis

  from p9 p8 have a1: "\<forall>i. i < length ?elst \<longrightarrow> length (?elst!i) \<ge> 2 \<and>
      getspc_es (?elst!i!0) = EvtSys es \<and> getspc_es (?elst!i!1) \<noteq> EvtSys es"
    using parse_es_cpts_i2_start_aux by metis

  from p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
  have "\<forall>i.  i < length ?elst \<longrightarrow> ?elst ! i \<in> preserves_es"
      using EventSys_sound_aux_i_preserve 
        [of es Pre Rely Guar Post pre rely guar post esl s x e s1 x1 xs ?elst] by blast
    then show ?thesis
      by (rule concat_preserve, simp add: a0)
  qed


lemma EventSys_sound : 
    "\<lbrakk>\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef];
     \<forall>ef\<in>es. pre \<subseteq> Pre ef;  \<forall>ef\<in>es. rely \<subseteq> Rely ef;
     \<forall>ef\<in>es. Guar ef \<subseteq> guar; \<forall>ef\<in>es. Post ef \<subseteq> post;
     \<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2;
     stable pre rely; \<forall>s. (s, s)\<in>guar \<rbrakk>
      \<Longrightarrow> \<Turnstile> EvtSys es sat\<^sub>s [pre, rely, guar, post]"
  proof -
    assume p0: "\<forall>ef\<in>es. \<Turnstile> ef sat\<^sub>e [Pre ef, Rely ef, Guar ef, Post ef]"
      and  p1: "\<forall>ef\<in>es. pre \<subseteq> Pre ef"
      and  p2: "\<forall>ef\<in>es. rely \<subseteq> Rely ef"
      and  p3: "\<forall>ef\<in>es. Guar ef \<subseteq> guar"
      and  p4: "\<forall>ef\<in>es. Post ef \<subseteq> post"
      and  p5: "\<forall>ef1 ef2. ef1\<in>es \<and> ef2\<in>es \<longrightarrow> Post ef1 \<subseteq> Pre ef2"
      and  p6: "stable pre rely"
      and  p7: "\<forall>s. (s, s)\<in>guar"
    then have "\<forall>s x. (cpts_of_es (EvtSys es) s x) \<inter> assume_es(pre, rely) \<subseteq> commit_es(guar, post) \<inter> preserves_es"
      proof-
      {
        fix s x
        have "\<forall>esl. esl\<in>(cpts_of_es (EvtSys es) s x) \<inter> assume_es (pre, rely) \<longrightarrow> esl\<in> commit_es (guar, post) \<inter> preserves_es"
          proof -
          {
            fix esl
            assume a0: "esl\<in>(cpts_of_es (EvtSys es) s x) \<inter> assume_es (pre, rely)"
            then have a1: "esl\<in>(cpts_of_es (EvtSys es) s x)" by simp
            then have a1_1: "esl!0 = (EvtSys es, s, x)" by (simp add:cpts_of_es_def)
            from a1 have a1_2: "esl \<in> cpts_es" by (simp add:cpts_of_es_def)
            from a0 have a2: "esl\<in>assume_es (pre, rely)" by simp
            then have  "\<forall>i. Suc i<length esl \<longrightarrow> (\<exists>t. esl!i -es-t\<rightarrow> esl!(Suc i)) \<longrightarrow> 
                          (gets_es (esl!i), gets_es (esl!Suc i)) \<in> guar"
              proof -
              {
                fix i
                assume b0: "Suc i<length esl"
                  and  b1: "\<exists>t. esl!i -es-t\<rightarrow> esl!(Suc i)"
                then obtain t where b2: "esl!i -es-t\<rightarrow> esl!(Suc i)" by auto
                from a1_2 b0 b1 have "(gets_es (esl!i), gets_es (esl!Suc i)) \<in> guar"
                  proof(cases "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) = EvtSys es")
                    assume c0: "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) = EvtSys es"

                    with b0 have "getspc_es (esl ! i) = EvtSys es" by simp
                    moreover from b0 c0 have "getspc_es (esl ! (Suc i)) = EvtSys es" by simp
                    ultimately have "\<not>(\<exists>t. esl!i -es-t\<rightarrow> esl!(Suc i))" 
                      using evtsys_not_eq_in_tran2 getspc_es_def by (metis surjective_pairing) 

                    with b1 show ?thesis by simp
                  next
                    assume c0: "\<not> (\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) = EvtSys es)"
                    then obtain m where c1: "Suc m \<le> length esl \<and> getspc_es (esl ! m) \<noteq> EvtSys es"
                      by auto
                    from a1_1 have c2: "getspc_es (esl!0) = EvtSys es" by (simp add:getspc_es_def)
                    from c1 have "\<exists>i. i \<le> m \<and> getspc_es (esl ! i) \<noteq> EvtSys es" by auto
                    with a1_2 a1_1 c1 c2 have "\<exists>i. (i < m \<and> getspc_es (esl ! i) = EvtSys es 
                              \<and> getspc_es (esl ! Suc i) \<noteq> EvtSys es) 
                              \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) = EvtSys es)" 
                      using evtsys_fst_ent by blast
                    then obtain n where c3: "(n < m \<and> getspc_es (esl ! n) = EvtSys es 
                              \<and> getspc_es (esl ! Suc n) \<noteq> EvtSys es) 
                              \<and> (\<forall>j. j < n \<longrightarrow> getspc_es (esl ! j) = EvtSys es)" by auto
                    with b1 have c4: "i \<ge> n" 
                      proof -
                      {
                        assume d0: "i < n"
                        with c3 have "getspc_es (esl ! i) = EvtSys es" by simp
                        moreover from c3 d0 have "getspc_es (esl ! Suc i) = EvtSys es"
                          using Suc_lessI by blast 
                        ultimately have "\<not>(\<exists>t. esl!i -es-t\<rightarrow> esl!Suc i)" 
                          using evtsys_not_eq_in_tran getspc_es_def by (metis surjective_pairing)
                        with b1 have False by simp
                      }
                      then show ?thesis using leI by auto 
                      qed

                    let ?esl = "drop n esl"
                    from c1 c3 have c5: "length ?esl \<ge> 2"
                      by (metis One_nat_def Suc_eq_plus1_left Suc_le_eq length_drop 
                          less_diff_conv less_trans_Suc numeral_2_eq_2)
                    from c1 c3 have c6: "getspc_es (?esl!0) = EvtSys es \<and> getspc_es (?esl!1) \<noteq> EvtSys es"
                      by force
                    

                    from a1_2 c1 c3 have c7: "?esl \<in> cpts_es" using cpts_es_dropi
                        by (metis (no_types, lifting) b0 c4 drop_0 dual_order.strict_trans 
                            le_0_eq le_SucE le_imp_less_Suc zero_induct) 
                    from c5 c6 c7 have "\<exists>s x ev s1 x1 xs. ?esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
                        using fst_esys_snd_eseq_exist by blast
                    then obtain s and x and e and s1 and x1 and xs where c8:
                        "?esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs" by auto
                    
                    let ?elst = "tl (parse_es_cpts_i2 ?esl es [[]])"
                    from c8 c7 have c9: "concat ?elst = ?esl" using parse_es_cpts_i2_concat3 by metis           
                    have c10: "?esl\<in>assume_es(pre,rely)"
                      proof(cases "n = 0")
                        assume d0: "n = 0"
                        then have "?esl = esl" by simp
                        with a2 show ?thesis by simp
                      next
                        assume d0: "n \<noteq> 0"
                        let ?eslh = "take (n + 1) esl"
                        from a2 have d1: "\<forall>i. Suc i<length ?esl \<longrightarrow> ?esl!i -ese\<rightarrow> ?esl!(Suc i) 
                          \<longrightarrow> (gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> rely" by (simp add:assume_es_def)
                        have "gets_es (?esl!0) \<in> pre"
                          proof - 
                            from a2 d0 have "gets_es (?eslh!0) \<in> pre" by (simp add:assume_es_def)
                            moreover
                            from a2 have "\<forall>i. Suc i<length ?eslh \<longrightarrow> ?eslh!i -ese\<rightarrow> ?eslh!(Suc i) 
                              \<longrightarrow> (gets_es (?eslh!i), gets_es (?eslh!Suc i)) \<in> rely" by (simp add:assume_es_def)
                            ultimately have "?eslh \<in> assume_es(pre, rely)" by (simp add:assume_es_def)
                            moreover
                            from c3 have "\<forall>i<length ?eslh. getspc_es (?eslh!i) = EvtSys es"
                              by (metis Suc_eq_plus1 length_take less_antisym min_less_iff_conj nth_take) 
                            ultimately have "\<forall>i<length ?eslh. gets_es (?eslh!i) \<in> pre" 
                              using p6 pre_trans by blast
                            with d0 have "gets_es (?eslh ! n) \<in> pre"
                              using b0 c4 by auto 
                            then show ?thesis by (simp add: c8 nth_via_drop) 
                          qed
                        with d1 show ?thesis by (simp add:assume_es_def)
                      qed
                    
                    from p0 p1 p2 p3 p4 p5 p6 p7 c7 c8 c10 
                    have c11: "\<forall>i. Suc i<length ?esl \<longrightarrow> (\<exists>t. ?esl!i -es-t\<rightarrow> ?esl!(Suc i)) \<longrightarrow> 
                          (gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> guar" 
                      using EventSys_sound_0 
                          [of es Pre Rely Guar Post pre rely guar post ?esl s x e s1 x1 xs] by simp
                    
                    from b0 c4 have c12: "esl ! i = ?esl ! (i - n)" by auto
                    moreover
                    from b0 c4 have c13: "esl ! Suc i = ?esl ! Suc (i - n)" by auto
                    moreover
                    from b0 c4 have "Suc (i - n) < length ?esl" by auto
                    moreover
                    from b1 c12 c13 have "\<exists>t. ?esl ! (i - n) -es-t\<rightarrow> ?esl ! Suc (i - n)" by simp
                    ultimately 
                    have "(gets_es (?esl ! (i - n)), gets_es (?esl ! Suc (i - n))) \<in> guar" 
                      using c11 by simp
                    
                    with c12 c13 show ?thesis by simp

                  qed
                    
              }
              then show ?thesis by auto
              qed
              then have l1 : "esl\<in>commit_es (guar, post)" by (simp add:commit_es_def)

              from a2 have "esl \<in> preserves_es"
              proof(cases "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) = EvtSys es")
                assume c0: "\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) = EvtSys es"
                then show ?thesis  by (simp add: preserves_es_def)
              next
                assume c0: "\<not> (\<forall>i. Suc i \<le> length esl \<longrightarrow> getspc_es (esl ! i) = EvtSys es)"
                then obtain m where c1: "Suc m \<le> length esl \<and> getspc_es (esl ! m) \<noteq> EvtSys es"
                  by auto
                from a1_1 have c2: "getspc_es (esl!0) = EvtSys es" by (simp add:getspc_es_def)
                from c1 have "\<exists>i. i \<le> m \<and> getspc_es (esl ! i) \<noteq> EvtSys es" by auto
                with a1_2 a1_1 c1 c2 have "\<exists>i. (i < m \<and> getspc_es (esl ! i) = EvtSys es 
                                          \<and> getspc_es (esl ! Suc i) \<noteq> EvtSys es) 
                                          \<and> (\<forall>j. j < i \<longrightarrow> getspc_es (esl ! j) = EvtSys es)" 
                      using evtsys_fst_ent by blast
                    then obtain n where c3: "(n < m \<and> getspc_es (esl ! n) = EvtSys es 
                    \<and> getspc_es (esl ! Suc n) \<noteq> EvtSys es) \<and> (\<forall>j. j < n \<longrightarrow> getspc_es (esl ! j) = EvtSys es)" by auto
                    let ?esl1 = "take n esl"
                    let ?esl = "drop n esl"
                    from c3 have c4: "?esl1 \<in> preserves_es" by (simp add: preserves_es_def)

                    from c1 c3 have c5: "length ?esl \<ge> 2"
                      by (metis One_nat_def Suc_eq_plus1_left Suc_le_eq length_drop 
                          less_diff_conv less_trans_Suc numeral_2_eq_2)
                    from c1 c3 have c6: "getspc_es (?esl!0) = EvtSys es \<and> getspc_es (?esl!1) \<noteq> EvtSys es"
                      by force

                    from a1_2 c1 c3 have c7: "?esl \<in> cpts_es" using cpts_es_dropi
                      using cpts_es_dropi2 by fastforce
                    from c5 c6 c7 have "\<exists>s x ev s1 x1 xs. ?esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
                      using fst_esys_snd_eseq_exist by blast
                    then obtain s and x and e and s1 and x1 and xs where c8:
                        "?esl = (EvtSys es, s, x) # (EvtSeq e (EvtSys es), s1,x1) # xs" by auto

                    have c9: "?esl\<in>assume_es(pre,rely)"
                    proof(cases "n = 0")
                      assume d0: "n = 0"
                      then have "?esl = esl" by simp
                      with a2 show ?thesis by simp
                    next
                      assume d0: "n \<noteq> 0"
                      let ?eslh = "take (n + 1) esl"
                      from a2 have d1: "\<forall>i. Suc i<length ?esl \<longrightarrow> ?esl!i -ese\<rightarrow> ?esl!(Suc i) 
                          \<longrightarrow> (gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> rely" by (simp add:assume_es_def)
                      have "gets_es (?esl!0) \<in> pre"
                      proof - 
                        from a2 d0 have "gets_es (?eslh!0) \<in> pre" by (simp add:assume_es_def)
                        moreover
                        from a2 have "\<forall>i. Suc i<length ?eslh \<longrightarrow> ?eslh!i -ese\<rightarrow> ?eslh!(Suc i) 
                              \<longrightarrow> (gets_es (?eslh!i), gets_es (?eslh!Suc i)) \<in> rely" by (simp add:assume_es_def)
                        ultimately have "?eslh \<in> assume_es(pre, rely)" by (simp add:assume_es_def)
                        moreover
                        from c3 have "\<forall>i<length ?eslh. getspc_es (?eslh!i) = EvtSys es"
                          by (metis Suc_eq_plus1 length_take less_antisym min_less_iff_conj nth_take) 
                        ultimately have "\<forall>i<length ?eslh. gets_es (?eslh!i) \<in> pre" 
                          using p6 pre_trans by blast
                        with d0 have "gets_es (?eslh ! n) \<in> pre"
                          by (metis (no_types, lifting)  Suc_le_lessD add_Suc c1 c3 le_less_trans 
                             length_take less_Suc_eq less_imp_le less_imp_le_nat min_less_iff_conj 
                             plus_1_eq_Suc semiring_normalization_rules(24)) 
                            then show ?thesis by (simp add: c8 nth_via_drop) 
                          qed
                        with d1 show ?thesis by (simp add:assume_es_def)
                      qed
                    
                    from p0 p1 p2 p3 p4 p5 p6 p7 c7 c8 c9 
                    have c10: "?esl \<in> preserves_es" 
                      using EventSys_sound_0_preserve 
                          [of es Pre Rely Guar Post pre rely guar post ?esl s x e s1 x1 xs] by simp
                    with c4 show ?thesis
                      by (rule_tac xs = "?esl1" and ys = "?esl" in preserves_es_append, simp_all)
                  qed

                  with l1 have "esl \<in> commit_es (guar, post) \<inter> preserves_es" by auto
                }        
                then show ?thesis by auto
              qed
            }
            then show ?thesis by blast
          qed
        
          then show "\<Turnstile> EvtSys es sat\<^sub>s [pre, rely, guar, post]" by (simp add:es_validity_def)
        qed



lemma esys_seq_sound: 
      "\<lbrakk>pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
        \<Turnstile> esys sat\<^sub>s [pre', rely', guar', post']\<rbrakk> 
    \<Longrightarrow> \<Turnstile> esys sat\<^sub>s [pre, rely, guar, post]"
  proof -
    assume p0: "pre \<subseteq> pre'"
      and  p1: "rely \<subseteq> rely'"
      and  p2: "guar' \<subseteq> guar"
      and  p3: "post' \<subseteq> post"
      and  p4: "\<Turnstile> esys sat\<^sub>s [pre', rely', guar', post']"
    from p4 have p5: "\<forall>s x. (cpts_of_es esys s x) \<inter> assume_es(pre', rely') \<subseteq> commit_es(guar', post') \<inter> preserves_es"
      by (simp add: es_validity_def)
    have "\<forall>s x. (cpts_of_es esys s x) \<inter> assume_es(pre, rely) \<subseteq> commit_es(guar, post) \<inter> preserves_es"
      proof -
      {
        fix c s x
        assume a0: "c\<in>(cpts_of_es esys s x) \<inter> assume_es(pre, rely)"
        then have "c\<in>(cpts_of_es esys s x) \<and> c\<in>assume_es(pre, rely)" by simp
        with p0 p1 have "c\<in>(cpts_of_es esys s x) \<and> c\<in>assume_es(pre', rely')"
          using assume_es_imp[of pre pre' rely rely' c] by simp
        with p5 have "c\<in>commit_es(guar', post') \<inter> preserves_es" by auto
        with p2 p3 have "c\<in>commit_es(guar, post) \<inter> preserves_es" 
          using commit_es_imp[of guar' guar post' post c] by simp
      }
      then show ?thesis by auto
      qed
    then show ?thesis by (simp add:es_validity_def)
  qed

theorem rgsound_es: "\<turnstile> esf sat\<^sub>s [pre, rely, guar, post] \<Longrightarrow> \<Turnstile> evtsys_spec esf sat\<^sub>s [pre, rely, guar, post]"
  apply(erule rghoare_es.induct)
  proof -
  {
    fix ef esf pre post rely guar
    assume p0: "\<turnstile> E\<^sub>e (ef::('l,'k,'s) rgformula_e) sat\<^sub>e [Pre\<^sub>e ef, Rely\<^sub>e ef, Guar\<^sub>e ef, Post\<^sub>e ef]"
      and  p1: "\<turnstile> fst (esf::('l,'k,'s) rgformula_ess \<times> 's rgformula) sat\<^sub>s [Pre\<^sub>f (snd esf), Rely\<^sub>f (snd esf), Guar\<^sub>f (snd esf), Post\<^sub>f (snd esf)]"
      and  p2: "\<Turnstile> evtsys_spec (fst esf) sat\<^sub>s [Pre\<^sub>f (snd esf), Rely\<^sub>f (snd esf), Guar\<^sub>f (snd esf), Post\<^sub>f (snd esf)]"
      and  p3: "pre = Pre\<^sub>e ef"
      and  p4: "post = Post\<^sub>f (snd esf)"
      and  p5: "rely \<subseteq> Rely\<^sub>e ef"
      and  p6: "rely \<subseteq> Rely\<^sub>f (snd esf)"
      and  p7: "Guar\<^sub>e ef \<subseteq> guar"
      and  p8: "Guar\<^sub>f (snd esf) \<subseteq> guar"
      and  p9: "Post\<^sub>e ef \<subseteq> Pre\<^sub>f (snd esf)"
    from p0 have a1: "\<Turnstile> E\<^sub>e (ef::('l,'k,'s) rgformula_e) sat\<^sub>e [Pre\<^sub>e ef, Rely\<^sub>e ef, Guar\<^sub>e ef, Post\<^sub>e ef]" 
      using rgsound_e by blast
    have a2: "evtsys_spec (rgf_EvtSeq ef esf) = EvtSeq (fst ef) (evtsys_spec (fst esf))"
      using evtsys_spec_evtseq by (simp add:E\<^sub>e_def)
    from p2 p3 p4 p5 p6 p7 p8 p9 a1 a2 show "\<Turnstile> evtsys_spec (rgf_EvtSeq ef esf) sat\<^sub>s [pre, rely, guar, post]"
      using EventSeq_sound [of "fst ef" "pre" "Rely\<^sub>e ef" "Guar\<^sub>e ef" "Post\<^sub>e ef"
            "evtsys_spec (fst esf)" "Pre\<^sub>f (snd esf)" "Rely\<^sub>f (snd esf)" "Guar\<^sub>f (snd esf)" "post"
            rely guar] by (simp add:E\<^sub>e_def)
  }
  next
  {
    fix esf pre rely guar post
    assume p0: "\<forall>ef\<in>esf. \<turnstile> E\<^sub>e ef sat\<^sub>e [Pre\<^sub>e ef, Rely\<^sub>e ef, Guar\<^sub>e ef, Post\<^sub>e ef]"
      and  p1: "\<forall>ef\<in>esf. pre \<subseteq> Pre\<^sub>e ef"
      and  p2: "\<forall>ef\<in>esf. rely \<subseteq>  Rely\<^sub>e ef"
      and  p3: "\<forall>ef\<in>esf. Guar\<^sub>e ef \<subseteq> guar"
      and  p4: "\<forall>ef\<in>esf. Post\<^sub>e ef \<subseteq> post"
      and  p5: "\<forall>ef1 ef2. ef1\<in>esf \<and> ef2\<in>esf \<longrightarrow> Post\<^sub>e ef1 \<subseteq> Pre\<^sub>e ef2"
      and  p6: "stable pre rely"
      and  p7: "\<forall>s. (s, s) \<in> guar"
    let ?es = "Domain esf" 
    let ?RG = "\<lambda>e. SOME rg. (e,rg)\<in>esf" 
    have a1: "\<forall>e\<in>?es. \<exists>ef\<in>esf. ?RG e = snd ef" by (metis Domain.cases snd_conv someI) 

    let ?Pre = "pre_rgf \<circ> ?RG"
    let ?Rely = "rely_rgf \<circ> ?RG"
    let ?Guar = "guar_rgf \<circ> ?RG"
    let ?Post = "post_rgf \<circ> ?RG"
    from p0 have a2: "\<forall>i\<in>esf. \<Turnstile> E\<^sub>e i sat\<^sub>e [Pre\<^sub>e i, Rely\<^sub>e i, Guar\<^sub>e i, Post\<^sub>e i]"
      by (simp add: rgsound_e) 
    have "\<forall>ef\<in>?es. \<Turnstile> ef sat\<^sub>e [?Pre ef, ?Rely ef, ?Guar ef, ?Post ef]"
      by (metis (mono_tags, lifting) Domain.cases E\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def 
          Pre\<^sub>e_def Rely\<^sub>e_def a2 comp_apply fst_conv snd_conv someI_ex) 
    moreover
    have "\<forall>ef\<in>?es. pre \<subseteq> ?Pre ef" by (metis Pre\<^sub>e_def a1 comp_def p1)
    moreover
    have "\<forall>ef\<in>?es. rely \<subseteq> ?Rely ef" by (metis Rely\<^sub>e_def a1 comp_apply p2)
    moreover
    have "\<forall>ef\<in>?es. ?Guar ef \<subseteq> guar" by (metis Guar\<^sub>e_def a1 comp_apply p3)
    moreover
    have "\<forall>ef\<in>?es. ?Post ef \<subseteq> post" by (metis Post\<^sub>e_def a1 comp_apply p4)
    moreover
    have "\<forall>ef1 ef2. ef1 \<in> ?es \<and> ef2 \<in> ?es \<longrightarrow> ?Post ef1 \<subseteq> ?Pre ef2"
      by (metis (mono_tags, lifting) Post\<^sub>e_def Pre\<^sub>e_def a1 comp_def p5) 
    ultimately have "\<Turnstile> EvtSys (Domain esf) sat\<^sub>s [pre, rely, guar, post]"
      using p6 p7 EventSys_sound [of ?es ?Pre ?Rely ?Guar ?Post pre rely guar post] by simp
    then show "\<Turnstile> evtsys_spec (rgf_EvtSys esf) sat\<^sub>s [pre, rely, guar, post]" by simp
  }
  next
  {
    fix pre pre' rely rely' guar' guar post' post esys
    assume "pre \<subseteq> pre'"
      and  "rely \<subseteq> rely'"
      and  "guar' \<subseteq> guar"
      and  "post' \<subseteq> post"
      and  "\<turnstile> esys sat\<^sub>s [pre', rely', guar', post']"
      and  "\<Turnstile> evtsys_spec esys sat\<^sub>s [pre', rely', guar', post']"
    then show "\<Turnstile> evtsys_spec esys sat\<^sub>s [pre, rely, guar, post] "
      using esys_seq_sound[of pre pre' rely rely' guar' guar post' post "evtsys_spec esys"] by simp
  }
 qed

subsection \<open>Soundness of Parallel Event Systems\<close>

lemma conjoin_comm_imp_rely_n[rule_format]:
  "\<lbrakk>\<forall>k. pre \<subseteq> Pre k; \<forall>k. rely \<subseteq> Rely k; 
    \<forall>k j. j\<noteq>k \<longrightarrow> Guar j \<subseteq> Rely k;
    \<forall>k. cs k \<in> commit_es(Guar k, Post k);
    c \<in> cpts_of_pes pes s x; c\<in>assume_pes(pre, rely); c \<propto> cs\<rbrakk> \<Longrightarrow>
    \<forall>n k. n \<le> length (cs k) \<and> n > 0 \<longrightarrow> take n (cs k) \<in> assume_es(Pre k, Rely k)"
  proof -
    assume p1: "\<forall>k. pre \<subseteq> Pre k"
      and  p2: "\<forall>k. rely \<subseteq> Rely k"
      and  p3: "\<forall>k j. j\<noteq>k \<longrightarrow>  Guar j \<subseteq> Rely k"
      and  p4: "c \<in> cpts_of_pes pes s x"
      and  p5: "c \<in> assume_pes(pre, rely)" 
      and  p6: "c \<propto> cs"
      and  p0: "\<forall>k. cs k \<in> commit_es(Guar k, Post k)"
    from p6 have p8: "\<forall>k. length (cs k) = length c" by (simp add:conjoin_def same_length_def)
    from p4 p6 have p7: "\<forall>k. cs k \<in> cpts_of_es (pes k) s x" using conjoin_imp_cptses_k by auto
    then have p9: "\<forall>k. cs k \<in> cpts_es \<and> cs k !0 = (pes k,s,x)" by (simp add:cpts_of_es_def)
    from p6 have p11: "\<forall>k j. j < length c \<longrightarrow> gets (c!j) = gets_es ((cs k)!j)" by (simp add:conjoin_def same_state_def)
    {
      fix n
      have "\<forall>k. n \<le> length (cs k) \<and> n > 0 \<longrightarrow> take n (cs k) \<in> assume_es(Pre k, Rely k)"
        proof(induct n)
          case 0 then show ?case by simp
        next
          case (Suc m)
          assume b0: "\<forall>k. m \<le> length (cs k) \<and> 0 < m \<longrightarrow> take m (cs k) \<in> assume_es (Pre k, Rely k)"
          {
            fix k
            assume c0: "Suc m \<le> length (cs k) \<and> 0 < Suc m"
            from p7 have c2: "length (cs k) > 0"
              by (metis (no_types, lifting) cpts_es_not_empty cpts_of_es_def gr0I length_0_conv mem_Collect_eq) 
            from p6 have c3: "length (cs k) = length c" by (simp add:conjoin_def same_length_def)

            let ?esl = "take (Suc m) (cs k)"

            have "take (Suc m) (cs k) \<in> assume_es (Pre k, Rely k)"
              proof(cases "m = 0")
                assume d0: "m = 0"
                have "gets_es (take (Suc m) (cs k)!0) \<in> Pre k" 
                  proof - 
                    from p6 c2 c3 have "gets (c!0) = gets_es ((cs k)!0)" 
                      by (simp add:conjoin_def same_state_def)
                    moreover
                    from p5 have "gets (c!0) \<in> pre" by (simp add:assume_pes_def)
                    ultimately show ?thesis using p1 p8  by auto 
                  qed
                moreover
                from d0 have d1: "length (take (Suc m) (cs k)) = 1"
                  using One_nat_def c2 gr0_implies_Suc length_take min_0R min_Suc_Suc by fastforce
                moreover
                from d1 have "\<forall>i. Suc i < length (take (Suc m) (cs k)) 
                      \<longrightarrow> (take (Suc m) (cs k)) ! i -ese\<rightarrow> (take (Suc m) (cs k)) ! Suc i 
                      \<longrightarrow> (gets_es ((take (Suc m) (cs k)) ! i), gets_es ((take (Suc m) (cs k)) ! Suc i)) \<in> rely"
                  by auto
                moreover
                have "assume_es (Pre k, Rely k) = {c. gets_es (c ! 0) \<in> Pre k \<and>
                      (\<forall>i. Suc i < length c \<longrightarrow> c ! i -ese\<rightarrow> c ! Suc i 
                            \<longrightarrow> (gets_es (c ! i), gets_es (c ! Suc i)) \<in> Rely k)}" by (simp add:assume_es_def)
                ultimately show ?thesis using Suc_neq_Zero less_one mem_Collect_eq by auto
              next
                assume "m \<noteq> 0"
                then have dd0: "m > 0" by simp
                with b0 c0 have dd1: "take m (cs k) \<in> assume_es (Pre k, Rely k)" by simp
                
                have "gets_es (?esl ! 0) \<in> Pre k"
                  proof - 
                    from p6 c2 c3 have "gets (c!0) = gets_es ((cs k)!0)" 
                      by (simp add:conjoin_def same_state_def)
                    moreover
                    from p5 have "gets (c!0) \<in> pre" by (simp add:assume_pes_def)
                    ultimately show ?thesis using p1 p8 by auto 
                  qed
                moreover
                have "\<forall>i. Suc i<length ?esl \<longrightarrow> 
                     ?esl!i -ese\<rightarrow> ?esl!(Suc i) \<longrightarrow> 
                     (gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> Rely k"
                  proof -
                  {
                    fix i
                    assume d0: "Suc i<length ?esl"
                      and  d1: "?esl!i -ese\<rightarrow> ?esl!Suc i"
                    then have d2: "?esl!i = (cs k)!i \<and> ?esl!Suc i = (cs k)! Suc i"
                      by auto
                    from p6 c3 d0 have d4: "(\<exists>t k. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<and>
                              (\<forall>k t. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i))))
                              \<or>
                              (((c!i) -pese\<rightarrow> (c!Suc i)) \<and> (\<forall>k. (((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i))))"
                      by (simp add:conjoin_def compat_tran_def)
                    from d1 have d5: "((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i)"
                          by (simp add: d2) 
                    from d4 have "(gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> Rely k"
                      proof
                        assume e0: "\<exists>t k. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<and>
                              (\<forall>k t. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i)))"
                        then obtain ct and k' where e1: "((c!i) -pes-(ct\<sharp>k')\<rightarrow> (c!Suc i)) \<and>
                                    (((cs k')!i) -es-(ct\<sharp>k')\<rightarrow> ((cs k')! Suc i))" by auto
                        with p6 p8 d0 d5 have e2: "k \<noteq> k'" 
                          using conjoin_def[of c cs] same_spec_def[of c cs]
                             es_tran_not_etran1 by blast 
  
                        with e0 e1 have e3: "((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i)" by auto
                        with d0 have "(?esl!i) -ese\<rightarrow> (?esl! Suc i)" by auto
                        then show ?thesis
                          proof(cases "i < m - 1")
                            assume f0: "i < m - 1"
                            with d2 have f1:"take (Suc m) (cs k) ! i = take m (cs k) ! i"
                              by (simp add: diff_less_Suc less_trans_Suc) 
                            
                            from f0 have f2: "take (Suc m) (cs k) ! Suc i = take m (cs k) ! Suc i"
                              by (simp add: d2 gr_implies_not0 nat_le_linear)
                            from dd1 have "\<forall>i. Suc i<length (take m (cs k)) \<longrightarrow> 
                                (take m (cs k))!i -ese\<rightarrow> (take m (cs k))!(Suc i) \<longrightarrow> 
                                (gets_es ((take m (cs k))!i), gets_es ((take m (cs k))!Suc i)) \<in> Rely k"
                              by (simp add:assume_es_def)
                            with dd0 f0 have "(gets_es (take m (cs k) ! i), gets_es (take m (cs k) ! Suc i)) \<in> Rely k"
                              by (metis (no_types, lifting) One_nat_def Suc_mono Suc_pred d0 d1 f1 f2 length_take min_less_iff_conj)
                            with f1 f2 show ?thesis by simp
                          next
                            assume  "\<not>(i < m - 1)"
                            with d0 have f0: "i = m - 1"
                              by (simp add: c0 dd0 less_antisym min.absorb2) 
                            let ?esl2 = "take (Suc m) (cs k')"
                            
                            from b0 c0 dd0 have "take m (cs k') \<in> assume_es (Pre k', Rely k')"
                              by (metis Suc_leD p8) 
                            moreover
                            from e1 f0 have "\<not>(cs k' ! (m-1) -ese\<rightarrow> cs k' !m)"
                              using Suc_pred' dd0 es_tran_not_etran1 by fastforce 
                            ultimately have f1: "take (Suc m) (cs k') \<in> assume_es (Pre k', Rely k')" 
                              using assume_es_one_more[of "cs k'" m "Pre k'" "Rely k'"] p8 p9 c0 dd0
                              by (simp add: Suc_le_eq)
                            from p7 have "cs k' \<in> cpts_of_es (pes k') s x" by simp
                            with p8 c0 dd0 have f2: "?esl2\<in>cpts_of_es (pes k') s x" 
                              using cpts_es_take[of "cs k'" m] cpts_of_es_def[of "pes k'" s x]
                                by (simp add: Suc_le_lessD) 
                            from p0 p8 c0 have "?esl2\<in>commit_es(Guar k', Post k')" 
                              using commit_es_take_n[of "Suc m" "cs k'" "Guar k'" "Post k'"] by auto
                            then have "\<forall>i. Suc i<length ?esl2 \<longrightarrow> 
                                          (\<exists>t. ?esl2!i -es-t\<rightarrow> ?esl2!(Suc i)) \<longrightarrow> 
                                          (gets_es (?esl2!i), gets_es (?esl2!Suc i)) \<in> Guar k'"
                              by (simp add:commit_es_def)
                            
                            with p8 e1 f0 c0 dd0 have "(gets_es (?esl2 ! (m-1)), gets_es (?esl2 ! m))\<in>Guar k'"
                              by (metis (no_types, lifting) One_nat_def Suc_pred diff_less_Suc length_take lessI min.absorb2 nth_take)
                            with p3 p11 c0 f0 e2 show ?thesis
                              by (smt Suc_diff_1 Suc_leD c3 dd0 le_less_linear not_less_eq_eq nth_take subsetCE)
                          qed
                      next
                        assume e0: "(((c!i) -pese\<rightarrow> (c!Suc i)) \<and> (\<forall>k. (((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i))))"
                        from p5 have "\<forall>i. Suc i<length c \<longrightarrow> 
                                          c!i -pese\<rightarrow> c!(Suc i) \<longrightarrow> 
                                          (gets (c!i), gets (c!Suc i)) \<in> rely"
                           by (simp add:assume_pes_def) 
                        moreover
                        from p8 c0 d0 have e1:"Suc i < length c" by simp
                        ultimately have "(gets (c!i), gets (c!Suc i)) \<in> rely" using e0 by simp
                        with p2 have "(gets (c!i), gets (c!Suc i)) \<in> Rely k" by auto
                        with p8 p11 c0 d0 show ?thesis
                          using Suc_lessD e1 d2 by auto 
                      qed
                  }
                  then show ?thesis by auto 
                  qed
                ultimately show ?thesis by (simp add:assume_es_def)
            qed
          }
          then show ?case by auto
        qed
    }
    then show ?thesis by auto
  qed

lemma conjoin_comm_imp_rely:
  "\<lbrakk>\<forall>k. pre \<subseteq> Pre k; \<forall>k. rely \<subseteq> Rely k; 
    \<forall>k j. j\<noteq>k \<longrightarrow> Guar j \<subseteq> Rely k;
    \<forall>k. cs k \<in> commit_es(Guar k, Post k);
    c \<in> cpts_of_pes pes s x; c\<in>assume_pes(pre, rely); c \<propto> cs\<rbrakk> \<Longrightarrow>
    \<forall>k. (cs k) \<in> assume_es(Pre k, Rely k)"
proof -
  assume a1: "\<forall>k. pre \<subseteq> Pre k"
  assume a2: "\<forall>k. rely \<subseteq> Rely k"
  assume a3: "\<forall>k j. j \<noteq> k \<longrightarrow> Guar j \<subseteq> Rely k"
  assume a4: "\<forall>k. cs k \<in> commit_es (Guar k, Post k)"
  assume a5: "c \<in> cpts_of_pes pes s x"
  assume a6: "c \<in> assume_pes (pre, rely)"
  assume a7: "c \<propto> cs"
  have f8: "c \<noteq> []"
    using a5 cpts_of_pes_def by force
  from a7 have p8: "\<forall>k. length (cs k) = length c" by (simp add:conjoin_def same_length_def)
  {
    fix k
    have "(cs k) \<in> assume_es(Pre k, Rely k)" 
      using a1 a2 a3 a4 a5 a6 a7 p8 f8 
      conjoin_comm_imp_rely_n[of pre Pre rely Rely Guar cs Post c pes s x "length (cs k)" k] by force
  }  
  then show ?thesis by simp    
qed 

lemma cpts_es_sat_rely[rule_format]:
  "\<lbrakk>\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]; 
        \<forall>k. pre \<subseteq> Pre k; 
        \<forall>k. rely \<subseteq> Rely k; 
        \<forall>k j. j\<noteq>k \<longrightarrow> Guar j \<subseteq> Rely k;
        c \<in> cpts_of_pes pes s x; c\<in>assume_pes(pre, rely);
        c \<propto> cs; \<forall>k. cs k \<in> cpts_of_es (pes k) s x\<rbrakk> \<Longrightarrow>
        \<forall>n k. n \<le> length (cs k) \<and> n > 0 \<longrightarrow> take n (cs k)\<in>assume_es(Pre k, Rely k)"
  proof -
    assume p0: "\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]"
      and  p1: "\<forall>k. pre \<subseteq> Pre k"
      and  p2: "\<forall>k. rely \<subseteq> Rely k"
      and  p3: "\<forall>k j. j\<noteq>k \<longrightarrow>  Guar j \<subseteq> Rely k"
      and  p4: "c \<in> cpts_of_pes pes s x"
      and  p5: "c \<in> assume_pes(pre, rely)" 
      and  p6: "c \<propto> cs"
      and  p7: "\<forall>k. cs k \<in> cpts_of_es (pes k) s x"
    from p6 have p8: "\<forall>k. length (cs k) = length c" by (simp add:conjoin_def same_length_def)
    from p7 have p9: "\<forall>k. cs k \<in> cpts_es" using cpts_of_es_def mem_Collect_eq by fastforce 
    from p6 have p11: "\<forall>k j. j < length c \<longrightarrow> gets (c!j) = gets_es ((cs k)!j)" by (simp add:conjoin_def same_state_def)
    {
      fix n
      have "\<forall>k. n \<le> length (cs k) \<and> n > 0 \<longrightarrow> take n (cs k)\<in>assume_es(Pre k, Rely k)"
        proof(induct n)
          case 0 then show ?case by simp
        next
          case (Suc m)
          assume b0: "\<forall>k. m \<le> length (cs k) \<and> 0 < m \<longrightarrow> take m (cs k) \<in> assume_es (Pre k, Rely k)"
           
          {
            fix k
            assume c0: "Suc m \<le> length (cs k) \<and> 0 < Suc m"
            from p7 have c2: "length (cs k) > 0"
              by (metis (no_types, lifting) cpts_es_not_empty cpts_of_es_def gr0I length_0_conv mem_Collect_eq) 
            from p6 have c3: "length (cs k) = length c" by (simp add:conjoin_def same_length_def)

            let ?esl = "take (Suc m) (cs k)"
            have "?esl \<in> assume_es (Pre k, Rely k)"
            proof(cases "m = 0")
              assume d0: "m = 0"
              have "gets_es (take (Suc m) (cs k)!0) \<in> Pre k" 
                proof - 
                  from p6 c2 c3 have "gets (c!0) = gets_es ((cs k)!0)" 
                    by (simp add:conjoin_def same_state_def)
                  moreover
                  from p5 have "gets (c!0) \<in> pre" by (simp add:assume_pes_def)
                  ultimately show ?thesis using p1 p8  by auto 
                qed
              moreover
              from d0 have d1: "length (take (Suc m) (cs k)) = 1"
                using One_nat_def c2 gr0_implies_Suc length_take min_0R min_Suc_Suc by fastforce
              moreover
              from d1 have "\<forall>i. Suc i < length (take (Suc m) (cs k)) 
                    \<longrightarrow> (take (Suc m) (cs k)) ! i -ese\<rightarrow> (take (Suc m) (cs k)) ! Suc i 
                    \<longrightarrow> (gets_es ((take (Suc m) (cs k)) ! i), gets_es ((take (Suc m) (cs k)) ! Suc i)) \<in> rely"
                by auto
              moreover
              have "assume_es (Pre k, Rely k) = {c. gets_es (c ! 0) \<in> Pre k \<and>
                    (\<forall>i. Suc i < length c \<longrightarrow> c ! i -ese\<rightarrow> c ! Suc i 
                          \<longrightarrow> (gets_es (c ! i), gets_es (c ! Suc i)) \<in> Rely k)}" by (simp add:assume_es_def)
              ultimately show ?thesis using Suc_neq_Zero less_one mem_Collect_eq by auto
            next
              assume "m \<noteq> 0"
              then have dd0: "m > 0" by simp
              with b0 c0 have dd1: "take m (cs k) \<in> assume_es (Pre k, Rely k)" by simp
              
              have "gets_es (?esl ! 0) \<in> Pre k"
                proof - 
                  from p6 c2 c3 have "gets (c!0) = gets_es ((cs k)!0)" 
                    by (simp add:conjoin_def same_state_def)
                  moreover
                  from p5 have "gets (c!0) \<in> pre" by (simp add:assume_pes_def)
                  ultimately show ?thesis using p1 p8 by auto 
                qed
              moreover
              have "\<forall>i. Suc i<length ?esl \<longrightarrow> 
                   ?esl!i -ese\<rightarrow> ?esl!(Suc i) \<longrightarrow> 
                   (gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> Rely k"
                proof -
                {
                  fix i
                  assume d0: "Suc i<length ?esl"
                    and  d1: "?esl!i -ese\<rightarrow> ?esl!Suc i"
                  then have d2: "?esl!i = (cs k)!i \<and> ?esl!Suc i = (cs k)! Suc i"
                    by auto
                  from p6 c3 d0 have d4: "(\<exists>t k. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<and>
                            (\<forall>k t. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                    (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i))))
                            \<or>
                            (((c!i) -pese\<rightarrow> (c!Suc i)) \<and> (\<forall>k. (((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i))))"
                    by (simp add:conjoin_def compat_tran_def)
                  from d1 have d5: "((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i)"
                        by (simp add: d2) 
                  from d4 have "(gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> Rely k"
                    proof
                      assume e0: "\<exists>t k. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<and>
                            (\<forall>k t. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                    (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i)))"
                      then obtain ct and k' where e1: "((c!i) -pes-(ct\<sharp>k')\<rightarrow> (c!Suc i)) \<and>
                                  (((cs k')!i) -es-(ct\<sharp>k')\<rightarrow> ((cs k')! Suc i))" by auto
                      with p6 p8 d0 d5 have e2: "k \<noteq> k'" 
                        using conjoin_def[of c cs] same_spec_def[of c cs]
                           es_tran_not_etran1 by blast 

                      with e0 e1 have e3: "((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i)" by auto
                      with d0 have "(?esl!i) -ese\<rightarrow> (?esl! Suc i)" by auto
                      then show ?thesis
                        proof(cases "i < m - 1")
                          assume f0: "i < m - 1"
                          with d2 have f1:"take (Suc m) (cs k) ! i = take m (cs k) ! i"
                            by (simp add: diff_less_Suc less_trans_Suc) 
                          
                          from f0 have f2: "take (Suc m) (cs k) ! Suc i = take m (cs k) ! Suc i"
                            by (simp add: d2 gr_implies_not0 nat_le_linear)
                          from dd1 have "\<forall>i. Suc i<length (take m (cs k)) \<longrightarrow> 
                              (take m (cs k))!i -ese\<rightarrow> (take m (cs k))!(Suc i) \<longrightarrow> 
                              (gets_es ((take m (cs k))!i), gets_es ((take m (cs k))!Suc i)) \<in> Rely k"
                            by (simp add:assume_es_def)
                          with dd0 f0 have "(gets_es (take m (cs k) ! i), gets_es (take m (cs k) ! Suc i)) \<in> Rely k"
                            by (metis (no_types, lifting) One_nat_def Suc_mono Suc_pred d0 d1 f1 f2 length_take min_less_iff_conj)
                          with f1 f2 show ?thesis by simp
                        next
                          assume  "\<not>(i < m - 1)"
                          with d0 have f0: "i = m - 1"
                            by (simp add: c0 dd0 less_antisym min.absorb2) 
                          let ?esl2 = "take (Suc m) (cs k')"
                          
                          from b0 c0 dd0 have "take m (cs k') \<in> assume_es (Pre k', Rely k')"
                            by (metis Suc_leD p8) 
                          moreover
                          from e1 f0 have "\<not>(cs k' ! (m-1) -ese\<rightarrow> cs k' !m)"
                            using Suc_pred' dd0 es_tran_not_etran1 by fastforce 
                          ultimately have f1: "take (Suc m) (cs k') \<in> assume_es (Pre k', Rely k')" 
                            using assume_es_one_more[of "cs k'" m "Pre k'" "Rely k'"] p8 p9 c0 dd0
                            by (simp add: Suc_le_eq)
                          from p7 have "cs k' \<in> cpts_of_es (pes k') s x" by simp
                          with p8 c0 dd0 have f2: "?esl2\<in>cpts_of_es (pes k') s x" 
                            using cpts_es_take[of "cs k'" m] cpts_of_es_def[of "pes k'" s x]
                              by (simp add: Suc_le_lessD) 
                          from p0 have f3: "\<Turnstile> pes k' sat\<^sub>s [Pre k', Rely k', Guar k', Post k'] " by simp
                          with f1 f2 have "?esl2\<in>commit_es(Guar k', Post k')" 
                            using es_validity_def[of "pes k'" "Pre k'" "Rely k'" "Guar k'" "Post k'"]
                              by auto
                          then have "\<forall>i. Suc i<length ?esl2 \<longrightarrow> 
                                        (\<exists>t. ?esl2!i -es-t\<rightarrow> ?esl2!(Suc i)) \<longrightarrow> 
                                        (gets_es (?esl2!i), gets_es (?esl2!Suc i)) \<in> Guar k'"
                            by (simp add:commit_es_def)
                          
                          with p8 e1 f0 c0 dd0 have "(gets_es (?esl2 ! (m-1)), gets_es (?esl2 ! m))\<in>Guar k'"
                            by (metis (no_types, lifting) One_nat_def Suc_pred diff_less_Suc length_take lessI min.absorb2 nth_take)
                          with p3 p11 c0 f0 e2 show ?thesis
                            by (smt Suc_diff_1 Suc_leD c3 dd0 le_less_linear not_less_eq_eq nth_take subsetCE)
                        qed
                    next
                      assume e0: "(((c!i) -pese\<rightarrow> (c!Suc i)) \<and> (\<forall>k. (((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i))))"
                      from p5 have "\<forall>i. Suc i<length c \<longrightarrow> 
                                        c!i -pese\<rightarrow> c!(Suc i) \<longrightarrow> 
                                        (gets (c!i), gets (c!Suc i)) \<in> rely"
                         by (simp add:assume_pes_def) 
                      moreover
                      from p8 c0 d0 have e1:"Suc i < length c" by simp
                      ultimately have "(gets (c!i), gets (c!Suc i)) \<in> rely" using e0 by simp
                      with p2 have "(gets (c!i), gets (c!Suc i)) \<in> Rely k" by auto
                      with p8 p11 c0 d0 show ?thesis
                        using Suc_lessD e1 d2 by auto 
                    qed
                }
                then show ?thesis by auto 
                qed

              ultimately show ?thesis by (simp add:assume_es_def)
            qed
                
          }
          then show ?case by auto
        qed
    }
    then show ?thesis by auto
  qed

lemma es_tran_sat_guar_aux: 
  "\<lbrakk>\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]; 
        \<forall>k. pre \<subseteq> Pre k; 
        \<forall>k. rely \<subseteq> Rely k; 
        \<forall>k j. j\<noteq>k \<longrightarrow> Guar j \<subseteq> Rely k;
        c \<in> cpts_of_pes pes s x; c\<in>assume_pes(pre, rely);
        c \<propto> cs; \<forall>k. cs k \<in> cpts_of_es (pes k) s x \<rbrakk> 
        \<Longrightarrow>\<forall>k i m. m \<le> length c \<longrightarrow> Suc i < length (take m (cs k)) \<longrightarrow> (\<exists>t.((take m (cs k))!i-es-t\<rightarrow>((take m (cs k))!Suc i))) 
        \<longrightarrow> ann_preserves_es ((take m (cs k))!i) \<and> (gets_es ((take m (cs k))!i), gets_es ((take m (cs k))!Suc i)) \<in> Guar k"
  proof -
    assume p0: "\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]"
      and  p1: "\<forall>k. pre \<subseteq> Pre k"
      and  p2: "\<forall>k. rely \<subseteq> Rely k"
      and  p3: "\<forall>k j. j\<noteq>k \<longrightarrow>  Guar j \<subseteq> Rely k"
      and  p4: "c \<in> cpts_of_pes pes s x"
      and  p5: "c \<in> assume_pes(pre, rely)" 
      and  p6: "c \<propto> cs"
      and  p7: "\<forall>k. cs k \<in> cpts_of_es (pes k) s x"
    from p6 have p8: "\<forall>k. length (cs k) = length c" by (simp add:conjoin_def same_length_def)
    {
      fix k i m
      assume a0: "m \<le> length c"
        and  a1: "Suc i < length (take m (cs k))"
        and  a2: "\<exists>t.((take m (cs k))!i-es-t\<rightarrow>((take m (cs k))!Suc i))"
      have "ann_preserves_es ((take m (cs k))!i) \<and> (gets_es ((take m (cs k))!i),
                              gets_es ((take m (cs k))!Suc i)) \<in> Guar k"
        proof(cases "m = 0")
          assume "m = 0" with a1 show ?thesis by auto
        next
          assume "m \<noteq> 0"
          then have b0: "m > 0" by simp
          let ?esl = "take m (cs k)"
          from p7 have "cs k \<in> cpts_of_es (pes k) s x" by simp
          then have "cs k!0=(pes k,s,x) \<and> cs k \<in> cpts_es" by (simp add:cpts_of_es_def)
          with b0 have "?esl!0=(pes k,s,x) \<and> ?esl \<in> cpts_es"
            by (metis Suc_pred a0 cpts_es_take leD not_less_eq nth_take p8) 
          then have r1: "?esl \<in> cpts_of_es (pes k) s x" by (simp add:cpts_of_es_def)
          from p0 p1 p2 p3 p4 p5 p6 p7
            have "\<forall>n. n \<le> length (cs k) \<and> n > 0 \<longrightarrow> take n (cs k)\<in>assume_es(Pre k, Rely k)"
              using cpts_es_sat_rely[of pes Pre Rely Guar Post pre rely c s x cs] by auto
          with p8 a0 b0 have r2: "?esl\<in>assume_es(Pre k, Rely k)" by auto
          
          from p0 have "(cpts_of_es (pes k) s x) \<inter> assume_es(Pre k, Rely k) \<subseteq> commit_es(Guar k, Post k)"
            by (simp add:es_validity_def)
          with r1 r2 have "?esl \<in> commit_es(Guar k, Post k)"
            using IntI subsetCE by auto 
          then have "\<forall>i. Suc i<length ?esl \<longrightarrow> (\<exists>t. ?esl!i -es-t\<rightarrow> ?esl!(Suc i)) \<longrightarrow> 
                    ann_preserves_es (?esl!i) \<and> (gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> Guar k"
            by (simp add:commit_es_def)
          with a1 a2 show ?thesis by auto
        qed
    }
    then show ?thesis by auto
  qed


lemma es_tran_sat_guar: 
      "\<lbrakk>\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]; 
        \<forall>k. pre \<subseteq> Pre k; 
        \<forall>k. rely \<subseteq> Rely k; 
        \<forall>k j. j\<noteq>k \<longrightarrow>  Guar j \<subseteq> Rely k;
        c \<in> cpts_of_pes pes s x; c\<in>assume_pes(pre, rely);
        c \<propto> cs; \<forall>k. cs k \<in> cpts_of_es (pes k) s x \<rbrakk> 
        \<Longrightarrow>\<forall>k i. Suc i < length (cs k) \<longrightarrow> (\<exists>t.((cs k)!i-es-t\<rightarrow>(cs k)!Suc i))\<longrightarrow> 
           ann_preserves_es ((cs k)!i) \<and> (gets_es ((cs k)!i),gets_es ((cs k)!Suc i)) \<in> Guar k"
  proof -
    assume p0: "\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]"
      and  p1: "\<forall>k. pre \<subseteq> Pre k"
      and  p2: "\<forall>k. rely \<subseteq> Rely k"
      and  p3: "\<forall>k j. j\<noteq>k \<longrightarrow>  Guar j \<subseteq> Rely k"
      and  p4: "c \<in> cpts_of_pes pes s x"
      and  p5: "c \<in> assume_pes(pre, rely)" 
      and  p6: "c \<propto> cs"
      and  p7: "\<forall>k. cs k \<in> cpts_of_es (pes k) s x"
    then have "\<forall>k i m. m \<le> length c \<longrightarrow> Suc i < length (take m (cs k)) \<longrightarrow> (\<exists>t.((take m (cs k))!i-es-t\<rightarrow>((take m (cs k))!Suc i))) 
      \<longrightarrow> ann_preserves_es ((take m (cs k))!i) \<and>(gets_es ((take m (cs k))!i),gets_es ((take m (cs k))!Suc i)) \<in> Guar k"
      using es_tran_sat_guar_aux [of pes Pre Rely Guar Post pre rely c s x cs] by simp
    moreover
    from p6 have "\<forall>k. length c = length (cs k)" by (simp add:conjoin_def same_length_def)
    ultimately show ?thesis by auto
  qed


lemma conjoin_es_sat_assume: 
      "\<lbrakk>\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]; 
        \<forall>k. pre \<subseteq> Pre k; 
        \<forall>k. rely \<subseteq> Rely k; 
        \<forall>k j. j\<noteq>k \<longrightarrow>  Guar j \<subseteq> Rely k;
        c \<in> cpts_of_pes pes s x; c\<in>assume_pes(pre, rely);
        c \<propto> cs; \<forall>k. cs k \<in> cpts_of_es (pes k) s x \<rbrakk> 
        \<Longrightarrow> \<forall>k. cs k \<in> assume_es(Pre k, Rely k)" 
  proof -
    assume p0: "\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]"
      and  p1: "\<forall>k. pre \<subseteq> Pre k"
      and  p2: "\<forall>k. rely \<subseteq> Rely k"
      and  p3[rule_format]: "\<forall>k j. j\<noteq>k \<longrightarrow>  Guar j \<subseteq> Rely k"
      and  p4: "c \<in> cpts_of_pes pes s x"
      and  p5: "c \<in> assume_pes(pre, rely)" 
      and  p6: "c \<propto> cs"
      and  p7: "\<forall>k. cs k \<in> cpts_of_es (pes k) s x"
    from p6 have p11[rule_format]: "\<forall>k. length (cs k) = length c" by (simp add:conjoin_def same_length_def)
    from p7 have p12: "\<forall>k. cs k \<in> cpts_es" using cpts_of_es_def mem_Collect_eq by fastforce 
    with p11 have "c \<noteq> Nil" using cpts_es_not_empty length_0_conv by auto 
    then have p13: "length c > 0" by auto
    {
      fix k
      have "cs k \<in> assume_es(Pre k, Rely k)"
        using p0 p1 p2 p3 p4 p5 p6 p7 p13 p11 
          cpts_es_sat_rely[of pes Pre Rely Guar Post pre rely c s x cs "length (cs k)" k] by force
    }
    then show ?thesis by auto
  qed


lemma pes_tran_sat_guar: 
      "\<lbrakk>\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]; 
        \<forall>k. pre \<subseteq> Pre k; 
        \<forall>k. rely \<subseteq> Rely k; 
        \<forall>k j. j\<noteq>k \<longrightarrow>  Guar j \<subseteq> Rely k;
        \<forall>k. Guar k \<subseteq> guar;
        c \<in> cpts_of_pes pes s x; c\<in>assume_pes(pre, rely)\<rbrakk> 
        \<Longrightarrow>\<forall>i. Suc i < length c \<longrightarrow> (\<exists>t. c!i -pes-t\<rightarrow> c!(Suc i)) \<longrightarrow> 
        ann_preserves_pes (c!i) \<and> (gets (c!i),gets (c!Suc i)) \<in> guar"
  proof -
    assume p0: "\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]"
      and  p1: "\<forall>k. pre \<subseteq> Pre k"
      and  p2: "\<forall>k. rely \<subseteq> Rely k"
      and  p3: "\<forall>k j. j\<noteq>k \<longrightarrow>  Guar j \<subseteq> Rely k"
      and  p4: "\<forall>k. Guar k \<subseteq> guar"
      and  p5: "c \<in> cpts_of_pes pes s x"
      and  p6: "c\<in>assume_pes(pre, rely)"
      {
        fix i
        assume a0: "Suc i < length c"
          and  a1: "\<exists>t. c!i -pes-t\<rightarrow> c!(Suc i)"
        from p5 have "\<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es (pes k) s x) \<and> c \<propto> cs" 
          by (meson cpt_imp_exist_conjoin_cs) 
        then obtain cs where a2: "(\<forall>k. (cs k) \<in> cpts_of_es (pes k) s x) \<and> c \<propto> cs" by auto
        then have "compat_tran c cs" by (simp add:conjoin_def)
        with a0 have a3: "(\<exists>t k. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<and>
                          (\<forall>k t. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i))))
                          \<or>
                          (((c!i) -pese\<rightarrow> (c!Suc i)) \<and> (\<forall>k. (((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i))))"
          by (simp add:compat_tran_def)
        from a1 have "\<not>((c!i) -pese\<rightarrow> (c!Suc i))"
          using pes_tran_not_etran1 by blast 
        with a3 have "\<exists>t k. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<and>
                          (\<forall>k t. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i)))"
          by simp
        then obtain t and k where a4: "(c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<and>
                          (\<forall>k t. (c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (cs k'!i -ese\<rightarrow> cs k'! Suc i)))"
          by auto
        from p0 p1 p2 p3 p4 p5 p6 a2 have
          "\<forall>k i. Suc i < length (cs k) \<longrightarrow> (\<exists>t.((cs k)!i-es-t\<rightarrow>(cs k)!Suc i))  \<longrightarrow> 
                 ann_preserves_es ((cs k)!i) \<and> (gets_es ((cs k)!i),gets_es ((cs k)!Suc i)) \<in> Guar k" 
          using es_tran_sat_guar [of pes Pre Rely Guar Post pre rely c s x cs] by simp
        then have a5: "Suc i < length (cs k) \<longrightarrow> (\<exists>t.((cs k)!i-es-t\<rightarrow>(cs k)!Suc i)) \<longrightarrow> 
                      ann_preserves_es ((cs k)!i) \<and> (gets_es ((cs k)!i),gets_es ((cs k)!Suc i)) \<in> Guar k" 
          by simp
        from a2 have a6: "length c = length (cs k)" by (simp add:conjoin_def same_length_def)
        with a0 a4 a5 have a7: "ann_preserves_es ((cs k)!i) \<and> (gets_es ((cs k)!i),gets_es ((cs k)!Suc i)) \<in> Guar k" by auto
        from a0 a2 have a8: "gets_es ((cs k)!i) = gets (c!i)" by (simp add:conjoin_def same_state_def)
        from a0 a2 have a9: "gets_es ((cs k)!Suc i) = gets (c!Suc i)" by (simp add:conjoin_def same_state_def)
        with a7 a8 have "(gets (c!i),gets (c!Suc i)) \<in> Guar k" by auto
        with p4 have "(gets (c!i),gets (c!Suc i)) \<in> guar" by auto
      }
      thus ?thesis by auto
    qed


lemma parallel_sound: 
      "\<lbrakk>\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]; 
        \<forall>k. pre \<subseteq> Pre k; 
        \<forall>k. rely \<subseteq> Rely k; 
        \<forall>k j. j\<noteq>k \<longrightarrow>  Guar j \<subseteq> Rely k;
        \<forall>k. Guar k \<subseteq> guar;
        \<forall>k. Post k \<subseteq> post\<rbrakk> 
    \<Longrightarrow> \<Turnstile> pes SAT [pre, rely, guar, post]"
  proof -
    assume p0: "\<forall>k. \<Turnstile> (pes k) sat\<^sub>s [Pre k, Rely k, Guar k, Post k]"
      and  p1: "\<forall>k. pre \<subseteq> Pre k"
      and  p2: "\<forall>k. rely \<subseteq> Rely k"
      and  p3: "\<forall>k j. j\<noteq>k \<longrightarrow>  Guar j \<subseteq> Rely k"
      and  p4: "\<forall>k. Guar k \<subseteq> guar"
      and  p5: "\<forall>k. Post k \<subseteq> post"
    have "\<forall>s x. (cpts_of_pes pes s x) \<inter> assume_pes(pre, rely) \<subseteq> commit_pes(guar, post)"
      proof -
      {
        fix c s x
        assume a0: "c\<in>(cpts_of_pes pes s x) \<inter> assume_pes(pre, rely)"
        then have a1: "c\<in>(cpts_of_pes pes s x) \<and> c\<in>assume_pes(pre, rely)" by simp
        with p0 p1 p2 p3 p4 have "\<forall>i. Suc i < length c \<longrightarrow> (\<exists>t. c!i -pes-t\<rightarrow> c!(Suc i)) \<longrightarrow> 
             ann_preserves_pes (c!i) \<and> (gets (c!i),gets (c!Suc i)) \<in> guar" 
          using pes_tran_sat_guar [of pes Pre Rely Guar Post pre rely guar c s x] by simp
        then have "c\<in>commit_pes(guar, post)" 
          by (simp add: commit_pes_def)
      }
      then show ?thesis by auto
      qed

    then show ?thesis by (simp add:pes_validity_def)
  qed


lemma parallel_seq_sound: 
      "\<lbrakk>pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
        \<Turnstile> pes SAT [pre', rely', guar', post']\<rbrakk> 
    \<Longrightarrow> \<Turnstile> pes SAT [pre, rely, guar, post]"
  proof -
    assume p0: "pre \<subseteq> pre'"
      and  p1: "rely \<subseteq> rely'"
      and  p2: "guar' \<subseteq> guar"
      and  p3: "post' \<subseteq> post"
      and  p4: "\<Turnstile> pes SAT [pre', rely', guar', post']"
    from p4 have p5: "\<forall>s x. (cpts_of_pes pes s x) \<inter> assume_pes(pre', rely') \<subseteq> commit_pes(guar', post')"
      by (simp add: pes_validity_def)
    have "\<forall>s x. (cpts_of_pes pes s x) \<inter> assume_pes(pre, rely) \<subseteq> commit_pes(guar, post)"
      proof -
      {
        fix c s x
        assume a0: "c\<in>(cpts_of_pes pes s x) \<inter> assume_pes(pre, rely)"
        then have "c\<in>(cpts_of_pes pes s x) \<and> c\<in>assume_pes(pre, rely)" by simp
        with p0 p1 have "c\<in>(cpts_of_pes pes s x) \<and> c\<in>assume_pes(pre', rely')"
          using assume_pes_imp[of pre pre' rely rely' c] by simp
        with p5 have "c\<in>commit_pes(guar', post')" by auto
        with p2 p3 have "c\<in>commit_pes(guar, post)" 
          using commit_pes_imp[of guar' guar post' post c] by simp
      }
      then show ?thesis by auto
      qed
    then show ?thesis by (simp add:pes_validity_def)
  qed

theorem rgsound_pes: "\<turnstile> rgf_par SAT [pre, rely, guar, post] \<Longrightarrow> \<Turnstile> paresys_spec rgf_par SAT [pre, rely, guar, post]"
  apply(erule rghoare_pes.induct)
  proof -
  {
    fix pes pre rely guar post
    assume p0: "\<forall>k. \<turnstile> fst ((pes::'k \<Rightarrow> ('l,'k,'s) rgformula_es) k) sat\<^sub>s [Pre\<^sub>e\<^sub>s (pes k), Rely\<^sub>e\<^sub>s (pes k), Guar\<^sub>e\<^sub>s (pes k), Post\<^sub>e\<^sub>s (pes k)]"
      and  p1: "\<forall>k. pre \<subseteq> Pre\<^sub>e\<^sub>s (pes k)"
      and  p2: "\<forall>k. rely \<subseteq> Rely\<^sub>e\<^sub>s (pes k)"
      and  p3: "\<forall>k j. j \<noteq> k \<longrightarrow> Guar\<^sub>e\<^sub>s (pes j) \<subseteq> Rely\<^sub>e\<^sub>s (pes k)"
      and  p4: "\<forall>k. Guar\<^sub>e\<^sub>s (pes k) \<subseteq> guar"
      and  p5: "\<forall>k. Post\<^sub>e\<^sub>s (pes k) \<subseteq> post"
    from p0 have "\<forall>k. \<Turnstile> evtsys_spec (fst (pes k)) sat\<^sub>s [Pre\<^sub>e\<^sub>s (pes k), Rely\<^sub>e\<^sub>s (pes k), Guar\<^sub>e\<^sub>s (pes k), Post\<^sub>e\<^sub>s (pes k)]"
      proof -
      {
        fix k
        from p0 have "\<turnstile> fst (pes k) sat\<^sub>s [Pre\<^sub>e\<^sub>s (pes k), Rely\<^sub>e\<^sub>s (pes k), Guar\<^sub>e\<^sub>s (pes k), Post\<^sub>e\<^sub>s (pes k)]"
          by simp
        then have "\<Turnstile> evtsys_spec (fst (pes k)) sat\<^sub>s [Pre\<^sub>e\<^sub>s (pes k), Rely\<^sub>e\<^sub>s (pes k), Guar\<^sub>e\<^sub>s (pes k), Post\<^sub>e\<^sub>s (pes k)]"
          using rgsound_es [of "fst (pes k)" "Pre\<^sub>e\<^sub>s (pes k)" "Rely\<^sub>e\<^sub>s (pes k)" "Guar\<^sub>e\<^sub>s (pes k)" "Post\<^sub>e\<^sub>s (pes k)"]
            by simp
      }
      then show ?thesis by auto
      qed
    with p1 p2 p3 p4 p5 show "\<Turnstile> paresys_spec pes SAT [pre, rely, guar, post]" 
      using parallel_sound [of "paresys_spec pes" "Pre\<^sub>e\<^sub>s\<circ>pes" "Rely\<^sub>e\<^sub>s\<circ>pes" "Guar\<^sub>e\<^sub>s\<circ>pes" "Post\<^sub>e\<^sub>s\<circ>pes"
            pre rely guar post] by (simp add:paresys_spec_def)
  }
  next
  {
    fix pre pre' rely rely' guar' guar post' post pesf
    assume "pre \<subseteq> pre'"
      and  "rely \<subseteq> rely'"
      and  "guar' \<subseteq> guar"
      and  "post' \<subseteq> post"
      and  "\<turnstile> pesf SAT [pre', rely', guar', post']"
      and  "\<Turnstile> paresys_spec pesf SAT [pre', rely', guar', post']"
    then show "\<Turnstile> paresys_spec pesf SAT [pre, rely, guar, post] "
      using parallel_seq_sound[of pre pre' rely rely' guar' guar post' post "paresys_spec pesf"] by simp
  }
qed


end
