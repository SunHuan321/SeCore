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
  apply (simp add: ann_pre_p_def ann_preserves_p_def ann_pre_def)
  apply (simp add:  gets_p_def getspc_p_def)
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

lemma tl_of_cptn_is_cptn: "\<lbrakk>x # xs \<in> cpts_p; xs \<noteq> []\<rbrakk> \<Longrightarrow> xs  \<in> cpts_p"
apply(subgoal_tac "1 < length (x # xs)")
 apply(drule dropcptn_is_cptn,simp+)
done

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
               (\<exists>t. c!i -et-t\<rightarrow> c!(Suc i)) \<longrightarrow> (ann_preserves_e (c!i) \<and>
               (gets_e (c!i), gets_e (c!Suc i)) \<in> guar1)) \<and> 
               (getspc_e (last c) = AnonyEvent (None) \<longrightarrow> gets_e (last c) \<in> post1)"
      by (simp add:commit_e_def)
    show ?thesis
    proof(simp add:commit_e_def)
        from p0 p1 a0 show "(\<forall>i. Suc i < length c \<longrightarrow> (\<exists>t. c ! i -et-t\<rightarrow> c ! Suc i) 
                            \<longrightarrow> (ann_preserves_e (c!i) \<and>
                                (gets_e (c ! i), gets_e (c ! Suc i)) \<in> guar)) \<and> 
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
            from c0 have c6: "(AnonyEvent P', s', x) -et-(Cmd CMP)\<sharp>k\<rightarrow> (AnonyEvent Q', t', x)" 
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
apply(simp add:prog_validity_def assume_p_def commit_p_def)
apply clarify
apply(erule_tac x=s in allE)
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
  apply(simp add:commit_p_def)
  apply(simp add:getspc_p_def gets_p_def)
  apply(rule conjI, clarify)
 apply (rule conjI)
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
   apply(simp add:cpts_of_p_def assume_p_def gets_p_def)
   apply clarify
   apply(frule_tac j=0 and k=i and p= r in stability)
  apply simp_all
     apply(erule_tac x=ia in allE,simp)
    apply(erule_tac i=i and f=f in unique_ctran_Basic,simp_all)
   apply(case_tac "x!i")
   apply clarify
   apply(drule_tac s="Some (AnnBasic r f)" in sym,simp)
  apply (rule ann_preserves_p_cmd, simp add: ann_preserves_p_def)
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
  apply(simp add:commit_p_def)
  apply(rule conjI, clarify)
  apply (rule conjI)
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
 apply(drule_tac c=l in subsetD)
  apply (simp add:cpts_of_p_def)
  apply clarify
  apply(erule_tac x=ia and P="\<lambda>i. H i \<longrightarrow> (J i, I i)\<in>ptran" for H J I in allE,simp)
  apply(erule petranE,simp)
    apply simp
   apply(simp add:cpts_of_p_def assume_p_def gets_p_def)
   apply clarify
   apply(frule_tac j=0 and k=i and p= r in stability)
  apply simp_all
     apply(erule_tac x=ia in allE,simp)
    apply(erule_tac i=i in unique_ctran_Await,force,simp_all)
   apply(case_tac "x!i")
   apply clarify
   apply(drule_tac s="Some (AnnAwait r b P)" in sym,simp)
   apply (rule ann_preserves_p_cmd, simp add: ann_preserves_p_def)
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
apply(frule_tac j=0 and k="j" and p= r in stability,simp_all)
  apply(erule_tac x=i in allE,simp)
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
   apply(drule_tac c="drop (Suc m) x" in subsetD)
    apply simp
    apply clarify
   apply simp
   apply clarify
    apply(case_tac "i\<le>m")
     apply (rule conjI)
      apply(erule_tac x=i in allE, erule impE, assumption)
     apply (metis (mono_tags, lifting) le_neq_implies_less snd_conv)
    apply (case_tac "i<m", simp, clarsimp)
    apply (rule ann_preserves_p_cmd, simp)
   apply (drule_tac a = "i - (Suc m)" in all_imp2D)
  back
     apply linarith
    apply simp+
apply(case_tac "length (drop (Suc m) x)",simp)
apply(erule_tac x="sa" in allE)
back
apply(drule_tac c="drop (Suc m) x" in subsetD,simp)
 apply clarify
apply simp
apply clarify
  apply(case_tac "i\<le>m")
  apply (rule conjI)
   apply(erule_tac x=i in allE, erule impE, assumption)
    apply (metis (no_types, hide_lams) linorder_neqE_nat not_less snd_conv)
    apply (case_tac "i<m", simp, clarsimp)
   apply (rule ann_preserves_p_cmd, simp)
  apply (drule_tac a = "i - (Suc m)" in all_imp2D)
  back
    apply linarith
  apply simp+
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

lemma lift_step : "lift Q (xs ! i) -c\<rightarrow> lift Q (xs ! Suc i) \<Longrightarrow> fst (xs ! i) \<noteq> None \<Longrightarrow>  xs ! i -c\<rightarrow> xs ! Suc i"
proof-
  assume a1: "lift Q (xs ! i) -c\<rightarrow> lift Q (xs ! Suc i)"
  and  a2: "fst (xs ! i) \<noteq> None"
  show ?thesis
  proof-
    from a2 have  "\<exists>P s. xs ! i = (Some P, s) "
      by (metis eq_fst_iff not_None_eq)
    then obtain P and s where b1 : "xs ! i = (Some P, s)"
      by auto
    then show ?thesis
    proof(induct "fst (xs ! (Suc i))")
      case None
      then have  "\<exists>t. xs ! (Suc i) = (None, t)"
        by (metis prod.collapse)
      then obtain t where b2 : "xs ! (Suc i) = (None, t)"
        by auto
      then have "(Some (AnnSeq P Q), s) -c\<rightarrow> (Some Q, t)"
        using a1 b1 by (simp add: lift_def)
      with b1 and b2 show ?case
        apply simp
        by (erule ptran.cases, simp_all)
    next
      case (Some R)
      then have "\<exists>t. xs ! (Suc i) = (Some R, t)"
        by (metis prod.collapse)
      then obtain R and t where b3: "xs ! (Suc i) = (Some R, t)"
        by auto
      then have "(Some (AnnSeq P Q), s) -c\<rightarrow> (Some (AnnSeq R Q), t)"
        using a1 b1 by (simp add: lift_def)
      with b1 and b3 show ?case
        apply simp
        by (erule ptran.cases, simp_all)
    qed
  qed
qed

lemma lift_not_None : "\<lbrakk>\<forall>i<length x. fst(x!i)\<noteq>Some Q ; x=map (lift Q) xs; i < length xs \<rbrakk> 
   \<Longrightarrow>  fst (xs !i) \<noteq> None"
proof
  assume a1: "\<forall>i<length x. fst(x!i)\<noteq>Some Q"
     and a2: "x=map (lift Q) xs"
     and a3: "i < length xs"
     and a4: "fst (xs ! i) = None"
  show False
  proof-
    from a4 have "\<exists>s. xs ! i = (None, s)"
      by (metis prod.collapse)
    then obtain s where "xs ! i = (None, s)"
      by auto
    then have "fst (lift Q (xs ! i)) = Some Q"
      by (simp add: lift_def)
    then have "fst (x ! i) = Some Q"
      by (simp add: a2 a3)
    then show ?thesis
      using a1 a2 a3 by auto
  qed
qed


lemma ann_preserves_p_lift: "ann_preserves_p (xs ! i) \<Longrightarrow> fst (xs ! i) \<noteq> None \<Longrightarrow> ann_preserves_p (lift Q (xs ! i))"
  apply (subgoal_tac "\<exists>P s. xs ! i = (Some P, s)")
   apply (simp add: lift_def)
   apply auto[1]
   apply (simp add: ann_preserves_p_def gets_p_def getspc_p_def)
  by (metis eq_fst_iff not_None_eq)

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
  apply (rule conjI)
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
    apply (subgoal_tac "fst (xs ! i) \<noteq> None")
    apply (drule_tac a = i in all_imp2D, simp)
      apply (rule_tac Q = Q in lift_step, simp, simp)
     apply (rule ann_preserves_p_lift, simp, simp)
    apply (rule lift_not_None, simp_all)
   apply clarify
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
(*@{text "\<exists>i<length x. fst (x ! i) = Some Q"}*)
  apply(erule exE)
  apply(drule_tac n=i and P="\<lambda>i. i < length x \<and> fst (x ! i) = Some Q" in Ex_first_occurrence)
  apply clarify
  apply (simp add:cpts_of_p_def)
  apply clarify
  apply(frule_tac i=m in Seq_sound2,force)
     apply simp+
  apply clarify
  apply(simp add:commit_p_def)
  apply(erule_tac x=s in allE)
  apply(drule_tac c=xs in subsetD,simp)
   apply(case_tac "xs=[]",simp)
   apply(simp add:cpts_of_p_def assume_p_def nth_append gets_p_def getspc_p_def)
   apply clarify
   apply(erule_tac x=i in allE)
  back
   apply(simp add:snd_lift)
   apply(erule mp)
   apply(force elim:petranE intro:EnvP simp add:lift_def)
  apply simp
  apply clarify
  apply(erule_tac x="snd(xs!m)" in allE)
  apply(simp add:getspc_p_def gets_p_def)
  apply(drule_tac c=ys in subsetD,simp add:cpts_of_p_def assume_p_def)
   apply(case_tac "xs\<noteq>[]")
    apply(drule last_conv_nth,simp)
    apply(rule conjI)
     apply(simp add:gets_p_def)
     apply(erule mp)
     apply(case_tac "xs!m")
     apply(case_tac "fst(xs!m)",simp)
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
   apply (rule conjI) 
    apply(case_tac "i<m",simp add:nth_append)
  apply(simp add:snd_lift)
  apply(erule allE, erule impE, assumption)
  apply(case_tac "(xs ! i)")
  apply(case_tac "(xs ! Suc i)")
  apply(case_tac "fst(xs ! i)",force simp add:lift_def)
     apply(case_tac "fst(xs ! Suc i)")
  using lift_step apply blast
  using lift_step apply blast
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
         apply(case_tac ys,simp+)
      apply force
     apply arith
    apply force
   apply (case_tac "i < m")
    apply (subgoal_tac "fst (xs ! i) \<noteq> None")
     apply (drule_tac a = i in all_imp2D, simp)
      apply (rule_tac Q = Q in lift_step, simp add: nth_append, simp)
     apply (simp add: nth_append, rule ann_preserves_p_lift, simp, simp)
    apply (case_tac "fst (xs ! i) = None", simp add: nth_append)
     apply (subgoal_tac "fst (lift Q (xs ! i)) = Some Q", simp)
     apply (simp add: lift_def)
     apply (smt case_prod_beta fstI, simp)
apply (case_tac "i = m", simp add: nth_append)
   apply (drule_tac a = 0 in all_imp2D, simp)
    apply (subgoal_tac "lift Q (xs ! m) = ys ! 0")
     apply (simp add: List.nth_tl)
    apply (metis (mono_tags, lifting) CollectD cpts_of_p_def lessI prod.collapse snd_lift)
   apply (metis (mono_tags, lifting) CollectD cpts_of_p_def lessI prod.collapse snd_lift)
  apply (simp add: nth_append)
  apply (drule_tac a = "i - m" in all_imp2D, simp)
   apply (metis (no_types) List.nth_tl One_nat_def Suc_diff_Suc Suc_lessD add_diff_inverse_nat 
      add_less_cancel_left length_tl linorder_neqE_nat)
  apply (simp add: List.nth_tl Suc_diff_Suc less_SucE less_SucI linorder_neqE_nat)
   apply clarify
   apply(case_tac "(map (lift Q) xs @ tl ys)\<noteq>[]")
    apply(drule last_conv_nth)
    apply(simp add: snd_lift nth_append)
    apply(rule conjI,clarify)
     apply(case_tac ys,simp+)
    apply clarify
   apply(case_tac ys,simp+)
  done


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

lemma take_assume_p: "l \<in> assume_p (pre, rely) \<Longrightarrow> take (Suc i) l \<in> assume_p (pre, rely)"
  by (simp add: assume_p_def)

lemma commit_post : "l \<in> commit_p (guar, post) \<Longrightarrow>  last l = (None, t) \<Longrightarrow> t \<in> post"
  by (simp add: commit_p_def getspc_p_def gets_p_def)

lemma commit_preserves : "\<lbrakk> Suc i < length l; l \<in> commit_p (guar, post);  
                          l!i -c\<rightarrow> l!(Suc i)\<rbrakk> \<Longrightarrow> ann_preserves_p (l!i)"
  by (simp add: commit_p_def getspc_p_def gets_p_def)

lemma While_one_ann_preserves_None: "\<lbrakk> \<Turnstile> P sat\<^sub>p [r \<inter> b, rely, guar, r]; (Some P, s) # xs \<in> cpts_p; 
  stable r rely; (Some P, s) # xs \<in> assume_p (r \<inter> b, rely); ((Some P, s) # xs) ! i = (None, t); 
  i < length ((Some P, s) # xs)\<rbrakk> \<Longrightarrow> t \<in> r"
  apply (simp add: prog_validity_def cpts_of_p_def)
  apply (erule_tac x = s in allE)
  apply(drule_tac c="take (Suc i) ((Some P, s) # xs)" in subsetD)
   apply (rule IntI)
    apply fastforce
   apply (rule take_assume_p, simp)
  apply (rule commit_post, simp)
  by (metis last_snoc length_Cons take_Suc_Cons take_Suc_conv_app_nth)

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

lemma append_take_i : "length xs \<le> i \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> (x # xs @ ys) ! i = (last xs # ys) ! (i - length xs)"
  by (simp add: last_conv_nth leD nth_Cons' nth_append)

lemma ctran_eq: "\<lbrakk>P = P1; Q = Q1; P -c\<rightarrow> Q\<rbrakk> \<Longrightarrow> P1 -c\<rightarrow>Q1"
  by simp

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
      apply (rule conjI)
       apply(force simp add:assume_p_def getspc_p_def gets_p_def)
      apply (simp add: ann_preserves_p_def assume_p_def getspc_p_def gets_p_def)
     apply(force simp add:assume_p_def getspc_p_def gets_p_def)
    apply(simp add: getspc_p_def gets_p_def)
    apply clarify
    apply(rule conjI, clarify)
     apply (rule conjI)
      apply(case_tac i,simp,simp)
      apply(force simp add:not_ctran_None2)
     apply (case_tac i, simp add: ann_preserves_p_def assume_p_def getspc_p_def gets_p_def)
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
    apply (rule conjI)
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
    apply (subgoal_tac "(Some P, sa) # xs \<in> assume_p (r \<inter> b, rely)")
     prefer 2
     apply (simp add:assume_p_def gets_p_def del:list.map)
     apply clarify
     apply(erule_tac x="Suc ia" in allE,simp add:snd_lift del:list.map)
     apply(erule mp)
     apply(case_tac "fst(((Some P, sa) # xs) ! ia)")
      apply(erule petranE,simp add:lift_def)
      apply(rule EnvP)
     apply(erule petranE,simp add:lift_def)
     apply(rule EnvP)
    apply(case_tac "fst(((Some P, sa) # xs) ! i)")
     apply(case_tac "((Some P, sa) # xs) ! i")
  apply (simp add: ann_preserves_p_def lift_def gets_p_def getspc_p_def)
     apply (rule While_one_ann_preserves_None, simp_all del:last.simps)
  using cpts_if_cpt_p_mod apply blast
     apply linarith
    apply(case_tac "((Some P, sa) # xs) ! i", simp)
    apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
    apply(erule_tac x=sa in allE)
    apply(drule_tac c="(Some P, sa) # xs" in subsetD, simp)
    apply (subgoal_tac "ann_preserves_p (((Some P, sa) # xs) ! i)")
     apply (simp add: ann_preserves_p_def lift_def gets_p_def getspc_p_def)
    apply (rule commit_preserves, simp, simp)
    apply (rule lift_step, simp, simp)
(*last=None*)
    apply(subgoal_tac "(map (lift (AnnWhile r b P)) ((Some P, sa) # xs))\<noteq>[]")
      apply(drule last_conv_nth)
    apply (simp add:getspc_p_def gets_p_def del:list.map)
    apply (metis last.simps last_length last_lift_not_None last_map)
   apply simp
(*WhileMore*)                                                              
  apply(thin_tac "P = AnnWhile r b P \<longrightarrow> Q" for Q)
  apply(rule ctran_in_comm, simp)
   apply (simp add: assume_p_def ann_pre_p_def gets_p_def getspc_p_def)
(*metiendo la hipotesis antes de dividir la conclusion.*)
  apply(subgoal_tac "(Some (AnnWhile r b P), snd (last ((Some P, sa) # xs))) # ys \<in> assume_p (r, rely)")
   apply (simp del:last.simps)
   prefer 2
   apply(erule assum_after_body)
      apply (simp del:last.simps)+
(*lo de antes.*)
apply(simp add:commit_p_def getspc_p_def gets_p_def del:list.map last.simps)
apply(rule conjI, clarify)
 apply (rule conjI)
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
     apply(thin_tac " \<forall>i. i < length ys \<longrightarrow> P i" for P)
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
    apply(erule_tac x="i-length xs" in allE,clarify)
    apply(case_tac "i=length xs")
     apply (simp add:nth_append snd_lift del:list.map last.simps)
     apply(simp add:last_length del:last.simps)
     apply(case_tac "last((Some P, sa) # xs)")
     apply(simp add:lift_def del:last.simps)
(*@{text "i>length xs"}*)
    apply(case_tac "i-length xs")
     apply arith
    apply(simp add:nth_append del:list.map last.simps)
    apply(rotate_tac -3)
    apply(subgoal_tac "i- Suc (length xs)=nat")
     prefer 2
     apply arith
    apply simp
   apply (subgoal_tac "ann_preserves_p ((map (lift (AnnWhile r b P)) ((Some P, sa) # xs) @ ys)!i)")
    apply (simp add: Cons_lift_append)
   apply (case_tac "i < length xs")
    apply (subgoal_tac "ann_preserves_p  (lift (AnnWhile r b P) (((Some P, sa) # xs)!i))")
     apply (metis length_Cons length_map less_SucI nth_append nth_map)
    apply (subgoal_tac "map (lift (AnnWhile r b P)) ((Some P, sa) # xs)  \<in> assume_p (r, rely)")
     apply (drule_tac P = "AnnWhile r b P" and l = "(Some P, sa) # xs" in lift_assume)
  using cpts_if_cpt_p_mod apply blast
     apply (case_tac "((Some P,sa) # xs)!i")
     apply (case_tac "fst (((Some P,sa) # xs)!i)")
      apply (drule_tac P = P and b = b and rely = rely and guar = guar and s = sa 
      in While_one_ann_preserves_None)
           apply (simp_all del: last.simps)
  using cpts_if_cpt_p_mod apply blast
        apply (simp add: assume_p_def gets_p_def)
       apply linarith
      apply (simp add: ann_preserves_p_def lift_def getspc_p_def gets_p_def)
     apply (simp add: prog_validity_def cpts_of_p_def)
     apply(erule_tac x=sa in allE)
     apply(drule_tac c="(Some P, sa) # xs" in subsetD)
      apply (simp add:assume_p_def gets_p_def cpts_if_cpt_p_mod)
     apply (subgoal_tac "ann_preserves_p (((Some P, sa) # xs)!i)")
      apply (simp add: ann_preserves_p_def lift_def gets_p_def getspc_p_def)
     apply (rule_tac guar = guar and post = r in commit_preserves, simp, simp)
     apply (rule_tac Q = "AnnWhile r b P" in lift_step)
      apply (metis (no_types) Cons_lift_append length_Cons length_map less_SucI nth_Cons_Suc nth_append nth_map)
     apply simp
    apply (simp add: assume_p_def gets_p_def getspc_p_def)
    apply (rule conjI, simp add: lift_def, clarify)
    apply (erule_tac x = "Suc ia" in allE)
    back
    apply simp
  apply (subgoal_tac "(snd (((Some (AnnSeq P (AnnWhile r b P)), sa) # map (lift (AnnWhile r b P)) xs 
  @ ys) ! ia), snd ((map (lift (AnnWhile r b P)) xs @ ys) ! ia)) \<in> rely")
     apply (metis (no_types, lifting) Cons_lift_append le_imp_less_Suc length_Cons length_map 
     less_or_eq_imp_le list.simps(9) nth_append nth_map)
    apply (erule mp)
    apply (metis (no_types, lifting) Cons_lift_append length_Cons length_map less_SucI list.simps(9) 
      nth_append nth_map)
   apply (subgoal_tac "ann_preserves_p (((Some (AnnWhile r b P), snd (last ((Some P, sa) # xs))) # ys) ! (i - length xs))")
    apply (subgoal_tac "ann_preserves_p ((last (map (lift (AnnWhile r b P)) xs) # ys) ! (i - length xs))")
     apply (metis append_take_i fst_conv last_length length_map list.size(3) not_less nth_Cons_0 option.distinct(1))
    apply (metis (no_types, lifting) One_nat_def fst_conv last_conv_nth last_length last_lift 
      last_snd list.size(3) map_is_Nil_conv nth_Cons' option.distinct(1) prod.expand snd_conv)
   apply (erule_tac x = "i - length xs" in allE)
   apply (subgoal_tac "((Some (AnnWhile r b P), snd (last ((Some P, sa) # xs))) # ys) ! 
  (i - length xs) -c\<rightarrow> ys ! (i - length xs)")
    apply linarith
   apply (rule_tac P = "((Some (AnnSeq P (AnnWhile r b P)), sa) # map (lift (AnnWhile r b P)) xs @ ys) ! i" 
      and Q = "(map (lift (AnnWhile r b P)) xs @ ys) ! i" in ctran_eq)
     apply (rule_tac s = "((last (map (lift (AnnWhile r b P)) xs)) # ys) ! (i - length xs)" in trans)
      apply (metis append_take_i eq_fst_iff last_ConsL length_map list.map_disc_iff not_less option.distinct(1))
     apply (metis (no_types, lifting) One_nat_def fstI last_ConsL last_conv_nth last_length last_lift 
      last_snd length_greater_0_conv map_is_Nil_conv nth_Cons_pos option.distinct(1) prod.collapse)
    apply (simp add: nth_append, simp)
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
    apply (simp del:list.map last.simps)
   apply simp
  apply simp
  done

lemma While_sound:
  "\<lbrakk> pre \<subseteq> r; stable r rely; r \<inter> - b \<subseteq> post; stable post rely;
    \<Turnstile> P sat\<^sub>p [r \<inter> b, rely, guar, r]; \<forall>s. (s,s)\<in>guar\<rbrakk>
  \<Longrightarrow> \<Turnstile> AnnWhile r b P sat\<^sub>p [pre, rely, guar, post]"
  apply (rule Conseq_sound_r, simp_all)
  apply(unfold prog_validity_def)
  apply clarify
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
  apply(clarify)
  apply(simp add:commit_p_def)
  apply(simp add:getspc_p_def gets_p_def)
  apply (rule conjI, clarify)
   apply (rule conjI)
  apply(simp add:cpts_of_p_def assume_p_def gets_p_def)
  apply clarify
  apply(frule_tac j=0 and k=i and p= r in stability)
      apply simp_all
    apply simp
  apply(erule_tac i=i and r=r in unique_ctran_Nondt,simp_all)
    apply(case_tac "x!i")
    apply clarify
    apply(drule_tac s="Some (AnnNondt r f)" in sym,simp)
    apply(thin_tac "\<forall>j. H j" for H)
    apply(force elim:ptran.cases)
  apply(simp add:cpts_of_p_def)
   apply clarify
   apply(simp add:cpts_of_p_def assume_p_def gets_p_def)
   apply clarify
   apply(frule_tac j=0 and k=i and p= r in stability)
  apply simp_all
     apply(erule_tac x=ia in allE,simp)
    apply(erule_tac i=i and f=f in unique_ctran_Nondt,simp_all)
   apply(case_tac "x!i")
   apply clarify
   apply(drule_tac s="Some (AnnNondt r f)" in sym,simp)
   apply (rule ann_preserves_p_cmd, simp add: ann_preserves_p_def)
  apply(simp add:cpts_of_p_def)
  apply clarify
apply(frule_tac i="length x - 1" and r=r and f = f in exists_ctran_Nondt_None,simp+)
    apply(case_tac x,simp+)
   apply(rule last_fst_esp,simp add:last_length)
   apply (case_tac x,simp+)
  apply(simp add:assume_p_def gets_p_def)
  apply clarify
  apply(frule_tac j=0 and k="j" and p= r in stability)
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
    then have a1: "\<forall>s. cpts_of_p (Some P) s \<inter> assume_p (pre, rely) \<subseteq> commit_p (guar, post)" 
      unfolding prog_validity_def cpts_of_p_def by simp
    then have "\<forall>s x. (cpts_of_ev (AnonyEvent (Some P)) s x) \<inter> assume_e (pre, rely) 
                      \<subseteq> commit_e (guar, post)"
      proof -
      {
        fix s x
        have "\<forall>el. el\<in>(cpts_of_ev (AnonyEvent (Some P)) s x) \<inter> assume_e (pre, rely) \<longrightarrow> el\<in> commit_e (guar, post)"
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

            with a1 b2 have b9: "pl \<in> commit_p (guar, post)" by auto
            then have b10: "(\<forall>i. Suc i<length el \<longrightarrow> 
               (\<exists>t. el!i -et-t\<rightarrow> el!(Suc i)) \<longrightarrow> (ann_preserves_e (el!i) \<and>
              (gets_e (el!i), gets_e (el!Suc i)) \<in> guar))"
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
                from c1 obtain t where d0: "el!i -et-t\<rightarrow> el!(Suc i)" by auto
                obtain s1 and x1 where d1: "s1 = gets_e (el ! i) \<and> x1 = getx_e (el ! i)" by simp
                obtain s2 and x2 where d2: "s2 = gets_e (el ! (Suc i)) \<and> x2 = getx_e (el ! (Suc i))" by simp
                    with d1 c71 c81 have d21: "el ! i = (AnonyEvent Q1, s1, x1) 
                                           \<and> el ! (Suc i) = (AnonyEvent Q2, s2, x2)" 
                      using gets_e_def getx_e_def getspc_e_def by (metis prod.collapse)
                    with d0 have d3: "(AnonyEvent Q1, s1, x1) -et-t\<rightarrow> (AnonyEvent Q2, s2, x2)" by simp
                    then have "\<exists>k. t = ((Cmd CMP)\<sharp>k)"
                      apply(rule etran.cases)
                       apply simp_all
                      by auto
                    then obtain k where "t = ((Cmd CMP)\<sharp>k)" by auto
                    with d3 have d4: "(Q1,s1) -c\<rightarrow> (Q2, s2)" 
                      apply(clarify)
                      apply(rule etran.cases)
                        apply simp_all+
                      done
                    from c3 d21 have d5: "pl!i = (Q1,s1)" by (simp add:lower_anonyevt1_def getspc_e_def gets_e_def)
                    from c4 d21 have d6: "pl! (Suc i) = (Q2,s2)" by (simp add:lower_anonyevt1_def getspc_e_def gets_e_def)
                    with d4 d5 have c5: "pl!i -c\<rightarrow> pl!(Suc i)" by simp 
                  with b9 c2 have c6: "(gets_p (pl!i), gets_p (pl!Suc i)) \<in> guar \<and>
                                        ann_preserves_p (pl!i)" by (simp add:commit_p_def)       
                  from c3 c71 have c9: "gets_e (el!i) = gets_p (pl!i)" using lower_anonyevt_s by fastforce
                  from c4 c81 have c10: "gets_e (el!Suc i) = gets_p (pl!Suc i)" using lower_anonyevt_s by fastforce 
                  from d5 d21 c6 c9 c10 have "ann_preserves_e (el!i) \<and> (gets_e (el!i), gets_e (el!Suc i)) \<in> guar"
                    by (simp add: ann_preserves_p_def ann_preserves_e_def  gets_p_def gets_e_def getspc_p_def getspc_e_def)
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
            
            with b10 have "el \<in> commit_e (guar, post)" by (simp add:commit_e_def)

          }
          then show ?thesis by auto
          qed

        then have "(cpts_of_ev (AnonyEvent (Some P)) s x) \<inter> assume_e (pre, rely) \<subseteq> commit_e (guar, post)" by auto
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
                      \<subseteq> commit_e (guar, post)"
      proof -
      {
        fix s x
        have "\<forall>el. el\<in>(cpts_of_ev (BasicEvent ev) s x) \<inter> assume_e (pre, rely) \<longrightarrow> el\<in> commit_e (guar, post)"
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
            have "el\<in> commit_e (guar, post)"
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

                with c6 c12 have c13: "drop (Suc m) el \<in> commit_e(guar, post)" 
                  by (meson AnonyEvt_sound IntI contra_subsetD evt_validity_def p0)
               

                have c14: "\<forall>i. Suc i < length el \<longrightarrow> (\<exists>t. el ! i -et-t\<rightarrow> el ! Suc i) 
                    \<longrightarrow> ann_preserves_e (el!i) \<and> (gets_e (el ! i), gets_e (el ! Suc i)) \<in> guar"
                  proof -
                  {
                    fix i 
                    assume d0: "Suc i < length el" and
                           d1: "(\<exists>t. el ! i -et-t\<rightarrow> el ! Suc i)"
                    then have "ann_preserves_e (el!i) \<and> (gets_e (el ! i), gets_e (el ! Suc i)) \<in> guar"
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
                            then have "is_basicevt (getspc_e (el!i)) \<and> gets_e (el ! i) = gets_e (el ! (Suc i))" 
                              by (simp add: c10 ent_spec f1)
                            with p1 show ?thesis by (simp add: ann_preserves_basic)
                          next
                            assume f0: "\<not> Suc i = m + 1"
                            with e1 have f1: "Suc i > Suc m" by auto
                            from c13 have f2: "\<forall>i. Suc i < length (drop (Suc m) el) \<longrightarrow> 
                                    (\<exists>t. (drop (Suc m) el) ! i -et-t\<rightarrow> (drop (Suc m) el) ! Suc i) \<longrightarrow> 
                                    ann_preserves_e ((drop (Suc m) el) ! i) \<and>
                                    (gets_e ((drop (Suc m) el) ! i), gets_e ((drop (Suc m) el) ! Suc i)) \<in> guar"
                                    by (simp add:commit_e_def)
                                  with d0 d1 f1 have "ann_preserves_e ((drop (Suc m) el) ! (i - Suc m)) \<and> 
                                  (gets_e (drop (Suc m) el ! (i - Suc m)), gets_e (drop (Suc m) el ! Suc (i - Suc m))) \<in> guar"
                              proof -
                                from d0 f1 have g0: "Suc (i - Suc m) < length (drop (Suc m) el)" by auto
                                from d1 f1 have "(\<exists>t. drop (Suc m) el ! (i - Suc m) -et-t\<rightarrow> drop (Suc m) el ! Suc (i - Suc m))"
                                  using d0 by auto
                                with g0 f2 show ?thesis by simp
                              qed
                              then show ?thesis using c1 f1 by auto
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

                from c14 c15 show ?thesis by (simp add:commit_e_def)
              next
                assume c0: "\<not> (\<exists>i k. Suc i < length el \<and> el ! i -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> el ! (Suc i) )"
                with b1 b2 have c1: "\<forall>j. Suc j < length el \<longrightarrow> getspc_e (el ! j) = BasicEvent ev 
                              \<and> el ! j -ee\<rightarrow> el ! (Suc j)
                              \<and> getspc_e (el ! (Suc j)) = BasicEvent ev"
                  using no_evtent_in_cpts by simp
                then have c2: "(\<forall>i. Suc i<length el \<longrightarrow> (\<exists>t. el!i -et-t\<rightarrow> el!(Suc i)) 
                          \<longrightarrow> (ann_preserves_e (el!i) \<and> (gets_e (el!i), gets_e (el!Suc i)) \<in> guar))"
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
                  
                with c2 show ?thesis by (simp add:commit_e_def)
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
    from p4 have p5: "\<forall>s x. (cpts_of_ev ev s x) \<inter> assume_e(pre', rely') \<subseteq> commit_e(guar', post')"
      by (simp add: evt_validity_def)
    have "\<forall>s x. (cpts_of_ev ev s x) \<inter> assume_e(pre, rely) \<subseteq> commit_e(guar, post)"
      proof -
      {
        fix c s x
        assume a0: "c\<in>(cpts_of_ev ev s x) \<inter> assume_e(pre, rely)"
        then have "c\<in>(cpts_of_ev ev s x) \<and> c\<in>assume_e(pre, rely)" by simp
        with p0 p1 have "c\<in>(cpts_of_ev ev s x) \<and> c\<in>assume_e(pre', rely')"
          using assume_e_imp[of pre pre' rely rely' c] by simp
        with p5 have "c\<in>commit_e(guar', post')" by auto
        with p2 p3 have "c\<in>commit_e(guar, post)" 
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



end
