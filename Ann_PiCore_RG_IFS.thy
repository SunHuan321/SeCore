theory Ann_PiCore_RG_IFS 
  imports Ann_PiCore_IFS Ann_PiCore_RG_Prop Ann_PiCore_Hoare
begin

(*declare [[show_types]]*)
locale RG_InfoFlow = InfoFlow C0 step interference vpeq obs dome
  for C0  ::  "('l,'k,'s) pesconf"
  and step :: "('l,'k,'s,'d) action \<Rightarrow> (('l,'k,'s) pesconf \<times> ('l,'k,'s) pesconf) set"
  and interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
  and vpeq ::  "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<sim>_\<sim> _)" [70,69,70] 60)
  and obs ::  "'s \<Rightarrow> 'd \<Rightarrow> 'o" (infixl "\<guillemotright>"  55)
  and dome :: "'s  \<Rightarrow> ('l,'k,'s) event \<Rightarrow> 'd"
  +
  fixes pesf :: "('l,'k,'s) rgformula_par"
  fixes s0 :: "'s"
  fixes x0 :: "('l,'k,'s) x"
  fixes evtrgfs :: "('l,'k,'s) event \<Rightarrow> 's rgformula option" (*a set of events and their rg conditions*)
  fixes spec_of_parsys :: "('l,'k,'s) paresys"
  assumes C0_ParSys: "C0 = (paresys_spec pesf, s0, x0)"
    and   spec_of_parsys: "spec_of_parsys = paresys_spec pesf"
    and   all_evts_are_basic: "\<forall>ef\<in>all_evts pesf. is_basicevt (E\<^sub>e ef)"
    and   parsys_sat_rg: "\<forall>k. \<turnstile> fst (pesf k) sat\<^sub>s [Pre\<^sub>e\<^sub>s (pesf k), Rely\<^sub>e\<^sub>s (pesf k), Guar\<^sub>e\<^sub>s (pesf k), Post\<^sub>e\<^sub>s (pesf k)]"
    and   parsys_sat_init: "\<forall>k. s0 \<in> Pre\<^sub>e\<^sub>s (pesf k)"
    and   parsys_rg_com: "\<forall>k j. j\<noteq>k \<longrightarrow>  Guar\<^sub>e\<^sub>s (pesf j) \<subseteq> Rely\<^sub>e\<^sub>s (pesf k)"
    and   evt_in_parsys_in_evtrgfs: "\<forall>erg\<in>all_evts pesf. the (evtrgfs (E\<^sub>e erg)) = snd erg" 
begin

lemma allD: "\<lbrakk> \<forall>a. P a\<rbrakk>\<Longrightarrow> P a"  
  by blast

lemma all2D: "\<lbrakk>\<forall>a b. P a b\<rbrakk> \<Longrightarrow> P a b"
  by blast

lemma all2_impD: "\<lbrakk> \<forall>a b . P a b  \<longrightarrow> Q a b  ; P a b  \<rbrakk>\<Longrightarrow> Q a b"  
  by blast

lemma all3_impD: "\<lbrakk> \<forall>a b c . P a b c  \<longrightarrow> Q a b c ; P a b c  \<rbrakk>\<Longrightarrow> Q a b c "  
  by blast

lemma all4_impD: "\<lbrakk> \<forall>a b c d. P a b c d \<longrightarrow> Q a b c d ; P a b c d \<rbrakk>\<Longrightarrow> Q a b c d"  
  by blast

lemma all5_impD: "\<lbrakk> \<forall>a b c d e. P a b c d e \<longrightarrow> Q a b c d e ; P a b c d e \<rbrakk>\<Longrightarrow> Q a b c d e"  
  by blast

lemma all7_impD: "\<lbrakk> \<forall>a b c d e f g. P a b c d e f g \<longrightarrow> Q a b c d e f g ; P a b c d e f g \<rbrakk>\<Longrightarrow> Q a b c d e f g"  
  by blast

lemma parsys_sat: "\<turnstile> pesf SAT [{s0}, {}, UNIV, UNIV]"
  by (rule ParallelESys, simp_all add: parsys_sat_rg  parsys_sat_init parsys_rg_com)

subsection \<open>local respect program\<close>
inductive lr_p :: "'s ann_prog \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool"
    ("\<turnstile>\<^sub>l\<^sub>r _ sat\<^sub>p _" [60] 45)
where
  Basic: "\<lbrakk>\<forall>s u. s \<in> r \<and> (dome s ev) \<setminus>\<leadsto> u \<longrightarrow> s  \<sim>u\<sim> f s\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r AnnBasic r f sat\<^sub>p ev"
| Seq: "\<lbrakk> \<turnstile>\<^sub>l\<^sub>r P sat\<^sub>p ev;  \<turnstile>\<^sub>l\<^sub>r Q sat\<^sub>p ev\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r AnnSeq P Q sat\<^sub>p ev"
| Cond: "\<lbrakk> \<turnstile>\<^sub>l\<^sub>r P1 sat\<^sub>p ev;  \<turnstile>\<^sub>l\<^sub>r P2 sat\<^sub>p ev \<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r AnnCond r b P1 P2 sat\<^sub>p ev"
| While: "\<lbrakk> \<turnstile>\<^sub>l\<^sub>r P sat\<^sub>p ev \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r AnnWhile r b P sat\<^sub>p ev"
| Await: "\<lbrakk> \<turnstile> AnnAwait r b P sat\<^sub>p [pre, rely, guar, post]; r \<subseteq> pre; \<forall>s u. s \<in> pre \<and> (dome s ev) \<setminus>\<leadsto> u 
           \<longrightarrow> (\<forall>t. (s, t) \<in> guar \<longrightarrow> s \<sim>u\<sim> t)\<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r AnnAwait r b P sat\<^sub>p ev"
| Nondt: "\<lbrakk>\<forall>s  u.  s \<in> r \<and> (dome s ev) \<setminus>\<leadsto> u \<longrightarrow> (\<forall>t. (s, t) \<in> f \<longrightarrow> s \<sim>u\<sim> t)\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r AnnNondt r f sat\<^sub>p ev"

definition locally_respect_p1 :: "'s ann_prog \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool"
  where "locally_respect_p1 P ev \<equiv> \<forall> s P' s'  u.  ann_preserves_p (Some P) s 
  \<and> (dome s ev) \<setminus>\<leadsto> u \<and> (Some P, s) -c\<rightarrow> (P', s') \<longrightarrow> s \<sim>u\<sim> s'"

definition locally_respect_p2 :: "'s ann_prog \<Rightarrow> 's ann_prog set \<Rightarrow> bool"
  where "locally_respect_p2 P \<S> \<equiv>  (\<forall> s P' s'. ann_preserves_p (Some P) s 
         \<and> (Some P, s) -c\<rightarrow> (Some P', s') \<longrightarrow> P' \<in> \<S>)"

definition locally_respect_p :: "'s ann_prog set \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool"
  where "locally_respect_p \<S> ev \<equiv> \<forall>P \<in> \<S>. locally_respect_p1 P ev \<and> locally_respect_p2 P \<S>"

lemma locally_respect_p_union: "\<lbrakk> locally_respect_p \<S> ev; locally_respect_p \<S>' ev \<rbrakk> \<Longrightarrow> locally_respect_p (\<S> \<union> \<S>') ev"
  apply (simp add: locally_respect_p_def, clarify)
  apply (case_tac "P \<in> \<S>", simp)
   apply (meson UnI1 locally_respect_p2_def)
  by (metis UnE UnI2 locally_respect_p2_def)

lemma locally_respect_p_insert: "\<lbrakk>locally_respect_p \<S> ev; locally_respect_p1 P ev; 
                                  locally_respect_p2 P (\<S> \<union> {P})\<rbrakk> \<Longrightarrow>  locally_respect_p (\<S> \<union> {P}) ev"
  apply (simp add: locally_respect_p_def)
  apply (case_tac "P \<in> \<S>")
   apply (simp add: insert_absorb)
  by (meson insertCI locally_respect_p2_def)

lemma lr_p_Basic_Sound: "\<forall>s  u. s \<in> r \<and> dome s  ev \<setminus>\<leadsto> u \<longrightarrow> s \<sim>u\<sim> f s \<Longrightarrow>
                          \<exists>\<S>. AnnBasic r f \<in> \<S> \<and> locally_respect_p \<S> ev"
  apply (rule_tac x = "{AnnBasic r f}" in exI, simp)
  apply (simp add: locally_respect_p_def)
  apply (rule conjI, simp add: locally_respect_p1_def, clarify)
   apply auto
  apply (simp add: locally_respect_p2_def)
  by fastforce

definition lift_prog_set :: "'s ann_prog \<Rightarrow> 's ann_prog set \<Rightarrow> 's ann_prog set"
  where "lift_prog_set Q \<S> \<equiv> {prog. \<exists>P \<in> \<S>. prog = AnnSeq P Q} \<union> {Q}"


lemma lift_prog_set_respect1 : "locally_respect_p1 P ev \<Longrightarrow> locally_respect_p1 (AnnSeq P Q) ev"
  apply (simp add: locally_respect_p1_def, clarify)
  by (erule_tac ptran.cases, simp_all)

lemma lr_p_Seq_Sound: "\<lbrakk>\<exists>\<S>. P \<in> \<S> \<and> locally_respect_p \<S> ev; \<exists>\<S>. Q \<in> \<S> \<and> locally_respect_p \<S> ev\<rbrakk>
                      \<Longrightarrow> \<exists>\<S>. AnnSeq P Q \<in> \<S> \<and> locally_respect_p \<S> ev"
  apply (erule exE, erule exE)
  apply (rule_tac x = "lift_prog_set Q \<S> \<union> \<S>'" in exI)
  apply (rule conjI, simp add: lift_prog_set_def)
  apply (simp add: locally_respect_p_def, clarify)
  apply (rule conjI)
   apply (case_tac "Pa \<in> \<S>'", simp)
   apply (simp add: lift_prog_set_def)
   apply (case_tac "Pa = Q", simp, clarsimp)
  using lift_prog_set_respect1 apply blast
  apply (case_tac "Pa \<in> \<S>'", simp add: locally_respect_p2_def)
  apply (simp add: lift_prog_set_def)
  apply (case_tac "Pa = Q")
   apply force
  apply (simp add: locally_respect_p2_def, clarify)
  apply (erule ptran.cases, simp_all)
  by blast

lemma lr_p_Cond_Sound: "\<lbrakk>\<exists>\<S>. P1 \<in> \<S> \<and> locally_respect_p \<S> ev; \<exists>\<S>. P2 \<in> \<S> \<and> locally_respect_p \<S> ev\<rbrakk>
                        \<Longrightarrow> \<exists>\<S>. AnnCond r b P1 P2 \<in> \<S> \<and> locally_respect_p \<S> ev"
  apply (clarsimp, rule_tac x = "\<S> \<union> \<S>' \<union> {AnnCond r b P1 P2}" in exI)
  apply (rule conjI, simp)
  apply (rule locally_respect_p_insert)
    apply (simp add: locally_respect_p_union)
  using locally_respect_p1_def vpeq_reflexive apply fastforce
  using UnI1 locally_respect_p2_def by fastforce

lemma lr_p_While_Sound: "\<lbrakk>\<exists>\<S>. P \<in> \<S> \<and> locally_respect_p \<S> ev \<rbrakk> 
                      \<Longrightarrow> \<exists>\<S>. AnnWhile r b P \<in> \<S> \<and> locally_respect_p \<S> ev"
  apply (erule exE)
  apply (rule_tac x = "lift_prog_set (AnnWhile r b P) \<S>" in exI)
  apply (rule conjI, simp add: lift_prog_set_def)
  apply (simp add: locally_respect_p_def, clarify)
  apply (rule conjI)
   apply (simp add: lift_prog_set_def)
   apply (case_tac "Pa = AnnWhile r b P")
    apply (drule_tac x = P in Set.bspec, simp, clarify)
  using locally_respect_p1_def vpeq_reflexive apply auto[1]
  using lift_prog_set_respect1 apply blast
  apply (simp add: lift_prog_set_def)
  apply (case_tac "Pa = AnnWhile r b P", simp add: locally_respect_p2_def)
   apply blast
  apply (clarify, drule_tac x = Paa in Set.bspec, simp, drule conjunct2)
  apply (simp add: locally_respect_p2_def, clarify)
  apply (erule ptran.cases, simp_all)
  by blast


lemma Await_guar: "\<lbrakk>\<turnstile> AnnAwait r b P sat\<^sub>p [pre, rely, guar, post]; (Some (AnnAwait r b P), s) -c\<rightarrow> (P', s'); s \<in> pre\<rbrakk> \<Longrightarrow> (s, s') \<in> guar"
  apply (drule rgsound_p, simp add: prog_validity_def)
  apply (drule_tac a = s in allD)
  apply (drule conjunct1)
  apply (drule_tac c = "[(Some (AnnAwait r b P), s), (P', s')]" in subsetD)
   apply (simp add: assume_p_def, rule conjI)
    apply (simp add: cpts_of_p_def cpts_p.CptsPComp cpts_p.CptsPOne)
   apply (rule conjI, simp add: gets_p_def)
  using petran.cases apply force
  apply (simp add: commit_p_def gets_p_def)
  done


lemma lr_p_Await_Sound: "\<lbrakk>\<turnstile> AnnAwait r b P sat\<^sub>p [pre, rely, guar, post]; r \<subseteq> pre; \<forall>s u. s \<in> pre \<and> 
                          dome s ev \<setminus>\<leadsto> u \<longrightarrow> (\<forall>t. (s, t) \<in> guar \<longrightarrow> s \<sim>u\<sim> t)\<rbrakk> \<Longrightarrow> 
                          \<exists>\<S>. AnnAwait r b P \<in> \<S> \<and> locally_respect_p \<S> ev"
  apply (rule_tac x = "{AnnAwait r b P}" in exI, simp add: locally_respect_p_def)
  apply (rule conjI, simp add: locally_respect_p1_def, clarify)
   apply (meson Await_guar subsetD)
  using locally_respect_p2_def by auto


lemma lr_p_Nondt_Sound: " \<forall>s u. s \<in> r \<and> dome s ev \<setminus>\<leadsto> u \<longrightarrow> (\<forall>t. (s, t) \<in> f \<longrightarrow> s \<sim>u\<sim> t) 
                          \<Longrightarrow> \<exists>\<S>. AnnNondt r f \<in> \<S> \<and> locally_respect_p \<S> ev"
  apply (rule_tac x = "{AnnNondt r f}" in exI, simp)
  apply (simp add: locally_respect_p_def)
  apply (rule conjI, simp add: locally_respect_p1_def, clarify)
   apply auto
  apply (simp add: locally_respect_p2_def)
  by fastforce

lemma lr_p_sound : " \<turnstile>\<^sub>l\<^sub>r P sat\<^sub>p ev \<Longrightarrow> \<exists>\<S>.  P \<in> \<S> \<and> locally_respect_p \<S> ev"
  apply (erule lr_p.induct)
  using lr_p_Basic_Sound apply force
  using lr_p_Seq_Sound apply auto[1]
     apply (simp add: lr_p_Cond_Sound)
    apply (simp add: lr_p_While_Sound)
   apply (simp add: lr_p_Await_Sound)
  by (simp add: lr_p_Nondt_Sound)

subsection \<open>local respect event\<close>

definition locally_respect_e1 :: "('l, 'k, 's) event \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool"
  where "locally_respect_e1 e ev \<equiv> \<forall> s x e' s' x' u t.  ann_preserves_e e s 
  \<and> (dome s ev) \<setminus>\<leadsto> u \<and> (e, s, x) -et-t\<rightarrow> (e', s', x') \<longrightarrow> s \<sim>u\<sim> s'"

definition locally_respect_e2 :: "('l, 'k, 's) event \<Rightarrow> ('l, 'k, 's) event set \<Rightarrow> bool"
  where "locally_respect_e2 e \<S> \<equiv> AnonyEvent None \<in> \<S> \<and> (\<forall>x s t e' s' x'. 
        ann_preserves_e e s \<and> (e, s, x) -et-t\<rightarrow> (e', s', x') \<longrightarrow> e' \<in> \<S>)"

definition locally_respect_e :: "('l, 'k, 's) event set \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool" where
  "locally_respect_e \<S> ev \<equiv> \<forall>e \<in> \<S>. locally_respect_e1 e ev \<and> locally_respect_e2 e \<S>"

lemma locally_respect_e_union: "\<lbrakk> locally_respect_e \<S> ev; locally_respect_e \<S>' ev \<rbrakk> \<Longrightarrow> 
                                 locally_respect_e (\<S> \<union> \<S>') ev"
  apply (simp add: locally_respect_e_def, clarify)
  apply (case_tac "e \<in> \<S>")
  using locally_respect_e2_def apply fastforce
  using locally_respect_e2_def by fastforce


lemma locally_respect_e_insert: "\<lbrakk>locally_respect_e \<S> ev; locally_respect_e1 e ev; 
                                 locally_respect_e2 e (\<S> \<union> {e})\<rbrakk>  \<Longrightarrow> locally_respect_e (\<S> \<union> {e}) ev"
  apply (simp add: locally_respect_e_def, clarify)
  using locally_respect_e2_def by fastforce

definition Prog_Trans_Anony :: "'s ann_prog set \<Rightarrow> ('l, 'k, 's) event set"
  where "Prog_Trans_Anony \<S> \<equiv> {ev. \<exists>P. P \<in> \<S> \<and> ev = AnonyEvent (Some P)} \<union> {AnonyEvent None}"


lemma Prog_Trans_Anony_Respect_aux1 : "  locally_respect_p1 P ev  \<Longrightarrow> 
                                          locally_respect_e1 (AnonyEvent (Some P)) ev"
  apply  (simp add: locally_respect_p1_def locally_respect_e1_def, clarify)
  apply (case_tac e', clarify)
    apply (drule_tac a = s and b = x1 and c = s' and d = u  in all4_impD)
     apply (simp add: etran.simps, simp)
  by (meson no_tran2basic)
  
lemma Prog_Trans_Anony_Respect_aux2 : "locally_respect_p2 P \<S> \<Longrightarrow> 
                                          locally_respect_e2 (AnonyEvent (Some P)) (Prog_Trans_Anony \<S>)"
  apply (simp add: locally_respect_p2_def locally_respect_e2_def)
  apply (rule conjI, simp add: Prog_Trans_Anony_def, clarify)
  apply (case_tac "e'", simp add: Prog_Trans_Anony_def)
   apply (case_tac x1, simp, simp)
   apply (erule etran.cases, simp_all)
  apply blast
  by (simp add: etran.simps)

lemma Prog_Trans_Anony_Respect: "\<lbrakk> P \<in> \<S>; locally_respect_p \<S> ev \<rbrakk> \<Longrightarrow> 
                         locally_respect_e (Prog_Trans_Anony \<S>) ev"
  apply (simp add: locally_respect_p_def)
  apply (simp add: locally_respect_e_def)
  apply (simp add: Prog_Trans_Anony_def)
  apply (rule conjI, simp add: locally_respect_e1_def, clarify)
   apply (erule etran.cases, clarify)
    apply (erule ptran.cases, simp_all)
  apply (rule conjI, simp add: locally_respect_e2_def locally_respect_p2_def, clarify)
   apply (erule etran.cases, clarify)
    apply (erule ptran.cases, simp_all, clarify)
  apply (rule conjI)
  using Prog_Trans_Anony_Respect_aux1 apply blast
  using Prog_Trans_Anony_Respect_aux2 Prog_Trans_Anony_def by auto


lemma lr_e_Anony: "\<lbrakk> \<turnstile>\<^sub>l\<^sub>r P sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. (AnonyEvent (Some P)) \<in> \<S> \<and> locally_respect_e \<S> ev"
  apply (drule lr_p_sound, erule exE)
  apply (rule_tac x = "(Prog_Trans_Anony \<S>)" in exI)
  apply (rule conjI, simp add: Prog_Trans_Anony_def)
  using Prog_Trans_Anony_Respect by blast


lemma lr_e_Basic: "\<lbrakk>ev = BasicEvent e;  \<turnstile>\<^sub>l\<^sub>r body e sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. ev \<in> \<S> \<and> locally_respect_e \<S> ev"
  apply (drule lr_e_Anony, erule exE)
  apply (rule_tac x = "\<S> \<union> {ev}" in exI)
  apply (rule conjI, simp)
  apply (rule locally_respect_e_insert, simp)
   apply (simp add: locally_respect_e1_def)
  apply (simp add: etran.simps vpeq_reflexive)
  apply (simp add: locally_respect_e2_def)
  apply (rule conjI, simp add: locally_respect_e_def locally_respect_e2_def)
   apply blast
  by (metis ent_spec2' noevtent_notran)

lemma lr_e_Basic1: "\<lbrakk>is_basicevt ev;  \<turnstile>\<^sub>l\<^sub>r the (body_e ev) sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. ev \<in> \<S> \<and> locally_respect_e \<S> ev"
proof-
  assume a0: " is_basicevt ev"
    and  a1: "\<turnstile>\<^sub>l\<^sub>r the (body_e ev) sat\<^sub>p ev"
  from a0 have "\<exists>e. ev = BasicEvent e" 
    by (metis event.exhaust is_basicevt.simps(1))
  then obtain e where b0: "ev = BasicEvent e" by auto
  with a1 have " \<turnstile>\<^sub>l\<^sub>r body e sat\<^sub>p ev" by simp
  with b0 show ?thesis
    by (rule_tac e = e in lr_e_Basic, simp_all)
qed


lemma locally_respect_event : "\<lbrakk>getspc_e c \<in> \<S> ; locally_respect_e \<S> ev; ann_preserves_e (getspc_e c) (gets_e c); 
                               \<exists>t. c -et-t\<rightarrow> c'\<rbrakk>  \<Longrightarrow> getspc_e c' \<in> \<S>"
  apply (case_tac "c", case_tac c', simp add: locally_respect_def getspc_e_def gets_e_def)
  by (meson locally_respect_e2_def locally_respect_e_def)

lemma locally_next_state : "\<lbrakk>e \<in> \<S> \<and> locally_respect_e \<S> ev; ann_preserves_e e s;
                             (dome s ev) \<setminus>\<leadsto> u; (e, s, x) -et-t\<rightarrow> (e', s', x')\<rbrakk> 
                              \<Longrightarrow> s \<sim>u\<sim> s'"
  apply (simp add: locally_respect_e_def, clarify)
  using locally_respect_e1_def by blast

lemma locally_respect_forall : "\<lbrakk>e \<in> \<S> ; locally_respect_e \<S> ev; el \<in> cpts_ev; getspc_e (el!0) = e; el \<in> preserves_e;
        i < length el\<rbrakk> \<Longrightarrow> getspc_e (el ! i) \<in> \<S>"
  apply (induct i, simp add: cpts_of_ev_def getspc_e_def)
  apply (case_tac "getspc_e (el ! i) = getspc_e (el ! Suc i)", simp)
  apply (simp add: preserves_e_def)
  by (meson Suc_lessD locally_respect_event notran_confeqi)


subsection \<open>step consistent program\<close>

inductive sc_p :: "'s ann_prog \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool"
    ("\<turnstile>\<^sub>s\<^sub>c _ sat\<^sub>p _" [60] 45)
where
  Basic: "\<lbrakk>\<forall>s1 s2 u. s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1 ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 ev)\<sim> s2)
           \<longrightarrow> f s1 \<sim>u\<sim> f s2\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnBasic r f sat\<^sub>p ev"
| Seq: "\<lbrakk> \<turnstile>\<^sub>s\<^sub>c P sat\<^sub>p ev;  \<turnstile>\<^sub>s\<^sub>c Q sat\<^sub>p ev\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnSeq P Q sat\<^sub>p ev"
| Cond: "\<lbrakk> \<turnstile>\<^sub>s\<^sub>c P1 sat\<^sub>p ev;  \<turnstile>\<^sub>s\<^sub>c P2 sat\<^sub>p ev \<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnCond r b P1 P2 sat\<^sub>p ev"
| While: "\<lbrakk> \<turnstile>\<^sub>s\<^sub>c P sat\<^sub>p ev \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnWhile r b P sat\<^sub>p ev"
| Await: "\<lbrakk> \<turnstile> AnnAwait r b P sat\<^sub>p [pre, rely, guar, post];  r \<subseteq> pre;
            \<forall>s1 s2  u. s1 \<in> pre \<and> s2 \<in> pre \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1  ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1  ev)\<sim> s2)
            \<longrightarrow> (\<forall>t1 t2. (s1, t1) \<in> guar \<and> (s2, t2) \<in> guar \<longrightarrow> t1 \<sim>u\<sim> t2)\<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnAwait r b P sat\<^sub>p ev"
| Nondt: "\<lbrakk>\<forall>s1 s2  u.  s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1  ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1  ev)\<sim> s2) \<longrightarrow>
           (\<forall>t1 t2. (s1, t1) \<in> f \<and> (s2, t2) \<in> f \<longrightarrow> t1 \<sim>u\<sim> t2) \<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c AnnNondt r f sat\<^sub>p ev"

definition step_consistent_p1 :: "'s ann_prog \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool" 
  where "step_consistent_p1 P ev \<equiv> \<forall> P1' P2' s1 s2 s1' s2'  u. 
         ann_preserves_p (Some P) s1 \<and> ann_preserves_p (Some P) s2 \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1 ev) \<leadsto> u 
          \<longrightarrow> s1 \<sim>(dome s1  ev)\<sim> s2) \<and> (Some P, s1) -c\<rightarrow> (P1', s1') \<and> (Some P, s2) -c\<rightarrow> (P2', s2') 
          \<longrightarrow> s1' \<sim>u\<sim> s2'"

lemma step_consistent_p1_eq : "\<forall> P1' P2' s1 s2 s1' s2'  u. 
         ann_preserves_p (Some P) s1 \<and> ann_preserves_p (Some P) s2 \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1  ev) \<leadsto> u 
          \<longrightarrow> s1 \<sim>(dome s1 ev)\<sim> s2) \<and> (Some P, s1) -c\<rightarrow> (P1', s1') \<and> (Some P, s2) -c\<rightarrow> (P2', s2') 
          \<longrightarrow> s1' \<sim>u\<sim> s2' \<Longrightarrow> step_consistent_p1 P ev"
  using step_consistent_p1_def by blast

definition step_consistent_p2 :: "'s ann_prog \<Rightarrow> 's ann_prog set \<Rightarrow> bool"
  where "step_consistent_p2 P \<S> \<equiv> \<forall>P1' s1 s1'.  ann_preserves_p (Some P) s1 \<and> (Some P, s1) -c\<rightarrow> (Some P1', s1') \<longrightarrow> P1' \<in> \<S>"


definition step_consistent_p :: "'s ann_prog set \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool"
  where "step_consistent_p \<S> ev \<equiv> \<forall>P \<in> \<S>. step_consistent_p1 P ev \<and> step_consistent_p2 P \<S>"


lemma step_consistent_p_union: "\<lbrakk> step_consistent_p \<S> ev; step_consistent_p \<S>' ev \<rbrakk> \<Longrightarrow> step_consistent_p (\<S> \<union> \<S>') ev"
  apply (simp add: step_consistent_p_def, clarify)
  apply (case_tac "P \<in> \<S>", simp)
   apply (meson UnI1 step_consistent_p2_def)
  by (metis UnE UnI2 step_consistent_p2_def)

lemma step_consistent_p_insert: "\<lbrakk>step_consistent_p \<S> ev; step_consistent_p1 P ev; 
                                  step_consistent_p2 P (\<S> \<union> {P})\<rbrakk> \<Longrightarrow>  step_consistent_p (\<S> \<union> {P}) ev"
  apply (simp add: step_consistent_p_def)
  apply (case_tac "P \<in> \<S>")
   apply (simp add: insert_absorb)
  by (meson insertCI step_consistent_p2_def)


lemma sc_p_Basic_Sound: " \<forall>s1 s2  u. s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> (dome s1 ev \<leadsto> u \<longrightarrow> s1 \<sim>dome s1 ev\<sim> s2) \<longrightarrow> 
        f s1 \<sim>u\<sim> f s2 \<Longrightarrow> \<exists>\<S>. AnnBasic r f \<in> \<S> \<and> step_consistent_p \<S> ev"
  apply (rule_tac x = "{AnnBasic r f}" in exI, simp)
  apply (simp add: step_consistent_p_def)
  apply (rule conjI, simp add: step_consistent_p1_def)
   apply auto
  apply (simp add: step_consistent_p2_def)
  by fastforce

lemma lift_prog_set_consistent1 : "step_consistent_p1 P ev \<Longrightarrow> step_consistent_p1 (AnnSeq P Q) ev"
  apply (rule step_consistent_p1_eq, clarify)
  apply (erule_tac ptran.cases, simp_all, clarify)
   apply (erule_tac ptran.cases, simp_all, clarify)
  unfolding step_consistent_p1_def
   apply (drule_tac a = "None" and b = "None" and c = "s1" and d = "s2" and e = "s1'" and f = "s2'"
           and g = "u" in all7_impD)
     apply (simp add: ann_preserves_p_def, simp)
   apply (drule_tac a = "None" and b = "Some P2" and c = "s1" and d = "s2" and e = "s1'" and f = "s2'"
          and g = "u"  in all7_impD, simp, simp)
  apply (erule ptran.cases)
          apply force apply fastforce
   apply (drule_tac all7_impD, simp, simp)
       by force+


lemma sc_p_Seq_Sound: "\<lbrakk> \<exists>\<S>. P \<in> \<S> \<and> step_consistent_p \<S> ev; \<exists>\<S>. Q \<in> \<S> \<and> step_consistent_p \<S> ev\<rbrakk>
                      \<Longrightarrow> \<exists>\<S>. AnnSeq P Q \<in> \<S> \<and> step_consistent_p \<S> ev"
  apply (erule exE, erule exE)
  apply (rule_tac x = "lift_prog_set Q \<S> \<union> \<S>'" in exI)
  apply (rule conjI, simp add: lift_prog_set_def)
  apply (simp add: step_consistent_p_def, clarify)
  apply (rule conjI)
   apply (case_tac "Pa \<in> \<S>'", simp)
   apply (simp add: lift_prog_set_def)
   apply (case_tac "Pa = Q", simp, clarsimp)
  using lift_prog_set_consistent1 apply blast
  apply (case_tac "Pa \<in> \<S>'", simp add: step_consistent_p2_def)
  apply (simp add: lift_prog_set_def)
  apply (case_tac "Pa = Q")
   apply force
  apply (simp add: step_consistent_p2_def, clarify)
  apply (erule ptran.cases, simp_all)
  by blast

lemma sc_p_Cond_Sound: "\<lbrakk>\<exists>\<S>. P1 \<in> \<S> \<and> step_consistent_p \<S> ev; \<exists>\<S>. P2 \<in> \<S> \<and> step_consistent_p \<S> ev\<rbrakk>
                \<Longrightarrow> \<exists>\<S>. AnnCond r b P1 P2 \<in> \<S> \<and> step_consistent_p \<S> ev"
  apply (clarsimp, rule_tac x = "\<S> \<union> \<S>' \<union> {AnnCond r b P1 P2}" in exI)
  apply (rule conjI, simp)
  apply (rule step_consistent_p_insert)
    apply (simp add: step_consistent_p_union)
  using step_consistent_p1_def apply auto[1]
  using step_consistent_p2_def by auto

lemma sc_p_While_Sound: "\<lbrakk> \<exists>\<S>. P \<in> \<S> \<and> step_consistent_p \<S> ev\<rbrakk>
                      \<Longrightarrow> \<exists>\<S>. AnnWhile r b P \<in> \<S> \<and> step_consistent_p \<S> ev"
  apply (erule exE)
  apply (rule_tac x = "lift_prog_set (AnnWhile r b P) \<S>" in exI)
  apply (rule conjI, simp add: lift_prog_set_def)
  apply (simp add: step_consistent_p_def, clarify)
  apply (rule conjI)
   apply (simp add: lift_prog_set_def)
   apply (case_tac "Pa = AnnWhile r b P")
    apply (drule_tac x = P in Set.bspec, simp, clarify)
    apply (rule step_consistent_p1_eq, simp add: ann_preserves_p_def, clarify)
    apply (erule ptran.cases, simp_all)
     apply (erule ptran.cases, simp_all, clarify)
    apply (erule ptran.cases, simp_all, clarify)
   apply (rule step_consistent_p1_eq, simp add: ann_preserves_p_def, clarify)
   apply (erule ptran.cases, simp_all)
    apply (erule ptran.cases, simp_all, clarify)
     apply (drule_tac x = P0a in Set.bspec, clarsimp)
     apply (drule conjunct1)
  unfolding step_consistent_p1_def
     apply (drule_tac a = None and b = None and c = s1 and d = s2 and e = s1' and f = s2' and 
            g = u  in all7_impD, simp, simp)
    apply (drule_tac x = P0a in Set.bspec, simp)
    apply (drule conjunct1)
    apply (drule_tac a = None and b = "Some P2" and c = s1 and d = s2 and e = s1' and f = s2' and 
            g = u  in all7_impD, simp, simp)
   apply (erule ptran.cases)
           apply force apply fastforce
         apply (smt (z3) ann_preserves_p.simps(2) ann_prog.inject(2) option.inject prod.inject)
        apply force apply force apply force apply force apply force apply force
  apply (simp add: lift_prog_set_def)
  apply (case_tac "Pa = AnnWhile r b P", simp add: step_consistent_p2_def)
   apply blast
  apply (clarify, drule_tac x = Paa in Set.bspec, simp, drule conjunct2)
  apply (simp add: step_consistent_p2_def, clarify)
  apply (erule ptran.cases, simp_all)
  by blast


lemma sc_p_Await_Sound: " \<lbrakk>\<turnstile> AnnAwait r b P sat\<^sub>p [pre, rely, guar, post] ; r \<subseteq> pre; 
                          \<forall>s1 s2  u. s1 \<in> pre \<and> s2 \<in> pre  \<and> s1 \<sim>u\<sim> s2 \<and> (dome s1  ev \<leadsto> u 
                          \<longrightarrow> s1 \<sim>dome s1  ev\<sim> s2) \<longrightarrow> (\<forall>t1 t2. (s1, t1) \<in> guar \<and> (s2, t2) \<in> guar 
                          \<longrightarrow> t1 \<sim>u\<sim> t2)\<rbrakk> \<Longrightarrow> \<exists>\<S>. AnnAwait r b P \<in> \<S> \<and> step_consistent_p \<S> ev"
  apply (rule_tac x = "{AnnAwait r b P}" in exI, simp add: step_consistent_p_def)
  apply (rule conjI)
   apply (rule step_consistent_p1_eq, clarify)
   apply (drule_tac a = s1 and b = s2 and c = u  in all3_impD, simp add: subset_eq)
   apply (erule all2_impD, simp add: ann_preserves_p_def)
   apply (simp add: Await_guar subset_eq)
  using step_consistent_p2_def by auto


lemma sc_p_Nondt_Sound: "\<forall>s1 s2  u. s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> (dome s1  ev \<leadsto> u \<longrightarrow> s1 \<sim>dome s1  ev\<sim> s2) 
                   \<longrightarrow> (\<forall>t1 t2. (s1, t1) \<in> f \<and> (s2, t2) \<in> f \<longrightarrow> t1 \<sim>u\<sim> t2) \<Longrightarrow> \<exists>\<S>. AnnNondt r f \<in> \<S> \<and> step_consistent_p \<S> ev"
  apply (rule_tac x = "{AnnNondt r f}" in exI, simp)
  apply (simp add: step_consistent_p_def)
  apply (rule conjI)
   apply (rule step_consistent_p1_eq, clarify)
  apply (subgoal_tac "s1 \<in> r \<and> s2 \<in> r")
    apply blast
  apply (metis ann_pre.simps(6) ann_preserves_p.simps(2))
  using step_consistent_p2_def apply auto[1]
  done

lemma sc_p_sound : " \<turnstile>\<^sub>s\<^sub>c P sat\<^sub>p ev \<Longrightarrow> \<exists>\<S>.  P \<in> \<S> \<and> step_consistent_p \<S> ev"
  apply (erule sc_p.induct)
  using sc_p_Basic_Sound apply auto[1]
  using sc_p_Seq_Sound apply auto[1]
  using sc_p_Cond_Sound apply auto[1]
  using sc_p_While_Sound apply auto[1]
   apply (smt (verit, del_insts) sc_p_Await_Sound)
  by (smt (verit, best) sc_p_Nondt_Sound)

subsection \<open>step consistent program\<close>

definition step_consistent_e1 :: "('l, 'k, 's) event \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool"
  where "step_consistent_e1 e ev \<equiv> \<forall>e1' e2' s1 s2 x1 x2 s1' s2' x1' x2' u t. 
  (ann_preserves_e e s1 \<and> ann_preserves_e e s2 \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1  ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1  ev)\<sim> s2) 
  \<and> (e, s1, x1) -et-t\<rightarrow> (e1', s1', x1') \<and> (e, s2, x2) -et-t\<rightarrow> (e2', s2', x2') \<longrightarrow>
   s1' \<sim>u\<sim> s2')"

lemma step_consistent_e1_eq : "\<forall>e1' e2' s1 s2 x1 x2 s1' s2' x1' x2' u t. 
  ann_preserves_e e s1 \<and> ann_preserves_e e s2 \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1  ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 ev)\<sim> s2) 
  \<and> (e, s1, x1) -et-t\<rightarrow> (e1', s1', x1') \<and> (e, s2, x2) -et-t\<rightarrow> (e2', s2', x2') \<longrightarrow>
   s1' \<sim>u\<sim> s2' \<Longrightarrow> step_consistent_e1 e ev"
  using step_consistent_e1_def by blast

definition step_consistent_e2 :: "('l, 'k, 's) event \<Rightarrow> ('l, 'k, 's) event set \<Rightarrow> bool"
  where "step_consistent_e2 e \<S> \<equiv>  AnonyEvent None \<in> \<S> \<and> (\<forall>x1 s1 t e1' s1' x1'. 
        ann_preserves_e e s1 \<and> (e, s1, x1) -et-t\<rightarrow> (e1', s1', x1') \<longrightarrow> e1' \<in> \<S>)"


definition step_consistent_e :: "('l, 'k, 's) event set \<Rightarrow> ('l, 'k, 's) event \<Rightarrow> bool" where
  "step_consistent_e \<S> ev \<equiv> \<forall>e \<in> \<S>. step_consistent_e1 e ev \<and> step_consistent_e2 e \<S>"


lemma step_consistent_e_union: "\<lbrakk> step_consistent_e \<S> ev; step_consistent_e \<S>' ev \<rbrakk> \<Longrightarrow> 
                                 step_consistent_e (\<S> \<union> \<S>') ev"
  apply (simp add: step_consistent_e_def, clarify)
  apply (case_tac "e \<in> \<S>")
  using step_consistent_e2_def apply fastforce
  using step_consistent_e2_def by fastforce


lemma step_consistent_e_insert: "\<lbrakk>step_consistent_e \<S> ev; step_consistent_e1 e ev; 
                                 step_consistent_e2 e (\<S> \<union> {e})\<rbrakk>  \<Longrightarrow> step_consistent_e (\<S> \<union> {e}) ev"
  apply (simp add: step_consistent_e_def, clarify)
  using step_consistent_e2_def by fastforce


lemma Prog_Trans_Anony_Consistent_aux1 : " step_consistent_p1 P ev  \<Longrightarrow> 
                                          step_consistent_e1 (AnonyEvent (Some P)) ev"
  apply  (simp add: step_consistent_p1_def)
  apply (rule step_consistent_e1_eq, clarify)
  apply (case_tac e1')
   apply (case_tac e2')
    apply (drule_tac a = x1a and b = x1b and c = s1 and d = s2 and e = s1' and f = s2' and g = u in all7_impD)
     apply (simp add: etran.simps, simp)
   apply (meson no_tran2basic)
  by (meson no_tran2basic)
  
lemma Prog_Trans_Anony_Consistent_aux2 : "step_consistent_p2 P \<S> \<Longrightarrow> 
                                          step_consistent_e2 (AnonyEvent (Some P)) (Prog_Trans_Anony \<S>)"
  apply (simp add: step_consistent_p2_def step_consistent_e2_def)
  apply (rule conjI, simp add: Prog_Trans_Anony_def, clarify)
  apply (case_tac "e1'", clarify)
   apply (case_tac "x1a", simp add: Prog_Trans_Anony_def)
   apply (drule_tac a = a in allD)
   apply (subgoal_tac "(Some P, s1) -c\<rightarrow> (Some a, s1')")
    apply (metis (mono_tags, lifting) CollectI Prog_Trans_Anony_def UnI1)
   apply (simp add: etran.simps)
  by (meson no_tran2basic)

lemma Prog_Trans_Anony_Consistent: "\<lbrakk> P \<in> \<S>; step_consistent_p \<S> ev \<rbrakk> \<Longrightarrow> 
                         step_consistent_e (Prog_Trans_Anony \<S>) ev"
  apply (simp add: step_consistent_p_def)
  apply (simp add: step_consistent_e_def)
  apply (simp add: Prog_Trans_Anony_def)
  apply (rule conjI, simp add: step_consistent_e1_def, clarify)
   apply (erule etran.cases, clarify)
    apply (erule ptran.cases, simp_all)
  apply (rule conjI, simp add: step_consistent_e2_def step_consistent_p2_def, clarify)
   apply (erule etran.cases, clarify)
    apply (erule ptran.cases, simp_all, clarify)
  apply (rule conjI)
  using Prog_Trans_Anony_Consistent_aux1 apply blast
  using Prog_Trans_Anony_Consistent_aux2 Prog_Trans_Anony_def by auto


lemma sc_e_Anony: "\<lbrakk> \<turnstile>\<^sub>s\<^sub>c P sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. (AnonyEvent (Some P)) \<in> \<S> \<and> step_consistent_e \<S> ev"
  apply (drule sc_p_sound, erule exE)
  apply (rule_tac x = "(Prog_Trans_Anony \<S>)" in exI)
  apply (rule conjI, simp add: Prog_Trans_Anony_def)
  using Prog_Trans_Anony_Consistent by blast


lemma sc_e_Basic: "\<lbrakk>ev = BasicEvent e;  \<turnstile>\<^sub>s\<^sub>c body e sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. ev \<in> \<S> \<and> step_consistent_e \<S> ev"
  apply (drule sc_e_Anony, erule exE)
  apply (rule_tac x = "\<S> \<union> {ev}" in exI)
  apply (rule conjI, simp)
  apply (rule step_consistent_e_insert, simp)
  apply (simp add: step_consistent_e1_def)
   apply (metis etran.simps event.distinct(1))
  apply (simp add: step_consistent_e2_def)
  apply (rule conjI, simp add: step_consistent_e_def step_consistent_e2_def)
   apply blast
  by (metis ent_spec2' noevtent_notran)

lemma sc_e_Basic1: "\<lbrakk>is_basicevt ev;  \<turnstile>\<^sub>s\<^sub>c the (body_e ev) sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. ev \<in> \<S> \<and> step_consistent_e \<S> ev"
proof-
  assume a0: "is_basicevt ev"
    and  a1: "\<turnstile>\<^sub>s\<^sub>c the (body_e ev) sat\<^sub>p ev"
  from a0 have "\<exists>e. ev = BasicEvent e" 
    by (metis anonyevt_isnot_basic event.exhaust is_anonyevt.simps(1))
  then obtain e where b0: "ev = BasicEvent e" by auto
  with a1 have "\<turnstile>\<^sub>s\<^sub>c body e sat\<^sub>p ev" by simp
  with b0 show ?thesis
    by (rule_tac e = e in sc_e_Basic, simp_all)
qed



lemma consistent_next_event : "\<lbrakk>getspc_e c \<in> \<S> ; step_consistent_e \<S> ev; ann_preserves_e (getspc_e c) (gets_e c); 
                               \<exists>t. c -et-t\<rightarrow> c'\<rbrakk>  \<Longrightarrow> getspc_e c' \<in> \<S>"
  apply (case_tac "c", case_tac c', simp add: step_consistent_e_def getspc_e_def gets_e_def)
  using step_consistent_e2_def by fastforce

lemma consistent_next_state : "\<lbrakk>e \<in> \<S> \<and> step_consistent_e \<S> ev; ann_preserves_e e s1; ann_preserves_e e s2;
                                s1 \<sim>u\<sim> s2; (dome s1  ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 ev)\<sim> s2; 
                                (e, s1, x1) -et-t\<rightarrow> (e1', s1', x1'); (e, s2, x2) -et-t\<rightarrow> (e2', s2', x2')\<rbrakk> 
                              \<Longrightarrow> s1' \<sim>u\<sim> s2'"
  apply (simp add: step_consistent_e_def, clarify)
  using step_consistent_e1_def by blast

lemma step_consistent_forall : "\<lbrakk>e \<in> \<S> ; step_consistent_e \<S> ev; el \<in> cpts_ev; getspc_e (el!0) = e; el \<in> preserves_e;
        i < length el\<rbrakk> \<Longrightarrow> getspc_e (el ! i) \<in> \<S>"
  apply (induct i, simp add: cpts_of_ev_def getspc_e_def)
  apply (case_tac "getspc_e (el ! i) = getspc_e (el ! Suc i)", simp)
  apply (rule_tac c = "el ! i" in consistent_next_event, simp_all)
   apply (simp add: preserves_e_def)
  using notran_confeqi by blast

subsection \<open>Proof Rules of Events For Unwinding Lemma \<close>

lemma cpt_is_run: 
  "\<forall>c C1 C2. c\<in>cpts_pes \<and> c!0 = C1 \<and> last c = C2 \<and> (\<forall>j. Suc j < length c \<longrightarrow> \<not>(c!j-pese\<rightarrow>c!Suc j)) 
            \<longrightarrow> (\<exists>as.  (C1,C2) \<in> run as \<and> Suc (length as) = length c \<and>
                       (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)) )"
  proof -
  {
    fix C2 c
    assume a0: "(c::('l,'k,'s) pesconfs)\<in>cpts_pes"
    then have "\<forall>C1. c!0 = C1 \<and> last c = C2 \<and> (\<forall>j. Suc j < length c \<longrightarrow> \<not>(c!j-pese\<rightarrow>c!Suc j)) 
            \<longrightarrow> (\<exists>as.  (C1,C2) \<in> run as \<and> Suc (length as) = length c \<and>
                       (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)) )"
      proof(induct c)
        case (CptsPesOne)
        show ?case by simp
      next
        case (CptsPesEnv)
        show ?case using nth_Cons_Suc pesetran.intros by force 
      next
        case (CptsPesComp pes1 s x ct pes2 t y xs)
        assume b0: "(pes1, s, x) -pes-ct\<rightarrow> (pes2, t, y)"
          and  b1: "(pes2, t, y) # xs \<in> cpts_pes"
          and  b2[rule_format]: "\<forall>C1. ((pes2, t, y) # xs) ! 0 = C1 \<and>
                       last ((pes2, t, y) # xs) = C2 \<and>
                       (\<forall>j. Suc j < length ((pes2, t, y) # xs) \<longrightarrow>
                            (((pes2, t, y) # xs) ! j, ((pes2, t, y) # xs) ! Suc j) \<notin> pesetran) \<longrightarrow>
                       (\<exists>as. (C1, C2) \<in> run as \<and>
                             Suc (length as) = length ((pes2, t, y) # xs) \<and>
                             (\<forall>j. Suc j < length ((pes2, t, y) # xs) \<longrightarrow>
                                  ((pes2, t, y) # xs) ! j -pes-actk (as ! j)\<rightarrow> ((pes2, t, y) # xs) ! Suc j))"
        then show ?case 
          proof -
          {
            fix C1
            assume c0: "((pes1, s, x) # (pes2, t, y) # xs) ! 0 = C1"
              and  c1: "last ((pes1, s, x) # (pes2, t, y) # xs) = C2"
              and  c2: "(\<forall>j. Suc j < length ((pes1, s, x) # (pes2, t, y) # xs) \<longrightarrow>
              (((pes1, s, x) # (pes2, t, y) # xs) ! j, ((pes1, s, x) # (pes2, t, y) # xs) ! Suc j) \<notin> pesetran)"
            then have c3: "C1 = (pes1, s, x)" by simp
            let ?C1 = "(pes2, t, y)"
            have "((pes2, t, y) # xs) ! 0 = ?C1" by simp
            moreover
            from c1 have "last ((pes2, t, y) # xs) = C2" by simp
            moreover
            from c2 have "\<forall>j. Suc j < length ((pes2, t, y) # xs) \<longrightarrow>
                            (((pes2, t, y) # xs) ! j, ((pes2, t, y) # xs) ! Suc j) \<notin> pesetran"
               using Suc_mono length_Cons nth_Cons_Suc by auto 
            ultimately have "\<exists>as. (?C1, C2) \<in> run as \<and>
                             Suc (length as) = length ((pes2, t, y) # xs) \<and>
                             (\<forall>j. Suc j < length ((pes2, t, y) # xs) \<longrightarrow>
                                  ((pes2, t, y) # xs) ! j -pes-actk (as ! j)\<rightarrow> ((pes2, t, y) # xs) ! Suc j)"
              using b2[of ?C1] by simp
            then obtain as where c4: "(?C1, C2) \<in> run as \<and>
                             Suc (length as) = length ((pes2, t, y) # xs) \<and>
                             (\<forall>j. Suc j < length ((pes2, t, y) # xs) \<longrightarrow>
                                  ((pes2, t, y) # xs) ! j -pes-actk (as ! j)\<rightarrow> ((pes2, t, y) # xs) ! Suc j)"
              by auto
            obtain tr and k where "ct = tr\<sharp>k" using get_actk_def
              by (metis actk.cases) 
            
            then have "\<exists>as. (C1, C2) \<in> run as \<and>
               Suc (length as) = length ((pes1, s, x) # (pes2, t, y) # xs) \<and>
               (\<forall>j. Suc j < length ((pes1, s, x) # (pes2, t, y) # xs) \<longrightarrow>
                    ((pes1, s, x) # (pes2, t, y) # xs) !
                    j -pes-actk (as ! j)\<rightarrow> ((pes1, s, x) # (pes2, t, y) # xs) ! Suc j)"
              proof(induct tr)
                case (Cmd cmd)
                assume d0: "ct = Cmd cmd\<sharp>k"
                obtain a1 where d1: "actk (a1::('l,'k,'s,'d) action) = ((Cmd cmd)\<sharp>k) \<and> eventof a1 = (getx C1) k 
                                          \<and> dome (gets C1) (eventof a1) = domain a1"
                  using action.select_convs(1) by fastforce 
                then obtain as1 where d2: "as1 = a1#as" by simp
                with d0 d1 b0 c3 c4 have "(C1, C2) \<in> run as1" using run_def step_def
                  using case_prod_conv mem_Collect_eq run_Cons by fastforce
                moreover
                from d2 c4 have "Suc (length as1) = length ((pes1, s, x) # (pes2, t, y) # xs)"
                  by auto
                moreover
                from c4 b0 d0 d1 d2 have "\<forall>j. Suc j < length ((pes1, s, x) # (pes2, t, y) # xs) \<longrightarrow>
                    ((pes1, s, x) # (pes2, t, y) # xs) !
                    j -pes-actk (as1 ! j)\<rightarrow> ((pes1, s, x) # (pes2, t, y) # xs) ! Suc j"
                  using c3 calculation(2) diff_Suc_1 length_Suc_conv less_Suc_eq_0_disj 
                    nat.discI not0_implies_Suc nth_Cons' by auto 
                ultimately show ?case by auto
              next
                case (EvtEnt ev)
                assume d0: "ct = EvtEnt ev\<sharp>k"
                obtain a1 where d1: "actk (a1::('l,'k,'s,'d) action) = ((EvtEnt ev)\<sharp>k) \<and> eventof a1 = ev 
                                          \<and> dome (gets C1) ev = domain a1"
                  using action.select_convs(1) by fastforce 
                then obtain as1 where d2: "as1 = a1#as" by simp
                with d0 d1 b0 c3 c4 have "(C1, C2) \<in> run as1" using run_def step_def
                  using case_prod_conv mem_Collect_eq run_Cons by fastforce
                moreover
                from d2 c4 have "Suc (length as1) = length ((pes1, s, x) # (pes2, t, y) # xs)"
                  by auto
                moreover
                from c4 b0 d0 d1 d2 have "\<forall>j. Suc j < length ((pes1, s, x) # (pes2, t, y) # xs) \<longrightarrow>
                    ((pes1, s, x) # (pes2, t, y) # xs) !
                    j -pes-actk (as1 ! j)\<rightarrow> ((pes1, s, x) # (pes2, t, y) # xs) ! Suc j"
                  using c3 calculation(2) diff_Suc_1 length_Suc_conv less_Suc_eq_0_disj 
                    nat.discI not0_implies_Suc nth_Cons' by auto 
                ultimately show ?case by auto
              qed
          }
          then show ?thesis by auto
          qed
      qed
  }
  then show ?thesis by auto
  qed

lemma run_is_cpt: "\<forall>C1 C2 as. (C1,C2) \<in> run as \<longrightarrow> 
            (\<exists>c. c\<in>cpts_pes \<and> c!0 = C1 \<and> last c = C2 \<and> Suc (length as) = length c \<and>
                 (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)) )" 
  proof -
  {
    fix C2 as 
    have "\<forall>C1. (C1,C2) \<in> run as \<longrightarrow> (\<exists>c. c\<in>cpts_pes \<and> c!0 = C1 \<and> last c = C2 \<and> Suc (length as) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)))"
      proof(induct as)
        case Nil
        show ?case
          proof -
          {
            fix C1
            assume a0: "(C1, C2) \<in> run []"
            then have b1: "C1 = C2" by (simp add:run_def)
            then have "[C1]\<in>cpts_pes" by (metis cpts_pes.CptsPesOne prod_cases3) 
            moreover
            have "[C1]!0 = C1" by simp
            moreover
            from b1 have "last [C1] = C2" by simp
            ultimately have "(\<exists>c. c \<in> cpts_pes \<and> c ! 0 = C1 \<and> last c = C2 \<and> Suc (length []) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk ([]!j))\<rightarrow>c!Suc j)))" by auto
          }
          then show ?thesis by blast
          qed
      next
        case (Cons b bs)
        assume a0: "\<forall>C1. (C1, C2) \<in> run bs \<longrightarrow> (\<exists>c. c \<in> cpts_pes \<and> c ! 0 = C1 \<and> last c = C2 \<and> Suc (length bs) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (bs!j))\<rightarrow>c!Suc j)))"
        then show ?case
          proof -
          {
            fix C1
            assume b0: "(C1, C2) \<in> run (b # bs)"
            then have "\<exists>R. (C1,R) \<in> step b \<and> (R,C2) \<in> run bs"
              by (simp add:run_def)
            then obtain R where b1: "(C1,R) \<in> step b \<and> (R,C2) \<in> run bs" by auto
            with a0 have "\<exists>c. c \<in> cpts_pes \<and> c ! 0 = R \<and> last c = C2 \<and> Suc (length bs) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (bs!j))\<rightarrow>c!Suc j))" by blast
            then obtain c where b2: "c \<in> cpts_pes \<and> c ! 0 = R \<and> last c = C2 \<and> Suc (length bs) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (bs!j))\<rightarrow>c!Suc j))" by auto
            then obtain c' where b3: "c=R#c'"
              by (metis cpts_pes_not_empty hd_conv_nth list.exhaust list.sel(1)) 
            from b1 have b4: "C1 -pes-(actk b)\<rightarrow> R" by (simp add:step_def)
            with b2 b3 have b5: "(C1#c) \<in> cpts_pes" 
              using pestran_cpts_pes by meson 
            from b2 have b6: "(C1#c)!0 = C1 \<and> last (C1#c) = C2 \<and> Suc (length (b#bs)) = length (C1#c)" by auto
            with b2 b4 have "\<forall>j. Suc j < length (C1#c) \<longrightarrow> ((C1#c)!j-pes-(actk ((b # bs)!j))\<rightarrow>(C1#c)!Suc j)"
              by (smt Suc_inject Suc_less_eq2 Suc_pred length_Cons neq0_conv nth_Cons' nth_Cons_Suc)
            with b5 b6 have "\<exists>c. c \<in> cpts_pes \<and> Suc (length (b # bs)) = length c \<and>
              c ! 0 = C1 \<and> last c = C2 \<and> (\<forall>j. Suc j < length c \<longrightarrow> c ! j -pes-actk ((b # bs) ! j)\<rightarrow> c ! Suc j)" 
              by auto
          }
          then show ?thesis by blast
          qed
      qed
  }
  then show ?thesis by auto
  qed

lemma run_cpt_preserves: "\<lbrakk>l \<in> cpts_of_pes (paresys_spec pesf) s0 x0; \<forall>i. Suc i < length l \<longrightarrow> (l ! i, l ! Suc i) \<notin> pesetran\<rbrakk> 
            \<Longrightarrow> l \<in> preserves_pes"
  apply (subgoal_tac "\<Turnstile> paresys_spec pesf SAT [{s0}, {}, UNIV, UNIV]")
   apply (simp add: pes_validity_def)
   apply (drule_tac a = s0 and b = x0 in all2D)
   apply (drule conjunct2)
   apply (drule_tac c = l in subsetD)
    apply (simp add: assume_pes_def gets_def cpts_of_pes_def, simp)
  apply (rule rgsound_pes)
  using parsys_sat by blast

lemma reachable_impl_cpts: "reachable C1 C2 \<Longrightarrow> \<exists>c. c\<in>cpts_pes \<and> c!0 = C1 \<and> last c = C2" 
  proof -
    assume "reachable C1 C2"
    then have "\<exists>as. (C1,C2) \<in> run as" by (simp add:reachable_def)
    then obtain as where a1: "(C1,C2) \<in> run as" by auto
    then show ?thesis using run_is_cpt by blast
  qed

lemma reachable0_impl_cpts: "reachable0 C \<Longrightarrow> \<exists>c. c\<in>cpts_pes \<and> c!0 = C0 \<and> last c = C"
  using reachable_impl_cpts reachable0_def by simp


definition locally_respect_events :: "bool" where
  "locally_respect_events \<equiv> \<forall>ef. ef\<in>all_evts pesf \<longrightarrow> ( (\<turnstile>\<^sub>l\<^sub>r the (body_e (E\<^sub>e ef)) sat\<^sub>p (E\<^sub>e ef)) \<or>
   (\<forall>u s1 s2. (s1, s2) \<in> Guar\<^sub>e ef \<longrightarrow> ((dome s1 (E\<^sub>e ef)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)))"

definition step_consistent_events :: "bool" where
  "step_consistent_events \<equiv> \<forall>ef. ef\<in>all_evts pesf  \<longrightarrow> \<turnstile>\<^sub>s\<^sub>c the (body_e (E\<^sub>e ef)) sat\<^sub>p (E\<^sub>e ef)"

lemma rg_lr_imp_lr: "locally_respect_events \<Longrightarrow> locally_respect"
proof-
  assume p0: "locally_respect_events"
  then have p1: "\<forall>ef. ef\<in>all_evts pesf  \<longrightarrow> ((\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> locally_respect_e \<S> (E\<^sub>e ef)) \<or> 
                 (\<forall>u s1 s2. (s1, s2) \<in> Guar\<^sub>e ef \<longrightarrow> ((dome s1 (E\<^sub>e ef)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2)))"
    using all_evts_are_basic locally_respect_events_def lr_e_Basic1 by blast
  show ?thesis
  proof-
    {
      fix a u C
      assume a0: "reachable0 C"
         and a1: "(domain (a::('l,'k,'s,'d) action)) \<setminus>\<leadsto> u"
      have "\<forall> C'. (C'\<in>nextc C a) \<longrightarrow> (C \<sim>.u.\<sim> C')"
      proof-
        {
          fix C'
          assume b0: "C'\<in>nextc C a"
          then have b1: "(C,C')\<in>step a" by (simp add:nextc_def)
          then have b2: "(C -pes-(actk a)\<rightarrow> C') \<and> ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                          \<and> dome (gets C) e = domain a) \<or> (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> 
                          eventof a = (getx C) k \<and> dome (gets C) (eventof a) = domain a))"
            by (simp add:step_def)
          obtain act_k and e and d where b3: "a = \<lparr>actk = act_k,eventof = e, domain=d\<rparr>"
            using action.cases by blast
          with b2 have b4: "(C -pes-act_k\<rightarrow> C') \<and> ((\<exists>e k. act_k = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                             \<and> dome (gets C) e = domain a) \<or> (\<exists>c k. act_k = ((Cmd c)\<sharp>k) \<and> 
                             eventof a = (getx C) k \<and> dome (gets C) (eventof a) = domain a))"
            by simp
          obtain act and k where b5: "act_k = act\<sharp>k"
            by (metis actk.cases get_actk_def)
          obtain pes1 and s1 and x1 where b6: "C = (pes1,s1,x1)" using prod_cases3 by blast 
          obtain pes2 and s2 and x2 where b7: "C' = (pes2,s2,x2)" using prod_cases3 by blast
          from b4 b5 b6 b7 have "\<exists>es'. ((pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es', s2, x2)) \<and> pes2 = pes1(k:=es')"
            using pestran_estran by force
          then obtain es' where b8: "((pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es', s2, x2)) \<and> pes2 = pes1(k:=es')" by auto
          from b5 have "C \<sim>.u.\<sim> C'"
          proof(induct act)
            case (Cmd x) 
            assume c0: "act_k = Cmd x\<sharp>k"
            from a0 have "\<exists>as. (C0,C) \<in> run as" by (simp add:reachable0_def reachable_def)
            then obtain as where "(C0,C) \<in> run as" by auto
            then have "(\<exists>c. c\<in>cpts_pes \<and> c!0 = C0 \<and> last c = C \<and> Suc (length as) = length c \<and>
                       (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)) )"
              using run_is_cpt by blast
            then obtain c where c1: "c\<in>cpts_pes \<and> c!0 = C0 \<and> last c = C \<and> Suc (length as) = length c \<and>
                        (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as!j))\<rightarrow>c!Suc j))" by auto
            with b1 have c2: "c@[C']\<in>cpts_pes" using cpts_pes_onemore step_def
              by (metis (no_types, lifting) b4 cpts_pes_not_empty last_conv_nth)
            with c1 have c3: "c @ [C'] \<in> cpts_of_pes (paresys_spec pesf) s0 x0" 
              using cpts_of_pes_def[of "paresys_spec pesf" s0 x0] C0_ParSys
              by (smt cpts_pes_not_empty length_greater_0_conv mem_Collect_eq nth_append)
            moreover
            from c1 have c4: "(c @ [C']) ! (length (c @ [C']) - 2) = C"
              by (metis Suc_1 diff_Suc_1 diff_Suc_Suc last_conv_nth length_0_conv length_append_singleton
                  lessI nat.simps(3) nth_append)
            moreover
            have c5: "(c @ [C']) ! (length (c @ [C']) - 1) = C'" by simp
            moreover
            from b1 c1 have c50: "\<forall>j. Suc j < length (c @ [C']) \<longrightarrow> ((c @ [C'])!j-pes-(actk ((as@[a])!j))
                    \<rightarrow>(c @ [C'])!Suc j)"
              by (smt Suc_1 Suc_lessI Suc_less_eq action.simps(1) b3 b4 c4 diff_Suc_1 diff_Suc_Suc
                  length_append_singleton nth_append nth_append_length) 
            ultimately have r1: "(gets C, gets C')\<in>Guar\<^sub>f (the (evtrgfs (getx C k)))" 
              using b1 b3 b4 c0 c1 act_cptpes_sat_guar_curevt_new2 [rule_format, of pesf "{s0}" UNIV s0 evtrgfs "c@[C']"]
                     step_def[of a] parsys_sat_rg all_evts_are_basic evt_in_parsys_in_evtrgfs parsys_sat
              by (smt One_nat_def Suc_1 append_is_Nil_conv butlast_snoc diff_Suc_1  diff_Suc_eq_diff_pred 
                 diff_Suc_less insertI1 length_butlast length_greater_0_conv not_Cons_self2)      
            from c3 c50 have c51: "\<forall>k i. Suc i < length (c @ [C']) \<longrightarrow> (\<exists>ca. (c @ [C']) ! i -pes-Cmd ca\<sharp>k\<rightarrow> 
                    (c @ [C']) ! Suc i) \<longrightarrow> (\<exists>ef\<in>all_evts pesf. getx ((c @ [C']) ! i) k = fst ef) " 
              using all_evts_are_basic cur_evt_in_specevts [of "c@[C']" pesf] by (metis E\<^sub>e_def) 
            moreover
            from b1 b3 c0 have c52: "C-pes-Cmd x\<sharp>k\<rightarrow>C'" using step_def by simp
            ultimately have "(\<exists>ef\<in>all_evts pesf. getx C k = fst ef)"
              using c1 c4 c5
            proof -
              have f1: "\<forall>k n. \<not> Suc n < length (c @ [C']) \<or>
                        (\<forall>ca. ((c @ [C']) ! n, Cmd ca\<sharp>k, (c @ [C']) ! Suc n) \<notin> pestran) \<or> 
                        (\<exists>p. p \<in> all_evts pesf \<and> fst p = getx ((c @ [C']) ! n) k)"
                by (metis c51)
              have f2: "\<forall>ps. c ! length as = (c @ ps) ! length as"
                by (metis (no_types) c1 lessI nth_append)
              have "c ! length as = C"
                by (metis (no_types) append_Nil c1 diff_Suc_1 id_take_nth_drop last_length 
                    length_Cons take_0 zero_less_Suc)
              then show ?thesis
                using f2 f1 by (metis c52 c1 c5 diff_Suc_1 length_append_singleton lessI)
            qed
            then obtain ef where c7: "ef\<in>all_evts pesf \<and> getx C k = fst ef" by auto
            from c0 have "\<not>(\<exists>e k. act_k = EvtEnt e\<sharp>k)"
              by (simp add: get_actk_def) 
            with b3 b4 c0 have c70: "\<exists>x k. act_k = Cmd x\<sharp>k \<and> eventof a = getx C k \<and> dome (gets C) (eventof a) = domain a"
              by simp
            with a1 b3 c0 have c8: "eventof a = getx C k \<and> dome (gets C) (eventof a) = domain a" 
              by (metis actk.iffs get_actk_def)

            with a1 b3 b6 c7 have c9 : "(dome s1  (E\<^sub>e ef)) \<setminus>\<leadsto> u" 
              using gets_def E\<^sub>e_def by (metis fst_conv snd_conv)

            from p1 c7 have c10: "(\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> locally_respect_e \<S> (E\<^sub>e ef)) \<or> 
            (\<forall>u s1 s2. (s1, s2) \<in> Guar\<^sub>e ef \<longrightarrow> ((dome s1 (E\<^sub>e ef)) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2))"
              by presburger
            then have " s1 \<sim>u\<sim> s2"
            proof
              assume d0: "\<exists>\<S>. E\<^sub>e ef \<in> \<S> \<and> locally_respect_e \<S> (E\<^sub>e ef)"
              let ?pes = "paresys_spec pesf"
              let ?i = "length (c @ [C']) - 2"
              have "\<exists>\<S>. AnonyEvent x \<in> \<S> \<and> locally_respect_e \<S> (E\<^sub>e ef)"
              proof-
                {
                  have "\<exists>el j.  getspc_e (el!0) = getx C k \<and> j < length el \<and>  el!j = rm_evtsys1 
                        ((getspc C k), gets C, getx C) \<and> el \<in> cpts_ev \<and> el \<in> preserves_e"
                    using act_cptpes_sat_e_sim[rule_format, of pesf "{s0}" UNIV s0 evtrgfs "c @ [C']"
                        x0 ?i k] parsys_sat_rg all_evts_are_basic evt_in_parsys_in_evtrgfs c1 c3 c4
                        c5 c50 c52 parsys_sat
                    by (smt One_nat_def Suc_1 Suc_diff_Suc Suc_less_eq diff_less insertI1
                        length_append_singleton zero_less_Suc)
                  then obtain el and j where e0: "getspc_e (el!0) = getx C k \<and> j < length el \<and> 
                     el!j = rm_evtsys1 ((getspc C k), gets C, getx C) \<and> el \<in> cpts_ev \<and> el \<in> preserves_e"
                    by auto
                with c7 have e1: "getspc_e (el!0) = E\<^sub>e ef \<and> j < length el \<and> 
                               el!j = rm_evtsys1 ((getspc C k), gets C, getx C) 
                               \<and> el \<in> cpts_ev \<and> el \<in> preserves_e"  by (simp add: E\<^sub>e_def)
                with c7 d0 have "\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> locally_respect_e \<S> (E\<^sub>e ef)" by blast
                then obtain \<S> where e2: "(E\<^sub>e ef) \<in> \<S> \<and> locally_respect_e \<S> (E\<^sub>e ef)" by auto

                from b5 b8 b4 c0 have "\<exists>es. getspc C k = EvtSeq (AnonyEvent x) es"
                  by (metis  pes_cmd_tran_anonyevt pesconf_trip)
                then obtain es where "getspc C k = EvtSeq (AnonyEvent x) es" by auto
                with e0 b8 have e3: "el!j = (AnonyEvent x, s1, x1)" 
                  using rm_evtsys1_def 
                  by (metis EvtSeqrm Pair_inject b6 esconf_trip pesconf_trip)
                with e0 e1 e2 e3 have "AnonyEvent x \<in> \<S>"
                  using locally_respect_forall[of "E\<^sub>e ef" \<S> "E\<^sub>e ef" el j]
                  by (metis getspc_e_def fstI)
                with e2 show ?thesis by auto
              }
            qed

            then obtain \<S> where d1: "AnonyEvent x \<in> \<S> \<and> locally_respect_e \<S> (E\<^sub>e ef)" by auto

            have d2: "ann_preserves_e (AnonyEvent x) s1"
            proof- 
              {
                from c3 c50 have "c @ [C'] \<in> preserves_pes"
                  using run_cpt_preserves pes_tran_not_etran1 by blast
                with c4 b6 have "ann_preserves_pes pes1 s1"
                  apply (simp add: preserves_pes_def)
                  apply (erule_tac x = "?i" in allE)
                  by (simp add: getspc_def gets_def)
                then have f0 : "ann_preserves_es (pes1 k) s1"
                  by (simp add: ann_preserves_pes_def)
                from b5 b8 c52 c0 have "\<exists>es. pes1 k = EvtSeq (AnonyEvent x) es"
                  by (metis  evtseq_cmd_tran_anonyevt)
                then obtain es where "pes1 k = EvtSeq (AnonyEvent x) es" by auto
                with f0 have "ann_preserves_e (AnonyEvent x) s1"
                  by (simp add: ann_preserves_es_def)
              }
              then show ?thesis by auto
            qed

            with b6 b7 c52 c9 d1 show ?thesis 
              by (metis locally_next_state pes_cmd_tran_anonyevt1)
          next
            assume f0: "\<forall>u s1 s2. (s1, s2) \<in> Guar\<^sub>e ef \<longrightarrow> dome s1 (E\<^sub>e ef) \<setminus>\<leadsto> u \<longrightarrow> s1 \<sim>u\<sim> s2"
            from p1 b6 b7 c7 c8 r1 have "(gets C, gets C')\<in>Guar\<^sub>e ef"
              using evt_in_parsys_in_evtrgfs Guar\<^sub>f_def E\<^sub>e_def Guar\<^sub>e_def by metis
            with f0 show ?thesis using p1 b6 b7 c7 c8 a1 vpeqc_def E\<^sub>e_def
              by (metis fst_conv gets_def snd_conv)
          qed

          then show ?case
            by (simp add: b6 b7 gets_def vpeqc_def)
        next
          case (EvtEnt x)
          from b5 b8 have "s1 = s2" 
            using entevt_notchgstate by (metis EvtEnt.prems evtent_is_basicevt)
          with b6 b7 show ?case by (simp add: gets_def vpeqc_def vpeq_reflexive)
        qed
      }
      then show ?thesis by auto
    qed
  }
  then show ?thesis using locally_respect_def by simp
qed
qed


lemma rg_sc_imp_sc: "step_consistent_events \<Longrightarrow> step_consistent"
proof-
  assume p0: "step_consistent_events"
  then have p1: "\<forall>ef. ef\<in>all_evts pesf  \<longrightarrow> (\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> step_consistent_e \<S> (E\<^sub>e ef))"
    by (simp add: all_evts_are_basic sc_e_Basic1 step_consistent_events_def)
  show ?thesis
  proof-
    {
      fix a u C1 C2
      assume a0: "(reachable0 C1) \<and> (reachable0 C2)"
      and    a1: "(C1 \<sim>.u.\<sim> C2) \<and> (((domain (a::('l,'k,'s,'d) action)) \<leadsto> u) \<longrightarrow> (C1 \<sim>.(domain a).\<sim> C2))"
      have "\<forall>C1' C2'. (C1'\<in>nextc C1 a) \<and> (C2'\<in>nextc C2 a) \<longrightarrow> (C1' \<sim>.u.\<sim> C2')"
      proof-
        {
          fix C1' C2'
          assume b0: "(C1'\<in>nextc C1 a) \<and> (C2'\<in>nextc C2 a)"
          obtain act_k and e and d where b3: "a = \<lparr>actk = act_k,eventof = e, domain=d\<rparr>"
            using action.cases by blast 
          obtain act and k where b5: "act_k = act\<sharp>k"
            by (metis actk.cases get_actk_def)

          from b0 have b1: "(C1, C1') \<in> step a" by (simp add: nextc_def)
          then have b2: "(C1 -pes-(actk a)\<rightarrow> C1') \<and>
                         ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C1) e = domain a) \<or>
                         (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C1) k \<and> dome (gets C1) (eventof a) = domain a))"
            by (simp add: step_def)
          with b3 have b4: "(C1 -pes-act_k\<rightarrow> C1') \<and> 
                            ((\<exists>e k. act_k = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C1) e = domain a) \<or>
                            (\<exists>c k. act_k = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C1) k \<and> dome (gets C1) (eventof a) = domain a))"
            by simp

          from b0 have b6: "(C2,C2')\<in>step a" by (simp add:nextc_def)
          then have "(C2 -pes-(actk a)\<rightarrow> C2') \<and>
                     ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C2) e = domain a) \<or>
                     (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C2) k \<and> dome (gets C2) (eventof a) = domain a))"
            by (simp add:step_def)
          with b3 have b7: "(C2 -pes-act_k\<rightarrow> C2') \<and> 
                            ((\<exists>e k. act_k = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C2) e = domain a) \<or>
                            (\<exists>c k. act_k = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C2) k \<and> dome (gets C2) (eventof a) = domain a))"
            by simp
          obtain pes1 and s1 and x1 where b8: "C1 = (pes1,s1,x1)" using prod_cases3 by blast 
          obtain pes1' and s1' and x1' where b9: "C1' = (pes1',s1',x1')" using prod_cases3 by blast
          obtain pes2 and s2 and x2 where b10: "C2 = (pes2,s2,x2)" using prod_cases3 by blast
          obtain pes2' and s2' and x2' where b11: "C2' = (pes2',s2',x2')" using prod_cases3 by blast
          from b4 b5 b8 b9 have "\<exists>es'. ((pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es', s1', x1')) \<and> pes1' = pes1(k:=es')" 
            using pestran_estran [of pes1 s1 x1 act k pes1' s1' x1'] by simp
          then obtain es1' where b12: "((pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es1', s1', x1')) \<and> pes1' = pes1(k:=es1')" by auto
          from b5 b7 b10 b11 have "\<exists>es'. ((pes2 k, s2, x2) -es-(act\<sharp>k)\<rightarrow> (es', s2', x2')) \<and> pes2' = pes2(k:=es')" 
            using pestran_estran [of pes2 s2 x2 act k pes2' s2' x2'] by simp
          then obtain es2' where b13: "((pes2 k, s2, x2) -es-(act\<sharp>k)\<rightarrow> (es2', s2', x2')) \<and> pes2' = pes2(k:=es2')"
            by auto

          from b5 have "C1' \<sim>.u.\<sim> C2'"
          proof(induct act)
            case (Cmd c)
            assume c0: "act_k = Cmd c\<sharp>k"

            from a0 have "\<exists>as. (C0, C1) \<in> run as" by (simp add: reachable0_def reachable_def)
            then obtain as1 where "(C0, C1) \<in> run as1" by auto
            then have "(\<exists>c. c\<in>cpts_pes \<and> c!0 = C0 \<and> last c = C1 \<and> Suc (length as1) = length c \<and>
                              (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as1!j))\<rightarrow>c!Suc j)) )"
              using run_is_cpt by blast
            then obtain c1 where c1: "c1\<in>cpts_pes \<and> c1!0 = C0 \<and> last c1 = C1 \<and> Suc (length as1) = length c1 \<and>
                (\<forall>j. Suc j < length c1 \<longrightarrow> (c1!j-pes-(actk (as1!j))\<rightarrow>c1!Suc j))" by auto
            with b1 have c2: "c1@[C1']\<in>cpts_pes" using cpts_pes_onemore step_def
              by (metis (no_types, lifting) b4 cpts_pes_not_empty last_conv_nth)
            with c1 have c3: "c1 @ [C1'] \<in> cpts_of_pes (paresys_spec pesf) s0 x0" 
              using cpts_of_pes_def[of "paresys_spec pesf" s0 x0] C0_ParSys
              by (smt cpts_pes_not_empty length_greater_0_conv mem_Collect_eq nth_append)
            moreover
            from c1 have c4: "(c1 @ [C1']) ! (length (c1 @ [C1']) - 2) = C1"
              by (metis Suc_1 diff_Suc_1 diff_Suc_Suc last_conv_nth length_0_conv length_append_singleton 
                  lessI nat.distinct(1) nth_append)
              
            moreover
            have c5: "(c1 @ [C1']) ! (length (c1 @ [C1']) - 1) = C1'" by simp
            moreover
            from b1 c1 have c50: "\<forall>j. Suc j < length (c1 @ [C1']) \<longrightarrow> 
             ((c1 @ [C1'])!j-pes-(actk ((as1@[a])!j))\<rightarrow>(c1 @ [C1'])!Suc j)"
              by (smt Suc_1 Suc_lessI Suc_less_eq action.simps(1) b3 b4 c4 diff_Suc_1 
                  diff_Suc_Suc length_append_singleton nth_append nth_append_length) 

            from a0 have "\<exists>as. (C0,C2) \<in> run as" by (simp add:reachable0_def reachable_def)
            then obtain as2 where "(C0,C2) \<in> run as2" by auto
            then have "(\<exists>c. c\<in>cpts_pes \<and> c!0 = C0 \<and> last c = C2 \<and> Suc (length as2) = length c \<and>
                        (\<forall>j. Suc j < length c \<longrightarrow> (c!j-pes-(actk (as2!j))\<rightarrow>c!Suc j)) )"
              using run_is_cpt by blast
            then obtain c2 where c7: "c2\<in>cpts_pes \<and> c2!0 = C0 \<and> last c2 = C2 \<and> Suc (length as2) = length c2 \<and>
                     (\<forall>j. Suc j < length c2 \<longrightarrow> (c2!j-pes-(actk (as2!j))\<rightarrow>c2!Suc j))" by auto
            with b6 have c8: "c2@[C2']\<in>cpts_pes" using cpts_pes_onemore step_def
              by (metis (no_types, lifting) b7 cpts_pes_not_empty last_conv_nth)
            with c7 have c9: "c2 @ [C2'] \<in> cpts_of_pes (paresys_spec pesf) s0 x0" 
              using cpts_of_pes_def[of "paresys_spec pesf" s0 x0] C0_ParSys
              by (smt cpts_pes_not_empty length_greater_0_conv mem_Collect_eq nth_append) 
            moreover
            from c7 have c10: "(c2 @ [C2']) ! (length (c2 @ [C2']) - 2) = C2"
              by (metis Suc_1 diff_Suc_1 diff_Suc_Suc last_conv_nth length_0_conv length_append_singleton 
                  lessI nat.distinct(1) nth_append)
            moreover
            have c11: "(c2 @ [C2']) ! (length (c2 @ [C2']) - 1) = C2'" by simp
            moreover
            from b1 c7 have c60: "\<forall>j. Suc j < length (c2 @ [C2']) \<longrightarrow> 
              ((c2 @ [C2'])!j-pes-(actk ((as2@[a])!j))\<rightarrow>(c2 @ [C2'])!Suc j)"
              by (smt Suc_1 Suc_lessI Suc_less_eq action.simps(1) b3 b7 c10 diff_Suc_1 
                 diff_Suc_Suc length_append_singleton nth_append nth_append_length) 


            from c3 c50 have c51: "\<forall>k i. Suc i < length (c1 @ [C1']) \<longrightarrow>
                      (\<exists>ca. (c1 @ [C1']) ! i -pes-Cmd ca\<sharp>k\<rightarrow> (c1 @ [C1']) ! Suc i) \<longrightarrow>
                      (\<exists>ef\<in>all_evts pesf. getx ((c1 @ [C1']) ! i) k = fst ef) " 
              using all_evts_are_basic cur_evt_in_specevts [of "c1@[C1']" pesf] by (metis E\<^sub>e_def)
            moreover
            from b1 b3 c0 have c52: "C1-pes-Cmd c\<sharp>k\<rightarrow>C1'" using step_def by simp
            from c9 c60 have c61: "\<forall>k i. Suc i < length (c2 @ [C2']) \<longrightarrow>
                      (\<exists>ca. (c2 @ [C2']) ! i -pes-Cmd ca\<sharp>k\<rightarrow> (c2 @ [C2']) ! Suc i) \<longrightarrow>
                      (\<exists>ef\<in>all_evts pesf. getx ((c2 @ [C2']) ! i) k = fst ef) " 
              using all_evts_are_basic cur_evt_in_specevts [of "c2@[C2']" pesf] by (metis E\<^sub>e_def)
            moreover
            from b6 b3 c0 have c62: "C2-pes-Cmd c\<sharp>k\<rightarrow>C2'" using step_def by simp

            ultimately have "(\<exists>ef\<in>all_evts pesf. getx C1 k = fst ef)"
              using c1 c4 c5
            proof-
              have f1: "\<forall>k n. \<not> Suc n < length (c1 @ [C1']) \<or>
                        (\<forall>ca. ((c1 @ [C1']) ! n, Cmd ca\<sharp>k, (c1 @ [C1']) ! Suc n) \<notin> pestran) \<or> 
                        (\<exists>p. p \<in> all_evts pesf \<and> fst p = getx ((c1 @ [C1']) ! n) k)"
                by (metis c51)
              from c1 have f2: "\<forall>ps. c1 ! length as1 = (c1 @ ps) ! length as1" 
                by (metis (no_types) c1 lessI nth_append)
              have "c1 ! length as1 = C1"
                by (metis (no_types) append_Nil c1 diff_Suc_1 id_take_nth_drop last_length 
                    length_Cons take_0 zero_less_Suc)
              then show ?thesis
                using f2 f1 by (metis c52 c1 c5 diff_Suc_1 length_append_singleton lessI)
            qed

            then obtain ef where c12: "ef\<in>all_evts pesf \<and> getx C1 k = E\<^sub>e ef" 
              by (metis E\<^sub>e_def)
            from c0 have c12_1: "\<not>(\<exists>e k. act_k = EvtEnt e\<sharp>k)"
              by (simp add: get_actk_def) 
            with b3 b4 c0 have c13: "\<exists>x k. act_k = Cmd c\<sharp>k \<and> eventof a = getx C1 k \<and> dome (gets C1) (eventof a) = domain a"
              by (metis actk.iffs get_actk_def)
            with a1 b3 c0 have c14: "eventof a = getx C1 k \<and> dome (gets C1) (eventof a) = domain a"
              by (metis actk.ext_inject get_actk_def)

            let ?pes = "paresys_spec pesf"
            let ?i = "length (c1 @ [C1']) - 2"
            have "\<exists>\<S>. AnonyEvent c \<in> \<S> \<and> step_consistent_e \<S> (E\<^sub>e ef)"
            proof-
              {
                have "\<exists>el j.  getspc_e (el!0) = getx C1 k \<and> j < length el \<and> 
                     el!j = rm_evtsys1 ((getspc C1 k), gets C1, getx C1) \<and> el \<in> cpts_ev \<and> el \<in> preserves_e"
                  using act_cptpes_sat_e_sim[rule_format, of pesf "{s0}" UNIV s0 evtrgfs "c1 @ [C1']"
                        x0 ?i k] parsys_sat_rg all_evts_are_basic evt_in_parsys_in_evtrgfs c1 c3 c4
                       c5 c50 c52 parsys_sat
                  by (smt One_nat_def Suc_1 Suc_diff_Suc Suc_less_eq diff_less insertI1  length_append_singleton 
                      zero_less_Suc)
                then obtain el and j where e0: "getspc_e (el!0) = getx C1 k \<and> j < length el \<and> 
                     el!j = rm_evtsys1 ((getspc C1 k), gets C1, getx C1) \<and> el \<in> cpts_ev \<and> el \<in> preserves_e"
                  by auto
                with c12 have c120: "getspc_e (el!0) = E\<^sub>e ef \<and> j < length el \<and> el!j = rm_evtsys1 ((getspc C1 k), gets C1, getx C1) 
                               \<and> el \<in> cpts_ev \<and> el \<in> preserves_e" by simp
                with c12 p1 have "\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> step_consistent_e \<S> (E\<^sub>e ef)" by blast
                then obtain \<S> where e1: "(E\<^sub>e ef) \<in> \<S> \<and> step_consistent_e \<S> (E\<^sub>e ef)" by auto

                from b5 b8 b12 c0 have "\<exists>es. getspc C1 k = EvtSeq (AnonyEvent c) es"
                  by (metis evtseq_cmd_tran_anonyevt fst_conv getspc_def)
                then obtain es where "getspc C1 k = EvtSeq (AnonyEvent c) es" by auto
                with e0 b8 have e2: "el!j = (AnonyEvent c, s1, x1)" 
                  using rm_evtsys1_def 
                  by (metis EvtSeqrm esconf_trip fst_conv gets_def getx_def snd_conv)
                with e0 e1 e2 c120 have "AnonyEvent c \<in> \<S>"
                  using step_consistent_forall[of "E\<^sub>e ef" \<S> "E\<^sub>e ef" el j]
                  by (metis getspc_e_def fstI)
                with e1 show ?thesis by auto
              }
            qed
      
        then obtain \<S> where d0: "AnonyEvent c \<in> \<S> \<and> step_consistent_e \<S> (E\<^sub>e ef)" by auto

        have d1: "ann_preserves_e (AnonyEvent c) s1"
        proof-     
          {
            from c3 c50 have "c1 @ [C1'] \<in> preserves_pes" 
              using run_cpt_preserves pes_tran_not_etran1 by blast
            with c4 b8 have "ann_preserves_pes pes1 s1"
              apply (simp add: preserves_pes_def)
              apply (erule_tac x = "?i" in allE)
              by (simp add: getspc_def gets_def)
            then have f0 : "ann_preserves_es (pes1 k) s1"
              by (simp add: ann_preserves_pes_def)
            from b8 c52 have "\<exists>es. pes1 k = EvtSeq (AnonyEvent c) es"
              using b12 b5 c0 evtseq_cmd_tran_anonyevt by fastforce
            then obtain es where "pes1 k = EvtSeq (AnonyEvent c) es" by auto
            with f0 have "ann_preserves_e (AnonyEvent c) s1"
              by (simp add: ann_preserves_es_def)
          }
          then show ?thesis by auto
        qed

        let ?j = "length (c2 @ [C2']) - 2"
        have d2: "ann_preserves_e (AnonyEvent c) s2"
        proof-     
          {
            from c9 c60 have "c2 @ [C2'] \<in> preserves_pes" 
              using pes_tran_not_etran1 run_cpt_preserves by blast
            with c10 b10 have "ann_preserves_pes pes2 s2"
              apply (simp add: preserves_pes_def)
              apply (erule_tac x = "?j" in allE)
              by (simp add: getspc_def gets_def)
            then have f0 : "ann_preserves_es (pes2 k) s2"
              by (simp add: ann_preserves_pes_def)
            from b10 c62 have "\<exists>es. pes2 k = EvtSeq (AnonyEvent c) es"
              using b13 b5 c0 evtseq_cmd_tran_anonyevt by fastforce
            then obtain es where "pes2 k = EvtSeq (AnonyEvent c) es" by auto
            with f0 have "ann_preserves_e (AnonyEvent c) s2"
              by (simp add: ann_preserves_es_def)
          }
          then show ?thesis by auto
        qed

        from b8 b9 c52 have "\<exists>e1. (AnonyEvent c, s1, x1) -et-Cmd c\<sharp>k\<rightarrow> (e1, s1', x1')"
          by (simp add:  pes_cmd_tran_anonyevt1)
        then obtain e1 where d3 : "(AnonyEvent c, s1, x1) -et-Cmd c\<sharp>k\<rightarrow> (e1, s1', x1')"by auto

        from b10 b11 c62 have "\<exists>e2. (AnonyEvent c, s2, x2) -et-Cmd c\<sharp>k\<rightarrow> (e2, s2', x2')"
          by (simp add:  pes_cmd_tran_anonyevt1)
        then obtain e2 where d4: "(AnonyEvent c, s2, x2) -et-Cmd c\<sharp>k\<rightarrow> (e2, s2', x2')" by auto

        from c14 a1 b3 b8 b10 c12 have d5: "(dome s1 (E\<^sub>e ef)) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 (E\<^sub>e ef))\<sim> s2" 
          using gets_def vpeqc_def  by (metis fst_conv snd_conv) 

        from a1 b8 b10 have d5 : "s1 \<sim>u\<sim> s2"
          by (simp add: gets_def vpeqc_def)

        from c14 a1 b3 b8 b10 c12 have d6: "(dome s1 (E\<^sub>e ef)) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 (E\<^sub>e ef))\<sim> s2" 
          using gets_def vpeqc_def by (metis fst_conv snd_conv) 

        with d0 d1 d2 d3 d4 d5 have "s1' \<sim>u\<sim> s2'"
          using consistent_next_state by blast

        then show ?case by (simp add: b11 b9 gets_def vpeqc_def)
          next
            case (EvtEnt x)
            from b12 have r1: "s1 = s1'" using entevt_notchgstate
              by (metis EvtEnt.prems b5 evtent_is_basicevt)
            from b13 have r2: "s2 = s2'" using entevt_notchgstate
              by (metis EvtEnt.prems b5 evtent_is_basicevt) 
            from a1 b8 b9 b10 b11 r1 r2 show ?case using gets_def vpeqc_def vpeq_reflexive
              by (metis fst_conv snd_conv)
          qed
        }
        then show ?thesis by auto qed
    }
    then show ?thesis using step_consistent_def by blast
  qed
qed

theorem UnwindingTheoremE_nonleakage:
    assumes p1: observed_consistent
    and     p2: step_consistent_events
  shows nonleakage
  by (simp add: UnwindingTheorem_nonleakage p1 p2 rg_sc_imp_sc)

theorem UnwindingTheoremE_noninfluence0: 
    assumes p1: observed_consistent
    and     p2: locally_respect_events
    and     p3: step_consistent_events
  shows     noninfluence0
  by (simp add: UnwindingTheorem_noninfluence0 p1 p2 p3 rg_lr_imp_lr rg_sc_imp_sc)

end

end