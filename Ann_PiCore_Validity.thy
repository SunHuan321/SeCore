section \<open>Validity of Correctness Formulas\<close>

theory Ann_PiCore_Validity
imports Ann_PiCore_Computation
begin

subsection \<open>Definitions Correctness Formulas\<close>

primrec ann_preserves_p :: "('s ann_prog) option \<Rightarrow> 's \<Rightarrow> bool"
  where "ann_preserves_p None s = True" |
        "ann_preserves_p (Some P) s = (s \<in> ann_pre P)"

definition assume_p :: "('s set \<times> ('s \<times> 's) set) \<Rightarrow> ('s pconfs) set" where
  "assume_p \<equiv> \<lambda>(pre, rely). {c. gets_p (c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -pe\<rightarrow> c!(Suc i) \<longrightarrow> (gets_p (c!i), gets_p (c!Suc i)) \<in> rely)}"

definition commit_p :: "(('s \<times> 's) set \<times> 's set) \<Rightarrow> ('s pconfs) set" where
  "commit_p \<equiv> \<lambda>(guar, post). {c. (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -c\<rightarrow> c!(Suc i) \<longrightarrow> (gets_p (c!i), gets_p (c!Suc i)) \<in> guar) \<and> 
               (getspc_p (last c) = None \<longrightarrow> gets_p (last c) \<in> post)}"

definition preserves_p :: "('s pconfs) set" where
  "preserves_p \<equiv> {c. (\<forall>i. i < length c \<longrightarrow> ann_preserves_p (getspc_p (c!i)) (gets_p (c!i)))}"

definition prog_validity :: "'s ann_prog \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool" 
                 ("\<Turnstile> _ sat\<^sub>p [_, _, _, _]" [60,0,0,0,0] 45) where
  "\<Turnstile> P sat\<^sub>p [pre, rely, guar, post] \<equiv> 
   \<forall>s. cpts_of_p (Some P) s \<inter> assume_p(pre, rely) \<subseteq> commit_p(guar, post) \<inter> preserves_p"

primrec ann_preserves_e :: "('l,'k,'s) event \<Rightarrow> 's \<Rightarrow> bool"
  where "ann_preserves_e (AnonyEvent P) s = (ann_preserves_p P s)" |
        "ann_preserves_e (BasicEvent _) s = True"
                                              

definition assume_e :: "('s set \<times> ('s \<times> 's) set) \<Rightarrow> (('l,'k,'s) econfs) set" where
  "assume_e \<equiv> \<lambda>(pre, rely). {c. gets_e (c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -ee\<rightarrow> c!(Suc i) \<longrightarrow> (gets_e (c!i), gets_e (c!Suc i)) \<in> rely)}"

definition commit_e :: "(('s \<times> 's) set \<times> 's set) \<Rightarrow> (('l,'k,'s) econfs) set" where
  "commit_e \<equiv> \<lambda>(guar, post). {c. (\<forall>i. Suc i<length c \<longrightarrow> 
               (\<exists>t. c!i -et-t\<rightarrow> c!(Suc i)) \<longrightarrow> (gets_e (c!i), gets_e (c!Suc i)) \<in> guar) \<and> 
               (getspc_e (last c) = AnonyEvent (None) \<longrightarrow> gets_e (last c) \<in> post)}"

definition preserves_e :: "(('l,'k,'s) econfs) set" where
  "preserves_e \<equiv> {c. (\<forall>i. i < length c \<longrightarrow> ann_preserves_e (getspc_e (c!i)) (gets_e (c!i)))}"

definition evt_validity :: "('l,'k,'s) event \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool" 
                 ("\<Turnstile> _ sat\<^sub>e [_, _, _, _]" [60,0,0,0,0] 45) where
  "\<Turnstile> Evt sat\<^sub>e [pre, rely, guar, post] \<equiv> 
   \<forall>s x. (cpts_of_ev Evt s x) \<inter> assume_e(pre, rely) \<subseteq> commit_e(guar, post) \<inter> preserves_e"

primrec ann_preserves_es :: "('l,'k,'s) esys \<Rightarrow> 's \<Rightarrow> bool"
  where "ann_preserves_es (EvtSeq e es) s = (ann_preserves_e e s)" |
        "ann_preserves_es (EvtSys es) s = (\<forall>e \<in> es. ann_preserves_e e s)"

definition assume_es :: "('s set \<times> ('s \<times> 's) set) \<Rightarrow> (('l,'k,'s) esconfs) set" where
  "assume_es \<equiv> \<lambda>(pre, rely). {c. gets_es (c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -ese\<rightarrow> c!(Suc i) \<longrightarrow> (gets_es (c!i), gets_es (c!Suc i)) \<in> rely)}"

definition commit_es :: "(('s \<times> 's) set \<times> 's set) \<Rightarrow> (('l,'k,'s) esconfs) set" where
  "commit_es \<equiv> \<lambda>(guar, post). {c. (\<forall>i. Suc i<length c \<longrightarrow> 
               (\<exists>t. c!i -es-t\<rightarrow> c!(Suc i)) \<longrightarrow> (gets_es (c!i), gets_es (c!Suc i)) \<in> guar) }"

definition preserves_es :: "(('l,'k,'s) esconfs) set" where
  "preserves_es \<equiv> {c. (\<forall>i. i < length c \<longrightarrow> ann_preserves_es (getspc_es (c!i)) (gets_es (c!i)))}"

definition es_validity :: "('l,'k,'s) esys \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool" 
                 ("\<Turnstile> _ sat\<^sub>s [_, _, _, _]" [60,0,0,0,0] 45) where
  "\<Turnstile> es sat\<^sub>s [pre, rely, guar, post] \<equiv> 
   \<forall>s x. (cpts_of_es es s x) \<inter> assume_es(pre, rely) \<subseteq> commit_es(guar, post) \<inter> preserves_es"

definition ann_preserves_pes :: "('l,'k,'s) paresys \<Rightarrow> 's \<Rightarrow> bool" where
  "ann_preserves_pes pes s \<equiv> \<forall>k. ann_preserves_es (pes k) s"

definition assume_pes :: "('s set \<times> ('s \<times> 's) set) \<Rightarrow> (('l,'k,'s) pesconfs) set" where
  "assume_pes \<equiv> \<lambda>(pre, rely). {c. gets (c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -pese\<rightarrow> c!(Suc i) \<longrightarrow> (gets (c!i), gets (c!Suc i)) \<in> rely)}"


definition commit_pes :: "(('s \<times> 's) set \<times> 's set) \<Rightarrow> (('l,'k,'s) pesconfs) set" where
  "commit_pes \<equiv> \<lambda>(guar, post). {c. (\<forall>i. Suc i<length c \<longrightarrow> 
               (\<exists>t. c!i -pes-t\<rightarrow> c!(Suc i)) \<longrightarrow> (gets (c!i), gets (c!Suc i)) \<in> guar)}"

definition preserves_pes :: "(('l,'k,'s) pesconfs) set" where
  "preserves_pes \<equiv> {c. (\<forall>i. i < length c \<longrightarrow> ann_preserves_pes (getspc (c!i)) (gets (c!i)))}"

definition pes_validity :: "('l,'k,'s) paresys \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool" 
                 ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0,0] 45) where
  "\<Turnstile> pes SAT [pre, rely, guar, post] \<equiv> 
   \<forall>s x. (cpts_of_pes pes s x) \<inter> assume_pes(pre, rely) \<subseteq> commit_pes(guar, post) \<inter> preserves_pes"

subsection \<open>Lemmas of Correctness Formulas\<close>

lemma assume_es_one_more: 
  "\<lbrakk>esl\<in>cpts_es; m > 0; m < length esl; take m esl\<in>assume_es(pre, rely); \<not>(esl!(m-1) -ese\<rightarrow>esl!m)\<rbrakk>
        \<Longrightarrow> take (Suc m) esl \<in> assume_es(pre, rely)"
  proof -
    assume p0: "esl\<in>cpts_es"
      and  p1: "m > 0"
      and  p2: "m < length esl"
      and  p3: "take m esl\<in>assume_es(pre, rely)"
      and  p4: "\<not>(esl!(m-1) -ese\<rightarrow>esl!m)"
    let ?esl1 = "take (Suc m) esl"
    let ?esl = "take m esl"
    have "gets_es (?esl1!0) \<in> pre \<and> (\<forall>i. Suc i<length ?esl1 \<longrightarrow> 
               ?esl1!i -ese\<rightarrow> ?esl1!(Suc i) \<longrightarrow> (gets_es (?esl1!i), gets_es (?esl1!Suc i)) \<in> rely)"
      proof
        from p1 p2 p3 show "gets_es (?esl1!0) \<in> pre" by (simp add:assume_es_def)
      next
        show "\<forall>i. Suc i<length ?esl1 \<longrightarrow> 
               ?esl1!i -ese\<rightarrow> ?esl1!(Suc i) \<longrightarrow> (gets_es (?esl1!i), gets_es (?esl1!Suc i)) \<in> rely"
          proof -
          {
            fix i
            assume a0: "Suc i<length ?esl1"
              and  a1: "?esl1!i -ese\<rightarrow> ?esl1!(Suc i)"
            have "(gets_es (?esl1!i), gets_es (?esl1!Suc i)) \<in> rely"
              proof(cases "i < m - 1")
                assume b0: "i < m - 1"
                with p1 have b1: "gets_es (?esl1!i) = gets_es (?esl!i)" by simp
                from b0 p1 have b2: "gets_es (?esl1!Suc i) = gets_es (?esl!Suc i)" by simp
                from p3 have "\<forall>i. Suc i<length ?esl \<longrightarrow> 
                                  ?esl!i -ese\<rightarrow> ?esl!(Suc i) \<longrightarrow> 
                                  (gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> rely"
                  by (simp add:assume_es_def)
                with b0 have "(gets_es (?esl!i), gets_es (?esl!Suc i)) \<in> rely"
                  by (metis (no_types, lifting) One_nat_def Suc_mono Suc_pred a1 
                    length_take less_SucI less_imp_le_nat min.absorb2 nth_take p1 p2) 
                with b1 b2 show ?thesis by simp
              next
                assume  "\<not>(i < m - 1)"
                with a0 have b0: "i = m - 1" by (simp add: less_antisym p1) 
                with p1 p4 a1 show ?thesis by simp
              qed
          } then show ?thesis by auto qed
      qed
    then show ?thesis by (simp add:assume_es_def)
  qed


lemma assume_es_take_n: 
  "\<lbrakk>m > 0; m \<le> length esl; esl\<in>assume_es(pre, rely)\<rbrakk>
        \<Longrightarrow> take m esl \<in> assume_es(pre, rely)"
  proof -
    assume p1: "m > 0"
      and  p2: "m \<le> length esl"
      and  p3: "esl\<in>assume_es(pre, rely)"
    let ?esl1 = "take m esl"
    from p3 have "gets_es (esl!0)\<in>pre" by (simp add:assume_es_def)
    with p1 p2 p3 have "gets_es (?esl1!0) \<in> pre" by simp
    moreover
    have "\<forall>i. Suc i<length ?esl1 \<longrightarrow> 
           ?esl1!i -ese\<rightarrow> ?esl1!(Suc i) \<longrightarrow> (gets_es (?esl1!i), gets_es (?esl1!Suc i)) \<in> rely"
      proof -
      {
        fix i
        assume a0: "Suc i<length ?esl1"
          and  a1: "?esl1!i -ese\<rightarrow> ?esl1!(Suc i)"
        with p3 have "(gets_es (esl!i), gets_es (esl!Suc i)) \<in> rely" by (simp add:assume_es_def)
        with p1 p2 a0 have "(gets_es (?esl1!i), gets_es (?esl1!Suc i)) \<in> rely"
          using Suc_lessD length_take min.absorb2 nth_take by auto
      }
      then show ?thesis by auto qed
    ultimately show ?thesis by (simp add:assume_es_def)
  qed

lemma assume_es_drop_n: 
  "\<lbrakk>m < length esl; esl\<in>assume_es(pre, rely); gets_es (esl!m) \<in> pre1\<rbrakk>
        \<Longrightarrow> drop m esl \<in> assume_es(pre1, rely)"
  proof -
    assume p1: "m < length esl"
      and  p3: "esl\<in>assume_es(pre, rely)"
      and  p2: "gets_es (esl!m) \<in> pre1"
    let ?esl1 = "drop m esl"
    from p1 p2 p3 have "gets_es (?esl1!0) \<in> pre1"
      by (simp add: hd_conv_nth hd_drop_conv_nth not_less) 
    moreover
    have "\<forall>i. Suc i<length ?esl1 \<longrightarrow> 
           ?esl1!i -ese\<rightarrow> ?esl1!(Suc i) \<longrightarrow> (gets_es (?esl1!i), gets_es (?esl1!Suc i)) \<in> rely"
      proof -
      {
        fix i
        assume a0: "Suc i<length ?esl1"
          and  a1: "?esl1!i -ese\<rightarrow> ?esl1!(Suc i)"
        with p1 p3 have "(gets_es (esl!(m+i)), gets_es (esl!Suc (m+i))) \<in> rely" by (simp add: assume_es_def)
        with p1 p2 a0 have "(gets_es (?esl1!i), gets_es (?esl1!Suc i)) \<in> rely"
          using Suc_lessD length_take min.absorb2 nth_take by auto
      }
      then show ?thesis by auto qed
    ultimately show ?thesis by (simp add:assume_es_def)
  qed

lemma commit_es_take_n: 
  "\<lbrakk>m > 0; m \<le> length esl; esl\<in>commit_es(guar, post)\<rbrakk>
        \<Longrightarrow> take m esl \<in> commit_es(guar, post)"
  proof -
    assume p1: "m > 0"
      and  p2: "m \<le> length esl"
      and  p3: "esl\<in>commit_es(guar, post)"
    let ?esl1 = "take m esl" 
    have "\<forall>i. Suc i<length ?esl1 \<longrightarrow> 
           (\<exists>t. ?esl1!i -es-t\<rightarrow> ?esl1!(Suc i)) \<longrightarrow> (gets_es (?esl1!i), gets_es (?esl1!Suc i)) \<in> guar"
      proof -
      {
        fix i
        assume a0: "Suc i<length ?esl1"
          and  a1: "(\<exists>t. ?esl1!i -es-t\<rightarrow> ?esl1!(Suc i))"
        with p3 have "(gets_es (esl!i), gets_es (esl!Suc i)) \<in> guar" by (simp add:commit_es_def)
        with p1 p2 a0 have "(gets_es (?esl1!i), gets_es (?esl1!Suc i)) \<in> guar"
          using Suc_lessD length_take min.absorb2 nth_take by auto
      }
      then show ?thesis by auto qed
    then show ?thesis by (simp add:commit_es_def)
  qed

lemma commit_es_drop_n: 
  "\<lbrakk>m < length esl; esl\<in>commit_es(guar, post)\<rbrakk>
        \<Longrightarrow> drop m esl \<in> commit_es(guar, post)"
  proof -
    assume p1: "m < length esl"
      and  p3: "esl\<in>commit_es(guar, post)"
    let ?esl1 = "drop m esl"
    have "\<forall>i. Suc i<length ?esl1 \<longrightarrow> 
           (\<exists>t. ?esl1!i -es-t\<rightarrow> ?esl1!(Suc i)) \<longrightarrow> (gets_es (?esl1!i), gets_es (?esl1!Suc i)) \<in> guar"
      proof -
      {
        fix i
        assume a0: "Suc i<length ?esl1"
          and  a1: "(\<exists>t. ?esl1!i -es-t\<rightarrow> ?esl1!(Suc i))"
        with p3 have "(gets_es (esl!(m+i)), gets_es (esl!Suc (m+i))) \<in> guar" by (simp add:commit_es_def)
        with p1 a0 have "(gets_es (?esl1!i), gets_es (?esl1!Suc i)) \<in> guar"
          using Suc_lessD length_take min.absorb2 nth_take by auto
      }
      then show ?thesis by auto qed
    then show ?thesis by (simp add:commit_es_def)
  qed

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

lemma assume_pes_imp: "\<lbrakk>pre1\<subseteq>pre; rely1\<subseteq>rely; c\<in>assume_pes(pre1,rely1)\<rbrakk> \<Longrightarrow> c\<in>assume_pes(pre,rely)"
  proof -
    assume p0: "pre1\<subseteq>pre"
      and  p1: "rely1\<subseteq>rely"
      and  p3: "c\<in>assume_pes(pre1,rely1)"
    then have a0: "gets (c!0) \<in> pre1 \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -pese\<rightarrow> c!(Suc i) \<longrightarrow> (gets (c!i), gets (c!Suc i)) \<in> rely1)"
      by (simp add:assume_pes_def)
    show ?thesis
      proof(simp add:assume_pes_def,rule conjI)
        from p0 a0 show "gets (c ! 0) \<in> pre" by auto
      next
        from p1 a0 show "\<forall>i. Suc i < length c \<longrightarrow> c ! i -pese\<rightarrow> c ! Suc i 
                            \<longrightarrow> (gets (c ! i), gets (c ! Suc i)) \<in> rely"
          by auto
      qed
  qed

lemma commit_pes_imp: "\<lbrakk>guar1\<subseteq>guar; post1\<subseteq>post; c\<in>commit_pes(guar1,post1)\<rbrakk> \<Longrightarrow> c\<in>commit_pes(guar,post)"
  proof -
    assume p0: "guar1\<subseteq>guar"
      and  p1: "post1\<subseteq>post"
      and  p3: "c\<in>commit_pes(guar1,post1)"
    then have a0: "\<forall>i. Suc i<length c \<longrightarrow> 
               (\<exists>t. c!i -pes-t\<rightarrow> c!(Suc i)) \<longrightarrow> (gets (c!i), gets (c!Suc i)) \<in> guar1"
      by (simp add:commit_pes_def)
    show ?thesis
      proof(simp add:commit_pes_def)
        from p0 a0 show "\<forall>i. Suc i < length c \<longrightarrow> (\<exists>t. c ! i -pes-t\<rightarrow> c ! Suc i) 
                            \<longrightarrow> (gets (c ! i), gets (c ! Suc i)) \<in> guar"
          by auto
      qed
  qed

lemma assume_pes_take_n: 
  "\<lbrakk>m > 0; m \<le> length esl; esl\<in>assume_pes(pre, rely)\<rbrakk>
        \<Longrightarrow> take m esl \<in> assume_pes(pre, rely)"
  proof -
    assume p1: "m > 0"
      and  p2: "m \<le> length esl"
      and  p3: "esl\<in>assume_pes(pre, rely)"
    let ?esl1 = "take m esl"
    from p3 have "gets (esl!0)\<in>pre" by (simp add:assume_pes_def)
    with p1 p2 p3 have "gets (?esl1!0) \<in> pre" by simp
    moreover
    have "\<forall>i. Suc i<length ?esl1 \<longrightarrow> 
           ?esl1!i -pese\<rightarrow> ?esl1!(Suc i) \<longrightarrow> (gets (?esl1!i), gets (?esl1!Suc i)) \<in> rely"
      proof -
      {
        fix i
        assume a0: "Suc i<length ?esl1"
          and  a1: "?esl1!i -pese\<rightarrow> ?esl1!(Suc i)"
        with p3 have "(gets (esl!i), gets (esl!Suc i)) \<in> rely" by (simp add:assume_pes_def)
        with p1 p2 a0 have "(gets (?esl1!i), gets (?esl1!Suc i)) \<in> rely"
          using Suc_lessD length_take min.absorb2 nth_take by auto
      }
      then show ?thesis by auto qed
    ultimately show ?thesis by (simp add:assume_pes_def)
  qed

lemma assume_pes_drop_n: 
  "\<lbrakk>m < length esl; esl\<in>assume_pes(pre, rely); gets (esl!m) \<in> pre1\<rbrakk>
        \<Longrightarrow> drop m esl \<in> assume_pes(pre1, rely)"
  proof -
    assume p1: "m < length esl"
      and  p3: "esl\<in>assume_pes(pre, rely)"
      and  p2: "gets (esl!m) \<in> pre1"
    let ?esl1 = "drop m esl"
    from p1 p2 p3 have "gets (?esl1!0) \<in> pre1"
      by (simp add: hd_conv_nth hd_drop_conv_nth not_less) 
    moreover
    have "\<forall>i. Suc i<length ?esl1 \<longrightarrow> 
           ?esl1!i -pese\<rightarrow> ?esl1!(Suc i) \<longrightarrow> (gets (?esl1!i), gets (?esl1!Suc i)) \<in> rely"
      proof -
      {
        fix i
        assume a0: "Suc i<length ?esl1"
          and  a1: "?esl1!i -pese\<rightarrow> ?esl1!(Suc i)"
        with p1 p3 have "(gets (esl!(m+i)), gets (esl!Suc (m+i))) \<in> rely" by (simp add: assume_pes_def)
        with p1 p2 a0 have "(gets (?esl1!i), gets (?esl1!Suc i)) \<in> rely"
          using Suc_lessD length_take min.absorb2 nth_take by auto
      }
      then show ?thesis by auto qed
    ultimately show ?thesis by (simp add:assume_pes_def)
  qed

end (*theory Validity*)