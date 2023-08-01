(*
Created by Yongwang Zhao (ywzhao@ntu.edu.sg, zhaoyw@buaa.edu.cn)
School of Computer Engineering, Nanyang Technological University, Singapore
and School of Computer Science & Engineering, Beihang University, China
*)

section \<open>Concrete Syntax of PiCore Language\<close>

theory PiCore_Syntax 
imports PiCore_Language (*PiCore_RG_IFS *)

(*keywords "procedures" :: thy_decl*)

begin

syntax
  "_quote"     :: "'b \<Rightarrow> ('s \<Rightarrow> 'b)"                ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('s \<Rightarrow> 'b) \<Rightarrow> 'b"                ("\<acute>_" [1000] 1000)
  "_Assert"    :: "'s \<Rightarrow> 's set"                    ("(\<lbrace>_\<rbrace>)" [0] 1000)

translations
  "\<lbrace>b\<rbrace>" \<rightharpoonup> "CONST Collect \<guillemotleft>b\<guillemotright>"

parse_translation \<open>
  let
    fun quote_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote"} t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(@{syntax_const "_quote"}, K quote_tr)] end
\<close>

definition Skip :: "'s prog"  ("SKIP")
  where "SKIP \<equiv> Basic id"

notation Seq  ("(_;;/ _)" [60,61] 60)

syntax
  "_Assign"    :: "idt \<Rightarrow> 'b \<Rightarrow> 's prog"                      ("(\<acute>_ :=/ _)" [70, 65] 61)
  "_Cond"      :: "'s bexp \<Rightarrow> 's prog \<Rightarrow> 's prog \<Rightarrow> 's prog"  ("(0IF _/ THEN _/ ELSE _/FI)" [0, 0, 0] 61)
  "_Cond2"     :: "'s bexp \<Rightarrow> 's prog \<Rightarrow> 's prog"             ("(0IF _ THEN _ FI)" [0,0] 56)
  "_While"     :: "'s bexp \<Rightarrow> 's prog \<Rightarrow> 's prog"             ("(0WHILE _ /DO _ /OD)"  [0, 0] 61)
  "_Await"     :: "'s bexp \<Rightarrow> 's prog \<Rightarrow> 's prog"             ("(0AWAIT _ /THEN /_ /END)"  [0,0] 61)
  "_Atom"      :: "'s prog \<Rightarrow> 's prog"                        ("(\<langle>_\<rangle>)" 61)
  "_Wait"      :: "'s bexp \<Rightarrow> 's prog"                       ("(0WAIT _ END)" 61)
  "_Event"     :: "['a, 'a, 'a] \<Rightarrow> ('l,'k,'s) event" ("(EVENT _ WHERE _ THEN _ END)" [0,0,0] 61)

translations
  "\<acute>x := a" \<rightharpoonup> "CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>"
  "IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST Cond \<lbrace>b\<rbrace> c1 c2"
  "IF b THEN c FI" \<rightleftharpoons> "IF b THEN c ELSE SKIP FI"
  "WHILE b DO c OD" \<rightharpoonup> "CONST While \<lbrace>b\<rbrace> c"
  "AWAIT b THEN c END" \<rightleftharpoons> "CONST Await \<lbrace>b\<rbrace> c"
  "\<langle>c\<rangle>" \<rightleftharpoons> "AWAIT CONST True THEN c END"
  "WAIT b END" \<rightleftharpoons> "AWAIT b THEN SKIP END"
  "EVENT l WHERE g THEN bd END" \<rightharpoonup> "CONST BasicEvent (l,(\<lbrace>g\<rbrace>,bd))"


text \<open>Translations for variables before and after a transition:\<close>

syntax
  "_before" :: "id \<Rightarrow> 'a" ("\<ordmasculine>_")
  "_after"  :: "id \<Rightarrow> 'a" ("\<ordfeminine>_")

translations
  "\<ordmasculine>x" \<rightleftharpoons> "x \<acute>CONST fst"
  "\<ordfeminine>x" \<rightleftharpoons> "x \<acute>CONST snd"

print_translation \<open>
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax_Trans.quote_tr' @{syntax_const "_antiquote"} t, ts)
      | quote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const @{syntax_const "_Assert"});

    fun bexp_tr' name ((Const (@{const_syntax Collect}, _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun assign_tr' (Abs (x, _, f $ k $ Bound 0) :: ts) =
          quote_tr' (Syntax.const @{syntax_const "_Assign"} $ Syntax_Trans.update_name_tr' f)
            (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | assign_tr' _ = raise Match;
  in
   [(@{const_syntax Collect}, K assert_tr'),
    (@{const_syntax Basic}, K assign_tr'),
    (@{const_syntax Cond}, K (bexp_tr' @{syntax_const "_Cond"})),
    (@{const_syntax While}, K (bexp_tr' @{syntax_const "_While"}))]
  end
\<close>

lemma colltrue_eq_univ[simp]: "\<lbrace>True\<rbrace> = UNIV" by auto

end
