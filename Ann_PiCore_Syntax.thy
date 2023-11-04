
section \<open>Concrete Syntax of PiCore Language\<close>

theory Ann_PiCore_Syntax 
imports Ann_PiCore_Language (*PiCore_RG_IFS *)

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

abbreviation AnnSkip :: "'s assn \<Rightarrow> 's ann_prog"  ("_//SKIP" [90] 63)
  where "r SKIP \<equiv> AnnBasic r id"

notation AnnSeq  ("(_;;/ _)" [60,61] 60)

syntax
  "_Assign"    :: "'s assn \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> 's ann_prog"                      ("(_ \<acute>_ :=/ _)" [70, 70, 65] 61)
  "_Cond"      :: "'s assn \<Rightarrow> 's bexp \<Rightarrow> 's ann_prog \<Rightarrow> 's ann_prog \<Rightarrow> 's ann_prog"  ("(0_ IF _/ THEN _/ ELSE _/FI)" [0, 0, 0, 0] 61)
  "_While"     :: "'s assn \<Rightarrow> 's bexp \<Rightarrow> 's ann_prog \<Rightarrow> 's ann_prog"             ("(0_ WHILE _ /DO _ /OD)"  [0,0,0] 61)
  "_Await"     :: "'s assn \<Rightarrow> 's bexp \<Rightarrow> 's ann_prog \<Rightarrow> 's ann_prog"             ("(0_ AWAIT _ /THEN /_ /END)"  [0,0,0] 61)
  "_Atom"      :: "'s assn \<Rightarrow> 's ann_prog \<Rightarrow> 's ann_prog"                        ("(_ ATOMIC _ END)" [0] 61)
  "_Event"     :: "['a, 'a, 'a] \<Rightarrow> ('l,'k,'s) event" ("(EVENT _ WHERE _ THEN _ END)" [0,0,0] 61)

translations
  "r \<acute>x := a" \<rightharpoonup> "CONST AnnBasic r \<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>"
  "r IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST AnnCond r \<lbrace>b\<rbrace> c1 c2"
  "r WHILE b DO c OD" \<rightharpoonup> "CONST AnnWhile r \<lbrace>b\<rbrace> c"
  "r AWAIT b THEN c END" \<rightleftharpoons> "CONST AnnAwait r \<lbrace>b\<rbrace> c"
  "r ATOMIC c END" \<rightleftharpoons> "r AWAIT CONST True THEN c END"
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
    (@{const_syntax AnnBasic}, K assign_tr'),
    (@{const_syntax AnnCond}, K (bexp_tr' @{syntax_const "_Cond"})),
    (@{const_syntax AnnWhile}, K (bexp_tr' @{syntax_const "_While"}))]
  end
\<close>

lemma colltrue_eq_univ[simp]: "\<lbrace>True\<rbrace> = UNIV" by auto

end