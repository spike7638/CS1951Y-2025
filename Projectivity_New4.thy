theory Projectivity_New4
  imports Complex_Main "Chapter4-3" "HOL-Algebra.Group"
begin

section \<open>Perspectivity Spec (Parameterized)\<close>

type_synonym ('p1, 'l1) pSpec = "('l1 \<times> 'p1 \<times> 'l1)"

fun is_pSpec_param :: "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('l \<times> 'p \<times> 'l) \<Rightarrow> bool" where
  "is_pSpec_param Pts Lns inc (k, P, m) = 
     (k \<in> Lns \<and> P \<in> Pts \<and> m \<in> Lns \<and> \<not>inc P k \<and> \<not>inc P m)"

definition spec_domain :: "('p, 'l) pSpec \<Rightarrow> 'l" where
  "spec_domain s = (case s of (k, _, _) \<Rightarrow> k)"

definition spec_center :: "('p, 'l) pSpec \<Rightarrow> 'p" where
  "spec_center s = (case s of (_, P, _) \<Rightarrow> P)"

definition spec_range :: "('p, 'l) pSpec \<Rightarrow> 'l" where
  "spec_range s = (case s of (_, _, m) \<Rightarrow> m)"

type_synonym ('p1, 'l1) pChain = "('p1, 'l1) pSpec list"
(* this might be a problem; we really need chains to be non-empty pspec-lists *)

fun is_pChain_param :: "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p, 'l) pChain \<Rightarrow> bool" where
  "is_pChain_param Pts Lns inc [] = False" |
  "is_pChain_param Pts Lns inc [s] = is_pSpec_param Pts Lns inc s" |
  "is_pChain_param Pts Lns inc (s1 # s2 # ss) = (
     is_pSpec_param Pts Lns inc s1 \<and> 
     is_pSpec_param Pts Lns inc s2 \<and> 
     spec_range s1 = spec_domain s2 \<and> 
     is_pChain_param Pts Lns inc (s2 # ss)
  )"

fun chain_begin :: "('p, 'l) pChain \<Rightarrow> 'l" where
  "chain_begin (s # _) = spec_domain s" |
  "chain_begin [] = undefined"

fun chain_end :: "('p, 'l) pChain \<Rightarrow> 'l" where
  "chain_end [s] = spec_range s" |
  "chain_end (_ # ss) = chain_end ss" |
  "chain_end [] = undefined"

section \<open>Perspectivities and Realizations (Parameterized)\<close>

definition perspectivity_from_spec_param :: 
  "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'l \<Rightarrow> 'p) \<Rightarrow> 
   ('p, 'l) pSpec \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "perspectivity_from_spec_param Pts Lns inc join_op meet_op s =
     (case s of (k, P, m) \<Rightarrow>
       if is_pSpec_param Pts Lns inc (k, P, m)
       then (\<lambda>Q. if Q \<in> Pts \<and> inc Q k then meet_op (join_op P Q) m else undefined)
       else undefined)"

fun realization_param :: 
  "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'l \<Rightarrow> 'p) \<Rightarrow> 
   ('p, 'l) pChain \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "realization_param Pts Lns inc join_op meet_op [] = (\<lambda>Q. Q)" |  (* potential problem here *)
  "realization_param Pts Lns inc join_op meet_op [s] = 
     perspectivity_from_spec_param Pts Lns inc join_op meet_op s" |
  "realization_param Pts Lns inc join_op meet_op (s # ss) = 
     (realization_param Pts Lns inc join_op meet_op ss) \<circ> 
     (perspectivity_from_spec_param Pts Lns inc join_op meet_op s)"

section \<open>Parameterized Chain Equivalence\<close>

definition chains_equiv_param :: 
  "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'l \<Rightarrow> 'p) \<Rightarrow> 
   ('p, 'l) pChain \<Rightarrow> ('p, 'l) pChain \<Rightarrow> bool" where
  "chains_equiv_param Pts Lns inc join_op meet_op c1 c2 \<longleftrightarrow> (
     is_pChain_param Pts Lns inc c1 \<and> 
     is_pChain_param Pts Lns inc c2 \<and>
     chain_begin c1 = chain_begin c2 \<and>
     chain_end c1 = chain_end c2 \<and>
     (\<forall>Q. Q \<in> Pts \<longrightarrow> inc Q (chain_begin c1) \<longrightarrow> 
          realization_param Pts Lns inc join_op meet_op c1 Q = 
          realization_param Pts Lns inc join_op meet_op c2 Q)
  )"

context projective_plane
begin

section \<open>Perspectivity Spec\<close>

abbreviation is_pSpec :: "('p, 'l) pSpec \<Rightarrow> bool" where
  "is_pSpec s \<equiv> is_pSpec_param Points Lines (\<lhd>) s"

lemma is_pSpec_unfold:
  "is_pSpec (k, P, m) = (k \<in> Lines \<and> P \<in> Points \<and> m \<in> Lines \<and> \<not>(P \<lhd> k) \<and> \<not>(P \<lhd> m))"
  by auto

lemma pSpec_components:
  "is_pSpec s \<Longrightarrow> 
   spec_domain s \<in> Lines \<and> 
   spec_center s \<in> Points \<and> 
   spec_range s \<in> Lines \<and>
   \<not>(spec_center s \<lhd> spec_domain s) \<and>
   \<not>(spec_center s \<lhd> spec_range s)"
  by (cases s) (auto simp: spec_domain_def spec_center_def spec_range_def)

abbreviation perspectivity_from_spec :: "('p, 'l) pSpec \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "perspectivity_from_spec s \<equiv> perspectivity_from_spec_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) s"

lemma perspectivity_from_spec_unfold:
  "perspectivity_from_spec (k, P, m) = 
     (if is_pSpec (k, P, m)
      then (\<lambda>Q. if Q \<in> Points \<and> Q \<lhd> k then meet (join P Q) m else undefined)
      else undefined)"
  unfolding perspectivity_from_spec_param_def by auto

lemma perspectivity_from_spec_alt:
  "perspectivity_from_spec s = 
   (if is_pSpec s
    then (\<lambda>Q. if Q \<in> Points \<and> Q \<lhd> spec_domain s 
              then meet (join (spec_center s) Q) (spec_range s) 
              else undefined)
    else undefined)"
  by (cases s) (auto simp: spec_domain_def spec_center_def spec_range_def 
                            perspectivity_from_spec_param_def)

text \<open>Basic properties of perspectivities\<close>

lemma perspectivity_maps_correctly:
  assumes "is_pSpec s"
  assumes "Q \<in> Points" "Q \<lhd> spec_domain s"
  shows "perspectivity_from_spec s Q \<in> Points \<and> 
         perspectivity_from_spec s Q \<lhd> spec_range s"
proof -
  obtain k P m where s_def: "s = (k, P, m)" by (cases s) auto
  have "k \<in> Lines" "P \<in> Points" "m \<in> Lines" "\<not>(P \<lhd> k)" "\<not>(P \<lhd> m)"
    using assms(1) s_def by auto
  moreover have "Q \<lhd> k" 
    using assms(3) s_def spec_domain_def by (metis case_prod_conv)
  have st: "(P \<bar> Q \<sqdot> m)  \<in> Points" using assms meet_properties2 
    join_properties1 join_properties2 using \<open>Q \<lhd> k\<close> calculation(2,3,4,5)
    by blast
  have su: "(P \<bar> Q \<sqdot> m) \<lhd> m" 
    using meet_properties2 join_properties1[of Or P] assms \<open>Q \<lhd> k\<close> calculation(2,3,4,5)
    join_properties1 by auto
  ultimately show ?thesis
    using assms(2) join_properties1 meet_properties2 s_def 
    by (simp add: \<open>Q \<lhd> k\<close> spec_range_def st perspectivity_from_spec_param_def)
qed

lemma perspectivity_inverse:
  assumes "is_pSpec (k, P, m)"
  assumes "is_pSpec (m, P, k)"
  assumes "Q \<in> Points" "Q \<lhd> k"
  shows "perspectivity_from_spec (m, P, k) (perspectivity_from_spec (k, P, m) Q) = Q"
proof -
  let ?f = "perspectivity_from_spec (k, P, m)"
  let ?g = "perspectivity_from_spec (m, P, k)"
  
  have fQ: "?f Q = meet (join P Q) m"
    using assms(1,3,4) perspectivity_from_spec_unfold by auto
  
  have fQ_props: "?f Q \<in> Points" "?f Q \<lhd> m"
    using assms perspectivity_maps_correctly[of "(k, P, m)" Q]
    by (auto simp: spec_domain_def spec_range_def)
  
  have "?g (?f Q) = meet (join P (?f Q)) k"
    using assms(2) fQ_props perspectivity_from_spec_unfold by auto
  
  also have "... = meet (join P (meet (join P Q) m)) k"
    using fQ by simp
  
  also have "... = Q"
    using assms join_properties1 meet_properties2 unique_meet
    by (smt (verit, best) is_pSpec_unfold)
  
  finally show ?thesis .
qed

lemma inverse_persp:
  fixes f Or l1 l2 Q
  assumes data_def: "is_pSpec (l1, Or, l2)"
  assumes f_def: "f = perspectivity_from_spec (l1, Or, l2)"
  assumes g_def: "g = perspectivity_from_spec (l2, Or, l1)"
  assumes Q_facts: "Q \<in> Points \<and> Q \<lhd> l1"
  shows "(g (f Q)) = Q"
proof -
  have f2: "(f Q) = (Or \<bar> Q) \<sqdot> l2" 
    unfolding f_def g_def perspectivity_from_spec_unfold using assms by auto
  then have fQnice: "(f Q) \<in> Points \<and> (f Q) \<lhd> l2" 
    using Q_facts data_def join_properties1 meet_properties2 by auto
  have gdata_def: "is_pSpec (l2, Or, l1)" using data_def by auto
  have g1: "g (f Q) = (Or \<bar> (f Q)) \<sqdot> l1"
    unfolding f_def g_def perspectivity_from_spec_unfold 
    using fQnice f2 Q_facts gdata_def assms by auto
  then have "g (f Q) = (Or \<bar> ((Or \<bar> Q) \<sqdot> l2)) \<sqdot> l1" using f2 by auto
  then show ?thesis using Q_facts data_def f_def g_def
    gdata_def perspectivity_inverse
    by presburger
qed

lemma perspectivity_injective:
  assumes "is_pSpec s"
  assumes "Q1 \<in> Points" "Q1 \<lhd> spec_domain s"
  assumes "Q2 \<in> Points" "Q2 \<lhd> spec_domain s"
  assumes "perspectivity_from_spec s Q1 = perspectivity_from_spec s Q2"
  shows "Q1 = Q2"
proof -
  obtain l0 Or l2 where s_def: "s = (l0, Or, l2)"  using prod_cases3 by blast
  obtain t where t_def: "t =(l2, Or, l0)" by blast
  obtain smap where smap_def: "smap = perspectivity_from_spec s" by blast
  obtain tmap where tmap_def: "tmap = perspectivity_from_spec t" by blast
  have f0: "Q \<lhd> l0 \<and> Q \<in> Points \<Longrightarrow>  tmap (smap Q) = Q" for Q using inverse_persp assms smap_def tmap_def
  using s_def t_def by blast
  have "spec_domain (l0, Or, l2) = l0" using  spec_domain_def by force
  then have uu: "spec_domain s = l0" using s_def by blast
  thm f0[of Q1]
  show ?thesis using f0 [of Q1] f0 [of Q2] uu assms smap_def by metis
qed

lemma perspectivity_injective2:
  assumes "is_pSpec s"
  assumes "D = {Q \<in> Points. Q \<lhd> spec_domain s}"
  shows "inj_on (perspectivity_from_spec s) D"
  by (smt (verit) assms(1,2) inj_on_def mem_Collect_eq perspectivity_injective)  (* can surely be simplified with an 'of' *)


lemma perspectivity_surjective:
  assumes "is_pSpec s"
  assumes "R \<in> Points" "R \<lhd> spec_range s"
  shows "\<exists>Q \<in> Points. Q \<lhd> spec_domain s \<and> perspectivity_from_spec s Q = R"
proof -
  obtain k P m where s_def: "s = (k, P, m)"  using prod_cases3 by blast
  obtain t where t_def: "t =(m, P, k)" by blast
  have t_good: "is_pSpec t" using assms t_def  by (simp add: s_def)
  have tr: "spec_range t = k" using t_def spec_range_def [of "(m,P,k)"] by simp
  have td: "spec_domain t = m" using t_def spec_domain_def [of "(m,P,k)"] by simp
  have sr: "spec_range s = m" using s_def spec_range_def [of "(k,P,m)"] by simp
  have sd: "spec_domain s = k" using s_def spec_domain_def [of "(k,P,m)"] by simp
  obtain smap where smap_def: "smap = perspectivity_from_spec s" by blast
  obtain tmap where tmap_def: "tmap = perspectivity_from_spec t" by blast
  have f0: "R0 \<lhd> m \<and> R0 \<in> Points \<Longrightarrow>  smap (tmap R0) = R0" for R0 using inverse_persp assms smap_def tmap_def
      s_def t_def by auto
  obtain Q0 where Q0_def: "Q0 = tmap R" by blast
  have Rm: "R \<lhd> spec_domain t" using td sr assms  by simp
  have "Q0 \<lhd> k" using  perspectivity_maps_correctly [of t R] t_good assms(2) td Rm  tmap_def t_def Q0_def assms spec_range_def s_def sr td tr t_good by blast
  then show ?thesis using Q0_def sd f0[of R]
    using Rm assms(2) perspectivity_maps_correctly smap_def t_good td tmap_def by blast
qed

lemma perspectivity_surjective2:
  assumes "is_pSpec s"
  assumes "D = {Q \<in> Points. Q \<lhd> spec_domain s}"
  assumes "R = {H \<in> Points. H \<lhd> spec_range s}"
  assumes "f = perspectivity_from_spec s"
  shows "f ` D = R"
proof -
  have a0: "f ` D = {y. \<exists>x\<in>D. y = f x}"  using Set.image_def[of f D] assms 
  by (smt (verit, ccfv_SIG) Collect_cong mem_Collect_eq perspectivity_maps_correctly perspectivity_surjective)
  have a1: "{y. \<exists>x\<in>D. y = f x} = {H \<in> Points. H \<lhd> spec_range s}" using perspectivity_surjective 
    by (metis (mono_tags, lifting) assms(1,2,4) mem_Collect_eq perspectivity_maps_correctly)
  show ?thesis using a0 a1 assms(3) by argo
qed

lemma perspectivity_bijective:
  assumes "is_pSpec s"
  shows "bij_betw (perspectivity_from_spec s)
                  {Q \<in> Points. Q \<lhd> spec_domain s}
                  {R \<in> Points. R \<lhd> spec_range s}"
proof -
  have "perspectivity_from_spec s ` {p \<in> Points. p \<lhd> spec_domain s} = {p \<in> Points. p \<lhd> spec_range s}"
    using assms perspectivity_surjective2 by auto
  then show ?thesis
    by (simp add: assms bij_betw_def perspectivity_injective2)
qed

section \<open>Perspectivity Chains\<close>

text \<open>A pChain is a non-empty list of pSpecs where range of the previous and domain of the next are the same\<close>

abbreviation is_pChain :: "('p, 'l) pChain \<Rightarrow> bool" where
  "is_pChain c \<equiv> is_pChain_param Points Lines (\<lhd>) c"

lemma is_pChain_unfold:
  "is_pChain [] = False"
  "is_pChain [s] = is_pSpec s"
  "is_pChain (s1 # s2 # ss) = (
     is_pSpec s1 \<and> 
     is_pSpec s2 \<and> 
     spec_range s1 = spec_domain s2 \<and> 
     is_pChain (s2 # ss)
  )"
  by auto

lemma pChain_nonempty:
  "is_pChain c \<Longrightarrow> c \<noteq> []"
  by (cases c) auto

lemma pChain_cons:
  "is_pChain (s # ss) \<Longrightarrow> is_pSpec s"
  by (cases ss) auto

lemma pChain_tail:
  assumes "is_pChain (s # ss)"
  assumes "ss \<noteq> []"
  shows "is_pChain ss"
  using assms by (cases ss) auto

lemma chain_begin_in_Lines:
  "is_pChain c \<Longrightarrow> chain_begin c \<in> Lines"
  by (smt (verit) chain_begin.elims is_pChain_param.elims(1) 
      is_pChain_param.simps(1) list.inject pSpec_components)

lemma chain_end_in_Lines:
  "is_pChain c \<Longrightarrow> chain_end c \<in> Lines"
  sorry (* need to figure out induction on the chain *)

section \<open>Realization of Chains\<close>

text \<open>The realization function composes perspectivities to get the actual function\<close>

abbreviation realization :: "('p, 'l) pChain \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "realization c \<equiv> realization_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c"

lemma realization_unfold:
  "realization [] = (\<lambda>Q. Q)"
  "realization [s] = perspectivity_from_spec s"
  "realization (s # ss) = (realization ss) \<circ> (perspectivity_from_spec s)"
  sorry (* need to figure out induction on the chain *)

lemma realization_single:
  "realization [s] = perspectivity_from_spec s"
  by simp

lemma realization_domain:
  assumes "is_pChain c"
  assumes "Q \<in> Points" "Q \<lhd> chain_begin c"
  shows "realization c Q \<in> Points \<and> realization c Q \<lhd> chain_end c"
  sorry (* need to figure out induction on the chain *)

lemma realization_append:
  assumes "is_pChain c1" "is_pChain c2"
  assumes "chain_end c1 = chain_begin c2"
  shows "realization (c1 @ c2) = (realization c2) \<circ> (realization c1)"
  sorry (* need to figure out induction on the chain *)

section \<open>Equivalence of Chains\<close>

abbreviation chains_equiv :: "('p, 'l) pChain \<Rightarrow> ('p, 'l) pChain \<Rightarrow> bool" 
  (infix "\<simeq>" 50) where
  "chains_equiv c1 c2 \<equiv> chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2"

lemma chains_equiv_unfold:
  "c1 \<simeq> c2 \<longleftrightarrow> (
     is_pChain c1 \<and> is_pChain c2 \<and>
     chain_begin c1 = chain_begin c2 \<and>
     chain_end c1 = chain_end c2 \<and>
     (\<forall>Q. Q \<in> Points \<longrightarrow> Q \<lhd> chain_begin c1 \<longrightarrow> realization c1 Q = realization c2 Q)
  )"
  unfolding chains_equiv_param_def by auto

lemma chains_equiv_refl:
  assumes "is_pChain c"
  shows "c \<simeq> c"
  using assms chains_equiv_unfold by auto

lemma chains_equiv_sym:
  assumes "c1 \<simeq> c2"
  shows "c2 \<simeq> c1"
  using assms chains_equiv_unfold by auto

lemma chains_equiv_trans:
  assumes "c1 \<simeq> c2" "c2 \<simeq> c3"
  shows "c1 \<simeq> c3"
  using assms chains_equiv_unfold by auto

lemma chains_equiv_param_refl_in_locale:
  assumes "is_pChain_param Points Lines (\<lhd>) c"
  shows "chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c c"
  using assms unfolding chains_equiv_param_def by auto

lemma chains_equiv_param_sym_in_locale:
  assumes "chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2"
  shows "chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c2 c1"
  using assms unfolding chains_equiv_param_def by auto

lemma chains_equiv_param_trans_in_locale:
  assumes "chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2"
  assumes "chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c2 c3"
  shows "chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c3"
  using assms unfolding chains_equiv_param_def by auto

lemma chains_equiv_param_is_equiv_in_locale:
  "equiv {c. is_pChain_param Points Lines (\<lhd>) c} 
         {(c1, c2). chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2}"
  unfolding equiv_def refl_on_def sym_def trans_def
  using chains_equiv_param_refl_in_locale
        chains_equiv_param_sym_in_locale
        chains_equiv_param_trans_in_locale
  sorry

lemma chains_equiv_is_equiv:
  "equiv {c. is_pChain c} {(c1, c2). c1 \<simeq> c2}"
  using chains_equiv_param_is_equiv_in_locale by simp

text \<open>Identity perspectivity example\<close>

lemma identity_perspectivity:
  assumes "is_pSpec (m, P, m)"
  assumes "Q \<in> Points" "Q \<lhd> m"
  shows "perspectivity_from_spec (m, P, m) Q = Q"
  using assms join_properties1 meet_properties2 unique_meet
  sorry

lemma chain_extend_with_identity:
  assumes "is_pSpec (k, P, m)"
  assumes "is_pSpec (m, P, m)"
  shows "[(k, P, m)] \<simeq> [(k, P, m), (m, P, m)]"
  sorry

section \<open>"Quotient Type" for Projectivities\<close>

definition projectivity_class :: "('p, 'l) pChain \<Rightarrow> ('p, 'l) pChain set" where
  "projectivity_class c = {c'. chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c c'}"

text \<open>The type of all projectivities is the set of equivalence classes of valid chains\<close>

definition all_projectivities :: "(('p, 'l) pChain set) set" where
  "all_projectivities = {projectivity_class c | c. is_pChain c}"

lemma projectivity_class_equiv:
  assumes "is_pChain c"
  assumes "is_pChain c'"
  assumes "c' \<in> projectivity_class c"
  shows "projectivity_class c = projectivity_class c'"
  using assms chains_equiv_param_trans_in_locale chains_equiv_param_sym_in_locale
  unfolding projectivity_class_def
  sorry

text \<open>A projectivity is represented by any member of its equivalence class\<close>

type_synonym ('p1, 'l1) projectivity = "('p1, 'l1) pChain"

text \<open>Two projectivities are equal if they're in the same equivalence class\<close>

definition proj_eq :: "('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c1 \<sim> c2 \<longleftrightarrow> chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2"

lemma proj_eq_equiv:
  "equiv {c. is_pChain c} {(c1, c2). c1 \<sim> c2}"
  sorry

text \<open>Define operations on projectivities\<close>

definition proj_domain :: "('p, 'l) projectivity \<Rightarrow> 'l" where
  "proj_domain c = chain_begin c"

definition proj_range :: "('p, 'l) projectivity \<Rightarrow> 'l" where
  "proj_range c = chain_end c"

lemma proj_domain_respects_equiv:
  assumes "c1 \<sim> c2"
  shows "proj_domain c1 = proj_domain c2"
  sorry

lemma proj_range_respects_equiv:
  assumes "c1 \<sim> c2"
  shows "proj_range c1 = proj_range c2"
  sorry

text \<open>Define composition of projectivities (when compatible)\<close>

definition proj_compose :: "('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity option" where
  "proj_compose c1 c2 = 
     (if is_pChain c1 \<and> is_pChain c2 \<and> chain_end c1 = chain_begin c2 
      then Some (c1 @ c2) 
      else None)"

lemma proj_compose_respects_equiv:
  assumes "c1 \<sim> c1'" "c2 \<sim> c2'"
  assumes "is_pChain c1" "is_pChain c2"
  shows "proj_compose c1 c2 = None \<and> proj_compose c1' c2' = None \<or>
         (\<exists>c c'. proj_compose c1 c2 = Some c \<and> 
                 proj_compose c1' c2' = Some c' \<and> 
                 c \<sim> c')"
  sorry

text \<open>Define the set of projectivities for a given line k (pLoops)\<close>

definition PJ :: "'l \<Rightarrow> ('p, 'l) projectivity set" where
  "PJ k = {c. is_pChain c \<and> chain_begin c = k \<and> chain_end c = k}"

lemma PJ_respects_equiv:
  assumes "c \<in> PJ k" "c \<sim> c'"
  shows "c' \<in> PJ k"
  sorry

text \<open>Define composition as a binary operation on PJ(k)\<close>

definition proj_mult :: "'l \<Rightarrow> ('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity" where
  "proj_mult k c1 c2 = (if c1 \<in> PJ k \<and> c2 \<in> PJ k 
                        then (case proj_compose c1 c2 of Some c \<Rightarrow> c | None \<Rightarrow> undefined)
                        else undefined)"

text \<open>Define the identity element for PJ(k) using any point P not on k\<close>

definition proj_identity :: "'l \<Rightarrow> 'p \<Rightarrow> ('p, 'l) projectivity" where
  "proj_identity k P = (if k \<in> Lines \<and> P \<in> Points \<and> \<not>(P \<lhd> k) \<and> is_pSpec (k, P, k)
                        then [(k, P, k)]
                        else undefined)"

lemma proj_identity_in_PJ:
  assumes "k \<in> Lines" "P \<in> Points" "\<not>(P \<lhd> k)" "is_pSpec (k, P, k)"
  shows "proj_identity k P \<in> PJ k"
  unfolding proj_identity_def PJ_def
  using assms
  by (auto simp: spec_domain_def spec_range_def)

text \<open>Inverse of projectivity\<close>

fun reverse_chain :: "('p, 'l) pChain \<Rightarrow> ('p, 'l) pChain" where
  "reverse_chain [] = []" |
  "reverse_chain ((k, P, m) # cs) = 
     reverse_chain cs @ [(m, P, k)]"

definition proj_inverse :: "('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity" where
  "proj_inverse c = reverse_chain c"

lemma reverse_chain_begin_finish:
  assumes "is_pChain c"
  shows "chain_begin (reverse_chain c) = chain_end c \<and>
         chain_end (reverse_chain c) = chain_begin c"
  sorry

lemma proj_inverse_in_PJ:
  assumes "c \<in> PJ k"
  shows "proj_inverse c \<in> PJ k"
  using assms reverse_chain_begin_finish
  unfolding proj_inverse_def PJ_def
  sorry

text \<open>Group\<close>

lemma PJ_closure:
  assumes "k \<in> Lines"
  assumes "c1 \<in> PJ k" "c2 \<in> PJ k"
  shows "proj_mult k c1 c2 \<in> PJ k"
  sorry

lemma PJ_associative:
  assumes "k \<in> Lines"
  assumes "c1 \<in> PJ k" "c2 \<in> PJ k" "c3 \<in> PJ k"
  shows "proj_mult k (proj_mult k c1 c2) c3 \<sim> 
         proj_mult k c1 (proj_mult k c2 c3)"
  sorry

lemma PJ_identity:
  assumes "k \<in> Lines" "P \<in> Points" "\<not>(P \<lhd> k)"
  assumes "c \<in> PJ k"
  shows "proj_mult k (proj_identity k P) c \<sim> c \<and>
         proj_mult k c (proj_identity k P) \<sim> c"
  sorry

lemma PJ_inverse:
  assumes "k \<in> Lines"
  assumes "c \<in> PJ k"
  shows "\<exists>c_inv \<in> PJ k. proj_mult k c c_inv \<sim> proj_identity k P \<and>
                        proj_mult k c_inv c \<sim> proj_identity k P"
  sorry

end

end
