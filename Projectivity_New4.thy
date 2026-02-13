theory Projectivity_New4
  imports Complex_Main "Chapter4-3" "HOL-Algebra.Group"
begin

section \<open>Perspectivity Spec (Parameterized)\<close>
text\<open>A perspectivity in a projective plane involves two lines and a point that's not on either one. 
We can abstract this as a "pSpec" (a proto perspectivity-specification) -- a line-point-line triple. But only 
certain pSpecs (ones where the point doesn't lie on either line) define perspectivities. To make 
sense of this, we need the projective plane apparatus: the set of points; the set of lines; 
the incidence function. Places where these are used get the suffix "param" (where the "parameters"
are the set of points, the set of lines, the incidence function, etc.. But even without
this, the notion of the domain, range, and center of the perspectivity-specification make sense. I'll 
also add the 'inverse' of a perspectivity specification, just to flesh things out. So:
pSpec: the abtract list of (k, P, n) where k and n have the same type, and P a different type
pSpec_param: the version of this where we have the apparatus of a projective plane to work with 
perspectivity: the version of this in a particular persp_realization: the function from k to n defined by a *(valid) pSpec in a projective plane .

When it comes to projectivities, which unfortunately start with the same letter, we'll use the word
'chain' for a list of perspecitivitys, chain_param for the version in a chain_realization for
the associated line-to-line function.  \<close>

type_synonym ('p1, 'l1) pSpec = "('l1 \<times> 'p1 \<times> 'l1)"

definition pSpec_domain :: "('p, 'l) pSpec \<Rightarrow> 'l" where
  "pSpec_domain s = (case s of (k, _, _) \<Rightarrow> k)"

definition pSpec_center :: "('p, 'l) pSpec \<Rightarrow> 'p" where
  "pSpec_center s = (case s of (_, P, _) \<Rightarrow> P)"

definition pSpec_range :: "('p, 'l) pSpec \<Rightarrow> 'l" where
  "pSpec_range s = (case s of (_, _, m) \<Rightarrow> m)"

definition pSpec_inverse :: "('p, 'l) pSpec \<Rightarrow> ('p, 'l) pSpec" where
  "pSpec_inverse s = (case s of (k, P, m) \<Rightarrow> (m, P, k))"

lemma [simp]: "pSpec_domain (pSpec_inverse s) = pSpec_range s"
  by (simp add: case_prod_unfold pSpec_domain_def pSpec_inverse_def pSpec_range_def)

lemma [simp]: "pSpec_range (pSpec_inverse s) = pSpec_domain s"
  by (simp add: case_prod_unfold pSpec_domain_def pSpec_inverse_def pSpec_range_def)

lemma  [simp]:"pSpec_center (pSpec_inverse s) = pSpec_center s"
  by (simp add: case_prod_unfold pSpec_domain_def pSpec_center_def pSpec_inverse_def pSpec_range_def)

text\<open>Chains, like pSpecs, are proto-projectivities: sequences of things that might represent
perspectivities. Note that to be an actual projectivity, the sequence must not be empty. \<close>


type_synonym ('p1, 'l1) chain = "('p1, 'l1) pSpec list"

fun chain_begin :: "('p, 'l) chain \<Rightarrow> 'l" where
  "chain_begin (s # _) = pSpec_domain s" |
  "chain_begin [] = undefined"

fun chain_end :: "('p, 'l) chain \<Rightarrow> 'l" where
  "chain_end [s] = pSpec_range s" |
  "chain_end (_ # ss) = chain_end ss" |
  "chain_end [] = undefined"

fun chain_inverse :: "('p, 'l) chain \<Rightarrow> ('p, 'l) chain" where
  "chain_inverse [] = undefined" |
  "chain_inverse (s) = map pSpec_inverse (rev s)" 


section \<open>Perspectivities in a projective geometry\<close>
fun is_pSpec_param :: "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('l \<times> 'p \<times> 'l) \<Rightarrow> bool" where
  "is_pSpec_param Pts Lns inc (k, P, m) = 
     (k \<in> Lns \<and> P \<in> Pts \<and> m \<in> Lns \<and> \<not>inc P k \<and> \<not>inc P m)"

fun is_chain_param :: "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p, 'l) chain \<Rightarrow> bool" where
  "is_chain_param Pts Lns inc [] = False" |
  "is_chain_param Pts Lns inc [s] = is_pSpec_param Pts Lns inc s" |
  "is_chain_param Pts Lns inc (s1 # s2 # ss) = (
     is_pSpec_param Pts Lns inc s1 \<and> 
     is_pSpec_param Pts Lns inc s2 \<and> 
     pSpec_range s1 = pSpec_domain s2 \<and> 
     is_chain_param Pts Lns inc (s2 # ss)
  )"

lemma chain_rest_is_chain1:
  "is_chain_param Pts Lns inc (s1 # s2 # ss) \<Longrightarrow> is_chain_param Pts Lns inc (s2 # ss)" by simp

text\<open>Now we take these specifications of perspectivities and projectivities and 
turn them into actual functions from the beginning line to the ending line; we call this
"realization"\<close>

definition perspectivity_from_pSpec_param :: 
  "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'l \<Rightarrow> 'p) \<Rightarrow> 
   ('p, 'l) pSpec \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "perspectivity_from_pSpec_param Pts Lns inc join_op meet_op s =
     (case s of (k, P, m) \<Rightarrow>
       if is_pSpec_param Pts Lns inc (k, P, m)
       then (\<lambda>Q. if Q \<in> Pts \<and> inc Q k then meet_op (join_op P Q) m else undefined)
       else undefined)"

(* The following definition needs sanity-checking; I inserted the is_chain_param condition *)
fun realization_param :: (* convert projectivity spec to function from beginning to ending line *)
  "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'l \<Rightarrow> 'p) \<Rightarrow> 
   ('p, 'l) chain \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "realization_param Pts Lns inc join_op meet_op [] = undefined" |  
  "realization_param Pts Lns inc join_op meet_op [s] = 
     perspectivity_from_pSpec_param Pts Lns inc join_op meet_op s" |
  "realization_param Pts Lns inc join_op meet_op c = 
      (case c of s # ss \<Rightarrow>
        if  is_chain_param Pts Lns inc c 
        then (realization_param Pts Lns inc join_op meet_op ss) \<circ> 
          (perspectivity_from_pSpec_param Pts Lns inc join_op meet_op s)
        else undefined)"



section \<open>Parameterized Chain Equivalence\<close>

definition chains_equiv_param :: (* do two chain define the same line-to-line function *)
  "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'l \<Rightarrow> 'p) \<Rightarrow> 
   ('p, 'l) chain \<Rightarrow> ('p, 'l) chain \<Rightarrow> bool" where
  "chains_equiv_param Pts Lns inc join_op meet_op c1 c2 \<longleftrightarrow> (
     is_chain_param Pts Lns inc c1 \<and> 
     is_chain_param Pts Lns inc c2 \<and>
     chain_begin c1 = chain_begin c2 \<and>
     chain_end c1 = chain_end c2 \<and>
     (\<forall>Q. Q \<in> Pts \<and> inc Q (chain_begin c1) \<longrightarrow> 
          realization_param Pts Lns inc join_op meet_op c1 Q = 
          realization_param Pts Lns inc join_op meet_op c2 Q)
  )"

(* Orig:
definition chains_equiv_param :: (* do two chain define the same line-to-line function *)
  "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'l \<Rightarrow> 'p) \<Rightarrow> 
   ('p, 'l) chain \<Rightarrow> ('p, 'l) chain \<Rightarrow> bool" where
  "chains_equiv_param Pts Lns inc join_op meet_op c1 c2 \<longleftrightarrow> (
     is_chain_param Pts Lns inc c1 \<and> 
     is_chain_param Pts Lns inc c2 \<and>
     chain_begin c1 = chain_begin c2 \<and>
     chain_end c1 = chain_end c2 \<and>
     (\<forall>Q. Q \<in> Pts \<and> inc Q (chain_begin c1) \<longrightarrow> 
          realization_param Pts Lns inc join_op meet_op c1 Q = 
          realization_param Pts Lns inc join_op meet_op c2 Q)
  )"
*)

section \<open>Perspectivity Spec\<close>
context projective_plane
begin

definition is_pSpec :: "('p, 'l) pSpec \<Rightarrow> bool" where
  "is_pSpec s \<equiv> is_pSpec_param Points Lines (\<lhd>) s"

lemma is_pSpec_unfold:
  "is_pSpec (k, P, m) = (k \<in> Lines \<and> P \<in> Points \<and> m \<in> Lines \<and> \<not>(P \<lhd> k) \<and> \<not>(P \<lhd> m))"
  unfolding is_pSpec_param.cases is_pSpec_def by auto

lemma pSpec_components:
  "is_pSpec s \<Longrightarrow> 
   pSpec_domain s \<in> Lines \<and> 
   pSpec_center s \<in> Points \<and> 
   pSpec_range s \<in> Lines \<and>
   \<not>(pSpec_center s \<lhd> pSpec_domain s) \<and>
   \<not>(pSpec_center s \<lhd> pSpec_range s)"
proof -
  assume ah: "is_pSpec s"
  obtain k P m where s_def: "s = (k, P, m) \<and> k \<in> Lines \<and> m \<in> Lines \<and> P \<in> Points" 
    using ah prod_cases3   by (metis is_pSpec_unfold)
  then have "(pSpec_domain s = k) \<and> (pSpec_center s = P) \<and> (pSpec_range s = m)" 
    using pSpec_domain_def pSpec_center_def pSpec_range_def by force
  then show ?thesis using s_def is_pSpec_param.cases is_pSpec_def is_pSpec_unfold [of k P m]
  using ah by auto
qed 

abbreviation perspectivity_from_spec2 :: "('p, 'l) pSpec \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "perspectivity_from_spec2 s \<equiv> perspectivity_from_pSpec_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) s"

definition perspectivity_from_pSpec ::  "('p, 'l) pSpec \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "perspectivity_from_pSpec  s =
     (case s of (k, P, m) \<Rightarrow>
       if is_pSpec_param Points Lines  (\<lhd>) (k, P, m)
       then (\<lambda>Q. if Q \<in> Points \<and>  Q \<lhd> k then ( P \<bar> Q) \<sqdot> m else undefined)
       else undefined)"

lemma perspectivity_from_pSpec_unfold:
  "perspectivity_from_pSpec (k, P, m) = 
     (if is_pSpec (k, P, m)
      then (\<lambda>Q. if Q \<in> Points \<and> Q \<lhd> k then meet (join P Q) m else undefined)
      else undefined)"
  unfolding perspectivity_from_pSpec_def is_pSpec_param.cases  using is_pSpec_def by auto

lemma perspectivity_from_pSpec_alt:
  "perspectivity_from_pSpec s = 
   (if is_pSpec s
    then (\<lambda>Q. if Q \<in> Points \<and> Q \<lhd> pSpec_domain s 
              then meet (join (pSpec_center s) Q) (pSpec_range s) 
              else undefined)
    else undefined)" 
proof -
  obtain k P m where s_def: "s = (k, P, m)" using prod_cases3 by blast
  then have f0: "perspectivity_from_pSpec s = perspectivity_from_pSpec (k, P, m)" by auto
  show ?thesis using f0 perspectivity_from_pSpec_unfold[of k P m] s_def pSpec_domain_def [of "(k,P,m)"] pSpec_range_def [of "(k,P,m)"] 
      pSpec_center_def [of "(k,P,m)"] by fastforce
qed

text \<open>Basic properties of perspectivities\<close>

lemma perspectivity_maps_correctly:
  assumes "is_pSpec s"
  assumes "Q \<in> Points" "Q \<lhd> pSpec_domain s"
  shows "perspectivity_from_pSpec s Q \<in> Points \<and> 
         perspectivity_from_pSpec s Q \<lhd> pSpec_range s"
proof -
  obtain k P m where s_def: "s = (k, P, m)" by (cases s) auto
  have "k \<in> Lines" "P \<in> Points" "m \<in> Lines" "\<not>(P \<lhd> k)" "\<not>(P \<lhd> m)"
    using assms(1) s_def is_pSpec_def is_pSpec_param.cases by auto
  moreover have qk: "Q \<lhd> k" 
    using assms(3) s_def pSpec_domain_def by (metis case_prod_conv)
  have st: "(P \<bar> Q \<sqdot> m)  \<in> Points" using assms meet_properties2 
    join_properties1 join_properties2 using \<open>Q \<lhd> k\<close> calculation(2,3,4,5)
    by blast
  have su: "(P \<bar> Q \<sqdot> m) \<lhd> m" 
    using meet_properties2 join_properties1[of Or P] assms \<open>Q \<lhd> k\<close> calculation(2,3,4,5)
    join_properties1 by auto
  ultimately show ?thesis
    using assms(2) join_properties1 meet_properties2 s_def 
      qk pSpec_range_def st perspectivity_from_pSpec_param_def
  by (smt (verit, ccfv_threshold) assms(1,3) pSpec_components perspectivity_from_pSpec_alt)
qed

lemma perspectivity_inverse:
  assumes "is_pSpec (k, P, m)"
  assumes "is_pSpec (m, P, k)"
  assumes "Q \<in> Points" "Q \<lhd> k"
  shows "perspectivity_from_pSpec (m, P, k) (perspectivity_from_pSpec (k, P, m) Q) = Q"
proof -
  let ?f = "perspectivity_from_pSpec (k, P, m)"
  let ?g = "perspectivity_from_pSpec (m, P, k)"
  
  have fQ: "?f Q = meet (join P Q) m"
    using assms(1,3,4) perspectivity_from_pSpec_unfold by auto
  
  have fQ_props: "?f Q \<in> Points" "?f Q \<lhd> m"
    using assms perspectivity_maps_correctly[of "(k, P, m)" Q]
    by (auto simp: pSpec_domain_def pSpec_range_def)
  
  have "?g (?f Q) = meet (join P (?f Q)) k"
    using assms(2) fQ_props perspectivity_from_pSpec_unfold by auto
  
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
  assumes f_def: "f = perspectivity_from_pSpec (l1, Or, l2)"
  assumes g_def: "g = perspectivity_from_pSpec (l2, Or, l1)"
  assumes Q_facts: "Q \<in> Points \<and> Q \<lhd> l1"
  shows "(g (f Q)) = Q"
proof -
  have f2: "(f Q) = (Or \<bar> Q) \<sqdot> l2" 
    unfolding f_def g_def perspectivity_from_pSpec_unfold using assms by auto
  then have fQnice: "(f Q) \<in> Points \<and> (f Q) \<lhd> l2" 
    using Q_facts data_def join_properties1 meet_properties2
  using is_pSpec_unfold by auto
  have gdata_def: "is_pSpec (l2, Or, l1)" using data_def  using is_pSpec_unfold by blast
  have g1: "g (f Q) = (Or \<bar> (f Q)) \<sqdot> l1"
    unfolding f_def g_def perspectivity_from_pSpec_unfold 
    using fQnice f2 Q_facts gdata_def assms by auto
  then have "g (f Q) = (Or \<bar> ((Or \<bar> Q) \<sqdot> l2)) \<sqdot> l1" using f2 by auto
  then show ?thesis using Q_facts data_def f_def g_def
    gdata_def perspectivity_inverse
    by presburger
qed

lemma perspectivity_injective:
  assumes "is_pSpec s"
  assumes "Q1 \<in> Points" "Q1 \<lhd> pSpec_domain s"
  assumes "Q2 \<in> Points" "Q2 \<lhd> pSpec_domain s"
  assumes "perspectivity_from_pSpec s Q1 = perspectivity_from_pSpec s Q2"
  shows "Q1 = Q2"
proof -
  obtain l0 Or l2 where s_def: "s = (l0, Or, l2)"  using prod_cases3 by blast
  obtain t where t_def: "t =(l2, Or, l0)" by blast
  obtain smap where smap_def: "smap = perspectivity_from_pSpec s" by blast
  obtain tmap where tmap_def: "tmap = perspectivity_from_pSpec t" by blast
  have f0: "Q \<lhd> l0 \<and> Q \<in> Points \<Longrightarrow>  tmap (smap Q) = Q" for Q using inverse_persp assms smap_def tmap_def
  using s_def t_def by blast
  have "pSpec_domain (l0, Or, l2) = l0" using  pSpec_domain_def by force
  then have uu: "pSpec_domain s = l0" using s_def by blast
  thm f0[of Q1]
  show ?thesis using f0 [of Q1] f0 [of Q2] uu assms smap_def by metis
qed

lemma perspectivity_injective2:
  assumes "is_pSpec s"
  assumes "D = {Q \<in> Points. Q \<lhd> pSpec_domain s}"
  shows "inj_on (perspectivity_from_pSpec s) D"
  by (smt (verit) assms(1,2) inj_on_def mem_Collect_eq perspectivity_injective)  (* can surely be simplified with an 'of' *)


lemma perspectivity_surjective:
  assumes "is_pSpec s"
  assumes "R \<in> Points" "R \<lhd> pSpec_range s"
  shows "\<exists>Q \<in> Points. Q \<lhd> pSpec_domain s \<and> perspectivity_from_pSpec s Q = R"
proof -
  obtain k P m where s_def: "s = (k, P, m)"  using prod_cases3 by blast
  obtain t where t_def: "t =(m, P, k)" by blast
  have t_good: "is_pSpec t" using assms t_def s_def is_pSpec_unfold by auto
  have tr: "pSpec_range t = k" using t_def pSpec_range_def [of "(m,P,k)"] by simp
  have td: "pSpec_domain t = m" using t_def pSpec_domain_def [of "(m,P,k)"] by simp
  have sr: "pSpec_range s = m" using s_def pSpec_range_def [of "(k,P,m)"] by simp
  have sd: "pSpec_domain s = k" using s_def pSpec_domain_def [of "(k,P,m)"] by simp
  obtain smap where smap_def: "smap = perspectivity_from_pSpec s" by blast
  obtain tmap where tmap_def: "tmap = perspectivity_from_pSpec t" by blast
  have f0: "R0 \<lhd> m \<and> R0 \<in> Points \<Longrightarrow>  smap (tmap R0) = R0" for R0 using inverse_persp assms smap_def tmap_def
      s_def t_def is_pSpec_unfold by auto
  obtain Q0 where Q0_def: "Q0 = tmap R" by blast
  have Rm: "R \<lhd> pSpec_domain t" using td sr assms  by simp
  have "Q0 \<lhd> k" using  perspectivity_maps_correctly [of t R] t_good assms(2) td Rm  tmap_def t_def Q0_def assms pSpec_range_def s_def sr td tr t_good by blast
  then show ?thesis using Q0_def sd f0[of R]
    using Rm assms(2) perspectivity_maps_correctly smap_def t_good td tmap_def by blast
qed

lemma perspectivity_surjective2:
  assumes "is_pSpec s"
  assumes "D = {Q \<in> Points. Q \<lhd> pSpec_domain s}"
  assumes "R = {H \<in> Points. H \<lhd> pSpec_range s}"
  assumes "f = perspectivity_from_pSpec s"
  shows "f ` D = R"
proof -
  have a0: "f ` D = {y. \<exists>x\<in>D. y = f x}"  using Set.image_def[of f D] assms 
  by (smt (verit, ccfv_SIG) Collect_cong mem_Collect_eq perspectivity_maps_correctly perspectivity_surjective)
  have a1: "{y. \<exists>x\<in>D. y = f x} = {H \<in> Points. H \<lhd> pSpec_range s}" using perspectivity_surjective 
    by (metis (mono_tags, lifting) assms(1,2,4) mem_Collect_eq perspectivity_maps_correctly)
  show ?thesis using a0 a1 assms(3) by argo
qed

lemma perspectivity_bijective:
  assumes "is_pSpec s"
  shows "bij_betw (perspectivity_from_pSpec s)
                  {Q \<in> Points. Q \<lhd> pSpec_domain s}
                  {R \<in> Points. R \<lhd> pSpec_range s}"
proof -
  have "perspectivity_from_pSpec s ` {p \<in> Points. p \<lhd> pSpec_domain s} = {p \<in> Points. p \<lhd> pSpec_range s}"
    using assms perspectivity_surjective2 by auto
  then show ?thesis
    by (simp add: assms bij_betw_def perspectivity_injective2)
qed

section \<open>Perspectivity Chains\<close>

text \<open>A chain is a non-empty list of pSpecs where range of the previous and domain of the next are the same\<close>

definition is_chain :: "('p, 'l) chain \<Rightarrow> bool" where
  "is_chain c \<equiv> is_chain_param Points Lines (\<lhd>) c"


lemma chain_rest_is_chain2:
  "is_chain (s1 # s2 # ss) \<Longrightarrow> is_chain (s2 # ss)"  by (simp add: is_chain_def)


lemma is_chain_unfold:
  "is_chain [] = False"
  "is_chain [s] = is_pSpec s"
  "is_chain (s1 # s2 # ss) = (
     is_pSpec s1 \<and> 
     is_pSpec s2 \<and> 
     pSpec_range s1 = pSpec_domain s2 \<and> 
     is_chain (s2 # ss)
  )"
proof -
  show "is_chain [] = False" using is_chain_def by auto
  show "is_chain [s] = is_pSpec s"  using  is_chain_def  is_pSpec_def by auto
  show "is_chain (s1 # s2 # ss) =
    (is_pSpec s1 \<and> is_pSpec s2 \<and> pSpec_range s1 = pSpec_domain s2 \<and> is_chain (s2 # ss))" 
    by (simp add: is_pSpec_def  is_chain_def )
qed

lemma chain_nonempty:
  "is_chain c \<Longrightarrow> c \<noteq> []"
  using is_chain_unfold(1) by auto


lemma chain_cons:
  "is_chain (s # ss) \<Longrightarrow> is_pSpec s"
  by (metis is_chain_param.simps(2,3) is_pSpec_def list.exhaust  is_chain_def)

lemma chain_tail:
  assumes "is_chain (s # ss)"
  assumes "ss \<noteq> []"
  shows "is_chain ss"
  using assms  is_chain_def  by (cases ss) auto

lemma chain_begin_in_Lines:
  "is_chain c \<Longrightarrow> chain_begin c \<in> Lines" 
  by (metis chain_begin.elims is_chain_unfold(1) chain_cons pSpec_components)
  

(* shows how to do induction on chains, which must be nonempty *)

lemma chain_end_in_Lines:
  "is_chain c \<Longrightarrow> chain_end c \<in> Lines"
proof -
  assume ah: "is_chain c"
  then have "c \<noteq> []" using  ah chain_nonempty by auto

  have step1: "\<lbrakk> c \<noteq>[]; is_chain c\<rbrakk> \<Longrightarrow> chain_end c \<in> Lines"
  proof (induction c rule: list_nonempty_induct)
    case (single c)
    then show ?case using is_chain_unfold(2) pSpec_components by auto
  next
    case (cons s ss)
    then show ?case  by (metis chain_end.simps(2) neq_Nil_conv chain_tail)
  qed
  show "is_chain c \<Longrightarrow> chain_end c \<in> Lines" using chain_nonempty step1 by auto
qed

section \<open>Realization of Chains\<close>

text \<open>The realization function composes perspectivities to get the actual function\<close>

(* working: 
fun realization :: "('p, 'l) chain \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "realization [] = undefined" |  
  "realization [s] =  perspectivity_from_pSpec_param  Points Lines (\<lhd>) (\<bar>) (\<sqdot>) s" |
  "realization (s # ss) =
        (if  is_chain_param  Points Lines (\<lhd>)  (s # ss) 
        then (realization ss) \<circ> 
          (perspectivity_from_pSpec_param  Points Lines (\<lhd>) (\<bar>) (\<sqdot>) s)
        else undefined)"
*)
definition realization :: "('p, 'l) chain \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "realization c = realization_param  Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c"


lemma realization_unfold:
  "realization [] = undefined"
  "realization [s] = perspectivity_from_pSpec s"
  (*  "\<lbrakk>ss \<noteq> []\<rbrakk> \<Longrightarrow> realization (s # ss) = (realization ss) \<circ> (perspectivity_from_pSpec s)" *)
proof -
  show "realization [] = undefined"   by (simp add: realization_def)
  show "realization [s] = perspectivity_from_pSpec s" by (simp add: realization_def perspectivity_from_pSpec_def perspectivity_from_pSpec_param_def)
qed

(* Major insight here from  https://stackoverflow.com/questions/67407437/how-to-use-the-base-case-assumption-when-proving-with-induct-in-isabelle, 
namely "Any assumptions that you need to be part of the induction need to be part of the proof state when you call induct."
and "You should therefore do a using assms before the proof" (!) *)

lemma realization_domain1:
  assumes "is_chain c"
  shows "\<And> Q . Q \<in> Points \<Longrightarrow> (Q \<lhd> chain_begin c \<Longrightarrow> realization c Q \<in> Points)"
proof -
  have ne: "c \<noteq> []" using is_chain_def  using assms(1) by auto
  then show "\<And>Q. Q \<in> Points \<Longrightarrow> Q \<lhd> chain_begin c \<Longrightarrow> realization c Q \<in> Points"
    using assms proof (induction c  rule: list_nonempty_induct)
    case (single x)
    then show ?case using chain_cons perspectivity_maps_correctly realization_unfold(2) by auto
  next
    case (cons s ss)
    obtain t ts where tfacts:"ss = t # ts" using chain_begin.cases cons.hyps by blast
    have f0: "is_chain (t#ts) \<Longrightarrow> Q \<in> Points \<Longrightarrow> Q \<lhd> chain_begin (t#ts) \<Longrightarrow> realization (t#ts) Q \<in> Points" for Q
      using tfacts cons.IH by auto
    have f1: "is_chain (t#ts)" using cons.prems(3) chain_tail tfacts by blast
    then have f2: "U \<in> Points \<Longrightarrow> U \<lhd> chain_begin (t#ts) \<Longrightarrow> realization (t#ts) U \<in> Points" for U  using f0 by auto
    have f4: "chain_begin (t # ts) = pSpec_domain t" by auto
    then have f5: "U \<in> Points \<and> U \<lhd> pSpec_domain t \<Longrightarrow> realization (t#ts) U \<in> Points" for U using f2 by auto
    have "(realization (s # ss) Q) =  (realization_param  Points Lines (\<lhd>) (\<bar>) (\<sqdot>) (s # ss) Q)" 
    using realization_def by auto

    then show ?case using realization_def realization_param.simps chain_begin.simps(1) comp_apply cons.prems(1,2,3) f2 is_chain_def
          is_chain_param.simps(3) chain_cons perspectivity_maps_correctly realization_param.simps realization_unfold(2)
          tfacts by sledgehammer

(*      by (smt (verit, ccfv_SIG) realization_def chain_begin.simps(1) comp_apply cons.prems(1,2,3) f2 is_chain_def
          is_chain_param.simps(3) chain_cons perspectivity_maps_correctly realization_param.simps realization_unfold(2)
          tfacts) *)
  qed
qed

lemma realization_domain2:
  assumes "is_chain c"
  shows "\<And> Q . Q \<in> Points \<Longrightarrow> (Q \<lhd> chain_begin c \<Longrightarrow> realization c Q \<lhd> chain_end c)"

proof -
  have c0: "c \<noteq> []" using assms is_chain_def by auto
  then show "\<And> Q . Q \<in> Points \<Longrightarrow> (Q \<lhd> chain_begin c \<Longrightarrow> realization c Q \<lhd> chain_end c)"
    using assms proof (induction c  rule: list_nonempty_induct)
    case (single x)
    then show ?case using chain_cons perspectivity_maps_correctly realization_unfold by auto
  next
    case (cons x xs)
    then show ?case 
      using assms proof (cases "xs = []")
      case True
      then show ?thesis using cons.hyps by blast
    next
      case False
      then obtain y ys where ydef: "xs = y # ys" using chain_begin.cases by blast
      show ?thesis 
        by (smt (verit, del_insts) chain_begin.simps(1) chain_end.simps(2) comp_apply cons.IH cons.prems(1,2,3)
            is_chain_def is_chain_param.simps(3) chain_cons perspectivity_maps_correctly realization.simps(2,3)
            realization_unfold(2) ydef)
    qed
  qed
qed


lemma realization_move:
  assumes "c1 = [u]"
  assumes "is_chain c1" "is_chain c2"
  assumes "chain_end c1 = chain_begin c2"
  shows "realization (c1 @ c2) = (realization c2) \<circ> (realization c1)"
  sorry (* need to figure out induction on the chain *)


lemma realization_append:
  assumes "is_chain c1" "is_chain c2"
  assumes "chain_end c1 = chain_begin c2"
  shows "realization (c1 @ c2) = (realization c2) \<circ> (realization c1)"
  sorry (* need to figure out induction on the chain *)

section \<open>Equivalence of Chains\<close>

abbreviation chains_equiv :: "('p, 'l) chain \<Rightarrow> ('p, 'l) chain \<Rightarrow> bool" 
  (infix "\<simeq>" 50) where
  "chains_equiv c1 c2 \<equiv> chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2"

(*
definition chains_equiv_param :: (* do two chain define the same line-to-line function *)
  "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'l \<Rightarrow> 'p) \<Rightarrow> 
   ('p, 'l) chain \<Rightarrow> ('p, 'l) chain \<Rightarrow> bool" where
  "chains_equiv_param Pts Lns inc join_op meet_op c1 c2 \<longleftrightarrow> (
     is_chain_param Pts Lns inc c1 \<and> 
     is_chain_param Pts Lns inc c2 \<and>
     chain_begin c1 = chain_begin c2 \<and>
     chain_end c1 = chain_end c2 \<and>
      (\<forall>Q. Q \<in> Pts \<and> inc Q (chain_begin c1) \<longrightarrow> 
          realization_param Pts Lns inc join_op meet_op c1 Q = 
          realization_param Pts Lns inc join_op meet_op c2 Q)
  )"
*)
lemma chains_equiv_unfold1:
  "c1 \<simeq> c2 \<Longrightarrow> (
     is_chain c1 \<and> is_chain c2 \<and>
     chain_begin c1 = chain_begin c2 \<and>
     chain_end c1 = chain_end c2 \<and>
     (\<forall>Q. Q \<in> Points \<longrightarrow> Q \<lhd> chain_begin c1 \<longrightarrow> realization c1 Q = realization c2 Q)
  )"
proof (safe)
  show f1: "c1 \<simeq> c2 \<Longrightarrow> is_chain c1" by (simp add: chains_equiv_param_def is_chain_def)
  show f2: "c1 \<simeq> c2 \<Longrightarrow> is_chain c2" by (simp add: chains_equiv_param_def is_chain_def)
  show f3: "c1 \<simeq> c2 \<Longrightarrow> (chain_begin c1 = chain_begin c2)" by (simp add: chains_equiv_param_def is_chain_def)
  show f4: "c1 \<simeq> c2 \<Longrightarrow> (chain_end c1 = chain_end c2)" by (simp add: chains_equiv_param_def is_chain_def)
  show f5: "\<And>Q. c1 \<simeq> c2 \<Longrightarrow> Q \<in> Points \<Longrightarrow> Q \<lhd> chain_begin c1 \<Longrightarrow> realization c1 Q = realization c2 Q" sorry
qed

lemma chains_equiv_unfold2:
  "(
     is_chain c1 \<and> is_chain c2 \<and>
     chain_begin c1 = chain_begin c2 \<and>
     chain_end c1 = chain_end c2 \<and>
     (\<forall>Q. Q \<in> Points \<longrightarrow> Q \<lhd> chain_begin c1 \<longrightarrow> realization c1 Q = realization c2 Q)
  ) \<Longrightarrow> c1 \<simeq> c2"
proof -
  assume ah: "is_chain c1 \<and>
    is_chain c2 \<and>
    chain_begin c1 = chain_begin c2 \<and>
    chain_end c1 = chain_end c2 \<and> (\<forall>Q. Q \<in> Points \<longrightarrow> Q \<lhd> chain_begin c1 \<longrightarrow> realization c1 Q= realization c2 Q)"

  have "(c1 \<simeq> c2) \<equiv> chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2" by simp
  then have "... = (
     is_chain_param Points Lines (\<lhd>) c1 \<and> 
     is_chain_param Points Lines (\<lhd>) c2 \<and>
     chain_begin c1 = chain_begin c2 \<and>
     chain_end c1 = chain_end c2 \<and>
     (\<forall>Q. Q \<in> Points \<and> (\<lhd>) Q (chain_begin c1) \<longrightarrow> 
          realization_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>)  c1 Q = 
          realization_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>)  c2 Q))" by (simp add: chains_equiv_param_def)
  then have "... = (is_chain c1 \<and> is_chain c2 \<and>
     chain_begin c1 = chain_begin c2 \<and>
     chain_end c1 = chain_end c2 \<and>
     (\<forall>Q. Q \<in> Points \<and> (\<lhd>) Q (chain_begin c1) \<longrightarrow> 
          realization_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>)  c1 Q = 
          realization_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>)  c2 Q))" by (simp add: is_chain_def)
  then have "... = (is_chain c1 \<and> is_chain c2 \<and>
     chain_begin c1 = chain_begin c2 \<and>
     chain_end c1 = chain_end c2 \<and>
     (\<forall>Q. Q \<in> Points \<and> (\<lhd>) Q (chain_begin c1) \<longrightarrow> 
          realization c1 Q = 
          realization_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>)  c2 Q))" by sledgehammer

  show r1: "is_chain c1 \<Longrightarrow>
    is_chain c2 \<Longrightarrow>
    chain_begin c1 = chain_begin c2 \<Longrightarrow>
    chain_end c1 = chain_end c2 \<Longrightarrow>
    \<forall>Q. Q \<in> Points \<longrightarrow> Q \<lhd> chain_begin c1 \<longrightarrow> realization c1 Q = realization c2 Q \<Longrightarrow> c1 \<simeq> c2"
  proof (clarsimp)
    have "?thesis \<equiv>  (is_chain c1 \<Longrightarrow>
    is_chain c2 \<Longrightarrow>
    chain_begin c1 = chain_begin c2 \<Longrightarrow>
    chain_end c1 = chain_end c2 \<Longrightarrow>
    \<forall>Q. Q \<in> Points \<longrightarrow> Q \<lhd> chain_begin c2 \<longrightarrow> realization c1 Q = realization c2 Q \<Longrightarrow> 
 chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2)"


lemma chains_equiv_refl:
  assumes "is_chain c"
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
  assumes "is_chain_param Points Lines (\<lhd>) c"
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
  "equiv {c. is_chain_param Points Lines (\<lhd>) c} 
         {(c1, c2). chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2}"
  unfolding equiv_def refl_on_def sym_def trans_def
  using chains_equiv_param_refl_in_locale
        chains_equiv_param_sym_in_locale
        chains_equiv_param_trans_in_locale
  sorry

lemma chains_equiv_is_equiv:
  "equiv {c. is_chain c} {(c1, c2). c1 \<simeq> c2}"
  using chains_equiv_param_is_equiv_in_locale by (simp add: is_chain_def)

text \<open>Identity perspectivity example\<close>

lemma identity_perspectivity:
  assumes "is_pSpec (m, P, m)"
  assumes "Q \<in> Points" "Q \<lhd> m"
  shows "perspectivity_from_pSpec (m, P, m) Q = Q"
  using assms join_properties1 meet_properties2 unique_meet
  sorry

lemma chain_extend_with_identity:
  assumes "is_pSpec (k, P, m)"
  assumes "is_pSpec (m, P, m)"
  shows "[(k, P, m)] \<simeq> [(k, P, m), (m, P, m)]"
  sorry

section \<open>"Quotient Type" for Projectivities\<close>

definition projectivity_class :: "('p, 'l) chain \<Rightarrow> ('p, 'l) chain set" where
  "projectivity_class c = {c'. chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c c'}"

text \<open>The type of all projectivities is the set of equivalence classes of valid chains\<close>

definition all_projectivities :: "(('p, 'l) chain set) set" where
  "all_projectivities = {projectivity_class c | c. is_chain c}"

lemma projectivity_class_equiv:
  assumes "is_chain c"
  assumes "is_chain c'"
  assumes "c' \<in> projectivity_class c"
  shows "projectivity_class c = projectivity_class c'"
  using assms chains_equiv_param_trans_in_locale chains_equiv_param_sym_in_locale
  unfolding projectivity_class_def
  sorry

text \<open>A projectivity is represented by any member of its equivalence class\<close>

type_synonym ('p1, 'l1) projectivity = "('p1, 'l1) chain"

text \<open>Two projectivities are equal if they're in the same equivalence class\<close>

definition proj_eq :: "('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c1 \<sim> c2 \<longleftrightarrow> chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2"

lemma proj_eq_equiv:
  "equiv {c. is_chain c} {(c1, c2). c1 \<sim> c2}"
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
     (if is_chain c1 \<and> is_chain c2 \<and> chain_end c1 = chain_begin c2 
      then Some (c1 @ c2) 
      else None)"

lemma proj_compose_respects_equiv:
  assumes "c1 \<sim> c1'" "c2 \<sim> c2'"
  assumes "is_chain c1" "is_chain c2"
  shows "proj_compose c1 c2 = None \<and> proj_compose c1' c2' = None \<or>
         (\<exists>c c'. proj_compose c1 c2 = Some c \<and> 
                 proj_compose c1' c2' = Some c' \<and> 
                 c \<sim> c')"
  sorry

text \<open>Define the set of projectivities for a given line k (pLoops)\<close>

definition PJ :: "'l \<Rightarrow> ('p, 'l) projectivity set" where
  "PJ k = {c. is_chain c \<and> chain_begin c = k \<and> chain_end c = k}"

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
  by (auto simp: pSpec_domain_def pSpec_range_def)

text \<open>Inverse of projectivity\<close>

fun reverse_chain :: "('p, 'l) chain \<Rightarrow> ('p, 'l) chain" where
  "reverse_chain [] = []" |
  "reverse_chain ((k, P, m) # cs) = 
     reverse_chain cs @ [(m, P, k)]"

definition proj_inverse :: "('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity" where
  "proj_inverse c = reverse_chain c"

lemma reverse_chain_begin_finish:
  assumes "is_chain c"
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
