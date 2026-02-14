theory Projectivity_New4
  imports Complex_Main "Chapter4-3" "HOL-Algebra.Group"
begin

(*
10 "sorry"s remaining
*)

section \<open>Perspectivity Spec\<close>
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

lemma pspec_domain_inverse [simp]: "pSpec_domain (pSpec_inverse s) = pSpec_range s"
  by (simp add: case_prod_unfold pSpec_domain_def pSpec_inverse_def pSpec_range_def)

lemma pspec_range_inverse[simp]: "pSpec_range (pSpec_inverse s) = pSpec_domain s"
  by (simp add: case_prod_unfold pSpec_domain_def pSpec_inverse_def pSpec_range_def)

lemma  [simp]:"pSpec_center (pSpec_inverse s) = pSpec_center s"
  by (simp add: case_prod_unfold pSpec_domain_def pSpec_center_def pSpec_inverse_def pSpec_range_def)


section \<open>Chains\<close>
text\<open>Chains, like pSpecs, are proto-projectivities: sequences of things that might represent
perspectivities. Note that to be an actual projectivity, the sequence must not be empty. \<close>


type_synonym ('p1, 'l1) chain = "('p1, 'l1) pSpec list"

fun chain_domain :: "('p, 'l) chain \<Rightarrow> 'l" where
  "chain_domain [] = undefined" |
  "chain_domain (s # _) = pSpec_domain s"

fun chain_range :: "('p, 'l) chain \<Rightarrow> 'l" where
  "chain_range [] = undefined" |
  "chain_range c = pSpec_range (last c)"

definition chain_inverse :: "('p, 'l) chain \<Rightarrow> ('p, 'l) chain" where
  "chain_inverse (s) = map pSpec_inverse (rev s)" 

lemma [simp]: "chain_domain (chain_inverse c) = chain_range c"
proof (cases "c = []")
  case True
  have f0: "chain_range c = undefined" by (simp add: True)
  have f1: "chain_inverse c = []" by (simp add: True chain_inverse_def)
  have f2: "chain_domain(chain_inverse c) = undefined" by (simp add: True chain_inverse_def)

  then show ?thesis using f0 f2 by auto
next
  case False
  obtain s ss where sfacts: "c = ss @ [s]" using False using rev_exhaust by blast
  have f0: "chain_range c = pSpec_range s" using sfacts
    by (metis False chain_domain.cases chain_range.simps(2) last_snoc)
  have f1: "chain_domain (chain_inverse c) = pSpec_domain (pSpec_inverse s)" using sfacts
    by (simp add: chain_inverse_def)
  then show ?thesis using f0 f1 pspec_domain_inverse by auto
qed

lemma [simp]: "chain_range (chain_inverse c) = chain_domain c"
proof (cases "c = []")
  case True
  have f1: "chain_inverse c = []" by (simp add: True chain_inverse_def)
  then show ?thesis   using True f1 by auto
next
  case False
  obtain s ss where sfacts: "c = s # ss " using False by (meson list.exhaust)
  have f0: "chain_domain c = pSpec_domain s" using sfacts by simp
  have f1: "chain_range (chain_inverse c) = pSpec_range (pSpec_inverse s)" using sfacts
    by (metis Nil_is_append_conv chain_inverse_def chain_range.elims last_map last_snoc 
      list.distinct(1) map_is_Nil_conv rev.simps(2))
  then show ?thesis using f0 f1 pspec_domain_inverse by auto
qed

section \<open>Perspectivities and Chains with projective geometry apparatus\<close>
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

lemma good_chain_domain [simp]:
  "is_chain_param Pts Lns inc c \<Longrightarrow> (chain_domain c) \<in> Lns"
proof -
  assume ah: "is_chain_param Pts Lns inc c"
  consider (empty) "c=[]" | (nonempty) "\<exists> s ss . c = s # ss"  
    by (metis list.exhaust)
  then show ?thesis
  proof cases
    case empty
    then show ?thesis using ah by auto
  next
    case nonempty
    obtain s ss where sfact: "c = s # ss" using nonempty by blast
    have f0: "chain_domain c = pSpec_domain s" using chain_domain.simps sfact by auto
    have f1: "is_pSpec_param Pts Lns inc s" using ah sfact is_chain_param.elims(1) by blast
    then have f2: "pSpec_domain s \<in> Lns"  
      by (metis (no_types, lifting) case_prod_unfold fst_conv is_pSpec_param.elims(2) pSpec_domain_def)

    show ?thesis using ah nonempty sfact f2 by auto
  qed
qed

lemma good_chain_range [simp]:
  "is_chain_param Pts Lns inc c \<Longrightarrow> (chain_range c) \<in> Lns"
  sorry
(*
 proof -
  assume ah: "is_chain_param Pts Lns inc c"
  consider (empty) "c=[]" | (nonempty) "\<exists> s ss . c = ss @ [s]"  by (metis append_butlast_last_id)  
  then show ?thesis
  proof cases
    case empty
    then show ?thesis using ah by auto
  next
    case nonempty
    obtain s ss where sfact: "c = ss @ [s]" using nonempty by blast
    have f0: "chain_range c = pSpec_range s" by (metis sfact chain_range.elims snoc_eq_iff_butlast)
    have f1: "is_chain_param Pts Lns inc [s]" using chain_rest_is_chain1 ah by sledgehammer
    have f1: "is_pSpec_param Pts Lns inc s" using ah sfact f0 chain_rest_is_chain1 by sledgehammer
    then have f2: "pSpec_range s \<in> Lns" 
      by (metis is_pSpec_param.simps pSpec_range_def prod_cases3 split_conv)

    show ?thesis using ah nonempty sfact f2 f0 by argo
    thm is_chain_param.simps

  qed
qed
*)

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

(*
primrec fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
fold_Nil:  "fold f [] = id" |
fold_Cons: "fold f (x # xs) = fold f xs \<circ> f x"
*)

definition realization_param2 :: (* convert projectivity spec to function from beginning to ending line *)
  "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'l \<Rightarrow> 'p) \<Rightarrow> 
   ('p, 'l) chain \<Rightarrow> ('p \<Rightarrow> 'p)" where  "realization_param2 Pts Lns inc join_op meet_op c = 
        (if  is_chain_param Pts Lns inc c 
then fold (\<lambda> s . perspectivity_from_pSpec_param Pts Lns inc join_op meet_op s) c
        else undefined)"


section \<open>Parameterized Chain Equivalence\<close>

definition chains_equiv_param :: (* do two chain define the same line-to-line function *)
  "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'l \<Rightarrow> 'p) \<Rightarrow> 
   ('p, 'l) chain \<Rightarrow> ('p, 'l) chain \<Rightarrow> bool" where
  "chains_equiv_param Pts Lns inc join_op meet_op c1 c2 \<longleftrightarrow> (
     is_chain_param Pts Lns inc c1 \<and> 
     is_chain_param Pts Lns inc c2 \<and>
     chain_domain c1 = chain_domain c2 \<and>
     chain_range c1 = chain_range c2 \<and>
     (\<forall>Q. Q \<in> Pts \<and> inc Q (chain_domain c1) \<longrightarrow> 
          realization_param2 Pts Lns inc join_op meet_op c1 Q = 
          realization_param2 Pts Lns inc join_op meet_op c2 Q)
  )"

(* Orig:
definition chains_equiv_param :: (* do two chain define the same line-to-line function *)
  "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'l \<Rightarrow> 'p) \<Rightarrow> 
   ('p, 'l) chain \<Rightarrow> ('p, 'l) chain \<Rightarrow> bool" where
  "chains_equiv_param Pts Lns inc join_op meet_op c1 c2 \<longleftrightarrow> (
     is_chain_param Pts Lns inc c1 \<and> 
     is_chain_param Pts Lns inc c2 \<and>
     chain_domain c1 = chain_domain c2 \<and>
     chain_range c1 = chain_range c2 \<and>
     (\<forall>Q. Q \<in> Pts \<and> inc Q (chain_domain c1) \<longrightarrow> 
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

abbreviation perspectivity_from_pSpec2 :: "('p, 'l) pSpec \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "perspectivity_from_pSpec2 s \<equiv> perspectivity_from_pSpec_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) s"

definition perspectivity_from_pSpec ::  "('p, 'l) pSpec \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "perspectivity_from_pSpec  s =
     (case s of (k, P, m) \<Rightarrow>
       if is_pSpec_param Points Lines  (\<lhd>) (k, P, m)
       then (\<lambda>Q. if Q \<in> Points \<and>  Q \<lhd> k then ( P \<bar> Q) \<sqdot> m else undefined)
       else undefined)"

lemma perspectivity_from_pSpec_unfold:
  "perspectivity_from_pSpec2 (k, P, m) = 
     (if is_pSpec (k, P, m)
      then (\<lambda>Q. if Q \<in> Points \<and> Q \<lhd> k then meet (join P Q) m else undefined)
      else undefined)"
  unfolding perspectivity_from_pSpec_param_def is_pSpec_param.cases  using is_pSpec_def by auto

lemma perspectivity_from_pSpec_alt:
  "perspectivity_from_pSpec2 s = 
   (if is_pSpec s
    then (\<lambda>Q. if Q \<in> Points \<and> Q \<lhd> pSpec_domain s 
              then meet (join (pSpec_center s) Q) (pSpec_range s) 
              else undefined)
    else undefined)" 
proof -
  obtain k P m where s_def: "s = (k, P, m)" using prod_cases3 by blast
  then have f0: "perspectivity_from_pSpec2 s = perspectivity_from_pSpec2 (k, P, m)" by auto
  show ?thesis using f0 perspectivity_from_pSpec_unfold[of k P m] s_def pSpec_domain_def [of "(k,P,m)"] pSpec_range_def [of "(k,P,m)"] 
      pSpec_center_def [of "(k,P,m)"] by fastforce
qed

text \<open>Basic properties of perspectivities\<close>

lemma perspectivity_maps_correctly:
  assumes "is_pSpec s"
  assumes "Q \<in> Points" "Q \<lhd> pSpec_domain s"
  shows "perspectivity_from_pSpec2 s Q \<in> Points \<and> 
         perspectivity_from_pSpec2 s Q \<lhd> pSpec_range s"
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
  shows "perspectivity_from_pSpec2 (m, P, k) (perspectivity_from_pSpec2 (k, P, m) Q) = Q"
proof -
  let ?f = "perspectivity_from_pSpec2 (k, P, m)"
  let ?g = "perspectivity_from_pSpec2 (m, P, k)"
  
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
  assumes f_def: "f = perspectivity_from_pSpec2 (l1, Or, l2)"
  assumes g_def: "g = perspectivity_from_pSpec2 (l2, Or, l1)"
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
  assumes "perspectivity_from_pSpec2 s Q1 = perspectivity_from_pSpec2 s Q2"
  shows "Q1 = Q2"
proof -
  obtain l0 Or l2 where s_def: "s = (l0, Or, l2)"  using prod_cases3 by blast
  obtain t where t_def: "t =(l2, Or, l0)" by blast
  obtain smap where smap_def: "smap = perspectivity_from_pSpec2 s" by blast
  obtain tmap where tmap_def: "tmap = perspectivity_from_pSpec2 t" by blast
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
  shows "inj_on (perspectivity_from_pSpec2 s) D"
  by (smt (verit) assms(1,2) inj_on_def mem_Collect_eq perspectivity_injective)  (* can surely be simplified with an 'of' *)


lemma perspectivity_surjective:
  assumes "is_pSpec s"
  assumes "R \<in> Points" "R \<lhd> pSpec_range s"
  shows "\<exists>Q \<in> Points. Q \<lhd> pSpec_domain s \<and> perspectivity_from_pSpec2 s Q = R"
proof -
  obtain k P m where s_def: "s = (k, P, m)"  using prod_cases3 by blast
  obtain t where t_def: "t =(m, P, k)" by blast
  have t_good: "is_pSpec t" using assms t_def s_def is_pSpec_unfold by auto
  have tr: "pSpec_range t = k" using t_def pSpec_range_def [of "(m,P,k)"] by simp
  have td: "pSpec_domain t = m" using t_def pSpec_domain_def [of "(m,P,k)"] by simp
  have sr: "pSpec_range s = m" using s_def pSpec_range_def [of "(k,P,m)"] by simp
  have sd: "pSpec_domain s = k" using s_def pSpec_domain_def [of "(k,P,m)"] by simp
  obtain smap where smap_def: "smap = perspectivity_from_pSpec2 s" by blast
  obtain tmap where tmap_def: "tmap = perspectivity_from_pSpec2 t" by blast
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
  assumes "f = perspectivity_from_pSpec2 s"
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
  shows "bij_betw (perspectivity_from_pSpec2 s)
                  {Q \<in> Points. Q \<lhd> pSpec_domain s}
                  {R \<in> Points. R \<lhd> pSpec_range s}"
proof -
  have "perspectivity_from_pSpec2 s ` {p \<in> Points. p \<lhd> pSpec_domain s} = {p \<in> Points. p \<lhd> pSpec_range s}"
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

lemma chain_domain_in_Lines:
  "is_chain c \<Longrightarrow> chain_domain c \<in> Lines" 
  by (metis chain_domain.elims is_chain_unfold(1) chain_cons pSpec_components)

lemma chain_range_in_Lines:
  "is_chain c \<Longrightarrow> chain_range c \<in> Lines"
  by (simp add: is_chain_def)


lemma chain_append:
  assumes "is_chain c1" "is_chain c2"
  assumes "chain_range c1 = chain_domain c2"
  shows "is_chain (c1 @ c2)"
  sorry (* need induction here surely *)

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
  "realization c = realization_param2  Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c"

lemma q:
  "fold f [a] = (f a)" using fold_def by simp

lemma realization_unfold:
  "realization [] = undefined"
  "is_chain[s] \<Longrightarrow> realization [s] = perspectivity_from_pSpec2 s"
  (*  "\<lbrakk>ss \<noteq> []\<rbrakk> \<Longrightarrow> realization (s # ss) = (realization ss) \<circ> (perspectivity_from_pSpec s)" *)
proof -
  show "realization [] = undefined" 
    by (simp add: realization_def realization_param2_def)
  assume ah: "is_chain[s]"
  have "realization [s] = realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>) [s]" using realization_def[of "[s]"] by auto
  also have "... = (if is_chain_param Points Lines (\<lhd>) [s] then fold perspectivity_from_pSpec2 [s] else undefined)" 
    using realization_param2_def [of Points Lines "(\<lhd>)" "(\<bar>)" "(\<sqdot>)" "[s]"] by auto
  also have "... = fold perspectivity_from_pSpec2 [s]" using ah is_chain_def by auto
  also have "... = perspectivity_from_pSpec2 s" using fold_def q by auto
  finally show "realization [s]  = perspectivity_from_pSpec2 s" .
qed

(* Major insight here from  https://stackoverflow.com/questions/67407437/how-to-use-the-base-case-assumption-when-proving-with-induct-in-isabelle, 
namely "Any assumptions that you need to be part of the induction need to be part of the proof state when you call induct."
and "You should therefore do a using assms before the proof" (!) *)

lemma realization_domain1:
  assumes "is_chain c"
  shows "\<And> Q . Q \<in> Points \<Longrightarrow> (Q \<lhd> chain_domain c \<Longrightarrow> realization c Q \<in> Points)"
proof -
  have ne: "c \<noteq> []" using is_chain_def  using assms(1) by auto
  then show "\<And>Q. Q \<in> Points \<Longrightarrow> Q \<lhd> chain_domain c \<Longrightarrow> realization c Q \<in> Points"
    using assms proof (induction c  rule: list_nonempty_induct)
    case (single x)
    then show ?case using chain_cons perspectivity_maps_correctly realization_unfold(2) by auto
  next
    case (cons s ss)
 
    obtain t ts where tfacts:"ss = t # ts" using chain_domain.cases cons.hyps by blast
    have f0: "is_chain (t#ts) \<Longrightarrow> Q \<in> Points \<Longrightarrow> Q \<lhd> chain_domain (t#ts) \<Longrightarrow> realization (t#ts) Q \<in> Points" for Q
      using tfacts cons.IH by auto
    have f1: "is_chain (t#ts)" using cons.prems(3) chain_tail tfacts by blast
    then have f2: "U \<in> Points \<Longrightarrow> U \<lhd> chain_domain (t#ts) \<Longrightarrow> realization (t#ts) U \<in> Points" for U  using f0 by auto
    have f4: "chain_domain (t # ts) = pSpec_domain t" by auto
    then have f5: "U \<in> Points \<and> U \<lhd> pSpec_domain t \<Longrightarrow> realization (t#ts) U \<in> Points" for U using f2 by auto
    thm realization_param2_def
    thm perspectivity_from_pSpec_param_def

    have g0: "(realization (s # ss) Q) =  (realization_param2  Points Lines (\<lhd>) (\<bar>) (\<sqdot>) (s # t # ts) Q)" 
      using realization_def tfacts by auto
    then have g1: "... = (if is_chain_param Points Lines (\<lhd>)  (s # ss)
                          then fold (perspectivity_from_pSpec_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) )(s # ss)
                          else undefined) Q"  by (simp add: realization_param2_def tfacts)
    then have g2: "... =  fold (perspectivity_from_pSpec_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) )(s # ss) Q" 
      using cons.prems(3) is_chain_def tfacts by force (* OK to here *)
    then have g3: "(realization (s # ss) Q) = (realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>) (t # ts) \<circ> 
                    perspectivity_from_pSpec2 s) Q" using g0 g1 g2 
    by (metis f1 fold_Cons is_chain_def realization_param2_def tfacts) 

    then show ?case using g3 
    by (metis chain_cons chain_domain.simps(2) comp_apply cons.IH cons.prems(1,2,3) is_chain_def is_chain_param.simps(3) perspectivity_maps_correctly
        realization_def tfacts)
  qed
qed

lemma realization_domain2:
  assumes "is_chain c"
  shows "\<And> Q . Q \<in> Points \<Longrightarrow> (Q \<lhd> chain_domain c \<Longrightarrow> realization c Q \<lhd> chain_range c)"

proof -
  have c0: "c \<noteq> []" using assms is_chain_def by auto
  then show "\<And> Q . Q \<in> Points \<Longrightarrow> (Q \<lhd> chain_domain c \<Longrightarrow> realization c Q \<lhd> chain_range c)"
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
      then obtain y ys where ydef: "xs = y # ys" using chain_domain.cases by blast
      assume ah: "(\<And>R. R \<in> Points \<Longrightarrow> R \<lhd> chain_domain xs \<Longrightarrow> is_chain xs \<Longrightarrow> realization xs R \<lhd> chain_range xs)"
      show "Q \<in> Points \<Longrightarrow>  Q \<lhd> chain_domain (x # xs) \<Longrightarrow> is_chain (x # xs)
         \<Longrightarrow> is_chain c \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> realization (x # xs) Q \<lhd> chain_range (x # xs)" for Q
      proof -
        assume a0: "Q \<in> Points" and a1: "Q \<lhd> chain_domain (x # xs)" and a2: " is_chain (x # xs)"
        and a3: "is_chain c" and a4: "xs \<noteq> []"  

        have a5: "(realization (x # xs) Q) = (realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>) (xs) \<circ> perspectivity_from_pSpec2 x) Q"
          using realization_def[of "x # xs"] a4  a2 is_chain_def ydef   by (simp add: realization_def realization_param2_def)
        let ?R = "realization [x] Q"
        have "?R \<lhd> pSpec_range x"
          using a0 a1 a2 chain_cons perspectivity_maps_correctly realization_unfold(2)  by (simp add: is_chain_unfold(2))
        then have "?R \<lhd> chain_domain xs" using a2 is_chain_unfold(3) ydef by auto
        then have "realization xs ?R \<lhd> chain_range xs" 
        by (metis a0 a1 a2 a4 ah chain_cons chain_domain.simps(2) chain_tail projective_plane.is_chain_unfold(2) projective_plane.realization_domain1
            projective_plane_axioms)
        then have "realization xs ?R \<lhd> chain_range (x # xs)" by (simp add: ydef)
        then have "realization (x#xs) Q \<lhd> chain_range (x # xs)" using a5 
          using a2 chain_cons is_chain_unfold(2) realization_def realization_unfold(2) by auto
        then show ?thesis by auto
      qed
    qed
  qed
qed

(* the following is just called "fold_append" *)
lemma q2:
  "a \<noteq> [] \<Longrightarrow> b \<noteq> [] \<Longrightarrow> fold f (a @ b) = (fold f b) \<circ> (fold f a)" 
  using fold_append by blast

lemma realization_move:
  assumes "c1 = [u]"
  assumes "is_chain c1" "is_chain c2"
  assumes "chain_range c1 = chain_domain c2"
  shows "realization (c1 @ c2) = (realization c2) \<circ> (realization c1)" using is_chain_def fold_append
  by (smt (verit, del_insts) append_Cons assms(1,2,3,4) chain_cons chain_domain.elims chain_range.elims is_chain_unfold(3) last_snoc
      realization_def realization_param2_def self_append_conv2)


lemma realization_append:
  assumes "is_chain c1" "is_chain c2"
  assumes "chain_range c1 = chain_domain c2"
  shows "realization (c1 @ c2) = (realization c2) \<circ> (realization c1)" using chain_append[of c1 c2] 
    by (metis assms(1,2,3) fold_append is_chain_def realization_def realization_param2_def)

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
     chain_domain c1 = chain_domain c2 \<and>
     chain_range c1 = chain_range c2 \<and>
      (\<forall>Q. Q \<in> Pts \<and> inc Q (chain_domain c1) \<longrightarrow> 
          realization_param Pts Lns inc join_op meet_op c1 Q = 
          realization_param Pts Lns inc join_op meet_op c2 Q)
  )"
*)
lemma chains_equiv_unfold1:
  "c1 \<simeq> c2 \<Longrightarrow> (
     is_chain c1 \<and> is_chain c2 \<and>
     chain_domain c1 = chain_domain c2 \<and>
     chain_range c1 = chain_range c2 \<and>
     (\<forall>Q. Q \<in> Points \<longrightarrow> Q \<lhd> chain_domain c1 \<longrightarrow> realization c1 Q = realization c2 Q)
  )"
proof (safe)
  show f1: "c1 \<simeq> c2 \<Longrightarrow> is_chain c1" by (simp add: chains_equiv_param_def is_chain_def)
  show f2: "c1 \<simeq> c2 \<Longrightarrow> is_chain c2" by (simp add: chains_equiv_param_def is_chain_def)
  show f3: "c1 \<simeq> c2 \<Longrightarrow> (chain_domain c1 = chain_domain c2)" by (simp add: chains_equiv_param_def is_chain_def)
  show f4: "c1 \<simeq> c2 \<Longrightarrow> (chain_range c1 = chain_range c2)" by (simp add: chains_equiv_param_def is_chain_def)
  show f5: "\<And>Q. c1 \<simeq> c2 \<Longrightarrow> Q \<in> Points \<Longrightarrow> Q \<lhd> chain_domain c1 \<Longrightarrow> (realization c1 Q = realization c2 Q)"
    by (simp add: chains_equiv_param_def realization_def)
qed

lemma chains_equiv_unfold2:
  "(
     is_chain c1 \<and> is_chain c2 \<and>
     chain_domain c1 = chain_domain c2 \<and>
     chain_range c1 = chain_range c2 \<and>
     (\<forall>Q. Q \<in> Points \<longrightarrow> Q \<lhd> chain_domain c1 \<longrightarrow> realization c1 Q = realization c2 Q)
  ) \<Longrightarrow> c1 \<simeq> c2"
proof -
  assume ah: "is_chain c1 \<and>
    is_chain c2 \<and>
    chain_domain c1 = chain_domain c2 \<and>
    chain_range c1 = chain_range c2 \<and> (\<forall>Q. Q \<in> Points \<longrightarrow> Q \<lhd> chain_domain c1 \<longrightarrow> realization c1 Q= realization c2 Q)"

  have "(c1 \<simeq> c2) \<equiv> chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2" by simp
  then have "... = (
     is_chain_param Points Lines (\<lhd>) c1 \<and> 
     is_chain_param Points Lines (\<lhd>) c2 \<and>
     chain_domain c1 = chain_domain c2 \<and>
     chain_range c1 = chain_range c2 \<and>
     (\<forall>Q. Q \<in> Points \<and> (\<lhd>) Q (chain_domain c1) \<longrightarrow> 
          realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>)  c1 Q = 
          realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>)  c2 Q))"  by (simp add: chains_equiv_param_def)
  then have "... = (is_chain c1 \<and> is_chain c2 \<and>
     chain_domain c1 = chain_domain c2 \<and>
     chain_range c1 = chain_range c2 \<and>
     (\<forall>Q. Q \<in> Points \<and> (\<lhd>) Q (chain_domain c1) \<longrightarrow> 
          realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>)  c1 Q = 
          realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>)  c2 Q))" by (simp add: is_chain_def)
  then have h: "... = (is_chain c1 \<and> is_chain c2 \<and>
     chain_domain c1 = chain_domain c2 \<and>
     chain_range c1 = chain_range c2 \<and>
     (\<forall>Q. Q \<in> Points \<and> (\<lhd>) Q (chain_domain c1) \<longrightarrow> 
          realization c1 Q = 
          realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>)  c2 Q))" 
    using realization_def by auto
  then show ?thesis 
  using
    \<open>(c1 \<simeq> c2) = (is_chain_param Points Lines (\<lhd>) c1 \<and> is_chain_param Points Lines (\<lhd>) c2 \<and> chain_domain c1 = chain_domain c2 \<and> chain_range c1 = chain_range c2 \<and> (\<forall>Q. Q \<in> Points \<and> Q \<lhd> chain_domain c1 \<longrightarrow> realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 Q = realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c2 Q))\<close>
    ah is_chain_def realization_def by auto
qed


lemma chains_equiv_refl:
  assumes "is_chain c"
  shows "c \<simeq> c"
  using assms chains_equiv_unfold2 by auto

lemma chains_equiv_sym:
  assumes "c1 \<simeq> c2"
  shows "c2 \<simeq> c1"
  using assms chains_equiv_unfold1 chains_equiv_unfold2 by metis

lemma chains_equiv_trans:
  assumes "c1 \<simeq> c2" "c2 \<simeq> c3"
  shows "c1 \<simeq> c3"
  using assms by (simp add: chains_equiv_param_def)

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
  using chains_equiv_param_def by blast

lemma chains_equiv_is_equiv:
  "equiv {c. is_chain c} {(c1, c2). c1 \<simeq> c2}"
  using chains_equiv_param_is_equiv_in_locale by (simp add: is_chain_def)

text \<open>Identity perspectivity example\<close>

lemma identity_perspectivity:
  assumes "is_pSpec (m, P, m)"
  assumes "Q \<in> Points" "Q \<lhd> m"
  shows "perspectivity_from_pSpec (m, P, m) Q = Q"
  using assms join_properties1 meet_properties2 unique_meet 
  by (smt (verit, ccfv_SIG) is_pSpec_def is_pSpec_param.simps old.prod.case perspectivity_from_pSpec_def)

lemma chain_extend_with_identity:
  assumes "is_pSpec (k, P, m)"
  assumes "is_pSpec (m, P, m)"
  shows "[(k, P, m)] \<simeq> [(k, P, m), (m, P, m)]"
proof -
  show "chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) [(k, P, m)] [(k, P, m), (m, P, m)]"
    unfolding chains_equiv_param_def 
  proof -
    have f0: "is_chain_param Points Lines (\<lhd>) [(k, P, m)]" using assms  by (simp add: is_pSpec_def)
    have f1: "is_chain_param Points Lines (\<lhd>) [(m, P, m)]" using assms using is_pSpec_def by auto
    have f2: "is_chain_param Points Lines (\<lhd>) [(k, P, m), (m, P, m)]" 
      using f0 f1 assms is_chain_param.simps(3)[of Points Lines "(\<lhd>)" "(k, P, m)" "(m, P, m)" "[]"] 
      by (simp add: pSpec_domain_def pSpec_range_def)
    have f3: "chain_domain [(k, P, m)] = chain_domain [(k, P, m), (m, P, m)]" using chain_domain.simps by auto
    have f4: "chain_range [(k, P, m)] = chain_range [(k, P, m), (m, P, m)]" 
      using chain_range.simps(2) [of "(k,P,m)" "[]"] pSpec_range_def[of "(k, P, m)"] by (simp add: pSpec_range_def)
    have f5: "(\<forall>Q. Q \<in> Points \<and> Q \<lhd> chain_domain [(k, P, m)] \<longrightarrow>
         realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>) [(k, P, m)] Q = realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>) [(k, P, m), (m, P, m)] Q)"
    proof (clarsimp)
      fix Q
      assume a1: "Q \<in> Points" and a2: "Q \<lhd> pSpec_domain (k, P, m)"
      show "realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>) [(k, P, m)] Q = realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>) [(k, P, m), (m, P, m)] Q"
        unfolding realization_param2_def
      proof -
        have g0: "(if is_chain_param Points Lines (\<lhd>) [(k, P, m)] then fold perspectivity_from_pSpec2 [(k, P, m)] else undefined) Q = 
          fold perspectivity_from_pSpec2 [(k, P, m)] Q" using f0 by auto
        also have g1: "... = (perspectivity_from_pSpec2 (k, P, m)) Q" by auto
        finally have  g2: "(if is_chain_param Points Lines (\<lhd>) [(k, P, m)] then fold perspectivity_from_pSpec2 [(k, P, m)] else undefined) Q =
          (perspectivity_from_pSpec2 (k, P, m)) Q" by auto
        have ka: "Q \<lhd> k" using a2 by (simp add: pSpec_domain_def)
        have k0: "((perspectivity_from_pSpec2 (k, P, m)) Q) \<in> Points"  using a1 a2 assms(1) perspectivity_maps_correctly by blast

        then have k1: "((perspectivity_from_pSpec2 (k, P, m)) Q) = perspectivity_from_pSpec_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) (k, P, m) Q" by auto
        also have k2: "... =  (if is_pSpec_param Points Lines (\<lhd>) (k, P, m)
                               then (\<lambda>Q. (if Q \<in> Points \<and> (\<lhd>) Q k then (\<sqdot>) ((\<bar>) P Q) m else undefined)) 
                               else undefined) Q" by (simp add: perspectivity_from_pSpec_param_def)
        also have k3: "... =  (\<lambda>Q. (if Q \<in> Points \<and> (\<lhd>) Q k then (\<sqdot>) ((\<bar>) P Q) m else undefined))  Q" using f2 by auto
        also have k4: "... =  (\<lambda>Q.  (\<sqdot>) ((\<bar>) P Q) m)  Q" using a1 a2 pSpec_domain_def ka by auto
        finally have k5: "(perspectivity_from_pSpec2 (k, P, m)) Q =  (\<lambda>Q.  (\<sqdot>) ((\<bar>) P Q) m)  Q" using k2 k3 k4 by argo
        
        then have k6: "((perspectivity_from_pSpec2 (k, P, m)) Q) \<lhd> m" 
          by (metis a1 assms(1) is_pSpec_unfold join_properties1 ka meet_properties2)



        have h0: "(if is_chain_param Points Lines (\<lhd>) [(k, P, m), (m, P, m)] then fold perspectivity_from_pSpec2 [(k, P, m), (m, P, m)] else undefined) Q =
          fold perspectivity_from_pSpec2 [(k, P, m), (m, P, m)] Q" using f2 by auto
        have h1: "... = ((perspectivity_from_pSpec2 (m, P, m)) \<circ> (perspectivity_from_pSpec2 (k, P, m))) Q" by auto
        have h2: "... = (perspectivity_from_pSpec2 (m, P, m))  ((perspectivity_from_pSpec2 (k, P, m)) Q)" by auto
        have h3: "... =   ((perspectivity_from_pSpec2 (k, P, m)) Q)" using k0 k1 k2 k3 k4 k5 k6 identity_perspectivity[of m P]  
          by (simp add: assms(2) perspectivity_from_pSpec_def perspectivity_from_pSpec_param_def)
        show "(if is_chain_param Points Lines (\<lhd>) [(k, P, m)] then fold perspectivity_from_pSpec2 [(k, P, m)] else undefined) Q =
    (if is_chain_param Points Lines (\<lhd>) [(k, P, m), (m, P, m)] then fold perspectivity_from_pSpec2 [(k, P, m), (m, P, m)] else undefined) Q " using 
f0 f1 f2 f3 f4 g0 g1 k0 k1 h0 h1 h2 h3 by auto
      qed
    qed
    show "is_chain_param Points Lines (\<lhd>) [(k, P, m)] \<and>
    is_chain_param Points Lines (\<lhd>) [(k, P, m), (m, P, m)] \<and>
    chain_domain [(k, P, m)] = chain_domain [(k, P, m), (m, P, m)] \<and>
    chain_range [(k, P, m)] = chain_range [(k, P, m), (m, P, m)] \<and>
    (\<forall>Q. Q \<in> Points \<and> Q \<lhd> chain_domain [(k, P, m)] \<longrightarrow>
         realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>) [(k, P, m)] Q = realization_param2 Points Lines (\<lhd>) (\<bar>) (\<sqdot>) [(k, P, m), (m, P, m)] Q) "
      using f2 f4 f5 by force
  qed
qed

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
  unfolding projectivity_class_def by blast

text \<open>A projectivity is represented by any member of its equivalence class\<close>

type_synonym ('p1, 'l1) projectivity = "('p1, 'l1) chain"

text \<open>Two projectivities are equal if they're in the same equivalence class\<close>

definition proj_eq :: "('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c1 \<sim> c2 \<longleftrightarrow> chains_equiv_param Points Lines (\<lhd>) (\<bar>) (\<sqdot>) c1 c2"

lemma proj_eq_equiv:
  "equiv {c. is_chain c} {(c1, c2). c1 \<sim> c2}" 
  by (simp add: chains_equiv_is_equiv proj_eq_def)

text \<open>Define operations on projectivities\<close>

definition proj_domain :: "('p, 'l) projectivity \<Rightarrow> 'l" where
  "proj_domain c = chain_domain c"

definition proj_range :: "('p, 'l) projectivity \<Rightarrow> 'l" where
  "proj_range c = chain_range c"

lemma proj_domain_respects_equiv:
  assumes "c1 \<sim> c2"
  shows "proj_domain c1 = proj_domain c2"
    by (metis assms chains_equiv_param_def proj_domain_def proj_eq_def)
  
lemma proj_range_respects_equiv:
  assumes "c1 \<sim> c2"
  shows "proj_range c1 = proj_range c2" 
    using assms chains_equiv_unfold1 proj_eq_def proj_range_def by auto
  
text \<open>Define composition of projectivities (when compatible)\<close>

definition proj_compose :: "('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity option" where
  "proj_compose c1 c2 = 
     (if is_chain c1 \<and> is_chain c2 \<and> chain_range c1 = chain_domain c2 
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
  "PJ k = {c. is_chain c \<and> chain_domain c = k \<and> chain_range c = k}"

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
proof -
  have f0: "(if k \<in> Lines \<and> P \<in> Points \<and> \<not> P \<lhd> k \<and> is_pSpec (k, P, k) then [(k, P, k)] else undefined) =
 [(k, P, k)]"  using assms by auto
  have f1: "is_chain [(k, P, k)]" using assms  by (simp add: is_chain_unfold(2))
  have f2: "chain_domain [(k, P, k)] = k" using assms f1 by (simp add: pSpec_domain_def)
  have f3: "chain_range [(k, P, k)] = k" using assms f1 f2
    by (metis chain_domain.simps(2) chain_extend_with_identity chain_range.simps(2) chains_equiv_unfold1 is_chain_unfold(3) last.simps)
  show "(if k \<in> Lines \<and> P \<in> Points \<and> \<not> P \<lhd> k \<and> is_pSpec (k, P, k) then [(k, P, k)] else undefined)
    \<in> {c. is_chain c \<and> chain_domain c = k \<and> chain_range c = k} " using f0 f1 f2 f3 by auto
qed

text \<open>Inverse of projectivity\<close>

fun reverse_chain :: "('p, 'l) chain \<Rightarrow> ('p, 'l) chain" where
  "reverse_chain [] = []" |
  "reverse_chain ((k, P, m) # cs) = 
     reverse_chain cs @ [(m, P, k)]"

definition proj_inverse :: "('p, 'l) projectivity \<Rightarrow> ('p, 'l) projectivity" where
  "proj_inverse c = reverse_chain c"

lemma reverse_chain_is_chain:
  assumes "is_chain c"
  shows "is_chain (reverse_chain c)" sorry

lemma reverse_chain_domain_finish:
  assumes "is_chain c"
  shows "chain_domain (reverse_chain c) = chain_range c \<and>
         chain_range (reverse_chain c) = chain_domain c"
  sorry

lemma proj_inverse_in_PJ:
  assumes "c \<in> PJ k"
  shows "proj_inverse c \<in> PJ k"
  using assms reverse_chain_domain_finish [of c]
  unfolding proj_inverse_def PJ_def using reverse_chain_is_chain by auto


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
