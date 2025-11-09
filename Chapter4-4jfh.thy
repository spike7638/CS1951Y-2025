theory "Chapter4-4jfh"
  imports Complex_Main  "Chapter4-3" "HOL-Algebra.Group"
begin

context projective_plane
begin
text\<open> start at "Perspectivies and Projectivities" and go to end of chapter\<close>

type_synonym ('p1, 'l1) persp_data = "('p1 \<times> 'l1 \<times> 'l1)"

fun is_persp_data :: "('p, 'l) persp_data \<Rightarrow> bool" 
  where "is_persp_data (Or, l1, l2) = (Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> 
  \<not> (Or \<lhd> l1) \<and> \<not> (Or \<lhd> l2))"

fun perspectivity :: "('p, 'l) persp_data \<Rightarrow> ('p \<Rightarrow> 'p)"
  where "perspectivity (Or, l1, l2) = (if is_persp_data (Or, l1, l2)
  then (\<lambda>P . if P \<in> Points \<and> P \<lhd> l1 then (meet (join Or P) l2) else undefined) else undefined)"

lemma  persp_data_sym [sym]: 
  "is_persp_data (Or, l1, l2) \<Longrightarrow> is_persp_data (Or, l2, l1)"
  by simp 

lemma perspectivity_nice: 
  fixes Or P l1 l2
  assumes "P \<in> Points \<and>  P \<lhd> l1"
  assumes "is_persp_data (Or, l1, l2)"
  shows "(perspectivity (Or, l1, l2) P) \<in> Points \<and> (perspectivity (Or, l1, l2) P) \<lhd> l2"
proof -
  have ss: "((perspectivity (Or, l1, l2) P) \<in> Points) \<equiv> ((Or \<bar> P \<sqdot> l2)  \<in> Points)" 
    using assms assms by auto
  have st: "(Or \<bar> P \<sqdot> l2)  \<in> Points" using meet_properties2 join_properties1 join_properties2 is_persp_data.simps
    by (metis assms(1,2))
  have su: "(Or \<bar> P \<sqdot> l2) \<lhd> l2" 
    using meet_properties2 join_properties1[of Or P] assms is_persp_data.simps by auto
  show ?thesis using ss st su perspectivity.simps assms by auto
qed

lemma perspectivity_nice2: 
  fixes Or l1 l2
  assumes "(perspectivity (Or, l1, l2)) \<noteq> undefined"
  shows "is_persp_data (Or, l1, l2)"
proof (rule ccontr)
  assume ch: "\<not> is_persp_data (Or, l1, l2)"
  show False using assms ch perspectivity.simps by auto
qed

(*
lemma perspectivity_nice3: 
  fixes Or l1 l2 
  assumes "\<forall> P . ((P \<in> Points \<and>  P \<lhd> l1) \<longrightarrow> (perspectivity Or l1 l2) P \<noteq> undefined)" 
  shows "is_persp_data Or l1 l2"
proof (rule ccontr)
  assume ch: "\<not> is_persp_data Or l1 l2"
  show False using assms ch perspectivity_def by sledgehammer
qed*)

lemma inverse_persp:
  fixes f Or l1 l2  Q
  assumes data_def: "is_persp_data (Or, l1, l2)"
  assumes f_def: "f = perspectivity (Or, l1, l2)"
  assumes g_def: "g = perspectivity (Or, l2, l1)"
  assumes Q_facts: "Q \<in> Points \<and> Q \<lhd> l1"
  shows "(g (f Q)) = Q"
proof -
  have f2: "(f Q) = (Or \<bar> Q) \<sqdot> l2" unfolding f_def g_def perspectivity.simps using assms by auto
  then have fQnice: "(f Q) \<in> Points \<and> (f Q) \<lhd> l2" unfolding f_def using perspectivity_nice [of Q l1 Or l2] Q_facts data_def by auto
  have gdata_def: "is_persp_data (Or, l2, l1)" using data_def is_persp_data.simps by blast
  have g1: "g (f Q) = (Or \<bar> (f Q)) \<sqdot> l1"
    unfolding f_def g_def perspectivity.simps using fQnice f2 Q_facts gdata_def assms by auto
  then have "g (f Q) = (Or \<bar> ((Or \<bar> Q) \<sqdot> l2)) \<sqdot> l1" using f2 by auto
  then show ?thesis 
    by (smt (verit) Q_facts data_def is_persp_data.simps join_properties1 meet_properties2 unique_meet)
qed

lemma perspectivity_inj:
  fixes f Or l1 l2 P Q
  assumes data_def: "is_persp_data (Or, l1, l2)"
  assumes f_def: "f = perspectivity (Or, l1, l2)"
  assumes P_fact: "P \<in> Points \<and> P \<lhd> l1"
  assumes Q_fact: "Q \<in> Points \<and> Q \<lhd> l1"
  assumes equal_image: "f P = f Q"
  shows "P = Q"
  using inverse_persp by (metis P_fact Q_fact data_def equal_image f_def)

lemma perspectivity_surj:
  fixes f Or l1 l2 Q
  assumes data_def: "is_persp_data (Or, l1, l2)"
  assumes f_def: "f = perspectivity (Or, l1, l2)"
  assumes Q_facts: "Q \<in> Points \<and> Q \<lhd> l2"
  shows "\<exists> P . P \<in> Points \<and> P \<lhd> l1 \<and> f P = Q"
  using inverse_persp assms by (meson persp_data_sym perspectivity_nice)

lemma perspectivity_bij:
  fixes f Or l1 l2
  assumes data_def: "is_persp_data (Or, l1, l2)"
  assumes f_def: "f = perspectivity (Or, l1, l2)"
  shows "bij_betw f {P \<in> Points. P \<lhd> l1} {Q \<in> Points. Q \<lhd> l2}"
proof -
  have inj: "inj_on f {P \<in> Points. P \<lhd> l1}" 
    using perspectivity_inj assms inj_on_def by (smt (verit, best)
    mem_Collect_eq)

  have surj: "f ` {P \<in> Points. P \<lhd> l1} = {Q \<in> Points. Q \<lhd> l2}"
  proof
    show "f ` {P \<in> Points. P \<lhd> l1} \<subseteq> {Q \<in> Points. Q \<lhd> l2}" 
      using perspectivity_nice data_def f_def by blast
  next
    show "{Q \<in> Points. Q \<lhd> l2} \<subseteq> f ` {P \<in> Points. P \<lhd> l1}"
    proof
      fix x assume "x \<in> {Q \<in> Points. Q \<lhd> l2}"
      then have h: "x \<in> Points \<and> x \<lhd> l2"
        using mem_Collect_eq by auto

      from h obtain P where "P \<in> Points \<and> P \<lhd> l1 \<and> f P = x"
        using perspectivity_surj assms by blast

      thus "x \<in> f ` {P \<in> Points. P \<lhd> l1}"
        by blast
    qed
  qed
  show ?thesis
    using inj surj bij_betw_def by blast
qed


lemma perspectivity_of_meet_is_itself:
  fixes f Or l1 l2 P
  assumes data_def: "is_persp_data (Or, l1, l2)"
  assumes f_def: "f = perspectivity (Or, l1, l2)"
  assumes P_def: "P \<in> Points \<and> P \<lhd> l1"
  assumes P_on_l2: "P \<lhd> l2"
  shows "f P = P"
proof-
  have h1: "f = (\<lambda>P . if P \<in> Points \<and> P \<lhd> l1 then (meet (join Or P) l2) else undefined)"
    using data_def f_def perspectivity.simps by presburger
  have h2: "f P = (meet (join Or P) l2)" using h1 P_def by auto
  have h3: "(meet (join Or P) l2) = P" 
    using P_on_l2 P_def data_def is_persp_data.simps join_properties1 meet_properties2 unique_meet
    by metis
  show ?thesis using h2 h3 by auto
qed


(*
definition is_proj_data :: "'p list \<Rightarrow> 'l list \<Rightarrow> bool" 
  where "is_proj_data ps ls  = True"

fun projectivity2 :: "'p list \<Rightarrow> 'l list \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "projectivity2 ps ls = (if is_proj_data ps ls then () else undefined)"*)


(*
  "projectivity2 (Cons p []) (Cons l1 (Cons l2 [])) = (perspectivity p l1 l2)" |
  "projectivity2 (Cons p ps) (Cons l1 (Cons l2 ls)) = (projectivity ps (Cons l2 ls)) \<circ> (perspectivity p l1 l2)" |
  "projectivity2 [] b = undefined" |
  "projectivity2 a [] = undefined" |
  "projectivity2 a [v] = undefined"


definition perspectivity :: "'p \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> ('p \<Rightarrow> 'p)"
  where "perspectivity Or l1 l2 = (if is_persp_data Or l1 l2
  then (\<lambda>P . if P \<in> Points \<and> P \<lhd> l1 then (meet (join Or P) l2) else undefined) else undefined)"
*)

(* Definition. A projectivity is a mapping of one line l into another l\<Zprime> (which may be equal to l), which can be expressed as a composition of perspectivities. 
We write l Z l\<Zprime>, and write ABC . . . Z A\<Zprime>B\<Zprime>C\<Zprime> . . . if the projectivity that takes  points A, B, C, . . . into A\<Zprime>, B\<Zprime>, C\<Zprime>, . . . respectively. 
Note that a projectivity also is always one-to-one and onto. *)

(*datatype ('l1, 'p1, 'l2) persp_data = Line 'l1*)

type_synonym ('d) proj_data = "'d list"

fun is_proj_data :: "(('p, 'l) persp_data) proj_data \<Rightarrow> bool" where
  "is_proj_data (Cons d []) = (is_persp_data d)" |
  "is_proj_data (Cons (Or, l1, l2) (Cons (Or', l1', l2') ds)) = 
    (is_persp_data (Or, l1, l2) \<and> l2 = l1' \<and> is_proj_data (Cons (Or', l1', l2') ds))" |
  "is_proj_data [] = False"

fun projectivity :: "(('p, 'l) persp_data) proj_data \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "projectivity (Cons d []) = (perspectivity d)" |
  "projectivity (Cons d ds) = (projectivity ds) \<circ> (perspectivity d)" |
  "projectivity [] = (\<lambda> Q . Q)"

lemma projectivity_nice: 
  fixes ds P
 (*  assumes "last ((Or, l1, l2) # ds) = (Or', l1', l2')" *)
  shows "is_proj_data ds \<Longrightarrow> P \<in> Points \<and> P \<lhd> (fst (snd (hd ds))) \<Longrightarrow>
        projectivity ds P \<in> Points \<and> 
        projectivity ds P \<lhd> (snd (snd (last ds)))"
proof (induction ds)
  case Nil
  then have "False" using Nil.prems(1) is_proj_data.simps(3) by auto
  then show ?case by auto
next
  case (Cons a qs)
  show ?case sorry
  (*proof (clarsimp)
    have p1:"(qs = [] \<longrightarrow> perspectivity a P \<in> Points \<and> perspectivity a P \<lhd> snd (snd a))"
      by (smt (z3) Cons.prems(1,2) fst_conv is_persp_data.elims(2) is_persp_data.simps is_proj_data.simps(1)
        list.sel(1) perspectivity.simps perspectivity.simps perspectivity_nice snd_conv)
    have p2: "(qs \<noteq> [] \<longrightarrow>
      projectivity (a # qs) P \<in> Points \<and> projectivity (a # qs) P \<lhd> snd (snd (last qs)))"
    proof -
      have "projectivity (a # qs) P = ((projectivity qs) \<circ> (perspectivity a)) P"
        by (smt (verit, ccfv_threshold) fun.map_ident_strong projectivity.cases
          projectivity.simps(1,2,3))
      also have "... = (projectivity qs) ((perspectivity a) P)" by auto
      finally have "projectivity (a # qs) P = (projectivity qs) ((perspectivity a) P)" .
      have "((perspectivity a P) \<in> Points) \<and> ((perspectivity a P) \<lhd> fst (snd (hd qs)))"
        using \<open>is_proj_data (a # qs)\<close> sorry
      show ?thesis sorry
    qed
    then show ?case sorry
  qed
  show ?thesis sorry
    (*then show "(qs = [] \<longrightarrow> perspectivity a P \<in> Points \<and> perspectivity a P \<lhd> snd (snd a)) \<and>
    (qs \<noteq> [] \<longrightarrow>
     projectivity (a # qs) P \<in> Points \<and> projectivity (a # qs) P \<lhd> snd (snd (last qs)))" using p1 p2 by blast*)*)
qed

(* This is the old proof. Can delete when the one above^ is fixed.
proof -
  have "projectivity ((Or, l1, l2) # []) P \<in> Points \<and> 
         projectivity ((Or, l1, l2) # []) P \<lhd> l2'" sorry
  assume "projectivity ((Or, l1, l2) # qs) P \<in> Points \<and> 
         projectivity ((Or, l1, l2) # qs) P \<lhd> l2'"
  have "projectivity ((Or, l1, l2) # (a#qs)) P \<in> Points \<and> 
         projectivity ((Or, l1, l2) # (a#qs)) P \<lhd> l2'" sorry

  show ?thesis by sledgehammer
  case Nil
  have False by sledgehammer
  then have "(Or, l1, l2) # ds = Nil" by sledgehammer
  then have "ds = Nil" using Nil by sledgehammer
  then have 
    by sledgehammer
  then show ?case sorry
next
  case (Cons a ds)
  then show ?case sorry
qed*)


(* Need to write a working comp function
fun comp :: "(('p, 'l) persp_data) proj_data \<Rightarrow> (('p, 'l) persp_data) proj_data \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "comp 

fun composition :: "'p list \<Rightarrow> 'l list \<Rightarrow> 'p list \<Rightarrow> 'l list \<Rightarrow> ('p \<Rightarrow> 'p)"
  where "composition ps ls ps' ls' = (if projectivity ps ls \<noteq> undefined \<and> projectivity ps' ls' \<noteq> undefined \<and>
  last ls = hd ls' then projectivity (ps @ ps') (ls @ (tl ls')) else undefined)"

fun composition :: "(('p \<Rightarrow> 'p)) \<Rightarrow> (('p \<Rightarrow> 'p)) \<Rightarrow> ('p \<Rightarrow> 'p)"
  where "composition (projectivity ps ls) (projectivity ps' ls') = (if last ls = hd ls' then
  projectivity (ps @ ps') (ls @ (tl ls')) else undefined)"

fun composition :: "(('p \<Rightarrow> 'p)) \<Rightarrow> (('p \<Rightarrow> 'p)) \<Rightarrow> ('p \<Rightarrow> 'p)"
  where "composition f f' = (if \<exists> ps ls ps' ls' . f = projectivity ps ls \<and> f \<noteq> undefined \<and> 
  f' = projectivity ps' ls' \<and> f' \<noteq> undefined \<and> last ls = hd ls' then
  projectivity (ps @ ps') (ls @ (tl ls')) else undefined)"
*)

fun projectivity :: "(('p, 'l) persp_data) proj_data \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "projectivity (Cons d []) = (perspectivity d)" |
  "projectivity (Cons d ds) = (projectivity ds) \<circ> (perspectivity d)" |
  "projectivity [] = (\<lambda> Q . Q)"

lemma proj_composition_is_proj:
  fixes ps ps' ls ls' f f'
  assumes f_def: "f = projectivity ps ls"
  assumes f'_def: "f' = projectivity ps' ls'"
  assumes ls_ls'_def: "last ls = hd ls'"
  shows "f' \<circ> f = projectivity (ps @ ps') (ls @ (tl ls'))"
  sorry

definition PJ :: "'l \<Rightarrow> (('p \<Rightarrow> 'p) monoid)" 
  where "PJ l = (if (l \<in> Lines) then
  \<lparr>carrier = {f . \<exists> ps . \<exists> ls . (f = projectivity ps ls) \<and> (hd ls = l) \<and> (last ls = l)},
  monoid.mult = (\<circ>),
  one = (\<lambda>P. if P \<in> Points \<and> P \<lhd> l then P else undefined)\<rparr> 
  else undefined)"

lemma PJ_carrier [simp]:
  fixes l
  assumes "l \<in> Lines"
  shows "carrier (PJ l) = {f . \<exists> ps . \<exists> ls . 
                            (f = projectivity ps ls) \<and> (hd ls = l) \<and> (last ls = l)}"
  using PJ_def assms by auto

lemma PJ_mult [simp]:
  fixes l
  fixes f g :: "'p \<Rightarrow> 'p"
  assumes "l \<in> Lines"
  shows "monoid.mult (PJ l) f g = f \<circ> g" 
  unfolding PJ_def using assms by auto

lemma PJ_one [simp]:
  fixes l
  assumes "l \<in> Lines"
  shows "one (PJ l) = (\<lambda>P. if P \<in> Points \<and> P \<lhd> l then P else undefined)" 
  unfolding PJ_def using assms by auto

lemma unique_meet:
  fixes Or l P
  assumes "l \<in> Lines"
  assumes "Or \<in> Points \<and> \<not> Or \<lhd> l"
  assumes "P \<in> Points \<and> P \<lhd> l"
  shows "meet (join Or P) l = P"
  sorry

(*
lemma
  fixes l
  assumes l_def "l \<in> Lines"
  shows PJ_inv [simp]: "A  \<in> carrier (PJ l) \<Longrightarrow> inv\<^bsub>(PJ l)\<^esub> A = matrix_inv A"
*)
lemma
  fixes l
  assumes "l \<in> Lines"
  shows PJ_group: "group (PJ l)"
proof -
  show "group (PJ l)"
  proof (unfold_locales, goal_cases)
    case (1 f g)
    obtain ps ls where f_proj: "f = projectivity ps ls" and "hd ls = l" and "last ls = l" 
      using "1"(1) assms by auto
    obtain ps' ls' where g_proj: "g = projectivity ps' ls' \<and> hd ls' = l \<and> last ls' = l" 
      using "1"(2) assms by auto
    have h1: "f \<circ> g = projectivity (ps' @ ps) (ls' @ (tl ls))" 
      using f_proj g_proj proj_composition_is_proj by auto
    have "ls = (Cons l (tl ls))" using \<open>hd ls = l\<close>
    proof (cases ls)
      case Nil
      have "hd [] = undefined" by (simp add: hd_def)
      then have False using \<open>ls = []\<close> \<open>hd ls = l\<close>
      then show ?thesis sorry
    next
      case (Cons a list)
      then show ?thesis using \<open>hd ls = l\<close> by auto
    qed
    have "hd (ls' @ (tl ls)) = hd ls'" sorry
    have "hd (ls' @ (tl ls)) = l \<and> last (ls' @ (tl ls)) = l" using f_proj g_proj sorry
    then show ?case using f_proj g_proj unfolding PJ_def sorry
  next
    thm proj_composition_is_proj
    case (2)
    show ?case using assms by auto
  next
    case 3
    obtain Or where Or_def: "Or \<in> Points \<and> \<not> Or \<lhd> l" using p3 pcollinear_def assms by fastforce
    let ?f = "perspectivity Or l l"
    have h1a: "?f = projectivity (Cons Or []) (Cons l (Cons l []))" by auto
    have h1b: "\<exists> ps . \<exists> ls . (?f = projectivity ps ls) \<and> (hd ls = l) \<and> (last ls = l)"
      using h1a by (metis last.simps list.sel(1))
    have h1c: "?f \<in> carrier (PJ l)" using h1a h1b assms by auto

    have h2: "P \<in> Points \<and> P \<lhd> l \<longrightarrow> meet (join Or P) l = P" for P 
      using unique_meet Or_def assms by auto
    have h3: "P \<in> Points \<and> P \<lhd> l \<longrightarrow> ?f P = P" for P 
      using Or_def assms is_persp_data.simps perspectivity_of_meet_is_itself by auto
    have h4: "\<not>(P \<in> Points \<and> P \<lhd> l) \<longrightarrow> ?f P = undefined" for P 
      using perspectivity.simps Or_def assms is_persp_data.simps by force
    have h5: "?f = (\<lambda>P. if P \<in> Points \<and> P \<lhd> l then P else undefined)" using h3 h4 by auto
    have h6: "?f = one (PJ l)" using h5 assms by auto
    show ?case using h1c h6 by force
  next
    case (4 x)
    have h0: "\<And>Q. (one (PJ l) \<circ> x) Q = x Q"
    proof -
      fix Q
      show "(one (PJ l) \<circ> x) Q = x Q"
      proof (cases "Q \<in> Points \<and> Q \<lhd> l")
        case True
          have h1: "one (PJ l) Q = Q" by (simp add: True assms)
          have h2: "(x Q) \<in> Points \<and> (x Q) \<lhd> l" by sledgehammer
          then show ?thesis sorry
        next
        case False
          have h1: "one (PJ l) Q = undefined" by (simp add: False assms)
          have h2: "one (PJ l) undefined = undefined" using assms by force
          have h3: "x Q = undefined" sorry
          then show ?thesis using h2 by auto
      qed
    qed
    then show ?case using PJ_mult assms
      by presburger
  next
    case (5 x)
    then show ?case sorry
  next
    case 6
    have "\<And>f . f \<in> carrier (PJ l) \<longrightarrow> True"
    then show ?case using inverse_persp perspectivity_bij unfolding PJ_def
  qed
qed

(*may need to create a projectivity identity element*)

(* Proposition 4.8 Let l be a line. Then the set of projectivities of l into itself forms a group, which we will call PJ(l). *)
lemma PJ_l_is_group:
  fixes l
  assumes l_def: "l \<in> Lines"
  shows "group (PJ l)"
  sorry

lemma double_non_containing_line:
  fixes A B l
  assumes AB_def: "A \<in> Points \<and> B \<in> Points"
  assumes l_def: "l \<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l \<and> C \<lhd> l"
  shows "\<exists> l' . l' \<in> Lines \<and> l' \<noteq> l \<and> \<not> A \<lhd> l' \<and> \<not> B \<lhd> l'" 
proof-
  obtain C where C_def: "C \<in> Points \<and> C \<lhd> l \<and> C \<noteq> A \<and> C \<noteq> B" 
    using l_def p4 distinct_length_2_or_more mem_Collect_eq by (metis (no_types, lifting))
  obtain D where D_def: "D \<in> Points \<and> \<not> D \<lhd> l" using l_def p3 pcollinear_def by metis
  let ?l' = "join D C"
  have h1: "?l' \<in> Lines \<and> ?l' \<noteq> l" using AB_def C_def D_def l_def join_properties1 by blast
  have h3: "\<not> A \<lhd> ?l' \<and> \<not> B \<lhd> ?l'" 
    using AB_def C_def D_def h1 join_properties1 l_def unique_meet p1 by metis
  show ?thesis using h1 h3 by auto
qed

lemma triplet_to_triplet_diff_lines:
  fixes A B C A' B' C' l l'
  assumes ABC_def: "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> distinct [A, B, C]"
  assumes ABC'_def: "A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points \<and> distinct [A', B', C']"
  assumes l_def: "l \<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l \<and> C \<lhd> l"
  assumes l'_def: "l' \<in> Lines \<and> A' \<lhd> l' \<and> B' \<lhd> l' \<and> C' \<lhd> l'"
  shows "\<exists> ps . \<exists> ls . \<exists> f . (f = projectivity ps ls) 
                        \<and> (hd ls = l) \<and> (last ls = l') 
                        \<and> (f A = A') \<and> (f B = B') \<and> (f C = C')"
  sorry  

(* Proposition 4.9 Let l be a line, and let A, B, C, and A\<Zprime>, B\<Zprime>, C\<Zprime> be two triples of three distinct points each on l.
Then there is a projectivity of l into itself which sends A, B, C into A\<Zprime>, B\<Zprime>, C\<Zprime>. *)
lemma (in projective_plane) triplet_to_triplet_same_line:
  fixes A B C A' B' C' l
  assumes ABC_def: "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> distinct [A, B, C]"
  assumes ABC'_def: "A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points \<and> distinct [A', B', C']"
  assumes l_def: "l \<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l \<and> C \<lhd> l \<and> A' \<lhd> l \<and> B' \<lhd> l \<and> C' \<lhd> l"
  shows "\<exists> ps . \<exists> ls . \<exists> f . (f = projectivity ps ls) 
                        \<and> (hd ls = l) \<and> (last ls = l) 
                        \<and> (f A = A') \<and> (f B = B') \<and> (f C = C')"
proof-
  have h1: "\<exists> l' . l' \<in> Lines \<and> l' \<noteq> l" using non_containing_line p1 p3 by blast
  obtain l' where l'_def: "l' \<in> Lines \<and> l' \<noteq> l \<and> \<not> A \<lhd> l' \<and> \<not> A' \<lhd> l'" 
    using double_non_containing_line[of A A' l] ABC'_def ABC_def l_def by auto
  obtain A'' B'' C'' where ABC''_def: "A'' \<in> Points \<and> B'' \<in> Points \<and> C'' \<in> Points 
    \<and> distinct [A'', B'', C''] \<and> A'' \<lhd> l' \<and> B'' \<lhd> l' \<and> C'' \<lhd> l'"
    using p4 l'_def ABC'_def by fastforce
  obtain ps ls f where f_def: "(f = projectivity ps ls) \<and> (hd ls = l) \<and> (last ls = l') 
    \<and> (f A = A'') \<and> (f B = B'') \<and> (f C = C'')"
    using triplet_to_triplet_diff_lines[of A B C A'' B'' C'' l l'] ABC_def ABC''_def l'_def l_def by blast
  obtain ps' ls' f' where f'_def: "(f' = projectivity ps' ls') \<and> (hd ls' = l') \<and> (last ls' = l) 
    \<and> (f' A'' = A') \<and> (f' B'' = B') \<and> (f' C'' = C')"
    using triplet_to_triplet_diff_lines[of A'' B'' C'' A' B' C' l' l] ABC''_def ABC'_def l'_def l_def by blast
  let ?ps'' = "ps @ ps'"
  let ?ls'' = "ls @ tl ls'"
  let ?f'' = "f' \<circ> f"
  have h2: "?f'' = projectivity ?ps'' ?ls''" 
    using proj_composition_is_proj[of f ps ls f' ps' ls'] f_def f'_def by auto
  have h3: "(hd ?ls'' = l) \<and> (last ?ls'' = l)" 
    using h2 f'_def f_def hd_Nil_eq_last hd_append2 l'_def last_ConsL last_append last_tl list.collapse
    by metis
  have h4: "(?f'' A = A') \<and> (?f'' B = B') \<and> (?f'' C = C')"
    using f_def f'_def by auto
  show ?thesis using h2 h3 h4 by auto
qed

lemma perspectivity_hquad_to_hquad:
  fixes A B C D f
  assumes ABCD_def: "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points \<and> harmonic_quadruple A B C D"
  assumes data_def: "Q \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> is_persp_data (Or, l1, l2)"
  assumes f_def: "f = perspectivity (Or, l1, l2)"
  assumes ABCD'_def: "A' = f A \<and> B' = f B \<and> C' = f C \<and> D' = f D"
  shows "harmonic_quadruple A' B' C' D'"
proof -
   have A'_def: "A' = (perspectivity Q l1 l2) A" 
    and B'_def: "B' = (perspectivity Q l1 l2) B"
    and C'_def: "C' = (perspectivity Q l1 l2) C"
    and D'_def: "D' = (perspectivity Q l1 l2) D"
    using f_def ABCD'_def sorry

  have A'_on_l2: "A' \<in> Points \<and> A' \<lhd> l2"
    and B'_on_l2: "B' \<in> Points \<and> B' \<lhd> l2"
    and C'_on_l2: "C' \<in> Points \<and> C' \<lhd> l2"
    and D'_on_l2: "D' \<in> Points \<and> D' \<lhd> l2"
    using A'_def B'_def C'_def D'_def ABCD_def sorry

  let ?l'' = "join A B'"

  let ?X = "meet (join B C') (join Q A)"

  have X_on_OA: "?X \<in> Points \<and> ?X \<lhd> (join Q A)"
    and X_on_BC': "?X \<in> Points \<and> ?X \<lhd> (join B C')"
    using join_properties1 meet_properties2 sorry

  have "meet (join X B') ?l'' = D"
  proof -
    have "C \<in> Points \<and> C \<lhd> (join Q C')"
      using C'_def perspectivity.simps join_properties1 join_properties2 meet_properties2 sorry

    have "meet (join ?X B') ?l'' = D"
      using ABCD_def A'_def B'_def C'_def D'_def sorry
    thus ?thesis sorry
  qed
  thus ?thesis sorry
qed



(* Proposition 4.10 A projectivity takes harmonic quadruples into harmonic quadruples. *)
lemma projectivity_hquad_to_hquad:
  fixes A B C D f
  assumes ABCD_def: "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> C \<in> Points \<and> (harmonic_quadruple A B C D)"
  assumes f_def: "\<exists> ps . \<exists> ls . (f = projectivity ps ls)"
  assumes ABCD'_def: "A' = f(A) \<and> B' = f(B) \<and> C' = f(C) \<and> D' = f(D)"
  shows "harmonic_quadruple A' B' C' D'"
  sorry

(* Previous attempts:

type_synonym ('a, 'b) persp_data = "'a \<times> 'b \<times> 'b"

definition is_persp_data :: "persp_data \<Rightarrow> bool" 
  where "is_persp_data (Or, l1, l2) = (if Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines 
  then (\<not> (incid Or l1) \<and> \<not> (incid Or l2)) else undefined)"

context projective_plane2
begin

locale perspectivity_data =
  fixes Or :: "'p" and l1 :: "'l" and l2 :: "'l"
begin 
end

locale perspectivity =
     perspectivity_data Or l1 l2
     for
     Or :: "'p" and 
     l1 :: "'l" and 
     l2 :: "'l" + 
   assumes
     p1: "Or \<in> Points" and
     p2: "l1 \<in> Lines \<and> l2 \<in> Lines" and
     p3: "(\<not> (incid Or l1) \<and> \<not> (incid Or l2))"
end*)

end
end


