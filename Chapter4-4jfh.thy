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

fun persp_domain :: "('p, 'l) persp_data \<Rightarrow> 'l"
  where "persp_domain (Or, l1, l2) = (if is_persp_data (Or, l1, l2) then l1 else undefined)"

fun persp_range :: "('p, 'l) persp_data \<Rightarrow> 'l"
  where "persp_range (Or, l1, l2) = (if is_persp_data (Or, l1, l2) then l2 else undefined)"

lemma perspectivity_nice: 
  fixes Or P l1 l2
  assumes "P \<in> Points \<and>  P \<lhd> persp_domain (Or, l1, l2)"
  assumes "is_persp_data (Or, l1, l2)"
  shows "(perspectivity (Or, l1, l2) P) \<in> Points \<and> (perspectivity (Or, l1, l2) P) \<lhd> persp_range (Or, l1, l2)"
proof -
  have ss: "((perspectivity (Or, l1, l2) P) \<in> Points) \<equiv> ((Or \<bar> P \<sqdot> l2)  \<in> Points)" 
    using assms assms by auto
  have st: "(Or \<bar> P \<sqdot> l2)  \<in> Points" using assms persp_domain.simps meet_properties2 
    join_properties1 join_properties2 is_persp_data.simps by metis
  have su: "(Or \<bar> P \<sqdot> l2) \<lhd> l2" 
    using meet_properties2 join_properties1[of Or P] assms by auto
  show ?thesis using ss st su assms by auto
qed

lemma perspectivity_nice2: 
  fixes d
  assumes "perspectivity d \<noteq> undefined"
  shows "is_persp_data d"
proof (rule ccontr)
  assume ch: "\<not> is_persp_data d"
  show False using assms ch perspectivity.elims by metis
qed

lemma persp_comp_nice:
  fixes d1 d2 P
  assumes "P \<in> Points \<and> P \<lhd> persp_domain d1"
  assumes "is_persp_data d1"
  assumes "is_persp_data d2"
  assumes "persp_range d1 = persp_domain d2"
  shows "(perspectivity d2 (perspectivity d1 P)) \<in> Points \<and> (perspectivity d2 (perspectivity d1 P)) \<lhd> persp_range d2"
  by (metis assms(1,2,3,4) is_persp_data.elims(2) perspectivity_nice)

(*
lemma persp_comp_nice2:
  fixes d1 d2 P
  assumes "perspectivity d2 \<circ> perspectivity d1 \<noteq> undefined"
  shows "is_persp_data d1 \<and> is_persp_data d2 \<and> persp_range d1 = persp_domain d2"
proof - 
  have "perspectivity d2 \<noteq> undefined" using assms by sledgehammer
*)

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
  fixes f d Q
  assumes data_def: "is_persp_data (Or, l1, l2)"
  assumes f_def: "f = perspectivity (Or, l1, l2)"
  assumes g_def: "g = perspectivity (Or, l2, l1)"
  assumes Q_facts: "Q \<in> Points \<and> Q \<lhd> l1"
  shows "(g (f Q)) = Q"
proof -
  have f2: "(f Q) = (Or \<bar> Q) \<sqdot> l2" unfolding f_def g_def perspectivity.simps using assms by auto
  then have fQnice: "(f Q) \<in> Points \<and> (f Q) \<lhd> l2" 
    using Q_facts data_def join_properties1 meet_properties2 by auto
  have gdata_def: "is_persp_data (Or, l2, l1)" using data_def is_persp_data.simps by blast
  have g1: "g (f Q) = (Or \<bar> (f Q)) \<sqdot> l1"
    unfolding f_def g_def perspectivity.simps using fQnice f2 Q_facts gdata_def assms by auto
  then have "g (f Q) = (Or \<bar> ((Or \<bar> Q) \<sqdot> l2)) \<sqdot> l1" using f2 by auto
  then show ?thesis 
    by (smt (verit) Q_facts data_def is_persp_data.simps join_properties1 meet_properties2 unique_meet)
qed

lemma perspectivity_inj:
  fixes f d P Q
  assumes data_def: "is_persp_data d"
  assumes f_def: "f = perspectivity d"
  assumes P_fact: "P \<in> Points \<and> P \<lhd> persp_domain d"
  assumes Q_fact: "Q \<in> Points \<and> Q \<lhd> persp_domain d"
  assumes equal_image: "f P = f Q"
  shows "P = Q"
  using inverse_persp P_fact Q_fact data_def equal_image f_def is_persp_data.elims(2) persp_domain.simps
    by metis

lemma perspectivity_surj:
  fixes f d Q
  assumes data_def: "is_persp_data d"
  assumes f_def: "f = perspectivity d"
  assumes Q_facts: "Q \<in> Points \<and> Q \<lhd> persp_range d"
  shows "\<exists> P . P \<in> Points \<and> P \<lhd> persp_domain d \<and> f P = Q"
  using inverse_persp assms
  by (metis is_persp_data.elims(2) persp_data_sym persp_domain.simps persp_range.simps perspectivity_nice)

lemma perspectivity_bij:
  fixes f d
  assumes data_def: "is_persp_data d"
  assumes f_def: "f = perspectivity d"
  shows "bij_betw f {P \<in> Points. P \<lhd> persp_domain d} {Q \<in> Points. Q \<lhd> persp_range d}"
proof -
  have inj: "inj_on f {P \<in> Points. P \<lhd> persp_domain d}" 
    using perspectivity_inj assms inj_on_def by (smt (verit, best)
    mem_Collect_eq)

  have surj: "f ` {P \<in> Points. P \<lhd> persp_domain d} = {Q \<in> Points. Q \<lhd> persp_range d}"
  proof
    show "f ` {P \<in> Points. P \<lhd> persp_domain d} \<subseteq> {Q \<in> Points. Q \<lhd> persp_range d}" 
      using perspectivity_nice data_def f_def
      by (smt (verit, best) image_Collect_subsetI is_persp_data.elims(2) mem_Collect_eq)
  next
    show "{Q \<in> Points. Q \<lhd> persp_range d} \<subseteq> f ` {P \<in> Points. P \<lhd> persp_domain d}"
    proof
      fix x assume "x \<in> {Q \<in> Points. Q \<lhd> persp_range d}"
      then have h: "x \<in> Points \<and> x \<lhd> persp_range d"
        using mem_Collect_eq by auto

      from h obtain P where "P \<in> Points \<and> P \<lhd> persp_domain d \<and> f P = x"
        using perspectivity_surj assms by blast

      thus "x \<in> f ` {P \<in> Points. P \<lhd> persp_domain d}"
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
  assumes P_def: "P \<in> Points \<and> P \<lhd> persp_domain (Or, l1, l2)"
  assumes P_on_l2: "P \<lhd> persp_range (Or, l1, l2)"
  shows "f P = P"
proof-
  have h1: "f = (\<lambda>P . if P \<in> Points \<and> P \<lhd> l1 then (meet (join Or P) l2) else undefined)"
    using data_def f_def perspectivity.simps by presburger
  have h2: "f P = (meet (join Or P) l2)" using h1 P_def persp_domain.simps persp_range.simps data_def by auto
  have h3: "(meet (join Or P) l2) = P" 
    using P_on_l2 P_def data_def is_persp_data.simps join_properties1 meet_properties2 unique_meet
    persp_domain.simps persp_range.simps by metis
  show ?thesis using h2 h3 persp_domain.simps persp_range.simps by auto
qed

(* 
Projectivities: 
*)

type_synonym ('d) proj_data = "'d list"

fun projectivity :: "(('p, 'l) persp_data) proj_data \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "projectivity (Cons d []) = (perspectivity d)" |
  "projectivity (Cons d ds) = (projectivity ds) \<circ> (perspectivity d)" |
  "projectivity [] = (\<lambda> Q . Q)"

fun proj_domain :: "(('p, 'l) persp_data) proj_data \<Rightarrow> 'l" where
  "proj_domain (Cons d []) = persp_domain d" |
  "proj_domain (Cons d ds) = persp_domain d" |
  "proj_domain [] = undefined"

fun proj_range :: "(('p, 'l) persp_data) proj_data \<Rightarrow> 'l" where
  "proj_range (Cons d []) = persp_range d" |
  "proj_range (Cons d ds) = proj_range ds" |
  "proj_range [] = undefined"

fun is_proj_data :: "(('p, 'l) persp_data) proj_data \<Rightarrow> bool" where
  "is_proj_data (Cons d []) = (is_persp_data d)" |
  "is_proj_data (Cons d (Cons d' ds)) = 
    (is_persp_data d \<and> persp_range d = persp_domain d' \<and> is_proj_data (Cons d' ds))" |
  "is_proj_data [] = False"

lemma is_proj_non_empty:
  fixes ds
  assumes "is_proj_data ds"
  shows "ds \<noteq> []"
  using assms by auto

lemma is_proj_made_up_of_persp:
  fixes ds
  assumes "is_proj_data ds"
  shows "\<exists> d. is_persp_data d \<and> d = hd ds"
  by (metis assms
    is_proj_data.simps(1,2,3)
    list.collapse) 

lemma proj_domain_cons [sym]:
  fixes d ds
  assumes "is_persp_data d"
  assumes "is_proj_data ds"
  shows "proj_domain (d # ds) = persp_domain d"
  by (metis assms(2)
    is_proj_data.simps(3)
    list.exhaust
    proj_domain.simps(2))

lemma proj_range_cons [sym]:
  fixes d ds
  assumes "is_persp_data d"
  assumes "is_proj_data ds"
  shows "proj_range (d # ds) = proj_range ds"
  by (metis assms(2)
    is_proj_data.simps(3)
    list.exhaust
    proj_range.simps(2))

lemma proj_domain_append [sym]:
  fixes d ds
  assumes "is_proj_data d"
  assumes "is_proj_data ds"
  shows "proj_domain (d @ ds) = proj_domain d"
  by (smt (verit)
    append_is_Nil_conv[of d ds]
    assms(1) hd_append2[of d ds]
    is_proj_data.simps(3)
    list.sel(1)[of _ "[]"]
    list.sel(1)[of _ "_ # _"]
    proj_domain.elims[of "d @ ds"
      "proj_domain (d @ ds)"]
    proj_domain.elims[of d
      "proj_domain d"])

lemma proj_range_append [sym]:
  fixes d ds
  assumes "is_proj_data d"
  assumes "is_proj_data ds"
  shows "proj_range (d @ ds) = proj_range ds"
  using assms
proof (induction d)
  case Nil
  then show ?case by auto
next
  case (Cons a ds)
  then show ?case by (metis append_Cons
    append_Nil
    is_proj_data.simps(2)
    is_proj_non_empty
    list.exhaust
    proj_range.simps(2))
qed

lemma projectivity_nice: 
  fixes ds P
 (*  assumes "last ((Or, l1, l2) # ds) = (Or', l1', l2')" *)
  shows "is_proj_data ds \<Longrightarrow> P \<in> Points \<and> P \<lhd> proj_domain ds \<Longrightarrow>
        projectivity ds P \<in> Points \<and> 
        projectivity ds P \<lhd> proj_range ds"
proof (induction ds arbitrary: "P" )
  case Nil
  then have "False" using Nil.prems(1) is_proj_data.simps(3) by auto
  then show ?case by auto
next
  case (Cons a qs)
  have h0: "is_proj_data qs \<Longrightarrow>
    P \<in> Points \<and> P \<lhd> proj_domain qs \<Longrightarrow> projectivity qs P \<in> Points \<and> projectivity qs P \<lhd> proj_range qs" 
    using Cons.IH by blast
  have h1: "is_proj_data (a # qs)" using Cons.prems(1) by auto
  have h2: "P \<in> Points \<and> P \<lhd> proj_domain (a # qs)" using Cons.prems(2) by auto
  show ?case
  proof -
    have p1:"(qs = [] \<longrightarrow> perspectivity a P \<in> Points \<and> perspectivity a P \<lhd> proj_range (a # qs))"
      using Cons.prems(1,2) is_persp_data.elims(2) is_proj_data.simps(1) perspectivity_nice 
        proj_domain.simps proj_range.simps by (smt (verit, del_insts) persp_domain.simps)
    have p2: "(qs \<noteq> [] \<longrightarrow>
      projectivity (a # qs) P \<in> Points \<and> projectivity (a # qs) P \<lhd> proj_range qs)"
    proof -
      have "projectivity (a # qs) P = ((projectivity qs) \<circ> (perspectivity a)) P"
        by (smt (verit, ccfv_threshold) fun.map_ident_strong projectivity.cases
          projectivity.simps(1,2,3))
      also have "... = (projectivity qs) ((perspectivity a) P)" by auto
      finally have p3a: "projectivity (a # qs) P = (projectivity qs) ((perspectivity a) P)" .
      have "is_persp_data a" using Cons.prems(1) is_proj_data.elims(1) by blast
      then have p3: "((perspectivity a P) \<in> Points) \<and> ((perspectivity a P) \<lhd> persp_range a)"
        by (smt (z3) Cons.prems(2) is_persp_data.elims(2) is_proj_data.elims(1) p1 proj_domain.simps(2) 
          proj_range.simps(1) projective_plane.perspectivity_nice projective_plane_axioms)
      have "qs \<noteq> [] \<longrightarrow> persp_range a = proj_domain qs" using h1 proj_domain_cons 
          is_proj_data.simps(2) proj_domain.simps(1) projectivity.cases by metis
      then have "qs \<noteq> [] \<longrightarrow> ((perspectivity a P) \<in> Points) \<and> ((perspectivity a P) \<lhd> proj_domain qs)" 
        using p3 by metis
      then have "qs \<noteq> [] \<longrightarrow> (projectivity qs (perspectivity a P) \<in> Points \<and> projectivity qs (perspectivity a P) \<lhd> proj_range qs)"
        using h0 by (metis Cons.IH h1 is_proj_data.simps(2) list.exhaust)
      then show ?thesis using p3a by auto
    qed
    then show ?case by (metis list.exhaust p1 proj_range.simps(2) projectivity.simps(1))
  qed
qed


lemma projectivity_not_nice: 
  fixes ds P
  assumes "is_proj_data ds"
  assumes "\<not>(P \<in> Points) \<or> \<not>(P \<lhd> proj_domain ds)"
  shows "projectivity ds P = undefined"
using assms
proof (induction ds arbitrary: P)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  show ?case
  proof (cases "ds = []")
    case True
    then have "projectivity (d # ds) P = perspectivity d P"
      by simp
    moreover have "\<not>(P \<in> Points) \<or> \<not>(P \<lhd> persp_domain d)"
      using Cons.prems True by auto
    ultimately show ?thesis
      using Cons.prems(1) is_persp_data.simps is_proj_made_up_of_persp
    by fastforce
  next
    case False
    then have h0: "projectivity (d # ds) P = (projectivity ds \<circ> perspectivity d) P"
      by (metis neq_Nil_conv projectivity.simps(2))
    then have "... = (projectivity ds (perspectivity d P))"
      by auto
    moreover have "\<not>(P \<in> Points) \<or> \<not>(P \<lhd> persp_domain d)"
      using Cons.prems(2) proj_domain.simps(2) by (metis False neq_Nil_conv) 
    moreover have "perspectivity d P = undefined" using Cons.prems(1) calculation(2) is_proj_made_up_of_persp
      by fastforce
    moreover have "projectivity ds undefined = undefined" using projectivity.simps sorry
    ultimately show ?thesis using h0 by presburger
  qed
qed

(*
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

lemma proj_is_persp_data:
  fixes d ds
  assumes "is_proj_data (d # ds)"
  shows "is_persp_data d"
  using assms is_proj_data.elims(1) by blast

lemma proj_is_persp_data2:
  fixes d ds
  assumes "d \<noteq> []"
  assumes "is_proj_data d"
  shows "is_persp_data (hd d)"
  using assms list.collapse proj_is_persp_data by metis

lemma proj_data_append_is_data:
  fixes d d'
  assumes "d' \<noteq> []"
  assumes "proj_range d = proj_domain d'"
  assumes "is_proj_data d"
  assumes "is_proj_data d'"
  shows "is_proj_data (d @ d')"
using assms
proof (induction d)
  case Nil
  then show ?case using assms(4) by auto
next
  case (Cons a ds)
  then show ?case sorry
qed

(* cvc5: Try this:
  by (smt (verit) append_Cons
    append_eq_append_conv2
    append_is_Nil_conv
    is_proj_data.elims(1)
    list.inject proj_domain.elims
    proj_range.elims
    proj_range.simps(1)) (> 1.0 s, timed out) 
cvc5: Try this:
  by (smt (verit) append_Cons
    append_self_conv2
    is_proj_data.simps(2)
    list.inject proj_domain.elims
    proj_is_persp_data
    proj_range.elims) (> 1.0 s, timed out) 
cvc5: Try this:
  by (smt (verit) append_Cons
    append_is_Nil_conv
    append_self_conv2
    is_proj_data.elims(1)
    list.inject proj_domain.elims
    proj_range.elims
    proj_range.simps(1))  *)

lemma persp_proj_composition_is_proj:
  fixes d d'
  assumes "persp_range d = proj_domain d'"
  assumes "is_persp_data d"
  assumes "is_proj_data d'"
  shows "projectivity (d # d') = (projectivity d') \<circ> (perspectivity d)"
  using fun.map_ident_strong projectivity.cases
          projectivity.simps(1,2,3) by metis

lemma proj_composition_is_proj:
  fixes d d'
  assumes "proj_range d = proj_domain d'"
  assumes "is_proj_data d"
  assumes "is_proj_data d'"
  shows "projectivity (d @ d') = (projectivity d') \<circ> (projectivity d)"
using assms
proof (induction d)
  case Nil
  then show ?case by simp
next
  case (Cons a ds)
  have h0: "projectivity ((a # ds) @ d') = projectivity ((a # ds) @ d')"
    by auto
  also have h1: "... = projectivity (a # (ds @ d'))"
    by force
  also have h2: "... = (projectivity (ds @ d')) \<circ> (perspectivity a)"
    using persp_proj_composition_is_proj by (metis fun.map_ident_strong neq_Nil_conv projectivity.simps(1,2,3))
  also have h3: "... = ((projectivity d') \<circ> (projectivity ds)) \<circ> (perspectivity a)"
    by (metis (no_types, opaque_lifting)
    Cons.IH Cons.prems(1,2)
    append_Nil assms(3)
    comp_apply
    is_proj_data.simps(2)
    list.exhaust
    proj_range.simps(2)
    projectivity.simps(3))
  also have h4: "... = (projectivity d') \<circ> ((projectivity ds) \<circ> (perspectivity a))"
    by (simp add: comp_assoc)
  also have h5: "... = (projectivity d') \<circ> (projectivity (a # ds))"
    by (metis fun.map_ident_strong
    neq_Nil_conv
    projectivity.simps(1,2,3))
  then show ?case using h1 h2 h3 h4
    by argo
qed 

definition PJ :: "'l \<Rightarrow> (('p \<Rightarrow> 'p) monoid)" 
  where "PJ l = (if (l \<in> Lines) then
  \<lparr>carrier = {f . \<exists> ds. (f = projectivity ds) \<and> (proj_domain ds = l) \<and> (proj_range ds  = l) \<and> (is_proj_data ds)},
  monoid.mult = (\<circ>),
  one = (\<lambda>P. if P \<in> Points \<and> P \<lhd> l then P else undefined)\<rparr> 
  else undefined)"

lemma PJ_carrier [simp]:
  fixes l
  assumes "l \<in> Lines"
  shows "carrier (PJ l) = {f . \<exists> ds . 
                            (f = projectivity ds) \<and> (proj_domain ds = l) \<and> (proj_range ds = l) \<and> (is_proj_data ds)}"
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

lemma PJ_one_proj [simp]:
  fixes l
  assumes "l \<in> Lines"
  shows "\<exists> ds. projectivity ds = one (PJ l) \<and> (proj_domain ds = l) \<and> (proj_range ds = l)"
proof -
  obtain Or where Or_def: "Or \<in> Points \<and> \<not> Or \<lhd> l" using p3 pcollinear_def assms by fastforce
  let ?f = "perspectivity (Or, l, l)"
  have h1a: "?f = projectivity [(Or, l, l)]" by auto
  have h1b: "\<exists> ds . (?f = projectivity ds) \<and> (proj_domain ds = l) \<and> (proj_range ds = l)"
    using h1a using Or_def assms by fastforce
  have h1c: "?f \<in> carrier (PJ l)" using h1a h1b assms 
    by (smt (verit, del_insts)
    Or_def PJ_carrier
    is_persp_data.simps
    is_proj_data.simps(1)
    mem_Collect_eq
    persp_domain.simps
    persp_range.simps
    proj_domain.simps(1)
    proj_range.simps(1))
  have h2: "P \<in> Points \<and> P \<lhd> l \<longrightarrow> meet (join Or P) l = P" for P
    using unique_meet Or_def assms by (metis join_properties1
  meet_properties2)
  have h3: "P \<in> Points \<and> P \<lhd> l \<longrightarrow> ?f P = P" for P 
    using Or_def assms perspectivity_of_meet_is_itself by auto
  have h4: "\<not>(P \<in> Points \<and> P \<lhd> l) \<longrightarrow> ?f P = undefined" for P 
    using Or_def assms by force
  have h5: "?f = (\<lambda>P. if P \<in> Points \<and> P \<lhd> l then P else undefined)" using h3 h4 by auto
  have h6: "?f = one (PJ l)" using h5 assms by auto
  show ?thesis using h1c h6 h1b by auto
qed

lemma PJ_one_proj_constuction [simp]:
  fixes l
  fixes Or
  assumes "l \<in> Lines"
  assumes "Or \<in> Points \<and> \<not> Or \<lhd> l"
  shows "projectivity [(Or, l, l)] = one (PJ l)"
proof -
  let ?f = "perspectivity (Or, l, l)"
  have h1a: "?f = projectivity [(Or, l, l)]" by auto
  have h1b: "\<exists> ds . (?f = projectivity ds) \<and> (proj_domain ds = l) \<and> (proj_range ds = l)"
    using h1a using assms by fastforce
  have h1c: "?f \<in> carrier (PJ l)" using h1a h1b assms 
    by (smt (verit, del_insts)
    PJ_carrier
    is_persp_data.simps
    is_proj_data.simps(1)
    mem_Collect_eq
    persp_domain.simps
    persp_range.simps
    proj_domain.simps(1)
    proj_range.simps(1))
  have h2: "P \<in> Points \<and> P \<lhd> l \<longrightarrow> meet (join Or P) l = P" for P 
    using unique_meet assms by (metis join_properties1 meet_properties2)
  have h3: "P \<in> Points \<and> P \<lhd> l \<longrightarrow> ?f P = P" for P 
    using assms perspectivity_of_meet_is_itself by auto
  have h4: "\<not>(P \<in> Points \<and> P \<lhd> l) \<longrightarrow> ?f P = undefined" for P 
    using assms by force
  have h5: "?f = (\<lambda>P. if P \<in> Points \<and> P \<lhd> l then P else undefined)" using h3 h4 by auto
  have h6: "?f = one (PJ l)" using h5 assms by auto
  show ?thesis using h1c h6 h1b by auto
qed

(* Proposition 4.8 Let l be a line. Then the set of projectivities of l into itself forms a group, which we will call PJ(l). *)
lemma
  fixes l
  assumes "l \<in> Lines"
  shows PJ_group: "group (PJ l)"
proof -
  show "group (PJ l)"
  proof (unfold_locales, goal_cases)
    case (1 f g)
    obtain ds where f_proj: "f = projectivity ds \<and> proj_domain ds = l \<and> proj_range ds = l \<and> is_proj_data ds" 
      using "1"(1) assms by auto
    obtain ds' where g_proj: "g = projectivity ds' \<and> proj_domain ds' = l \<and> proj_range ds' = l \<and> is_proj_data ds'" 
      using "1"(2) assms by auto
    have h1: "f \<circ> g = (projectivity ds) \<circ> (projectivity ds')" 
      using f_proj g_proj by simp
    thm proj_composition_is_proj
    also have h2: "... = projectivity (ds' @ ds)" 
      using f_proj g_proj proj_composition_is_proj[of "ds'" "ds"] by argo
    have h3: "proj_domain (ds' @ ds) = l" 
    by (metis f_proj g_proj
    is_proj_data.simps(3)
    proj_domain_append)
    have h4: "proj_range (ds' @ ds) = l" 
      by (metis f_proj g_proj
      is_proj_data.simps(3)
      proj_range_append)
    have h5: "is_proj_data (ds' @ ds)" 
      by (metis f_proj g_proj
      is_proj_data.simps(3)
      proj_data_append_is_data)
    then show ?case using f_proj g_proj unfolding PJ_def using assms h2 h3 h4
    by auto
  next
    thm proj_composition_is_proj
    case (2)
    show ?case using assms by auto
  next
    case 3
    obtain Or where Or_def: "Or \<in> Points \<and> \<not> Or \<lhd> l" using p3 pcollinear_def assms by fastforce
    let ?f = "perspectivity (Or, l, l)"
    have h1a: "?f = projectivity [(Or, l, l)]" by auto
    have h1b: "\<exists> ds . (?f = projectivity ds) \<and> (proj_domain ds = l) \<and> (proj_range ds = l)"
      using h1a using Or_def assms by fastforce
    have h1c: "?f \<in> carrier (PJ l)" using h1a h1b assms 
      by (smt (verit, del_insts)
      Or_def PJ_carrier
      is_persp_data.simps
      is_proj_data.simps(1)
      mem_Collect_eq
      persp_domain.simps
      persp_range.simps
      proj_domain.simps(1)
      proj_range.simps(1))
    have h2: "P \<in> Points \<and> P \<lhd> l \<longrightarrow> meet (join Or P) l = P" for P 
      using unique_meet Or_def assms by (metis join_properties1
    meet_properties2)
    have h3: "P \<in> Points \<and> P \<lhd> l \<longrightarrow> ?f P = P" for P 
      using Or_def assms perspectivity_of_meet_is_itself by auto
    have h4: "\<not>(P \<in> Points \<and> P \<lhd> l) \<longrightarrow> ?f P = undefined" for P 
      using Or_def assms by force
    have h5: "?f = (\<lambda>P. if P \<in> Points \<and> P \<lhd> l then P else undefined)" using h3 h4 by auto
    have h6: "?f = one (PJ l)" using h5 assms by auto
    show ?case using h1c h6 by force
  next
    case (4 x)
    obtain ds where h0: "x = projectivity ds \<and> proj_domain ds = l \<and> proj_range ds = l \<and> is_proj_data ds" using "4" assms by auto
    obtain Or where Or_def: "Or \<in> Points \<and> \<not> Or \<lhd> l" using p3 pcollinear_def assms by fastforce
    then have h1: "projectivity [(Or, l, l)] = one (PJ l)" using assms PJ_one_proj_constuction assms by blast
    then have h2: "Q \<in> Points \<and> Q \<lhd> l \<longrightarrow> (one (PJ l)) Q = Q" for Q
      using PJ_one assms by presburger
    then have h3: "Q \<in> Points \<and> Q \<lhd> l \<longrightarrow> (x Q) \<in> Points \<and> (x Q) \<lhd> l" for Q 
      using "4" assms projectivity_nice by fastforce
    then have h4: "Q \<in> Points \<and> Q \<lhd> l \<longrightarrow>  projectivity [(Or, l, l)] (x Q) = x Q" for Q 
      using assms "4" projectivity_nice h1 by auto
    then have h5: "Q \<in> Points \<and> Q \<lhd> l \<longrightarrow> (one (PJ l) \<circ> x) Q = x Q" for Q 
      using h0 h1 by auto
    then have h6: "\<not>(Q \<in> Points \<and> Q \<lhd> l) \<longrightarrow> one (PJ l) Q = undefined" for Q 
      using PJ_one assms by presburger
    then have h7: "\<not>(Q \<in> Points \<and> Q \<lhd> l) \<longrightarrow> x Q = undefined" for Q 
      by (metis h0
      is_proj_data.simps(3)
      projectivity_not_nice)
    show ?case using PJ_mult assms comp_apply h2 h5 h7
      by fastforce
  next
    case (5 x)
    then show ?case sorry
  next
    case 6
    have "\<And>f . f \<in> carrier (PJ l) \<longrightarrow> True" by blast
    then show ?case using inverse_persp perspectivity_bij unfolding PJ_def sorry
  qed
qed

lemma double_non_containing_line:
  fixes A B l
  assumes AB_def: "A \<in> Points \<and> B \<in> Points"
  assumes l_def: "l \<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l \<and> C \<lhd> l"
  shows "\<exists> l' . l' \<in> Lines \<and> l' \<noteq> l \<and> \<not> A \<lhd> l' \<and> \<not> B \<lhd> l'" 
proof -
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
  assumes distinct_lines: "l \<noteq> l'"
  assumes A_not_on_l': "\<not> A \<lhd> l'"
  assumes A'_not_on_l: "\<not> A' \<lhd> l"
  shows "\<exists> ds f. (f = projectivity ds) \<and> (is_proj_data ds) \<and> 
                 (f A = A') \<and> (f B = B') \<and> (f C = C')"
proof -
  let ?AA' = "join A A'"
  have AA'_line: "?AA' \<in> Lines \<and> A \<lhd> ?AA' \<and> A' \<lhd> ?AA'"
    using ABC_def ABC'_def join_properties1 join_properties2 by (metis A'_not_on_l
    l_def)
  
  let ?AB' = "join A B'"
  have AB'_line: "?AB' \<in> Lines \<and> A \<lhd> ?AB' \<and> B' \<lhd> ?AB'"
    using ABC_def ABC'_def join_properties1 join_properties2 by (metis A_not_on_l'
    l'_def)
  
  let ?A'B = "join A' B"
  have A'B_line: "?A'B \<in> Lines \<and> A' \<lhd> ?A'B \<and> B \<lhd> ?A'B"
    using ABC_def ABC'_def join_properties1 join_properties2 by (metis A'_not_on_l
    l_def)
  
  let ?B'' = "meet ?AB' ?A'B"
  have B''_def: "?B'' \<in> Points \<and> ?B'' \<lhd> ?AB' \<and> ?B'' \<lhd> ?A'B"
    using AB'_line A'B_line meet_properties2 by (metis A'_not_on_l ABC_def
    distinct_length_2_or_more
    l_def unique_meet)

  let ?AC' = "join A C'"
  have AC'_line: "?AC' \<in> Lines \<and> A \<lhd> ?AC' \<and> C' \<lhd> ?AC'"
    using ABC_def ABC'_def join_properties1 join_properties2 by (metis A_not_on_l'
    l'_def)

  let ?A'C = "join A' C"
  have A'C_line: "?A'C \<in> Lines \<and> A' \<lhd> ?A'C \<and> C \<lhd> ?A'C"
    using ABC_def ABC'_def join_properties1 join_properties2 using A'_not_on_l l_def
    by blast

  let ?C'' = "meet ?AC' ?A'C"
  have C''_def: "?C'' \<in> Points \<and> ?C'' \<lhd> ?AC' \<and> ?C'' \<lhd> ?A'C"
    using AC'_line A'C_line meet_properties2 by (metis A'_not_on_l ABC_def
    distinct_length_2_or_more
    l_def unique_meet)

  let ?l'' = "join ?B'' ?C''"
  have l''_line: "?l'' \<in> Lines \<and> ?B'' \<lhd> ?l'' \<and> ?C'' \<lhd> ?l''"
    using B''_def C''_def join_properties1 join_properties2 by (smt (verit, del_insts)
    A'_not_on_l ABC'_def ABC_def
    A_not_on_l'
    distinct_length_2_or_more
    l'_def l_def)

  let ?A'' = "meet ?l'' ?AA'"
  have A''_def: "?A'' \<in> Points \<and> ?A'' \<lhd> ?l'' \<and> ?A'' \<lhd> ?AA'"
    using l''_line AA'_line meet_properties2 by (smt (verit, ccfv_threshold)
    A'B_line A'_not_on_l AB'_line
    ABC'_def ABC_def A_not_on_l'
    distinct_length_2_or_more
    l'_def l_def
    unique_meet)
  
  (* First perspectivity *)
  let ?d1 = "(A', l, ?l'')"
  have d1_persp: "is_persp_data ?d1"
    using ABC'_def l_def l''_line A'_not_on_l by (smt (z3) A'B_line A'C_line
    AB'_line ABC_def AC'_line
    A_not_on_l' B''_def C''_def
    distinct_length_2_or_more
    is_persp_data.simps l'_def
    s)
  
  (* Second perspectivity *)
  let ?d2 = "(A, ?l'', l')"
  have d2_persp: "is_persp_data ?d2"
    using ABC_def l'_def l''_line A_not_on_l' by (smt (verit, del_insts)
    A'B_line A'C_line A'_not_on_l
    AB'_line ABC'_def AC'_line
    B''_def C''_def
    distinct_length_2_or_more
    is_persp_data.simps l_def
    unique_meet)

  have A_dp_eq_meet_join_Ap_A_ldp: "?A'' = (meet (join A' A) ?l'')"
    by (smt (verit, ccfv_SIG) AA'_line ABC'_def
    ABC_def join_properties2 l''_line
    meet_properties2)
  
  have B_dp_eq_meet_join_Ap_B_ldp: "?B'' = (meet (join A' B) ?l'')" 
    by (metis A'B_line B''_def d1_persp
    is_persp_data.simps l''_line
    meet_properties2 unique_meet)
  
  have C_dp_eq_meet_join_Ap_C_ldp: "?C'' = (meet (join A' C) ?l'')" 
    by (metis A'C_line C''_def d1_persp
    is_persp_data.simps l''_line
    meet_properties2 unique_meet)
  
  have Ap_eq_meet_join_Ap_Adp_lp: "A' = (meet (join A ?A'') l')"
    by (smt (verit, del_insts) AA'_line ABC'_def
    d2_persp is_persp_data.simps
    join_properties2 l'_def
    meet_properties2)
  
  have Bp_eq_meet_join_Ap_Bdp_lp: "B' = (meet (join A ?B'') l')"
    by (metis (full_types) AB'_line ABC'_def
    B''_def d2_persp is_persp_data.simps
    join_properties2 l''_line l'_def
    meet_properties2)
  
  have Cp_eq_meet_join_Ap_Cdp_lp: "C' = (meet (join A ?C'') l')"
    by (metis (full_types) ABC'_def AC'_line
    C''_def d2_persp is_persp_data.simps
    join_properties2 l''_line l'_def
    meet_properties2)
  
  (* First perspectivity: A \<rightarrow> A'', B \<rightarrow> B'', C \<rightarrow> C'' *)
  have persp1_A: "perspectivity ?d1 A = ?A''"
    using d1_persp ABC_def l_def A''_def AA'_line AA'_line A_dp_eq_meet_join_Ap_A_ldp
    perspectivity.simps by auto
  
  have persp1_B: "perspectivity ?d1 B = ?B''"
    using d1_persp ABC_def l_def B''_def A'B_line B_dp_eq_meet_join_Ap_B_ldp
    perspectivity.simps by presburger
  
  have persp1_C: "perspectivity ?d1 C = ?C''"
    using d1_persp ABC_def l_def C''_def A'C_line C_dp_eq_meet_join_Ap_C_ldp
    perspectivity.simps by presburger
  
  (* Second perspectivity: A'' \<rightarrow> A', B'' \<rightarrow> B', C'' \<rightarrow> C' *)
  have persp2_A'': "perspectivity ?d2 ?A'' = A'"
    using d2_persp A''_def l''_line ABC'_def AA'_line Ap_eq_meet_join_Ap_Adp_lp
    perspectivity.simps by presburger
  
  have persp2_B'': "perspectivity ?d2 ?B'' = B'"
    using d2_persp B''_def l''_line ABC'_def AB'_line Bp_eq_meet_join_Ap_Bdp_lp
    perspectivity.simps by presburger
  
  have persp2_C'': "perspectivity ?d2 ?C'' = C'"
    using d2_persp C''_def l''_line ABC'_def AC'_line Cp_eq_meet_join_Ap_Cdp_lp
    perspectivity.simps by presburger
  
  (* Compose perspectivities *)
  let ?ds = "[?d1, ?d2]"
  let ?f = "projectivity ?ds"
  
  have ds_valid: "is_proj_data ?ds"
    using d1_persp d2_persp by simp
  
  have f_A: "?f A = A'"
    using persp1_A persp2_A'' by simp
  
  have f_B: "?f B = B'"
    using persp1_B persp2_B'' by simp
  
  have f_C: "?f C = C'"
    using persp1_C persp2_C'' by simp
  
  show ?thesis
    using ds_valid f_A f_B f_C by blast
qed

(* Proposition 4.9 Let l be a line, and let A, B, C, and A\<Zprime>, B\<Zprime>, C\<Zprime> be two triples of three distinct points each on l. Then there is a projectivity of l into itself which sends A, B, C into A\<Zprime>, B\<Zprime>, C\<Zprime>. *)
lemma triplet_to_triplet_same_line:
  fixes A B C A' B' C' l
  assumes ABC_def: "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> distinct [A, B, C]"
  assumes ABC'_def: "A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points \<and> distinct [A', B', C']"
  assumes l_def: "l \<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l \<and> C \<lhd> l \<and> A' \<lhd> l \<and> B' \<lhd> l \<and> C' \<lhd> l"
  shows "\<exists> ds f. (f = projectivity ds) \<and> (is_proj_data ds) \<and> 
                 (f A = A') \<and> (f B = B') \<and> (f C = C')"
proof -
  obtain l' where l'_props: "l' \<in> Lines \<and> l' \<noteq> l \<and> \<not> A \<lhd> l' \<and> \<not> A' \<lhd> l'"
    using double_non_containing_line[of A A' l] ABC_def ABC'_def l_def
    by blast
  
  obtain Or where Or_def: "Or \<in> Points \<and> \<not> Or \<lhd> l \<and> \<not> Or \<lhd> l'"
    using p3 pcollinear_def l_def l'_props sorry
  
  let ?d_proj = "(Or, l, l')"
  have d_proj_persp: "is_persp_data ?d_proj"
    using Or_def l_def l'_props by simp
  
  let ?A'' = "perspectivity ?d_proj A'"
  let ?B'' = "perspectivity ?d_proj B'"
  let ?C'' = "perspectivity ?d_proj C'"
  
  have A''_props: "?A'' \<in> Points \<and> ?A'' \<lhd> l'"
    using perspectivity_nice[of A' Or l l'] d_proj_persp ABC'_def l_def
    by simp
  
  have B''_props: "?B'' \<in> Points \<and> ?B'' \<lhd> l'"
    using perspectivity_nice[of B' Or l l'] d_proj_persp ABC'_def l_def
    by simp
  
  have C''_props: "?C'' \<in> Points \<and> ?C'' \<lhd> l'"
    using perspectivity_nice[of C' Or l l'] d_proj_persp ABC'_def l_def
    by simp
  
  have A''_not_on_l: "\<not> ?A'' \<lhd> l"
    using A''_props l'_props l_def p1 by (smt (verit, best) ABC'_def
    d_proj_persp
    persp_domain.simps
    persp_range.simps
    perspectivity_of_meet_is_itself
    projective_plane.perspectivity_inj
    projective_plane_axioms)
  
  obtain ds1 f1 where f1_props: 
    "f1 = projectivity ds1 \<and> is_proj_data ds1 \<and> 
     f1 A = ?A'' \<and> f1 B = ?B'' \<and> f1 C = ?C''"
    using triplet_to_triplet_diff_lines[of A B C ?A'' ?B'' ?C'' l l']
          ABC_def A''_props B''_props C''_props l_def l'_props A''_not_on_l
    by (metis (no_types, lifting)
    ABC'_def d_proj_persp
    distinct_length_2_or_more
    distinct_singleton
    inverse_persp)
  
  obtain ds2 f2 where f2_props:
    "f2 = projectivity ds2 \<and> is_proj_data ds2 \<and>
     f2 ?A'' = A' \<and> f2 ?B'' = B' \<and> f2 ?C'' = C'"
    using triplet_to_triplet_diff_lines[of ?A'' ?B'' ?C'' A' B' C' l' l]
          A''_props B''_props C''_props ABC'_def l_def l'_props A''_not_on_l
    by (metis d_proj_persp
    inverse_persp
    is_proj_data.simps(1)
    persp_data_sym
    projectivity.simps(1))
  
  let ?ds = "ds1 @ ds2"
  let ?f = "f2 \<circ> f1"
  
  have ds_valid: "is_proj_data ?ds"
    using f1_props f2_props proj_data_append_is_data sorry
  
  have f_comp: "?f = projectivity ?ds"
    using f1_props f2_props proj_composition_is_proj sorry
  
  have f_A: "?f A = A'"
    using f1_props f2_props by force
  
  have f_B: "?f B = B'"
    using f1_props f2_props by force
  
  have f_C: "?f C = C'"
    using f1_props f2_props by force
  
  show ?thesis
    using ds_valid f_comp f_A f_B f_C by blast
qed

lemma perspectivity_hquad_to_hquad:
  fixes A B C D f
  assumes ABCD_def: "(A \<in> Points \<and> A \<lhd> l1) \<and> (B \<in> Points \<and> A \<lhd> l1) \<and> (C \<in> Points \<and> C \<lhd> l1) \<and> (D \<in> Points \<and> D \<lhd> l1)"
  assumes ABCD_harmonic_quadruple: "harmonic_quadruple A B C D"
  assumes data_def: "is_persp_data d"
  assumes f_def: "f = perspectivity d"
  assumes f_domain: "persp_domain d = l1"
  assumes f_domain: "persp_range d = l2"
  assumes ABCD'_def: "A' = f A \<and> B' = f B \<and> C' = f C \<and> D' = f D"
  shows "harmonic_quadruple A' B' C' D'"
proof -
   have A'_def: "A' = (perspectivity d) A" 
    and B'_def: "B' = (perspectivity d) B"
    and C'_def: "C' = (perspectivity d) C"
    and D'_def: "D' = (perspectivity d) D"
    using f_def ABCD'_def by blast+

  have A'_on_l2: "A' \<in> Points \<and> A' \<lhd> l2"
    and B'_on_l2: "B' \<in> Points \<and> B' \<lhd> l2"
    and C'_on_l2: "C' \<in> Points \<and> C' \<lhd> l2"
    and D'_on_l2: "D' \<in> Points \<and> D' \<lhd> l2"
    using A'_def B'_def C'_def D'_def ABCD_def ABCD'_def f_def data_def
    f_domain is_persp_data.elims(2) perspectivity_nice assms(5) sorry

  let ?l'' = "join A B'"

  let ?X = "meet (join B C') (join Q A)"

  have X_on_OA: "?X \<in> Points \<and> ?X \<lhd> (join Q A)"
    and X_on_BC': "?X \<in> Points \<and> ?X \<lhd> (join B C')"
    using join_properties1 meet_properties2 sorry

  have "meet (join X B') ?l'' = D"
  proof -
    have "C \<in> Points \<and> C \<lhd> (join Q C')"
      using C'_def join_properties1 join_properties2 meet_properties2 sorry

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
  assumes f_def: "\<exists> ds . (f = projectivity ds)"
  assumes ds_def: "is_proj_data ds"
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


