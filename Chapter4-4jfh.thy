theory "Chapter4-4jfh"
  imports Complex_Main  "Chapter4-3" "HOL-Algebra.Group"
begin

context projective_plane
begin
text‹ start at "Perspectivies and Projectivities" and go to end of chapter›

type_synonym ('p1, 'l1) persp_data = "('p1 × 'l1 × 'l1)"

fun is_persp_data :: "('p, 'l) persp_data ⇒ bool" 
  where "is_persp_data (Or, l1, l2) = (Or ∈ Points ∧ l1 ∈ Lines ∧ l2 ∈ Lines ∧ 
  ¬ (Or ⊲ l1) ∧ ¬ (Or ⊲ l2))"

fun perspectivity :: "('p, 'l) persp_data ⇒ ('p ⇒ 'p)"
  where "perspectivity (Or, l1, l2) = (if is_persp_data (Or, l1, l2)
  then (λP . if P ∈ Points ∧ P ⊲ l1 then (meet (join Or P) l2) else undefined) else undefined)"

lemma  persp_data_sym [sym]: 
  "is_persp_data (Or, l1, l2) ⟹ is_persp_data (Or, l2, l1)"
  by simp 

fun persp_domain :: "('p, 'l) persp_data ⇒ 'l"
  where "persp_domain (Or, l1, l2) = (if is_persp_data (Or, l1, l2) then l1 else undefined)"

fun persp_range :: "('p, 'l) persp_data ⇒ 'l"
  where "persp_range (Or, l1, l2) = (if is_persp_data (Or, l1, l2) then l2 else undefined)"

lemma perspectivity_nice: 
  fixes Or P l1 l2
  assumes "P ∈ Points ∧  P ⊲ persp_domain (Or, l1, l2)"
  assumes "is_persp_data (Or, l1, l2)"
  shows "(perspectivity (Or, l1, l2) P) ∈ Points ∧ (perspectivity (Or, l1, l2) P) ⊲ persp_range (Or, l1, l2)"
proof -
  have ss: "((perspectivity (Or, l1, l2) P) ∈ Points) ≡ ((Or ¦ P · l2)  ∈ Points)" 
    using assms assms by auto
  have st: "(Or ¦ P · l2)  ∈ Points" using assms persp_domain.simps meet_properties2 
    join_properties1 join_properties2 is_persp_data.simps by metis
  have su: "(Or ¦ P · l2) ⊲ l2" 
    using meet_properties2 join_properties1[of Or P] assms by auto
  show ?thesis using ss st su assms by auto
qed

lemma perspectivity_nice2: 
  fixes d
  assumes "perspectivity d ≠ undefined"
  shows "is_persp_data d"
proof (rule ccontr)
  assume ch: "¬ is_persp_data d"
  show False using assms ch perspectivity.elims by metis
qed

lemma persp_comp_nice:
  fixes d1 d2 P
  assumes "P ∈ Points ∧ P ⊲ persp_domain d1"
  assumes "is_persp_data d1"
  assumes "is_persp_data d2"
  assumes "persp_range d1 = persp_domain d2"
  shows "(perspectivity d2 (perspectivity d1 P)) ∈ Points ∧ (perspectivity d2 (perspectivity d1 P)) ⊲ persp_range d2"
  by (metis assms(1,2,3,4) is_persp_data.elims(2) perspectivity_nice)

(*
lemma persp_comp_nice2:
  fixes d1 d2 P
  assumes "perspectivity d2 ∘ perspectivity d1 ≠ undefined"
  shows "is_persp_data d1 ∧ is_persp_data d2 ∧ persp_range d1 = persp_domain d2"
proof - 
  have "perspectivity d2 ≠ undefined" using assms by sledgehammer
*)

(*
lemma perspectivity_nice3: 
  fixes Or l1 l2 
  assumes "∀ P . ((P ∈ Points ∧  P ⊲ l1) ⟶ (perspectivity Or l1 l2) P ≠ undefined)" 
  shows "is_persp_data Or l1 l2"
proof (rule ccontr)
  assume ch: "¬ is_persp_data Or l1 l2"
  show False using assms ch perspectivity_def by sledgehammer
qed*)

lemma inverse_persp:
  fixes f d Q
  assumes data_def: "is_persp_data (Or, l1, l2)"
  assumes f_def: "f = perspectivity (Or, l1, l2)"
  assumes g_def: "g = perspectivity (Or, l2, l1)"
  assumes Q_facts: "Q ∈ Points ∧ Q ⊲ l1"
  shows "(g (f Q)) = Q"
proof -
  have f2: "(f Q) = (Or ¦ Q) · l2" unfolding f_def g_def perspectivity.simps using assms by auto
  then have fQnice: "(f Q) ∈ Points ∧ (f Q) ⊲ l2" 
    using Q_facts data_def join_properties1 meet_properties2 by auto
  have gdata_def: "is_persp_data (Or, l2, l1)" using data_def is_persp_data.simps by blast
  have g1: "g (f Q) = (Or ¦ (f Q)) · l1"
    unfolding f_def g_def perspectivity.simps using fQnice f2 Q_facts gdata_def assms by auto
  then have "g (f Q) = (Or ¦ ((Or ¦ Q) · l2)) · l1" using f2 by auto
  then show ?thesis 
    by (smt (verit) Q_facts data_def is_persp_data.simps join_properties1 meet_properties2 unique_meet)
qed

lemma perspectivity_inj:
  fixes f d P Q
  assumes data_def: "is_persp_data d"
  assumes f_def: "f = perspectivity d"
  assumes P_fact: "P ∈ Points ∧ P ⊲ persp_domain d"
  assumes Q_fact: "Q ∈ Points ∧ Q ⊲ persp_domain d"
  assumes equal_image: "f P = f Q"
  shows "P = Q"
  using inverse_persp P_fact Q_fact data_def equal_image f_def is_persp_data.elims(2) persp_domain.simps
    by metis

lemma perspectivity_surj:
  fixes f d Q
  assumes data_def: "is_persp_data d"
  assumes f_def: "f = perspectivity d"
  assumes Q_facts: "Q ∈ Points ∧ Q ⊲ persp_range d"
  shows "∃ P . P ∈ Points ∧ P ⊲ persp_domain d ∧ f P = Q"
  using inverse_persp assms
  by (metis is_persp_data.elims(2) persp_data_sym persp_domain.simps persp_range.simps perspectivity_nice)

lemma perspectivity_bij:
  fixes f d
  assumes data_def: "is_persp_data d"
  assumes f_def: "f = perspectivity d"
  shows "bij_betw f {P ∈ Points. P ⊲ persp_domain d} {Q ∈ Points. Q ⊲ persp_range d}"
proof -
  have inj: "inj_on f {P ∈ Points. P ⊲ persp_domain d}" 
    using perspectivity_inj assms inj_on_def by (smt (verit, best)
    mem_Collect_eq)

  have surj: "f ` {P ∈ Points. P ⊲ persp_domain d} = {Q ∈ Points. Q ⊲ persp_range d}"
  proof
    show "f ` {P ∈ Points. P ⊲ persp_domain d} ⊆ {Q ∈ Points. Q ⊲ persp_range d}" 
      using perspectivity_nice data_def f_def
      by (smt (verit, best) image_Collect_subsetI is_persp_data.elims(2) mem_Collect_eq)
  next
    show "{Q ∈ Points. Q ⊲ persp_range d} ⊆ f ` {P ∈ Points. P ⊲ persp_domain d}"
    proof
      fix x assume "x ∈ {Q ∈ Points. Q ⊲ persp_range d}"
      then have h: "x ∈ Points ∧ x ⊲ persp_range d"
        using mem_Collect_eq by auto

      from h obtain P where "P ∈ Points ∧ P ⊲ persp_domain d ∧ f P = x"
        using perspectivity_surj assms by blast

      thus "x ∈ f ` {P ∈ Points. P ⊲ persp_domain d}"
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
  assumes P_def: "P ∈ Points ∧ P ⊲ persp_domain (Or, l1, l2)"
  assumes P_on_l2: "P ⊲ persp_range (Or, l1, l2)"
  shows "f P = P"
proof-
  have h1: "f = (λP . if P ∈ Points ∧ P ⊲ l1 then (meet (join Or P) l2) else undefined)"
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

fun projectivity :: "(('p, 'l) persp_data) proj_data ⇒ ('p ⇒ 'p)" where
  "projectivity (Cons d []) = (perspectivity d)" |
  "projectivity (Cons d ds) = (projectivity ds) ∘ (perspectivity d)" |
  "projectivity [] = (λ Q . Q)"

fun proj_domain :: "(('p, 'l) persp_data) proj_data ⇒ 'l" where
  "proj_domain (Cons d []) = persp_domain d" |
  "proj_domain (Cons d ds) = persp_domain d" |
  "proj_domain [] = undefined"

fun proj_range :: "(('p, 'l) persp_data) proj_data ⇒ 'l" where
  "proj_range (Cons d []) = persp_range d" |
  "proj_range (Cons d ds) = proj_range ds" |
  "proj_range [] = undefined"

fun is_proj_data :: "(('p, 'l) persp_data) proj_data ⇒ bool" where
  "is_proj_data (Cons d []) = (is_persp_data d)" |
  "is_proj_data (Cons d (Cons d' ds)) = 
    (is_persp_data d ∧ persp_range d = persp_domain d' ∧ is_proj_data (Cons d' ds))" |
  "is_proj_data [] = False"

lemma proj_domain_cons [sym]:
  fixes d ds
  assumes "is_persp_data d"
  assumes "is_proj_data ds"
  assumes "ds ≠ []"
  shows "proj_domain (d # ds) = persp_domain d"
  by (metis assms(3) list.exhaust proj_domain.simps(2))

lemma proj_range_cons [sym]:
  fixes d ds
  assumes "is_persp_data d"
  assumes "is_proj_data ds"
  assumes "ds ≠ []"
  shows "proj_range (d # ds) = proj_range ds"
  by (metis assms(3) list.exhaust proj_range.simps(2))

lemma proj_domain_append [sym]:
  fixes d ds
  assumes "is_proj_data d"
  assumes "is_proj_data ds"
  assumes "ds ≠ []"
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
  assumes "ds ≠ []"
  shows "proj_range (d @ ds) = proj_range ds"
  using assms
proof (induction d)
  case Nil
  then show ?case by auto
next
  case (Cons a ds)
  then show ?case by (metis (no_types, lifting)
    append.left_neutral
    append_Cons
    is_proj_data.simps(2)
    neq_Nil_conv
    proj_range.simps(2))
qed

lemma projectivity_nice: 
  fixes ds P
 (*  assumes "last ((Or, l1, l2) # ds) = (Or', l1', l2')" *)
  shows "is_proj_data ds ⟹ P ∈ Points ∧ P ⊲ proj_domain ds ⟹
        projectivity ds P ∈ Points ∧ 
        projectivity ds P ⊲ proj_range ds"
proof (induction ds arbitrary: "P" )
  case Nil
  then have "False" using Nil.prems(1) is_proj_data.simps(3) by auto
  then show ?case by auto
next
  case (Cons a qs)
  have h0: "is_proj_data qs ⟹
    P ∈ Points ∧ P ⊲ proj_domain qs ⟹ projectivity qs P ∈ Points ∧ projectivity qs P ⊲ proj_range qs" 
    using Cons.IH by blast
  have h1: "is_proj_data (a # qs)" using Cons.prems(1) by auto
  have h2: "P ∈ Points ∧ P ⊲ proj_domain (a # qs)" using Cons.prems(2) by auto
  show ?case
  proof -
    have p1:"(qs = [] ⟶ perspectivity a P ∈ Points ∧ perspectivity a P ⊲ proj_range (a # qs))"
      using Cons.prems(1,2) is_persp_data.elims(2) is_proj_data.simps(1) perspectivity_nice 
        proj_domain.simps proj_range.simps by (smt (verit, del_insts) persp_domain.simps)
    have p2: "(qs ≠ [] ⟶
      projectivity (a # qs) P ∈ Points ∧ projectivity (a # qs) P ⊲ proj_range qs)"
    proof -
      have "projectivity (a # qs) P = ((projectivity qs) ∘ (perspectivity a)) P"
        by (smt (verit, ccfv_threshold) fun.map_ident_strong projectivity.cases
          projectivity.simps(1,2,3))
      also have "... = (projectivity qs) ((perspectivity a) P)" by auto
      finally have p3a: "projectivity (a # qs) P = (projectivity qs) ((perspectivity a) P)" .
      have "is_persp_data a" using Cons.prems(1) is_proj_data.elims(1) by blast
      then have p3: "((perspectivity a P) ∈ Points) ∧ ((perspectivity a P) ⊲ persp_range a)"
        by (smt (z3) Cons.prems(2) is_persp_data.elims(2) is_proj_data.elims(1) p1 proj_domain.simps(2) 
          proj_range.simps(1) projective_plane.perspectivity_nice projective_plane_axioms)
      have "qs ≠ [] ⟶ persp_range a = proj_domain qs" using h1 proj_domain_cons 
          is_proj_data.simps(2) proj_domain.simps(1) projectivity.cases by metis
      then have "qs ≠ [] ⟶ ((perspectivity a P) ∈ Points) ∧ ((perspectivity a P) ⊲ proj_domain qs)" 
        using p3 by metis
      then have "qs ≠ [] ⟶ (projectivity qs (perspectivity a P) ∈ Points ∧ projectivity qs (perspectivity a P) ⊲ proj_range qs)"
        using h0 by (metis Cons.IH h1 is_proj_data.simps(2) list.exhaust)
      then show ?thesis using p3a by auto
    qed
    then show ?case by (metis list.exhaust p1 proj_range.simps(2) projectivity.simps(1))
  qed
qed


lemma projectivity_not_nice: 
  fixes ds P
  assumes "is_proj_data ds"
  assumes "¬(P ∈ Points) ∨ ¬(P ⊲ proj_domain ds)"
  shows "projectivity ds P = undefined"
proof -
  consider (not_point) "¬(P ∈ Points)" | (is_point) "¬(P ⊲ proj_domain ds)" using assms by blast
  then show ?thesis
  proof cases
    case not_point
    then show ?thesis using is_proj_made_up_of_persp by sledgehammer
  next
    case is_point
    then show ?thesis sorry
  qed
qed


(*
fun composition :: "'p list ⇒ 'l list ⇒ 'p list ⇒ 'l list ⇒ ('p ⇒ 'p)"
  where "composition ps ls ps' ls' = (if projectivity ps ls ≠ undefined ∧ projectivity ps' ls' ≠ undefined ∧
  last ls = hd ls' then projectivity (ps @ ps') (ls @ (tl ls')) else undefined)"

fun composition :: "(('p ⇒ 'p)) ⇒ (('p ⇒ 'p)) ⇒ ('p ⇒ 'p)"
  where "composition (projectivity ps ls) (projectivity ps' ls') = (if last ls = hd ls' then
  projectivity (ps @ ps') (ls @ (tl ls')) else undefined)"

fun composition :: "(('p ⇒ 'p)) ⇒ (('p ⇒ 'p)) ⇒ ('p ⇒ 'p)"
  where "composition f f' = (if ∃ ps ls ps' ls' . f = projectivity ps ls ∧ f ≠ undefined ∧ 
  f' = projectivity ps' ls' ∧ f' ≠ undefined ∧ last ls = hd ls' then
  projectivity (ps @ ps') (ls @ (tl ls')) else undefined)"
*)

lemma proj_is_persp_data:
  fixes d ds
  assumes "is_proj_data (d # ds)"
  shows "is_persp_data d"
  using assms is_proj_data.elims(1) by blast

lemma proj_is_persp_data2:
  fixes d ds
  assumes "d ≠ []"
  assumes "is_proj_data d"
  shows "is_persp_data (hd d)"
  using assms list.collapse proj_is_persp_data by metis

lemma proj_data_append_is_data:
  fixes d d'
  assumes "d' ≠ []"
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
  shows "projectivity (d # d') = (projectivity d') ∘ (perspectivity d)"
  using fun.map_ident_strong projectivity.cases
          projectivity.simps(1,2,3) by metis

lemma proj_composition_is_proj:
  fixes d d'
  assumes "proj_range d = proj_domain d'"
  assumes "is_proj_data d"
  assumes "is_proj_data d'"
  shows "projectivity (d @ d') = (projectivity d') ∘ (projectivity d)"
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
  also have h2: "... = (projectivity (ds @ d')) ∘ (perspectivity a)"
    using persp_proj_composition_is_proj by (metis fun.map_ident_strong neq_Nil_conv projectivity.simps(1,2,3))
  also have h3: "... = ((projectivity d') ∘ (projectivity ds)) ∘ (perspectivity a)"
    by (metis (no_types, opaque_lifting)
    Cons.IH Cons.prems(1,2)
    append_Nil assms(3)
    comp_apply
    is_proj_data.simps(2)
    list.exhaust
    proj_range.simps(2)
    projectivity.simps(3))
  also have h4: "... = (projectivity d') ∘ ((projectivity ds) ∘ (perspectivity a))"
    by (simp add: comp_assoc)
  also have h5: "... = (projectivity d') ∘ (projectivity (a # ds))"
    by (metis fun.map_ident_strong
    neq_Nil_conv
    projectivity.simps(1,2,3))
  then show ?case using h1 h2 h3 h4
    by argo
qed 

definition PJ :: "'l ⇒ (('p ⇒ 'p) monoid)" 
  where "PJ l = (if (l ∈ Lines) then
  ⦇carrier = {f . ∃ ds. (f = projectivity ds) ∧ (proj_domain ds = l) ∧ (proj_range ds  = l) ∧ (is_proj_data ds)},
  monoid.mult = (∘),
  one = (λP. if P ∈ Points ∧ P ⊲ l then P else undefined)⦈ 
  else undefined)"

lemma PJ_carrier [simp]:
  fixes l
  assumes "l ∈ Lines"
  shows "carrier (PJ l) = {f . ∃ ds . 
                            (f = projectivity ds) ∧ (proj_domain ds = l) ∧ (proj_range ds = l) ∧ (is_proj_data ds)}"
  using PJ_def assms by auto

lemma PJ_mult [simp]:
  fixes l
  fixes f g :: "'p ⇒ 'p"
  assumes "l ∈ Lines"
  shows "monoid.mult (PJ l) f g = f ∘ g" 
  unfolding PJ_def using assms by auto

lemma PJ_one [simp]:
  fixes l
  assumes "l ∈ Lines"
  shows "one (PJ l) = (λP. if P ∈ Points ∧ P ⊲ l then P else undefined)" 
  unfolding PJ_def using assms by auto

lemma PJ_one_proj [simp]:
  fixes l
  assumes "l ∈ Lines"
  shows "∃ ds. projectivity ds = one (PJ l) ∧ (proj_domain ds = l) ∧ (proj_range ds = l)"
proof -
  obtain Or where Or_def: "Or ∈ Points ∧ ¬ Or ⊲ l" using p3 pcollinear_def assms by fastforce
  let ?f = "perspectivity (Or, l, l)"
  have h1a: "?f = projectivity [(Or, l, l)]" by auto
  have h1b: "∃ ds . (?f = projectivity ds) ∧ (proj_domain ds = l) ∧ (proj_range ds = l)"
    using h1a using Or_def assms by fastforce
  have h1c: "?f ∈ carrier (PJ l)" using h1a h1b assms 
    by (smt (verit, del_insts)
    Or_def PJ_carrier
    is_persp_data.simps
    is_proj_data.simps(1)
    mem_Collect_eq
    persp_domain.simps
    persp_range.simps
    proj_domain.simps(1)
    proj_range.simps(1))
  have h2: "P ∈ Points ∧ P ⊲ l ⟶ meet (join Or P) l = P" for P
    using unique_meet Or_def assms by (metis join_properties1
  meet_properties2)
  have h3: "P ∈ Points ∧ P ⊲ l ⟶ ?f P = P" for P 
    using Or_def assms perspectivity_of_meet_is_itself by auto
  have h4: "¬(P ∈ Points ∧ P ⊲ l) ⟶ ?f P = undefined" for P 
    using Or_def assms by force
  have h5: "?f = (λP. if P ∈ Points ∧ P ⊲ l then P else undefined)" using h3 h4 by auto
  have h6: "?f = one (PJ l)" using h5 assms by auto
  show ?thesis using h1c h6 h1b by auto
qed

lemma PJ_one_proj_constuction [simp]:
  fixes l
  fixes Or
  assumes "l ∈ Lines"
  assumes "Or ∈ Points ∧ ¬ Or ⊲ l"
  shows "projectivity [(Or, l, l)] = one (PJ l)"
proof -
  let ?f = "perspectivity (Or, l, l)"
  have h1a: "?f = projectivity [(Or, l, l)]" by auto
  have h1b: "∃ ds . (?f = projectivity ds) ∧ (proj_domain ds = l) ∧ (proj_range ds = l)"
    using h1a using assms by fastforce
  have h1c: "?f ∈ carrier (PJ l)" using h1a h1b assms 
    by (smt (verit, del_insts)
    PJ_carrier
    is_persp_data.simps
    is_proj_data.simps(1)
    mem_Collect_eq
    persp_domain.simps
    persp_range.simps
    proj_domain.simps(1)
    proj_range.simps(1))
  have h2: "P ∈ Points ∧ P ⊲ l ⟶ meet (join Or P) l = P" for P 
    using unique_meet assms by (metis join_properties1 meet_properties2)
  have h3: "P ∈ Points ∧ P ⊲ l ⟶ ?f P = P" for P 
    using assms perspectivity_of_meet_is_itself by auto
  have h4: "¬(P ∈ Points ∧ P ⊲ l) ⟶ ?f P = undefined" for P 
    using assms by force
  have h5: "?f = (λP. if P ∈ Points ∧ P ⊲ l then P else undefined)" using h3 h4 by auto
  have h6: "?f = one (PJ l)" using h5 assms by auto
  show ?thesis using h1c h6 h1b by auto
qed

(* Proposition 4.8 Let l be a line. Then the set of projectivities of l into itself forms a group, which we will call PJ(l). *)
lemma
  fixes l
  assumes "l ∈ Lines"
  shows PJ_group: "group (PJ l)"
proof -
  show "group (PJ l)"
  proof (unfold_locales, goal_cases)
    case (1 f g)
    obtain ds where f_proj: "f = projectivity ds ∧ proj_domain ds = l ∧ proj_range ds = l ∧ is_proj_data ds" 
      using "1"(1) assms by auto
    obtain ds' where g_proj: "g = projectivity ds' ∧ proj_domain ds' = l ∧ proj_range ds' = l ∧ is_proj_data ds'" 
      using "1"(2) assms by auto
    have h1: "f ∘ g = (projectivity ds) ∘ (projectivity ds')" 
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
    obtain Or where Or_def: "Or ∈ Points ∧ ¬ Or ⊲ l" using p3 pcollinear_def assms by fastforce
    let ?f = "perspectivity (Or, l, l)"
    have h1a: "?f = projectivity [(Or, l, l)]" by auto
    have h1b: "∃ ds . (?f = projectivity ds) ∧ (proj_domain ds = l) ∧ (proj_range ds = l)"
      using h1a using Or_def assms by fastforce
    have h1c: "?f ∈ carrier (PJ l)" using h1a h1b assms 
      by (smt (verit, del_insts)
      Or_def PJ_carrier
      is_persp_data.simps
      is_proj_data.simps(1)
      mem_Collect_eq
      persp_domain.simps
      persp_range.simps
      proj_domain.simps(1)
      proj_range.simps(1))
    have h2: "P ∈ Points ∧ P ⊲ l ⟶ meet (join Or P) l = P" for P 
      using unique_meet Or_def assms by (metis join_properties1
    meet_properties2)
    have h3: "P ∈ Points ∧ P ⊲ l ⟶ ?f P = P" for P 
      using Or_def assms perspectivity_of_meet_is_itself by auto
    have h4: "¬(P ∈ Points ∧ P ⊲ l) ⟶ ?f P = undefined" for P 
      using Or_def assms by force
    have h5: "?f = (λP. if P ∈ Points ∧ P ⊲ l then P else undefined)" using h3 h4 by auto
    have h6: "?f = one (PJ l)" using h5 assms by auto
    show ?case using h1c h6 by force
  next
    case (4 x)
    obtain ds where h0: "x = projectivity ds ∧ proj_domain ds = l ∧ proj_range ds = l ∧ is_proj_data ds" using "4" assms by auto
    obtain Or where Or_def: "Or ∈ Points ∧ ¬ Or ⊲ l" using p3 pcollinear_def assms by fastforce
    then have h1: "projectivity [(Or, l, l)] = one (PJ l)" using assms PJ_one_proj_constuction assms by blast
    then have h2: "Q ∈ Points ∧ Q ⊲ l ⟶ (one (PJ l)) Q = Q" for Q
      using PJ_one assms by presburger
    then have h3: "Q ∈ Points ∧ Q ⊲ l ⟶ (x Q) ∈ Points ∧ (x Q) ⊲ l" for Q 
      using "4" assms projectivity_nice by fastforce
    then have h4: "Q ∈ Points ∧ Q ⊲ l ⟶  projectivity [(Or, l, l)] (x Q) = x Q" for Q 
      using assms "4" projectivity_nice h1 by auto
    then have h5: "Q ∈ Points ∧ Q ⊲ l ⟶ (one (PJ l) ∘ x) Q = x Q" for Q 
      using h0 h1 by auto
    then have h6: "¬(Q ∈ Points ∧ Q ⊲ l) ⟶ one (PJ l) Q = undefined" for Q 
      using PJ_one assms by presburger
    then have h7: "¬(Q ∈ Points ∧ Q ⊲ l) ⟶ x Q = undefined" for Q 
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
    have "⋀f . f ∈ carrier (PJ l) ⟶ True" by blast
    then show ?case using inverse_persp perspectivity_bij unfolding PJ_def
  qed
qed

lemma double_non_containing_line:
  fixes A B l
  assumes AB_def: "A ∈ Points ∧ B ∈ Points"
  assumes l_def: "l ∈ Lines ∧ A ⊲ l ∧ B ⊲ l ∧ C ⊲ l"
  shows "∃ l' . l' ∈ Lines ∧ l' ≠ l ∧ ¬ A ⊲ l' ∧ ¬ B ⊲ l'" 
proof-
  obtain C where C_def: "C ∈ Points ∧ C ⊲ l ∧ C ≠ A ∧ C ≠ B" 
    using l_def p4 distinct_length_2_or_more mem_Collect_eq by (metis (no_types, lifting))
  obtain D where D_def: "D ∈ Points ∧ ¬ D ⊲ l" using l_def p3 pcollinear_def by metis
  let ?l' = "join D C"
  have h1: "?l' ∈ Lines ∧ ?l' ≠ l" using AB_def C_def D_def l_def join_properties1 by blast
  have h3: "¬ A ⊲ ?l' ∧ ¬ B ⊲ ?l'" 
    using AB_def C_def D_def h1 join_properties1 l_def unique_meet p1 by metis
  show ?thesis using h1 h3 by auto
qed

lemma triplet_to_triplet_diff_lines:
  fixes A B C A' B' C' l l'
  assumes ABC_def: "A ∈ Points ∧ B ∈ Points ∧ C ∈ Points ∧ distinct [A, B, C]"
  assumes ABC'_def: "A' ∈ Points ∧ B' ∈ Points ∧ C' ∈ Points ∧ distinct [A', B', C']"
  assumes l_def: "l ∈ Lines ∧ A ⊲ l ∧ B ⊲ l ∧ C ⊲ l"
  assumes l'_def: "l' ∈ Lines ∧ A' ⊲ l' ∧ B' ⊲ l' ∧ C' ⊲ l'"
  shows "∃ ps . ∃ ls . ∃ f . (f = projectivity ps ls) 
                        ∧ (hd ls = l) ∧ (last ls = l') 
                        ∧ (f A = A') ∧ (f B = B') ∧ (f C = C')"
  sorry  

(* Proposition 4.9 Let l be a line, and let A, B, C, and A′, B′, C′ be two triples of three distinct points each on l.
Then there is a projectivity of l into itself which sends A, B, C into A′, B′, C′. *)
lemma (in projective_plane) triplet_to_triplet_same_line:
  fixes A B C A' B' C' l
  assumes ABC_def: "A ∈ Points ∧ B ∈ Points ∧ C ∈ Points ∧ distinct [A, B, C]"
  assumes ABC'_def: "A' ∈ Points ∧ B' ∈ Points ∧ C' ∈ Points ∧ distinct [A', B', C']"
  assumes l_def: "l ∈ Lines ∧ A ⊲ l ∧ B ⊲ l ∧ C ⊲ l ∧ A' ⊲ l ∧ B' ⊲ l ∧ C' ⊲ l"
  shows "∃ ds . ∃ f . (f = projectivity ds) 
                        ∧ (proj_domain ds = l) ∧ (proj_range ds = l) 
                        ∧ (f A = A') ∧ (f B = B') ∧ (f C = C')"
  sorry
(* proof-
  have h1: "∃ l' . l' ∈ Lines ∧ l' ≠ l" using non_containing_line p1 p3 by blast
  obtain l' where l'_def: "l' ∈ Lines ∧ l' ≠ l ∧ ¬ A ⊲ l' ∧ ¬ A' ⊲ l'" 
    using double_non_containing_line[of A A' l] ABC'_def ABC_def l_def by auto
  obtain A'' B'' C'' where ABC''_def: "A'' ∈ Points ∧ B'' ∈ Points ∧ C'' ∈ Points 
    ∧ distinct [A'', B'', C''] ∧ A'' ⊲ l' ∧ B'' ⊲ l' ∧ C'' ⊲ l'"
    using p4 l'_def ABC'_def by fastforce
  obtain ps ls f where f_def: "(f = projectivity ps ls) ∧ (hd ls = l) ∧ (last ls = l') 
    ∧ (f A = A'') ∧ (f B = B'') ∧ (f C = C'')"
    using triplet_to_triplet_diff_lines[of A B C A'' B'' C'' l l'] ABC_def ABC''_def l'_def l_def by blast
  obtain ps' ls' f' where f'_def: "(f' = projectivity ps' ls') ∧ (hd ls' = l') ∧ (last ls' = l) 
    ∧ (f' A'' = A') ∧ (f' B'' = B') ∧ (f' C'' = C')"
    using triplet_to_triplet_diff_lines[of A'' B'' C'' A' B' C' l' l] ABC''_def ABC'_def l'_def l_def by blast
  let ?ps'' = "ps @ ps'"
  let ?ls'' = "ls @ tl ls'"
  let ?f'' = "f' ∘ f"
  have h2: "?f'' = projectivity ?ps'' ?ls''" 
    using proj_composition_is_proj[of f ps ls f' ps' ls'] f_def f'_def by auto
  have h3: "(hd ?ls'' = l) ∧ (last ?ls'' = l)" 
    using h2 f'_def f_def hd_Nil_eq_last hd_append2 l'_def last_ConsL last_append last_tl list.collapse
    by metis
  have h4: "(?f'' A = A') ∧ (?f'' B = B') ∧ (?f'' C = C')"
    using f_def f'_def by auto
  show ?thesis using h2 h3 h4 by auto
qed *)

lemma perspectivity_hquad_to_hquad:
  fixes A B C D f
  assumes ABCD_def: "A ∈ Points ∧ B ∈ Points ∧ C ∈ Points ∧ D ∈ Points ∧ harmonic_quadruple A B C D"
  assumes data_def: "Q ∈ Points ∧ l1 ∈ Lines ∧ l2 ∈ Lines ∧ is_persp_data Or l1 l2"
  assumes f_def: "f = perspectivity Or l1 l2"
  assumes ABCD'_def: "A' = f A ∧ B' = f B ∧ C' = f C ∧ D' = f D"
  shows "harmonic_quadruple A' B' C' D'"
proof -
   have A'_def: "A' = (perspectivity Q l1 l2) A" 
    and B'_def: "B' = (perspectivity Q l1 l2) B"
    and C'_def: "C' = (perspectivity Q l1 l2) C"
    and D'_def: "D' = (perspectivity Q l1 l2) D"
    using f_def ABCD'_def sorry

  have A'_on_l2: "A' ∈ Points ∧ A' ⊲ l2"
    and B'_on_l2: "B' ∈ Points ∧ B' ⊲ l2"
    and C'_on_l2: "C' ∈ Points ∧ C' ⊲ l2"
    and D'_on_l2: "D' ∈ Points ∧ D' ⊲ l2"
    using A'_def B'_def C'_def D'_def ABCD_def sorry

  let ?l'' = "join A B'"

  let ?X = "meet (join B C') (join Q A)"

  have X_on_OA: "?X ∈ Points ∧ ?X ⊲ (join Q A)"
    and X_on_BC': "?X ∈ Points ∧ ?X ⊲ (join B C')"
    using join_properties1 meet_properties2 sorry

  have "meet (join X B') ?l'' = D"
  proof -
    have "C ∈ Points ∧ C ⊲ (join Q C')"
      using C'_def perspectivity_def join_properties1 join_properties2 meet_properties2 sorry

    have "meet (join ?X B') ?l'' = D"
      using ABCD_def A'_def B'_def C'_def D'_def sorry
    thus ?thesis sorry
  qed
  thus ?thesis sorry
qed



(* Proposition 4.10 A projectivity takes harmonic quadruples into harmonic quadruples. *)
lemma projectivity_hquad_to_hquad:
  fixes A B C D f
  assumes ABCD_def: "A ∈ Points ∧ B ∈ Points ∧ C ∈ Points ∧ C ∈ Points ∧ (harmonic_quadruple A B C D)"
  assumes f_def: "∃ ps . ∃ ls . (f = projectivity ps ls)"
  assumes ABCD'_def: "A' = f(A) ∧ B' = f(B) ∧ C' = f(C) ∧ D' = f(D)"
  shows "harmonic_quadruple A' B' C' D'"
  sorry

(* Previous attempts:

type_synonym ('a, 'b) persp_data = "'a × 'b × 'b"

definition is_persp_data :: "persp_data ⇒ bool" 
  where "is_persp_data (Or, l1, l2) = (if Or ∈ Points ∧ l1 ∈ Lines ∧ l2 ∈ Lines 
  then (¬ (incid Or l1) ∧ ¬ (incid Or l2)) else undefined)"

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
     p1: "Or ∈ Points" and
     p2: "l1 ∈ Lines ∧ l2 ∈ Lines" and
     p3: "(¬ (incid Or l1) ∧ ¬ (incid Or l2))"
end*)
end
end


