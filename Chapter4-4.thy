theory "Chapter4-4"
  imports Complex_Main  "Chapter4-3" "HOL-Algebra.Group"
begin

context projective_plane
begin
text\<open> start at "Perspectivies and Projectivities" and go to end of chapter\<close>

definition is_persp_data :: "'p \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool" 
  where "is_persp_data Or l1 l2 = (if Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines 
  then (\<not> (Or \<lhd> l1) \<and> \<not> (Or \<lhd> l2)) else undefined)"

definition perspectivity :: "'p \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> ('p \<Rightarrow> 'p)"
  where "perspectivity Or l1 l2 = (if (Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> is_persp_data Or l1 l2)
  then (\<lambda>P . if P \<in> Points \<and> P \<lhd> l1 then (meet (join Or P) l2) else undefined) else undefined)"

lemma perspectivity_inj:
  fixes f Or l1 l2 P Q
  assumes data_def: "Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> is_persp_data Or l1 l2"
  assumes f_def: "f = perspectivity Or l1 l2"
  assumes P_def: "P \<in> Points \<and> P \<lhd> l1"
  assumes Q_def: "Q \<in> Points \<and> Q \<lhd> l1"
  assumes PQ_neq: "f P = f Q"
  shows "P = Q"
  using assms perspectivity_def[of Or l1 l2] is_persp_data_def[of Or l1 l2] join_properties2 meet_properties2 p1
    by (smt (verit))
 
lemma perspectivity_surj:
  fixes f Or l1 l2 Q
  assumes data_def: "Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> is_persp_data Or l1 l2"
  assumes f_def: "f = perspectivity Or l1 l2"
  assumes Q_def: "Q \<in> Points \<and> Q \<lhd> l2"
  shows "\<exists> P . P \<in> Points \<and> P \<lhd> l1 \<and> f P = Q"
proof -
  have h0: "is_persp_data Or l1 l2 = True" using data_def is_persp_data_def[of Or l1 l2] by presburger
  let ?P = "meet l1 (join Or Q)"
  have h1: "?P \<in> Points \<and> ?P \<lhd> l1" 
    using data_def Q_def join_properties1 meet_properties2 is_persp_data_def[of Or l1 l2] 
    by metis
  have h2: "f ?P = Q" 
    using assms h0 h1 perspectivity_def[of Or l1 l2] join_properties1 join_properties2 meet_properties2 punctured_r_3_def is_persp_data_def 
    by (smt (z3))
  show ?thesis using h1 h2 by auto
qed

lemma perspectivity_bij:
  fixes f Or l1 l2
  assumes data_def: "Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> is_persp_data Or l1 l2"
  assumes f_def: "f = perspectivity Or l1 l2"
  shows "bij_betw f {P \<in> Points. P \<lhd> l1} {Q \<in> Points. Q \<lhd> l2}"
proof -
  have inj: "inj_on f {P \<in> Points. P \<lhd> l1}"
    using perspectivity_inj assms inj_on_def by (smt (verit, best)
    mem_Collect_eq)

  have surj: "f ` {P \<in> Points. P \<lhd> l1} = {Q \<in> Points. Q \<lhd> l2}"
  proof
    show "f ` {P \<in> Points. P \<lhd> l1} \<subseteq> {Q \<in> Points. Q \<lhd> l2}"
      using assms perspectivity_def is_persp_data_def
      by (smt (verit, del_insts) imageE
    join_properties1 meet_properties2
    mem_Collect_eq subsetI)
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

lemma perspectivity_has_inverse:
  assumes data_def: "Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> is_persp_data Or l1 l2"
  shows "\<exists> g. bij_betw g {Q \<in> Points. Q \<lhd> l2} {P \<in> Points. P \<lhd> l1}"
proof -
  let ?f = "perspectivity Or l1 l2"
  from perspectivity_bij[OF data_def refl]
  obtain g where "g = inv_into {P \<in> Points. P \<lhd> l1} ?f"
    by blast
  thus ?thesis using
    \<open>bij_betw (perspectivity Or l1 l2) {P \<in> Points. P \<lhd> l1} {Q \<in> Points. Q \<lhd> l2}\<close>
    bij_betw_inv_into by blast
qed

(* lemma (in projective_plane) inv_is_perspectivity:
  fixes Or l1 l2 f f_inv
  assumes data_def: "Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> is_persp_data Or l1 l2"
  (*assumes Or_def: "Or \<in> Points \<and> \<not> (Or \<lhd> l1) \<and> \<not> (Or \<lhd> l2)"
  assumes l1_def: "l1 \<in> Lines"
  assumes l2_def: "l2 \<in> Lines"*)
  assumes f_def: "f = perspectivity Or l1 l2"
  assumes f_inv_def: "\<forall> P . if P \<in> Points \<and> P \<lhd> l1 then f_inv (f P) = P else f_inv (f P) = undefined"
  (*assumes f_inv_def: "f_inv = (\<lambda>Q . if Q = f P then P else undefined)"*)
  (*assumes f_inv_def: "f_inv = (\<lambda>Q . if \<exists>P . f P = Q then P else undefined)"*)
  (*\<forall> P . P \<in> Points \<and> P \<lhd> l1 \<longrightarrow> f_inv (f P) = P"*)
  (*assumes P_def: "P \<in> Points \<and> P \<lhd> l1"
  assumes f_inv_def: "f_inv (f P) = P"*)
  shows "f_inv = perspectivity Or l2 l1"
proof-
  have h1: "f = (\<lambda>P . if P \<in> Points \<and> P \<lhd> l1 then (meet (join Or P) l2) else undefined)"
    using data_def f_def perspectivity_def[of Or l1 l2] by presburger
  have h2: "f_inv = (\<lambda>Q . if \<exists>P . P \<in> Points \<and> P \<lhd> l1 \<and> (meet (join Or P) l2) = Q then P else undefined)"
    using h1 f_inv_def by sledgehammer
  have h2: "\<forall> P . P \<in> Points \<and> P \<lhd> l1 \<longrightarrow> f_inv (meet (join Or P) l2) = P"
    using h1 f_inv_def by auto
  have h3: "\<forall> Q . Q \<in> Points \<and> Q \<lhd> l2 \<longrightarrow> (\<exists> P . P \<in> Points \<and> P \<lhd> l1 \<and> f P = Q)"
    using perspectivity_surj assms by auto
  have h4: "\<forall> Q . Q \<in> Points \<and> Q \<lhd> l2 \<longrightarrow> (\<exists> P . P \<in> Points \<and> P \<lhd> l1 \<and> (meet (join Or P) l2) = Q)"
    using h1 h3 by metis
  have h5: "\<forall> Q . Q \<in> Points \<and> Q \<lhd> l2 \<longrightarrow> (\<exists> P . P \<in> Points \<and> P \<lhd> l1 \<and> f_inv (meet (join Or P) l2) = P)"
    using h4 h2 by auto
  have h6: "\<forall> Q . Q \<in> Points \<and> Q \<lhd> l2 \<longrightarrow> (f_inv Q = (meet (join Or Q) l1))"
    using h4 h2 data_def is_persp_data_def join_properties1 join_properties2 meet_properties2
    by (smt (verit))
  show ?thesis using h6 perspectivity_def[of Or l2 l1] by sledgehammer
  have h7: "f_inv = (\<lambda>Q . if Q \<in> Points \<and> Q \<lhd> l2 then (meet (join Or Q) l1) else undefined)"
    using  *)

lemma inv_is_perspectivity:
  fixes Or l1 l2 f f_inv
  assumes data_def: "Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> is_persp_data Or l1 l2"
  assumes f_def: "f = perspectivity Or l1 l2"
  (* assumes f_inv_def: "\<And>P. P \<in> Points \<and> P \<lhd> l1 \<Longrightarrow> f_inv (f P) = P" *)
  assumes f_inv_def: "\<And>P. (if P \<in> Points \<and> P \<lhd> l1 then (f_inv (f P) = P) else (f_inv (f P) = undefined))" 
  shows "f_inv = perspectivity Or l2 l1"
proof (rule ext)
  fix Q :: 'p
  show "f_inv Q = perspectivity Or l2 l1 Q"
  proof (cases "Q \<in> Points \<and> Q \<lhd> l2")
    case False
    then show ?thesis by sledgehammer
  next
    case True
    then obtain P where P_props: "P \<in> Points \<and> P \<lhd> l1 \<and> f P = Q"
      using perspectivity_surj[OF data_def f_def True] by blast

    from P_props have "f_inv Q = P"
      using f_inv_def P_props by blast

    moreover have "perspectivity Or l2 l1 Q = P"
    proof -
      have persp_Q: "perspectivity Or l2 l1 Q = meet l1 (join Or Q)"
        using perspectivity_def data_def True by (smt (verit, del_insts)
    is_persp_data_def join_properties1
    meet_properties2 s)

      moreover from P_props have "P = meet l1 (join Or Q)"
        using data_def P_props join_properties1 join_properties2 meet_properties2
        unfolding is_persp_data_def perspectivity_def f_def
        by smt
      ultimately show ?thesis by simp
    qed

    ultimately show ?thesis by simp
  qed
qed


lemma perspectivity_of_meet_is_itself:
  fixes f Or l1 l2 P
  assumes data_def: "Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> is_persp_data Or l1 l2"
  (*assumes Or_def: "Or \<in> Points"
  assumes l1_def: "l1 \<in> Lines"
  assumes l2_def: "l2 \<in> Lines"
  *)
  assumes f_def: "f = perspectivity Or l1 l2"
  assumes P_def: "P \<in> Points \<and> P \<lhd> l1"
  assumes P_on_l2: "P \<lhd> l2"
  shows "f P = P"
  (*using Or_def P_def P_on_l2 f_def inv_is_perspectivity l1_def l2_def by fastforce*)
proof-
  have h1: "f = (\<lambda>P . if P \<in> Points \<and> P \<lhd> l1 then (meet (join Or P) l2) else undefined)"
    using data_def f_def perspectivity_def[of Or l1 l2] by presburger
  have h2: "f P = (meet (join Or P) l2)" using h1 P_def by auto
  have h3: "(meet (join Or P) l2) = P" 
    using P_on_l2 P_def data_def is_persp_data_def join_properties1 meet_properties2 unique_meet
    by metis
  show ?thesis using h2 h3 by auto
qed

(* Definition. A projectivity is a mapping of one line l into another l\<Zprime> (which may be equal to l), which can be expressed as a composition of perspectivities. 
We write l Z l\<Zprime>, and write ABC . . . Z A\<Zprime>B\<Zprime>C\<Zprime> . . . if the projectivity that takes  points A, B, C, . . . into A\<Zprime>, B\<Zprime>, C\<Zprime>, . . . respectively. 
Note that a projectivity also is always one-to-one and onto. *)
fun projectivity :: "'p list \<Rightarrow> 'l list \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "projectivity (Cons p []) (Cons l1 (Cons l2 [])) = (perspectivity p l1 l2)" |
  "projectivity (Cons p ps) (Cons l1 (Cons l2 ls)) = (projectivity ps (Cons l2 ls)) \<circ> (perspectivity p l1 l2)" |
  "projectivity [] b = undefined" |
  "projectivity a [] = undefined" |
  "projectivity a [v] = undefined"
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
(*
lemma proj_composition_is_proj:
  fixes ps ps' ls ls' f f'
  assumes f_def: "f = projectivity ps ls"
  assumes f'_def: "f' = projectivity ps' ls'"
  assumes ls_ls'_def: "last ls = hd ls'"
  shows "f' \<circ> f = projectivity (ps @ ps') (ls @ (tl ls'))"
  sorry*)

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
    case (1 x y)
    then show ?case unfolding PJ_def sorry
  next
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
      using Or_def assms is_persp_data_def perspectivity_of_meet_is_itself by auto
    have h4: "\<not>(P \<in> Points \<and> P \<lhd> l) \<longrightarrow> ?f P = undefined" for P 
      using perspectivity_def[of Or l l] Or_def assms is_persp_data_def by force
    have h5: "?f = (\<lambda>P. if P \<in> Points \<and> P \<lhd> l then P else undefined)" using h3 h4 by auto
    have h6: "?f = one (PJ l)" using h5 assms by auto
    show ?case using h1c h6 by force
  next
    case (4 x)
    then show ?case sorry
  next
    case (5 x)
    then show ?case sorry
  next
    case 6
    then show ?case sorry
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
    using AB_def C_def D_def h1 join_properties1 l_def unique_meet by metis
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
  assumes data_def: "Q \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> is_persp_data Or l1 l2"
  assumes f_def: "f = perspectivity Or l1 l2"
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


