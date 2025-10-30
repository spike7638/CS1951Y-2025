theory "Chapter4-4"
  imports Complex_Main  "Chapter4-3" "HOL-Algebra.Group"
begin
text\<open> start at "Perspectivies and Projectivities" and go to end of chapter\<close>

definition (in projective_plane) isperspectivity :: "'p \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool" 
  where "isperspectivity Or l1 l2 = (if Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines 
  then (\<not> (Or \<lhd> l1) \<and> \<not> (Or \<lhd> l2)) else undefined)"

definition (in projective_plane) perspectivity :: "'p \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> ('p \<Rightarrow> 'p)"
  where "perspectivity Or l1 l2 = (if (Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> isperspectivity Or l1 l2)
  then (\<lambda>P . if P \<in> Points \<and> P \<lhd> l1 then (meet (join Or P) l2) else undefined) else undefined)"

lemma (in projective_plane) perspectivity_inj:
  fixes f Or l1 l2 P Q
  assumes l1_def: "l1 \<in> Lines"
  assumes l2_def: "l2 \<in> Lines"
  assumes Or_def: "Or \<in> Points \<and> \<not> (Or \<lhd> l1) \<and> \<not> (Or \<lhd> l2)"
  assumes f_def: "f = perspectivity Or l1 l2"
  assumes P_def: "P \<in> Points \<and> P \<lhd> l1"
  assumes Q_def: "Q \<in> Points \<and> Q \<lhd> l1"
  assumes PQ_neq: "f P = f Q"
  shows "P = Q"
  using assms perspectivity_def[of Or l1 l2] isperspectivity_def[of Or l1 l2] join_properties2 meet_properties2 p1
    by (smt (verit))
 
lemma (in projective_plane) perspectivity_surj:
  fixes f Or l1 l2 Q
  assumes l1_def: "l1 \<in> Lines"
  assumes l2_def: "l2 \<in> Lines"
  assumes Or_def: "Or \<in> Points \<and> \<not> (Or \<lhd> l1) \<and> \<not> (Or \<lhd> l2)"
  assumes f_def: "f = perspectivity Or l1 l2"
  assumes Q_def: "Q \<in> Points \<and> Q \<lhd> l2"
  shows "\<exists> P . P \<in> Points \<and> P \<lhd> l1 \<and> f P = Q"
proof -
  have h0: "isperspectivity Or l1 l2 = True" using Or_def isperspectivity_def[of Or l1 l2] l1_def l2_def by presburger
  let ?P = "meet l1 (join Or Q)"
  have h1: "?P \<in> Points \<and> ?P \<lhd> l1" using Or_def Q_def join_properties1 l1_def meet_properties2 
    by auto
  have h2: "f ?P = Q" using assms h0 h1 perspectivity_def[of Or l1 l2] join_properties1 join_properties2 meet_properties2 punctured_r_3_def 
    by (smt (z3))
  show ?thesis using h1 h2 by auto
qed

lemma (in projective_plane) inv_is_perspectivity:
  fixes f Or l1 l2 f_inv P
  assumes data_def: "Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> isperspectivity Or l1 l2"
  (*assumes Or_def: "Or \<in> Points \<and> \<not> (Or \<lhd> l1) \<and> \<not> (Or \<lhd> l2)"
  assumes l1_def: "l1 \<in> Lines"
  assumes l2_def: "l2 \<in> Lines"
  assumes f_def: "f = perspectivity Or l1 l2"*)
  assumes P_def: "P \<in> Points \<and> P \<lhd> l1"
  assumes f_inv_def: "f_inv (f P) = P"
  shows "f_inv = perspectivity Or l2 l1"
  sorry

lemma (in projective_plane) perspectivity_of_meet_is_itself:
  fixes f Or l1 l2 P
  assumes data_def: "Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> isperspectivity Or l1 l2"
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
    using P_on_l2 P_def data_def isperspectivity_def join_properties1 meet_properties2 unique_meet
    by metis
  show ?thesis using h2 h3 by auto
qed

(* Definition. A projectivity is a mapping of one line l into another l\<Zprime> (which may be equal to l), which can be expressed as a composition of perspectivities. 
We write l Z l\<Zprime>, and write ABC . . . Z A\<Zprime>B\<Zprime>C\<Zprime> . . . if the projectivity that takes  points A, B, C, . . . into A\<Zprime>, B\<Zprime>, C\<Zprime>, . . . respectively. 
Note that a projectivity also is always one-to-one and onto. *)
fun (in projective_plane) projectivity :: "'p list \<Rightarrow> 'l list \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "projectivity (Cons p []) (Cons l1 (Cons l2 [])) = (perspectivity p l1 l2)" |
  "projectivity (Cons p ps) (Cons l1 (Cons l2 ls)) = (projectivity ps (Cons l2 ls)) \<circ> (perspectivity p l1 l2)" |
  "projectivity [] b = undefined" |
  "projectivity a [] = undefined" |
  "projectivity a [v] = undefined"

definition (in projective_plane) PJ :: "'l \<Rightarrow> (('p \<Rightarrow> 'p) monoid)" 
  where "PJ l = (if (l \<in> Lines) then
  \<lparr>carrier = {f . \<exists> ps . \<exists> ls . (f = projectivity ps ls) \<and> (hd ls = l) \<and> (last ls = l)},
  monoid.mult = (\<circ>),
  one = (\<lambda>Q. Q)\<rparr> 
  else undefined)"

lemma (in projective_plane) proj_composition_is_proj:
  fixes ps ps' ls ls' f f'
  assumes f_def: "f = projectivity ps ls"
  assumes f'_def: "f' = projectivity ps' ls'"
  assumes ls_ls'_def: "last ls = hd ls'"
  shows "f' \<circ> f = projectivity (ps @ ps') (ls @ (tl ls'))"
  sorry

(*may need to create a projectivity identity element*)

(* Proposition 4.8 Let l be a line. Then the set of projectivities of l into itself forms a group, which we will call PJ(l). *)
lemma (in projective_plane) PJ_l_is_group:
  fixes l
  assumes l_def: "l \<in> Lines"
  shows "group (PJ l)"
  sorry

lemma (in projective_plane) double_non_containing_line:
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

lemma (in projective_plane) triplet_to_triplet_diff_lines:
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

(* Proposition 4.10 A projectivity takes harmonic quadruples into harmonic quadruples. *)
lemma (in projective_plane) projectivity_hquad_to_hquad:
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


