theory "Chapter4-4"
  imports Complex_Main  "Chapter4-3"
begin
text\<open> start at "Perspectivies and Projectivities" and go to end of chapter\<close>

(*This stuff took us two hours... we'll keep going when we have time to meet again*)

definition (in projective_plane_data2) isperspectivity :: "'p \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool" 
  where "isperspectivity Or l1 l2 = (if Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines 
  then (\<not> (incid Or l1) \<and> \<not> (incid Or l2)) else undefined)"

definition (in projective_plane_data2) perspectivity :: "'p \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> ('p \<Rightarrow> 'p)"
  where "perspectivity Or l1 l2 = (if (Or \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> isperspectivity Or l1 l2)
  then (\<lambda>Q . if Q \<in> Points \<and> incid Q l1 then (meet (join Or Q) l2) else undefined) else undefined)"

lemma (in projective_plane_data2) perspectivity_inj:
  fixes f Or l1 l2 P Q
  assumes l1_def: "l1 \<in> Lines"
  assumes l2_def: "l2 \<in> Lines"
  assumes Or_def: "Or \<in> Points \<and> \<not> (Or \<lhd> l1) \<and> \<not> (Or \<lhd> l2)"
  assumes f_def: "f = perspectivity Or l1 l2"
  assumes P_def: "P \<in> Points \<and> P \<lhd> l1"
  assumes Q_def: "Q \<in> Points \<and> Q \<lhd> l1"
  assumes PQ_neq: "P \<noteq> Q"
  shows "f P \<noteq> f Q"
  sorry

lemma (in projective_plane_data2) perspectivity_surj:
  fixes f Or l1 l2 Q
  assumes l1_def: "l1 \<in> Lines"
  assumes l2_def: "l2 \<in> Lines"
  assumes Or_def: "Or \<in> Points \<and> \<not> (Or \<lhd> l1) \<and> \<not> (Or \<lhd> l2)"
  assumes f_def: "f = perspectivity Or l1 l2"
  assumes Q_def: "Q \<in> Points \<and> Q \<lhd> l2"
  shows "\<exists> P . P \<in> Points \<and> P \<lhd> l1 \<and> f P = Q"
  sorry

lemma (in projective_plane_data2) inv_is_perspectivity:
  fixes f Or l1 l2 f_inv P
  assumes Or_def: "Or \<in> Points"
  assumes l1_def: "l1 \<in> Lines"
  assumes l2_def: "l2 \<in> Lines"
  assumes f_def: "f = perspectivity Or l1 l2"
  assumes P_def: "P \<in> Points \<and> P \<lhd> l1"
  assumes f_inv_def: "f_inv (f P) = P"
  shows "f_inv = perspectivity Or l2 l1"
  sorry

lemma (in projective_plane_data2) perspectivity_of_meet_is_itself:
  fixes f Or l1 l2 P
  assumes Or_def: "Or \<in> Points"
  assumes l1_def: "l1 \<in> Lines"
  assumes l2_def: "l2 \<in> Lines"
  assumes f_def: "f = perspectivity Or l1 l2"
  assumes P_def: "P \<in> Points \<and> P \<lhd> l1"
  assumes P_on_l2: "P \<lhd> l2"
  shows "f P = P"
  sorry

(* Definition. A projectivity is a mapping of one line l into another l\<Zprime> (which may be equal to l), which can be expressed as a composition of perspectivities. We write l Z l\<Zprime>, and write ABC . . . Z A\<Zprime>B\<Zprime>C\<Zprime> . . . if the projectivity that takes  points A, B, C, . . . into A\<Zprime>, B\<Zprime>, C\<Zprime>, . . . respectively. Note that a projectivity also is always one-to-one and onto.   *)

fun (in projective_plane_data2) projectivity :: "'p list \<Rightarrow> 'l list \<Rightarrow> ('p \<Rightarrow> 'p)" where
  "projectivity (Cons p []) (Cons l1 (Cons l2 [])) = (perspectivity p l1 l2)" |
  "projectivity (Cons p ps) (Cons l1 (Cons l2 ls)) = (projectivity ps (Cons l2 ls)) \<circ> (perspectivity p l1 l2)" |
  "projectivity [] b = undefined" |
  "projectivity a [] = undefined" |
  "projectivity a [v] = undefined"

(* Proposition 4.8 Let l be a line. Then the set of projectivities of l into itself forms a group, which we will call PJ(l). *)

(* Proposition 4.9 Let l be a line, and let A, B, C, and A\<Zprime>, B\<Zprime>, C\<Zprime> be two triples of three distinct points each on l. Then there is a projectivity of l into itself which sends A, B, C into A\<Zprime>, B\<Zprime>, C\<Zprime>. *)

(* Proposition 4.10 A projectivity takes harmonic quadruples into harmonic quadruples. *)

end


