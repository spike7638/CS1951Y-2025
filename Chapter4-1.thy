theory "Chapter4-1"
  imports Complex_Main "Chapter1-1"

begin
text\<open> Everything up to the Principle of Duality and the remarks after it. (You don't need to prove 
remark 2!)\<close>

definition (in projective_plane2) proj_point_pencil :: "'p \<Rightarrow> 'l set" where
  "proj_point_pencil (P::'p) = {n::'l . (n \<in> Lines) \<and> incid P n}"

lemma dual_plane_is_projective:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane2 Points Lines incid"
  defines dPoints: "dPoints \<equiv> Lines"
  defines dLines: 
    "dLines \<equiv> {projective_plane2.proj_point_pencil P::'p | P. (P \<in> Points)}"
  shows "P = 1"
 
end


