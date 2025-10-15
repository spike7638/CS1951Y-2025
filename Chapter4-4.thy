theory "Chapter4-4"
  imports Complex_Main  "Chapter4-3"
begin
text\<open> start at "Perspectivies and Projectivities" and go to end of chapter\<close>

(*This stuff took us two hours... we'll keep going when we have time to meet again*)

definition (in projective_plane_data2) isperspectivity :: "'p \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool" 
  where "isperspectivity P l1 l2 = (if P \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines 
  then (\<not> (incid P l1) \<and> \<not> (incid P l2)) else undefined)"

definition (in projective_plane_data2) perspectivity :: "'p \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> ('p \<Rightarrow> 'p)"
  where "perspectivity P l1 l2 = (if (P \<in> Points \<and> l1 \<in> Lines \<and> l2 \<in> Lines \<and> isperspectivity P l1 l2)
  then (\<lambda>Q . if Q \<in> Points then (meet (join P Q) l2) else undefined) else undefined)"

end


