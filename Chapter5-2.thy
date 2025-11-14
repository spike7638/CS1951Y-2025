theory "Chapter5-2"
  imports "Chapter5-1"
begin
text \<open>Proposition 5.3 and 5.4\<close>

theorem FT_implies_P6: 
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes FT_plane: "FTPL Points Lines incid"
  shows "P6 Points Lines incid" unfolding P6_def
  sorry

lemma (in projective_plane) lemma_54:
  fixes l m n
  fixes R P
  assumes "l \<in> Lines \<and> m \<in> Lines \<and> n \<in> Lines \<and> distinct2 l n"
  assumes "R \<in> Points \<and> P \<in> Points"
  assumes "(is_persp_data (R, l, m)) \<and> (is_persp_data (P, m, n))"
  assumes "(coincident l m n) \<or> (pcollinear R P (meet l n))"
  fixes l_to_n
  assumes "l_to_n = projectivity (Cons (R, l, m) (Cons (P, m, n) []))"
  shows "\<exists>Q. (Q \<in> Points \<and> 
    (\<forall>S. S \<in> Points \<and> S \<lhd> l \<and> (perspectivity (Q, l, n) S) = l_to_n S))"
  sorry
end
