theory "Chapter5-2"
  imports "Chapter5-1" "Chapter4-4jfh"
begin
text \<open>Proposition 5.3 and 5.4\<close>



theorem FT_implies_P6: 
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes FT_plane: "FTPL Points Lines incid"
  shows "P6 Points Lines incid"
proof - 
  have is_proj_plane: "projective_plane Points Lines incid" using FTPL_def assms by auto
  have p6: "(\<forall>l l' A B C A' B' C'. (l \<in> Lines \<and> l' \<in> Lines \<and> l \<noteq> l'
    \<and> A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points 
    \<and> distinct4 A B C (projective_plane_data.meet Points Lines incid l l') 
    \<and> distinct4 A' B' C' (projective_plane_data.meet Points Lines incid l l')
    \<and> incid A l \<and> incid B l \<and> incid C l 
    \<and> incid A' l' \<and> incid B' l' \<and> incid C' l')
    \<longrightarrow> (projective_plane_data.pcollinear Points Lines incid 
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid A B')
          (projective_plane_data.join Points Lines incid A' B))
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid A C')
          (projective_plane_data.join Points Lines incid A' C))
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid B C')
          (projective_plane_data.join Points Lines incid B' C))))"
  proof (intro allI impI)
    fix l l' A B C A' B' C'
    assume "l \<in> Lines \<and> l' \<in> Lines \<and> l \<noteq> l'
    \<and> A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points 
    \<and> distinct4 A B C (projective_plane_data.meet Points Lines incid l l') 
    \<and> distinct4 A' B' C' (projective_plane_data.meet Points Lines incid l l')
    \<and> incid A l \<and> incid B l \<and> incid C l 
    \<and> incid A' l' \<and> incid B' l' \<and> incid C' l'"

    let ?Y = "projective_plane_data.meet Points Lines incid l l'"
    let ?P = "projective_plane_data.meet Points Lines incid (projective_plane_data.join Points Lines incid A B') (projective_plane_data.join Points Lines incid A' B)"
    let ?Q = "projective_plane_data.meet Points Lines incid (projective_plane_data.join Points Lines incid A C') (projective_plane_data.join Points Lines incid A' C)"
    let ?R = "projective_plane_data.meet Points Lines incid (projective_plane_data.join Points Lines incid B C') (projective_plane_data.join Points Lines incid B' C)"

    let ?l'' = "projective_plane_data.join Points Lines incid ?P ?Q"
    obtain f where f_def: "f = projective_plane.projectivity Points Lines incid (Cons (A', l, ?l'') (Cons (A, ?l'', l') [])) 
             \<and> (f A = A') \<and> (f B = B') \<and> (f C = C')"  using projective_plane.triplet_to_triplet_diff_lines_two[of Points Lines incid A B C A' B' C' l l' ?l'' ?P ?Q]
    is_proj_plane assms sorry
    
    show "(projective_plane_data.pcollinear Points Lines incid 
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid A B')
          (projective_plane_data.join Points Lines incid A' B))
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid A C')
          (projective_plane_data.join Points Lines incid A' C))
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid B C')
          (projective_plane_data.join Points Lines incid B' C)))" sorry
  qed
  
  show ?thesis unfolding P6_def using is_proj_plane p6 by auto
qed
  

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