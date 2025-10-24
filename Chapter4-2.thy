theory "Chapter4-2"
  imports Complex_Main  "Chapter4-1" "Chapter1-2"

begin
text\<open> start at definition of complete quadrangle; stop just before "Harmonic points"\<close>

definition (in projective_plane) cquadrangle :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  where "cquadrangle A B C D = (A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points \<and> 
  \<not>pcollinear A B C \<and> \<not>pcollinear A B D \<and> \<not>pcollinear A C D \<and> \<not>pcollinear B C D)"

definition (in projective_plane) cquadrangle_sides :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'l set"
  where "cquadrangle_sides A B C D = (if (cquadrangle A B C D) 
  then({join A B, 
        join A C,
        join A D,
        join B C,
        join B D,
        join C D})
  else undefined)"

definition (in projective_plane) cquadrangle_points :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p list"
  where "cquadrangle_points A B C D = (if (cquadrangle A B C D) 
  then([meet (join B C) (join A D), 
        meet (join A C) (join B D), 
        meet (join A B) (join C D)])
  else undefined)"




definition (in projective_plane) cquadrangle_points_diag_1 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p"
  where "cquadrangle_points_diag_1 A B C D = (if (cquadrangle A B C D) 
  then(meet (join B C) (join A D))
  else undefined)"

definition (in projective_plane) cquadrangle_points_diag_2 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p"
  where "cquadrangle_points_diag_2 A B C D = (if (cquadrangle A B C D) 
  then(meet (join A C) (join B D))
  else undefined)"

definition (in projective_plane) cquadrangle_points_diag_3 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p"
  where "cquadrangle_points_diag_3 A B C D = (if (cquadrangle A B C D) 
  then(meet (join A B) (join C D))
  else undefined)"


definition (in projective_plane) P7 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  where "P7 A B C D = (if (cquadrangle A B C D) 
  then(\<not>pcollinear (cquadrangle_points_diag_1 A B C D) 
                   (cquadrangle_points_diag_2 A B C D)
                   (cquadrangle_points_diag_3 A B C D))
  else undefined)"


(*
theorem rp2_P7:
  fixes A B C D
  fixes E F G
  assumes "A \<in> rp2_Points \<and> B \<in> rp2_Points \<and> C \<in> rp2_Points \<and> D \<in> rp2_Points \<and> 
            E \<in> rp2_Points \<and> F \<in> rp2_Points \<and> G \<in> rp2_Points"
  assumes "cquadrangle A B C D"
  assumes "{E, F, G} = cquadrangle_points A B C D"
  shows "\<not>pcollinear E F G"
  sorry 
*)

definition (in projective_plane) cquadrilateral :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
  where "cquadrilateral a b c d = (a \<in> Lines \<and> b \<in> Lines \<and> c \<in> Lines \<and> d \<in> Lines \<and> 
  meet a b \<noteq> meet b c \<and> meet b c \<noteq> meet c d \<and> meet a c \<noteq> meet c d \<and> meet a b \<noteq> meet b d)"

definition (in projective_plane) cquadrilateral_points :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'p set"
  where "cquadrilateral_points a b c d = (if (cquadrilateral a b c d) 
  then({meet a b,
        meet a c,
        meet a d,
        meet b c,
        meet b d,
        meet c d})
  else undefined)"

definition (in projective_plane) cquadrilateral_lines :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l list"
  where "cquadrilateral_lines a b c d = (if (cquadrilateral a b c d) 
  then([join (meet a b) (meet c d),
        join (meet a c) (meet b d),
        join (meet a d) (meet b c)])
  else undefined)"


theorem (in projective_plane) quadrilateral_lines_distinct:
  fixes a b c d
  assumes "a \<in> Lines \<and> b \<in> Lines \<and> c \<in> Lines \<and> d \<in> Lines"
  assumes "cquadrilateral a b c d"
  shows "a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d"
  sorry

theorem (in projective_plane) meet_of_quadrilateral_is_quadrangle:
  fixes a b c d
  assumes "a \<in> Lines \<and> b \<in> Lines \<and> c \<in> Lines \<and> d \<in> Lines"
  assumes "cquadrilateral a b c d"
  shows "cquadrangle (meet b d) (meet c d) (meet a b) (meet a c)"
proof - 
  have lines_distinct: "a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d" 
    using quadrilateral_lines_distinct[of a b c d] assms by auto
  let ?D = "meet b d"
  let ?F = "meet c d"
  let ?E = "meet a b"
  let ?A = "meet a c"

  have d_point: "?D \<in> Points" using lines_distinct meet_properties2 assms by auto
  have f_point: "?F \<in> Points" using lines_distinct meet_properties2 assms by auto
  have e_point: "?E \<in> Points" using lines_distinct meet_properties2 assms by auto
  have a_point: "?A \<in> Points" using lines_distinct meet_properties2 assms by auto

  have not_collin_1: "\<not>pcollinear ?D ?F ?E"
  proof (rule ccontr)
    assume ch: "\<not>(\<not>pcollinear ?D ?F ?E)"
    then have "pcollinear ?D ?F ?E" by auto
    then have ch_alt: "\<exists> l. l \<in> Lines \<and> ?D \<lhd> l \<and> ?F \<lhd> l \<and> ?E \<lhd> l" 
      using assms(1) lines_distinct meet_properties2 pcollinear_def by force

    have D_in_bd: "?D \<lhd> b \<and> ?D \<lhd> d"
      using assms(1) lines_distinct meet_properties2 by auto
    have F_in_cd: "?F \<lhd> c \<and> ?F \<lhd> d"
      using assms(1) lines_distinct meet_properties2 by auto
    have E_in_ab: "?E \<lhd> a \<and> ?E \<lhd> b"
      using assms(1) lines_distinct meet_properties2 by auto

    have join_DF_is_d: "join ?D ?F = d" 
      using D_in_bd F_in_cd assms by (metis cquadrilateral_def join_properties2 lines_distinct meet_properties2)
    
    have "meet a b \<noteq> meet b d" using cquadrilateral_def assms by auto
    then have E_notin_d: "\<not>(?E \<lhd> d)" 
      using E_in_ab assms D_in_bd d_point e_point lines_distinct unique_meet by blast 

    have "\<not>(pcollinear ?D ?F ?E)" using join_DF_is_d E_notin_d 
      by (metis assms(2) ch_alt cquadrilateral_def join_properties2 lines_distinct meet_properties2)

    then show False using ch by auto
  qed
  show ?thesis sorry
qed



theorem (in projective_plane) P7_dual:
  fixes a b c d
  fixes p q r
  assumes "a \<in> Lines \<and> b \<in> Lines \<and> c \<in> Lines \<and> d \<in> Lines \<and> 
            p \<in> Lines \<and> q \<in> Lines \<and> r \<in> Lines"
  assumes "cquadrilateral a b c d"
  assumes "[p, q, r] = cquadrilateral_lines a b c d"
  assumes "P7 (meet b d) (meet c d) (meet a b) (meet a c)"
  shows "\<not> (meet p q = meet p r \<and> meet p r = meet q r \<and> meet p q = meet q r)"
proof (rule ccontr)
  assume ch: "\<not>(\<not>(meet p q = meet p r \<and> meet p r = meet q r \<and> meet p q = meet q r))"
  then have ch_alt: "meet p q = meet p r \<and> meet p r = meet q r \<and> meet p q = meet q r" by blast
  have pqr: "p = join (meet a b) (meet c d) \<and> q = join (meet a c) (meet b d) \<and> r = join (meet a d) (meet b c)"
    using assms by (simp add: cquadrilateral_lines_def)
  let ?A = "meet b d"
  let ?B = "meet c d"
  let ?C = "meet a b"
  let ?D = "meet a c"
  have abcd_qd: "cquadrangle ?A ?B ?C ?D" 
    using assms meet_of_quadrilateral_is_quadrangle[of a b c d] by blast
  let ?E = "cquadrangle_points_diag_1 ?A ?B ?C ?D"
  let ?F = "cquadrangle_points_diag_2 ?A ?B ?C ?D"
  let ?G = "cquadrangle_points_diag_3 ?A ?B ?C ?D"
  have nc_efg: "\<not> pcollinear ?E ?F ?G" using assms P7_def abcd_qd by fastforce
  have e: "?E = meet (join (meet c d) (meet a b)) (join (meet b d) (meet a c))" using abcd_qd cquadrangle_points_diag_1_def by force
  have f: "?F = meet (join (meet b d) (meet a b)) (join (meet c d) (meet a c))" using abcd_qd cquadrangle_points_diag_2_def by force
  have g: "?G = meet (join (meet b d) (meet c d)) (join (meet a b) (meet a c))" using abcd_qd cquadrangle_points_diag_3_def by force
  have ef_1: "join ?E ?F = join (meet (join (meet c d) (meet a b)) (join (meet b d) (meet a c))) 
                        (meet (join (meet b d) (meet a b)) (join (meet c d) (meet a c)))"
    using e f by argo
  
  (*fix later*)
  then have intm: "\<not> pcollinear
      (cquadrangle_points_diag_1 (b . d) (c . d) (a . b) (a . c)) 
      (cquadrangle_points_diag_2 (b . d) (c . d) (a . b) (a . c)) 
      (cquadrangle_points_diag_3 (b . d) (c . d) (a . b) (a . c))"
    using
      \<open>\<not> pcollinear (cquadrangle_points_diag_1 (b . d) (c . d) (a . b) (a . c)) 
            (cquadrangle_points_diag_2 (b . d) (c . d) (a . b) (a . c)) 
            (cquadrangle_points_diag_3 (b . d) (c . d) (a . b) (a . c))\<close>
    by force

  (*fix later*)
  then have ef_a: "join ?E ?F = a" using assms abcd_qd ch cquadrangle_def e f g join_properties1
        meet_properties2 pcollinear_def pqr unique_meet by (smt (verit))
  have fg_a: "join ?F ?G = a" using assms abcd_qd ch cquadrangle_def e f g join_properties1
        meet_properties2 pcollinear_def pqr unique_meet ef_a
    by (smt (verit))
  then have c_efg:"pcollinear ?E ?F ?G" using ef_a fg_a abcd_qd assms(2) cquadrangle_def cquadrilateral_def e f g
        join_properties1 meet_properties2 pcollinear_def by (smt (verit))

  then show False using c_efg nc_efg by auto
qed

end


