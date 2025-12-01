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

definition P7 :: "('p set) \<Rightarrow> ('l set) \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool"
  where "P7 Points Lines incid \<equiv> ((projective_plane Points Lines incid) \<and> 
        (\<forall>A B C D. (A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points \<and> 
                    (projective_plane.cquadrangle Points Lines incid  A B C D))
         \<longrightarrow> (\<not>(projective_plane_data.pcollinear Points Lines incid 
            (projective_plane.cquadrangle_points_diag_1 Points Lines incid A B C D) 
            (projective_plane.cquadrangle_points_diag_2 Points Lines incid A B C D)
            (projective_plane.cquadrangle_points_diag_3 Points Lines incid A B C D)))))"

locale projective_plane_7 = projective_plane  Points Lines incid
  for Points Lines incid + 
  assumes
  p7: "(cquadrangle A B C D) \<Longrightarrow> \<not> (pcollinear ((B\<bar>C) \<sqdot> (A\<bar>D)) ((A\<bar>C) \<sqdot> (B\<bar>D)) ((A\<bar>B) \<sqdot> (C\<bar>D)))"
begin
end

locale projective_plane_5_7 = projective_plane_7 Points Lines incid
  for Points Lines incid + 
  assumes
  p5:"\<lbrakk>U \<in> Points; A \<in> Points; B \<in> Points; C \<in> Points; 
    A' \<in> Points; B' \<in> Points; C' \<in> Points;
    distinct[U, A, B, C, A', B', C'];
    pcollinear A A' U; pcollinear B B' U; pcollinear C C' U;
    \<not>pcollinear A B C; \<not>pcollinear A' B' C'; 
    join A B \<noteq> join A' B'; join A C \<noteq> join A' C'; join B C \<noteq> join B' C';
    P = meet (join A B) (join A' B');
    Q = meet (join A C) (join A' C');
    R = meet (join B C)  (join B' C')\<rbrakk> \<Longrightarrow> pcollinear P Q R"
begin
end

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
  \<not>coincident a b c \<and> \<not>coincident b c d \<and> \<not>coincident a b d \<and> \<not>coincident a c d)"

definition (in projective_plane) cquadrilateral_points :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'p set"
  where "cquadrilateral_points a b c d = (if (cquadrilateral a b c d) 
  then({meet a b,
        meet a c,
        meet a d,
        meet b c,
        meet b d,
        meet c d})
  else undefined)"

definition (in projective_plane) cquadrilateral_lines_1 :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l"
  where "cquadrilateral_lines_1 a b c d = (if (cquadrilateral a b c d) 
  then(join (meet a b) (meet c d))
  else undefined)"

definition (in projective_plane) cquadrilateral_lines_2 :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l"
  where "cquadrilateral_lines_2 a b c d = (if (cquadrilateral a b c d) 
  then(join (meet a c) (meet b d))
  else undefined)"

definition (in projective_plane) cquadrilateral_lines_3 :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l"
  where "cquadrilateral_lines_3 a b c d = (if (cquadrilateral a b c d) 
  then(join (meet a d) (meet b c))
  else undefined)"

theorem (in projective_plane) quadrangle_points_distinct:
  fixes A B C D
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points"
  assumes "cquadrangle A B C D"
  shows "distinct[A, B, C, D]"
proof - 
  show ?thesis using assms(2) cquadrangle_def distinct4_def p1 p3 pcollinear_def by metis
qed

theorem (in projective_plane) quadrangle_lines_distinct:
  fixes A B C D
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points"
  assumes "cquadrangle A B C D"
  shows "distinct[(join A B), (join A C), (join A D), (join B C), (join B D), (join C D)]"
proof - 
  have 0: "(join A B) \<noteq> (join A C) \<and> (join A B) \<noteq> (join A D) \<and> (join A B) \<noteq> (join B C) \<and> (join A B) \<noteq> (join B D)  \<and> (join A B) \<noteq> (join C D)"
    using assms(2) cquadrangle_def distinct4_def join_properties1 pcollinear_def
        quadrangle_points_distinct
    by (smt (verit))
  have 1: "(join A C) \<noteq> (join A D) \<and> (join A C) \<noteq> (join B C) \<and> (join A C) \<noteq> (join B D) \<and> (join A C) \<noteq> (join C D)"
    using assms(2) cquadrangle_def distinct4_def join_properties1 pcollinear_def
        quadrangle_points_distinct
    by (smt (verit))
  have 2: "(join A D) \<noteq> (join B C) \<and>  (join A D) \<noteq> (join B D) \<and> (join A D) \<noteq> (join C D)"
    using assms(2) cquadrangle_def distinct4_def join_properties1 pcollinear_def
        quadrangle_points_distinct
    by (smt (verit))
  have 3: "(join B C) \<noteq> (join B D) \<and>  (join B C) \<noteq> (join C D) \<and> (join B D) \<noteq> (join C D)"
    using assms(2) cquadrangle_def distinct4_def join_properties1 pcollinear_def
        quadrangle_points_distinct
    by (smt (verit))
  then show ?thesis unfolding distinct6_def using cquadrangle_def distinct6_def join_properties1 1 2 3 0
    by argo
qed

theorem (in projective_plane) quadrangle_diag_are_points:
  fixes A B C D
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points"
  assumes "cquadrangle A B C D"
  shows "(projective_plane.cquadrangle_points_diag_1 Points Lines incid A B C D) \<in> Points \<and>  
         (projective_plane.cquadrangle_points_diag_2 Points Lines incid A B C D) \<in> Points \<and>  
         (projective_plane.cquadrangle_points_diag_3 Points Lines incid A B C D) \<in> Points"
proof - 
  have 0: "(join B C) \<noteq> (join A D)" using assms quadrangle_lines_distinct distinct6_def by metis
  have 1: "(join A C) \<noteq> (join B D)" using assms quadrangle_lines_distinct distinct6_def by metis
  have 2: "(join A B) \<noteq> (join C D)" using assms quadrangle_lines_distinct distinct6_def by metis

  have 3: "(projective_plane.cquadrangle_points_diag_1 Points Lines incid A B C D) \<in> Points" 
    using 0 assms cquadrangle_points_diag_1_def distinct4_def join_properties1 meet_properties2
      quadrangle_points_distinct
    by metis
  have 4: "(projective_plane.cquadrangle_points_diag_2 Points Lines incid A B C D) \<in> Points" 
    using 1 assms cquadrangle_points_diag_2_def distinct4_def join_properties1 meet_properties2
      quadrangle_points_distinct
    by metis
  have 5: "(projective_plane.cquadrangle_points_diag_3 Points Lines incid A B C D) \<in> Points" 
    using 2 assms cquadrangle_points_diag_3_def distinct4_def join_properties1 meet_properties2
      quadrangle_points_distinct
    by metis

  show ?thesis using 3 4 5 by auto
qed

theorem quadrangle_diagonal_points_distinct:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes A B C D
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points"
  assumes "projective_plane.cquadrangle Points Lines incid A B C D"
  assumes "P7 Points Lines incid"
  shows "distinct[(projective_plane.cquadrangle_points_diag_1 Points Lines incid A B C D), 
                   (projective_plane.cquadrangle_points_diag_2 Points Lines incid A B C D), 
                   (projective_plane.cquadrangle_points_diag_3 Points Lines incid A B C D)]"
proof (rule ccontr)
  assume ch: "\<not>distinct[(projective_plane.cquadrangle_points_diag_1 Points Lines incid A B C D),
                   (projective_plane.cquadrangle_points_diag_2 Points Lines incid A B C D),
                   (projective_plane.cquadrangle_points_diag_3 Points Lines incid A B C D)]"
  let ?E = "projective_plane.cquadrangle_points_diag_1 Points Lines incid A B C D"
  let ?F = "projective_plane.cquadrangle_points_diag_2 Points Lines incid A B C D"
  let ?G = "projective_plane.cquadrangle_points_diag_3 Points Lines incid A B C D"
  have is_proj: "projective_plane Points Lines incid" using assms P7_def by auto
  have efg_points: "?E \<in> Points \<and> ?F \<in> Points \<and> ?G \<in> Points" 
    using projective_plane.quadrangle_diag_are_points assms is_proj by metis

  have efg_nc: "\<not>projective_plane_data.pcollinear Points Lines incid ?E ?F ?G" using assms P7_def by fastforce
  have ch_alt: "(?E = ?F) \<or> (?E = ?G) \<or> (?F = ?G)" using distinct3_def ch by metis
  consider (e_eq_f) "?E = ?F"
    | (e_eq_g) "?E = ?G"
    | (f_eq_g) "?F = ?G" using ch_alt by blast
  then show False
  proof cases
    case e_eq_f
    then show ?thesis 
      using projective_plane.pcollinear_if_two_points_equal[of Points Lines incid ?E ?F ?G] efg_nc efg_points is_proj by auto
  next
    case e_eq_g
    then show ?thesis 
      using projective_plane.pcollinear_if_two_points_equal[of Points Lines incid ?E ?G ?F] efg_nc efg_points is_proj projective_plane_data.collinear_comm by metis  
  next
    case f_eq_g
    then show ?thesis 
      using projective_plane.pcollinear_if_two_points_equal[of Points Lines incid ?F ?G ?E] efg_nc efg_points is_proj projective_plane_data.collinear_comm by metis    
  qed
qed

theorem (in projective_plane) quadrilateral_lines_distinct:
  fixes a b c d
  assumes "a \<in> Lines \<and> b \<in> Lines \<and> c \<in> Lines \<and> d \<in> Lines"
  assumes "cquadrilateral a b c d"
  shows "distinct[a, b, c, d]"
proof - 
  show ?thesis using  assms(2) coincident_def cquadrilateral_def distinct4_def p2 by metis
qed

theorem (in projective_plane) meet_of_quadrilateral_is_quadrangle:
  fixes a b c d
  assumes "a \<in> Lines \<and> b \<in> Lines \<and> c \<in> Lines \<and> d \<in> Lines"
  assumes "cquadrilateral a b c d"
  shows "cquadrangle (meet b d) (meet c d) (meet a b) (meet a c)"
proof - 
  have lines_distinct: "a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d" 
    using quadrilateral_lines_distinct[of a b c d] assms distinct4_def by metis
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
      using D_in_bd F_in_cd assms by (metis coincident_def cquadrilateral_def d_point f_point join_properties2)
    
    have "meet a b \<noteq> meet b d" using cquadrilateral_def assms coincident_def D_in_bd E_in_ab d_point by force
    then have E_notin_d: "\<not>(?E \<lhd> d)" 
      using E_in_ab assms D_in_bd d_point e_point lines_distinct unique_meet by blast 

    have "\<not>(pcollinear ?D ?F ?E)" 
      using join_DF_is_d E_notin_d assms(2) ch_alt cquadrilateral_def join_properties2 lines_distinct meet_properties2 coincident_def
      by (smt (verit))

    then show False using ch by auto
  qed
  
  have not_collin_2: "\<not>pcollinear ?D ?F ?A"
  proof (rule ccontr)
    assume ch: "\<not>(\<not>pcollinear ?D ?F ?A)"
    then have "pcollinear ?D ?F ?A" by auto
    then have ch_alt: "\<exists> l. l \<in> Lines \<and> ?D \<lhd> l \<and> ?F \<lhd> l \<and> ?A \<lhd> l" 
      using assms(1) lines_distinct meet_properties2 pcollinear_def by force

    have D_in_bd: "?D \<lhd> b \<and> ?D \<lhd> d"
      using assms(1) lines_distinct meet_properties2 by auto
    have F_in_cd: "?F \<lhd> c \<and> ?F \<lhd> d"
      using assms(1) lines_distinct meet_properties2 by auto
    have A_in_ac: "?A \<lhd> a \<and> ?A \<lhd> c"
      using assms(1) lines_distinct meet_properties2 by auto

    have join_DF_is_d: "join ?D ?F = d" 
      using D_in_bd F_in_cd assms by (metis coincident_def cquadrilateral_def join_properties2 lines_distinct meet_properties2)
    
    have "meet a c \<noteq> meet c d" using cquadrilateral_def assms A_in_ac F_in_cd coincident_def f_point by auto
    then have E_notin_d: "\<not>(?A \<lhd> d)" 
      using A_in_ac assms D_in_bd d_point a_point f_point lines_distinct unique_meet F_in_cd by blast 

    have "\<not>(pcollinear ?D ?F ?A)" 
      using join_DF_is_d E_notin_d coincident_def assms(2) ch_alt cquadrilateral_def join_properties2 lines_distinct meet_properties2 
      by (smt (verit))

    then show False using ch by auto
  qed

  have not_collin_3: "\<not>pcollinear ?F ?E ?A"
  proof (rule ccontr)
    assume ch: "\<not>(\<not>pcollinear ?F ?E ?A)"
    then have "pcollinear ?F ?E ?A" by auto
    then have ch_alt: "\<exists> l. l \<in> Lines \<and> ?F \<lhd> l \<and> ?E \<lhd> l \<and> ?A \<lhd> l" 
      using assms(1) lines_distinct meet_properties2 pcollinear_def by force

    have E_in_ab: "?E \<lhd> a \<and> ?E \<lhd> b"
      using assms(1) lines_distinct meet_properties2 by auto
    have F_in_cd: "?F \<lhd> c \<and> ?F \<lhd> d"
      using assms(1) lines_distinct meet_properties2 by auto
    have A_in_ac: "?A \<lhd> a \<and> ?A \<lhd> c"
      using assms(1) lines_distinct meet_properties2 by auto

    have join_EA_is_a: "join ?E ?A = a" 
      using E_in_ab A_in_ac assms by (metis cquadrilateral_def coincident_def join_properties2 lines_distinct meet_properties2)
    
    have "meet a c \<noteq> meet c d" using cquadrilateral_def assms
      by (metis lines_distinct meet_properties2 not_collin_2 pcollinear_def)
    then have E_notin_d: "\<not>(?F \<lhd> a)" 
      using A_in_ac assms E_in_ab d_point a_point f_point lines_distinct unique_meet F_in_cd by blast 

    have "\<not>(pcollinear ?F ?E ?A)" 
      using join_EA_is_a E_notin_d coincident_def assms(2) ch_alt cquadrilateral_def join_properties2 lines_distinct meet_properties2
      by (smt(verit))

    then show False using ch by auto
  qed

  have not_collin_4: "\<not>pcollinear ?F ?E ?A"
  proof (rule ccontr)
    assume ch: "\<not>(\<not>pcollinear ?F ?E ?A)"
    then have "pcollinear ?F ?E ?A" by auto
    then have ch_alt: "\<exists> l. l \<in> Lines \<and> ?F \<lhd> l \<and> ?E \<lhd> l \<and> ?A \<lhd> l" 
      using assms(1) lines_distinct meet_properties2 pcollinear_def by force

    have E_in_ab: "?E \<lhd> a \<and> ?E \<lhd> b"
      using assms(1) lines_distinct meet_properties2 by auto
    have D_in_bd: "?D \<lhd> b \<and> ?D \<lhd> d"
      using assms(1) lines_distinct meet_properties2 by auto
    have A_in_ac: "?A \<lhd> a \<and> ?A \<lhd> c"
      using assms(1) lines_distinct meet_properties2 by auto

    have join_EA_is_a: "join ?E ?A = a" 
      using E_in_ab A_in_ac assms by (metis cquadrilateral_def join_properties2 coincident_def lines_distinct meet_properties2)

    then show False using ch not_collin_3 by auto
  qed

  show ?thesis using not_collin_1 not_collin_2 not_collin_3 not_collin_4 
    by (smt (verit, del_insts) assms(1) cquadrangle_def lines_distinct meet_properties2 pcollinear_def
        unique_meet)
qed


theorem dual_collinear_is_coincident:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  fixes A B C
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points"
  assumes "projective_plane_data.pcollinear Points Lines incid A B C"
  shows "projective_plane_data.coincident dPoints dLines dincid A B C"
proof - 
  show ?thesis
    using assms(5) dLdef dPdef dm projective_plane_data.coincident_def projective_plane_data.pcollinear_def
    by fastforce
qed

theorem dual_coincident_is_collinear:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  fixes a b c
  assumes "a \<in> Lines \<and> b \<in> Lines \<and> c \<in> Lines"
  assumes "projective_plane_data.coincident Points Lines incid a b c"
  shows "projective_plane_data.pcollinear dPoints dLines dincid a b c"
proof - 
  show ?thesis
    using assms(5) dLdef dPdef dm projective_plane_data.coincident_def projective_plane_data.pcollinear_def
    by fastforce
qed

theorem dual_quadrangle_is_quadrilateral:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  fixes A B C D
  assumes "projective_plane Points Lines incid"
  assumes "projective_plane.cquadrangle Points Lines incid A B C D"
  shows "projective_plane.cquadrilateral dPoints dLines dincid A B C D"
proof - 
  have ncollinear: "\<not>projective_plane_data.pcollinear Points Lines incid A B C \<and>
   \<not> projective_plane_data.pcollinear Points Lines incid A B D \<and>
   \<not> projective_plane_data.pcollinear Points Lines incid A C D \<and>
   \<not> projective_plane_data.pcollinear Points Lines incid B C D" using assms 
     projective_plane.cquadrangle_def[of Points Lines incid A B C D] by auto
  then have nc_abc: "\<not>projective_plane_data.coincident dPoints dLines dincid A B C" using assms
      mdualize.elims(2) projective_plane_data.coincident_def[of dPoints dLines dincid A B C]
      projective_plane_data.pcollinear_def[of Points Lines incid A B C] by metis
  have nc_abd: "\<not>projective_plane_data.coincident dPoints dLines dincid A B D" using assms
      mdualize.elims(2) projective_plane_data.coincident_def[of dPoints dLines dincid A B D]
      projective_plane_data.pcollinear_def[of Points Lines incid A B D] ncollinear by metis
  have nc_acd: "\<not>projective_plane_data.coincident dPoints dLines dincid A C D" using assms
      mdualize.elims(2) projective_plane_data.coincident_def[of dPoints dLines dincid A C D]
      projective_plane_data.pcollinear_def[of Points Lines incid A C D] ncollinear by metis
  have nc_bcd: "\<not>projective_plane_data.coincident dPoints dLines dincid B C D" using assms
      mdualize.elims(2) projective_plane_data.coincident_def[of dPoints dLines dincid B C D]
      projective_plane_data.pcollinear_def[of Points Lines incid B C D] ncollinear by metis
  then show ?thesis using assms nc_abc nc_abd nc_acd nc_bcd dual_plane_is_projective projective_plane.cquadrangle_def
        projective_plane.cquadrilateral_def by metis
qed

theorem P7_dual:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes p7: "P7 Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  shows "P7 dPoints dLines dincid"
proof - 
  have projective_dual: "projective_plane dPoints dLines dincid" using dual_plane_is_projective P7_def dLdef dPdef dm p7 by blast
  have given_plane_projective: "projective_plane Points Lines incid" using p7 P7_def by auto

  have distinct_cquadrilateral_lines: "\<forall>A B C D. (A \<in> dPoints \<and> B \<in> dPoints \<and> C \<in> dPoints \<and> D \<in> dPoints \<and> 
            (projective_plane.cquadrangle dPoints dLines dincid  A B C D))
         \<longrightarrow> (\<not>(projective_plane_data.pcollinear dPoints dLines dincid 
            (projective_plane.cquadrangle_points_diag_1 dPoints dLines dincid A B C D) 
            (projective_plane.cquadrangle_points_diag_2 dPoints dLines dincid A B C D)
            (projective_plane.cquadrangle_points_diag_3 dPoints dLines dincid A B C D)))" 
  proof (intro allI impI)
    fix a b c d 
    assume dassms1: "a \<in> dPoints \<and> b \<in> dPoints \<and> c \<in> dPoints \<and> d \<in> dPoints \<and> (projective_plane.cquadrangle dPoints dLines dincid  a b c d)"

    have abcd_lines: "a \<in> Lines \<and> b \<in> Lines \<and> c \<in> Lines \<and> d \<in> Lines" using assms dassms1 by auto

    let ?p = "projective_plane_data.join Points Lines incid (projective_plane_data.meet Points Lines incid a b) (projective_plane_data.meet Points Lines incid c d)"
    let ?q = "projective_plane_data.join Points Lines incid (projective_plane_data.meet Points Lines incid a c) (projective_plane_data.meet Points Lines incid b d)"
    let ?r = "projective_plane_data.join Points Lines incid (projective_plane_data.meet Points Lines incid b c) (projective_plane_data.meet Points Lines incid a d) "

    have abcd_distinct: "distinct[a, b, c, d]" 
      using projective_plane.quadrangle_points_distinct[of dPoints dLines dincid a b c d] dassms1 projective_dual by auto 

    then have r_is_diag_1: "?r = projective_plane.cquadrangle_points_diag_1 dPoints dLines dincid a b c d" 
      using dLdef dPdef dassms1 dm dual_join_is_meet dual_meet_is_join given_plane_projective projective_dual projective_plane.cquadrangle_points_diag_1_def
      by metis

    then have q_is_diag_2: "?q = projective_plane.cquadrangle_points_diag_2 dPoints dLines dincid a b c d" 
      using dLdef dPdef dassms1 dm dual_join_is_meet dual_meet_is_join given_plane_projective projective_dual projective_plane.cquadrangle_points_diag_2_def
      by metis

    then have p_is_diag_3: "?p = projective_plane.cquadrangle_points_diag_3 dPoints dLines dincid a b c d" 
      using dLdef dPdef dassms1 dm dual_join_is_meet dual_meet_is_join given_plane_projective projective_dual projective_plane.cquadrangle_points_diag_3_def
      by metis

    show "\<not>(projective_plane_data.pcollinear dPoints dLines dincid 
            (projective_plane.cquadrangle_points_diag_1 dPoints dLines dincid a b c d) 
            (projective_plane.cquadrangle_points_diag_2 dPoints dLines dincid a b c d)
            (projective_plane.cquadrangle_points_diag_3 dPoints dLines dincid a b c d))"
    proof (rule ccontr)
      assume "\<not>(\<not>(projective_plane_data.pcollinear dPoints dLines dincid 
            (projective_plane.cquadrangle_points_diag_1 dPoints dLines dincid a b c d) 
            (projective_plane.cquadrangle_points_diag_2 dPoints dLines dincid a b c d)
            (projective_plane.cquadrangle_points_diag_3 dPoints dLines dincid a b c d)))"
      then have ch_alt: "projective_plane_data.pcollinear dPoints dLines dincid ?r ?q ?p" 
        using p_is_diag_3 q_is_diag_2 r_is_diag_1 by auto
      then have ch_alt_alt: "projective_plane_data.coincident Points Lines incid ?r ?q ?p"
        by (smt (verit, best) dLdef dPdef dm dual_collinear_is_coincident mmi_eq projective_plane_data.coincident_def
          projective_plane_data.pcollinear_def)

      let ?A = "projective_plane_data.meet Points Lines incid b d"
      let ?B = "projective_plane_data.meet Points Lines incid c d"
      let ?C = "projective_plane_data.meet Points Lines incid a b"
      let ?D = "projective_plane_data.meet Points Lines incid a c"

      have abcd_distinct_alt: "b \<noteq> d \<and> c \<noteq> d \<and> a \<noteq> b \<and> a \<noteq> c" using distinct4_def abcd_distinct by metis
      then have ABCD_points: "?A \<in> Points \<and> ?B \<in> Points \<and> ?C \<in> Points \<and> ?D \<in> Points" 
        using projective_plane.meet_properties2[of Points Lines incid d b] projective_plane.meet_properties2[of Points Lines incid d c]
          projective_plane.meet_properties2[of Points Lines incid b a] projective_plane.meet_properties2[of Points Lines incid c a] 
          abcd_lines abcd_distinct P7_def p7 by auto
  
      have abcd_cquadrilateral: "projective_plane.cquadrilateral Points Lines incid a b c d" 
        using dassms1 dual_quadrangle_is_quadrilateral dLdef dPdef dm mmi_eq given_plane_projective projective_dual
        by metis

      have ABCD_cquadrangle: "projective_plane.cquadrangle Points Lines incid ?A ?B ?C ?D" 
        using projective_plane.meet_of_quadrilateral_is_quadrangle[of Points Lines incid  a b c d] abcd_cquadrilateral abcd_lines P7_def p7 
        by auto

      have "?p = projective_plane_data.join Points Lines incid ?C ?B" by auto
      have "?q = projective_plane_data.join Points Lines incid ?D ?A" by auto

      let ?E = "projective_plane.cquadrangle_points_diag_1 Points Lines incid ?A ?B ?C ?D" 
      let ?F = "projective_plane.cquadrangle_points_diag_2 Points Lines incid ?A ?B ?C ?D" 
      let ?G = "projective_plane.cquadrangle_points_diag_3 Points Lines incid ?A ?B ?C ?D" 

      have e: "?E = projective_plane_data.meet Points Lines incid (projective_plane_data.join Points Lines incid (projective_plane_data.meet Points Lines incid c d) (projective_plane_data.meet Points Lines incid a b)) 
         (projective_plane_data.join Points Lines incid (projective_plane_data.meet Points Lines incid b d) (projective_plane_data.meet Points Lines incid a c))"
        by (smt (verit) ABCD_cquadrangle P7_def p7 projective_plane.cquadrangle_points_diag_1_def)
      have f: "?F = projective_plane_data.meet Points Lines incid (projective_plane_data.join Points Lines incid (projective_plane_data.meet Points Lines incid b d) (projective_plane_data.meet Points Lines incid a b)) 
         (projective_plane_data.join Points Lines incid (projective_plane_data.meet Points Lines incid c d) (projective_plane_data.meet Points Lines incid a c))" 
        by (smt (verit) ABCD_cquadrangle P7_def p7 projective_plane.cquadrangle_points_diag_2_def)
      have g: "?G = projective_plane_data.meet Points Lines incid (projective_plane_data.join Points Lines incid (projective_plane_data.meet Points Lines incid b d) (projective_plane_data.meet Points Lines incid c d)) 
       (projective_plane_data.join Points Lines incid (projective_plane_data.meet Points Lines incid a b) (projective_plane_data.meet Points Lines incid a c))" 
        by (smt (verit) ABCD_cquadrangle P7_def p7 projective_plane.cquadrangle_points_diag_3_def)

      have efg_collinear: "projective_plane_data.pcollinear Points Lines incid ?E ?F ?G"
      proof -
        (* Since ?r, ?q, ?p are coincident, they all pass through a common point U *)
        have pqr_lines: "?r \<in> Lines \<and> ?q \<in> Lines \<and> ?p \<in> Lines"
          by (smt (verit) ABCD_cquadrangle abcd_distinct dPdef dassms1 distinct4_def given_plane_projective
              projective_plane.join_properties1 projective_plane.meet_properties2
              projective_plane.quadrangle_points_distinct projective_plane.unique_meet)

        then obtain U where U_props: "U \<in> Points" "incid U ?r" "incid U ?q" "incid U ?p"
          using ch_alt_alt projective_plane_data.coincident_def by (smt (verit))

        have AB_is_d: "projective_plane_data.join Points Lines incid ?A ?B = d"
          using projective_plane.join_of_meet[of Points Lines incid d b c ?A ?B] ABCD_cquadrangle ABCD_points abcd_distinct_alt abcd_lines distinct3_def distinct4_def
              given_plane_projective projective_plane.meet_comm projective_plane.quadrangle_points_distinct
          by metis
        have CD_is_a: "projective_plane_data.join Points Lines incid ?C ?D = a"
          using projective_plane.join_of_meet[of Points Lines incid a b c ?C ?D] ABCD_cquadrangle ABCD_points abcd_distinct_alt dPdef dassms1 distinct3_def distinct4_def given_plane_projective projective_plane.quadrangle_points_distinct
          by metis 
        have AC_is_b: "projective_plane_data.join Points Lines incid ?A ?C = b" 
          using projective_plane.join_of_meet[of Points Lines incid b a d ?A ?C] ABCD_cquadrangle ABCD_points abcd_distinct dPdef dassms1 distinct3_def distinct4_def
              given_plane_projective projective_plane.join_of_meet projective_plane.meet_comm
              projective_plane.quadrangle_points_distinct
          by metis 
        have BD_is_c: "projective_plane_data.join Points Lines incid ?B ?D = c" 
          using projective_plane.join_of_meet[of Points Lines incid c d a ?B ?D] ABCD_cquadrangle ABCD_points abcd_distinct abcd_lines distinct3_def distinct4_def
              given_plane_projective projective_plane.meet_comm projective_plane.quadrangle_points_distinct
          by metis

        have g_is_ad: "?G = projective_plane_data.meet Points Lines incid d a" using AB_is_d CD_is_a g by auto
        have f_is_bc: "?F = projective_plane_data.meet Points Lines incid b c" using AC_is_b BD_is_c f by auto

        have e_is_U: "?E = U"
          by (smt (z3) ABCD_cquadrangle ABCD_points AB_is_d AC_is_b CD_is_a U_props(1,3,4) distinct4_def e
              given_plane_projective projective_plane.join_properties1 projective_plane.meet_properties2
              projective_plane.quadrangle_points_distinct projective_plane.unique_meet)

        let ?fg = "projective_plane_data.join Points Lines incid ?F ?G"

        have r_is_fg: "?r = ?fg"
          by (smt (verit, best) dPdef dassms1 f_is_bc g_is_ad given_plane_projective projective_plane.meet_properties2
            projective_plane.unique_meet)

        have U_in_FG: "incid U ?fg" using U_props r_is_fg by auto

        have e_in_fg: "incid ?E ?fg" using e_is_U U_in_FG by auto
      
        have "?F \<noteq> ?G" 
        by (smt (verit, ccfv_SIG) AB_is_d AC_is_b abcd_distinct dPdef dassms1 distinct4_def f_is_bc g_is_ad
            given_plane_projective projective_plane.meet_properties2 projective_plane.unique_meet)
        then have fg_in_fg: "incid ?F ?fg \<and> incid ?G ?fg" 
          using  abcd_distinct dPdef dassms1 distinct4_def f_is_bc g_is_ad given_plane_projective
              projective_plane.join_properties1 projective_plane.meet_properties2
          by metis
        then have efg_in_fg: "incid ?F ?fg \<and> incid ?G ?fg \<and> incid ?E ?fg" using e_in_fg by auto

        have fg_line: "?fg \<in> Lines" using pqr_lines r_is_fg by auto
        have efg_points: "?E \<in> Points \<and> ?F \<in> Points \<and> ?G \<in> Points" 
          using U_props(1) abcd_distinct abcd_lines distinct4_def e_is_U f_is_bc g_is_ad given_plane_projective projective_plane.meet_properties2
          by metis

        then show ?thesis using efg_in_fg fg_line efg_points using projective_plane_data.pcollinear_def by force
      qed

      have efg_nc: "\<not>projective_plane_data.pcollinear Points Lines incid ?E ?F ?G" unfolding P7_def 
        using ABCD_cquadrangle ABCD_points P7_def[of Points Lines incid] p7 by auto 

      show False using efg_nc efg_collinear by auto
    qed
  qed
  show ?thesis unfolding P7_def
    using projective_dual distinct_cquadrilateral_lines assms projective_plane.quadrilateral_lines_distinct by meson
qed


end