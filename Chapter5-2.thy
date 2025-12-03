theory "Chapter5-2"
  imports "Chapter5-1" 
begin
text \<open>Proposition 5.3 and 5.4\<close>

lemma (in projective_plane) nonintersection_distinct: 
  fixes l l' A B C
  assumes "l \<in> Lines \<and> l' \<in> Lines \<and> A \<in> Points \<and> B \<in> Points \<and> C \<in> Points"
  assumes "l \<noteq>  l'"
  assumes "C \<lhd> l \<and> C \<lhd> l' \<and> A \<lhd> l \<and> B \<lhd> l'"
  assumes "A \<noteq> C \<and> B \<noteq> C"
  shows "A \<noteq> B"
proof (rule ccontr)
  assume ch: "\<not>(A \<noteq> B)"
  have ch_alt: "A = B" using ch by blast
  have 0: "A \<lhd> l'" using assms ch_alt by auto
  show False using 0 assms unique_meet by force
qed

lemma (in projective_plane) two_joins_of_distinct4_distinct: 
  fixes l l' A B A' B' AB' A'B
  assumes "l \<in> Lines \<and> l' \<in> Lines \<and> A \<in> Points \<and> B \<in> Points \<and> A' \<in> Points \<and> B' \<in> Points \<and> AB' \<in> Lines \<and> A'B \<in> Lines"
  assumes "l \<noteq>  l'"
  assumes "A \<lhd> l \<and> B \<lhd> l \<and> A' \<lhd> l' \<and> B' \<lhd> l'"
  assumes "distinct[A, B, A', B']"
  assumes "AB' = join A B' \<and> A'B = join A' B"
  shows "AB' \<noteq> A'B"
proof (rule ccontr)
  assume ch: "\<not>AB' \<noteq> A'B"
  then have ch_alt: "AB' = A'B" by blast
  have same: "A \<lhd> l \<and> B \<lhd> l \<and> A \<lhd> AB' \<and> B \<lhd> AB'" using ch_alt assms 
          distinct4_def join_properties1 by metis
  show False using same assms ch_alt distinct4_def join_properties1
        nonintersection_distinct by metis
qed

lemma (in projective_plane) two_meets_of_distinct8_distinct: 
  fixes l l' AB' A'B AC' A'C 
  fixes A B C A' B' C' Y P Q
  assumes "l \<in> Lines \<and> l' \<in> Lines \<and> AB' \<in> Lines \<and> A'B \<in> Lines \<and> AC' \<in> Lines \<and> A'C \<in> Lines"
  assumes "A \<in> Points \<and> B \<in> Points \<and>  C \<in> Points \<and> A' \<in> Points \<and> B' \<in> Points \<and>  C' \<in> Points \<and> Y \<in> Points \<and> P \<in> Points \<and> Q \<in> Points"
  assumes "l \<noteq>  l' \<and> Y \<lhd> l \<and> Y \<lhd> l'"
  assumes "A \<lhd> l \<and> B \<lhd> l \<and> A' \<lhd> l' \<and> B' \<lhd> l' \<and> C \<lhd> l \<and> C' \<lhd> l' "
  assumes "distinct[A, B, C,  A', B', C', Y]"
  assumes "AB' = join A B' \<and> A'B = join A' B
          \<and> AC' = join A C' \<and> A'C = join A' C"
  assumes "AB' \<noteq> A'B \<and> AC' \<noteq> A'C"
  assumes "P \<lhd> AB' \<and> P \<lhd> A'B \<and> Q \<lhd> AC' \<and> Q \<lhd> A'C"
  shows "P \<noteq> Q"
proof (rule ccontr)
  assume ch: "\<not>P \<noteq> Q"
  then have ch_alt: "P = Q" by blast
  have pabac: "P \<lhd> AB' \<and> P \<lhd> AC'" using ch_alt assms by auto
  have pnota: "P \<noteq> A" 
    proof (rule ccontr)
      assume ch_1: "\<not>P \<noteq> A"
      then have ch_alt_1: "P = A" by blast
      have 0: "l = A'B" using ch_alt_1 assms distinct7_def join_properties1 nonintersection_distinct by metis
      then show False using assms distinct7_def join_properties1 nonintersection_distinct by metis
    qed
  have qnota: "Q \<noteq> A" using pnota ch_alt by auto
  obtain k where kdef: "k \<in> Lines \<and> k = join A P" using qnota assms
     distinct7_def join_properties1 ch_alt by presburger
  have abp_k: "B'\<lhd> k" using kdef  assms ch_alt join_properties1 nonintersection_distinct
        qnota by metis
  show False using assms abp_k distinct7_def join_properties1 pabac s by metis
qed

lemma (in projective_plane) triplet_to_triplet_diff_lines:
  fixes A B C A' B' C' l l'
  assumes ABC_def: "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> distinct [A, B, C]"
  assumes ABC'_def: "A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points \<and> distinct [A', B', C']"
  assumes l_def: "l \<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l \<and> C \<lhd> l"
  assumes l'_def: "l' \<in> Lines \<and> A' \<lhd> l' \<and> B' \<lhd> l' \<and> C' \<lhd> l'"
  assumes ll'_diff: "l \<noteq>  l'"
  (*shows "\<exists> ps . \<exists> ls . \<exists> f . (f = projectivity ps ls) 
                        \<and> (hd ls = l) \<and> (last ls = l') 
                        \<and> (f A = A') \<and> (f B = B') \<and> (f C = C')"*)
  shows "\<exists> ds . \<exists> f . (f = projectivity ds) 
                        \<and> (proj_domain ds = l) \<and> (proj_range ds = l') 
                        \<and> (f A = A') \<and> (f B = B') \<and> (f C = C')"
  sorry  

lemma (in projective_plane) triplet_to_triplet_diff_lines_two:
  fixes A B C A' B' C' l l' l'' P Q
  assumes ABC_def: "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> distinct [A, B, C]"
  assumes ABC'_def: "A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points \<and> distinct [A', B', C']"
  assumes l_def: "l \<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l \<and> C \<lhd> l"
  assumes l'_def: "l' \<in> Lines \<and> A' \<lhd> l' \<and> B' \<lhd> l' \<and> C' \<lhd> l'"
  assumes l''_def: "l'' \<in> Lines  \<and> l'' = join P Q"
  assumes P_def: "P \<in> Points \<and> P = meet (join A B') (join A' B)"
  assumes Q_def: "Q \<in> Points \<and> Q = meet (join A C') (join A' C)"
  
  assumes ll'_diff: "l \<noteq>  l'"
  (*shows "\<exists> ps . \<exists> ls . \<exists> f . (f = projectivity ps ls) 
                        \<and> (hd ls = l) \<and> (last ls = l') 
                        \<and> (f A = A') \<and> (f B = B') \<and> (f C = C')"*)
  shows "\<exists> f. f = projectivity (Cons (A', l, l'') (Cons (A, l'', l') [])) 
             \<and> (f A = A') \<and> (f B = B') \<and> (f C = C') \<and> is_persp_data (A', l, l'') \<and> is_persp_data (A, l'', l')"
  sorry

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
    \<and> distinct[A, B, C, (projective_plane_data.meet Points Lines incid l l')] 
    \<and> distinct[A', B', C', (projective_plane_data.meet Points Lines incid l l')]
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
    assume assmsimpl: "l \<in> Lines \<and> l' \<in> Lines \<and> l \<noteq> l'
    \<and> A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points 
    \<and> distinct[A, B, C, (projective_plane_data.meet Points Lines incid l l')] 
    \<and> distinct[A', B', C', (projective_plane_data.meet Points Lines incid l l')]
    \<and> incid A l \<and> incid B l \<and> incid C l 
    \<and> incid A' l' \<and> incid B' l' \<and> incid C' l'"

    let ?k = "projective_plane_data.join Points Lines incid A B'"
    have distinct_abc: "distinct[A, B, C]" using assms assmsimpl by auto

    obtain Y where ydef: "Y = projective_plane_data.meet Points Lines incid l l' \<and> Y \<in> Points" 
      using assmsimpl is_proj_plane projective_plane.meet_properties2 by metis

    have ab_distinct: "A \<noteq> B'" using assmsimpl assms projective_plane.nonintersection_distinct[of Points Lines incid l l' A B' Y]
      distinct4_def is_proj_plane projective_plane.meet_properties2 ydef by metis
    have ab_distinct2: "A' \<noteq> B" using assmsimpl assms projective_plane.nonintersection_distinct[of Points Lines incid l' l A' B Y]
      distinct4_def is_proj_plane projective_plane.meet_properties2 ydef by metis
    have ac_distinct: "A \<noteq> C'" using assmsimpl assms projective_plane.nonintersection_distinct[of Points Lines incid l l' A C' Y]
      distinct4_def is_proj_plane projective_plane.meet_properties2 ydef by metis
    have ac_distinct2: "A' \<noteq> C" using assmsimpl assms projective_plane.nonintersection_distinct[of Points Lines incid l' l A' C Y]
      distinct4_def is_proj_plane projective_plane.meet_properties2 ydef by metis
    have bc_distinct: "B \<noteq> C'" using assmsimpl assms projective_plane.nonintersection_distinct[of Points Lines incid l l' B C' Y]
      distinct4_def is_proj_plane projective_plane.meet_properties2 ydef by metis
    have bc_distinct2: "B' \<noteq> C" using assmsimpl assms projective_plane.nonintersection_distinct[of Points Lines incid l' l B' C Y]
      distinct4_def is_proj_plane projective_plane.meet_properties2 ydef by metis
    have aa_distinct: "A \<noteq> A'" using assmsimpl is_proj_plane projective_plane.meet_properties2 projective_plane.unique_meet
      by fastforce
    have bb_distinct: "B \<noteq> B'" using assmsimpl is_proj_plane projective_plane.meet_properties2 projective_plane.unique_meet
      by fastforce
    have cc_distinct: "C \<noteq> C'" using assmsimpl is_proj_plane projective_plane.meet_properties2 projective_plane.unique_meet
      by fastforce

    have d7: "distinct[A, B, C, A', B', C', Y]" 
      using aa_distinct ab_distinct ab_distinct2 ac_distinct ac_distinct2 assmsimpl bb_distinct bc_distinct
        bc_distinct2 cc_distinct ydef by blast

    obtain AB' where ab'_def: "AB' = projective_plane_data.join Points Lines incid A B' \<and> AB' \<in> Lines"
      using ab_distinct assms by (simp add: assmsimpl is_proj_plane projective_plane.join_properties1)
    obtain A'B where a'b_def: "A'B = projective_plane_data.join Points Lines incid A' B \<and> A'B \<in> Lines"
      using ab_distinct2 assms by (simp add: assmsimpl is_proj_plane projective_plane.join_properties1)
    obtain AC' where ac'_def: "AC' = projective_plane_data.join Points Lines incid A C' \<and> AC' \<in> Lines"
      using ac_distinct assms by (simp add: assmsimpl is_proj_plane projective_plane.join_properties1)
    obtain A'C where a'c_def: "A'C = projective_plane_data.join Points Lines incid A' C \<and> A'C \<in> Lines"
      using ac_distinct2 assms by (simp add: assmsimpl is_proj_plane projective_plane.join_properties1)

    have abab_neq: "AB'\<noteq> A'B" using assms projective_plane.two_joins_of_distinct4_distinct[of Points Lines incid l l' A B A' B' AB' A'B]
      ab'_def a'b_def ab_distinct ab_distinct2 assmsimpl is_proj_plane projective_plane.join_properties2 aa_distinct bb_distinct 
      by blast
    have acac_neq: "AC'\<noteq> A'C" using assms projective_plane.two_joins_of_distinct4_distinct[of Points Lines incid l l' A C A' C' AC' A'C]
      ac'_def a'c_def ac_distinct ac_distinct2 assmsimpl is_proj_plane projective_plane.join_properties2 distinct4_def aa_distinct cc_distinct 
      by blast
        
    let ?P = "projective_plane_data.meet Points Lines incid AB' A'B"
    let ?Q = "projective_plane_data.meet Points Lines incid AC' A'C"
    let ?R = "projective_plane_data.meet Points Lines incid (projective_plane_data.join Points Lines incid B C') (projective_plane_data.join Points Lines incid B' C)"

    obtain P where pdef: "P = projective_plane_data.meet Points Lines incid AB' A'B \<and> P \<in> Points" 
      using ab_distinct ab_distinct2 ac_distinct ac_distinct2 abab_neq acac_neq
      by (simp add: a'b_def ab'_def assmsimpl is_proj_plane projective_plane.mjj_point)
    obtain Q where qdef: "Q = projective_plane_data.meet Points Lines incid AC' A'C \<and> Q \<in> Points"
      using ab_distinct ab_distinct2 ac_distinct ac_distinct2 abab_neq acac_neq
      by (simp add: a'c_def ac'_def assmsimpl is_proj_plane projective_plane.mjj_point)

    have pq_neq: "?P \<noteq> ?Q" 
      using assms pdef qdef a'b_def a'c_def ab'_def abab_neq ac'_def ydef
      projective_plane.two_meets_of_distinct8_distinct[of Points Lines incid l l' AB' A'B AC' A'C A B C A' B' C' Y P Q]  acac_neq
      assmsimpl is_proj_plane projective_plane.meet_properties2 d7
      by metis

    obtain l'' where l''_def: "l'' = projective_plane_data.join Points Lines incid P Q \<and> l'' \<in> Lines"
      using is_proj_plane pdef pq_neq projective_plane.join_properties1 qdef by metis

    obtain f where f_def: "f = projective_plane.projectivity Points Lines incid (Cons (A', l, l'') (Cons (A, l'', l') [])) 
             \<and> (f A = A') \<and> (f B = B') \<and> (f C = C') \<and> projective_plane.is_persp_data Points Lines incid (A', l, l'') \<and> projective_plane.is_persp_data Points Lines incid (A, l'', l')"  
      using projective_plane.triplet_to_triplet_diff_lines_two[of Points Lines incid A B C A' B' C' l l' l'' P Q]
      is_proj_plane assms  assmsimpl distinct_abc l''_def pdef qdef a'b_def a'c_def ab'_def ac'_def 
      by blast

    obtain persp_ap where persp_ap_def: "persp_ap = projective_plane.perspectivity Points Lines incid (A', l, l'') \<and>
                    projective_plane.is_persp_data Points Lines incid (A', l, l'')" using f_def by auto
    obtain persp_a where persp_a_def: "persp_a = projective_plane.perspectivity Points Lines incid (A, l'', l') \<and>
                    projective_plane.is_persp_data Points Lines incid (A, l'', l')" using f_def by auto

    have p_not_lp: "\<not> incid P l'" 
      using a'b_def ab'_def assmsimpl distinct4_def is_proj_plane pdef
          projective_plane.join_properties1 projective_plane.meet_properties2
          projective_plane.nonintersection_distinct
      by (smt (verit, ccfv_threshold))

    obtain Y' where yp_def: "Y' = projective_plane_data.meet Points Lines incid l' l'' \<and> Y' \<in> Points" 
      using assms assmsimpl dual_join_is_meet dual_plane_is_projective is_proj_plane l''_def p_not_lp pdef pq_neq
          projective_plane.join_properties1 qdef
      by metis
    obtain A'' where a''def: "A'' = persp_ap A \<and> incid A'' l''" 
      using assmsimpl is_proj_plane persp_ap_def projective_plane.persp_domain.simps projective_plane.persp_range.simps
          projective_plane.perspectivity_nice
      by metis

    have "f = (projective_plane.projectivity Points Lines incid (Cons (A, l'', l') [])) \<circ> (projective_plane.perspectivity Points Lines incid (A', l, l''))"
      by (simp add: f_def is_proj_plane projective_plane.projectivity.simps(2))
    then have f2: "f = (projective_plane.perspectivity Points Lines incid (A, l'', l')) \<circ> (projective_plane.perspectivity Points Lines incid (A', l, l''))"
      by (simp add: is_proj_plane projective_plane.projectivity.simps(1))

    have 1: "persp_a A'' = A'" using a''def f2 f_def persp_a_def persp_ap_def by auto
    have 2: "persp_ap B = P" sorry

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