theory "hadi_zichens_claim" 
  imports "Chapter1-1"
begin

lemma (in projective_plane) pmissed_point:
  fixes l
  assumes "l \<in> Lines"
  shows "\<exists>P. P \<in> Points \<and> (\<not> P \<lhd> l)"
  using assms p3 pcollinear_def by metis

lemma bij_points_to_lines:
  fixes Points1 :: "'p set"
  fixes Lines1 :: "'l set"
  fixes incid1 :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp1: "projective_plane Points1 Lines1 incid1"
  fixes Points2 :: "'p set"
  fixes Lines2 :: "'l set"
  fixes incid2 :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp2: "projective_plane Points2 Lines2 incid2"
  fixes f :: "'p \<Rightarrow> 'p"
  assumes fbij: "bij_betw f Points1 Points2"
  assumes collt: "\<forall>A B C. A \<in> Points1 \<and> B \<in> Points1 \<and> C \<in> Points1 \<and>
    projective_plane_data.pcollinear Points1 Lines1 incid1 A B C
    \<longrightarrow> projective_plane_data.pcollinear Points2 Lines2 incid2 (f A) (f B) (f C)"
  fixes l1 :: 'l
  assumes l1def: "l1 \<in> Lines1"
  shows "\<exists>!l2. l2 \<in> Lines2 \<and> (\<forall>P. P \<in> Points1 \<and> incid1 P l1 \<longrightarrow> incid2 (f P) l2)"
proof -
  obtain A B where abdef: "A \<in> Points1 \<and> B \<in> Points1 \<and> incid1 A l1 \<and> incid1 B l1 
    \<and> A \<noteq> B" using l1def pp1 projective_plane.p4 [of Points1 Lines1 incid1 l1] by auto
  then have l1ab: "l1 = projective_plane_data.join Points1 Lines1 incid1 A B" 
    using l1def pp1 projective_plane.join_properties2 [of _ _ _ A B] by auto
  obtain l2 where l2def: "l2 \<in> Lines2 \<and> l2 = projective_plane_data.join 
    Points2 Lines2 incid2 (f A) (f B)" using abdef fbij bij_betw_iff_bijections 
    pp2 projective_plane.join_properties1 by metis
  have l2_fact2: "\<forall>P. P \<in> Points1 \<and> incid1 P l1 \<longrightarrow> (incid2 (f P) l2)"
  proof (safe)
    fix P
    assume a1: "P \<in> Points1" and a2: "incid1 P l1"
    show "incid2 (f P) l2"
    proof (cases "P = A")
      case True
      then show ?thesis using abdef fbij bij_betw_iff_bijections pp2
        projective_plane.join_properties1 l2def by metis
    next
      case False
      then have "l1 = projective_plane_data.join Points1 Lines1 incid1 A P" 
        using projective_plane.join_properties2 [of _ _ _ A P] 
        a1 a2 l1def abdef pp1 by auto
      then obtain l3 where l3def: "l3 \<in> Lines2 \<and> l3 = projective_plane_data.join 
        Points2 Lines2 incid2 (f A) (f P)" using False a1 abdef fbij pp2
        bij_betw_iff_bijections projective_plane.join_properties1 by metis
      then have pl3: "incid2 (f P) l3" using a1 abdef fbij bij_betw_iff_bijections 
         pp2 projective_plane.join_properties1 False by metis
      have "projective_plane_data.pcollinear Points1 Lines1 incid1 A B P" using a1 a2 
        abdef l1def projective_plane_data.pcollinear_def [of _ _ incid1] by auto
      then have "projective_plane_data.pcollinear Points2 Lines2 incid2 (f A) (f B) (f P)"
        using a1 abdef collt by auto
      then have "l2 = l3" using False a1 abdef l2def l3def fbij bij_betw_iff_bijections pp2
        projective_plane_data.pcollinear_def [of Points2 Lines2 _ "f A" "f B" "f P"]        
        projective_plane.join_properties2 [of Points2 Lines2 incid2 "f A" "f P"]
        projective_plane.join_properties2 [of Points2 Lines2 incid2 "f A" "f B"] by metis
      then show ?thesis using pl3 by auto
    qed
  qed
  have "k \<in> Lines2 \<and> (\<forall>P. P \<in> Points1 \<and> incid1 P l1 \<longrightarrow> incid2 (f P) k) \<Longrightarrow> k = l2" for k
    using pp2 projective_plane.join_properties2 [of Points2 Lines2 incid2 "f A" "f B"]
      abdef l2def fbij bij_betw_iff_bijections by metis
  then show ?thesis using l2def l2_fact2 by blast
qed

theorem zichen:
  fixes Points1 :: "'p set"
  fixes Lines1 :: "'l set"
  fixes incid1 :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp1: "projective_plane Points1 Lines1 incid1"
  fixes Points2 :: "'p set"
  fixes Lines2 :: "'l set"
  fixes incid2 :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp2: "projective_plane Points2 Lines2 incid2"
  fixes f :: "'p \<Rightarrow> 'p"
  assumes fbij: "bij_betw f Points1 Points2"
  assumes collt: "\<forall>A B C. A \<in> Points1 \<and> B \<in> Points1 \<and> C \<in> Points1
    \<and> projective_plane_data.pcollinear Points1 Lines1 incid1 A B C
    \<longrightarrow> projective_plane_data.pcollinear Points2 Lines2 incid2 (f A) (f B) (f C)"
  shows "\<forall>A B C. A \<in> Points1 \<and> B \<in> Points1 \<and> C \<in> Points1
    \<and> projective_plane_data.pcollinear Points2 Lines2 incid2 (f A) (f B) (f C) 
    \<longrightarrow> projective_plane_data.pcollinear Points1 Lines1 incid1 A B C"
proof (safe)
  fix A B C
  assume a1a: "A \<in> Points1" and a1b: "B \<in> Points1" and a1c: "C \<in> Points1" 
  assume a2: "projective_plane_data.pcollinear Points2 Lines2 incid2 (f A) (f B) (f C)"
  show "projective_plane_data.pcollinear Points1 Lines1 incid1 A B C"
  proof (rule ccontr)
    assume cd: "\<not> (projective_plane_data.pcollinear Points1 Lines1 incid1 A B C)"
    show False
    proof -
      obtain l1 where l1def: "l1 \<in> Lines1 \<and> incid1 A l1 \<and> incid1 B l1"
        using pp1 projective_plane.p1 [of _ _ incid1] projective_plane.p3 
        [of _ _ incid1] a1a a1b unfolding projective_plane_def by metis
      obtain l2 where l2def: "l2 \<in> Lines1 \<and> incid1 B l2 \<and> incid1 C l2"
        using pp1 projective_plane.p1 [of _ _ incid1] projective_plane.p3 
        [of _ _ incid1] a1b a1c unfolding projective_plane_def by metis
      then have onlyb: "T \<in> Points1 \<and> incid1 T l1 \<and> incid1 T l2 \<Longrightarrow> T = B" for T
        using a1a a1b a1c cd l1def pp1 projective_plane.p1 [of Points1 Lines1 incid1 T]
        projective_plane_data.pcollinear_def [of _ _ incid1] by auto
      then have l1neql2: "l1 \<noteq> l2" using a1a a1c cd l1def l2def 
        projective_plane_data.pcollinear_def [of _ _ incid1] by auto
      obtain l3 where l3def: "l3 \<in> Lines1 \<and> incid1 A l3 \<and> incid1 C l3"
        using pp1 projective_plane.p1 [of _ _ incid1] projective_plane.p3 
        [of _ _ incid1] a1a a1c unfolding projective_plane_def by metis
      obtain k where kdef: "k \<in> Lines2 \<and> incid2 (f A) k \<and> incid2 (f B) k 
        \<and> incid2 (f C) k" using a1a a1b a1c a2 fbij bij_betwE
        projective_plane_data.pcollinear_def by meson
      obtain Q where qdef: "Q \<in> Points2 \<and> (\<not> incid2 Q k)" using kdef pp2
        projective_plane.pmissed_point [of Points2 Lines2] by auto
      then obtain P where pdef: "P \<in> Points1 \<and> (f P) = Q" using fbij image_iff
        bij_betw_def [of f] by auto
      then obtain PB where pbdef: "PB \<in> Lines1 \<and> incid1 P PB \<and> incid1 B PB" 
        using a1b kdef qdef pp1 projective_plane.p1 [of _ _ _ P B] by blast
      then obtain E where edef: "E \<in> Points1 \<and> incid1 E PB \<and> incid1 E l3"
        using a1c l3def pp1 projective_plane.s [of _ _ _ PB l3] by blast
      then obtain l10 where l10def: "l10 \<in> Lines2 \<and> (\<forall>P. P \<in> Points1 
        \<and> incid1 P l3 \<longrightarrow> incid2 (f P) l10)" using collt l3def fbij pp1 pp2 
        bij_points_to_lines [of _ Lines1] by blast
      then have "incid2 (f A) l10 \<and> incid2 (f C) l10" using a1a a1c l3def by auto
      then have "k = l10" using a1a a1b a1c bij_betw_iff_bijections cd fbij kdef 
        l10def l1def pp2 projective_plane.unique_meet [of _ _ _ k l10 "f A" "f C"]
        projective_plane_data.pcollinear_def [of _ _ incid1] by metis
      then have eonk: "incid2 (f E) k" using edef l10def by auto
      have "projective_plane_data.pcollinear Points1 Lines1 incid1 E P B" 
        using projective_plane_data.pcollinear_def [of _ _ incid1] 
        pbdef edef pdef a1b by auto
      then have "projective_plane_data.pcollinear Points2 Lines2 incid2 (f E) (f P) (f B)" 
        using a1b edef pdef collt by auto
      then obtain m where mdef: "m \<in> Lines2 \<and> incid2 (f E) m \<and> incid2 (f P) m 
        \<and> incid2 (f B) m" using edef pdef a1b a2 fbij bij_betwE
        projective_plane_data.pcollinear_def by meson 
      then have "m = k" using cd a1a a1b a1c edef eonk kdef l3def fbij bij_betw_iff_bijections 
        pp2 projective_plane.unique_meet  [of _ _ _ m k "f E" "f B"] 
        unfolding projective_plane_data.pcollinear_def by metis
      then show False using mdef pdef qdef by auto
    qed
  qed
qed
end