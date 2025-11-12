theory "Chapter2-1"
  imports  "HOL-Library.Uprod" "Chapter1-3" 

begin
declare [[smt_timeout = 1500]]
declare [[smt_reconstruction_step_timeout = 1500]]

(* hide_const join *)

section \<open>Desargues Introduction, Projective 3-Spaces\<close>
locale projective_space_data =
  fixes Points :: "'p set" and Lines :: "'p set set" and Planes:: "'p set set" 
  fixes join:: "'p \<Rightarrow> 'p \<Rightarrow> 'p set"
  fixes plane_through:: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p set"

begin

definition collinear :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where 
  "collinear (A::'p) (B::'p) (C::'p) = (if (A \<in> Points \<and> B \<in> Points \<and> C \<in> Points)  
    then (\<exists>l. l \<in> Lines \<and> A \<in> l \<and> B \<in> l \<and> C \<in> l) else undefined)"

definition coplanar :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "coplanar (A::'p) (B::'p) (C::'p) D = (if (A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points)  
    then (\<exists>H. H \<in> Planes \<and> A \<in> H \<and> B \<in> H \<and> C \<in> H \<and> D \<in> H) else undefined)"

definition coincident :: "'p set \<Rightarrow> 'p set \<Rightarrow> 'p set \<Rightarrow> bool" where
  "coincident n k m  = (if (n \<in> Lines) \<and> (k \<in> Lines) \<and> (m  \<in> Lines)
    then (\<exists>P. P \<in> Points \<and> P \<in> n \<and> P \<in> k \<and> P \<in> m) else undefined)"

end

locale projective_space = projective_space_data Points Lines Planes join plane_through
  for
     Points :: "'p set" and
     Lines :: "'p set set" and
     Planes :: "'p set set" and
     join :: "'p \<Rightarrow> 'p \<Rightarrow> 'p set" and
     plane_through :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p set" + 
assumes
    S1a: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (P \<in> join P Q \<and> Q \<in> join P Q \<and> (join P Q) \<in> Lines)" and
    S1b: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points; k \<in> Lines; P \<in> k; Q \<in> k\<rbrakk> \<Longrightarrow> (k = join P Q)" and
    S2a: "\<lbrakk>\<not> collinear P Q R; P \<in> Points; Q \<in> Points; R \<in> Points\<rbrakk> \<Longrightarrow> (P \<in> plane_through P Q R 
      \<and> Q \<in> plane_through P Q R \<and> R \<in> plane_through P Q R \<and> (plane_through P Q R) \<in> Planes)" and
    S2b: "\<lbrakk>\<not> collinear P Q R; P \<in> Points; Q \<in> Points; R \<in> Points; H \<in> Planes; P \<in> H; Q \<in> H; R \<in> H\<rbrakk> 
      \<Longrightarrow> (H = plane_through P Q R)" and 
    S3: "\<lbrakk>k \<in> Lines; H \<in> Planes; \<not> k \<subseteq> H\<rbrakk> \<Longrightarrow> (\<exists>!P. P \<in> k \<and> P \<in> H)" and
    S4: "\<lbrakk>H \<in> Planes; N \<in> Planes \<rbrakk> \<Longrightarrow> (\<exists>k \<in> Lines. k \<subseteq> H \<and> k \<subseteq> N)" and
    S5: "(\<exists>P Q R S. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points \<and> 
          \<not> coplanar P Q R S \<and> 
          \<not> collinear P Q R \<and> \<not> collinear P Q S \<and> \<not> collinear P R S \<and> \<not> collinear Q R S)" and
    S6: "\<lbrakk>k \<in> Lines\<rbrakk> \<Longrightarrow> (\<exists>P Q R . P \<in> k \<and> Q \<in> k \<and> R \<in> k \<and> distinct3 P Q R)" and
    S0a: "\<lbrakk>k \<in> Lines; P \<in> k\<rbrakk> \<Longrightarrow> P \<in> Points" and
    S0b: "\<lbrakk>H \<in> Planes; P \<in> H\<rbrakk> \<Longrightarrow> P \<in> Points"
begin

text \<open>\hadi\<close>
lemma S5_dist:
  fixes P Q R S
  assumes "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points 
    \<and> S \<in> Points \<and> \<not> coplanar P Q R S \<and> \<not> collinear P Q R 
    \<and> \<not> collinear P Q S \<and> \<not> collinear P R S \<and> \<not> collinear Q R S"
  shows "distinct4 P Q R S" 
  using assms S2a distinct4_def unfolding coplanar_def by metis

lemma collinear_commute:
  fixes P Q R
  assumes "collinear P Q R"
  shows "collinear Q P R \<and> collinear P R Q"
  using assms collinear_def by auto

lemma joins_eq_collinear:
  fixes P Q R
  assumes "P \<in> Points" and "Q \<in> Points" and "R \<in> Points"
  assumes "P \<noteq> Q" and "Q \<noteq> R"
  assumes "(join P Q) = (join Q R)"
  shows "collinear P Q R" 
  using assms S1a collinear_def by auto
text \<open>\done\<close>

lemma point_outside_plane: (* For any plane H, there's a point P not on it *)
  assumes "H \<in> Planes"
  obtains P where "P \<in> Points \<and> P \<notin> H"
  using assms S2a S2b S5 unfolding coplanar_def by metis

lemma crossing_planes: (* two distinct planes intersect in exactly one line *) 
  assumes "H \<in> Planes \<and> K \<in> Planes"
  assumes "H \<noteq> K"
  shows "\<exists>!n \<in> Lines . (n = (H \<inter> K))"
proof -
  from S4 obtain k where kdef: "k \<in> Lines \<and> k \<subseteq> H \<and> k \<subseteq> K" using assms by blast
  from S6 obtain A B where abdef: "A \<in> k \<and> B \<in> k \<and> A \<noteq> B" using kdef distinct3_def by metis
  from kdef  have "k \<subseteq> H \<inter> K" by blast
  have empty_diff: "(H \<inter> K) - k = {}" 
  proof (rule ccontr)
    assume ch: "\<not> ((H \<inter> K) - k = {})"
    then obtain P where pdef:" P \<in> (H \<inter> K) - k" by blast
    have nc: "\<not> collinear P A B" using pdef kdef abdef S1b [of A B] S0a S0b 
      assms Diff_iff Int_iff unfolding collinear_def by metis
    have abph: "A \<in> H \<and> B \<in> H \<and> P \<in> H" using abdef pdef kdef by blast
    have abpk: "A \<in> K \<and> B \<in> K \<and> P \<in> K" using abdef pdef kdef by blast
    from S0b S2a S2b nc have "H = K" using abph abpk assms by metis
    then show False using assms by auto
  qed
  have "H \<inter> K = k" using empty_diff kdef by auto
  then show ?thesis using kdef by auto
qed

lemma two_point_line_in_plane:
  fixes P Q H
  assumes "H \<in> Planes"
  assumes "P \<in> Points" and "Q \<in> Points"
  assumes "P \<in> H" and "Q \<in> H"
  assumes "P \<noteq> Q"
  shows "join P Q \<subseteq> H" 
  using assms S1a S3 by blast

text \<open>\hadi\<close>
lemma outside_plane_ncoll:
  fixes P Q R H
  assumes "H \<in> Planes"
  assumes "P \<in> Points" and "Q \<in> Points" and "R \<in> Points"
  assumes "P \<in> H" and "Q \<in> H" and "R \<notin> H"
  assumes "P \<noteq> Q"
  shows "\<not> collinear P Q R"
proof -
  have "(join P Q) \<subseteq> H" using assms two_point_line_in_plane by simp
  then show ?thesis using assms S1b collinear_def by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma extra_point: 
  fixes P Q H
  assumes "H \<in> Planes"
  assumes "P \<in> Points" and "Q \<in> Points"
  assumes "P \<noteq> Q"
  shows "\<exists>R \<in> Points. (\<not> collinear P Q R) \<and> (R \<notin> H)"
proof -
  obtain R where Rdef: "R \<in> Points \<and> R \<notin> H" 
    using assms point_outside_plane by auto
  show ?thesis
  proof (cases "collinear P Q R")
    case PQRcoll: True
    consider (OneH) "(P \<in> H \<and> Q \<notin> H) \<or> (P \<notin> H \<and> Q \<in> H)" 
      | (BothH) "P \<in> H \<and> Q \<in> H" | (NeitherH) "P \<notin> H \<and> Q \<notin> H" by auto
    then show ?thesis
    proof (cases)
      case OneH
      obtain S where Sdef: "S \<in> H \<and> S \<noteq> P \<and> S \<noteq> Q"
        using assms S4 S6 subset_eq unfolding distinct3_def by metis
      obtain T where Tdef: "T \<in> (join R S) \<and> T \<noteq> R \<and> T \<noteq> S" 
        using assms Rdef Sdef S0b S1a S6 distinct3_def by metis
      then have TnH: "T \<notin> H" using assms Rdef Sdef outside_plane_ncoll [of H] 
        S0b S1a unfolding collinear_def by metis
      have "\<not> collinear P Q T" using assms Rdef Sdef Tdef OneH PQRcoll
        outside_plane_ncoll [of H _ S] S0a [of "join R S"] S0b [of H] 
        S1a [of R S] S1b unfolding collinear_def by metis
      then show ?thesis using assms Rdef Sdef Tdef S0a S0b S1a TnH by metis
    next
      case BothH
      then show ?thesis using assms Rdef outside_plane_ncoll [of H] by auto
    next
      case NeitherH
      obtain k where kdef: "k \<in> Lines \<and> P \<in> k \<and> Q \<in> k \<and> R \<in> k"
        using assms Rdef PQRcoll collinear_def by auto
      then obtain S where Sdef: "S \<in> k \<and> S \<in> H \<and> (\<forall>G. G \<in> k \<and> G \<in> H \<longrightarrow> G = S)"
        using assms Rdef S3 [of k] subset_iff by metis
      then obtain T where Tdef: "T \<in> H \<and> T \<noteq> S"
        using assms S4 S6 subset_iff distinct3_def by metis
      then obtain U where Udef: "U \<in> (join Q T) \<and> U \<noteq> Q \<and> U \<noteq> T"
        using assms NeitherH S0b S1a S6 distinct3_def by metis
      then have UnH: "U \<in> Points \<and> U \<notin> H" using assms NeitherH Tdef S0a S0b 
        S1a S1b S3 [of "join Q T" H] subset_iff by metis
      have "\<not> collinear P Q U"
      proof (rule ccontr)
        assume "\<not> (\<not> collinear P Q U)"
        then obtain l where ldef: "l \<in> Lines \<and> P \<in> l \<and> Q \<in> l \<and> U \<in> l"
          using assms NeitherH Tdef Udef UnH collinear_def by metis
        then have leqk: "l = k" using assms kdef S1b by blast
        then have "\<forall>G. G \<in> l \<and> G \<in> H \<longrightarrow> G = S" using Sdef by simp
        then show False using assms Tdef Udef ldef S0a S0b S1a S1b by metis
      qed
      then show ?thesis using UnH by auto
    qed
  next
    case False
    then show ?thesis using Rdef by auto
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma plane_through_point_line:
  fixes P l
  assumes "P \<in> Points" and "l \<in> Lines"
  assumes "P \<notin> l"
  shows "\<exists>!H \<in> Planes. P \<in> H \<and> l \<subseteq> H"
proof -
  obtain Q R where QRdef: "Q \<in> Points \<and> R \<in> Points \<and> Q \<noteq> R \<and> l = (join Q R)" 
    using assms S0a S1b S6 distinct3_def by metis
  then have pqrncoll: "\<not> collinear P Q R" using assms S1b 
    unfolding collinear_def by metis
  then obtain H where 
    Hdef: "H \<in> Planes \<and> H = (plane_through P Q R) \<and> P \<in> H \<and> l \<subseteq> H" 
    using assms QRdef pqrncoll two_point_line_in_plane S2a by auto
  then have "N \<in> Planes \<and> P \<in> N \<and> l \<subseteq> N \<longrightarrow> N = H" for N
    using assms S1a S2b QRdef pqrncoll in_mono by metis
  then show ?thesis using Hdef by metis
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma collinear_implies_coplanar:
  fixes P Q R
  assumes "P \<in> Points" and "Q \<in> Points" and "R \<in> Points"
  assumes "distinct3 P Q R" and "collinear P Q R"
  shows "\<exists>S \<in> Points. distinct4 P Q R S \<and> coplanar P Q R S"
proof -
  obtain l where ldef: "l \<in> Lines \<and> P \<in> l \<and> Q \<in> l \<and> R \<in> l" 
    using assms unfolding collinear_def by auto
  then obtain S where Sdef: "S \<in> Points \<and> S \<notin> l" using S5 collinear_def by metis
  then have PQRSdist: "distinct4 P Q R S" 
    using assms ldef distinct3_def distinct4_def by metis
  obtain H where Hdef: "H \<in> Planes \<and> S \<in> H \<and> l \<subseteq> H" 
    using ldef Sdef plane_through_point_line by blast
  then show ?thesis using assms ldef Sdef PQRSdist Hdef subset_eq
    unfolding coplanar_def by metis
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma crossing_lines:
  fixes k n P
  assumes "k \<in> Lines" and "n \<in> Lines"
  assumes "k \<noteq> n"
  assumes "P \<in> Points"
  assumes "P \<in> k \<inter> n"
  shows "\<exists>!H. H \<in> Planes \<and> k \<subseteq> H \<and> n \<subseteq> H"
proof -
  obtain Q where qdef: "Q \<in> k \<and> Q \<notin> n" using assms S0a S1b S6 
    distinct3_def by metis
  obtain R where rdef: "R \<in> n \<and> R \<notin> k" using assms S0a S1b S6 
    distinct3_def by metis
  then have pqr: "\<not> collinear P Q R" using assms qdef S0a S1b Int_iff
    unfolding collinear_def by metis
  then obtain H where Hdef: "H \<in> Planes \<and> H = plane_through P Q R"
    using assms qdef rdef S0a S2a by simp
  then have Hkn: "k \<subseteq> H \<and> n \<subseteq> H" 
    using assms pqr qdef rdef S0a S2a S3 [of _ H] Int_iff by metis
  have "N \<in> Planes \<and> k \<subseteq> N \<and> n \<subseteq> N \<Longrightarrow> H = N" for N using assms pqr qdef rdef
    Hdef S0a S2b [of P Q R] Int_iff subset_iff by metis
  then show ?thesis using Hdef Hkn by metis
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma space_plane_p2:
  fixes H k n
  assumes "H \<in> Planes" and "k \<in> Lines" and "n \<in> Lines"
  assumes "k \<subseteq> H" and "n \<subseteq> H"
  shows "\<exists>P. (P \<in> H \<and> P \<in> k \<and> P \<in> n)"
proof -
  obtain Pk Qk Rk where k_pts: "Pk \<in> k \<and> Qk \<in> k \<and> Rk \<in> k \<and> distinct3 Pk Qk Rk" 
    using assms S6 [of k] by auto
  show "\<exists>P. (P \<in> H \<and> P \<in> k \<and> P \<in> n)"
  proof (cases "k = n")
    case True
    then show ?thesis using assms k_pts by auto
  next
    case kndist: False
    obtain X where Xdef: "X \<in> Points \<and> X \<notin> H" 
      using assms point_outside_plane by blast
    then have "X \<notin> k \<and> X \<notin> n"  using assms by auto
    then obtain U V where Udef: "U \<in> Planes \<and> X \<in> U \<and> k \<subseteq> U" 
      and Vdef: "V \<in> Planes \<and> X \<in> V \<and> n \<subseteq> V" 
      using assms Xdef plane_through_point_line by metis
    then have k_int: "k \<in> Lines \<and> k \<subseteq> H \<and> k \<subseteq> U" using assms by simp
    then obtain S where Sdef: "S \<in> k \<and> S \<in> V" using k_pts Vdef S3 in_mono by metis
    then have "S \<in> n" 
      using assms Xdef Vdef k_int plane_through_point_line S0b by blast
    then show ?thesis using assms Sdef Vdef k_int by auto
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma crossing_lines_2:
  fixes k n H
  assumes "k \<in> Lines" and "n \<in> Lines"
  assumes "k \<noteq> n"
  assumes "H \<in> Planes"
  assumes "k \<subseteq> H \<and> n \<subseteq> H"
  shows "\<exists>!P. P \<in> Points \<and> P \<in> k \<and> P \<in> n"
proof -
  have "\<exists>P. (P \<in> H \<and> P \<in> k \<and> P \<in> n)" 
    using assms space_plane_p2 [of H] by simp
  then have pexist: "\<exists>P. P \<in> Points \<and> P \<in> k \<and> P \<in> n" using assms S0b by auto
  then obtain P where "P \<in> Points \<and> P \<in> k \<and> P \<in> n" by auto
  then have "Q \<in> Points \<and> Q \<in> k \<and> Q \<in> n \<longrightarrow> Q = P" for Q 
    using assms S1b [of Q P] by auto
  then show ?thesis using pexist by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma space_plane_p3:
  fixes H
  assumes HP: "H \<in> Planes"
  shows "\<exists>P Q R. P \<in> H \<and> Q \<in> H \<and> R \<in> H \<and> distinct3 P Q R \<and> \<not> (collinear P Q R)"
proof -
  obtain P Q where PQdef: "P \<in> H \<and> Q \<in> H \<and> P \<noteq> Q" 
    using HP S4 S6 distinct3_def subset_iff by metis
  then have PQpts: "P \<in> Points \<and> Q \<in> Points" using HP S0b by simp
  then obtain S where Sdef: "S \<in> Points \<and> S \<notin> H \<and> \<not> collinear P Q S" 
    using HP PQdef extra_point by blast
  then obtain N where Ndef: "N \<in> Planes \<and> N = plane_through P Q S" 
    using PQpts S2a by auto
  then have "H \<noteq> N" using PQpts Sdef S2a by auto
  then have PQisHiN: "(join P Q) = H \<inter> N" 
    using HP PQdef PQpts Sdef Ndef crossing_planes S1b S2a IntI by metis
  obtain T where Tdef: "T \<in> Points \<and> T \<notin> N \<and> \<not> collinear Q S T" 
    using PQdef PQpts Sdef Ndef extra_point by blast
  then obtain M where Mdef: "M \<in> Planes \<and> M = plane_through Q S T"
    using PQpts Sdef S2a by auto
  then have "M \<noteq> H" using PQpts Sdef Tdef S2a by auto
  then obtain l where ldef: "l \<in> Lines \<and> l = M \<inter> H"
    using HP Mdef crossing_planes by auto
  then have "l \<noteq> (join P Q)"
    using PQpts Sdef Tdef Ndef Mdef S1a S2a S2b Int_iff by metis
  then obtain R where Rdef: "R \<in> l \<and> R \<notin> (join P Q)" using PQdef PQpts ldef
    S0a S1a S1b S6 [of l] unfolding distinct3_def by metis
  then have "\<not> collinear P Q R" using HP PQdef Sdef PQisHiN Ndef ldef 
    outside_plane_ncoll S0a S0b S2a Int_iff by metis
  then show ?thesis 
    using PQdef PQpts Rdef ldef S0a S1a Int_iff distinct3_def by metis
qed

lemma plane_by_three_points:
  fixes H
  assumes "H \<in> Planes"
  shows "\<exists>P Q R. (H = plane_through P Q R)"
  using assms S0b S2b space_plane_p3 [of H] by blast
text \<open>\done\<close>

text \<open>\hadi\<close>
theorem space_plane_is_proj_plane:
  fixes H
  assumes HP: "H \<in> Planes"
  defines HLdef: "HLines \<equiv> {L. L \<in> Lines \<and> L \<subseteq> H}"
  defines Hidef: "Hincid \<equiv> (\<lambda>P L. (if P \<in> H \<and> L \<in> HLines then P \<in> L else undefined))"
  shows "projective_plane H HLines Hincid"
proof (unfold_locales)
  show "\<lbrakk>P \<noteq> Q; P \<in> H; Q \<in> H\<rbrakk> \<Longrightarrow> (\<exists>!k. k \<in> HLines \<and> Hincid P k \<and> Hincid Q k)" for P Q
  proof -
    assume pnq: "P \<noteq> Q" and php: "P \<in> H" and qhp: "Q \<in> H"
    then have pqhl: "(join P Q) \<in> HLines" 
      using two_point_line_in_plane S0b S1a HP HLdef by auto
    then have kexist: "\<exists>k. k \<in> HLines \<and> Hincid P k \<and> Hincid Q k" 
      using pnq php qhp S0b S1a HP Hidef by metis
    then have "l \<in> HLines \<and> Hincid P l \<and> Hincid Q l \<Longrightarrow> l = (join P Q)" for l 
      using pnq php qhp S0a S1b HLdef Hidef by simp
    then show "\<exists>!k. k \<in> HLines \<and> Hincid P k \<and> Hincid Q k" using kexist by auto
  qed
  show "\<lbrakk>k \<in> HLines; n \<in> HLines\<rbrakk> \<Longrightarrow> \<exists>P. (P \<in> H \<and> Hincid P k \<and> Hincid P n)"
    for k n using assms space_plane_p2 [of H k n] by auto
  show "\<exists>P Q R. P \<in> H \<and> Q \<in> H \<and> R \<in> H \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R 
    \<and> \<not> (projective_plane_data.pcollinear H HLines Hincid P Q R)"
  proof -
    obtain P Q R where PQRdef: "P \<in> H \<and> Q \<in> H \<and> R \<in> H \<and> distinct3 P Q R 
      \<and> \<not> collinear P Q R" using HP space_plane_p3 [of H] by auto
    then have "\<not> (projective_plane_data.pcollinear H HLines Hincid P Q R)"
      using HP HLdef Hidef S0b [of H] mem_Collect_eq collinear_def
      unfolding projective_plane_data.pcollinear_def by auto
    then show ?thesis using PQRdef unfolding distinct3_def by auto
  qed
  show "\<lbrakk>k \<in> HLines; U = {P. (P \<in> H \<and> Hincid P k)}\<rbrakk> 
    \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct[Q,R,S]" for k U
  proof -
    assume khl: "k \<in> HLines" and Uset: "U = {P. (P \<in> H \<and> Hincid P k)}"
    then obtain Q R S where qrs: "Q \<in> k \<and> R \<in> k \<and> S \<in> k \<and> distinct3 Q R S" 
      using S6 HLdef by blast
    then have "Q \<in> U \<and> R \<in> U \<and> S \<in> U" using khl Uset qrs S0a HLdef Hidef by auto
    then show "\<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct[Q,R,S]" using qrs 
      distinct_length_2_or_more distinct_singleton unfolding distinct3_def by metis
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma projected_points_collinear:
  fixes H X A B C A' C'
  assumes "H \<in> Planes" and "X \<in> Points" and "A \<in> Points" and "B \<in> Points" 
    and "C \<in> Points" and "A' \<in> Points" and "C' \<in> Points"
  assumes "A \<noteq> C" and "A' \<noteq> C'"
  assumes "A \<in> H" and "B \<in> H" and "C \<in> H"
  assumes "X \<notin> H" and "A' \<notin> H" and "C' \<notin> H"
  assumes "collinear X A A'" and "collinear X C C'"
  assumes "collinear A' B C'"
  shows "collinear A B C"
proof -
  obtain l where ldef: "l \<in> Lines \<and> A' \<in> l \<and> B \<in> l \<and> C' \<in> l"
    using assms unfolding collinear_def by auto
  have ACXncoll: "\<not> collinear A C X" 
    using assms outside_plane_ncoll by auto
  then obtain N where Ndef: "N \<in> Planes \<and> N = (plane_through A C X)"
    using assms S2a by auto
  then obtain k where kdef: "k \<in> Lines \<and> k = H \<inter> N" 
    using assms ACXncoll crossing_planes S2a by blast
  then have ACink: "A \<in> k \<and> C \<in> k" using assms ACXncoll Ndef S2a by simp
  have "(join A' C') \<subseteq> N" using assms Ndef S2a outside_plane_ncoll
    two_point_line_in_plane [of N A' C'] by metis
  then show ?thesis using assms ldef kdef ACink S1b [of A' C'] 
    collinear_def by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
theorem desargues_case_1:
  fixes U A B C A' B' C' P Q R
  assumes "U \<in> Points" and "A \<in> Points" and "B \<in> Points" and "C \<in> Points"
    and "A' \<in> Points" and "B' \<in> Points" and "C' \<in> Points"
  assumes "distinct7 U A B C A' B' C'" 
  assumes "collinear A A' U" and "collinear B B' U" and "collinear C C' U"
  assumes "\<not> collinear A B C" and "\<not> collinear A' B' C'" 
  assumes "plane_through A B C \<noteq> plane_through A' B' C'"
  assumes "join A B \<noteq> join A' B'"
  assumes "join A C \<noteq> join A' C'"
  assumes "join B C \<noteq> join B' C'"
  assumes "P \<in> (join A B) \<inter> (join A' B')"
  assumes "Q \<in> (join A C) \<inter> (join A' C')"
  assumes "R \<in> (join B C) \<inter> (join B' C')"
  shows "collinear P Q R"
proof -
  let ?abc = "plane_through A B C" let ?a'b'c' = "plane_through A' B' C'"
  have "P \<in> ?abc" and "P \<in> ?a'b'c'" and "Q \<in> ?abc" and "Q \<in> ?a'b'c'" 
    and "R \<in> ?abc" and "R \<in> ?a'b'c'" using assms S2a two_point_line_in_plane 
    distinct7_def Int_iff inf_absorb2 by metis+
  then obtain k where "k \<in> Lines \<and> P \<in> k \<and> Q \<in> k \<and> R \<in> k" 
    using assms crossing_planes S2a Int_iff by metis
  then show ?thesis using S0a collinear_def by auto
qed

theorem desargues_case_2:
  fixes U A B C A' B' C' P Q R
  assumes "U \<in> Points" and "A \<in> Points" and "B \<in> Points" and "C \<in> Points" and
    "A' \<in> Points" and "B' \<in> Points" and "C' \<in> Points"
  assumes "distinct7 U A B C A' B' C'" 
  assumes "collinear A A' U" and "collinear B B' U" and "collinear C C' U"
  assumes "\<not> collinear A B C" and "\<not> collinear A' B' C'" 
  assumes "plane_through A B C = plane_through A' B' C'"
  assumes "join A B \<noteq> join A' B'"
  assumes "join A C \<noteq> join A' C'"
  assumes "join B C \<noteq> join B' C'"
  assumes "P \<in> (join A B) \<inter> (join A' B')"
  assumes "Q \<in> (join A C) \<inter> (join A' C')"
  assumes "R \<in> (join B C) \<inter> (join B' C')"
  shows "collinear P Q R"
proof -
  let ?S = "plane_through A B C"
  have Spts: "A \<in> ?S \<and> B \<in> ?S \<and> C \<in> ?S \<and> A' \<in> ?S \<and> B' \<in> ?S \<and> C' \<in> ?S"
    using assms S2a by auto
  have PQRinS: "P \<in> ?S \<and> Q \<in> ?S \<and> R \<in> ?S" using assms S2a in_mono inf_le1
    two_point_line_in_plane [of ?S] unfolding distinct7_def by (metis (full_types))
  obtain X where xdef: "X \<in> Points \<and> X \<notin> ?S" 
    using assms S2a point_outside_plane by blast
  then have XBnS: "\<not> (join X B) \<subseteq> ?S" and XB'nS: "\<not> (join X B') \<subseteq> ?S"
    using assms Spts S1a subset_eq by metis+
  obtain D where ddef: "D \<in> Points \<and> D \<in> (join X B) \<and> D \<noteq> X \<and> D \<noteq> B" 
    using assms xdef S0a S1a S2a S6 distinct3_def by metis
  then have "(join X D) \<in> Lines \<and> \<not> (join X D) \<subseteq> ?S" 
    using xdef S1a subset_iff by metis
  then have "\<forall>G. G \<in> (join X D) \<and> G \<in> ?S \<longrightarrow> G = B" 
    using assms xdef ddef S1a S1b S2a S3 by metis
  then have DnS: "D \<notin> ?S" using xdef ddef S1a by auto
  let ?ubx = "plane_through U B X"
  have nubx: "\<not> collinear U B X" 
    using assms xdef S1b S2a two_point_line_in_plane [of ?S B]
    distinct7_def distinct3_def in_mono unfolding collinear_def by (smt (verit))
  then have "join U B \<subseteq> ?ubx" using assms xdef S2a two_point_line_in_plane
    by (metis distinct7_def)
  then have "B' \<in> ?ubx" using assms S1b distinct7_def in_mono
    unfolding collinear_def by metis
  then have xb'inubx: "join X B' \<subseteq> ?ubx" and "join X B \<subseteq> ?ubx"
    using assms nubx xdef S2a two_point_line_in_plane by metis+
  then have "D \<in> ?ubx" using ddef by auto
  then have "join U D \<subseteq> ?ubx" using assms nubx xdef S1a S2a two_point_line_in_plane 
    ddef unfolding collinear_def by metis
  then obtain D' where d'def: "D' \<in> Points \<and> D' \<in> (join U D) \<inter> (join X B')" 
    using assms xdef nubx ddef xb'inubx crossing_lines_2 [of "join U D"] 
    S1a S2a IntI unfolding collinear_def by metis
  have nub'x: "\<not> collinear U B' X"
  proof (rule ccontr)
    assume "\<not> (\<not> collinear U B' X)"
    then obtain l where ldef: "l \<in> Lines \<and> U \<in> l \<and> B' \<in> l \<and> X \<in> l" 
      using assms xdef unfolding collinear_def by presburger
    then have "l = join U X" using assms nubx xdef S1b 
      unfolding collinear_def by metis
    then have uxub': "join U X = join U B'" using assms ldef S1b
      unfolding distinct7_def by metis
    have "B \<in> join U B'" using assms(1,3,6,8,10) S1b collinear_def 
      unfolding distinct7_def by auto
    then have "B \<in> join U X" using uxub' by simp
    then have "collinear U B X" using assms ldef xdef S1b 
      unfolding collinear_def by metis
    then show False using nubx by simp
  qed
  have und': "U \<noteq> D'"
  proof
    assume "U = D'"
    then have "U \<in> join X B'" using d'def by auto
    then have "collinear U B' X" using assms xdef S1a S2a 
      unfolding collinear_def by metis
    then show False using nub'x by simp
  qed
  have newdist: "distinct7 U A D C A' D' C'"
  proof (rule ccontr)
    assume "\<not> distinct7 U A D C A' D' C'"
    then consider
    "U = A" | "U = C" | "U = A'" | "U = C'" | "A = C" | "A = A'" | "A = C'" 
    | "C = A'" | "C = C'" | "A' = C'" | "U = D" | "A = D" | "D = C'" 
    | "D = C" | "U = D'" | "A = D'"  | "D = A'" | "D = D'"  | "C = D'" 
    | "A' = D'" | "D' = C'" unfolding distinct7_def by fastforce
    then show False using assms unfolding distinct7_def apply cases apply simp+
    using S1a ddef nubx xdef unfolding collinear_def
    apply metis using assms S1a S1b S2a ddef in_mono
      two_point_line_in_plane xdef unfolding distinct7_def apply (smt (verit))
    using assms S1a S1b S2a ddef in_mono
      two_point_line_in_plane xdef apply (smt (verit))
    using assms S1a S1b S2a ddef in_mono
      two_point_line_in_plane xdef apply (smt (verit))
    using und' unfolding distinct7_def apply simp
    using assms Spts xdef ddef d'def outside_plane_ncoll S1a S2a Int_iff
    unfolding collinear_def distinct7_def apply (smt (verit, ccfv_threshold))
    using assms Spts xdef ddef d'def XBnS S1a S1b S2a S3 
    unfolding distinct7_def apply metis
    using assms Spts xdef ddef d'def XBnS S1a S1b S2a S3 Int_iff
    unfolding distinct7_def apply metis
    using assms Spts xdef ddef d'def outside_plane_ncoll S1a S2a Int_iff
    unfolding collinear_def distinct7_def by (smt (verit, ccfv_threshold))+
  qed
  have dd'u: "collinear D D' U" using assms S1a ddef d'def IntE
    unfolding collinear_def by metis
  have adca'd'c'ncoll: "(\<not> collinear A D C) \<and> (\<not> collinear A' D' C')"
  proof (rule ccontr)
    assume cd: "\<not> ((\<not> collinear A D C) \<and> (\<not> collinear A' D' C'))"
    then obtain l where ldef: "l \<in> Lines \<and> ((A \<in> l \<and> D \<in> l \<and> C \<in> l)
      \<or> (A' \<in> l \<and> D' \<in> l \<and> C' \<in> l))" using assms ddef d'def collinear_def by auto
    then have lac: "(l = join A C) \<or> (l = join A' C')" using assms S1a S1b 
      unfolding collinear_def by (metis (no_types))
    have "(join A C \<subseteq> ?S) \<or> (join A' C' \<subseteq> ?S)" using assms ldef S1a S2a 
      two_point_line_in_plane unfolding collinear_def by metis
    then have "(D \<in> ?S) \<or> (D' \<in> ?S)" using assms Spts ldef lac S0a S2a
      two_point_line_in_plane [of ?S] in_mono unfolding distinct7_def by metis
    then have "D = B \<or> D' = B'" using assms S1a S1b S2a xdef ddef d'def 
      Int_iff in_mono two_point_line_in_plane by (smt (verit))
    then show False using assms cd xdef ddef XBnS S1a S2a S3 
      outside_plane_ncoll collinear_commute distinct7_def by metis
  qed
  then obtain H N where HNdef: "H \<in> Planes \<and> N \<in> Planes \<and> H = (plane_through A D C) 
    \<and> N = (plane_through A' D' C')" using assms d'def ddef S2a by simp
  then have HneqN: "H \<noteq> N" using assms Spts xdef ddef d'def adca'd'c'ncoll XBnS 
    crossing_lines S0a S1a S2a S3 Int_iff distinct7_def by (smt (verit, del_insts))
  have ada'd': "join A D \<noteq> join A' D'"
  proof
    assume cd: "join A D = join A' D'"
    then have "(join A D) \<subseteq> N" using assms newdist d'def adca'd'c'ncoll HNdef
      S2a two_point_line_in_plane distinct7_def by metis
    then show False using assms(12,2,3,4,5) cd Spts xdef ddef d'def newdist 
      S1a S1b S2a S3 subset_iff unfolding distinct7_def by (smt (z3))
  qed
  have dcd'c': "join D C \<noteq> join D' C'"
  proof
    assume cd: "join D C = join D' C'"
    then have "(join D C) \<subseteq> N" using assms newdist d'def adca'd'c'ncoll HNdef
      S2a two_point_line_in_plane distinct7_def by metis
    then show False using assms(12,2,3,4,7) cd Spts xdef ddef d'def newdist
      S1a S1b S2a S3 subset_iff unfolding distinct7_def by (smt (verit))
  qed
  have uadncoll: "\<not> collinear U A D" using assms ddef d'def ada'd' newdist S1b 
    Int_iff unfolding collinear_def distinct7_def by metis
  then obtain K where Kdef: "K \<in> Planes \<and> K = (plane_through U A D)"
    using assms ddef S2a by simp
  then have ADA'D'K: "(join A D) \<subseteq> K \<and> (join A' D') \<subseteq> K" using assms uadncoll 
    ddef d'def dd'u newdist two_point_line_in_plane outside_plane_ncoll 
    collinear_commute S2a distinct7_def by metis
  then obtain P'::'p where p'def: "P' \<in> (join A D) \<and> P' \<in> (join A' D')" 
    using assms ddef d'def newdist Kdef space_plane_p2 S1a distinct7_def by metis
  have uadncoll: "\<not> collinear U D C" using assms ddef d'def dcd'c' newdist S1b 
    Int_iff unfolding collinear_def distinct7_def by metis
  then obtain M where Mdef: "M \<in> Planes \<and> M = (plane_through U D C)"
    using assms ddef S2a by simp
  then have "(join D C) \<subseteq> M \<and> (join D' C') \<subseteq> M" using assms uadncoll 
    ddef d'def dd'u newdist two_point_line_in_plane outside_plane_ncoll 
    collinear_commute S2a distinct7_def by metis
  then obtain R'::'p where r'def: "R' \<in> (join D C) \<and> R' \<in> (join D' C')"
    using assms ddef d'def newdist Mdef space_plane_p2 S1a distinct7_def by metis
  then have P'QR'coll: "collinear P' Q R'"
    using assms ddef d'def newdist ada'd' dcd'c' dd'u adca'd'c'ncoll
    HNdef HneqN p'def desargues_case_1 [of U A D C A' D' C'] by auto
  have XneqP': "X \<noteq> P'" and XneqR': "X \<noteq> R'" 
    using assms Spts xdef ddef XBnS adca'd'c'ncoll HNdef p'def r'def
    two_point_line_in_plane S0a S0b S1a S1b S2a unfolding distinct7_def by metis+
  have PXP'RXR': "P \<in> (join X P') \<and> R \<in> (join X R')"
  proof
    show "P \<in> (join X P')" sorry
    show "R \<in> (join X R')" sorry
  qed
  have P'nAA': "P' \<noteq> A \<and> P' \<noteq> A'" and R'nCC': "R' \<noteq> C \<and> R' \<noteq> C'"
    using assms ddef d'def ada'd' dcd'c' newdist p'def r'def
    S1a S1b Int_iff unfolding collinear_def distinct7_def by metis+
  have "\<not> (join A D) \<subseteq> ?S" and "\<not> (join D C) \<subseteq> ?S"
    using assms Spts ddef DnS S1a [of A D] S1a [of D C] by auto
  then have "\<forall>G. G \<in> (join A D) \<and> G \<in> ?S \<longrightarrow> G = A" 
    and "\<forall>G. G \<in> (join D C) \<and> G \<in> ?S \<longrightarrow> G = C" using assms ddef DnS 
    S1a S2a S3 [of "join A D" ?S] S3 [of "join D C" ?S] by metis+
  then have P'R'nS: "P' \<notin> ?S \<and> R' \<notin> ?S" using p'def r'def P'nAA' R'nCC' by auto
  have PRP'R'dist: "P \<noteq> R \<and> P' \<noteq> R'"
  proof (safe)
    assume "P = R"
    then have "(join A B) = (join B C) \<or> (join A' B') = (join B' C')"
      using assms S0a S1a S1b [of B'] Int_iff distinct7_def by metis
    then show False using assms joins_eq_collinear distinct7_def by metis
  next
    assume "P' = R'"
    then have "(join A D) = (join D C) \<or> (join A' D') = (join D' C')"
      using assms ddef d'def newdist p'def r'def S0a S1a S1b [of D']
      unfolding distinct7_def by metis
    then show False using assms adca'd'c'ncoll d'def ddef newdist 
      joins_eq_collinear distinct7_def by metis
  qed
  have "collinear X P P'" and "collinear X R R'" using xdef PXP'RXR'
    XneqP' XneqR' P'QR'coll S0a S1a unfolding collinear_def by metis+
  then show ?thesis using assms xdef ddef DnS PQRinS p'def r'def P'QR'coll 
    P'R'nS PRP'R'dist projected_points_collinear [of ?S X P Q R P' R'] 
    S0a S0b S1a S2a by metis
qed

end

section \<open>Configurations\<close>

locale configuration = projective_plane_data Points Lines incid for
Points Lines incid +
  assumes C1: "(U \<in> Points  \<and> V \<in> Points  \<and> k \<in> Lines  \<and> n \<in> Lines 
    \<and> incid  U k \<and> incid  V k \<and> incid  U n \<and> incid  V n \<and> U \<noteq> V) \<Longrightarrow> k = n"
begin

lemma C1alt: 
  fixes P Q k n
  assumes "(P \<in> Points  \<and> Q \<in> Points \<and> k \<in> Lines  \<and> n \<in> Lines 
    \<and> incid  P k \<and> incid  Q k \<and> incid  P n \<and> incid  Q n \<and> k \<noteq> n)"
  shows "P = Q" using assms C1 by auto

end

lemma affine_is_config: 
  fixes incid:: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes Points:: "'p set"
  fixes Lines:: "'l set"
  fixes join::"'p \<Rightarrow> 'p \<Rightarrow> 'l"
  fixes find_parallel::"'l \<Rightarrow> 'p \<Rightarrow> 'l"
  assumes "affine_plane Points Lines incid join find_parallel"
  shows "configuration Points Lines incid"
  using assms affine_plane.prop1P2 configuration_def by (smt (verit, del_insts))

section \<open>The Desargues configuration and the empty configuration\<close>
datatype pointD = Hd | Ad | Bd | Cd | Dd | Ed | Fd | Pd | Qd | Rd
definition PointsD::"pointD set" where "PointsD = (UNIV::(pointD set))"
definition LinesD::"pointD set set" where "LinesD = 
  {{Ad,Bd, Pd}, {Bd, Cd,Rd}, {Cd, Ad, Qd}, {Dd, Ed, Pd}, {Ed, Fd, Rd}, {Fd, Dd, Qd},
    {Hd, Ad, Dd}, {Hd, Bd, Ed}, {Hd, Cd, Fd}, {Pd, Qd, Rd}}"
definition incidD:: "pointD \<Rightarrow> pointD set \<Rightarrow> bool" where "incidD X k = (X \<in> k)"

lemma lines_distinctD: 
  shows [simp]:
    \<open>{Hd, Cd, Fd} \<noteq> {Hd, Bd, Ed}\<close>
    \<open>{Hd, Cd, Fd} \<noteq> {Hd, Ad, Dd}\<close>
    \<open>{Hd, Bd, Ed} \<noteq> {Hd, Ad, Dd}\<close>
    \<open>{Hd, Ad, Dd} \<noteq> {Cd, Ad, Qd}\<close>
    \<open>{Hd, Ad, Dd} \<noteq> {Ad, Bd, Pd}\<close>
    \<open>{Cd, Ad, Qd} \<noteq> {Ad, Bd, Pd}\<close>
    \<open>{Hd, Bd, Ed} \<noteq> {Bd, Cd, Rd}\<close>
    \<open>{Hd, Bd, Ed} \<noteq> {Ad, Bd, Pd}\<close>
    \<open>{Bd, Cd, Rd} \<noteq> {Ad, Bd, Pd}\<close>
    \<open>{Hd, Cd, Fd} \<noteq> {Cd, Ad, Qd}\<close>
    \<open>{Hd, Cd, Fd} \<noteq> {Bd, Cd, Rd}\<close>
    \<open>{Cd, Ad, Qd} \<noteq> {Bd, Cd, Rd}\<close>
    \<open>{Hd, Ad, Dd} \<noteq> {Fd, Dd, Qd}\<close>
    \<open>{Hd, Ad, Dd} \<noteq> {Dd, Ed, Pd}\<close>
    \<open>{Fd, Dd, Qd} \<noteq> {Dd, Ed, Pd}\<close>
    \<open>{Hd, Bd, Ed} \<noteq> {Ed, Fd, Rd}\<close>
    \<open>{Hd, Bd, Ed} \<noteq> {Dd, Ed, Pd}\<close>
    \<open>{Ed, Fd, Rd} \<noteq> {Dd, Ed, Pd}\<close>
    \<open>{Hd, Cd, Fd} \<noteq> {Fd, Dd, Qd}\<close>
    \<open>{Hd, Cd, Fd} \<noteq> {Ed, Fd, Rd}\<close>
    \<open>{Fd, Dd, Qd} \<noteq> {Ed, Fd, Rd}\<close>
    \<open>{Pd, Qd, Rd} \<noteq> {Dd, Ed, Pd}\<close>
    \<open>{Pd, Qd, Rd} \<noteq> {Ad, Bd, Pd}\<close>
    \<open>{Dd, Ed, Pd} \<noteq> {Ad, Bd, Pd}\<close>
    \<open>{Pd, Qd, Rd} \<noteq> {Fd, Dd, Qd}\<close>
    \<open>{Pd, Qd, Rd} \<noteq> {Cd, Ad, Qd}\<close>
    \<open>{Fd, Dd, Qd} \<noteq> {Cd, Ad, Qd}\<close>
    \<open>{Pd, Qd, Rd} \<noteq> {Ed, Fd, Rd}\<close>
    \<open>{Pd, Qd, Rd} \<noteq> {Bd, Cd, Rd}\<close>
    \<open>{Ed, Fd, Rd} \<noteq> {Bd, Cd, Rd}\<close>
    by auto

lemma desargues_three_lines: (* every pt lies on 3 lines *)
  fixes X::"pointD"
  assumes "X \<in> PointsD"
  shows "\<exists>l m n. distinct3 l m n 
    \<and> incidD X l \<and> incidD X m \<and> incidD X n 
    \<and> l \<in> LinesD \<and> m \<in> LinesD \<and> n \<in> LinesD" 
  using lines_distinctD unfolding incidD_def LinesD_def distinct3_def
  sorry

  (*by (cases X)

    (simp only: insert_iff empty_iff conj_disj_distribL conj_disj_distribR
     ex_disj_distrib simp_thms(39); simp; fail)+
*)
lemma desargues_three_points: (* every line contains 3 points *)
  assumes "k \<in> LinesD"
  shows "\<forall> k \<in> LinesD . card k = 3"
proof -
  consider "k = {Ad,Bd, Pd}" | "k= {Bd, Cd,Rd}" | "k= {Cd, Ad, Qd}" 
  | "k= {Dd, Ed, Pd}" | "k= {Ed, Fd, Rd}" | "k= {Fd, Dd, Qd}" | "k={Hd, Ad, Dd}"
  | "k= {Hd, Bd, Ed}" | "k= {Hd, Cd, Fd}" | "k= {Pd, Qd, Rd}" 
  using assms LinesD_def insertE singleton_iff by metis
  then show ?thesis 
    using pointD.distinct LinesD_def card_3_iff insertE singletonD by (smt (z3))+
qed

lemma desargues_is_config:
  shows "configuration PointsD LinesD incidD"
  using LinesD_def emptyE incidD_def insertE pointD.simps 
  unfolding configuration_def by (smt (verit))

lemma no_lines_is_config: 
  fixes Points::"'a set"
  shows "configuration Points {} (\<lambda>x L . False)"
  unfolding configuration_def by simp

section \<open>The free projective plane on a configuration -- introduction\<close>

text \<open>Let $\pi_0$ be a configuration. We will now define the free projective plane generated by $\pi_0$.

Let $\pi_1$ be the new configuration defined as follows: The points of $\pi_1$ are the points of $\pi_0$. The lines of $\pi_1$ 
are the lines of $\pi_0$, plus, for each pair of points $P_1, P_2 \in \pi_0$ not on a line, a new line $\{P_1, P_2\}$. Then $\pi_1$
 has the property:

a) Every two distinct points lie on a line.

Construct $\pi_2$ from $\pi_1$ as follows. The points of $\pi_2$ are the points of $\pi_1$, plus, for each pair of lines l1,l2 of $\pi_1$
 which do not meet, a new point $l_1 \cdot l_2$. The lines of $\pi_2$ are the lines of $\pi_1$, extended by their 
new points, e.g. the point $l_1 \cdot l_2$ lies on the extensions of the lines $l_1, l_2$. Then \<pi>2 has the property

b) Every pair of distinct lines intersects in a point, but $\pi_2$ no longer has the property a).

We proceed in the same fashion. For $n$ even, we construct $\<pi>_{n+1}$ by adding
new lines, and for $n$ odd, we construct $\<pi>_{n+1}$ by adding new points.
Let $\Pi = \bigcup_{n=0}^{\infty}  \pi_n$, and define a line in $\Pi$ to be a subset of $L \subset \Pi$ such that
for all large enough $n$,  $L \cap ]pi_n$ is a line of $\pi_n$.\<close>

text \<open>Our version of this is slightly modified to suit Isabelle's constraints. Making infinite unions of sets is possible,
but not pretty. And extending the set of points on a line (creating the "extension") is particularly messy. Instead, we modify the
`incid' function to say that more points meet a particular line. The definition of 'incid P k" for $k$ a line in $\Pi$ now simplifies:
first, $k$ can be any line that's been constructed so far (e.g., `join P Q', where $P$ and $Q$ are previously-created points), and 
`incid P k' becomes the statement that there is some natural number $n$ such that `fppincid ... P k n'. \<close>

text\<open>We define mutually-recursive datatypes for points and lines. Basepoints and Baselines are those that occur at level 0. 
Every point/line is given an natural-number component to indicate the level at which it was created. If a crossing has level $k$,
then the two lines that created it must both have level less than $k$; similarly, if a join has level $k$, then the two points 
that produced it must have level less than $k$. 

Furthermore, for $n > 2$, there's something even more specific: if a crossing has level $k$ (which must be even!), 
then at least one of the two lines that created it must have level $k-1$. Why? If not, they'd both have
level no more than $k-3$ (the previous odd number), and this crossing would have been created at level $k-2$.

Note that although levels for points are always even, levels for lines are always odd \emph{except} 
that a line may have level 0.\<close>

section \<open>Free projective plane datatypes and function definitions\<close>

datatype ('a, 'b) fpoint =
  Base_point 'a | Crossing "(('a, 'b) fline) uprod" nat 
and ('a, 'b) fline = 
  Base_line 'b | Join "(('a, 'b) fpoint) uprod" nat

(* example of a function on a uprod *)
fun f_example::"int uprod \<Rightarrow> bool" where
"f_example(x) = (if (\<exists> a b . (x = Upair a b) \<and> (a = b)) then True else False)"

(* go level by level *)
fun p_level::" ('a, 'b)fpoint \<Rightarrow> nat" where
"p_level (Base_point _) = 0" |
"p_level (Crossing _ n) = n"

fun l_level::" ('a, 'b)fline \<Rightarrow> nat" where
"l_level (Base_line _) = 0" |
"l_level (Join _ n) = n"

text \<open>Notice that in the following definition, a BasePoint or BaseLine always (implicitly) has level 0. 
Also, the definition depends on the set of base points,
the set of base lines, and a 'incid' function for that configuration. \<close>

context configuration
begin
(* Does this point lie on this line in \Pi? *)
fun fppincid::  "('a, 'b) fpoint \<Rightarrow> ('a, 'b) fline \<Rightarrow> bool" where
(* if lines meet in pi0, they meet in Pi: *)
  "fppincid (Base_point P) (Base_line m) = (incid  P m)"  
(* if a basepoint incid a join-line, it must be one of the two ends of the join *) 
| "fppincid (Base_point P) (Join x n2) = (\<exists> A1 B1 . (x = Upair A1 B1) 
 \<and> (A1 = (Base_point P) \<or> (B1 = (Base_point P))))"
(* if a baseline incid a crossing, it must be one of the two crossing lines *)
| "fppincid  (Crossing u n1) (Base_line m) = (\<exists> l k . (u = Upair l k) 
 \<and> (l = (Base_line m)   \<or> (k =  (Base_line m))))" 

(* If a crossing lies on a join...then it must be one of the two points that formed the join *)
(* this is not correct! for that join might later be extended by further crossings with other lines *)
(*"fppincid CPoints CLines (incid) (Crossing u n1)  (Join x n2) = (\<exists> A1 B1 . (x = Upair A1 B1) 
 \<and> (A1 = (Crossing u n1)   \<or> (B1 = (Crossing u n1))))" *)
| "fppincid  (Crossing u n1)  (Join x n2) = (
     ((n1 < n2) \<and> 
      (\<exists> A1 B1 . x = Upair A1 B1 \<and> (A1 = Crossing u n1 \<or> B1 = Crossing u n1))) 
     \<or> 
     (\<exists> k m . u = Upair k m \<and> k = Join x n2 \<or> m = Join x n2)
   )"   
(*N.B.:  Two clauses above correspond to (1) previous condition, and (2) a crossing being on the extension of some join *)
fun point_set::"nat \<Rightarrow> (('a, 'b) fpoint) set" and
    line_set::" nat \<Rightarrow> (('a, 'b) fline) set" and
    new_points::"nat \<Rightarrow> (('a, 'b) fpoint) set" and
    new_lines::"nat \<Rightarrow> (('a, 'b) fline) set"    
    where
  "point_set  (0 ::nat) = new_points 0" | 
  "line_set  (0 ::nat) = new_lines 0" |
  "point_set  ( Suc n ::nat) = point_set n \<union> new_points (Suc n)" | 
  "line_set  (Suc n ) = line_set n \<union>  new_lines (Suc n)" |
  "new_points 0 = {Base_point Q | Q . Q \<in> Points}" |
  "new_points (Suc 0) = ({}::(('a, 'b) fpoint) set)" |
  "new_points (Suc (Suc 0)) =   
  {Crossing (Upair k l) (Suc (Suc 0)) | k l . 
    ((k \<in> new_lines 0) \<or> (k \<in> new_lines (Suc 0))) \<and> 
    (l \<in> line_set (Suc 0)) \<and> (k \<noteq> l) \<and>
    \<not> (\<exists>Y \<in> point_set (Suc 0) . fppincid Y k \<and> fppincid Y l \<and> (p_level Y \<le> (Suc 0)))}" |
  "new_points (Suc (Suc n::nat)) = 
  (if (odd n) then {} else 
  {Crossing (Upair k l) (Suc (Suc n)) | k l . 
    (k \<in> new_lines (Suc n)) \<and> 
    (l \<in> line_set (Suc n)) \<and> (k \<noteq> l) \<and>
    \<not> (\<exists>Y \<in> point_set (Suc n) . fppincid Y k \<and> fppincid Y l \<and> (p_level Y \<le> (Suc n)))})" |
  "new_lines 0 = {Base_line k| k . k \<in> Lines}"  |
  "new_lines (Suc 0) = {Join (Upair S T) 1 | S T . 
    (S \<in> new_points 0) \<and> 
    (T \<in> point_set 0) \<and> (S \<noteq> T) \<and>
    \<not> (\<exists>k \<in> line_set 0 . fppincid  S k \<and> fppincid T k \<and> (l_level k \<le> 1))}" |
  "new_lines (Suc (Suc n)) = 
  (if (even n) then {} else 
   {Join (Upair S T) (Suc (Suc n)) | S T . 
    (S \<in> new_points (Suc n)) \<and> 
    (T \<in> point_set (Suc n)) \<and>  (S \<noteq> T) \<and> 
    \<not> (\<exists>k \<in> line_set (Suc n) . fppincid  S k \<and> fppincid T k \<and> (l_level k \<le> (Suc n)))})" 

definition Pi_points::"((('a, 'b) fpoint) set)" 
  where "Pi_points  = 
     \<Union> ((new_points)  ` UNIV)"

definition Pi_lines::" ((('a, 'b) fline) set)" 
  where "Pi_lines = 
     \<Union> ((new_lines)  ` UNIV)"

(* Now claim that Pi_points, Pi_lines, fppincid defines a projective plane. *)
(*  (maybe using the projective_plane2 locale, rather than the standard one *)
(* start with many lemmas *)
(* All lines have odd levels or 0
   All points have levels that are even
   If two lines have level \<le>= p, then either they intersect already OR they intersect at level p + 1
   If q incid join A B and level q = level A or level B, then q = A or q = B
*)
(* First,a lemma or two *)
(* Note: lines are added at odd levels; points are added at even levels.

* If n is even and two lines don't intersect at level n, then they don't intersect at level n+1
* either, but do intersect at level n + 2 
*
* If n is odd and two points don't join at level n, then they don't join at level n+1 either, but 
* do join at level n+2. 
*
* in either a Join or a Crossing, the two items in the Upair are distinct.
*) 
section \<open>FPP elementary theorems\<close>

lemma increase_initial_segment: (* append n+1 to the naturals from 0 to n, and you get 0:(n+1) *)
  fixes n::nat
  shows "({i::nat . i \<le> n} \<union> {Suc n}) = ({i::nat . i \<le> (Suc n)} )"
  by fastforce

lemma point_level: (* a point in new_points n has level n *)
  assumes "P \<in> new_points n"
  shows "p_level P = n"
proof -
  consider (zero) "n = 0" | (one) "n = Suc 0" | (two) "n = Suc (Suc 0)" 
  | (many) "\<exists>p .  n = Suc (Suc (Suc p))" using old.nat.exhaust by metis
  then show ?thesis
  proof cases
    case many
    obtain p where nd: "n = Suc (Suc (Suc p))" using many by auto
    obtain k l where p_def:"P = Crossing (Upair k l) (Suc (Suc (Suc p))) \<and>
         k \<in> new_lines (Suc (Suc p)) \<and>
         l \<in> line_set (Suc (Suc p)) \<and> k \<noteq> l 
          \<and> \<not> (\<exists>Y\<in>point_set (Suc (Suc p)). fppincid Y k \<and> fppincid Y l 
          \<and> p_level Y \<le> Suc (Suc p))" 
    using assms nd new_points.simps empty_iff mem_Collect_eq by (smt (verit))
    then have "p_level P = Suc (Suc (Suc p))" using p_level.simps by simp
    then show ?thesis using nd by simp
  next
  case zero
    then show ?thesis using assms by auto
  next
    case one
    then show ?thesis using assms by auto
  next
    case two
    then show ?thesis using assms by auto
  qed
qed

lemma point_level2: (* if a Point's level is k, it's in new_points k *)
  fixes Pn
  assumes a1: "P \<in> Pi_points"
  assumes a2: "k = p_level P"
  shows "P \<in> new_points k"
proof -
  obtain n where u1: "P \<in> new_points  n" 
    using a1 Pi_points_def new_points.simps by auto
  have u2: "k = n" using u1 a2 p_level.simps point_level by auto
  show ?thesis using a2 u1 u2 by auto
qed

lemma points_even: (* if a Point's level is k, then k is even *)
  fixes P 
  assumes a1: "P \<in> Pi_points "
  assumes a2: "n = p_level P"
  shows "even n"
proof -
  have u0: "P \<in> new_points  n" using a1 a2 point_level2 by auto
  show ?thesis
  proof (cases n)
    case 0
    then show ?thesis by auto
  next
    case (Suc k)
    then show ?thesis 
    proof (cases "even k")
      case False
      then show ?thesis by (simp add: Suc)
    next
      case True
      then have "odd n" by (simp add: Suc)
      then show ?thesis using Suc u0 empty_iff even_Suc_Suc_iff even_zero
        new_points.elims by (metis (full_types))
    qed
  qed
qed

lemma crossing_lines_distinct: (* If P in Pi_points is the crossing of m and k, then m and k are unequal *)
  fixes P  
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  assumes a1: "P \<in> Pi_points "
  assumes a2: "P = Crossing (Upair m s) n"
  shows "m \<noteq> s"
proof (cases P)
  case (Base_point x11)
  have False using a2 Base_point by auto
  then show ?thesis by blast
next
  case (Crossing x21 n)
  obtain v where vv: "P \<in> new_points  v" 
    using a1 Pi_points_def new_points.simps by auto
  consider (zero) "v = 0" | (one) "v = Suc 0" | (two) "v = Suc (Suc 0)" 
  | (many) "\<exists>p. v = Suc (Suc (Suc p))" using old.nat.exhaust by metis
  then show ?thesis
  proof cases
    case zero
    then show ?thesis using Crossing vv by auto
  next
    case one
    then show ?thesis using Crossing vv by auto
  next
    case two
    have t1: "new_points  v = {Crossing (Upair k l) v | k l . 
    ((k \<in> new_lines  0) \<or> (k \<in> new_lines  (Suc 0))) \<and> 
    (l \<in> line_set  (Suc 0)) \<and> (k \<noteq> l) \<and>
    \<not> (\<exists>Y \<in> point_set  (Suc 0) . fppincid  Y k \<and> fppincid  Y l \<and> (p_level Y \<le> (Suc 0)))}"
      using new_points.simps vv two by auto
    obtain k l where kl: "P = Crossing (Upair k l) v \<and> 
    ((k \<in> new_lines  0) \<or> (k \<in> new_lines  (Suc 0))) \<and> 
    (l \<in> line_set  (Suc 0)) \<and> (k \<noteq> l) \<and>
    \<not> (\<exists>Y \<in> point_set  (Suc 0) . fppincid  Y k \<and> fppincid  Y l \<and> (p_level Y \<le> (Suc 0)))" 
      using t1 vv by fastforce
    have "k \<noteq> l" using kl by blast
    then show ?thesis using Crossing a1 a2 t1 fpoint.inject(2) kl proper_uprod_simps by metis
  next
    case many 
    obtain p where pdef: "n = Suc (Suc (Suc p))" 
      using many by (metis Crossing p_level.simps(2) point_level vv) 
    have KL: "new_points  (Suc (Suc (Suc p))) =
    (if odd (Suc p) then {}
     else {Crossing (Upair k l) (Suc (Suc (Suc p))) |k l.
           k \<in> new_lines  (Suc (Suc p)) \<and>
           l \<in> line_set  (Suc (Suc p)) \<and> k \<noteq> l 
           \<and> \<not> (\<exists>Y\<in>point_set  (Suc (Suc p)). fppincid  Y k \<and> fppincid  Y l \<and> p_level Y \<le> Suc (Suc p))})"
      using new_points.simps by auto
    obtain k l where kl: "P = Crossing (Upair k l) (Suc (Suc (Suc p))) \<and>
           k \<in> new_lines  (Suc (Suc p)) \<and>
           l \<in> line_set  (Suc (Suc p)) \<and> k \<noteq> l 
           \<and> \<not> (\<exists>Y\<in>point_set  (Suc (Suc p)). fppincid  Y k \<and> fppincid  Y l \<and> p_level Y \<le> Suc (Suc p))" using vv KL
      by (smt (verit, ccfv_SIG) Crossing pdef a1 empty_iff mem_Collect_eq p_level.simps(2) point_level2)
    have "k \<noteq> l" using kl by blast
    then show ?thesis using Crossing a1  by (metis a2 fpoint.inject(2) kl proper_uprod_simps)
  qed
qed

lemma point_containment: (* new_points  n is in Pi_points  *)
  fixes P 
  assumes "\<exists> n::nat. P \<in> new_points  n"
  shows "P \<in> Pi_points "
proof -
  obtain n where 1: "P \<in> new_points  n" using assms by blast
  have 2: "new_points  n \<subseteq> Pi_points " using Pi_points_def by blast
  show ?thesis using 1 2 by auto
qed

lemma pi_points_contents: (* anything in new_points  n is in Pi_points  *)
  fixes  n
  shows "new_points  n \<subseteq> Pi_points "
  using Pi_points_def by auto

lemma point_set_contents: (* point_set  n is the union of new_points  i for i = 0 .. n *)
  fixes  n
  shows "point_set  n =   \<Union> ((new_points )  ` {i::nat . i \<le> n})"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc k)
  note this
  have u1: "point_set  k =  \<Union> ((new_points )  ` {i::nat . i \<le> k})" 
    using Suc by blast  
  have u2: "point_set  (Suc k ) = point_set  k \<union>  new_points  (Suc k)" 
    using point_set.simps by blast
  have u3: "point_set  (Suc k ) 
    = (\<Union> ((new_points )  ` {i::nat . i \<le> k})) \<union>  new_points  (Suc k)" 
    using u1 u2  by blast
  have u4: "point_set  (Suc k ) 
    = (\<Union> ((new_points )  ` ({i::nat . i \<le> k} \<union> {Suc k})))" 
    using u3 increase_initial_segment by blast
  have u5: "point_set  (Suc k ) 
    = (\<Union> ((new_points )  ` ({i::nat . i \<le> (Suc k)} )))" 
    using u4 increase_initial_segment by blast   
  then show ?case using u5 by auto 
qed

lemma pi_points_contents2: (* point_set  n is a subset of Pi_points  *)
  fixes  n
  shows "point_set  n \<subseteq> Pi_points "
  using Pi_points_def Sup_subset_mono image_mono point_set_contents top_greatest by metis

lemma line_level: (* if a line is in new_lines  n, its level is n *)
  fixes k  
  fixes n::nat
  assumes a1: "k \<in> new_lines  n"
  assumes a2: "s = l_level k"
  shows "s = n"
proof -
  consider (zero) "n = 0" | (one) "n = Suc 0" | (many) "\<exists>p .  n = Suc (Suc p)" by (metis old.nat.exhaust)
  then show ?thesis
  proof cases
    case zero
    then show ?thesis using a1 a2 by auto
  next
    case one
    then show ?thesis using a1 a2 by auto
  next
    case many
    then show ?thesis    
      by (smt (verit, ccfv_threshold) a1 a2 empty_iff l_level.simps(2) mem_Collect_eq new_lines.simps(3))
  qed
qed

lemma line_level2: (* if a line's level is k, it's in new_lines  k *)
  fixes k  n
  assumes a1: "k \<in> Pi_lines "
  assumes a2: "s = l_level k"
  shows  "k \<in> new_lines  s"
proof -
  obtain n where u1:"k \<in> new_lines  n" using a1 Pi_lines_def new_lines.simps by auto
  have u2: "s = n" using u1 a2 l_level.simps line_level by auto
  show ?thesis using u1 u2 by auto
qed

lemma lines_odd_or_zero: (* every line's level is either odd or zero *)
  fixes k 
  assumes a1: "k \<in> Pi_lines "
  assumes a2: "n = l_level k"
  shows "n = 0 \<or> odd n"
proof -
  have u0: "k \<in> new_lines  n" using a1 a2 line_level2 by auto
  show ?thesis
  proof (cases n)
    case 0
    then show ?thesis by auto
  next
    case (Suc k)
    then show ?thesis 
    proof (cases "(odd n)")
      case True
      then show ?thesis by blast
    next
      case False
      then show ?thesis using Suc u0
      by (metis empty_iff even_Suc even_zero new_lines.elims)
    qed
  qed
qed

lemma pi_lines_contents: (* new_lines  n is in Pi_lines  *)
  fixes  n
  shows "new_lines  n \<subseteq> Pi_lines "
  using Pi_lines_def by auto

lemma line_set_contents: (* line_set  n is the union of all new_lines  k for k = 0:n *)
  fixes  n
  shows "line_set  n =   \<Union> ((new_lines )  ` {i::nat . i \<le> n})"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note this
  have u1: "line_set  n =  \<Union> ((new_lines )  ` {i::nat . i \<le> n})" using Suc by blast  
  have u2: "line_set  (Suc n ) = line_set  n \<union>  new_lines  (Suc n)" using line_set.simps by blast
  have u3: "line_set  (Suc n ) = (\<Union> ((new_lines )  ` {i::nat . i \<le> n})) \<union>  new_lines  (Suc n)" using u1 u2  by blast
  have u4: "line_set  (Suc n ) = (\<Union> ((new_lines )  ` ({i::nat . i \<le> n} \<union> {Suc n})))" using u3 increase_initial_segment by blast
  have u5: "line_set  (Suc n ) = (\<Union> ((new_lines )  ` ({i::nat . i \<le> (Suc n)} )))" using u4 increase_initial_segment by blast   
  then show ?case using u5 by auto 
qed

lemma pi_lines_contents2: (* and Pi_lines  is the union of all line_set s *)
  fixes  n
  shows "line_set  n \<subseteq> Pi_lines "
  using Pi_lines_def Union_mono line_set_contents subset_image_iff top_greatest by metis

lemma joining_line: (* there's a line between any two distinct points of a free projective plane with the right order of levels *)
  fixes P Q 
  assumes "P \<in> Pi_points " and "Q \<in> Pi_points "
  assumes "p_level P \<le> p_level Q"
  assumes "P \<noteq> Q"
  defines "n \<equiv> p_level Q"
  shows "\<exists>k \<in> Pi_lines . fppincid  P k \<and> fppincid  Q k"
proof -
  consider (zero) "n = 0" | (one) "n = Suc 0" | (many) "\<exists>p .  n = Suc (Suc p)" 
    using old.nat.exhaust by metis
  then show ?thesis
  proof cases
    case zero
    have 1: "p_level P = 0" using assms(3) n_def zero by auto
    obtain A where 2:"P = Base_point A" using "1" assms(1) point_level2 by fastforce
    obtain B where 3:"Q = Base_point B" using assms(2) n_def point_level2 zero by fastforce
    then show ?thesis 
    proof (cases "\<exists> m \<in> line_set  0 . fppincid  P m \<and> fppincid  Q m \<and> (l_level m \<le> 1)")
      case True
      then show ?thesis by (metis in_mono pi_lines_contents2)
    next
      case False
      have "new_lines  1 = {Join (Upair S T) 1 | S T . 
        (S \<in> new_points  0) \<and> 
        (T \<in> point_set  0) \<and> (S \<noteq> T) \<and>
          \<not> (\<exists>k \<in> line_set  0 . fppincid   S k \<and> fppincid  T k \<and> (l_level k \<le> 1))}" 
        using new_lines.cases by simp
      then have "Join (Upair P Q) 1 \<in> new_lines  1"
        by (smt (verit) 1 False assms(1,2,4) mem_Collect_eq n_def point_level2 point_set.simps(1) zero)
      then show ?thesis by (metis 2 3 fppincid.simps(2) in_mono pi_lines_contents)
    qed
  next
    case one (* higher level point has level 1 -- can't happen *)
    have False using  One_nat_def assms(2) bot_nat_def n_def odd_one one points_even by metis
    then show ?thesis by blast
  next
    case many (*higher-level point has degree 2 or greater *)
    obtain q where uu: "n = Suc q" using many by blast
    have u0: "Q \<in> new_points  n" using assms(2) n_def point_level2 by auto
    have u1: "Q \<in> point_set  n" using u0 point_set.simps by (metis UnCI point_set.elims)
    have u2: "P \<in> new_points  (p_level P)" by (simp add: assms(1) point_level2)
    have u3: "P \<in> point_set   (p_level P)" by (metis UnCI point_set.elims u2)
    have u4: "P \<in> point_set   n" 
      by (smt (verit, best) UnCI assms(3) in_mono lift_Suc_mono_le n_def point_set.elims point_set.simps(1,2) subsetI u2)
    have u5: "even n" using assms(2) points_even n_def by blast
    have u6: "new_lines  (Suc n) = new_lines  (Suc (Suc q))" using uu by blast 
    have u7: "new_lines  (Suc n) = 
  (if (even q) then {} else
   {Join (Upair S T) (Suc (Suc q)) | S T . 
    (S \<in> new_points  (Suc q)) \<and> 
    (T \<in> point_set  (Suc q)) \<and> (S \<noteq> T) \<and>
    \<not> (\<exists>k \<in> line_set  (Suc q) . fppincid   S k \<and> fppincid  T k \<and> (l_level k \<le> (Suc q)))})" using u6 by simp
    then have u8: "new_lines  (Suc n) = 
     {Join (Upair S T) (Suc (Suc q)) | S T . 
      (S \<in> new_points  (Suc q)) \<and> 
      (T \<in> point_set  (Suc q)) \<and> (S \<noteq> T) \<and>
      \<not> (\<exists>k \<in> line_set  (Suc q) . fppincid   S k \<and> fppincid  T k \<and> (l_level k \<le> (Suc q)))}" using u5 uu by auto
    let ?C = "\<exists>k \<in> line_set  n . fppincid   P k \<and> fppincid  Q k \<and> (l_level k \<le> n)"
    show "\<exists>k\<in>Pi_lines . fppincid  P k \<and> fppincid  Q k "
    proof (cases ?C)
      case True
      obtain k where u9: "k \<in> line_set  n \<and> fppincid  P k \<and> fppincid  Q k \<and> l_level k \<le> n" using True by blast
      have "k \<in> Pi_lines  " using u9 pi_lines_contents2 by blast
      then show ?thesis using u9 by blast
    next
      case False
      have v1: "Join (Upair P Q) (Suc n) \<in> new_lines  (Suc n)" using u8 False using u0 u4 uu  assms(4) by force
      let ?L = "Join (Upair P Q) (Suc n)"
      have v2:  "?L \<in> Pi_lines " using v1 Pi_lines_def by blast
      have v3:  "fppincid  P ?L \<and> fppincid  Q ?L"
      by (smt (verit, best) fline.distinct(1) fline.inject(2) fppincid.elims(3))
      then show ?thesis using v2 by blast
    qed
  qed
qed

theorem free_planes_join:  (* there's a line between any two distinct points of a free projective plane *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  assumes "card CPoints \<ge> 4"
  fixes P Q
  assumes "P \<in> Pi_points "
  assumes "Q \<in> Pi_points "
  assumes "P \<noteq> Q"
  shows " \<exists>k. k \<in> Pi_lines  \<and> fppincid  P k \<and>  fppincid  Q k"
  using assms joining_line nle_le by metis

lemma line_point_levels: (* points of join P Q, a line at level n, are either P or Q or have level > n *)
 fixes CPoints::"'a set"
  fixes CLines::"'b set"
  assumes "card CPoints \<ge> 4"
  fixes P A1 B1 n
  assumes "P \<in> Pi_points "
  assumes "Join (Upair A1 B1) n \<in> Pi_lines "
  assumes "fppincid  P (Join (Upair A1 B1) n)"
  shows "P = A1 \<or> P = B1 \<or> (p_level P \<ge> n)" 
proof (cases P)
  case (Base_point x1)
  show ?thesis using assms Base_point  by auto
next
  case (Crossing x21 x22)
  then show ?thesis sorry
qed
 
(* A theorem we don't know how to prove, and Hartshorne finesses it! *)
theorem free_planes_unique_join: (* two distinct points are joined by a UNIQUE line ... still unproved *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes  U
  assumes "U \<subseteq> CPoints"
  assumes "card U \<ge> 4"
  fixes P Q
  assumes "P \<in> Pi_points "
  assumes "Q \<in> Pi_points "
  assumes "P \<noteq> Q"
  shows " \<exists>!k. k \<in> Pi_lines  \<and> fppincid  P k \<and> fppincid  Q k"
  sorry
(* gist of possible proof: 
(i) if they're joined in the base, it's easy
(ii) if they're both base points, they're joined at level 1. All NEW points on that line have level \<ge> 2. 
(iii) If ONE is a base-point, then the level of the line is some odd number n, one of constructor poijnts in is
the base, the other's at level n-1. All OTHER points on this line are of level > n
(iv) If NEITHER is a base-point, then one is at level n-1, and the other is at or below level n-1, and 
all other points on this line are at level > n. [actually,this subsumes case iii]

Now look at another line containing P and Q. Either P and.or Q is a constructor point, or both are
'new' points with levels higher than the line level. That means ... what DOES it mean? 
*)

lemma line_containment: (* anything in new_lines  n is in Pi_lines  *)
  fixes k 
  assumes "\<exists> n::nat. k \<in> new_lines  n"
  shows "k \<in> Pi_lines "
proof -
  obtain n where 1: "k \<in> new_lines  n" using assms by blast
  have 2: "new_lines  n \<subseteq> Pi_lines " using Pi_lines_def by blast
  show ?thesis using 1 2 by auto
qed

lemma crossing_point: (* any two distinct lines in Pi_lines meet at a point in Pi_points *)
  fixes k m 
  assumes "k \<in> Pi_lines " and "m \<in> Pi_lines "
  assumes "l_level k \<le> l_level m"
  assumes "k \<noteq> m"
  defines "n \<equiv> l_level m"
  shows "\<exists> P \<in> Pi_points  . fppincid  P k \<and> fppincid  P m"
proof -
  consider (zero) "n = 0" | (one) "n = Suc 0" | (many) "\<exists>p .  n = Suc (Suc p)" 
    using old.nat.exhaust by metis
  then show ?thesis
  proof cases
    case zero
    have 1: "l_level k = 0" using assms(3) n_def zero by auto
    obtain a where 2:"k = Base_line a" using "1" assms(1) line_level2 by fastforce
    obtain b where 3:"m = Base_line b" using assms(2) n_def line_level2 zero by fastforce
    then show ?thesis 
    proof (cases "\<exists> P \<in> point_set  0 . fppincid  P k \<and> fppincid  P m \<and> (p_level P \<le> 1)")
      case True
      then show ?thesis  using pi_points_contents2 by blast
    next
      case False
      have p0: "new_points  1 =  {}"  using new_points.cases by simp
      have p1: "new_points  2 = {Crossing (Upair k l) (Suc (Suc 0)) | k l . 
    ((k \<in> new_lines  0) \<or> (k \<in> new_lines  (Suc 0))) \<and> 
    (l \<in> line_set  (Suc 0)) \<and> (k \<noteq> l) \<and>
    \<not> (\<exists>Y \<in> point_set  (Suc 0) . fppincid  Y k \<and> fppincid  Y l \<and> (p_level Y \<le> (Suc 0)))}"  
      by (metis new_points.simps(3) numeral_2_eq_2)
      have "Crossing (Upair k m) 2 \<in> new_points  2" using p1 False
        by (smt (verit, del_insts) 1 One_nat_def UnCI assms(1,2,4) diff_Suc_1 line_level2 
          line_set.elims mem_Collect_eq n_def numeral_2_eq_2 p0 point_set.simps(2)
          sup_bot.right_neutral zero)
      then show ?thesis by (metis 2 3 fppincid.simps(3) point_containment)
    qed
  next
    case one (* higher level line has level 1 *)
    show ?thesis
    proof (cases "\<exists> P \<in> point_set  0 . fppincid  P k \<and> fppincid  P m \<and> (p_level P \<le> 1)")
      case True
      then show ?thesis  using pi_points_contents2 by blast
    next
      case False
      have q0: "new_points  1 = {}" by simp
      have q2: "point_set  1 = point_set  0" by auto
      have q3: "\<not> (\<exists> P \<in> point_set  1 .  fppincid  P k \<and> fppincid  P m \<and> (p_level P \<le> 1))" using False q2 by blast
      have q4: "new_points  2  = {Crossing (Upair k l) (Suc (Suc 0)) | k l . 
        ((k \<in> new_lines  0) \<or> (k \<in> new_lines  (Suc 0))) \<and> 
        (l \<in> line_set  (Suc 0)) \<and> (k \<noteq> l) \<and> 
        \<not> (\<exists>Y \<in> point_set  (Suc 0) . fppincid  Y k \<and> fppincid  Y l \<and> (p_level Y \<le> (Suc 0)))}"   
        by (metis new_points.simps(3) numeral_2_eq_2)
      have q5: "Crossing (Upair k m) 2 \<in> new_points  2" 
      by (smt (verit) One_nat_def UnCI assms(1,2,3,4) diff_is_0_eq line_level2 line_set.simps(2) lines_odd_or_zero mem_Collect_eq n_def new_points.simps(3) numeral_2_eq_2
          odd_Suc_minus_one one q3)
      then show ?thesis
         by (metis configuration.fppincid.simps(3) configuration_axioms fppincid.simps(4) l_level.elims point_containment)
    qed
  next
    case many (*higher-level line has level 2 or greater *)
    obtain q where uu: "n = Suc q" using many by blast
    have u0: "m \<in> new_lines  n" by (simp add: assms(2) line_level2 n_def)
    have u1: "m \<in> line_set  n" using u0 line_set.simps by (metis UnCI point_set.elims)
    have u2: "k \<in> new_lines  (l_level k)" by (simp add: assms(1) line_level2)
    have u3: "k \<in> line_set   (l_level k)" by (metis UnCI line_set.elims u2)
    have u4: "k \<in> line_set   n" using assms(3) line_set_contents n_def u2 by fastforce 
    have u5: "odd n" using assms(2) points_even n_def many u0 by fastforce
    have u6: "new_points  (Suc n) = new_points  (Suc (Suc q))" using uu by blast 
    then have u7: "new_points  (Suc n) = (if (odd q) then {} else 
      {Crossing (Upair k l) (Suc (Suc q)) | k l . 
       (k \<in> new_lines  (Suc q)) \<and> 
       (l \<in> line_set  (Suc q)) \<and> (k \<noteq> l) \<and>
       \<not> (\<exists>Y \<in> point_set  (Suc q) . fppincid  Y k \<and> fppincid  Y l \<and> (p_level Y \<le> (Suc q)))})"
    using many uu by force
    then have u8: "new_points  (Suc n) = 
     {Crossing (Upair k l) (Suc (Suc q)) | k l . 
       (k \<in> new_lines  (Suc q)) \<and> 
       (l \<in> line_set  (Suc q)) \<and> (k \<noteq> l) \<and>
       \<not> (\<exists>Y \<in> point_set  (Suc q) . fppincid  Y k \<and> fppincid  Y l \<and> (p_level Y \<le> (Suc q)))}" using u5 uu by auto
    let ?C = "\<exists>Y \<in> point_set  n . fppincid  Y k \<and> fppincid  Y m \<and> (p_level Y \<le> n)"
    show "\<exists>P \<in> Pi_points . fppincid  P k \<and> fppincid  P m"
    proof (cases ?C)
      case True
      obtain P where u9: "P \<in> point_set n \<and> fppincid P k \<and> fppincid P m \<and> p_level P \<le> n" using True by blast
      have "P \<in> Pi_points" using u9 pi_points_contents2 by blast
      then show ?thesis using u9 by blast
    next
      case False
      have v1: "Crossing (Upair k m) (Suc n) \<in> new_points (Suc n)" 
        using u8 False u0 u4 uu assms(4) by force
      let ?P = "Crossing (Upair k m) (Suc n)"
      have v2:  "?P \<in> Pi_points" using v1 Pi_points_def by blast
      have v3:  "fppincid ?P k \<and> fppincid ?P m"
      by (smt (verit, best) fpoint.distinct(1) fpoint.inject(2) fppincid.elims)
      then show ?thesis using v2 by blast
    qed
  qed
qed

(* all crossings in CPoints have levels > 0 *)
theorem crossing_level: (* of P is a crossing of level s in  Pi_points, then s > 0 *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  assumes "P \<in> Pi_points"
  assumes "P = Crossing (Upair m k) s"
  shows "s > 0"
proof -
  obtain n where  oh: "P \<in> new_points n" using Pi_points_def assms by blast
  show ?thesis
  proof (cases)
    assume "n > 0"
    then show ?thesis using oh  using assms point_level by fastforce
  next
    assume ah: "\<not> n > 0"
    have "n = 0" using ah by simp
    then have "new_points n =  {Base_point Q  | Q . Q \<in> Points}" using new_lines.cases by simp
    then have a: False using assms oh by blast
    show ?thesis using a FalseE [of ?thesis] by blast
  qed
qed
                                                                     
theorem base_in_join: (* if a Join line contains a basepoint, it's one of the two generators of the join *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  assumes "k \<in> Pi_lines"
  assumes "P = Base_point A"
  assumes "fppincid P k"
  assumes "k = Join (Upair J H) s"
  shows "P = J \<or> P = H"
proof -
  obtain n where "k \<in> new_lines n" using Pi_lines_def assms by blast
  have 1: "n \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (n \<noteq> 0)"
    then have "n = 0" by blast
    then have "new_lines n =  {Base_line s | s . s \<in> Lines}" using new_lines.simps by blast
    then have "k \<notin> new_lines n" using assms by blast
    thus "False" using assms \<open>k \<in> new_lines n\<close> by blast
  qed
  obtain u where "n = Suc u" using 1 by (metis nat.collapse) 
  (* OK, so now k is a line at level n > 0; what's incident on that?  *)
  have 1: "(\<exists> A1 B1 . (Upair J H = Upair A1 B1)
 \<and> (A1 = (Base_point A) \<or> (B1 = (Base_point A))))" using assms fppincid.simps by force
  then have "(\<exists> A1 B1 . (Upair J H = Upair A1 B1)
 \<and> (A1 = P \<or> (B1 = P)))" using assms by force
  then show ?thesis by force
qed

theorem join_level: (* a join with level s has one of its two component points at level s-1 *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes P Q
  shows "Join (Upair P Q) s \<in> Pi_lines \<Longrightarrow> p_level P = s-1 \<or> p_level Q = s-1"
proof - 
  let ?k = "Join (Upair P Q) s"
  assume ah: "?k \<in> Pi_lines"
  have 0: "?k \<in> new_lines s" using ah line_level2 by fastforce
  have 1: "s > 0"  using 0  gr_zeroI by fastforce
  obtain n where 2: "s = Suc n" using 1  using gr0_conv_Suc by blast
  show ?thesis
  proof (cases n)
    case 0
    have "new_lines s =  {Join (Upair S T) 1 | S T . 
    (S \<in> new_points 0) \<and> 
    (T \<in> point_set 0) \<and> (S \<noteq> T) \<and>
    \<not> (\<exists>k \<in> line_set 0 . fppincid S k \<and> fppincid T k \<and> (l_level k \<le> 1))}" 
    using "0" "2" by auto
    then show ?thesis 
    by (smt (z3) One_nat_def Upair_inject ah diff_Suc_1 fline.inject(2) l_level.simps(2) line_level2 mem_Collect_eq point_level)
  next
    case (Suc p)
(* new_lines (Suc (Suc n)) = *)
    have nld: "new_lines n =  (if (even n) then {} else 
      {Join (Upair S T) (Suc (Suc n)) | S T . 
      (S \<in> new_points (Suc n)) \<and> 
      (T \<in> point_set (Suc n)) \<and>  (S \<noteq> T) \<and>
      \<not> (\<exists>k \<in> line_set (Suc n) . fppincid S k \<and> fppincid T k \<and> (l_level k \<le> (Suc n)))})"
      by (metis "2" One_nat_def Suc ah even_Suc l_level.simps(2) lines_odd_or_zero nat.distinct(1) new_lines.elims odd_one)
    then show ?thesis 
    proof (cases "odd n")
      case True
      have s0: "new_lines s = {}" using nld True  by (simp add: "2" Suc)
      then have False using 0 by blast
      then show ?thesis by blast
    next
      case False
      have r0: "even n" using False by blast
      then have nld2: "new_lines (Suc (Suc p)) = 
       (if (even p) then {} else 
       {Join (Upair S T) (Suc (Suc p)) | S T . 
       (S \<in> new_points (Suc p)) \<and> 
       (T \<in> point_set (Suc p)) \<and>  (S \<noteq> T) \<and>
       \<not> (\<exists>k \<in> line_set (Suc p) . fppincid S k \<and> fppincid T k \<and> (l_level k \<le> (Suc p)))})" by simp
      then have nld3: "new_lines (Suc (Suc p)) = 
       {Join (Upair S T) (Suc (Suc p)) | S T . 
       (S \<in> new_points (Suc p)) \<and> 
       (T \<in> point_set (Suc p)) \<and>  (S \<noteq> T) \<and>
       \<not> (\<exists>k \<in> line_set (Suc p) . fppincid S k \<and> fppincid T k \<and> (l_level k \<le> (Suc p)))}" using r0 Suc by auto
      then have nld4: "new_lines (Suc n) = 
       {Join (Upair S T) (Suc n) | S T . 
       (S \<in> new_points n) \<and> 
       (T \<in> point_set n) \<and>  (S \<noteq> T) \<and>
       \<not> (\<exists>k \<in> line_set n . fppincid S k \<and> fppincid T k \<and> (l_level k \<le> n))}" using r0 Suc by auto
      then have nld5: "new_lines s = 
       {Join (Upair S T) (Suc n) | S T . 
       (S \<in> new_points n) \<and> 
       (T \<in> point_set n) \<and>  (S \<noteq> T) \<and>
       \<not> (\<exists>k \<in> line_set n . fppincid S k \<and> fppincid T k \<and> (l_level k \<le> n))}" using "2" by fastforce
      then obtain S T where r1: "?k = Join (Upair S T) (Suc n) \<and> (S \<in> new_points n) \<and> 
       (T \<in> point_set n)" using 0 by auto
      then have "S \<in> new_points n" by blast
      then have "p_level S = n" by (simp add:point_level)
      then have "p_level S = s-1" by(simp add:2)
      then show ?thesis  using r1 by auto
    qed
  qed
qed

theorem base_in_base: (* if a base-point (created from plane_r point A) is in a base-line (from plane_r line m), then A was in m already. *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes  P k m A
  assumes "k = Base_line m"
  assumes "P = Base_point A"
  assumes "fppincid P k"
  shows "incidx A m" 
  sorry

theorem base_pair: (* if a line contains two distinct base points, it's a base line or the join of two base points at level 1 *) 
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes s1 s2 t A B k
  assumes "k \<in> Pi_lines"
  assumes "k \<in> Pi_lines"
  assumes "P = Base_point A"
  assumes "Q = Base_point B"
  assumes "P \<in> Pi_points"
  assumes "Q \<in> Pi_points"
  assumes "A \<noteq> B"
  assumes "fppincid P k"
  assumes "fppincid Q k"
  shows "k \<in> new_lines 0 \<or> k = (Join (Upair P Q) 1)"
proof (cases k)
  case (Base_line x11)
  then show ?thesis  using assms line_level2 by force
next
  case (Join pts s)
  obtain H K where 0: "pts = Upair H K" using uprod_exhaust by auto
  then show ?thesis 
  by (metis Join One_nat_def Suc_leI Upair_inject assms(1,2,3,4,7,8,9) base_in_join diff_is_0_eq fpoint.inject(1) join_level
      l_level.simps(2) line_level2 nle_le not_gr0 p_level.simps(1)) 
qed


theorem free_planes_meet: (* two distinct lines have a point in common in fpp where base plane_r has at least 4 pts *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  assumes "card CPoints \<ge> 4"
  fixes k m
  assumes "k \<in> Pi_lines"
  assumes "m \<in> Pi_lines"
  assumes "k \<noteq> m"
  shows " \<exists>P. P \<in> Pi_points \<and>
               fppincid P k \<and>
               fppincid P m"
  by (metis assms(2,3,4) crossing_point linorder_linear)

theorem non_collinear_persistence:(*if P Q R in the configuration are not collinear, then they are also not collinear in the free projective plane. *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes P Q R
  assumes "card {P, Q, R} = 3"
  assumes "{P, Q, R} \<subseteq> CPoints"
  shows "\<not> (\<exists>k \<in> CLines . incidx P k \<and> incidx Q k \<and> incidx R k) \<Longrightarrow> 
         \<not> (\<exists>m \<in> Pi_lines . fppincid (Base_point P) m \<and> fppincid (Base_point Q) m \<and> fppincid (Base_point R) m)" 
proof (erule contrapos_np)
  assume " \<not> \<not> (\<exists>m\<in>Pi_lines. fppincid (Base_point P) m \<and> fppincid (Base_point Q) m \<and> fppincid (Base_point R) m) "
  then obtain m where  ch: "m\<in>Pi_lines \<and> fppincid (Base_point P) m \<and> fppincid (Base_point Q) m \<and> fppincid (Base_point R) m" by blast
    then show "\<exists>k\<in>CLines. incidx P k \<and> incidx Q k \<and> incidx R k" 
  proof (cases m)
    case (Base_line L)
    have "incidx P L \<and> incidx Q L \<and> incidx R L"  using Base_line assms ch by (metis base_in_base)
    then show ?thesis using Base_line  assms ch line_level2
    by (meson base_in_base)
  next
    case (Join Pair n)
    obtain S T where b: "Pair = (Upair S T)" using uprod_exhaust by auto
    then have "n \<noteq> 0" (* do I need this? *)
    by (smt (verit) Join ch fline.distinct(1) l_level.simps(2) line_level2 mem_Collect_eq new_lines.simps(1))
    have belong: "fppincid (Base_point X) (Join (Upair S T) n) = (\<exists> A1 B1 . ((Upair S T) = Upair A1 B1) 
 \<and> (A1 = (Base_point X) \<or> (B1 = (Base_point X))))" by simp 
    then have "... = (S = (Base_point X)) \<or> (T = (Base_point X))" by auto 
    then have u: "fppincid (Base_point X) (Join (Upair S T) n) = (S = (Base_point X)) \<or> (T = (Base_point X))" for X by auto 
    have z1: "(Base_point P = S) \<or> (Base_point P = T)" using u [of P]  b ch Join by blast
    have z2: "(Base_point Q = S) \<or> (Base_point Q = T)" using u [of Q]  b ch Join by blast
    have z3: "(Base_point R = S) \<or> (Base_point R = T)" using u [of R]  b ch Join by blast
    have dups: "(P = Q) \<or> (P = R) \<or> (Q = R)" using z1 z2 z3 by blast
    have False using dups assms
      by (smt (verit, best) One_nat_def Suc_1 card.empty card.insert finite.intros(1) finite_insert insert_absorb insert_absorb2 insert_commute insert_not_empty
          numeral_eq_iff one_eq_numeral_iff semiring_norm(89) verit_eq_simplify(12))
  then show ?thesis
  by fastforce
  qed
qed

lemma three_elements: (* From a set with cardinality more than 2, we can obtain 3 distinct items *)
  fixes U::"'a set"
  assumes a: "card U > 2"
  shows "\<exists> A B C  . A \<in> U \<and> B \<in> U \<and> C \<in> U  \<and> distinct3 A B C"
proof -
  obtain A where aa: "A \<in> U" using a by force
  have c1: "card (U - {A}) > 1" using aa  using assms by force
  obtain B where bb: "B \<in>  (U - {A})"
  by (metis c1 all_not_in_conv bot_nat_0.extremum_strict card.empty)
  have "B \<noteq> A" using bb by blast
  have c2: "card (U - {A,B}) > 0" using aa bb assms 
    using not_numeral_le_zero by fastforce
  obtain C where cc: "C \<in> (U - {A, B})"
  by (metis c2 card_gt_0_iff equals0I)
  have "C \<noteq> A \<and> C \<noteq> B" using cc by blast
  show ?thesis using aa bb cc distinct3_def by (metis DiffE insert_iff)
qed

lemma fpp_two_points_zero: (* a level zero line contains at least two points: needs 4-elt set U! *)
  assumes "k \<in> Pi_lines"
  assumes "l_level k = 0"
  assumes "U \<subseteq> Points"
  assumes "card U = 4"
  assumes imp: "\<And> P Q R . ((distinct3 P Q R) \<and> ({P, Q, R} \<subseteq> U)) \<Longrightarrow>  \<not> (pcollinear P Q R)" 
  shows "\<exists> P Q . P \<noteq> Q \<and> fppincid P k \<and> fppincid Q k \<and> P \<in> Pi_points \<and> Q \<in> Pi_points"
proof (rule ccontr)
  assume ch: "\<not> (\<exists> P Q . P \<noteq> Q \<and> fppincid P k \<and> fppincid Q k \<and> P \<in> Pi_points \<and> Q \<in> Pi_points)"
  let ?kpts = "{X . fppincid X k \<and> X \<in> Pi_points}"
  have kpchoice: "?kpts = {} \<or> (\<exists> R . ?kpts = {R})" using ch by blast
  then have "card ?kpts < 2" by (metis (mono_tags, lifting) card.empty card.insert finite.intros(1) insert_absorb less_2_cases_iff)
  let ?g = "\<lambda> x .  Base_point x"
  let ?Upts = "?g ` U"
  have Upts_pi: "?Upts \<subseteq> Pi_points"
  by (smt (verit, best) assms(3) imageE mem_Collect_eq new_points.simps(1) pi_points_contents subset_iff)
  have "card ?Upts = 4"  
    by (simp add: assms card_image inj_on_def)
  have s: "card (?Upts - ?kpts) > 2"
  by (metis (lifting) Diff_empty Diff_insert0 \<open>card (Base_point ` U) = 4\<close> add_2_eq_Suc add_diff_cancel_left' card_Diff_singleton
      diff_is_0_eq kpchoice lessI linorder_not_le numeral_Bit0 plus_1_eq_Suc zero_neq_numeral)
  then obtain P Q R where pqr_def: "P \<in> (?Upts - ?kpts) \<and> Q \<in> (?Upts - ?kpts) \<and> R \<in> (?Upts - ?kpts) \<and> 
    distinct3 P Q R" using s  three_elements sorry
  have "{P, Q, R} \<subseteq> ?Upts" using  pqr_def by blast
  then have "{P,Q,R} \<subseteq> Pi_points" using Upts_pi by order
  then have not_k: "(\<not> (fppincid P k)) \<and> (\<not> (fppincid Q k)) \<and> (\<not> (fppincid R k))" using pqr_def by blast
  obtain uP uQ uR where upqr_def: "P = Base_point uP \<and> Q = Base_point uQ \<and> R = Base_point uR \<and>  
    distinct3 uP uQ uR \<and> uP \<in> U \<and> uQ \<in> U \<and> uR \<in> U" using pqr_def  
    by (smt (verit, ccfv_SIG) DiffE distinct3_def imageE)
  then have "\<not> (pcollinear uP uQ uR)" using assms by blast
  then have jj: "\<not> (\<exists>s\<in> Lines. incid uP s \<and> incid uQ s \<and> incid uR s)" 
    using upqr_def assms(4) in_mono pcollinear_def using assms(3) by fastforce
  show False using  bexE configuration.base_in_base configuration.fppincid.simps(1) configuration_def distinct3_def empty_iff insertCI upqr_def
  by (smt (verit, best))
qed


lemma fpp_two_points_one: (* a level-one line contains at least two points *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  assumes "k \<in> Pi_lines"
  assumes "l_level k = 1"
  shows "\<exists> P Q . P \<noteq> Q \<and> fppincid P k \<and> fppincid Q k \<and> P \<in> Pi_points \<and> Q \<in> Pi_points"
proof -
thm line_level2 
thm line_level2 [of k 1] 
  have "k \<in> new_lines 1" using assms line_level2 [of k 1] by auto
  then obtain S T where join_def: "k = Join (Upair S T) 1 \<and> S \<noteq> T" and contents: "S \<in> Pi_points \<and> T \<in> Pi_points"  using new_lines.simps
    by (smt (verit, ccfv_threshold) One_nat_def mem_Collect_eq point_containment point_set.simps(1))
  then have "fppincid S k \<and> fppincid T k \<and> S \<in> Pi_points \<and> T \<in> Pi_points"  using join_def 
    using fppincid.elims(3) by blast
  then show ?thesis  using join_def by blast
qed

lemma fpp_two_points_two: (* a level two or higher line contains at least two points *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes p
  assumes "k \<in> Pi_lines"
  assumes "l_level k \<ge> 2"
  assumes "p = l_level k"
  shows "\<exists> P Q . P \<noteq> Q \<and> fppincid P k \<and> fppincid Q k \<and> P \<in> Pi_points \<and> Q \<in> Pi_points"
proof -
  have kloc: "k \<in> new_lines p" using assms line_level2  by blast
  have n2: "p \<ge> 2" using assms by blast
  show ?thesis
  proof (cases "even p")
    case True
    have False using True new_lines.simps assms(1,3) lines_odd_or_zero n2 by fastforce
    then show ?thesis by auto
  next
    case False
    obtain n where "p = Suc (Suc n)" using n2 
      by (metis One_nat_def Suc_1 Suc_le_D Suc_le_mono)
    then obtain S T where kdef: "k = Join (Upair S T) (Suc (Suc n))\<and> 
    (S \<in> new_points (Suc n)) \<and> 
    (T \<in> point_set (Suc n)) \<and>  (S \<noteq> T)" 
      by (smt (verit, best) emptyE kloc mem_Collect_eq new_lines.simps(3))
    then have "fppincid S k \<and> fppincid T k \<and> S \<in> Pi_points \<and> T \<in> Pi_points"  
      using kdef fppincid.elims(3)
      by (smt (verit) fline.simps(4) fppincid.simps(2) pi_points_contents2 point_containment subsetD)
    then show ?thesis  using kdef by blast
  qed
qed

lemma fpp_two_points:

  fixes  p
  assumes "k \<in> Pi_lines"
  assumes "p = l_level k"
  assumes "U \<subseteq> Points"
  assumes "card U = 4"
  assumes imp: "\<And> P Q R . ((distinct3 P Q R) \<and> ({P, Q, R} \<subseteq> U)) \<Longrightarrow>  \<not> (pcollinear P Q R)" 
  shows "\<exists> P Q . P \<noteq> Q \<and>  fppincid P k \<and> fppincid Q k \<and> P \<in> Pi_points \<and> Q \<in> Pi_points"
proof -
  consider (zero) "p = 0" | (one) "p = 1" | (many) "p \<ge> 2" by fastforce
  then have "\<exists> P Q . P \<noteq> Q \<and>  fppincid P k \<and> fppincid Q k \<and> P \<in> Pi_points \<and> Q \<in> Pi_points"
  proof cases
    case zero
    then show ?thesis using assms fpp_two_points_zero imp by presburger
  next
    case one
    then show ?thesis using assms fpp_two_points_one imp by presburger
  next
    case many
    then show ?thesis using assms fpp_two_points_two imp by simp
  qed
  then show ?thesis by auto
qed

end
end


