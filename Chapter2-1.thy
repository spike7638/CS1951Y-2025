theory "Chapter2-1R"
  imports  "HOL-Library.Uprod" "../COMPLETED-VERSIONS/ALTERNATIVE-VERSIONS/Chapter1-3R" 

begin
declare [[smt_timeout = 1500]]
declare [[smt_reconstruction_step_timeout = 1500]]

(* hide_const join *)

section\<open>Desargues Introduction\<close>
locale projective_space_data =
  fixes Points :: "'p set" and Lines :: "'p set set" and Planes:: "'p set set" 
  fixes join:: "'p \<Rightarrow> 'p \<Rightarrow> 'p set"
  fixes plane_through:: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p set"

begin

definition (in projective_space_data) collinear :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
    where "collinear (A::'p) (B::'p) (C::'p) = (if (A \<in> Points \<and> B \<in> Points \<and> C \<in> Points)  
  then (\<exists> l. l \<in> Lines \<and> A \<in> l \<and> B \<in> l \<and> C \<in> l) else undefined)"

definition (in projective_space_data) coplanar :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
    where "coplanar (A::'p) (B::'p) (C::'p) D = (if (A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points)  
  then (\<exists> H. H \<in> Planes \<and> A \<in> H \<and> B \<in> H \<and> C \<in> H \<and> D \<in> H) else undefined)"

definition (in projective_space_data) coincident :: "'p set \<Rightarrow> 'p set \<Rightarrow> 'p set \<Rightarrow> bool"
    where "coincident n k m  = (if (n \<in> Lines) \<and> (k \<in> Lines) \<and> (m  \<in> Lines)
  then (\<exists> P. P \<in> Points \<and> P \<in> n \<and> P \<in> k \<and> P \<in> m) else undefined)"
end (* projective_space_data *)

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
(*  S2: "\<lbrakk>\<not> collinear P Q R; P \<in> Points; Q \<in> Points; R \<in> Points\<rbrakk> 
      \<Longrightarrow> (\<exists> H . H \<in> Planes \<and> P \<in> H \<and> Q \<in> H \<and> R \<in> H) \<and> H = plane_through P Q R" and *)
    S3: "\<lbrakk>k \<in> Lines; H \<in> Planes\<rbrakk> \<Longrightarrow> (\<exists>P . P \<in> k \<and> P \<in> H)" and
    S4: "\<lbrakk>H \<in> Planes; N \<in> Planes \<rbrakk> \<Longrightarrow> (\<exists>k \<in> Lines . k \<subseteq> H \<and> k \<subseteq> N)" and
    S5: "(\<exists>P Q R S. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points \<and> 
          \<not> coplanar P Q R S \<and> 
          \<not> collinear P Q R \<and> \<not> collinear P Q S \<and> \<not> collinear P R S \<and> \<not> collinear Q R S)" and
    S6: "\<lbrakk>k \<in> Lines\<rbrakk> \<Longrightarrow> (\<exists>P Q R . P \<in> k \<and> Q \<in> k \<and> R \<in> k \<and> distinct[P,Q,R])" and
    S0a: "\<lbrakk>k \<in> Lines; P \<in> k\<rbrakk> \<Longrightarrow> P \<in> Points" and
    S0b: "\<lbrakk>H \<in> Planes; P \<in> H\<rbrakk> \<Longrightarrow> P \<in> Points"
begin

text \<open>\hadi\<close>
lemma S5_dist:
  fixes P Q R S
  assumes "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points 
    \<and> S \<in> Points \<and> \<not> coplanar P Q R S \<and> \<not> collinear P Q R \<and> \<not> collinear P Q S 
    \<and> \<not> collinear P R S \<and> \<not> collinear Q R S"
  shows "distinct[P,Q,R,S]"
proof (rule ccontr)
  assume "\<not> distinct[P,Q,R,S]"
  then consider
  "P = Q" | "P = R " | "P = S" | "Q = R" | "Q = S" | "R = S" by fastforce
  then show False using assms S2a unfolding coplanar_def by metis
qed
text \<open>\done\<close>

lemma (in projective_space) point_outside_plane: (* For any plane H, there's a point P not on it *)
  assumes "H \<in> Planes"
  obtains P where "P \<in> Points \<and> P \<notin> H"
  using assms S2a S2b S5 unfolding coplanar_def by metis

lemma (in projective_space) crossing_planes: (* two distinct planes intersect in exactly a line. *) 
  assumes "H \<in> Planes \<and> K \<in> Planes"
  assumes "H \<noteq> K"
  shows "\<exists> n \<in> Lines . (n = (H \<inter> K))"
proof -
  from S4 obtain k where kdef: "k \<in> Lines \<and> k \<subseteq> H \<and> k \<subseteq> K" using assms by blast
  from S6 obtain A B where abdef: "A \<in> k \<and> B \<in> k \<and> A \<noteq> B" using kdef by fastforce
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

text \<open>\hadi\<close>
lemma (in projective_space) extra_point:
  fixes P Q H
  assumes "H \<in> Planes"
  assumes "P \<in> Points" and "Q \<in> Points"
  assumes "P \<noteq> Q"
  shows "\<exists>R \<in> Points. ((\<not> collinear P Q R) \<and> (R \<notin> H))"
proof -
  obtain R where rdef: "R \<in> Points \<and> R \<notin> (join P Q)" using assms S1a S5
    unfolding collinear_def by metis
  then have pqr: "\<not> collinear P Q R" using assms S1b collinear_def by auto
  show ?thesis sorry
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in projective_space) two_point_line_in_plane:
  fixes P Q H
  assumes "H \<in> Planes"
  assumes "P \<in> Points" and "Q \<in> Points"
  assumes "P \<in> H" and "Q \<in> H"
  assumes "P \<noteq> Q"
  shows "join P Q \<subseteq> H"
proof -
  obtain R where rdef: "R \<in> Points \<and> \<not> collinear P Q R \<and> R \<notin> H" 
    using assms extra_point [of H] by auto
  then obtain l where ldef: "l \<in> Lines \<and> l = H \<inter> (plane_through P Q R)" 
    using assms S2a crossing_planes [of H] by auto
  then show ?thesis using assms S1b S2a rdef ldef by simp
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in projective_space) proj_space_plane_p1:
  fixes H
  assumes HP: "H \<in> Planes"
  defines HPdef: "HPoints \<equiv> {P. P \<in> Points \<and> P \<in> H}"
  defines HLdef: "HLines \<equiv> {L. L \<in> Lines \<and> L \<subseteq> H}"
  defines Hidef: "Hincid \<equiv> (\<lambda>P L. (if P \<in> HPoints \<and> L \<in> HLines then P \<in> L else undefined))"
  shows "\<lbrakk>P \<noteq> Q; P \<in> HPoints; Q \<in> HPoints\<rbrakk> \<Longrightarrow> (\<exists>!k. k \<in> HLines \<and> Hincid P k \<and> Hincid Q k)"
proof -
  fix P Q
  assume pnq: "P \<noteq> Q" and php: "P \<in> HPoints" and qhp: "Q \<in> HPoints"
  then have pqhl: "(join P Q) \<in> HLines" 
    using two_point_line_in_plane S1a HP HPdef HLdef by simp
  then have kexist: "\<exists>k. k \<in> HLines \<and> Hincid P k \<and> Hincid Q k" 
    using pnq php qhp S1a HPdef Hidef by auto
  then have "l \<in> HLines \<and> Hincid P l \<and> Hincid Q l \<Longrightarrow> l = (join P Q)" for l 
    using pnq php qhp S0a S1b HLdef Hidef by simp
  then show "\<exists>!k. k \<in> HLines \<and> Hincid P k \<and> Hincid Q k" using kexist by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in projective_space) proj_space_plane_p2:
  fixes H
  assumes HP: "H \<in> Planes"
  defines HPdef: "HPoints \<equiv> {P. P \<in> Points \<and> P \<in> H}"
  defines HLdef: "HLines \<equiv> {L. L \<in> Lines \<and> L \<subseteq> H}"
  defines Hidef: "Hincid \<equiv> (\<lambda>P L. (if P \<in> HPoints \<and> L \<in> HLines then P \<in> L else undefined))"
  shows "\<lbrakk>k \<in> HLines; n \<in> HLines\<rbrakk> \<Longrightarrow> \<exists>P. (P \<in> HPoints \<and> Hincid P k \<and> Hincid P n)"
proof (rule ccontr)
  fix k n
  assume khl: "k \<in> HLines" and nhl: "n \<in> HLines"
  assume cd: "\<not> (\<exists>P. (P \<in> HPoints \<and> Hincid P k \<and> Hincid P n))"
  have "\<forall>P. P \<in> HPoints \<and> Hincid P k \<longrightarrow> \<not> Hincid P n"
    and "\<forall>P. P \<in> HPoints \<and> Hincid P n \<longrightarrow> \<not> Hincid P k" using cd by auto
  then have kton: "\<forall>P. P \<in> Points \<and> P \<in> H \<and> P \<in> k \<longrightarrow> \<not> P \<in> n"
    and ntok: "\<forall>P. P \<in> Points \<and> P \<in> H \<and> P \<in> n \<longrightarrow> \<not> P \<in> k" 
    using khl nhl HPdef Hidef by simp+
  then show False sorry
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in projective_space) proj_space_plane_p3:
  fixes H
  assumes HP: "H \<in> Planes"
  defines HPdef: "HPoints \<equiv> {P. P \<in> Points \<and> P \<in> H}"
  defines HLdef: "HLines \<equiv> {L. L \<in> Lines \<and> L \<subseteq> H}"
  defines Hidef: "Hincid \<equiv> (\<lambda>P L. (if P \<in> HPoints \<and> L \<in> HLines then P \<in> L else undefined))"
  shows "\<exists>P Q R. P \<in> HPoints \<and> Q \<in> HPoints \<and> R \<in> HPoints 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)"
proof (rule ccontr)
  assume "\<not> (\<exists>P Q R. P \<in> HPoints \<and> Q \<in> HPoints \<and> R \<in> HPoints 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R))"
  then have "\<forall>P Q R. P \<in> HPoints \<and> Q \<in> HPoints \<and> R \<in> HPoints 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<longrightarrow> collinear P Q R" by auto
  then have cd: "\<forall>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<in> H \<and> Q \<in> H 
    \<and> R \<in> H \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<longrightarrow> collinear P Q R" using HPdef by simp
  obtain P Q where pqdef: "P \<in> H \<and> Q \<in> H \<and> P \<noteq> Q" 
    using S3 [of H] S4 [of H] S6 HP distinct_length_2_or_more subset_eq by metis
  then have pqh: "(join P Q) \<subseteq> H" using S0b two_point_line_in_plane HP by auto
  then have "\<forall>R. R \<in> H \<longrightarrow> collinear P Q R" using cd pqdef S0b S1a HP
    unfolding collinear_def by metis
  then have "\<forall>R. R \<in> H \<longrightarrow> R \<in> (join P Q)" 
    using pqdef S0b S1b HP collinear_def by auto
  then have "H = (join P Q)" using pqh by auto
  then show False sorry
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in projective_space) proj_space_plane_p4:
  fixes H
  assumes HP: "H \<in> Planes"
  defines HPdef: "HPoints \<equiv> {P. P \<in> Points \<and> P \<in> H}"
  defines HLdef: "HLines \<equiv> {L. L \<in> Lines \<and> L \<subseteq> H}"
  defines Hidef: "Hincid \<equiv> (\<lambda>P L. (if P \<in> HPoints \<and> L \<in> HLines then P \<in> L else undefined))"
  shows "\<lbrakk>k \<in> HLines; U = {P. (P \<in> HPoints \<and> Hincid P k)}\<rbrakk> 
    \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
proof -
  fix k U
  assume khl: "k \<in> HLines" and udef: "U = {P. (P \<in> HPoints \<and> Hincid P k)}"
  then obtain P Q R where pqr: "P \<in> k \<and> Q \<in> k \<and> R \<in> k \<and> distinct[P,Q,R]" 
    using S6 HLdef by blast
  then have "P \<in> HPoints \<and> Q \<in> HPoints \<and> R \<in> HPoints" 
    using khl pqr S0a HPdef HLdef by auto
  then show "\<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct[Q,R,S]" 
    using khl udef pqr Hidef by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in projective_space) space_plane_is_proj_plane:
  fixes H
  assumes HP: "H \<in> Planes"
  defines HPdef: "HPoints \<equiv> {P. P \<in> Points \<and> P \<in> H}"
  defines HLdef: "HLines \<equiv> {L. L \<in> Lines \<and> L \<subseteq> H}"
  defines Hidef: "Hincid \<equiv> (\<lambda>P L. (if P \<in> HPoints \<and> L \<in> HLines then P \<in> L else undefined))"
  shows "\<lbrakk>P \<noteq> Q; P \<in> HPoints; Q \<in> HPoints\<rbrakk> \<Longrightarrow> (\<exists>!k. k \<in> HLines \<and> Hincid P k \<and> Hincid Q k)"  
    and "\<lbrakk>k \<in> HLines; n \<in> HLines\<rbrakk> \<Longrightarrow> \<exists>P. (P \<in> HPoints \<and> Hincid P k \<and> Hincid P n)" 
    and "\<exists>P Q R. P \<in> HPoints \<and> Q \<in> HPoints \<and> R \<in> HPoints 
      \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)"
    and "\<lbrakk>k \<in> HLines; U = {P. (P \<in> HPoints \<and> Hincid P k)}\<rbrakk> 
      \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct[Q, R, S]"
proof -
  show "\<lbrakk>P \<noteq> Q; P \<in> HPoints; Q \<in> HPoints\<rbrakk> \<Longrightarrow> (\<exists>!k. k \<in> HLines \<and> Hincid P k \<and> Hincid Q k)"
    using assms proj_space_plane_p1 by simp
  show "\<lbrakk>k \<in> HLines; n \<in> HLines\<rbrakk> \<Longrightarrow> \<exists>P. (P \<in> HPoints \<and> Hincid P k \<and> Hincid P n)"
    using assms proj_space_plane_p2 by simp
  show "\<exists>P Q R. P \<in> HPoints \<and> Q \<in> HPoints \<and> R \<in> HPoints 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)"
    using assms proj_space_plane_p3 by simp
  show "\<lbrakk>k \<in> HLines; U = {P. (P \<in> HPoints \<and> Hincid P k)}\<rbrakk> 
    \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct[Q, R, S]"
    using assms proj_space_plane_p4 by simp
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in projective_space) crossing_lines: (* two distinct lines through a point determine a unique plane *)
  fixes k n P
  assumes "k \<in> Lines" and "n \<in> Lines"
  assumes "k \<noteq> n"
  assumes "P \<in> Points"
  assumes "P \<in> k \<inter> n"
  shows "\<exists>!H. H \<in> Planes \<and> k \<subseteq> H \<and> n \<subseteq> H"
proof -
  obtain Q where qdef: "Q \<in> k \<and> Q \<notin> n" using assms S0a S1b S6 
    distinct_length_2_or_more by metis
  obtain R where rdef: "R \<in> n \<and> R \<notin> k" using assms S0a S1b S6 
    distinct_length_2_or_more by metis
  then have pqr: "\<not> collinear P Q R" using assms qdef S0a S1b Int_iff
    unfolding collinear_def by metis
  then obtain H where hdef: "H = plane_through P Q R" by simp
  then have hkn: "H \<in> Planes \<and> k \<subseteq> H \<and> n \<subseteq> H" using assms qdef rdef pqr S0a S1b S2a
    two_point_line_in_plane Int_iff by metis
  have "N \<in> Planes \<and> k \<subseteq> N \<and> n \<subseteq> N \<Longrightarrow> H = N" for N using assms hdef qdef rdef pqr
    S0a S2b Int_iff subsetD by metis
  then show ?thesis using hkn by metis
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in projective_space) crossing_lines_2:
  fixes k n H
  assumes "k \<in> Lines" and "n \<in> Lines"
  assumes "k \<noteq> n"
  assumes "H \<in> Planes"
  assumes "k \<subseteq> H \<and> n \<subseteq> H"
  shows "\<exists>!P. P \<in> Points \<and> P \<in> k \<and> P \<in> n"
proof -
  let ?HPoints = "{P. P \<in> Points \<and> P \<in> H}"
  let ?HLines = "{L. L \<in> Lines \<and> L \<subseteq> H}"
  let ?Hincid = "\<lambda>P L. (if P \<in> ?HPoints \<and> L \<in> ?HLines then P \<in> L else undefined)"
  have "\<exists>P. (P \<in> ?HPoints \<and> ?Hincid P k \<and> ?Hincid P n)" 
    using assms proj_space_plane_p2 [of H] by simp
  then have pexist: "\<exists>P. P \<in> Points \<and> P \<in> k \<and> P \<in> n" using assms by auto
  then obtain P where "P \<in> Points \<and> P \<in> k \<and> P \<in> n" by auto
  then have "Q \<in> Points \<and> Q \<in> k \<and> Q \<in> n \<longrightarrow> Q = P" for Q 
    using assms S1b [of Q P] by auto
  then show ?thesis using pexist by auto
qed
text \<open>\done\<close>

(*definition distinct7 where 
  "distinct7 x y z w r s t \<equiv> 
    y \<noteq> x \<and> 
    z \<noteq> x \<and> z \<noteq> y \<and> 
    w \<noteq> x \<and> w \<noteq> y \<and> w \<noteq> z \<and>
    r \<noteq> x \<and> r \<noteq> y \<and> r \<noteq> z \<and> r \<noteq> w \<and>
    s \<noteq> x \<and> s \<noteq> y \<and> s \<noteq> z \<and> s \<noteq> w \<and> s \<noteq> r \<and>
    t \<noteq> x \<and> t \<noteq> y \<and> t \<noteq> z \<and> t \<noteq> w \<and> t \<noteq> r \<and> t \<noteq> s"*)

text \<open>\hadi\<close>
theorem (in projective_space) Desargues_case_1:
  fixes U A B C A' B' C' P Q R
  assumes "U \<in> Points" and "A \<in> Points" and "B \<in> Points" and "C \<in> Points" and
    "A' \<in> Points" and "B' \<in> Points" and "C' \<in> Points"
  assumes "distinct[U, A, B, C, A', B', C']" 
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
  let ?abc = "plane_through A B C" 
  let ?a'b'c' = "plane_through A' B' C'"
  have "P \<in> ?abc" and "P \<in> ?a'b'c'" and "Q \<in> ?abc" and "Q \<in> ?a'b'c'" 
    and "R \<in> ?abc" and "R \<in> ?a'b'c'" using assms S2a two_point_line_in_plane
    distinct_length_2_or_more Int_iff inf.absorb_iff2 by metis+
  then obtain k where "k \<in> Lines \<and> P \<in> k \<and> Q \<in> k \<and> R \<in> k" 
    using assms S2a crossing_planes IntI by metis
  then show ?thesis using S0a collinear_def by auto
qed
text \<open>\done\<close>

theorem (in projective_space) Desargues_case_2:
  fixes U A B C A' B' C' P Q R
  assumes "U \<in> Points" and "A \<in> Points" and "B \<in> Points" and "C \<in> Points" and
    "A' \<in> Points" and "B' \<in> Points" and "C' \<in> Points"
  assumes "distinct[U, A, B, C, A', B', C']" 
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
  obtain X where xdef: "X \<in> Points \<and> X \<notin> ?S" 
    using assms S2a point_outside_plane by blast
  then obtain D where ddef: "D \<in> Points \<and> D \<in> (join X B) \<and> D \<noteq> X \<and> D \<noteq> B" 
    using assms S0a S1a S2a S6 distinct_length_2_or_more by metis
  let ?ubx = "plane_through U B X"
  have nubx: "\<not> collinear U B X" 
    using assms xdef S1b S2a two_point_line_in_plane [of ?S B]
    distinct_length_2_or_more in_mono unfolding collinear_def by (smt (verit))
  then have "join U B \<subseteq> ?ubx" using assms xdef S2a two_point_line_in_plane by auto
  then have "B' \<in> ?ubx" using assms S1b collinear_def by auto
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
    then have uxub': "join U X = join U B'" using assms ldef S1b by auto
    have "B \<in> join U B'" using assms(1,3,6,8,10) S1b collinear_def by auto
    then have "B \<in> join U X" using uxub' by simp
    then have "collinear U B X" using assms ldef xdef S1b 
      unfolding collinear_def by metis
    then show False using nubx by simp
  qed
  have und': "U \<noteq> D'"
  proof (rule ccontr)
    assume "\<not> U \<noteq> D'"
    then have "U \<in> join X B'" using d'def by auto
    then have "collinear U B' X" using assms xdef S1a S2a 
      unfolding collinear_def by metis
    then show False using nub'x by simp
  qed
  have ddist: "distinct[U,A,D,C,A',D',C']"
  proof (rule ccontr)
    assume "\<not> distinct[U,A,D,C,A',D',C']"
    then consider
    "U = A" | "U = C" | "U = A'" | "U = C'" | "A = C" | "A = A'" | "A = C'" 
    | "C = A'" | "C = C'" | "A' = C'" | "U = D" | "A = D" | "D = C'" 
    | "D = C" | "U = D'" | "A = D'"  | "D = A'" | "D = D'"  | "C = D'" 
    | "A' = D'" | "D' = C'" by fastforce
    then show False using assms apply cases 
    apply simp+ using S1a ddef nubx xdef unfolding collinear_def
    apply metis using assms S1a S1b S2a ddef in_mono
      two_point_line_in_plane xdef apply (smt (verit))
    using assms S1a S1b S2a ddef in_mono
      two_point_line_in_plane xdef apply (smt (verit))
    using assms S1a S1b S2a ddef in_mono
      two_point_line_in_plane xdef apply (smt (verit))
    using und' apply simp sorry
  qed
  have dd'u: "collinear D D' U" using assms S1a ddef d'def IntE
    unfolding collinear_def by metis
  have adc: "\<not> collinear A D C"
  proof (rule ccontr)
    assume "\<not> (\<not> collinear A D C)"
    then obtain l where ldef: "l \<in> Lines \<and> A \<in> l \<and> D \<in> l \<and> C \<in> l" 
      using assms ddef unfolding collinear_def by auto
    then have lac: "l = join A C" using assms S1a S1b 
      unfolding collinear_def by metis
    have "join A C \<subseteq> ?S" using assms ldef S1a S2a two_point_line_in_plane 
      unfolding collinear_def by metis
    then have "D \<in> ?S" using lac ldef by auto
    then have "D = B" using assms S1a S1b S2a xdef ddef in_mono
      two_point_line_in_plane [of ?S D B] by (smt (verit))
    then show False using ddef by simp
  qed
  have a'd'c': "\<not> collinear A' D' C'"
  proof (rule ccontr)
    assume cd: "\<not> (\<not> collinear A' D' C')"
    then obtain l where ldef: "l \<in> Lines \<and> A' \<in> l \<and> D' \<in> l \<and> C' \<in> l" 
      using assms d'def unfolding collinear_def by auto
    then have lac: "l = join A' C'" using assms S1a S1b 
      unfolding collinear_def by metis
    have "join A' C' \<subseteq> ?S" using assms ldef S1a S2a two_point_line_in_plane 
      unfolding collinear_def by metis
    then have "D' \<in> ?S" using lac ldef by auto
    then have "D' = B'" using assms S1a S1b S2a xdef d'def in_mono Int_iff
      two_point_line_in_plane [of ?S D' B'] by (smt (verit, ccfv_threshold))
    then show False using assms cd by simp
  qed
  have adca'd'c': "plane_through A D C \<noteq> plane_through A' D' C'" sorry
  then have ada'd': "join A D \<noteq> join A' D'" sorry
  have dcd'c': "join D C \<noteq> join D' C'" sorry
  obtain P'::'p where p'def: "P \<in> (join A D) \<inter> (join A' D')" sorry
  obtain R'::'p where r'def: "R \<in> (join D C) \<inter> (join D' C')" sorry
  have "collinear P' Q R'" using assms ddist dd'u ddef d'def adc a'd'c'
    adca'd'c' ada'd' dcd'c' p'def r'def Desargues_case_1 [of U A D C A' D' C' P' Q R'] sorry
  then show ?thesis using assms Desargues_case_1 a'd'c' ada'd' adc adca'd'c'
    d'def dcd'c' dd'u ddef ddist p'def r'def by metis
qed
end

section \<open>Configurations\<close>

locale configuration =
  fixes S::"('p, 'l) plane_r" (structure)
  assumes C1: "(U \<in> Points S \<and> V \<in> Points S \<and> k \<in> Lines S \<and> n \<in> Lines S
    \<and> incid S U k \<and> incid S V k \<and> incid S U n \<and> incid S V n \<and> U \<noteq> V) \<Longrightarrow> k = n"
begin

lemma C1alt: 
  fixes P Q k n
  assumes "(P \<in> Points S \<and> Q \<in> Points S \<and> k \<in> Lines S \<and> n \<in> Lines S
    \<and> incid S P k \<and> incid S Q k \<and> incid S P n \<and> incid S Q n \<and> k \<noteq> n)"
  shows "P = Q" using assms C1 by auto

end

lemma affine_is_config: 
  fixes incid:: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes Points:: "'p set"
  fixes Lines:: "'l set"
  defines "AP \<equiv> \<lparr>Points=Points, Lines=Lines, incid= incid\<rparr>"
  assumes "affine_plane AP"
  shows "configuration \<lparr> Points=Points, Lines=Lines, incid=incid \<rparr>"
  using assms affine_plane.prop1P2 configuration_def by fastforce

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
  shows "\<exists>l m n. distinct[l, m, n] 
    \<and> incidD X l \<and> incidD X m \<and> incidD X n 
    \<and> l \<in> LinesD \<and> m \<in> LinesD \<and> n \<in> LinesD"
  using lines_distinctD unfolding incidD_def LinesD_def by (cases X)
    (simp only: insert_iff empty_iff conj_disj_distribL conj_disj_distribR
     ex_disj_distrib simp_thms(39); simp; fail)+

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
  shows "configuration \<lparr> Points=PointsD, Lines=LinesD, incid=incidD \<rparr>"
  using LinesD_def emptyE incidD_def insertE pointD.simps select_convs(2,3) 
  unfolding configuration_def by (smt (verit))

lemma no_lines_is_config: 
  fixes Points::"'a set"
  shows "configuration \<lparr> Points=Points, Lines={}, incid = (\<lambda>x L . False) \<rparr>"
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

(* Does this point lie on this line in \Pi? *)
fun fppincid::  " ('a, 'b) plane_r \<Rightarrow>  ('a, 'b) fpoint \<Rightarrow> ('a, 'b) fline \<Rightarrow> bool" where
(* if lines meet in pi0, they meet in Pi: *)
  "fppincid (c:: ('a, 'b) plane_r) (Base_point P) (Base_line m) = (incid c  P m)"  
(* if a basepoint incid a join-line, it must be one of the two ends of the join *) 
| "fppincid (c:: ('a, 'b)  plane_r) (Base_point P) (Join x n2) = (\<exists> A1 B1 . (x = Upair A1 B1) 
 \<and> (A1 = (Base_point P) \<or> (B1 = (Base_point P))))"
(* if a baseline incid a crossing, it must be one of the two crossing lines *)
| "fppincid (c:: ('a, 'b) plane_r) (Crossing u n1) (Base_line m) = (\<exists> l k . (u = Upair l k) 
 \<and> (l = (Base_line m)   \<or> (k =  (Base_line m))))" 

(* If a crossing lies on a join...then it must be one of the two points that formed the join *)
(* this is not correct! for that join might later be extended by further crossings with other lines *)
(*"fppincid CPoints CLines (incid) (Crossing u n1)  (Join x n2) = (\<exists> A1 B1 . (x = Upair A1 B1) 
 \<and> (A1 = (Crossing u n1)   \<or> (B1 = (Crossing u n1))))" *)
| "fppincid (c:: ('a, 'b) plane_r) (Crossing u n1)  (Join x n2) = (
     ((n1 < n2) \<and> 
      (\<exists> A1 B1 . x = Upair A1 B1 \<and> (A1 = Crossing u n1 \<or> B1 = Crossing u n1))) 
     \<or> 
     (\<exists> k m . u = Upair k m \<and> k = Join x n2 \<or> m = Join x n2)
   )"   
(*N.B.:  Two clauses above correspond to (1) previous condition, and (2) a crossing being on the extension of some join *)
fun point_set::"(('a, 'b) plane_r) \<Rightarrow> nat \<Rightarrow> (('a, 'b) fpoint) set" and
    line_set::"(('a, 'b) plane_r) \<Rightarrow> nat \<Rightarrow> (('a, 'b) fline) set" and
    new_points::"(('a, 'b)  plane_r) \<Rightarrow> nat \<Rightarrow> (('a, 'b) fpoint) set" and
    new_lines::"(('a, 'b)  plane_r) \<Rightarrow> nat \<Rightarrow> (('a, 'b) fline) set"    
    where
  "point_set (c:: ('a, 'b) plane_r) (0 ::nat)= new_points c 0" | 
  "line_set (c:: ('a, 'b) plane_r) (0 ::nat)= new_lines c 0" |
  "point_set (c:: ('a, 'b) plane_r) ( Suc n ::nat) = point_set c n \<union> new_points c (Suc n)" |
  "line_set (c:: ('a, 'b) plane_r) (Suc n ) = line_set c n \<union>  new_lines c (Suc n)" |
  "new_points c 0 = {Base_point Q | Q . Q \<in> Points c}" |
  "new_points c (Suc 0) = ({}::(('a, 'b) fpoint) set)" |
  "new_points c (Suc (Suc 0)) =   
  {Crossing (Upair k l) (Suc (Suc 0)) | k l . 
    ((k \<in> new_lines c 0) \<or> (k \<in> new_lines c (Suc 0))) \<and> 
    (l \<in> line_set c (Suc 0)) \<and> (k \<noteq> l) \<and>
    \<not> (\<exists>Y \<in> point_set c (Suc 0) . fppincid c Y k \<and> fppincid c Y l \<and> (p_level Y \<le> (Suc 0)))}" |
  "new_points c (Suc (Suc n::nat)) = 
  (if (odd n) then {} else 
  {Crossing (Upair k l) (Suc (Suc n)) | k l . 
    (k \<in> new_lines c (Suc n)) \<and> 
    (l \<in> line_set c (Suc n)) \<and> (k \<noteq> l) \<and>
    \<not> (\<exists>Y \<in> point_set c (Suc n) . fppincid c Y k \<and> fppincid c Y l \<and> (p_level Y \<le> (Suc n)))})" |
  "new_lines c 0 = {Base_line k| k . k \<in> Lines c}"  |
  "new_lines c (Suc 0) = {Join (Upair S T) 1 | S T . 
    (S \<in> new_points c 0) \<and> 
    (T \<in> point_set c 0) \<and> (S \<noteq> T) \<and>
    \<not> (\<exists>k \<in> line_set c 0 . fppincid  c S k \<and> fppincid c T k \<and> (l_level k \<le> 1))}" |
  "new_lines c (Suc (Suc n)) = 
  (if (even n) then {} else 
   {Join (Upair S T) (Suc (Suc n)) | S T . 
    (S \<in> new_points c (Suc n)) \<and> 
    (T \<in> point_set c (Suc n)) \<and>  (S \<noteq> T) \<and> 
    \<not> (\<exists>k \<in> line_set c (Suc n) . fppincid  c S k \<and> fppincid c T k \<and> (l_level k \<le> (Suc n)))})" 

definition Pi_points::"(('a, 'b) plane_r) \<Rightarrow> ((('a, 'b) fpoint) set)" 
  where "Pi_points (c::('a, 'b) plane_r) = 
     \<Union> ((new_points c)  ` UNIV)"

definition Pi_lines::"(('a, 'b) plane_r) \<Rightarrow> ((('a, 'b) fline) set)" 
  where "Pi_lines c = 
     \<Union> ((new_lines c)  ` UNIV)"

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

lemma point_level: (* a point in new_points c n has level n *)
  assumes "P \<in> new_points c n"
  shows "p_level P = n"
proof -
  consider (zero) "n = 0" | (one) "n = Suc 0" | (two) "n = Suc (Suc 0)" 
  | (many) "\<exists>p .  n = Suc (Suc (Suc p))" using old.nat.exhaust by metis
  then show ?thesis
  proof cases
    case many
    obtain p where nd: "n = Suc (Suc (Suc p))" using many by auto
    obtain k l where p_def:"P = Crossing (Upair k l) (Suc (Suc (Suc p))) \<and>
         k \<in> new_lines c (Suc (Suc p)) \<and>
         l \<in> line_set c (Suc (Suc p)) \<and> k \<noteq> l 
          \<and> \<not> (\<exists>Y\<in>point_set c (Suc (Suc p)). fppincid c Y k \<and> fppincid c Y l 
          \<and> p_level Y \<le> Suc (Suc p))" 
    using assms nd new_points.simps empty_iff mem_Collect_eq by (smt (verit))
    then have "p_level P = Suc (Suc (Suc p))" using p_level.simps by simp
    then show ?thesis using nd by simp
  next
  case zero
    then show ?thesis using assms by auto
  next
    case one
    then show ?thesis  using assms by auto
  next
    case two
    then show ?thesis  using assms by auto
  qed
qed

lemma point_level2: (* if a Point's level is k, it's in new_points c k *)
  fixes P c n
  assumes a1: "P \<in> Pi_points c"
  assumes a2: "k = p_level P"
  shows "P \<in> new_points c k"
proof -
  obtain n where u1: "P \<in> new_points c n" 
    using a1 Pi_points_def new_points.simps by auto
  have u2: "k = n" using u1 a2 p_level.simps point_level by auto
  show ?thesis using a2 u1 u2 by auto
qed

lemma points_even: (* if a Point's level is k, then k is even *)
  fixes P c
  assumes a1: "P \<in> Pi_points c"
  assumes a2: "n = p_level P"
  shows "even n"
proof -
  have u0: "P \<in> new_points c n" using a1 a2 point_level2 by auto
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
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes a1: "P \<in> Pi_points c"
  assumes a2: "P = Crossing (Upair m s) n"
  shows "m \<noteq> s"
proof (cases P)
  case (Base_point x11)
  have False using a2 Base_point by auto
  then show ?thesis by blast
next
  case (Crossing x21 n)
  obtain v where vv: "P \<in> new_points c v" 
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
    have t1: "new_points c v = {Crossing (Upair k l) v | k l . 
    ((k \<in> new_lines c 0) \<or> (k \<in> new_lines c (Suc 0))) \<and> 
    (l \<in> line_set c (Suc 0)) \<and> (k \<noteq> l) \<and>
    \<not> (\<exists>Y \<in> point_set c (Suc 0) . fppincid c Y k \<and> fppincid c Y l \<and> (p_level Y \<le> (Suc 0)))}"
      using new_points.simps vv two by auto
    obtain k l where kl: "P = Crossing (Upair k l) v \<and> 
    ((k \<in> new_lines c 0) \<or> (k \<in> new_lines c (Suc 0))) \<and> 
    (l \<in> line_set c (Suc 0)) \<and> (k \<noteq> l) \<and>
    \<not> (\<exists>Y \<in> point_set c (Suc 0) . fppincid c Y k \<and> fppincid c Y l \<and> (p_level Y \<le> (Suc 0)))" 
      using t1 vv by fastforce
    have "k \<noteq> l" using kl by blast
    then show ?thesis using Crossing a1 a2 t1 fpoint.inject(2) kl proper_uprod_simps by metis
  next
    case many 
    obtain p where pdef: "n = Suc (Suc (Suc p))" 
      using many by (metis Crossing p_level.simps(2) point_level vv) 
    have KL: "new_points c (Suc (Suc (Suc p))) =
    (if odd (Suc p) then {}
     else {Crossing (Upair k l) (Suc (Suc (Suc p))) |k l.
           k \<in> new_lines c (Suc (Suc p)) \<and>
           l \<in> line_set c (Suc (Suc p)) \<and> k \<noteq> l 
           \<and> \<not> (\<exists>Y\<in>point_set c (Suc (Suc p)). fppincid c Y k \<and> fppincid c Y l \<and> p_level Y \<le> Suc (Suc p))})"
      using new_points.simps by auto
    obtain k l where kl: "P = Crossing (Upair k l) (Suc (Suc (Suc p))) \<and>
           k \<in> new_lines c (Suc (Suc p)) \<and>
           l \<in> line_set c (Suc (Suc p)) \<and> k \<noteq> l 
           \<and> \<not> (\<exists>Y\<in>point_set c (Suc (Suc p)). fppincid c Y k \<and> fppincid c Y l \<and> p_level Y \<le> Suc (Suc p))" using vv KL
      by (smt (verit, ccfv_SIG) Crossing pdef a1 empty_iff mem_Collect_eq p_level.simps(2) point_level2)
    have "k \<noteq> l" using kl by blast
    then show ?thesis using Crossing a1  by (metis a2 fpoint.inject(2) kl proper_uprod_simps)
  qed
qed

lemma point_containment: (* new_points c n is in Pi_points c *)
  fixes P c
  assumes "\<exists> n::nat. P \<in> new_points c n"
  shows "P \<in> Pi_points c"
proof -
  obtain n where 1: "P \<in> new_points c n" using assms by blast
  have 2: "new_points c n \<subseteq> Pi_points c" using Pi_points_def by blast
  show ?thesis using 1 2 by auto
qed

lemma pi_points_contents: (* anything in new_points c n is in Pi_points c *)
  fixes c n
  shows "new_points c n \<subseteq> Pi_points c"
  using Pi_points_def by auto

lemma point_set_contents: (* point_set c n is the union of new_points c i for i = 0 .. n *)
  fixes c n
  shows "point_set c n =   \<Union> ((new_points c)  ` {i::nat . i \<le> n})"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc k)
  note this
  have u1: "point_set c k =  \<Union> ((new_points c)  ` {i::nat . i \<le> k})" 
    using Suc by blast  
  have u2: "point_set c (Suc k ) = point_set c k \<union>  new_points c (Suc k)" 
    using point_set.simps by blast
  have u3: "point_set c (Suc k ) 
    = (\<Union> ((new_points c)  ` {i::nat . i \<le> k})) \<union>  new_points c (Suc k)" 
    using u1 u2  by blast
  have u4: "point_set c (Suc k ) 
    = (\<Union> ((new_points c)  ` ({i::nat . i \<le> k} \<union> {Suc k})))" 
    using u3 increase_initial_segment by blast
  have u5: "point_set c (Suc k ) 
    = (\<Union> ((new_points c)  ` ({i::nat . i \<le> (Suc k)} )))" 
    using u4 increase_initial_segment by blast   
  then show ?case using u5 by auto 
qed

lemma pi_points_contents2: (* point_set c n is a subset of Pi_points c *)
  fixes c n
  shows "point_set c n \<subseteq> Pi_points c"
  using Pi_points_def Sup_subset_mono image_mono point_set_contents top_greatest by metis

lemma line_level: (* if a line is in new_lines c n, its level is n *)
  fixes k c 
  fixes n::nat
  assumes a1: "k \<in> new_lines c n"
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

lemma line_level2: (* if a line's level is k, it's in new_lines c k *)
  fixes k c n
  assumes a1: "k \<in> Pi_lines c"
  assumes a2: "s = l_level k"
  shows  "k \<in> new_lines c s"
proof -
  obtain n where u1:"k \<in> new_lines c n" using a1 Pi_lines_def new_lines.simps by auto
  have u2: "s = n" using u1 a2 l_level.simps line_level by auto
  show ?thesis using u1 u2 by auto
qed

lemma lines_odd_or_zero: (* every line's level is either odd or zero *)
  fixes k c
  assumes a1: "k \<in> Pi_lines c"
  assumes a2: "n = l_level k"
  shows "n = 0 \<or> odd n"
proof -
  have u0: "k \<in> new_lines c n" using a1 a2 line_level2 by auto
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

lemma pi_lines_contents: (* new_lines c n is in Pi_lines c *)
  fixes c n
  shows "new_lines c n \<subseteq> Pi_lines c"
  using Pi_lines_def by auto

lemma line_set_contents: (* line_set c n is the union of all new_lines c k for k = 0:n *)
  fixes c n
  shows "line_set c n =   \<Union> ((new_lines c)  ` {i::nat . i \<le> n})"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note this
  have u1: "line_set c n =  \<Union> ((new_lines c)  ` {i::nat . i \<le> n})" using Suc by blast  
  have u2: "line_set c (Suc n ) = line_set c n \<union>  new_lines c (Suc n)" using line_set.simps by blast
  have u3: "line_set c (Suc n ) = (\<Union> ((new_lines c)  ` {i::nat . i \<le> n})) \<union>  new_lines c (Suc n)" using u1 u2  by blast
  have u4: "line_set c (Suc n ) = (\<Union> ((new_lines c)  ` ({i::nat . i \<le> n} \<union> {Suc n})))" using u3 increase_initial_segment by blast
  have u5: "line_set c (Suc n ) = (\<Union> ((new_lines c)  ` ({i::nat . i \<le> (Suc n)} )))" using u4 increase_initial_segment by blast   
  then show ?case using u5 by auto 
qed

lemma pi_lines_contents2: (* and Pi_lines c is the union of all line_set s *)
  fixes c n
  shows "line_set c n \<subseteq> Pi_lines c"
  using Pi_lines_def Union_mono line_set_contents subset_image_iff top_greatest by metis

lemma joining_line: (* there's a line between any two distinct points of a free projective plane with the right order of levels *)
  fixes P Q c
  assumes "P \<in> Pi_points c" and "Q \<in> Pi_points c"
  assumes "p_level P \<le> p_level Q"
  assumes "P \<noteq> Q"
  defines "n \<equiv> p_level Q"
  shows "\<exists>k \<in> Pi_lines c. fppincid c P k \<and> fppincid c Q k"
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
    proof (cases "\<exists> m \<in> line_set c 0 . fppincid c P m \<and> fppincid c Q m \<and> (l_level m \<le> 1)")
      case True
      then show ?thesis by (metis in_mono pi_lines_contents2)
    next
      case False
      have "new_lines c 1 = {Join (Upair S T) 1 | S T . 
        (S \<in> new_points c 0) \<and> 
        (T \<in> point_set c 0) \<and> (S \<noteq> T) \<and>
          \<not> (\<exists>k \<in> line_set c 0 . fppincid  c S k \<and> fppincid c T k \<and> (l_level k \<le> 1))}" 
        using new_lines.cases by simp
      then have "Join (Upair P Q) 1 \<in> new_lines c 1"
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
    have u0: "Q \<in> new_points c n" using assms(2) n_def point_level2 by auto
    have u1: "Q \<in> point_set c n" using u0 point_set.simps by (metis UnCI point_set.elims)
    have u2: "P \<in> new_points c (p_level P)" by (simp add: assms(1) point_level2)
    have u3: "P \<in> point_set c  (p_level P)" by (metis UnCI point_set.elims u2)
    have u4: "P \<in> point_set c  n" 
      by (smt (verit, best) UnCI assms(3) in_mono lift_Suc_mono_le n_def point_set.elims point_set.simps(1,2) subsetI u2)
    have u5: "even n" using assms(2) points_even n_def by blast
    have u6: "new_lines c (Suc n) = new_lines c (Suc (Suc q))" using uu by blast 
    have u7: "new_lines c (Suc n) = 
  (if (even q) then {} else
   {Join (Upair S T) (Suc (Suc q)) | S T . 
    (S \<in> new_points c (Suc q)) \<and> 
    (T \<in> point_set c (Suc q)) \<and> (S \<noteq> T) \<and>
    \<not> (\<exists>k \<in> line_set c (Suc q) . fppincid  c S k \<and> fppincid c T k \<and> (l_level k \<le> (Suc q)))})" using u6 by simp
    then have u8: "new_lines c (Suc n) = 
     {Join (Upair S T) (Suc (Suc q)) | S T . 
      (S \<in> new_points c (Suc q)) \<and> 
      (T \<in> point_set c (Suc q)) \<and> (S \<noteq> T) \<and>
      \<not> (\<exists>k \<in> line_set c (Suc q) . fppincid  c S k \<and> fppincid c T k \<and> (l_level k \<le> (Suc q)))}" using u5 uu by auto
    let ?C = "\<exists>k \<in> line_set c n . fppincid  c P k \<and> fppincid c Q k \<and> (l_level k \<le> n)"
    show "\<exists>k\<in>Pi_lines c. fppincid c P k \<and> fppincid c Q k "
    proof (cases ?C)
      case True
      obtain k where u9: "k \<in> line_set c n \<and> fppincid c P k \<and> fppincid c Q k \<and> l_level k \<le> n" using True by blast
      have "k \<in> Pi_lines c " using u9 pi_lines_contents2 by blast
      then show ?thesis using u9 by blast
    next
      case False
      have v1: "Join (Upair P Q) (Suc n) \<in> new_lines c (Suc n)" using u8 False using u0 u4 uu  assms(4) by force
      let ?L = "Join (Upair P Q) (Suc n)"
      have v2:  "?L \<in> Pi_lines c" using v1 Pi_lines_def by blast
      have v3:  "fppincid c P ?L \<and> fppincid c Q ?L"
      by (smt (verit, best) fline.distinct(1) fline.inject(2) fppincid.elims(3))
      then show ?thesis using v2 by blast
    qed
  qed
qed

theorem free_planes_join:  (* there's a line between any two distinct points of a free projective plane *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes c
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "card CPoints \<ge> 4"
  fixes P Q
  assumes "P \<in> Pi_points c"
  assumes "Q \<in> Pi_points c"
  assumes "P \<noteq> Q"
  shows " \<exists>k. k \<in> Pi_lines c \<and> fppincid c P k \<and>  fppincid c Q k"
  using assms joining_line nle_le by metis

lemma line_point_levels: (* points of join P Q, a line at level n, are either P or Q or have level > n *)
 fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes c
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "card CPoints \<ge> 4"
  fixes P A1 B1 n
  assumes "P \<in> Pi_points c"
  assumes "Join (Upair A1 B1) n \<in> Pi_lines c"
  assumes "fppincid c P (Join (Upair A1 B1) n)"
  shows "P = A1 \<or> P = B1 \<or> (p_level P \<ge> n)" 
proof (cases P)
  case (Base_point x1)
  then show ?thesis using assms(5) by auto
next
  case (Crossing x21 x22)
  then show ?thesis sorry
qed
  (*
fun fppincid::  " ('a, 'b) plane_r \<Rightarrow>  ('a, 'b) fpoint \<Rightarrow> ('a, 'b) fline \<Rightarrow> bool" where
(* if lines meet in pi0, they meet in Pi: *)
  "fppincid (c:: ('a, 'b) plane_r) (Base_point P) (Base_line m) = (incid c  P m)"  
(* if a basepoint incid a join-line, it must be one of the two ends of the join *) 
| "fppincid (c:: ('a, 'b)  plane_r) (Base_point P) (Join x n2) = (\<exists> A1 B1 . (x = Upair A1 B1) 
 \<and> (A1 = (Base_point P) \<or> (B1 = (Base_point P))))"
(* if a baseline incid a crossing, it must be one of the two crossing lines *)
| "fppincid (c:: ('a, 'b) plane_r) (Crossing u n1) (Base_line m) = (\<exists> l k . (u = Upair l k) 
 \<and> (l = (Base_line m)   \<or> (k =  (Base_line m))))" 

(* If a crossing lies on a join...then it must be one of the two points that formed the join *)
(* this is not correct! for that join might later be extended by further crossings with other lines *)
(*"fppincid CPoints CLines (incid) (Crossing u n1)  (Join x n2) = (\<exists> A1 B1 . (x = Upair A1 B1) 
 \<and> (A1 = (Crossing u n1)   \<or> (B1 = (Crossing u n1))))" *)
| "fppincid (c:: ('a, 'b) plane_r) (Crossing u n1)  (Join x n2) = (
     ((n1 < n2) \<and> 
      (\<exists> A1 B1 . x = Upair A1 B1 \<and> (A1 = Crossing u n1 \<or> B1 = Crossing u n1))) 
     \<or> 
     (\<exists> k m . u = Upair k m \<and> k = Join x n2 \<or> m = Join x n2)
   )"   

*)


(* A theorem we don't know how to prove, and Hartshorne finesses it! *)
theorem free_planes_unique_join: (* two distinct points are joined by a UNIQUE line ... still unproved *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes c U
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "U \<subseteq> CPoints"
  assumes "card U \<ge> 4"
  fixes P Q
  assumes "P \<in> Pi_points c"
  assumes "Q \<in> Pi_points c"
  assumes "P \<noteq> Q"
  shows " \<exists>!k. k \<in> Pi_lines c \<and> fppincid c P k \<and> fppincid c Q k"
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

lemma line_containment: (* anything in new_lines c n is in Pi_lines c *)
  fixes k c
  assumes "\<exists> n::nat. k \<in> new_lines c n"
  shows "k \<in> Pi_lines c"
proof -
  obtain n where 1: "k \<in> new_lines c n" using assms by blast
  have 2: "new_lines c n \<subseteq> Pi_lines c" using Pi_lines_def by blast
  show ?thesis using 1 2 by auto
qed

lemma crossing_point: (* any two distinct lines in Pi_lines c meet at a point in Pi_points *)
  fixes k m c
  assumes "k \<in> Pi_lines c" and "m \<in> Pi_lines c"
  assumes "l_level k \<le> l_level m"
  assumes "k \<noteq> m"
  defines "n \<equiv> l_level m"
  shows "\<exists> P \<in> Pi_points c . fppincid c P k \<and> fppincid c P m"
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
    proof (cases "\<exists> P \<in> point_set c 0 . fppincid c P k \<and> fppincid c P m \<and> (p_level P \<le> 1)")
      case True
      then show ?thesis  using pi_points_contents2 by blast
    next
      case False
      have p0: "new_points c 1 =  {}"  using new_points.cases by simp
      have p1: "new_points c 2 = {Crossing (Upair k l) (Suc (Suc 0)) | k l . 
    ((k \<in> new_lines c 0) \<or> (k \<in> new_lines c (Suc 0))) \<and> 
    (l \<in> line_set c (Suc 0)) \<and> (k \<noteq> l) \<and>
    \<not> (\<exists>Y \<in> point_set c (Suc 0) . fppincid c Y k \<and> fppincid c Y l \<and> (p_level Y \<le> (Suc 0)))}"  
      by (metis new_points.simps(3) numeral_2_eq_2)
      have "Crossing (Upair k m) 2 \<in> new_points c 2" using p1 False
        by (smt (verit, del_insts) 1 One_nat_def UnCI assms(1,2,4) diff_Suc_1 line_level2 
          line_set.elims mem_Collect_eq n_def numeral_2_eq_2 p0 point_set.simps(2)
          sup_bot.right_neutral zero)
      then show ?thesis by (metis 2 3 fppincid.simps(3) point_containment)
    qed
  next
    case one (* higher level line has level 1 *)
    show ?thesis
    proof (cases "\<exists> P \<in> point_set c 0 . fppincid c P k \<and> fppincid c P m \<and> (p_level P \<le> 1)")
      case True
      then show ?thesis  using pi_points_contents2 by blast
    next
      case False
      have q0: "new_points c 1 = {}" by simp
      have q2: "point_set c 1 = point_set c 0" by auto
      have q3: "\<not> (\<exists> P \<in> point_set c 1 .  fppincid c P k \<and> fppincid c P m \<and> (p_level P \<le> 1))" using False q2 by blast
      have q4: "new_points c 2  = {Crossing (Upair k l) (Suc (Suc 0)) | k l . 
        ((k \<in> new_lines c 0) \<or> (k \<in> new_lines c (Suc 0))) \<and> 
        (l \<in> line_set c (Suc 0)) \<and> (k \<noteq> l) \<and> 
        \<not> (\<exists>Y \<in> point_set c (Suc 0) . fppincid c Y k \<and> fppincid c Y l \<and> (p_level Y \<le> (Suc 0)))}"   
        by (metis new_points.simps(3) numeral_2_eq_2)
      have q5: "Crossing (Upair k m) 2 \<in> new_points c 2" 
      by (smt (verit) One_nat_def UnCI assms(1,2,3,4) diff_is_0_eq line_level2 line_set.simps(2) lines_odd_or_zero mem_Collect_eq n_def new_points.simps(3) numeral_2_eq_2
          odd_Suc_minus_one one q3)
      then show ?thesis 
        by (metis Pi_points_def UnionI fppincid.simps(3,4) l_level.elims rangeI)
    qed
  next
    case many (*higher-level line has level 2 or greater *)
    obtain q where uu: "n = Suc q" using many by blast
    have u0: "m \<in> new_lines c n" by (simp add: assms(2) line_level2 n_def)
    have u1: "m \<in> line_set c n" using u0 line_set.simps by (metis UnCI point_set.elims)
    have u2: "k \<in> new_lines c (l_level k)" by (simp add: assms(1) line_level2)
    have u3: "k \<in> line_set c  (l_level k)" by (metis UnCI line_set.elims u2)
    have u4: "k \<in> line_set c  n" using assms(3) line_set_contents n_def u2 by fastforce 
    have u5: "odd n" using assms(2) points_even n_def many u0 by fastforce
    have u6: "new_points c (Suc n) = new_points c (Suc (Suc q))" using uu by blast 
    then have u7: "new_points c (Suc n) = (if (odd q) then {} else 
      {Crossing (Upair k l) (Suc (Suc q)) | k l . 
       (k \<in> new_lines c (Suc q)) \<and> 
       (l \<in> line_set c (Suc q)) \<and> (k \<noteq> l) \<and>
       \<not> (\<exists>Y \<in> point_set c (Suc q) . fppincid c Y k \<and> fppincid c Y l \<and> (p_level Y \<le> (Suc q)))})"
    using many uu by force
    then have u8: "new_points c (Suc n) = 
     {Crossing (Upair k l) (Suc (Suc q)) | k l . 
       (k \<in> new_lines c (Suc q)) \<and> 
       (l \<in> line_set c (Suc q)) \<and> (k \<noteq> l) \<and>
       \<not> (\<exists>Y \<in> point_set c (Suc q) . fppincid c Y k \<and> fppincid c Y l \<and> (p_level Y \<le> (Suc q)))}" using u5 uu by auto
    let ?C = "\<exists>Y \<in> point_set c n . fppincid c Y k \<and> fppincid c Y m \<and> (p_level Y \<le> n)"
    show "\<exists>P \<in> Pi_points c. fppincid c P k \<and> fppincid c P m"
    proof (cases ?C)
      case True
      obtain P where u9: "P \<in> point_set c n \<and> fppincid c P k \<and> fppincid c P m \<and> p_level P \<le> n" using True by blast
      have "P \<in> Pi_points c" using u9 pi_points_contents2 by blast
      then show ?thesis using u9 by blast
    next
      case False
      have v1: "Crossing (Upair k m) (Suc n) \<in> new_points c (Suc n)" 
        using u8 False u0 u4 uu assms(4) by force
      let ?P = "Crossing (Upair k m) (Suc n)"
      have v2:  "?P \<in> Pi_points c" using v1 Pi_points_def by blast
      have v3:  "fppincid c ?P k \<and> fppincid c ?P m"
      by (smt (verit, best) fpoint.distinct(1) fpoint.inject(2) fppincid.elims)
      then show ?thesis using v2 by blast
    qed
  qed
qed

(* all crossings in CPoints have levels > 0 *)
theorem crossing_level: (* of P is a crossing of level s in  Pi_points, then s > 0 *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes c
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "P \<in> Pi_points c"
  assumes "P = Crossing (Upair m k) s"
  shows "s > 0"
proof -
  obtain n where  oh: "P \<in> new_points c n" using Pi_points_def assms(2) by blast
  show ?thesis
  proof (cases)
    assume "n > 0"
    then show ?thesis using oh  using assms(3) point_level by fastforce
  next
    assume ah: "\<not> n > 0"
    have "n = 0" using ah by simp
    then have "new_points c n =  {Base_point Q  | Q . Q \<in> Points c}" using new_lines.cases by simp
    then have a: False using assms(3) oh by blast
    show ?thesis using a FalseE [of ?thesis] by blast
  qed
qed
                                                                     
theorem base_in_join: (* if a Join line contains a basepoint, it's one of the two generators of the join *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes c
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "k \<in> Pi_lines c"
  assumes "P = Base_point A"
  assumes "fppincid c P k"
  assumes "k = Join (Upair J H) s"
  shows "P = J \<or> P = H"
proof -
  obtain n where "k \<in> new_lines c n" using Pi_lines_def assms by blast
  have 1: "n \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (n \<noteq> 0)"
    then have "n = 0" by blast
    then have "new_lines c n =  {Base_line s | s . s \<in> Lines c}" using new_lines.simps by blast
    then have "k \<notin> new_lines c n" using assms by blast
    thus "False" using assms \<open>k \<in> new_lines c n\<close> by blast
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
  fixes c P Q
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  shows "Join (Upair P Q) s \<in> Pi_lines c \<Longrightarrow> p_level P = s-1 \<or> p_level Q = s-1"
proof - 
  let ?k = "Join (Upair P Q) s"
  assume ah: "?k \<in> Pi_lines c"
  have 0: "?k \<in> new_lines c s" using ah line_level2 by fastforce
  have 1: "s > 0"  using 0  gr_zeroI by fastforce
  obtain n where 2: "s = Suc n" using 1  using gr0_conv_Suc by blast
  show ?thesis
  proof (cases n)
    case 0
    have "new_lines c s =  {Join (Upair S T) 1 | S T . 
    (S \<in> new_points c 0) \<and> 
    (T \<in> point_set c 0) \<and> (S \<noteq> T) \<and>
    \<not> (\<exists>k \<in> line_set c 0 . fppincid  c S k \<and> fppincid c T k \<and> (l_level k \<le> 1))}" 
    using "0" "2" by auto
    then show ?thesis 
    by (smt (z3) One_nat_def Upair_inject ah diff_Suc_1 fline.inject(2) l_level.simps(2) line_level2 mem_Collect_eq point_level)
  next
    case (Suc p)
(* new_lines c (Suc (Suc n)) = *)
    have nld: "new_lines c n =  (if (even n) then {} else 
      {Join (Upair S T) (Suc (Suc n)) | S T . 
      (S \<in> new_points c (Suc n)) \<and> 
      (T \<in> point_set c (Suc n)) \<and>  (S \<noteq> T) \<and>
      \<not> (\<exists>k \<in> line_set c (Suc n) . fppincid  c S k \<and> fppincid c T k \<and> (l_level k \<le> (Suc n)))})"
      by (metis "2" One_nat_def Suc ah even_Suc l_level.simps(2) lines_odd_or_zero nat.distinct(1) new_lines.elims odd_one)
    then show ?thesis 
    proof (cases "odd n")
      case True
      have s0: "new_lines c s = {}" using nld True  by (simp add: "2" Suc)
      then have False using 0 by blast
      then show ?thesis by blast
    next
      case False
      have r0: "even n" using False by blast
      then have nld2: "new_lines c (Suc (Suc p)) = 
       (if (even p) then {} else 
       {Join (Upair S T) (Suc (Suc p)) | S T . 
       (S \<in> new_points c (Suc p)) \<and> 
       (T \<in> point_set c (Suc p)) \<and>  (S \<noteq> T) \<and>
       \<not> (\<exists>k \<in> line_set c (Suc p) . fppincid  c S k \<and> fppincid c T k \<and> (l_level k \<le> (Suc p)))})" by simp
      then have nld3: "new_lines c (Suc (Suc p)) = 
       {Join (Upair S T) (Suc (Suc p)) | S T . 
       (S \<in> new_points c (Suc p)) \<and> 
       (T \<in> point_set c (Suc p)) \<and>  (S \<noteq> T) \<and>
       \<not> (\<exists>k \<in> line_set c (Suc p) . fppincid  c S k \<and> fppincid c T k \<and> (l_level k \<le> (Suc p)))}" using r0 Suc by auto
      then have nld4: "new_lines c (Suc n) = 
       {Join (Upair S T) (Suc n) | S T . 
       (S \<in> new_points c n) \<and> 
       (T \<in> point_set c n) \<and>  (S \<noteq> T) \<and>
       \<not> (\<exists>k \<in> line_set c n . fppincid  c S k \<and> fppincid c T k \<and> (l_level k \<le> n))}" using r0 Suc by auto
      then have nld5: "new_lines c s = 
       {Join (Upair S T) (Suc n) | S T . 
       (S \<in> new_points c n) \<and> 
       (T \<in> point_set c n) \<and>  (S \<noteq> T) \<and>
       \<not> (\<exists>k \<in> line_set c n . fppincid  c S k \<and> fppincid c T k \<and> (l_level k \<le> n))}" using "2" by fastforce
      then obtain S T where r1: "?k = Join (Upair S T) (Suc n) \<and> (S \<in> new_points c n) \<and> 
       (T \<in> point_set c n)" using 0 by auto
      then have "S \<in> new_points c n" by blast
      then have "p_level S = n" by (simp add:point_level)
      then have "p_level S = s-1" by(simp add:2)
      then show ?thesis  using r1 by auto
    qed
  qed
qed

theorem base_in_base: (* if a base-point (created from plane_r point A) is in a base-line (from plane_r line m), then A was in m already. *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes c s t m A
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "k = Base_line m"
  assumes "P = Base_point A"
  assumes "fppincid c P k"
  shows "incidx A m"
  using assms(1,2,3,4) by force

theorem base_pair: (* if a line contains two distinct base points, it's a base line or the join of two base points at level 1 *) 
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes c s1 s2 t A B k
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "k \<in> Pi_lines c"
  assumes "P = Base_point A"
  assumes "Q = Base_point B"
  assumes "P \<in> Pi_points c"
  assumes "Q \<in> Pi_points c"
  assumes "A \<noteq> B"
  assumes "fppincid c P k"
  assumes "fppincid c Q k"
  shows "k \<in> new_lines c 0 \<or> k = (Join (Upair P Q) 1)"
proof (cases k)
  case (Base_line x11)
  then show ?thesis  using assms(2) line_level2 by force
next
  case (Join pts s)
  obtain H K where 0: "pts = Upair H K" using uprod_exhaust by auto
(* have 1: "P = H \<or> P = K" using Join \<open>pts = Upair H K\<close> assms(3,6) by force
  have 2: "Q = H \<or> Q = K" using Join \<open>pts = Upair H K\<close> assms(4,7) by force
  have 3: "k = Join (Upair P Q) s"  using 0 1 2 assms(3,4,5) Join by fastforce *)
  then show ?thesis 
  by (metis Join One_nat_def Suc_leI Upair_inject assms(1,2,3,4,7,8,9) base_in_join diff_is_0_eq fpoint.inject(1) join_level
      l_level.simps(2) line_level2 nle_le not_gr0 p_level.simps(1)) 
qed


theorem free_planes_meet: (* two distinct lines have a point in common in fpp where base plane_r has at least 4 pts *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes c
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "card CPoints \<ge> 4"
  fixes k m
  assumes "k \<in> Pi_lines c"
  assumes "m \<in> Pi_lines c"
  assumes "k \<noteq> m"
  shows " \<exists>P. P \<in> Pi_points c \<and>
               fppincid c P k \<and>
               fppincid c P m"
  by (metis assms(3,4,5) crossing_point linorder_linear)

theorem non_collinear_persistence:(*if P Q R in the configuration are not collinear, then they are also not collinear in the free projective plane. *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes P Q R
  fixes c
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "card {P, Q, R} = 3"
  assumes "{P, Q, R} \<subseteq> CPoints"
  shows "\<not> (\<exists>k \<in> CLines . incidx P k \<and> incidx Q k \<and> incidx R k) \<Longrightarrow> 
         \<not> (\<exists>m \<in> Pi_lines c . fppincid c (Base_point P) m \<and> fppincid c (Base_point Q) m \<and> fppincid c (Base_point R) m)" 
proof (erule contrapos_np)
  assume " \<not> \<not> (\<exists>m\<in>Pi_lines c. fppincid c (Base_point P) m \<and> fppincid c (Base_point Q) m \<and> fppincid c (Base_point R) m) "
  then obtain m where  ch: "m\<in>Pi_lines c \<and> fppincid c (Base_point P) m \<and> fppincid c (Base_point Q) m \<and> fppincid c (Base_point R) m" by blast
    then show "\<exists>k\<in>CLines. incidx P k \<and> incidx Q k \<and> incidx R k" 
  proof (cases m)
    case (Base_line L)
    have "incidx P L \<and> incidx Q L \<and> incidx R L"  using Base_line assms ch by auto
    then show ?thesis using Base_line  assms(1) ch line_level2 by fastforce
  next
    case (Join Pair n)
    obtain S T where b: "Pair = (Upair S T)" using uprod_exhaust by auto
    then have "n \<noteq> 0" (* do I need this? *)
    by (smt (verit) Join ch fline.distinct(1) l_level.simps(2) line_level2 mem_Collect_eq new_lines.simps(1))
    have belong: "fppincid c (Base_point X) (Join (Upair S T) n) = (\<exists> A1 B1 . ((Upair S T) = Upair A1 B1) 
 \<and> (A1 = (Base_point X) \<or> (B1 = (Base_point X))))" by simp 
    then have "... = (S = (Base_point X)) \<or> (T = (Base_point X))" by auto 
    then have u: "fppincid c (Base_point X) (Join (Upair S T) n) = (S = (Base_point X)) \<or> (T = (Base_point X))" for X by auto 
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
  shows "\<exists> A B C  . A \<in> U \<and> B \<in> U \<and> C \<in> U  \<and> distinct [A,B,C]"
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
  show ?thesis using aa bb cc by auto
qed

lemma fpp_two_points_zero: (* a level zero line contains at least two points: needs 4-elt set U! *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes incidx::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  fixes c p
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "k \<in> Pi_lines c"
  assumes "l_level k = 0"
  assumes "U \<subseteq> CPoints"
  assumes "card U = 4"
  assumes imp: "\<And> P Q R . ((distinct [P,Q,R]) \<and> ({P, Q, R} \<subseteq> U)) \<Longrightarrow>  \<not> (projective_plane_data.pcollinear c P Q R)" 

  shows "\<exists> P Q . P \<noteq> Q \<and> fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c"
proof (rule ccontr)
  assume ch: "\<not> (\<exists> P Q . P \<noteq> Q \<and> fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c)"
  let ?kpts = "{X . fppincid c X k \<and> X \<in> Pi_points c}"
  have kpchoice: "?kpts = {} \<or> (\<exists> R . ?kpts = {R})" using ch by blast
  then have "card ?kpts < 2" by (metis (mono_tags, lifting) card.empty card.insert finite.intros(1) insert_absorb less_2_cases_iff)
  let ?g = "\<lambda> x .  Base_point x"
  let ?Upts = "?g ` U"
  have Upts_pi: "?Upts \<subseteq> Pi_points c" 
  by (metis (mono_tags, lifting) assms(1,4) image_subsetI mem_Collect_eq new_points.simps(1) pi_points_contents select_convs(1)
      subsetD)
  have "card ?Upts = 4"  
    by (simp add: assms(5) card_image inj_on_def)
  have "card (?Upts - ?kpts) > 2"
  by (metis (lifting) Diff_empty Diff_insert0 \<open>card (Base_point ` U) = 4\<close> add_2_eq_Suc add_diff_cancel_left' card_Diff_singleton
      diff_is_0_eq kpchoice lessI linorder_not_le numeral_Bit0 plus_1_eq_Suc zero_neq_numeral)
  then obtain P Q R where pqr_def: "P \<in> (?Upts - ?kpts) \<and> Q \<in> (?Upts - ?kpts) \<and> R \<in> (?Upts - ?kpts) \<and> 
    distinct [P, Q, R]" using three_elements by blast
  have "{P, Q, R} \<subseteq> ?Upts" using  pqr_def by blast
  then have "{P,Q,R} \<subseteq> Pi_points c" using Upts_pi by order
  then have not_k: "(\<not> (fppincid c P k)) \<and> (\<not> (fppincid c Q k)) \<and> (\<not> (fppincid c R k))" using pqr_def by blast
  obtain uP uQ uR where upqr_def: "P = Base_point uP \<and> Q = Base_point uQ \<and> R = Base_point uR \<and>  
    distinct [uP, uQ, uR] \<and> uP \<in> U \<and> uQ \<in> U \<and> uR \<in> U" using pqr_def by force
  then have "\<not> (projective_plane_data.pcollinear c uP uQ uR)" using assms by blast
  then have jj: "\<not> (\<exists>s\<in>CLines. incidx uP s \<and> incidx uQ s \<and> incidx uR s)" 
    using upqr_def assms(4) in_mono projective_plane_data.pcollinear_def
    by (smt (verit, best) assms(1) empty_iff projective_plane_data_def select_convs(1,2,3))

  thm non_collinear_persistence [of c CPoints CLines incidx uP uQ uR ]

  then have "\<not> (\<exists>m\<in>Pi_lines c. fppincid c (Base_point uP) m \<and> fppincid c (Base_point uQ) m \<and> fppincid c (Base_point uR) m)" 
    using non_collinear_persistence [of c CPoints CLines incidx uP uQ uR ] assms(1,4) upqr_def by auto 
  then have non_co: "\<not> (\<exists>m\<in>Pi_lines c. fppincid c P m \<and> fppincid c Q m \<and> fppincid c R m)" using upqr_def by blast

  (* so P, Q, R, are distinct noncollinear and not on k; use them to construct two points on k *)
  obtain PQ where pq_def: "fppincid c P PQ \<and> fppincid c Q PQ \<and> PQ \<in> Pi_lines c" 
    by (metis One_nat_def \<open>{P, Q, R} \<subseteq> Pi_points c\<close> add_Suc distinct_length_2_or_more fpoint.inject(1) insert_subset joining_line
      le_add1 nat.inject p_level.simps(1) plus_1_eq_Suc upqr_def)
  obtain PR where pr_def: "fppincid c P PR \<and> fppincid c R PR  \<and> PR \<in> Pi_lines c" 
    by (metis One_nat_def \<open>{P, Q, R} \<subseteq> Pi_points c\<close> add_Suc distinct_length_2_or_more fpoint.inject(1) insert_subset joining_line
      le_add1 nat.inject p_level.simps(1) plus_1_eq_Suc upqr_def)
  obtain k1 where k1_def: "fppincid c k1 PQ \<and> fppincid c k1 k \<and> k1 \<in> Pi_points c"
    by (metis assms(2,3) crossing_point le0 not_k pq_def)
  obtain k2 where k2_def: "fppincid c k2 PR \<and> fppincid c k2 k \<and> k2 \<in> Pi_points c" 
    by (metis assms(2,3) crossing_point k1_def less_eq_nat.simps(1) pr_def)
  have "k1 \<noteq> k2" 
  by (smt (verit) Diff_iff Upts_pi \<open>\<And>thesis. (\<And>PQ. fppincid c P PQ \<and> fppincid c Q PQ \<and> PQ \<in> Pi_lines c \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
      assms(1,2,4,5) ch crossing_point free_planes_unique_join nle_le non_co not_k pqr_def subset_iff)
  then have "k1 \<noteq> k2 \<and>
          fppincid c k1 k \<and>
          fppincid c k2 k \<and> k1 \<in> Pi_points c \<and> k2 \<in> Pi_points c" using k1_def k2_def by blast
  have f:False using \<open>k1 \<noteq> k2\<close> ch k1_def k2_def by blast
  show "\<nexists>P Q. P \<noteq> Q \<and> fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c \<Longrightarrow> False " using f by blast
qed


lemma fpp_two_points_one: (* a level-one line contains at least two points *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes c
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "k \<in> Pi_lines c"
  assumes "l_level k = 1"
  shows "\<exists> P Q . P \<noteq> Q \<and> fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c"
proof -
thm line_level2 
thm line_level2 [of k c 1] 
  have "k \<in> new_lines c 1" using assms line_level2 [of k c 1] by presburger
  then obtain S T where join_def: "k = Join (Upair S T) 1 \<and> S \<noteq> T" and contents: "S \<in> Pi_points c \<and> T \<in> Pi_points c"  using new_lines.simps
    by (smt (verit, ccfv_threshold) One_nat_def mem_Collect_eq point_containment point_set.simps(1))
  then have "fppincid c S k \<and> fppincid c T k \<and> S \<in> Pi_points c \<and> T \<in> Pi_points c"  using join_def 
    using fppincid.elims(3) by blast
  then show ?thesis  using join_def by blast
qed

lemma fpp_two_points_two: (* a level two or higher line contains at least two points *)
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes c p
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "k \<in> Pi_lines c"
  assumes "l_level k \<ge> 2"
  assumes "p = l_level k"
  shows "\<exists> P Q . P \<noteq> Q \<and> fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c"
proof -
  have kloc: "k \<in> new_lines c p" using assms line_level2  by blast
  have n2: "p \<ge> 2" using assms by blast
  show ?thesis
  proof (cases "even p")
    case True
    have False using True new_lines.simps assms(2,4) lines_odd_or_zero n2 by fastforce
    then show ?thesis by auto
  next
    case False
    obtain n where "p = Suc (Suc n)" using n2 
      by (metis One_nat_def Suc_1 Suc_le_D Suc_le_mono)
    then obtain S T where kdef: "k = Join (Upair S T) (Suc (Suc n))\<and> 
    (S \<in> new_points c (Suc n)) \<and> 
    (T \<in> point_set c (Suc n)) \<and>  (S \<noteq> T)" 
      by (smt (verit, best) emptyE kloc mem_Collect_eq new_lines.simps(3))
    then have "fppincid c S k \<and> fppincid c T k \<and> S \<in> Pi_points c \<and> T \<in> Pi_points c"  
      using kdef fppincid.elims(3)
      by (smt (verit) fline.simps(4) fppincid.simps(2) pi_points_contents2 point_containment subsetD)
    then show ?thesis  using kdef by blast
  qed
qed

lemma fpp_two_points:
  fixes CPoints::"'a set"
  fixes CLines::"'b set"
  fixes c p
  assumes "(c::(('a, 'b) plane_r)) = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>"
  assumes "k \<in> Pi_lines c"
  assumes "p = l_level k"
  assumes "U \<subseteq> CPoints"
  assumes "card U = 4"
  assumes imp: "\<And> P Q R . ((distinct [P,Q,R]) \<and> ({P, Q, R} \<subseteq> U)) \<Longrightarrow>  \<not> (projective_plane_data.pcollinear c P Q R)" 
  shows "\<exists> P Q . P \<noteq> Q \<and>  fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c"
proof -
  consider (zero) "p = 0" | (one) "p = 1" | (many) "p \<ge> 2" by fastforce
  then have "\<exists> P Q . P \<noteq> Q \<and>  fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c"
  proof cases
    case zero
    then show ?thesis using fpp_two_points_zero [of c CPoints CLines incidx k U] assms by auto
  next
    case one
    then show ?thesis using fpp_two_points_one [of c CPoints CLines incidx k] assms by auto
  next
    case many
    then show ?thesis using fpp_two_points_two [of c CPoints CLines incidx k p] assms by auto
  qed
  then show ?thesis by auto
qed


(* ======TO BE MOVED UP TO THE START LATER ==== *)
end


