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
    S3: "\<lbrakk>k \<in> Lines; H \<in> Planes\<rbrakk> \<Longrightarrow> (\<exists>P. P \<in> k \<and> P \<in> H)" and
    S4: "\<lbrakk>H \<in> Planes; N \<in> Planes \<rbrakk> \<Longrightarrow> (\<exists>k \<in> Lines. k \<subseteq> H \<and> k \<subseteq> N)" and
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
    \<and> S \<in> Points \<and> \<not> coplanar P Q R S \<and> \<not> collinear P Q R 
    \<and> \<not> collinear P Q S \<and> \<not> collinear P R S \<and> \<not> collinear Q R S"
  shows "distinct[P,Q,R,S]" 
  using assms S2a distinct4_def unfolding coplanar_def by metis

lemma collinear_commute:
  fixes P Q R
  assumes "collinear P Q R"
  shows "collinear Q P R \<and> collinear P R Q"
  using assms collinear_def by auto

lemma join_commute:
  fixes P Q
  assumes "P \<in> Points" and "Q \<in> Points" and "P \<noteq> Q"
  shows "(join P Q) = (join Q P)"
  using assms S1a S1b by auto

lemma joins_eq_collinear:
  fixes P Q R
  assumes "P \<in> Points" and "Q \<in> Points" and "R \<in> Points"
  assumes "P \<noteq> Q" and "Q \<noteq> R"
  assumes "(join P Q) = (join Q R)"
  shows "collinear P Q R" 
  using assms S1a collinear_def by auto
text \<open>\done\<close>

lemma point_outside_plane: (* for any plane H, there's a point P not on it *)
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
  from kdef have "k \<subseteq> H \<inter> K" by blast
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

text \<open>\robert\<close>
lemma S2_exists_unique:
  fixes P Q R
  assumes "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points"
  assumes "\<not> collinear P Q R"
  shows "\<exists>!H. H \<in> Planes \<and> P \<in> H \<and> Q \<in> H \<and> R \<in> H" 
  using assms S2a S2b by blast

lemma collinear_join [iff] :
  fixes P Q X
  assumes "P \<in> Points \<and> Q \<in> Points \<and> X \<in> Points"
  assumes "P \<noteq> Q"
  shows "collinear P Q X \<longleftrightarrow> X \<in> join P Q"
  using assms S1a S1b unfolding collinear_def by auto

lemma same_joins:
  fixes a b x y
  assumes "a \<in> Points \<and> b \<in> Points \<and> x \<in> Points \<and> y \<in> Points"
  assumes "x \<in> join a b \<and> y \<in> join a b"
  assumes "distinct[a,b,x,y]"
  shows "join x y = join a b"
  using assms S1a S1b distinct4_def by metis

lemma vanadium1:
  fixes a b L
  assumes "a \<in> Points \<and> b \<in> Points \<and> L \<in> Lines"
  assumes "a \<noteq> b"
  assumes "a \<in> L \<and> b \<in> L"
  shows "L = join a b"
  using assms S1b by auto

lemma vanadium2:
  fixes a b c P Q 
  assumes "a \<in> Points \<and> b \<in> Points\<and> c \<in> Points \<and> P \<in> Planes \<and> Q \<in> Planes"
  assumes "\<not> collinear a b c" 
  assumes "a \<in> P \<and> b \<in> P \<and> c \<in> P" 
  assumes "a \<in> Q \<and> b \<in> Q \<and> c \<in> Q" 
  assumes "distinct[a,b,c]" 
  shows "P = Q"
  using assms collinear_join S2a S2b by metis

lemma vanadium3:
  fixes x y P Q
  assumes "x \<in> Points \<and> y \<in> Points \<and> P \<in> Planes \<and> Q \<in> Planes"
  assumes "x \<in> P \<and> x \<in> Q \<and> y \<in> P \<and> y \<in> Q"
  assumes "x \<noteq> y"
  shows "P = Q \<or> P \<inter> Q = join x y"
proof -
  obtain L where L_facts: "L \<in> Lines \<and> L \<subseteq> P \<and> L \<subseteq> Q" using S4 assms by metis
  then obtain a b where h0: "a \<in> Points \<and> b \<in> Points \<and> a \<noteq> b \<and> a \<in> L \<and> b \<in> L" 
    using S6 S0a unfolding distinct3_def by metis
  then have h1: "L = join a b" using L_facts S1b by auto
  show ?thesis
  proof (cases "\<exists>p. (p \<in> Points \<and> p \<notin> L \<and> p \<in> P \<and> p \<in> Q)")
    case True
    then obtain p where p_facts: "(p \<in> Points \<and> p \<notin> L \<and> p \<in> P \<and> p \<in> Q)" by auto
    then have "distinct[a,b,p]" using h0 by auto
    then show ?thesis using assms h0 h1 p_facts L_facts vanadium2 [of a b p P Q] by blast
  next
    case nexistp: False
    then have h2: "P \<inter> Q = L" using assms L_facts crossing_planes S0b by auto
    then have "join a b = join x y" using assms nexistp h1 L_facts S1b by metis
    then show ?thesis using h1 h2 by auto
  qed
qed

lemma vanadium4:
  fixes x y z w
  assumes "x \<in> Points \<and> y \<in> Points \<and> z \<in> Points \<and> w \<in> Points"
  assumes "distinct[x,y,z,w]"
  assumes "\<not> collinear x y z \<and> \<not> collinear x y w"
  shows "(plane_through x y z) = (plane_through x y w)
    \<or> (plane_through x y z) \<inter> (plane_through x y w) = (join x y)"
proof -
  let ?P = "plane_through x y z" let ?Q = "plane_through x y w"
  have "x \<in> ?P \<and> y \<in> ?P \<and> x \<in> ?Q \<and> y \<in> ?Q" using S2a assms by auto
  then show ?thesis using assms vanadium3 S2a distinct4_def by metis
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma choose_subset_helper:
  fixes X Y Z W
  assumes "X \<in> Points \<and> Y \<in> Points \<and> Z \<in> Points
    \<and> W \<in> Points \<and> \<not> coplanar X Y Z W \<and> \<not> collinear X Y Z \<and> \<not> collinear X Y W 
    \<and> \<not> collinear X Z W \<and> \<not> collinear Y Z W \<and> distinct[X,Y,Z,W]"
  shows "\<forall>X0 Y0 Z0. distinct[X0,Y0,Z0] \<and> {X0,Y0,Z0} \<subseteq> {X,Y,Z,W} 
    \<longrightarrow> \<not> collinear X0 Y0 Z0" 
  and "\<forall>X0 Y0 Z0 W0. distinct[X0,Y0,Z0,W0] \<and> {X0,Y0,Z0,W0} = {X,Y,Z,W} 
    \<longrightarrow> \<not> coplanar X0 Y0 Z0 W0"
proof (clarify)
  fix X0 Y0 Z0
  assume a1: "X0 \<noteq> Y0" and a2: "X0 \<noteq> Z0" and a3: "Y0 \<noteq> Z0" and "{X0,Y0,Z0} \<subseteq> {X,Y,Z,W}"
  then consider "{X0,Y0,Z0} = {X,Y,Z}" | "{X0,Y0,Z0} = {X,Y,W}"
    | "{X0,Y0,Z0} = {X,Z,W}" | "{X0,Y0,Z0} = {Y,Z,W}" by auto
  then show "collinear X0 Y0 Z0 \<Longrightarrow> False" by (cases,
    (metis assms a1 a2 a3 collinear_commute empty_iff insert_iff)+)
next
  show "\<forall>X0 Y0 Z0 W0. distinct[X0,Y0,Z0,W0] \<and> {X0,Y0,Z0,W0} = {X,Y,Z,W} 
    \<longrightarrow> \<not> coplanar X0 Y0 Z0 W0" using assms insert_subset bot.extremum 
    unfolding coplanar_def by metis
qed

lemma two_point_line_in_plane: (* credit to Jade Vanadium on MSE *)
  fixes A B P
  assumes "P \<in> Planes"
  assumes "A \<in> Points" and "B \<in> Points"
  assumes "A \<in> P" and "B \<in> P"
  assumes "A \<noteq> B"
  shows "join A B \<subseteq> P" 
proof (rule ccontr)
  let ?AB = "join A B" assume cd: "\<not> (?AB \<subseteq> P)"
  then have Punq: "\<forall>Q \<in> Planes. A \<in> Q \<and> B \<in> Q \<longrightarrow> Q = P" using assms vanadium3 by blast
  then have CABCP: "\<forall>C \<in> Points. C \<notin> ?AB \<longrightarrow> C \<in> P" using assms collinear_join S2a by metis
  obtain X Y Z W where XYZWdef: "X \<in> Points \<and> Y \<in> Points \<and> Z \<in> Points 
    \<and> W \<in> Points \<and> \<not> coplanar X Y Z W \<and> \<not> collinear X Y Z \<and> \<not> collinear X Y W 
    \<and> \<not> collinear X Z W \<and> \<not> collinear Y Z W \<and> distinct[X,Y,Z,W]" using S5 S5_dist by metis
  let ?XYZW = "{X,Y,Z,W}"
  have "\<nexists>X0 Y0. {X0,Y0} \<subseteq> ?XYZW \<and> X0 \<in> ?AB \<and> Y0 \<in> ?AB \<and> X0 \<noteq> Y0"
  proof (rule ccontr)
    assume cd1: "\<not> (\<nexists>X0 Y0. {X0,Y0} \<subseteq> ?XYZW \<and> X0 \<in> ?AB \<and> Y0 \<in> ?AB \<and> X0 \<noteq> Y0)"
    then obtain X0 Y0 where X0Y0def: "{X0,Y0} \<subseteq> ?XYZW \<and> X0 \<in> ?AB \<and> Y0 \<in> ?AB \<and> X0 \<noteq> Y0" by auto
    then have ABX0Y0: "?AB = (join X0 Y0)" using assms S0a S1a S1b by metis
    obtain Z0 W0 where Z0W0def: "{Z0,W0} \<subseteq> ?XYZW \<and> Z0 \<noteq> W0 \<and> Z0 \<noteq> X0 \<and> Z0 \<noteq> Y0 \<and> W0 \<noteq> X0 
      \<and> W0 \<noteq> Y0" using XYZWdef insert_mono subset_insertI subset_insertI2 distinct4_def by metis
    then have allp: "X0 \<in> Points \<and> Y0 \<in> Points \<and> Z0 \<in> Points \<and> W0 \<in> Points 
      \<and> {X0,Y0,Z0,W0} = ?XYZW \<and> distinct[X0,Y0,Z0,W0]" using X0Y0def XYZWdef by auto
    then have X0Y0Z0W0ncop: "\<not> coplanar X0 Y0 Z0 W0" 
      using XYZWdef choose_subset_helper(2) by presburger
    have X0Y0Z0ncoll: "\<not> collinear X0 Y0 Z0" and X0Y0W0ncoll: "\<not> collinear X0 Y0 W0"
      using XYZWdef X0Y0def Z0W0def allp choose_subset_helper(1) insert_subset 
      distinct3_def by metis+
    then have neqW: "(plane_through X0 Y0 Z0) \<noteq> (plane_through X0 Y0 W0)"
      using allp X0Y0Z0W0ncop S2a unfolding coplanar_def by metis
    then have "(join X0 Y0) = (plane_through X0 Y0 Z0) \<inter> (plane_through X0 Y0 W0)"
      using allp X0Y0def Z0W0def X0Y0Z0ncoll X0Y0W0ncoll vanadium4 by metis
    then have "A \<in> (plane_through X0 Y0 Z0) \<and> B \<in> (plane_through X0 Y0 Z0)
      \<and> A \<in> (plane_through X0 Y0 W0) \<and> B \<in> (plane_through X0 Y0 W0)" 
      using assms ABX0Y0 S1a by auto
    then show False using Punq allp X0Y0W0ncoll X0Y0Z0ncoll neqW S2a by metis
  qed
  then have "\<forall>X0. X0 \<in> ?XYZW \<and> X0 \<in> ?AB \<longrightarrow> (\<nexists>Y0. Y0 \<in> ?XYZW \<and> Y0 \<in> ?AB \<and> X0 \<noteq> Y0)"
    using insert_subset subsetI by metis
  then have "\<exists>X0 Y0 Z0. {X0,Y0,Z0} \<subseteq> ?XYZW \<and> X0 \<notin> ?AB \<and> Y0 \<notin> ?AB \<and> Z0 \<notin> ?AB \<and> distinct[X0,Y0,Z0]"
    using XYZWdef subset_insertI insert_mono insert_subset distinct3_def distinct4_def by metis
  then obtain X0 Y0 Z0 where X0Y0Z0def: "{X0,Y0,Z0} \<subseteq> ?XYZW \<and> X0 \<notin> ?AB
    \<and> Y0 \<notin> ?AB \<and> Z0 \<notin> ?AB \<and> distinct[X0,Y0,Z0]" by presburger
  then obtain W0 where W0def: "W0 \<in> ?XYZW \<and> distinct[X0,Y0,Z0,W0]" using XYZWdef by auto
  then have allp2: "X0 \<in> Points \<and> Y0 \<in> Points \<and> Z0 \<in> Points \<and> W0 \<in> Points 
     \<and> {X0,Y0,Z0,W0} = ?XYZW" using X0Y0Z0def XYZWdef by auto
  then have X0Y0Z0W0ncop: "\<not> coplanar X0 Y0 Z0 W0"
    using XYZWdef W0def choose_subset_helper(2) by presburger
  have X0Y0Z0ncoll: "\<not> collinear X0 Y0 Z0"  and X0Y0W0ncoll: "\<not> collinear X0 Y0 W0" 
    using XYZWdef X0Y0Z0def W0def choose_subset_helper(1)
    by (metis, metis insert_subset distinct3_def distinct4_def)
  have xyzinP: "X0 \<in> P \<and> Y0 \<in> P \<and> Z0 \<in> P" using XYZWdef X0Y0Z0def CABCP by blast
  then have X0Y0Z0eqP: "(plane_through X0 Y0 Z0) = P" using assms X0Y0Z0ncoll S0b S2b by auto
  then have W0notinXYZ: "W0 \<notin> (plane_through X0 Y0 Z0)" 
    using assms xyzinP X0Y0Z0W0ncop S0b coplanar_def by auto
  then have W0AB: "W0 \<in> ?AB" using XYZWdef X0Y0Z0eqP W0def CABCP by auto
  have W0nAoB: "W0 \<noteq> A \<and> W0 \<noteq> B" using assms X0Y0Z0eqP W0notinXYZ by auto
  then have ABisAW: "?AB = (join A W0)" and ABisBW: "?AB = (join B W0)"
    using assms W0AB S0a S1a S1b by metis+
  then have AXWncoll: "\<not> collinear A X0 W0" and AYWncoll: "\<not> collinear A Y0 W0" 
    and BXWncoll: "\<not> collinear B X0 W0" and BYWncoll: "\<not> collinear B Y0 W0" 
    using assms allp2 X0Y0Z0def W0nAoB S1a vanadium1 collinear_join by metis+
  then have "(plane_through A X0 W0) = (plane_through A Y0 W0)" 
    and "(plane_through B X0 W0) = (plane_through B Y0 W0)" 
    using assms Punq allp2 W0nAoB S1a S2a Int_iff
    by (metis ABisAW vanadium3 [of A W0], metis ABisBW vanadium3 [of B W0])
  then have "A \<in> (plane_through X0 Y0 W0)" and "B \<in> (plane_through X0 Y0 W0)"
    using assms allp2 S2a S2b X0Y0W0ncoll AXWncoll AYWncoll BXWncoll BYWncoll by metis+
  then have "P = (plane_through X0 Y0 W0)" using Punq allp2 X0Y0W0ncoll S2a by auto
  then show False using assms xyzinP X0Y0Z0eqP X0Y0W0ncoll W0notinXYZ W0AB S0a S0b S1a S2a by metis
qed

corollary int_line_plane_unique:
  fixes k N
  assumes "k \<in> Lines" and "N \<in> Planes"
  assumes "\<not> k \<subseteq> N"
  shows "\<exists>!P. P \<in> k \<and> P \<in> N"
proof -
  obtain P where Pdef: "P \<in> k \<and> P \<in> N" using assms S3 by auto
  from two_point_line_in_plane have "Q \<in> k \<and> Q \<in> N \<longrightarrow> Q = P" for Q
    using assms Pdef S0b S1b by metis
  then show ?thesis using Pdef by auto
qed

corollary outside_plane_ncoll:
  fixes P Q R H
  assumes "H \<in> Planes"
  assumes "P \<in> Points" and "Q \<in> Points" and "R \<in> Points"
  assumes "P \<in> H" and "Q \<in> H" and "R \<notin> H"
  assumes "P \<noteq> Q"
  shows "\<not> collinear P Q R"
proof -
  from two_point_line_in_plane have "(join P Q) \<subseteq> H" using assms by simp
  then show ?thesis using assms S1b collinear_def by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma crossing_planes_2: (* three distinct planes intersect in exactly one point *)
  fixes H N K
  assumes "H \<in> Planes" and "N \<in> Planes" and "K \<in> Planes"
  assumes "distinct[H,N,K]" and "\<not> H \<inter> N \<subseteq> K"
  shows "\<exists>!P. P \<in> Points \<and> P \<in> H \<inter> N \<inter> K"
proof -
  obtain l where "l \<in> Lines \<and> l = H \<inter> N" 
    using assms crossing_planes by auto
  then show ?thesis using assms int_line_plane_unique [of l K] S0a Int_iff by metis
qed

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
        using assms Rdef int_line_plane_unique [of k] subset_iff by metis
      then obtain T where Tdef: "T \<in> H \<and> T \<noteq> S"
        using assms S4 S6 subset_iff distinct3_def by metis
      then obtain U where Udef: "U \<in> (join Q T) \<and> U \<noteq> Q \<and> U \<noteq> T"
        using assms NeitherH S0b S1a S6 distinct3_def by metis
      then have UnH: "U \<in> Points \<and> U \<notin> H" using assms NeitherH Tdef S0a S0b 
        S1a S1b int_line_plane_unique [of "join Q T" H] subset_iff by metis
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
lemma space_plane_p2:
  fixes H k n
  assumes "H \<in> Planes" and "k \<in> Lines" and "n \<in> Lines"
  assumes "k \<subseteq> H" and "n \<subseteq> H"
  shows "\<exists>P. (P \<in> H \<and> P \<in> k \<and> P \<in> n)"
proof -
  obtain Pk Qk Rk where k_pts: "Pk \<in> k \<and> Qk \<in> k \<and> Rk \<in> k \<and> distinct[Pk,Qk,Rk]" 
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
    then obtain S where Sdef: "S \<in> k \<and> S \<in> V" using k_pts Vdef S3 by metis
    then have "S \<in> n" 
      using assms Xdef Vdef k_int plane_through_point_line S0b by blast
    then show ?thesis using assms Sdef Vdef k_int by auto
  qed
qed

lemma space_plane_p3:
  fixes H
  assumes HP: "H \<in> Planes"
  shows "\<exists>P Q R. P \<in> H \<and> Q \<in> H \<and> R \<in> H \<and> distinct[P,Q,R] \<and> \<not> (collinear P Q R)"
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
  show "\<lbrakk>k \<in> HLines; n \<in> HLines\<rbrakk> \<Longrightarrow> \<exists>P. (P \<in> H \<and> Hincid P k \<and> Hincid P n)" for k n
    using assms space_plane_p2 [of H k n] by auto
  show "\<exists>P Q R. P \<in> H \<and> Q \<in> H \<and> R \<in> H \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R 
    \<and> \<not> (projective_plane_data.pcollinear H HLines Hincid P Q R)"
  proof -
    obtain P Q R where PQRdef: "P \<in> H \<and> Q \<in> H \<and> R \<in> H \<and> distinct[P,Q,R] 
      \<and> \<not> collinear P Q R" using HP space_plane_p3 [of H] by auto
    then have "\<not> (projective_plane_data.pcollinear H HLines Hincid P Q R)"
      using HP HLdef Hidef S0b [of H] mem_Collect_eq collinear_def
      unfolding projective_plane_data.pcollinear_def by auto
    then show ?thesis using PQRdef by auto
  qed
  show "\<lbrakk>k \<in> HLines; U = {P. (P \<in> H \<and> Hincid P k)}\<rbrakk> 
    \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct[Q,R,S]" for k U
  proof -
    assume khl: "k \<in> HLines" and Uset: "U = {P. (P \<in> H \<and> Hincid P k)}"
    then obtain Q R S where qrs: "Q \<in> k \<and> R \<in> k \<and> S \<in> k \<and> distinct[Q,R,S]" 
      using S6 [of k] HLdef by auto
    then have "Q \<in> U \<and> R \<in> U \<and> S \<in> U" using khl Uset qrs S0a HLdef Hidef by auto
    then show "\<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct[Q,R,S]" using qrs by auto
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma crossing_lines: (* two lines through a point determine a unique plane *)
  fixes k n P
  assumes "k \<in> Lines" and "n \<in> Lines" and "k \<noteq> n"
  assumes "P \<in> Points" and "P \<in> k \<inter> n"
  shows "\<exists>!H. H \<in> Planes \<and> k \<subseteq> H \<and> n \<subseteq> H"
proof -
  obtain Q where qdef: "Q \<in> k \<and> Q \<notin> n" using assms S0a S1b S6 distinct3_def by metis
  obtain R where rdef: "R \<in> n \<and> R \<notin> k" using assms S0a S1b S6 distinct3_def by metis
  then have pqr: "\<not> collinear P Q R" using assms qdef S0a S1b Int_iff
    unfolding collinear_def by metis
  then obtain H where Hdef: "H \<in> Planes \<and> H = plane_through P Q R"
    using assms qdef rdef S0a S2a by simp
  then have Hkn: "k \<subseteq> H \<and> n \<subseteq> H" 
    using assms pqr qdef rdef S0a S2a int_line_plane_unique [of _ H] Int_iff by metis
  have "N \<in> Planes \<and> k \<subseteq> N \<and> n \<subseteq> N \<Longrightarrow> H = N" for N using assms pqr qdef rdef
    Hdef S0a S2b [of P Q R] Int_iff subset_iff by metis
  then show ?thesis using Hdef Hkn by metis
qed

lemma crossing_lines_2: (* just a usable version of space_plane_p2 *)
  fixes k n H
  assumes "k \<in> Lines" and "n \<in> Lines" and "k \<noteq> n"
  assumes "H \<in> Planes" and "k \<subseteq> H \<and> n \<subseteq> H"
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

lemma crossing_lines_3:
  fixes k n P
  assumes "k \<in> Lines" and "n \<in> Lines" and "k \<noteq> n"
  assumes "P \<in> Points" and "P \<in> k \<inter> n"
  shows "\<forall>Q. (Q \<in> Points \<and> Q \<in> k \<inter> n \<longrightarrow> Q = P)"
  using assms S0a S1b Int_iff by metis
text \<open>\done\<close>

(*text \<open>\hadi\<close>
lemma space_plane_min7:
  assumes "finite Points"
  fixes H
  assumes "H \<in> Planes"
  shows "card H \<ge> 7"
proof -
  let ?HLines = "{L. L \<in> Lines \<and> L \<subseteq> H}"
  let ?Hincid = "(\<lambda>P L. (if P \<in> H \<and> L \<in> ?HLines then P \<in> L else undefined))"
  have "H \<subseteq> Points" using assms S0b by auto
  then have finH: "finite H" using assms finite_subset by auto
  have "projective_plane H ?HLines ?Hincid" 
    using assms space_plane_is_proj_plane by blast
  then show ?thesis using finH projective_plane.PPmin7 by auto
qed

lemma union_planes_min8:
  assumes "finite Points"
  fixes A B
  assumes "A \<in> Planes" and "B \<in> Planes" and "A \<noteq> B"
  shows "card (A \<union> B) \<ge> 8"
proof -
  have allg7: "card A \<ge> 7 \<and> card B \<ge> 7" using assms space_plane_min7 by auto
  have "(A \<inter> B) \<in> Lines" using assms crossing_planes by auto
  then have anAiB: "\<exists>a \<in> A. a \<notin> A \<inter> B" and "\<exists>b \<in> B. b \<notin> A \<inter> B"
    using assms space_plane_p3 S0b unfolding collinear_def by metis+
  then have AiBle: "card (A \<inter> B) \<le> (card A) - 1" using allg7 anAiB Suc_pred'
    card_seteq inf_le1 less_Suc_eq_0_disj linorder_not_less numeral_eq_Suc
    not_less_eq_eq card.infinite by metis
  have "(card (A \<union> B)) = (card A) + (card B) - (card (A \<inter> B))" using assms
    allg7 card_eq_sum card.infinite not_numeral_le_zero sum_Un_nat by metis
  then show ?thesis using allg7 AiBle diff_le_mono2 by auto
qed

theorem PSmin12:
  assumes "finite Points"
  shows "card Points \<ge> 12"
proof -
  obtain P Q R S where pqrs: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points 
    \<and> \<not> coplanar P Q R S \<and> \<not> collinear P Q R \<and> \<not> collinear P Q S \<and> \<not> collinear P R S 
    \<and> \<not> collinear Q R S \<and> distinct[P,Q,R,S]" using S5 S5_dist by metis
  then obtain A B C D where abcd: "A \<in> Planes \<and> B \<in> Planes \<and> C \<in> Planes \<and> D \<in> Planes
    \<and> A = (plane_through P Q R) \<and> B = (plane_through P Q S) \<and> C = (plane_through P R S)
    \<and> D = (plane_through Q R S)" using S2a by auto
  then have "card (A \<union> B) \<ge> 8" and "card (A \<union> C) \<ge> 8" and "card (A \<union> D) \<ge> 8"
    and "card (B \<union> C) \<ge> 8" and "card (B \<union> D) \<ge> 8" and "card (C \<union> D) \<ge> 8" 
    using assms pqrs union_planes_min8 S2a unfolding coplanar_def by metis+
  then have "card (A \<union> B \<union> C) \<ge> 9" and "card (A \<union> B \<union> D) \<ge> 9"
    and "card (A \<union> C \<union> D) \<ge> 9" and "card (B \<union> C \<union> D) \<ge> 9" sorry
  then have "card Points \<ge> 10" sorry
  then show "card Points \<ge> 12" sorry
qed
text \<open>\done\<close>*)

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
  have ACXncoll: "\<not> collinear A C X" using assms outside_plane_ncoll by auto
  then obtain N where Ndef: "N \<in> Planes \<and> N = (plane_through A C X)"
    using assms S2a by auto
  then obtain k where kdef: "k \<in> Lines \<and> k = H \<inter> N" 
    using assms ACXncoll crossing_planes S2a by blast
  then have ACink: "A \<in> k \<and> C \<in> k" using assms ACXncoll Ndef S2a by simp
  have "(join A' C') \<subseteq> N" using assms Ndef S2a outside_plane_ncoll
    two_point_line_in_plane [of N A' C'] by metis
  then show ?thesis
    using assms ldef kdef ACink S1b [of A' C'] collinear_def by auto
qed

lemma desargues_2_helper: (* see https://www.geogebra.org/3d/q7mpxjx7 *)
  fixes H X U A B A' B' D D' P P'
  assumes "H \<in> Planes"
  assumes "U \<in> Points" and "A \<in> Points" and "D \<in> Points" and "B \<in> Points"
    and "A' \<in> Points" and "D' \<in> Points" and "B' \<in> Points" and "X \<in> Points"
  assumes "distinct[U,A,D,B,A',D',B']"
  assumes "U \<in> H" and "A \<in> H" and "B \<in> H"  and "A' \<in> H" and "B' \<in> H"
  assumes "X \<notin> H" and "D \<notin> H" and "D' \<notin> H"
  assumes "\<not> collinear A D B" and "\<not> collinear A' D' B'"
  assumes "collinear A A' U" and "collinear D D' U" and "collinear B B' U" 
  assumes "collinear X D B" and "collinear X D' B'"
  assumes "join A B \<noteq> join A' B'" and "join A D \<noteq> join A' D'"
  assumes "join A A' \<noteq> join B B'"
  assumes "P \<in> (join A B) \<inter> (join A' B')" and "P' \<in> (join A D) \<inter> (join A' D')"
  shows "collinear X P P'"
proof -
  have p: "P \<in> Points" and p': "P' \<in> Points" 
    using assms S0a S1a Int_iff by metis+
  obtain N1 N2 N3 where N1def: "N1 \<in> Planes \<and> N1 = (plane_through U A D)"
    and N2def: "N2 \<in> Planes \<and> N2 = (plane_through A D B)"
    and N3def: "N3 \<in> Planes \<and> N3 = (plane_through A' D' B')"
    using assms outside_plane_ncoll S2a distinct7_def by metis
  then have N1neqN2: "N1 \<noteq> N2" using assms p outside_plane_ncoll [of N1] crossing_lines 
    two_point_line_in_plane collinear_commute S1a S2a distinct7_def by metis
  then have N1neqN3: "N1 \<noteq> N3" using assms N1def N2def N3def outside_plane_ncoll
    collinear_commute S2a S2b distinct7_def by metis
  then have N2neqN3: "N2 \<noteq> N3" using assms N1def N2def N3def N1neqN2 outside_plane_ncoll
    S2a S2b [of _ _ _ N2] distinct7_def by (metis (mono_tags))
  have XinN2N3: "X \<in> N2 \<inter> N3" using assms N2def N3def outside_plane_ncoll
    collinear_commute S2a Int_iff distinct7_def by metis
  have "X \<notin> N1" using assms N1def N2def N3def N1neqN2 N1neqN3 collinear_commute [of X P]
    outside_plane_ncoll [of H] outside_plane_ncoll [of N1] S2a [of U A D] S2b [of _ _ _ N1]
    unfolding collinear_def distinct7_def by metis
  then have "\<not> N2 \<inter> N3 \<subseteq> N1" using XinN2N3 by auto
  then obtain R where Rdef: "R \<in> Points \<and> R \<in> N1 \<inter> N2 \<inter> N3
    \<and> (\<forall>Q. (Q \<in> Points \<and> Q \<in> N1 \<inter> N2 \<inter> N3) \<longrightarrow> Q = R)"
    using N1def N2def N3def N1neqN2 N1neqN3 N2neqN3 XinN2N3 inf_assoc inf_commute
    crossing_planes_2 [of N2 N3 N1] distinct3_def by metis
  have "P \<in> N2" and "P \<in> N3" using assms N2def N3def two_point_line_in_plane S2a
    Int_iff subset_eq distinct7_def by (metis (no_types))+
  then have "(join X P) = N2 \<inter> N3" using assms p N2def N3def N2neqN3 XinN2N3 S1b Int_iff
    crossing_planes two_point_line_in_plane subsetD distinct7_def by (metis (no_types))
  then have XPRcoll: "collinear X P R" using p Rdef N2def N3def N2neqN3 XinN2N3
    crossing_planes S0a S1a Int_iff unfolding collinear_def by metis
  have RinAD: "R \<in> (join A D)" using assms Rdef N1def N2def N1neqN2 S1a S2a
    two_point_line_in_plane outside_plane_ncoll plane_through_point_line [of R]
    Int_iff distinct7_def by metis
  have "R \<in> (join A' D')" using assms Rdef N1def N3def N1neqN3 S1a S2a
    two_point_line_in_plane outside_plane_ncoll plane_through_point_line [of R]
    collinear_commute Int_iff distinct7_def by metis
  then show ?thesis using assms p' Rdef RinAD XPRcoll S1a Int_iff
    crossing_lines_3 [of "join A D" "join A' D'"] by metis
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
theorem desargues_case_1: (* desargues' theorem for two distinct planes *)
  fixes U A B C A' B' C' P Q R
  assumes "U \<in> Points" and "A \<in> Points" and "B \<in> Points" and "C \<in> Points"
    and "A' \<in> Points" and "B' \<in> Points" and "C' \<in> Points"
  assumes "distinct[U,A,B,C,A',B',C']" 
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

theorem desargues_case_2: (* desargues' theorem for a single plane *)
  fixes U A B C A' B' C' P Q R
  assumes "U \<in> Points" and "A \<in> Points" and "B \<in> Points" and "C \<in> Points" and
    "A' \<in> Points" and "B' \<in> Points" and "C' \<in> Points"
  assumes "distinct[U,A,B,C,A',B',C']" 
  assumes "collinear A A' U" and "collinear B B' U" and "collinear C C' U"
  assumes "\<not> collinear A B C" and "\<not> collinear A' B' C'" 
  assumes "distinct[(join A A'),(join B B'),(join C C')]"
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
  have Spts: "U \<in> ?S \<and> A \<in> ?S \<and> B \<in> ?S \<and> C \<in> ?S \<and> A' \<in> ?S \<and> B' \<in> ?S \<and> C' \<in> ?S"
    and SP: "?S \<in> Planes" using assms outside_plane_ncoll S2a by metis+
  have PQRinS: "P \<in> ?S \<and> Q \<in> ?S \<and> R \<in> ?S" using assms S2a in_mono inf_le1
    two_point_line_in_plane [of ?S] unfolding distinct7_def by (metis (full_types))
  obtain X where xdef: "X \<in> Points \<and> X \<notin> ?S"
    using assms S2a point_outside_plane by metis
  then have XBnS: "\<not> (join X B) \<subseteq> ?S" and XB'nS: "\<not> (join X B') \<subseteq> ?S"
    using assms Spts S1a subset_eq by metis+
  obtain D where ddef: "D \<in> Points \<and> D \<in> (join X B) \<and> D \<noteq> X \<and> D \<noteq> B" 
    using assms xdef S0a S1a S2a S6 distinct3_def by metis
  then have "(join X D) \<in> Lines \<and> \<not> (join X D) \<subseteq> ?S" 
    using xdef S1a subset_iff by metis
  then have XDintSunq: "\<forall>G. G \<in> (join X D) \<and> G \<in> ?S \<longrightarrow> G = B" 
    using assms xdef ddef int_line_plane_unique S1a S1b S2a by metis
  then have DnS: "D \<notin> ?S" using xdef ddef S1a by auto
  have nubx: "\<not> collinear U B X" using assms Spts xdef ddef XDintSunq S1b 
    distinct7_def unfolding collinear_def by metis
  let ?ubx = "plane_through U B X"
  have "join U B \<subseteq> ?ubx" using assms xdef nubx two_point_line_in_plane S2a
    unfolding distinct7_def by metis
  then have "B' \<in> ?ubx" using assms S1b distinct7_def in_mono
    unfolding collinear_def by metis
  then have xb'inubx: "join X B' \<subseteq> ?ubx" and "join X B \<subseteq> ?ubx"
    using assms nubx xdef S2a two_point_line_in_plane by metis+
  then have "D \<in> ?ubx" using ddef by auto
  then have "join U D \<subseteq> ?ubx" using assms xdef nubx ddef S1a S2a  
    two_point_line_in_plane unfolding collinear_def by metis
  then obtain D' where d'def: "D' \<in> Points \<and> D' \<in> (join U D) \<inter> (join X B')" 
    using assms xdef nubx ddef xb'inubx crossing_lines_2 [of "join U D"] 
    S1a S2a IntI unfolding collinear_def by metis
  have nub'x: "\<not> collinear U B' X" 
    using assms SP Spts xdef outside_plane_ncoll distinct7_def by metis
  have "D' \<noteq> B'" using assms Spts ddef d'def DnS S1a S1b S2a Int_iff inf_absorb2
    two_point_line_in_plane [of ?S U] outside_plane_ncoll distinct7_def by metis
  then have D'nS: "D' \<notin> ?S" 
    using assms Spts xdef d'def XB'nS int_line_plane_unique S1a S2a Int_iff by metis
  have "D \<noteq> D'" using assms Spts xdef ddef d'def XDintSunq 
    S1a S1b Int_iff distinct7_def by metis
  then have ADCdist: "distinct[U,A,D,C,A',D',C']" using assms Spts DnS D'nS by auto
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
      two_point_line_in_plane [of ?S] in_mono distinct7_def by metis
    then show False using DnS D'nS by simp
  qed
  then obtain H N where HNdef: "H \<in> Planes \<and> N \<in> Planes \<and> H = (plane_through A D C) 
    \<and> N = (plane_through A' D' C')" using assms d'def ddef S2a by simp
  then have HneqN: "H \<noteq> N" using assms Spts xdef ddef d'def adca'd'c'ncoll XBnS S1a S2a
    vanadium3 [of _ _ H ?S] int_line_plane_unique [of _ N] unfolding distinct7_def by metis
  have ada'd': "(join A D \<noteq> join A' D')" and dcd'c': "(join D C \<noteq> join D' C')"
    using assms SP Spts ddef d'def DnS D'nS S1a S1b in_mono
    two_point_line_in_plane [of ?S] unfolding distinct7_def by metis+
  then have UADncoll: "\<not> collinear U A D" using assms ddef d'def ADCdist S1b 
    Int_iff distinct7_def unfolding collinear_def by metis
  then obtain K where Kdef: "K \<in> Planes \<and> K = (plane_through U A D)"
    using assms ddef S2a by simp
  then have "(join A D) \<subseteq> K \<and> (join A' D') \<subseteq> K" using assms UADncoll 
    ddef d'def dd'u ADCdist two_point_line_in_plane outside_plane_ncoll 
    collinear_commute S2a distinct7_def by metis
  then obtain P'::'p where p'def: "P' \<in> (join A D) \<and> P' \<in> (join A' D')" 
    using assms ddef d'def ADCdist Kdef space_plane_p2 S1a distinct7_def by metis
  have UDCncoll: "\<not> collinear U D C" using assms ddef d'def dcd'c' ADCdist 
    S1b Int_iff distinct7_def unfolding collinear_def by metis
  then obtain M where Mdef: "M \<in> Planes \<and> M = (plane_through U D C)"
    using assms ddef S2a by simp
  then have "(join D C) \<subseteq> M \<and> (join D' C') \<subseteq> M" using assms UDCncoll 
    ddef d'def dd'u ADCdist two_point_line_in_plane outside_plane_ncoll 
    collinear_commute S2a distinct7_def by metis
  then obtain R'::'p where r'def: "R' \<in> (join D C) \<and> R' \<in> (join D' C')"
    using assms ddef d'def ADCdist Mdef space_plane_p2 S1a distinct7_def by metis
  have PRP'R'dist: "P \<noteq> R \<and> P' \<noteq> R'"
  proof (safe)
    assume "P = R"
    then have "(join A B) = (join B C) \<or> (join A' B') = (join B' C')"
      using assms S0a S1a S1b [of B'] Int_iff distinct7_def by metis
    then show False using assms joins_eq_collinear distinct7_def by metis
  next
    assume "P' = R'"
    then have "(join A D) = (join D C) \<or> (join A' D') = (join D' C')"
      using assms ddef d'def ADCdist p'def r'def S0a S1a S1b [of D'] distinct7_def by metis
    then show False using assms adca'd'c'ncoll d'def ddef ADCdist 
      joins_eq_collinear distinct7_def by metis
  qed
  have P'QR'coll: "collinear P' Q R'"
    using assms ddef d'def ADCdist ada'd' dcd'c' dd'u adca'd'c'ncoll
    HNdef HneqN p'def r'def desargues_case_1 [of U A D C A' D' C'] by auto
  have XDBcoll: "collinear X D B" and XD'B'coll: "collinear X D' B'" using assms
    xdef ddef d'def S1a unfolding collinear_def by (metis, metis Int_iff)
  have alldist: "distinct[U,A,D,B,A',D',B'] \<and> distinct[U,C,D,B,C',D',B']" 
    using assms Spts DnS D'nS ADCdist unfolding distinct7_def by metis
  then have "\<not> collinear A D B \<and> \<not> collinear A' D' B'"
    and CDBncoll: "\<not> collinear C D B \<and> \<not> collinear C' D' B'" 
    using assms SP Spts ddef d'def DnS D'nS collinear_commute 
    outside_plane_ncoll distinct7_def by metis+
  then have XPP'coll: "collinear X P P'" using assms SP Spts xdef ddef d'def
    DnS D'nS dd'u outside_plane_ncoll desargues_2_helper [of ?S U A D B A' D' B' X] 
    ada'd' p'def XDBcoll XD'B'coll alldist distinct3_def Int_iff by metis
  have XRR'coll: "collinear X R R'" using assms SP Spts xdef ddef d'def DnS D'nS  
    dd'u outside_plane_ncoll desargues_2_helper [of ?S U C D B C' D' B' X R R'] 
    dcd'c' r'def XDBcoll XD'B'coll CDBncoll alldist distinct3_def
    join_commute [of C] join_commute [of C'] Int_iff by metis
  have P'nAA': "P' \<noteq> A \<and> P' \<noteq> A'" and R'nCC': "R' \<noteq> C \<and> R' \<noteq> C'"
    using assms ddef d'def ada'd' dcd'c' ADCdist p'def r'def
    S1a S1b Int_iff unfolding distinct7_def collinear_def by metis+
  have "\<not> (join A D) \<subseteq> ?S" and "\<not> (join D C) \<subseteq> ?S"
    using assms Spts ddef DnS S1a [of A D] S1a [of D C] by auto
  then have "\<forall>G. G \<in> (join A D) \<and> G \<in> ?S \<longrightarrow> G = A" 
    and "\<forall>G. G \<in> (join D C) \<and> G \<in> ?S \<longrightarrow> G = C" using assms ddef DnS S1a S2a
    int_line_plane_unique [of "join A D" ?S] int_line_plane_unique [of "join D C" ?S] by metis+
  then have P'R'nS: "P' \<notin> ?S \<and> R' \<notin> ?S" using p'def r'def P'nAA' R'nCC' by auto
  then show ?thesis using assms xdef ddef DnS PQRinS p'def r'def P'QR'coll 
    PRP'R'dist projected_points_collinear [of ?S X P Q R P' R'] 
    XPP'coll XRR'coll S0a S0b S1a S2a by metis
qed
text \<open>\done\<close>

end

end