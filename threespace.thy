theory threespace
  imports Main

begin

definition distinct3 where 
  "distinct3 x y z \<equiv> (x \<noteq> y) \<and> (x \<noteq> z) \<and> (y \<noteq> z)"

definition distinct4 where 
  "distinct4 x y z w \<equiv> y \<noteq> x \<and> z \<noteq> x \<and> z \<noteq> y \<and> w \<noteq> x \<and> w \<noteq> y \<and> w \<noteq> z"

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

lemma coplanar_commute:
  fixes P Q R S
  assumes "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points"
  assumes "coplanar P Q R S"
  shows "coplanar Q P R S" and "coplanar P R Q S" and "coplanar P Q S R"
    and "coplanar S Q R P" using assms coplanar_def by auto

lemma collinear_commute:
  fixes P Q R
  assumes "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points"
  assumes "collinear P Q R"
  shows "collinear Q P R" and "collinear P R Q" and "collinear R Q P"
  using assms collinear_def by auto
text \<open>\done\<close>

text \<open>\spike\<close>
lemma crossing_planes:
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
text \<open>\done\<close>

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
  assumes "distinct4 a b x y"
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
  assumes "distinct3 a b c" 
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
    using S6 S0a unfolding distinct3_def by blast
  then have h1: "L = join a b" using L_facts S1b by auto
  show ?thesis
  proof (cases "\<exists>p. (p \<in> Points \<and> p \<notin> L \<and> p \<in> P \<and> p \<in> Q)")
    case True
    then obtain p where p_facts: "(p \<in> Points \<and> p \<notin> L \<and> p \<in> P \<and> p \<in> Q)" by auto
    then have "distinct3 a b p" using h0 unfolding distinct3_def by auto
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
  assumes "distinct4 x y z w"
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
    \<and> \<not> collinear X Z W \<and> \<not> collinear Y Z W \<and> distinct4 X Y Z W"
  shows "\<forall>X0 Y0 Z0. distinct3 X0 Y0 Z0 \<and> {X0,Y0,Z0} \<subseteq> {X,Y,Z,W} 
    \<longrightarrow> \<not> collinear X0 Y0 Z0" 
  and "\<forall>X0 Y0 Z0 W0. distinct4 X0 Y0 Z0 W0 \<and> {X0,Y0,Z0,W0} = {X,Y,Z,W} 
    \<longrightarrow> \<not> coplanar X0 Y0 Z0 W0"
proof (clarify)
  fix X0 Y0 Z0
  assume a1: "distinct3 X0 Y0 Z0" and "{X0,Y0,Z0} \<subseteq> {X,Y,Z,W}"
  then consider "{X0,Y0,Z0} = {X,Y,Z}" | "{X0,Y0,Z0} = {X,Y,W}"
    | "{X0,Y0,Z0} = {X,Z,W}" | "{X0,Y0,Z0} = {Y,Z,W}"
    unfolding distinct3_def by force
  then show "collinear X0 Y0 Z0 \<Longrightarrow> False" by (cases, 
    (metis assms a1 collinear_commute empty_iff insert_iff distinct3_def)+)
next
  show "\<forall>X0 Y0 Z0 W0. distinct4 X0 Y0 Z0 W0 \<and> {X0,Y0,Z0,W0} = {X,Y,Z,W} 
    \<longrightarrow> \<not> coplanar X0 Y0 Z0 W0" using assms insert_subset bot.extremum 
    unfolding coplanar_def by metis
qed

lemma vanadium_two_point_line_in_plane:
  fixes A B P
  assumes "P \<in> Planes"
  assumes "A \<in> Points" and "B \<in> Points"
  assumes "A \<in> P" and "B \<in> P"
  assumes "A \<noteq> B"
  shows "join A B \<subseteq> P" 
proof (rule ccontr)
  let ?AB = "join A B"
  assume cd: "\<not> (?AB \<subseteq> P)"
  then have Punq: "\<forall>Q \<in> Planes. A \<in> Q \<and> B \<in> Q \<longrightarrow> Q = P" using assms vanadium3 by blast
  then have CABCP: "\<forall>C \<in> Points. C \<notin> ?AB \<longrightarrow> C \<in> P" using assms collinear_join S2a by metis
  obtain X Y Z W where XYZWdef: "X \<in> Points \<and> Y \<in> Points \<and> Z \<in> Points 
    \<and> W \<in> Points \<and> \<not> coplanar X Y Z W \<and> \<not> collinear X Y Z \<and> \<not> collinear X Y W 
    \<and> \<not> collinear X Z W \<and> \<not> collinear Y Z W \<and> distinct4 X Y Z W" using S5 S5_dist by metis
  let ?XYZW = "{X,Y,Z,W}"
  have "\<nexists>X0 Y0. {X0,Y0} \<subseteq> ?XYZW \<and> X0 \<in> ?AB \<and> Y0 \<in> ?AB \<and> X0 \<noteq> Y0"
  proof (rule ccontr)
    assume cd1: "\<not> (\<nexists>X0 Y0. {X0,Y0} \<subseteq> ?XYZW \<and> X0 \<in> ?AB \<and> Y0 \<in> ?AB \<and> X0 \<noteq> Y0)"
    then obtain X0 Y0 where X0Y0def: "{X0,Y0} \<subseteq> ?XYZW \<and> X0 \<in> ?AB \<and> Y0 \<in> ?AB \<and> X0 \<noteq> Y0" by auto
    then have ABX0Y0: "?AB = (join X0 Y0)" using assms S0a S1a S1b by metis
    obtain Z0 W0 where Z0W0def: "{Z0,W0} \<subseteq> ?XYZW \<and> Z0 \<noteq> W0 \<and> Z0 \<noteq> X0 \<and> Z0 \<noteq> Y0 \<and> W0 \<noteq> X0 \<and> W0 \<noteq> Y0" 
      using XYZWdef insert_mono subset_insertI subset_insertI2 unfolding distinct4_def by metis
    then have allp: "X0 \<in> Points \<and> Y0 \<in> Points \<and> Z0 \<in> Points \<and> W0 \<in> Points \<and> {X0,Y0,Z0,W0} = ?XYZW 
      \<and> distinct4 X0 Y0 Z0 W0" using X0Y0def XYZWdef unfolding distinct4_def by auto
    then have X0Y0Z0W0ncop: "\<not> coplanar X0 Y0 Z0 W0" 
      using XYZWdef choose_subset_helper(2) by presburger
    have X0Y0Z0ncoll: "\<not> collinear X0 Y0 Z0" and X0Y0W0ncoll: "\<not> collinear X0 Y0 W0"
      using XYZWdef X0Y0def Z0W0def allp choose_subset_helper(1) insert_subset 
      unfolding distinct3_def by metis+
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
  then have "\<exists>X0 Y0 Z0. {X0,Y0,Z0} \<subseteq> ?XYZW \<and> X0 \<notin> ?AB \<and> Y0 \<notin> ?AB \<and> Z0 \<notin> ?AB \<and> distinct3 X0 Y0 Z0"
    using XYZWdef subset_insertI insert_mono insert_subset distinct3_def distinct4_def by metis
  then obtain X0 Y0 Z0 where X0Y0Z0def: "{X0,Y0,Z0} \<subseteq> ?XYZW \<and> X0 \<notin> ?AB
    \<and> Y0 \<notin> ?AB \<and> Z0 \<notin> ?AB \<and> distinct3 X0 Y0 Z0" by presburger
  then obtain W0 where W0def: "W0 \<in> ?XYZW \<and> distinct4 X0 Y0 Z0 W0"
    using XYZWdef unfolding distinct3_def distinct4_def by auto
  then have Oeq0: "X0 \<in> Points \<and> Y0 \<in> Points \<and> Z0 \<in> Points \<and> W0 \<in> Points 
     \<and> {X0,Y0,Z0,W0} = ?XYZW" using X0Y0Z0def XYZWdef unfolding distinct4_def by auto
  then have X0Y0Z0W0ncop: "\<not> coplanar X0 Y0 Z0 W0"
    using XYZWdef W0def choose_subset_helper(2) by presburger
  have X0Y0Z0ncoll: "\<not> collinear X0 Y0 Z0" and X0Y0W0ncoll: "\<not> collinear X0 Y0 W0"
   using XYZWdef X0Y0Z0def W0def Oeq0 choose_subset_helper(1)
   unfolding distinct3_def distinct4_def by (metis, metis insert_subset)
  have xyzinP: "X0 \<in> P \<and> Y0 \<in> P \<and> Z0 \<in> P" using XYZWdef X0Y0Z0def CABCP by blast
  then have X0Y0Z0eqP: "(plane_through X0 Y0 Z0) = P" using assms X0Y0Z0ncoll S0b S2b by auto
  then have W0notinXYZ: "W0 \<notin> (plane_through X0 Y0 Z0)" 
    using assms xyzinP X0Y0Z0W0ncop S0b coplanar_def by auto
  then have W0AB: "W0 \<in> ?AB" using XYZWdef X0Y0Z0eqP W0def CABCP by auto
  have W0nAoB: "W0 \<noteq> A \<and> W0 \<noteq> B" using assms X0Y0Z0eqP W0notinXYZ by auto
  then have ABisAW: "?AB = (join A W0)" using assms W0AB S0a S1a S1b by metis
  then have AXWncoll: "\<not> collinear A X0 W0" and AYWncoll: "\<not> collinear A Y0 W0" 
    using assms Oeq0 X0Y0Z0def W0nAoB S1a vanadium1 collinear_join by metis+
  have AXWeqAYW: "(plane_through A X0 W0) = (plane_through A Y0 W0)" using assms 
    Punq Oeq0 W0nAoB ABisAW AXWncoll AYWncoll vanadium3 [of A W0] S1a S2a Int_iff by metis
  then have AinXYW: "A \<in> (plane_through X0 Y0 W0)" 
    using assms Oeq0 S2a S2b X0Y0W0ncoll AXWncoll AYWncoll by metis
  have ABisBW: "?AB = (join B W0)" using assms W0nAoB W0AB S0a S1a S1b by metis
  then have BXWncoll: "\<not> collinear B X0 W0" and BYWncoll: "\<not> collinear B Y0 W0" 
    using assms Oeq0 X0Y0Z0def W0nAoB S1a vanadium1 collinear_join by metis+
  have BXWeqBYW: "(plane_through B X0 W0) = (plane_through B Y0 W0)" using assms 
    Punq Oeq0 W0nAoB ABisBW BXWncoll BYWncoll vanadium3 [of B W0] S1a S2a Int_iff by metis
  then have "B \<in> (plane_through X0 Y0 W0)" 
    using assms Oeq0 S2a S2b X0Y0W0ncoll BXWncoll BYWncoll by metis
  then have "P = (plane_through X0 Y0 W0)" using Punq Oeq0 AinXYW X0Y0W0ncoll S2a by auto
  then show False using assms xyzinP X0Y0Z0eqP X0Y0W0ncoll W0notinXYZ W0AB S0a S0b S1a S2a by metis
qed
text \<open>\done\<close>

end
end