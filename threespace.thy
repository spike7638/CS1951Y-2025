theory threespace
  imports Main

begin

definition distinct3 where "distinct3 x y z \<equiv> (x \<noteq> y) \<and> (x \<noteq> z) \<and> (y \<noteq> z)"
definition distinct4 where 
  "distinct4 x y z w \<equiv> y \<noteq> x \<and> 
                       z \<noteq> x \<and> z \<noteq> y \<and> 
                       w \<noteq> x \<and> w \<noteq> y \<and> w \<noteq> z"
definition distinct5 where 
  "distinct5 x y z w r \<equiv> y \<noteq> x \<and> 
                       z \<noteq> x \<and> z \<noteq> y \<and> 
                       w \<noteq> x \<and> w \<noteq> y \<and> w \<noteq> z \<and>
   r \<noteq> x \<and> r \<noteq> y \<and> r \<noteq> z \<and> r \<noteq> w"

definition distinct6 where 
  "distinct6 x y z w r s \<equiv> y \<noteq> x \<and> 
                           z \<noteq> x \<and> z \<noteq> y \<and> 
                           w \<noteq> x \<and> w \<noteq> y \<and> w \<noteq> z \<and>
   r \<noteq> x \<and> r \<noteq> y \<and> r \<noteq> z \<and> r \<noteq> w \<and>
   s \<noteq> x \<and> s \<noteq> y \<and> s \<noteq> z \<and> s \<noteq> w \<and> s \<noteq> r" 

definition distinct7 where 
  "distinct7 x y z w r s t \<equiv> 
    y \<noteq> x \<and> 
    z \<noteq> x \<and> z \<noteq> y \<and> 
    w \<noteq> x \<and> w \<noteq> y \<and> w \<noteq> z \<and>
    r \<noteq> x \<and> r \<noteq> y \<and> r \<noteq> z \<and> r \<noteq> w \<and>
    s \<noteq> x \<and> s \<noteq> y \<and> s \<noteq> z \<and> s \<noteq> w \<and> s \<noteq> r \<and>
    t \<noteq> x \<and> t \<noteq> y \<and> t \<noteq> z \<and> t \<noteq> w \<and> t \<noteq> r \<and> t \<noteq> s"

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
    S6: "\<lbrakk>k \<in> Lines\<rbrakk> \<Longrightarrow> (\<exists>P Q R . P \<in> k \<and> Q \<in> k \<and> R \<in> k \<and> distinct3 P Q R)" and
    S0a: "\<lbrakk>k \<in> Lines; P \<in> k\<rbrakk> \<Longrightarrow> P \<in> Points" and
    S0b: "\<lbrakk>H \<in> Planes; P \<in> H\<rbrakk> \<Longrightarrow> P \<in> Points"
begin

lemma S2_exists_unique:
  fixes P Q R
  assumes "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points"
  assumes "\<not> collinear P Q R"
  shows "\<exists>! H . H \<in> Planes \<and> P \<in> H \<and> Q \<in> H \<and> R \<in> H" 
  using assms S2a S2b by blast

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

lemma join_commute:
  fixes P Q
  assumes "P \<in> Points" and "Q \<in> Points" and "P \<noteq> Q"
  shows "(join P Q) = (join Q P)"
  using assms S1a S1b by auto
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


lemma S5alt:
  shows "\<exists> A B C D . (A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in>  Points \<and>                                   
(\<not> coplanar A B C D) \<and> 
(\<not> collinear A B C) \<and> 
(\<not> collinear A B D) \<and> 
(\<not> collinear A C D) \<and> 
(\<not> collinear B C D))" using S5 coplanar_def collinear_def by metis

lemma collinear_join [iff] :
  fixes P Q X
  assumes "P \<in> Points \<and> Q \<in> Points \<and> X \<in> Points"
  assumes "P \<noteq> Q"
  shows "collinear P Q X \<longleftrightarrow> X \<in> join P Q"
  using assms collinear_def S1a S1b by fastforce


lemma distinct3_alt [simp]:
  "distinct[A,B,C] \<longleftrightarrow> (A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C)" 
  by auto

lemma fargle:
  fixes S T
  assumes "S \<noteq> T"
  assumes "S \<in> Planes \<and> T \<in> Planes"
  shows "\<exists> k . (k \<in> Lines \<and> k = (S \<inter> T))"
proof -
  obtain k where kfacts: "(k \<in> Lines \<and> k \<subseteq> (S \<inter> T))" using assms S4[of S T] by auto
  obtain  P Q where pqfacts: "P\<in> Points \<and> Q \<in> Points \<and> P \<in> k \<and> Q \<in> k \<and> P \<noteq> Q" using kfacts S6[of k] S0a
  by (metis distinct3_def)
  have u: "P \<in> S \<and> Q \<in> S \<and> P \<in>T \<and> Q\<in> T" using kfacts pqfacts by auto
  fix X 
  have  a0: "X \<in> S\<inter>T \<Longrightarrow> collinear P Q X" for X
  proof (rule ccontr) (* classical contradiction *)
    assume ch: "\<not>collinear P Q X"
    assume minor: "X \<in> S \<inter> T"
    have d: "distinct[P,Q,X]" using pqfacts ch collinear_def kfacts by force
    have b: "\<exists>! H . H \<in> Planes \<and> P \<in> H \<and> Q \<in> H \<and> X \<in> H" using S2a[of P Q X] S2b[of P Q X] d ch distinct3_alt[of P Q X] 
    by (metis Int_iff S0b assms(2) minor u)
    then have "S = T" using assms u ch b minor by auto 
    then show False using assms by auto
  qed
  have a1: "X \<in> S\<inter>T \<Longrightarrow> X \<in> join P Q" using a0 pqfacts
  using S0b assms(2) by auto
  then have a2: "S \<inter> T = join P Q" using S1b a0 kfacts pqfacts
  by (meson IntI assms(1,2) crossing_planes u)
  then show ?thesis by (simp add: S1a pqfacts)
qed

lemma same_joins:
  fixes a b x y
  assumes "a \<in> Points \<and> b \<in> Points \<and> x \<in> Points \<and> y \<in> Points"
  assumes "x \<in> join a b \<and> y \<in> join a b"
  assumes "distinct4 a b x y"
  shows "join x y = join a b"
  using assms
  by (metis S1a S1b distinct4_def)

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
  assumes "distinct [a, b, c]" 
  shows "P = Q"
  using S2a S2b assms collinear_join
  by (simp; metis)

lemma vanadium3:
  fixes x y P Q
  assumes "x \<in> Points \<and> y \<in> Points \<and> P \<in> Planes \<and> Q \<in> Planes"
  assumes "x \<in> P \<and> x \<in> Q \<and> y \<in> P \<and> y \<in> Q"
  assumes "x \<noteq> y"
  shows "P = Q \<or> P \<inter> Q = join x y"
proof -
  obtain L where L_facts: "L \<in> Lines \<and> L \<subseteq> P \<and> L \<subseteq> Q" using S4 assms by metis
  then obtain a b where h: "a \<in> Points \<and> b \<in> Points \<and> a \<noteq> b \<and> a \<in> L \<and> b \<in> L" using S6 S0a
    by (metis distinct3_def)
  then have h1: "L = join a b" using L_facts S1b by auto
  show ?thesis
  proof (cases "\<exists> p . (p \<in> Points \<and> p \<notin> L \<and> p \<in> P \<and> p \<in> Q)")
    case True
    then obtain p where p_facts: "(p \<in> Points \<and> p \<notin> L \<and> p \<in> P \<and> p \<in> Q)" by auto
    then have "distinct [a, b, p]" using h by auto
    then have "P = Q" using vanadium2 p_facts h1 L_facts S2_exists_unique assms 
      by (smt (verit, del_insts) collinear_join h subset_iff)
    then show ?thesis by auto
  next
    case False
    then have "p \<in> Points \<and> p \<in> P \<and> p \<in> Q \<Longrightarrow> p \<in> L" for p by auto
    then have h2: "P \<inter> Q = L" using crossing_planes L_facts S0b assms(1) by auto
    then have "join a b = join x y" using h1 same_joins assms
    by (metis False L_facts S1b)
    then show ?thesis using h1 h2 by auto
  qed
qed

lemma vanadium4:
  fixes x y z w
  assumes "x \<in> Points \<and> y \<in> Points \<and> z \<in> Points \<and> w \<in> Points"
  assumes "distinct4 x y z w"
  assumes "\<not> collinear x y z \<and> \<not> collinear x y w"
  shows "plane_through x y z = plane_through x y w \<or> 
        plane_through x y z \<inter> plane_through x y w = join x y"
proof -
  let ?P = "plane_through x y z"
  let ?Q = "plane_through x y w"
  have "x \<in> ?P \<and> y \<in> ?P \<and> x \<in> ?Q \<and> y \<in> ?Q" using S2a assms by auto
  then show ?thesis using vanadium3[of x y ?P ?Q] assms S2a distinct4_def by metis
qed
  

lemma two_point_line_in_plane0:
  fixes A B P
  assumes "P \<in> Planes"
  assumes "A \<in> Points" and "B \<in> Points"
  assumes "A \<in> P" and "B \<in> P"
  assumes "A \<noteq> B"
  shows "join A B \<subseteq> P" 
proof (rule ccontr)
  let ?AB = "join A B"
  assume cd: "\<not> (?AB \<subseteq> P)"
  then have Punq: "\<forall>Q \<in> Planes. A \<in> Q \<and> B \<in> Q \<longrightarrow> Q = P"
    using assms crossing_planes S1b by fastforce
  then have CABCP: "\<forall>C \<in> Points. C \<notin> ?AB \<longrightarrow> C \<in> P" 
    using assms S1b S2a unfolding collinear_def by (smt (verit))
  obtain X Y Z W where XYZWdef: "X \<in> Points \<and> Y \<in> Points \<and> Z \<in> Points 
    \<and> W \<in> Points \<and> \<not> coplanar X Y Z W \<and> \<not> collinear X Y Z \<and> \<not> collinear X Y W 
    \<and> \<not> collinear X Z W \<and> \<not> collinear Y Z W" using S5 by auto
  then have XYZWdist: "distinct4 X Y Z W" using S5_dist by simp
  have X00: "\<nexists>X0 Y0. {X0,Y0} \<subseteq> {X,Y,Z,W} \<and> X0 \<in> ?AB \<and> Y0 \<in> ?AB \<and> X0 \<noteq> Y0"
  proof (rule ccontr)
    assume cd1: "\<not> (\<nexists>X0 Y0. {X0,Y0} \<subseteq> {X,Y,Z,W} \<and> X0 \<in> ?AB \<and> Y0 \<in> ?AB \<and> X0 \<noteq> Y0)"
    then obtain X0 Y0 where X0Y0def: "{X0,Y0} \<subseteq> {X,Y,Z,W} \<and> X0 \<in> ?AB \<and> Y0 \<in> ?AB
      \<and> X0 \<noteq> Y0" by auto
    then have ABX0Y0: "?AB = (join X0 Y0)" using assms S0a S1a S1b by metis
    obtain Z0 W0 where Z0W0def: "{Z0,W0} \<subseteq> {X,Y,Z,W} \<and> Z0 \<noteq> W0 \<and> Z0 \<noteq> X0 \<and> Z0 \<noteq> Y0
      \<and> W0 \<noteq> X0 \<and> W0 \<noteq> Y0" using XYZWdist
      by (metis distinct4_def insert_mono subset_insertI subset_insertI2)
    then have X0Y0Z0W0ncop: "\<not> coplanar X0 Y0 Z0 W0"
      using X0Y0def XYZWdef coplanar_def by fastforce
    have X0Y0Z0ncoll: "\<not> collinear X0 Y0 Z0" and X0Y0W0ncoll: "\<not> collinear X0 Y0 W0"
      and X0Z0W0ncoll: "\<not> collinear X0 Z0 W0" and Y0Z0W0ncoll: "\<not> collinear Y0 Z0 W0"
      using X0Y0def XYZWdef Z0W0def collinear_def
      by (smt (verit, ccfv_threshold) empty_iff insert_iff insert_subset)+
    then have "(plane_through X0 Y0 Z0) \<noteq> (plane_through X0 Y0 W0)"
      by (smt (verit, del_insts) S2a X0Y0def XYZWdef Z0W0def coplanar_def empty_iff
          insert_iff insert_subset)
    then obtain l where ldef: "l \<in> Lines \<and> l = (plane_through X0 Y0 Z0) \<inter> (plane_through X0 Y0 W0)"
      by (smt (verit, ccfv_threshold) S2a X0Y0W0ncoll X0Y0Z0ncoll X0Y0def XYZWdef Z0W0def
          crossing_planes empty_iff insert_iff insert_subset)
    have "X0 \<in> (plane_through X0 Y0 Z0) \<and> Y0 \<in> (plane_through X0 Y0 Z0)
      \<and> X0 \<in> (plane_through X0 Y0 W0) \<and> Y0 \<in> (plane_through X0 Y0 W0)"
      using S2a X0Y0W0ncoll X0Y0Z0ncoll X0Y0def XYZWdef Z0W0def by auto
    then have "l = ?AB" using ldef ABX0Y0
      by (metis Int_iff S0a S1b X0Y0def)
    then have "A \<in> (plane_through X0 Y0 Z0) \<and> B \<in> (plane_through X0 Y0 Z0)
      \<and> A \<in> (plane_through X0 Y0 W0) \<and> B \<in> (plane_through X0 Y0 W0)"
      using S1a assms(2,3,6) ldef by auto
    then show False using Punq S0a S2a X0Y0Z0ncoll X0Y0def XYZWdef Z0W0def 
       \<open>l = join A B\<close> cd empty_iff inf_commute inf_le2 insert_commute insert_iff 
       insert_subset ldef by metis
  qed
  have "\<exists>X0 Y0 Z0. {X0,Y0,Z0} \<subseteq> {X,Y,Z,W} \<and> X0 \<notin> ?AB
    \<and> Y0 \<notin> ?AB \<and> Z0 \<notin> ?AB \<and> distinct3 X0 Y0 Z0"
  proof (rule ccontr)
    assume cd2: "\<not> (\<exists>X0 Y0 Z0. {X0,Y0,Z0} \<subseteq> {X,Y,Z,W} \<and> X0 \<notin> ?AB
      \<and> Y0 \<notin> ?AB \<and> Z0 \<notin> ?AB \<and> distinct3 X0 Y0 Z0)"
    then have "\<forall>X0 Y0 Z0. {X0,Y0,Z0} \<subseteq> {X,Y,Z,W} \<and> X0 \<notin> ?AB \<and> Y0 \<notin> ?AB
      \<and> distinct3 X0 Y0 Z0 \<longrightarrow> Z0 \<in> ?AB" by meson
    then have "\<exists>X0 Y0. {X0,Y0} \<subseteq> {X,Y,Z,W} \<and> X0 \<in> ?AB \<and> Y0 \<in> ?AB \<and> X0 \<noteq> Y0"
      sorry
    then show False using X00 by blast
  qed
  then obtain X0 Y0 Z0 where X0Y0Z0def: "{X0,Y0,Z0} \<subseteq> {X,Y,Z,W} \<and> X0 \<notin> ?AB
    \<and> Y0 \<notin> ?AB \<and> Z0 \<notin> ?AB \<and> distinct3 X0 Y0 Z0" by presburger
  then obtain W0 where W0def: "W0 \<in> {X,Y,Z,W} \<and> distinct4 X0 Y0 Z0 W0"
    by (metis XYZWdist distinct3_def distinct4_def insertCI)
  then have X0Y0Z0W0ncop: "\<not> coplanar X0 Y0 Z0 W0"
      using X0Y0Z0def XYZWdef coplanar_def unfolding distinct4_def sorry
  have X0Y0Z0ncoll: "\<not> collinear X0 Y0 Z0" and X0Y0W0ncoll: "\<not> collinear X0 Y0 W0"
    and X0Z0W0ncoll: "\<not> collinear X0 Z0 W0" and Y0Z0W0ncoll: "\<not> collinear Y0 Z0 W0"
    using X0Y0Z0def XYZWdef W0def collinear_def sorry
  have "X0 \<in> P \<and> Y0 \<in> P \<and> Z0 \<in> P" using X0Y0Z0def CABCP
    using XYZWdef by blast
  then have X0Y0Z0P: "(plane_through X0 Y0 Z0) = P" using X0Y0Z0ncoll
    using S0b S2b assms(1) by auto
  then have "W0 \<notin> (plane_through X0 Y0 Z0)"
    using S0b X0Y0Z0W0ncop \<open>X0 \<in> P \<and> Y0 \<in> P \<and> Z0 \<in> P\<close> assms(1) coplanar_def
    by force
  then have W0AB: "W0 \<in> ?AB" using CABCP W0def X0Y0Z0P XYZWdef by blast
  then show False sorry
qed

end
end