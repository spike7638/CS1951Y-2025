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

definition (in projective_plane) cquadrangle_points :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p set"
  where "cquadrangle_points A B C D = (if (cquadrangle A B C D) 
  then({meet (join B C) (join A D), 
        meet (join A C) (join B D), 
        meet (join A B) (join C D)})
  else undefined)"


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
    distinct7 U A B C A' B' C';
    pcollinear A A' U; pcollinear B B' U; pcollinear C C' U;
    \<not>pcollinear A B C; \<not>pcollinear A' B' C'; 
    join A B \<noteq> join A' B'; join A C \<noteq> join A' C'; join B C \<noteq> join B' C';
    P = meet (join A B) (join A' B');
    Q = meet (join A C) (join A' C');
    R = meet (join B C)  (join B' C')\<rbrakk> \<Longrightarrow> pcollinear P Q R"
begin
end

(*
lemma P7:
  fixes A B C D
  fixes E F G
  assumes "cquadrangle A B C D"
  assumes "E \<in> Points \<and> F \<in> Points \<and> G \<in> Points" 
  assumes "{E, F, G} = cquadrangle_points A B C D"
  shows "\<not>pcollinear E F G"
  sorry
*)

theorem rp2_P7:
  fixes A B C D
  fixes E F G
  assumes "A \<in> rp2_Points \<and> B \<in> rp2_Points \<and> C \<in> rp2_Points \<and> D \<in> rp2_Points \<and> E \<in> rp2_Points \<and> F \<in> rp2_Points \<and> G \<in> rp2_Points"
  assumes "cquadrangle A B C D"
  assumes "{E, F, G} = cquadrangle_points A B C D"
  shows "\<not>pcollinear E F G"
  sorry 

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

definition (in projective_plane) cquadrilateral_lines :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l set"
  where "cquadrilateral_lines a b c d = (if (cquadrilateral a b c d) 
  then({join (meet a b) (meet c d),
        join (meet a c) (meet b d),
        join (meet a d) (meet b c)})
  else undefined)"

end


