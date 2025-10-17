theory "Chapter4-3"
  imports Complex_Main  "Chapter4-2" "Chapter1-1"

begin
text\<open> start at  "Harmonic points", stop just before "Perspectivies and Projectivities"\<close>



text\<open>an ordered quadruple of distinct points A,B,C,D on a line is a harmonic quadruple if there is
is a complete quadrangle X,Y,Z,W such that A and B are diagonal points of the complete quadrangle. 
This is denoted H(AB,CD) if A,B,C,D form a harmonic quadruple\<close>

text\<open>\jackson \oliver\<close>
definition (in projective_plane) harmonic_quadruple :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  where "harmonic_quadruple A B C D = (if
    (A \<in> Points) \<and> (B \<in> Points) \<and> (C \<in> Points) \<and> (D \<in> Points)
    then (\<exists>l X Y Z W.
    l \<in> Lines \<and> incid A l \<and> incid B l \<and> incid C l \<and> incid D l \<and>
    X \<in> Points \<and> Y \<in> Points \<and> Z \<in> Points \<and> W \<in> Points \<and>
    cquadrangle X Y Z W \<and>
    A = meet (join X Y) (join Z W) \<and> B = meet (join X Z) (join Y W) \<and>
    incid C (join X W) \<and> incid D (join Y Z))\<and> (distinct[A,B,C,D])
    else undefined)"
text\<open>\done\<close>

text\<open>Lemma: if A,B,C,D are distinct, the diagonal points of a defining quadrangle XYZW aren't 
collinear\<close>

text\<open>\jackson \oliver\<close>
lemma diagonal_points_noncollinear:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes A B C D::"'p"
  fixes X Y Z W::"'p"
  assumes pp: "projective_plane Points Lines incid"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points"
  assumes "cquadrangle X Y Z W"
  assumes "harmonic_quadruple A B C D"
  (*assume also that we have a complete quadrilateral and need to say that that additional Q (diagonal) isn't collinear with A B*)
  shows "\<not>(\<exists>l. l \<in> Lines \<and> incid A l \<and> incid B l \<and> incid Q l)"
  sorry
text\<open>\done\<close>


text\<open>Proposition 4.5. $H(AB,CD)\iff H(BA,CD)\iff H(AB,DC)\iff H(BA,DC).$\<close>

text\<open>\jackson \oliver\<close>
theorem (in projective_plane) p4_5:
  fixes A B C D::"'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  shows "harmonic_quadruple A B C D \<longleftrightarrow> 
         harmonic_quadruple B A C D \<and>
         harmonic_quadruple B A C D \<longleftrightarrow> 
         harmonic_quadruple A B D C \<and>
         harmonic_quadruple A B D C \<longleftrightarrow> 
         harmonic_quadruple B A D C"
  sorry
text\<open>\done\<close>

text\<open>Proposition 4.6. A,B,C are distinct points on a line. Assume p7. There's a point D such that
H(AB,CD). Also, assuming P5, D is unique.\<close>

text\<open>\oliver \jackson\<close>
theorem (in projective_plane) p4_6_existence:
  fixes A B C ::"'p"
  fixes l :: "'l"
  assumes "A \<in> Points" and "B \<in> Points" and "C \<in> Points"
  assumes "l\<in>Lines"
  assumes "incid A l" and "incid B l" and "incid C l"
  assumes "distinct [A,B,C]"
  assumes p7 (*comes from 4_2*)
  shows "\<exists>D. D\<in>Points\<and>harmonic_quadruple A B C D"
  sorry
text\<open>\done\<close>

text\<open>\jackson \oliver\<close>
theorem (in projective_plane) p4_6_uniqueness:
  fixes A B C D E ::"'p"
  fixes l :: "'l"
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points \<and> E \<in> Points"
  assumes "l\<in>Lines"
  assumes "incid A l" and "incid B l" and "incid C l"
  assumes p7
  assumes "harmonic_quadruple A B C D"
  assumes p5
  assumes "harmonic_quadruple A B C E"
  shows "D=E"
  sorry 
text \<open>\done\<close>

text\<open>Definition: fourth harmonic point of A,B,C is the D satisfying 4.6.\<close>

text\<open>\oliver \jackson\<close>
text\<open>Proposition 4.7. AB,CD are four harmonic points. Assuming P5, then CD,AB are four harmonic
points.\<close>
theorem (in projective_plane) p4_7:
  fixes A B C D ::"'p"
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points"
  assumes p5
  assumes "harmonic_quadruple A B C D"
  shows "harmonic_quadruple C D A B"
  sorry 
text\<open>\done\<close>

text\<open>\oliver \jackson\<close>
text\<open>Proposition 4.7B. Inverse direction of p4_7\<close>
theorem (in projective_plane) p4_7b:
  fixes A B C D::"'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  assumes p5
  shows "harmonic_quadruple A B C D\<longleftrightarrow>harmonic_quadruple C D A B"
proof -
  show ?thesis using p4_7 assms by blast
qed
text\<open>\done\<close>

text\<open>\oliver \jackson\<close>
text\<open>Proposition 4.7C. The really big implication after Proposition 4.7. Hopefully will be useful for harmonic stuff\<close>
theorem (in projective_plane) p4_7c:
  fixes A B C D::"'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  assumes p5
  shows "harmonic_quadruple D C B A \<longleftrightarrow>
         harmonic_quadruple C D B A \<and>
         harmonic_quadruple C D B A \<longleftrightarrow>
         harmonic_quadruple D C A B \<and>
         harmonic_quadruple D C A B \<longleftrightarrow>
         harmonic_quadruple C D A B \<and>
         harmonic_quadruple C D A B \<longleftrightarrow>
         harmonic_quadruple A B C D \<and>
         harmonic_quadruple A B C D \<longleftrightarrow> 
         harmonic_quadruple B A C D \<and>
         harmonic_quadruple B A C D \<longleftrightarrow> 
         harmonic_quadruple A B D C \<and>
         harmonic_quadruple A B D C \<longleftrightarrow> 
         harmonic_quadruple B A D C"
proof -
  show ?thesis using assms p4_7b p4_5 by (smt (z3))
qed
text\<open>\done\<close>

end

