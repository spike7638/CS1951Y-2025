theory "Chapter4-3"
  imports Complex_Main  "Chapter4-2" "Chapter1-1"

begin
text\<open> start at  "Harmonic points", stop just before "Perspectivies and Projectivities"\<close>



text\<open>an ordered quadruple of distinct points A,B,C,D on a line is a harmonic quadruple if there is
is a complete quadrangle X,Y,Z,W such that A and B are diagonal points of the complete quadrangle. 
This is denoted H(AB,CD) if A,B,C,D form a harmonic quadruple\<close>

definition harmonic_quadruple :: "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  where "harmonic_quadruple Points Lines incid A B C D \<equiv>
    A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points \<and>
    distinct [A,B,C,D] \<and>
    (\<exists>l. l \<in> Lines \<and> incid A l \<and> incid B l \<and> incid C l \<and> incid D l) \<and>
    STILL NEED DEF OF COMPLETE QUADRILATERAL"


text\<open>Lemma: if A,B,C,D are distinct, the diagonal points of a defining quadrangle XYZW aren't 
collinear\<close>

text\<open>\oliver\<close>
lemma diagonal_points_noncollinear:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes A B C D::"'p"
  fixes X Y Z W::"'p"
  assumes "distinct[A,B,C,D]"
  assumes pp: "projective_plane Points Lines incid"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points"
  (*assume also that we have a complete quadrilateral*)
  shows "\<not>(\<exists>l. l \<in> Lines \<and> incid X l \<and> incid Y l \<and> incid Z l \<and> incid W l)"
  sorry
text\<open>\done\<close>


text\<open>Proposition 4.5. $H(AB,CD)\iff H(BA,CD)\iff H(AB,DC)\iff H(BA,DC).$\<close>

text\<open>\oliver\<close>
theorem p4_5:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes A B C D::"'p"
  assumes pp: "projective_plane Points Lines incid"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  assumes "distinct [A,B,C,D]"
  shows "harmonic_quadruple Points Lines incid A B C D \<longleftrightarrow> 
         harmonic_quadruple Points Lines incid B A C D \<and>
         harmonic_quadruple Points Lines incid B A C D \<longleftrightarrow> 
         harmonic_quadruple Points Lines incid A B D C \<and>
         harmonic_quadruple Points Lines incid A B D C \<longleftrightarrow> 
         harmonic_quadruple Points Lines incid B A D C"
  sorry
text\<open>\done\<close>

text\<open>Proposition 4.6. A,B,C are distinct points on a line. Assume p7. There's a point D such that
H(AB,CD). Also, assuming P5, D is unique.\<close>

theorem p4_6_existence:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes A B C ::"'p"
  assumes pp: "projective_plane Points Lines incid"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points"
  assumes "distinct [A,B,C]"
  assumes p7
  shows "\<exists>D. D\<in>Points\<and>harmonic_quadruple Points Lines incid A B C D"
  sorry

theorem p4_6_uniqueness:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes A B C D ::"'p"
  assumes pp: "projective_plane Points Lines incid"
  assumes "A \<in> Points\<and>B \<in> Points\<and>C \<in> Points\<and>D\<in>Points"
  assumes "distinct [A,B,C,D]"
  assumes p7
  assumes "harmonic_quadruple Points Lines incid A B C D"
  assumes p5
  assumes "\<exists>D'. D'\<in>Points\<and>harmonic_quadruple Points Lines incid A B C D'"
  shows "D=D'"
  sorry 
  

text\<open>Definition: fourth harmonic point of A,B,C is the D satisfying 4.6.\<close>

text\<open>Proposition 4.7. AB,CD are four harmonic points. Assuming P5, then CD,AB are four harmonic
points.\<close>
theorem p4_7:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes A B C D ::"'p"
  assumes pp: "projective_plane Points Lines incid"
  assumes "A \<in> Points\<and>B \<in> Points\<and>C \<in> Points\<and>D\<in>Points"
  assumes "distinct [A,B,C,D]"
  assumes p5
  assumes "harmonic_quadruple Points Lines incid A B C D"
  shows "harmonic_quadruple Points Lines incid C D A B"
  sorry 

end

