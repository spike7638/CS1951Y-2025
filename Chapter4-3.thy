theory "Chapter4-3"
  imports Complex_Main  "Chapter4-2" "Chapter1-1"

begin
text\<open> start at  "Harmonic points", stop just before "Perspectivies and Projectivities"\<close>

text\<open>an ordered quadruple of distinct points A,B,C,D on a line is a harmonic quadruple if there is
is a complete quadrangle X,Y,Z,W such that A and B are diagonal points of the complete quadrangle. 
This is denoted H(AB,CD) if A,B,C,D form a harmonic quadruple\<close>

text\<open>\jackson \oliver\<close>
(* WE SHOULD COMMENT THIS OUT UPON PUSH -- FIX WHEN LOCALE SITUATION IS RESOLVED *)
proposition (in projective_plane) P5:
  fixes A B C D E F Z P Q R (* D E F = A' B' C', Z = O *)
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points \<and> E \<in> Points \<and>
           F \<in> Points \<and> Z \<in> Points \<and> P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points"
  assumes "distinct [A, B, C, D, E, F, Z]" 
  assumes "\<not>pcollinear A B C"
  assumes "\<not>pcollinear D E F"
  assumes "P = meet (join A B) (join D E)"
  assumes "Q = meet (join B C) (join E F)"
  assumes "R = meet (join A C) (join D F)"
  assumes "incid Z (join A D)"
  assumes "incid Z (join B E)"
  assumes "incid Z (join C F)"
  
  shows "pcollinear P Q R"
  sorry
text\<open>\done\<close>


text\<open>\jackson \oliver\<close>
(* WE SHOULD COMMENT THIS OUT UPON PUSH -- FIX WHEN LOCALE SITUATION IS RESOLVED *)
(* This is equivalent to the P5 above. I am not sure which will be easier to work with *)
proposition (in projective_plane) P5_equivalent:
  fixes A B C D E F Z P Q R (* D E F = A' B' C', Z = O *)
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points \<and> E \<in> Points \<and>
           F \<in> Points \<and> Z \<in> Points \<and> P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points"
  assumes "distinct [A, B, C, D, E, F, Z]" 
  assumes "\<not>pcollinear A B C"
  assumes "\<not>pcollinear D E F"
  assumes "P = meet (join A B) (join D E)"
  assumes "Q = meet (join B C) (join E F)"
  assumes "R = meet (join A C) (join D F)"
  assumes "pcollinear Z A D"
  assumes "pcollinear Z B E"
  assumes "pcollinear Z C F"
  
  shows "pcollinear P Q R"
  sorry
text\<open>\done\<close>


text\<open>\jackson \oliver\<close>
(* WE SHOULD COMMENT THIS OUT UPON PUSH -- FIX WHEN LOCALE SITUATION IS RESOLVED *)
proposition (in projective_plane) P7:
  fixes X Y Z W::"'p"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points"
  assumes "cquadrangle X Y Z W"
  shows "\<not> pcollinear  (meet (join Y Z) (join X W))
                       (meet (join X Z) (join Y W))
                       (meet (join X Y) (join Z W))"
  sorry
text\<open>\done\<close>

text\<open>\jackson \oliver\<close>
lemma (in projective_plane) quadrangle_order:
  fixes X Y Z W::"'p"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points"
  assumes "cquadrangle X Y Z W"
  shows "cquadrangle X Y W Z \<and> 
         cquadrangle X W Y Z \<and>
         cquadrangle X W Z Y \<and>
         cquadrangle Y X W Z \<and> 
         cquadrangle Y W X Z \<and>
         cquadrangle Y W Z X \<and>
         cquadrangle Y X W Z \<and> 
         cquadrangle Z W Y X \<and>
         cquadrangle Z W X Y \<and>
         cquadrangle Z Y W X \<and> 
         cquadrangle Z W Y X \<and>
         cquadrangle W X Z Y \<and>
         cquadrangle W Y X Z \<and> 
         cquadrangle W X Y Z \<and>
         cquadrangle W X Z Y"
proof -
  show ?thesis using assms using cquadrangle_def pcollinear_def by force
qed

text\<open>\jackson \oliver\<close>
definition (in projective_plane) harmonic_quadruple :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  where "harmonic_quadruple A B C D = (if
    (A \<in> Points) \<and> (B \<in> Points) \<and> (C \<in> Points) \<and> (D \<in> Points)
    then (\<exists>l X Y Z W.
    l \<in> Lines \<and> incid A l \<and> incid B l \<and> incid C l \<and> incid D l \<and>
    X \<in> Points \<and> Y \<in> Points \<and> Z \<in> Points \<and> W \<in> Points \<and>
    cquadrangle X Y Z W \<and>
    A = meet (join X Y) (join Z W) \<and> B = meet (join X Z) (join Y W) \<and>
    incid C (join X W) \<and> incid D (join Y Z)) \<and> (distinct[A,B,C,D])
    else undefined)"
text\<open>\done\<close>

text\<open>Lemma: if A,B,C,D are distinct, the diagonal points of a defining quadrangle XYZW aren't 
collinear\<close>

text\<open>\jackson \oliver\<close>
lemma (in projective_plane) quadrangle_points_distinct:
  fixes X Y Z W::"'p"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points"
  assumes "cquadrangle X Y Z W"
  shows "distinct[X, Y, Z, W]"
proof (rule ccontr)
  assume ch:  "\<not>distinct[X, Y, Z, W]"
  show False
  proof -
    have 0: "X = Y \<or>
             X = Z \<or> 
             X = W \<or> 
             Y = Z \<or> 
             Y = W \<or>
             Z = W" using assms ch by auto
    show ?thesis using 0 assms cquadrangle_def by (metis p1 p3 pcollinear_def)
  qed
qed
text\<open>\done\<close>

text\<open>\jackson \oliver\<close>
lemma (in projective_plane) collinear_helper:
  fixes A B C D:: "'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  assumes "pcollinear A B C"
  assumes "pcollinear A B D"
  assumes "distinct[A, B, C, D]"
  shows "pcollinear A C D"
proof -
  show ?thesis unfolding pcollinear_def using assms 
    by (smt (verit) distinct_length_2_or_more pcollinear_def unique_meet)
qed

text\<open>\jackson \oliver\<close>
lemma (in projective_plane) incid_join_collinear:
  fixes A B C :: "'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" 
  assumes "incid A (join B C)"
  shows "pcollinear A B C"
proof -
  show ?thesis using assms by (metis join_properties1 p3 pcollinear_def)
qed
text\<open>\done\<close>

text\<open>\jackson \oliver\<close>
lemma (in projective_plane) cquadrangle_joins_distinct:
  fixes X Y Z W::"'p"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points"
  assumes "cquadrangle X Y Z W"
  shows "(join X W) \<noteq> (join Y Z)"
proof -
  show ?thesis using assms
    by (metis cquadrangle_def distinct_length_2_or_more join_properties1 pcollinear_def quadrangle_points_distinct)
qed
text\<open>\done\<close>

text\<open>\jackson \oliver\<close>
lemma (in projective_plane) meet_implies_incid:
  fixes X Y Z W Q::"'p"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points" "Q \<in> Points"
  assumes "distinct[X, Y, Z, W]"
  assumes "Q = meet (join X W) (join Y Z)"
  assumes "(join X W) \<noteq> (join Y Z)"

  shows "incid Q (join X W) \<and> incid Q (join Y Z)"
proof -
  have 0: "incid Q (join X W)" using assms meet_properties2 join_properties1 by auto
  have 1: "incid Q (join Y Z)" using assms meet_properties2 join_properties1 by auto
  show ?thesis using 0 1 by auto
qed
text\<open>\done\<close>

text\<open>\jackson \oliver\<close>
lemma (in projective_plane) diagonal_points_distinct:
  fixes X Y Z W P Q R::"'p"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points" "P \<in> Points" "Q \<in> Points" "R \<in> Points"
  assumes "cquadrangle X Y Z W"
  assumes "P = meet (join X Y) (join Z W)"
  assumes "Q = meet (join X Z) (join Y W)"
  assumes "R = meet (join X W) (join Y Z)"
  shows "distinct[P, Q, R]"
proof -
  show ?thesis using assms 
  by (smt (z3) cquadrangle_joins_distinct distinct_length_2_or_more distinct_singleton join_properties1
      meet_implies_incid quadrangle_order quadrangle_points_distinct unique_meet)
qed
text\<open>\done\<close>

text\<open>\jackson \oliver\<close>
lemma (in projective_plane) quadrangle_all_points_distinct:
  fixes X Y Z W P Q R::"'p"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points" "P \<in> Points" "Q \<in> Points" "R \<in> Points"
  assumes "cquadrangle X Y Z W"
  assumes "P = meet (join X Y) (join Z W)"
  assumes "Q = meet (join X Z) (join Y W)"
  assumes "R = meet (join X W) (join Y Z)"
  shows "distinct[X, Y, Z, W, P, Q, R]"
proof - (* This lemma heavily relies on strong provers and helper lemmas which also use strong proves, maybe we can simplify it somehow *)
  have 0: "distinct[X, Y, Z, W]" using assms quadrangle_points_distinct by auto
  have 1: "distinct[P, Q, R]" using assms diagonal_points_distinct by auto
  have 2: "distinct[X, Y, Z, W, P]" using assms 0 
      by (smt (verit, del_insts) cquadrangle_def diagonal_points_distinct distinct_length_2_or_more join_properties1
      meet_properties2 pcollinear_def)
  have 3: "distinct[X, Y, Z, W, Q]" using assms 0 
      by (smt (verit, del_insts) cquadrangle_def diagonal_points_distinct distinct_length_2_or_more join_properties1
      meet_properties2 pcollinear_def)
  have 4: "distinct[X, Y, Z, W, R]" using assms 0 
      by (smt (verit, del_insts) cquadrangle_def diagonal_points_distinct distinct_length_2_or_more join_properties1
      meet_properties2 pcollinear_def)
  show ?thesis using 1 2 3 4 by auto
qed
text\<open>\done\<close>


text\<open>\Jackson \Oliver\<close>
lemma (in projective_plane) harmonic_and_quadrangle_all_points_distinct:
  fixes X Y Z W P Q R A B C D::"'p"
  (* ASSUMES P7*)
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points" "R \<in> Points"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  assumes "cquadrangle X Y Z W"
  assumes "R = meet (join X W) (join Y Z)"
  assumes "harmonic_quadruple A B C D"
  assumes "A = meet (join X Y) (join Z W)" "B = meet (join X Z) (join Y W)" 
  assumes "incid C (join X W)"  "incid D (join Y Z)"
  shows "distinct[X, Y, Z, W, A, B, R, C, D]"
 proof -
  have 0: "distinct[X, Y, Z, W, A, B, R]" using assms quadrangle_all_points_distinct by metis
  have 1: "distinct[A, B, C, D]" using assms harmonic_quadruple_def by auto
  have 2: "distinct[X, Y, Z, W, A, B, R, C]"
  proof (rule ccontr)
    assume ch: "\<not>distinct[X, Y, Z, W, A, B, R, C]"
    show False
    proof -
      have ch2: "C = X \<or> C = Y \<or> C = Z \<or> C = W \<or> C = A  \<or> C = B \<or> C = R" using ch 0 by auto
      show ?thesis using assms ch2
      by (smt (verit) cquadrangle_def[of X Y Z W] distinct_length_2_or_more harmonic_quadruple_def[of A B C D] incid_join_collinear join_properties1
          join_properties2 meet_properties2)
    qed
  qed

  have 3: "distinct[X, Y, Z, W, A, B, R, D]"
  proof (rule ccontr)
    assume ch: "\<not>distinct[X, Y, Z, W, A, B, R, D]"
    show False
    proof -
      have ch2: "D = X \<or> D = Y \<or> D = Z \<or> D = W \<or> D = A  \<or> D = B \<or> D = R" using ch 0 by auto
      show ?thesis using assms ch2 
      by (smt (verit) cquadrangle_def[of X Y Z W] distinct_length_2_or_more harmonic_quadruple_def[of A B C D] incid_join_collinear join_properties1
          join_properties2 meet_properties2)
    qed
  qed

  show ?thesis using 1 2 3 by auto
qed
text\<open>\done\<close>



text\<open>\jackson \oliver\<close>
lemma (in projective_plane) diagonal_points_noncollinear:
  fixes A B C D Q::"'p"
  fixes X Y Z W::"'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points" "Q \<in> Points"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points"
  assumes "cquadrangle X Y Z W"
  assumes "harmonic_quadruple A B C D"
  assumes "Q = meet (join X W) (join Y Z)"
  (* We need to connect XYZW and ABCD through the definition of a harmonic quadruple*)
  (* Otherwise, we have an arbitrary harmonic quadruple and complete quadrangle that are unrelated *)
  (* Assumes P7  *)
  assumes "A = meet (join X Y) (join Z W)" "B = meet (join X Z) (join Y W)" 
  assumes "incid C (join X W)"  "incid D (join Y Z)"
  shows "\<not>(\<exists>l. l \<in> Lines \<and> incid A l \<and> incid B l \<and> incid Q l)"
proof (rule ccontr)
  assume ch: "\<not>\<not>(\<exists>l. l \<in> Lines \<and> incid A l \<and> incid B l \<and> incid Q l)"
  show False
  proof -
    have 0: "(\<exists>l. l \<in> Lines \<and> incid A l \<and> incid B l \<and> incid Q l)" using ch by auto
    (* diag_l is the line containing the three diagonal points of quadrangle XYZW *)
    obtain diag_l where 1: "diag_l \<in> Lines \<and> incid A diag_l \<and> incid B diag_l \<and> incid Q diag_l" using 0 by auto

    have 2: "\<not>pcollinear Q B A" using assms P7[of X Y Z W] by (smt (verit, ccfv_threshold) meet_def meet_properties2 unique_meet)
    show ?thesis using 0 1 2 assms P7[of X Y Z W] pcollinear_def by auto
  qed
qed
text\<open>\done\<close>

text\<open>\jackson \oliver\<close>
theorem (in projective_plane) harmonic_swap_first_pair:
  fixes A B C D::"'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  assumes "harmonic_quadruple A B C D"
  shows "harmonic_quadruple B A C D"
proof -
 obtain l X Y Z W where harmon: "l \<in> Lines \<and> incid A l \<and> incid B l \<and> incid C l \<and> incid D l \<and>
    X \<in> Points \<and> Y \<in> Points \<and> Z \<in> Points \<and> W \<in> Points \<and>
    cquadrangle X Y Z W \<and>
    A = meet (join X Y) (join Z W) \<and> B = meet (join X Z) (join Y W) \<and>
    incid C (join X W) \<and> incid D (join Y Z) \<and> (distinct[A,B,C,D])" using assms harmonic_quadruple_def by auto

      have 1: "cquadrangle X Z Y W" using harmon quadrangle_order by auto
      have 2: "B = meet (join X Z) (join Y W)" using harmon by auto
      have 3: "A = meet (join X Y) (join Z W)" using harmon by auto
      

      show ?thesis unfolding harmonic_quadruple_def using assms 1 2 3 harmon
        by (smt (verit, ccfv_threshold) distinct_length_2_or_more join_properties1 join_properties2)
    qed
text\<open>\done\<close>

text\<open>\jackson \oliver\<close>
theorem (in projective_plane) harmonic_swap_second_pair:
  fixes A B C D::"'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  assumes "harmonic_quadruple A B C D"
  shows "harmonic_quadruple A B D C"
proof -
 obtain l X Y Z W where harmon: "l \<in> Lines \<and> incid A l \<and> incid B l \<and> incid C l \<and> incid D l \<and>
    X \<in> Points \<and> Y \<in> Points \<and> Z \<in> Points \<and> W \<in> Points \<and>
    cquadrangle X Y Z W \<and>
    A = meet (join X Y) (join Z W) \<and> B = meet (join X Z) (join Y W) \<and>
    incid C (join X W) \<and> incid D (join Y Z) \<and> (distinct[A,B,C,D])" using assms harmonic_quadruple_def by auto

  have 1: "cquadrangle Y X W Z" using harmon quadrangle_order by auto
  have 2: "incid C (join X W)" using harmon by auto
  have 3: "incid D (join Y Z)" using harmon by auto
      

  show ?thesis unfolding harmonic_quadruple_def using assms 1 2 3 harmon 
    by (smt (z3) distinct_length_2_or_more join_properties1 meet_properties2 quadrangle_points_distinct unique_meet)
qed 
text\<open>\done\<close>


text\<open>Proposition 4.5. $H(AB,CD)\iff H(BA,CD)\iff H(AB,DC)\iff H(BA,DC).$\<close>
text\<open>\jackson \oliver\<close>
theorem (in projective_plane) p4_5:
  fixes A B C D::"'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
 (* assume P7 *)
  shows "harmonic_quadruple A B C D \<longleftrightarrow> 
         harmonic_quadruple B A C D \<and>
         harmonic_quadruple B A C D \<longleftrightarrow> 
         harmonic_quadruple A B D C \<and>
         harmonic_quadruple A B D C \<longleftrightarrow> 
         harmonic_quadruple B A D C"
proof -
  show ?thesis using assms harmonic_swap_first_pair harmonic_swap_second_pair by blast
qed
text\<open>\done\<close>

    
text\<open>Proposition 4.6. A,B,C are distinct points on a line. Assume p7. There's a point D such that
H(AB,CD). Also, assuming P5, D is unique.\<close>

text\<open>\oliver \jackson\<close>
theorem (in projective_plane) p4_6_existence:
  fixes A B C ::"'p"
  assumes "A \<in> Points" and "B \<in> Points" and "C \<in> Points"
  assumes "pcollinear A B C"
  assumes "distinct [A,B,C]"
  (* Assume P7 *)
  (* Showing distinctness of the obtained lines may simplify the smt / metis proofs *)
  shows "\<exists>D. D \<in> Points \<and> harmonic_quadruple A B C D"
proof -
  obtain h where collin: "h \<in> Lines \<and> (incid A h)  \<and> (incid B h)  \<and> (incid C h)" using assms pcollinear_def by auto

  obtain l m where 
    0: "l \<in> Lines \<and> m \<in> Lines \<and> (incid A l) \<and> (incid A m) \<and> l \<noteq> m \<and> l \<noteq> h \<and> h \<noteq> m " using assms sorry

  obtain n where 1: "n \<in> Lines \<and> (incid C n) \<and> n \<noteq> h" using 0 collin sorry

  obtain r where r_fact: "r \<in> Lines \<and> r = (join B (meet l n))" 
    by (metis 0 1 assms(1,2,3,5) collin distinct_length_2_or_more join_properties1 meet_properties2 unique_meet) 

  obtain s where s_fact: "s \<in> Lines \<and> s = (join B (meet m n))" 
    by (metis 0 1 assms(1,2,3,5) collin distinct_length_2_or_more join_properties1 meet_properties2 unique_meet)

  obtain t where t_fact: "t \<in> Lines \<and> t = (join (meet r m) (meet s l))" using r_fact s_fact 0 
    by (smt (z3) 1 assms(1,3,5) collin distinct_length_2_or_more join_properties1 local.join_def meet_properties2
        unique_meet)

  obtain D where d_fact: "D \<in> Points \<and> D = meet t h" 
    by (smt (z3) 0 1 assms(1,2,3,5) collin distinct_length_2_or_more join_properties1 projective_plane.meet_properties2
        projective_plane.unique_meet projective_plane_axioms r_fact s_fact t_fact)

  (*have 1: "h \<noteq> r" 
    by (metis "0" "1" assms(1,2,3,5) collin distinct_length_2_or_more join_properties1 meet_properties2 r_fact
        unique_meet)*)

  (* I think we need to build a quadrangle to show the next two statements *)
  have 1: "distinct[A, B, C, D]" 
  proof (rule ccontr)
    assume ch: "\<not>distinct[A, B, C, D]"
    show False
    proof -
      consider
        (AD) "A = D" 
        |(BD) "B = D"
        |(CD) "C = D" using assms ch by auto
      then show ?thesis
      proof (cases)
        case AD
        then show ?thesis
          by (smt (verit) 0 1 assms(2,3,5) collin d_fact distinct_length_2_or_more join_properties1 meet_properties2
              projective_plane.unique_meet projective_plane_axioms r_fact s_fact t_fact)
      next
        case BD (* sledgehammer can do this case on its own but provided no proof *)
        then show ?thesis sorry
      next
        case CD
        obtain X Y Z W (* IDEA: XYZW is a qudrangle, whose diagonal points are ABC (under the assumption CD, which violates P7*)
          where quad: "X \<in> Points \<and> Y \<in> Points \<and> Z \<in> Points \<and> W \<in> Points \<and>
                       X = meet s n \<and> Y = meet r t \<and> Z = meet t l \<and> W = meet l n" 
          by (metis (no_types) 0 1 CD assms(1,2,5) collin d_fact distinct_length_2_or_more meet_properties2
              projective_plane.join_properties1 projective_plane_axioms r_fact s_fact t_fact unique_meet)
        then show ?thesis sorry
      qed
    qed
  qed
  show ?thesis sorry
qed

text\<open>\jackson \oliver\<close>
theorem (in projective_plane) p4_6_uniqueness:
  fixes A B C D E ::"'p"
  fixes l :: "'l"
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points \<and> E \<in> Points"
  assumes "l\<in>Lines"
  assumes "incid A l" and "incid B l" and "incid C l"
  assumes "desarguesian Points Lines incid"
  (* Assume P7 *)
  assumes "harmonic_quadruple A B C D"
  assumes "harmonic_quadruple A B C E"
  shows "D=E"
  sorry 


text\<open>Definition: fourth harmonic point of A,B,C is the D satisfying 4.6.\<close>

text\<open>\oliver \jackson\<close>
text\<open>Proposition 4.7. AB,CD are four harmonic points. Assuming P5, then CD,AB are four harmonic
points.\<close>
theorem (in projective_plane) p4_7a:
  fixes A B C D ::"'p"
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points"
  assumes "desarguesian Points Lines incid"
  (* Assume P7 *)
  assumes "harmonic_quadruple A B C D"
  shows "harmonic_quadruple C D A B"
  
proof -
   obtain l X Y Z W where harmon: "l \<in> Lines \<and> incid A l \<and> incid B l \<and> incid C l \<and> incid D l \<and>
    X \<in> Points \<and> Y \<in> Points \<and> Z \<in> Points \<and> W \<in> Points \<and>
    cquadrangle X Y Z W \<and>
    A = meet (join X Y) (join Z W) \<and> B = meet (join X Z) (join Y W) \<and>
    incid C (join X W) \<and> incid D (join Y Z) \<and> (distinct[A,B,C,D])" using assms harmonic_quadruple_def by auto
   obtain R where fact: "R \<in> Points \<and> R = meet (join X W) (join Y Z)" using harmon 
     by (metis cquadrangle_joins_distinct distinct_length_2_or_more join_properties1 meet_properties2
       quadrangle_points_distinct)

   have distinct: "distinct[X, Y, Z, W, A, B, R, C, D]" 
     using assms fact harmon harmonic_and_quadrangle_all_points_distinct[of X Y Z W R A B C D] by auto
   have 0: "(join X D) \<noteq> (join C Z)" 
   proof (rule ccontr)
     assume ch: "\<not>(join X D) \<noteq> (join C Z)"
     show False
     proof -
       have 0: "(join X D) = (join C Z)" using ch by auto
       have 1: "incid X (join C Z)" using 0
        by (metis assms(1) cquadrangle_def[of X Y Z W] harmon incid_join_collinear join_properties1)
      have 2: "pcollinear X C Z" using 1 harmon assms incid_join_collinear[of X C Z] pcollinear_def by auto
      have 3: "pcollinear X C W" using assms harmon 
        by (metis (no_types, lifting) incid_join_collinear pcollinear_def)

      have 4: "pcollinear X W Z" 
        using assms(1) distinct distinct_length_2_or_more harmon 2 3 collinear_helper[of X C W Z]
        by metis

      show ?thesis using 4 cquadrangle_def[of X Y Z W] harmon pcollinear_def by auto
    qed
   qed

  obtain U where u: " U \<in> Points \<and> U = meet (join X D) (join C Z)" 
     using assms harmon harmonic_and_quadrangle_all_points_distinct 0 
   by (metis distinct distinct_length_2_or_more join_properties1 meet_properties2)
  obtain T where t: "T \<in> Points \<and> T = meet (join X W) (join Y Z)" 
    using assms harmonic_and_quadrangle_all_points_distinct fact by auto

  have distinctu: "distinct[X, Y, Z, W, C, U]" 
  proof (rule ccontr)
    assume ch: "\<not>distinct[X, Y, Z, W, C, U]"
    show False
    proof -
      have 0: "distinct[X, Y, Z, W, C]" using distinct by auto
      have 1: "U = X \<or> U = Y \<or> U = Z \<or> U = W \<or> U = C" using ch 0 by force
      have 2: "pcollinear C W X" by (metis (no_types) assms(1) harmon incid_join_collinear pcollinear_def)
      have 3: "incid U (join C Z)" using u assms harmon
        by (smt (verit) distinct distinct_length_2_or_more projective_plane.join_properties1 projective_plane.join_properties2
            projective_plane.meet_properties2 projective_plane_axioms)
      have 4: "pcollinear U C Z" using assms u pcollinear_def 0 3 harmon incid_join_collinear by auto
      have 5: "incid U (join D X)" using u assms harmon
        by (smt (verit) distinct distinct_length_2_or_more projective_plane.join_properties1 projective_plane.join_properties2
            projective_plane.meet_properties2 projective_plane_axioms)
      have 6: "pcollinear U D X" using assms u pcollinear_def 0 5 harmon incid_join_collinear by auto
          
      consider 
        (UX) "U = X"
        | (UY) "U = Y"
        | (UZ) "U = Z"
        | (UW) "U = W"
        | (UC) "U = C" using 1 by auto

      then show ?thesis
      proof (cases)
        case UX
        have 7: "pcollinear X C W" using assms 2 pcollinear_def by auto
        have 8: "pcollinear X C Z" using 4 UX pcollinear_def harmon by auto
        have 9: "pcollinear X W Z" using assms harmon 7 8 collinear_helper[of X C W Z] 0 by auto

        then show ?thesis using 7 cquadrangle_def harmon quadrangle_order by blast
      next
        case UY
        have 7: "pcollinear Y D X" using assms 2 6 pcollinear_def UY by auto
        have 8: "pcollinear Y D Z" using assms pcollinear_def 
          by (smt (verit, ccfv_threshold) harmon join_properties1)
        have 9: "pcollinear Y X Z" using assms harmon 7 8 collinear_helper[of Y D X Z] distinct by auto

         then show ?thesis using 9 cquadrangle_def harmon quadrangle_order by blast
      next
        case UZ
        have 7: "pcollinear Z D Y" using assms pcollinear_def harmon incid_join_collinear by metis 
        have 8: "pcollinear Z D X" using assms 2 6 pcollinear_def UZ by auto 
        have 9: "pcollinear Z Y X" using assms harmon 7 8 collinear_helper[of Z D Y X] distinct by auto

        then show ?thesis using 9 cquadrangle_def harmon quadrangle_order by blast
      next
        case UW
        have 7: "pcollinear W C X" using 2 pcollinear_def by auto
        have 8: "pcollinear W C Z" using assms pcollinear_def UW 4 by blast
        have 9: "pcollinear W X Z" using distinct harmon assms 7 8 collinear_helper[of W C X Z] by auto

        then show ?thesis using 9 cquadrangle_def harmon quadrangle_order by blast
      next
        case UC
        then show ?thesis
          by (smt (z3) assms(1) distinct distinct_length_2_or_more harmon projective_plane.join_properties1
              projective_plane.meet_properties2 projective_plane.unique_meet projective_plane_axioms u)
      qed
    qed
  qed

  have distinctt: "distinct[X, Y, Z, W, C, T]" using distinct fact t by auto

  have tnequ: "T \<noteq> U" using t u
    by (smt assms(1) distinctu distinct_length_2_or_more harmon join_properties2 join_properties1
        meet_properties2 projective_plane_axioms)

  have distinct2: "distinct[X, Y, Z, W, C, U, T]" using distinctu distinctt tnequ by auto
 
  have ncXTU: "\<not>pcollinear X T U" 
  proof (rule ccontr)
    assume ch: "\<not>\<not>pcollinear X T U"
    show False
    proof -
      have 0: "pcollinear X T U" using ch by auto
      have 1: "incid T (join X W)" 
        using cquadrangle_joins_distinct harmon meet_implies_incid quadrangle_points_distinct t
        by metis
      have 2: "incid X (join X W)" using distinct distinct_length_2_or_more harmon join_properties1
        by metis
      have 3: "pcollinear X T C" using 1 2 
        by (metis assms(1) distinct distinct_length_2_or_more harmon join_properties1 pcollinear_def t)
        
      have 4: "pcollinear X U C" using 0 3 distinct
        by (smt (verit) distinct_length_2_or_more fact pcollinear_def t unique_meet)

      have 5: "pcollinear U Z C" 
        by (smt (verit, del_insts) assms(1) distinct distinct_length_2_or_more harmon join_properties1
            meet_properties2 pcollinear_def u unique_meet)

      have 6: "pcollinear C U X \<and> pcollinear C U Z" using 4 5 pcollinear_def by auto
      have 7: "pcollinear C X Z" using assms(1) harmon u 6 collinear_helper[of C U X Z] distinctu by auto

      have 8: "pcollinear C X W" using assms(1) harmon incid_join_collinear by auto

      have 9: "pcollinear X C Z \<and> pcollinear X C W" using 7 8 pcollinear_def by auto
      have 10: "pcollinear X Z W" using assms harmon 9 distinctu collinear_helper[of X C Z W] by force

      show ?thesis using 10 cquadrangle_def harmon by auto
    qed
  qed

  have ncXUZ: "\<not>pcollinear X U Z" 
  proof (rule ccontr)
    assume ch: "\<not>\<not>pcollinear X U Z"
    show False
    proof -
      have 0: "pcollinear X U Z" using ch by auto
      have 1: "pcollinear U Z C"
        by (smt (verit, del_insts) assms(1) distinct distinct_length_2_or_more harmon join_properties1
            meet_properties2 pcollinear_def u unique_meet)
      have 2: "pcollinear C X W" using assms(1) harmon incid_join_collinear by auto
      have 3: "pcollinear Z U X \<and> pcollinear Z U C" using 0 1 pcollinear_def by auto


      have 4: "pcollinear Z X C" using assms(1) 2 3 harmon u distinctu collinear_helper[of Z U X C] by auto

      have 5: "pcollinear X C W \<and> pcollinear X C Z" using 2 4 pcollinear_def by auto
      have 6: "pcollinear X W Z" using assms harmon 5 collinear_helper[of X C W Z] distinctu by auto 

      show ?thesis using 6 harmon cquadrangle_def quadrangle_order by blast
    qed
  qed

  have ncTUZ: "\<not>pcollinear T U Z" 
  proof (rule ccontr)
    assume ch: "\<not>\<not>pcollinear T U Z"
    show False
    proof -
      have 0: "pcollinear T U Z" using ch by auto
      have 1: "pcollinear T X W" 
        using cquadrangle_joins_distinct harmon incid_join_collinear meet_implies_incid quadrangle_points_distinct t
        by metis
      have 2: "pcollinear T W X" using 1 pcollinear_def by auto
      have 3: "pcollinear C X W" using assms(1) harmon incid_join_collinear by auto
      have 4: "pcollinear X W T \<and> pcollinear X W C" using 1 3 pcollinear_def by auto
      have 5: "pcollinear X T C" using assms harmon 4 collinear_helper[of X W T C] t distinct2 by auto

      have 6: "incid U (join C Z)" using assms harmon u  distinct 
      by (smt (z3) distinct_length_2_or_more join_properties1 meet_properties2
          projective_plane_axioms unique_meet)

      have 7: "pcollinear U C Z" using 6 u assms harmon incid_join_collinear by auto
      have 8: "pcollinear Z U C \<and> pcollinear Z U T" using 0 7 pcollinear_def by auto
      have 9: "pcollinear Z T C" using 8 collinear_helper[of Z U C T] pcollinear_def u t distinct2 by auto
      have 10: "pcollinear T C Z \<and> pcollinear T C X" using 9 5 pcollinear_def by auto

      have 11: "pcollinear T Z X" 
        using 10 assms harmon collinear_helper[of T C Z X] distinct2 distinct_length_2_or_more t by metis
      have 12: "pcollinear T Y Z" using t
        by (metis cquadrangle_joins_distinct harmon incid_join_collinear meet_implies_incid quadrangle_points_distinct)

      have 13: "pcollinear Z T X \<and> pcollinear Z T Y" using 11 12 pcollinear_def by auto
      have 14: "pcollinear Z X Y" 
        using 13 collinear_helper[of Z T X Y] distinct_length_2_or_more distinctt harmon t by force


      show ?thesis using 14 harmon cquadrangle_def quadrangle_order by blast
    qed
  qed

  have ncXTZ: "\<not>pcollinear X T Z"
  proof (rule ccontr)
    assume ch: "\<not>\<not>pcollinear X T Z"
    show False
    proof -
      have 0: "pcollinear X T Z" using ch by auto
      have 2: "distinct[T, X, W, Y]" using distinct2 by auto
      have 3: "incid T (join Y Z)" 
        using 2 harmon distinct2 t meet_implies_incid[of X Y Z W T] cquadrangle_joins_distinct by auto
      have 4: "pcollinear Y T Z" using 3 harmon join_properties1 pcollinear_def t by auto

      have 5: "pcollinear Z T X \<and> pcollinear Z T Y" using 0 4 pcollinear_def by auto
      have 6: "pcollinear Z X Y" using 5 collinear_helper[of Z T X Y] t distinct2 harmon by force

      show ?thesis using 6 harmon cquadrangle_def quadrangle_order[of X Y Z W] by blast
    qed
  qed
 
  have 0: "cquadrangle X T U Z" unfolding cquadrangle_def
    using u t assms harmon ncXTU ncXUZ ncTUZ ncXTZ by auto

  (* Build the dual_desarguesian plane points *)
  obtain a where a_fact: "a \<in> Lines \<and> a = join X U" using harmon 
    by (metis incid_join_collinear join_properties1 ncXTZ ncXUZ t tnequ u)
  obtain a' where ap_fact: "a' \<in> Lines \<and> a' = join Y T" using harmon t
    by (metis distinct_length_2_or_more distinctt join_properties1)
  obtain b where b_fact: "b \<in> Lines \<and> b = join X Z" using harmon 
    by (metis distinct_length_2_or_more distinctt join_properties1)
  obtain b' where bp_fact: "b' \<in> Lines \<and> b' = join Y W" using harmon 
    by (metis distinct_length_2_or_more distinctt join_properties1)
  obtain c where c_fact: "c \<in> Lines \<and> c = join U Z" using harmon 
    by (metis b_fact join_properties1 ncXUZ pcollinear_def u)
  obtain c' where cp_fact: "c' \<in> Lines \<and> c' = join T W" using harmon t
    by (metis distinct_length_2_or_more distinctt join_properties1)
   (* line l = m in desarg thm *)

  (* n = not, dc = dual collinear, m = line l, ap = a' *)
  have distinct3: "distinct[a, a', b, b', c, c', (join X Y)]" 
  proof (rule ccontr)
    assume ch: "\<not>distinct[a, a', b, b', c, c', (join  X Y)]"
    show False
    proof -
      (* IDEA: Split into the 21 cases and use apply to solve many cases at once (see section 4.1.thy) *)
      show ?thesis sorry
  qed
qed

  have dcmaap_helper: "incid D l \<and> incid D a \<and> incid D a'"
    by (smt (z3) a_fact ap_fact assms(1) distinct2 distinct_length_2_or_more harmon projective_plane.join_properties1
        projective_plane.meet_properties2 projective_plane.unique_meet projective_plane_axioms t u)
  have dcmaap: "projective_plane_data.pcollinear Lines Points (mdualize (\<lhd>)) l a a'" 
    unfolding projective_plane_data.pcollinear_def 
    using a_fact ap_fact assms(1) dcmaap_helper harmon by auto
  have dcmbbp: "projective_plane_data.pcollinear Lines Points (mdualize (\<lhd>)) l b b'" 
    by (metis b_fact bp_fact dual_join_is_meet dual_plane_is_projective harmon mdualize.elims(3)
        projective_plane.incid_join_collinear projective_plane_axioms)
  have dcmccp_helper1: "incid C l" using harmon by blast
  have dcmccp_helper2: "incid C c'" 
    by (smt (z3) cp_fact cquadrangle_def distinct distinct_length_2_or_more harmon incid_join_collinear meet_implies_incid
        projective_plane.join_properties1 projective_plane.join_properties2 projective_plane_axioms t)
  have dcmccp_helper3: "pcollinear U C Z" 
    using distinct2 u harmon assms(1) meet_implies_incid[of X C Z D U] incid_join_collinear[of U C Z]
    by (smt (verit, del_insts) cquadrangle_def cquadrangle_joins_distinct incid_join_collinear
        projective_plane.join_properties1 projective_plane.meet_properties2 projective_plane.unique_meet
        projective_plane_axioms quadrangle_order)
  have dcmccp_helper4: "incid C c" using dcmccp_helper3
    by (smt (verit) assms(1) c_fact cquadrangle_joins_distinct harmon incid_join_collinear meet_implies_incid ncTUZ
        pcollinear_def projective_plane.join_properties2 projective_plane_axioms quadrangle_points_distinct t)
  have dcmccp: "projective_plane_data.pcollinear Lines Points (mdualize (\<lhd>)) l c c'" 
    using dcmccp_helper1 dcmccp_helper2 dcmccp_helper4
    using assms(1) c_fact cp_fact harmon projective_plane_data.pcollinear_def by fastforce
  have ndcabc: "\<not>projective_plane_data.pcollinear Lines Points (mdualize (\<lhd>)) a b c"
  proof (rule ccontr)
    assume ch: "\<not>\<not>projective_plane_data.pcollinear Lines Points (mdualize (\<lhd>)) a b c"
    show False
    proof -
      have 0: "projective_plane_data.pcollinear Lines Points (mdualize (\<lhd>)) a b c" using ch by auto
      obtain P
        where p_fact: "P \<in> Points \<and> (mdualize incid) a P  \<and> (mdualize incid) b P  \<and> (mdualize incid) c P" 
        using 0 by (meson a_fact b_fact c_fact projective_plane_data.pcollinear_def)
      have p_fact2: "P \<in> Points \<and> incid P a \<and> incid P b \<and> incid P c" using p_fact by auto
      show ?thesis 
        using p_fact2 a_fact b_fact c_fact distinct3 distinct_length_2_or_more harmon join_properties1 p1 u
        by metis
    qed
  qed
  have ndcapbpcp: "\<not>projective_plane_data.pcollinear Lines Points (mdualize (\<lhd>)) a' b' c'" 
  proof (rule ccontr)
    assume ch: "\<not>\<not>projective_plane_data.pcollinear Lines Points (mdualize (\<lhd>)) a' b' c'"
    show False
    proof -
      have 0: "projective_plane_data.pcollinear Lines Points (mdualize (\<lhd>)) a' b' c'" using ch by auto
      obtain P
        where p_fact: "P \<in> Points \<and> (mdualize incid) a' P  \<and> (mdualize incid) b' P  \<and> (mdualize incid) c' P" 
        using 0 by (meson ap_fact bp_fact cp_fact projective_plane_data.pcollinear_def)
      have p_fact2: "P \<in> Points \<and> incid P a' \<and> incid P b' \<and> incid P c'" using p_fact by auto
      show ?thesis using p_fact2 ap_fact bp_fact cp_fact distinct3 distinct_length_2_or_more harmon join_properties1 p1 t
        by metis
    qed
  qed




  (* e = equals, m = meet, ap = a prime*)
  (* I may have setup the following stuff wrong (l is not the dual meet of X, Y? *)
  (* Also, one of these facts uses distinct3, so we should ensure that distinct3 is true before moving forward *)
  (* I think some smt proofs that were excluded dont use distinct3 here and reduce runtime *)
  have lemabapbp_helper1: "X = (projective_plane_data.join Lines Points (mdualize (\<lhd>)) a b)" 
    using a_fact b_fact harmon
    by (metis dual_plane_is_projective fact join_properties1 mdualize.elims(3) ncXUZ pcollinear_def
        projective_plane.join_properties2 projective_plane_axioms u)
  have lemabapbp_helper2: "Y = (projective_plane_data.join Lines Points (mdualize (\<lhd>)) a' b')" 
    using ap_fact bp_fact harmon
    by (metis distinct3 distinct_length_2_or_more distinctt dual_plane_is_projective join_properties1 mdualize.elims(3)
        projective_plane.join_properties2 projective_plane_axioms t)
  have XYemabapbp: "(join X Y) = (projective_plane_data.meet Lines Points (mdualize (\<lhd>))
         (projective_plane_data.join Lines Points (mdualize (\<lhd>)) a b)
         (projective_plane_data.join Lines Points (mdualize (\<lhd>)) a' b'))" 
    using dual_meet_is_join lemabapbp_helper1 lemabapbp_helper2 projective_plane_axioms by fastforce
  have UTemacapcp_helper1: "U = (projective_plane_data.join Lines Points (mdualize (\<lhd>)) a c)" 
    using a_fact c_fact u 
    by (metis assms(1) cquadrangle_def dcmaap_helper dcmccp_helper4 distinct2 distinct_length_2_or_more dual_join_is_meet
      harmon incid_join_collinear join_properties1 join_properties2 projective_plane_axioms)
  have UTemacapcp_helper2: "T = (projective_plane_data.join Lines Points (mdualize (\<lhd>)) a' c')"
    using ap_fact cp_fact t
    by (metis distinct2 distinct3 distinct_length_2_or_more dual_meet_is_join dual_plane_is_projective harmon
        projective_plane.join_properties2 projective_plane.meet_properties2 projective_plane_axioms)
  have UTemacapcp: "(join U T) = (projective_plane_data.meet Lines Points (mdualize (\<lhd>))
         (projective_plane_data.join Lines Points (mdualize (\<lhd>)) a c)
         (projective_plane_data.join Lines Points (mdualize (\<lhd>)) a' c'))" 
    using UTemacapcp_helper1 UTemacapcp_helper2 dual_meet_is_join projective_plane_axioms by fastforce
  have ZWembcbpcp_helper1: "Z = (projective_plane_data.join Lines Points (mdualize (\<lhd>)) b c)"
    using b_fact c_fact harmon (* For simplicty we may say Z = meet b c first, then the dual statement *)
    by (smt (verit) UTemacapcp_helper1 a_fact dual_join_is_meet ncXUZ projective_plane.join_properties1
        meet_properties2 unique_meet projective_plane_axioms projective_plane_data.pcollinear_def u)
  have ZWembcbpcp_helper2: "W = meet b' c'"
    using bp_fact cp_fact harmon 
    by (metis (full_types) distinct2 distinct3 distinct_length_2_or_more join_properties1 meet_properties2 p1 t)
  have ZWembcbpcp_helper3: "W = (projective_plane_data.join Lines Points (mdualize (\<lhd>)) b' c')"
    using  ZWembcbpcp_helper2 dual_join_is_meet projective_plane_axioms by metis
  have ZWembcbpcp: "(join Z W) = (projective_plane_data.meet Lines Points (mdualize (\<lhd>))
         (projective_plane_data.join Lines Points (mdualize (\<lhd>)) b c)
         (projective_plane_data.join Lines Points (mdualize (\<lhd>)) b' c'))" 
    using ZWembcbpcp_helper1 ZWembcbpcp_helper3 dual_meet_is_join projective_plane_axioms by fastforce
  

  have "desarguesian Lines Points (mdualize (\<lhd>))" using P5 dual_plane_is_desarguesian[of Points Lines incid "mdualize incid"]
    using assms(2) by auto
  then have 1: "projective_plane_data.pcollinear Lines Points (mdualize incid) (join X Y) (join U T) (join Z W)" 
    using a_fact ap_fact b_fact bp_fact c_fact cp_fact distinct3 dcmaap dcmbbp dcmccp ndcabc ndcapbpcp
      XYemabapbp UTemacapcp ZWembcbpcp
    unfolding desarguesian_def[of Lines Points "mdualize incid"] sorry 

  obtain P where p_fact: "P \<in> Points \<and> (mdualize incid) (join X Y) P \<and> (mdualize incid) (join U T) P \<and> (mdualize incid) (join Z W) P"
    unfolding projective_plane_data.pcollinear_def 
    using 1 
    by (smt (verit, ccfv_threshold) distinct2 distinct_length_2_or_more harmon join_properties1 ncTUZ
        projective_plane_data.pcollinear_def)

  have p_fact2: "P \<in> Points \<and> incid P (join X Y) \<and> incid P (join U T) \<and> incid P (join Z W)" using p_fact by auto
  have 3: "incid A (join X Y) \<and> incid A (join Z W)" 
    by (metis assms(1) cquadrangle_joins_distinct harmon meet_implies_incid quadrangle_order
        quadrangle_points_distinct)
  have 4: "(join X Y) \<noteq> (join Z W)" using cquadrangle_joins_distinct harmon quadrangle_order by presburger
  have 5: "P = A" using 3 4
    by (metis assms(1) distinct distinct_length_2_or_more harmon join_properties1 p_fact2 unique_meet)
  have 6: "incid A (join U T)" using p_fact 5 by auto
  have 7: "incid B (join X Z)" 
    by (metis b_fact bp_fact distinct3 distinct_length_2_or_more harmon meet_properties2)
  have 8: "C = meet (join X T) (join U Z)" 
    by (smt (z3) assms(1) distinct distinct_length_2_or_more harmon projective_plane.join_properties1
        projective_plane.meet_properties2 projective_plane.unique_meet projective_plane_axioms t u)
  have 9: "D = meet (join T Z) (join X U)"
    by (smt (z3) assms(1) distinct distinct_length_2_or_more harmon meet_properties2 projective_plane.join_properties1
        projective_plane.unique_meet projective_plane_axioms t u)
 (* Idea: Break up harmon and harmonic_def of A B C D and show the individual statements rather than using the entirety of harmon *)
  show ?thesis using assms harmon 0 6 7 8 9 t u unfolding harmonic_quadruple_def sorry
  (*show ?thesis using 0 P5 thm dual_plane_is_desarguesian [of Points Lines incid "mdualize incid"] sorry*)
qed

 (* have meetA: "incid A (join U T)" using u t 0 by auto
  have 1: "pcollinear C D A B" using assms harmon by auto
  show ?thesis using 1 0 P5 by auto
  *)
   


text\<open>\oliver \jackson\<close>
text\<open>Proposition 4.7B. Inverse direction of p4_7\<close>

theorem (in projective_plane) p4_7b:
  fixes A B C D::"'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  (* Assume P5 *)
  (* Assume P7 *)
  assumes "desarguesian Points Lines incid"
  shows "harmonic_quadruple A B C D\<longleftrightarrow>harmonic_quadruple C D A B"
proof -
  show ?thesis using p4_7a assms by blast
qed
text\<open>\done\<close>

text\<open>\oliver \jackson\<close>
text\<open>Proposition 4.7C. The really big implication after Proposition 4.7. Hopefully will be useful for harmonic stuff\<close>
theorem (in projective_plane) p4_7c:
  fixes A B C D::"'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  (* Assume P5 *)
  (* Assume P7 *)
  assumes "desarguesian Points Lines incid"
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

