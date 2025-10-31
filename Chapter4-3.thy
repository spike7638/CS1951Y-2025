theory "Chapter4-3"
  imports Complex_Main  "Chapter4-2" "Chapter1-1"

begin
text\<open> start at  "Harmonic points", stop just before "Perspectivies and Projectivities"\<close>

text\<open>an ordered quadruple of distinct points A,B,C,D on a line is a harmonic quadruple if there is
is a complete quadrangle X,Y,Z,W such that A and B are diagonal points of the complete quadrangle. 
This is denoted H(AB,CD) if A,B,C,D form a harmonic quadruple\<close>

text\<open>\jackson \oliver\<close>
(* WE SHOULD COMMENT THIS OUT UPON PUSH  -- FIX WHEN LOCALE SITUATION IS RESOLVED *)
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
(* WE SHOULD COMMENT THIS OUT UPON PUSH  -- FIX WHEN LOCALE SITUATION IS RESOLVED *)
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
(* WE SHOULD COMMENT THIS OUT UPON PUSH  -- FIX WHEN LOCALE SITUATION IS RESOLVED *)
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
lemma (in projective_plane) quadrangle_meet_implies_incid:
  fixes X Y Z W Q::"'p"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points" "Q \<in> Points"
  assumes "cquadrangle X Y Z W"
  assumes "Q = meet (join X W) (join Y Z)"

  shows "incid Q (join X W) \<and> incid Q (join Y Z)"
proof -
  show ?thesis using assms meet_properties2[of "(join X W)" "(join Y Z)"] 
    by (metis cquadrangle_joins_distinct distinct_length_2_or_more join_properties1 meet_properties2
      quadrangle_points_distinct)
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
  sorry (* sledgehammer was able to prove this but for now it is omitted to try and simplify the proof *)
(*proof (rule ccontr)
  assume ch: "\<not>distinct[P, Q, R]"
  show False
  proof -
    have 0: "P = Q \<or> P = R \<or> Q = R" using ch by auto
    consider 
      (PQ) "P = Q"
      | (PR) "P = R"
      | (QR) "Q = R"
      using 0 by blast
    then show ?thesis
    proof (cases)
      case PQ
      have 0: "incid P (join X Y)" using assms quadrangle_meet_implies_incid[of X Z W Y P] quadrangle_order by metis
      have 1: "incid Q (join X Z)" 
        using assms quadrangle_meet_implies_incid[of X Y W Z Q] 0 quadrangle_order by metis

      have 2: "incid X (join X Y)" using assms 
          by (metis distinct_length_2_or_more join_properties1 quadrangle_points_distinct)
      have 3: "pcollinear P X Y" using 0 2 assms pcollinear_def 
          by (smt (verit, del_insts) cquadrangle_joins_distinct join_properties1)
      sorry
 *)

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


(*
lemma (in projective_plane) harmonic_and_quadrangle_all_points_distinct:
  fixes X Y Z W P Q R A B C D::"'p"
  assumes "X \<in> Points" "Y \<in> Points" "Z \<in> Points" "W \<in> Points" "P \<in> Points" "Q \<in> Points" "R \<in> Points"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  assumes "cquadrangle X Y Z W"
  assumes "P = meet (join X Y) (join Z W)"
  assumes "Q = meet (join X Z) (join Y W)"
  assumes "R = meet (join X W) (join Y Z)"
  assumes "harmonic_quadruple A B C D"
  assumes "A = meet (join X Y) (join Z W)" "B = meet (join X Z) (join Y W)" 
  assumes "incid C (join X W)"  "incid D (join Y Z)"
  shows "distinct[X, Y, Z, W, P, Q, R, C, D]"
  sorry
(*proof -
  have 0: "distinct[X, Y, Z, W, P, Q, R]" using assms quadrangle_all_points_distinct by metis
  have 1: "distinct[A, B, C, D]" using assms harmonic_quadruple_def by auto
  have 2: "distinct[X, Y, Z, W, P, Q, R, C]" using 0 assms harmonic_quadruple_def[of A B C D] by sledgehammer
*)
*)

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
  (* NEEDS P7  *)
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
  fixes l :: "'l"
  assumes "A \<in> Points" and "B \<in> Points" and "C \<in> Points"
  assumes "l\<in>Lines"
  assumes "incid A l" and "incid B l" and "incid C l"
  assumes "distinct [A,B,C]"
  (* Assume P7 *)
  shows "\<exists>D. D \<in> Points \<and> harmonic_quadruple A B C D"
  sorry


text\<open>\jackson \oliver\<close>
theorem (in projective_plane) p4_6_uniqueness:
  fixes A B C D E ::"'p"
  fixes l :: "'l"
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points \<and> E \<in> Points"
  assumes "l\<in>Lines"
  assumes "incid A l" and "incid B l" and "incid C l"
  (* Assume P5 *)
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
  (* Assume P5 *)
  (* Assume P7 *)
  assumes "harmonic_quadruple A B C D"
  shows "harmonic_quadruple C D A B"
  sorry 
text\<open>\done\<close>

text\<open>\oliver \jackson\<close>
text\<open>Proposition 4.7B. Inverse direction of p4_7\<close>
theorem (in projective_plane) p4_7b:
  fixes A B C D::"'p"
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  (* Assume P5 *)
  (* Assume P7 *)
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

