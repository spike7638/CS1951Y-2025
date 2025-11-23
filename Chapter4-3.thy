theory "Chapter4-3"
  imports Complex_Main  "Chapter4-2" "Chapter1-1"

begin
text\<open> start at  "Harmonic points", stop just before "Perspectivies and Projectivities"\<close>

text\<open>an ordered quadruple of distinct points A,B,C,D on a line is a harmonic quadruple if there is
is a complete quadrangle X,Y,Z,W such that A and B are diagonal points of the complete quadrangle. 
This is denoted H(AB,CD) if A,B,C,D form a harmonic quadruple\<close>

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
    incid C (join X W) \<and> incid D (join Y Z)) \<and> distinct[A,B,C,D]
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


text\<open>\Jackson\Oliver\<close>
lemma (in projective_plane) four_points_noncollinear_triples:
  fixes A :: "'p"
  assumes "A \<in> Points"
  shows "\<exists> Q R S. Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points \<and>
         A \<noteq> Q \<and> A \<noteq> R \<and> Q \<noteq> R \<and> S \<noteq> A \<and> S \<noteq> Q \<and> S \<noteq> R \<and> 
         \<not> (pcollinear A Q R) \<and> \<not> (pcollinear A Q S) \<and> \<not> (pcollinear Q R S) \<and> \<not> (pcollinear A R S)"
proof -
  obtain Q R  
      where three_pts: " Q \<in> Points \<and> R \<in> Points \<and> A \<noteq> Q \<and> A \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear A Q R)" 
    using p3 assms join_properties2 pcollinear_def by (smt (verit)) 

  obtain D 
    where d_fact: "D \<in> Points \<and> incid D (join R Q) \<and> D \<noteq> R \<and> D \<noteq> Q"
      using p4[of "(join R Q)" _] join_def[of R Q]
      by (metis (no_types, lifting) distinct_length_2_or_more join_properties1 mem_Collect_eq three_pts)

  obtain S where s_fact: "S \<in> Points \<and> incid S (join A D) \<and> S \<noteq> A \<and> S \<noteq> D \<and> S \<noteq> Q \<and> S \<noteq> R"
    using p4[of "(join A D)" _] join_def[of A D] d_fact 
    by (smt (verit) assms distinct_length_2_or_more incid_join_collinear join_properties1 join_properties2 mem_Collect_eq
        three_pts)

  have 0: "\<not>(pcollinear A Q S)" using three_pts d_fact s_fact
    by (smt (verit) assms join_properties2 p1 pcollinear_def)

  have 1: "\<not>(pcollinear Q R S)" using three_pts d_fact s_fact
    by (smt (verit) assms join_properties1 pcollinear_def unique_meet)

  have 2: "\<not>(pcollinear A R S)" using three_pts d_fact s_fact
    by (smt (verit) assms incid_join_collinear join_properties2 pcollinear_def)

  show ?thesis using three_pts s_fact 0 1 2 by auto
qed
text\<open>\done\<close>

text\<open>\Jackson\Oliver\<close>
lemma (in projective_plane) point_on_three_lines:
  fixes A :: "'p"
  assumes "A \<in> Points"
  shows "\<exists>l m n. l \<in> Lines \<and> m \<in> Lines \<and> n \<in> Lines \<and> incid A l \<and> incid A m \<and> incid A n
        \<and> l \<noteq> m \<and> l \<noteq> n \<and> m \<noteq> n"
proof -
  obtain Q R S
    where four_pts:  "Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points \<and>
         A \<noteq> Q \<and> A \<noteq> R \<and> Q \<noteq> R \<and> S \<noteq> A \<and> S \<noteq> Q \<and> S \<noteq> R \<and> 
         \<not> (pcollinear A Q R) \<and> \<not> (pcollinear A Q S) \<and> \<not> (pcollinear Q R S) \<and> \<not> (pcollinear A R S)"
    using assms four_points_noncollinear_triples by presburger


  obtain l m n 
    where lines: "l \<in> Lines \<and> m \<in> Lines \<and> n \<in> Lines \<and> l = (join A Q) \<and> m = (join A R) \<and> n = (join A S)"
    using assms four_pts join_def join_properties1 by auto

  show ?thesis using lines assms four_pts join_properties1 pcollinear_def by metis
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
lemma (in projective_plane_7) diagonal_points_noncollinear:
  fixes A B C D Q
  fixes X Y Z W
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

    have 2: "\<not>pcollinear Q B A" using assms p7[of X Y Z W] by (smt (verit, ccfv_threshold) meet_def meet_properties2 unique_meet)
    show ?thesis using 0 1 2 assms p7[of X Y Z W] pcollinear_def by auto
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
theorem (in projective_plane_7) p4_5:
  fixes A B C D
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

definition (in projective_plane_7) harmonic_conjugate where
"harmonic_conjugate A B C l m n = (if (distinct[A,B,C] \<and> pcollinear A B C \<and> 
l \<noteq> join A B \<and> incid A l \<and>  incid A m \<and> m \<noteq> join A B  \<and> m \<noteq> l \<and> n \<noteq> join A B \<and> incid C n \<and>
A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> l \<in> Lines \<and> m \<in> Lines \<and> n \<in> Lines
) then meet (join A B) (join (meet (join B (meet l n)) m) (meet (join B (meet m n)) l)) else undefined)"

text\<open>\oliver \jackson\<close>
lemma (in projective_plane_7) conjugate_is_harmonic:
  fixes A B C l m n D
    (* harmonic_conjugate assumptions *)
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> l \<in> Lines \<and> m \<in> Lines \<and> n \<in> Lines"
  assumes "distinct[A,B,C]"
  assumes "pcollinear A B C"
  assumes "l \<noteq> join A B \<and> incid A l \<and> incid A m \<and> m \<noteq> join A B \<and> m \<noteq> l \<and> n \<noteq> join A B \<and> incid C n"
  assumes "harmonic_conjugate A B C l m n = D"
  shows "harmonic_quadruple A B C D"
proof -
  obtain h where collin: "h \<in> Lines \<and> (incid A h)  \<and> (incid B h)  \<and> (incid C h)" 
    using assms pcollinear_def harmonic_conjugate_def by auto

  have harmonic_line: "h = (join A B)" using assms(1,2) collin join_properties2 by auto
  have mn_fact: "l \<noteq> h \<and> m \<noteq> h \<and> n \<noteq> h \<and> m \<noteq> n" using assms(1,2,4) collin unique_meet harmonic_line by force

  obtain r where r_fact: "r \<in> Lines \<and> r = (join B (meet l n))" 
  by (metis assms(1,2,4) collin distinct_length_2_or_more join_properties1 join_properties2 meet_properties2)

  obtain s where s_fact: "s \<in> Lines \<and> s = (join B (meet m n))"
    by (metis assms(1,2,4) collin distinct_length_2_or_more join_properties1 meet_properties2 unique_meet)
  
  obtain t where t_fact: "t \<in> Lines \<and> t = (join (meet r m) (meet s l))" using r_fact s_fact
    by (smt (z3) assms(1,2,4) collin distinct_length_2_or_more join_properties1 meet_properties2 r_fact s_fact
        unique_meet)

  have a0: "D = meet (join A B) (join (meet (join B (meet l n)) m) (meet (join B (meet m n)) l))" 
    using assms unfolding harmonic_conjugate_def by auto

  have d_fact: "D = meet t h" 
    using a0 assms t_fact collin harmonic_line r_fact s_fact meet_properties2 unique_meet by metis

  have d_fact2: "(incid D h)" using d_fact meet_implies_incid 
    by (smt (z3) assms(1,2,4) collin distinct_length_2_or_more join_properties1 meet_def meet_properties2
        r_fact s s_fact t_fact)

  have 0: "h \<in> Lines \<and> (incid A h) \<and> (incid B h) \<and> (incid C h) \<and> (incid D h)" using collin d_fact d_fact2 by auto


  have 1: "distinct[l, h, m, n, s, r, t]" 
  proof (rule ccontr)
    assume ch: "\<not>distinct[l, h, m, n, s, r, t]"
    show False
    proof -
      have 0: "l = n \<or> l = s \<or> l = r \<or> l = t \<or>
               h = n \<or> h = s \<or> h = r \<or> h = t \<or>
               m = n \<or> m = s \<or> m = r \<or> m = t \<or>
               n = s \<or> n = r \<or> n = t \<or> 
               s = r \<or> s = t \<or> 
               r = t" using ch mn_fact assms(4) by auto
      consider 
         (ln) "l = n" | (ls) "l = s" | (lr) "l = r" | (lt) "l = t" | (hn) "h = n"
       | (hs) "h = s" | (hr) "h = r" | (ht) "h = t" | (mn) "m = n" | (ms) "m = s"
       | (mr) "m = r" | (mt) "m = t" | (ns) "n = s" | (nr) "n = r" | (nt) "n = t"
       | (sr) "s = r" | (st) "s = t" | (rt) "r = t"
        using 0 by blast
      then show ?thesis
        apply (cases)
        using assms(1,3,5) collin mn_fact unique_meet apply auto[1]
        using assms(2,4) apply auto[1]
        apply (metis assms(1,4) join_properties1 join_properties2 meet_properties2 mn_fact s_fact)
        apply (metis assms(1,2,4) collin distinct_length_2_or_more join_properties1 meet_properties2 r_fact
            unique_meet)
        apply (smt (verit) assms(1,2,4) collin distinct_length_2_or_more join_properties1
            join_properties2 meet_properties2 projective_plane_axioms r_fact
            s_fact t_fact)
        using mn_fact apply blast
        apply (metis assms(1,2,4) collin distinct_length_2_or_more join_properties1
            meet_properties2 s_fact unique_meet)
        apply (metis assms(1,2,4) collin distinct_length_2_or_more join_properties1 meet_properties2
            r_fact unique_meet)
        apply (smt (z3) assms(1,2,4) collin distinct_length_2_or_more join_properties1 join_properties2
            meet_properties2 r_fact s_fact t_fact)
        using mn_fact apply auto
        apply (metis assms(1,2,4) distinct_length_2_or_more join_properties1 join_properties2 meet_properties2
            s_fact)
        apply (metis assms(1,2,4) collin distinct_length_2_or_more join_properties1 meet_properties2 r_fact
            unique_meet)
        apply (smt (z3) assms(1,2,4) collin distinct_length_2_or_more join_properties1 join_properties2
            meet_properties2 r_fact s_fact t_fact)
        apply (metis assms(1,2,4) collin distinct_length_2_or_more join_properties1 meet_properties2 s_fact
            unique_meet)
        apply (metis assms(1,2,4) collin distinct_length_2_or_more join_properties1 meet_properties2 r_fact
            unique_meet)
        apply (smt (verit, best) assms(1,2,4) collin distinct_length_2_or_more join_properties1 meet_properties2
            r_fact s_fact t_fact unique_meet)
        apply (smt (verit, best) assms(1,2,4) collin distinct_length_2_or_more join_properties1 meet_properties2
            r_fact s_fact unique_meet)
        apply (smt (z3) assms(1,2,4) collin distinct_length_2_or_more join_properties1 join_properties2
            meet_properties2 r_fact s_fact t_fact)
        by (smt (z3) assms(1,2,4) collin distinct_length_2_or_more join_properties1 meet_properties2 r_fact
            s_fact t_fact unique_meet)
    qed
  qed

  
  obtain X where x_fact: "X \<in> Points \<and> X = meet m s" using 1 mn_fact meet_properties2 s_fact assms by force
  obtain Y where y_fact: "Y \<in> Points \<and> Y = meet m r" using 1 mn_fact meet_properties2 r_fact assms by force
  obtain Z where z_fact: "Z \<in> Points \<and> Z = meet l s" using 1 mn_fact meet_properties2 s_fact assms by force
  obtain W where w_fact: "W \<in> Points \<and> W = meet l r" using 1 mn_fact meet_properties2 r_fact assms by force

  have cquad_helper1: "\<not>pcollinear X Y Z" using x_fact y_fact z_fact mn_fact  s_fact r_fact 1 
    by (smt (verit) assms(1) distinct_length_2_or_more join_properties1 join_properties2 meet_properties2
        pcollinear_def)
  have cquad_helper2: "\<not>pcollinear X W Y" using x_fact y_fact w_fact mn_fact s_fact r_fact 1 
    by (smt (verit, ccfv_threshold) assms(1) cquad_helper1 distinct_length_2_or_more join_properties2 meet_properties2
        pcollinear_def t_fact z_fact)
  have cquad_helper3: "\<not>pcollinear X Z W" using x_fact z_fact w_fact mn_fact s_fact r_fact 1 
    by (smt (verit, ccfv_threshold) assms(1) distinct_length_2_or_more join_properties1 meet_properties2 pcollinear_def
        join_properties2 projective_plane_axioms)
  have cquad_helper4: "\<not>pcollinear Y Z W" using y_fact z_fact w_fact mn_fact s_fact r_fact 1 
    by (smt (verit, del_insts) assms(1) distinct_length_2_or_more join_properties1 join_properties2 meet_properties2
        pcollinear_def)

  (* May be able to reformulate statement "2" as a contradiction, where the 4 helpers are cases and use apply to solve all at once *)
  have 2: "cquadrangle X Y Z W" 
    using x_fact y_fact z_fact w_fact cquad_helper1 cquad_helper2 cquad_helper3 cquad_helper4 pcollinear_def
    unfolding cquadrangle_def by metis
  have three_helper1: "incid A (join X Y)"
    by (metis 1 assms(1,4) cquad_helper1 distinct_length_2_or_more join_properties2 meet_properties2 pcollinear_degeneracy
        r_fact s_fact x_fact y_fact z_fact)
  have three_helper2: "incid A (join Z W)"
    by (metis 1 assms(1,4) cquad_helper3 distinct_length_2_or_more join_properties2  meet_properties2 pcollinear_degeneracy
        r_fact s_fact w_fact x_fact z_fact)
  have 3: "A = meet (join X Y) (join Z W)" using three_helper1 three_helper2 
    by (smt assms(1) cquad_helper1 cquad_helper3 incid_join_collinear join_properties1 meet_properties2
        pcollinear_degeneracy projective_plane.unique_meet projective_plane_axioms w_fact x_fact y_fact z_fact)
  have 4: "B = meet (join X Z) (join Y W)"
    by (smt (z3) 1 assms(1, 4) distinct_length_2_or_more join_properties2 mn_fact join_properties1
        meet_properties2 projective_plane_axioms r_fact s_fact w_fact x_fact y_fact z_fact)
  have 5: "incid C (join X W)" 
    by (smt (verit) 3 4 assms(1, 4) collin cquad_helper1 cquad_helper3 join_properties2 mn_fact meet_properties2  p1
        pcollinear_degeneracy r_fact s s_fact t_fact w_fact x_fact y_fact z_fact)
  have 6: "incid D (join Y Z)"
    by (smt 0 d_fact meet_def meet_properties2 t_fact unique_meet y_fact z_fact)
   


  have 7: "distinct[A, B, C, D]" 
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
            by (smt (verit) 6 assms(1) cquad_helper1 cquad_helper4 join_properties1 pcollinear_degeneracy
                incid_join_collinear three_helper1 three_helper2 unique_meet w_fact x_fact y_fact z_fact)
        next
          case BD 
          then show ?thesis
            by (smt (z3) 2 4 6 incid_join_collinear join_properties1 meet_properties2 p1 projective_plane.cquadrangle_def
                cquadrangle_joins_distinct projective_plane_axioms quadrangle_order)
        next
          case CD
            (* IDEA: XYZW is a qudrangle, whose diagonal points are ABC (under the assumption CD, which violates P7*)
          have use_P7: "\<not> pcollinear  (meet (join Y Z) (join X W))
                       (meet (join X Z) (join Y W))
                       (meet (join X Y) (join Z W))" using p7 x_fact y_fact z_fact w_fact 2 by auto
          have d_fact2: "D = meet (join Y Z) (join X W)" 
            using d_fact x_fact y_fact z_fact w_fact 
            by (metis 2 5 6 CD assms(1) cquadrangle_def join_properties1 meet_properties2
                pcollinear_degeneracy cquadrangle_joins_distinct unique_meet)
      

          have 8: "\<not> pcollinear A B D" using use_P7 d_fact2 3 4 pcollinear_def by auto

          then show ?thesis using CD assms by auto
        qed
      qed
    qed

  show ?thesis 
    using assms 0 1 2 3 4 5 6 7 d_fact x_fact y_fact z_fact w_fact distinct_length_2_or_more meet_properties2 t_fact
    unfolding harmonic_quadruple_def
    by metis
qed

text\<open>\oliver \jackson\<close>
theorem (in projective_plane_7) harmonic_is_conjugate:
  fixes A B C D
  assumes "A \<in> Points" and "B \<in> Points" and "C \<in> Points" and "D \<in> Points"
  assumes "harmonic_quadruple A B C D"
  shows "\<exists> l m n. D = harmonic_conjugate A B C l m n"
proof -
  obtain h X Y Z W where harmon: "h \<in> Lines \<and> incid A h \<and> incid B h \<and> incid C h \<and> incid D h \<and>
    X \<in> Points \<and> Y \<in> Points \<and> Z \<in> Points \<and> W \<in> Points \<and>
    cquadrangle X Y Z W \<and>
    A = meet (join X Y) (join Z W) \<and> B = meet (join X Z) (join Y W) \<and>
    incid C (join X W) \<and> incid D (join Y Z) \<and> (distinct[A,B,C,D])" using assms harmonic_quadruple_def by auto
  obtain l m n where lines: "l \<in> Lines \<and> m \<in> Lines \<and> n \<in> Lines \<and> l = join A X \<and> m = join A Z \<and> n = join C X" 
    using assms by (smt (z3) cquadrangle_def distinct_length_2_or_more harmon join_properties1
        incid_join_collinear meet_properties2 unique_meet
        projective_plane_axioms)
  obtain R where r: "R \<in> Points \<and> R = meet (join X W) (join Y Z)" using quadrangle_points_distinct[of X Y Z W] assms harmon using cquadrangle_joins_distinct mjj_point by auto
  have distinctness: "distinct[X, Y, Z, W, A, B, R, C, D]" using harmon harmonic_and_quadrangle_all_points_distinct[of X Y Z W R A B C D] r assms by auto
  have incid: "incid A l \<and> incid A m \<and> incid C n" 
    using harmon lines assms join_properties1 distinct_length_2_or_more distinctness by auto

  have 0: "m \<noteq> l" 
    by (smt (verit) assms(1) cquadrangle_def harmon lines p1 cquadrangle_joins_distinct
        incid_join_collinear join_properties2 meet_implies_incid  quadrangle_order quadrangle_points_distinct)
  have 1: "m \<noteq> join A B"
    by (smt (z3) cquadrangle_def harmon join_properties1 lines cquadrangle_joins_distinct
        incid_join_collinear meet_properties2 quadrangle_order unique_meet)
  have 2: "n \<noteq> join A B"
    by (smt (z3) assms(1,2,3) distinct_length_2_or_more distinctness harmon lines meet_implies_incid p1
        join_properties1 quadrangle_points_distinct projective_plane_axioms quadrangle_order)
  have 3: "l \<noteq> join A B"
    by (smt (verit, del_insts) assms(1,2) distinct_length_2_or_more distinctness harmon join_properties2 lines
        join_properties1 meet_implies_incid)

  have conjugate_prelims: "l \<noteq> join A B \<and> incid A l \<and> incid A m \<and> m \<noteq> join A B  \<and> m \<noteq> l \<and> n \<noteq> join A B \<and> incid C n" 
    using harmon lines assms incid 0 1 2 3 by auto

  have d_fact_helper1: "W = meet m n" 
    by (smt (z3) assms(3) conjugate_prelims harmon lines join_def cquadrangle_joins_distinct unique_meet
        join_properties1 meet_implies_incid meet_properties2 quadrangle_order quadrangle_points_distinct projective_plane_axioms)
  have d_fact_helper_2: "Y = (meet (join B (meet m n)) l)" using d_fact_helper1 
    by (smt (verit, ccfv_threshold) distinct_length_2_or_more distinctness harmon lines join_properties1
        meet_properties2 projective_plane_axioms unique_meet)
  have d_fact_helper_3: "Z = (meet (join B (meet l n)) m)" 
    by (smt (verit, del_insts) assms(3) distinct_length_2_or_more distinctness harmon lines join_properties1
        meet_properties2 projective_plane_axioms unique_meet)

  have d_fact: "D = meet (join A B) (join (meet (join B (meet l n)) m) (meet (join B (meet m n)) l))" 
    using d_fact_helper_2 d_fact_helper_3 
    by (smt (verit, ccfv_threshold) assms(1,2,4) conjugate_prelims distinct_length_2_or_more harmon join_properties2 lines
        projective_plane.join_properties1 projective_plane.meet_properties2 projective_plane_axioms)

  show ?thesis using conjugate_prelims d_fact unfolding harmonic_conjugate_def 
    by (metis assms(1,2,3) distinct_length_2_or_more harmon lines pcollinear_def)
qed
text\<open>\done\<close>

text\<open>\oliver \jackson\<close>
lemma (in projective_plane_7) conjugate_swap_ml:
  fixes A B C l m n D
  shows "(harmonic_conjugate A B C l m n) = (harmonic_conjugate A B C m l n)"
  using join_properties1 join_properties2 join_def 
  unfolding harmonic_conjugate_def
  by (smt (verit))
text\<open>\done\<close>

text\<open>\oliver \jackson\<close>
lemma (in projective_plane_5_7) conjugate_change_l:
  fixes A B C l l' m n D
    (* harmonic_conjugate assumptions *)
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> l \<in> Lines \<and> l' \<in> Lines \<and> m \<in> Lines \<and> n \<in> Lines"
  assumes "distinct[A,B,C]"
  assumes "pcollinear A B C"
  assumes "l \<noteq> join A B \<and> incid A l \<and> l' \<noteq> join A B \<and> incid A l' 
           \<and> incid A m \<and> m \<noteq> join A B \<and> m \<noteq> l \<and> m \<noteq> l' \<and> n \<noteq> join A B \<and> incid C n"
  shows "harmonic_conjugate A B C l m n = harmonic_conjugate A B C l' m n"
  sorry

text\<open>\oliver \jackson\<close>
lemma (in projective_plane_5_7) conjugate_change_m:
  fixes A B C l m m' n D
    (* harmonic_conjugate assumptions *)
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> l \<in> Lines \<and> m \<in> Lines \<and> m' \<in> Lines \<and> n \<in> Lines"
  assumes "distinct[A,B,C]"
  assumes "pcollinear A B C"
  assumes "l \<noteq> join A B \<and> incid A l \<and> 
           incid A m \<and> m \<noteq> join A B \<and> incid A m' \<and> m' \<noteq> join A B \<and> m \<noteq> l \<and> m' \<noteq> l \<and> n \<noteq> join A B \<and> incid C n"
  shows "harmonic_conjugate A B C l m n = harmonic_conjugate A B C l m' n"
  using assms(1,2,3,4) conjugate_change_l conjugate_swap_ml by metis
text\<open>\done\<close>

text\<open>\oliver \jackson\<close>
lemma (in projective_plane_5_7) conjugate_change_n:
  fixes A B C l m n n' D
    (* harmonic_conjugate assumptions *)
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> l \<in> Lines \<and> m \<in> Lines \<and> n \<in> Lines \<and> n' \<in> Lines"
  assumes "distinct[A,B,C]"
  assumes "pcollinear A B C"
  assumes "l \<noteq> join A B \<and> incid A l \<and> 
           incid A m \<and> m \<noteq> join A B \<and> m \<noteq> l \<and> n \<noteq> join A B \<and> incid C n \<and> n' \<noteq> join A B \<and> incid C n'"
  shows "harmonic_conjugate A B C l m n = harmonic_conjugate A B C l m n'"
  sorry


text\<open>\oliver \jackson\<close>
theorem (in projective_plane_7) p4_6_existence:
  fixes A B C
  assumes "A \<in> Points" and "B \<in> Points" and "C \<in> Points"
  assumes "pcollinear A B C"
  assumes "distinct [A,B,C]"
  (* Assume P7 *)
  (* Showing distinctness of the obtained lines may simplify the smt / metis proofs *)
  shows "\<exists>D. D \<in> Points \<and> harmonic_quadruple A B C D"
proof -
  obtain h where collin: "h \<in> Lines \<and> (incid A h)  \<and> (incid B h)  \<and> (incid C h)" using assms pcollinear_def by auto

  obtain l m where 
    lm_fact: "l \<in> Lines \<and> m \<in> Lines \<and> (incid A l) \<and> (incid A m) \<and> l \<noteq> m \<and> l \<noteq> h \<and> h \<noteq> m " 
    using assms(1) collin point_on_three_lines[of A] by auto

  obtain n where n_fact: "n \<in> Lines \<and> (incid C n) \<and> n \<noteq> h" using assms(3) collin point_on_three_lines[of C] by auto

  have 0: "h = (join A B)" using assms(1,2,5) collin join_properties2 by auto

  obtain D where d_fact: "D = harmonic_conjugate A B C l m n" by auto

  (* Conjugate prelims *)
  have 1: "l \<noteq> join A B \<and> incid A l \<and> incid A m \<and> m \<noteq> join A B \<and> m \<noteq> l \<and> n \<noteq> join A B \<and> incid C n" 
    using 0 lm_fact n_fact by auto

  have 2: "harmonic_quadruple A B C D" 
    using 1 assms(1,2,3,4,5) conjugate_is_harmonic d_fact lm_fact n_fact by auto

  have 3: "D \<in> Points" using d_fact unfolding harmonic_conjugate_def
  by (smt (z3) assms(1,2,3,4,5) collin distinct_length_2_or_more join_properties1 lm_fact meet_properties2 n_fact
      unique_meet)

  show ?thesis using 2 3 by auto
qed
text\<open>\done\<close>



text\<open>\jackson \oliver\<close>
theorem (in projective_plane_5_7) p4_6_uniqueness:
  fixes A B C D D' l m n
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points \<and> D' \<in> Points"
  assumes "harmonic_quadruple A B C D" (*harmonic_quadruple A B C D" *)
  assumes "harmonic_quadruple A B C D'"
  shows "D = D'"
proof -
  obtain l m n where d_fact: "D = harmonic_conjugate A B C l m n" using assms harmonic_is_conjugate[of A B C D] by auto
  obtain l' m' n' where dp_fact: "D' = harmonic_conjugate A B C l' m' n'" using assms harmonic_is_conjugate[of A B C D'] by auto

  have a0: "D = harmonic_conjugate A B C l m n" using d_fact by auto

  then show ?thesis sorry
qed

text\<open>Definition: fourth harmonic point of A,B,C is the D satisfying 4.6.\<close>

text\<open>\oliver \jackson\<close>
text\<open>Proposition 4.7. AB,CD are four harmonic points. Assuming P5, then CD,AB are four harmonic
points.\<close>
theorem (in projective_plane_7) p4_7a:
  fixes A B C D
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points"
  assumes "desarguesian Points Lines incid"
  (* Assume P7 *)
  assumes "harmonic_quadruple A B C D"
  shows "harmonic_quadruple C D B A"
  
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
  have distinct3: "distinct[a, a', b, b', c, c', l]" 
  proof (rule ccontr)
    assume ch: "\<not>distinct[a, a', b, b', c, c', l]"
    show False
    proof -
      have temp: "a' \<noteq> b'" 
        by (smt (z3) ap_fact bp_fact cquadrangle_def distinct_length_2_or_more harmon incid_join_collinear meet_implies_incid p1
            projective_plane.join_properties2 projective_plane_axioms quadrangle_points_distinct t)
      have temp2: "b' \<noteq> c" 
        by (metis bp_fact c_fact cquadrangle_def distinct2 distinct_length_2_or_more harmon incid_join_collinear join_properties1
            quadrangle_order u)
      have temp3: "a' \<noteq> l"
        by (metis ap_fact assms(1,3) diagonal_points_noncollinear distinct_length_2_or_more distinctt harmon
            projective_plane.join_properties1 projective_plane_axioms t)
      have temp4: "b \<noteq> l" 
        by (smt (verit) assms(1) b_fact distinct distinct_length_2_or_more harmon join_properties1
            unique_meet projective_plane_axioms)
      have temp5: "b' \<noteq> l"
        by (smt (verit) assms(1) bp_fact distinct distinct_length_2_or_more harmon join_properties1
            projective_plane.unique_meet projective_plane_axioms)
      have 0:
        "a = a' \<or> a = b \<or> a = b' \<or> a = c \<or> a = c' \<or> a = l \<or>
         a' = b \<or> a' = b' \<or> a' = c \<or> a' = c' \<or> a' = l \<or>
         b = b' \<or> b = c \<or> b = c' \<or> b = l \<or>
         b' = c \<or> b' = c' \<or> b' = l \<or>
         c = c' \<or> c = l \<or> c' =l" using ch by auto
      (* IDEA: Split into the 21 cases and use apply to solve many cases at once (see section 4.1.thy) *)
     consider
      (aa') "a = a'" | (ab) "a = b" | (ab') "a = b'" | (ac) "a = c" | (ac') "a = c'" | (al) "a = l" |
      (a'b) "a' = b" | (a'b') "a' = b'" | (a'c) "a' = c" | (a'c') "a' = c'" | (a'l) "a' = l" |
      (bb') "b = b'" | (bc) "b = c" | (bc') "b = c'" | (bl) "b = l" |
      (b'c) "b' = c" | (b'c') "b' = c'" | (b'l) "b' = l" |
      (cc') "c = c'" | (cl) "c  =l" | (c'l) "c' = l"
       using 0 by auto
     then show False
       apply cases
       apply (metis (no_types, lifting) a_fact ap_fact distinct_length_2_or_more distinctt harmon join_properties1 ncXTU
           pcollinear_def t u) 
       apply (metis a_fact b_fact bp_fact fact cquadrangle_def harmon incid_join_collinear join_properties1 ncXUZ pcollinear_def u)
       apply (metis a_fact bp_fact cquadrangle_def harmon incid_join_collinear join_properties1 ncXTU t tnequ u)
       apply (metis a_fact c_fact distinct_length_2_or_more distinctt harmon incid_join_collinear join_properties1 ncXUZ
           u)
       apply (metis a_fact cp_fact distinct_length_2_or_more distinctt harmon incid_join_collinear join_properties1
        join_properties2 ncXTU t tnequ u)
       apply (smt (z3) a_fact assms(1) distinct distinct_length_2_or_more harmon projective_plane.join_properties1
           projective_plane.meet_properties2 projective_plane.unique_meet projective_plane_axioms u)
       apply (metis ap_fact b_fact cquadrangle_def distinct_length_2_or_more distinctt harmon incid_join_collinear
           join_properties1 quadrangle_order t)   
       using temp apply blast
       apply (smt (z3) ap_fact assms(1) c_fact distinct distinct_length_2_or_more harmon projective_plane.join_properties1
           projective_plane.meet_properties2 projective_plane.unique_meet projective_plane_axioms t u)
       apply (metis ap_fact bp_fact cp_fact distinct distinct_length_2_or_more harmon join_properties1 t temp
           unique_meet)
       
       using temp3 apply blast
       apply (simp add: b_fact bp_fact cquadrangle_joins_distinct harmon quadrangle_order)
       apply (metis b_fact c_fact distinct_length_2_or_more distinctt harmon incid_join_collinear join_properties1 ncXUZ
        u)
       apply (metis ap_fact b_fact bp_fact cp_fact cquadrangle_def harmon incid_join_collinear join_properties1 quadrangle_order
        t temp)
       using temp4 apply blast
       using temp2 apply blast
       apply (metis ap_fact bp_fact cp_fact distinct2 distinct_length_2_or_more harmon join_properties1 p1 t temp)
       using temp5 apply blast
       apply (metis ap_fact bp_fact c_fact cp_fact harmon incid_join_collinear join_properties1 ncTUZ t temp u)
       using c_fact distinct2 harmon incid_join_collinear join_properties1 ncXUZ u apply auto
       apply (smt (z3) assms(1) meet_implies_incid quadrangle_order quadrangle_points_distinct unique_meet) 
       by (metis assms(1,3) cp_fact diagonal_points_noncollinear t)
   qed
 qed

  have distinct3_alt: "distinct[l, a, b, c, a', b', c']" using distinct3 by auto


  have dcmaap_helper: "incid D l \<and> incid D a \<and> incid D a'"
    by (smt (z3) a_fact ap_fact assms(1) distinct2 distinct_length_2_or_more harmon projective_plane.join_properties1
        projective_plane.meet_properties2 projective_plane.unique_meet projective_plane_axioms t u)
  have dcmaap: "projective_plane_data.pcollinear Lines Points (mdualize incid) l a a'" 
    unfolding projective_plane_data.pcollinear_def 
    using a_fact ap_fact assms(1) dcmaap_helper harmon by auto
  have dcmbbp: "projective_plane_data.pcollinear Lines Points (mdualize incid) l b b'" 
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
  have dcmccp: "projective_plane_data.pcollinear Lines Points (mdualize incid) l c c'" 
    using dcmccp_helper1 dcmccp_helper2 dcmccp_helper4
    using assms(1) c_fact cp_fact harmon projective_plane_data.pcollinear_def by fastforce
  have ndcabc: "\<not>projective_plane_data.pcollinear Lines Points (mdualize incid) a b c"
  proof (rule ccontr)
    assume ch: "\<not>\<not>projective_plane_data.pcollinear Lines Points (mdualize incid) a b c"
    show False
    proof -
      have 0: "projective_plane_data.pcollinear Lines Points (mdualize incid) a b c" using ch by auto
      obtain P
        where p_fact: "P \<in> Points \<and> (mdualize incid) a P  \<and> (mdualize incid) b P  \<and> (mdualize incid) c P" 
        using 0 by (meson a_fact b_fact c_fact projective_plane_data.pcollinear_def)
      have p_fact2: "P \<in> Points \<and> incid P a \<and> incid P b \<and> incid P c" using p_fact by auto
      show ?thesis 
        using p_fact2 a_fact b_fact c_fact distinct3 distinct_length_2_or_more harmon join_properties1 p1 u
        by metis
    qed
  qed
  have ndcapbpcp: "\<not>projective_plane_data.pcollinear Lines Points (mdualize incid) a' b' c'" 
  proof (rule ccontr)
    assume ch: "\<not>\<not>projective_plane_data.pcollinear Lines Points (mdualize incid) a' b' c'"
    show False
    proof -
      have 0: "projective_plane_data.pcollinear Lines Points (mdualize incid) a' b' c'" using ch by auto
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
  have lemabapbp_helper1: "X = (projective_plane_data.join Lines Points (mdualize incid) a b)" 
    using a_fact b_fact harmon
    by (metis dual_plane_is_projective fact join_properties1 mdualize.elims(3) ncXUZ pcollinear_def
        projective_plane.join_properties2 projective_plane_axioms u)
  have lemabapbp_helper2: "Y = (projective_plane_data.join Lines Points (mdualize incid) a' b')" 
    using ap_fact bp_fact harmon
    by (metis distinct3 distinct_length_2_or_more distinctt dual_plane_is_projective join_properties1 mdualize.elims(3)
        projective_plane.join_properties2 projective_plane_axioms t)
  have XYemabapbp: "(join X Y) = (projective_plane_data.meet Lines Points (mdualize incid)
         (projective_plane_data.join Lines Points (mdualize incid) a b)
         (projective_plane_data.join Lines Points (mdualize incid) a' b'))" 
    using dual_meet_is_join lemabapbp_helper1 lemabapbp_helper2 projective_plane_axioms by fastforce
  have UTemacapcp_helper1: "U = (projective_plane_data.join Lines Points (mdualize incid) a c)" 
    using a_fact c_fact u 
    by (metis assms(1) cquadrangle_def dcmaap_helper dcmccp_helper4 distinct2 distinct_length_2_or_more dual_join_is_meet
      harmon incid_join_collinear join_properties1 join_properties2 projective_plane_axioms)
  have UTemacapcp_helper2: "T = (projective_plane_data.join Lines Points (mdualize incid) a' c')"
    using ap_fact cp_fact t
    by (metis distinct2 distinct3 distinct_length_2_or_more dual_meet_is_join dual_plane_is_projective harmon
        projective_plane.join_properties2 projective_plane.meet_properties2 projective_plane_axioms)
  have UTemacapcp: "(join U T) = (projective_plane_data.meet Lines Points (mdualize incid)
         (projective_plane_data.join Lines Points (mdualize incid) a c)
         (projective_plane_data.join Lines Points (mdualize incid) a' c'))" 
    using UTemacapcp_helper1 UTemacapcp_helper2 dual_meet_is_join projective_plane_axioms by fastforce
  have ZWembcbpcp_helper1: "Z = (projective_plane_data.join Lines Points (mdualize incid) b c)"
    using b_fact c_fact harmon (* For simplicty we may say Z = meet b c first, then the dual statement *)
    by (smt (verit) UTemacapcp_helper1 a_fact dual_join_is_meet ncXUZ projective_plane.join_properties1
        meet_properties2 unique_meet projective_plane_axioms projective_plane_data.pcollinear_def u)
  have ZWembcbpcp_helper2: "W = meet b' c'"
    using bp_fact cp_fact harmon 
    by (metis (full_types) distinct2 distinct3 distinct_length_2_or_more join_properties1 meet_properties2 p1 t)
  have ZWembcbpcp_helper3: "W = (projective_plane_data.join Lines Points (mdualize incid) b' c')"
    using  ZWembcbpcp_helper2 dual_join_is_meet projective_plane_axioms by metis
  have ZWembcbpcp: "(join Z W) = (projective_plane_data.meet Lines Points (mdualize incid)
         (projective_plane_data.join Lines Points (mdualize incid) b c)
         (projective_plane_data.join Lines Points (mdualize incid) b' c'))" 
    using ZWembcbpcp_helper1 ZWembcbpcp_helper3 dual_meet_is_join projective_plane_axioms by fastforce

  have deaap: "D = projective_plane_data.join Lines Points (mdualize incid) a a'"
    by (metis (no_types, opaque_lifting) a_fact ap_fact assms(1) dcmaap_helper distinct3 distinct_length_2_or_more
        dual_join_is_meet meet_properties2 p1 projective_plane_axioms)
  have bebbp: "B = projective_plane_data.join Lines Points (mdualize incid) b b'"
    by (metis b_fact bp_fact dual_join_is_meet harmon projective_plane_axioms)
  have ceccp: "C = projective_plane_data.join Lines Points (mdualize incid) c c'"
    by (metis assms(1) c_fact cp_fact dcmccp_helper2 dcmccp_helper4 distinct3 distinct_length_2_or_more
        dual_plane_is_projective mdualize.elims(3) projective_plane.join_properties2 projective_plane_axioms)

  (* last lemma needed for dual P5 (distinct dual joins of sides of the two triangles) *)
  have daapbbpccp: "distinct
         [projective_plane_data.join Lines Points (mdualize incid) a a',
          projective_plane_data.join Lines Points (mdualize incid) b b',
          projective_plane_data.join Lines Points (mdualize incid) c c']" 
    using deaap bebbp ceccp harmon by auto


  have helper1: "desarguesian Lines Points (mdualize incid)" using dual_plane_is_desarguesian[of Points Lines incid "mdualize incid"]
    using assms(2) by auto
  have helper2: "l \<in> Lines" using harmon by auto
  have helper3: "projective_plane Lines Points (mdualize incid)" using assms desarguesian_def helper1 by auto

  have helper4: " distinct [M, A, B, C, A', B', C'] \<and>
        M \<in> Lines \<and>
        A \<in> Lines \<and>
        B \<in> Lines \<and>
        C \<in> Lines \<and>
        A' \<in> Lines \<and>
        B' \<in> Lines \<and>
        C' \<in> Lines \<and>
        projective_plane_data.pcollinear Lines Points (mdualize incid) M A A' \<and>
        projective_plane_data.pcollinear Lines Points (mdualize incid) M B B' \<and>
        projective_plane_data.pcollinear Lines Points (mdualize incid) M C C' \<and>
        \<not> projective_plane_data.pcollinear Lines Points (mdualize incid) A B C \<and>
        \<not> projective_plane_data.pcollinear Lines Points (mdualize incid) A' B' C' \<and>
        distinct
         [projective_plane_data.join Lines Points (mdualize incid) A A',
          projective_plane_data.join Lines Points (mdualize incid) B B',
          projective_plane_data.join Lines Points (mdualize incid) C C'] \<longrightarrow>
        projective_plane_data.pcollinear Lines Points (mdualize incid)
         (projective_plane_data.meet Lines Points (mdualize incid)
           (projective_plane_data.join Lines Points (mdualize incid) A B)
           (projective_plane_data.join Lines Points (mdualize incid) A' B'))
         (projective_plane_data.meet Lines Points (mdualize incid)
           (projective_plane_data.join Lines Points (mdualize incid) A C)
           (projective_plane_data.join Lines Points (mdualize incid) A' C'))
         (projective_plane_data.meet Lines Points (mdualize incid)
           (projective_plane_data.join Lines Points (mdualize incid) B C)
           (projective_plane_data.join Lines Points (mdualize incid) B' C'))" for A B C A' B' C' M
    using  helper1 
    unfolding desarguesian_def[of Lines Points "mdualize incid"] by blast
  (*by (metis desarguesian_def helper1)*)
  have 1: "projective_plane_data.pcollinear Lines Points (mdualize incid) (join X Y) (join U T) (join Z W)"
    using  helper4[of l a b c "a'" "b'" "c'"] helper3 helper2 a_fact ap_fact b_fact bp_fact c_fact cp_fact distinct3_alt dcmaap dcmbbp dcmccp ndcabc ndcapbpcp
      XYemabapbp UTemacapcp ZWembcbpcp daapbbpccp
    unfolding desarguesian_def[of Lines Points "mdualize incid"] by auto
   

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
  have 9: "D = meet (join X U) (join T Z)"
    by (smt (z3) assms(1) distinct distinct_length_2_or_more harmon meet_properties2 projective_plane.join_properties1
        projective_plane.unique_meet projective_plane_axioms t u)
 (* Idea: Break up harmon and harmonic_def of A B C D and show the individual statements rather than using the entirety of harmon *)

    have prelim: "C \<in> Points \<and> D \<in> Points \<and> B \<in> Points \<and> A \<in> Points" using assms(1) by auto
    have a0: "(if C \<in> Points \<and> D \<in> Points \<and> B \<in> Points \<and> A \<in> Points
    then (\<exists>l X Y Z W.
             l \<in> Lines \<and>
             incid C l \<and>
             incid D l \<and>
             incid B l \<and>
             incid A l \<and>
             X \<in> Points \<and>
             Y \<in> Points \<and>
             Z \<in> Points \<and>
             W \<in> Points \<and>
             cquadrangle X Y Z W \<and> C = (X \<bar> Y) \<sqdot> (Z \<bar> W) \<and> D = (X \<bar> Z) \<sqdot> (Y \<bar> W) \<and> incid B (X \<bar> W) \<and> incid A (Y \<bar> Z)) \<and>
         distinct [C, D, B, A]
    else undefined) = 
  (if True
    then (\<exists>l X Y Z W.
             l \<in> Lines \<and>
             incid C l \<and>
             incid D l \<and>
             incid A l \<and>
             incid B l \<and>
             X \<in> Points \<and>
             Y \<in> Points \<and>
             Z \<in> Points \<and>
             W \<in> Points \<and>
             cquadrangle X Y Z W \<and> C = (X \<bar> Y) \<sqdot> (Z \<bar> W) \<and> D = (X \<bar> Z) \<sqdot> (Y \<bar> W) \<and> incid B (X \<bar> W) \<and> incid A (Y \<bar> Z)) \<and>
         distinct [C, D, B, A]
    else undefined)" using prelim by meson
    then have a1: "... = ((\<exists>l X Y Z W.
             l \<in> Lines \<and>
             incid C l \<and>
             incid D l \<and>
             incid A l \<and>
             incid B l \<and>
             X \<in> Points \<and>
             Y \<in> Points \<and>
             Z \<in> Points \<and>
             W \<in> Points \<and>
             cquadrangle X Y Z W \<and> C = (X \<bar> Y) \<sqdot> (Z \<bar> W) \<and> D = (X \<bar> Z) \<sqdot> (Y \<bar> W) \<and> incid B (X \<bar> W) \<and> incid A (Y \<bar> Z)) \<and>
         distinct [C, D, B, A])" by auto

    have reorder_distinct: "distinct [C, D, B, A]" using harmon by auto
    have a_lemma: " incid A (T \<bar> U)"  using 6 join_properties1 join_properties2 t u by metis
    have prelim_H: "((l \<in> Lines \<and>
             incid C l \<and>
             incid D l \<and>
             incid A l \<and>
             incid B l \<and>
             X \<in> Points \<and>
             T \<in> Points \<and>
             U \<in> Points \<and>
             Z \<in> Points \<and>
             cquadrangle X T U Z \<and> C = (X \<bar> T) \<sqdot> (U \<bar> Z) \<and> D = (X \<bar> U) \<sqdot> (T \<bar> Z) \<and> incid B (X \<bar> Z) \<and> incid A (T \<bar> U)) \<and>
         distinct [C, D, B, A])" using assms(1) harmon 0 6 7 8 9 t u reorder_distinct a_lemma by argo
    have H: "((\<exists>l X Y Z W.
             l \<in> Lines \<and>
             incid C l \<and>
             incid D l \<and>
             incid A l \<and>
             incid B l \<and>
             X \<in> Points \<and>
             Y \<in> Points \<and>
             Z \<in> Points \<and>
             W \<in> Points \<and>
             cquadrangle X Y Z W \<and> C = (X \<bar> Y) \<sqdot> (Z \<bar> W) \<and> D = (X \<bar> Z) \<sqdot> (Y \<bar> W) \<and> incid B (X \<bar> W) \<and> incid A (Y \<bar> Z)) \<and>
         distinct [C, D, B, A])" using prelim_H by blast
    (*by (smt (verit) assms(3) diagonal_points_noncollinear distinct_length_2_or_more harmon join_properties1 meet_properties2
        prelim quadrangle_order unique_meet)*)

    have final_statement: "(if C \<in> Points \<and> D \<in> Points \<and> B \<in> Points \<and> A \<in> Points
    then (\<exists>l X Y Z W.
             l \<in> Lines \<and>
             incid C l \<and>
             incid D l \<and>
             incid A l \<and>
             incid B l \<and>
             X \<in> Points \<and>
             Y \<in> Points \<and>
             Z \<in> Points \<and>
             W \<in> Points \<and>
             cquadrangle X Y Z W \<and> C = (X \<bar> Y) \<sqdot> (Z \<bar> W) \<and> D = (X \<bar> Z) \<sqdot> (Y \<bar> W) \<and> incid B (X \<bar> W) \<and> incid A (Y \<bar> Z)) \<and>
         distinct [C, D, B, A]
    else undefined)" using H a0 a1 by auto

    show ?thesis using final_statement unfolding harmonic_quadruple_def by metis
qed


text\<open>\oliver \jackson\<close>
text\<open>Proposition 4.7B. Inverse direction of p4_7\<close>

theorem (in projective_plane_7) p4_7b:
  fixes A B C D
  assumes "A \<in> Points" "B \<in> Points" "C \<in> Points" "D \<in> Points"
  (* Assume P5 *)
  (* Assume P7 *)
  assumes "desarguesian Points Lines incid"
  shows "harmonic_quadruple A B C D\<longleftrightarrow>harmonic_quadruple C D A B"
proof -
  show ?thesis using p4_7a assms harmonic_swap_second_pair by blast
qed
text\<open>\done\<close>

text\<open>\oliver \jackson\<close>
text\<open>Proposition 4.7C. The really big implication after Proposition 4.7. Hopefully will be useful for harmonic stuff\<close>
theorem (in projective_plane_7) p4_7c:
  fixes A B C D
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

