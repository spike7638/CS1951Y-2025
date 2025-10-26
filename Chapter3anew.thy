theory Chapter3anew
  imports Complex_Main "HOL-Algebra.Ring" "HOL-Algebra.QuotRing" Chapter3new 
begin
(* In this theory, we will prove that the the automorphisms of RP2 given by 
   matrices are in fact all the automorphisms of RP2. *)

(*Note: It appears that the first place where "ring_iso" is defined is in QuotRing. *)

(*To state (and prove) Theorem 3.9 and Lemma 3.10,
 we need to define a notion of collinearity in RP2. *)

definition RP2_collinear :: "v3 \<Rightarrow> v3 \<Rightarrow> v3 \<Rightarrow> bool" 
  where "RP2_collinear x y z \<longleftrightarrow> (\<exists>L . (is_line L) \<and> x \<in> L \<and> y \<in> L \<and> z \<in> L)"

definition set_not_RP2_collinear :: "(v3 set) \<Rightarrow> bool"
  where "set_not_RP2_collinear S \<longleftrightarrow> (\<forall>x\<in>S.\<forall>y\<in>(S - {x}) .\<forall>z\<in>(S - {x, y}). \<not>RP2_collinear x y z)"

definition set_non_zero :: "(v3 set) \<Rightarrow> bool"
  where "set_non_zero S \<longleftrightarrow> (\<forall> x \<in> S . x \<noteq> 0)"

definition mat_from_pts :: "v3 \<Rightarrow> v3 \<Rightarrow> v3 \<Rightarrow> m33"
  where "mat_from_pts x y z = vector[x, y, z]"

lemma mat_from_pts_rows:
  "(mat_from_pts x y z) $ 1 = x"
  "(mat_from_pts x y z) $ 2 = y"
  "(mat_from_pts x y z) $ 3 = z"
  unfolding mat_from_pts_def
  using vector_3[of x y z]
  by simp_all

lemma mat_from_pts_rows_v2:
  "row 1 (mat_from_pts x y z) = x"
  "row 2 (mat_from_pts x y z) = y"
  "row 3 (mat_from_pts x y z) = z"
  using mat_from_pts_rows row_def
  by (metis vec_nth_inverse)+

lemma mat_from_pts_dep_imp_det_0:
  fixes x y z :: v3
  assumes "vec.dependent {x, y, z}"
  shows "det (mat_from_pts x y z) = 0"
proof -
  have "{x, y, z} \<subseteq> rows (mat_from_pts x y z)"
    using rows_def[of "mat_from_pts x y z"] mat_from_pts_rows_v2[of x y z]
  by (metis (mono_tags, lifting) bot.extremum insert_subsetI iso_tuple_UNIV_I
      mem_Collect_eq)
  then show ?thesis using assms
    using det_dependent_rows vec.dependent_mono by auto
qed

lemma lin_comb_dep:
  fixes a b :: real
  fixes x y z :: v3
  assumes "a *s x + b *s y = z"
  assumes "x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z" 
  shows "vec.dependent {x, y, z}"
  using assms vec.independent_insert vec.span_add_eq2 vec.span_base vec.span_scale
  by (smt (verit) insert_commute insert_iff singletonD)

lemma lin_comb_det_0:
  fixes a b :: real
  fixes x y z :: v3
  assumes "a *s x + b *s y = z"
  assumes "x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z" 
  shows "det (mat_from_pts x y z) = 0"
  using assms mat_from_pts_dep_imp_det_0 lin_comb_dep by blast
  

lemma det_0_imp_collinear:
  fixes x y z :: v3
  shows "det (mat_from_pts x y z) = 0 \<longrightarrow> RP2_collinear x y z"
proof (rule impI)
  let ?A = "mat_from_pts x y z"
  assume det_0: "det ?A  = 0"
  obtain h :: v3 where a1: "h \<noteq> 0 \<and> ?A *v h = 0" 
   using det_0
   by (meson invertible_det_nz invertible_left_inverse matrix_left_invertible_ker)
  let ?a = "h$1" 
  let ?b = "h$2"
  let ?c = "h$3"
  have x_online: "?a * x$1 + ?b * x$2 + ?c * x$3 = 0"
    using a1
    unfolding mat_from_pts_def
    using explicit_inner_prod matrix_vector_mul_component
    by (metis inner_commute vector_3(1) zero_index)
  have y_online: "?a * y$1 + ?b * y$2 + ?c * y$3 = 0"
    using a1
    unfolding mat_from_pts_def
    using explicit_inner_prod matrix_vector_mul_component
    by (metis inner_commute vector_3(2) zero_index)
  have z_online: "?a * z$1 + ?b * z$2 + ?c * z$3 = 0"
   using a1
   unfolding mat_from_pts_def
   using explicit_inner_prod matrix_vector_mul_component
   by (metis inner_commute vector_3(3) zero_index)
  have nalz: "not_all_zero ?a ?b ?c" using a1
   by (metis exhaust_3 not_all_zero_def vect_zero_eqv2) 
  show "RP2_collinear x y z"
    unfolding RP2_collinear_def
    unfolding is_line_def
    using nalz x_online y_online z_online a1
    by blast
qed

lemma collinear_imp_det_0:
  fixes x y z :: v3
  shows "RP2_collinear x y z \<longrightarrow> det (mat_from_pts x y z) = 0"
proof (rule impI)
  let ?A = "mat_from_pts x y z"
  assume "RP2_collinear x y z"
  then obtain a b c :: real 
    where a1: "not_all_zero a b c \<and> a * x$1 + b * x$2 + c * x$3 = 0
                              \<and> a * y$1 + b * y$2 + c * y$3 = 0
                              \<and> a * z$1 + b * z$2 + c * z$3 = 0"
    unfolding RP2_collinear_def
    unfolding is_line_def
    by blast
  let ?h = "vector[a, b, c] :: (real, 3) vec"
  have h_non_zero: "?h \<noteq> 0" using not_all_zero_eqv[of a b c] a1 by auto
  have "(?A *v ?h) $ 1 = a * x$1 + b * x$2 + c * x$3"
    unfolding mat_from_pts_def
    by (simp add: explicit_inner_prod matrix_vector_mul_component)
  then have Ahr1: "(?A *v ?h) $ 1 = 0" using a1 by auto
  have "(?A *v ?h) $ 2 = a * y$1 + b * y$2 + c * y$3"
     unfolding mat_from_pts_def
     by (simp add: explicit_inner_prod matrix_vector_mul_component)
   then have Ahr2: "(?A *v ?h) $ 2 = 0" using a1 by auto
   have "(?A *v ?h) $ 3 = a * z$1 + b*z$2 + c*z$3"
     unfolding mat_from_pts_def
     by (simp add: explicit_inner_prod matrix_vector_mul_component)
   then have Ahr3: "(?A *v ?h) $ 3 = 0" using a1 by auto
  have Ah_zero: "?A *v ?h = (0 :: (real, 3) vec)" 
    using Ahr1 Ahr2 Ahr3
    by (metis exhaust_3 vect_zero_eqv2)
    (*This is not the nicest way to finish it but it'll do for now... *)
  show "det ?A  = 0"
    using Ah_zero h_non_zero inv_matrix_inj tom_def by auto
qed

lemma collinear_iff_det_0:
  fixes x y z :: v3
  shows "RP2_collinear x y z \<longleftrightarrow> det (mat_from_pts x y z) = 0"
proof
  show "RP2_collinear x y z \<Longrightarrow> det (mat_from_pts x y z) = 0"
    using collinear_imp_det_0[of x y z] by auto
  show "det (mat_from_pts x y z) = 0 \<Longrightarrow> RP2_collinear x y z"
    using det_0_imp_collinear[of x y z] by auto
qed 

lemma equal_points_collinear:
  fixes x y z :: v3
  assumes "x = y" 
  shows "RP2_collinear x y z"
proof -
  let ?A = "mat_from_pts x y z"
  have "?A$1 = ?A$2" using assms 
    unfolding mat_from_pts_def vector_3
    by simp
  then have "det (mat_from_pts x y z) = 0" by (simp add: det_3)
  then show ?thesis using collinear_iff_det_0 by auto
qed

lemma collinearity_preserved_under_scaling:
  fixes x y z :: v3
  fixes l u v :: real
  assumes coll: "RP2_collinear x y z"
  shows "RP2_collinear (l *s x) (u *s y) (v *s z)"
proof -
  obtain L :: "(real, 3) vec set"
    where h1: "is_line L \<and> x \<in> L \<and> y \<in> L \<and> z \<in> L"
    using coll
    unfolding RP2_collinear_def
    by auto
  then obtain a b c :: real where h2: "not_all_zero a b c \<and> L = {x . a*x$1 + b * x$2 + c * x$3 = 0}"
    using is_line_def[of L] by blast
  have "a * x$1 + b*x$2 + c*x$3 = 0" using h1 h2 by auto
  then have "l * (a * x$1 + b*x$2 + c*x$3) = 0" by auto
  then have "l*a*x$1 + l *b*x$2 + l * c*x$3 = 0" by (simp add: distrib_left)
  then have "a*l*x$1 + b*l*x$2 + c*l*x$3 = 0" by (simp add: mult.commute)
  then have "a*(l*s x)$1 + b*(l*s x)$2 + c*(l*s x)$3 = 0" by simp
  then have l1: "(l*s x) \<in> L" using h2 by auto
  have "a * y$1 + b*y$2 + c*y$3 = 0" using h1 h2 by auto
  then have "u * (a * y$1 + b*y$2 + c*y$3) = 0" by auto
  then have "u*a*y$1 + u *b*y$2 + u * c*y$3 = 0" by (simp add: distrib_left)
  then have "a*u*y$1 + b*u*y$2 + c*u*y$3 = 0" by (simp add: mult.commute)
  then have "a*(u*s y)$1 + b*(u*s y)$2 + c*(u*s y)$3 = 0" by simp
  then have l2: "(u*s y) \<in> L" using h2 by auto
  have "a * z$1 + b*z$2 + c*z$3 = 0" using h1 h2 by auto
  then have "v * (a * z$1 + b*z$2 + c*z$3) = 0" by auto
  then have "v *a*z$1 + v *b*z$2 + v *c*z$3 = 0" by (simp add: distrib_left)
  then have "a* v *z$1 + b* v *z$2 + c* v * z$3 = 0" by (simp add: mult.commute)
  then have "a*(v *s z)$1 + b*(v *s z)$2 + c*(v *s z)$3 = 0" by simp
  then have l3: "(v *s z) \<in> L" using h2 by auto
  show ?thesis
    unfolding RP2_collinear_def
    using h1 l1 l2 l3 by blast
qed

(* lemma not_collinear_set_collinear_iff: "set_not_RP2_collinear {x, y, z} \<longleftrightarrow> \<not> RP2_collinear x y z"
  unfolding set_not_RP2_collinear_def
  sorry *)
lemma p1p2p3q_not_collinear: "set_not_RP2_collinear {p1, p2, p3, q}"
  unfolding set_not_RP2_collinear_def
  (* This amounts to a TON of casework, because
     Isabelle doesn't realize that the order of the arguments
     to RP2_collinear doesn't matter 
     Perhaps proving the above lemma would helpful
   *)
  sorry

   

lemma p1p2p3q_not_zero: "set_non_zero {p1, p2, p3, q}"
proof -
  have "p1 \<noteq> 0 \<and> p2 \<noteq> 0 \<and> p3 \<noteq> 0 \<and> q \<noteq> 0" using p1_def p2_def p3_def q_def vect_zero_eqv by auto
  then show ?thesis using set_non_zero_def by auto
qed

lemma p1p2p3q_distinct: "p1 \<noteq> p2 \<and> p1 \<noteq> p3 \<and> p1 \<noteq> q \<and> p2 \<noteq> p3 \<and> p2 \<noteq> q \<and> p3 \<noteq> q" 
  using p1_def p2_def p3_def q_def vector_3(1) vector_3(3) zero_neq_one by metis

lemma det_non_zero_is_non_zero_after_non_zero_scaling_of_rows:
  fixes x y z :: v3
  fixes l u v :: real
  assumes non_zero: "l \<noteq> 0 \<and> u \<noteq> 0 \<and> v \<noteq> 0"
  assumes "det (mat_from_pts x y z) \<noteq>  0"
  shows "det (mat_from_pts (l *s x) (u *s y) (v *s z)) \<noteq> 0"
proof
  assume contr_1: "det (mat_from_pts (l *s x) (u *s y) (v *s z)) = 0"
  have h1: "RP2_collinear (l *s x) (u *s y) (v *s z)" using collinear_iff_det_0 contr_1 by auto
  then have "RP2_collinear x y z"
  proof - 
    have "RP2_collinear (1/l *s (l *s x)) (1/u *s (u *s y)) (1/v *s (v *s z))"
      using collinearity_preserved_under_scaling h1 by blast
    then show ?thesis by (simp add: non_zero)
  qed
  then have "det (mat_from_pts x y z) = 0" using collinear_iff_det_0 by auto
  then show "False" using assms(2) by auto
qed

lemma exists_auto_helper:
  fixes a' b' c' d' :: v3
  assumes non_zero: "set_non_zero {a', b', c', d'}"
  assumes not_collinear_img: "set_not_RP2_collinear {a', b', c', d'}"
  assumes distinct: "a' \<noteq> b' \<and> a' \<noteq> c' \<and> a' \<noteq> d' \<and> b' \<noteq> c' \<and> b' \<noteq> d' \<and> c' \<noteq> d'"
  (* By the lemma "equal_points_collinear," we can make the distinctness assumption. *)
  shows "\<exists> A :: m33 . \<exists> l u v :: real . l \<noteq> 0 \<and> u \<noteq> 0 \<and> v \<noteq>0 
    \<and>  det A \<noteq> 0 \<and> tom A p1 = l *s a' \<and> tom A p2 = u *s b' \<and> tom A p3 = v *s c' \<and> tom A q = d'"
  (* The addition of scalars l u v is equivalent to the statement of Hartshorne's lemma,
     by the definition of the quotient relation, and is clearly necessary 
     (count degrees of freedom). *)

proof -
  have h0a: "d' \<noteq> 0" using non_zero unfolding set_non_zero_def by blast
  have h0: "\<not> RP2_collinear a' b' c'"
      using not_collinear_img distinct
      unfolding set_not_RP2_collinear_def
      by blast
    then have h1: "det (mat_from_pts a' b' c') \<noteq> 0" using collinear_iff_det_0 by auto
    then have h1b: "det (transpose (mat_from_pts a' b' c')) \<noteq> 0" by auto
  then obtain h :: v3 where eq0: "(transpose (mat_from_pts a' b' c')) *v h = d'" 
    using h0a
    by (metis invertible_det_nz invertible_right_inverse matrix_vector_mul_assoc matrix_vector_mul_lid)
  let ?l = "h$1"
  let ?u = "h$2"
  let ?v = "h$3"
  have eq1: "?l *s a' + ?u *s b' + ?v *s c' = d'"
    using eq0
    unfolding mat_from_pts_def
    using vect_vect_by_vect_mult by auto
  let ?T = "transpose (mat_from_pts (?l *s a') (?u *s b') (?v *s c'))"
  have r1: "tom ?T p1 = ?l *s a'" using mat_mult_by_p1 mat_from_pts_def tom_def by fastforce
  have r2: "tom ?T p2 = ?u *s b'" using mat_mult_by_p2 mat_from_pts_def tom_def by fastforce
  have r3: "tom ?T p3 = ?v *s c'" using mat_mult_by_p3 mat_from_pts_def tom_def by fastforce
  have r4: "tom ?T q = d'" using lin_comb r1 r2 r3 eq1 
    by (metis (no_types, lifting) q_def tom_def vec.add vec.scale_one)
  have l_non_zero: "?l \<noteq> 0"
  proof
    assume l_zero: "?l = 0"
    have "?u *s b' + ?v *s c' = d'" using eq1 l_zero by simp
    then have contr1: "det (mat_from_pts b' c' d') = 0"
      using lin_comb_det_0 distinct by blast
  have "\<not> RP2_collinear b' c' d'" 
    using not_collinear_img distinct 
    unfolding set_not_RP2_collinear_def
    by blast
  then have contr2: "det (mat_from_pts b' c' d') \<noteq> 0"
    using collinear_iff_det_0[of b' c' d']
    by simp
  show "False" using contr1 contr2 by auto
  qed 
  have u_non_zero: "?u \<noteq> 0" 
  proof
    assume u_zero: "?u = 0"
    have "?l *s a' + ?v *s c' = d'" using eq1 u_zero by simp
    then have contr1: "det (mat_from_pts a' c' d') = 0"
     using lin_comb_det_0 distinct by blast
    have "\<not> RP2_collinear a' c' d'" 
      using not_collinear_img
      using distinct
      unfolding set_not_RP2_collinear_def
      by auto
    then have contr2: "det (mat_from_pts a' c' d') \<noteq> 0"
    using collinear_iff_det_0[of a' c' d'] by auto
  show "False" using contr1 contr2 by auto
  qed 
  have v_non_zero: "?v \<noteq> 0"
  proof
    assume v_zero: "?v = 0"
    have "?l *s a' + ?u *s b' = d'" using eq1 v_zero by simp
    then have contr1: "det (mat_from_pts a' b' d') = 0" 
      using lin_comb_det_0 distinct by blast
    have "\<not> RP2_collinear a' b' d'"
      using not_collinear_img
      using distinct
      unfolding set_not_RP2_collinear_def
      by auto
    then have contr2: "det (mat_from_pts a' b' d') \<noteq> 0"
      using collinear_iff_det_0[of a' b' d'] by auto
    show "False" using contr1 contr2 by auto
  qed 
  have "det (transpose (mat_from_pts a' b' c')) \<noteq> 0" using h1 by auto
  then have det_non_zero: "det ?T \<noteq> 0" 
    using det_non_zero_is_non_zero_after_non_zero_scaling_of_rows[of ?l ?u ?v a' b' c']
    using l_non_zero u_non_zero v_non_zero
    by auto
  show ?thesis using l_non_zero u_non_zero v_non_zero det_non_zero r1 r2 r3 r4
    by blast
qed

lemma unique_auto_helper:
 fixes a' b' c' d' :: v3
 fixes A B :: m33
 assumes non_zero: "set_non_zero {a', b', c', d'}"
 assumes not_collinear_img: "set_not_RP2_collinear {a', b', c', d'}"
 assumes distinct: "a' \<noteq> b' \<and> a' \<noteq> c' \<and> a' \<noteq> d' \<and> b' \<noteq> c' \<and> b' \<noteq> d' \<and> c' \<noteq> d'"
 assumes A_maps_to: "\<exists> l u v :: real . l \<noteq> 0 \<and> u \<noteq> 0 \<and> v \<noteq>0 
    \<and>  det A \<noteq> 0 \<and> tom A p1 = l *s a' \<and> tom A p2 = u *s b' \<and> tom A p3 = v *s c' \<and> tom A q = d'"
 assumes B_maps_to: "\<exists> l u v :: real . l \<noteq> 0 \<and> u \<noteq> 0 \<and> v \<noteq>0 
    \<and>  det B \<noteq> 0 \<and> tom B p1 = l *s a' \<and> tom B p2 = u *s b' \<and> tom B p3 = v *s c' \<and> tom B q = d'"
 shows "equiv_maps (tom A) (tom B)"
  unfolding equiv_maps_def
  unfolding well_defined_def
proof (safe)
  show "respects_scaling (tom A)"
    using matrices_respect_scaling by auto
  show "image_non_zero (tom A)"
    using A_maps_to inv_matrices_image_non_zero by auto
  show "respects_scaling (tom B)"
    using matrices_respect_scaling by auto
  show "image_non_zero (tom B)"
    using B_maps_to inv_matrices_image_non_zero by auto
  obtain l u v :: real where A_assms: "l \<noteq> 0 \<and> u \<noteq> 0 \<and> v \<noteq>0 
    \<and>  det A \<noteq> 0 \<and> tom A p1 = l *s a' \<and> tom A p2 = u *s b' \<and> tom A p3 = v *s c' \<and> tom A q = d'"
    using A_maps_to by auto
  obtain l' u' v' :: real where B_assms: "l' \<noteq> 0 \<and> u' \<noteq> 0 \<and> v' \<noteq>0 
    \<and>  det B \<noteq> 0 \<and> tom B p1 = l' *s a' \<and> tom B p2 = u' *s b' \<and> tom B p3 = v' *s c' \<and> tom B q = d'"
    using B_maps_to by auto
  have "tom A x = x$1 *s tom A p1 + x$2 *s tom A p2 + x$3 *s tom A p3"
    using matrix_mult_unfold[of A x] by auto
  have hc1: "tom A p1 = (l/l') *s tom B p1 \<and> l/l' \<noteq> 0" using A_assms B_assms by auto
  have hc2: "tom A p2 = (u/u') *s tom B p2 \<and> u/u' \<noteq> 0" using A_assms B_assms by auto
  have hc3: "tom A p3 = (v/v') *s tom B p3 \<and> v/v' \<noteq> 0" using A_assms B_assms by auto
  have hc4: "tom A q = tom B q \<and> (1 :: real) \<noteq> 0" using A_assms B_assms by auto
  have A_invertible: "det A \<noteq> 0" using A_assms by auto
  have B_invertible: "det B \<noteq> 0" using B_assms by auto 
  fix x
  show "\<exists>l. l \<noteq> 0 \<and> tom A x = l *s tom B x" 
    using equiv_on_basis_imp_equiv[of A B] hc1 hc2 hc3 hc4 A_invertible B_invertible
  by (metis vector_smult_lid)
qed

lemma tom_mult_is_matrix_mult:
  fixes A :: m33
  fixes B :: m33
  fixes x :: v3
  shows "tom (A ** B) x  = tom A (tom B x)"
  unfolding tom_def using matrix_vector_mul_assoc by metis

lemma matrix_inv_reverses:
  fixes A :: m33
  fixes x :: v3
  assumes "invertible A"
  shows "(tom (matrix_inv A)) (tom A x) = x"
  unfolding matrix_inv_def tom_def
  by (metis (mono_tags, lifting) assms inverse_m_matrix_is_ident matrix_inv_def matrix_vector_mul_assoc
      matrix_vector_mul_lid)

lemma tom_div_hom:
  fixes A :: m33
  fixes x :: v3
  fixes r :: real
  assumes "r \<noteq> 0"
  shows "tom A x = 1/r *s tom A (r *s x)" 
  unfolding tom_def
  by (simp add: assms vec.scale)

lemma equiv_maps_right_mult:
  fixes A B :: m33
  fixes T :: m33
  assumes invertible: "det A \<noteq> 0 \<and> det B \<noteq> 0 \<and> det T \<noteq> 0" 
  assumes equiv:  "equiv_maps (tom A) (tom B)"
  shows "equiv_maps (tom (A ** T)) (tom (B ** T))"
  unfolding equiv_maps_def
proof (safe)
  show "well_defined (tom (A ** T))" using invertible
  by (metis inv_matrices_image_non_zero invertible_det_nz invertible_mult matrices_respect_scaling
      well_defined_def)
  show "well_defined (tom (B ** T))" using invertible
    by (metis inv_matrices_image_non_zero invertible_det_nz invertible_mult matrices_respect_scaling
      well_defined_def)
  obtain l :: real where l_assms: "l \<noteq> 0 \<and> (\<forall> x :: v3 . tom A x = l *s tom B x)"
    using equiv invertible inv_matrices_equiv_iff by auto
  fix x
  have "tom A (tom T x) = l *s tom B (tom T x)" using l_assms by auto
  then have "tom (A ** T) x = l *s tom (B ** T) x" using tom_mult_is_matrix_mult by auto
  then show "\<exists>l. l \<noteq> 0 \<and> tom (A ** T) x = l *s tom (B ** T) x" using l_assms by auto
qed

lemma equiv_maps_left_mult:
  fixes A B :: m33
  fixes T :: m33
  assumes invertible: "det A \<noteq> 0 \<and> det B \<noteq> 0 \<and> det T \<noteq> 0" 
  assumes equiv:  "equiv_maps (tom A) (tom B)"
  shows "equiv_maps (tom (T ** A)) (tom (T ** B))"
  unfolding equiv_maps_def
proof (safe)
  show "well_defined (tom (T ** A))" using invertible
  by (metis inv_matrices_image_non_zero invertible_det_nz invertible_mult matrices_respect_scaling
      well_defined_def)
  show "well_defined (tom (T ** B))" using invertible
    by (metis inv_matrices_image_non_zero invertible_det_nz invertible_mult matrices_respect_scaling
      well_defined_def)
  obtain l :: real where l_assms: "l \<noteq> 0 \<and> (\<forall> x :: v3 . tom A x = l *s tom B x)"
    using equiv invertible inv_matrices_equiv_iff by auto
  fix x
  have "tom T (tom A x) = l *s tom T (tom B x)" using l_assms tom_def vec.scale by auto
  then have "tom (T ** A) x = l *s tom (T ** B) x" using tom_mult_is_matrix_mult by auto
  then show "\<exists>l. l \<noteq> 0 \<and> tom (T ** A) x = l *s tom (T ** B) x" using l_assms by auto
qed

lemma exists_auto:
  fixes a b c d :: v3
  fixes a' b' c' d' :: v3
  assumes non_zero: "set_non_zero {a, b, c, d, a', b', c', d'}"
  assumes not_collinear: "set_not_RP2_collinear {a, b, c, d}"
  assumes not_collinear_img: "set_not_RP2_collinear {a', b', c', d'}"
  assumes distinct: "a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d"
  assumes distinct_img: "a' \<noteq> b' \<and> a' \<noteq> c' \<and> a' \<noteq> d' \<and> b' \<noteq> c' \<and> b' \<noteq> d' \<and> c' \<noteq> d'"
  shows "\<exists> A :: m33 . \<exists> l u v :: real . l \<noteq> 0 \<and> u \<noteq> 0 \<and> v \<noteq>0 
    \<and> det A \<noteq> 0 \<and> tom A a  = l *s a' \<and> tom A b = u *s b' \<and> tom A c = v *s c' \<and> tom A d = d'"
proof -
  obtain F f1 f2 f3 where F_assms: "f1 \<noteq> 0 \<and> f2 \<noteq> 0 \<and> f3 \<noteq> 0
    \<and> det F \<noteq> 0 \<and> tom F p1 = f1 *s a \<and> tom F p2 = f2 *s b \<and> tom F p3 = f3 *s c \<and> tom F q = d"
    using not_collinear distinct non_zero exists_auto_helper[of a b c d] set_non_zero_def by auto
  obtain B b1 b2 b3 where B_assms: "b1 \<noteq> 0 \<and> b2 \<noteq> 0 \<and> b3 \<noteq> 0
   \<and> det B \<noteq> 0 \<and> tom B p1 = b1 *s a' \<and> tom B p2 = b2 *s b' \<and> tom B p3 = b3 *s c' \<and> tom B q = d'"
    using not_collinear_img distinct_img non_zero exists_auto_helper[of a' b' c' d'] 
    set_non_zero_def by auto
  let ?A = "B ** (matrix_inv F)"
  have invertible_F: "invertible F" using F_assms using invertible_det_nz by blast
  have  "tom (matrix_inv F) (tom F p1) = p1" 
    using invertible_F  matrix_inv_reverses[of F] by auto
  then have "tom (matrix_inv F) (f1 *s a) = p1" using F_assms by auto
  then have hf1: "tom (matrix_inv F) a = 1/f1 *s p1" using F_assms tom_div_hom by metis 
  have  "tom (matrix_inv F) (tom F p2) = p2" 
    using invertible_F  matrix_inv_reverses[of F] by auto
  then have "tom (matrix_inv F) (f2 *s b) = p2" using F_assms by auto
  then have hf2: "tom (matrix_inv F)  b = 1/f2 *s p2" using F_assms tom_div_hom by metis
  have  "tom (matrix_inv F) (tom F p3) = p3" 
    using invertible_F  matrix_inv_reverses[of F] by auto
  then have "tom (matrix_inv F) (f3 *s c) = p3" using F_assms by auto
  then have hf3: "tom (matrix_inv F) c  = 1/f3 *s p3" using F_assms tom_div_hom by metis
  have  "tom (matrix_inv F) (tom F q) = q" 
    using invertible_F  matrix_inv_reverses[of F] by auto
  then have hf4: "tom (matrix_inv F) d = q" using F_assms by auto
  have "tom ?A a = tom B (1/f1 *s p1)" using tom_mult_is_matrix_mult hf1 by auto
  then have hA1: "tom ?A a = 1/f1 * b1 *s a'" using B_assms tom_div_hom
  by (metis F_assms \<open>tom (matrix_inv F) (f1 *s a) = p1\<close> tom_mult_is_matrix_mult
      vec.scale_scale)
  have "tom ?A b = tom B (1/f2 *s p2)" using tom_mult_is_matrix_mult hf2 by auto
  then have hA2: "tom ?A b = 1/f2 * b2 *s b'" using B_assms tom_div_hom
  by (metis F_assms \<open>tom (matrix_inv F) (f2 *s b) = p2\<close> tom_mult_is_matrix_mult
      vec.scale_scale)
  have "tom ?A c = tom B (1/f3 *s p3)" using tom_mult_is_matrix_mult hf3 by auto
  then have hA3: "tom ?A c = 1/f3 * b3 *s c'" using B_assms tom_div_hom
  by (metis F_assms \<open>tom (matrix_inv F) (tom F p3) = p3\<close> tom_mult_is_matrix_mult
      vector_smult_assoc)
  have "tom ?A d = tom B q" using tom_mult_is_matrix_mult hf4 by auto
  then have hA4: "tom ?A d = d'" using B_assms tom_div_hom by auto
  have c1nz: "1/f1 * b1 \<noteq> 0" using F_assms B_assms by auto
  have c2nz: "1/f2 * b2 \<noteq> 0" using F_assms B_assms by auto
  have c3nz: "1/f3 * b3 \<noteq> 0" using F_assms B_assms by auto
  have "det (matrix_inv F) \<noteq> 0" using F_assms
    using inverse_m_matrix_is_ident invertible_det_nz invertible_right_inverse
    by auto
  then have det_nz: "det ?A \<noteq> 0" using B_assms det_mul[of B "matrix_inv F"] by auto
  show ?thesis using c1nz c2nz c3nz det_nz hA1 hA2 hA3 hA4 by blast
qed

lemma unique_auto:
  fixes a b c d :: v3
  fixes a' b' c' d' :: v3
  fixes A B :: m33
  assumes non_zero: "set_non_zero {a, b, c, d, a', b', c', d'}"
  assumes not_collinear: "set_not_RP2_collinear {a, b, c, d}"
  assumes not_collinear_img: "set_not_RP2_collinear {a', b', c', d'}"
  assumes distinct: "a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d"
  assumes distinct_img: "a' \<noteq> b' \<and> a' \<noteq> c' \<and> a' \<noteq> d' \<and> b' \<noteq> c' \<and> b' \<noteq> d' \<and> c' \<noteq> d'"
  assumes A_maps_to: "\<exists> l u v :: real . l \<noteq> 0 \<and> u \<noteq> 0 \<and> v \<noteq>0 
    \<and>  det A \<noteq> 0 \<and> tom A a = l *s a' \<and> tom A b = u *s b' \<and> tom A c  = v *s c' \<and> tom A d = d'"
  assumes B_maps_to: "\<exists> l u v :: real . l \<noteq> 0 \<and> u \<noteq> 0 \<and> v \<noteq>0 
    \<and>  det B \<noteq> 0 \<and> tom B a = l *s a' \<and> tom B b = u *s b' \<and> tom B c  = v *s c' \<and> tom B d = d'"
  shows "equiv_maps (tom A) (tom B)"
  unfolding equiv_maps_def
  unfolding well_defined_def
proof (safe)
  show "respects_scaling (tom A)"
    using matrices_respect_scaling by auto
  show "image_non_zero (tom A)"
    using A_maps_to inv_matrices_image_non_zero by auto
  show "respects_scaling (tom B)"
    using matrices_respect_scaling by auto
  show "image_non_zero (tom B)"
    using B_maps_to inv_matrices_image_non_zero by auto
  fix x 
  obtain l u v :: real where A_assms: "l \<noteq> 0 \<and> u \<noteq> 0 \<and> v \<noteq>0 
    \<and>  det A \<noteq> 0 \<and> tom A a = l *s a' \<and> tom A b = u *s b' \<and> tom A c  = v *s c' \<and> tom A d = d'" 
    using A_maps_to by auto
  obtain l' u' v' :: real where B_assms: "l' \<noteq> 0 \<and> u' \<noteq> 0 \<and> v' \<noteq>0 
    \<and>  det B \<noteq> 0 \<and> tom B a = l' *s a' \<and> tom B b = u' *s b' \<and> tom B c  = v' *s c' \<and> tom B d = d'"
    using B_maps_to by auto
  have "set_non_zero {a', b', c', d', p1, p2, p3, q}" using p1p2p3q_not_zero non_zero 
    unfolding set_non_zero_def by auto  
  then obtain T c1 c2 c3  where T_assms: "c1 \<noteq> 0 \<and> c2 \<noteq> 0 \<and> c3 \<noteq> 0 \<and> det T \<noteq> 0 \<and> tom T p1 = c1 *s a \<and> tom T p2 = c2 *s b \<and> tom T p3 = c3 *s c \<and> tom T q = d"
    using exists_auto[of p1 p2 p3 q a b c d] distinct p1p2p3q_distinct not_collinear p1p2p3q_not_collinear non_zero set_non_zero_def
    by auto
  have T_invertible: "invertible T" using T_assms by (simp add: invertible_det_nz)
  then have T_inv_invertible: "det (matrix_inv T) \<noteq> 0"
    using inverse_m_matrix_is_ident invertible_det_nz invertible_right_inverse by auto
  have "tom A (tom T p1) = (l * c1) *s a'" using A_assms T_assms tom_def
    by (simp add: vector_scalar_commute) 
  then have hAa: "tom (A ** T) p1 = (l * c1) *s  a'" using tom_mult_is_matrix_mult[of A T] A_assms T_assms by auto
  have "tom B (tom T p1) = (l' * c1) *s a'" using B_assms T_assms tom_def
    by (simp add: vector_scalar_commute)
  then have hBa: "tom (B ** T) p1 = (l' * c1) *s a' \<and> (l' * c1) \<noteq> 0" using tom_mult_is_matrix_mult[of B T] B_assms T_assms by auto
  have "tom A (tom T p2) = (u * c2) *s b'" using A_assms T_assms tom_def
    by (simp add: vector_scalar_commute)
  then have hAb: "tom (A ** T) p2 = (u * c2) *s b' \<and> (u * c2) \<noteq> 0" using tom_mult_is_matrix_mult[of A T] A_assms T_assms by auto
  have "tom B (tom T p2) = (u' * c2) *s b'" using B_assms T_assms tom_def
    by (simp add: vector_scalar_commute)
  then have hBb: "tom (B ** T) p2 = (u' * c2) *s b' \<and> (u' * c2) \<noteq> 0" using tom_mult_is_matrix_mult[of B T] B_assms T_assms by auto
  have "tom A (tom T p3) = (v * c3) *s c'" using A_assms T_assms tom_def
    by (simp add: vector_scalar_commute)
  then have hAc: "tom (A ** T) p3 = (v * c3) *s c' \<and> (v * c3) \<noteq> 0" using tom_mult_is_matrix_mult[of A T] A_assms T_assms by auto
  have "tom B (tom T p3) = (v' * c3) *s c'" using B_assms T_assms tom_def
    by (simp add: vector_scalar_commute)
  then have hBc: "tom (B ** T) p3 = (v' * c3) *s c' \<and> (v' * c3) \<noteq> 0" using tom_mult_is_matrix_mult[of B T] B_assms T_assms by auto
  have hAd: "tom (A ** T) q = d'"
   by (simp add: A_assms T_assms tom_mult_is_matrix_mult)
  have hBd: "tom (B ** T) q = d'"
    by (simp add: B_assms T_assms tom_mult_is_matrix_mult)
  have AT_invertible: "invertible (A ** T)" using T_invertible A_assms
    using invertible_det_nz invertible_mult by auto
  have BT_invertible: "invertible (B ** T)" using T_invertible B_assms
    using invertible_det_nz invertible_mult by auto
  have h1: "equiv_maps (tom (A ** T)) (tom (B ** T))"
    using AT_invertible BT_invertible hAa hBa hAb hBb hAc hBc hAd hBd not_collinear_img non_zero distinct_img
    using set_non_zero_def A_assms invertible_det_nz
    using unique_auto_helper[of a' b' c' d' "A ** T" "B ** T"] by auto              
  have comp_inv: "det (A ** T) \<noteq> 0 \<and> det (B ** T) \<noteq> 0" using T_invertible A_maps_to B_maps_to
    using invertible_det_nz invertible_mult by blast
  then have "equiv_maps (tom (A ** T ** matrix_inv T)) (tom (B ** T ** matrix_inv T))"
    using T_inv_invertible comp_inv h1 equiv_maps_right_mult[of "A ** T" "B ** T" "matrix_inv T"]
    by auto
  then have "equiv_maps (tom A) (tom B)" using matrix_inv_def
    by (smt (verit, del_insts) T_invertible inverse_m_matrix_is_ident invertible_right_inverse matrix_mul_assoc
        matrix_mul_rid)
  then show "\<exists>l. l \<noteq> 0 \<and> tom A x = l *s tom B x" unfolding equiv_maps_def by auto
qed


theorem RP2_auto_given_by_matrix:
(*shows PGL2 is in fact equal to Aut \<pi> *)
  fixes f :: "v3 \<Rightarrow> v3" 
  assumes "is_RP2_auto f"
  shows "\<exists> A :: m33 . (\<forall> x \<in> v3. x \<noteq> 0 \<longrightarrow> f x = (tom A) x)"
  by sorry

end