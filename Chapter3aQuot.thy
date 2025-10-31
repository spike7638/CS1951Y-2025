theory Chapter3aQuot

imports Chapter3anew "HOL-Algebra.Group" "HOL-Algebra.Coset"

begin

(* The following definitions are copied almost verbatim from:
 https://www.isa-afp.org/sessions/topological_groups/#Matrix_Group.html#Matrix_Group *)

(*First we define GL(n) generally: *)
definition GL :: "(('a :: field)^'n^'n) monoid" where
"GL = \<lparr>carrier = {A. invertible A}, monoid.mult = (**), one = mat 1\<rparr>"

definition GL3 :: "((real)^3^3) monoid" where
"GL3 = GL"

(*We need a generalization of several matrix theorems which I initially proved
  only for 3x3 matrices... *)

lemma matrix_inv_is_inv:
  assumes "invertible A"
  shows "A ** (matrix_inv A) = mat 1" and "(matrix_inv A) ** A = mat 1"  
proof -
  show "A ** matrix_inv A = mat 1" 
    using assms unfolding invertible_def matrix_inv_def by (simp add: verit_sko_ex')
  show "(matrix_inv A) ** A = mat 1" 
    using assms unfolding invertible_def matrix_inv_def by (simp add: verit_sko_ex')
qed

lemma invertible_imp_right_inverse_is_inverse:
  assumes invertible: "invertible A" and "A ** B = mat 1"
  shows "matrix_inv A = B"
  using matrix_inv_is_inv[OF invertible] assms by (metis matrix_mul_assoc matrix_mul_lid)

lemma matrix_inv_invertible:
  assumes "invertible A"
  shows "invertible (matrix_inv A)"
  using assms matrix_inv_is_inv invertible_def by fast

lemma
  GL_group: "group GL" and 
  GL_carrier [simp]: "carrier GL = {A. invertible A}" and
  GL_inv [simp]: "A  \<in> carrier GL \<Longrightarrow> inv\<^bsub>GL\<^esub> A = matrix_inv A"
proof -
  show h: "carrier GL = {A. invertible A}" unfolding GL_def by simp
  show "group GL"
  proof (unfold_locales, goal_cases)
    case 3
    then show ?case unfolding GL_def by (simp add: invertible_def)
    case 6
    then show ?case using GL_def using invertible_def  unfolding h Group.Units_def
    by (smt (verit) Collect_mono mem_Collect_eq monoid.select_convs(1,2))
  qed (unfold GL_def, auto simp: matrix_mul_assoc invertible_mult)
  interpret group GL by fact
  show "A \<in> carrier GL \<Longrightarrow> inv\<^bsub>GL\<^esub> A = matrix_inv A"
  proof -
    fix A
    assume "A \<in> carrier GL"
    show "inv\<^bsub>GL\<^esub> A = matrix_inv A" using matrix_inv_is_inv matrix_inv_invertible
      using inv_equality h unfolding GL_def
      using \<open>A \<in> carrier GL\<close> h by fastforce
  qed
qed

lemma GL3_group: "group GL3" using GL3_def GL_group by auto

lemma GL_mult: "a \<otimes>\<^bsub>GL\<^esub> b = a ** b" using GL_def
  by (metis monoid.select_convs(1))

lemma GL_one: "monoid.one GL = mat 1" unfolding GL_def by simp

definition ZGL3 :: "(real^3^3) monoid" where
"ZGL3 = GL \<lparr>carrier := {A :: m33 . \<exists> l :: real . l \<noteq> 0 \<and>  A = scaleR l (mat 1)}\<rparr>"

(*Defined over the reals because I could not figure out how to write scalar multiplication
  for an arbitrary field ... *)


(* As the name suggests, ZGL is the center of GL *)

lemma ZGL3_carrier [simp]: "carrier ZGL3 = {A :: m33 . \<exists> l . l \<noteq> 0 \<and> A = scaleR l (mat 1) }" 
  unfolding ZGL3_def by simp

lemma in_ZGL3:
  fixes Q :: m33
  fixes l :: real
  assumes "l \<noteq> 0 \<and> Q = scaleR l (mat 1)"
  shows "Q \<in> carrier ZGL3"
  unfolding ZGL3_carrier
  using assms
  by auto

lemma ZGL3_not_empty: "carrier ZGL3 \<noteq> {}"
proof - 
  have "mat 1 \<in> carrier ZGL3" using ZGL3_carrier
    by (metis (mono_tags, lifting) mem_Collect_eq scaleR_one zero_neq_one)
  then show ?thesis by auto
qed

lemma ZGL3_subset_GL3: "carrier ZGL3 \<subseteq> carrier GL"
proof 
  fix A :: m33
  assume hx: "A \<in> carrier ZGL3"
  let ?I = "(mat 1) :: ((real, 3) vec, 3) vec"
  obtain l where A_assm: " l \<noteq> 0 \<and> A = scaleR l (?I)" using hx ZGL3_carrier by fastforce
  have "invertible (?I)"
    by (simp add: invertible_def)
  then have "invertible (scaleR l ?I)" using scalar_invertible[of l ?I] A_assm by simp
  then have "invertible A"
    by (simp add: A_assm)
  then show "A \<in> carrier GL" using GL_carrier by blast
qed

lemma matrix_mult_scalar_distrib:
  fixes A B :: m33
  fixes a b :: real
  shows "scaleR a A ** scaleR b B = scaleR (a * b) (A ** B)"
  by (metis matrix_scalar_ac scalar_matrix_assoc scaleR_scaleR)

lemma ZGL3_subgroup_GL: "subgroup (carrier ZGL3) GL"
 proof (rule group.subgroupI, goal_cases)
   case 1
   then show ?case using GL_group by simp
 next
   case 2
   then show ?case using ZGL3_subset_GL3 by simp
 next
   case 3
   then show ?case using ZGL3_not_empty by auto
 next
   case (4 a)
   then show ?case 
   proof - 
     obtain l :: real where l_assms: "l \<noteq> 0 \<and> a = scaleR l (mat 1)"
       using "4" ZGL3_carrier by auto
     have non_zero: "1/l \<noteq> (0 :: real)" using l_assms by auto
     then have h0: "(scaleR l (mat 1 :: m33)) ** (scaleR (1/l) (mat 1)) = (scaleR (l * (1/l))(mat 1 ** mat 1))"
       using matrix_mult_scalar_distrib[of l "mat 1" "1/l" "mat 1"] by simp
     have h1: "(1/l * l) = 1 \<and> (mat 1) ** (mat 1) = mat 1" using l_assms by simp
     then have h2: "(scaleR l (mat 1 :: m33)) ** (scaleR (1/l) (mat 1)) = (mat 1)" 
       using h0 l_assms  matrix_mult_scalar_distrib [of l "(mat 1::m33)" "(1/l)" "(mat 1)"] by simp
     then have h3: "a ** (scaleR (1/l) (mat 1)) = (mat 1)" using l_assms by blast
     then have "inv\<^bsub>GL\<^esub> a = scaleR (1/l) (mat 1)" 
     using GL_carrier GL_inv invertible_imp_right_inverse_is_inverse invertible_right_inverse
         mem_Collect_eq by metis
   then show ?thesis using l_assms non_zero ZGL3_carrier by blast
 qed 
 next
   case (5 a b)
   then show ?case
   proof -
     obtain l :: real where l_assms: "l \<noteq> 0 \<and> a = scaleR l (mat 1)" 
       using "5" ZGL3_carrier by auto
     obtain p :: real where p_assms: "p \<noteq> 0 \<and> b = scaleR p (mat 1)" 
       using "5" ZGL3_carrier by auto
     have non_zero: "l * p \<noteq> 0" using l_assms p_assms by auto
     have "(scaleR l (mat 1 :: m33)) ** (scaleR p (mat 1)) = scaleR (l * p) (mat 1)" 
       using  matrix_mult_scalar_distrib[of l "mat 1" p "mat 1"] by simp
     then have "a ** b = scaleR (l * p) (mat 1)" by (simp add: l_assms p_assms)
     then have "a ** b \<in> carrier ZGL3" using non_zero in_ZGL3 non_zero by auto
     then show ?thesis using GL_mult[of a b] by simp
qed
qed

thm group.normal_inv_iff[of GL "carrier ZGL3"]
thm normal.factorgroup_is_group
(*use normal_inv_iff *)

lemma ZGL3_conj_action:
fixes x h 
assumes "x \<in> carrier GL"
assumes "h \<in> carrier ZGL3"
shows "x \<otimes>\<^bsub>GL\<^esub> h \<otimes>\<^bsub>GL\<^esub> inv\<^bsub>GL\<^esub> x \<in> carrier ZGL3"
proof -
  obtain l :: real where l_assms: "l \<noteq> 0 \<and> h = scaleR l (mat 1)" using ZGL3_carrier assms(2) by auto
  then have "x ** h = scaleR l (x ** (mat 1))" by (simp add: matrix_scalar_ac)
  then have h1: "x ** h = scaleR l x" by simp
  have h2:  "(scaleR l x) ** matrix_inv x = scaleR l (x ** inv\<^bsub>GL\<^esub> x)" 
    by (metis GL_inv assms(1) scalar_matrix_assoc)
  have "x ** inv\<^bsub>GL\<^esub> x = mat 1" unfolding GL_def 
   by (metis GL_carrier GL_def GL_inv assms(1) matrix_inv_is_inv(1) mem_Collect_eq)
  then have "(scaleR l x) ** matrix_inv x = scaleR l (mat 1)" using h2 by simp 
  then have "x ** h ** matrix_inv x = scaleR l (mat 1)" using h1 by auto
  then show ?thesis using l_assms GL_mult
    by (metis GL_inv assms(1,2))
qed

lemma ZGL3_normal_in_GL3: "normal (carrier ZGL3) GL"
  using group.normal_inv_iff[of GL "carrier ZGL3"] GL_group ZGL3_subgroup_GL ZGL3_conj_action
  by auto

(* definition
  FactGroup :: "[('a,'b) monoid_scheme, 'a set] \<Rightarrow> ('a set) monoid" (infixl \<open>Mod\<close> 65)
    \<comment> \<open>Actually defined for groups rather than monoids\<close>
   where "FactGroup G H = \<lparr>carrier = rcosets\<^bsub>G\<^esub> H, mult = set_mult G, one = H\<rparr>" *)

definition PGL2 :: "m33 set monoid"  where "PGL2 = FactGroup GL (carrier ZGL3)"

(* Could also write GL Mod (carrier ZGL3) *)

lemma PGL2_group: "group PGL2"
  using normal.factorgroup_is_group[of "carrier ZGL3" GL] ZGL3_normal_in_GL3 PGL2_def by auto


definition SL :: "(('a :: field)^'n^'n) monoid" where
"SL = GL \<lparr>carrier := {A. det A = 1}\<rparr>"

definition unit_group :: "('a :: field) monoid" where
"unit_group = \<lparr>carrier = UNIV - {0}, monoid.mult = (*), one = 1\<rparr>" 

lemma 
  group_unit_group: "group unit_group" and
  inv_unit_group: "x \<in> carrier unit_group \<Longrightarrow> inv\<^bsub>unit_group\<^esub> x = inverse x"
proof -
  have h1: "x \<in> Group.Units unit_group" if "x \<noteq> 0" for x
  proof -
    have "x \<otimes>\<^bsub>unit_group\<^esub> 1/x = \<one>\<^bsub>unit_group\<^esub>" "1/x \<otimes>\<^bsub>unit_group\<^esub> x = \<one>\<^bsub>unit_group\<^esub>" 
      using that unfolding unit_group_def by auto
    then show ?thesis unfolding Group.Units_def unit_group_def using that by fastforce
  qed
  have "carrier unit_group = {x . x \<noteq> 0}" unfolding unit_group_def by force
  then have h2: "carrier unit_group \<subseteq> Group.Units unit_group" using h1 by blast
  have h3: "Group.monoid unit_group" unfolding Group.monoid_def unit_group_def by simp
  then show "group unit_group" unfolding group_def group_axioms_def using h2 h3 by auto
  then interpret group unit_group by blast
  show "inv\<^bsub>unit_group\<^esub> x = inverse x" if "x \<in> carrier unit_group"
    using that inv_equality[of "inverse x"] unfolding unit_group_def by simp
qed


lemma det_homomorphism: "group_hom GL unit_group det"
proof -
  have "det \<in> carrier GL \<rightarrow> carrier unit_group"
    unfolding GL_carrier unit_group_def using invertible_det_nz by auto
  moreover have "det (A \<otimes>\<^bsub>GL\<^esub> B) = det A \<otimes>\<^bsub>unit_group\<^esub> det B" for A B
    unfolding GL_def unit_group_def using det_mul by auto
  ultimately have "det \<in> hom GL unit_group" unfolding hom_def by blast 
  then show ?thesis using GL_group group_unit_group
    unfolding group_hom_def group_hom_axioms_def by blast
qed
                              
lemma
  SL_kernel_det: "carrier (SL :: (('a :: field)^'n^'n) monoid) = kernel GL unit_group det" and
  SL_subgroup: "subgroup (carrier SL) (GL :: ('a^'n^'n) monoid)" and
  SL_carrier [simp]: "carrier SL = {A. det A = 1}"                  
proof -                           
  interpret group_hom "GL :: ('a^'n^'n) monoid" unit_group det using det_homomorphism by blast
  show h:  "carrier SL = {A. det A = 1}" unfolding SL_def by simp
   show "carrier (SL :: ('a^'n^'n) monoid) = kernel GL unit_group det"     
    unfolding kernel_def[of GL unit_group det] h using invertible_det_nz unfolding unit_group_def by force
  then show "subgroup (carrier SL) (GL :: ('a^'n^'n) monoid)" using subgroup_kernel by presburger
qed

lemma SL_one: "monoid.one SL = mat 1" using SL_def GL_def 
  by (metis monoid.select_convs(2) partial_object.update_convs(1))

definition SL3 where "SL3 = (SL :: ((real)^3^3) monoid)"  

lemma SL3_group: "group SL3" using SL3_def SL_subgroup subgroup.subgroup_is_group
  by (metis GL_group SL_carrier SL_def)

(* take items in SL3 to things in PGL2 *)
definition g :: "m33 \<Rightarrow> m33 set" where "g x = (if (x \<in> carrier SL3) then (carrier ZGL3)#>\<^bsub>GL3\<^esub>x else undefined)"

definition f :: "m33 \<Rightarrow> m33" where "f x = (if x \<in> carrier GL3 then scaleR (1/((root 3) (det x))) x else undefined)"

lemma det_scale_helper:
  fixes A :: m33
  fixes c :: real
  shows "det (scaleR c (mat 1 :: m33)) = c^3"
  (* using Determinants.det_matrix_scaleR[of c]
  matrix_id_mat_1 *)
proof -
  have "scaleR c (mat 1 :: m33) = matrix ((*\<^sub>R) c)"
  by (metis (lifting) ext matrix_of_matrix_vector_mul matrix_vector_mul_lid
      scaleR_matrix_vector_assoc)
  then show "det (scaleR c (mat 1 :: m33)) = c^3" using Determinants.det_matrix_scaleR by auto
qed
  

lemma det_scale:
  fixes A :: m33
  fixes c :: real
  shows "det (scaleR c A) = c^3 * (det A)"
proof -
  have h1: "det (scaleR c A) = det ((scaleR c (mat 1) :: m33) ** A)"
  by (metis matrix_mul_lid matrix_scalar_ac)
  have h2: "det ((scaleR c (mat 1) :: m33) ** A) = det (scaleR c (mat 1) :: m33) * det A" using det_mul by auto
  have h3: "det (scaleR c (mat 1) :: m33) = c^3" using det_scale_helper[of c] by auto
  show ?thesis using h1 h2 h3 by auto
qed

thm Determinants.det_matrix_scaleR
lemma f_lands_in_SL3: "f ` (carrier GL3) \<subseteq> carrier SL3"
proof 
 fix y
  assume "y \<in> f ` (carrier GL3)"
  then obtain x where x_assm: "x \<in> carrier GL3 \<and> f x = y" using image_def by blast
  have h0: "invertible x" using x_assm GL_carrier GL3_def by simp
  then have h1: "det x \<noteq> 0" using invertible_det_nz[of x] by auto
  have h2: "f x = scaleR (1/(root 3) ((det x))) x" using f_def x_assm by auto
  have "(1/((root 3) (det x)))^3 = 1 / det x" using h1
  by (simp add: odd_real_root_pow power_one_over)
  then have "det (f x) = 1" using det_scale h1 h2 by simp
  then have "f x \<in> carrier SL3" using SL3_def SL_carrier by simp
  then have "x \<in> carrier GL3 \<Longrightarrow> f x \<in> carrier SL3" by auto
  then show "y \<in> f ` (carrier GL3) \<Longrightarrow> y \<in> carrier SL3" using x_assm by auto
qed

lemma f_sl3_subset_img: "carrier SL3 \<subseteq> f ` (carrier GL3)"
proof
  fix x
  assume "x \<in> carrier SL3"
  have h0: "x \<in> carrier GL3" 
  by (metis GL3_def SL3_def SL_subgroup \<open>x \<in> carrier SL3\<close>
      subgroup.mem_carrier)
  have "det x = 1" using SL3_def SL_def SL_carrier using \<open>x \<in> carrier SL3\<close> by auto
  then have h1: "(root 3) (1/((det x))) = 1" by auto
  have "f x = scaleR ((1/((root 3)(det x)))) x" using h0 f_def by auto
  then have "f x = x" using f_def SL3_def SL_def using h1 by auto
  then show "x \<in> f ` (carrier GL3)" using h0  by (simp add: rev_image_eqI)
qed

lemma f_image:
  shows "f ` (carrier GL3) = (carrier SL3)"
proof 
  show "f ` carrier GL3 \<subseteq> carrier SL3" using f_lands_in_SL3 by auto
  show "carrier SL3 \<subseteq> f ` carrier GL3" using f_sl3_subset_img by auto
qed
  
lemma f_hom: "f \<in> hom GL3 SL3"
proof (rule homI)
  fix x y
  assume x_assm: "x \<in> carrier GL3"
  assume y_assm: "y \<in> carrier GL3"
  show "f x \<in> carrier SL3" using f_lands_in_SL3 x_assm by auto
  show " f (x \<otimes>\<^bsub>GL3\<^esub> y) = f x \<otimes>\<^bsub>SL3\<^esub> f y"
    unfolding GL3_def GL_def SL_def SL3_def
    using GL_mult f_def det_mul
  by (smt (verit, del_insts) GL3_def GL_carrier invertible_mult lambda_one
      matrix_mult_scalar_distrib mem_Collect_eq monoid.select_convs(1)
      numeral_eq_one_iff numeral_times_numeral partial_object.update_convs(1)
      real_root_mult times_divide_times_eq x_assm y_assm)
qed

lemma f_group_hom: "group_hom GL3 SL3 f" unfolding group_hom_def group_hom_axioms_def
  using GL3_group SL3_group f_hom by auto

lemma f_kernel_subset: "kernel GL3 SL3 f \<subseteq> carrier ZGL3"
proof 
  fix x
  assume x_assm: "x \<in> kernel GL3 SL3 f"
  then have h0: "x \<in> carrier GL3"
    by (metis f_group_hom group_hom.subgroup_kernel subgroup.mem_carrier)
  then have "invertible x" using GL3_def GL_carrier by simp
  then have h0a: "det x \<noteq> 0" using invertible_det_nz[of x] by auto
  have h1: "f x = mat 1" using kernel_def SL_one using x_assm
    by (metis (mono_tags, lifting) SL3_def mem_Collect_eq)
  have h2: "scaleR (1/((root 3) (det x))) x = f x" using f_def x_assm h0
    by auto
  then have "scaleR (1/((root 3) (det x))) x = mat 1" using h1 by auto
  then have h3: "x = scaleR ((root 3) (det x)) (mat 1)"
  by (smt (verit, ccfv_threshold) det_0 det_I divide_cancel_left
      eq_vector_fraction_iff mat_0 nonzero_divide_mult_cancel_right scaleR_scaleR
      zero_eq_1_divide_iff)
  have "((root 3) (det x)) \<noteq> 0" using h0a by simp
  then show "x \<in> carrier ZGL3" using ZGL3_carrier h3 by blast
qed

lemma f_kernel_supset: "carrier ZGL3 \<subseteq> kernel GL3 SL3 f"
proof
  fix x
  assume x_assm: "x \<in> carrier ZGL3"
  then obtain l where l_assm: "l \<noteq> 0 \<and> x = scaleR l ( mat 1)" using ZGL3_carrier by auto
  then have h0: "det x = l^3" using det_scale by simp
  have "x \<in> carrier GL3" using GL3_def ZGL3_subset_GL3 x_assm by auto
  then have "f x =  scaleR (1/((root 3) (det x))) x" using f_def by auto
  then have "f x = scaleR (1/l) x" using h0 by (simp add: odd_real_root_power_cancel)
  then have "f x = scaleR (1/l) (scaleR l (mat 1))" using l_assm by auto
  then have "f x = mat 1" using l_assm by auto
  then show "x \<in> kernel GL3 SL3 f" using kernel_def SL_one
    by (metis (mono_tags, lifting) SL3_def \<open>x \<in> carrier GL3\<close> mem_Collect_eq)
qed
  
lemma f_kernel: "kernel GL3 SL3 f = carrier ZGL3"
proof
  show "kernel GL3 SL3 f \<subseteq> carrier ZGL3" using f_kernel_subset by auto
  show "carrier ZGL3 \<subseteq> kernel GL3 SL3 f" using f_kernel_supset by auto
qed

thm normal.r_coset_hom_Mod[of "carrier PGL2"]
thm group_hom.FactGroup_iso

theorem PGL2_iso_SL3: "is_iso PGL2 SL3"
  using group_hom.FactGroup_iso[of GL3 SL3 f] f_group_hom f_kernel f_image PGL2_def GL3_def by simp
end 

