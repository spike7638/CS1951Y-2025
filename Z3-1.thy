theory "Z3-1"
  imports Main  
         "HOL-Algebra.Group" 
         "HOL-Algebra.Bij" 
         "HOL-Analysis.Cartesian_Space"
         "HOL-Analysis.Finite_Cartesian_Product"
         "HOL-Analysis.Determinants"
         "HOL-Analysis.Cross3"
         "Chapter1-2"
         "Chapter1-3"
begin


section "Isabelle groups and monoids"
text\<open> In Isabelle, a group is defined as a monoid with inverses\<close>

definition
  Units :: "_ => 'a set"
  \<comment> \<open>The set of invertible elements\<close>
  where "Units G = {y. y \<in> carrier G \<and> (\<exists>x \<in> carrier G. x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub> \<and> y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>)}"
text\<open>
The above says that Units is a function which, given some algebraic structure (presumably a group
   or a monoid), returns the set of units (invertible elements) in that structure.

 Note that a subscript of "G" denotes that this is the operation in G. 

 locale monoid =
  fixes G (structure)
  assumes m_closed [intro, simp]:
         "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrier G"
      and m_assoc:
         "\<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G\<rbrakk>
          \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
      and one_closed [intro, simp]: "\<one> \<in> carrier G"
      and l_one [simp]: "x \<in> carrier G \<Longrightarrow> \<one> \<otimes> x = x"
      and r_one [simp]: "x \<in> carrier G \<Longrightarrow> x \<otimes> \<one> = x"

locale group = monoid +
  assumes Units: "carrier G <= Units G" *)

 Here "<=" means subset 

 Subgroups are defined in a similar way to Hartshorne: 

locale subgroup =
  fixes H and G (structure)
  assumes subset: "H \<subseteq> carrier G"
    and m_closed [intro, simp]: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> H"
    and one_closed [simp]: "\<one> \<in> H"
    and m_inv_closed [intro,simp]: "x \<in> H \<Longrightarrow> inv x \<in> H" *)

Note that the condition "1 \in H" is equivalent to the group being non-empty

The bijections on a set form a group, with the operation being function composition and
   the neutral element  being the identity function: 

definition
  Bij :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) set"
    \<comment> \<open>Only extensional functions, since otherwise we get too many.\<close>
  (* An extensional function on S is a function defined on S that is undefined outside of S.*) 
  where "Bij S = extensional S \<inter> {f. bij_betw f S S}" 

The set of automorphisms of a group is the set of homomorphisms from the group to itself
   that are also bijections... 

definition
  auto :: "('a, 'b) monoid_scheme \<Rightarrow> ('a \<Rightarrow> 'a) set"
  where "auto G = hom G G \<inter> Bij (carrier G)"

(*... and the group structure on this set is the same as for a BijGroup. *)

(*definition
  AutoGroup :: "('a, 'c) monoid_scheme \<Rightarrow> ('a \<Rightarrow> 'a) monoid"
  where "AutoGroup G = BijGroup (carrier G) \<lparr>carrier := auto G\<rparr>" *)



(*In Isabelle, a homomorphism between G and H is an element of the set hom G H, defined below. *)

(* definition
  hom :: "_ => _ => ('a => 'b) set" where
  "hom G H =
    {h. h \<in> carrier G \<rightarrow> carrier H \<and>
      (\<forall>x \<in> carrier G. \<forall>y \<in> carrier G. h (x \<otimes>_G y) = h x \<otimes>_H h y)}" *)

(*An isomorphism between groups G and H is defined as a homomorphism that is a bijection. *)

(* definition iso :: "_ => _ => ('a => 'b) set"
  where "iso G H = {h. h \<in> hom G H \<and> bij_betw h (carrier G) (carrier H)}" *)
\<close>
(*== P 11-13: Introduce group theory and actions of a permutation group on its underlying set ==*)
(*== P 14-16: Apply this to automorphisms of the 7-point projective plane and the 9-point affine
plane in detail. ==*)

text \<open>Harthshorne reviews RP2 as a quotient of R3 - (0,0,0); lines are sets of points 
x satisfying b \cdot x = 0 for some fixed nonzero vector b. 

Page 17-18(top) introduce matrices and determinants. Let's do those things here now, starting
with the definition of rp2 and working from there. 

Our version of vectors is the type v3 = real^3; a matrix is a list of three of these, i.e.,
real^3^3. Indexing is 1-based, and uses the syntax v$2 or m$3$1. When constructing a vector 
we use the 'vector' function, which takes a list and makes a vector, as in "vector[x,y,z]". 
This is a very generic operator, and it's important to assign a type, either with vector[x,y,z]::v3,
or vector[x::real, y, z] so that Isabelle knows you're working with a vector of 3 real components.
For proofs involving coordinates, unfolding vector_def and using the proof-method "vector" can be a 
big help. We'll start with just vectors, define and prove a few things about RP2, and then move on to matrices.

Fortunately, for real vectors addition is predefined, and scalar multiplication is denoted by a * 
with a subscript R. 
\<close>

subsection\<open>Automorphisms of the real projective plane\<close>
text\<open>
Now let $A = (a_{ij})$ be a $3 \times 3$ matrix of real numbers, and let $\pi$ be the real
projective plane, with homogeneous coordinates $x_1, x_2, x_3$. We define a transformation $T_A$ of $\pi$ as follows: 
The point $(x_1, x_2, x_3)$ goes into the point
\[T_A(x_1, x_2, x_3) = (x_1', x_2', x_3')\]
where
\[x_1' = a_{11}x_1 + a_{12}x_2 + a_{13}x_3\]
\[x_2' = a_{21}x_1 + a_{22}x_2 + a_{23}x_3\]
\[x_3' = a_{31}x_1 + a_{32}x_2 + a_{33}x_3\]
\end{hartshorne}


We'll need 3x3 matrices (our type m33) and we'll define what Hartshorne calls T_A
as a map from RP2 to RP2, and show that 
(i) if A is invertible, then T_A is an automorphism of rp2 (3.7, bottom of p.18)
(ii) if A = cA', then T_A and T_A' are the SAME automorphism  (3.8, top of p 20)
The set of all such matrix xforms will be called PGL(2,R). It's a subgroup 
of the group of all automorphisms (T_A \circ T_B = T_{AB} proves that). 

\<close>
type_synonym m33 = "real^3^3"

definition not_all_zero :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"
  where "not_all_zero x y z  \<longleftrightarrow> x \<noteq> 0 \<or> y \<noteq> 0 \<or> z \<noteq> 0"

lemma vect_zero_eqv2:
  fixes x :: v3
  shows "x = 0 \<longleftrightarrow> x$1 = 0 \<and> x$2 = 0 \<and> x$3 = 0"
  by (metis (mono_tags, lifting) exhaust_3 vec_eq_iff zero_index)

lemma vect_zero_eqv: 
  fixes x y z :: real
  shows "vector[x, y, z] = (0 :: (real, 3) vec) \<longleftrightarrow> x = 0 \<and> y = 0 \<and> z = 0"
  using vect_zero_eqv2 [of "(vector[x, y, z])"] by auto

lemma not_all_zero_eqv: "not_all_zero x y z \<longleftrightarrow> vector[x, y, z] \<noteq> (0 :: (real, 3) vec)"
  unfolding not_all_zero_def using vect_zero_eqv by auto
lemma not_all_zero_eqv2: "not_all_zero x y z \<longleftrightarrow> vector[x, y, z] \<noteq> zvec"
  unfolding not_all_zero_def using vect_zero_eqv by (metis zvec_def) 
   (*Robert: could we simplify this definition by using rp2_coll? *)


definition maps_lines_to_lines :: "(rp2 \<Rightarrow> rp2) \<Rightarrow> bool"
  where "maps_lines_to_lines f \<longleftrightarrow> (\<forall>k P Q R . ((k \<in> rp2_Lines \<and> rp2_incid P k \<and> rp2_incid Q k \<and> rp2_incid R k) \<longrightarrow> 
                                   (\<exists>m . m \<in> rp2_Lines  \<and>  rp2_incid (f P) m \<and> rp2_incid (f Q) m \<and> rp2_incid (f R) m)))"


(*Note that inclusion is sufficient. See also this MSE post:
https://math.stackexchange.com/questions/3481844/is-isomorphic-between-projective-planes-actually-equivalence-relation *)

definition is_RP2_auto :: "(rp2 \<Rightarrow> rp2) \<Rightarrow> bool"
  where "is_RP2_auto f \<longleftrightarrow> (bij_betw f UNIV UNIV) \<and> maps_lines_to_lines f"


(* The below definition helps make the types work out when working with
   definitions like "image_non_zero." In general, writing A *v x will also work.
   tom is short for "transformation of matrix." This transformation, when 
   considered as acting on RP2, is denoted T_A in Hartshorne.
*)
definition tom :: "m33 \<Rightarrow> (v3 \<Rightarrow> v3)"
  where "tom A = (if (invertible A) then (\<lambda>x. A *v x) else (\<lambda>x::v3. x))" 

theorem "tom_inv" [simp]:
  fixes A :: m33
  assumes "invertible A"
  shows "tom A = (\<lambda>x. A *v x)"
  unfolding tom_def using assms by auto

theorem "tom_nonz_det" [simp]:
  fixes A :: m33
  assumes "det A \<noteq> 0"
  shows "tom A = (\<lambda>x. A *v x)"
  unfolding tom_def using assms
  by (simp add: invertible_det_nz)


lift_definition rp2tom::"m33 \<Rightarrow> (rp2 \<Rightarrow> rp2)"
is "tom"
proof (transfer,clarsimp)
  show "\<And>A x y.
       rp2rel x y \<Longrightarrow>
       (rp2rel (tom A x) (tom A y))"
  proof -
    fix A::m33
    fix x::v3
    fix y::v3
    assume ah: "rp2rel x y"
    show "rp2rel (tom A x) (tom A y)" (is ?claim)
    proof (cases "invertible A")
      case inv: True
      have ta: "tom A t = A *v t" for t using tom_def inv by auto
      have xz: "x \<noteq> zvec"  using rp2rel_def ah by blast
      have yz: "y \<noteq> zvec"  using rp2rel_def ah by blast
      obtain c where "x = c *\<^sub>R y" using ah xz yz rp2rel_def by blast
      have nzAt: "t \<noteq> zvec \<longrightarrow> A *v t \<noteq> zvec" for t using xz inv 
        by (metis invertible_def matrix_left_invertible_ker vect_zero_eqv zvec_def)
      have "tom A x \<noteq> zvec" using xz nzAt ta by auto
      have "tom A y \<noteq> zvec" using yz nzAt ta by auto
      then show ?thesis 
        using \<open>tom A x \<noteq> zvec\<close> ah matrix_vector_mult_scaleR rp2rel_def tom_def by auto
      next
      case id: False
      then show ?thesis 
        using ah tom_def by auto
    qed
  qed
qed

lemma "rp2tom_explicit":
  fixes A
  assumes "invertible A"
  shows "rp2tom A = Abs_rp2 \<circ> (tom A) \<circ> Rep_rp2" 
  using rp2tom_def
  by (metis id_apply map_fun_apply map_fun_def)

lemma "rp2tom_explicit2":
  fixes A x
  assumes "invertible A"
  shows "(rp2tom A) x = Abs_rp2 ((tom A)(Rep_rp2 x))" 
  using rp2tom_explicit
  by (metis UNIV_I ar equal_implies_rp2rel rp2_Points_def rp2tom.abs_eq)

(*== the following is more or less the set-up for Theorem 3.7 == *)

(* This actually requires a proof: that make_RP2_auto (tom A) really IS an automorphism, 
rather than undefined. That's most of page 19 of Hartshorne. That theorem appear 
below as "inv_matrices_are_auts" *)

(* Now there follow some basic lemmas about matrices, which will be helpful for the later theorems. *)

definition adj_inv :: "m33 \<Rightarrow> m33"
  where "adj_inv A = transpose (matrix_inv A)"

(* Note that "inner" here denotes the inner product on a vector space *)
lemma transpose_is_adjoint:
  fixes A :: m33
  fixes u :: v3
  fixes w :: v3
  shows "inner u (A *v w) = inner ((transpose A) *v u) w"
  by (simp add: dot_lmul_matrix tom_def)

lemma inverse_m_matrix_is_ident:
  fixes A :: m33
  assumes "invertible A"
  shows "matrix_inv A ** A = mat 1"
  unfolding matrix_inv_def
  using assms invertible_def[of A] 
  by (simp add: verit_sko_ex')
  
lemma collapsing_adjoint:
  fixes A :: m33
  assumes invertible: "det A \<noteq> 0"
  fixes s :: v3
  fixes x :: v3
  shows "inner (tom (adj_inv A) s) (tom A x) = inner s x"
proof - 
  have h0: "invertible A" using invertible_det_nz invertible by auto
  have h1: "inner ((adj_inv A) *v s) (A *v x) = inner s ((matrix_inv A ** A)*v x)" 
    using transpose_is_adjoint adj_inv_def
  by (metis (lifting) matrix_vector_mul_assoc)
  have h2a: "matrix_inv A ** A = mat 1" 
    using h0 inverse_m_matrix_is_ident by auto
  have h2: "inner s (tom (matrix_inv A ** A) x) = inner s ((tom (mat 1)) x)"
    using h2a by simp 
  have h3: "inner s ((tom (mat 1)) x) = inner s x"
    using matrix_vector_mul_lid tom_def by simp
  show ?thesis using h1 h2 h3 tom_def 
  using adj_inv_def h0 h2a invertible_right_inverse transpose_invertible by auto
qed 

lemma explicit_inner_prod:
  fixes s :: v3
  fixes x :: v3
  shows "inner s x =  s$1 * x$1 + s$2 * x$2 +  s$3 * x$3"
  unfolding inner_vec_def
  using sum_3 by auto

lemma va0: 
  fixes x y::v3
  fixes i
  shows "(x+y)$i = x$i + y$i" by (rule vector_component)


(*A simple lemma to help work with vector constructors... *)
lemma vector_add:
  fixes a x b y c z :: real 
  shows "(vector[a + x, b + y, c + z] :: (real, 3) vec) = vector[a, b, c] + vector[x, y, z]"
  unfolding vector_def by vector

(*Another simple lemma to work with vector constructors...*)
lemma matrix_rows:
  fixes A :: m33
  shows "A$1 = vector[A$1$1, A$1$2, A$1$3]"
        "A$2 = vector[A$2$1, A$2$2, A$2$3]"
        "A$3 = vector[A$3$1, A$3$2, A$3$3]"
 using vector_3 row_def vector_def exhaust_3
  by (smt (verit, best) vec_eq_iff)+

lemma matrix_vect_mult_helper:
  fixes B :: m33
  fixes a b c :: real
  assumes "invertible B"
  shows "(tom B) (vector[a, b, c]) = 
          vector[inner (vector [a, b, c]) (B $ 1), inner (vector [a, b, c]) (B $ 2), 
          inner (vector [a, b, c]) (B $ 3)]" 
proof -
  let ?s = "vector[a, b, c]"
  have "(tom B) ?s$1 = inner ?s (B$1) \<and> (tom B) ?s$2 = inner ?s (B$2) \<and> (tom B) ?s$3 = inner ?s (B$3)" 
    using  inner_commute matrix_vector_mul_component tom_def assms by metis
(* (simp add: inner_commute matrix_vector_mul_component tom_def) *)
  then show ?thesis using vector_3
    by (smt (verit, ccfv_SIG) exhaust_3 vec_eq_iff)
qed

(*The lemma below is helpful for the proof of Theorem 3.9 *)
lemma matrix_by_vect_mult:
  fixes s :: v3
  fixes A :: m33
  shows "transpose A *v s = s$1 *s A$1 + s$2 *s A$2 + s$3 *s A$3"
proof -
  let ?At = "transpose A"
  have h1: "(?At *v s)$1 = s$1 * ?At$1$1 + s$2 * ?At$1$2 + s$3 * ?At$1$3"
    using matrix_vector_mul_component[of ?At s 1] explicit_inner_prod[of s "?At$1"]
    using inner_commute[of s "?At$1"] by auto
  have h2: "(?At *v s)$2 = s$1 * ?At$2$1 + s$2 * ?At$2$2 + s$3 * ?At$2$3"
    using matrix_vector_mul_component[of ?At s 2] explicit_inner_prod[of s "?At$2"]
    using inner_commute[of s "?At$2"] by auto
  have h3: "(?At *v s)$3 = s$1 * ?At$3$1 + s$2 * ?At$3$2 + s$3 * ?At$3$3"
    using matrix_vector_mul_component[of ?At s 3] explicit_inner_prod[of s "?At$3"]
    using inner_commute[of s "?At$3"] by auto
  have "?At *v s = vector[s$1 * ?At$1$1 + s$2 * ?At$1$2 + s$3 * ?At$1$3,
                          s$1 * ?At$2$1 + s$2 * ?At$2$2 + s$3 * ?At$2$3,
                          s$1 * ?At$3$1 + s$2 * ?At$3$2 + s$3 * ?At$3$3]"
    using h1 h2 h3 vector_3
    by (smt (verit, del_insts) exhaust_3 vec_eq_iff)  
  then have "?At *v s = vector[s$1 * A$1$1 + s$2 * A$2$1 + s$3 * A$3$1,
                                  s$1 * A$1$2 + s$2 * A$2$2 + s$3 * A$3$2,
                                  s$1 * A$1$3 + s$2 * A$2$3 + s$3 * A$3$3]"
    unfolding transpose_def by simp
  then have "?At *v s = vector[s$1 * A$1$1, s$1 * A$1$2, s$1 * A$1$3] +
                                vector[s$2 * A$2$1, s$2 * A$2$2, s$2 * A$2$3] +
                                vector[s$3 * A$3$1, s$3 * A$3$2, s$3 * A$3$3]"
    using vector_add by metis
  then have "?At *v s = s$1 *s vector[A$1$1, A$1$2, A$1$3] +
                        s$2 *s vector[A$2$1, A$2$2, A$2$3] +
                        s$3 *s vector[A$3$1, A$3$2, A$3$3]"
    using vector_3(1) vector_scalar_mult_def matrix_rows
    by (metis (no_types, lifting) vector_smult_component)
  then show ?thesis using matrix_rows by presburger
  qed

lemma vect_vect_by_vect_mult:
  (* A useful variant of the above for dealing with vectors of vectors, i.e., matrices *)
  fixes s :: v3
  fixes x y z :: v3
  shows "transpose (vector[x, y, z]) *v s = s$1 *s x + s$2 *s y + s$3 *s z"
  using matrix_by_vect_mult vector_3[of x y z]
  by (simp add: matrix_vector_mult_def)

lemma maps_lines_to_lines_helper:
  fixes A :: m33
  fixes a b c :: real
  assumes invertible: "det A \<noteq> 0"
  assumes "(not_all_zero a b c)"
  shows "\<exists> d e f  :: real. not_all_zero d e f \<and> (\<forall>x :: v3. a * x$1 + b*x$2 + c*x$3 = 0
           \<longrightarrow> ( d * ((tom A) x)$1 + e *((tom A) x)$2 + f *((tom A) x)$3 = 0))"
proof - 
  let ?s = "vector[a, b, c]"
  let ?B = "adj_inv A"
  let ?d = "inner ?s (?B$1)"
  let ?e = "inner ?s (?B$2)"
  let ?f = "inner ?s (?B$3)"
  let ?r = "vector[?d, ?e, ?f]"
  have rw1: "?r = tom ?B ?s" using matrix_vect_mult_helper 
  by (metis adj_inv_def inverse_m_matrix_is_ident invertible invertible_det_nz invertible_right_inverse
      transpose_invertible) 
  have req1: "a * x$1 + b*x$2 + c*x$3 = 0
              \<longrightarrow> ( ?d * ((tom A) x)$1 + ?e *((tom A) x)$2 + ?f *((tom A) x)$3 = 0)" for x
  proof (rule impI)
    fix x :: v3
    assume on_line: "a * x$1 + b*x$2 + c*x$3 = 0"
    have inner_rw: "inner ?s x = a * x$1 + b*x$2 + c*x$3"
      using explicit_inner_prod by auto
    have h2a: "inner ?r ((tom A) x) = a * x$1 + b*x$2 + c*x$3"
      using collapsing_adjoint inner_rw invertible rw1 by auto
    have h2: "inner ?r ((tom A) x) = 0" using h2a on_line by auto
    have h3:  "?d * tom A x $ 1 + ?e * tom A x $ 2 + ?f * tom A x $ 3 = inner ?r ((tom A) x)"
      using explicit_inner_prod by auto
    show "?d * tom A x $ 1 +  ?e * tom A x $ 2 +?f * tom A x $ 3 = 0"
      using h2 h3 by auto
    qed
    have req2: "not_all_zero ?d ?e ?f"
    proof (rule ccontr)
      assume not_not_all_zero: "\<not> (not_all_zero ?d ?e ?f)"
      have vect_zero: "?r = (0 :: (real, 3) vec)" using not_all_zero_eqv not_not_all_zero by simp
      then have "vector [a, b, c]\<bullet>adj_inv A$1 = 0 \<and> vector[a, b, c]\<bullet>adj_inv A$2 = 0 \<and> vector [a,b,c] \<bullet> adj_inv A$3 = 0"
      using vect_zero_eqv by auto
      then have s_zero: "?s = (0 :: (real, 3) vec)" using vect_zero
        using all_zero_iff collapsing_adjoint invertible rw1 by metis 
      have s_not_zero: "?s \<noteq> 0" using not_all_zero_eqv[of a b c] assms s_zero by auto
      show "False" using s_zero s_not_zero by auto 
qed 
  show ?thesis using req1 req2 by auto
qed 

lemma maps_lines_to_lines_helper2:
  fixes A :: m33
  fixes y :: v3
  assumes "det A \<noteq> 0"
  and "y \<noteq> zvec"
  shows "\<exists> k :: v3 . (k \<noteq> zvec) \<and> (\<forall>x :: v3. (inner y x = 0)
           \<longrightarrow> (inner k (tom A x) = 0))"
  using  maps_lines_to_lines_helper explicit_inner_prod assms
  by (metis collapsing_adjoint inner_zero_left)

definition v3coplanar :: "(v3) \<Rightarrow> (v3) \<Rightarrow> v3  \<Rightarrow> bool"
  where "v3coplanar x y z \<longleftrightarrow> (x \<noteq> zvec) \<and> (y \<noteq> zvec) \<and> (z \<noteq> zvec) \<and>
    (\<exists>k::v3. k \<noteq> zvec \<and> k \<bullet> x = 0 \<and> k \<bullet> y = 0 \<and> k \<bullet> z = 0)" 

lift_definition rp2coll::"rp2 \<Rightarrow> rp2 \<Rightarrow> rp2 \<Rightarrow> bool"
is "v3coplanar" 
  by (smt (verit, best) Domainp_cr_proj Quotient3_rel Quotient3_rp2 cross_nz cross_refl rp2.domain rp2_incid.abs_eq v3coplanar_def
      zvec_alt)

definition maps_lines_to_lines2 :: "(rp2 \<Rightarrow> rp2) \<Rightarrow> bool"
  where "maps_lines_to_lines2 f \<longleftrightarrow> (\<forall>P Q R . ((rp2coll P Q R) \<longrightarrow> 
                                   (rp2coll (f P) (f Q) (f R))))"

definition is_RP2_auto2 ::  "(rp2 \<Rightarrow> rp2) \<Rightarrow> bool"
  where "is_RP2_auto2 f \<longleftrightarrow> (bij_betw f UNIV UNIV) \<and> maps_lines_to_lines2 f"
(*This is the definition of is_RP2_auto but using the new maps_lines_to_lines *)

lemma t:
  fixes A::m33
  fixes P Q R
  assumes "det A \<noteq> 0"
  assumes "rp2coll P Q R"
  shows "rp2coll (rp2tom A P) (rp2tom A Q) (rp2tom A R)"
proof -
  obtain k where kfacts: "rp2_incid k P \<and> rp2_incid k Q \<and> rp2_incid k R" using rp2coll_def 
  by (metis ar assms(2) dot_product_zero_implies_incid iso_tuple_UNIV_I rp2_Lines_def rp2_Points_def rp2coll.rep_eq
      v3coplanar_def) 
  define h where hfact:"h \<equiv> rp2tom (adj_inv A) k"
  have aifact: "det (adj_inv A) \<noteq> 0"
    by (metis adj_inv_def assms(1) inverse_m_matrix_is_ident invertible_det_nz invertible_right_inverse
      transpose_invertible)
  have "rp2_incid k S \<longrightarrow> rp2_incid h (rp2tom A S)" for S 
  proof (safe)
    have a0: "rp2_incid k S \<equiv> inner (Rep_rp2 k) (Rep_rp2 S) = 0" using rp2_incid.rep_eq by simp
    have a1: "rp2_incid h U \<equiv> (inner (Rep_rp2 h) (Rep_rp2 U) = 0)" for U  using rp2_incid.rep_eq by auto
    then have a2: "rp2_incid h (rp2tom A S) \<equiv> (inner (Rep_rp2 h) (Rep_rp2 (rp2tom A S)) = 0)"  by auto
    then have a3: "rp2_incid (rp2tom (adj_inv A) k) (rp2tom A S) \<equiv> 
      (inner (Rep_rp2 (rp2tom (adj_inv A) k)) (Rep_rp2 (rp2tom A S)) = 0)" using hfact by auto
    have b0: "rp2rel (Rep_rp2 (rp2tom U x))  ((tom U) (Rep_rp2 x))" for U x
      by (metis ar invertible_left_inverse matrix_left_invertible_ker ra rep_P_nz rp2tom.abs_eq tom_def zvec_alt
        zvec_def)
    have b1: "det U \<noteq> 0 \<Longrightarrow> rp2rel  ((tom U) (Rep_rp2 x)) (U *v  (Rep_rp2 x))" for U x 
    by (metis b0 rp2rel_def rp2rel_self tom_nonz_det)

    then have b2: "rp2rel (Rep_rp2 ((rp2tom (adj_inv A)) k)) ((adj_inv A) *v (Rep_rp2 k))" 
    by (metis aifact b0 tom_nonz_det)
  show "rp2_incid k S \<Longrightarrow> rp2_incid h (rp2tom A S) " using a0 a1 a2 a3 b0 b1
    by (metis aifact assms(1) collapsing_adjoint hfact invertible_det_nz rp2_incid.abs_eq rp2tom_explicit2
      tom_def)
qed
  then show ?thesis  using kfacts rep_P_nz rp2_incid.rep_eq rp2coll.rep_eq v3coplanar_def by auto
qed 

definition matrix_scalar_mult :: "real \<Rightarrow> m33 \<Rightarrow> m33"
(infixl "*k" 70) where "k *k A \<equiv> (\<chi> i j. k * A $ i $ j)"

(* Need to prove some associativity things for this, I suspect. *)
lemma msmul_props: 
  fixes A::m33
  fixes s::real
  fixes t::real
  shows "(t *k (s *k A)) = (t * s) *k A" 
  unfolding matrix_scalar_mult_def by fastforce

lemma matrix_scalar_mult_forall [intro]:
 "(A :: m33) = c *k B \<longleftrightarrow> (\<forall> x :: v3 . A *v x = c *\<^sub>R (B *v x))"
  sorry


(* lemma s0:
  assumes "k \<in> rp2_Lines"
  shows "rp2_incid P k \<longleftrightarrow>  ((Rep_rp2 P) \<bullet> (Rep_rp2 k)  = 0)"
  by (simp add: rp2_incid.rep_eq) *)

lemma inv_matrices_img_nonzero:
  fixes A :: m33
  and x :: v3
  assumes "det A \<noteq> 0"
  and "x \<noteq> zvec"
  shows "tom A x \<noteq> zvec"
  using assms tom_nonz_det[of A]
  by (metis collapsing_adjoint inner_eq_zero_iff inner_zero_right
      zvec_alt)

(* We should probably get rid of the next lemma *)
lemma inv_matrix_inj:
  fixes A :: m33
  fixes x :: v3
  assumes "det A \<noteq> 0"
  shows "tom A x = 0 \<longrightarrow> x = 0"
  sorry
(*
proof (rule impI; rule ccontr)
  assume x_in_ker: "tom A x = 0"
  assume to_contr: "x \<noteq> 0"
  show "False" using assms to_contr  image_non_zero_def x_in_ker sorry
qed
*)

lemma inv_matrices_maps_lines_to_lines2:
  fixes A :: m33
  assumes invertible: "det A \<noteq> 0"
  shows "maps_lines_to_lines2 (rp2tom A)"
  unfolding maps_lines_to_lines2_def
proof (safe)
  fix P Q R :: rp2
  assume coll: "rp2coll P Q R"
  obtain Pr Qr Rr :: v3 where Pr_def: "Abs_rp2 Pr = P" 
    and Qr_def: "Abs_rp2 Qr = Q"
    and Rr_def: "Abs_rp2 Rr = R"
    and nz: "(Pr \<noteq> zvec \<and> Qr \<noteq> zvec \<and> Rr \<noteq> zvec)"
    using ar rep_P_nz by blast
  then obtain V :: v3 where V_def: "V \<noteq> 0 \<and> inner V Pr = 0 \<and> inner V Qr = 0 \<and> inner V Rr = 0" 
  by (metis coll cross_nz cross_refl rp2coll.abs_eq v3coplanar_def
      zvec_alt)
  then obtain K :: v3 where K_def: "K \<noteq> zvec \<and> ((inner V) x = (0 :: real)
           \<longrightarrow> (inner K (tom A x) = 0))" for x :: v3 
    using maps_lines_to_lines_helper2 invertible
  using zvec_alt by force
  then have h1: "inner K (tom A Pr) = 0 \<and> inner K (tom A Qr) = 0 \<and> inner K (tom A Rr) = 0"
    using V_def using all_zero_iff zvec_alt by blast
  have h2: "(tom A Pr \<noteq> zvec) \<and> (tom A Qr \<noteq> zvec) \<and> (tom A Rr \<noteq> zvec)" using invertible nz
  inv_matrices_img_nonzero by auto
  then have "v3coplanar (tom A Pr) (tom A Qr) (tom A Rr)" 
    using v3coplanar_def[of "tom A Pr" "tom A Qr" "tom A Rr"] K_def h1 by auto
  then show "rp2coll (rp2tom A P) (rp2tom A Q) (rp2tom A R)"
  by (metis Pr_def Qr_def Rr_def cross_nz cross_refl h2 nz rp2coll.abs_eq
      rp2tom.abs_eq zvec_alt)
qed

lemma tom_representative:
  fixes A x
  assumes invertible: "det A \<noteq> 0"
  shows "(rp2tom A x) = Abs_rp2 ((tom A) (Rep_rp2 x))" 
  by (simp add: ar invertible invertible_det_nz rp2tom_explicit2)

lemma tom_representative_rel:
  fixes A x
  assumes invertible: "det A \<noteq> 0"
  shows "rp2rel (Rep_rp2 (rp2tom A x)) ((tom A) (Rep_rp2 x))" 
  using tom_representative assms
  by (metis Quotient3_rp2 cross_nz cross_refl inv_matrices_img_nonzero
      rep_P_nz rep_abs_rsp_left zvec_alt)

lemma tom_bij: 
  fixes A :: m33
  assumes invertible: "det A \<noteq> 0"
  shows "bij (tom A)"
  using tom_nonz_det[of A] invertible 
  using invertible_det_nz invertible_eq_bij by auto

lemma tom_inj:
  fixes A :: m33
  assumes invertible: "det A \<noteq> 0"
  shows "inj (tom A)" using tom_bij[of A] invertible bij_def by auto

lemma tom_surj:
  fixes A :: m33
  assumes invertible: "det A \<noteq> 0"
  shows "surj (tom A)" using tom_bij[of A] invertible bij_def by metis
  
theorem inv_matrices_are_auts: (* theorem 3.7 *)
  fixes A :: m33
  assumes invertible: "det A \<noteq> 0"
  shows "is_RP2_auto2 (rp2tom A)" 
  unfolding is_RP2_auto2_def
(*  unfolding well_defined_def *)
proof (safe)
  have inj: "inj (rp2tom A)"
    unfolding inj_def
  proof (safe)
    fix x y :: rp2
    assume "rp2tom A x = rp2tom A y"
    then have "rp2rel (tom A (Rep_rp2 x)) (tom A (Rep_rp2 y))"
    by (metis invertible part_equivp_def part_equivp_rp2rel
        tom_representative_rel)
    then obtain c :: real where c_def: "c \<noteq> 0 \<and> (tom A (Rep_rp2 x)) = c *\<^sub>R (tom A (Rep_rp2 y))"
      using rp2rel_def by auto
    then have "(Rep_rp2 x) = c *\<^sub>R (Rep_rp2 y)" using tom_nonz_det[of A] invertible 
      by (metis (mono_tags, lifting) inv_matrices_img_nonzero matrix_left_invertible_ker
          matrix_vector_mul_assoc matrix_vector_mul_lid matrix_vector_mult_scaleR zvec_alt)
          (*provable, just need to write it out *)
    then have "rp2rel (Rep_rp2 x) (Rep_rp2 y)" using c_def rp2rel_def
      using rep_P_nz by blast
    then have "Abs_rp2 (Rep_rp2 x) = Abs_rp2 (Rep_rp2 y)"
      by (meson Quotient3_rel_abs Quotient3_rp2)
    then show "x = y"
      by (simp add: ar)
  qed
  have surj: "surj (rp2tom A)"
    unfolding surj_def
  proof (safe)
   fix y :: rp2
   obtain xr where xr_facts: "tom A (xr) = Rep_rp2 y" 
     using invertible surj_def tom_surj by metis
   then have h0: "Abs_rp2 (tom A (xr)) = y" using ar by auto
   then show "\<exists> x . y = (rp2tom A) x"
   by (metis cross_nz cross_refl invertible rep_P_nz rp2tom.abs_eq tom_nonz_det vec.zero xr_facts
       zvec_alt)
qed
  then show "bij (rp2tom A)" using inj surj bij_def by auto
 show "maps_lines_to_lines2 (rp2tom A)"
    using invertible inv_matrices_maps_lines_to_lines2 by auto
qed


definition RP2_auto :: "(rp2 \<Rightarrow> rp2) set" where 
"RP2_auto = {A :: (rp2 \<Rightarrow> rp2) . is_RP2_auto2 A}"


(*== Page 21 ==*)
(*The above theorem justifies the following definition: *)
definition PGL2R :: "(rp2 \<Rightarrow> rp2) set" where
"PGL2R = {rp2tom A | A . det ((A::m33)) \<noteq> 0}"

(* What we have proved above is that 3x3 matrices give rise to a subset of
   the set of all automorphisms of rp2. The next theorem makes this explicit. *)
theorem inv_matrices_subset_auts: "PGL2R \<subseteq> RP2_auto"
  unfolding PGL2R_def RP2_auto_def using inv_matrices_are_auts by auto

(*The next section deals with the proof of Proposition 3.8 *)
(*
definition equiv_maps :: "(v3 \<Rightarrow> v3) \<Rightarrow> (v3 \<Rightarrow> v3) \<Rightarrow> bool"
  where "equiv_maps f g \<longleftrightarrow>
  (well_defined f) \<and> (well_defined g) \<and> (\<forall>x :: v3 . \<exists>t :: real . t \<noteq> 0 \<and> f x = t *s (g x))"
*)
(*
lift_definition RP2_equiv_maps :: "(rp2 \<Rightarrow> rp2) \<Rightarrow> (rp2 \<Rightarrow> rp2) \<Rightarrow> bool" is equiv_maps sorry
*)
(* proof (transfer, clarsimp)
  show "\<And>f g h r . 
         (\<And>x y . rp2rel x y \<Longrightarrow> rp2rel (f x) (g y)) \<Longrightarrow> 
         (\<And>x y . rp2rel x y \<Longrightarrow> rp2rel (h x) (r y)) \<Longrightarrow> equiv_maps f h = equiv_maps g r"
  proof (safe)
    fix f g h r 
    assume "rp2rel x y \<Longrightarrow> rp2rel (f x) (g y)" for x y 
    assume "rp2rel x y \<Longrightarrow> rp2rel (h x) (r y)" for x y
    show "equiv_maps f h \<Longrightarrow> equiv_maps g r"by sorry
    next
      show "\<And>f g h r . 
         (\<And>x y . rp2rel x y \<Longrightarrow> rp2rel (f x) (g y)) \<Longrightarrow> 
         (\<And>x y . rp2rel x y \<Longrightarrow> rp2rel (h x) (r y)) \<Longrightarrow> equiv_maps g r \<Longrightarrow> equiv_maps f h" sorry
qed
*)

definition p1 :: v3 where "p1 = vector[1, 0, 0]"
definition p2 :: v3 where "p2 = vector[0, 1, 0]"
definition p3 :: v3 where "p3 = vector[0, 0, 1]"
definition q :: v3 where "q = vector[1, 1, 1]"

(*Some matrix-vector multiplication lemmas, which might be helpful *)

lemma mat_mult_by_p1: "(A :: m33) *v p1 = (transpose A) $ 1" 
proof -
  have "(A *v vector [1,0,0])$1=A$1$1\<and>(A *v vector[1,0,0])$2 =  A$2$1 \<and> (A *v vector [1,0,0])$3 = A $3$1"
    using explicit_inner_prod
    by (simp add: matrix_vector_mul_component)
  then show ?thesis unfolding p1_def unfolding transpose_def
    by (smt (verit, del_insts) exhaust_3 vec_lambda_unique)
qed

lemma mat_mult_by_p2: "(A :: m33) *v p2 = (transpose A) $ 2" 
proof -
   have "(A *v vector [0,1,0])$1=A$1$2 \<and>(A *v vector[0,1,0])$2 = A$2$2 \<and> (A *v vector [0,1,0])$3 = A $3$2"
    using explicit_inner_prod
    by (simp add: matrix_vector_mul_component)
  then show ?thesis unfolding p2_def unfolding transpose_def
    by (smt (verit, del_insts) exhaust_3 vec_lambda_unique)
qed

lemma mat_mult_by_p3: "(A :: m33) *v p3 = (transpose A) $ 3" 
proof -
  have "(A *v vector [0,0,1])$1=A$1$3 \<and>(A *v vector[0,0,1])$2 = A$2$3 \<and> (A *v vector [0,0,1])$3 = A $3$3"
    using explicit_inner_prod
    by (simp add: matrix_vector_mul_component)
    then show ?thesis unfolding p3_def unfolding transpose_def
    by (smt (verit, del_insts) exhaust_3 vec_lambda_unique)
qed

lemma lin_comb:
  fixes a b c  :: real
  shows "vector[a, b, c] = a *\<^sub>R p1 + b *\<^sub>R p2 + c *\<^sub>R p3"
  unfolding p1_def p2_def p3_def vector_def
  by vector

lemma matrix_mult_unfold:
  fixes x :: v3
  fixes A :: m33
  shows "tom A x = x$1 *\<^sub>R tom A p1 + x$2 *\<^sub>R tom A p2 + x$3 *\<^sub>R tom A p3"
proof -
  have "x = x$1 *\<^sub>R p1 + x$2 *\<^sub>R p2 + x$3 *\<^sub>R p3" using lin_comb
    by (metis matrix_rows(1) vector_1)
  then have "tom A x = tom A (x$1 *\<^sub>R p1 + x$2 *\<^sub>R p2 + x$3 *\<^sub>R p3)" by auto
  then have "tom A x = tom A (x$1 *\<^sub>R p1) + tom A (x$2 *\<^sub>R p2) + tom A (x$3 *\<^sub>R p3)" 
    unfolding tom_def by (simp add: vec.add)
  then show ?thesis
    unfolding tom_def 
  by (simp add: matrix_vector_mult_scaleR)
qed

lemma comb: "q = p1 +  p2 + p3" 
  unfolding q_def p1_def p2_def p3_def
  using lin_comb by vector

lemma matrices_equal_on_basis:
  fixes A B :: m33
  and u :: real
  assumes "tom A p1 = u *\<^sub>R tom B p1"
  and "tom A p2 = u *\<^sub>R tom B p2"
  and "tom A p3 = u *\<^sub>R tom B p3"
  shows "\<forall> x :: v3. tom A x = u *\<^sub>R tom B x"
proof (rule allI)
  fix x :: v3
  let ?a = "x $ 1"
  let ?b = "x $ 2" 
  let ?c = "x $ 3"
  have "x = vector[?a, ?b, ?c]" unfolding vector_def vec_eq_iff using exhaust_3 by auto
  then have x_eq: "x = ?a *\<^sub>R p1 + ?b *\<^sub>R p2 + ?c *\<^sub>R p3" using lin_comb by auto
  then have eq1: "u *\<^sub>R tom B x = u *\<^sub>R tom B (?a *\<^sub>R p1 + ?b *\<^sub>R p2 + ?c *\<^sub>R p3)" by auto
  have eq2: "u *\<^sub>R tom B ((?a *\<^sub>R p1) + (?b *\<^sub>R p2) + (?c *\<^sub>R p3)) = 
               u *\<^sub>R tom B (?a *\<^sub>R p1) + u *\<^sub>R tom B (?b *\<^sub>R p2) + u *\<^sub>R  tom B (?c *\<^sub>R p3)" 
    using tom_def matrix_vector_right_distrib
  by (metis (no_types, lifting) scaleR_right_distrib)
  have eq3: "u *\<^sub>R tom B (?a *\<^sub>R p1) + u *\<^sub>R tom B (?b *\<^sub>R p2) + u *\<^sub>R  tom B (?c *\<^sub>R p3) =
            ?a *\<^sub>R (u *\<^sub>R tom B p1) + ?b *\<^sub>R (u *\<^sub>R tom B p2) + ?c *\<^sub>R (u *\<^sub>R tom B p3)"
    using tom_def
  by (metis (no_types, lifting) eq2 matrix_mult_unfold scaleR_left_commute
      scaleR_right_distrib x_eq)
  have eq4: "?a *\<^sub>R (u *\<^sub>R tom B p1) + ?b *\<^sub>R (u *\<^sub>R tom B p2) + ?c *\<^sub>R (u *\<^sub>R tom B p3) =
            ?a *\<^sub>R tom A p1 + ?b *\<^sub>R tom A p2 + ?c *\<^sub>R tom A p3" using assms by auto
  have eq5: "?a *\<^sub>R tom A p1 + ?b *\<^sub>R tom A p2 + ?c *\<^sub>R tom A p3 = 
             tom A (?a *\<^sub>R p1 + ?b *\<^sub>R p2 + ?c *\<^sub>R p3)" using tom_def 
  by (metis matrix_mult_unfold x_eq) 
  have eq6: "tom A (?a *\<^sub>R p1 + ?b *\<^sub>R p2 + ?c *\<^sub>R p3) = tom A x" using x_eq by auto
  show "tom A x = u *\<^sub>R tom B x" using eq1 eq2 eq3 eq4 eq5 eq6 by auto
qed

lemma equiv_on_basis_imp_equiv:
  (*The key part of the next theorem is separated out here, since we also need it for the uniqueness
    part of Theorem 3.9 *)
  fixes A :: m33
  fixes B :: m33
  assumes invertible_A: "det A \<noteq> 0"
  and invertible_B: "det B \<noteq> 0"
  and "rp2rel (tom A p1) (tom B p1)"
  and "rp2rel (tom A p2) (tom B p2)"
  and "rp2rel (tom A p3) (tom B p3)"
  and "rp2rel (tom A q) (tom B q)"
  shows "\<forall>x :: v3 . x \<noteq> 0 \<longrightarrow> rp2rel (tom A x) (tom B x)"
proof -
  obtain c1 :: real where hc1: "c1 \<noteq> 0 \<and> tom A p1 = c1  *\<^sub>R (tom B p1)" 
    using assms(3) p1_def unfolding rp2rel_def by blast
  obtain c2 :: real where hc2: "c2 \<noteq> 0 \<and> tom A p2 = c2 *\<^sub>R (tom B p2)" 
    using assms(4) p2_def unfolding rp2rel_def by blast
  obtain c3 :: real where hc3: "c3 \<noteq> 0 \<and> tom A p3 = c3 *\<^sub>R (tom B p3)" 
    using assms(5) p3_def unfolding rp2rel_def by blast
  obtain u:: real where hu: "u \<noteq> 0 \<and> tom A q  = u *\<^sub>R tom B q" 
    using assms(6) q_def unfolding rp2rel_def by blast
  let ?r = "vector[u - c1, u - c2, u - c3]"
  have comb2: "(u - c1) *\<^sub>R p1 + (u - c2) *\<^sub>R  p2 + (u - c3) *\<^sub>R p3 = ?r" 
    unfolding p1_def p2_def p3_def vector_def by vector
  have eq1: "u *\<^sub>R tom B p1 + u *\<^sub>R tom B p2 + u *\<^sub>R tom B p3 =
             u *\<^sub>R (tom B p1 + tom  B p2 + tom B p3)"
  by (simp add: pth_6)
  have eq2: "u *\<^sub>R (tom B p1 + tom  B p2 + tom B p3) = u *\<^sub>R (tom B (p1 + p2 + p3))"
    by (simp add: tom_def vec.add)
  have eq3: "u *\<^sub>R (tom B (p1 + p2 + p3)) = u *\<^sub>R (tom B q)"
    using comb by auto
  have eq4: "u *\<^sub>R (tom B q) = tom A q" using hu by auto
  have eq5: "tom A q = tom A p1 + tom A p2 + tom A p3" using comb
    by (metis matrix_vector_right_distrib
        tom_def)
  have eq6: "tom A p1 + tom A p2 + tom A p3 =
             c1 *\<^sub>R tom B p1 + c2 *\<^sub>R tom B p2 + c3 *\<^sub>R tom B p3" using hc1 hc2 hc3 by auto
  then have eq7: "u *\<^sub>R tom B p1 + u *\<^sub>R tom B p2 + u *\<^sub>R tom B p3 = 
                 c1 *\<^sub>R tom B p1 + c2 *\<^sub>R tom B p2 + c3 *\<^sub>R tom B p3"
    using eq1 eq2 eq3 eq4 eq5 eq6 by auto
  then have rw1: "u *\<^sub>R tom B p1 - c1 *\<^sub>R tom B p1 + u *\<^sub>R tom B p2 - c2 *\<^sub>R tom B p2 + u *\<^sub>R tom B p3 
             - c3 *\<^sub>R tom B p3 = 0" 
  by (simp add: add.commute add_diff_eq)
  then have "(u - c1) *\<^sub>R tom B p1 + (u - c2) *\<^sub>R tom B p2 + (u - c3) *\<^sub>R tom B p3 = 0"
  by (metis (no_types, lifting)
     eq7
      add_diff_add eq_iff_diff_eq_0 scaleR_left.diff)
  then have "tom B ((u - c1) *\<^sub>R p1) + tom B ((u - c2) *\<^sub>R p2) + tom B ((u - c3) *\<^sub>R p3) = 0"
    using tom_def 
   by (metis (no_types, lifting) matrix_vector_mult_scaleR)
  then have "tom B ((u - c1) *\<^sub>R p1 + (u - c2)*\<^sub>R  p2 + (u - c3) *\<^sub>R p3) = 0"
    using tom_def 
  by (metis (no_types, lifting) matrix_vector_right_distrib)
  then have "tom B ?r = 0"
    using comb2 assms(2) by auto
  then have "?r = (0 :: (real, 3) vec)"
    using inv_matrix_inj[of B ?r] invertible_B by simp
  then have "u - c1 = 0 \<and> u - c2 = 0 \<and> u - c3 = 0"
  by (simp add: vect_zero_eqv)
  then have all_equal: "u = c1 \<and> u = c2 \<and> u = c3" by auto
  have h1: "tom A p1 = u *\<^sub>R tom B p1" using all_equal hc1 by auto
  have h2: "tom A p2 = u *\<^sub>R tom B p2" using all_equal hc2 by auto
  have h3: "tom A p3 = u *\<^sub>R tom B p3" using all_equal hc3 by auto
  have exists: "\<forall>x. tom A x = u *\<^sub>R tom B x" 
    using h1 h2 h3 matrices_equal_on_basis by blast
  have non_zero: "u \<noteq> 0" using hu by auto
  show ?thesis using exists non_zero assms(1) assms(2) inv_matrix_inj zvec_alt
    unfolding rp2rel_def
  by metis
qed 



lemma matrix_agreeing_with_I_on_basis_is_scalar_mult_of_I: 
  fixes A :: m33
  assumes invertible_A: "det A \<noteq> 0"
  assumes "rp2rel (A *v p1) p1"
  assumes "rp2rel (A *v p2) p2"
  assumes "rp2rel (A *v p3) p3"
  assumes "rp2rel (A *v q) q"
  shows "(\<exists>c :: real . 
        A  = c *k I33)"
  sorry

lemma matrices_agreeing_on_basis_are_scalar_mults: 
  fixes A B :: m33
  assumes invertible_A: "det A \<noteq> 0"
  assumes invertible_B: "det A \<noteq> 0"
  assumes "rp2rel (A *v p1) (B *v p1)"
  assumes "rp2rel (A *v p2) (B *v p2)"
  assumes "rp2rel (A *v p3) (B *v p3)"
  assumes "rp2rel (A *v q) (B *v q)"
  shows "\<exists>c :: real .  A  = c *k B"
  sorry (* should follow instantly from previous lemma, applied to AB^{-1} *)


theorem equal_matrix_transforms_implies_matrix_scalar_multiple: (* theorem 3.8 *)
  fixes A B:: m33
  assumes invertible: "det A \<noteq> 0 \<and> det B \<noteq> 0"
  assumes equal_maps: "rp2tom A = rp2tom B"
  shows "\<exists>c::real . c \<noteq> 0 \<and> A = c *k B" 
  
 
  sorry


(* If the transformations for matrices A and B are equal up to a constant factor c,
  then they are "equiv_maps", i.e., they represent the same maps when considered as 
  rp2 \<Rightarrow> rp2 maps: *)
(* This is proposition 3.8 *)
lemma inv_matrices_equiv_iff:
  fixes A B :: m33
  assumes invertible_A: "det A \<noteq> 0"
  and invertible_B: "det B \<noteq> 0"
shows "(\<exists>c :: real .  A  = c *k B) \<longleftrightarrow> ((rp2tom A) = (rp2tom B))"
  sorry

(* WHAT REMAINS 
** ## State that A B C are coplanar in v3 iff det([A,B,C]) = 0
** ## State that (rp2abs A) (rp2abs B) (rp2abs C) are collinear in rp3, iff det([A,B,C]) = 0 (i.e. them 3.10)
*)


(* =========prior stuff ===========*)
(*
proof (rule impI; safe)
  fix c :: real
  assume c_scales: "\<forall>x . (tom A) x = c *s (tom B) x"
  have c_nonzero: "c \<noteq> 0"
  proof 
    assume "c = 0"
    then have "c *s (tom B) x = 0" for x by simp
    then have "tom A x = 0" for x using c_scales by auto
    then have "A = 0" using tom_def by (simp add: matrix_eq)
    then have "det A = 0" using det_0 by auto
    then show "False" using invertible_A by auto
  qed
  show "equiv_maps (tom A) (tom B)"
    unfolding equiv_maps_def
  proof (safe)
    show "well_defined (tom A)"
      unfolding well_defined_def
      using matrices_respect_scaling inv_matrices_image_non_zero invertible_A 
      by auto
    show "well_defined (tom B)"
      unfolding well_defined_def
      using matrices_respect_scaling inv_matrices_image_non_zero invertible_B 
      by auto
    fix x :: v3
    show "\<exists>l. l \<noteq> 0 \<and> tom A x = l *s tom B x" 
      using c_nonzero c_scales by auto
  qed 
qed
*)

(*Some matrix-vector multiplication lemmas, which might be helpful *)

lemma mat_mult_by_p1_s: "(A :: m33) *v p1 = (transpose A) $ 1" 
proof -
  have "(A *v vector [1,0,0])$1=A$1$1\<and>(A *v vector[1,0,0])$2 =  A$2$1 \<and> (A *v vector [1,0,0])$3 = A $3$1"
    using explicit_inner_prod
    by (simp add: matrix_vector_mul_component)
  then show ?thesis unfolding p1_def unfolding transpose_def
    by (smt (verit, del_insts) exhaust_3 vec_lambda_unique)
qed

lemma mat_mult_by_p2_s: "(A :: m33) *v p2 = (transpose A) $ 2" 
proof -
   have "(A *v vector [0,1,0])$1=A$1$2 \<and>(A *v vector[0,1,0])$2 = A$2$2 \<and> (A *v vector [0,1,0])$3 = A $3$2"
    using explicit_inner_prod
    by (simp add: matrix_vector_mul_component)
  then show ?thesis unfolding p2_def unfolding transpose_def
    by (smt (verit, del_insts) exhaust_3 vec_lambda_unique)
qed

lemma mat_mult_by_p3_s: "(A :: m33) *v p3 = (transpose A) $ 3" 
proof -
  have "(A *v vector [0,0,1])$1=A$1$3 \<and>(A *v vector[0,0,1])$2 = A$2$3 \<and> (A *v vector [0,0,1])$3 = A $3$3"
    using explicit_inner_prod
    by (simp add: matrix_vector_mul_component)
    then show ?thesis unfolding p3_def unfolding transpose_def
    by (smt (verit, del_insts) exhaust_3 vec_lambda_unique)
qed


(*A general note: when proving statements involving vector arithmetic,
  ALWAYS unfold every definition first; then often writing "by vector"
  completes the goal. *)

lemma lin_comb_s:
  fixes a b c  :: real
  shows "vector[a, b, c] = a *s p1 + b *s p2 + c *s p3"
  unfolding p1_def p2_def p3_def vector_def
  by vector

lemma matrix_mult_unfold_s:
  fixes x :: v3
  fixes A :: m33
  shows "tom A x = x$1 *s tom A p1 + x$2 *s tom A p2 + x$3 *s tom A p3"
proof -
  have "x = x$1 *s p1 + x$2 *s p2 + x$3 *s p3" using lin_comb_s
    by (metis matrix_rows(1) vector_1)
  then have "tom A x = tom A (x$1 *s p1 + x$2 *s p2 + x$3 *s p3)" by auto
  then have "tom A x = tom A (x$1 *s p1) + tom A (x$2 *s p2) + tom A (x$3 *s p3)" 
    unfolding tom_def by (simp add: vec.add)
  then show ?thesis
    unfolding tom_def by (simp add: vec.scale)
qed

lemma comb_s: "q = p1 +  p2 + p3" 
  unfolding q_def p1_def p2_def p3_def
  using lin_comb by vector


lemma inv_matrices_equiv_bwd:
  fixes A :: m33
  fixes B :: m33
  assumes invertible_A: "det A \<noteq> 0"
  and invertible_B: "det B \<noteq> 0"
  shows "equiv_maps (tom A) (tom B) \<longrightarrow> (\<exists>c :: real . \<forall>x :: v3 . 
        (tom A) x = c *s (tom B) x \<and> c \<noteq> 0)"
  sorry
  (* unfolding equiv_maps_def *)
(* proof (safe)
  assume wd_A: "well_defined (tom A)"
  assume wd_B: "well_defined (tom B)"
  assume equivs: "\<forall>x. \<exists>l. l \<noteq> 0 \<and> tom A x = l *s tom B x"
  obtain c1 :: real where hc1: "c1 \<noteq> 0 \<and> tom A p1 = c1 *s tom B p1" using equivs by auto
  obtain c2 :: real where hc2: "c2 \<noteq> 0 \<and> tom A p2 = c2 *s tom B p2" using equivs by auto
  obtain c3 :: real where hc3: "c3 \<noteq> 0 \<and> tom A p3 = c3 *s tom B p3" using equivs by auto
  obtain u:: real where hu: "u \<noteq> 0 \<and> tom A q  = u *s tom B q" using equivs by auto
  show "\<exists>c. \<forall>x. tom A x = c *s tom B x \<and> c \<noteq> 0" 
    using hc1 hc2 hc3 hu equiv_on_basis_imp_equiv invertible_A invertible_B by auto
qed 
*)

theorem inv_matrices_equiv_iff:
  fixes A :: m33
  fixes B :: m33
  assumes invertible_A: "det A \<noteq> 0"
  and invertible_B: "det B \<noteq> 0"
  shows "equiv_maps (tom A) (tom B) \<longleftrightarrow> (\<exists>c :: real . \<forall>x :: v3 . 
        (tom A) x = c *s (tom B) x \<and> c \<noteq> 0)"
  sorry
(*
proof
  show "\<exists>c. \<forall>x. tom A x = c *s tom B x \<and> c \<noteq> 0 \<Longrightarrow> equiv_maps (tom A) (tom B)"
    using inv_matrices_equiv_fwd invertible_A invertible_B by auto
  show " equiv_maps (tom A) (tom B) \<Longrightarrow> \<exists>c. \<forall>x. tom A x = c *s tom B x \<and> c \<noteq> 0"
    using inv_matrices_equiv_bwd invertible_A invertible_B by auto
qed 
*)
end       





