theory "Chapter1-2"
  imports Complex_Main "Chapter1-1" "HOL-Analysis.Cross3"

begin
(* Team RP2-quotient:  Jiayi, Luke, George, Nick, Oliver *)
text\<open> Start out by defining RP2 as a quotient of R3 - {origin}. I'll need various 
linear-algebra-like operations; smult is "scalar multiplication", dot and cross
are dot product and cross product. vplus is vector addition.\<close>


subsection \<open>Defining a quotient space for RP2\<close>

(* We've defined RP2, but we still need to show it's a projective plane, i.e., demonstrate 
axioms 1 - 4. Then we can move on to isomorphism with the completion of the affine plane. *)

(* We're going to need cross and dot-products *)
unbundle cross3_syntax

type_synonym v3 = "real^3"
definition punctured_r_3 where
"punctured_r_3 = (UNIV::(v3 set)) - {0::v3}"

definition zvec where "zvec = vector[0::real, 0, 0]"

lemma [simp]:
  shows "zvec = vector[0::real, 0, 0]" using zvec_def by auto

definition map_vec where
"map_vec f g v = vec_lambda (map_fun g f (vec_nth v))"
functor map_vec
  unfolding map_vec_def
  using eq_id_iff by fastforce+

definition projrel :: "(v3) \<Rightarrow> (v3) \<Rightarrow> bool"
  where "projrel x y \<longleftrightarrow> (x \<noteq> zvec) \<and> (y \<noteq> zvec) \<and> (\<exists>t::real. t \<noteq> 0 \<and> x = t *\<^sub>R y)" 

text\<open>\spike Current definition of projective relation 
is that there's nonzero constant c such that u = cv. The alternative definition 
is that the cross product is zero.  Let's start
with the big theorem that these two things are equivalent\<close>
lemma alt_projrel:
  assumes "u \<noteq> zvec"
  assumes "v \<noteq> zvec"
  shows "(projrel u v) \<longleftrightarrow> (u \<noteq> zvec) \<and> (v \<noteq> zvec) \<and> (u \<times> v) = zvec"
proof 
  assume ah1: "projrel u v"
  then obtain t where "t \<noteq> 0 \<and> u =  t *\<^sub>R  v" using projrel_def assms by blast
  then show "(u \<noteq> zvec) \<and> (v \<noteq> zvec) \<and> (u \<times> v) = zvec" 
    using projrel_def cross_refl assms(1) cross3_def cross_zero_right by auto 
  next
    assume ah2: "(u \<noteq> zvec) \<and> (v \<noteq> zvec) \<and> (u \<times> v) = zvec"
    then have "collinear {0, u, v}" 
      using cross_eq_0 [of u v] zvec_def cross3_simps(1) cross_zero_right by force
    then obtain w where col_fact: "\<forall>x\<in>{0, u, v}. \<forall>y\<in>{0, u, v}. \<exists>c. x - y = c *\<^sub>R w" 
      using collinear_def by blast
    then obtain r where rf: "u - 0 = r *\<^sub>R w" by blast
    obtain s where sf: "v - 0 = s *\<^sub>R w" using col_fact by blast
    have uw: "u = r *\<^sub>R w" using rf by simp
    have vw: "v = s *\<^sub>R w" using sf by simp
    have sr: "s \<noteq> 0 \<and> r \<noteq> 0" using uw vw assms ah2 cross3_def by fastforce
    then have "u = (r/s) *\<^sub>R v" using uw vw by simp
    then have "(\<exists> t::real . (t \<noteq>0) \<and> u =  t *\<^sub>R  v)" using sr  divide_eq_0_iff by blast
    then show "projrel u v" using projrel_def ah2 assms by blast
  qed
  
text \<open>\done\<close>

lemma vt:
  shows "(vector[1,0,0]::real^3) \<noteq> zvec" 
  using zvec_def vector_3(1) zero_neq_one by metis

lemma exists_projrel_refl: "\<exists>x. projrel x x" 
proof -
  have "projrel (vector [1,0,0]::real^3) (vector [1,0,0]::v3)" using projrel_def vt by auto
  then show ?thesis by blast
qed

lemma symp_projrel: "symp projrel"
  using divideR_right scaleR_zero_left cross_mult_right projrel_def 
  unfolding symp_def projrel_def by metis

text \<open>\hadi\<close>
lemma transp_projrel: "transp projrel"
proof (rule transpI)
  fix x y z
  assume 1: "projrel x y"
  assume 2: "projrel y z"
  show "projrel x z" using 1 2 alt_projrel cross_mult_left 
    cross_zero_right projrel_def by (metis (lifting) ext)
qed
text \<open>\done\<close>

lemma part_equivp_projrel: "part_equivp projrel"
  by (rule part_equivpI [OF exists_projrel_refl symp_projrel transp_projrel])

text \<open>\nick\jackson\<close>
lemma smult_projrel: 
  fixes x y c
  assumes x_def: "x \<noteq> zvec"
  assumes y_def: "y \<noteq> zvec"
  assumes c_def: "c \<noteq> 0"
  assumes smult: "x = c *\<^sub>R y"
  shows "projrel x y"
  using c_def projrel_def smult x_def y_def by blast
text \<open>\done\<close>

quotient_type rp2 = "v3" / partial: "projrel"
  morphisms Rep_Proj Abs_Proj
  using part_equivp_projrel .

find_theorems name: "rp2"
find_theorems name: "Quotient3_rp2"

lemma Domainp_cr_proj [transfer_domain_rule]: "Domainp cr_rp2 = (\<lambda>x .((x \<noteq> zvec) \<and> projrel x x))"
proof -
  have "projrel x x \<longrightarrow> x  \<noteq> zvec" for x using projrel_def by blast
  then show ?thesis using projrel_def rp2.domain by auto 
qed

lemma rep_P_nz:
  fixes P
  assumes a1: "P \<in> rp2_Points" 
  shows "Rep_Proj P \<noteq> zvec" 
  using projrel_def Quotient_rel_rep Quotient_rp2 by metis

(* a remaining theorem from the "warmup" section, one that needs "projrel", and
needs rewriting using Cross3 rather than our (now-delete) version of 'cross' *)

text \<open>\hadi\<close>
lemma cross_nz:
  assumes "u \<noteq> zvec"
  assumes "v \<noteq> zvec"
  assumes "\<not> projrel u v"
  defines s_def: "s \<equiv> u \<times> v"
  shows "s \<noteq> zvec" 
  using assms cross3_def projrel_def s_def alt_projrel by metis
text \<open>\done\<close>

(* We've defined RP2, but we still need to show it's a projective plane, i.e., demonstrate 
axioms 1 - 4. Then we can move on to isomorphism with the completion of the affine plane. *)

(* RP2 is a projective plane *)

definition rp2_Points where
"rp2_Points = (UNIV::rp2 set)" 

definition rp2_Lines where
"rp2_Lines = (UNIV::rp2 set)"

definition rp2_incid_rep where
"rp2_incid_rep P k = (P \<bullet> k = 0)"

text \<open>\hadi\<close>
lift_definition rp2_incid::"rp2 \<Rightarrow> rp2 \<Rightarrow> bool"
is "\<lambda>P k. (P \<bullet> k = 0)"
proof -
  fix P1 P2 k1 k2
  assume a1: "projrel P1 P2"
  assume a2: "projrel k1 k2"
  obtain s where P12: "s \<noteq> 0 \<and> P1 = s *\<^sub>R P2" 
    using a1 alt_projrel [of P1] projrel_def [of P1] cross3_def by fastforce
  obtain t where k12: "t \<noteq> 0 \<and> k1 = t *\<^sub>R k2"
    using a2 alt_projrel [of k1] projrel_def [of k1] cross3_def by fastforce
  have ts: "t \<noteq> 0 \<and> s \<noteq> 0" using P12 k12 by auto
  have "(P1 \<bullet> k1 = 0) = (P1 \<bullet> (t *\<^sub>R k2) = 0)" using k12 by auto 
  also have "... = ( P2 \<bullet>  k2 = 0)" using P12 ts by auto
  finally show "(P1 \<bullet> k1 = 0) = (P2 \<bullet> k2 = 0)" .
qed

lemma incid_commute:
  shows "rp2_incid A B \<longleftrightarrow> rp2_incid B A"
  by (simp add: inner_commute rp2_incid.rep_eq)
text \<open>\done\<close>
(*
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k . k \<in> Lines \<and> P \<lhd> k  \<and> Q \<lhd>  k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = { P . (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
*)

definition join :: "real^3 \<Rightarrow> real^3 \<Rightarrow> real^3"
  where "join P Q = (if P \<times> Q = zvec then vector[0,0,1] else P \<times> Q)"

text \<open>\hadi\<close>
lift_definition Join :: "rp2 \<Rightarrow> rp2 \<Rightarrow> rp2" is "\<lambda>P Q. join P Q" 
proof -
  fix v1 v2 v3 v4
  assume a1: "projrel v1 v2"
  assume a2: "projrel v3 v4"
  show "projrel (join v1 v3) (join v2 v4)" 
  proof -
    have nz: "(join v1 v3) \<noteq> zvec \<and> (join v2 v4) \<noteq> zvec" 
      using join_def zvec_def vector_3(3) rel_simps(93) by metis
    obtain t1 t2 where t1t2def: "t1 \<noteq> 0 \<and> v1 = t1 *\<^sub>R v2 
      \<and> t2 \<noteq> 0 \<and> v3 = t2 *\<^sub>R v4" using a1 a2 projrel_def by auto
    consider
    (allnz) "v1 \<times> v3 \<noteq> zvec \<and> v2 \<times> v4 \<noteq> zvec"
    | (onez) "(v1 \<times> v3 = zvec \<and> v2 \<times> v4 \<noteq> zvec) \<or> (v1 \<times> v3 \<noteq> zvec \<and> v2 \<times> v4 = zvec)"
    | (allz) "v1 \<times> v3 = zvec \<and> v2 \<times> v4 = zvec" by blast
    then show ?thesis 
    proof (cases)
      case allnz
      then show ?thesis using t1t2def join_def alt_projrel projrel_def cross_refl
        cross_mult_left cross_mult_right scaleR_zero_right by (metis (no_types))
    next
      case onez
      then have "(join v1 v3) \<times> (join v2 v4) = zvec" using a1 a2 join_def
        alt_projrel projrel_def part_equivp_def part_equivp_projrel by metis
      then show ?thesis using nz alt_projrel by auto
    next
      case allz
      then show ?thesis using nz join_def projrel_def by auto
    qed
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma join_commute:
  fixes P Q
  assumes a1: "P \<in> rp2_Points" 
  assumes a2: "Q \<in> rp2_Points"
  assumes a3: "P \<noteq> Q"
  shows "Join P Q = Join Q P"
proof (transfer)
  fix Ps Qs
  assume b1: "Ps \<noteq> zvec \<and> projrel Ps Ps"
  assume b2: "Qs \<noteq> zvec \<and> projrel Qs Qs"
  show "projrel (join Ps Qs) (join Qs Ps)"
  proof -
    have nz: "(join Ps Qs) \<noteq> zvec \<and> (join Qs Ps) \<noteq> zvec" 
      using join_def zvec_def vector_3(3) rel_simps(93) by metis
    have "\<exists>(t::real). t \<noteq> 0 \<and> (join Ps Qs) = t *\<^sub>R (join Qs Ps)"
      using b2 alt_projrel cross_skew join_def pth_1 scaleR_left.minus 
      scaleR_zero_right zero_neq_one by (metis (no_types))
    then show ?thesis using nz projrel_def by auto
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma rp2_P1a:
  fixes P Q
  assumes a1: "P \<in> rp2_Points" 
  assumes a2: "Q \<in> rp2_Points"
  shows "(\<exists>k. rp2_incid P k \<and> rp2_incid Q k)"
proof (transfer)
  fix P Q 
  show "P \<noteq> zvec \<and> projrel P P \<Longrightarrow> Q \<noteq> zvec \<and> projrel Q Q 
    \<Longrightarrow> \<exists>k \<in> {x. x \<noteq> zvec \<and> projrel x x}. (P \<bullet> k = 0) \<and> (Q \<bullet> k = 0)"
  proof -
    assume pf: "P \<noteq> zvec \<and> projrel P P"
    assume qf: "Q \<noteq> zvec \<and> projrel Q Q"
    show "\<exists>k \<in> {x. x \<noteq> zvec \<and> projrel x x}. (P \<bullet> k = 0) \<and> (Q \<bullet> k = 0)"
    proof (cases "projrel P Q")
      case pqrel: True
      obtain u where udef: "P \<times> u \<noteq> 0" 
        using cross_basis_nonzero [of P] alt_projrel pf by metis
      then have "P \<bullet> (P \<times> u) = 0 \<and> Q \<bullet> (P \<times> u) = 0"
        using pqrel cross_mult_left projrel_def dot_cross_self(1) by auto
      then show ?thesis using udef alt_projrel pf by auto
    next
      case False
      then show ?thesis using alt_projrel dot_cross_self(1,2) pf qf by auto
    qed
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma unique_cross:
  fixes a b n k
  assumes "a \<times> b \<noteq> 0"
  assumes "k \<bullet> a = 0" and "k \<bullet> b = 0" 
  shows "\<exists>s. k = s *\<^sub>R (a \<times> b)"
  using assms Lagrange zvec_def projrel_def cross3_def cross_nz scaleR_zero_left
    cancel_comm_monoid_add_class.diff_cancel zero_index by (metis (no_types))
text \<open>\done\<close>

(* TO DO: To show uniqueness of the join, we have to show (for P,Q nonzero and P and Q not proj_rel,
that if h is orthog to P and Q, then h is a nonzero multiple of the cross product, i.e., the lemma
above *)
lemma rp2_P1b_helper:
  fixes P Q k n
  assumes P_def: "P \<noteq> zvec" 
  assumes Q_def: "Q \<noteq> zvec"
  assumes PQ_nprojrel: "\<not> projrel P Q"
  assumes n_def: "n = P \<times> Q"
  assumes k_def: "k \<noteq> zvec"
  assumes k_facts: "(P \<bullet> k = 0)  \<and> (Q \<bullet> k = 0)" 
  shows "\<exists>c. (c \<noteq> 0) \<and> k = c *\<^sub>R n"
  using assms alt_projrel cross_refl exists_projrel_refl inner_commute 
    projrel_def scaleR_zero_left unique_cross by metis

text \<open>\nick\jackson\<close>
lemma rp2_P1b:
  fixes P Q k n
  assumes a1: "P \<in> rp2_Points" 
  assumes a2: "Q \<in> rp2_Points"
  assumes a3: "k \<in> rp2_Lines"
  assumes a4: "n \<in> rp2_Lines"
  assumes a5: "P \<noteq> Q"
  assumes k_facts: "rp2_incid P k  \<and> rp2_incid Q k" 
  assumes n_facts: "rp2_incid P n  \<and> rp2_incid Q n" 
  shows "k = n"
proof -
  obtain Pvec where hPrep: "Pvec = Rep_Proj P" and hPpr3: "Pvec \<in> punctured_r_3" and hPnz: "Pvec \<noteq> 0" 
    using cross3_def cross_zero_left punctured_r_3_def rep_P_nz by fastforce
  obtain Qvec where hQrep: "Qvec = Rep_Proj Q" and hQpr3: "Qvec \<in> punctured_r_3" and hQnz: "Qvec \<noteq> 0" 
    using cross3_def cross_zero_left punctured_r_3_def rep_P_nz by fastforce
  have h1: "\<not> projrel Pvec Qvec" 
    using hPrep hQrep Quotient_rel_rep Quotient_rp2 a5 by metis
  let ?crossPQ = "Pvec \<times> Qvec"
  obtain kvec where hkrep: "kvec = Rep_Proj k" and hkpr3: "kvec \<noteq> zvec" and hknz: "kvec \<noteq> 0" 
    using cross3_def cross_zero_left  rep_P_nz by fastforce
  obtain nvec where hnrep: "nvec = Rep_Proj n" and hnpr3: "nvec \<noteq> zvec" and hknz: "nvec \<noteq> 0" 
    using cross3_def cross_zero_left  rep_P_nz by fastforce
  have h2: "(Pvec \<bullet> kvec = 0) \<and> (Qvec \<bullet> kvec = 0)"
    using hPrep hQrep hkrep k_facts rp2_incid.rep_eq by auto
  have h3: "(Pvec \<bullet> nvec = 0) \<and> (Qvec \<bullet> nvec = 0)"
    using hPrep hQrep hnrep n_facts rp2_incid.rep_eq by auto
  obtain c_k where hck: "(c_k \<noteq> 0) \<and> kvec = c_k *\<^sub>R ?crossPQ"
    using a1 a2 h1 h2 hPrep hQrep hkrep hPpr3 hQpr3 hkpr3  rep_P_nz rp2_P1b_helper[of Pvec Qvec ?crossPQ kvec] by auto
  obtain c_n where hcn: "(c_n \<noteq> 0) \<and> nvec = c_n *\<^sub>R ?crossPQ"
    using a1 a2 a3 h1 h3 hPrep hQrep hkrep hPpr3 hQpr3 hnpr3 rep_P_nz rp2_P1b_helper[of Pvec Qvec ?crossPQ nvec] by auto
  have h4: "((c_k/c_n) \<noteq> 0) \<and> kvec = (c_k/c_n) *\<^sub>R nvec" using hck hcn by auto
  show ?thesis using h4 Quotient3_rel_rep Quotient3_rp2 hkrep hnrep projrel_def hkpr3 hnpr3 smult_projrel by metis
qed
text \<open>\done\<close>

text \<open>\nick\<close>
lemma rp2_P2:
  fixes m k 
  assumes a1: "m \<in> rp2_Lines" 
  assumes a2: "k \<in> rp2_Lines"
  assumes a3: "m \<noteq> k"
  shows "(\<exists>P . P \<in> rp2_Points \<and> rp2_incid P m \<and> rp2_incid P k)"
  using rp2_P1a [of m k] incid_commute rp2_Points_def by auto

lemma rp2_P3:
  shows "\<exists>P Q R. P \<in> rp2_Points \<and> Q \<in> rp2_Points \<and> R \<in> rp2_Points \<and> P \<noteq> Q \<and> P \<noteq> R 
    \<and> Q \<noteq> R \<and> \<not> (\<exists>k \<in> rp2_Lines. rp2_incid P k \<and> rp2_incid Q k \<and> rp2_incid R k)"
  sorry
  text \<open>\George\<close>

text \<open>\Jiayi\Luke\<close>
lemma vector_3_eq_iff:
  fixes a1 a2 a3 b1 b2 b3 :: real
  shows "(vector[a1, a2, a3] :: real^3) = (vector[b1, b2, b3] :: real^3) \<longleftrightarrow> a1 = b1 \<and> a2 = b2 \<and> a3 = b3"
  using vector_3 exhaust_3 by (metis (no_types, opaque_lifting))

lemma projrel_imp_smult:
  assumes "projrel u v"
  shows "\<exists>c::real. c \<noteq> 0 \<and> u = c *\<^sub>R v"
  using assms unfolding projrel_def by blast

lemma projrel_self:
  fixes x
  assumes "x \<noteq> (vector[0,0,0]:: real^3)"
  shows "projrel x x"
proof - 
  show ?thesis using assms projrel_def by force
qed

lemma ar: "Abs_Proj (Rep_Proj x) = x"
  by (meson Quotient_abs_rep Quotient_rp2)

lemma ra: 
  fixes x
  assumes "(x \<noteq> (vector[0,0,0]:: real^3))"
  shows "projrel (Rep_Proj (Abs_Proj x)) x" using projrel_self
  by (simp add: Quotient3_rp2 assms rep_abs_rsp_left) 

lemma equal_implies_projrel:
  fixes P Q
  assumes "P = Q"
  assumes "P \<in> rp2_Points \<and> Q \<in> rp2_Points"
  shows "projrel (Rep_Proj P) (Rep_Proj Q)"
proof -
  show ?thesis using assms by (metis Quotient_alt_def3 Quotient_rp2)
qed

lemma equal_implies_projrel_ra:
  fixes P Q
  fixes x y
  assumes "P = Q"
  assumes "P \<in> rp2_Points \<and> Q \<in> rp2_Points"
  assumes "P = Abs_Proj x \<and> Q = Abs_Proj y"
  shows "projrel (Rep_Proj (Abs_Proj x)) (Rep_Proj (Abs_Proj y))"
proof - 
  show ?thesis using assms equal_implies_projrel ra by auto
qed

lemma dot_product_zero_implies_incid:
  fixes P
  fixes k
  fixes x kvec
  assumes "P \<in> rp2_Points"
  assumes "k \<in> rp2_Lines"
  assumes "x \<noteq> zvec \<and> kvec \<noteq> zvec"
  assumes "P = Abs_Proj x"
  assumes "k = Abs_Proj kvec"
  assumes "x \<bullet> kvec = 0"
  shows "rp2_incid P k"
proof (rule ccontr)
  assume not_incid: "\<not>rp2_incid P k"
  have "projrel (Rep_Proj P) x" using ra smult_projrel assms  by fastforce
  then have temp1: "\<exists>e. e *\<^sub>R x = (Rep_Proj P)" using projrel_def by auto
  then obtain e where edef: "e *\<^sub>R x = (Rep_Proj P)" by auto

  have "(Rep_Proj P) \<bullet> (Rep_Proj k) \<noteq> 0" using rp2_incid.rep_eq not_incid by auto
  then have "(e *\<^sub>R x) \<bullet> (Rep_Proj k) \<noteq> 0" using edef by auto
  then have "e *\<^sub>R (x \<bullet> kvec) \<noteq> 0" 
    using assms alt_projrel equal_implies_projrel not_incid rep_P_nz rp2_incid.abs_eq by force
  then have "e*\<^sub>R 0 \<noteq> 0" using assms by auto
  then show False using scaleR_zero_right by fastforce
qed

lemma rp2_P4:
  fixes k
  fixes U
  assumes "k \<in> rp2_Lines"
  assumes "U = {X . X \<in> rp2_Points \<and> rp2_incid X k}"
  shows "\<exists>P Q R. P \<in> U \<and> Q \<in> U \<and> R \<in> U \<and> distinct [P,Q,R]"
proof - 
  obtain kvec where kvec_def: "kvec = Rep_Proj k" by auto
  have kvec_nz: "kvec \<noteq> zvec" using rep_P_nz using kvec_def by auto
  obtain a b c :: real where abc_def: "kvec = vector[a, b, c]" using kvec_def
  using forall_vector_3 by fastforce

  let ?v1 = "(vector[0, -c, b] :: real^3)"
  let ?v2 = "(vector[c, 0, -a] :: real^3)"
  let ?v3 = "(vector[-b, a, 0] :: real^3)"

  have abc_not_all_zero: "a \<noteq> 0 \<or> b \<noteq> 0 \<or> c \<noteq> 0" using kvec_nz abc_def zvec_def by auto

  consider (a_nz) "a \<noteq> 0" | (b_nz) "b \<noteq> 0" | (c_nz) "c \<noteq> 0"
    using abc_not_all_zero by auto
  then show ?thesis
  proof (cases)
    case a_nz

    let ?v4 = "?v2 + ?v3"
    
    have ortho2: "?v2 \<bullet> kvec = 0" unfolding abc_def by (simp add: inner_vec_def sum_3)
    have ortho3: "?v3 \<bullet> kvec = 0" unfolding abc_def by (simp add: inner_vec_def sum_3)

    have orthom: "(?v2 + ?v3) \<bullet> kvec = 0" unfolding abc_def using ortho2 ortho3
      by (simp add: abc_def inner_left_distrib)
    have ortho4: "?v4 \<bullet> kvec = 0" unfolding abc_def
      using abc_def orthom by auto

    (* Since a \<noteq> 0, ?v2 and ?v3 are non-zero *)
    have v2_nz: "?v2 \<noteq> zvec"
    proof (rule ccontr)
      assume "\<not>(?v2 \<noteq> zvec)"
      then have "vector[c, 0, -a] = vector[0, 0, 0]" by (simp add: vector_3_eq_iff)
      then have "-a = 0" by (metis vector_3(3))
      then have "a = 0" by simp
      then show False using a_nz by auto
    qed
    
    have v3_nz: "?v3 \<noteq> zvec"
    proof (rule ccontr)
      assume "\<not>(?v3 \<noteq> zvec)"
      then have "vector[-b, a, 0] = vector[0, 0, 0]" by (simp add: vector_3_eq_iff)
      then have "a = 0" by (metis vector_3(2))
      then show False using a_nz by auto
    qed

    have v4_nz: "?v4 \<noteq> zvec"
    proof (rule ccontr)
      assume v4_z: "\<not>(?v4 \<noteq> zvec)"
      have sum_eq: "vector[c, 0, -a] + vector[-b, a, 0] = vector[c - b, a, -a]"
        unfolding vector_def by vector
      then show False using a_nz local.sum_eq  v4_z vector_3_eq_iff zvec_def by metis
    qed

    let ?P = "Abs_Proj ?v2"
    let ?Q = "Abs_Proj ?v3"
    let ?R = "Abs_Proj ?v4"

    have p_point: "?P \<in> rp2_Points" unfolding rp2_Points_def by auto 
    have q_point: "?Q \<in> rp2_Points" unfolding rp2_Points_def by auto 
    have r_point: "?R \<in> rp2_Points" unfolding rp2_Points_def by auto 

    have "k = Abs_Proj kvec" using kvec_def using Quotient3_abs_rep Quotient3_rp2 by fastforce
    then have "rp2_incid ?P k = rp2_incid (Abs_Proj ?v2) (Abs_Proj kvec)"
      by auto

    have abs_proj_kvec: "k = Abs_Proj kvec" using ar kvec_def by auto

    have inc_P: "rp2_incid ?P k" 
      using dot_product_zero_implies_incid[of ?P k ?v2 kvec] abs_proj_kvec assms(1) kvec_nz ortho2 p_point v2_nz by auto

    have inc_Q: "rp2_incid ?Q k" 
      using dot_product_zero_implies_incid[of ?Q k ?v3 kvec] abs_proj_kvec assms kvec_nz ortho3 q_point v3_nz by auto

    have inc_R: "rp2_incid ?R k"
      using dot_product_zero_implies_incid[of ?R k ?v4 kvec] abs_proj_kvec assms kvec_nz ortho4 r_point v4_nz by auto

    have projrel_v4: "projrel (Rep_Proj (Abs_Proj (vector [c, 0, - a] + vector [- b, a, 0]))) (vector [c, 0, - a] + vector [- b, a, 0])" 
      using v4_nz ra[of ?v4] by auto
    have projrel_v3: "projrel (Rep_Proj (Abs_Proj (vector [- b, a, 0]))) (vector [- b, a, 0])"
      using v3_nz ra[of ?v3] by auto
    have projrel_v2: "projrel (Rep_Proj (Abs_Proj (vector [c, 0, - a]))) (vector [c, 0, - a])"
      using v2_nz ra[of ?v2] by auto

    have p_not_q: "?P \<noteq> ?Q"
      using projrel_v3 projrel_v2 a_nz alt_projrel cross3_def projrel_def vector_3_eq_iff
      by force 

    have p_not_r: "?P \<noteq> ?R"
      using projrel_v4 projrel_v2 a_nz alt_projrel cross3_def projrel_def vector_3_eq_iff
      by force 

    have q_not_r: "?Q \<noteq> ?R" 
      using projrel_v4 projrel_v3 a_nz alt_projrel cross3_def projrel_def vector_3_eq_iff
      by force 

    have pqr_distinct: "distinct[?P, ?Q, ?R]" using p_not_q p_not_r q_not_r by auto

    then show ?thesis using inc_P inc_Q inc_R pqr_distinct assms(2) p_point q_point r_point by blast
  next
    case b_nz
    let ?v4 = "?v1 + ?v3"
    
    have ortho1: "?v1 \<bullet> kvec = 0" unfolding abc_def by (simp add: inner_vec_def sum_3)
    have ortho3: "?v3 \<bullet> kvec = 0" unfolding abc_def by (simp add: inner_vec_def sum_3)

    have orthom: "(?v1 + ?v3) \<bullet> kvec = 0" unfolding abc_def using ortho1 ortho3
      by (simp add: abc_def inner_left_distrib)
    have ortho4: "?v4 \<bullet> kvec = 0" unfolding abc_def
      using abc_def orthom by auto

    (* Since b \<noteq> 0, ?v1 and ?v3 are non-zero *)
    have v1_nz: "?v1 \<noteq> zvec"
    proof (rule ccontr)
      assume "\<not>(?v1 \<noteq> zvec)"
      then have "vector[0, -c, b] = vector[0, 0, 0]" by (simp add: vector_3_eq_iff)
      then have "b = 0" by (metis vector_3(3))
      then show False using b_nz by auto
    qed
    
    have v3_nz: "?v3 \<noteq> zvec"
    proof (rule ccontr)
      assume "\<not>(?v3 \<noteq> zvec)"
      then have "vector[-b, a, 0] = vector[0, 0, 0]" by (simp add: vector_3_eq_iff)
      then have "-b = 0"  using vector_3_eq_iff by blast
      then show False using b_nz by auto
    qed

    have v4_nz: "?v4 \<noteq> zvec"
    proof (rule ccontr)
      assume v4_z: "\<not>(?v4 \<noteq> zvec)"
      have sum_eq: "vector[0, -c, b] + vector[-b, a, 0] = vector[-b, -c + a, b]"
        unfolding vector_def by vector
      then show False using b_nz local.sum_eq v4_z vector_3_eq_iff zvec_def by metis
    qed

    let ?P = "Abs_Proj ?v1"
    let ?Q = "Abs_Proj ?v3"
    let ?R = "Abs_Proj ?v4"

    have p_point: "?P \<in> rp2_Points" unfolding rp2_Points_def by auto 
    have q_point: "?Q \<in> rp2_Points" unfolding rp2_Points_def by auto 
    have r_point: "?R \<in> rp2_Points" unfolding rp2_Points_def by auto 

    have "k = Abs_Proj kvec" using kvec_def using Quotient3_abs_rep Quotient3_rp2 by fastforce
    then have "rp2_incid ?P k = rp2_incid (Abs_Proj ?v1) (Abs_Proj kvec)"
      by auto

    have abs_proj_kvec: "k = Abs_Proj kvec" using ar kvec_def by auto

    have inc_P: "rp2_incid ?P k" 
      using dot_product_zero_implies_incid[of ?P k ?v1 kvec] abs_proj_kvec assms(1) kvec_nz ortho1 p_point v1_nz by auto

    have inc_Q: "rp2_incid ?Q k" 
      using dot_product_zero_implies_incid[of ?Q k ?v3 kvec] abs_proj_kvec assms kvec_nz ortho3 q_point v3_nz by auto

    have inc_R: "rp2_incid ?R k"
      using dot_product_zero_implies_incid[of ?R k ?v4 kvec] abs_proj_kvec assms kvec_nz ortho4 r_point v4_nz by auto

    have projrel_v4: "projrel (Rep_Proj (Abs_Proj (vector[0, -c, b] + vector[-b, a, 0]))) (vector [0, -c, b] + vector [- b, a, 0])" 
      using v4_nz ra[of ?v4] by auto
    have projrel_v3: "projrel (Rep_Proj (Abs_Proj (vector [- b, a, 0]))) (vector [- b, a, 0])"
      using v3_nz ra[of ?v3] by auto
    have projrel_v2: "projrel (Rep_Proj (Abs_Proj (vector [0, -c, b]))) (vector [0, -c, b])"
      using v1_nz ra[of ?v1] by auto

    have p_not_q: "?P \<noteq> ?Q"
      using projrel_v3 projrel_v2 b_nz alt_projrel cross3_def projrel_def vector_3_eq_iff
      by force 

    have p_not_r: "?P \<noteq> ?R"
      using projrel_v4 projrel_v2 b_nz alt_projrel cross3_def projrel_def vector_3_eq_iff
      by force 

    have q_not_r: "?Q \<noteq> ?R" 
      using projrel_v4 projrel_v3 b_nz alt_projrel cross3_def projrel_def vector_3_eq_iff
      by force 

    have pqr_distinct: "distinct[?P, ?Q, ?R]" using p_not_q p_not_r q_not_r by auto

    then show ?thesis using inc_P inc_Q inc_R pqr_distinct assms(2) p_point q_point r_point by blast
  next
    case c_nz
    let ?v4 = "?v1 + ?v2"
    
    have ortho1: "?v1 \<bullet> kvec = 0" unfolding abc_def by (simp add: inner_vec_def sum_3)
    have ortho2: "?v2 \<bullet> kvec = 0" unfolding abc_def by (simp add: inner_vec_def sum_3)

    have orthom: "(?v1 + ?v2) \<bullet> kvec = 0" unfolding abc_def using ortho1 ortho2
      by (simp add: abc_def inner_left_distrib)
    have ortho4: "?v4 \<bullet> kvec = 0" unfolding abc_def
      using abc_def orthom by auto

    (* Since c \<noteq> 0, ?v1 and ?v2 are non-zero *)
    have v1_nz: "?v1 \<noteq> zvec"
    proof (rule ccontr)
      assume "\<not>(?v1 \<noteq> zvec)"
      then have x: "vector[0, -c, b] = vector[0, 0, 0]" by (simp add: vector_3_eq_iff)
      then have "b = 0" by (metis vector_3(3))
      then show False using c_nz neg_equal_0_iff_equal vector_3_eq_iff x by metis
    qed
    
    have v2_nz: "?v2 \<noteq> zvec"
    proof (rule ccontr)
      assume "\<not>(?v2 \<noteq> zvec)"
      then have y: "vector[c, 0, -a] = vector[0, 0, 0]" by (simp add: vector_3_eq_iff)
      then have "-a = 0"  using vector_3_eq_iff by blast
      then show False using c_nz y vector_3_eq_iff by blast
    qed

    have v4_nz: "?v4 \<noteq> zvec"
    proof (rule ccontr)
      assume v4_z: "\<not>(?v4 \<noteq> zvec)"
      have sum_eq: "vector[0, -c, b] + vector[c, 0, -a] = vector[c, -c, b-a]"
        unfolding vector_def by vector
      then show False using c_nz local.sum_eq v4_z vector_3_eq_iff zvec_def by metis
    qed

    let ?P = "Abs_Proj ?v1"
    let ?Q = "Abs_Proj ?v2"
    let ?R = "Abs_Proj ?v4"

    have p_point: "?P \<in> rp2_Points" unfolding rp2_Points_def by auto 
    have q_point: "?Q \<in> rp2_Points" unfolding rp2_Points_def by auto 
    have r_point: "?R \<in> rp2_Points" unfolding rp2_Points_def by auto 

    have "k = Abs_Proj kvec" using kvec_def using Quotient3_abs_rep Quotient3_rp2 by fastforce
    then have "rp2_incid ?P k = rp2_incid (Abs_Proj ?v1) (Abs_Proj kvec)"
      by auto

    have abs_proj_kvec: "k = Abs_Proj kvec" using ar kvec_def by auto

    have inc_P: "rp2_incid ?P k" 
      using dot_product_zero_implies_incid[of ?P k ?v1 kvec] abs_proj_kvec assms(1) kvec_nz ortho1 p_point v1_nz by auto

    have inc_Q: "rp2_incid ?Q k" 
      using dot_product_zero_implies_incid[of ?Q k ?v2 kvec] abs_proj_kvec assms kvec_nz ortho2 q_point v2_nz by auto

    have inc_R: "rp2_incid ?R k"
      using dot_product_zero_implies_incid[of ?R k ?v4 kvec] abs_proj_kvec assms kvec_nz ortho4 r_point v4_nz by auto

    have projrel_v4: "projrel (Rep_Proj (Abs_Proj (vector[0, -c, b] + vector[c, 0, -a]))) (vector [0, -c, b] + vector[c, 0, -a])" 
      using v4_nz ra[of ?v4] by auto
    have projrel_v1: "projrel (Rep_Proj (Abs_Proj (vector[0, -c, b]))) (vector[0, -c, b])"
      using v1_nz ra[of ?v1] by auto
    have projrel_v2: "projrel (Rep_Proj (Abs_Proj (vector[c, 0, -a]))) (vector[c, 0, -a])"
      using v2_nz ra[of ?v2] by auto

    have p_not_q: "?P \<noteq> ?Q"
      using projrel_v1 projrel_v2 c_nz alt_projrel cross3_def projrel_def vector_3_eq_iff
      by force 

    have p_not_r: "?P \<noteq> ?R"
      using projrel_v4 projrel_v1 c_nz alt_projrel cross3_def projrel_def vector_3_eq_iff
      by force 

    have q_not_r: "?Q \<noteq> ?R" 
      using projrel_v4 projrel_v2 c_nz alt_projrel cross3_def projrel_def vector_3_eq_iff
      by force 

    have pqr_distinct: "distinct[?P, ?Q, ?R]" using p_not_q p_not_r q_not_r by auto

    then show ?thesis using inc_P inc_Q inc_R pqr_distinct assms(2) p_point q_point r_point by blast
  qed
qed

text \<open>\done\done\<close>

text \<open>\done\done\<close>

text \<open>\hadi\<close>
theorem analytic_rp2:
  shows "projective_plane rp2_Points rp2_Lines rp2_incid"
proof (unfold_locales)
  show "\<lbrakk>P \<noteq> Q; P \<in> rp2_Points; Q \<in> rp2_Points\<rbrakk> 
    \<Longrightarrow> (\<exists>!k. k \<in> rp2_Lines \<and> rp2_incid P k \<and> rp2_incid Q k)" for P Q 
    using rp2_P1a [of P Q] rp2_P1b [of P Q] rp2_Lines_def by auto
  show "\<lbrakk>k \<in> rp2_Lines; n \<in> rp2_Lines\<rbrakk> 
    \<Longrightarrow> \<exists>P. (P \<in> rp2_Points \<and> rp2_incid P k \<and> rp2_incid P n)" for k n
    using rp2_P2 [of k n] rp2_P4 by auto
  show "\<exists>P Q R. P \<in> rp2_Points \<and> Q \<in> rp2_Points \<and> R \<in> rp2_Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R 
    \<and> \<not> (projective_plane_data.pcollinear rp2_Points rp2_Lines rp2_incid P Q R)"
    using rp2_P3 unfolding projective_plane_data.pcollinear_def by auto
  show "\<lbrakk>k \<in> rp2_Lines; U = {P. (P \<in> rp2_Points \<and> rp2_incid P k)}\<rbrakk> 
    \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]" for k U 
    using rp2_P4 by auto
qed
text \<open>\done\<close>

(* also needed: an interpretation claim like those for A4 and A2 *)
interpretation RP2Q: projective_plane rp2_Points rp2_Lines rp2_incid
  using analytic_rp2 by auto

theorem projectivisation_of_A2:
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P. (P \<in> A2Points)} \<union> {Ideal t | k t. 
     ((k \<in> A2Lines) \<and> (t = affine_plane_data.line_pencil A2Points A2Lines (a2incid) k))}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n. (n \<in>  A2Lines)} \<union> {Infty}"
  defines pm: "pincid \<equiv> mprojectivize (a2incid)"
  shows "projective_plane pPoints pLines pincid"
  using "Chapter1-1.projectivization_is_projective" A2_affine assms(1,2,3) by blast

interpretation RP2C: projective_plane  "{OrdinaryP P | P. (P \<in> A2Points)} \<union> {Ideal t | k t. 
  ((k \<in> A2Lines) \<and> (t = affine_plane_data.line_pencil A2Points A2Lines (a2incid) k))}" 
  " {OrdinaryL n | n. (n \<in> A2Lines)} \<union> {Infty}" "(mprojectivize (a2incid))"
  using projectivisation_of_A2 by auto

(* need definition of isomorphism, and proof that RP2Q is isomorphic to RP2C; 
place these Chapter 1-3. *)

text \<open>\nick\<close>

end