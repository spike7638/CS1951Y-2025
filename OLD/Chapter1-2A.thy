theory "Chapter1-2A"
  imports Complex_Main  "Chapter1-1" "HOL-Analysis.Cross3"

begin
(* Team RP2-quotient:  Jiayi, Luke, George, Nick, Oliver *)

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
  shows "zvec =  vector[0::real, 0, 0]" using zvec_def by auto

definition map_vec where
"map_vec f g v = vec_lambda (map_fun g f (vec_nth v))"
functor map_vec
  unfolding map_vec_def
  using eq_id_iff by fastforce+

definition projrel :: "(v3) \<Rightarrow> (v3) \<Rightarrow> bool"
  where "projrel x y \<longleftrightarrow> (x \<noteq>zvec) \<and>  (y \<noteq> zvec) \<and> (\<exists> t::real . t \<noteq> 0 \<and> x =  t *\<^sub>R  y)" 

text\<open>\spike Current definition of projective relation is that the cross product is zero; 
former definition was that there's a nonzero constant c such that u = cv. Let's start
with the big theorem that these two things are equivalent\<close>
lemma alt_projrel:
  assumes "u \<noteq> zvec"
  assumes "v \<noteq> zvec"
  shows "(projrel u v) \<longleftrightarrow> (u \<noteq> zvec) \<and> (v \<noteq> zvec) \<and> (u \<times> v) = zvec"
proof 
  assume ah1: "projrel u v"
  then obtain t where "t \<noteq> 0 \<and> u =  t *\<^sub>R  v" using projrel_def assms by blast
  then show "(u \<noteq> zvec) \<and> (v \<noteq> zvec) \<and> (u \<times> v) = zvec" 
    using projrel_def cross_refl assms(1) cross3_def cross_zero_right  by auto 
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
    have sr: "s \<noteq> 0 \<and> r \<noteq> 0" using uw vw assms ah2 cross3_def  by fastforce
    then have "u = (r/s) *\<^sub>R v" using uw vw by simp
    then have "(\<exists> t::real . (t \<noteq>0) \<and> u =  t *\<^sub>R  v)" using sr  divide_eq_0_iff by blast
    then show "projrel u v" using projrel_def ah2 assms by blast
  qed
  
text \<open>\done\<close>

lemma vt:
  shows "(vector[1,0,0]::real^3) \<noteq> zvec" using zvec_def
  by (metis vector_3(1) zero_neq_one)

lemma exists_projrel_refl: "\<exists>x. projrel x x" 
proof -
  have "projrel (vector [1,0,0]::real^3) (vector [1,0,0]::v3)" using projrel_def vt by auto
  then show ?thesis by blast
qed

lemma symp_projrel: "symp projrel"
proof -
  show ?thesis  unfolding symp_def projrel_def 
    using cross_mult_right projrel_def by (metis divideR_right scaleR_zero_left)
qed

lemma transp_projrel: "transp projrel"
proof (rule transpI)
  fix x y z
  assume 1: "projrel x y"
  assume 2: "projrel y z"
  obtain s where xym: "s \<noteq> 0 \<and> x = s *\<^sub>R y" using alt_projrel projrel_def 1 by auto
  obtain t where yzm: "t \<noteq> 0 \<and> y = t *\<^sub>R z" using alt_projrel projrel_def 2 by auto
  have xz: "(s*t) \<noteq> 0 \<and> x = (s*t) *\<^sub>R z" using xym yzm by simp
  then show  "projrel x z" using  xz projrel_def 1 2 by blast
qed

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
  using c_def projrel_def smult x_def y_def  by blast
text \<open>\done\<close>

quotient_type rp2 = "v3" / partial: "projrel"
  morphisms Rep_Proj Abs_Proj
  using part_equivp_projrel .

find_theorems name: "rp2"
find_theorems name: "Quotient3_rp2"

lemma Domainp_cr_proj [transfer_domain_rule]: "Domainp cr_rp2 = (\<lambda>x .( (x \<noteq> zvec) \<and> projrel x x))"
proof -
  have "projrel x x \<longrightarrow> x  \<noteq> zvec" for x using projrel_def by blast
  then show ?thesis  using projrel_def rp2.domain by auto 
qed

lemma rep_P_nz:
  fixes P
  assumes a1: "P \<in> rp2_Points" 
  shows "Rep_Proj P \<noteq> zvec" 
using projrel_def Quotient_rel_rep Quotient_rp2 by metis

(* a remaining theorem from the "warmup" section, one that needs "projrel", and
needs rewriting using Cross3 rather than our (now-delete) version of 'cross' *)

lemma cross_nz:
  assumes "u \<noteq> zvec"
  assumes "v \<noteq> zvec"
  assumes "\<not> projrel u v"
  defines s_def: "s \<equiv> u \<times> v"
  shows "s  \<noteq> zvec" 
  using assms(1,2,3) cross3_def projrel_def  s_def alt_projrel zvec_def by metis

(* We've defined RP2, but we still need to show it's a projective plane, i.e., demonstrate 
axioms 1 - 4. Then we can move on to isomorphism with the completion of the affine plane. *)

(* RP2 is a projective plane *)

definition rp2_Points where
"rp2_Points = (UNIV::rp2 set)" 

definition rp2_Lines where
"rp2_Lines = (UNIV::rp2 set)"

definition rp2_incid_rep where
"rp2_incid_rep P k = (P \<bullet> k = 0)"

lift_definition rp2_incid::"rp2 \<Rightarrow> rp2 \<Rightarrow> bool"
is "\<lambda> P k . (P \<bullet> k = 0)"
proof -
  fix P1 P2 k1 k2
  assume a1: "projrel P1 P2"
  assume a2: "projrel k1 k2"
  obtain s where P12: "s \<noteq> 0 \<and> P1 = s *\<^sub>R P2" 
    using alt_projrel [of P1 P2]  a1 projrel_def [of P1 P2] cross3_def by fastforce
  obtain t where k12: "t \<noteq> 0 \<and> k1 = t *\<^sub>R k2"
    using alt_projrel [of k1 k2]  a2 projrel_def [of k1 k2]  cross3_def by fastforce
  have ts: "t \<noteq> 0 \<and> s \<noteq> 0"  using P12 k12 by auto
  have "(P1 \<bullet> k1 = 0) = (P1 \<bullet> (t *\<^sub>R k2) = 0)" using k12 by auto 
  also have "... = ( P2 \<bullet>  k2 = 0)" using P12 ts by auto
  finally show "(P1 \<bullet> k1 = 0) =(P2 \<bullet> k2 = 0)" .
qed
lemma incid_commute:
  shows "rp2_incid A B \<longleftrightarrow> rp2_incid B A"
  by (simp add: inner_commute rp2_incid.rep_eq)

(*
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k . k \<in> Lines \<and> P \<lhd> k  \<and> Q \<lhd>  k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = { P . (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
*)

definition join :: "real^3 \<Rightarrow> real^3 \<Rightarrow> real^3"
  where
  "join P Q = (if P \<times> Q = zvec then vector[0,0,1] else P \<times> Q)"

lift_definition Join :: "rp2 \<Rightarrow> rp2 \<Rightarrow> rp2"
  is "\<lambda>P Q. join P Q" 
proof -
  show "projrel P Q \<Longrightarrow> projrel R S \<Longrightarrow> projrel (join P R) (join Q S)" for P Q R S
  proof -
    assume a1: "projrel P Q"
    assume a2: "projrel R S"
    obtain s where PQ: "s \<noteq> 0 \<and> P = s *\<^sub>R Q" 
      using alt_projrel [of P Q]  a1 projrel_def [of P Q] cross3_def by fastforce
    obtain t where RS: "t \<noteq> 0 \<and> R = t *\<^sub>R S"
      using alt_projrel [of R S]  a2 projrel_def [of R S]  cross3_def by fastforce
    have ts: "t \<noteq> 0 \<and> s \<noteq> 0"  using PQ RS by auto
    have ts2: "t * s \<noteq> 0" using ts by simp
    have "join P R = (if P \<times> R = zvec then vector[0,0,1] else P \<times> R)" using join_def by auto
    also have "... = (if P \<times> (t *\<^sub>R S) = zvec then vector[0,0,1] else P \<times> (t *\<^sub>R S))" using RS by auto
    also have "... = (if (s *\<^sub>R Q) \<times> (t *\<^sub>R S) = zvec then vector[0,0,1] else  (s *\<^sub>R Q) \<times> (t *\<^sub>R S))" using PQ by auto
    also have "... = (if ((s*t) *\<^sub>R (Q \<times> S) = zvec) then vector[0,0,1] else  ((s*t)*\<^sub>R ( Q \<times> S)))" 
      using bilinear_cross  by (simp add: bilinear_lmul bilinear_rmul)
    also have "... = (if ( (Q \<times> S) = zvec) then vector[0,0,1] else  ((s*t)*\<^sub>R ( Q \<times> S)))" 
      using ts2  alt_projrel smult_projrel by fastforce
    finally have rel: "join P R = (if Q \<times> S = zvec then vector [0, 0, 1] else (s * t) *\<^sub>R Q \<times> S)" .
    have "projrel (join P R) (join Q S)"
    proof (cases "Q \<times>S = zvec")
      case 1: True
      have a: "(join P R) = vector [0, 0, 1]" using 1 rel by auto
      have b: "(join Q S) = vector [0, 0, 1]" using 1 join_def by auto
      have "projrel (join P R) (join Q S) = ((join P R \<noteq> zvec) \<and> (join Q S \<noteq> zvec) \<and> (\<exists>t . join P R = t *\<^sub>R join Q S))" 
        using projrel_def a b by auto
      then have c: "projrel (join P R) (join Q S) = ((\<exists>t . join P R = t *\<^sub>R join Q S))" 
        using a b by (metis vector_3(3) zero_neq_one zvec_def)
      have d: "join P R =  1 *\<^sub>R join Q S" using a b by simp
      then show "projrel (join P R) (join Q S)" using  c d projrel_def by blast
    next
      case 2: False
      have a: "(join P R) = P \<times> R" 
        using 2 rel projrel_def by (simp add: PQ RS cross_mult_left cross_mult_right)
      have b: "(join Q S) = Q \<times> S" using 2 join_def by auto
      have "projrel (join P R) (join Q S) = ((join P R \<noteq> zvec) \<and> (join Q S \<noteq> zvec) \<and> (\<exists>h . join P R = h *\<^sub>R join Q S))" 
        using projrel_def a b by (metis mult.commute rel ts2)
      then have c: "projrel (join P R) (join Q S) = ((\<exists>h . join P R = h *\<^sub>R join Q S))" 
        using 2 join_def [of P R] join_def [of Q S] projrel_def  by (metis (full_types) RS div_by_1 divide_eq_0_iff vector_3(3) zvec_def)
      also have d: "... = ((\<exists>h . (P \<times> R) = h *\<^sub>R (Q \<times> S)))" using a b by auto
      also have e: "... =  ((\<exists>h . ((s *\<^sub>R Q) \<times> (t *\<^sub>R S)) = h *\<^sub>R (Q \<times> S)))" using PQ RS by simp
      also have f: "... =  ((\<exists>h . (s * t)*\<^sub>R (Q \<times> S) = h *\<^sub>R (Q \<times> S)))" using PQ RS 2 a rel by auto
      finally have "projrel (join P R) (join Q S) = ((\<exists>h . (s * t)*\<^sub>R (Q \<times> S) = h *\<^sub>R (Q \<times> S)))" .
      then show "projrel (join P R) (join Q S)" using  c d projrel_def by blast
    qed
    show "projrel (join P R) (join Q S)"   using \<open>projrel (join P R) (join Q S)\<close> by auto
  qed
qed

lemma join_commute:
  fixes P Q
  assumes a1: "P \<in> rp2_Points" 
  assumes a2: "Q \<in> rp2_Points"
  assumes a3: "P \<noteq> Q"
  shows "Join P Q = Join Q P"
proof (transfer)
  fix P Q 
  show "P \<noteq> zvec \<and> projrel P P \<Longrightarrow> Q \<noteq> zvec \<and> projrel Q Q \<Longrightarrow> projrel (join P Q) (join Q P)"
  proof -
    show ?thesis
      by (smt (verit, best) alt_projrel cross_minus_left cross_nz cross_refl cross_skew exists_projrel_refl join_def projrel_def vector_3(3) zvec_def) 
  qed
qed
    

lemma rp2_P1a:
  fixes P Q
  assumes a1: "P \<in> rp2_Points" 
  assumes a2: "Q \<in> rp2_Points"
(*  assumes a3: "P \<noteq> Q" *)
  shows "(\<exists>k . rp2_incid P  k  \<and>  rp2_incid Q  k)"
proof (transfer)
  fix P Q 
  show "P \<noteq> zvec \<and> projrel P P \<Longrightarrow> Q \<noteq> zvec \<and> projrel Q Q \<Longrightarrow> \<exists>k\<in>{x. x \<noteq> zvec \<and> projrel x x}. P \<bullet> k = 0 \<and> Q \<bullet> k = 0"
  proof -
    assume pf: "P \<noteq> zvec \<and> projrel P P"
    assume qf: "Q \<noteq> zvec \<and> projrel Q Q"
    show "\<exists>k\<in>{x. x \<noteq> zvec \<and> projrel x x}. P \<bullet> k = 0 \<and> Q \<bullet> k = 0"
    proof (cases "projrel P Q")
      case 1: True
      obtain u where "P \<times> u \<noteq> 0" using cross_basis_nonzero[of P] by (metis alt_projrel pf)
      then have "P \<bullet> (P \<times> u) = 0 \<and> Q \<bullet> (P \<times> u) = 0"
       using 1 cross_mult_left dot_cross_self(1) projrel_def by auto
      then show ?thesis using \<open>P \<times> u \<noteq> 0\<close> alt_projrel pf by auto
    next
      case 2: False
      then show ?thesis  using alt_projrel dot_cross_self(1,2) pf qf by auto
    qed
  qed
qed

lemma unique_cross:
  fixes a b n k
  assumes "a \<times> b \<noteq> 0"
  assumes "k \<bullet> a = 0" and "k \<bullet> b = 0" 
  shows "\<exists> s . k = s *\<^sub>R (a \<times> b)"
proof -
  have "k \<times> (a \<times> b) = (k \<bullet> b) *\<^sub>R a -  (k \<bullet> a) *\<^sub>R b" using Lagrange [of k a b] .
  then have "k \<times> (a \<times> b) = 0" using assms by auto
  then show "\<exists> s.  k = s *\<^sub>R (a \<times> b)" 
    by (metis alt_projrel assms(1) cross_refl exists_projrel_refl projrel_def scaleR_zero_left)
qed

(* TO DO: To show uniqueness, we have to show (for P,Q nonzero and P and Q not proj_rel,
that if h is orthog to P and Q, then h is a nonzero multiple of the cross product. Ugh. Ugly algebra ahead *)
lemma rp2_P1b_helper:
  fixes P Q k n
  assumes P_def: "P \<noteq> zvec" 
  assumes Q_def: "Q \<noteq> zvec"
  assumes PQ_nprojrel: "\<not> projrel P Q"
  assumes n_def: "n = P \<times> Q"
  assumes k_def: "k \<noteq> zvec"
  assumes k_facts: "(P \<bullet> k = 0)  \<and> (Q \<bullet> k = 0)" 
  shows "\<exists>c . (c \<noteq> 0) \<and> k = c *\<^sub>R n"
proof -
  show ?thesis using unique_cross assms
    by (metis alt_projrel cross_refl exists_projrel_refl inner_commute projrel_def scaleR_zero_left)
qed

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
  obtain Pvec where hPrep: "Pvec = Rep_Proj P" and hPpr3: "Pvec \<noteq> zvec" and hPnz: "Pvec \<noteq> 0" 
    using cross3_def cross_zero_left  rep_P_nz by fastforce
  obtain Qvec where hQrep: "Qvec = Rep_Proj Q" and hQpr3: "Qvec \<noteq> zvec" and hQnz: "Qvec \<noteq> 0" 
    using cross3_def cross_zero_left  rep_P_nz by fastforce
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
    using h1 h2 hPpr3 hQpr3 hkpr3 rp2_P1b_helper[of Pvec Qvec ?crossPQ kvec] by blast
  obtain c_n where hcn: "(c_n \<noteq> 0) \<and> nvec = c_n *\<^sub>R ?crossPQ"
    using h1 h3 hPpr3 hQpr3 hnpr3 rp2_P1b_helper[of Pvec Qvec ?crossPQ nvec] by blast
  have h4: "((c_k/c_n) \<noteq> 0) \<and> kvec = (c_k/c_n) *\<^sub>R nvec" using hck hcn by auto
  show ?thesis 
    using h4 Quotient3_rel_rep Quotient3_rp2 hkrep hnrep projrel_def hkpr3 hnpr3 smult_projrel
    by metis
qed
text \<open>\done\<close>

lemma rp2_P2:
  fixes m k 
  assumes a1: "m \<in> rp2_Lines" 
  assumes a2: "k \<in> rp2_Lines"
  assumes a3: "m \<noteq> k"
  shows "(\<exists>P . P \<in> rp2_Points \<and> rp2_incid P  m  \<and>  rp2_incid P  k)"
  using rp2_P1a [of m k] incid_commute  by (simp add: rp2_Points_def)

lemma rp2_P3:
  shows "\<exists>P Q R. P \<in> rp2_Points \<and> Q \<in>  rp2_Points \<and> R \<in>  rp2_Points \<and> 
          P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> 
          \<not> (\<exists>k \<in> rp2_Lines . rp2_incid P k \<and> rp2_incid Q k \<and> rp2_incid R k)"
proof -
  define p1 where "p1 = Abs_Proj (vector[1,0,0::real]::v3)"
  define p2 where "p2 = Abs_Proj (vector[0,1,0::real]::v3)"
  define p3 where "p3 = Abs_Proj (vector[0,0,1::real]::v3)"
  have u1: "p1 \<in> rp2_Points \<and> p2 \<in> rp2_Points \<and> p3 \<in> rp2_Points"  using rp2_Points_def by auto
  have v12: "p1 \<noteq> p2"  
    by (smt (verit) alt_projrel cart_eq_inner_axis cross_refl exists_projrel_refl norm_and_cross_eq_0 p1_def p2_def projrel_def rp2_incid.abs_eq vector_3 vt)
  have v13: "p1 \<noteq>p3"  
    by (smt (verit) alt_projrel cart_eq_inner_axis cross_refl exists_projrel_refl norm_and_cross_eq_0 p1_def p3_def projrel_def rp2_incid.abs_eq vector_3(1,3))
  have "(vector[0,1,0::real]::v3) \<times>(vector[0,0,1::real]::v3) = (vector[1,0,0::real]::v3)" using cross3_def by simp
  then have v23: "p2 \<noteq> p3"
    by (smt (verit, ccfv_threshold) Join.abs_eq \<open>p1 \<noteq> p2\<close> alt_projrel cross_zero_right join_def p1_def p2_def p3_def scaleR_one smult_projrel vector_3(2) vt zero_index)

  have u2: "\<not> (\<exists>k \<in> rp2_Lines . rp2_incid p1 k \<and> rp2_incid p2 k \<and> rp2_incid p3 k)"
    by (smt (verit, ccfv_SIG) UNIV_I \<open>vector [0, 1, 0] \<times> vector [0, 0, 1] = vector [1, 0, 0]\<close> alt_projrel cross_refl dot_cross_self(1,2) exists_projrel_refl norm_and_cross_eq_0 p1_def p2_def
        p3_def projrel_def rp2_Lines_def rp2_P1b rp2_Points_def rp2_incid.abs_eq v23 vt) 
  show ?thesis using u1 v12 v13 v23 u2 by auto
qed

lemma rp2_P4jfh:
  fixes k
  fixes U
  assumes "k \<in> rp2_Lines"
  assumes "U = {X . X \<in> rp2_Points \<and> rp2_incid X k}"
  shows "\<exists>P Q R. P \<in> U \<and> Q \<in> U \<and> R \<in> U \<and> distinct [P,Q,R]"
proof -
  obtain kR where "kR = Rep_Proj k" by blast
  then have "kR \<noteq> zvec" using rep_P_nz by auto
  then obtain u where "kR \<times> u \<noteq> 0" using cross_basis_nonzero 
    by (metis alt_projrel cross_refl exists_projrel_refl projrel_def)
  define PR where "PR = kR \<times> u"
  define QR where "QR = kR \<times> PR"
  have "kR \<bullet> PR = 0" using PR_def dot_cross_self(1) by presburger
  have "kR \<bullet> QR = 0" using PR_def QR_def dot_cross_self by auto
  have "\<not> (projrel PR QR)" using PR_def QR_def projrel_def alt_projrel
    by (metis Quotient_rel_rep Quotient_rp2 cross_refl dot_cross_self(2) norm_and_cross_eq_0)
  define RR where "RR = PR + QR"
  have "kR \<bullet> RR = 0"  by (simp add: RR_def \<open>kR \<bullet> PR = 0\<close> \<open>kR \<bullet> QR = 0\<close> inner_right_distrib)
  have "kR \<noteq> PR"  using \<open>kR \<bullet> PR = 0\<close> \<open>kR \<times> u \<noteq> 0\<close> by force
  have "kR \<noteq> QR"  using \<open>kR \<bullet> QR = 0\<close> \<open>kR \<times> u \<noteq> 0\<close> by force
  define P where "P = Abs_Proj PR"
  define Q where "Q = Abs_Proj QR"
  define R where "R = Abs_Proj RR"
  have "distinct[P, Q, R]"
    by (smt (verit) Domainp_cr_proj PR_def P_def QR_def Q_def RR_def R_def \<open>kR \<bullet> PR = 0\<close> \<open>kR \<times> u \<noteq> 0\<close> alt_projrel cross_refl cross_triple distinct_length_2_or_more distinct_singleton
        dot_cross_self(2) exists_projrel_refl inner_left_distrib norm_and_cross_eq_0 rp2.domain rp2_incid.abs_eq) 
  have "rp2_incid P k" 
  by (metis (full_types) PR_def P_def Quotient3_def Quotient3_rp2 \<open>kR = Rep_Proj k\<close> \<open>kR \<bullet> PR = 0\<close> \<open>kR \<noteq> zvec\<close> \<open>kR \<times> u \<noteq> 0\<close> alt_projrel cross_refl incid_commute rp2_incid.abs_eq)
  have "rp2_incid Q k"
  by (metis (full_types) PR_def QR_def Q_def Quotient3_def Quotient3_rp2 \<open>kR = Rep_Proj k\<close> \<open>kR \<bullet> PR = 0\<close> \<open>kR \<bullet> QR = 0\<close> \<open>kR \<noteq> zvec\<close> \<open>kR \<times> u \<noteq> 0\<close> alt_projrel cross_refl incid_commute
      norm_and_cross_eq_0 rp2_incid.abs_eq)
  have "rp2_incid R k" 
    by (smt (verit, ccfv_threshold) PR_def QR_def Quotient3_def Quotient3_rp2 RR_def R_def \<open>kR = Rep_Proj k\<close> \<open>kR \<bullet> RR = 0\<close> \<open>kR \<noteq> zvec\<close> \<open>kR \<times> u \<noteq> 0\<close> alt_projrel cross_refl dot_cross_self(3)
      incid_commute inner_left_distrib norm_and_cross_eq_0 rp2_incid.abs_eq)
  show ?thesis 
    using \<open>distinct [P, Q, R]\<close> \<open>rp2_incid P k\<close> \<open>rp2_incid Q k\<close> \<open>rp2_incid R k\<close> assms(2) rp2_Points_def by auto
qed






text \<open>\Jiayi\Luke\<close>
lemma rp2_P4:
  fixes k
  fixes U
  assumes "k \<in> rp2_Lines"
  assumes "U = {X . X \<in> rp2_Points \<and> rp2_incid X k}"
  shows "\<exists>P Q R. P \<in> U \<and> Q \<in> U \<and> R \<in> U \<and> distinct [P,Q,R]"
proof - 
  obtain P Q where pq: "P \<in> U \<and> Q \<in> U" using assms 
      mem_Collect_eq rp2_P1a rp2_P2 rp2_P3 by metis
  obtain a b c :: real where abc: "Rep_Proj P = vector[a, b, c]" 
    using forall_vector_3 by fastforce
  obtain d e f :: real where def: "Rep_Proj Q = vector[d, e, f]" 
    using forall_vector_3 by fastforce
  obtain g h i :: real where ghi: "g=(a+b)/2 \<and> h= (b+e)/2 \<and> i=(c+f)/2" 
    by blast

  have 0: "Abs_Proj (vector[g, h, i]) \<in> rp2_Points" using rp2_Points_def by auto 

  obtain R where r: " R = Abs_Proj (vector[g, h, i])" using 0 by auto
  then have r_rep: "projrel((Rep_Proj R)) (vector[g, h, i])" using ra
    sorry
  then have 0: "distinct[P,Q,R]" using num1_eq1 vt sorry
  then have 1: "R \<in> U" using num1_eq1 vt sorry
  then show ?thesis using pq r 0 1 by auto
qed

text \<open>\done\done\<close>

theorem analytic_rp2:
  shows "projective_plane2 rp2_Points rp2_Lines rp2_incid"
  sorry

(* also needed: an interpretation claim like those for A4 and A2 *)
interpretation RP2Q: projective_plane2 rp2_Points rp2_Lines rp2_incid
  using analytic_rp2 by auto


theorem projectivisation_of_A2:
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> A2Points)} \<union> {Ideal t | k t . 
                  ((k \<in> A2Lines) \<and> (t = affine_plane_data.line_pencil  A2Points  A2Lines ( a2incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in>  A2Lines)} \<union> {Infty}"
  defines pm: "pincid \<equiv>  mprojectivize (a2incid)"
  shows   "projective_plane2 pPoints pLines pincid"
  using "Chapter1-1.projectivization_is_projective" A2_affine assms(1,2,3) by blast

interpretation RP2C: projective_plane2  "{OrdinaryP P | P . (P \<in> A2Points)} \<union> {Ideal t | k t . 
                  ((k \<in> A2Lines) \<and> (t = affine_plane_data.line_pencil  A2Points  A2Lines ( a2incid) k) )}" " {OrdinaryL n | n . (n \<in>  A2Lines)} \<union> {Infty}" "(mprojectivize (a2incid))"
  using projectivisation_of_A2 by auto

(* need definition of isomorphism, and proof that RP2Q is isomorphism to RP2C; 
place these Chapter 1-3. *)

end


