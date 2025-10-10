theory "Chapter1-2"
  imports Complex_Main  "Chapter1-1" "HOL-Analysis.Cross3"

begin
(* Team RP2-quotient:  Jiayi, Luke, George, Nick, Oliver *)
text\<open> Start out by defining RP2 as a quotient of R3 - {origin}. I'll need various 
linear-algebra-like operations; smult is "scalar multiplication", dot and cross
are dot product and cross product. vplus is vector addition.

Chances are that all this is pointless once you include HOL-Analysis.Cross3, 
except that it wants to work with "real^3" (which is a type with 
a fancy definition that seems not to be amenable to quotients), while we 
have real \<times> real \<times> real.  It may help to look at Cross3 regardless,
as it shows how to prove some facts that we may need, and mimicking those proofs
may be feasible even if using them direectly is not. 

\<close>
type_synonym v3 = "real^3"
definition punctured_r_3 where
"punctured_r_3 = (UNIV::(v3 set)) - {0::v3}"

text\<open>
(* STUDENTS: click on the Cross3.thy file that's imported above to see that cross and dot product
are defined already, with infix notation ready to use! *)

(*
definition cross::"(real \<times> real \<times> real) \<Rightarrow>(real \<times> real \<times> real) \<Rightarrow> (real \<times> real \<times> real)"  where
"cross =  (\<lambda> (x1, x2, x3) (y1, y2, y3) . (x2*y3 - x3 * y2, x3 * y1  - x1 * y3, x1 * y2 - x2* y1))"
*)
(* Idea: show that |u x v|^2 = |u|^2 |v|^2 sin^2 theta = |u|^2 |v|^2 (1 - cos^2theta)
 = |u|^2 |v|^2 (1 - dot(u,v)^2/ |u|^2 |v|^2 ) = |u|^2 |v|^2 - dot(u,v)^2 > 0 for some reason...
*)
(*
definition squared_length::"(real \<times> real \<times> real) \<Rightarrow>real" where
"squared_length =  (\<lambda> (x1, x2, x3) . (x1*x1 + x2*x2 + x3 * x3))"

definition dot::"(real \<times> real \<times> real) \<Rightarrow>(real \<times> real \<times> real) \<Rightarrow> real" where
"dot =  (\<lambda> (x1, x2, x3) (y1, y2, y3) . (x1 * y1 + x2 * y2 + x3 * y3))"

definition vplus::"(real \<times> real \<times> real) \<Rightarrow>(real \<times> real \<times> real) \<Rightarrow> (real \<times> real \<times> real)"  where
"vplus =  (\<lambda> (x1, x2, x3) (y1, y2, y3) . (x1+y1, x2+y2, x3+y3))"

definition smult::"real \<Rightarrow> (real \<times> real \<times> real) \<Rightarrow>(real \<times> real \<times> real)"  where
"smult =  (\<lambda> s (x1, x2, x3). (s*x1, s* x2, s* x3))"
*)
(* already included via Cross3 in various forms
lemma smult_assoc: 
  "smult a (smult b v) = smult (a * b) v"
  unfolding smult_def
  sorry

lemma smult_ident: 
  "smult 1 v =  v"
  unfolding smult_def by simp

lemma vplus_comm:
  shows "vplus u v = vplus v u"  
  sorry

lemma squared_length_is_self_dot:
  fixes x1 x2 x3::real
  shows "squared_length (x1, x2, x3)  = dot (x1, x2, x3) (x1, x2, x3)"
  sorry

lemma nonzero_vector_implies_nonzero_square_length:
  assumes "(x1, x2, x3) \<in> punctured_r_3"
  shows "squared_length (x1, x2, x3) > 0"
  sorry

lemma nonzero_square_length_implies_nonzero_vector:
  fixes x1 x2 x3
  assumes "squared_length (x1, x2, x3) > 0"
  shows "(x1, x2, x3) \<noteq> (0,0,0)"
  sorry


lemma sq_diff: 
  shows "((a::real) - b)*(a-b) = a*a - 2 * a * b + b * b"
  by algebra

lemma abcpqr:
  shows "((a::real) + b + c) * (p + q + r) = a*p + a*q + a * r + b *p + b*q + b*r + c*p + c*q + c*r" by argo 

thm abcpqr [of "x1*y1" "x2*y2" "x3*y3"  "x1*y1" "x2*y2" "x3*y3"]

lemma cross_prod_length:
  fixes x1 x2 x3::real
  fixes y1 y2 y3::real
  shows "squared_length (cross (x1, x2, x3) (y1, y2, y3)) = 
    (squared_length (x1, x2, x3) ) * (squared_length (y1, y2, y3) ) - 
  (dot (x1, x2, x3) (y1, y2, y3)) *  (dot (x1, x2, x3) (y1, y2, y3))"
  sorry

lemma cross_prod_length2:
  fixes u v
  shows "squared_length (cross u v) = 
    (squared_length u ) * (squared_length v ) - 
  (dot u v) *  (dot u v)"
  sorry

lemma dot_commute:
  fixes u v
  shows "dot u v = dot v u"
  sorry

lemma dot_distrib [simp]:
  fixes u v w
  shows "dot (vplus u v) w = dot u w + dot v w"
  sorry

lemma dot_scalar [simp]:
  fixes u v s
  shows "dot u (smult s v) = s * dot u v"
  sorry

lemma dot_pos:
  fixes u
  shows "(dot u u \<ge> 0)"
  sorry

(* prove dot(u,u) = 0 only if u = 0 *)
lemma dot_non_degenerate:
  fixes u
  shows "(dot u u = 0) \<longleftrightarrow> (u = (0,0,0))"
  sorry

lemma pythag_setup:
  fixes u v
  assumes "v \<noteq> (0,0,0)"
  defines "s \<equiv> smult ((dot u v)/(dot v v)) v"
  defines "t \<equiv> vplus u (smult (-1) s)"
  shows "dot s t = 0"
  sorry

lemma pythag:
  fixes u v w
  assumes "dot v w = 0"
  assumes "u = vplus v w"
  shows "(dot u u) = (dot v v) + (dot w w)"
  sorry


lemma cs1: (* cauchy-schwartz, step 1 *)
  fixes u v s
  assumes "(dot v v)  \<noteq> 0"
  shows "s * s * (dot v v) + s * 2 *  (dot u   v) + (dot  u u) \<ge> 0"
  sorry

lemma cs2:
  fixes u v s
  assumes "(dot v v)  \<noteq> 0"
  shows "\<forall>s . s * s * dot v v + s * 2 *  (dot u   v) + (dot  u u) \<ge> 0"
  sorry
*)

(* These, too, may be irrelevant !*)
(*thm discriminant_iff [of "(dot v v)" t "2* (dot u v)" "(dot u u)"]*)

(* re=quoted from the discriminant theory *)
lemma discriminant_nonneg_ex:
  fixes a b c :: real
  assumes "a \<noteq> 0"
    and "discrim a b c \<ge> 0"
  shows "\<exists> x. a * x\<^sup>2 + b * x + c = 0"
  by (auto simp: discriminant_nonneg assms)

(*thm discriminant_pos_ex*)

lemma discriminant_pos_cross_axis:
  fixes a b c :: real
  assumes "a \<noteq> 0"
    and "discrim a b c > 0"
  shows "\<exists> x. (a * x\<^sup>2 + b * x + c) * a  < 0"
  sorry

lemma no_solutions_discrim_neg:
  fixes a b c :: real
  assumes "a \<noteq> 0"
  assumes "\<forall> x. a * x\<^sup>2 + b * x + c \<noteq> 0"
  shows "discrim a b c < 0"
  sorry

(* we should really grab these from  Inner_Product.real_inner.norm_cauchy_schwarz *)
(*
find_theorems name: "cauchy_sch"
lemma cauchy_schwartz:
  fixes u v
  shows "(dot u v)^2 \<le> ( dot u u)* (dot v v)"
  sorry
*)
(* Prove squared-cauchy-schwartz by expanding dot(u+v, u+v) \ge 0 *)
(* Prove equality in dot^2(u,v) = dot^2(u,u) dot^2(v,v) iff v = -cu for some c. Idea: look at dot(v + cu, v+cu).  *)
(*
lemma q:
  fixes u v
  shows "vplus (vplus u (smult (-1) v)) v = u"
  sorry

lemma cs_equality:
  fixes u v w
  assumes "v \<noteq> (0,0,0)"
  assumes "(dot u v)^2  = (dot u u) *  (dot v v)"
  defines "s \<equiv> smult ((dot u v)/(dot v v)) v"
  defines tdef: "t \<equiv> vplus u (smult (-1) s)"
  shows "\<exists> c . u = smult c v"
  sorry

lemma dot_cross_zero: 
  fixes ux uy uz vx vy vz::"real"
  assumes "u = (ux, uy, uz)"
  assumes "v = (vx, vy, vz)"
  assumes "n = (nx, ny, nz)"
  assumes "n = cross u v"
  shows "(dot u n = 0)" and "(dot v n = 0)"
  sorry
*)
\<close>
section \<open>Homogeneous Coordinates in the real projective plane\<close>
text\<open>
\hartshorne

{\textbf} Homogeneous coordinates in the real projective plane

We can give an analytic definition of the real projective plane
as follows. We consider the example given above of lines in $\mathbb R^33$.

A point of $S$ is a line through $O$.
We will represent the point $P$ of
$S$ corresponding to the line $l$ by
choosing any point $(x1, x2, x3)$ on
$l$ different from the point $(0, 0, 0)$.
The numbers $x1, x2, x3$ are ho-
mogeneous coordinates of $P$ . Any 
other point of $l$ has the coordinates
$(\<lambda>x1, \<lambda>x2, \<lambda>x3)$, where $\<lambda> \in \mathbb R, \<lambda> \ne 0$. 
Thus $S$ is the collection of triples $(x1, x2, x3)$ of real numbers, not all zero, 
and two triples $(x1, x2, x3)$ and $(x\<Zprime>1, x\<Zprime>2, x\<Zprime>3)$
represent the same point \<Leftrightarrow> \<exists>\<lambda> \<in> R such that
$x\<Zprime>i =\<lambda>xi$ for $i=1,2,3$.

Since the equation of a plane in $\mathbb R^3$ passing through $O$ is of the form $a1x1+a2x2+a3x3 =0$, $ ai$ not all $0$,
we see that this is also the equation of a line in $S$, in terms of the homogeneous coordinates.

subsection \<open>Isomorphism of projective planes\<close>
\textbf{Definition.} Two projective planes $S$ and $S\<Zprime>$ are isomorphic if there exists 
a one-to-one transformation $T : S \to S\<Zprime>$ which takes collinear points into collinear points.
\done
\spike
At this point you might be asking 'is that definition enough to show that if $k$ is a line of $S$, 
then $h = \{T(P) \mid P \in k \}$ is a line in $S'$? Couldn't $h$ potentially be just a \emph{subset} 
of some line in $S'$? If $S$ and $S'$ are finite sets, that can't happen, but if they're infinite, 
it certainly seems like a possibility. 

If $h$ really has to be a line, then this definition is a sweet one: in proving something's an isomorphism,
we need only show collinear points map to collinear points, not that whole lines map to whole lines. 

Anyhow, if you're asking this question, you're not alone. Not only did I wonder about this as I read 
it, but Zichen Gao did too: https://math.stackexchange.com/questions/3481844/is-isomorphic-between-projective-planes-actually-equivalence-relation
And Zichen provided an answer: yes, this definition really \emph{is} enough to guarantee lines are sent to lines. It goes like
this:

Suppose $f$ is a bijective mapping that takes collinear points in $S$ to collinear points in $S'$, 
we wish to prove that $f^{-1}$ also has this property, i.e. if $f$ takes $A, B, C$ to 
$A',B',C'$ which are collinear, then $A,B,C$ must be collinear:

If not, then the lines $AB$ and $BC$ intersect in only the point $B$. For any point 
$D$ on $AB$, since $A,B,D$ are collinear, the image of $D$ must lie on the line 
$A'B'C'$. For the same reason, so is the image of each point lying on the line $BC$. 
Since we know that the image of every point on $AB$ and $BC$ is on $A'B'C'$, we can 
use the property of $f$ again to see that the image of every line that intersects 
$AB$ and $BC$ at different points must also be on $A'B'C'$. However, through any point 
in $S$ except $A,B,C$, such a line exists. Hence we know that $f$ takes all the points 
in $S$ into the line $A'B'C'$, which is a contradiction to the fact that $f$ is a 
bijection, since every projective plane (here we indicate $S'$) must have  points 
which are not collinear.

We'll leave the formalization of that proof as a homework problem.
\done
\<close>
subsection \<open>Defining a quotient space for RP2\<close>

(* We've defined RP2, but we still need to show it's a projective plane, i.e., demonstrate 
axioms 1 - 4. Then we can move on to isomorphism with the completion of the affine plane. *)

    (* Define a type representing the cartesian product *)
definition projrel :: "(v3) \<Rightarrow> (v3) \<Rightarrow> bool"
  where "projrel x y \<longleftrightarrow> (x \<noteq> vector [0,0,0]) \<and> (y \<noteq> vector [0,0,0]) \<and> x$2 * y$1 = x$1 * y$2 \<and> x$3 * y$1 = y$3 * x$1 \<and> x$2 * y$3 = x$3 * y$2" 

find_theorems name: "vector_space"
lemma vt: 
  shows "(vector[1,0,0]::real^3) \<noteq> vector[0,0,0]" 
proof-
  show ?thesis 
  by (metis vector_3(1) zero_neq_one)
qed

lemma exists_projrel_refl: "\<exists>x. projrel x x" 
proof -
  have "projrel (vector [1,0,0]::real^3) (vector [1,0,0])"  by (simp add: projrel_def vt)
  then show ?thesis by blast
qed

lemma symp_projrel: "symp projrel"
proof -
  show ?thesis  unfolding symp_def projrel_def by (simp add: mult.commute)
qed

lemma transp_projrel: "transp projrel"
proof (rule transpI)
  fix x y z
  assume 1: "projrel x y"
  assume 2: "projrel y z"
  show  "projrel x z" sorry
qed

lemma part_equivp_projrel: "part_equivp projrel"
  by (rule part_equivpI [OF exists_projrel_refl symp_projrel transp_projrel])

text \<open>\nick\jackson\<close>
lemma smult_projrel: 
  fixes x y c
  assumes x_def: "x \<in> punctured_r_3"
  assumes y_def: "y \<in> punctured_r_3"
  assumes c_def: "c \<noteq> 0"
  assumes smult: "x = c *\<^sub>R y"
  shows "projrel x y"
proof -
  have h1: "x \<noteq> 0" using x_def punctured_r_3_def by auto
  have h2: "y \<noteq> 0" using y_def punctured_r_3_def by auto
  have h3: "x$2 * y$1 = x$1 * y$2" using assms by auto
  have h4: "x$3 * y$1 = y$3 * x$1" using assms by auto
  have h5: "x$2 * y$3 = x$3 * y$2" using assms by auto
  show "?thesis" using h1 h2 h3 h4 h5 projrel_def cross3_def cross_eq_self(2) by fastforce
qed
text \<open>\done\<close>

quotient_type rp2 = "v3" / partial: "projrel"
  morphisms Rep_Proj Abs_Proj
  using part_equivp_projrel .

find_theorems name: "rp2"
find_theorems name: "Quotient3_rp2"

lemma Domainp_cr_proj [transfer_domain_rule]: "Domainp cr_rp2 = (\<lambda>x .( (x \<noteq> vector [0,0,0]) \<and> projrel x x))"
  using projrel_def rp2.domain by presburger

lemma rep_P_nz:
  fixes P
  assumes a1: "P \<in> rp2_Points" 
  shows "Rep_Proj P \<noteq> vector [0, 0, 0]" 
using projrel_def Quotient_rel_rep Quotient_rp2 by metis

(* a remaining theorem from the "warmup" section, one that needs "projrel", and
needs rewriting using Cross3 rather than our (now-delete) version of 'cross' *)
unbundle cross3_syntax
lemma cross_nz:
  assumes "u \<in> punctured_r_3"
  assumes "v \<in> punctured_r_3"
  assumes "\<not> projrel u v"
  defines s_def: "s \<equiv> u \<times> v"
  shows "s \<in> punctured_r_3"
  sorry
(*proof (rule ccontr)
  assume "\<not> s \<in> punctured_r_3"
  then consider (snotr3) "s \<notin> (UNIV::(v3 set))" | (sz) "s \<in> {0::v3}" 
    using punctured_r_3_def by auto
  then show False
  proof cases
    case snotr3 
    then show False using assms s_def cross3_def by auto
  next
    case sz
    then show False using assms s_def
  sorry*)

lemma old_projrel:
  assumes "u \<in> punctured_r_3"
  assumes "v \<in> punctured_r_3"
  shows "(projrel u v) \<longleftrightarrow> (\<exists> t::real . u =  t *\<^sub>R  v)"
proof -
  assume ah: "projrel u v"
  have "\<exists>t. u = t *\<^sub>R v"
  proof (cases "v$1 = 0")
    case True
    then show ?thesis sorry
  next
    case False
    have "u$1 * v$2 = u$2 * v$1" using assms projrel_def ah by simp
    then have "v$2 = (u$2/u$1) * v$1" using False 
    by (smt (verit) ah divide_eq_0_iff exhaust_3 nonzero_mult_div_cancel_left projrel_def
        times_divide_eq_left vec_eq_iff vector_3(1,2,3))
    then show ?thesis sorry
  qed

(* We've defined RP2, but we still need to show it's a projective plane, i.e., demonstrate 
axioms 1 - 4. Then we can move on to isomorphism with the completion of the affine plane. *)

(* RP2 is a projective plane *)

lemma projrel_scalar: 
  shows "\<lbrakk>projrel P Q\<rbrakk> \<Longrightarrow> \<exists> s . s \<noteq> (0::real) \<and> P = s *\<^sub>R Q"
    sorry
  
definition rp2_Points where
"rp2_Points = (UNIV::rp2 set)" 

definition rp2_Lines where
"rp2_Lines = (UNIV::rp2 set)"

lemma good_lift1:
  fixes x
  assumes "x \<in> punctured_r_3"
  shows "\<not> (projrel x 0)" 
  sorry

definition rp2_incid_rep where
"rp2_incid_rep P k = (P \<bullet> k = 0)"

lift_definition rp2_incid::"rp2 \<Rightarrow> rp2 \<Rightarrow> bool"
is "\<lambda> P k . (P \<bullet> k = 0)"
proof -
  fix P1 P2 k1 k2
  assume a1: "projrel P1 P2"
  assume a2: "projrel k1 k2"
  show "(P1 \<bullet> k1 = 0) = (P2 \<bullet> k2 = 0)"
    sorry
  qed

(*
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k . k \<in> Lines \<and> P \<lhd> k  \<and> Q \<lhd>  k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = { P . (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
*)

definition join :: "real^3 \<Rightarrow> real^3 \<Rightarrow> real^3"
  where
  "join \<equiv> \<lambda>P Q . (if P \<times> Q = 0 then vector[0,0,1] else P \<times> Q)"


lift_definition Join :: "real^3 \<Rightarrow> real^3 \<Rightarrow> rp2"
  is "\<lambda>P Q. join P Q"
proof -
  fix P Q
  show "projrel (join P Q)
        (join P Q)" unfolding projrel_def join_def
  by (smt (verit) prod.inject smult_ident)
qed

lemma rp2_P1a:
  fixes P Q
  assumes a1: "P \<in> rp2_Points" 
  assumes a2: "Q \<in> rp2_Points"
  assumes a3: "P \<noteq> Q"
  shows "(\<exists>k . k \<in> rp2_Lines \<and> rp2_incid P  k  \<and>  rp2_incid Q  k)"
  sorry

(* TO DO: To show uniqueness, we have to show (for P,Q in punctured_r_3 and P and Q not proj_rel, 
that if h is orthog to P and Q, then h is a nonzero multiple of the cross product. Ugh. Ugly algebra ahead *)
lemma rp2_P1b_helper:
  fixes P Q k n
  assumes a1: "P \<in> punctured_r_3" 
  assumes a2: "Q \<in>  punctured_r_3"
  assumes a3: "\<not> projrel P Q"
  assumes a4: "n = P \<times> Q"
  assumes a5: "k \<in>  punctured_r_3"
  assumes k_facts: "(P \<bullet> k = 0)  \<and> (Q \<bullet> k = 0)" 
  shows "\<exists>c . (c \<noteq> 0) \<and> k = c *\<^sub>R n"
  sorry

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
  obtain kvec where hkrep: "kvec = Rep_Proj k" and hkpr3: "kvec \<in> punctured_r_3" and hknz: "kvec \<noteq> 0" 
    using cross3_def cross_zero_left punctured_r_3_def rep_P_nz by fastforce
  obtain nvec where hnrep: "nvec = Rep_Proj n" and hnpr3: "nvec \<in> punctured_r_3" and hknz: "nvec \<noteq> 0" 
    using cross3_def cross_zero_left punctured_r_3_def rep_P_nz by fastforce
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

lemma ar: "Abs_Proj (Rep_Proj x) = x"
  by (meson Quotient_abs_rep Quotient_rp2)

lemma ra: 
  fixes x
  assumes "(x \<noteq> (0,0,0)) \<and> projrel x x"
  shows "projrel (Rep_Proj (Abs_Proj x)) x" 
  by (simp add: Quotient3_rp2 assms rep_abs_rsp_left) 

lemma rp2_P2:
  fixes m k 
  assumes a1: "m \<in> rp2_Lines" 
  assumes a2: "k \<in> rp2_Lines"
  assumes a3: "m \<noteq> k"
  shows "(\<exists>P . P \<in> rp2_Points \<and> rp2_incid P  m  \<and>  rp2_incid P  k)"
  sorry

lemma rp2_P3:
  shows "\<exists>P Q R. P \<in> rp2_Points \<and> Q \<in>  rp2_Points \<and> R \<in>  rp2_Points \<and> 
          P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> 
          \<not> (\<exists>k \<in> rp2_Lines . rp2_incid P k \<and> rp2_incid Q k \<and> rp2_incid R k)"
  sorry

lemma rp2_P4:
  fixes k
  fixes U
  assumes "k \<in> rp2_Lines"
  assumes "U = {X . X \<in> rp2_Points \<and> rp2_incid X k}"
  shows "\<exists>P Q R. P \<in> U \<and> Q \<in> U \<and> R \<in> U \<and> distinct [P,Q,R]"
  sorry

(*
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k . k \<in> Lines \<and> P \<lhd> k  \<and> Q \<lhd>  k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = { P . (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
*)

theorem analytic_rp2:
  shows "projective_plane2 rp2_Points rp2_Lines rp2_incid"
  sorry

(* also needed: an interpretation claim like those for A4 and A2 *)

(*
proof (unfold_locales)
  ...
*)

theorem projectivisation_of_A2:
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> A2Points)} \<union> {Ideal t | k t . 
                  ((k \<in> A2Lines) \<and> (t = affine_plane_data.line_pencil  A2Points  A2Lines ( a2incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in>  A2Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes pm: \<open>pincid =  mprojectivize (a2incid)\<close>
  assumes ap: "affine_plane  A2Points  A2Lines a2incid a2join a2find_parallel"
  shows   "projective_plane2 pPoints pLines pincid"
  using "Chapter1-1.projectivization_is_projective" A2_affine assms(1,2,3) by blast

end


