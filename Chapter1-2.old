theory "Chapter1-2"
  imports Complex_Main "Chapter1-1" "HOL-Analysis.Cross3"

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
definition punctured_r_3 where "punctured_r_3 = (UNIV::(v3 set)) - {0::v3}"

text\<open>
(* STUDENTS: click on the Cross3.thy file that's imported above to see that cross and dot product
are defined already, with infix notation ready to use! *)
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

(* We're going to need cross and dot-products *)
unbundle cross3_syntax

definition projrel :: "(v3) \<Rightarrow> (v3) \<Rightarrow> bool"
  where "projrel x y \<longleftrightarrow> (x \<noteq> vector [0::real,0,0]) \<and> (y \<noteq> vector [0::real,0,0]) \<and> (x \<times> y) = (0::v3)" 

text\<open>\spike Current definition of projective relation is that the cross product is zero; 
former definition was that there's a nonzero constant c such that u = cv. Let's start
with the big theorem that these two things are equivalent\<close>
lemma alt_projrel:
  assumes "u \<in> punctured_r_3"
  assumes "v \<in> punctured_r_3"
  shows "(projrel u v) \<longleftrightarrow> (\<exists> t::real . u =  t *\<^sub>R  v)"
proof 
  assume ah1: "(\<exists> t::real . u =  t *\<^sub>R  v)"
  show "projrel u v"
  proof -
    have "projrel u v = (u \<times> v = (0::v3))" using assms projrel_def punctured_r_3_def cross3_def by auto
    also have "... = True" using ah1 cross_mult_left by auto
    finally show ?thesis by auto
  qed
  next
    assume ah2: "projrel u v"
    have "u \<times> v = (0::v3)" using ah2 assms projrel_def punctured_r_3_def cross3_def by auto
    then have "collinear {0, u, v}" using cross_eq_0 by auto
    then obtain w where col_fact: "\<forall>x\<in>{0, u, v}. \<forall>y\<in>{0, u, v}. \<exists>c. x - y = c *\<^sub>R w" 
      using collinear_def by blast
    then obtain r where rf: "u - 0 = r *\<^sub>R w" by blast
    obtain s where sf: "v - 0 = s *\<^sub>R w" using col_fact by blast
    have uw: "u = r *\<^sub>R w" using rf by simp
    have vw: "v = s *\<^sub>R w" using sf by simp
    have "s \<noteq> 0" using vw assms by (simp add: punctured_r_3_def)
    then have "u = (r/s) *\<^sub>R v" using uw vw by simp
    then show "(\<exists>t::real. u = t *\<^sub>R v)" by blast
  qed
text \<open>\done\<close>

lemma vt:
  shows "(vector[1,0,0]::real^3) \<noteq> vector[0,0,0]" 
proof-
  show ?thesis 
  by (metis vector_3(1) zero_neq_one)
qed

lemma exists_projrel_refl: "\<exists>x. projrel x x" 
proof -
  have "projrel (vector [1,0,0]::real^3) (vector [1,0,0])" by (simp add: projrel_def vt)
  then show ?thesis by blast
qed

lemma symp_projrel: "symp projrel"
proof -
  show ?thesis  unfolding symp_def projrel_def  by (metis cross_refl cross_skew)
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

text \<open>\hadi\<close>
lemma cross_nz:
  assumes "u \<in> punctured_r_3"
  assumes "v \<in> punctured_r_3"
  assumes "\<not> projrel u v"
  defines s_def: "s \<equiv> u \<times> v"
  shows "s \<in> punctured_r_3"
  using assms cross3_def projrel_def punctured_r_3_def s_def by auto
(*proof (rule ccontr)
  assume cd: "\<not> (s \<in> punctured_r_3)"
  show False
  proof -
    obtain x1 x2 x3 y1 y2 y3 where uv_coords: "u = vector[x1,x2,x3] 
      \<and> v = vector[y1,y2,y3]" using forall_vector_3 by fastforce
    have sz: "s = vector[0,0,0]" 
      using cd punctured_r_3_def cross3_def cross_zero_right by auto
    have "vector[x1,x2,x3] \<noteq> c *\<^sub>R vector[y1,y2,y3]" for c 
      using assms cd sz projrel_def cross3_def cross_zero_right by fastforce
    consider 
    (uz) "(x1,x2,x3) = (0,0,0)" 
    | (vz) "(y1,y2,y3) = (0,0,0)" 
      using assms sz cd projrel_def DiffI UNIV_I punctured_r_3_def singletonD by metis
    then show ?thesis
    proof (cases)
      case uz
      then show ?thesis using assms cd sz uv_coords by auto
    next
      case vz
      then show ?thesis using assms cd sz uv_coords by auto
    qed
  qed
qed*)
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
  show "(P1 \<bullet> k1 = 0) = (P2 \<bullet> k2 = 0)"
  proof
    have p1p2rel: "(P1 \<noteq> vector [0::real,0,0]) \<and> (P2 \<noteq> vector [0::real,0,0]) 
      \<and> (P1 \<times> P2) = (0::v3)" using a1 projrel_def by auto
    have k1k2rel: "(k1 \<noteq> vector [0::real,0,0]) \<and> (k2 \<noteq> vector [0::real,0,0]) 
      \<and> (k1 \<times> k2) = (0::v3)" using a2 projrel_def by auto
    show "(P1 \<bullet> k1 = 0) \<Longrightarrow> (P2 \<bullet> k2 = 0)" 
    proof -
      assume b1: "P1 \<bullet> k1 = 0"
      show "P2 \<bullet> k2 = 0"
      proof -
        have "P2 \<bullet> k1 = 0" using b1 p1p2rel Lagrange cross3_def diff_zero inner_commute 
          mult_zero_right scaleR_eq_0_iff zero_index by (metis (no_types))
        then show ?thesis using Lagrange cross3_def diff_zero k1k2rel
          mult_not_zero scaleR_eq_0_iff vector_3 by (metis (no_types))
      qed
    qed
    show "(P2 \<bullet> k2 = 0) \<Longrightarrow> (P1 \<bullet> k1 = 0)" 
    proof -
      assume b2: "P2 \<bullet> k2 = 0"
      show "P1 \<bullet> k1 = 0"
      proof -
        have "P1 \<bullet> k2 = 0" using b2 p1p2rel Lagrange cross3_def diff_zero inner_commute 
          mult_zero_right scaleR_eq_0_iff zero_index cross_skew by (metis (no_types))
        then show ?thesis using Lagrange cross3_def diff_zero k1k2rel cross_skew
          mult_not_zero scaleR_eq_0_iff vector_3 by (metis (no_types))
      qed
    qed
  qed
qed
text \<open>\done\<close>

(*
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k . k \<in> Lines \<and> P \<lhd> k  \<and> Q \<lhd>  k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = { P . (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
*)

definition join :: "real^3 \<Rightarrow> real^3 \<Rightarrow> real^3"
  where "join \<equiv> \<lambda>P Q. (if P \<times> Q = 0 then vector[0,0,1] else P \<times> Q)"

text \<open>\hadi\<close>
lift_definition Join :: "real^3 \<Rightarrow> real^3 \<Rightarrow> rp2" is "\<lambda>P Q. join P Q" 
  using cross3_def cross_refl vector_3(3) zero_index zero_neq_one 
  unfolding projrel_def join_def by (metis (no_types))
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma obtain_coords:
  fixes P
  assumes "P \<in> rp2_Points"
  shows "\<exists>Px Py Pz. vector[Px, Py, Pz] = Rep_Proj P 
    \<and> vector[Px, Py, Pz] \<noteq> ((vector[0,0,0])::v3)" 
proof -
  obtain v::v3 where vdef: "v \<in> punctured_r_3 \<and> Rep_Proj P = v" using cross3_def 
    exists_projrel_refl projrel_def punctured_r_3_def rep_P_nz by fastforce
  have vnz: "v \<noteq> ((vector[0,0,0])::v3)" 
    using vdef cross3_def cross_zero_right punctured_r_3_def by auto
  obtain Px Py Pz where "v = vector[Px, Py, Pz]" using forall_vector_3 by fastforce
  then show ?thesis using vdef vnz by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma rp2_P1a:
  fixes P Q
  assumes a1: "P \<in> rp2_Points" 
  assumes a2: "Q \<in> rp2_Points"
  assumes a3: "P \<noteq> Q"
  shows "(\<exists>k. k \<in> rp2_Lines \<and> rp2_incid P k \<and> rp2_incid Q k)"
proof -
  obtain Px Py Pz Qx Qy Qz where pq_coords: "vector[Px, Py, Pz] = Rep_Proj P 
    \<and> vector[Px, Py, Pz] \<noteq> ((vector[0,0,0])::v3) \<and> vector[Qx, Qy, Qz] = Rep_Proj Q 
    \<and> vector[Qx, Qy, Qz] \<noteq> ((vector[0,0,0])::v3)" using assms obtain_coords by blast
  let ?k = "Join (vector[Px, Py, Pz]) (vector[Qx, Qy, Qz])"
  let ?n = "join (vector[Px, Py, Pz]) (vector[Qx, Qy, Qz])"
  have nneqz: "vector[Px, Py, Pz] \<times> vector[Qx, Qy, Qz] \<noteq> vector[0,0,0]" using a3 
    Quotient_rel_rep [of projrel] Quotient_rp2 cross3_def cross_refl projrel_def 
    vector_3 pq_coords by (smt (verit))
(*proof -
    obtain f :: "rp2 \<Rightarrow> real" and g :: "rp2 \<Rightarrow> real" 
      and h :: "rp2 \<Rightarrow> real" where f1: "\<forall>x. (vector[0, 0, 0]::(real, 3) vec) 
      \<noteq> vector[f x, g x, h x] \<and> Rep_Proj x = vector [f x, g x, h x] 
      \<or> x \<notin> rp2_Points" using obtain_coords by metis
    have f2: "vector[0, 0, 0] = (0::v3)" 
      using cross3_def cross_zero_right by auto
    have f3: "\<forall>v. (v::(real, 3) vec) \<in> UNIV" by auto
    then have f4: "Rep_Proj Q \<in> punctured_r_3" using f1 f2 a2 punctured_r_3_def 
      insert_Diff_single insert_iff by metis
    have "Rep_Proj P \<in> punctured_r_3" using f1 f2 f3 a1 insert_Diff_single 
      insert_iff punctured_r_3_def by metis
    then show ?thesis using a3 f2 f4 Quotient_rel_rep Quotient_rp2 cross_nz
      p_coords q_coords punctured_r_3_def insert_iff Diff_iff by metis
  qed*)
  then have "?n = vector[Px, Py, Pz] \<times> vector[Qx, Qy, Qz]" using join_def 
    cross3_def cross_zero_right zero_index by (smt (verit))
  then have "rp2_incid P ?k \<and> rp2_incid Q ?k" using nneqz pq_coords 
    Quotient3_def Quotient3_rp2 cross_refl projrel_def
    by (smt (verit) Join.abs_eq rp2_incid.abs_eq dot_cross_self)
  then show ?thesis using rp2_Lines_def by auto
qed
text \<open>\done\<close>

(* TO DO: To show uniqueness, we have to show (for P,Q in punctured_r_3 and P and Q not proj_rel, 
that if h is orthog to P and Q, then h is a nonzero multiple of the cross product. Ugh. Ugly algebra ahead *)
lemma rp2_P1b_helper:
  fixes P Q k n
  assumes P_def: "P \<in> punctured_r_3" 
  assumes Q_def: "Q \<in>  punctured_r_3"
  assumes PQ_nprojrel: "\<not> projrel P Q"
  assumes n_def: "n = P \<times> Q"
  assumes k_def: "k \<in> punctured_r_3"
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
(* need definition of isomorphism, and proof that RP2A is isomorphism to RP2P; 
place these Chapter 1-3. *)
end