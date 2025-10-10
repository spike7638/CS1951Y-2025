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
  obtain a b c where fu: "u = (vector[(a::real), b, c]::v3)"   using forall_vector_3 by fastforce
  obtain x y z where fv: "v = (vector[(x::real), y, z]::v3)"   using forall_vector_3 by fastforce
  have "\<exists>t. u = t *\<^sub>R v"
  proof (cases "a = 0")
    case True
    then show ?thesis sorry
  next
    case False
    have zs: "(a*z - c*x, a*y - b*x, b*z - c*y) = (0,0,0)" using assms projrel_def ah fu fv by simp
    have ainv: "(1/a) * a = 1" using False by simp
    have "z = (1/a)*c * x" using zs ainv
      by (smt (verit, ccfv_SIG) mult_cancel_right2 prod.inject times_divide_eq_left)
    then have f3: "z = (x/a) * c" by argo
    have f2: "y = (x/a) * b"
      by (smt (verit, best) False Pair_inject mult.commute nonzero_mult_div_cancel_left
        times_divide_eq_left zs)
    have f1: "x = (x/a) * a" using zs ainv False by simp
    have "[x, y, z] = [(x/a)*a, (x/a)*b, (x/a)*c]" using f1 f2 f3 by presburger
    fix s
    have "vector[s*a, s*b, s*c] = (s::real)  *\<^sub>R vector[a, b, c]" by sledgehammer
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
  shows "\<exists>c . (c \<noteq> 0) \<and> k = scalar_mult c n"
  sorry

(* sorry I've broken your proof, Nick -- Spike *)
text \<open>\nick\<close>
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
   obtain Qvec where hPrep: "Qvec = Rep_Proj Q" and hPpr3: "Qvec \<in> punctured_r_3" and hPnz: "Qvec \<noteq> 0" 
    using cross3_def cross_zero_left punctured_r_3_def rep_P_nz by fastforce
  have h1: "\<not> projrel (Px, Py, Pz) (Qx, Qy, Qz)" 
    using hPrep hQrep Quotient_rel_rep Quotient_rp2 a5 by metis
  let ?crossPQ = "(Px, Py, Pz) \<times> (Qx, Qy, Qz)"
  obtain kx ky kz where hkrep: "(kx, ky, kz) = Rep_Proj k" 
    and hknz: "(kx, ky, kz) \<noteq> (0, 0, 0)" 
    and hkpr3: "(kx, ky, kz) \<in> punctured_r_3" 
    using rep_P_nz a3 prod_cases3 Diff_iff UNIV_I empty_iff insert_iff punctured_r_3_def by metis
  obtain nx ny nz where hnrep: "(nx, ny, nz) = Rep_Proj n"
    and hknz: "(nx, ny, nz) \<noteq> (0, 0, 0)" 
    and hnpr3: "(nx, ny, nz) \<in> punctured_r_3" 
    using rep_P_nz a4 prod_cases3 Diff_iff UNIV_I empty_iff insert_iff punctured_r_3_def by metis
  have h2: "(dot (Px, Py, Pz) (kx, ky, kz) = 0) \<and> (dot (Qx, Qy, Qz) (kx, ky, kz) = 0)"
    using hPrep hQrep hkrep k_facts rp2_incid.rep_eq by auto
  have h3: "(dot (Px, Py, Pz) (nx, ny, nz) = 0) \<and> (dot (Qx, Qy, Qz) (nx, ny, nz) = 0)"
    using hPrep hQrep hnrep n_facts rp2_incid.rep_eq by auto
  let ?Pxyz = "(Px, Py, Pz)" let ?Qxyz = "(Qx, Qy, Qz)" let ?kxyz = "(kx, ky, kz)" let ?nxyz = "(nx, ny, nz)"
  obtain c_k where hck: "(c_k \<noteq> 0) \<and> ?crossPQ = scalar_mult c_k ?kxyz"
    using h1 h2 rp2_P1b_helper[of ?Pxyz ?Qxyz ?crossPQ ?kxyz] hPpr3 hQpr3 hkpr3 Quotient3_rel Quotient3_rp2 dot_non_degenerate dot_scalar hknz mult_zero_left projrel_def 
     by (smt (verit, del_insts) Diff_iff cross_nz insert_iff punctured_r_3_def) (*why is this so complicated?*)
  obtain c_n where hcn: "(c_n \<noteq> 0) \<and> ?crossPQ = scalar_mult c_n ?nxyz"
    using h1 h3 rp2_P1b_helper[of ?Pxyz ?Qxyz ?crossPQ ?nxyz] hPpr3 hQpr3 hnpr3 Quotient3_rel Quotient3_rp2 dot_non_degenerate dot_scalar hknz mult_zero_left projrel_def 
    by (smt (verit, del_insts) Diff_iff cross_nz insert_iff punctured_r_3_def) (*why is this so complicated?*)
  have h4: "((c_n/c_k) \<noteq> 0) \<and> ?kxyz = scalar_mult (c_n/c_k) ?nxyz" using hck hcn by (smt (verit) divide_eq_0_iff divide_self_if mult.commute scalar_mult_assoc scalar_mult_ident
      times_divide_eq_left)
  show ?thesis using h4 Quotient3_rel_rep Quotient3_rp2 hkrep hnrep projrel_def by (metis (no_types, lifting))
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


