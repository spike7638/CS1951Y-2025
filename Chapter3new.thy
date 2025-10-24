theory Chapter3new
  imports Main  
         "HOL-Algebra.Group" 
         "HOL-Algebra.Bij" 
         "HOL-Analysis.Cartesian_Space"
         "HOL-Analysis.Finite_Cartesian_Product"
         "HOL-Analysis.Determinants"
begin

section\<open>Digression on Groups and Automorphisms\<close>
text \<open>
\begin{hartshorne}
\defn[group]. A \term{group} is a set $G$ together with a binary operation, called multiplication,
written $ab$ such that
\begin{itemize}
\item[G1] (\term{Associativity}) For all $a,b,c\in G, (ab)c = a(bc)$.
\item[G2] There exists an element $1 \in G$ such that $a \cdot 1 = 1 \cdot a = a \cdot 1 = a$ for all $a$.
\item[G3] For each $a \in G$, there exists an element $a^{-1} \in G$ such that $aa^{-1} = a^{-1}a = 1$.
\end{itemize}
The element $1$ is called the \term{identity}, or \term{unit}, element. The element $a^{-1}$ is 
called the \term{inverse} of $a.$ Note that in general the product $ab$ may be different from $ba.$
However, we say that the group $G$ is \term{abelian,} or \term{commutative,} if
G4 $\forall a, b \in G, ab = ba.$


Examples. 

1. Let $S$ be any set, and let $G$ be the set of permutations of the set $S.$
A \term{permutation} is a 1–1 mapping of a set $S$ onto $S.$ If $g_1, g_2 \in G$
are two permutations, we define $g_1 g_2 \in G$ to be the permutation obtained by 
performing first $g_2$, then $g_1$, i.e., if $x \in S$, then
$$
(g_1g_2)(x) = g_1(g_2(x)).
$$

2. Let $C$ be a configuration, and let $G$ be the set of \term{automorphisms} of $C$,
i.e., the set of those permutations of $C$ which send lines into lines. 
Again we define the product $g_1g_2$ of two automorphisms $g_1,g_2$, by performing 
$g_2$ first, and then $g_1.$ This group is written $\operatorname{Aut} C$.

\defn [homomorphism] A \term{homomorphism} $\phi: G_1 \to G_2$ of one group to another is a 
mapping of the set $G_1$ to the set $G_2$ such that $\phi(ab) = \phi(a) \phi(b)$ for each $a, b \in G_1$. 

An \term{isomorphism} of one group with another is a homomorphism which is
1–1 and onto.

\defn [subgroup]  Let $G$ be a group. A subgroup of $G$ is a non-empty subset
$H \subseteq G,$ such that for any $a,b \in H,$ $ab \in H$ and $a^{-1} \in H.$
\end{hartshorne}
 \<close>

(* In Isabelle, a group is defined as a monoid with inverses *)

definition
  Units :: "_ => 'a set"
  \<comment> \<open>The set of invertible elements\<close>
  where "Units G = {y. y \<in> carrier G \<and> (\<exists>x \<in> carrier G. x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub> \<and> y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>)}"

(* The above says that Units is a function which, given some algebraic structure (presumably a group
   or a monoid), returns the set of units (invertible elements) in that structure *)

(* Note that \<^bsub>G\<^esub> denotes that this is the operation in G. *)

(* locale monoid =
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

(* Here "<=" means subset *)

(* Subgroups are defined in a similar way to Hartshorne: *)

(* locale subgroup =
  fixes H and G (structure)
  assumes subset: "H \<subseteq> carrier G"
    and m_closed [intro, simp]: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> H"
    and one_closed [simp]: "\<one> \<in> H"
    and m_inv_closed [intro,simp]: "x \<in> H \<Longrightarrow> inv x \<in> H" *)

(* Note that the condition "1 \in H" is equivalent to the group being non-empty *)

(* The bijections on a set form a group, with the operation being function composition and
   the neutral element  being the identity function: *)

(* definition
  Bij :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) set"
    \<comment> \<open>Only extensional functions, since otherwise we get too many.\<close>
  (* An extensional function on S is a function defined on S that is undefined outside of S.*) 
  where "Bij S = extensional S \<inter> {f. bij_betw f S S}" *)

(* The set of automorphisms of a group is the set of homomorphisms from the group to itself
   that are also bijections... *)

(* definition
  auto :: "('a, 'b) monoid_scheme \<Rightarrow> ('a \<Rightarrow> 'a) set"
  where "auto G = hom G G \<inter> Bij (carrier G)" *)

(*... and the group structure on this set is the same as for a BijGroup. *)

(*definition
  AutoGroup :: "('a, 'c) monoid_scheme \<Rightarrow> ('a \<Rightarrow> 'a) monoid"
  where "AutoGroup G = BijGroup (carrier G) \<lparr>carrier := auto G\<rparr>" *)



(*In Isabelle, a homomorphism between G and H is an element of the set hom G H, defined below. *)

(* definition
  hom :: "_ => _ => ('a => 'b) set" where
  "hom G H =
    {h. h \<in> carrier G \<rightarrow> carrier H \<and>
      (\<forall>x \<in> carrier G. \<forall>y \<in> carrier G. h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y)}" *)

(*An isomorphism between groups G and H is defined as a homomorphism that is a bijection. *)

(* definition iso :: "_ => _ => ('a => 'b) set"
  where "iso G H = {h. h \<in> hom G H \<and> bij_betw h (carrier G) (carrier H)}" *)


subsection\<open>Automorphisms of the real projective plane\<close>
text \<open>\begin{hartshorne}Here we study another important example of the automorphisms of a pro-
jective plane. Recall that the real projective plane is defined as follows: A point
is given by homogeneous coordinates $(x_1 , x_2 , x_3 )$. That is, a triple of real num-
bers, not all zero, and with the convention that $(x_1 , x_2 , x_3)$ and $(\lambda x_1, \lambda x_2, \lambda x_3)$
represent the same point, for any $\lambda \ne 0$, $\lambda \in \Bbb R.$ 
A \term{line} is the set of points which satisfy an equation of the form 

\begin{equation*}
a_1 x_1 + a_2 x_2 + a_3 x_3 = 0,
\end{equation*}

$a_i \in \Bbb R,$ not all zero. \end{hartshorne}\<close>

subsubsection\<open>Brief review of matrices\<close>
text \<open>\begin{hartshorne}
A $n \times n$ \term{matrix} of real numbers is a collection of $n^2$ real numbers, indexed
by two indices, say $i$, $j$, each of which may take values from 1 to $n$. Hence
$A = {a_{11}, a_{12}, \ldots , a_{21}, a_{22}, \ldots , a_{n1}, a_{n2}, \ldots , a_{nn}}.$ The matrix is
usually written in a square:
$$
\begin{pmatrix}
a_{11} & a_{12} & \hdots & a_{1n} \\
a_{21} & a_{22} & \hdots & a_{2n} \\
\vdots & \vdots & \ddots & \vdots \\
a_{n1} & a_{n2} & \hdots & a_{nn}
\end{pmatrix} 
$$
Here the first subscript determines the row, and the second subscript determines
the column.

The product of two matrices $A = (a_{ij})$ and $B = (b_{ij})$ (both of order $n$) is
defined to be

\begin{equation*}
  A \cdot B = C
\end{equation*}

where $C = (c_{ij})$ and

\begin{equation*}
  c_{ij} = \sum_{k=1}^n a_{ik} b_{kj}.
\end{equation*}

\[
\begin{pmatrix}
a_{i1} & \hdots & a_{in} \\
\end{pmatrix}
\begin{pmatrix}
b_{1j} \\
\vdots \\
b_{nj} \\
\end{pmatrix}
= ( c_{ij} )
\]


\[c_{ij} = a_{i1}b_{1j} + a_{i2}b_{2j} + \hdots  + a_{in}b_{nj}\]

There is also a function \textbf{determinant}, from the set of $n \times n$ matrices to $\mathbb{R}$,
which is characterized by the following two properties:

\textbf{D1} \textit{If A, B are two matrices}

\[ det(A \cdot B) = det A \cdot det B\]

\textbf{D2} \textit{For each $a \in R$, let $C(a) = \ldots $}

Note incidentally that the identity matrix $I = C(1)$ behaves as a multiplicative identity. 
One can prove the following facts:
\begin{enumerate}
\item $(A \cdot B) \cdot C = A \cdot (B \cdot C)$, i.e. multiplication of matrices is associative. 
(In general it is not commutative.)

\item A matrix $A$ has a multiplicative inverse $A^{-1}$
if and only if $det A \neq 0$.

Hence the set of $n \times n$ matrices $A$ with $\det A \neq 0$ forms a group under multiplication, 
denoted by GL$(n, \mathbb{R})$. 
\item Let $A = (a_{ij})$ be a matrix, and consider the set of simultaneous linear
equations
\begin{align}
a_{11}x_1 + a_{12}x_2 + \hdots + a_{1n}x_n &= b_1 \\
a_{21}x_1 + a_{22}x_2 + \hdots + a_{2n}x_n &= b_2 \\
\vdots &= \vdots\\
a_{n1}x_1 + a_{n2}x_2 + \hdots + a_{nn}x_n &= b_n
\end{align}
If $\det A \neq 0$, then this set of equations has a solution. Conversely, if this
set of equations has a solution for all possible choices of $b_1, \hdots, b_n$ then
$\det A \neq 0$.
\end{enumerate}
For proofs of these statements, refer to any book on algebra. We will take
them for granted, and use them without comment in the rest of the course. One
can prove easily that 3 follows from 1 and 2. Because to say $x_1, \hdots, x_n$ are a
solution of that system of linear equations is the same as saying that

\[
A \cdot
\begin{pmatrix}
x_1 \\
x_2 \\
\vdots \\
x_n \\
\end{pmatrix}
=
\begin{pmatrix}
b_1 \\
b_2 \\
\vdots \\
b_n \\
\end{pmatrix}
\]
Now let $A = (a_{ij})$ be a $3 \times 3$ matrix of real numbers, and let $\pi$ be the real
projective plane, with homogeneous coordinates $x_1, x_2, x_3$. We define a transformation $T_A$ of $\pi$ as follows: 
The point $(x_1, x_2, x_3)$ goes into the point
\[T_A(x_1, x_2, x_3) = (x_1', x_2', x_3')\]
where
\[x_1' = a_{11}x_1 + a_{12}x_2 + a_{13}x_3\]
\[x_2' = a_{21}x_1 + a_{22}x_2 + a_{23}x_3\]
\[x_3' = a_{31}x_1 + a_{32}x_2 + a_{33}x_3\]
\end{hartshorne}
\<close>

(*
CONTINUES WITH DOT-PRODUCT DEFINITION OF MATRIX MULTIPLICATION
*)

(* The next part will build up to the proof that every invertible 3x3 real matrix
   induces an automorphism of the real projective plane.
   First, we need some definitions, culminating in one that defines what it means
   to be an automorphism of the real projective plane. *)


(* Note: use vector_3 for index stuff... *)

type_synonym m33 = "real^3^3"
type_synonym v3 = "real^3"

definition zvec
  where "zvec = vector[0::real, 0, 0]"

definition map_vec where
"map_vec f g v = vec_lambda (map_fun g f (vec_nth v))"
functor map_vec
  unfolding map_vec_def
  using eq_id_iff
  by fastforce+

definition projrel :: "v3 \<Rightarrow> v3 \<Rightarrow> bool"
  where "projrel = (\<lambda>x y. (x \<noteq> zvec \<and> y \<noteq> zvec) \<and>  (\<exists> (t::real) . t \<noteq> 0 \<and> (x =  t *\<^sub>R y)))"

lemma exists_projrel_refl: "\<exists>x. projrel x x"
proof -
  have "vector[1, 0, 0] =  1 *\<^sub>R vector[1, 0, 0]" by simp
  then show ?thesis using projrel_def scaleR_one zero_neq_one by metis
qed

lemma nonzero_inverse: "((c::real) \<noteq> 0) \<Longrightarrow> ((1/c) \<noteq> 0)" by simp

lemma divide_through: "((c::real) \<noteq> 0) \<Longrightarrow> (a = c*q) \<Longrightarrow> ((1/c)*a = q)" by simp

lemma symp_projrel: "symp projrel"
  by (metis divideR_right projrel_def scaleR_left.zero sympI)

lemma transp_projrel: "transp projrel"
proof (rule transpI)
  show "\<And>x y z. projrel x y \<Longrightarrow> projrel y z \<Longrightarrow> projrel x z" 
  by (smt (verit) projrel_def scaleR_eq_0_iff vector_space_assms(3))
qed

lemma part_equivp_projrel: "part_equivp projrel"
  by (rule part_equivpI [OF exists_projrel_refl symp_projrel transp_projrel])

quotient_type rp2 = v3 / partial: "projrel"
  morphisms Rep_Proj Abs_Proj
  using part_equivp_projrel .

lemma Domainp_cr_proj [transfer_domain_rule]: "Domainp cr_rp2 = (\<lambda>x .( (x \<noteq> zvec) \<and> projrel x x))"
  using projrel_def rp2.domain by presburger
(*  by (simp add: projrel_def rp2.domain_eq) *)

definition not_all_zero :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"
  where "not_all_zero x y z  \<longleftrightarrow> x \<noteq> 0 \<or> y \<noteq> 0 \<or> z \<noteq> 0"

lemma vect_zero_eqv2:
  fixes x :: v3
  shows "x = 0 \<longleftrightarrow> x$1 = 0 \<and> x$2 = 0 \<and> x$3 = 0"
  by (metis (mono_tags, lifting) exhaust_3 vec_eq_iff zero_index)

lemma vect_zero_eqv [simp]: 
  fixes x y z :: real
  shows "vector[x, y, z] = (0 :: (real, 3) vec) \<longleftrightarrow> x = 0 \<and> y = 0 \<and> z = 0"
  using vect_zero_eqv2 [of "(vector[x, y, z])"] by auto

lemma not_all_zero_eqv: "not_all_zero x y z \<longleftrightarrow> vector[x, y, z] \<noteq> (0 :: (real, 3) vec)"
  unfolding not_all_zero_def using vect_zero_eqv by auto

(*Now, the components of the definition of RP2 *)

definition respects_scaling :: "(v3 \<Rightarrow> v3) \<Rightarrow> bool"
  where "respects_scaling f \<longleftrightarrow> (\<forall>x::v3. \<forall>l :: real. l \<noteq> 0 \<longrightarrow> (\<exists>q . f (l *s x) = q *s (f x)))"

(*Note that q is not required to be  non-zero; this requirement comes into play
  in the next definition *)

definition image_non_zero :: "(v3 \<Rightarrow> v3) \<Rightarrow> bool"
  where "image_non_zero f \<longleftrightarrow> (\<forall>x :: v3 . x \<noteq> 0 \<longrightarrow> f x \<noteq> 0)"

definition well_defined :: "(v3 \<Rightarrow> v3) \<Rightarrow> bool"
  where "well_defined f \<longleftrightarrow> respects_scaling f \<and> image_non_zero f"


definition is_line :: "(v3) set \<Rightarrow> bool" 
  where "is_line L \<longleftrightarrow> (\<exists> a b c  :: real. (not_all_zero a b c) \<and> 
                         L = {x. a  * x$1 + b * x$2 + c * x$3 = 0})"

(*Above, I stay faithful to Hartshorne and do not translate this into the language
  of inner products. *)

definition lines_to_lines :: "(v3 \<Rightarrow> v3) \<Rightarrow> bool"
  where "lines_to_lines f \<longleftrightarrow> (\<forall>L. is_line L \<longrightarrow> (\<exists>L' . is_line L' \<and> (f ` L) \<subseteq> L'))"

(*Note that inclusion is sufficient. See also this MSE post:
https://math.stackexchange.com/questions/3481844/is-isomorphic-between-projective-planes-actually-equivalence-relation *)

definition is_RP2_auto :: "(v3 \<Rightarrow> v3) \<Rightarrow> bool"
  where "is_RP2_auto f \<longleftrightarrow> well_defined f \<and> (bij_betw f UNIV UNIV) \<and> lines_to_lines f"

definition make_RP2_auto :: "(v3 \<Rightarrow> v3) \<Rightarrow> (rp2 \<Rightarrow> rp2)"
  where "make_RP2_auto f = (if is_RP2_auto f then Abs_Proj \<circ> f \<circ> Rep_Proj else undefined)"

lemma projrel_almost_refl:
  fixes x
  assumes "x \<noteq> zvec"
  shows "projrel x x"
  using assms unfolding projrel_def zvec_def
  by (metis scaleR_one vect_zero_eqv zero_neq_one)

lemma well_defined_lift:
  fixes f g
  assumes "\<forall> x y . projrel x y \<longrightarrow>  projrel (f x) (g y)" 
  shows "well_defined f \<longrightarrow> well_defined g"
proof (safe)
  assume 2: "well_defined f" 
   have h1: "respects_scaling g" unfolding respects_scaling_def
  proof (safe)
    fix x :: v3
    fix l :: real
    assume "l \<noteq> 0"
    show "\<exists>q. g (l *s x) = q *s g x"
    proof (cases "x = zvec")
      case True
      then show ?thesis unfolding zvec_def
      by (metis vec.scale_one vect_zero_eqv vector_mul_eq_0)
    next
      case False
      then have 3: "projrel x x" using projrel_almost_refl by auto
      have 4: "\<exists> q. f (l *s x) = q *s f x" using 2 unfolding well_defined_def respects_scaling_def
      by sorry
      have "projrel (f x) (g x)" using assms 3 by auto
      then show ?thesis using 4 unfolding projrel_def
        by sorry
  qed
qed
  have h2: "image_non_zero g" unfolding image_non_zero_def
  proof (rule ccontr)
    assume " \<not> (\<forall>x. x \<noteq> 0 \<longrightarrow> g x \<noteq> 0)"
    then obtain x where x_assm: "x \<noteq> zvec \<and> g x = zvec" unfolding zvec_def
    by (metis vect_zero_eqv)
  then have "projrel x x" using projrel_almost_refl by auto
  then have "projrel (f x) (g x)" using assms by auto
  then show "False" using projrel_def x_assm by meson
qed
  show "well_defined g" using h1 h2 well_defined_def by auto
qed

(*One would expect a proof obligation from this -- to show that f respects the equivalence 
  relation -- but I guess the obligation will be in the
  proofs, not in the definition?  *)

(*We will follow the HOL-Analysis.Finite_Cartesian_Product definition of matrices. The basic idea
  is that 3-vectors are elements of the Cartesian product \<real> \<times> \<real> \<times> \<real>, and matrices are vectors
  of vectors. 3 \<times> 3 matrices are represented by the type class "v3^3".
  Some useful notes: given A :: v3^3, the entries of A are one-indexed, and one can access 
  them using A $ i $ j. To make a vector, write vector[a, b, c]; note that it is also one-indexed.
*)

(* The below definition helps make the types work out when working with
   definitions like "image_non_zero." In general, writing A *v x will also work.
   tom is short for "transformation of matrix." 
*)
definition tom :: "m33 \<Rightarrow> (v3 \<Rightarrow> v3)"
  where "tom A = (\<lambda>x. A *v x)" 

(* To take a matrix and create an automorphism of RP2 *)
definition matrix_to_rp2_auto :: "m33 \<Rightarrow> (rp2 \<Rightarrow> rp2)"
  where "matrix_to_rp2_auto A = make_RP2_auto (tom A)"

(*Now there follow some basic lemmas about matrices, which will be helpful for the later theorems. *)

definition adj_inv :: "m33 \<Rightarrow> m33"
  where "adj_inv A = transpose (matrix_inv A)"

(* Note that "inner" here denotes the inner product on a vector space *)
lemma transpose_is_adjoint:
  fixes A :: m33
  fixes s :: v3
  fixes x :: v3
  shows "inner s (A *v x) = inner ((transpose A) *v s) x"
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
  show ?thesis using h1 h2 h3 tom_def by simp
qed 

lemma inv_matrices_image_non_zero:
  fixes A :: m33
  assumes invertible: "det A \<noteq> 0"
  shows "image_non_zero (tom A)"
  unfolding image_non_zero_def
  unfolding tom_def
proof (rule allI; rule impI) 
  fix x :: v3
  assume non_zero: "x \<noteq> 0" 
  show "A *v x \<noteq> 0"
    using invertible non_zero invertible_def invertible_det_nz matrix_left_invertible_ker
    by auto
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
  shows "(tom B) (vector[a, b, c]) = 
          vector[inner (vector [a, b, c]) (B $ 1), inner (vector [a, b, c]) (B $ 2), 
          inner (vector [a, b, c]) (B $ 3)]" 
proof -
  let ?s = "vector[a, b, c]"
  have "(tom B) ?s$1 = inner ?s (B$1) \<and> (tom B) ?s$2 = inner ?s (B$2) \<and> (tom B) ?s$3 = inner ?s (B$3)" 
    by (simp add: inner_commute matrix_vector_mul_component tom_def)
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

lemma matrices_respect_scaling:
  fixes A :: m33
  shows "respects_scaling (tom A)"
  using tom_def respects_scaling_def[of "tom A"] vec.scale
  by metis

lemma lines_to_lines_helper:
  fixes A :: m33
  fixes a b c :: real
  assumes invertible: "det A \<noteq> 0"
  assumes "(not_all_zero a b c) \<and> L = {x. a  * x$1 + b * x$2 + c * x$3 = 0}"
  shows "\<exists> d e f  :: real. not_all_zero d e f \<and> (\<forall>x :: v3. a * x$1 + b*x$2 + c*x$3 = 0
           \<longrightarrow> ( d * ((tom A) x)$1 + e *((tom A) x)$2 + f *((tom A) x)$3 = 0))"
proof - 
  let ?s = "vector[a, b, c]"
  let ?B = "adj_inv A"
  let ?d = "inner ?s (?B$1)"
  let ?e = "inner ?s (?B$2)"
  let ?f = "inner ?s (?B$3)"
  let ?r = "vector[?d, ?e, ?f]"
  have rw1: "?r = tom ?B ?s" using matrix_vect_mult_helper by auto 
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

lemma inv_matrices_lines_to_lines:
  fixes A :: m33
  assumes invertible: "det A \<noteq> 0"
  shows "lines_to_lines (tom A)"
  unfolding lines_to_lines_def
  proof (rule allI; rule impI)
    fix L
    assume have_line: "is_line L"
    then obtain a b c :: real
      where h1: "(not_all_zero a b c) \<and> L = {x. a  * x$1 + b * x$2 + c * x$3 = 0}"
      using have_line is_line_def by auto
    show "\<exists>L'. is_line L' \<and> tom A ` L \<subseteq> L'"
      unfolding is_line_def
    proof -
      obtain d e f :: real
        where h2: "not_all_zero d e f \<and> (\<forall>x :: v3. a * x$1 + b*x$2 + c*x$3 = 0
           \<longrightarrow> ( d * ((tom A) x)$1 + e *((tom A) x)$2 + f *((tom A) x)$3 = 0))" 
        using lines_to_lines_helper h1 invertible by presburger
      let ?L' = "{x. d * x $ 1 + e * x $ 2 + f * x $ 3 = 0}"
      have req1a: "tom A ` L \<subseteq> ?L'"
        using h1 h2 by blast
      have req2: "not_all_zero d e f"
        using h2 by auto
      have req1b: "is_line ?L'" using req2 is_line_def by auto
      show "\<exists>L'. (\<exists>a b c. not_all_zero a b c \<and> L' = {x. a * x $ 1 + b * x $ 2 + c * x $ 3 = 0}) \<and>
         tom A ` L \<subseteq> L'" using req1a req1b req2 by auto
qed  
qed 

theorem inv_matrices_are_auts:
  fixes A :: m33
  assumes invertible: "det A \<noteq> 0"
  shows "is_RP2_auto (tom A)" 
  unfolding is_RP2_auto_def
  unfolding well_defined_def
proof (safe)
  show "respects_scaling (tom A)" 
    using matrices_respect_scaling by auto
  show "image_non_zero (tom A)"
    using invertible inv_matrices_image_non_zero by auto
  show "bij (tom A)"
    using tom_def invertible invertible_det_nz invertible_eq_bij by auto
  show "lines_to_lines (tom A)"
    using invertible inv_matrices_lines_to_lines by auto
qed

definition RP2_auto :: "(rp2 \<Rightarrow> rp2) set" where 
"RP2_auto = {A :: (rp2 \<Rightarrow> rp2) . (\<exists> f :: v3 \<Rightarrow> v3 . make_RP2_auto f = A)}"

definition rp2_auto_to_transf :: "(rp2 \<Rightarrow> rp2) \<Rightarrow> (v3 \<Rightarrow> v3)"
  where "rp2_auto_to_transf r = Rep_Proj \<circ> r \<circ> Abs_Proj"

(*The above theorem justifies the following definition: *)
definition RP2_matrix_auto :: "(rp2 \<Rightarrow> rp2) set" where
"RP2_matrix_auto = {A :: (rp2 \<Rightarrow> rp2) . (\<exists> f :: m33 . matrix_to_rp2_auto f = A)}"

(* What we have proved above is that 3x3 matrices give rise to a subset of
   the set of all automorphisms of rp2. The next theorem makes this explicit. *)
theorem inv_matrices_subset_auts: "RP2_matrix_auto \<subseteq> RP2_auto"
proof 
  fix A
  assume A_assm: "A \<in> RP2_matrix_auto"
  then obtain f :: m33 where "matrix_to_rp2_auto f = A" using RP2_matrix_auto_def by auto
  then have "make_RP2_auto (tom f) = A" 
    using tom_def make_RP2_auto_def matrix_to_rp2_auto_def by auto
  then show "A \<in> RP2_auto" using RP2_auto_def by auto
qed
  
(*The next section deals with the proof of Proposition 3.8 *)

definition equiv_maps :: "(v3 \<Rightarrow> v3) \<Rightarrow> (v3 \<Rightarrow> v3) \<Rightarrow> bool"
  where "equiv_maps f g \<longleftrightarrow>
  (well_defined f) \<and> (well_defined g) \<and> (\<forall>x :: v3 . \<exists>l :: real . l \<noteq> 0 \<and> f x = l *s (g x))"

lift_definition RP2_equiv_maps :: "(rp2 \<Rightarrow> rp2) \<Rightarrow> (rp2 \<Rightarrow> rp2) \<Rightarrow> bool" is equiv_maps
proof (transfer, clarsimp)
 fix f g h r
  assume 1: "projrel x y \<Longrightarrow> projrel (f x) (g y)" for x y
  assume 2: "projrel x y \<Longrightarrow> projrel (h x) (r y)" for x y
  have h1: "equiv_maps f h \<longrightarrow> equiv_maps g r"
  proof (rule impI)
    assume "equiv_maps f h"
    then have 3: "well_defined f \<and> well_defined h \<and> (\<forall>x :: v3 . \<exists>l :: real . l \<noteq> 0 \<and> f x = l *s (h x))"
      using equiv_maps_def by auto
    have 4: "well_defined g" using well_defined_lift 1 3 by auto
    have 5: "well_defined h" using well_defined_lift 2 3 by auto
    have 6: "(\<forall>x :: v3 . \<exists>l :: real . l \<noteq> 0 \<and> g x = l *s (r x))" using 1 2 3 by sorry
  show "equiv_maps f h \<longleftrightarrow> equiv_maps g r" 
qed

(* If the transformations for matrices A and B are equal up to a constant factor c,
  then they are "equiv_maps", i.e., they represent the same maps when considered as 
  rp2 \<Rightarrow> rp2 maps: *)

lemma inv_matrices_equiv_fwd:
  fixes A B :: m33
  assumes invertible_A: "det A \<noteq> 0"
  and invertible_B: "det B \<noteq> 0"
  shows "(\<exists>c :: real . \<forall>x :: v3 . 
        (tom A) x = c *s (tom B) x) \<longrightarrow> equiv_maps (tom A) (tom B)"
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

lemma inv_matrix_inj:
  fixes A :: m33
  fixes x :: v3
  assumes "det A \<noteq> 0"
  shows "tom A x = 0 \<longrightarrow> x = 0"
proof (rule impI; rule ccontr)
  assume x_in_ker: "tom A x = 0"
  assume to_contr: "x \<noteq> 0"
  show "False" using assms to_contr inv_matrices_image_non_zero image_non_zero_def x_in_ker by auto
qed

(*A general note: when proving statements involving vector arithmetic,
  ALWAYS unfold every definition first; then often writing "by vector"
  completes the goal. *)

lemma lin_comb:
  fixes a b c  :: real
  shows "vector[a, b, c] = a *s p1 + b *s p2 + c *s p3"
  unfolding p1_def p2_def p3_def vector_def
  by vector

lemma matrix_mult_unfold:
  fixes x :: v3
  fixes A :: m33
  shows "tom A x = x$1 *s tom A p1 + x$2 *s tom A p2 + x$3 *s tom A p3"
proof -
  have "x = x$1 *s p1 + x$2 *s p2 + x$3 *s p3" using lin_comb
    by (metis matrix_rows(1) vector_1)
  then have "tom A x = tom A (x$1 *s p1 + x$2 *s p2 + x$3 *s p3)" by auto
  then have "tom A x = tom A (x$1 *s p1) + tom A (x$2 *s p2) + tom A (x$3 *s p3)" 
    unfolding tom_def by (simp add: vec.add)
  then show ?thesis
    unfolding tom_def by (simp add: vec.scale)
qed

lemma comb: "q = p1 +  p2 + p3" 
  unfolding q_def p1_def p2_def p3_def
  using lin_comb by vector

lemma matrices_equal_on_basis:
  fixes A B :: m33
  and u :: real
  assumes "tom A p1 = u *s tom B p1"
  and "tom A p2 = u *s tom B p2"
  and "tom A p3 = u *s tom B p3"
  shows "\<forall>x :: v3. tom A x = u *s tom B x"
proof (rule allI)
  fix x :: v3
  let ?a = "x $ 1"
  let ?b = "x $ 2" 
  let ?c = "x $ 3"
  have "x = vector[?a, ?b, ?c]" unfolding vector_def vec_eq_iff using exhaust_3 by auto
  then have x_eq: "x = ?a *s p1 + ?b *s p2 + ?c *s p3" using lin_comb by auto
  then have eq1: "u *s tom B x = u *s tom B (?a *s p1 + ?b *s p2 + ?c *s p3)" by auto
  have eq2: "u *s tom B ((?a *s p1) + (?b *s p2) + (?c *s p3)) = 
               u *s tom B (?a *s p1) + u *s tom B (?b *s p2) + u *s  tom B (?c *s p3)" 
    using tom_def matrix_vector_right_distrib vector_add_ldistrib by metis 
  have eq3: "u *s tom B (?a *s p1) + u *s tom B (?b *s p2) + u *s  tom B (?c *s p3) =
            ?a *s (u *s tom B p1) + ?b *s (u *s tom B p2) + ?c *s (u *s tom B p3)"
    using tom_def vec.scale_left_commute vector_scalar_commute by (metis (no_types, lifting))
  have eq4: "?a *s (u *s tom B p1) + ?b *s (u *s tom B p2) + ?c *s (u *s tom B p3) =
            ?a *s tom A p1 + ?b *s tom A p2 + ?c *s tom A p3" using assms by auto
  have eq5: "?a *s tom A p1 + ?b *s tom A p2 + ?c *s tom A p3 = 
             tom A (?a *s p1 + ?b *s p2 + ?c *s p3)" using tom_def 
    by (simp add: matrix_vector_right_distrib vector_scalar_commute) 
  have eq6: "tom A (?a *s p1 + ?b *s p2 + ?c *s p3) = tom A x" using x_eq by auto
  show "tom A x = u *s tom B x" using eq1 eq2 eq3 eq4 eq5 eq6 by auto
qed

lemma equiv_on_basis_imp_equiv:
  (*The key part of the next theorem is separated out here, since we also need it for the uniqueness
    part of Theorem 3.9 *)
  fixes A :: m33
  fixes B :: m33
  assumes invertible_A: "det A \<noteq> 0"
  and invertible_B: "det B \<noteq> 0"
  and "\<exists>c1  :: real . c1 \<noteq> 0 \<and> tom A p1 = c1 *s tom B p1"
  and "\<exists>c2 :: real . c2 \<noteq> 0 \<and> tom A p2 = c2 *s tom B p2"
  and "\<exists>c3 :: real . c3 \<noteq> 0 \<and> tom A p3 = c3 *s tom B p3"
  and "\<exists> u :: real . u \<noteq> 0 \<and> tom A q = u *s tom B q"
  shows "\<exists>c :: real . \<forall>x :: v3 . (tom A) x = c *s (tom B) x \<and> c \<noteq> 0"
proof -
  obtain c1 :: real where hc1: "c1 \<noteq> 0 \<and> tom A p1 = c1 *s tom B p1" using assms(3) by auto
  obtain c2 :: real where hc2: "c2 \<noteq> 0 \<and> tom A p2 = c2 *s tom B p2" using assms(4) by auto
  obtain c3 :: real where hc3: "c3 \<noteq> 0 \<and> tom A p3 = c3 *s tom B p3" using assms(5) by auto
  obtain u:: real where hu: "u \<noteq> 0 \<and> tom A q  = u *s tom B q" using assms(6) by auto
  let ?r = "vector[u - c1, u - c2, u - c3]"
  have comb2: "(u - c1) *s p1 + (u - c2) *s  p2 + (u - c3) *s p3 = ?r" 
    unfolding p1_def p2_def p3_def vector_def by vector
  have eq1: "u *s tom B p1 + u *s tom B p2 + u *s tom B p3 =
             u *s (tom B p1 + tom  B p2 + tom B p3)"
    by (simp add: vec.scale_right_distrib)
  have eq2: "u *s (tom B p1 + tom  B p2 + tom B p3) = u *s (tom B (p1 + p2 + p3))"
    by (simp add: tom_def vec.add)
  have eq3: "u *s (tom B (p1 + p2 + p3)) = u *s (tom B q)"
    using comb by auto
  have eq4: "u *s (tom B q) = tom A q" using hu by auto
  have eq5: "tom A q = tom A p1 + tom A p2 + tom A p3" using comb
    by (metis matrix_vector_right_distrib
        tom_def)
  have eq6: "tom A p1 + tom A p2 + tom A p3 =
             c1 *s tom B p1 + c2 *s tom B p2 + c3 *s tom B p3" using hc1 hc2 hc3 by auto
  then have "u *s tom B p1 + u *s tom B p2 + u *s tom B p3 = 
                 c1 *s tom B p1 + c2 *s tom B p2 + c3 *s tom B p3"
    using eq1 eq2 eq3 eq4 eq5 eq6 by auto
  then have rw1: "u *s tom B p1 - c1 *s tom B p1 + u *s tom B p2 - c2 *s tom B p2 + u *s tom B p3 
             - c3 *s tom B p3 = 0" 
     by (simp add: diff_add_eq)
  then have "(u - c1) *s tom B p1 + (u - c2) *s tom B p2 + (u - c3) *s tom B p3 = 0"
    by (simp add: group_cancel.sub1 vec.scale_left_diff_distrib)
  then have "tom B ((u - c1) *s p1) + tom B ((u - c2) *s p2) + tom B ((u - c3) *s p3) = 0"
    using tom_def by (simp add: vector_scalar_commute)
  then have "tom B ((u - c1) *s p1 + (u - c2) *s  p2 + (u - c3) *s p3) = 0"
    using tom_def by (simp add: matrix_vector_right_distrib)
  then have "tom B ?r = 0"
    using comb2 by auto
  then have "?r = (0 :: (real, 3) vec)"
    using inv_matrix_inj[of B ?r] invertible_B by simp
  then have "u - c1 = 0 \<and> u - c2 = 0 \<and> u - c3 = 0"
  by (simp add: vect_zero_eqv)
  then have all_equal: "u = c1 \<and> u = c2 \<and> u = c3" by auto
  have h1: "tom A p1 = u *s tom B p1" using all_equal hc1 by auto
  have h2: "tom A p2 = u *s tom B p2" using all_equal hc2 by auto
  have h3: "tom A p3 = u *s tom B p3" using all_equal hc3 by auto
  have exists: "\<forall>x. tom A x = u *s tom B x" 
    using h1 h2 h3 matrices_equal_on_basis by blast
  have non_zero: "u \<noteq> 0" using hu by auto
  show "\<exists>c. \<forall>x. tom A x = c *s tom B x \<and> c \<noteq> 0" using exists non_zero by auto
qed 

lemma inv_matrices_equiv_bwd:
  fixes A :: m33
  fixes B :: m33
  assumes invertible_A: "det A \<noteq> 0"
  and invertible_B: "det B \<noteq> 0"
  shows "equiv_maps (tom A) (tom B) \<longrightarrow> (\<exists>c :: real . \<forall>x :: v3 . 
        (tom A) x = c *s (tom B) x \<and> c \<noteq> 0)"
  unfolding equiv_maps_def
proof (safe)
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

theorem inv_matrices_equiv_iff:
  fixes A :: m33
  fixes B :: m33
  assumes invertible_A: "det A \<noteq> 0"
  and invertible_B: "det B \<noteq> 0"
  shows "equiv_maps (tom A) (tom B) \<longleftrightarrow> (\<exists>c :: real . \<forall>x :: v3 . 
        (tom A) x = c *s (tom B) x \<and> c \<noteq> 0)"
proof
  show "\<exists>c. \<forall>x. tom A x = c *s tom B x \<and> c \<noteq> 0 \<Longrightarrow> equiv_maps (tom A) (tom B)"
    using inv_matrices_equiv_fwd invertible_A invertible_B by auto
  show " equiv_maps (tom A) (tom B) \<Longrightarrow> \<exists>c. \<forall>x. tom A x = c *s tom B x \<and> c \<noteq> 0"
    using inv_matrices_equiv_bwd invertible_A invertible_B by auto
qed 
end       





