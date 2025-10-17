theory "doctest"
  imports Complex_Main  "HOL-Library.Uprod" "HOL-Library.Quadratic_Discriminant" 

begin

(* ML\<open>Context.>> (Context.map_theory (Config.put_global Blast.trace (true)))\<close> *)
declare [[quick_and_dirty=true]]
declare [[smt_timeout = 1000]]
(* declare [[show_types = true]] *)
section \<open>Preface\<close>
text \<open>
\spike
This text is a formalization of Robin Hartshorne's \emph{Foundations of Projective Geometry}
using the Isabelle proof assistant, primarily relying on Isar. Quotations 
from Hartshorne appear indented, with a blue line to the left. Additional material 
written by either the professor (John (Spike) Hughes) or various students are surrounded by colored 
markers, like this:
\spike
This is something written by Spike
\done
with the black marker indicating the end of the section written by Spike (except that in this case, 
it's part of a larger section Spike wrote). 

Within Isabelle, numbered propositions or theorems from Hartshorne are given names that tie back 
to the text, so Proposition 1.1 in the text is called \texttt{Prop1P1}, with ``P'' replacing the period, 
for instance. 

We've based our theory on "Complex\_Main" instead of main so that we have the datatype "real". To 
characterize affine and projective planes (the main topics of study) we use ``locales'', an Isabelle 
construct that lets us say ``this entity satisfies this collection of defining axioms.''
\done\<close>

chapter \<open>Introduction: Affine Planes and Projective Planes\<close>
text \<open>
\begin{hartshorne}
Projective geometry is concerned with properties of incidence --- properties which are 
invariant under stretching, translation, or rotation of the plane. Thus in the axiomatic 
development of the theory, the notions of distance and angle will play no part.
However, one of the most important examples of the theory is the real projective plane,
and there we will use all the techniques available (e.g. those of Euclidean geometry and analytic 
geometry) to see what is true and what is not true.
\end{hartshorne}\<close>

section \<open>Affine geometry\<close>
text\<open>
\begin{hartshorne}
Let us start with some of the most elementary facts of ordinary plane geometry, which we will
take as axioms for our synthetic development.

Definition. An \emph{affine plane} is a set, whose elements are called points, and a set of
subsets, called \emph{lines}, satisfying the following three axioms, A1–A3. We will use the
terminology ``$P$ lies on $l$'' or ``$l$ passes through $P$'' to mean the point $P$ is an 
element of the line $l.$
\begin{itemize}
\item{A1.}
Given two distinct points $P$ and $Q$, there is one and only one line containing both $P$ and $Q.$
We say that two lines are parallel if they are equal or if they have no points in common.\\
\item{A2.}
Given a line $l$ and a point $P$ not on $l,$ there is one and only one line 
$m$ which is parallel to $l$ and which passes through $P.$\\

\item{A3.} There exist three non-collinear points. (A set of points $P_1, \ldots, P_n$ is said to be 
\emph{collinear} if there exists a line $l$ containing them all.)
\end{itemize}

Notation: 
\begin{align}
P \ne Q && \text{$P$ is not equal to $Q$.} \\
P \in l && \text{$P$ lies on $l$.}\\
l \cap m && \text{the intersection of $l$ and $m$.}\\
l \parallel m && \text{$l$ is parallel to  $m$.}\\
\forall && \text{for all.}\\
\exists && \text{there exists.}\\
\implies && \text{implies.}
\iff && \text{if and only if.}
\end{align}
\end{hartshorne}
\<close>
text \<open>
\spike
To translate to Isabelle, we are saying that to have an affine plane, you need two types (one for points, 
one for lines), and a set, which we'll call `Points', of items of the first type, and a set, which we'll call 
`Lines', of the second type. 

In a first attempt to formalize this text, I actually chose to use a \emph{type} for points and lines, but that rapidly becomes
inconvenient. Unfortunately, in Isabelle functions are defined on domains that must be types, 
not sets. Fortunately, they need not be fully specified:  $F(a)$ may be 'undefined' for
 some element $a$ of the domain of $F$, which effectively limits the domain of $F$ to those 
items in its domain type for which we \emph{have} provided a description of the associated value. 

To complete the definition of an affine plane, you not only need types for points and lines, you 
need a relationship between them. The statement "incid P l" indicates the notion
that the "point" P lies on (or is "incident on") the "line" l. For Hartshorne, we would say P 
is an element of l, but using
point sets as lines turns out to be a horrible idea in Isabelle, so we just deal with "incid".

Furthermore, if you look closely at the first axiom, it's saying that there's a function that takes two distinct 
points and returns the (unique) line joining them, so we'll also use a function called "join P Q" to represent that. 

Similarly, A2 implicitly describes another function that takes a line and a point and returns a line,
 one that we'll call ``find parallel''. The three functions --- incid, join, find_parallel --- encode the 
essence of an affine plane. 

Sadly, the notion of "parallel" makes sense only after we have our sets of Points and Lines, and a "incid" function, 
so if we want to define parallel, it has to happen after we describe the affine plane. But without a definition of
parallel, the statements of the axioms become very messy, since they essentially have to replace "parallel" with 
the not-yet-written definition. We address this by first creating a locale called "affine_plane_data", in which 
we specify the data needed to define an affine plane, and can then define things like parallel and collinear, 
and then we define a further locale, \isi{affine_plane}, which is an \isi{affine_plane_data} together with some
extra rules (the axioms).

In what follows, "p" and "l" are the types used for points and lines, and Points and Lines are the particular subsets 
of the types p and l, the ones that constitute our geometry. These are named in the locale "affine_plane_data", which is then 
used within the locale "affine_plane". This allows us to define "parallel" strictly in terms of "incid", so that the
term "parallel" can be used in the description of the locale affine_plane. While we're defining those 
things, we also prove some small facts about them that we'll use later. We could have put these proofs
in \isi{affine_plane}, but it's nice to have them near the introduction of these functions.

Notice that if we apply "parallel" to two equal items of type \isi{'l} that happen to not be lines, 
it returns \isi{False}. That means that \isi{parallel} is not a reflexive relation on universal set of type 
\isi{'l}. If we consider it only on the smaller set \isi{Lines}, then it \emph{is} in fact a reflexive
relation. 
\<close>
text\<open> The use of 'infix' below means that we can write "P \<lhd> m" instead of "incid P m" from now on. \<close>

locale affine_plane_data =
  fixes Points :: "'p set" and Lines :: "'l set" and incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool" (infix "\<lhd>" 60)
  fixes join:: "'p \<Rightarrow> 'p \<Rightarrow> 'l"
  fixes find_parallel:: "'l \<Rightarrow> 'p \<Rightarrow> 'l"
begin


definition (in affine_plane_data) collinear :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
    where "collinear A B C = (if A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
  then (\<exists> l. l \<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l \<and>  C \<lhd> l) else undefined)"

definition parallel::"'l \<Rightarrow> 'l \<Rightarrow> bool"  (infix "||" 50)  where
  "parallel l m = ((l \<in> Lines) \<and> (m \<in> Lines) \<and> ((l = m) \<or>  
  ((\<not> (\<exists> P. P \<in> Points \<and> P \<lhd> l \<and> P \<lhd> m)))))"

text \<open>
This \isi{infix} clause says that from now on we 
can write \isi{n || k} and it will be immediately converted internally to \isi{parallel n k}, and 
that when it comes time for Isabelle to output something represented as 
\isi{parallel a b}, it'll be written \isi{a || b}. (A similar statement holds for "\<lhd>".)
Note that \isi{a} and \isi{b} can be complex expressions here rather than just single names; Isabelle 
recognizes and parses them correctly. 
\done
\<close> 

text\<open>Skipping ahead here to the discussion of equivalence relations, we'll prove some
properties of parallelism.\<close>

(* defined to say that k and m are parallel only if they are both Lines and if either (i) k = m, or
(ii) k and m  don't meet. That allows us to say that "parallel" is an equiv reln on 
Lines, but not on all of type 'l *)

lemma parallel_reflexive [iff]: 
  fixes l
  assumes "l \<in> Lines" 
  shows "parallel l l"
  sorry

lemma parallel_symmetric [iff]: 
  fixes l m
  assumes "parallel l m"
  shows "parallel m l"
  sorry

(* We can't prove parallel is transitive yet, because it 
actually requires axiom 2 of a plane *)

lemma parallelE [elim]:
  assumes "parallel l m"  and
  "l \<in> Lines" and "m \<in> Lines"
  obtains (eq) "l = m" | (disjoint) "(\<not> (\<exists> P. P \<in> Points \<and> P \<lhd>  l \<and> P \<lhd>  m)) \<and> (l \<in> Lines) \<and> (m \<in> Lines)"
proof -
  show "(l = m \<Longrightarrow> thesis) \<Longrightarrow>
    ((\<nexists>P. P \<in> Points \<and>
          P \<lhd> l \<and> P \<lhd> m) \<and>
     l \<in> Lines \<and> m \<in> Lines \<Longrightarrow>
     thesis) \<Longrightarrow>
    thesis" using assms unfolding parallel_def by blast
qed

lemma parallel_if_no_shared_pointsI [intro]:
  assumes " \<not> (\<exists> P. P \<in> Points \<and> P \<lhd>  l \<and> P \<lhd>  m)" and
  "l \<in> Lines" and "m \<in> Lines"
  shows "l || m"
  sorry

lemma parallel_if_no_shared_points2I [intro]:
  assumes "\<forall>P .  P \<notin>  Points \<or> \<not> P \<lhd>  l \<and>  \<not>P \<lhd>  m" and
  "l \<in> Lines" and "m \<in> Lines"
  shows "l || m"
  sorry

definition point_pencil::"'p \<Rightarrow> 'l set" where
"point_pencil P = { n::'l . (n \<in> Lines) \<and> P \<lhd>  n}"

definition line_pencil::"'l \<Rightarrow> 'l set" where
"line_pencil k = { n::'l . n || k}"

end (* affine_plane_data *)

locale affine_plane =
     affine_plane_data Points Lines incid join find_parallel
     for
     Points :: "'p set" and
     Lines :: "'l set" and
     incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"  (infix "\<lhd>" 60) and
     join:: "'p \<Rightarrow> 'p \<Rightarrow> 'l" and
     find_parallel:: "'l \<Rightarrow> 'p \<Rightarrow> 'l" +
   assumes
    a1a: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> join P Q \<in> Lines \<and> P \<lhd>  (join P Q)  \<and> Q \<lhd>  (join P Q)" and
    a1b: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points; P \<lhd>  m; Q \<lhd>  m\<rbrakk> \<Longrightarrow> m = join P Q" and
    a2a: "\<lbrakk> P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> find_parallel l P \<in> Lines" and
    a2b: "\<lbrakk> P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow>  ( find_parallel l P) || l" and
    a2c: "\<lbrakk> P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow>  P \<lhd>  (find_parallel l P)" and
    a2d: "\<lbrakk> P \<in> Points; l \<in> Lines; m \<in> Lines; m || l; P \<lhd>  m\<rbrakk> \<Longrightarrow> m = find_parallel l P" and
    a3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)"
begin
text \<open>
It's worth looking at this collection pretty carefully. Do the required properties of \isi{join} in
\isi{a1a} and \isi{a1b} make sense? Do they properly represent Hartshorne's axiom A1? What about the 
other encodings of axioms? And what is \isi{m1} telling us? 

A locale-description like this is followed by a begin-end block (the isi{begin} is included above)
 within which all the things mentioned
in the locale-description are available for use, so you can refer to \isi{parallel} or \isi{Points} 
freely. You can also prove small theorems, which will then be usable whenever they're applied to 
something that is an instance of an \isi{affine_plane}.\<close>

lemma join_symmetric: 
  fixes P Q
  assumes "P \<in> Points"
  assumes "Q \<in> Points"
  assumes "P \<noteq> Q" 
  shows "join P Q = join Q P" 
  sorry

definition (in affine_plane_data) liesOn :: "'p \<Rightarrow> 'l \<Rightarrow> bool" (infix "liesOn" 50) where
  "P liesOn m = (if P  \<in> Points \<and> (m \<in> Lines) then P \<lhd>  m  else undefined)"

definition  (in affine_plane_data) contains :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "contains" 50) where
  "m contains P = (P liesOn m)"

theorem join_containsL:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "P liesOn (join P Q)"
  sorry

theorem join_containsL2:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "P \<lhd>  (join P Q)"
  sorry                            

theorem join_containsR:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "Q liesOn (join P Q)"
  sorry

theorem join_containsR2:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "Q \<lhd> (join P Q)"
  sorry

theorem join_symmetric0:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"
  shows "join P Q = join Q P"
  sorry

theorem contains_implies_liesOn:
  fixes P m
  assumes "P  \<in> Points"
  assumes "m  \<in> Lines"
  assumes "m contains P"
  shows "P liesOn m"
  sorry

theorem liesOn_implies_contains:
  fixes P m
  assumes "P  \<in> Points"
  assumes "m  \<in> Lines"
  assumes "P liesOn m"
  shows "m contains P"
  sorry

lemma parallel_transitive: 
  fixes l m k
  assumes "parallel l m"
  assumes "parallel m k"
  shows "parallel l k"
proof -
  have 0: "parallel l m = ((l = m) \<or> \<not> (\<exists> P. P \<in> Points \<and> P \<lhd>  l \<and> P \<lhd>  m))" using assms parallel_def by auto
  have 1: "parallel m k = ((m = k) \<or> \<not> (\<exists> P. P \<in> Points \<and> P \<lhd>  m \<and> P \<lhd>  k))" using assms parallel_def by auto
  consider 
    (lmmk) "(l = m)" and "(m = k)" 
    | (lm) "(l = m)" and "(m \<noteq> k)" 
    | (mk) "(l \<noteq> m)" and "(m = k)" 
    | (neither) "(l \<noteq> m)" and "(m \<noteq> k)" by blast
  then have  ?thesis
  proof cases
    case lmmk
    have "l = k" using assms lmmk by auto
    then have "parallel l k" using parallel_def assms by auto
    show ?thesis  using \<open>l || k\<close> by blast
  next
    case lm
    then have "parallel l k" using parallel_def assms by auto
show ?thesis  using \<open>l || k\<close> by blast
  next 
    case mk
    then have "parallel l k" using parallel_def assms by auto
    show ?thesis  using \<open>l || k\<close> by blast
  next
    case neither
    consider (same) "l = k" | (different) "l \<noteq> k" by auto
    then have "parallel l k" 
    proof cases
      case same
      then show ?thesis using same parallel_def assms by auto
    next
      case different
      then show ?thesis using a2d parallel_def parallel_symmetric assms parallel_if_no_shared_pointsI by metis
    qed
    show ?thesis  using \<open>l || k\<close> by blast
  qed
  show ?thesis  using \<open>l || k\<close> by blast
qed

text\<open>The following says not that parallelism is reflexive (it's not, at least not on all of type 'l!), 
but rather that when restricted to the set Lines, it's reflexive.\<close>
lemma parallel_refl:
  shows "reflp_on Lines parallel"
by (simp add: reflp_onI)

lemma parallel_sym:
  shows "symp parallel" by (simp add: sympI)

lemma parallel_trans:
  shows "transp_on Lines parallel" 
proof -
  show ?thesis
    using parallel_transitive transp_onI by metis
qed

text\<open>Sadly, defining an equivalence relation on a set
(as contrasted with a whole type) is a bit of a pain, so we have to settle for just the three lemmas above.
We'd really love to define the notion of a "pencil" as a quotient type, and we could
almost do that...but not in the context of a locale, because that would effectively introduce dependent
types, which Isabelle lacks. \<close>

text\<open>
\begin{hartshorne}
Example. The ordinary plane, known to us from Euclidean geometry, satisfies the axioms A1–A3, and 
therefore is an affine plane. [NB: We'll return to this, and a second example, below. -- jfh]

A convenient way of representing this plane is by introducing Cartesian coordinates, 
as in analytic geometry. Thus a point $P$ is represented as a pair $(x, y)$ of real numbers. 
(We write $x, y \in \Bbb R$.)

[Omitted picture]
\prop[1.1] Parallelism is an equivalence relation.

\end{hartshorne}
\<close>

  text \<open>
\begin{hartshorne}
\defn[equivalence relation] A relation $\sim$ is an equivalence relation if it has the following
three properties:
\begin{enumerate}
\item Reflexive: $a \sim a$
\item Symmetric: $a \sim b \implies b \sim a$
\item Transitive: $a \sim b$ and $b \sim c \implies a \sim c$.
\end{enumerate}

\proof (of proposition)
We must check the three properties:
1. Any line is parallel to itself, by definition. 

2. $l \parallel m \implies m \parallel l$ by definition.

3. If $l \parallel m$, and $m \parallel n$, we wish to prove $l \parallel n.$

If $l=n$ ,there is nothing to prove.If $l \ne n$,and there is a point
$P \in l \cap n$,then $l, n$ are both $\parallel m$ and pass through $P$, which is impossible by 
axiom A2. We conclude that $l \cap n = \emptyset$ (the empty set), and so $l \parallel n.$
\end{hartshorne}
\<close>

text \<open>
\spike
As you've seen above, we put the proofs of equivalence-relation properties right next to where the relations
were defined, making things a little bit out of order here. 

\done\<close>

lemma parallel_to_Lines:
  fixes k m
  assumes "k || m" and "k \<noteq> m"
  shows "k \<in> Lines" and "m \<in> Lines"
proof -
  show "k \<in> Lines" using assms parallel_def by blast
next
  show "m \<in> Lines" using assms parallel_def by blast
qed

text \<open>Here's more or less a translation of Hartshorne's three-line proof.\<close>

lemma parallel_transitive2:
  fixes k m n 
  assumes asm1:"k || m" and asm2:"m || n" 
  shows "k || n"
proof (cases "k = m")
  case True
  then show ?thesis using parallel_def assms True by blast
next
  case False
  from False have kmdiff1: "k \<noteq> m" by auto
  then show ?thesis 
  proof (cases "m = n")
    case True
    then show ?thesis using parallel_def assms True by blast 
  next
    case False
    have all_lines: "k \<in> Lines \<and> m \<in> Lines \<and> n \<in> Lines"  using parallel_to_Lines False kmdiff1  asm2 asm1  False by blast 
    show "k || n"
    proof (rule ccontr)
      assume cHyp: "\<not> (k || n)"
      from parallel_def cHyp  have 0: " ((\<not>(k = n)) \<and>  (((\<exists> P. P \<in> Points \<and> P \<lhd>  k \<and> P \<lhd>  n)) \<or> (k \<notin> Lines) \<or> (n \<notin> Lines)))" using asm1 by blast 
      have 3: "(\<not>(k = n)) \<and>  (((\<exists> P. P \<in> Points \<and> P \<lhd>  k \<and> P \<lhd>  n)))" using 0 all_lines by blast
      have 5: "(\<exists> P. P \<in> Points \<and> P \<lhd>  k \<and> P \<lhd>  n)" using 3 cHyp by blast
      obtain P where 6: "P \<in> Points \<and> P \<lhd>  k \<and> P \<lhd>  n" using 5 by auto
      have 7: "k ||m \<and> P \<lhd>  k" using asm1 6 by blast
      have 8: "k = find_parallel m P" using  6 7 a2d kmdiff1 all_lines by blast
      have 9: "n ||m \<and> P \<lhd>  n" using asm2 6  by blast
      have 10: "n = find_parallel m P" using  6 9 a2d kmdiff1 all_lines by blast
      have 11: "n = k" using 8 10 by auto
      show " \<not> k || n \<Longrightarrow> False" using 3 11 by blast
    qed
  qed
qed

end

text  \<open>\spike To help Isabelle along, we insert a tiny theorem giving a different 
characterization of parallelism \done\<close>

theorem (in affine_plane) parallel_alt:
  fixes l
  fixes m
  assumes "l \<noteq> m"
  assumes "l \<in> Lines" and "m \<in> Lines"
  assumes "\<forall>P. (\<not>P \<lhd>  l) \<or> (\<not> P \<lhd>  m)"
  shows "l || m"
  sorry

text  \<open>\begin{hartshorne}
\prop[1.2] Two distinct lines have at most one point in common.

\proof For if $l, m$ both pass through two distinct points $P, Q,$ then by axiom A1, $l = m.$ \endproof
\end{hartshorne}
\<close>


lemma (in affine_plane) prop1P2: 
"\<lbrakk>l \<noteq> m; l \<in> Lines; m \<in> Lines; P \<in> Points; Q \<in> Points; P \<lhd>  l; P \<lhd>  m; Q \<lhd>  l; Q \<lhd>  m\<rbrakk> \<Longrightarrow> P = Q"
  sorry

find_theorems affine_plane

text \<open>
We can also prove some basic theorems about affine planes not in Hartshorne: every
point lies on some line; for every line, there's \emph{some} point not on it; every line contains some point, and in fact every line 
contains two points, although we'll delay that for a moment. \<close>

lemma (in affine_plane) containing_line: "S \<in> Points \<Longrightarrow> (\<exists>l . (l \<in> Lines \<and>  S \<lhd> l))"
  sorry

lemma (in affine_plane) missed_point: "k \<in> Lines \<Longrightarrow> (\<exists>S . (S \<in> Points \<and> ( \<not>  S \<lhd> k)))" 
  sorry

lemma (in affine_plane) contained_point: 
  assumes "k \<in> Lines"
  shows "\<exists> S. S \<in> Points \<and>  S \<lhd> k"
  sorry

text  \<open>\begin{hartshorne}
Example. An affine plane has at least four points. There is an affine plane with four points.

Indeed, by A3 there are three non-collinear points. Call them $P, Q, R.$ By A2 there is a line 
$l$ through $P,$ parallel to the line $QR$ joining $Q$ and $R,$ which exists by A1. 
Similarly, there is a line $m \parallel  PQ$, passing through $R.$

Now $l$ is not parallel to $m$ ($l \nparallel m$). For if it were, then we would have 
$PQ \parallel m \parallel l \parallel QR$
and hence $PQ \parallel QR$ by Proposition 1.1. This is impossible, however, because $P Q \ne QR$, 
and both contain $Q.$

Hence $l$ must meet $m$ in some point $S.$ Since $S$ lies on $m,$ which is parallel to $PQ$, and 
different from $PQ,$ $S$ does not lie on $PQ,$ so $S\ne P$,and $S \ne Q$.Similarly $S \ne R$. Thus
$S$ is indeed a fourth point. This proves the first assertion.

Now consider the lines $PR$ and $QS$. It
may happen that they meet (for example in the real projective plane they will (proof?)). 
On the other hand, it is consistent with the axioms to assume that they do not meet.
In that case we have an affine plane consisting of four points $P, Q, R, S$ and six lines 
$PQ, PR, PS, QR, QS, RS,$ and one can verify easily that the axioms A1–A3 are satisfied. 
This is the smallest affine plane. [NB: We'll return to this final claim presently.]

\end{hartshorne}
\<close>

text\<open>\spike In fact, not only have we shown that there are four points, we can show
that there are four points, no three of which are collinear. The proofs of these will appear
shortly.\<close>

text \<open>The proof of the following small theorem --- that every line k contains at least two points ---
really uses everything we know about an affine plane. We start by assuming k contains
just one point, S (zero is out because of the \isi{contained_point} theorem.The four-points-no-three-collinear
theorem tells us that distinct from S, we have a triple of points UVW that are noncollinear. 

find_parallel UV S = k
find_parallel VW S = k
That makes UV and VW parallel; because they both contain V, they're equal. That means that UV contains 
U, V, and W, so they're collinear -- a contradiction. 
Here's the theorem statement, with proof delayed:
lemma (in affine_plane) contained_points: 
  fixes k
  assumes "k \<in> Lines"
  shows "\<exists> S T. S \<in> Points \<and> T \<in> Points \<and>  S \<noteq> T \<and>  S \<lhd> k \<and>  T \<lhd> k"
\<close>

section  \<open> The real affine plane\<close>

text \<open> Hartshorne mentioned, just after the definition of an affine plane and some notational
remarks, that the ordinary affine plane $A2$ is an example of an affine plane, as is the 4-point
affine plane $A4$. For $A2$, we should prove 
that it IS actually an affine plane. It's pretty clear how to represent points --- pairs of real 
numbers --- but what about lines? A line is the set of points satisfying an equation of 
the form Ax + By + C = 0, with not both of A and B being zero. The problem is that there's 
no datatype for ``pair of real numbers, at least one of which is nonzero''. We'll have 
to hack this by breaking lines into ``ordinary'' and ``vertical'', alas.  The construction
and proofs for these two examples is in Chapter1a.thy. Much of the work here 
on the first draft, with a rather different formulation of the locale, was done by Seiji and Caleb,with Jackson 
also contributing. \<close>

text\<open>\done \done  Examples of some easy theorems about affine planes, not mentioned in Hartshorne.
\jackson \<close>      

(* Some HW Problems to give you practice with Isabelle:
Try to state and prove these:
1. Every line contains at least two points (this is stated for you below, but
with "sorry" as a "proof". 
2. Every line contains at least three points [false!]
*)

text\<open>To prove that every line contains at least two points, firstly we should think about where the
contradiction is when the line contains only one point. Usually, contradiction happens when something
violates a unique existence. For example, in A2, if an assumption leads to the conclusion that there
are more lines that could parallel to a specific line passing through the same point, then the assumption
is proved to be false. Here are the ideas for our proof.

i. If l only contains one point Q and point P != point Q, then every line passing through P is parallel
to l.
ii. To prove the contradiction to A2, we have to prove there are at least two lines passing through P. 
NB: need lemma contained-lines: for every point, there are at least two lines that pass through that point.
iii.Lemma contained-lines can be proved with the three non-collinear points P Q R in A3. Two cases:
1. The point is P or Q or R. 2. The point T is different from those 3 points. Then PT, QT, RT cannot
be the same line, which proves that at least two lines pass through T.


\siqi\<close>


  text \<open>
 We now try to prove that every affine plane contains at least four points. Sledgehammer 
(a generally-useful approach) doesn't get anywhere with this one. 

Here's Hartshorne's proof, though, so we can use the pieces to construct an Isabelle proof.

i. by A3 there are three distinct non-collinear points; call them P,Q,R. 
ii. By A1, there's a line, which I'll call QR, through Q and R. 
iii. By A2, there's a line l through P, parallel to QR.
iv. Similarly, there's a line PQ containing P and Q. 
v. There's a line m through R, parallel to the line PQ.

CASES: l is parallel to m, or it is not.  

vi. l is not parallel to m, for if it were, then PQ || m || l || QR, hence PQ || QR (by 
the lemmas about parallelism) and since both contain Q,  they are identical, but then P,Q,R are collinear,
which is a contradiction. 

vii. So l and m are nonparallel, and they share some point S. 

viii. S lies on m, which is parallel to PQ but not equal to it,
hence disjoint from it (see definition of parallel), so S is not on PQ.

ix.  Hence S != P, S != Q. 

x. Similar (arguing about l), we get  S != R. 

xi. Hence the four points P,Q,R,S are all distinct, and we are done. 
\<close>

proposition (in affine_plane) four_points_necessary: "\<exists>(P :: 'p) (Q :: 'p) (R :: 'p) (S :: 'p). 
      P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S \<and> P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points"
    proof -
      obtain P Q R where PQR: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R"
        using a3 by blast
      let ?PQ =" join P Q"
      let ?l = "find_parallel ?PQ R"
      let ?QR = "join Q R"
      let ?m = "find_parallel ?QR P" 
      have mline: "?m \<in> Lines" using PQR a1a a2a by blast
      have lline: "?l \<in> Lines" using PQR a1a a2a by blast
      have np: "\<not> parallel ?m ?l" 
      proof (rule ccontr)
        assume a: "\<not> \<not> parallel ?m ?l"
        then have aq: "parallel ?m ?l" by blast
        also have 0: "parallel ?l ?PQ"  using PQR a1a a2b by blast
        have 1: "parallel ?m ?QR" using PQR a1a a2b by blast
        have 2: "?l || ?QR" 
          using "1" calculation parallel_transitive by blast
        have 3: "?PQ || ?QR"
          by (meson "0" "2" parallel_symmetric parallel_transitive2)
        have 4: "?PQ = ?QR" using "3" PQR a1a by blast
        have 5: "collinear P Q R" using 4 by (metis PQR a1a collinear_def)
        show False using 5 PQR by auto
      qed
      obtain S where S: "S \<in> Points \<and>  S \<lhd> ?l \<and> S \<lhd> ?m"
        using np mline lline parallel_def by blast
      have spoint: "S \<in> Points" using S by auto 
      have three_more: "S \<noteq> P \<and> S \<noteq> Q \<and> S \<noteq> R"
        by (metis PQR S a1a a2b a2c collinear_def lline mline parallelE)
      have p1: " P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R" using PQR by blast
      have tma: "P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S" using three_more by blast
      have p2: "P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       P \<noteq> S \<and>
       Q \<noteq> S \<and> R \<noteq> S" using p1 tma by blast
      thus ?thesis
        using spoint PQR p2 exI by blast
    qed

    text\<open>\<close>
    text \<open>We can amplify this slightly to show that not only are there four points, but that no 
three are collinear; then we'll finally be able to show that every line contains at least two points!\<close>

proposition (in affine_plane) four_points_noncollinear_triples: "\<exists>(P :: 'p) (Q :: 'p) (R :: 'p) (S :: 'p). 
      P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S \<and> P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points
\<and> \<not> collinear P Q R \<and> \<not> collinear P Q S \<and> \<not> collinear P R S \<and> \<not> collinear Q R S"
    proof -
      obtain P Q R where PQR: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R"
        using a3 by blast
      let ?PQ =" join P Q"
      let ?l = "find_parallel ?PQ R"
      let ?QR = "join Q R"
      let ?m = "find_parallel ?QR P" 
      have mline: "?m \<in> Lines" using PQR a1a a2a by blast
      have lline: "?l \<in> Lines" using PQR a1a a2a by blast
      have np: "\<not> parallel ?m ?l" 
      proof (rule ccontr)
        assume a: "\<not> \<not> parallel ?m ?l"
        then have aq: "parallel ?m ?l" by blast
        also have 0: "parallel ?l ?PQ"  using PQR a1a a2b by blast
        have 1: "parallel ?m ?QR" using PQR a1a a2b by blast
        have 2: "?l || ?QR" 
          using "1" calculation parallel_transitive by blast
        have 3: "?PQ || ?QR"
          by (meson "0" "2" parallel_symmetric parallel_transitive2)
        have 4: "?PQ = ?QR" using "3" PQR a1a by blast
        have 5: "collinear P Q R" using 4 by (metis PQR a1a collinear_def)
        show False using 5 PQR by auto
      qed
      obtain S where S: "S \<in> Points \<and> S \<lhd> ?l \<and> S \<lhd> ?m"
        using np mline lline parallel_def by blast
      have spoint: "S \<in> Points" using S by auto 
      have three_more: "S \<noteq> P \<and> S \<noteq> Q \<and> S \<noteq> R"
        by (metis PQR S a1a a2b a2c collinear_def lline mline parallelE)
      have p1: " P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R" using PQR by blast
      have tma: "P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S" using three_more by blast
      have p2: "P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       P \<noteq> S \<and>
       Q \<noteq> S \<and> R \<noteq> S" using p1 tma by blast
      thus ?thesis
        using spoint PQR p2 exI 
      by (smt (verit) S a1a a1b a2b a2c collinear_def parallel_def)
    qed


proposition (in affine_plane) four_points_parallel_pairs: "\<exists>(P :: 'p) (Q :: 'p) (R :: 'p) (S :: 'p). 
      P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S \<and> 
      P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points \<and> 
      parallel (join P Q) (join R S) \<and> parallel (join P R) (join Q S) \<and> 
      (join P Q) \<noteq> (join R S) \<and> (join P R) \<noteq> (join Q S) \<and> 
      \<not> collinear P Q R \<and>\<not> collinear P Q S \<and> \<not> collinear P R S \<and> \<not> collinear Q R S"
    proof -
      obtain P Q R where PQR: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R"
        using a3 by blast
      let ?PQ =" join P Q"
      let ?l = "find_parallel ?PQ R"
      let ?QR = "join Q R"
      let ?m = "find_parallel ?QR P" 
      have mline: "?m \<in> Lines" using PQR a1a a2a by blast
      have lline: "?l \<in> Lines" using PQR a1a a2a by blast
      have np: "\<not> parallel ?m ?l" 
      proof (rule ccontr)
        assume a: "\<not> \<not> parallel ?m ?l"
        then have aq: "parallel ?m ?l" by blast
        also have 0: "parallel ?l ?PQ"  using PQR a1a a2b by blast
        have 1: "parallel ?m ?QR" using PQR a1a a2b by blast
        have 2: "?l || ?QR" 
          using "1" calculation parallel_transitive by blast
        have 3: "?PQ || ?QR"
          by (meson "0" "2" parallel_symmetric parallel_transitive2)
        have 4: "?PQ = ?QR" using "3" PQR a1a by blast
        have 5: "collinear P Q R" using 4 by (metis PQR a1a collinear_def)
        show False using 5 PQR by auto
      qed
      obtain S where S: "S \<in> Points \<and> S \<lhd> ?l \<and> S \<lhd> ?m"
        using np mline lline parallel_def by blast
      have spoint: "S \<in> Points" using S by auto 
      have three_more: "S \<noteq> P \<and> S \<noteq> Q \<and> S \<noteq> R"
        by (metis PQR S a1a a2b a2c collinear_def lline mline parallelE)
      have p1: " P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R" using PQR by blast
      have tma: "P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S" using three_more by blast
      have p2: "P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       P \<noteq> S \<and>
       Q \<noteq> S \<and> R \<noteq> S" using p1 tma by blast
      thus ?thesis
        using spoint PQR p2 exI 
      by (smt (verit) S a1a a1b a2b a2c collinear_def parallel_def)
  qed

    text \<open>Yes, those last two proofs were via sledgehammer. Finally, we can prove that every line contains 
at least two points. Recall that the statement was

lemma (in affine_plane) contained_points: 
  fixes k
  assumes "k \<in> Lines"
  shows "\<exists> S T. S \<in> Points \<and> T \<in> Points \<and>  S \<noteq> T \<and>  S \<lhd> k \<and>  T \<lhd> k"

The idea of the proof is this: take the set of four points, no three collinear, given by the last lemma.
Remove from this the one point, S, of the line. The you get three (other) non-collinear points, 
say, A, B, C. The line parallel to AB through S is k. The line parallel to AC through S is also k. So $AB$
and $AC$ are parallel, which means they're equal, which means that $A,B,C$ are collinear, a contradiction 

Doesn't work

Let's try another: we have 4 distinct lines, in two parallel pairs H and K. But each line from 
H intersects each line from K. 

 If l = {X}, then the special point X lies on at most one line in each of H and K. Select 
the (or an) other line in each set, k and n. Then find_parallel k X = l and same for n X. 
That makes both k and n parallel to l, so parallel to each other. But they intersect and are 
distinct. Contradiction. 
\<close>
lemma (in affine_plane) parallel_overlap_equal:
  fixes k n P
  assumes "k \<in> Lines \<and> n \<in> Lines \<and> P \<in> Points"
  assumes "k || n"
  assumes "P \<lhd>  k" and "P \<lhd>  n"
  shows "k = n"
  using assms(1,2,3,4) by blast


lemma (in affine_plane) parallel_to_collinear:
  fixes A B C
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points"
  assumes "A \<noteq>  B \<and> B \<noteq> C \<and> A \<noteq> C"
  assumes "join A C = join A B"
  shows "collinear A B C"
  by (metis a1a assms(1,2,3) collinear_def)

lemma (in affine_plane) contained_points: 
  fixes l
  assumes "l \<in> Lines"
  shows "\<exists> S T. S \<in> Points \<and> T \<in> Points \<and>  S \<noteq> T \<and>  S \<lhd> l \<and>  T \<lhd> l"
proof (rule ccontr)
  assume ch: "\<not> (\<exists> S T. S \<in> Points \<and> T \<in> Points \<and>  S \<noteq> T \<and> S \<lhd> l \<and> T \<lhd> l)"
  have 0: "{A . A \<in> Points \<and> A \<lhd> l} \<noteq> {}" using contained_point assms by blast
  have 1: "\<exists> B \<in> Points . {A . A \<in> Points \<and> A \<lhd> l} = {B}" using ch 0 by force
  obtain X where xfacts: " X \<in> Points \<and> X \<lhd> l" using contained_point assms by blast
  have 11: "(Y \<in> Points) \<and> (Y \<lhd> l) \<longrightarrow> Y = X" using xfacts 1 ch by blast
  obtain P Q R where  "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points
                      \<and> \<not> collinear P Q R  \<and> X \<notin> {P,Q,R}" 
    by (smt (verit) empty_iff four_points_noncollinear_triples insert_iff)
  have 2: "{X} = {A. A\<in>Points \<and> A \<lhd> l}" using 1 \<open>X \<in> Points \<and> X \<lhd> l\<close> ch by blast

  obtain P Q R S where 
    distinct_points: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S" and 
    all_points:"P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points" and 
    parallel_groups: "parallel (join P Q) (join R S) \<and> parallel (join P R) (join Q S)" and
    distinct_lines: "(join P Q) \<noteq> (join R S) \<and> (join P R) \<noteq> (join Q S)" and
    non_collinear_triples: "\<not> collinear P Q R \<and>\<not> collinear P Q S \<and> \<not> collinear P R S \<and> \<not> collinear Q R S" 
    using four_points_parallel_pairs by blast
(* Let's try another: we have 4 distinct lines, in two parallel pairs H and K. *)
  let ?H = "{join P Q, join R S}"
  let ?K = "{join P R, join Q S}"
  have "card ?H = 2 \<and> card ?K = 2" using distinct_lines by auto
(* But each line from H intersects each line from K. *)
  have non_parallel: "\<And>h k . (h \<in> ?H \<and> k \<in> ?K \<Longrightarrow> \<not> parallel h k)" 
  by (metis a1a all_points distinct_lines distinct_points insert_iff parallel_def parallel_groups
      singleton_iff)

(* If l = {X}, then the special point X lies on at most one line in each of H and K. Select 
the (or an) other line in each set, k and n. *)
  obtain h where hset: "h \<in> ?H" and "h \<noteq> l" and x_not_on_h: "\<not> X \<lhd> h"  using distinct_lines
    by (metis insert_iff parallel_def parallel_groups xfacts)
  obtain k where kset: "k \<in> ?K" and "k \<noteq> l" and x_not_on_k: "\<not> X \<lhd> k"  using distinct_lines 
    by (metis insert_iff parallel_def parallel_groups xfacts)
  have lh_par: "parallel l h"  
  using 1 x_not_on_h parallel_def \<open>h \<in> {join P Q, join R S}\<close> assms ch parallel_groups xfacts by auto
  have lk_par: "parallel l k" 
  using 1 x_not_on_k parallel_def \<open>k \<in> {join P R, join Q S}\<close> assms ch parallel_groups xfacts by auto
  have "X \<lhd> l" using xfacts by blast
(* Then find_parallel k X = l and same for n X.*)
  have "find_parallel h X = l" using a2d lh_par parallel_def xfacts by blast 
  have "find_parallel k X = l" using a2d lk_par parallel_def xfacts by blast 
(*That makes both k and n parallel to l, so parallel to each other. *)
  have par_hk: "(k || h)" using lh_par lk_par using parallel_transitive2 by blast   
(* On the other hand, they're also NOT parallel *)
  have nonpar_hk: "\<not> (k || h)" proof
    have 0: "h \<in> {join P Q, join R S} \<and>  k \<in> {join P R, join Q S}" using hset kset by blast
    show "k || h \<Longrightarrow> False" using 0 non_parallel by blast 
  qed
  show False using par_hk nonpar_hk by blast
qed

text \<open>We've now proved the first assertion in the Example after Prop 1.2, and several other
small lemmas that may be useful when we get to later steps. We must also show there
\emph{is} an affine plane with four points. We'll do this two ways: by explicit construction, and
by using the wonderful "nitpick" 'prover'.\<close>


(*
proposition (in affine_plane) five_points_necessary: 
  assumes "finite Points"
  shows "card Points \<ge> 5"
    by nitpick
  oops
*)

datatype a4pt = Pa | Qa | Ra | Sa
definition  "A4Points = {Pa, Qa, Ra, Sa}"
definition "A4PQ = {Pa, Qa}"
definition "A4PR = {Pa, Ra}"
definition "A4PS = {Pa, Sa}"
definition "A4QR = {Qa, Ra}"
definition "A4QS = {Qa, Sa}"
definition "A4RS = {Ra, Sa}"

definition "A4Lines = {A4PQ, A4PR, A4PS, A4QR, A4QS, A4RS}"

fun  A4join::"a4pt \<Rightarrow> a4pt \<Rightarrow> a4pt set"  where 
"A4join x y = (if (x = y) then undefined else {x, y})"


fun A4incid::"a4pt \<Rightarrow> a4pt set \<Rightarrow> bool" where
"A4incid x m = ((m \<in> A4Lines) \<and> (x \<in> m))"

fun A4complement::"a4pt set \<Rightarrow> a4pt set" where
"A4complement n = (if n = A4PQ then A4RS else 
(if n = A4RS then A4PQ else 
(if n = A4PR then A4QS else
(if n = A4QS then A4PR else 
(if n = A4PS then A4QR else 
(if n = A4QR then A4PS else 
undefined))))))"

fun A4find_parallel::"a4pt set \<Rightarrow> a4pt \<Rightarrow> a4pt set"  where
"A4find_parallel m T = (if T \<in> m then m else (A4complement m))"

lemma all_pairs:
  fixes P::a4pt and Q::a4pt
  assumes "P \<noteq> Q" 
  shows "{P, Q} \<in> A4Lines"
  by (metis (full_types) A4Lines_def A4PQ_def A4PR_def A4PS_def 
      A4QR_def A4QS_def A4RS_def a4pt.exhaust assms 
      insert_commute insert_subset subset_insertI)

lemma all_joins_are_lines:
  fixes P Q
  assumes   "P \<noteq> Q" and
  "P \<in> A4Points"  and" Q \<in> A4Points"
shows "A4join P Q \<in> A4Lines"
proof -
  show ?thesis by (simp add: all_pairs assms(1))
qed

theorem PinPQ1:
  fixes P Q
  assumes   "P \<noteq> Q" and
 " P \<in> A4Points"  and" Q \<in> A4Points"
shows "P \<in> A4join P Q"
proof -
  show ?thesis by (simp add: assms(1))
qed

theorem QinPQ1:
  fixes P Q
  assumes   "P \<noteq> Q" and
 " P \<in> A4Points"  and" Q \<in> A4Points"
shows "Q \<in> A4join P Q"
proof -
  show ?thesis by (simp add: assms(1))
qed

theorem
  fixes P Q
  assumes   "P \<noteq> Q" and
  "P \<in> A4Points"  and "Q \<in> A4Points"
shows "A4incid P (A4join P Q)"
proof -
  show ?thesis using assms A4incid.elims A4join.simps all_pairs by auto
qed

theorem
  fixes P Q
  assumes   "P \<noteq> Q" and
 " P \<in> A4Points"  and " Q \<in> A4Points"
shows "A4incid Q (A4join P Q)"
proof -
  show ?thesis using assms A4incid.elims A4join.simps all_pairs by auto
qed

find_theorems name: collinear

theorem  A4affine_plane_a3_lemma:
  shows "Pa \<in> A4Points \<and>
       Qa \<in> A4Points \<and>
       Ra \<in> A4Points" and 
       "Pa \<noteq> Qa \<and>
       Pa \<noteq> Ra \<and>
       Qa \<noteq> Ra" and  
    "\<not>  affine_plane_data.collinear A4Points A4Lines A4incid Pa Qa Ra"
proof -
  show P1: "Pa \<in> A4Points \<and> Qa \<in> A4Points \<and> Ra \<in> A4Points" using A4Points_def by blast
  show P2: "Pa \<noteq> Qa \<and> Pa \<noteq> Ra \<and> Qa \<noteq> Ra" by auto
  show P3: "\<not> affine_plane_data.collinear
           A4Points
           A4Lines
           A4incid Pa Qa Ra"
  proof (rule ccontr)
    assume cHyp: "\<not>\<not>affine_plane_data.collinear
           A4Points
           A4Lines
           A4incid Pa Qa Ra"
    have 2: "(if Pa \<in> A4Points \<and> Qa \<in> A4Points \<and> Ra \<in> A4Points  then (\<exists> l. l \<in> A4Lines \<and> A4incid Pa l \<and> A4incid Qa l \<and> A4incid Ra l) else undefined)"
      using cHyp by (simp add: affine_plane_data.collinear_def)
    then obtain n where 3:"n \<in> A4Lines \<and> A4incid Pa n \<and> A4incid Qa n \<and> A4incid Ra n" using A4Points_def A4Lines_def P1 by auto
    have cP: "(n = {Pa, Qa}) \<or> (n = {Pa, Ra}) \<or> (n = {Pa, Sa})"  
      by (metis (full_types) "3" A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4incid.simps P2 empty_iff insert_iff)
    have cQ: "(n = {Pa, Qa}) \<or> (n = {Qa, Ra}) \<or> (n = {Qa, Sa})"  
      by (metis (full_types) "3" A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4incid.simps P2 empty_iff insert_iff)
    have cPQ: "n = {Pa, Qa}" using cP cQ by blast
    have ncR: "\<not> A4incid Ra n" using A4incid.simps cPQ by auto
    show f: False using ncR 3 by auto
  qed
qed

theorem A4affine_plane_a3: 
  " \<exists>P Q R.
       P \<in> A4Points \<and>
       Q \<in> A4Points \<and>
       R \<in> A4Points \<and>
       P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       \<not> affine_plane_data.collinear
           A4Points
           A4Lines
           A4incid P Q R" 
proof -
  show ?thesis  using A4affine_plane_a3_lemma(1) A4affine_plane_a3_lemma(3) by blast
qed

theorem A4affine_plane_a1a: 
  fixes P Q
  assumes " P \<noteq> Q" and "P \<in> A4Points" and " Q \<in> A4Points" 
  shows "A4join P Q \<in> A4Lines" and "A4incid P (A4join P Q)" and "A4incid Q (A4join P Q)"
proof -
  show "A4join P Q \<in> A4Lines" using all_joins_are_lines using assms by blast
next
  show "A4incid P (A4join P Q)" using A4incid.simps A4join.simps A4Lines_def assms by (simp add: all_pairs)
next
  show "A4incid Q (A4join P Q)" using A4incid.simps A4join.simps A4Lines_def assms by (simp add: all_pairs)
qed

theorem A4affine_plane_a1b:  
  fixes P Q
  assumes 
    "P \<noteq> Q" and 
    "P \<in> A4Points" and  "Q \<in> A4Points" and
    "A4incid P m" and "A4incid Q m"
  shows "m = A4join P Q"
proof -
  show ?thesis by (smt (verit, best) A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4incid.elims(2) A4join.simps assms insertE insert_commute singleton_iff)
qed (* replaced a 250-line proof! *)

lemma A4line_complement:
  fixes l
  assumes "l \<in> A4Lines"
  shows "A4complement l \<in> A4Lines"
  by (smt (verit, best) A4Lines_def A4complement.simps assms empty_iff insert_iff)

lemma A4complement_parallel_helper: 
  fixes n
  assumes "n \<in> A4Lines"
  shows "n \<inter> (A4complement n) = {}"
proof -
  show ?thesis 
    by (smt (verit) A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def 
    Int_insert_right a4pt.distinct(10) a4pt.distinct(12) a4pt.distinct(2) a4pt.distinct(4) a4pt.distinct(6) a4pt.distinct(8) 
    A4complement.elims assms inf.orderE insertE insert_disjoint(2) insert_inter_insert singletonD singleton_insert_inj_eq)
qed

lemma A4disjoint_parallel:
  fixes n k
  assumes "n \<inter> k = {}" and "n \<in> A4Lines" and "k \<in> A4Lines"
  shows "affine_plane_data.parallel A4Points A4Lines A4incid k n"
proof -
  show ?thesis
  using affine_plane_data.parallel_def assms(1) assms(2) assms(3) 
  by (metis A4incid.elims(1) Int_iff empty_iff)
qed

lemma A4complement: 
  fixes n
  assumes "n \<in> A4Lines"
  shows "affine_plane_data.parallel A4Points A4Lines A4incid (A4complement n) n"
proof -
  show ?thesis using A4complement_parallel_helper
    using A4disjoint_parallel A4line_complement assms by auto
qed

theorem A4affine_plane_a2: 
  fixes P l
  assumes "\<not> A4incid P l" 
  assumes "P \<in> A4Points " and "l \<in> A4Lines"
  shows "A4find_parallel l P \<in> A4Lines" and
     "affine_plane_data.parallel A4Points A4Lines A4incid  (A4find_parallel l P) l" and
     "A4incid P (A4find_parallel l P)"
proof -
  show "A4find_parallel l P \<in> A4Lines" using A4line_complement assms(3) by auto
next
  show "affine_plane_data.parallel A4Points A4Lines A4incid  (A4find_parallel l P) l" using A4complement assms by force
next
  show "A4incid P (A4find_parallel l P)" 
  by (smt (verit, del_insts) A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4complement.elims A4find_parallel.elims A4incid.elims(3) Un_iff a4pt.exhaust assms(3) insertI1 insert_is_Un singletonD)
qed

lemma fpp: 
  fixes P l m
  assumes "l \<in> A4Lines" and  "m \<in> A4Lines"
    and  "m \<inter> l = {}" 
  shows  "m = A4complement  l"
proof -
  show ?thesis 
  by (smt (verit) A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4complement.simps assms disjoint_iff_not_equal insert_iff singleton_iff)
qed

theorem A4affine_plane: "affine_plane A4Points A4Lines A4incid A4join A4find_parallel"
proof standard
  show f1a: "\<And>P Q. P \<noteq> Q \<Longrightarrow> P \<in> A4Points \<Longrightarrow> Q \<in> A4Points \<Longrightarrow> A4join P Q \<in> A4Lines \<and> A4incid P (A4join P Q) \<and> A4incid Q (A4join P Q)" 
    using A4affine_plane_a1a by auto
  show f1b: "\<And>P Q m. P \<noteq> Q \<Longrightarrow> P \<in> A4Points \<Longrightarrow> Q \<in> A4Points \<Longrightarrow> A4incid P m \<Longrightarrow> A4incid Q m \<Longrightarrow> m = A4join P Q"
    using A4affine_plane_a1b by auto    
  show f2a: "\<And>P l. P \<in> A4Points \<Longrightarrow>
           l \<in> A4Lines \<Longrightarrow>
           A4find_parallel l P \<in> A4Lines" using A4line_complement by auto
  show f2b: "\<And>P l. P \<in> A4Points \<Longrightarrow>
           l \<in> A4Lines \<Longrightarrow>
           affine_plane_data.parallel A4Points
            A4Lines A4incid (A4find_parallel l P)
            l" by (metis A4affine_plane_a2(2) A4find_parallel.simps A4incid.simps affine_plane_data.parallel_reflexive) 
  show f2c: "\<And>P l. P \<in> A4Points \<Longrightarrow>
           l \<in> A4Lines \<Longrightarrow>
           A4incid P
            (A4find_parallel l P)"  using A4affine_plane_a2(3) by auto
  show f2d:"\<And>P l m.
       P \<in> A4Points \<Longrightarrow>
       l \<in> A4Lines \<Longrightarrow>
       m \<in> A4Lines \<Longrightarrow>
       affine_plane_data.parallel
        A4Points A4Lines
        A4incid m l \<Longrightarrow>
       A4incid P m \<Longrightarrow>
       m =
       A4find_parallel l P" 
  proof -
    fix P l m 
    assume h1: "P \<in> A4Points" and "l \<in> A4Lines" and  "m \<in> A4Lines"
    assume h2: "A4incid P m"
    assume h3: "affine_plane_data.parallel
        A4Points A4Lines A4incid m
        l"
    from h3 have  h4: "(l=m) \<or>( (\<not> (\<exists> T. T \<in> A4Points \<and> A4incid T l \<and> A4incid T m)) \<and> (l \<in> A4Lines) \<and> (m \<in> A4Lines))" 
      by (metis affine_plane_data.parallel_def)
    show "m = A4find_parallel l P"
    proof (cases "l = m")
      case True
      then show ?thesis using h2 by auto
    next
      case False
      from h4 False have h5: "( (\<not> (\<exists> T. T \<in> A4Points \<and> A4incid T l \<and> A4incid T m)) \<and> (l \<in> A4Lines) \<and> (m \<in> A4Lines))" by auto
      from h1 h5 have h6: "\<not> (\<exists> T. T \<in> A4Points \<and> A4incid T l \<and> A4incid T m)" by auto
      have q: "A4incid T l ==> T \<in> A4Points" using A4Points_def a4pt.exhaust by blast
      have h7: "\<not> (\<exists> T. A4incid T l \<and> A4incid T m)" using h6 q by (metis (full_types) A4Points_def a4pt.exhaust insertCI)  
      from h7 have 8: "l \<inter> m = {}" by (simp add: disjoint_iff h5)
      show ?thesis using 8 fpp  by (metis A4find_parallel.simps \<open>l \<in> A4Lines\<close> \<open>m \<in> A4Lines\<close> f2c h1 h2 h7 inf_commute)     
    qed
  qed
next
  show " \<exists>P Q R.
       P \<in> A4Points \<and>
       Q \<in> A4Points \<and>
       R \<in> A4Points \<and>
       P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       \<not> affine_plane_data.collinear
           A4Points A4Lines A4incid
           P Q R" using A4affine_plane_a3 by blast
qed


(* ======================Switch to talking about A2, real affine 2-space =================*)

datatype a2pt = A2Point "real" "real"
datatype a2ln = A2Ordinary "real" "real" 
  | A2Vertical "real"

definition A2Points::"a2pt set"
  where "A2Points \<equiv> (UNIV::a2pt set)"

definition A2Lines::"a2ln set"
  where "A2Lines \<equiv> (UNIV::a2ln set)"

text "Ordinary m b represents the line y = mx+b; Vertical xo is the line x = xo. With this in 
mind, we define the  `incid' operation for this purported plane, using cases for the definition."

text\<open> There's a problem here, though: for A2Ordinary, we have to have the "m" term be nonzero,
so we need to define a set Lines; the set Points is just all a2pts\<close>

fun a2incid :: "a2pt \<Rightarrow> a2ln \<Rightarrow> bool" where
"a2incid (A2Point x y) (A2Ordinary m b) = (y = m*x + b)" |
"a2incid (A2Point x y) (A2Vertical xi) = (x = xi)"

definition a2parallel:: "a2ln  \<Rightarrow> a2ln \<Rightarrow> bool" (infix "a2||" 50)
      where "l a2|| m \<longleftrightarrow> (l = m \<or>  (\<forall> P. (\<not> a2incid P l)  \<or> (\<not>a2incid P m)))"
  
text\<open> Notice that I've written the definition of parallel for the euclidean affine plane
as a forall rather than exists. I think this might make things easier.\<close>


text\<open> To make this work in 2025, I need to provide a join and find_parallel function\<close>
fun a2join :: "a2pt \<Rightarrow> a2pt \<Rightarrow> a2ln" where
"a2join (A2Point x1 y1) (A2Point x2 y2) = (if ((x1 = x2)  \<and> (y1 = y2)) then undefined else if (x1 = x2) then A2Vertical(x1) else 
(A2Ordinary ((y2 - y1)/(x2-x1)) (y1 - x1* (y2 - y1)/(x2-x1))))"

fun a2find_parallel::"a2ln \<Rightarrow> a2pt \<Rightarrow> a2ln" where
"a2find_parallel (A2Ordinary m b) (A2Point x y)  = (A2Ordinary m (y-m*x))" |
"a2find_parallel  (A2Vertical xi) (A2Point x y) = (A2Vertical x)"

text\<open>Now we'll write some small lemmas, basically establishing the three axioms.\<close>

  text\<open>
A note about naming: Everything related to real-affine-2-space will be written with a prefix
``A2''. When we want to state axiom 3 for A2, we'll write ``A2\_a3''. Sometimes we'll need some preliminary
results, and we'll append an ``a'' or ``b'' or ``c'', etc., before stating the main result.  \<close>

theorem A2_a1a1: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2join P Q \<in> A2Lines"
proof -
  show ?thesis   by (simp add: A2Lines_def)
qed



theorem A2_a1a2: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2incid P (a2join P Q)"
proof -
  show ?thesis
  proof -
    fix x0 y0 assume Pcoords: "P = (A2Point x0 y0)"
    fix x1 y1 assume Qcoords: "Q = (A2Point x1 y1)" 
    have 0: "a2incid P (a2join P Q)" 
    proof (cases "(x0 = x1)")
      case True (* Case where x0 = x1 *)
      have 0: "a2join P Q =  A2Vertical x0" using True assms Pcoords Qcoords by auto
      have 1: "a2incid P (A2Vertical x0)" using True assms Pcoords a2incid.simps by blast
      thus "a2incid P (a2join P Q)" using 0 1 by auto
    next
      case False
      have 0: "a2join P Q =  (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))" using False assms Pcoords Qcoords a2join.simps by auto
      have 1: "a2incid P (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))" using False assms Pcoords a2incid.simps by simp
      thus "a2incid P (a2join P Q)" using 0 1 by auto
    qed 
  next
    show 1: "a2incid P (a2join P Q)" 
      by (smt (verit, ccfv_threshold) a2join.elims a2ln.simps(1) a2ln.simps(3) a2incid.elims(3) a2incid.simps(2) a2pt.inject assms(1) mult.commute times_divide_eq_left)
  qed
qed

theorem A2_a1a3: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2incid Q (a2join P Q)"
proof -
  obtain x0 y0 where Pcoords: "P = (A2Point x0 y0)" using a2pt.exhaust by auto
  obtain x1 y1 where Qcoords: "Q = (A2Point x1 y1)" using a2pt.exhaust by auto
  have 0: "a2incid Q (a2join P Q)" 
    proof (cases "(x0 = x1)")
      case True (* Case where x0 = x1 *)
      have 0: "a2join P Q =  A2Vertical x0" using True assms Pcoords Qcoords by auto
      have 1: "a2incid Q (A2Vertical x0)" using True assms Qcoords a2incid.simps by blast
      thus "a2incid Q (a2join P Q)" using 0 1 by auto
    next
      case False
      have 0: "a2join P Q =  (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))" using False assms Pcoords Qcoords a2join.simps by auto
      have 1: "a2incid Q (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))" 
      proof -
        have J1: "a2incid Q (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0))) = 
          a2incid (A2Point x1 y1) (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))" using Qcoords by auto
        have J2: "(a2incid (A2Point x1 y1) (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))) = 
          (y1 = (((y1 - y0)/(x1-x0))*x1 +  (y0 - x0* (y1 - y0)/(x1-x0))))" using a2incid.simps by blast
        have J3: "(y1 = (((y1 - y0)/(x1-x0))*x1 +  (y0 - x0* (y1 - y0)/(x1-x0)))) =
                (y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0 - x0* (y1 - y0)/(x1-x0))))"  by (simp add: left_diff_distrib')
        have J4: "(y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0 - x0* (y1 - y0)/(x1-x0)))) = 
              (y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0 - (x0*y1 - x0*y0)/(x1-x0))))"  by (simp add: right_diff_distrib)
        have J5: "(y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0 - (x0*y1 - x0*y0)/(x1-x0)))) =
              (y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0*(x1-x0)/(x1-x0) - (x0*y1 - x0*y0)/(x1-x0))))"  using False by auto
        have J6: "(y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0*(x1-x0)/(x1-x0) - (x0*y1 - x0*y0)/(x1-x0)))) =
              (y1 = (((y1*x1 - y0*x1 + y0*(x1-x0))/(x1-x0))  - (x0*y1 - x0*y0)/(x1-x0)))" by argo
        have J7: "(y1 = (((y1*x1 - y0*x1 + y0*(x1-x0))/(x1-x0))  - (x0*y1 - x0*y0)/(x1-x0))) = 
              (y1 = (((y1*x1 - y0*x1 + y0*(x1-x0) -(x0*y1 - x0*y0) )/(x1-x0))))" by argo
        have J8: "(y1 = (((y1*x1 - y0*x1 + y0*(x1-x0) -(x0*y1 - x0*y0) )/(x1-x0)))) = 
                  (y1 = (((y1*x1 - y0*x1 + y0*x1-y0*x0) - x0*y1 + x0*y0)/(x1-x0)))" by argo
        have J9: "(y1 = (((y1*x1 - y0*x1 + y0*x1-y0*x0) - x0*y1 + x0*y0)/(x1-x0))) =
                  (y1 = ((y1*x1 - y0*x1 + y0*x1 - x0*y1 )/(x1-x0)))" by argo
        have J10: "(y1 = ((y1*x1 - y0*x1 + y0*x1 - x0*y1 )/(x1-x0))) =
                   (y1 = ((y1*(x1-x0) )/(x1-x0)))" by argo
        have J11: "(y1 = ((y1*(x1-x0) )/(x1-x0)))" using False by auto
        show ?thesis using J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 by auto
      qed
      thus 3:?thesis using 0 by simp
    qed
    show ?thesis using 0 by auto
  qed 

theorem A2_a1a: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2join P Q \<in> A2Lines" and "a2incid P (a2join P Q)" and "a2incid Q (a2join P Q)"
proof -
  show "a2join P Q \<in> A2Lines" using assms A2_a1a1 by blast
  show "a2incid P (a2join P Q)" using assms A2_a1a2 by blast
  show "a2incid Q (a2join P Q)" using assms A2_a1a3 by blast
qed

text\<open>\done For this next theorem, it might make sense to phrase it as "P notequal Q lets us derive a unique
line l such that..."
but that would require proving the existence of l (which we just did in the previous lemma) and
then proving that it's unique. Instead, we can just say that if l and m both contain the 
distinct points P and Q, then l must equal m. From this, and the previous lemma, we can then 
conclude that axiom 1 is true (which we'll do in a final theorem). 

This is arguably the ugliest theorem in the bunch, because it involves four cases (one each for 
l and m being ordinary or vertical). Once again, we start by providing names for the constructor
arguments for P and Q:
 \seiji\<close>

lemma A2_a1b: 
  fixes P :: a2pt
  fixes Q
  fixes l
  assumes pq: "P \<noteq> Q"
  assumes pl : "a2incid P l"
  assumes ql : "a2incid Q l"
  shows "l = a2join P Q"

proof - 
  obtain x0 y0 where Pcoords: "P = (A2Point x0 y0)"  using a2pt.exhaust by auto
  obtain x1 y1 where Qcoords: "Q = (A2Point x1 y1)"  using a2pt.exhaust by auto
  show ?thesis
  proof (cases "(x0 = x1)")
    case True
    then show ?thesis using Pcoords Qcoords a2incid.elims(2) pl pq ql by fastforce
  next  
    case False
    obtain m b  where Lcoords: "l = (A2Ordinary m b)" using False a2join.simps
    by (metis Pcoords Qcoords a2ln.exhaust a2incid.simps(2) pl ql)

    have 1: "(a2incid P l) = (m*x0 + b = y0)" using False a2incid.simps Lcoords Pcoords by auto
    have 2: "(a2incid Q l) = (m*x1 + b = y1)" using False a2incid.simps Lcoords Qcoords by auto
    have 3: "m * (x1 - x0) = y1 - y0" using 1 2 pl ql by argo
    have 4: "m = (y1 - y0)/(x1 - x0)" using False 3 by (simp add: nonzero_eq_divide_eq)
    have 5: " (y1 - y0)/(x1 - x0)*x1 + b = y1" using 2 4 assms by auto
    have 6: "b = y1 - x1* (y1 - y0)/(x1 - x0)" using 5 by argo
    thus ?thesis using 1 4 6 Lcoords Pcoords Qcoords a2join.simps False 
    by (metis  add.commute  eq_diff_eq mult.commute pl times_divide_eq_right)
  qed
qed

(* (A2Ordinary ((y2 - y1)/(x2-x1)) (y1 - x1* (y2 - y1)/(x2-x1))))" *)


text \<open>\done Whew! We've proved axiom 1 for the real affine plane. On to Axiom 2. This one's 
a little trickier because we're proving a conjunction. \caleb\<close>


(*
    a2: "\<lbrakk>\<not> P \<lhd> l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> 
    find_parallel l P \<in> Lines \<and> ( find_parallel l P) || l \<and> P \<lhd> (find_parallel l P)" and
*)

lemma A2_a2a:
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> (a2incid P l)"
  assumes "P \<in> A2Points" and "l \<in> A2Lines" (* vacuous here, but parallel to the A4 case *)
  shows  "a2find_parallel l P \<in> A2Lines"
proof -
  show ?thesis using A2Lines_def by auto
qed


(*
fun a2find_parallel::"a2ln \<Rightarrow> a2pt \<Rightarrow> a2ln" where
"a2find_parallel (A2Ordinary m b) (A2Point x y)  = (A2Ordinary m (y-m*x))" |
"a2find_parallel  (A2Vertical xi) (A2Point x y) = (A2Vertical x)"

*)
lemma A2_a2b:
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> (a2incid P l)"
  assumes "P \<in> A2Points" and "l \<in> A2Lines" (* vacuous here, but parallel to the A4 case *)
  shows   "(a2find_parallel l P) a2|| l"
proof -
  obtain x0 y0 where Pcoords: "P = (A2Point x0 y0)" using a2incid.elims by metis
  show ?thesis 
  proof (cases l)
    case (A2Vertical x1)
    have 0: "a2find_parallel l P = A2Vertical x0" using a2find_parallel.cases assms  A2Vertical Pcoords by simp 
    have 1: "A2Vertical x0 a2|| l"  by (metis A2Vertical a2incid.simps(2) a2parallel_def a2pt.exhaust)
    thus ?thesis using 0 1 by auto
  next
    case (A2Ordinary m b)
    have 0: "a2find_parallel l P = (A2Ordinary m (y0-m*x0))" using a2find_parallel.cases assms  A2Ordinary Pcoords by simp 
    thus ?thesis using 0 a2parallel_def assms Pcoords a2incid.elims by (smt (verit) A2Ordinary a2incid.simps(1))
  qed
qed

lemma A2_a2c:
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> (a2incid P l)"
  assumes "P \<in> A2Points" and "l \<in> A2Lines" (* vacuous here, but parallel to the A4 case *)
  shows  "a2incid P  (a2find_parallel l P)" 
proof -
  obtain x0 y0 where Pcoords: "P = (A2Point x0 y0)" using a2incid.elims by metis
  show ?thesis 
  proof (cases l)
    case (A2Vertical x1)
    have 0: "a2find_parallel l P = A2Vertical x0" using a2find_parallel.cases assms  A2Vertical Pcoords by simp 
    have 1: "a2incid P (A2Vertical x0)" using Pcoords a2incid.simps A2Vertical by auto
    thus ?thesis using 0 1 by auto
  next
    case (A2Ordinary m b)
    have 0: "a2find_parallel l P = (A2Ordinary m (y0-m*x0))" using a2find_parallel.cases assms  A2Ordinary Pcoords by simp 
    have 1: "a2incid P (A2Ordinary m (y0-m*x0))" using Pcoords a2incid.simps A2Ordinary by auto
    thus ?thesis using 0 1 by auto 
  qed
qed

lemma a2parallel_caseV:
  fixes l and k and x0 and m and b
  assumes "l = A2Vertical x0"
  assumes "k = A2Ordinary m b"
  shows "a2incid (A2Point x0 (m*x0 + b)) l" and "a2incid (A2Point x0 (m*x0 + b)) k"
  and "\<not> l a2|| k"
proof -
  show 0: "a2incid (A2Point x0 (m * x0 + b)) l" using assms by auto
next
  show 1:"a2incid (A2Point x0 (m * x0 + b)) k" using assms by auto
next
  show " \<not> l a2|| k" 
  using a2incid.simps(1) a2incid.simps(2) a2parallel_def assms(1) assms(2) by blast
qed


lemma a2parallel_caseOa:
  fixes l and k and  m1 and b1 and m2 and b2
  assumes "m1 \<noteq> m2"
  assumes "l = A2Ordinary m1 b1"
  assumes "k = A2Ordinary m2 b2"
  shows "a2incid (A2Point (-(b1 - b2)/(m1-m2)) (m1* (-(b1 - b2)/(m1-m2)) + b1)) l" and 
   "a2incid (A2Point (-(b1 - b2)/(m1-m2)) (m1* (-(b1 - b2)/(m1-m2)) + b1)) k" 
proof -
  have 0: "a2incid
     (A2Point (- (b1 - b2) / (m1 - m2))
       (m1 * (- (b1 - b2) / (m1 - m2)) + b1))
     l = a2incid
     (A2Point (- (b1 - b2) / (m1 - m2))
       (m1 * (- (b1 - b2) / (m1 - m2)) + b1))
     (A2Ordinary m1 b1)" using assms by auto
  also have "... = ((m1 * (- (b1 - b2) / (m1 - m2)) + b1 = (m1 * (- (b1 - b2) / (m1 - m2)) + b1)))" using a2incid.elims by auto
  also have "..." by simp
  thus  "a2incid
     (A2Point (- (b1 - b2) / (m1 - m2))
       (m1 * (- (b1 - b2) / (m1 - m2)) + b1))
     l" using calculation by auto 
next
   have 0: "a2incid
     (A2Point (- (b1 - b2) / (m1 - m2))
       (m1 * (- (b1 - b2) / (m1 - m2)) + b1))
     k = a2incid
     (A2Point (- (b1 - b2) / (m1 - m2))
       (m1 * (- (b1 - b2) / (m1 - m2)) + b1))
     (A2Ordinary m2 b2)" using assms by auto
   also have "... = ((m2 * (- (b1 - b2) / (m1 - m2)) + b2 = (m1 * (- (b1 - b2) / (m1 - m2)) + b1)))" using a2incid.elims by auto
   also have "... = ( (- m2*(b1 - b2) / (m1 - m2) + b2 =  (- m1* (b1 - b2) / (m1 - m2)) + b1))" by argo 
   also have "... = ( (- m2*(b1 - b2)   + b2*(m1 - m2) =  (- m1* (b1 - b2) ) + b1*(m1 - m2)))" using assms(1)
   by (smt (verit, best) add_divide_eq_if_simps(2) divide_cancel_right)
   also have "... = (( -m2*b1 + m2*b2   + b2*m1 - b2*m2 =  (- m1*b1 + m1*b2)  + b1*m1 - b1*m2))" by argo
   also have "... = ((     b2*m1  =  (- m1*b1 + m1*b2)  + b1*m1 ))" by argo
   also have "..." by argo
  thus "a2incid
     (A2Point (- (b1 - b2) / (m1 - m2))
       (m1 * (- (b1 - b2) / (m1 - m2)) + b1))
     k" using calculation by auto 
qed

lemma a2parallel_caseO:
  fixes l and k and x0 and m1 and b1 and m2 and b2
  assumes "m1 \<noteq> m2"
  assumes "l = A2Ordinary m1 b1"
  assumes "k = A2Ordinary m2 b2"
  shows "\<not> k a2|| l"
proof -
  show ?thesis using assms
  by (metis a2ln.inject(1) a2incid.simps(1) a2parallel_caseOa(2) a2parallel_def)
qed



lemma A2_a2d:
  fixes P and l and k 
  assumes  "P \<in> A2Points" and  "l \<in> A2Lines" and  "k \<in> A2Lines" and "k a2|| l" and "a2incid P k"
  shows "k = a2find_parallel l P"
proof - 
  obtain x0 y0 where Pcoords: "P = (A2Point x0 y0)" using a2pt.exhaust by auto
  have 0: "k a2|| l =  (l = k \<or>  (\<forall> P. (\<not> a2incid P l)  \<or> (\<not>a2incid P k)))" using assms a2parallel_def by auto
  show ?thesis
  proof (cases l)
    case (A2Vertical x1)
    have 1: "a2find_parallel l P = A2Vertical x0" using a2find_parallel.cases assms  A2Vertical Pcoords by simp 
    show ?thesis
    proof (cases "l = k")
      case True
      then show ?thesis using A2Vertical Pcoords assms(5) by force
    next
      case False
      have 2: "\<forall> S. (\<not> a2incid S l)  \<or> (\<not>a2incid S k)" using assms False a2parallel_def by auto
      then show ?thesis 
      by (metis "1" A2Vertical Pcoords a2ln.exhaust a2incid.simps(2) a2parallel_caseV(3) a2parallel_def assms(5))
  qed
next
    case  ql:(A2Ordinary m b)
    then show ?thesis
    proof -
      have 0: "a2find_parallel l P = (A2Ordinary m (y0-m*x0))" using a2find_parallel.cases assms  ql Pcoords by simp 
      show ?thesis
      proof (cases k)
        case (A2Vertical x2)
        have "False" using ql A2Vertical a2parallel_caseV(3) assms(4) by auto
        then show ?thesis by auto
      next
        case qk:(A2Ordinary mk bk)
        then show ?thesis 
        proof -
          have a0: "mk = m" 
            by (metis qk ql  a2parallel_caseO assms(4))
          have a1: "a2incid P k"  using assms by auto 
          have a2: "mk*x0 + bk = y0" using a1 Pcoords qk by auto 
          have a3: "m*x0 + bk = y0" using a0 a2 assms by auto
          have a4: "bk = y0 - m*x0" using a3 by argo
          have a5: "k = A2Ordinary m (y0 - m*x0)" using a0 a4 qk by blast
          thus ?thesis using 0 a5 by auto
        qed
      qed
    qed
  qed
qed



lemma A2_a2abc:
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> (a2incid P l)"
  assumes "P \<in> A2Points" and "l \<in> A2Lines" 
  shows  
    "a2find_parallel l P \<in> A2Lines" and   
    "(a2find_parallel l P) a2|| l" and 
    "a2incid P  (a2find_parallel l P)"  
proof -
  show "a2find_parallel l P \<in> A2Lines" using A2_a2a A2Lines_def by auto 
  show "(a2find_parallel l P) a2|| l" using A2_a2b assms by auto
  show "a2incid P  (a2find_parallel l P)" using assms A2_a2c by auto
qed

(*
    a2: "\<lbrakk>\<not> P \<lhd> l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> find_parallel l P \<in> Lines \<and> ( find_parallel l P) || l \<and> P \<lhd>  (find_parallel l P)" and
    a3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)"
*)
lemma A2_a3:
  shows  "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> (\<nexists> m. a2incid P m \<and> a2incid Q m \<and> a2incid R m)"
proof -
  obtain P where P: "P = (A2Point 0 0)" by simp
  obtain Q where Q: "Q = (A2Point 1 0)" by simp
  obtain R where R: "R = (A2Point 0 1)" by simp

  have "(\<nexists> m. a2incid P m \<and> a2incid Q m \<and> a2incid R m)"
    by (metis A2_a1b P Q R a2incid.simps(2) a2pt.inject zero_neq_one)

  thus ?thesis 
  by (metis (full_types) P a2pt.inject zero_neq_one)
qed

text\<open>\done \done\<close>


text\<open> At this point we've established that the Cartesian Plane satisfies Cartesian 
versions of the three axioms, etc., but it'd be nice to be able to say that as
a *structure*, it matches the Isabelle "locale" that we defined. \caleb \seiji 
\<close>

theorem A2_affine: "affine_plane A2Points A2Lines a2incid a2join a2find_parallel"
  unfolding affine_plane_def
proof (intro conjI)
  show 11: "\<forall>P Q. P \<noteq> Q \<longrightarrow>
            P \<in> A2Points \<longrightarrow>
            Q \<in> A2Points \<longrightarrow>
            a2join P Q
            \<in> A2Lines \<and>
            a2incid P
             (a2join P Q) \<and>
            a2incid Q
             (a2join P Q)"   using A2_a1a A2_a1b by auto    
next
  show 12: "\<forall>P Q m.
       P \<noteq> Q \<longrightarrow>
       P \<in> A2Points \<longrightarrow>
       Q \<in> A2Points \<longrightarrow>
       a2incid P m \<longrightarrow>
       a2incid Q m \<longrightarrow>
       m = a2join P Q" using A2_a1b by auto
next
  show 2: " \<forall>P l.
          P \<in> A2Points \<longrightarrow>
          l \<in> A2Lines \<longrightarrow>
          a2find_parallel l P \<in> A2Lines" 
    using A2_a2a A2_a2b A2_a2c a2parallel_def affine_plane_data.parallel_def A2Lines_def by auto
next
  show 2: " \<forall>P l. P \<in> A2Points \<longrightarrow>
          l \<in> A2Lines \<longrightarrow>
          affine_plane_data.parallel
           A2Points A2Lines
           a2incid
           (a2find_parallel l
             P)
           l" using A2_a2d A2Lines_def A2_a2b iso_tuple_UNIV_I a2parallel_def 
              affine_plane_data.parallel_def  by (smt (verit, best))
next
  show 2: " \<forall>P l. P \<in> A2Points \<longrightarrow>
          l \<in> A2Lines \<longrightarrow>
          a2incid P
           (a2find_parallel l
             P)" using A2_a2d A2_a2b A2_a2c a2parallel_def by metis
next
  show "\<forall>P l m.
       P \<in> A2Points \<longrightarrow>
       l \<in> A2Lines \<longrightarrow>
       m \<in> A2Lines \<longrightarrow>
       affine_plane_data.parallel
        A2Points A2Lines
        a2incid m l \<longrightarrow>
       a2incid P m \<longrightarrow>
       m = a2find_parallel l P" using A2_a2d A2Points_def  a2parallel_def affine_plane_data.parallel_def UNIV_I by metis 
  show 3: "\<exists>P Q R.
       P \<in> A2Points \<and>
       Q \<in> A2Points \<and>
       R \<in> A2Points \<and>
       P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       \<not> affine_plane_data.collinear
           A2Points A2Lines
           a2incid P Q R" using A2_a3  A2Points_def UNIV_I affine_plane_data.collinear_def by (smt (verit))
(* Yay! We've proved the euclidean plane is an affine plane! *)
qed

text  \<open> 
\spike
Completion of an affine plane to a projective plane 

Small problem: we need a data type for the points of the projective plane, which consists of
     all points of the affine plane together with all ideal points (i.e., line pencils), and we 
     need another for the lines of the PP, which consists of all lines of the affine plane (extended 
     by their associated ideal point) and the line at infinity consisting of all ideal points. We'll
     return to this, but first we need axioms for a projective plane.

2020: The main problem is that we really, really need quotient types; with luck, Haoze and Daniel will 
soon have worked these out for us so that we can proceed. 

2025: Actually, now that we have carrier sets for points and lines, we don't need quotient types,
which is good because you cannot use \isi{quotient_type} within a locale, because the resulting type
ends up dependent on any \emph{values} used to define the local (in our case, things like \isi{incid}, 
and this requires a notion of so-called 'dependent types', which Isabelle/HOL does not support. (Shoutout
to Lean here: it's based on dependent types, so this particular bit would be much nicer in Lean.)
\done
\<close>
  
text  \<open> 
\begin{hartshorne}
\section*{Ideal points and the projective plane}

We will now complete the affine plane by adding certain ``points at infinity'' and thus arrive at 
the notion of the projective plane.

Let $A$ be an affine plane. For each line $l \in A,$ we will denote by $[l]$ the pencil of lines 
parallel to $l,$ and we will call $[l]$ an ``ideal point,'' or ``point at infinity,'' in the 
direction of $l.$ We write $P^{*} = [l]$.

We define the completion $S$ of $A$ as follows. The points of $S$ are the points of $A,$ plus all 
the ideal points of $A.$ A line in $S$ is either

\begin{enumerate}
\item An ordinary line $l$ of $A,$ plus the ideal point $P^{*} = [l]$ of $l$, or 
\item the ``line at infinity,'' consisting of all the ideal points of $A.$
\end{enumerate}

We will see shortly that $S$ is a projective plane, in the sense of the following definition.

\defn[Projective Plane] A ``projective plane'' $S$ is a set, whose elements are called points, 
and a set of subsets, called lines, satisfying the following four axioms.
\begin{enumerate}
\item[P1] Two distinct points $P, Q$ of $S$ lie on one and only one line. 
\item[P2] Any two lines meet in at least one point.
\item[P3] There exist three non-collinear points.
\item[P4] Every line contains at least three points.
\end{enumerate}

Let's go ahead and make a locale description for a projective plane, as we did for an affine plane. 

There's no need for a \isi{find_parallel} function this time, but other things are fairly similar.
\<close>

locale projective_plane_data =
  fixes Points :: "'p set" and Lines :: "'l set" and incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool" (infix "\<lhd>" 60)
begin

definition (in projective_plane_data) pcollinear :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
    where "pcollinear A B C = (if (A \<in> Points \<and> B \<in> Points \<and> C \<in> Points)  
  then (\<exists> l. l \<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l \<and> C \<lhd> l) else undefined)"

definition (in projective_plane_data) coincident :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
    where "coincident n k m  = (if (n \<in> Lines) \<and> (k \<in> Lines) \<and> (m  \<in> Lines)
  then (\<exists> P. P \<in> Points \<and> P \<lhd> n \<and> P \<lhd> k \<and> P \<lhd> m) else undefined)"
end (* projective_plane_data *)

(* 
locale affine_plane =
     affine_plane_data Points Lines incid join find_parallel
     for
     Points :: "'p set" and
     Lines :: "'l set" and
     incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool" and
     join:: "'p \<Rightarrow> 'p \<Rightarrow> 'l" and
     find_parallel:: "'l \<Rightarrow> 'p \<Rightarrow> 'l" +
*)

locale projective_plane = projective_plane_data Points Lines incid
  for
     Points :: "'p set" and
     Lines :: "'l set" and
     incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"  (infix "\<lhd>" 60)  + 
assumes
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k . k \<in> Lines \<and> P \<lhd> k  \<and> Q \<lhd>  k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = { P . (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
(*    p4: "\<lbrakk>k \<in> Lines; U = { P . (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> S \<noteq> Q \<and> Q \<noteq> R \<and> R \<noteq> S" *)
begin

(* To be added once the necessary lemmas are proved:

definition meet::"'l \<Rightarrow> 'l \<Rightarrow> 'p" (infix "." 60) where
"meet n k = (if n \<in> Lines \<and> k \<in> Lines \<and> n \<noteq> k then  THE P . P \<lhd> n \<and> P \<lhd> k) else undefined)"

definition join::"'p \<Rightarrow> 'p \<Rightarrow> 'l" (infix "\<^bold>" 60) where
"join P Q = (if P \<in> Points \<and> Q \<in> Points \<and> P \<noteq> Q then THE k . P \<lhd> k \<and> Q \<lhd> k) else undefined"

*)

end
(* right above here is where many small theorems about projective planes should go, theorems like "any
two lines in a projective plane have the same cardinality", etc. -- Spike *)

text \<open>
\hartshorne
\prop[1.3] The completion $S$ of an affine plane $A,$ as described above, is a projective plane.

\proof. We must verify the four axioms P1–P4 of the definition. 
\done
\spike
We'll define the projectivization of the incid function for an affine plane, but to do so, we'll first
have to define a ('p, 'l) projective point and a ('p, 'l) projective line, which we'll call 'ppoint and 'pline,
to be the types of the "point" and "line" sets in the projectivization of an affine plane that uses 
types 'p and 'l for its points and lines. 
\done

       
P1. Let $P,Q  \in S$.
\begin{enumerate}
\item If $P,Q$  are ordinary points of $A,$ then $P$ and $Q$ lie on only one line of $A.$ They do not 
lie on the line at infinity of $S,$ hence they lie on only one line of $S.$

\item If $P$ is an ordinary point, and $Q = [l]$ is an ideal point, we can find by A2 a line $m$ 
such that $P \in m$ and $m \parallel l$,i.e. $m \in [l]$,so that $Q$  lies on the extension of $m$ 
to $S.$ This is clearly the only line of $S$ containing $P$ and $Q.$

\item If $P, Q$ are both ideal points, then they both lie on the line of $S$ containing them.
\end{enumerate}

P2. Let $l, m$ be lines. 
\begin{enumerate}
\item If they are both ordinary lines, and $l \nparallel m,$ then they meet
in a point of $A.$ If $l \parallel m,$ then the ideal point $P^{*} =[l]=[m]$ lies on both $l$ and
$ m$ in $S.$
\item If $l$ is an ordinary line, and $m$ is the line at infinity, then $P^{*} = [l]$ lies on 
both $l$ and $m.$
\end{enumerate}

P3. Follows immediately from A3. One must check only that if $P,Q,R$ are non-collinear in $A,$ then
 they are also non-collinear in $S.$ Indeed, the only new line is the line at infinity, 
which contains none of them.

P4. Indeed, by Problem 1, it follows that each line of $A$ contains at least two points. 
Hence, in $S$ it has also its point at infinity, so has at least three points. \endproof

Examples. 

\begin{enumerate}
\item By completing the real affine plane of Euclidean geometry, we obtain the real projective plane.
\item By completing the affine plane of $4$ points, we obtain a projective plane with $7$ points.
\item Another example of a projective plane can be constructed as follows: let $\Bbb R^3$ be 
ordinary Euclidean 3-space, and let $O$ be a point of $\Bbb R^3.$ Let $L$ be the set of lines 
through $O.$

We define a point of $L$ to be a line through $O$ in $\Bbb R^3.$ We define a line of $L$ to be 
the collection of lines through $O$ which all lie in some plane through $O.$
Then $L$ satisfies the axioms P1–P4 (left to the reader), and so it is a projective plane.
\end{enumerate}
\end{hartshorne}
\spike
We'll go ahead and formalize the notion of projective plane as we did earlier; we won't prove 
proposition 1.3 (in Isabelle) until we have a good tool for quotient types, but we'll proceed 
with the work on the 7-point plane, etc.
\done
\<close>           

text\<open>OK, so it's time to define a parameterized datatype for the points and lines of a 
projectivized affine plane. We'll call these new types 'projPoint' and 'projLine'.\<close>


datatype ('point, 'line) projPoint = OrdinaryP 'point | Ideal "'line set"
datatype ('point, 'line) projLine = OrdinaryL 'line | Infty 

text \<open> To construct the projective "join" operation (i.e., to prove property p1, 
we need to be able to join an ordinary point
P to an ideal point \isi{Ideal t}, where t is a line-pencil. If t consists of all lines parallel to
some line m, then \isi{find_parallel m P} gives such a line. But we need to show that this result 
doesn't depend on which representative line m we choose from then pencil $t$. The following 
lemma shows that.\<close>

lemma AB:
  fixes Points::"'p set" 
  fixes Lines::"'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"  (infix "\<lhd>" 60) 
  fixes join::"'p \<Rightarrow> 'p \<Rightarrow> 'l" 
  fixes find_parallel::"'l \<Rightarrow> 'p \<Rightarrow> 'l"
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines "lp \<equiv> affine_plane_data.line_pencil Points Lines incid"
  assumes "P \<in> Points"
  defines pp: "pPoints \<equiv>  {OrdinaryP R | R. (R \<in> Points)} \<union> {Ideal s | s k . (k \<in> Lines) \<and> s = lp k}" 
  assumes "Ideal t \<in> pPoints" 
  shows "\<exists>! k \<in> Lines . k \<in> t \<and> P \<lhd> k"

proof -
  obtain u where 0:" (u \<in> Lines) \<and> (t = lp u)"  using assms(4) pp  using assms(5) by blast
  have 1: "(find_parallel u P) \<in> Lines \<and> P \<lhd> (find_parallel u P)" 
    by (meson "0" affine_plane.a2a affine_plane.a2c ap assms(3))
  have 2: "affine_plane_data.parallel Points Lines incid (find_parallel u P) u"
    using "0" affine_plane.a2b affine_plane_data.parallel_def ap assms(3) by fastforce

  have 3: "(find_parallel u P) \<in> lp u" using 0 2 ap affine_plane_data.line_pencil_def
    using assms(2) by fastforce
  have 4:"\<exists>k. k \<in> Lines \<and> k \<in> t \<and>  P \<lhd> k" using 0 1 3 by auto
  obtain u where 5: "u \<in> Lines \<and> u \<in> t \<and>  P \<lhd> u" using 1 4 by auto
  have 6: "\<forall> k . (( k \<in> Lines \<and> k \<in> t \<and>  P \<lhd> k) \<longrightarrow> k = u)" 
  by (smt (verit, ccfv_SIG) "0" "5" affine_plane.a2d affine_plane_data.line_pencil_def ap assms(2,3)
      mem_Collect_eq)

  show ?thesis using 5 6 by blast
qed


fun mprojectivize :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (('a, 'b) projPoint \<Rightarrow> ('a, 'b) projLine \<Rightarrow> bool)" where
  "mprojectivize (incid) (OrdinaryP P) (OrdinaryL k) = incid P k"
| "mprojectivize (incid) (Ideal s) (OrdinaryL m) = (m \<in> s)"
| "mprojectivize (incid) (OrdinaryP P) Infty = False"
| "mprojectivize (incid) (Ideal s) Infty = True"
text \<open>Let's prove the axioms of a projective plane hold in the projectivization of an 
affine plane. Goals are: 
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k . k \<in> Lines \<and> incid P k  \<and> Q \<lhd>  k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> Points \<and> incid P k \<and> incid P n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = { P . (P \<in> Points \<and> incid P k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> S \<noteq> Q \<and> Q \<noteq> R \<and> R \<noteq> S"
\<close>

(* Notation problem:
lemma Ap2:
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> Points)} \<union> {Ideal t | k t . 
                  ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in> Lines)} \<union> {Infty}"
  defines \<open>pincid \<equiv>  mprojectivize (incid) (infix "\<lhd>" 60)\<close>
  shows "\<lbrakk>k \<in> pLines; n \<in> pLines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> pPoints \<and> P \<lhd> k \<and> P \<lhd> n)"
*)

lemma Ap2:
  fixes Points Lines join find_parallel
  fixes incid (infix "\<lhd>" 60)
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> Points)} \<union> {Ideal t | k t . 
                  ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes \<open>pincid =  mprojectivize (incid)\<close>
  shows "\<lbrakk>k \<in> pLines; n \<in> pLines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> pPoints \<and> P p\<lhd> k \<and> P p\<lhd> n)"

proof -
  let ?conclusion = "\<exists> P . (P \<in> pPoints \<and> P p\<lhd> k \<and> P p\<lhd> n)"
  assume kk: "k \<in> pLines" and nn: "n \<in> pLines"
  have "(k = Infty) |  (\<exists> k0 . k = OrdinaryL k0)" using pLdef kk by auto
  then show ?conclusion
  proof
    assume kI: "(k = Infty)"
    have "(n = Infty) |  (\<exists> n0 . n = OrdinaryL n0)" using pLdef nn by auto
    then show ?conclusion
    proof
      assume nI: "n = Infty"
      obtain "A" where aP: "A \<in> Points" using affine_plane.a3 ap by blast
      obtain "B" where bP: "B\<in> Points \<and> A \<noteq> B" using affine_plane.a3 ap by blast
      let ?s = "Ideal (affine_plane_data.line_pencil Points Lines (incid) (join  A B))"
      have s_on_n: "?s p\<lhd> n"  by (simp add: \<open>n = Infty\<close> assms(4))
      have s_on_k: "?s p\<lhd> k"  using kI nI s_on_n by blast 
      have sP: "?s \<in> pPoints"  using aP bP  affine_plane.a1a ap pPdef by fastforce
      show ?conclusion
        using sP kI nI s_on_k by blast
    next
      assume zz: "(\<exists> n0 . n = OrdinaryL n0)"
      obtain n0 where "n = OrdinaryL n0" using zz by blast
      let ?s = "Ideal (affine_plane_data.line_pencil Points Lines (incid) n0)"
      have sn1: "?s p\<lhd> n" 
        by (smt (verit, ccfv_threshold) Un_iff \<open>n = OrdinaryL n0\<close> affine_plane_data.line_pencil_def 
            affine_plane_data.parallel_def assms(4) empty_iff insert_iff mem_Collect_eq
            mprojectivize.simps(2) nn pLdef projLine.simps(3))
      have sn2: "?s p\<lhd> k"  by (simp add: \<open>k = Infty\<close> assms(4))
      have sn3: "?s \<in> pPoints" 
        using \<open>n = OrdinaryL n0\<close> affine_plane_data.line_pencil_def affine_plane_data.parallel_def 
          assms(4) pPdef sn1 by fastforce 
      show ?conclusion
        using sn1 sn2 sn3 by auto
    qed
  next
    assume kOrd: "(\<exists> k0 . k = OrdinaryL k0)"
    obtain k0 where "k = OrdinaryL k0" using kOrd by auto
    have "(n = Infty) |  (\<exists> n0 . n = OrdinaryL n0)" using pLdef nn  by auto
    then show ?conclusion
    proof
      assume "n = Infty"
      obtain "A" where "A \<in> Points" using affine_plane.a3 ap by blast
      obtain "B" where "B\<in> Points \<and> A \<noteq> B" using affine_plane.a3 ap by blast
      let ?s = "Ideal (affine_plane_data.line_pencil Points Lines (incid) k0)"
      have "?s p\<lhd> k"
        by (smt (verit, ccfv_threshold) Un_iff \<open>k = OrdinaryL k0\<close> affine_plane_data.line_pencil_def 
            affine_plane_data.parallel_def assms(4) empty_iff insert_iff kk
            mem_Collect_eq mprojectivize.simps(2) pLdef projLine.simps(3)) 
      have "?s p\<lhd> n"  by (simp add: \<open>n = Infty\<close> assms)
      have "?s \<in> pPoints"  using \<open>A \<in> Points\<close> \<open>B \<in> Points \<and> A \<noteq> B\<close> affine_plane.a1a ap pPdef
        \<open>n = Infty\<close> nn pLdef \<open>k = OrdinaryL k0\<close> kk by blast
      then show ss: "\<exists>P. P \<in> pPoints \<and> P p\<lhd> k \<and> P p\<lhd> n"
        using \<open>Ideal (affine_plane_data.line_pencil Points Lines incid k0) \<in> pPoints\<close> 
          \<open>(Ideal (affine_plane_data.line_pencil Points Lines incid k0)) p\<lhd> k\<close>
          \<open>(Ideal (affine_plane_data.line_pencil Points Lines incid k0)) p\<lhd> n\<close> by auto
      have "\<exists>n0. n =  OrdinaryL n0 \<Longrightarrow>\<exists>P. P \<in> pPoints \<and> P p\<lhd> k  \<and> P p\<lhd> n"  using ss by auto
    next
      assume a1: "(\<exists> n0 . n = OrdinaryL n0)"
      obtain n0 where "n = OrdinaryL n0" using a1 by auto
      then show ?conclusion
      proof (cases  "affine_plane_data.parallel Points Lines (incid) n0 k0") (* parallel ordinary lines *)
        case True
        let ?s = "Ideal (affine_plane_data.line_pencil Points Lines incid k0)"
        have spp: "?s \<in> pPoints" 
          by (metis (mono_tags, lifting) True UnCI
              affine_plane_data.parallel_def mem_Collect_eq
              pPdef)
        have sk: "?s p\<lhd> k"
          by (metis True \<open>k = OrdinaryL k0\<close> affine_plane.parallel_to_Lines(2) affine_plane_data.line_pencil_def
              affine_plane_data.parallel_reflexive ap assms(4) mem_Collect_eq mprojectivize.simps(2))
        have sn: "?s p\<lhd> n"
          by (simp add: True \<open>n = OrdinaryL n0\<close> affine_plane_data.line_pencil_def assms(4))
        have almost: "\<exists>P. P \<in> pPoints \<and> P p\<lhd> k \<and> P p\<lhd> n" using spp sk sn by blast
        show  "\<exists>P. P \<in> pPoints \<and> P p\<lhd> k \<and> P p\<lhd> n" using almost by auto
      next
        case False (* intersecting ordinary lines*)
        obtain P where "P \<lhd> n0  \<and> P \<lhd> k0 \<and> P \<in> Points" 
          by (smt (verit, best) False Un_iff \<open>k = OrdinaryL k0\<close> \<open>n = OrdinaryL n0\<close> 
              affine_plane_data.parallel_if_no_shared_pointsI empty_def insert_iff kk 
              mem_Collect_eq nn pLdef projLine.inject projLine.simps(3))

        have "(OrdinaryP P) p\<lhd> n \<and> (OrdinaryP P) p\<lhd> k \<and> (OrdinaryP P) \<in>  pPoints" 
          by (simp add: \<open>k = OrdinaryL k0\<close> \<open>P \<lhd> n0 \<and> P \<lhd> k0 \<and> P \<in> Points\<close> 
              \<open>n = OrdinaryL n0\<close> assms(4) pPdef)
        then show "\<exists>P. P \<in> pPoints \<and> P p\<lhd> k \<and> P p\<lhd> n" by auto
      qed
    qed
  qed
qed 

lemma Ap3:
  fixes Points Lines join find_parallel
  fixes incid (infix "\<lhd>" 60)
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> Points)} \<union> {Ideal t | k t . 
                  ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes \<open>pincid =  mprojectivize (incid)\<close>
  (* defines "pincid \<equiv>  mprojectivize (incid) (infix "\<lhd>" 60)"*)
  shows "\<exists>P Q R. P \<in> pPoints \<and> Q \<in> pPoints \<and> R \<in> pPoints \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (projective_plane_data.pcollinear pPoints pLines (pincid) P Q R)"
  text \<open>Idea: the three noncollinear points in the affine plane are noncollinear in the projectivization as well\<close>
proof -
  obtain P Q R where ss: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (affine_plane_data.collinear Points Lines (incid) P Q R)" 
    using ap by (smt (verit) affine_plane.a3 affine_plane_data.collinear_def)
  then have p1: "OrdinaryP P \<in> pPoints \<and> OrdinaryP Q \<in> pPoints \<and> OrdinaryP R \<in> pPoints" using pPdef by blast
  have p2: "(OrdinaryP P \<noteq> OrdinaryP Q) \<and> (OrdinaryP P \<noteq> OrdinaryP R) \<and> (OrdinaryP Q \<noteq> OrdinaryP R)"
    by (simp add: \<open>P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> affine_plane_data.collinear Points Lines incid P Q R\<close>)
  have p2: "((OrdinaryP A) p\<lhd> k) \<Longrightarrow> k \<noteq>Infty" using assms(4) by force
  have p3: "((OrdinaryP A) p\<lhd> k) \<Longrightarrow> (\<exists> n. k = OrdinaryL n)" using p2 assms(4) projLine.exhaust by meson 
  have p4: "((OrdinaryP A) p\<lhd> (OrdinaryL n)) \<Longrightarrow>  A \<lhd> n" using assms(4) by auto
  have p5: "(((OrdinaryP P) p\<lhd> (OrdinaryL n))\<and> ((OrdinaryP Q) p\<lhd> (OrdinaryL n)) \<and> ((OrdinaryP R) p\<lhd> (OrdinaryL n)) ) \<Longrightarrow>  
    (P \<lhd> n) \<and> (Q \<lhd> n) \<and> (R \<lhd> n)" using affine_plane.a1b p4  ap assms(4) by auto 

  have p6: "(projective_plane_data.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> (if ((OrdinaryP P) \<in> pPoints \<and> (OrdinaryP Q) \<in> pPoints \<and> (OrdinaryP R) \<in> pPoints) 
  then (\<exists> l. l \<in> pLines \<and> (OrdinaryP P) p\<lhd> l \<and> (OrdinaryP Q) p\<lhd> l \<and> (OrdinaryP R) p\<lhd> l) 
  else undefined)" using projective_plane_data.pcollinear_def by fastforce
  have p7: "(projective_plane_data.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> 
    \<exists> l. l \<in> pLines \<and> (OrdinaryP P) p\<lhd> l \<and> (OrdinaryP Q) p\<lhd> l \<and> (OrdinaryP R) p\<lhd> l" using p6 p1 by auto
  have p8: "(projective_plane_data.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> 
    \<exists> l. l \<noteq> Infty \<and> l \<in> pLines \<and> (OrdinaryP P) p\<lhd> l \<and> (OrdinaryP Q) p\<lhd> l \<and> (OrdinaryP R) p\<lhd> l" using p7 p2  by (metis assms(4) mprojectivize.simps(3))
  have p9: "(projective_plane_data.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> 
    \<exists> k.  (OrdinaryP P) p\<lhd> ( OrdinaryL k) \<and> (OrdinaryP Q) p\<lhd>  ( OrdinaryL k) \<and>  (OrdinaryP R) p\<lhd>  ( OrdinaryL k)" using p8
  by (metis projLine.exhaust)
  have p10: "(projective_plane_data.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> 
    \<exists> k. P \<lhd> k \<and> Q \<lhd> k \<and> R \<lhd> k" using p9 assms(4) by auto
  have p11: "(projective_plane_data.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> 
    (affine_plane_data.collinear Points Lines (incid)P Q R)" 
  using ss affine_plane.a1b affine_plane.parallel_to_collinear ap p10 by fastforce

  have p12: "\<not>(affine_plane_data.collinear Points Lines (incid) P Q R)" 
    by (simp add: \<open>P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> affine_plane_data.collinear Points Lines incid P Q R\<close>)
  have p13: "\<not> (projective_plane_data.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R))" using p11 p12
  using affine_plane.a1b affine_plane.parallel_to_collinear ap p10 ss by fastforce
  
  show ?thesis using p13 p1 p2 ss  by auto
qed

lemma Ap41:   
  fixes k n
  assumes ap: "affine_plane Points Lines incid join find_parallel" 
  assumes "k \<in> Lines" and "n \<in> Lines"
  assumes same_pencil: "(affine_plane_data.line_pencil Points Lines (incid) k) =
                      (affine_plane_data.line_pencil Points Lines (incid) n)"
  shows "(affine_plane_data.parallel Points Lines incid k n)"
proof -
  show ?thesis
  by (metis affine_plane_data.line_pencil_def affine_plane_data.parallel_def assms(2) mem_Collect_eq same_pencil)
qed


lemma Ap4:
  fixes incid (infix "\<lhd>" 60)
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> Points)} \<union> {Ideal t | k t . 
                  ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in> Lines)} \<union> {Infty}"
(*  defines "pincid \<equiv>  mprojectivize (incid)" *)
  fixes pincid (infix "p\<lhd>" 60)
  assumes \<open>pincid =  mprojectivize (incid)\<close>
  shows "\<lbrakk>k \<in> pLines; U = { P . (P \<in> pPoints \<and> P p\<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct[Q,R,S]"
  
text\<open>idea: Each line of A has at least two points; its completion also contains an ideal point. And the line at infty contains AB, BC, AC where ABC are three 
noncollinear points of A.\<close>
proof -
  assume kl: "k \<in> pLines" and u_def: "U = { P . (P \<in> pPoints \<and> (P p\<lhd> k))}"
  show ?thesis 
  proof -
      obtain A B C where 0:"A \<in> Points" and 1: "B \<in> Points" and 2: "C \<in> Points" and 3: "\<not> ((affine_plane_data.collinear Points Lines (incid)) A B C)" using ap
      by (smt (verit, ccfv_SIG) affine_plane.a3 affine_plane_data.collinear_def)
      have 4: "join A B \<noteq> join A C" using 0 1 2 3
        by (smt (verit, best) affine_plane.a1a affine_plane.containing_line affine_plane_data.collinear_def ap)
      have 5: "join A B \<noteq> join B C" using 0 1 2 3
        by (smt (verit, best) affine_plane.a1a affine_plane.containing_line affine_plane_data.collinear_def ap)
      have 51: "join A B \<in> Lines \<and> join A C \<in> Lines \<and> join B C \<in> Lines"
        by (smt (verit) "0" "1" "2" "3" "4" affine_plane.a1a affine_plane_data.collinear_def ap) 
    consider (inf) "(k = Infty)" | (ord) "(\<exists> n . (n \<in> Lines) \<and> (k = OrdinaryL n))" using kl pLdef by blast 
    then have ?thesis 
    proof cases
      case inf
      let ?AB = "(Ideal  (affine_plane_data.line_pencil Points Lines (incid) (join A B)))"
      let ?AC = "(Ideal  (affine_plane_data.line_pencil Points Lines (incid) (join A C)))"
      let ?BC = "(Ideal  (affine_plane_data.line_pencil Points Lines (incid) (join B C)))"
      have 52: "?AB \<noteq> ?AC" 
      proof (rule ccontr)
        assume ch: "\<not> (?AB \<noteq> ?AC)"
        hence "?AB = ?AC" by blast
        hence "(affine_plane_data.line_pencil Points Lines (incid) (join A B)) =
             (affine_plane_data.line_pencil Points Lines (incid) (join A C))" by simp
        hence "affine_plane_data.parallel Points Lines incid (join A B) (join A C)" by (meson "51" Ap41 ap)
        hence "(join A B) = (join A C)" using affine_plane.parallel_overlap_equal
          by (smt (verit) "0" "1" "2" "3" affine_plane.a1a affine_plane_data.collinear_def ap)
        hence qq: " affine_plane_data.collinear Points Lines (incid) A B C" using affine_plane.parallel_to_collinear using 4 by auto
        show "False" using "3" qq by auto
      qed
      have 53: "?AB \<noteq> ?BC" 
      proof (rule ccontr)
        assume ch: "\<not> (?AB \<noteq> ?BC)"
        hence "?AB = ?BC" by blast
        hence "(affine_plane_data.line_pencil Points Lines (incid) (join A B)) =
             (affine_plane_data.line_pencil Points Lines (incid) (join B C))" by simp
        hence "affine_plane_data.parallel Points Lines incid (join A B) (join B C)" by (meson "51" Ap41 ap)
        hence "(join A B) = (join B C)" using affine_plane.parallel_overlap_equal
          by (smt (verit) "0" "1" "2" "3" affine_plane.a1a affine_plane_data.collinear_def ap)
        hence qq: "affine_plane_data.collinear Points Lines (incid) A B C" using affine_plane.parallel_to_collinear 5 by fastforce 
        show "False"
          using "3" qq by auto
      qed
      have 54: "?AC \<noteq> ?BC" 
      proof (rule ccontr)
        assume ch: "\<not> (?AC \<noteq> ?BC)"
        hence "?AC = ?BC" by blast
        hence "(affine_plane_data.line_pencil Points Lines (incid) (join A C)) =
             (affine_plane_data.line_pencil Points Lines (incid) (join B C))" by simp
        hence "affine_plane_data.parallel Points Lines incid (join A C) (join B C)" by (meson "51" Ap41 ap)
        hence "(join A B) = (join B C)" using affine_plane.parallel_overlap_equal
          by (smt (verit) "0" "1" "2" "3" affine_plane.a1a affine_plane_data.collinear_def ap)
        hence qq: "affine_plane_data.collinear Points Lines (incid) A B C" using affine_plane.parallel_to_collinear 5 by fastforce 
        show "False"
          using "3" qq by auto
      qed
      have 62: "?AB \<in> U \<and> ?AC \<in> U \<and> ?BC \<in> U" 
      using "51" assms(4) inf pPdef u_def by auto
      then show ?thesis using 52 53 54 62 by auto
    next
      case ord
      obtain n where n_facts:  " (n \<in> Lines) \<and> (k = OrdinaryL n)" using ord by blast
      obtain A B where two_point_facts: "A \<in> Points \<and> B \<in> Points \<and> A \<lhd> n \<and> B \<lhd> n \<and> A \<noteq> B" 
        using affine_plane.contained_points n_facts ap by fastforce
      have first_two: " (OrdinaryP A) p\<lhd> k \<and>  (OrdinaryP B) p\<lhd> k" using two_point_facts n_facts assms by auto
      have first_two_ppts: "(OrdinaryP A) \<in> pPoints \<and> (OrdinaryP B) \<in> pPoints" using pPdef two_point_facts by blast
      let ?C = "Ideal (affine_plane_data.line_pencil Points Lines (incid) (join A B))"
      have third: "?C p\<lhd> k"
      using Ap41 affine_plane.a1b affine_plane_data.line_pencil_def ap assms n_facts two_point_facts by fastforce
      have third_pt: "?C \<in> pPoints" using affine_plane.a1a ap pPdef two_point_facts by fastforce
      have third_diff: "?C \<noteq>  (OrdinaryP A) \<and> ?C \<noteq> (OrdinaryP B)" by simp

      then show ?thesis using first_two first_two_ppts third third_pt third_diff two_point_facts u_def by auto
    qed
    show ?thesis using \<open>\<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q,R,S]\<close> by blast
  qed
qed


lemma Ap1a:
  fixes incid (infix "\<lhd>" 60)
  fixes P Q
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> Points)} \<union> {Ideal t | k t . 
                  ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes \<open>pincid =  mprojectivize (incid)\<close>
  assumes pq_pts: "P \<in> pPoints \<and> Q \<in> pPoints"
  assumes pq_diff:"P \<noteq> Q"
  shows "(\<exists>k . k \<in> pLines \<and> P p\<lhd> k  \<and> Q p\<lhd> k)"
proof (cases P)
  case PO: (OrdinaryP A)
  then show ?thesis 
  proof (cases Q)
    case QO: (OrdinaryP B)
    let ?k = "OrdinaryL (join A B)"
    have join_line: "join A B \<in> Lines"  using PO QO affine_plane.a1a ap pPdef pq_diff pq_pts by fastforce
    have pk: "P p\<lhd> ?k" using PO QO affine_plane.a1a ap assms pPdef pq_diff pq_pts by fastforce
    have qk: "Q p\<lhd> ?k" using PO QO affine_plane.a1a ap assms pPdef pq_diff pq_pts by fastforce
    have kline: "?k \<in> pLines" using  join_line  using pLdef by auto
    then show ?thesis using pk qk kline by blast
  next
    case QI:(Ideal s)
    obtain n where n_facts: "s = affine_plane_data.line_pencil Points Lines (incid) n \<and> n \<in> Lines" using pPdef QI pq_pts by blast 
    let ?m = "find_parallel n A" 
    have m_line: "?m \<in> Lines" using PO affine_plane.a2a ap n_facts pPdef pq_pts by fastforce
    have am: "A \<lhd> ?m" using PO affine_plane.a2c ap n_facts pPdef pq_pts by fastforce 
    let ?k = "OrdinaryL ?m"
    have pk: "P p\<lhd> ?k" using  PO am assms by auto
    have qk: "Q p\<lhd> ?k" using PO QI affine_plane.a2b affine_plane_data.line_pencil_def ap assms n_facts pPdef pq_pts 
    by (smt (verit, best) Un_iff mem_Collect_eq mprojectivize.simps(2) projPoint.distinct(1) projPoint.inject(1))
    have k_line: "?k \<in> pLines" using m_line pLdef by blast
    show ?thesis using pk qk k_line by blast
  qed
next
  case PI: (Ideal t)
  obtain n where n_facts: "t = affine_plane_data.line_pencil Points Lines (incid) n \<and> n \<in> Lines" using pPdef PI pq_pts by blast 
  then show ?thesis 
  proof (cases Q)
    case QO: (OrdinaryP B)
    let ?m = "find_parallel n B" 
    have m_line: "?m \<in> Lines" using PI QO affine_plane.a2a ap n_facts pPdef pq_pts by fastforce
    have bm: "B \<lhd> ?m" using QO affine_plane.a2c ap n_facts pPdef pq_pts by fastforce 
    let ?k = "OrdinaryL ?m"
    have pk: "P p\<lhd> ?k"
    using PI QO affine_plane.a2b affine_plane_data.line_pencil_def ap n_facts pPdef assms pq_pts 
      by (smt (verit, ccfv_threshold) Un_iff mem_Collect_eq mprojectivize.simps(2) projPoint.distinct(1) projPoint.inject(1)) 
    have qk: "Q p\<lhd> ?k" using QO PI bm affine_plane.a2b affine_plane_data.line_pencil_def ap assms n_facts pPdef pq_pts by auto
    have k_line: "?k \<in> pLines" using m_line pLdef by blast
    show ?thesis using pk qk k_line by auto
  next
    case QI: (Ideal s)
    have qk: "Q p\<lhd> Infty" using QI pLdef assms by auto
    have pk: "P p\<lhd> Infty" using PI pLdef assms by auto
    have kline: "Infty \<in> pLines" using pLdef by auto
    then show ?thesis using qk pk kline by blast 
  qed
qed

lemma disjoint_pencils:
  fixes s t k n
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  assumes tdef: "t = affine_plane_data.line_pencil Points Lines (incid) k"
  assumes sdef: "s = affine_plane_data.line_pencil Points Lines (incid) n"
  assumes kn_diff: "\<not> affine_plane_data.parallel Points Lines (incid) k n"
  shows "s \<inter> t = {}"
  by (metis affine_plane.parallel_transitive2 affine_plane_data.line_pencil_def affine_plane_data.parallel_symmetric ap
      disjoint_iff_not_equal kn_diff mem_Collect_eq sdef tdef)

lemma same_pencils:
  fixes s t k n
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  assumes knlines: "k \<in> Lines \<and> n \<in> Lines"
  assumes tdef: "t = affine_plane_data.line_pencil Points Lines (incid) k"
  assumes sdef: "s = affine_plane_data.line_pencil Points Lines (incid) n"
  assumes kn_par: "affine_plane_data.parallel Points Lines (incid) k n"
  shows "s = t"
proof -
  have s_in_t: "s \<subseteq> t"
  proof
    fix m
    assume ms: "m \<in> s"
    have "affine_plane_data.parallel Points Lines (incid) m n" 
      using affine_plane_data.line_pencil_def ms sdef by force
    have "affine_plane_data.parallel Points Lines (incid) m k" 
      by (meson \<open>affine_plane_data.parallel Points Lines incid m n\<close> affine_plane.parallel_transitive2 affine_plane_data.parallel_symmetric
          ap kn_par) 
    have "m \<in> t"  by (simp add: \<open>affine_plane_data.parallel Points Lines incid m k\<close> affine_plane_data.line_pencil_def tdef)
    have  "s \<subseteq> t"
      by (metis \<open>affine_plane_data.parallel Points Lines incid m k\<close> affine_plane.parallel_transitive2 affine_plane_data.line_pencil_def
          affine_plane_data.parallel_symmetric ap mem_Collect_eq ms sdef subsetI tdef)
    show " \<And>x. x \<in> s \<Longrightarrow> x \<in> t" using \<open>s \<subseteq> t\<close> by auto
  qed
  have t_in_s: "t \<subseteq> s"
  proof
    fix m
    assume mt: "m \<in> t"
    have "affine_plane_data.parallel Points Lines (incid) m k" 
      using affine_plane_data.line_pencil_def mt tdef by force 
    have mn: "affine_plane_data.parallel Points Lines (incid) m n"
    by (meson \<open>affine_plane_data.parallel Points Lines incid m k\<close> affine_plane.parallel_transitive2 ap kn_par)
    
    have ms: "m \<in> s" using mn affine_plane_data.line_pencil_def sdef by force
    have  "t \<subseteq> s" 
      by (metis ms \<open>affine_plane_data.parallel Points Lines incid m k\<close> affine_plane.parallel_transitive2 affine_plane_data.line_pencil_def
          affine_plane_data.parallel_symmetric ap mem_Collect_eq sdef subsetI tdef)
    show " \<And>x. x \<in> t \<Longrightarrow> x \<in> s" using \<open>t \<subseteq> s\<close> by auto
  qed
  show "s = t" using s_in_t t_in_s by auto
qed
  
lemma two_ideal_is_infinite:
  fixes P Q k
  assumes pq_def: "P = Ideal s \<and> Q = Ideal t"
  assumes pq_diff:"P \<noteq> Q"
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> Points)} \<union> {Ideal t | k t . 
                  ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes pm_def: \<open>pincid =  mprojectivize (incid)\<close>
  assumes pPoint: "P \<in> pPoints"
  assumes qPoint: "Q \<in> pPoints"
  assumes k_facts: "k \<in> pLines \<and> P p\<lhd> k \<and> Q p\<lhd> k" 
  shows "k = Infty"
proof -
  have not_ordinary: "\<not> (\<exists> n . n \<in> Lines \<and> k = OrdinaryL n)" 
  proof (rule ccontr)
    assume ch: "\<not> \<not> (\<exists> n . n \<in> Lines \<and> k = OrdinaryL n)"
    have ch2: "\<exists> n . n \<in> Lines \<and> k = OrdinaryL n" using ch by blast
    obtain k1 where k1_facts: "k1 \<in> Lines \<and> s =  affine_plane_data.line_pencil Points Lines (incid) k1" 
      using pq_def pPdef pPoint by blast 
    obtain k2 where k2_facts: "k2 \<in> Lines \<and> t =  affine_plane_data.line_pencil Points Lines (incid) k2" 
      using pq_def pPdef qPoint by blast 
    obtain nn where nn_facts:"nn \<in> Lines \<and> k = OrdinaryL nn" using ch2 by blast
    from k_facts have nns: "nn \<in> s" using nn_facts pq_def pm_def by auto 
    from k_facts have nnt: "nn \<in> t" using nn_facts pq_def pm_def by auto 
    from nns have nn_k1_par: "affine_plane_data.parallel Points Lines (incid) nn k1" using k1_facts affine_plane_data.line_pencil_def by force
    from nnt have nn_k2_par: "affine_plane_data.parallel Points Lines (incid) nn k2" using k2_facts affine_plane_data.line_pencil_def by force
    from nns nnt have k1k2: "affine_plane_data.parallel Points Lines (incid) k1 k2" 
      by (meson affine_plane.parallel_transitive affine_plane_data.parallel_symmetric ap nn_k1_par nn_k2_par)
    from k1k2 have "s = t" using k1_facts k2_facts ap same_pencils by metis
    show False  using \<open>s = t\<close> pq_def pq_diff by blast
  qed
  show ?thesis using not_ordinary pLdef k_facts by blast 
qed

 
lemma any_ordinary_is_ordinary:
  fixes P k
  assumes p_def: "P = OrdinaryP A"
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> Points)} \<union> {Ideal t | k t . 
                  ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in> Lines)} \<union> {Infty}"
  defines pm_def: "pincid \<equiv>  mprojectivize (incid)"
  assumes pPoint: "P \<in> pPoints"
  assumes k_facts: "k \<in> pLines \<and> pincid P k" 
  shows "\<exists> n.  n \<in> Lines \<and> k = OrdinaryL n"
  using k_facts pLdef p_def pm_def by auto

lemma Ap1b:
  fixes P Q k n Points Lines incid
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> Points)} \<union> {Ideal t | k t . 
                  ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes pm: \<open>pincid =  mprojectivize (incid)\<close>
  assumes pq_pts: "P \<in> pPoints \<and> Q \<in> pPoints"
  assumes pq_diff:"P \<noteq> Q"
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  assumes k_facts: "k \<in> pLines \<and> P p\<lhd> k  \<and> Q p\<lhd> k" and n_facts: "n \<in> pLines \<and> P p\<lhd> n  \<and> Q p\<lhd> n"
  shows "k = n"
proof (cases P)
  case PO: (OrdinaryP A)
  obtain k0 where k0_facts: "k = OrdinaryL k0 \<and> k0 \<in> Lines" using k_facts  pLdef pm PO by auto
  obtain n0 where n0_facts: "n = OrdinaryL n0 \<and> n0 \<in> Lines" using n_facts  pLdef pm PO by auto
  then show ?thesis 
  proof (cases Q)
    case QO: (OrdinaryP B)
    have abk0: "incid A k0 \<and> incid B k0" using PO QO k0_facts k_facts pm by auto
    have abn0: "incid A n0 \<and> incid B n0" using PO QO n0_facts n_facts pm by auto
    have k0n0: "k0 = n0" using pq_diff abk0 abn0
      using PO QO \<open>incid A n0 \<and> incid B n0\<close> abk0 affine_plane.prop1P2 ap k0_facts n0_facts pPdef pq_diff pq_pts by fastforce
    then show ?thesis using k0n0 k0_facts n0_facts by auto
  next
    case QI: (Ideal t)
    obtain h where h_facts: "h \<in> Lines \<and> t = affine_plane_data.line_pencil Points Lines (incid) h"  using QI pPdef pq_pts by blast
    have hk0: "affine_plane_data.parallel Points Lines (incid) h k0"
      by (metis QI affine_plane_data.line_pencil_def affine_plane_data.parallel_symmetric h_facts k0_facts k_facts mem_Collect_eq
          mprojectivize.simps(2) pm)
    have hn0: "affine_plane_data.parallel Points Lines (incid) h n0"
      by (metis QI affine_plane_data.line_pencil_def affine_plane_data.parallel_symmetric h_facts mem_Collect_eq mprojectivize.simps(2)
          n0_facts n_facts pm)
    have k0n0: "affine_plane_data.parallel Points Lines (incid) k0 n0" using hn0 hk0 affine_plane.parallel_transitive 
         affine_plane_data.parallel_symmetric ap by meson
    then show ?thesis using k_facts n_facts k0n0
      by (smt (verit, ccfv_threshold) PO Un_iff affine_plane_data.parallel_def k0_facts mem_Collect_eq mprojectivize.simps(1) n0_facts pPdef
          pm pq_pts projPoint.distinct(1))
  qed
next
  case PI: (Ideal s)
  then show ?thesis
  proof (cases Q)
    case QO: (OrdinaryP B)
    obtain k0 where k0_facts: "k = OrdinaryL k0 \<and> k0 \<in> Lines" using k_facts  pLdef pm PI QO by auto
    obtain n0 where n0_facts: "n = OrdinaryL n0 \<and> n0 \<in> Lines" using n_facts  pLdef pm PI QO by auto

    obtain h where h_facts: "h \<in> Lines \<and> s = affine_plane_data.line_pencil Points Lines (incid) h"  using QO pPdef pq_pts PI by blast
    have hk0: "affine_plane_data.parallel Points Lines (incid) h k0"
    by (metis Ap41 PI affine_plane_data.line_pencil_def ap h_facts k0_facts k_facts mem_Collect_eq mprojectivize.simps(2) pm
        same_pencils)
    have hn0: "affine_plane_data.parallel Points Lines (incid) h n0"
      by (metis Ap41 PI affine_plane_data.line_pencil_def ap h_facts mem_Collect_eq mprojectivize.simps(2) n0_facts n_facts pm
          same_pencils)
    have k0n0: "affine_plane_data.parallel Points Lines (incid) k0 n0" using hn0 hk0 affine_plane.parallel_transitive 
         affine_plane_data.parallel_symmetric ap by meson
    then show ?thesis using k_facts n_facts k0n0
      by (smt (verit, ccfv_threshold) QO Un_iff affine_plane_data.parallel_def k0_facts mem_Collect_eq mprojectivize.simps(1,3,4) n0_facts
          pPdef pm pq_pts)
  next
    case QI: (Ideal t)
    have h1: "P = Ideal s \<and> Q = Ideal t" using PI QI by blast
    have h2: "P \<noteq> Q" using pq_diff by auto
    have h3: "P \<in> pPoints" using pq_pts by auto
    have h4: "Q \<in> pPoints" using pq_pts by auto
    thm two_ideal_is_infinite  [OF h1 h2 ap _ _ _]
    have kI: "k = Infty" using two_ideal_is_infinite [OF h1 h2 ap _ _ _] 
    by (metis k_facts pLdef pPdef pm pq_pts)
    have nI: "n = Infty" using two_ideal_is_infinite [OF h1 h2 ap _ _ _] 
    by (metis h3 h4 n_facts pLdef pPdef pm)
    then show ?thesis using kI nI by blast
  qed
qed

theorem projectivization_is_projective:
  fixes Points::"'p set" 
  fixes Lines:: "'l set"
  fixes incid::"'p \<Rightarrow> 'l \<Rightarrow> bool" 
  fixes join::"'p \<Rightarrow> 'p \<Rightarrow> 'l"
  fixes find_parallel::"'l \<Rightarrow> 'p \<Rightarrow> 'l"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> Points)} \<union> {Ideal t | k t . 
                  ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes pm: \<open>pincid =  mprojectivize (incid)\<close>
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  shows   "projective_plane pPoints pLines pincid"

proof (unfold_locales)
  find_theorems name: projective_plane_def

  have pp1a: "\<And>P Q .\<lbrakk>P \<noteq> Q; P \<in> pPoints; Q \<in> pPoints\<rbrakk> \<Longrightarrow> (\<exists>k . k \<in> pLines \<and>  P p\<lhd> k  \<and> Q p\<lhd> k)" using ap Ap1a 
  by (smt (verit) Collect_cong pLdef pPdef pm) 
  have pp1b: "\<And>P Q k n .\<lbrakk>P \<noteq> Q; P \<in> pPoints; Q \<in> pPoints; 
    k \<in> pLines;  P p\<lhd> k;  Q p\<lhd> k; n \<in> pLines;  P p\<lhd> n;  Q p\<lhd> n\<rbrakk>  \<Longrightarrow> k = n" 
    by (metis (lifting) ext Ap1b ap pLdef pPdef pm)
  have pp1:  "\<And>P Q .\<lbrakk>P \<noteq> Q; P \<in> pPoints; Q \<in> pPoints\<rbrakk> \<Longrightarrow> 
    (\<exists>!k . k \<in> pLines \<and>  P p\<lhd> k  \<and>  Q p\<lhd> k)" using pp1a pp1b by meson
  show " \<And>P Q. P \<noteq> Q \<Longrightarrow>
         P \<in> pPoints \<Longrightarrow>
           Q \<in> pPoints  \<Longrightarrow>
           \<exists>!k. k \<in> pLines  \<and>
                P p\<lhd> k \<and>
                Q p\<lhd> k"
    using pp1 by auto 

  have pp2: "\<And>n k .\<lbrakk>k \<in> pLines; n \<in> pLines\<rbrakk> \<Longrightarrow> 
  \<exists> P . (P \<in> pPoints \<and> P p\<lhd> k \<and> P p\<lhd> n)"
    by (smt (verit) Ap2 Collect_cong assms)

  show "\<And>k n. k \<in> pLines \<Longrightarrow> n \<in> pLines \<Longrightarrow>
           \<exists>P. P \<in> pPoints \<and>
                P p\<lhd> k \<and>
                P p\<lhd> n" using pp2 by auto

  have pp3: "\<exists>P Q R. P \<in> pPoints \<and> Q \<in> pPoints \<and> R \<in> pPoints \<and>
    P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> 
  \<not> (projective_plane_data.pcollinear pPoints pLines (pincid) P Q R)"
    by (smt (verit) Ap3 Collect_cong ap pLdef pPdef pm)
  show " \<exists>P Q R.
       P \<in> pPoints \<and> Q \<in> pPoints \<and> R \<in> pPoints  \<and>
       P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       \<not> projective_plane_data.pcollinear
           pPoints pLines pincid P Q R" using pp3 by auto


  show x: " \<And>k U. k \<in> pLines \<Longrightarrow>
           U =
           {P \<in> pPoints .  P p\<lhd> k} \<Longrightarrow>
           \<exists>Q R S.
              Q \<in> U \<and>
              R \<in> U \<and>
              S \<in> U \<and> distinct[Q,R,S]" using Ap4 [OF ap] ap 
  using pLdef pPdef pm by auto

  have pp4: "\<And>k U . (\<lbrakk>k \<in> pLines; U = { P . (P \<in> pPoints \<and> P p\<lhd> k)} \<rbrakk> \<Longrightarrow>
      \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q,R,S] )" using Ap4 ap x by auto
qed

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
section \<open>Homogeneous coords for RP2, preparatory material\<close>
text\<open>To show that the analytic definition of RP2 gives
a projective plane, we're going to need to do lots of things 
with nonzero vectors, their dot- and cross-products, and 
even the Cauchy-Schwartz inequality; this section does all that. \<close>


definition punctured_r_3 where
"punctured_r_3 = (UNIV::((real \<times> real \<times> real) set)) - {(0::real,0::real,0::real)}"

definition cross::"(real \<times> real \<times> real) \<Rightarrow>(real \<times> real \<times> real) \<Rightarrow> (real \<times> real \<times> real)"  where
"cross =  (\<lambda> (x1, x2, x3) (y1, y2, y3) . (x2*y3 - x3 * y2, x3 * y1  - x1 * y3, x1 * y2 - x2* y1))"

(* Idea: show that |u x v|^2 = |u|^2 |v|^2 sin^2 theta = |u|^2 |v|^2 (1 - cos^2theta)
 = |u|^2 |v|^2 (1 - dot(u,v)^2/ |u|^2 |v|^2 ) = |u|^2 |v|^2 - dot(u,v)^2 > 0 for some reason...
*) 
definition squared_length::"(real \<times> real \<times> real) \<Rightarrow>real" where
"squared_length =  (\<lambda> (x1, x2, x3) . (x1*x1 + x2*x2 + x3 * x3))"

definition dot::"(real \<times> real \<times> real) \<Rightarrow>(real \<times> real \<times> real) \<Rightarrow> real" where
"dot =  (\<lambda> (x1, x2, x3) (y1, y2, y3) . (x1 * y1 + x2 * y2 + x3 * y3))"

definition vplus::"(real \<times> real \<times> real) \<Rightarrow>(real \<times> real \<times> real) \<Rightarrow> (real \<times> real \<times> real)"  where
"vplus =  (\<lambda> (x1, x2, x3) (y1, y2, y3) . (x1+y1, x2+y2, x3+y3))"

definition smult::"real \<Rightarrow> (real \<times> real \<times> real) \<Rightarrow>(real \<times> real \<times> real)"  where
"smult =  (\<lambda> s (x1, x2, x3). (s*x1, s* x2, s* x3))"

lemma smult_assoc: 
  "smult a (smult b v) = smult (a * b) v"
  unfolding smult_def
  by (metis (no_types, lifting) mult.assoc old.prod.case prod_cases3)

lemma smult_ident: 
  "smult 1 v =  v"
  unfolding smult_def by simp


lemma vplus_comm:
  shows "vplus u v = vplus v u"  
proof - 
  obtain x1 x2 x3 where ux: "u = (x1, x2, x3)" using prod_cases3 by blast
  obtain y1 y2 y3 where vy: "v = (y1, y2, y3)" using prod_cases3 by blast
  have 1: "vplus u v = (x1+y1, x2 + y2, x3 +y3)" using ux vy by (simp add: vplus_def)
  have 2: "vplus v u = (y1+x1, y2 + x2, y3 +x3)" using ux vy by (simp add: vplus_def)
  show ?thesis using 1 2 by simp
qed

lemma squared_length_is_self_dot:
  fixes x1 x2 x3::real
  shows "squared_length (x1, x2, x3)  = dot (x1, x2, x3) (x1, x2, x3)"
proof -
  have 0: "(squared_length (x1, x2, x3)) = x1 * x1 + x2 * x2 + x3 * x3" by (simp add: squared_length_def)
  have 1: "dot (x1, x2, x3) (x1, x2, x3) = x1 * x1 + x2 * x2 + x3 * x3" by (simp add: dot_def)
  show ?thesis using 0 1 by force
qed

lemma nonzero_vector_implies_nonzero_square_length:
  assumes "(x1, x2, x3) \<in> punctured_r_3"
  shows "squared_length (x1, x2, x3) > 0"
proof -
  have 0: "x1 \<noteq> 0\<or> x2 \<noteq> 0 \<or> x3 \<noteq> 0" using assms punctured_r_3_def by blast
  have 1: "x1*x1 > 0 \<or> x2*x2 > 0 \<or> x3*x3 > 0" using 0 not_real_square_gt_zero by blast
  have 2: "x1*x1 +x2*x2 +x3*x3 > 0" using 1 by (smt (verit) real_minus_mult_self_le)
  show ?thesis by (simp add: "2" squared_length_def)
qed

lemma nonzero_square_length_implies_nonzero_vector:
  fixes x1 x2 x3
  assumes "squared_length (x1, x2, x3) > 0"
  shows "(x1, x2, x3) \<noteq> (0,0,0)"
proof -
  have 0:"x1*x1 + x2*x2 + x3*x3 > 0" using assms
    unfolding squared_length_def by auto
  show ?thesis  using "0" by force
qed


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
proof -
  have 0: "cross (x1, x2, x3) (y1, y2, y3) =  (x2*y3 - x3 * y2, x3 * y1  - x1 * y3, x1 * y2 - x2* y1)" by (simp add: cross_def)
  have 1: "squared_length (cross (x1, x2, x3) (y1, y2, y3)) = 
   (x2*y3 - x3*y2)*(x2*y3 - x3*y2) + (x3*y1  - x1*y3)*(x3*y1  - x1*y3) + (x1*y2 - x2*y1)*(x1*y2 - x2*y1)" using 0 by (simp add:squared_length_def)
  also have 2: "squared_length (cross (x1, x2, x3) (y1, y2, y3)) =
                    x2 * y3 * (x2 * y3) -  2 * (x2 * y3) * (x3 * y2) + x3 * y2 * (x3 * y2) + 
                    x3 * y1 * (x3 * y1) -  2 * (x3 * y1) * (x1 * y3) + x1 * y3 * (x1 * y3) +
                    x1 * y2 * (x1 * y2) -  2 * (x1 * y2) * (x2 * y1) + x2 * y1 * (x2 * y1)" 
    using sq_diff [of "(x2*y3)" "x3*y2"] sq_diff [of "(x3*y1)" "x1*y3"] sq_diff [of "(x1*y2)" "x2*y1"] using 1 by argo
  have 3:"(squared_length (x1, x2, x3) ) * (squared_length (y1, y2, y3) ) - 
  (dot (x1, x2, x3) (y1, y2, y3)) *  (dot (x1, x2, x3) (y1, y2, y3)) = 
  (x1*x1 + x2*x2 + x3*x3)*(y1*y1 + y2*y2 + y3*y3) - ( (x1*y1 + x2*y2 + x3*y3)* (x1*y1 + x2*y2 + x3*y3))" by (simp add: squared_length_def dot_def)
  have 4: "(squared_length (x1, x2, x3) ) * (squared_length (y1, y2, y3) ) -   (dot (x1, x2, x3) (y1, y2, y3)) *  (dot (x1, x2, x3) (y1, y2, y3)) = 
    (x1*x1*y1*y1 + x1*x1*y2*y2 + x1*x1*y3*y3 + x2*x2*y1*y1 + x2*x2*y2*y2 + x2*x2*y3*y3 + x3*x3*y1*y1 + x3*x3*y2*y2 + x3*x3*y3*y3) -  
 ( (x1*y1 + x2*y2 + x3*y3)* (x1*y1 + x2*y2 + x3*y3))" using 3 abcpqr [of "x1*x1" "x2*x2" "x3*x3"  "y1*y1" "y2*y2" "y3*y3"] by simp
  have 5: "(squared_length (x1, x2, x3) ) * (squared_length (y1, y2, y3) ) -   (dot (x1, x2, x3) (y1, y2, y3)) *  (dot (x1, x2, x3) (y1, y2, y3)) = 
    (x1*x1*y1*y1 + x1*x1*y2*y2 + x1*x1*y3*y3 + x2*x2*y1*y1 + x2*x2*y2*y2 + x2*x2*y3*y3 + x3*x3*y1*y1 + x3*x3*y2*y2 + x3*x3*y3*y3) -  
 ( x1 * y1 * (x1 * y1) + x1 * y1 * (x2 * y2) + x1 * y1 * (x3 * y3) + x2 * y2 * (x1 * y1) + x2 * y2 * (x2 * y2) + x2 * y2 * (x3 * y3) + x3 * y3 * (x1 * y1) +
x3 * y3 * (x2 * y2) +
x3 * y3 * (x3 * y3))" using abcpqr [of "x1*y1" "x2*y2" "x3*y3"  "x1*y1" "x2*y2" "x3*y3"] 4 by simp
  have 6: "(squared_length (x1, x2, x3) ) * (squared_length (y1, y2, y3) ) -   (dot (x1, x2, x3) (y1, y2, y3)) *  (dot (x1, x2, x3) (y1, y2, y3)) = 
    (  x1*x1*y2*y2 + x1*x1*y3*y3 + x2*x2*y1*y1 +  x2*x2*y3*y3 + x3*x3*y1*y1 + x3*x3*y2*y2 ) -  
 (   x1 * y1 * (x2 * y2) + x1 * y1 * (x3 * y3) + x2 * y2 * (x1 * y1)  + x2 * y2 * (x3 * y3) + x3 * y3 * (x1 * y1) +
x3 * y3 * (x2 * y2))" using 5 by simp
  show ?thesis using  6 2 by simp
qed

lemma cross_prod_length2:
  fixes u v
  shows "squared_length (cross u v) = 
    (squared_length u ) * (squared_length v ) - 
  (dot u v) *  (dot u v)"
proof -
  show ?thesis using cross_prod_length by (metis prod_cases3)
qed

lemma dot_commute:
  fixes u v
  shows "dot u v = dot v u"
proof -
  obtain x1 x2 x3 where ux: "u = (x1, x2, x3)" using prod_cases3 by blast
  obtain y1 y2 y3 where vy: "v = (y1, y2, y3)" using prod_cases3 by blast
  have 1: "dot u v = x1*y1 + x2 * y2 + x3 *y3" using ux vy by (simp add: dot_def)
  have 2: "dot v u = x1*y1 + x2 * y2 + x3 *y3" using ux vy by (simp add: dot_def)
  show ?thesis using 1 2 by simp
qed

lemma dot_distrib [simp]:
  fixes u v w
  shows "dot (vplus u v) w = dot u w + dot v w"
proof -
  obtain x1 x2 x3 where ux: "u = (x1, x2, x3)" using prod_cases3 by blast
  obtain y1 y2 y3 where vy: "v = (y1, y2, y3)" using prod_cases3 by blast
  obtain z1 z2 z3 where wz: "w = (z1, z2, z3)" using prod_cases3 by blast
  have 0: "vplus u v = (x1+y1, x2+y2, x3+y3)" using ux vy by (simp add:vplus_def)
  have 1: "dot (vplus u v) w = ((x1+y1)*z1+(x2+y2)*z2+(x3+y3)*z3)" using 0 wz  by (simp add: dot_def)
  have 2: "dot u w = x1 * z1 + x2 * z2 + x3 *z3" using ux wz by (simp add: dot_def)
  have 3: "dot v w = y1 * z1 + y2 * z2 + y3 *z3" using vy wz by (simp add: dot_def)
  show ?thesis using 1 2 3 by argo
qed

lemma dot_scalar [simp]:
  fixes u v s
  shows "dot u (smult s v) = s * dot u v"
proof -
  obtain x1 x2 x3 where ux: "u = (x1, x2, x3)" using prod_cases3 by blast
  obtain y1 y2 y3 where vy: "v = (y1, y2, y3)" using prod_cases3 by blast
  have 0: "smult s v = (s*y1, s*y2, s*y3)" using ux vy by (simp add:smult_def)
  have 1: "dot u (smult s v) = x1*s*y1+ x2*s*y2+ x3*s*y3" using ux vy 0 by (simp add:dot_def)
  have 2: "dot u (smult s v) = s * (x1*y1+ x2*y2+ x3*y3)" using 1 by argo 
  have 3: "s * dot u v = s * (x1*y1+ x2*y2+ x3*y3)" using ux vy by (simp add: dot_def)
  show ?thesis using 0 1 2 3 by argo
qed

lemma dot_pos:
  fixes u
  shows "(dot u u \<ge> 0)"
proof -
  obtain x1 x2 x3 where ux: "u = (x1, x2, x3)" using prod_cases3 by blast
  have 1: "dot u u  = x1*x1 + x2*x2 + x3*x3 " using ux dot_def by (simp add: dot_def ux)
  have 2: "x1*x1 + x2*x2 + x3*x3 \<ge> 0 " by simp
  show ?thesis using 1 2 by auto
qed

(* prove dot(u,u) = 0 only if u = 0 *)
lemma dot_non_degenerate:
  fixes u
  shows "(dot u u = 0) \<longleftrightarrow> (u = (0,0,0))"
proof -
  obtain x1 x2 x3 where ux: "u = (x1, x2, x3)" using prod_cases3 by blast
  have 1: "(dot u u = 0)  = (x1*x1 + x2*x2 + x3*x3 = 0)" using ux dot_def by (simp add: dot_def ux)
  show ?thesis using 1 dot_pos by (simp add: add_nonneg_eq_0_iff ux)
qed

lemma pythag_setup:
  fixes u v
  assumes "v \<noteq> (0,0,0)"
  defines "s \<equiv> smult ((dot u v)/(dot v v)) v"
  defines "t \<equiv> vplus u (smult (-1) s)"
  shows "dot s t = 0"
  using dot_commute dot_distrib dot_scalar s_def t_def by auto


lemma pythag:
  fixes u v w
  assumes "dot v w = 0"
  assumes "u = vplus v w"
  shows "(dot u u) = (dot v v) + (dot w w)"
  using assms(1,2) dot_commute dot_distrib by auto



thm  discriminant_iff

lemma cs1: 
  fixes u v s
  assumes "(dot v v)  \<noteq> 0"
  shows "s*s* dot v v + s * 2 *  (dot u   v) + (dot  u u) \<ge> 0"
proof - 
  have 0: "dot (vplus u (smult s v))  (vplus u (smult s v)) \<ge> 0" using dot_pos smult_def by blast
  have 1: "dot u u + dot u (smult s v)  + dot (smult s v) u + dot  (smult s v)  (smult s v) \<ge> 0"  
    using 0 dot_distrib dot_commute by simp
  have 2: "dot u u + 2 * (dot u (smult s v)) + dot  (smult s v)  (smult s v) \<ge> 0" using 1 dot_commute by simp
  have A3: "dot v v \<noteq> 0" using assms by auto
  have 5: "s*s* dot v v + s * 2 *  (dot u   v) + (dot  u u) \<ge> 0" using 2 by (simp add:  dot_commute)
  then show ?thesis using 5 by auto
qed

lemma cs2:
  fixes u v s
  assumes "(dot v v)  \<noteq> 0"
  shows "\<forall>s . s*s* dot v v + s * 2 *  (dot u   v) + (dot  u u) \<ge> 0"
  using cs1 assms by blast

thm discriminant_iff

thm discriminant_iff [of "(dot v v)" t "2* (dot u v)" "(dot u u)"]

(* re=quoted from the discriminant theory *)
lemma discriminant_nonneg_ex:
  fixes a b c :: real
  assumes "a \<noteq> 0"
    and "discrim a b c \<ge> 0"
  shows "\<exists> x. a * x\<^sup>2 + b * x + c = 0"
  by (auto simp: discriminant_nonneg assms)

thm discriminant_pos_ex

lemma discriminant_pos_cross_axis:
  fixes a b c :: real
  assumes "a \<noteq> 0"
    and "discrim a b c > 0"
  shows "\<exists> x. (a * x\<^sup>2 + b * x + c) * a  < 0"
proof -
  have 0: "(a * (-b/(2*a))^2 + b * (-b/(2*a)) + c ) * a = ((a*b^2)/(4*a^2) - b^2 / (2*a) + c)*a" using assms 
  by (simp add: power2_eq_square)
  have 1: "... = (b^2 / (4*a) - 2 * (b^2)/(4*a) + c)* a" using 0 by (simp add: power2_eq_square)
  have 2: "... = (-(b^2) / (4*a)  + c) * a" using 1 by argo
  have 3: "... = -(b^2)*a / (4*a)  + c * a" using 2 assms by argo
  have 4: "... = -(b^2) / (4)  + c * a" using 3 assms by auto
  have 5: "... = (1/4) * (-(b^2)   + 4 * a * c)" using 4 assms by auto
  have 6: "... = (1/4) * (- (discrim a b c))" using 5 discrim_def by auto
  have 7: "(a * (-b/(2*a))^2 + b * (-b/(2*a)) + c ) * a = (1/4) * (- (discrim a b c))" using 0 1 2 3 4 5 6 by presburger
  have 8: "(a * (-b/(2*a))^2 + b * (-b/(2*a)) + c ) * a < 0" using 7 assms by auto
  show ?thesis using 8 by blast
qed

lemma no_solutions_discrim_neg:
  fixes a b c :: real
  assumes "a \<noteq> 0"
  assumes "\<forall> x. a * x\<^sup>2 + b * x + c \<noteq> 0"
  shows "discrim a b c < 0"
  using discriminant_nonneg_ex 
  using assms(1,2) not_less by blast

lemma cauchy_schwartz:
  fixes u v
  shows "(dot u v)^2 \<le> ( dot u u)* (dot v v)"
proof (cases "(dot v v)  = 0")
  case True
  then show ?thesis
  by (metis dot_non_degenerate dot_scalar mult_zero_left mult_zero_right nle_le power2_eq_square)
next
  case False
  have vpos: "dot v v > 0" using False dot_pos less_eq_real_def by metis
  have 0: "\<forall> s . dot (vplus u (smult s v))  (vplus u (smult s v)) \<ge> 0" using dot_pos smult_def by blast
  have 1: "\<forall> s .dot u u + dot u (smult s v)  + dot (smult s v) u + dot  (smult s v)  (smult s v) \<ge> 0"  
    using 0 dot_distrib dot_commute  by (simp add: is_num_normalize(1))
  have 2: "\<forall> s . dot u u + 2 * (dot u (smult s v)) + dot  (smult s v)  (smult s v) \<ge> 0" 
    using 1 dot_commute by (simp add: add.assoc)
  have 5: "\<forall> s . s*s* dot v v + s * 2 *  (dot u   v) + (dot  u u) \<ge> 0" using 2  using False cs1 by blast

  have 6: "discrim (dot v v) (2 * dot u v) (dot u u) \<le> 0"
  proof (rule ccontr)
    assume ch: "\<not> (discrim (dot v v) (2 * dot u v) (dot u u) \<le> 0)"
    have A: "discrim (dot v v) (2 * dot u v) (dot u u) > 0" using ch by simp
    have B: "\<exists> x. ((dot v v) * x\<^sup>2 + (2 * dot u v)  * x + dot u u) * (dot v v) < 0" 
      using A vpos discriminant_pos_cross_axis [of "(dot v v)" "2* (dot u v)" "(dot u u)"] by argo
    show "False" using B 5  by (metis dot_pos linorder_not_less mult.assoc mult.commute mult_nonneg_nonneg power2_eq_square)
  qed 
  have 7: "(2 * dot u v)^2 - 4 * (dot v v) * (dot u u) \<le> 0" using 0 6 discrim_def by simp
  then show ?thesis using 7  by (simp add: mult.commute)
qed

(* Prove squared-cauchy-schwartz by expanding dot(u+v, u+v) \ge 0 *)
(* Prove equality in dot^2(u,v) = dot^2(u,u) dot^2(v,v) iff v = -cu for some c. Idea: look at dot(v + cu, v+cu).  *)
lemma q:
  fixes u v
  shows "vplus (vplus u (smult (-1) v)) v = u"
proof -
  obtain x1 x2 x3 where ux: "u = (x1, x2, x3)" using prod_cases3 by blast
  obtain y1 y2 y3 where vy: "v = (y1, y2, y3)" using prod_cases3 by blast
  have 2: "vplus (vplus u (smult (-1) v)) v = vplus (vplus u (-y1, -y2, -y3)) v" using vy unfolding smult_def by simp
  have 3: "... = vplus (vplus (x1, x2, x3) (-y1, -y2, -y3)) (y1, y2, y3)" by (simp add: ux vy)
  have 4: "... = vplus (x1 - y1, x2-y2, x3-y3) (y1, y2, y3)" by (simp add: vplus_def)
  have 5: "... = (x1, x2, x3)" by (simp add: vplus_def)
  have 6: "... = u" using ux by simp
  thus ?thesis using 2 3 4 5 6 by simp
qed

lemma cs_equality:
  fixes u v w
  assumes "v \<noteq> (0,0,0)"
  assumes "(dot u v)^2  = (dot u u) *  (dot v v)"
  defines "s \<equiv> smult ((dot u v)/(dot v v)) v"
  defines tdef: "t \<equiv> vplus u (smult (-1) s)"
  shows "\<exists> c . u = smult c v"
proof -
  have 0: "u = vplus s t" using q assms vplus_comm by auto
  have 1: "t = (0,0,0)" using assms tdef 
  by (smt (z3) Groups.mult_ac(2) divide_non_zero dot_commute dot_distrib dot_non_degenerate dot_scalar power2_eq_square q times_divide_eq_left)
  have 2: "u = s" using 0 1 vplus_def 
  by (metis (lifting) add.commute add_cancel_left_right dot_distrib dot_non_degenerate q)
  have 3: "u = smult ((dot u v)/(dot v v)) v" using 2 assms by blast
  show ?thesis using 3 by blast
qed

lemma dot_cross_zero: 
  fixes ux uy uz vx vy vz::"real"
  assumes "u = (ux, uy, uz)"
  assumes "v = (vx, vy, vz)"
  assumes "n = (nx, ny, nz)"
  assumes "n = cross u v"
  shows "(dot u n = 0)" and "(dot v n = 0)"
proof -
  have ndef: "n = (uy * vz - uz * vy, -ux * vz + uz * vx, ux * vy - uy * vx)" using cross_def assms 
  by (metis (no_types, lifting) add.commute add.inverse_inverse diff_minus_eq_add mult.commute mult_minus_right old.prod.case)

  have "dot u n = dot (ux,uy, uz)  (uy * vz - uz * vy, -ux * vz + uz * vx, ux * vy - uy * vx)" using assms ndef by auto
  also have "... = ux * (uy * vz - uz * vy) + uy * ( -ux * vz + uz * vx) + uz * (ux * vy - uy * vx)" 
    by (simp add: dot_def)
  also have "... = ux * uy * vz - ux * uz * vy - uy*ux*vz + uy*uz*vx + uz * ux * vy - uz * uy * vx"
    by argo
  also have "... = 0" by simp
  finally show s:"dot u n = 0" by auto

  have "dot v n = dot (vx,vy, vz)  (uy * vz - uz * vy, -ux * vz + uz * vx, ux * vy - uy * vx)" using assms ndef by auto
  also have "... = vx * (uy * vz - uz * vy) + vy * ( -ux * vz + uz * vx) + vz * (ux * vy - uy * vx)" 
    by (simp add: dot_def)
  also have "... = vx * uy * vz - vx * uz * vy - vy*ux*vz + vy*uz*vx + vz * ux * vy - vz * uy * vx"
    by argo
  also have "... = 0" by simp
  finally show s:"dot v n = 0" by auto
qed

(*
lemma cross_prod_length2:
  fixes u v
  shows "squared_length (cross u v) = 
    (squared_length u ) * (squared_length v ) - 
  (dot u v) *  (dot u v)"

nonzero_square_length_implies_nonzero_vector
*)

end


