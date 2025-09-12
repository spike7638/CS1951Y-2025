theory "Chapter1-1"
  imports Complex_Main  "HOL-Library.Uprod" "HOL-Library.Quadratic_Discriminant" 

begin

(* ML\<open>Context.>> (Context.map_theory (Config.put_global Blast.trace (true)))\<close> *)

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

(* a real treat: checking to see whether you have to have at least 5 points in an affine plane. *)
(*
proposition (in affine_plane) five_points_necessary: 
  assumes "finite Points"
  shows "card Points \<ge> 5"
    by nitpick
  oops
*)

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
    sorry
  oops
(*  proof cases
    case lmmk
    ... *)

text\<open>The following says not that parallelism is reflexive (it's not, at least not on all of type 'l!), 
but rather that when restricted to the set Lines, it's reflexive.\<close>
lemma parallel_refl:
  shows "reflp_on Lines parallel"
  sorry

lemma parallel_sym:
  shows "symp parallel" 
  sorry

lemma parallel_trans:
  shows "transp_on Lines parallel" 
  sorry

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
  sorry

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

text \<open>\daniel
We can also prove some basic theorems about affine planes not in Hartshorne: every
point lies on some line; for every line, there's \emph{some} point not on it; every line contains some point, and in fact every line 
contains two points, although we'll delay that for a moment. \done\<close>

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


end


