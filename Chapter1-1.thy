theory "Chapter1-1"
  imports Complex_Main  "HOL-Library.Uprod" (*"HOL-Library.Quadratic_Discriminant" *)

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
git@github.com:spike7638/CS1951Y-2025.git
Within Isabelle, numbered propositions or theorems from Hartshorne are given names that tie back 
to the text, so Proposition 1.1 in the text is called \texttt{Prop1P1}, with ``P'' replacing the period, 
for instance. 

We've based our theory on "Complex\_Main" instead of main so that we have the datatype "real". To 
characterize affine and projective planes (the main topics of study) we use ``locales'', an Isabelle 
construct that lets us say ``this entity satisfies this collection of defining axioms.''

This "starter file" is about 1400 lines long, and reflects a modest part of Chapter 1 of 
Hartshorne's book. That's partly because I've added some commentary, and partly because I've often 
used the more verbose fixes-assumes-shows way of stating theorem, and partly because a single throwaway
sentence in the text, like "it's easy to see that the usual coordinate plane satisfies the axioms 
of an affine plane" can turn into a great many lines of proving here; even asserting the truth 
of the implicit claims can take a page, and proofs are often longer.

If something I've written seems duplicated, out of order, unnecessary -- go ahead and delete it.
In subsequent chapters, the process of translating statements in Hartshorne into lemmas/theorems
in this formalization will fall more and more to students rather than to me. 

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
  using assms parallel_def by auto

lemma parallel_symmetric [iff]: 
  fixes l m
  assumes "parallel l m"
  shows "parallel m l"
  using assms parallel_def by auto
(* We can't prove parallel is transitive yet, because it 
actually requires axiom 2 of a projective plane *)

lemma parallelE [elim]:
  assumes "parallel l m"  and
  "l \<in> Lines" and "m \<in> Lines"
  obtains (eq) "l = m" | (disjoint) "(\<not> (\<exists> P. P \<in> Points \<and> P \<lhd>  l \<and> P \<lhd>  m)) 
    \<and> (l \<in> Lines) \<and> (m \<in> Lines)"
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
  using assms parallel_def by auto

lemma parallel_if_no_shared_points2I [intro]:
  assumes "\<forall>P .  P \<notin>  Points \<or> \<not> P \<lhd>  l \<and>  \<not>P \<lhd>  m" and
  "l \<in> Lines" and "m \<in> Lines"
  shows "l || m"
  using assms parallel_def by auto

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
    a1a: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> join P Q \<in> Lines \<and> P \<lhd> (join P Q)  \<and> Q \<lhd>  (join P Q)" and
    a1b: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points; P \<lhd> m; Q \<lhd> m\<rbrakk> \<Longrightarrow> m = join P Q" and
    a2a: "\<lbrakk>P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> find_parallel l P \<in> Lines" and
    a2b: "\<lbrakk>P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> (find_parallel l P) || l" and
    a2c: "\<lbrakk>P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> P \<lhd> (find_parallel l P)" and
    a2d: "\<lbrakk>P \<in> Points; l \<in> Lines; m \<in> Lines; m || l; P \<lhd> m\<rbrakk> \<Longrightarrow> m = find_parallel l P" and
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
  using assms a1a a1b by auto

definition (in affine_plane_data) liesOn :: "'p \<Rightarrow> 'l \<Rightarrow> bool" (infix "liesOn" 50) where
  "P liesOn m = (if P  \<in> Points \<and> (m \<in> Lines) then P \<lhd>  m  else undefined)"

definition  (in affine_plane_data) contains :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "contains" 50) where
  "m contains P = (P liesOn m)"

theorem join_containsL:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P \<in> Points"
  assumes "Q \<in> Points"                                          
  shows "P liesOn (join P Q)"
  using assms a1a liesOn_def by auto                                                                                                                   

theorem join_containsL2:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P \<in> Points"
  assumes "Q \<in> Points"                                          
  shows "P \<lhd> (join P Q)"
  using assms a1a by auto

theorem join_containsR:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P \<in> Points"
  assumes "Q \<in> Points"                                          
  shows "Q liesOn (join P Q)"
  using assms a1a liesOn_def by auto

theorem join_containsR2:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "Q \<lhd> (join P Q)"
  using assms a1a by auto

theorem contains_implies_liesOn:
  fixes P m
  assumes "P  \<in> Points"
  assumes "m  \<in> Lines"
  assumes "m contains P"
  shows "P liesOn m"
  using assms contains_def liesOn_def by auto

theorem liesOn_implies_contains:
  fixes P m
  assumes "P  \<in> Points"
  assumes "m  \<in> Lines"
  assumes "P liesOn m"
  shows "m contains P"
  using assms contains_def liesOn_def by auto

lemma parallel_transitive: 
  fixes l m k
  assumes "parallel l m"
  assumes "parallel m k"
  shows "parallel l k"
proof -
  consider 
    (lmmk) "(l = m)" and "(m = k)" 
    | (lm) "(l = m)" and "(m \<noteq> k)" 
    | (mk) "(l \<noteq> m)" and "(m = k)" 
    | (neither) "(l \<noteq> m)" and "(m \<noteq> k)" by blast
  then show ?thesis
  proof (cases)
    case lmmk
    then show ?thesis using assms parallel_def by auto
  next
    case lm
    then show ?thesis using assms parallel_def by auto
  next
    case mk
    then show ?thesis using assms parallel_def by auto
  next
    case neither
    then show ?thesis using assms parallel_def a2d by metis 
  qed
qed

text\<open>The following says not that parallelism is reflexive (it's not, at least not on all of type 'l!), 
but rather that when restricted to the set Lines, it's reflexive.\<close>
lemma parallel_refl:
  shows "reflp_on Lines parallel" 
  using parallel_reflexive reflp_on_def by auto

lemma parallel_sym:
  shows "symp parallel" 
  using symp_def by auto

lemma parallel_trans:
  shows "transp_on Lines parallel" 
  using parallel_transitive transp_on_def by blast

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
  using assms parallel_def by auto

text \<open>Here's more or less a translation of Hartshorne's three-line proof.\<close>

lemma parallel_transitive2:
  fixes k m n 
  assumes asm1: "k || m" and asm2: "m || n" 
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
    have all_lines: "k \<in> Lines \<and> m \<in> Lines \<and> n \<in> Lines" 
      using parallel_to_Lines False kmdiff1 asm2 asm1 False by blast 
    show "k || n"
    proof (rule ccontr)
      assume cHyp: "\<not> (k || n)"
      from parallel_def cHyp 
      have 0: " ((\<not> (k = n)) \<and> (((\<exists>P. P \<in> Points \<and> P \<lhd>  k \<and> P \<lhd>  n)) 
        \<or> (k \<notin> Lines) \<or> (n \<notin> Lines)))" using asm1 by blast 
      have 3: "(\<not> (k = n)) \<and> (((\<exists>P. P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)))" 
        using 0 all_lines by blast
      have 5: "(\<exists>P. P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" using 3 cHyp by blast
      obtain P where 6: "P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n" using 5 by auto
      have 7: "k || m \<and> P \<lhd> k" using asm1 6 by blast
      have 8: "k = find_parallel m P" using  6 7 a2d kmdiff1 all_lines by blast
      have 9: "n || m \<and> P \<lhd> n" using asm2 6  by blast
      have 10: "n = find_parallel m P" using  6 9 a2d kmdiff1 all_lines by blast
      have 11: "n = k" using 8 10 by auto
      show "\<not> k || n \<Longrightarrow> False" using 3 11 by blast
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
  assumes "\<forall>P. (P \<in> Points) \<longrightarrow> (\<not> P \<lhd> l) \<or> (\<not> P \<lhd> m)"
  shows "l || m" 
  using assms by auto


text  \<open>\begin{hartshorne}
\prop[1.2] Two distinct lines have at most one point in common.

\proof For if $l, m$ both pass through two distinct points $P, Q,$ then by axiom A1, $l = m.$ \endproof
\end{hartshorne}
\<close>

lemma (in affine_plane) prop1P2: 
  "\<lbrakk>l \<noteq> m; l \<in> Lines; m \<in> Lines; P \<in> Points; Q \<in> Points; 
  P \<lhd> l; P \<lhd> m; Q \<lhd> l; Q \<lhd> m\<rbrakk> \<Longrightarrow> P = Q"
  using a1b by blast

text \<open>We can use find_theorems to show all the things that have been created in the background as a result of 
defining the 'affine_plane' locale and proving all these small lemmas. Be sure to look at the last two in the list closely. \<close>
find_theorems affine_plane

text \<open>\daniel
We can also prove some basic theorems about affine planes not in Hartshorne: every
point lies on some line; for every line, there's \emph{some} point not on it; every line contains some point, and in fact every line 
contains two points, although we'll delay that for a moment. \done\<close>

text \<open>\hadi\<close>
lemma (in affine_plane) containing_line: 
  "S \<in> Points \<Longrightarrow> (\<exists>l. (l \<in> Lines \<and> S \<lhd> l))"
proof -
  assume sdef: "S \<in> Points"
  obtain T where tdef: "T \<in> Points \<and> T \<noteq> S" using a3 by auto
  have "(join S T) \<in> Lines" using a1a tdef sdef by auto
  then show ?thesis using join_containsL2 sdef tdef by auto
qed
(* or simply using a1a a3 by metis *)
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in affine_plane) missed_point: 
  "k \<in> Lines \<Longrightarrow> (\<exists>S. (S \<in> Points \<and> (\<not> S \<lhd> k)))" 
proof -
  assume kdef: "k \<in> Lines"
  obtain P Q R where pqr: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)" using a3 by auto
  have "(\<not> P \<lhd> k) \<or> (\<not> Q \<lhd> k) \<or> (\<not> R \<lhd> k)" 
    using kdef pqr collinear_def by auto
  then show ?thesis using pqr by auto
qed
(* or simply using collinear_def a3 by metis *)
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in affine_plane) contained_point: 
  assumes "k \<in> Lines"
  shows "\<exists>S. S \<in> Points \<and> S \<lhd> k"
proof (rule ccontr)
  assume cd: "\<not> (\<exists>S. S \<in> Points \<and> S \<lhd> k)"
  obtain P Q R where pqr: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)" using a3 by auto
  show False
  proof -
    have 0: "\<not> (join P Q || join Q R)" 
      using pqr a1a collinear_def parallel_def by metis
    have 1: "join P Q || k \<and> join Q R || k" using pqr a1a assms cd by auto
    show False using 0 1 parallel_transitive by blast
  qed
qed
text \<open>\done\<close>


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
Here's the theorem:
lemma (in affine_plane) contained_points: 
  fixes k
  assumes "k \<in> Lines"
  shows "\<exists>S T. S \<in> Points \<and> T \<in> Points \<and> S \<noteq> T \<and> S \<lhd> k \<and> T \<lhd> k"
  sorry
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

text\<open>\done \done  Examples of some easy theorems about affine planes, not mentioned in Hartshorne. \jackson \<close>      

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
1. The point is P or Q or R. (you need to figure out how to proceed from here) 
2. The point T is different from those 3 points. Then PT, QT, RT cannot
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

proposition (in affine_plane) four_points_necessary: 
  "\<exists>(P :: 'p) (Q :: 'p) (R :: 'p) (S :: 'p). P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S 
  \<and> Q \<noteq> S \<and> R \<noteq> S \<and> P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points"
text \<open> \George \<close>
proof -
  obtain P Q R where h0a: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points" and h0b: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)" using a3 by auto
  have h1: "join Q R \<in> Lines \<and> Q \<lhd>  (join Q R)  \<and> R \<lhd>  (join Q R)" using a1a h0a h0b by auto
  let ?l = "find_parallel (join Q R) P"
  have h2a: "?l \<in> Lines" using a2a h1 h0a by auto
  have h2b: "?l || join Q R" using a2b h1 h0a by auto
  have h3: "join P Q \<in> Lines \<and> P \<lhd>  (join P Q)  \<and> Q \<lhd>  (join P Q)" using a1a h0a h0b by auto
  let ?m = "find_parallel (join P Q) R"
  have h4a: "?m \<in> Lines" using a2a h3 h0a by auto
  have h4b: "?m || join P Q" using a2b h3 h0a by auto
  consider (parallel) "?l || ?m" | (not_parallel) "\<not>(?l || ?m)" by auto
  then show ?thesis
  proof cases
    case parallel
    show ?thesis
    proof (rule ccontr)
      have c0: "join Q R || join P Q" using parallel h2b h4b parallel_symmetric 
        parallel_transitive [of "join P Q"] by blast
      have c1: "Q \<lhd> join Q R" and "Q \<lhd> join P Q" using h1 h3 by auto
      consider (equal) "join Q R = join P Q" 
      | (not_equal) "join Q R \<noteq> join P Q" by auto
      then have c2: "join Q R = join P Q" 
      proof cases 
        case equal
        show ?thesis using equal by auto
      next
        case not_equal
        show ?thesis
        proof (rule ccontr)
          show False using c0 c1 h2a h4a not_equal parallel_def h0a h3 by blast
        qed
      qed
      show False using c2 h0b collinear_def h0a h1 h3 by auto
    qed
  next
    case not_parallel
    obtain S where "S \<in> Points" and "P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S" using a2c h0a h0b h1 
      h2b h3 h4b not_parallel parallel_def unfolding collinear_def by metis
    show ?thesis using \<open>P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S\<close> \<open>S \<in> Points\<close> h0a h0b by auto
  qed
qed
text \<open>\done\<close>

text \<open>We can amplify this slightly to show that not only are there four points, but that no 
three are collinear; then we'll finally be able to show that every line contains at least two points!\<close>

text \<open>\hadi\<close>
lemma (in affine_plane) not_collinear_join:
  fixes P Q R 
  assumes "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points"
  assumes "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R"
  assumes "\<not> R \<lhd> (join P Q)"
  shows "\<not> collinear P Q R"
proof (rule ccontr)
  assume cd: "\<not> (\<not> collinear P Q R)"
  show False
  proof -
    have 0: "collinear P Q R" using cd by auto
    obtain l where ldef: "l \<in> Lines \<and> P \<lhd> l \<and> Q \<lhd> l \<and> R \<lhd> l" 
      using 0 assms collinear_def by auto
    have 1: "l = (join P Q)" using a1b assms ldef by auto
    show False using 1 assms ldef by auto
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in affine_plane) collinear_join:
  fixes P Q R 
  assumes "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points"
  assumes "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R"
  assumes "R \<lhd> (join P Q)"
  shows "collinear P Q R"
proof -
  have "P \<lhd> (join P Q) \<and> Q \<lhd> (join P Q)" 
    using assms join_containsL2 join_containsR2 by auto
  then show ?thesis using assms a1a collinear_def by auto
qed
(* or simply using a1a assms collinear_def containing_line by metis *)
text \<open>\done\<close>

proposition (in affine_plane) four_points_noncollinear_triples: "\<exists>(P :: 'p) (Q :: 'p) (R :: 'p) (S :: 'p). 
      P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S \<and> P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points
\<and> \<not> collinear P Q R \<and> \<not> collinear P Q S \<and> \<not> collinear P R S \<and> \<not> collinear Q R S"
proof -
  obtain P Q R where h0: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points
    \<and> \<not> collinear P Q R" using a3  by auto
  obtain l where h1: "l=find_parallel (join P Q) R" by auto
  obtain k where h2: "k=find_parallel (join P R) Q" by auto
  have h3: "\<not>l||k"  
  proof (rule ccontr)
    assume ch: "\<not>\<not>(l||k)"
    have h4: "(join P Q)||l" using h0 h1 a1a a2b by auto
    have h5: "k||(join P R)" using h0 h2 a1a a2b by auto
    have h6: "(join P Q)||(join P R)" using parallel_transitive ch a1a h4 h5 by metis
    have h7: "P\<lhd>(join P Q)\<and>P\<lhd>(join P R)" using a1a h0 by blast
    have h8: "\<not>(join P Q||join P R)" using h7 h0 parallel_def collinear_def a1a by metis
    show False using parallel_def h6 h0 h8 by auto 
  qed
  obtain S where h4: "S\<in>Points\<and>S\<lhd>l\<and>S\<lhd>k" using h0 h3 h1 h2 parallel_def a1a a2a by auto
  (*now we need to show that S is not equal to P Q R*)
  have h5: "P\<noteq>S\<and>R\<noteq>S\<and>Q\<noteq>S " using a1a a1b a2b a2c h3 h4 h0 h1 h2 parallel_def by metis
  (* now we need to show that S isn't collinear to PQ, PR, QR*)
  have h6: "\<not>(collinear P Q S)"
  proof (rule ccontr)
    assume ch: "\<not>\<not>(collinear P Q S)"
    have h7: "collinear P Q S" using ch by auto
    have h8: "\<not> l||join P Q" using h7 h0 a1a a1b a2c h1 h2 h3 h4 h5 parallelE collinear_def by metis
    show "False" using h0 h1 a1a a2b h8 by auto
  qed
  have h7: "\<not>(collinear P R S)"
  proof (rule ccontr)
    assume ch: "\<not>\<not>(collinear P R S)"
    have h8: "collinear P R S" using ch by auto
    have h9: "\<not> k||join P R" using h8 h0 a1a a1b a2c h1 h2 h3 h4 h5 parallelE collinear_def by metis
    show "False" using h0 h1 h2 a1a a2b h9 by metis
  qed
  have h8: "\<not>(collinear Q R S)"
  proof (rule ccontr)
    assume ch: "\<not>\<not>(collinear Q R S)"
    have h9: "collinear Q R S" using ch by auto
    have h10: "S\<lhd>join Q R\<and>S\<lhd>k" using h0 h2 join_containsR collinear_def a1b h9 h4 by auto
    have h11: "S=Q" using a1a a2a a2c h0 h1 h10 h2 h3 h4 h5 parallel_def prop1P2 by metis
    show "False" using h11 h5 by auto
  qed
  show ?thesis using h8 h0 h7 h6 h5 h4 by blast
qed

text \<open>\hadi\<close>
lemma (in affine_plane) join_parallel_collinear:
  fixes P Q R
  assumes "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points"
  assumes "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R"
  assumes "(join P Q) || (join P R)"
  shows "collinear P Q R"
proof -
  let ?l = "join P Q" and ?m = "join P R"
  consider
  (eq) "?l = ?m"
  | (disj) "(\<not> (\<exists> P. P \<in> Points \<and> P \<lhd> ?l \<and> P \<lhd> ?m)) 
    \<and> (?l \<in> Lines) \<and> (?m \<in> Lines)" 
    using assms parallelE parallel_def by blast
  then show ?thesis
  proof (cases)
    case eq
    then show ?thesis using assms a1a collinear_join by auto
  next
    case disj
    then show ?thesis using assms join_containsL2 by blast
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
proposition (in affine_plane) four_points_parallel_pairs: 
  "\<exists>(P :: 'p) (Q :: 'p) (R :: 'p) (S :: 'p). P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S 
  \<and> Q \<noteq> S \<and> R \<noteq> S \<and> P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points 
  \<and> parallel (join P Q) (join R S) \<and> parallel (join P R) (join Q S) 
  \<and> (join P Q) \<noteq> (join R S) \<and> (join P R) \<noteq> (join Q S) \<and> \<not> collinear P Q R 
  \<and> \<not> collinear P Q S \<and> \<not> collinear P R S \<and> \<not> collinear Q R S"
proof -
  obtain P Q R where pqr: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R 
    \<and> P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> \<not> collinear P Q R"
    using a3 by auto
  let ?l = "find_parallel (join P R) Q"
  let ?m = "find_parallel (join P Q) R" 
  have 0: "\<not> ?l || ?m"
  proof (rule ccontr)
    assume cd: "\<not> (\<not> ?l || ?m)"
    show False
    proof -
      have prls: "?l || ?m \<and> (join P Q) || ?m \<and> (join P R) || ?l" 
        using cd a1a a2b pqr by auto
      then have "?m || (join P R)" using parallel_transitive by blast
      then have "(join P Q) || (join P R)" 
        using prls parallel_transitive parallel_symmetric by blast
      then have "collinear P Q R" using pqr join_parallel_collinear by auto
      then show False using pqr by auto
    qed
  qed
  obtain S where sdef0: "S \<in> Points \<and> S \<lhd> ?l \<and> S \<lhd> ?m" 
    using 0 a1a a2a pqr by blast
  then have "S \<noteq> P \<and> S \<noteq> Q \<and> S \<noteq> R" 
    using 0 a1a a1b a2b a2c pqr parallelE unfolding collinear_def by metis
  then have sdef: "S \<in> Points \<and> S \<noteq> P \<and> S \<noteq> Q \<and> S \<noteq> R \<and> S \<lhd> ?l \<and> S \<lhd> ?m" 
    using sdef0 by auto
  have 1: "?m = (join R S) \<and> ?l = (join Q S)" 
    using a1a a1b a2c pqr sdef by auto
  have 2: "?m || (join P Q) \<and> ?l || (join P R)" using a1a a2b pqr by auto
  have 3: "(join P Q) || (join R S) \<and> (join P R) || (join Q S)" 
    using 1 2 by auto
  have 4: "(join P Q) \<noteq> (join R S) \<and> (join P R) \<noteq> (join Q S)" 
    using a1a pqr sdef unfolding collinear_def by metis
  have "\<not> S \<lhd> (join P Q) \<and> \<not> S \<lhd> (join P R) \<and> \<not> S \<lhd> (join Q R)" 
    using 1 2 4 parallel_def sdef a1a a1b pqr by metis
  then have 5: "\<not> collinear P Q S \<and> \<not> collinear P R S \<and> \<not> collinear Q R S" 
    using sdef pqr not_collinear_join by auto
  show ?thesis using 3 4 5 pqr sdef by metis
qed
text \<open>\done\<close>

text \<open>Finally, we can prove that every line contains at least two points. Recall that the statement was

lemma (in affine_plane) contained_points: 
  fixes k
  assumes "k \<in> Lines"
  shows "\<exists> S T. S \<in> Points \<and> T \<in> Points \<and>  S \<noteq> T \<and>  S \<lhd> k \<and>  T \<lhd> k"

The idea of one possible proof is this: : we have 4 distinct lines, in two parallel pairs H and K. But each line from 
H intersects each line from K. 
We already know l cannot be empty. 

If l = {X}, i.e., if l contains only a single point, then that special point X lies on at most one 
line in each of H and K. 

Select the (or an) other line in each set, and call them k and n. 

Then find_parallel k X = l and same for n X. (Why?)

That makes both k and n parallel to l, so parallel to each other. But they intersect and are 
distinct. Contradiction. 
\<close>
lemma (in affine_plane) parallel_overlap_equal:
  fixes k n P
  assumes "k \<in> Lines \<and> n \<in> Lines \<and> P \<in> Points"
  assumes "k || n"
  assumes "P \<lhd> k" and "P \<lhd> n"
  shows "k = n" 
  using assms by auto

text \<open>\hadi\<close>
lemma (in affine_plane) parallel_to_collinear:
  fixes A B C
  assumes "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points"
  assumes "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C"
  assumes "join A C = join A B"
  shows "collinear A B C"
proof -
  have "C \<lhd> (join A C)" using assms join_containsR2 by blast
  then have "C \<lhd> (join A B)" using assms by auto
  then show ?thesis using assms collinear_join by auto
qed
(* or simply using assms a1a collinear_join by metis *)
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in affine_plane) contained_points: 
  fixes k
  assumes "k \<in> Lines"
  shows "\<exists>S T. S \<in> Points \<and> T \<in> Points \<and> S \<noteq> T \<and> S \<lhd> k \<and> T \<lhd> k"
proof (rule ccontr)
  assume cd: "\<not> (\<exists>S T. S \<in> Points \<and> T \<in> Points \<and> S \<noteq> T \<and> S \<lhd> k \<and> T \<lhd> k)"
  show False
  proof -
    obtain X where xdef: "X \<in> Points \<and> X \<lhd> k" 
      using assms contained_point by auto
    have k1pt: "\<forall>T. T \<in> Points \<and> X \<noteq> T \<longrightarrow> \<not> T \<lhd> k" using xdef cd by auto
    obtain P Q R S where pqrs: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S 
      \<and> Q \<noteq> S \<and> R \<noteq> S \<and> P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points 
      \<and> parallel (join P Q) (join R S) \<and> parallel (join P R) (join Q S) 
      \<and> (join P Q) \<noteq> (join R S) \<and> (join P R) \<noteq> (join Q S) \<and> \<not> collinear P Q R 
      \<and> \<not> collinear P Q S \<and> \<not> collinear P R S \<and> \<not> collinear Q R S"
      using four_points_parallel_pairs by auto
    have rsNpq: "X \<lhd> (join R S) \<longrightarrow> \<not> X \<lhd> (join P Q)"
      and prNqs: "X \<lhd> (join P R) \<longrightarrow> \<not> X \<lhd> (join Q S)" 
      using a1a pqrs xdef by auto
    obtain a b where abdef: "a \<in> Lines \<and> b \<in> Lines 
      \<and> a \<in> {(join P Q), (join R S)} \<and> b \<in> {(join P R), (join Q S)}" 
      using insertCI a1a pqrs by metis
    consider
      (some) "X \<lhd> a \<or> X \<lhd> b"
      | (none) "\<not> X \<lhd> a \<and> \<not> X \<lhd> b" by auto
    then show False
    proof (cases)
      case some
      obtain c where cdef: "c \<in> Lines \<and> c \<in> {(join P Q), (join R S)} 
        \<and> c \<noteq> a" using insertCI a1a pqrs by metis
      obtain d where ddef: "d \<in> Lines \<and> d \<in> {(join P R), (join Q S)} 
        \<and> d \<noteq> b" using insertCI a1a pqrs by metis
      then have "\<not> X \<lhd> c \<or> \<not> X \<lhd> d" using some rsNpq prNqs abdef cdef by auto
      then have "(\<forall>T. T \<in> Points \<longrightarrow> (\<not> T \<lhd> k \<or> \<not> T \<lhd> c)) 
        \<or> (\<forall>T. T \<in> Points \<longrightarrow> (\<not> T \<lhd> k \<or> \<not> T \<lhd> d))" using k1pt by auto
      then have "k || c \<or> k || d" using assms cdef ddef parallel_def by auto
      then have kcxkdx: "k = (find_parallel c X) \<or> k = (find_parallel d X)" 
        using assms a2d xdef cdef ddef by auto
      have "a = (find_parallel c X) \<or> b = (find_parallel d X)" 
        using some a2d pqrs abdef cdef ddef xdef by blast
      then have kab: "k = a \<or> k = b" using a2d parallel_if_no_shared_pointsI 
          assms cdef ddef k1pt parallel_reflexive xdef kcxkdx by metis
      obtain E where "E \<in> Points \<and> (E \<lhd> a \<or> E \<lhd> b) \<and> E \<noteq> X" using abdef pqrs
        insert_iff join_containsL2 join_containsR2 singleton_iff by metis
      then show False using k1pt kab abdef pqrs insert_iff singletonD
        join_containsL2 join_containsR2 by metis
    next
      case none
      then obtain G where gdef: "G \<in> Points \<and> G \<lhd> a \<and> G \<lhd> b" 
        using a1a abdef pqrs by auto
      have "k || a \<and> k || b" using assms none abdef k1pt by auto
      then have "a || b" using parallel_transitive by blast
      then have "a = b" using gdef abdef by auto 
      then have "collinear P Q R \<or> collinear P Q S \<or> collinear P R S 
        \<or> collinear Q R S" using parallel_to_collinear pqrs a1a a1b 
        abdef insertE singleton_iff by metis
      then show False using pqrs by auto
    qed
  qed
qed
text \<open>\done\<close>

lemma (in affine_plane) contained_points_2: 
  fixes l
  assumes "l \<in> Lines"
  shows "\<exists> S T. S \<in> Points \<and> T \<in> Points \<and>  S \<noteq> T \<and>  S \<lhd> l \<and>  T \<lhd> l"
proof (rule ccontr)
  assume ch: "\<not>(\<exists> S T. S \<in> Points \<and> T \<in> Points \<and>  S \<noteq> T \<and>  S \<lhd> l \<and>  T \<lhd> l)"
  obtain S where s_def: "S\<in>Points\<and>S\<lhd>l" using contained_point assms by auto
  have 0: "\<not>(\<exists>T. T\<in>Points\<and>S\<noteq>T\<and>T\<lhd>l)" using s_def ch assms by auto
  obtain P Q where h0: "P\<in>Points\<and>Q\<in>Points\<and>P\<noteq>Q\<and>P\<noteq>S\<and>Q\<noteq>S\<and>(\<not>collinear P Q S)\<and>(\<not>P\<lhd>l)\<and>(\<not>Q\<lhd>l)" using 0 collinear_def a3 s_def a1a prop1P2 by smt
  obtain P_parallel where h1: "P_parallel=find_parallel (join Q S) P" by auto
  have 1: "\<not>S\<lhd>P_parallel" using h1 h0 a1a a2a a2b a2c collinear_def parallel_overlap_equal s_def by metis
  have 2: "P_parallel||l" using 0 h1 h0 1 parallel_def s_def a1a a2a assms by auto
  have 3: "l||join P Q" using assms h0 a1a ch collinear_def s_def by (metis parallel_def)
  have 4: "P_parallel||join P Q" using parallel_transitive 2 3  by blast
  have 5: "P\<lhd>P_parallel\<and>P\<lhd>join P Q" using h1 h0 join_containsR a1a a2c s_def by presburger
  have 6: "\<not>P_parallel=join P Q" using h1 h0 1 a1a a2b parallel_overlap_equal s_def by metis
  show "False" using 6 4 5 h0 parallel_def by blast
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

text \<open>\spike Now we move on to showing that the four-point plane is indeed a plane. 
This is surprisingly messy. A first step is setting up the points and lines of the plane. 
Everything starting with a4 or A4 refers to this particular plane. 
\<close>
datatype a4pt = Pa | Qa | Ra | Sa
definition "A4Points = {Pa, Qa, Ra, Sa}"
definition "A4PQ = {Pa, Qa}"
definition "A4PR = {Pa, Ra}"
definition "A4PS = {Pa, Sa}"
definition "A4QR = {Qa, Ra}"
definition "A4QS = {Qa, Sa}"
definition "A4RS = {Ra, Sa}"

definition "A4Lines = {A4PQ, A4PR, A4PS, A4QR, A4QS, A4RS}"

fun A4join::"a4pt \<Rightarrow> a4pt \<Rightarrow> a4pt set"  where 
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
"A4find_parallel m T = (if (m \<in> A4Lines) then (if T \<in> m then m else (A4complement m)) else undefined)"

lemma all_pairs:
  fixes P::a4pt and Q::a4pt
  assumes "P \<noteq> Q" 
  shows "{P, Q} \<in> A4Lines"
proof (rule ccontr)
  assume cd: "\<not> ({P, Q} \<in> A4Lines)"
  show False
  proof -
    have "{P, Q} \<notin> A4Lines" using cd by auto
    then show False using assms a4pt.exhaust insert_commute insert_iff
      unfolding A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def
      A4QS_def A4RS_def by (smt (verit))
  qed
qed

text \<open>\hadi\<close>
lemma all_pairs_2:
  fixes P::a4pt and Q::a4pt
  assumes "P \<noteq> Q" 
  shows "{P, Q} \<in> A4Lines"
proof -
  consider (pq) "P = Pa \<and> Q = Qa" | (pr) "P = Pa \<and> Q = Ra" | (ps) "P = Pa \<and> Q = Sa"
  | (qr) "P = Qa \<and> Q = Ra" | (qs) "P = Qa \<and> Q = Sa" | (rs) "P = Ra \<and> Q = Sa"
  | (qp) "P = Qa \<and> Q = Pa" | (rp) "P = Ra \<and> Q = Pa" | (sp) "P = Sa \<and> Q = Pa"
  | (rq) "P = Ra \<and> Q = Qa" | (sq) "P = Sa \<and> Q = Qa" | (sr) "P = Sa \<and> Q = Ra" 
    using a4pt.exhaust assms by metis
  then show ?thesis unfolding A4Lines_def A4PQ_def A4PR_def A4PS_def 
    A4QR_def A4QS_def A4RS_def by (cases, auto)
qed
text \<open>\done\<close>

lemma all_joins_are_lines:
  fixes P Q
  assumes "P \<noteq> Q" and "P \<in> A4Points" and "Q \<in> A4Points"
  shows "A4join P Q \<in> A4Lines"
  using assms all_pairs by auto
(* this lemma does not need the second and third assumptions *)

theorem PinPQ1:
  fixes P Q
  assumes "P \<noteq> Q" and "P \<in> A4Points" and "Q \<in> A4Points" 
  shows "P \<in> A4join P Q"
  using assms by auto
(* this lemma does not need the second and third assumptions *)

theorem QinPQ1:
  fixes P Q
  assumes "P \<noteq> Q" and "P \<in> A4Points" and "Q \<in> A4Points"
  shows "Q \<in> A4join P Q"
  using assms by auto
(* this lemma does not need the second and third assumptions *)

theorem
  fixes P Q
  assumes "P \<noteq> Q" and "P \<in> A4Points" and "Q \<in> A4Points"
  shows "A4incid P (A4join P Q)"
  using assms all_pairs by auto

text \<open>\Jiayi\<close>
theorem
  fixes P Q
  assumes "P \<noteq> Q" and "P \<in> A4Points" and "Q \<in> A4Points"
  shows "A4incid Q (A4join P Q)"
  using assms all_pairs by auto
text \<open>\Done\<close>

text \<open>\Luke\<close>
theorem  A4affine_plane_a3_lemma:
  shows "Pa \<in> A4Points \<and> Qa \<in> A4Points \<and> Ra \<in> A4Points" and 
        "Pa \<noteq> Qa \<and> Pa \<noteq> Ra \<and> Qa \<noteq> Ra" and  
        "\<not>  affine_plane_data.collinear A4Points A4Lines A4incid Pa Qa Ra"
proof - 
  have 0: "Pa \<in> A4Points" using A4Points_def by auto
  have 1: "Qa \<in> A4Points" using A4Points_def by auto
  have 2: "Ra \<in> A4Points" using A4Points_def by auto

  show "Pa \<in> A4Points \<and> Qa \<in> A4Points \<and> Ra \<in> A4Points" using 0 1 2 by auto
  show "Pa \<noteq> Qa \<and> Pa \<noteq> Ra \<and> Qa \<noteq> Ra" by auto
  show "\<not>  affine_plane_data.collinear A4Points A4Lines A4incid Pa Qa Ra" 
    unfolding affine_plane_data.collinear_def A4incid.simps A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def
    using 0 1 2 by auto
qed

theorem A4affine_plane_a3: 
  " \<exists>P Q R.
       P \<in> A4Points \<and> Q \<in> A4Points \<and> R \<in> A4Points \<and>
       P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and>
       \<not> affine_plane_data.collinear
           A4Points
           A4Lines
           A4incid P Q R" 
proof - 
  show ?thesis using  A4affine_plane_a3_lemma by auto
qed
text \<open>\Done\<close>

text \<open>\Luke \Jiayi\<close>
theorem A4affine_plane_a1a: 
  fixes P Q
  assumes "P \<noteq> Q" and "P \<in> A4Points" and "Q \<in> A4Points" 
  shows "A4join P Q \<in> A4Lines" and "A4incid P (A4join P Q)" 
    and "A4incid Q (A4join P Q)"
  using assms all_pairs by auto
text \<open>\done\<close>

lemma A4affine_line_card_2:
  fixes m
  assumes "m \<in> A4Lines"
  shows "card(m) = 2"
proof -
  consider
  (pq) "m = A4PQ"
      | (pr) "m = A4PR"
      | (ps) "m = A4PS"
      | (qr) "m = A4QR"
      | (qs) "m = A4QS"
      | (rs) "m = A4RS"
    using assms A4Lines_def by blast
  then show ?thesis
  proof cases
    case pq
    have "m = {Pa, Qa}" using A4PQ_def pq by auto
    then show ?thesis using assms by auto
  next
    case pr
    have "m = {Pa, Ra}" using A4PR_def pr by auto
    then show ?thesis using assms by auto
  next
    case ps
    have "m = {Pa, Sa}" using A4PS_def ps by auto
    then show ?thesis using assms by auto
  next
    case qr
    have "m = {Qa, Ra}" using A4QR_def qr by auto
    then show ?thesis using assms by auto
  next
    case qs
    have "m = {Qa, Sa}" using A4QS_def qs by auto
    then show ?thesis using assms by auto
  next
    case rs
    have "m = {Ra, Sa}" using A4RS_def rs by auto
    then show ?thesis using assms by auto
  qed
qed

theorem A4affine_plane_a1b:  
  fixes P Q
  assumes "P \<noteq> Q" and "P \<in> A4Points" and "Q \<in> A4Points"
    and "A4incid P m" and "A4incid Q m"
  shows "m = A4join P Q"
proof -
  have 0: "A4join P Q = {P, Q}" using assms by auto
  have 1: "card(A4join P Q) = 2" using assms 0 by auto
  have 2: "m \<in> A4Lines" using assms by auto
  have 3: "card(m) = 2" using assms 2 A4affine_line_card_2 by auto
  have 4: "P \<in> m" using assms by auto
  have 5: "Q \<in> m" using assms by auto
  have 6: "m = {P, Q}" using assms 3 4 5 card_2_iff
      emptyE insertE insert_commute by metis
  then show ?thesis using assms by auto
qed

(* NB. My initial proof of the theorem above was 250 lines long. My final proof was one line. --Spike *)

lemma A4line_complement:
  fixes l
  assumes "l \<in> A4Lines"
  shows "A4complement l \<in> A4Lines"
proof -
  let ?m = "A4complement l"
  have "l = A4PQ \<or> l = A4PR \<or> l = A4PS \<or> l = A4QR \<or> l = A4QS \<or> l = A4RS" 
    using assms unfolding A4Lines_def by auto
  then have 
    "?m = A4RS \<or> ?m = A4QS \<or> ?m = A4QR \<or> ?m = A4PS \<or> ?m = A4PR \<or> ?m = A4PQ" 
    using assms A4complement.simps unfolding A4Lines_def by presburger
  then show ?thesis unfolding A4Lines_def by blast
qed

lemma A4complement_parallel_helper: 
  fixes n
  assumes "n \<in> A4Lines"
  shows "n \<inter> (A4complement n) = {}"
proof -
  have "(A4complement n) \<in> A4Lines" using assms A4line_complement by auto
  then show ?thesis
  by (smt (verit) A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def
      A4RS_def A4complement.simps Int_insert_right_if0 Int_insert_right_if1
      a4pt.distinct(1,11,3,5,7,9) assms bot_set_def disjoint_iff empty_iff inf.idem
      inf.left_idem inf_bot_left inf_bot_right inf_commute insertE insert_absorb
      insert_absorb2 insert_commute insert_disjoint(2) insert_ident insert_iff
      singletonD singletonI singleton_iff)
qed

lemma A4disjoint_parallel:
  fixes n k
  assumes "n \<inter> k = {}" and "n \<in> A4Lines" and "k \<in> A4Lines"
  shows "affine_plane_data.parallel A4Points A4Lines A4incid k n"
  using assms affine_plane_data.parallel_def by fastforce

lemma A4complement: 
  fixes n
  assumes "n \<in> A4Lines"
  shows "affine_plane_data.parallel A4Points A4Lines A4incid (A4complement n) n"
  using assms A4complement_parallel_helper 
    A4disjoint_parallel A4line_complement by presburger

theorem A4affine_plane_a2: 
  fixes P l
  assumes "\<not> A4incid P l" 
  assumes "P \<in> A4Points " and "l \<in> A4Lines"
  shows "A4find_parallel l P \<in> A4Lines" and
     "affine_plane_data.parallel A4Points A4Lines A4incid  (A4find_parallel l P) l" and
     "A4incid P (A4find_parallel l P)"

proof - 
  show "A4find_parallel l P \<in> A4Lines" using A4find_parallel.simps A4line_complement assms A4Lines_def by auto
  show "affine_plane_data.parallel A4Points A4Lines A4incid  (A4find_parallel l P) l"
    using A4find_parallel.simps A4line_complement assms A4Lines_def A4complement by auto
  have 0: "A4find_parallel l P = A4complement l" using A4find_parallel.simps assms by auto
  consider (PPa) "P = Pa"
    | (PQa) "P = Qa"
    | (PRa) "P = Ra"
    | (PSa) "P = Sa" using A4Points_def a4pt.exhaust by blast
  then show "A4incid P (A4find_parallel l P)"
  proof cases
    case PPa
    consider (lQR) "l = A4QR"
      | (lQS) "l = A4QS"
      | (lRS) "l = A4RS" using PPa A4Lines_def A4PQ_def A4PR_def A4PS_def assms(1,3) by auto
    then show ?thesis
    proof cases
      case lQR
      then have "A4complement l = A4PS" using A4complement assms PPa 
        by (simp add: A4PQ_def A4PR_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4PS_def PPa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    next
      case lQS
      then have "A4complement l = A4PR" using A4complement assms PPa 
        by (simp add: A4PQ_def A4PR_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4PR_def PPa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    next
      case lRS
      then have "A4complement l = A4PQ" using A4complement assms PPa 
        by (simp add: A4PQ_def A4PR_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4PQ_def PPa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    qed
  next
    case PQa
    consider (lPR) "l = A4PR"
      | (lPS) "l = A4PS"
      | (lRS) "l = A4RS" using PQa A4Lines_def A4PQ_def A4QR_def A4QS_def assms(1,3) by auto
    then show ?thesis
    proof cases
      case lPR
      then have "A4complement l = A4QS" using A4complement assms PQa 
        by (simp add: A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4QS_def PQa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    next
      case lPS
      then have "A4complement l = A4QR" using A4complement assms PQa 
        by (simp add: A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4QR_def PQa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    next
      case lRS
      then have "A4complement l = A4PQ" using A4complement assms PQa 
        by (simp add: A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4PQ_def PQa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    qed
  next
    case PRa
    consider (lPQ) "l = A4PQ"
      | (lPS) "l = A4PS"
      | (lQS) "l = A4QS" using PRa A4Lines_def A4PR_def A4QR_def A4RS_def assms(1,3) by auto
    then show ?thesis
    proof cases
      case lPQ
      then have "A4complement l = A4RS" using A4complement assms PRa 
        by (simp add: A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4RS_def PRa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    next
      case lPS
      then have "A4complement l = A4QR" using A4complement assms PRa 
        by (simp add: A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4QR_def PRa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    next
      case lQS
      then have "A4complement l = A4PR" using A4complement assms PRa 
        by (simp add: A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4PR_def PRa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    qed
  next
    case PSa
    consider (lPQ) "l = A4PQ"
      | (lPR) "l = A4PR"
      | (lQR) "l = A4QR" using PSa A4Lines_def A4PS_def A4QS_def A4RS_def assms(1,3) by auto
    then show ?thesis
    proof cases
      case lPQ
      then have "A4complement l = A4RS" using A4complement assms PSa 
        by (simp add: A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4RS_def PSa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    next
      case lPR
      then have "A4complement l = A4QS" using A4complement assms PSa 
        by (simp add: A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4QS_def PSa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    next
      case lQR
      then have "A4complement l = A4PS" using A4complement assms PSa 
        by (simp add: A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def doubleton_eq_iff)
      then show ?thesis using "0" A4PS_def PSa \<open>A4find_parallel l P \<in> A4Lines\<close> by auto
    qed
  qed
qed

lemma fpp: 
  fixes P l m
  assumes "l \<in> A4Lines" and  "m \<in> A4Lines"
    and  "m \<inter> l = {}" 
  shows  "m = A4complement l"
proof -
  have 0: "affine_plane_data.parallel A4Points A4Lines A4incid m l" using A4disjoint_parallel assms by auto
  have 1: "affine_plane_data.parallel A4Points A4Lines A4incid (A4complement l) l" using A4complement assms by auto
  have 2: "l \<inter> (A4complement l) = {}" using A4complement_parallel_helper assms by auto
  have what:  "(\<inter>) (m \<inter> l) \<noteq> (\<inter>) (l \<inter> m) \<or> l \<inter> m \<inter> l = m \<inter> l \<inter> l" using assms by arith
  consider
  (pq) "l = A4PQ"
      | (pr) "l = A4PR"
      | (ps) "l = A4PS"
      | (qr) "l = A4QR"
      | (qs) "l = A4QS"
      | (rs) "l = A4RS"
    using assms A4Lines_def by blast
  then show ?thesis
  proof cases
    case pq
    then have 3: "A4complement l = A4RS" using A4complement assms by auto
    then have "l \<inter> A4RS = {}" using 2 assms by auto 
    then have "m = A4RS" using what assms pq A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def disjoint_insert(2)
        insertE insertI1 singletonD by metis
    then have "m = A4complement l" using 3 by auto
    then show ?thesis .
  next
    case pr
    then have 3: "A4complement l = A4QS" using A4complement assms
      by (simp add: A4PQ_def A4PR_def A4RS_def doubleton_eq_iff)
    then have "l \<inter> A4QS = {}" using 2 assms by auto 
    then have "m = A4QS" using what assms pr A4Lines_def A4RS_def A4PQ_def A4PR_def A4PS_def A4QR_def disjoint_insert(2)
        insertE singletonD insert_iff singleton_iff by metis
    then have "m = A4complement l" using 3 by auto
    then show ?thesis .
  next
    case ps
    then have 3: "A4complement l = A4QR" using A4complement assms
    by (simp add: A4PQ_def A4PR_def A4PS_def A4QS_def A4RS_def doubleton_eq_iff)
    then have "l \<inter> A4QR = {}" using 2 assms by auto 
    then have "m = A4QR" using what assms ps A4Lines_def A4PQ_def A4PR_def A4PS_def A4QS_def A4QR_def A4PQ_def disjoint_insert(2)
        insertE singletonD A4RS_def insert_iff singleton_iff by metis
    then have "m = A4complement l" using 3 by auto
    then show ?thesis .
  next
    case qr
    then have 3: "A4complement l = A4PS" using A4complement assms
    by (simp add: A4PQ_def A4PR_def A4PS_def A4QS_def A4RS_def A4QR_def doubleton_eq_iff)
    then have "l \<inter> A4PS = {}" using 2 assms by auto 
    then have "m = A4PS" using what assms qr A4Lines_def A4PQ_def A4PR_def A4PS_def A4QS_def A4QR_def A4PQ_def disjoint_insert(2)
        insertE singletonD A4RS_def insert_iff singleton_iff by metis
    then have "m = A4complement l" using 3 by auto
    then show ?thesis .
  next
    case qs
    then have 3: "A4complement l = A4PR" using A4complement assms
    by (simp add: A4PQ_def A4PR_def A4PS_def A4QS_def A4RS_def A4QR_def doubleton_eq_iff)
    then have "l \<inter> A4PR = {}" using 2 assms by auto 
    then have "m = A4PR" using what assms qs A4Lines_def A4PQ_def A4PR_def A4PS_def A4QS_def A4QR_def A4PQ_def disjoint_insert(2)
        insertE singletonD A4RS_def insert_iff singleton_iff by metis
    then have "m = A4complement l" using 3 by auto
    then show ?thesis .
  next
    case rs
    then have 3: "A4complement l = A4PQ" using A4complement assms
    by (simp add: A4PQ_def A4PR_def A4PS_def A4QS_def A4RS_def A4QR_def doubleton_eq_iff)
    then have "l \<inter> A4PQ = {}" using 2 assms by auto 
    then have "m = A4PQ" using what assms rs A4Lines_def A4PQ_def A4PR_def A4PS_def A4QS_def A4QR_def A4PQ_def disjoint_insert(2)
        insertE singletonD A4RS_def insert_iff singleton_iff by metis
    then have "m = A4complement l" using 3 by auto
    then show ?thesis .
  qed
qed
text \<open>\Done \Done\<close>

theorem A4affine_plane: 
  "affine_plane A4Points A4Lines A4incid A4join A4find_parallel"
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
    assume h3: "affine_plane_data.parallel A4Points A4Lines A4incid m l"
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
      have q: "A4incid T l \<Longrightarrow> T \<in> A4Points" for T using A4Points_def a4pt.exhaust by blast
      have h7: "\<not> (\<exists> T. A4incid T l \<and> A4incid T m)" using h6 by (metis (full_types) A4Points_def a4pt.exhaust insertCI)  
      from h7 have 8: "l \<inter> m = {}" by (simp add: disjoint_iff h5)
      show ?thesis using 8 fpp  by (metis A4find_parallel.simps \<open>l \<in> A4Lines\<close> \<open>m \<in> A4Lines\<close> f2c h1 h2 h7 inf_commute)     
    qed
  qed
next
  show " \<exists>P Q R. P \<in> A4Points \<and> Q \<in> A4Points \<and> R \<in> A4Points \<and> P \<noteq> Q \<and> P \<noteq> R
    \<and> Q \<noteq> R \<and> \<not> affine_plane_data.collinear A4Points A4Lines A4incid P Q R" 
    using A4affine_plane_a3 by blast
qed

text \<open>\jfh\<close>
interpretation A4: affine_plane A4Points A4Lines A4incid  A4join A4find_parallel
  using A4affine_plane by auto
text \<open>\done\<close>

(* ======================Switch to talking about A2, real affine 2-space =================*)
(* Team A2 = Jackson and Hadi *)

text\<open>\spike Now we move on to showing that the real affine plane is in fact an affine plane. 
Everything related to this plane has the prefix 'a2' or 'A2'.\done\<close>
datatype a2pt = A2Point "real" "real"
datatype a2ln = A2Ordinary "real" "real" | A2Vertical "real"

definition A2Points::"a2pt set"
  where "A2Points \<equiv> (UNIV::a2pt set)"

definition A2Lines::"a2ln set"
  where "A2Lines \<equiv> (UNIV::a2ln set)"

text "Ordinary m b represents the line y = mx+b; Vertical xo is the line x = xo. With this in 
mind, we define the  `incid' operation for this purported plane, using cases for the definition."

fun a2incid :: "a2pt \<Rightarrow> a2ln \<Rightarrow> bool" where
"a2incid (A2Point x y) (A2Ordinary m b) = (y = m*x + b)" |
"a2incid (A2Point x y) (A2Vertical xi) = (x = xi)"

definition a2parallel:: "a2ln  \<Rightarrow> a2ln \<Rightarrow> bool" (infix "a2||" 50)
  where "l a2|| m \<longleftrightarrow> (l = m \<or> (\<forall>P. (\<not> a2incid P l) \<or> (\<not> a2incid P m)))"

text \<open>To make this work, I need to provide a join and find_parallel function\<close>
fun a2join :: "a2pt \<Rightarrow> a2pt \<Rightarrow> a2ln" where
"a2join (A2Point x1 y1) (A2Point x2 y2) = (if ((x1 = x2)  \<and> (y1 = y2)) then undefined else if (x1 = x2) then A2Vertical(x1) else 
(A2Ordinary ((y2 - y1)/(x2-x1)) (y1 - x1* (y2 - y1)/(x2-x1))))"

fun a2find_parallel::"a2ln \<Rightarrow> a2pt \<Rightarrow> a2ln" where
"a2find_parallel (A2Ordinary m b) (A2Point x y) = (A2Ordinary m (y-m*x))" |
"a2find_parallel (A2Vertical xi) (A2Point x y) = (A2Vertical x)"

text \<open>\hadi\<close>
lemma ord_not_vert_pencils:
  fixes l k::a2ln
  fixes m b x::real
  assumes "l \<in> A2Lines" and "k \<in> A2Lines"
  assumes "l = A2Ordinary m b" and "k = A2Vertical x"
  shows "(affine_plane_data.line_pencil A2Points A2Lines a2incid l) 
    \<noteq> (affine_plane_data.line_pencil A2Points A2Lines a2incid k)" 
  using assms a2incid.simps unfolding affine_plane_data.line_pencil_def 
    affine_plane_data.parallel_def A2Points_def by blast

lemma ord_pencil_slopes:
  fixes l k::a2ln
  fixes m b::real
  assumes "l \<in> A2Lines" and "k \<in> A2Lines"
  assumes "l = A2Ordinary m b"
  assumes "k \<in> (affine_plane_data.line_pencil A2Points A2Lines a2incid l)"
  shows "\<exists>c::real. k = A2Ordinary m c"
proof (cases "l = k")
  case True
  then show ?thesis using assms by auto
next
  case lneqk: False
  have lpark: "l a2|| k" using assms affine_plane_data.parallel_def A2Points_def 
    a2parallel_def affine_plane_data.line_pencil_def mem_Collect_eq UNIV_I by metis
  show ?thesis
  proof (rule ccontr)
    assume cd: "\<nexists>c::real. k = A2Ordinary m c"
    show False
    proof (cases k)
      case ordk: (A2Ordinary m' b')
      let ?x = "(b' - b)/(m - m')" let ?y = "m * ((b' - b)/(m - m')) + b"
      have "a2incid (A2Point ?x ?y) k" using cd ordk a2incid.simps(1)
        eq_divide_eq left_diff_distrib mult.commute by (smt (verit))
      then show ?thesis using assms lneqk lpark a2parallel_def by simp
    next
      case (A2Vertical _)
      then show ?thesis using assms lpark a2incid.simps a2parallel_def by blast
    qed
  qed
qed

lemma ord_slopes_pencil:
  fixes l k::a2ln
  fixes m b c::real
  assumes "l \<in> A2Lines" and "k \<in> A2Lines"
  assumes "l = A2Ordinary m b"
  assumes "k = A2Ordinary m c"
  shows "k \<in> (affine_plane_data.line_pencil A2Points A2Lines a2incid l)"
proof (cases "l = k")
  case True
  then show ?thesis using assms unfolding affine_plane_data.line_pencil_def
    affine_plane_data.parallel_def by simp
next
  case lneqk: False
  have lpark: "k a2|| l" using assms a2incid.simps(1) a2pt.exhaust 
    a2parallel_def add_diff_cancel_left' by metis
  then show ?thesis using assms mem_Collect_eq affine_plane_data.parallel_def 
    unfolding a2parallel_def affine_plane_data.line_pencil_def by metis
qed
text \<open>\done\<close>

text \<open>\hadi\<close>

text \<open>\done\<close>

text\<open>Now we'll write some small lemmas, basically establishing the three axioms.\<close>

text\<open>
A note about naming: Everything related to real-affine-2-space will be written with a prefix
``A2''. When we want to state axiom 3 for A2, we'll write ``A2\_a3''. Sometimes we'll need some preliminary
results, and we'll append an ``a'' or ``b'' or ``c'', etc., before stating the main result.  \<close>

theorem A2_a1a1: 
  fixes P::a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2join P Q \<in> A2Lines"
  using A2Lines_def by auto

theorem A2_a1a2: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2incid P (a2join P Q)"
proof -
  obtain x1 y1 x2 y2 where "P = A2Point x1 y1 \<and> Q = A2Point x2 y2" 
    using a2pt.exhaust by metis
  then show ?thesis using assms by auto
qed

text \<open>\hadi \jackson\<close>
theorem A2_a1a3: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2incid Q (a2join P Q)"
proof -
  obtain x1 y1 x2 y2 where xydef: "P = A2Point x1 y1 \<and> Q = A2Point x2 y2" 
    using a2pt.exhaust by meson
  consider (vert) "x1 = x2" | (ord) "x1 \<noteq> x2" by auto
  then show ?thesis
  proof (cases)
    case vert
    then show ?thesis using xydef assms by auto
  next
    case ord
    then have pqjoin: "(a2join P Q) = A2Ordinary ((y2 - y1)/(x2 - x1)) 
      (y1 - x1* (y2 - y1)/(x2 - x1))" using xydef by auto
    have "y2 - y1 = (y2 - y1)*((x2 - x1)/(x2 - x1))" using ord by auto
    then have "y2 = ((y2 - y1)/(x2 - x1))*x2 
      + (y1 - x1* (y2 - y1)/(x2 - x1))" by argo
    then show ?thesis using pqjoin xydef by auto
  qed
qed
text \<open>\done\<close>

text\<open>\spike It might be easier to prove the lemma above if you first show that a2join P Q = a2join Q P. Then 
again, that might also be harder. \<close>

text \<open>\hadi \jackson\<close>
theorem A2_a1a: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2join P Q \<in> A2Lines" and "a2incid P (a2join P Q)" 
    and "a2incid Q (a2join P Q)"
  using assms A2_a1a1 A2_a1a2 A2_a1a3 by auto
text \<open>\done\<close>

text\<open>\spike For this next theorem, it might make sense to phrase it as "P notequal Q lets us 
derive a unique line l such that..."
but that would require proving the existence of l (which we just did in the previous lemma) and
then proving that it's unique. Instead, we can just say that if l and m both contain the 
distinct points P and Q, then l must equal m. From this, and the previous lemma, we can then 
conclude that axiom 1 is true (which we'll do in a final theorem). 

This is arguably the ugliest theorem in the bunch, because it involves four cases (one each for 
l and m being ordinary or vertical). Once again, we start by providing names for the constructor
arguments for P and Q:
 \seiji\<close>

text \<open>\hadi,\jackson\<close>
lemma A2_a1b: 
  fixes P::a2pt
  fixes Q
  fixes l
  assumes pq: "P \<noteq> Q"
  assumes pl: "a2incid P l"
  assumes ql: "a2incid Q l"
  shows "l = a2join P Q"
proof -
  obtain x1 y1 where p_coords: "P = A2Point x1 y1" 
    using assms a2pt.exhaust by auto 
  obtain x2 y2 where q_coords: "Q = A2Point x2 y2" 
    using assms a2pt.exhaust by auto
  consider (vert) "x1 = x2" | (ord) "x1 \<noteq> x2" by auto
  then show ?thesis
  proof (cases)
    case vert
    then show ?thesis using assms a2incid.elims p_coords q_coords by fastforce
  next
    case ord
    let ?m2 = "(y2 - y1)/(x2 - x1)"
    let ?b2 = "y1 - x1*(y2 - y1)/(x2 - x1)" 
    obtain m b where l_ord: "l = A2Ordinary m b" using assms a2incid.simps 
      a2ln.exhaust ord p_coords q_coords by metis
    have join_ord: "a2join P Q = A2Ordinary ?m2 ?b2" 
      using assms ord p_coords q_coords by auto
    have "l = A2Ordinary ?m2 ?b2" using assms ord eq_divide_eq l_ord 
      p_coords q_coords right_diff_distrib by fastforce
    then show ?thesis using join_ord by auto
  qed
qed
text \<open>\done\<close>  

text \<open>\done Whew! We've proved axiom 1 for the real affine plane. On to Axiom 2. This one's 
a little trickier because we're proving a conjunction.\<close>

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
  using assms A2Lines_def by auto

(*
fun a2find_parallel::"a2ln \<Rightarrow> a2pt \<Rightarrow> a2ln" where
"a2find_parallel (A2Ordinary m b) (A2Point x y)  = (A2Ordinary m (y-m*x))" |
"a2find_parallel  (A2Vertical xi) (A2Point x y) = (A2Vertical x)"
*)

text \<open>\hadi \jackson\<close>
lemma A2_a2b:
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> (a2incid P l)"
  assumes "P \<in> A2Points" and "l \<in> A2Lines" (* vacuous here, but parallel to the A4 case *)
  shows   "(a2find_parallel l P) a2|| l"
proof (cases l)
  case Ol: (A2Ordinary m b)
  obtain x y where "P = A2Point x y" using a2pt.exhaust by auto
  then have "a2find_parallel l P = A2Ordinary m (y - m*x)" using Ol assms by auto
  then show ?thesis using Ol a2incid.elims a2parallel_def by fastforce
next
  case (A2Vertical x)
  then show ?thesis using a2find_parallel.simps a2incid.simps
    a2parallel_def a2pt.exhaust by metis
qed
text \<open>\done\<close>

text \<open>\hadi,\jackson\<close>
lemma A2_a2c:
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> (a2incid P l)"
  assumes "P \<in> A2Points" and "l \<in> A2Lines" (* vacuous here, but parallel to the A4 case *)
  shows  "a2incid P (a2find_parallel l P)" 
proof (cases l)
  case Ol: (A2Ordinary m b)
  obtain x y where p_coords: "P = A2Point x y" using a2pt.exhaust by auto
  then have "a2find_parallel l P = A2Ordinary m (y - m*x)" 
    using assms Ol by auto
  then show ?thesis using p_coords by auto
next
  case (A2Vertical x)
  then show ?thesis using a2incid.elims(3) by fastforce
qed 
text \<open>\done\<close>

text \<open>\hadi,\jackson\<close>
lemma a2parallel_caseV:
  fixes l and k and x0 and m and b
  assumes "l = A2Vertical x0"
  assumes "k = A2Ordinary m b"
  shows "a2incid (A2Point x0 (m*x0 + b)) l" and "a2incid (A2Point x0 (m*x0 + b)) k"
  and "\<not> l a2|| k"
proof -
  show 0: "a2incid (A2Point x0 (m*x0 + b)) l" 
    and 1: "a2incid (A2Point x0 (m*x0 + b)) k" using assms by auto
  show "\<not> l a2|| k" using 0 1 assms a2parallel_def by blast
qed
text \<open>\done\<close>

text \<open>\hadi,\jackson\<close>
lemma a2parallel_caseOa:
  fixes l and k and m1 and b1 and m2 and b2
  assumes "m1 \<noteq> m2"
  assumes "l = A2Ordinary m1 b1"
  assumes "k = A2Ordinary m2 b2"
  shows "a2incid (A2Point (-(b1 - b2)/(m1-m2)) (m1* (-(b1 - b2)/(m1-m2)) + b1)) l" and 
   "a2incid (A2Point (-(b1 - b2)/(m1-m2)) (m1* (-(b1 - b2)/(m1-m2)) + b1)) k" 
proof -
  show 0: "a2incid (A2Point (-(b1 - b2)/(m1-m2)) 
    (m1* (-(b1 - b2)/(m1-m2)) + b1)) l" using assms by auto
  have "m2*((-(b1 - b2)/(m1-m2))) + b2 = m2*((-b1+b2)/(m1-m2))+(-b1+b2)+b1" 
    by argo
  then have "m2*((-(b1 - b2)/(m1-m2))) + b2 
    = (-b1+b2)*((m2/(m1-m2))+1)+b1" by argo
  then have "m2*((-(b1 - b2)/(m1-m2))) + b2 
    = (-b1+b2)*((m2/(m1-m2))+((m1-m2)/(m1-m2)))+b1" using assms by auto
  then have "m2*((-(b1 - b2)/(m1-m2))) + b2 
    = (-b1+b2)*((m1/(m1-m2)))+b1" by argo
  then show 
    "a2incid (A2Point (-(b1 - b2)/(m1-m2)) (m1* (-(b1 - b2)/(m1-m2)) + b1)) k"  
    using assms by auto
qed
text \<open>\done\<close>

text \<open>\hadi,\jackson\<close>
lemma a2parallel_caseO:
  fixes l and k and x0 and m1 and b1 and m2 and b2
  assumes "m1 \<noteq> m2"
  assumes "l = A2Ordinary m1 b1"
  assumes "k = A2Ordinary m2 b2"
  shows "\<not> k a2|| l"
  using assms a2parallel_caseOa a2ln.inject a2parallel_def by metis
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma a2parallel_caseO2:
  fixes l and k and x0 and m1 and b1 and m2 and b2
  assumes "m1 = m2"
  assumes "l = A2Ordinary m1 b1"
  assumes "k = A2Ordinary m2 b2"
  shows "k a2|| l"
  using assms a2incid.elims(2) a2parallel_def by fastforce
text \<open>\done\<close>

text \<open>\hadi \jackson\<close>
lemma A2_a2d:
  fixes P and l and k 
  assumes "P \<in> A2Points" and  "l \<in> A2Lines" and  "k \<in> A2Lines" and "k a2|| l" and "a2incid P k"
  shows "k = a2find_parallel l P"
proof (rule ccontr)
  assume cd: "\<not> (k = a2find_parallel l P)"
  show False
  proof (cases k)
    case Ok: (A2Ordinary m1 b1)
    then show False
    proof (cases l)
      case Ol: (A2Ordinary m2 b2)
      then have "m1 \<noteq> m2" using assms Ol Ok cd a2incid.elims(2) by force
      then show False using assms Ok Ol a2parallel_caseO by auto
    next
      case (A2Vertical x)
      then show ?thesis using assms Ok a2incid.simps a2parallel_def by blast
    qed
  next
    case Vk: (A2Vertical xk)
    then show False
    proof (cases l)
      case (A2Ordinary m b)
      then show ?thesis using assms Vk a2incid.simps a2parallel_def by blast
    next
      case Vl: (A2Vertical xl)
      obtain x y where p_coords: "P = A2Point x y" using a2pt.exhaust by auto
      then have "x = xk" using assms Vk by auto
      then show False using Vk Vl cd p_coords by auto
    qed
  qed
qed
text \<open>\done\<close>

text \<open>\hadi,\jackson\<close>
lemma A2_a2abc:
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> (a2incid P l)"
  assumes "P \<in> A2Points" and "l \<in> A2Lines" 
  shows  
    "a2find_parallel l P \<in> A2Lines" and   
    "(a2find_parallel l P) a2|| l" and 
    "a2incid P  (a2find_parallel l P)"  
  using assms A2_a2a A2_a2b A2_a2c by auto
text \<open>\done\<close>


text\<open>\hadi,\jackson\<close>
lemma A2_a3:
  shows  "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R 
    \<and> (\<nexists> m. a2incid P m \<and> a2incid Q m \<and> a2incid R m)"
proof -
  let ?r = "A2Point 1 0" let ?t = "A2Point 0 1" let ?z = "A2Point 0 0"
  have dist: "?r \<noteq> ?t \<and> ?r \<noteq> ?z \<and> ?t \<noteq> ?z" by auto
  have "\<nexists>m. a2incid ?r m \<and> a2incid ?t m \<and> a2incid ?z m"
  proof (rule ccontr)
    assume cd: "\<not> (\<nexists>m. a2incid ?r m \<and> a2incid ?t m \<and> a2incid ?z m)"
    show False
    proof -
      obtain m where mdef: "a2incid ?r m \<and> a2incid ?t m \<and> a2incid ?z m" 
        using cd by auto
      then have mj: "m = a2join ?r ?t" using A2_a1b dist by blast
      have "\<not> (a2incid ?z (a2join ?r ?t))" by auto
      then show False using mdef mj by auto
    qed
  qed
  then show ?thesis using dist by blast
qed
text\<open>\done\<close>


text\<open> \spike At this point we've established that the Cartesian Plane satisfies Cartesian 
versions of the three axioms, etc., but it'd be nice to be able to say that as
a *structure*, it matches the Isabelle "locale" that we defined.
\<close>

text \<open>\hadi,\jackson\<close>
theorem A2_affine: "affine_plane A2Points A2Lines a2incid a2join a2find_parallel"
proof (unfold_locales)
  show "\<lbrakk>P \<noteq> Q; P \<in> A2Points; Q \<in> A2Points\<rbrakk> 
    \<Longrightarrow> a2join P Q \<in> A2Lines \<and> a2incid P (a2join P Q) \<and> a2incid Q (a2join P Q)" 
    for P Q using A2_a1a by auto
  show "\<lbrakk>P \<noteq> Q; P \<in> A2Points; Q \<in> A2Points; a2incid P m; a2incid Q m\<rbrakk> 
    \<Longrightarrow> m = a2join P Q" for P Q m using A2_a1b by auto
  show "\<lbrakk>P \<in> A2Points; l \<in> A2Lines\<rbrakk> \<Longrightarrow> a2find_parallel l P \<in> A2Lines" for P l
    using A2_a2a A2Lines_def by auto
  show "\<lbrakk>P \<in> A2Points; l \<in> A2Lines\<rbrakk> \<Longrightarrow> affine_plane_data.parallel 
    A2Points A2Lines a2incid (a2find_parallel l P) l" for P l
  proof -
    have "\<lbrakk>Q \<in> A2Points; k \<in> A2Lines\<rbrakk> \<Longrightarrow> (a2find_parallel k Q) a2|| k" 
      for Q k using A2_a2b A2_a2d a2parallel_def by metis
    then show ?thesis by (simp add: A2Lines_def A2Points_def a2parallel_def
      affine_plane_data.parallel_def)
  qed
  show "\<lbrakk>P \<in> A2Points; l \<in> A2Lines\<rbrakk> \<Longrightarrow> a2incid P (a2find_parallel l P)" 
    for P l using A2_a2c A2_a2d A2Lines_def a2parallel_def by metis
  show "\<lbrakk>P \<in> A2Points; l \<in> A2Lines; m \<in> A2Lines; affine_plane_data.parallel 
    A2Points A2Lines a2incid m l; a2incid P m\<rbrakk> \<Longrightarrow> m = a2find_parallel l P" 
    for P l m by (simp add: A2_a2d A2Points_def 
    a2parallel_def affine_plane_data.parallel_def)
  show "\<exists>P Q R. P \<in> A2Points \<and> Q \<in> A2Points \<and> R \<in> A2Points 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (affine_plane_data.collinear 
    A2Points A2Lines a2incid P Q R)" using A2_a3 
    unfolding affine_plane_data.collinear_def A2Points_def A2Lines_def by auto
qed
text \<open>\done\<close>
text  \<open> 
\spike Let's go ahead and make an interpretation so that we can use "A2" in the rest of the book 
to refer to this affine plane\<close>
interpretation A2: affine_plane A2Points A2Lines a2incid  a2join a2find_parallel 
  by (rule A2_affine)

text \<open>\done\<close>
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

locale projective_plane = projective_plane_data Points Lines incid
  for
     Points :: "'p set" and
     Lines :: "'l set" and
     incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"  (infix "\<lhd>" 60)  + 
assumes
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k. k \<in> Lines \<and> P \<lhd> k \<and> Q \<lhd> k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists>P. (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = {P. (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
begin

(*Uncommented and fixed by Nick and George for use in 4-4:*)
definition (in projective_plane_data) meet::"'l \<Rightarrow> 'l \<Rightarrow> 'p" (infix "." 60) where
"meet n k = (if (n \<in> Lines \<and> k \<in> Lines \<and> n \<noteq> k) then THE P . P \<in> Points \<and> P \<lhd> n \<and> P \<lhd> k else undefined)"

definition (in projective_plane_data) join::"'p \<Rightarrow> 'p \<Rightarrow> 'l" (infix "\<^bold>" 60) where
"join P Q = (if (P \<in> Points \<and> Q \<in> Points \<and> P \<noteq> Q) then THE k. k \<in> Lines \<and> P \<lhd> k \<and> Q \<lhd> k else undefined)"

thm p1
thm p1[of P Q]
thm theI'
thm theI'[OF p1]
thm theI'[OF p1[of P Q]]

lemma join_properties1:
  "\<lbrakk>P \<in> Points; Q \<in> Points; P \<noteq> Q\<rbrakk> \<Longrightarrow> P \<lhd> join P Q  \<and> Q \<lhd> join P Q \<and> join P Q \<in> Lines"
  unfolding join_def using theI' [OF p1[of P Q]] by auto

lemma join_properties2:
  "\<lbrakk>P \<in> Points; Q \<in> Points; P \<noteq> Q; k \<in> Lines\<rbrakk> \<Longrightarrow> P \<lhd> k  \<Longrightarrow> Q \<lhd> k \<Longrightarrow> k =  join P Q"
  using join_properties1 p1 by blast

lemma unique_meet:
  "\<lbrakk>k \<in> Lines; n \<in> Lines; P \<in> Points; Q \<in> Points; k \<noteq> n; P \<lhd> k; P \<lhd> n; Q \<lhd> k; Q \<lhd> n\<rbrakk> \<Longrightarrow> P = Q"
  using p1 by auto

lemma s:
   "\<lbrakk>k \<in> Lines; n \<in> Lines; k \<noteq> n\<rbrakk> \<Longrightarrow> \<exists>!P. (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" 
  using p2 unique_meet by blast

lemma meet_properties2:
  "\<lbrakk>k \<in> Lines; n \<in> Lines; k \<noteq> n\<rbrakk> \<Longrightarrow> meet n k \<in> Points \<and> meet n k \<lhd> k \<and> meet n k \<lhd> n "
  using s theI meet_def by (smt (verit))
end

text \<open>\hadi\<close>
lemma (in projective_plane) pcollinear_degeneracy:
  fixes P Q R::'p
  assumes "P \<in> Points" and "Q \<in> Points" and "R \<in> Points"
  assumes "P = Q \<or> P = R \<or> Q = R"
  shows "pcollinear P Q R" 
  using assms p1 p3 unfolding pcollinear_def by metis
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in projective_plane) pcollinear_commute:
  fixes P Q R::'p
  assumes "P \<in> Points" and "Q \<in> Points" and "R \<in> Points"
  assumes"P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R"
  shows "(pcollinear P Q R) \<Longrightarrow> (pcollinear Q P R)"
  using assms pcollinear_def by auto
text \<open>\done\<close>

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
lie on the line at iparnfinity of $S,$ hence they lie on only one line of $S.$

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

text \<open>\hadi\<close>
lemma AB:
  fixes Points::"'p set" 
  fixes Lines::"'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"  (infix "\<lhd>" 60) 
  fixes join::"'p \<Rightarrow> 'p \<Rightarrow> 'l" 
  fixes find_parallel::"'l \<Rightarrow> 'p \<Rightarrow> 'l"
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines "lp \<equiv> affine_plane_data.line_pencil Points Lines incid"
  assumes "P \<in> Points"
  defines pp: "pPoints \<equiv> {OrdinaryP R | R. (R \<in> Points)} 
    \<union> {Ideal s | s k. (k \<in> Lines) \<and> s = lp k}"
  assumes "Ideal t \<in> pPoints" 
  shows "\<exists>!k \<in> Lines. k \<in> t \<and> P \<lhd> k"  
proof -
  obtain k where kdef: "k \<in> Lines \<and> t = lp k" using assms by auto
  obtain l where ldef: "l \<in> Lines \<and> P \<lhd> l
    \<and> affine_plane_data.parallel Points Lines incid l k" using assms ap kdef
    affine_plane.a2b [of _ _ _ _ _ P k] affine_plane.a2c [of _ _ _ _ _ P k] 
    affine_plane_data.parallel_def [of _ _ _ _ k] by blast
  have "l \<in> t" using kdef ldef affine_plane_data.line_pencil_def lp_def 
    by fastforce
  then show ?thesis using assms kdef ldef mem_Collect_eq
    affine_plane.a2d [of Points Lines incid join find_parallel P k] 
    affine_plane_data.line_pencil_def by metis
qed
text \<open>\done\<close>

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

text \<open>\Jackson\<close>
lemma Ap2:
  fixes Points Lines join find_parallel
  fixes incid (infix "\<lhd>" 60)
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P. (P \<in> Points)} \<union> {Ideal t | k t. 
    ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k))}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n. (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes \<open>pincid = mprojectivize (incid)\<close>
  shows "\<lbrakk>k \<in> pLines; n \<in> pLines\<rbrakk> \<Longrightarrow> \<exists>P. (P \<in> pPoints \<and> P p\<lhd> k \<and> P p\<lhd> n)"
proof -
  fix k n
  assume assms1: "k \<in> pLines" and
         assms2: "n \<in> pLines"
  show "\<exists> P . (P \<in> pPoints \<and> P p\<lhd> k \<and> P p\<lhd> n)"
  proof (cases k)
    case k_ord: (OrdinaryL ko)
    then show ?thesis 
    proof(cases n)
      case n_ord: (OrdinaryL no) (*ord, ord*)
      have 0: "ko \<in> Lines" using assms1 k_ord pLdef by auto
      have 1: "no \<in> Lines" using assms2 n_ord pLdef by auto
      consider 
        (parallel) "affine_plane_data.parallel Points Lines incid ko no"
        | (not_parallel) "\<not>(affine_plane_data.parallel Points Lines incid ko no)" by blast
      then show ?thesis
      proof cases
        case parallel
          obtain t where 2: "t = affine_plane_data.line_pencil Points Lines (incid) ko" by auto
          have 3: "Ideal t \<in> pPoints" using assms 0 2 by blast
          have 4: "Ideal t p\<lhd> k" using 3 2 0 assms by (simp add: affine_plane_data.line_pencil_def 
            affine_plane_data.parallel_reflexive k_ord)
          have 5: "no \<in> t" using parallel affine_plane_data.line_pencil_def 
            affine_plane_data.parallel_symmetric mem_Collect_eq 2 by metis
          have 6: "Ideal t p\<lhd> n" by (simp add: 5 assms(4) n_ord)
          show ?thesis using 3 4 6 by auto
        next 
          case not_parallel
          have 2: "\<not>((ko \<in> Lines) \<and> (no \<in> Lines) \<and> ((ko = no) 
            \<or> ((\<not> (\<exists> P. P \<in> Points \<and> P \<lhd> ko \<and> P \<lhd> no)))))"
            using 0 1 not_parallel by (simp add: affine_plane_data.parallel_def)
          have 3: "\<exists> P. P \<in> Points \<and> P \<lhd> ko \<and> P \<lhd> no" using 0 1 2 by auto
          obtain P where 4: "P \<in> Points \<and> P \<lhd> ko \<and> P \<lhd> no" using 3 by auto
          show ?thesis using 4 assms(4) k_ord n_ord pPdef by auto
        qed
    next
      case Infty (*ord, inf*)
       have 0: "ko \<in> Lines" using assms1 k_ord pLdef by auto
       obtain t where 1: "t = affine_plane_data.line_pencil Points Lines (incid) ko" by auto
       have 2: "Ideal t \<in> pPoints" using assms 0 1 by auto
       have 3: "Ideal t p\<lhd> k" using 2 1 0 assms by (simp add: affine_plane_data.line_pencil_def 
         affine_plane_data.parallel_reflexive k_ord)
       show ?thesis using assms(4) Infty 2 3 by auto
     qed
  next
    case Infty
    then show ?thesis 
    proof (cases n)
      case n_ord: (OrdinaryL no) (*inf, ord*)
       have 0: "no \<in> Lines" using assms2 n_ord pLdef by auto
       obtain t where 1: "t = affine_plane_data.line_pencil Points Lines (incid) no" by auto
       have 2: "Ideal t \<in> pPoints" using assms 0 1 by auto
       have 3: "Ideal t p\<lhd> n" using 2 1 0 assms by (simp add: affine_plane_data.line_pencil_def 
         affine_plane_data.parallel_reflexive n_ord)
       show ?thesis using assms(4) Infty 2 3 by auto
    next
      case Infty1: Infty (*inf, inf*)
      obtain P Q where 0: "P \<in> Points \<and> Q \<in> Points \<and> P \<noteq> Q" using affine_plane.a3 ap by blast
      obtain l where 1: "l = (join P Q) \<and> l \<in> Lines" using 0 affine_plane.a1a ap by metis
      have 2: "l \<in> Lines" using 1 by auto
      obtain t where 3: "t = affine_plane_data.line_pencil Points Lines (incid) l" by auto
      have 4: "Ideal t \<in> pPoints" using assms 0 1 3 by auto
      have 5: "Ideal t p\<lhd> n" by (simp add: Infty1 assms(4))
      have 6: "Ideal t p\<lhd> k" using 5 Infty Infty1 by auto
      show ?thesis using 4 5 6 by auto
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
  obtain P Q R where pqr: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q 
    \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (affine_plane_data.collinear Points Lines incid P Q R)"
    using ap affine_plane.a3 by blast
  let ?pP = "OrdinaryP P" let ?pQ = "OrdinaryP Q" let ?pR = "OrdinaryP R"
  have ppqrpts:"?pP \<in> pPoints \<and> ?pQ \<in> pPoints \<and> ?pR \<in> pPoints" 
    using pqr ap pPdef by blast
  have ppqrdist: "?pP \<noteq> ?pQ \<and> ?pP \<noteq> ?pR \<and> ?pQ \<noteq> ?pR" using pqr by blast
  have ppqrnc: "\<not> (projective_plane_data.pcollinear pPoints pLines (pincid) 
    ?pP ?pQ ?pR)" using pqr assms affine_plane.a1b ppqrpts
    affine_plane.parallel_to_collinear projective_plane_data.pcollinear_def
    by (smt (verit, ccfv_threshold) mprojectivize.elims(2) projLine.inject
      projPoint.distinct(1) projPoint.inject(1))
  show ?thesis using ppqrpts ppqrdist ppqrnc by auto
qed

lemma Ap41: 
  fixes k n
  assumes ap: "affine_plane Points Lines incid join find_parallel" 
  assumes "k \<in> Lines" and "n \<in> Lines"
  assumes same_pencil: "(affine_plane_data.line_pencil Points Lines (incid) k) =
                      (affine_plane_data.line_pencil Points Lines (incid) n)"
  shows "(affine_plane_data.parallel Points Lines incid k n)"
proof -
  have 0: "k\<in>(affine_plane_data.line_pencil Points Lines (incid) k)" using assms affine_plane.parallel_refl affine_plane_data.line_pencil_def mem_Collect_eq
      reflp_on_def by metis
  have 1: "n\<in>(affine_plane_data.line_pencil Points Lines (incid) k)" using assms 0 affine_plane.parallel_refl affine_plane_data.line_pencil_def mem_Collect_eq
      reflp_on_def by metis
  show ?thesis using 1 0 assms affine_plane_data.line_pencil_def by force
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
  fixes k U
  assumes useful_defs: "k \<in> pLines\<and> U = { P . (P \<in> pPoints \<and> P p\<lhd> k)}"
  shows " \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct[Q,R,S]"

 (* shows "\<lbrakk>k \<in> pLines; U = { P . (P \<in> pPoints \<and> P p\<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct[Q,R,S]" *)
  
text\<open>idea: Each line of A has at least two points; its completion also contains an ideal point. And the line at infty contains AB, BC, AC where ABC are three 
noncollinear points of A.\<close>
proof (cases k)
  case o1: (OrdinaryL ko)
  then show ?thesis
  proof -
    have 0: "ko\<in>Lines" using assms o1 by auto
    then obtain R Q where rq_info: "R\<in>Points\<and>Q\<in>Points\<and>R\<lhd>ko\<and>Q\<lhd>ko\<and>R\<noteq>Q" using affine_plane.contained_points assms  by (metis (no_types, opaque_lifting))
    then have 1: "(OrdinaryP R)\<in>pPoints \<and>(OrdinaryP Q)\<in>pPoints" using pPdef by auto
    then have 2: "(OrdinaryP R)\<in>U\<and>(OrdinaryP Q)\<in>U" using pPdef assms 0 o1 rq_info by auto
    then have 3: "(OrdinaryP R)\<noteq>(OrdinaryP Q)" using rq_info by auto
    obtain kpencil where kpencil_info: "kpencil=affine_plane_data.line_pencil Points Lines (incid) ko" by auto
    then have 4: "Ideal kpencil\<in>pPoints" using 0 pPdef by blast
    then have 5: "(Ideal kpencil) p\<lhd> k" using kpencil_info "0" affine_plane.parallel_refl affine_plane_data.line_pencil_def ap assms(4) mem_Collect_eq
        mprojectivize.simps(2) o1 reflp_on_def by metis
    then have 6: "(Ideal kpencil)\<in>U" using kpencil_info 4 assms by blast
    have 7: "(OrdinaryP R)\<noteq>(Ideal kpencil)\<and>(OrdinaryP Q)\<noteq>(Ideal kpencil)" using kpencil_info rq_info assms by auto
    then have 8: "distinct[(OrdinaryP R),(OrdinaryP Q),(Ideal kpencil)]" using 3 by auto
    then show ?thesis using 6 2 3 by auto
  qed
  next
  case Infty
  then show ?thesis
  proof -
   obtain A B C where 0: "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> \<not> (affine_plane_data.collinear Points Lines incid A B C)" using assms affine_plane.a3 by blast
   obtain ab bc ac where 1: "ab\<in>Lines\<and>bc\<in>Lines\<and>ac\<in>Lines\<and>ab=(join A B)\<and>bc=(join B C)\<and>ac=(join A C)" using assms 0 by (simp add: affine_plane_def)
   obtain abpencil bcpencil acpencil where 2: "abpencil=affine_plane_data.line_pencil Points Lines (incid) ab\<and>bcpencil=affine_plane_data.line_pencil Points Lines (incid) bc\<and>acpencil=affine_plane_data.line_pencil Points Lines (incid) ac" by auto
   have 3: "ab\<in>abpencil\<and>bc\<in>bcpencil\<and>ac\<in>acpencil" using 1 0 ap 2 mem_Collect_eq affine_plane_data.line_pencil_def affine_plane_data.parallel_def by metis
   have 4: "A\<lhd>ab\<and>A\<lhd>ac\<and>B\<lhd>bc\<and>B\<lhd>ab\<and>C\<lhd>ac\<and>C\<lhd>bc" using 0 1 assms by (simp add: affine_plane.a1a)
   have nonpar: "\<not>(affine_plane_data.parallel Points Lines (incid) ab bc)\<and>\<not>(affine_plane_data.parallel Points Lines (incid) ab ac)\<and>\<not>(affine_plane_data.parallel Points Lines (incid) bc ac)" using  assms 0 1 4 affine_plane.parallel_to_collinear affine_plane.prop1P2 affine_plane_data.parallelE ap by (metis (lifting))
   have 5: "abpencil\<noteq>acpencil\<and>abpencil\<noteq>bcpencil\<and>bcpencil\<noteq>acpencil" using 0 1 2 3 4 assms affine_plane_data.line_pencil_def mem_Collect_eq nonpar by metis
   have 6: "(Ideal abpencil)\<in>pPoints\<and>(Ideal acpencil)\<in>pPoints\<and>(Ideal bcpencil)\<in>pPoints" using 2 1 pPdef by blast
   have 7: "(Ideal abpencil)\<noteq>(Ideal bcpencil)\<and>(Ideal abpencil)\<noteq>(Ideal acpencil)\<and>(Ideal bcpencil)\<noteq>(Ideal acpencil)" using assms 2 5 6 by auto
   have 8: "distinct[(Ideal abpencil),(Ideal acpencil),(Ideal bcpencil)]" using 7 by auto
   have 9: "(Ideal abpencil) p\<lhd> k\<and>(Ideal acpencil) p\<lhd> k\<and>(Ideal bcpencil) p\<lhd> k" using assms 0 1 2 6 by (simp add: Infty)
   then show ?thesis using 6 7 8 9 useful_defs by auto
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
  shows "(\<exists>k. k \<in> pLines \<and> P p\<lhd> k \<and> Q p\<lhd> k)"
text \<open> \George \<close>
proof (cases P)
  case Ordinary_P: (OrdinaryP x1)
  then show ?thesis
  proof (cases Q)
    case Ordinary_Q: (OrdinaryP y1)
    have xy_diff: "x1 \<noteq> y1" using pq_diff Ordinary_P Ordinary_Q by auto
    (* Show join P Q \in affine_plane_data.lines using a1a
    Show anything in lines must be in pLines
    Show that pincid is induced by incid in a1a *)
    let ?l = "join x1 y1"
    thm emptyE
    have h0: "?l \<in> Lines \<and> incid x1 ?l \<and> incid y1 ?l" using xy_diff affine_plane.a1a Ordinary_P Ordinary_Q ap pPdef pq_pts by fastforce
    then show ?thesis using Ordinary_P Ordinary_Q Un_def assms(4) mem_Collect_eq pLdef by auto
  next
    case Ideal_Q: (Ideal y2)
    obtain k0 where k0_props:
      "k0 \<in> Lines" "y2 = affine_plane_data.line_pencil Points Lines (incid) k0"
      using pq_pts pPdef Ordinary_P Ideal_Q by auto
    obtain m where m_props: "m \<in> Lines" "incid x1 m" "m \<in> affine_plane_data.line_pencil Points Lines (incid) k0"
      using ap by (smt (z3) Ordinary_P
    Un_iff affine_plane.a2c
    affine_plane_data.line_pencil_def
    affine_plane_def
    k0_props(1)
    mem_Collect_eq pPdef
    pq_pts
    projPoint.distinct(1)
    projPoint.inject(1))
    have h0: "OrdinaryL m \<in> pLines" using pLdef m_props(1) by auto
    have h1: "OrdinaryP x1 p\<lhd> OrdinaryL m" using m_props(2) assms(4) mprojectivize.simps by auto
    have h2: "Ideal y2 p\<lhd> OrdinaryL m" using m_props(3) k0_props assms(4)
      by auto
    show ?thesis using Ideal_Q Ordinary_P h0 h1 h2 by auto
  qed
next
  case Ideal_P: (Ideal x2)
  then show ?thesis 
  proof (cases Q)
    case Ordinary_Q: (OrdinaryP y1)
      obtain k0 where k0_props:
        "k0 \<in> Lines" "x2 = affine_plane_data.line_pencil Points Lines (incid) k0"
        using pq_pts pPdef Ideal_P Ordinary_Q by auto
      obtain m where m_props: 
        "m \<in> Lines" "incid y1 m" "m \<in> affine_plane_data.line_pencil Points Lines (incid) k0"
        using ap by (smt (z3) Ordinary_Q
          Un_iff affine_plane.a2c
          affine_plane_data.line_pencil_def
          affine_plane_def
          k0_props(1)
          mem_Collect_eq pPdef
          pq_pts
          projPoint.distinct(1)
          projPoint.inject(1))
      have h0: "OrdinaryL m \<in> pLines" using pLdef m_props(1) by auto
      have h1: "OrdinaryP y1 p\<lhd> OrdinaryL m" 
        using m_props(2) assms(4) mprojectivize.simps by auto
      have h2: "Ideal x2 p\<lhd> OrdinaryL m" 
        using m_props(3) k0_props assms(4) by auto
      show ?thesis using Ideal_P Ordinary_Q h0 h1 h2 by auto
  next
    case Ideal_Q: (Ideal y2)
    (* Any 2 ideal points are on the line at Infinity *)
    have h0: "Infty \<in> pLines" using pLdef by auto
    have h1: "Ideal y2 p\<lhd> Infty" using assms(4) by auto
    have h1: "Ideal x2 p\<lhd> Infty" using assms(4) by auto
    then show ?thesis using Ideal_P Ideal_Q assms(4) h0 by auto
  qed
qed
text \<open> \done \<close>

text \<open>\george\<close>
lemma disjoint_pencils:
  fixes s t k n
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  assumes tdef: "t = affine_plane_data.line_pencil Points Lines (incid) k"
  assumes sdef: "s = affine_plane_data.line_pencil Points Lines (incid) n"
  assumes kn_diff: "\<not> affine_plane_data.parallel Points Lines (incid) k n"
  shows "s \<inter> t = {}"
proof (rule ccontr)
  assume contr_kn_diff: "\<not>(s \<inter> t = {})"
  obtain p where p_in_s_t: "p \<in> (s \<inter> t)" using contr_kn_diff by auto
  have h0: "affine_plane_data.parallel Points Lines (incid) p k" 
    using affine_plane_data.line_pencil_def p_in_s_t tdef by force
  have h1: "affine_plane_data.parallel Points Lines (incid) p n" 
    using affine_plane_data.line_pencil_def p_in_s_t sdef by force
  have h2: "affine_plane_data.parallel Points Lines (incid) k n" 
    using h0 h1 affine_plane.parallel_transitive 
    affine_plane_data.parallel_symmetric by (metis ap)
  show "False" using h2 kn_diff by auto
qed
text \<open>\done\<close>

text \<open>\george,\hadi\<close>
lemma same_pencils:
  fixes s t k n
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  assumes knlines: "k \<in> Lines \<and> n \<in> Lines"
  assumes tdef: "t = affine_plane_data.line_pencil Points Lines (incid) k"
  assumes sdef: "s = affine_plane_data.line_pencil Points Lines (incid) n"
  assumes kn_par: "affine_plane_data.parallel Points Lines (incid) k n"
  shows "s = t" using assms affine_plane.parallel_transitive [of _ Lines]
    affine_plane_data.parallel_symmetric [of _ _ _ k] 
    affine_plane_data.line_pencil_def [of _ Lines] by blast
text \<open>\done\<close>

text \<open>\nick\<close>
lemma two_ideal_is_infinite:
  fixes P Q k
  assumes pq_def: "P = Ideal s \<and> Q = Ideal t"
  assumes pq_diff:"P \<noteq> Q"
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P. (P \<in> Points)} \<union> {Ideal t | k t. 
    ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k))}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n. (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes pm_def: \<open>pincid =  mprojectivize (incid)\<close>
  assumes pPoint: "P \<in> pPoints"
  assumes qPoint: "Q \<in> pPoints"
  assumes k_facts: "k \<in> pLines \<and> P p\<lhd> k \<and> Q p\<lhd> k" 
  shows "k = Infty"
  proof (rule ccontr)
    assume ch: "\<not> k = Infty"
    obtain n where hn: "n \<in> Lines \<and> k = OrdinaryL n" using ch k_facts projLine.exhaust pLdef by auto
    have h1: "n \<in> s \<and> n \<in> t" using pq_def k_facts hn pm_def by auto
    obtain k1 where hk1: "k1 \<in> Lines \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k1)"
      using pPdef pq_def qPoint by blast
    obtain k2 where hk2: "k2 \<in> Lines \<and> (s = affine_plane_data.line_pencil Points Lines (incid) k2)"
      using pPdef pq_def pPoint by blast
    have h2: "affine_plane_data.parallel Points Lines incid n k1" 
      using hk1 affine_plane_data.line_pencil_def h1 by fastforce
    have h3: "affine_plane_data.parallel Points Lines incid n k2" 
      using hk2 affine_plane_data.line_pencil_def h1 by fastforce
    have h4: "affine_plane_data.parallel Points Lines incid k1 k2" 
      using h2 h3 affine_plane.parallel_transitive affine_plane_data.parallel_symmetric ap by metis
    have h5: "P = Q" using h4 ap hk1 hk2 same_pencils pq_def by metis
    show False using h5 pq_diff by auto
  qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma any_ordinary_is_ordinary:
  fixes P k
  assumes p_def: "P = OrdinaryP A"
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P. (P \<in> Points)} \<union> {Ideal t | k t. 
    ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k))}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in> Lines)} \<union> {Infty}"
  defines pm_def: "pincid \<equiv>  mprojectivize (incid)"
  assumes pPoint: "P \<in> pPoints"
  assumes k_facts: "k \<in> pLines \<and> pincid P k" 
  shows "\<exists>n. n \<in> Lines \<and> k = OrdinaryL n" 
  using k_facts pLdef p_def pm_def by auto
(*Nick's old proof
proof (rule ccontr)
  assume cd: "\<not> (\<exists>n. n \<in> Lines \<and> k = OrdinaryL n)"
  show False
  proof -
    have "k = Infty" using cd k_facts pLdef by auto
    then show False using k_facts p_def pm_def by auto
  qed
qed*)
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in affine_plane) in_pencil_parallel:
  fixes l m k
  assumes "l \<in> Lines \<and> m \<in> Lines \<and> k \<in> Lines"
  assumes "l \<in> (line_pencil k) \<and> m \<in> (line_pencil k)"
  shows "l || m" using assms line_pencil_def affine_plane_axioms
    same_pencils mem_Collect_eq by metis
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma Ap1b:
  fixes P Q k n Points Lines incid
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P. (P \<in> Points)} \<union> {Ideal t | k t. 
    ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k))}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n. (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes pm: \<open>pincid =  mprojectivize (incid)\<close>
  assumes pq_pts: "P \<in> pPoints \<and> Q \<in> pPoints"
  assumes pq_diff:"P \<noteq> Q"
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  assumes k_facts: "k \<in> pLines \<and> P p\<lhd> k  \<and> Q p\<lhd> k" 
    and n_facts: "n \<in> pLines \<and> P p\<lhd> n  \<and> Q p\<lhd> n"
  shows "k = n"
proof (cases P)
  case PO: (OrdinaryP A)
  obtain k0 where k0def: "k = OrdinaryL k0 \<and> k0 \<in> Lines" 
    using k_facts pLdef pm PO by auto
  obtain n0 where n0def: "n = OrdinaryL n0 \<and> n0 \<in> Lines" 
    using n_facts pLdef pm PO by auto
  then show ?thesis
  proof (cases Q)
    case QO: (OrdinaryP B)
    have abk0: "incid A k0 \<and> incid B k0" 
      using PO QO k0def k_facts pm by auto
    have abn0: "incid A n0 \<and> incid B n0" 
      using PO QO n0def n_facts pm by auto
    have k0n0: "k0 = n0" using abn0 PO QO abk0 affine_plane.prop1P2 ap 
      k0def n0def pPdef pq_diff pq_pts by fastforce
    then show ?thesis using k0n0 k0def n0def by auto
  next
    case QI: (Ideal C)
    have ak0n0: "incid A k0 \<and> incid A n0" 
      using PO k0def k_facts n0def n_facts pm by auto
    have k0n0C: "k0 \<in> C \<and> n0 \<in> C" 
      using QI k0def k_facts n0def n_facts pm by auto
    have k0parn0: "affine_plane_data.parallel Points Lines incid k0 n0"
      using QI ap k0def k0n0C n0def pPdef pq_pts 
      affine_plane.in_pencil_parallel by fastforce
    obtain R where rdef: "R \<in> Points \<and> incid R k0 \<and> incid R n0" 
      using PO ak0n0 pPdef pq_pts by blast
    have k0eqn0: "k0 = n0" 
      using rdef affine_plane_data.parallel_def k0parn0 by metis
    show ?thesis using k0eqn0 k0def n0def by auto
  qed
next
  case PI: (Ideal D)
  then show ?thesis
  proof (cases Q)
    case QO: (OrdinaryP E)
    obtain k0 where k0def: "k = OrdinaryL k0 \<and> k0 \<in> Lines" 
      using k_facts pLdef pm QO by auto
    obtain n0 where n0def: "n = OrdinaryL n0 \<and> n0 \<in> Lines" 
      using n_facts pLdef pm QO by auto
    have ek0n0: "incid E k0 \<and> incid E n0" 
      using QO k0def k_facts n0def n_facts pm by auto
    have k0n0D: "k0 \<in> D \<and> n0 \<in> D" 
      using PI k0def k_facts n0def n_facts pm by auto
    have k0parn0: "affine_plane_data.parallel Points Lines incid k0 n0"
      using PI ap k0def k0n0D n0def pPdef pq_pts 
      affine_plane.in_pencil_parallel by fastforce
    obtain R where rdef: "R \<in> Points \<and> incid R k0 \<and> incid R n0" 
      using QO ek0n0 pPdef pq_pts by blast
    have k0eqn0: "k0 = n0" 
      using rdef affine_plane_data.parallel_def k0parn0 by metis
    show ?thesis using k0eqn0 k0def n0def by auto
  next
    case (Ideal F)
    then show ?thesis using PI assms two_ideal_is_infinite [of P] by blast
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma Ap1:
  fixes Points::"'p set" 
  fixes Lines:: "'l set"
  fixes incid::"'p \<Rightarrow> 'l \<Rightarrow> bool" 
  fixes join::"'p \<Rightarrow> 'p \<Rightarrow> 'l"
  fixes find_parallel::"'l \<Rightarrow> 'p \<Rightarrow> 'l"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P. (P \<in> Points)} \<union> {Ideal t | k t. 
    ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k))}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n. (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes pm: \<open>pincid = mprojectivize (incid)\<close>
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  fixes P Q
  assumes pq_facts: "P \<noteq> Q \<and> P \<in> pPoints \<and> Q \<in> pPoints"
  shows "\<exists>!k. k \<in> pLines \<and> P p\<lhd> k \<and> Q p\<lhd> k"
proof (cases P)
  case PO: (OrdinaryP A)
  then show ?thesis
  proof (cases Q)
    case QO: (OrdinaryP B)
    then obtain l where ldef: "l \<in> Lines \<and> incid A l \<and> incid B l"
      using PO ap affine_plane.a1a pPdef pq_facts by fastforce
    let ?k = "OrdinaryL l"
    have kexist: "?k \<in> pLines \<and> P p\<lhd> ?k \<and> Q p\<lhd> ?k" 
      using PO QO pm pLdef ldef by auto
    have "m \<in> pLines \<and> P p\<lhd> m \<and> Q p\<lhd> m \<longrightarrow> m = ?k" for m  using PO QO pm ap 
      affine_plane.prop1P2 ldef pLdef pPdef pq_facts by fastforce
    then show ?thesis using kexist by auto
  next
    case QI: (Ideal C)
    then obtain l1 where ldef: "l1 \<in> Lines \<and> C = affine_plane_data.line_pencil 
      Points Lines incid l1" using assms by auto
    let ?l2 = "find_parallel l1 A"
    have l2line: "?l2 \<in> Lines" 
      using PO affine_plane.a2a ap ldef pPdef pq_facts by fastforce
    have ainl2: "incid A ?l2" 
      using PO ap affine_plane.a2c ldef pPdef pq_facts by fastforce
    have l2pl1: "affine_plane_data.parallel Points Lines incid ?l2 l1" 
      using PO ap affine_plane.a2b ldef pPdef pq_facts by fastforce 
    have l2inC: "?l2 \<in> C" 
      using affine_plane_data.line_pencil_def l2pl1 ldef by fastforce
    let ?k = "OrdinaryL ?l2"
    have kpline: "?k \<in> pLines" using l2line pLdef by auto
    have pink: "P p\<lhd> ?k" using ainl2 PO pm by auto
    have cink: "Q p\<lhd> ?k" using l2inC QI pm by auto
    have "m \<in> pLines \<and> P p\<lhd> m \<and> Q p\<lhd> m \<longrightarrow> m = ?k" for m using ap cink pink
      Ap1b [of _ _ P _ _ Q _ _ m ?k] kpline pLdef pPdef pq_facts pm by blast
    then show ?thesis using kpline pink cink by auto
  qed
next
  case PI: (Ideal D)
  then show ?thesis
  proof (cases Q)
    case QO: (OrdinaryP E)
    obtain l1 where ldef: "l1 \<in> Lines \<and> D = affine_plane_data.line_pencil 
      Points Lines incid l1" using PI assms by auto
    let ?l2 = "find_parallel l1 E"
    have l2line: "?l2 \<in> Lines" 
      using QO affine_plane.a2a ap ldef pPdef pq_facts by fastforce
    have ainl2: "incid E ?l2" 
      using QO ap affine_plane.a2c ldef pPdef pq_facts by fastforce
    have l2pl1: "affine_plane_data.parallel Points Lines incid ?l2 l1" 
      using QO ap affine_plane.a2b ldef pPdef pq_facts by fastforce 
    have l2inC: "?l2 \<in> D" 
      using affine_plane_data.line_pencil_def l2pl1 ldef by fastforce
    let ?k = "OrdinaryL ?l2"
    have kpline: "?k \<in> pLines" using l2line pLdef by auto
    have pink: "P p\<lhd> ?k" using l2inC PI pm by auto
    have cink: "Q p\<lhd> ?k" using ainl2 QO pm by auto
    have "m \<in> pLines \<and> P p\<lhd> m \<and> Q p\<lhd> m \<longrightarrow> m = ?k" for m using ap cink pink
      Ap1b [of _ _ P _ _ Q _ _ m ?k] kpline pLdef pPdef pq_facts pm by blast
    then show ?thesis using kpline pink cink by auto
  next
    case QI: (Ideal F)
    have oninf: "P p\<lhd> Infty \<and> Q p\<lhd> Infty" using PI QI pm by auto
    have "m \<in> pLines \<and> P p\<lhd> m \<and> Q p\<lhd> m \<longrightarrow> m = Infty" for m using PI QI ap pm
      two_ideal_is_infinite [of P] pLdef pPdef pq_facts by blast
    then show ?thesis using oninf pLdef by auto
  qed
qed
text \<open>\done\<close>

(* text \<open>\hadi\<close>
lemma projectivization_p2:
  fixes Points::"'p set" 
  fixes Lines:: "'l set"
  fixes incid::"'p \<Rightarrow> 'l \<Rightarrow> bool" 
  fixes join::"'p \<Rightarrow> 'p \<Rightarrow> 'l"
  fixes find_parallel::"'l \<Rightarrow> 'p \<Rightarrow> 'l"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P. (P \<in> Points)} \<union> {Ideal t | k t. 
    ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k))}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n. (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes pm: \<open>pincid = mprojectivize (incid)\<close>
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  fixes k n
  assumes kn_facts: "k \<in> pLines \<and> n \<in> pLines"
  shows "\<exists>P. (P \<in> pPoints \<and> P p\<lhd> k \<and> P p\<lhd> n)"
proof (cases k)
  case Ok: (OrdinaryL a)
  then show ?thesis
  proof (cases n)
    case On: (OrdinaryL b)
    consider
    (aparb) "affine_plane_data.parallel Points Lines incid a b"
    | (aintb) "\<exists>Q. (Q \<in> Points \<and> incid Q a \<and> incid Q b)"
      using affine_plane_data.parallel_def [of _ _ incid] 
      kn_facts pLdef On Ok by fastforce
    then show ?thesis
    proof (cases)
      case aparb
      let ?t = "affine_plane_data.line_pencil Points Lines (incid) b"
      have aint: "a \<in> ?t" 
        using affine_plane_data.line_pencil_def aparb by fastforce
      let ?P = "Ideal ?t"
      have pppoint: "?P \<in> pPoints" using ap aparb pPdef 
        affine_plane_data.parallel_def [of _ _ _ a b] by fastforce
      have ponk: "?P p\<lhd> k" using Ok pm aint by auto
      have "?P p\<lhd> n" using On pm aint by (simp add: 
        affine_plane_data.line_pencil_def affine_plane_data.parallel_def)
      then show ?thesis using pppoint ponk by auto
    next
      case aintb
      then obtain Q where qdef: "Q \<in> Points \<and> incid Q a \<and> incid Q b" by auto
      let ?pQ = "OrdinaryP Q"
      have "?pQ p\<lhd> k \<and> ?pQ p\<lhd> n" using Ok On pm qdef by auto
      then show ?thesis using pPdef qdef by auto
    qed
  next
    case In: Infty
    let ?penk = "Ideal (affine_plane_data.line_pencil Points Lines incid a)"
    have penkppt: "?penk \<in> pPoints" using pPdef Ok kn_facts pLdef by auto
    have penkonn: "?penk p\<lhd> n" using In pm by auto
    have "?penk p\<lhd> k" using Ok pm affine_plane_data.line_pencil_def 
      affine_plane_data.parallel_reflexive kn_facts pLdef by fastforce
    then show ?thesis using penkppt penkonn by auto
  qed
next
  case Ik: Infty
  then show ?thesis
  proof (cases n)
    case On: (OrdinaryL c)
    let ?penc = "(affine_plane_data.line_pencil Points Lines incid c)"
    let ?penn = "Ideal (affine_plane_data.line_pencil Points Lines incid c)"
    have pennppt: "?penn \<in> pPoints" using pPdef On kn_facts pLdef by auto
    have pennonk: "?penn p\<lhd> k" using Ik pm by auto
    have "?penn p\<lhd> n" using Ik On pm affine_plane_data.line_pencil_def 
      affine_plane_data.parallel_reflexive kn_facts pLdef by fastforce
    then show ?thesis using pennppt pennonk by auto
  next
    case In: Infty
    obtain l where ldef: "l \<in> Lines" 
      using Ap3 affine_plane.containing_line ap by fastforce
    let ?penl = "Ideal (affine_plane_data.line_pencil Points Lines incid l)"
    have "?penl p\<lhd> k \<and> ?penl p\<lhd> n" using Ik In pm by auto
    then show ?thesis using ldef pPdef by auto
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma projectivization_p4:
  fixes Points::"'p set" 
  fixes Lines:: "'l set"
  fixes incid::"'p \<Rightarrow> 'l \<Rightarrow> bool" 
  fixes join::"'p \<Rightarrow> 'p \<Rightarrow> 'l"
  fixes find_parallel::"'l \<Rightarrow> 'p \<Rightarrow> 'l"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P. (P \<in> Points)} \<union> {Ideal t | k t. 
    ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k))}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n. (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes pm: \<open>pincid = mprojectivize (incid)\<close>
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  fixes k U
  assumes ku_facts: "k \<in> pLines \<and> U = {P. (P \<in> pPoints \<and> P p\<lhd> k)}"
  shows "\<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
proof (cases k)
  case Ok: (OrdinaryL l)
  then obtain QO RO  where QOROdef: 
    "QO \<in> Points \<and> RO \<in> Points \<and> incid QO l \<and> incid RO l \<and> RO \<noteq> QO" 
    using affine_plane.contained_points ap ku_facts pLdef by force
  let ?Q = "OrdinaryP QO" let ?R = "OrdinaryP RO"
  have QOROonk: "?Q p\<lhd> k \<and> ?R p\<lhd> k" using QOROdef Ok pm by auto
  let ?S = "Ideal (affine_plane_data.line_pencil Points Lines incid l)"
  have "?S p\<lhd> k" using affine_plane_data.line_pencil_def Ok pm pLdef
    affine_plane_data.parallel_reflexive ku_facts by fastforce
  then show ?thesis using Ok QOROonk QOROdef ku_facts pLdef pPdef by auto
next
  case (Infty)
  then show ?thesis using Ap4 ap ku_facts pPdef pm by fastforce
qed
text \<open>\done\<close> *)

text \<open>\hadi\<close>
theorem projectivization_is_projective:
  fixes Points::"'p set" 
  fixes Lines:: "'l set"
  fixes incid::"'p \<Rightarrow> 'l \<Rightarrow> bool" 
  fixes join::"'p \<Rightarrow> 'p \<Rightarrow> 'l"
  fixes find_parallel::"'l \<Rightarrow> 'p \<Rightarrow> 'l"
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P. (P \<in> Points)} \<union> {Ideal t | k t. 
    ((k \<in> Lines) \<and> (t = affine_plane_data.line_pencil Points Lines (incid) k))}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n. (n \<in> Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes pm: \<open>pincid = mprojectivize (incid)\<close>
  assumes ap: "affine_plane Points Lines incid join find_parallel"
  shows "projective_plane pPoints pLines pincid"
proof (unfold_locales)
  show "\<lbrakk>P \<noteq> Q; P \<in> pPoints; Q \<in> pPoints\<rbrakk> 
    \<Longrightarrow> (\<exists>!k. k \<in> pLines \<and> P p\<lhd> k \<and> Q p\<lhd> k)" for P Q 
    using assms pLdef pPdef Ap1 [of pincid] by auto
  show "\<lbrakk>k \<in> pLines; n \<in> pLines\<rbrakk> 
    \<Longrightarrow> \<exists>P. (P \<in> pPoints \<and> P p\<lhd> k \<and> P p\<lhd> n)" for k n 
    using assms Ap2 [of _ _ incid] by auto
  show "\<exists>P Q R. P \<in> pPoints \<and> Q \<in> pPoints \<and> R \<in> pPoints 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R  
    \<and> \<not> (projective_plane_data.pcollinear pPoints pLines pincid P Q R)"
    using Ap3 [of _ _ incid] pLdef pPdef ap pm by auto
  show "\<lbrakk>k \<in> pLines; U = {P. (P \<in> pPoints \<and> P p\<lhd> k)}\<rbrakk> 
    \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]" for k U
    using assms Ap4 [of _ _ incid] by auto
qed 
text \<open>\done\<close>
end
