theory "Chapter1-2"
  imports Complex_Main  "Chapter1-1"

begin

declare [[smt_timeout = 1000]]

(* Reminder of definitions
locale projective_plane_data2 =
  fixes Points :: "'p set" and Lines :: "'l set" and incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool" (infix "\<lhd>" 60)
begin

definition (in projective_plane_data2) pcollinear :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
    where "pcollinear A B C = (if (A \<in> Points \<and> B \<in> Points \<and> C \<in> Points)  
  then (\<exists> l. l \<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l \<and> C \<lhd> l) else undefined)"

definition (in projective_plane_data2) coincident :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
    where "coincident n k m  = (if (n \<in> Lines) \<and> (k \<in> Lines) \<and> (m  \<in> Lines)
  then (\<exists> P. P \<in> Points \<and> P \<lhd> n \<and> P \<lhd> k \<and> P \<lhd> m) else undefined)"
end (* projective_plane_data2 *)

locale projective_plane2 = projective_plane_data2 Points Lines incid
  for
     Points :: "'p set" and
     Lines :: "'l set" and
     incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"  (infix "\<lhd>" 60)  + 
assumes
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k . k \<in> Lines \<and> P \<lhd> k  \<and> Q \<lhd>  k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = { P . (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
*)

definition (in projective_plane2) meet ::"'l \<Rightarrow> 'l \<Rightarrow> 'p" (infix "." 60) where
"meet n k = (if n \<in> Lines \<and> k \<in> Lines \<and> n \<noteq> k then  (THE P . P \<lhd> n \<and> P \<lhd> k) else undefined)"

definition (in projective_plane2) join::"'p \<Rightarrow> 'p \<Rightarrow> 'l" (infix "\<^bold>" 60) where
"join P Q = (if P \<in> Points \<and> Q \<in> Points \<and> P \<noteq> Q then (THE k . P \<lhd> k \<and> Q \<lhd> k) else undefined)"

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
  shows "\<exists>P Q R. P \<in> pPoints \<and> Q \<in> pPoints \<and> R \<in> pPoints \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (projective_plane_data2.pcollinear pPoints pLines (pincid) P Q R)"
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

  have p6: "(projective_plane_data2.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> (if ((OrdinaryP P) \<in> pPoints \<and> (OrdinaryP Q) \<in> pPoints \<and> (OrdinaryP R) \<in> pPoints) 
  then (\<exists> l. l \<in> pLines \<and> (OrdinaryP P) p\<lhd> l \<and> (OrdinaryP Q) p\<lhd> l \<and> (OrdinaryP R) p\<lhd> l) 
  else undefined)" using projective_plane_data2.pcollinear_def by fastforce
  have p7: "(projective_plane_data2.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> 
    \<exists> l. l \<in> pLines \<and> (OrdinaryP P) p\<lhd> l \<and> (OrdinaryP Q) p\<lhd> l \<and> (OrdinaryP R) p\<lhd> l" using p6 p1 by auto
  have p8: "(projective_plane_data2.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> 
    \<exists> l. l \<noteq> Infty \<and> l \<in> pLines \<and> (OrdinaryP P) p\<lhd> l \<and> (OrdinaryP Q) p\<lhd> l \<and> (OrdinaryP R) p\<lhd> l" using p7 p2  by (metis assms(4) mprojectivize.simps(3))
  have p9: "(projective_plane_data2.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> 
    \<exists> k.  (OrdinaryP P) p\<lhd> ( OrdinaryL k) \<and> (OrdinaryP Q) p\<lhd>  ( OrdinaryL k) \<and>  (OrdinaryP R) p\<lhd>  ( OrdinaryL k)" using p8
  by (metis projLine.exhaust)
  have p10: "(projective_plane_data2.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> 
    \<exists> k. P \<lhd> k \<and> Q \<lhd> k \<and> R \<lhd> k" using p9 assms(4) by auto
  have p11: "(projective_plane_data2.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R)) \<Longrightarrow> 
    (affine_plane_data.collinear Points Lines (incid)P Q R)" 
  using ss affine_plane.a1b affine_plane.parallel_to_collinear ap p10 by fastforce

  have p12: "\<not>(affine_plane_data.collinear Points Lines (incid) P Q R)" 
    by (simp add: \<open>P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> affine_plane_data.collinear Points Lines incid P Q R\<close>)
  have p13: "\<not> (projective_plane_data2.pcollinear pPoints pLines pincid (OrdinaryP P) (OrdinaryP Q) (OrdinaryP R))" using p11 p12
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
  shows   "projective_plane2 pPoints pLines pincid"

proof (unfold_locales)
  find_theorems name: projective_plane2_def

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
  \<not> (projective_plane_data2.pcollinear pPoints pLines (pincid) P Q R)"
    by (smt (verit) Ap3 Collect_cong ap pLdef pPdef pm)
  show " \<exists>P Q R.
       P \<in> pPoints \<and> Q \<in> pPoints \<and> R \<in> pPoints  \<and>
       P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       \<not> projective_plane_data2.pcollinear
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

definition pfirst:: "(real \<times> real \<times> real) \<Rightarrow> real" where
  "pfirst = (\<lambda> x . fst x)"

definition psecond:: "(real \<times> real \<times> real) \<Rightarrow> real" where
  "psecond = (\<lambda> x . fst (snd x))"

definition pthird:: "(real \<times> real \<times> real) \<Rightarrow> real" where
  "pthird = (\<lambda> x . snd (snd x))"


    (* Define a type representing the cartesian product *)
definition projrel :: "(real \<times> real \<times> real) \<Rightarrow> (real \<times> real \<times> real) \<Rightarrow> bool"
  where "projrel = (\<lambda>x y. (x \<noteq> (0,0,0) \<and> y \<noteq> (0,0,0)) \<and>  (\<exists> (c::real) . c \<noteq> 0 \<and> (x = smult c y)))"



lemma exists_projrel_refl: "\<exists>x. projrel x x" 
proof -
  have "(1,0,0) = smult 1 (1,0,0)"  by (simp add: smult_def)
  then show ?thesis by (metis old.prod.inject one_neq_zero projrel_def)
qed

lemma nonzero_inverse: "((c::real) \<noteq> 0) \<Longrightarrow> ((1/c) \<noteq> 0)" by simp

lemma divide_through: "((c::real) \<noteq> 0) \<Longrightarrow> (a = c*q) \<Longrightarrow> ((1/c)*a = q)" by simp

lemma symp_projrel: "symp projrel"
proof -
  show ?thesis  unfolding symp_def 
  proof (clarify) 
    fix x y
    assume a: "projrel x y"
    obtain c where a1:"(x \<noteq> (0,0,0) \<and> y \<noteq> (0,0,0)) \<and>   c \<noteq> 0 \<and>
         (x = smult c y)" using a projrel_def by meson
    have inv: "(1/c) * c = 1" using a1 by auto
    from a1 have "smult (1/c) x = smult (1/c) (smult c y)" by auto
    also have "... = smult 1 y" using smult_assoc inv by simp
    also have "... =  y" using smult_ident by simp
    finally have "smult (1/c) x = y" by auto
    then have a2: "(x \<noteq> (0,0,0) \<and> y \<noteq> (0,0,0)) \<and>   (1/c) \<noteq> 0 \<and>
         (y = smult (1/c) x)" unfolding smult_def using a1 nonzero_inverse divide_through smult_assoc smult_ident by blast
    then  show "projrel y x" by (metis projrel_def)
  qed
qed

lemma transp_projrel: "transp projrel"
proof (rule transpI, unfold split_paired_all)
  fix x y z
  assume 1: "projrel x y"
  obtain c where a1:"(x \<noteq> (0,0,0) \<and> x \<noteq> (0,0,0)) \<and>   c \<noteq> 0 \<and>
         (x = smult c y)" using 1 projrel_def by meson
  assume 2: "projrel y z"
  obtain d where a2:"(y \<noteq> (0,0,0) \<and> z \<noteq> (0,0,0)) \<and>   d \<noteq> 0 \<and>
         (y = smult d z)" using 2 projrel_def by meson
  have p1: "c*d \<noteq> 0" using a1 a2 by auto
  have a3: "(x \<noteq> (0,0,0) \<and> z \<noteq> (0,0,0)) \<and>  (c*d) \<noteq> 0 \<and>
         x = smult (c*d) z" using a1 a2 p1 smult_assoc by blast
  show  "projrel x z" using a3  projrel_def by metis
qed

lemma part_equivp_projrel: "part_equivp projrel"
  by (rule part_equivpI [OF exists_projrel_refl symp_projrel transp_projrel])

quotient_type rp2 = "real \<times> real \<times> real" / partial: "projrel"
  morphisms Rep_Proj Abs_Proj
  using part_equivp_projrel .

lemma Domainp_cr_proj [transfer_domain_rule]: "Domainp pcr_rp2 = (\<lambda>x .( (x \<noteq> (0,0,0)) \<and> projrel x x))"
  by (simp add: projrel_def rp2.domain_eq)

thm rp2.domain_eq
thm Abs_Proj_def

(* a remaining theorem from the "warmup" section, one that needs "projrel": *)

lemma cross_nz:
  assumes "u \<in> punctured_r_3"
  assumes "v \<in> punctured_r_3"
  assumes "\<not> projrel u v"
  defines s_def: "s \<equiv> cross u v"
  shows "s \<in> punctured_r_3"
proof -
  show ?thesis unfolding punctured_r_3_def 
  proof (rule ccontr)
    assume ch: "s \<notin> UNIV - {(0, 0, 0)}"
    have 0: "s = (0,0,0)" using ch by simp 
    have 1: "squared_length s = (squared_length u) * (squared_length v) - (dot u v) * (dot u v)" using cross_prod_length2 assms by auto
    have 2: "squared_length s = 0" using squared_length_def 0 
      using dot_non_degenerate squared_length_is_self_dot by presburger
    have 3: "(squared_length u) * (squared_length v) = (dot u v) * (dot u v)" using 1 2 by simp
    have uu: "u \<noteq> (0,0,0)" using assms(1) punctured_r_3_def by auto
    have vv: "v \<noteq> (0,0,0)" using assms(2) punctured_r_3_def by auto
    have 5: "\<exists> c . u = smult c v" using cs_equality 3 assms 
      by (metis vv power2_eq_square prod_cases3 squared_length_is_self_dot)
    obtain x1 x2 x3 where ux: "u = (x1, x2, x3)" using prod_cases3 by blast
    obtain y1 y2 y3 where vy: "v = (y1, y2, y3)" using prod_cases3 by blast
    have 6: "\<exists> c . u = smult c v \<equiv> \<exists> c . u =   (c * y1, c * y2, c * y3)" by (simp add: smult_def vy)
    have 7: "\<exists> c . u =   (c * y1, c * y2, c * y3) \<equiv>  \<exists> c . (x1, x2, x3) =   (c * y1, c * y2, c * y3)" using 6 by (simp add: ux)
    have 8: "\<exists> c . (x1, x2, x3) = (c*y1, c*y2, c*y3)" using 5 6 7 by blast 
    obtain c where cdef: "(x1, x2, x3) = (c*y1, c*y2, c*y3)" using 8 by blast
    have cz: "c \<noteq> 0" using cdef uu vv ux by auto
    have 9: "projrel u v" using 8 projrel_def ux vy 
    by (metis (no_types, lifting) "5" dot_non_degenerate dot_scalar mult_eq_0_iff uu)
    show False using assms(3) 9 by auto
  qed
qed


(* We've defined RP2, but we still need to show it's a projective plane, i.e., demonstrate 
axioms 1 - 4. Then we can move on to isomorphism with the completion of the affine plane. *)

(* RP2 is a projective plane *)

lemma projrel_scalar: 
  shows "\<lbrakk>projrel P Q\<rbrakk> \<Longrightarrow> \<exists> s . s \<noteq> (0::real) \<and> P = smult s Q" using projrel_def by meson

definition rp2_Points where
"rp2_Points = (UNIV::rp2 set)" 

definition rp2_Lines where
"rp2_Lines = (UNIV::rp2 set)"

lemma good_lift1:
  fixes x
  assumes "x \<in> punctured_r_3"
  shows "\<not> (projrel x (0,0,0))" 
  using projrel_def by presburger

(* next defn unneeded? *)
definition rp2_incid_rep where
"rp2_incid_rep P k = (dot P k = 0)"

lift_definition rp2_incid::"rp2 \<Rightarrow> rp2 \<Rightarrow> bool"
is "\<lambda> P k . (dot P k = 0)"
proof -
  fix P1 P2 k1 k2
  assume a1: "projrel P1 P2"
  assume a2: "projrel k1 k2"
  show "(dot P1 k1 = 0) = (dot P2 k2 = 0)"
  proof -
    obtain s where f1: "s\<noteq> 0 \<and> P1 = smult s P2" using a1 projrel_scalar by blast
    obtain t where f2: "t\<noteq> 0 \<and> k1 = smult t k2" using a2 projrel_scalar by blast
    have stz: "s * t \<noteq> 0" using f1 f2 by auto
    have "dot P1 k1 = dot (smult s P2) k1" using f1 by blast
    also have "... = s * dot P2 k1" by (simp add: dot_commute)
    also have "... = s * dot P2 (smult t k2)" using f2 by blast
    also have "... = s * t * dot P2  k2" by (simp add: dot_commute)
    finally have proportion: "dot P1 k1 = s * t * dot P2  k2".
    have "(dot P1 k1 = 0) = (s * t * dot P2 k2 = 0)" using proportion by simp
    also have "... = (dot P2 k2 = 0)" using stz by auto
    finally show "(dot P1 k1 = 0) = (dot P2 k2 = 0)" by auto
  qed
qed

(*
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k . k \<in> Lines \<and> P \<lhd> k  \<and> Q \<lhd>  k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = { P . (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
*)

definition join :: "(real \<times> real \<times> real) \<Rightarrow> (real \<times> real \<times> real) \<Rightarrow> (real \<times> real \<times> real)"
  where
  "join \<equiv> \<lambda>P Q . (if cross P Q  = (0,0,0) then (0,0,1) else cross P Q)"


lift_definition Join :: "(real \<times> real \<times> real) \<Rightarrow> (real \<times> real \<times> real) \<Rightarrow> rp2"
  is "\<lambda>P Q. join P Q"
proof -
  fix P Q
  show "projrel (join P Q)
        (join P Q)" unfolding projrel_def join_def
  by (smt (verit) prod.inject smult_ident)
qed

thm Join.abs_eq


lemma rp2_P1a:
  fixes P Q
  assumes a1: "P \<in> rp2_Points" 
  assumes a2: "Q \<in> rp2_Points"
  assumes a3: "P \<noteq> Q"
  shows "(\<exists>k . k \<in> rp2_Lines \<and> rp2_incid P  k  \<and>  rp2_incid Q  k)"
proof -
  let ?rP = "(Rep_Proj P)"
  let ?rQ = "(Rep_Proj Q)"
  have diff: "\<not> projrel ?rP ?rQ" using Quotient3_rel_rep Quotient3_rp2 a3 by fastforce
  have diff2: "cross (Rep_Proj P) (Rep_Proj Q) \<noteq> (0, 0, 0)" using diff
  by (metis Diff_iff Domainp_cr_proj Quotient3_rep_reflp Quotient3_rp2 UNIV_I cross_nz nonzero_square_length_implies_nonzero_vector
      nonzero_vector_implies_nonzero_square_length punctured_r_3_def rp2.domain_eq singletonD)
  have rpgood: "?rP \<in> punctured_r_3" by (metis Diff_iff Domainp_cr_proj Quotient_rep_reflp Quotient_rp2 iso_tuple_UNIV_I punctured_r_3_def rp2.domain_eq singletonD)
  have rqgood: "?rQ \<in> punctured_r_3" by (metis Diff_iff Domainp_cr_proj Quotient_rep_reflp Quotient_rp2 iso_tuple_UNIV_I punctured_r_3_def rp2.domain_eq singletonD)
  let ?rk = "join ?rP ?rQ"

  thm cross_nz

  let ?k = "Abs_Proj ?rk"
  have s1: "?k \<in> rp2_Lines"  by (simp add: rp2_Lines_def)
  have u1: "(dot ?rP ?rk = 0) = 
   (dot (Rep_Proj P) (if cross (Rep_Proj P) (Rep_Proj Q) = (0, 0, 0) then (0, 0, 1) else cross (Rep_Proj P) (Rep_Proj Q)) = 0)" unfolding join_def by blast
  also have "... = (dot (Rep_Proj P) (cross (Rep_Proj P) (Rep_Proj Q)) = 0)" using diff2 by auto
  also have "... = True"   by (smt (z3) diff2 dot_cross_zero(1) old.prod.exhaust)
  finally have u2: "dot ?rP ?rk = 0" by auto
  have p1: "rp2_incid_rep ?rP  ?rk" unfolding rp2_incid_rep_def using u2 by blast
  have pa1: "rp2_incid P ?k" using p1
  by (smt (verit, ccfv_SIG) Quotient3_abs_rep Quotient3_rep_reflp Quotient3_rp2 diff2 join_def projrel_def rp2_incid.abs_eq smult_ident u2)

  have v1: "(dot ?rQ ?rk = 0) =
   (dot (Rep_Proj Q) (if cross (Rep_Proj P) (Rep_Proj Q) = (0, 0, 0) then (0, 0, 1) else cross (Rep_Proj P) (Rep_Proj Q)) = 0)" unfolding join_def by blast
  also have "... = (dot (Rep_Proj Q) (cross (Rep_Proj P) (Rep_Proj Q)) = 0)" using diff2 by auto
  also have "... = True"  by (metis dot_cross_zero(2) old.prod.exhaust)
  finally have v2: "dot ?rQ ?rk = 0" by auto
  
  have p2: "rp2_incid_rep ?rQ  ?rk" unfolding rp2_incid_rep_def using v2 by blast
  have pa2: "rp2_incid Q ?k" using p2
  by (smt (verit, ccfv_SIG) Quotient3_abs_rep Quotient3_rep_reflp Quotient3_rp2 diff2 join_def projrel_def rp2_incid.abs_eq smult_ident v2)

  show ?thesis using pa1 pa2 s1 by blast
qed

(* TO DO: To show uniqueness, we have to show (for P,Q in punctured_r_3 and P and Q not proj_rel, 
that if h is orthog to P and Q, then h is a nonzero multiple of the cross product. Ugh. Ugly algebra ahead *)
lemma rp2_P1b_helper:
  fixes P Q k n
  assumes a1: "P \<in> punctured_r_3" 
  assumes a2: "Q \<in>  punctured_r_3"
  assumes a3: "\<not> projrel P Q"
  assumes a4: "n = cross P Q"
  assumes a5: "k \<in>  punctured_r_3"
  assumes k_facts: "(dot P k = 0)  \<and> (dot Q k = 0)" 
  shows "\<exists>c . (c \<noteq> 0) \<and> k = smult c n"
proof -
  obtain a b c where pdef: "P = (a, b, c)" and "(a, b, c) \<noteq> (0,0,0)" using a1 prod_cases3
  by (metis nonzero_square_length_implies_nonzero_vector nonzero_vector_implies_nonzero_square_length)
  obtain p q r where qdef: "Q = (p, q, r)" and "(p, q, r) \<noteq> (0,0,0)" using a2 prod_cases3
  by (metis nonzero_square_length_implies_nonzero_vector nonzero_vector_implies_nonzero_square_length)
  obtain x y z where kdef: "k = (x, y, z)" and "(x, y, z) \<noteq> (0, 0, 0)" using a5 prod_cases3
  by (metis nonzero_square_length_implies_nonzero_vector nonzero_vector_implies_nonzero_square_length)

  have nz: "n \<noteq> (0, 0, 0)" using a4 cross_nz by (metis Diff_iff a1 a2 a3 punctured_r_3_def singletonI)
  obtain nx ny nz where n_def: "n = (nx, ny, nz)" using nz prod_cases3 by blast
  have "(nx, ny, nz) = cross (a, b, c) (p, q, r)" using a4 pdef qdef n_def by auto
  also have "... = (b * r - c * q, c * p - a * r, a * q - b * p)" unfolding cross_def by fastforce
  finally have nfact: "(nx, ny, nz) = (b * r - c * q, c * p - a * r, a * q - b * p)" by auto

  consider (X) "(nx \<noteq> 0)" | (Y) "(ny \<noteq> 0)"   | (Z) "(nz \<noteq> 0)" using n_def nz by blast
  then have ?thesis
  proof cases
    case X
    have u0: "a * x + y * b + z * c = (0::real)" using k_facts pdef  by (simp add: dot_def kdef mult.commute)
    then have s1: "a * x * r + y * b * r + z * c * r = 0" by (metis distrib_right mult_cancel_left2)
    have u1: "x * p + y * q + z * r = (0::real)" using k_facts qdef  by (simp add: dot_def kdef mult.commute)
    then have s2: "x * p * c + y * q * c + z * r * c = (0::real)" by (metis distrib_right mult_cancel_left2)
    have s3: "x*(a*r - p*c) + y*(b*r - q*c) = 0" using s1 s2 by argo
    have hy: "-x * ny + y * nx = 0" using s3 nfact by (smt (verit, best) minus_mult_minus mult.commute prod.inject)

    have t1: "a * x * q + y * b * q + z * c * q = 0" using u0 by (metis distrib_right mult_cancel_left2)
    have "x * p + y * q + z * r = (0::real)" using k_facts qdef  by (simp add: dot_def kdef mult.commute)
    then have t2: "x * p * b + y * q * b + z * r * b = (0::real)" using u1 by (metis distrib_right mult_cancel_left2)
    have t3: "x*(a*q - p*b) + z*(c*q - r*b) = 0" using t1 t2 by argo
    have hz: "-x * nz + z * nx = 0" using t3 nfact  by (smt (verit) minus_mult_minus mult.commute mult_minus_left prod.inject)
    have hx: "-x * nx + x * nx = 0" by auto
    have kx: "x * nx = x * nx" using hx by argo
    have ky: "x * ny = y * nx" using hy by argo
    have kz: "x * nz = z * nx" using hz by argo

    have "smult x (nx, ny, nz) = smult nx (x, y, z)" unfolding smult_def using kx ky kz by force
    then show ?thesis
    by (metis X \<open>(x, y, z) \<noteq> (0, 0, 0)\<close> divide_through dot_non_degenerate dot_scalar kdef mult_cancel_left2 n_def smult_assoc smult_ident)
  next
    case Y
    have u0: "a * x + y * b + z * c = (0::real)" using k_facts pdef  by (simp add: dot_def kdef mult.commute)
    then have s1: "a * x * p + y * b * p + z * c * p = 0" by (metis distrib_right mult_cancel_left2)
    have u1: "x * p + y * q + z * r = (0::real)" using k_facts qdef  by (simp add: dot_def kdef mult.commute)
    then have s2: "x * p * a + y * q * a + z * r * a = (0::real)" by (metis distrib_right mult_cancel_left2)
    have s3: "y*(b*p - a*q) + z*(c*p - a*r) = 0" using s1 s2 by argo
    have hz: "-y * nz + z * ny = 0" by (smt (verit) minus_mult_minus nfact prod.inject s3)
    
    have t1: "a * x * r + y * b * r + z * c * r = 0" using u0 by (metis distrib_right mult_cancel_left2)
    have "x * p + y * q + z * r = (0::real)" using k_facts qdef  by (simp add: dot_def kdef mult.commute)
    then have t2: "x * p * c + y * q * c + z * r * c = (0::real)" using u1 by (metis distrib_right mult_cancel_left2)
    have t3: "x*(c*p - a*r) + y*(q*c - b*r) = 0" using t1 t2 by argo
    have hx: "-x * ny + y * nx = 0" using t3 nfact  by (smt (verit) minus_mult_minus mult.commute mult_minus_left prod.inject)
    have kx: "y * nx = x * ny" using hx by argo
    have hy: "-y * ny + y * ny = 0" by auto 
    have ky: "y * ny = y * ny" using hy by argo
    have kz: "y * nz = z * ny" using hz by argo

    have "smult y (nx, ny, nz) = smult ny (x, y, z)" unfolding smult_def using kx ky kz by force
    then show ?thesis
    by (metis Y \<open>(x, y, z) \<noteq> (0, 0, 0)\<close> divide_through dot_non_degenerate dot_scalar kdef mult_cancel_left2 n_def smult_assoc smult_ident)
  next
    case Z
    have u0: "a * x + y * b + z * c = (0::real)" using k_facts pdef  by (simp add: dot_def kdef mult.commute)
    then have s1: "a * x * p + y * b * p + z * c * p = 0" by (metis distrib_right mult_cancel_left2)
    have u1: "x * p + y * q + z * r = (0::real)" using k_facts qdef  by (simp add: dot_def kdef mult.commute)
    then have s2: "x * p * a + y * q * a + z * r * a = (0::real)" by (metis distrib_right mult_cancel_left2)
    have s3: "y*(b*p - q*a) + z*(c*p - r*a) = 0" using s1 s2 by argo
    have hy: "-y * nz + z * ny = 0" using s3 nfact by (smt (verit) minus_mult_minus mult.commute prod.inject)  

    have t1: "a * x * q + y * b * q + z * c * q = 0" using u0 by (metis distrib_right mult_cancel_left2)
    have "x * p + y * q + z * r = (0::real)" using k_facts qdef  by (simp add: dot_def kdef mult.commute)
    then have t2: "x * p * b + y * q * b + z * r * b = (0::real)" using u1 by (metis distrib_right mult_cancel_left2)
    have t3: "x*(a*q - p*b) + z*(c*q - r*b) = 0" using t1 t2 by argo
    have hx: "-x * nz + z * nx = 0" using t3 nfact  by (smt (verit) minus_mult_minus mult.commute mult_minus_left prod.inject)
    have hz: "-z * nz + z * nz = 0" by auto
    have kx: "z * nx = x * nz" using hx by argo
    have ky: "z * ny = y * nz" using hy by argo
    have kz: "z * nz = z * nz" using hz by argo

    have "smult z (nx, ny, nz) = smult nz (x, y, z)" unfolding smult_def using kx ky kz by force
    then show ?thesis
    by (metis Z \<open>(x, y, z) \<noteq> (0, 0, 0)\<close> divide_through dot_non_degenerate dot_scalar kdef mult_cancel_left2 n_def smult_assoc smult_ident)
  qed
  show ?thesis by (simp add: \<open>\<exists>c. c \<noteq> 0 \<and> k = smult c n\<close>)
qed

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
  obtain xp yp zp where rpdef: "((xp, yp, zp) = Rep_Proj P) \<and> (xp, yp, zp) \<noteq> (0,0,0)" using a1 rp2_Points_def 
    by (metis Quotient3_rep_reflp Quotient3_rp2 prod_cases3 projrel_def)
  obtain xq yq zq where rqdef: "((xq, yq, zq) = Rep_Proj Q) \<and> (xq, yq, zq) \<noteq> (0,0,0)" using a1 rp2_Points_def 
    by (metis Quotient3_rep_reflp Quotient3_rp2 prod_cases3 projrel_def)
  let ?rP = "(xp, yp, zp)"
  let ?rQ = "(xq, yq, zq)"
  obtain rk where rkdef: "(rk = Rep_Proj k) \<and> (rk \<noteq> (0,0,0))" using a3 by (metis Quotient3_rel_rep Quotient3_rp2 projrel_def)
  obtain rn where rndef: "(rn = Rep_Proj n) \<and> (rn \<noteq> (0,0,0))" using a4 by (metis Quotient3_rel_rep Quotient3_rp2 projrel_def)
  have diff: "\<not> projrel ?rP ?rQ" using rpdef rqdef projrel_def a5 by (metis Quotient_rel_rep Quotient_rp2) 
  let ?n0 = "cross ?rP ?rQ"
  have pkfact: "dot ?rP rk = 0" using k_facts rkdef by (simp add: rp2_incid.rep_eq rpdef)
  have qkfact: "dot ?rQ rk = 0" using k_facts rkdef by (simp add: rp2_incid.rep_eq rqdef)
  obtain c where cfact: "(c \<noteq> 0) \<and> rk = smult c ?n0" using rp2_P1b_helper pkfact qkfact 
    by (metis (no_types, lifting) Diff_iff UNIV_I diff punctured_r_3_def rkdef rpdef rqdef singletonD) 
  have pnfact: "dot ?rP rn = 0" using n_facts rndef by (simp add: rp2_incid.rep_eq rpdef)
  have qnfact: "dot ?rQ rn = 0" using n_facts rndef by (simp add: rp2_incid.rep_eq rqdef)
  obtain d where dfact: "(d \<noteq> 0) \<and> rn = smult d ?n0" using rp2_P1b_helper pnfact qnfact 
    by (metis (no_types, lifting) Diff_iff UNIV_I diff punctured_r_3_def rndef rpdef rqdef singletonD) 
  have "rn = smult (d/c) rk" using cfact dfact smult_assoc by auto
  then have nkrel: "projrel rn rk" using projrel_def 
    by (metis cfact dfact divide_eq_0_iff rkdef rndef)
  then show "k = n" using nkrel by (metis Quotient_rel_rep Quotient_rp2 rkdef rndef)
qed

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
proof -
  show ?thesis using rp2_P1a [of k m]   using a3 dot_commute rp2_Points_def rp2_incid.rep_eq  a1 a2 rp2_Lines_def by auto
 (* wow, that was easy! *)
qed

lemma rp2_P3:
  shows "\<exists>P Q R. P \<in> rp2_Points \<and> Q \<in>  rp2_Points \<and> R \<in>  rp2_Points \<and> 
          P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> 
          \<not> (\<exists>k \<in> rp2_Lines . rp2_incid P k \<and> rp2_incid Q k \<and> rp2_incid R k)"
proof -
  let ?rP =" (1,0,0::real)"
  let ?rQ =" (0,1,0::real)"
  let ?rR =" (0,0,1::real)"
  let ?P = "Abs_Proj ?rP"
  let ?Q = "Abs_Proj ?rQ"
  let ?R = "Abs_Proj ?rR"
  have "?P \<in> rp2_Points" by (simp add: rp2_Points_def)
  have "?Q \<in> rp2_Points" by (simp add: rp2_Points_def)
  have "?R \<in> rp2_Points" by (simp add: rp2_Points_def)
  have da: "projrel (Rep_Proj (Abs_Proj (1,0,0)))  (1,0,0)" using ra [of "(1,0,0)"]
    by (metis prod.inject projrel_def smult_ident zero_neq_one)
  have db: "projrel (Rep_Proj (Abs_Proj (0,1,0)))  (0,1,0)" using ra [of "(0,1,0)"] 
    by (metis prod.inject projrel_def smult_ident zero_neq_one)
  have dc: "projrel (Rep_Proj (Abs_Proj (0,0,1)))  (0,0,1)" using ra [of "(0,0,1)"] 
    by (metis prod.inject projrel_def smult_ident zero_neq_one)
   
  have diffPQ: "\<not>projrel ?rP ?rQ" by (simp add: projrel_def smult_def)
  have "?P \<noteq> ?Q" using diffPQ  
    by (smt (verit, best) Quotient3_rel Quotient3_rp2 da db)
  have diffPR: "\<not>projrel ?rP ?rR" by (simp add: projrel_def smult_def)
  have "?P \<noteq> ?R" using diffPR  
    by (smt (verit, best) Quotient3_rel Quotient3_rp2 da dc)
  have diffQR: "\<not>projrel ?rQ ?rR" by (simp add: projrel_def smult_def)
  have "?Q \<noteq> ?R" using diffQR  
    by (smt (verit, best) Quotient3_rel Quotient3_rp2 db dc)

  have mm: "\<not> (\<exists>k\<in>rp2_Lines. rp2_incid ?P k \<and> rp2_incid ?Q k \<and> rp2_incid ?R k)"
  proof (rule ccontr)
    assume "\<not>\<not> (\<exists>k\<in>rp2_Lines. rp2_incid ?P k \<and> rp2_incid ?Q k \<and> rp2_incid ?R k)"
    then have "(\<exists>k\<in>rp2_Lines. rp2_incid ?P k \<and> rp2_incid ?Q k \<and> rp2_incid ?R k)" by blast
    then obtain k where kfact: "k\<in>rp2_Lines \<and> rp2_incid ?P k \<and> rp2_incid ?Q k \<and> rp2_incid ?R k" by blast
    let ?rk = "Rep_Proj k"
    from kfact have hx: "dot ?rk ?rP = 0" unfolding rp2_incid_def 
    by (smt (verit, ccfv_SIG) Quotient3_rel Quotient3_rel_rep Quotient3_rp2 ar da dot_commute rp2_incid.abs_eq rp2_incid_def)
    from kfact have hy: "dot ?rk ?rQ = 0" unfolding rp2_incid_def 
      by (smt (verit, ccfv_SIG) Quotient3_rel Quotient3_rel_rep Quotient3_rp2 ar db dot_commute rp2_incid.abs_eq rp2_incid_def)
    from kfact have hz: "dot ?rk ?rR = 0" unfolding rp2_incid_def 
      by (smt (verit, ccfv_SIG) Quotient3_rel Quotient3_rel_rep Quotient3_rp2 ar dc dot_commute rp2_incid.abs_eq rp2_incid_def)
    obtain x y z where kdef: "?rk = (x, y, z)" using prod_cases3 by blast
    have xx: "x = 0" using hx dot_def kdef 
      by (smt (verit) mult_eq_0_iff old.prod.case)
    have yy: "y = 0" using hy dot_def kdef
      by (smt (verit) mult_eq_0_iff old.prod.case)
    have zz: "z = 0" using hz dot_def kdef  
      by (smt (verit) mult_eq_0_iff old.prod.case)
    have uu: "?rk = (0,0,0)" using xx yy zz kdef by blast
    show "False" using uu kfact
      by (metis Quotient_rep_reflp Quotient_rp2 projrel_def)
  qed
  show ?thesis using diffPQ diffPR diffQR mm 
  using \<open>Abs_Proj (0, 0, 1) \<in> rp2_Points\<close> \<open>Abs_Proj (0, 1, 0) \<in> rp2_Points\<close> \<open>Abs_Proj (0, 1, 0) \<noteq> Abs_Proj (0, 0, 1)\<close> \<open>Abs_Proj (1, 0, 0) \<in> rp2_Points\<close>
    \<open>Abs_Proj (1, 0, 0) \<noteq> Abs_Proj (0, 0, 1)\<close> \<open>Abs_Proj (1, 0, 0) \<noteq> Abs_Proj (0, 1, 0)\<close> by blast
qed

lemma rp2_P4:
  fixes k
  fixes U
  assumes "k \<in> rp2_Lines"
  assumes "U = {X . X \<in> rp2_Points \<and> rp2_incid X k}"
  shows "\<exists>P Q R. P \<in> U \<and> Q \<in> U \<and> R \<in> U \<and> distinct [P,Q,R]"
proof -
  let ?rk = "Rep_Proj k"
  obtain x y z where rkdef: "(x, y, z) = ?rk" by (metis surj_pair)
  have nz: "(x, y, z) \<noteq> (0,0,0)" using rkdef assms(1) by (metis Quotient_rep_reflp Quotient_rp2 projrel_def) 
  consider (X) "(x \<noteq> 0)" | (Y) "(y \<noteq> 0)"   | (Z) "(z \<noteq> 0)" using nz by blast 
  then have ?thesis
  proof cases
    case X
    let ?rA = "(y, -x, 0)"
    let ?rB = "(z, 0, -x)"
    let ?rC = "(y+z, -x, -x)"
    have ssum: "?rC = vplus ?rA ?rB" using vplus_def 
    by (smt (verit) internal_case_prod_conv internal_case_prod_def)
    have Ain: "dot ?rA ?rk = 0" using rkdef X  by (smt (verit, best) Groups.mult_ac(2) dot_def mult_minus_right prod.simps(2))
    have Bin: "dot ?rB ?rk = 0" using rkdef X  by (smt (verit, best) Groups.mult_ac(2) dot_def mult_minus_right prod.simps(2))
    have Cin: "dot ?rC ?rk = 0" using rkdef X  using ssum by (simp add: Ain Bin)
    have diffAB: "\<not> projrel ?rA ?rB" by (simp add: X projrel_def smult_def)
    have diffAC: "\<not> projrel ?rA ?rC" by (simp add: X projrel_def smult_def)
    have diffBC: "\<not> projrel ?rB ?rC" by (simp add: X projrel_def smult_def)
    let ?A = "Abs_Proj ?rA"
    let ?B = "Abs_Proj ?rB"
    let ?C = "Abs_Proj ?rC"
    have da: "projrel (Rep_Proj (Abs_Proj (1,0,0)))  (1,0,0)" using ra [of "(1,0,0)"]
      by (metis prod.inject projrel_def smult_ident zero_neq_one)
    have db: "projrel (Rep_Proj (Abs_Proj (0,1,0)))  (0,1,0)" using ra [of "(0,1,0)"] 
      by (metis prod.inject projrel_def smult_ident zero_neq_one)
    have dc: "projrel (Rep_Proj (Abs_Proj (0,0,1)))  (0,0,1)" using ra [of "(0,0,1)"] 
      by (metis prod.inject projrel_def smult_ident zero_neq_one)
   
    have ab1: "?A \<noteq> ?B" using diffAB 
      by (smt (verit, del_insts) Quotient3_rel Quotient3_rp2 X prod.inject projrel_def smult_ident)
    have ac1: "?A \<noteq> ?C" using diffAC  
      by (smt (verit, del_insts) Quotient3_rel Quotient3_rp2 X prod.inject projrel_def smult_ident)
    have bc1: "?B \<noteq> ?C" using diffBC  
      by (smt (verit, del_insts) Quotient3_rel Quotient3_rp2 X prod.inject projrel_def smult_ident)
    have au: "?A \<in> U" 
      by (smt (verit, ccfv_threshold) Ain Quotient3_rel_rep Quotient3_rp2 UNIV_I X ar assms(2) mem_Collect_eq prod.inject projrel_def rp2_Points_def
        rp2_incid.abs_eq smult_ident)
    have bu: "?B \<in> U" 
      by (smt (verit, ccfv_threshold) Bin Quotient3_rel_rep Quotient3_rp2 UNIV_I X ar assms(2) mem_Collect_eq prod.inject projrel_def rp2_Points_def
        rp2_incid.abs_eq smult_ident)
    have cu: "?C \<in> U" 
      by (smt (verit, ccfv_threshold) Cin Quotient3_rel_rep Quotient3_rp2 UNIV_I X ar assms(2) mem_Collect_eq prod.inject projrel_def rp2_Points_def
        rp2_incid.abs_eq smult_ident)
    then show ?thesis using ab1 ac1 bc1 au bu cu by auto
  next
    case Y
    let ?rA = "(-y, x, 0)"
    let ?rB = "(0, z, -y)"
    let ?rC = "(-y, x+z, -y)"
    have ssum: "?rC = vplus ?rA ?rB" using vplus_def 
    by (smt (verit) internal_case_prod_conv internal_case_prod_def)
    have Ain: "dot ?rA ?rk = 0" using rkdef Y by (smt (verit, best) Groups.mult_ac dot_def mult_minus_right prod.simps)
    have Bin: "dot ?rB ?rk = 0" using rkdef Y  by (smt (verit, best) Groups.mult_ac dot_def mult_minus_right prod.simps)
    have Cin: "dot ?rC ?rk = 0" using rkdef Y  using ssum by (simp add: Ain Bin)
    have diffAB: "\<not> projrel ?rA ?rB" by (simp add: Y projrel_def smult_def)
    have diffAC: "\<not> projrel ?rA ?rC" by (simp add: Y projrel_def smult_def)
    have diffBC: "\<not> projrel ?rB ?rC" by (simp add: Y projrel_def smult_def)
    let ?A = "Abs_Proj ?rA"
    let ?B = "Abs_Proj ?rB"
    let ?C = "Abs_Proj ?rC"
    have da: "projrel (Rep_Proj (Abs_Proj (1,0,0)))  (1,0,0)" using ra [of "(1,0,0)"]
      by (metis prod.inject projrel_def smult_ident zero_neq_one)
    have db: "projrel (Rep_Proj (Abs_Proj (0,1,0)))  (0,1,0)" using ra [of "(0,1,0)"] 
      by (metis prod.inject projrel_def smult_ident zero_neq_one)
    have dc: "projrel (Rep_Proj (Abs_Proj (0,0,1)))  (0,0,1)" using ra [of "(0,0,1)"] 
      by (metis prod.inject projrel_def smult_ident zero_neq_one)
   
    have ab1: "?A \<noteq> ?B" using diffAB 
      by (smt (verit, del_insts) Quotient3_rel Quotient3_rp2 Y prod.inject projrel_def smult_ident)
    have ac1: "?A \<noteq> ?C" using diffAC  
      by (smt (verit, del_insts) Quotient3_rel Quotient3_rp2 Y prod.inject projrel_def smult_ident)
    have bc1: "?B \<noteq> ?C" using diffBC  
      by (smt (verit, del_insts) Quotient3_rel Quotient3_rp2 Y prod.inject projrel_def smult_ident)
    have au: "?A \<in> U" 
      by (smt (verit, ccfv_threshold) Ain Quotient3_rel_rep Quotient3_rp2 UNIV_I Y ar assms(2) mem_Collect_eq prod.inject projrel_def rp2_Points_def
        rp2_incid.abs_eq smult_ident)
    have bu: "?B \<in> U" 
      by (smt (verit, ccfv_threshold) Bin Quotient3_rel_rep Quotient3_rp2 UNIV_I Y ar assms(2) mem_Collect_eq prod.inject projrel_def rp2_Points_def
        rp2_incid.abs_eq smult_ident)
    have cu: "?C \<in> U" 
      by (smt (verit, ccfv_threshold) Cin Quotient3_rel_rep Quotient3_rp2 UNIV_I Y ar assms(2) mem_Collect_eq prod.inject projrel_def rp2_Points_def
        rp2_incid.abs_eq smult_ident)
    then show ?thesis using ab1 ac1 bc1 au bu cu by auto
  next
    case Z
    let ?rA = "(-z, 0, x)"
    let ?rB = "(0, -z, y)"
    let ?rC = "(-z, -z, x+y)"
    have ssum: "?rC = vplus ?rA ?rB" using vplus_def 
    by (smt (verit) internal_case_prod_conv internal_case_prod_def)
    have Ain: "dot ?rA ?rk = 0" using rkdef Z by (smt (verit, best) Groups.mult_ac dot_def mult_minus_right prod.simps)
    have Bin: "dot ?rB ?rk = 0" using rkdef Z  by (smt (verit, best) Groups.mult_ac dot_def mult_minus_right prod.simps)
    have Cin: "dot ?rC ?rk = 0" using rkdef Z  using ssum by (simp add: Ain Bin)
    have diffAB: "\<not> projrel ?rA ?rB" by (simp add: Z projrel_def smult_def)
    have diffAC: "\<not> projrel ?rA ?rC" by (simp add: Z projrel_def smult_def)
    have diffBC: "\<not> projrel ?rB ?rC" by (simp add: Z projrel_def smult_def)
    let ?A = "Abs_Proj ?rA"
    let ?B = "Abs_Proj ?rB"
    let ?C = "Abs_Proj ?rC"
    have da: "projrel (Rep_Proj (Abs_Proj (1,0,0)))  (1,0,0)" using ra [of "(1,0,0)"]
      by (metis prod.inject projrel_def smult_ident zero_neq_one)
    have db: "projrel (Rep_Proj (Abs_Proj (0,1,0)))  (0,1,0)" using ra [of "(0,1,0)"] 
      by (metis prod.inject projrel_def smult_ident zero_neq_one)
    have dc: "projrel (Rep_Proj (Abs_Proj (0,0,1)))  (0,0,1)" using ra [of "(0,0,1)"] 
      by (metis prod.inject projrel_def smult_ident zero_neq_one)
   
    have ab1: "?A \<noteq> ?B" using diffAB 
      by (smt (verit, del_insts) Quotient3_rel Quotient3_rp2 Z prod.inject projrel_def smult_ident)
    have ac1: "?A \<noteq> ?C" using diffAC  
      by (smt (verit, del_insts) Quotient3_rel Quotient3_rp2 Z prod.inject projrel_def smult_ident)
    have bc1: "?B \<noteq> ?C" using diffBC  
      by (smt (verit, del_insts) Quotient3_rel Quotient3_rp2 Z prod.inject projrel_def smult_ident)
    have au: "?A \<in> U" 
      by (smt (verit, ccfv_threshold) Ain Quotient3_rel_rep Quotient3_rp2 UNIV_I Z ar assms(2) mem_Collect_eq prod.inject projrel_def rp2_Points_def
        rp2_incid.abs_eq smult_ident)
    have bu: "?B \<in> U" 
      by (smt (verit, ccfv_threshold) Bin Quotient3_rel_rep Quotient3_rp2 UNIV_I Z ar assms(2) mem_Collect_eq prod.inject projrel_def rp2_Points_def
        rp2_incid.abs_eq smult_ident)
    have cu: "?C \<in> U" 
      by (smt (verit, ccfv_threshold) Cin Quotient3_rel_rep Quotient3_rp2 UNIV_I Z ar assms(2) mem_Collect_eq prod.inject projrel_def rp2_Points_def
        rp2_incid.abs_eq smult_ident)
    then show ?thesis using ab1 ac1 bc1 au bu cu by auto
  qed
  show ?thesis  using \<open>\<exists>P Q R. P \<in> U \<and> Q \<in> U \<and> R \<in> U \<and> distinct [P, Q, R]\<close> by blast
qed

(*
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k . k \<in> Lines \<and> P \<lhd> k  \<and> Q \<lhd>  k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P . (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = { P . (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
*)

theorem analytic_rp2:
shows "projective_plane2 rp2_Points rp2_Lines rp2_incid"
proof (unfold_locales)
  have pp1a: "\<And>P Q .\<lbrakk>P \<noteq> Q; P \<in> rp2_Points; Q \<in> rp2_Points\<rbrakk> \<Longrightarrow> (\<exists>k . k \<in> rp2_Lines \<and>  rp2_incid P k  \<and> rp2_incid Q k)" using rp2_P1a  by blast 
  have pp1b: "\<And>P Q k n .\<lbrakk>P \<noteq> Q; P \<in> rp2_Points; Q \<in> rp2_Points; 
    k \<in> rp2_Lines;  rp2_incid P  k;  rp2_incid Q  k; n \<in> rp2_Lines;   rp2_incid P n;  rp2_incid Q n\<rbrakk>  \<Longrightarrow> k = n" using rp2_P1b by blast
  have pp1:  "\<And>P Q .\<lbrakk>P \<noteq> Q; P \<in> rp2_Points; Q \<in> rp2_Points\<rbrakk> \<Longrightarrow> 
    (\<exists>!k . k \<in> rp2_Lines \<and>  rp2_incid P k  \<and>  rp2_incid Q k)" using pp1a pp1b by meson
  show " \<And>P Q. P \<noteq> Q \<Longrightarrow>
         P \<in> rp2_Points \<Longrightarrow>
           Q \<in> rp2_Points  \<Longrightarrow>
           \<exists>!k. k \<in> rp2_Lines  \<and>
                 rp2_incid P  k \<and>
                 rp2_incid Q  k"
    using pp1 by auto 
  next
    show "\<And>k n. k \<in> rp2_Lines \<Longrightarrow> n \<in> rp2_Lines \<Longrightarrow> \<exists>P. P \<in> rp2_Points \<and> rp2_incid P k \<and> rp2_incid P n" using rp2_P2 by (metis rp2_P1a rp2_P3)
  next
    show " \<exists>P Q R.
       P \<in> rp2_Points \<and>
       Q \<in> rp2_Points \<and> R \<in> rp2_Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> projective_plane_data2.pcollinear rp2_Points rp2_Lines rp2_incid P Q R" 
      using rp2_P3 by (smt (verit) projective_plane_data2.pcollinear_def)
  next
    show "\<And>k U. k \<in> rp2_Lines \<Longrightarrow> U = {P \<in> rp2_Points. rp2_incid P k} \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
      using rp2_P4 by blast
  qed

theorem projectivisation_of_A2:
  defines pPdef: "pPoints \<equiv> {OrdinaryP P | P . (P \<in> A2Points)} \<union> {Ideal t | k t . 
                  ((k \<in> A2Lines) \<and> (t = affine_plane_data.line_pencil  A2Points  A2Lines ( a2incid) k) )}"
  defines pLdef: "pLines \<equiv> {OrdinaryL n | n . (n \<in>  A2Lines)} \<union> {Infty}"
  fixes pincid (infix "p\<lhd>" 60)
  assumes pm: \<open>pincid =  mprojectivize (a2incid)\<close>
  assumes ap: "affine_plane  A2Points  A2Lines a2incid a2join a2find_parallel"
  shows   "projective_plane2 pPoints pLines pincid"
  using "Chapter1-2.projectivization_is_projective" A2_affine assms(1,2,3) by blast

end


