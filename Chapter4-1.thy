theory "Chapter4-1"
  imports Complex_Main "Chapter1-1"

begin
text \<open>Everything up to the Principle of Duality and the remarks after it. 
(You don't need to prove remark 2!)\<close>

text \<open>\hadi\<close>
fun mdualize :: "('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('l \<Rightarrow> 'p \<Rightarrow> bool)" 
  where "mdualize (incid) (l::'l) (P::'p) = incid P l"
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma dp_p1:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  fixes P Q
  assumes pq_facts: "P \<noteq> Q \<and> P \<in> dPoints \<and> Q \<in> dPoints"
  shows "\<exists>!k. k \<in> dLines \<and> P d\<lhd> k \<and> Q d\<lhd> k"
proof -
  obtain R where rdef: "R \<in> Points \<and> incid R P \<and> incid R Q" 
    using pq_facts pp projective_plane.p2 [of _ _ incid P Q] dPdef by auto
  then have "\<lbrakk>S \<in> Points; incid S P; incid S Q\<rbrakk> \<Longrightarrow> R = S" for S 
    using pq_facts pp projective_plane.p1 [of Points Lines _ R] dPdef by auto
  then show ?thesis using rdef dLdef dm by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma dp_p2:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  fixes k n
  assumes kn_facts: "k \<in> dLines \<and> n \<in> dLines"
  shows "\<exists>P. (P \<in> dPoints \<and> P d\<lhd> k \<and> P d\<lhd> n)"
proof (cases "k = n")
  case 1: True
  then obtain m where "m \<in> Lines \<and> incid k m" 
    using kn_facts pp unfolding projective_plane_def dLdef by metis
  then show ?thesis using 1 dm dPdef by auto
next
  case False
  then obtain m where "m \<in> Lines \<and> incid k m \<and> incid n m" 
    using kn_facts pp projective_plane.p1 [of Points] dLdef by blast
  then show ?thesis using dPdef dm by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma dp_p3:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  shows "\<exists>P Q R. P \<in> dPoints \<and> Q \<in> dPoints \<and> R \<in> dPoints \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R 
    \<and> \<not> (projective_plane_data.pcollinear dPoints dLines dincid P Q R)"
proof -
  obtain P Q R where pqr: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R 
    \<and> Q \<noteq> R \<and> \<not> (projective_plane_data.pcollinear Points Lines incid P Q R)" 
    using pp projective_plane.p3 by blast
  then obtain pq where pqdef: "pq \<in> Lines \<and> incid P pq \<and> incid Q pq" 
    using pp projective_plane.p1 [of Points Lines incid P Q] by auto
  obtain qr where qrdef: "qr \<in> Lines \<and> incid Q qr \<and> incid R qr" 
    using pqr pp projective_plane.p1 [of Points Lines incid Q R] by auto
  obtain pr where prdef: "pr \<in> Lines \<and> incid P pr \<and> incid R pr" 
    using pqr pp projective_plane.p1 [of Points Lines incid P R] by auto
  have alldp: "pq \<in> dPoints \<and> qr \<in> dPoints \<and> pr \<in> dPoints" 
    using pqdef qrdef prdef dPdef by auto
  have alldist: "pq \<noteq> qr \<and> pq \<noteq> pr \<and> qr \<noteq> pr" using pqr pqdef qrdef prdef 
    projective_plane_data.pcollinear_def [of _ _ incid] by auto
  have qnot: "\<not> (incid Q pr)" using pqr prdef 
    projective_plane_data.pcollinear_def [of _ _ incid] by auto
  have "\<not> (projective_plane_data.pcollinear dPoints dLines dincid pq qr pr)"
  proof (rule ccontr)
    assume cd: "\<not> (\<not> (projective_plane_data.pcollinear dPoints dLines (d\<lhd>) pq qr pr))"
    show False
    proof -
      obtain L where ldef: "L \<in> dLines \<and> pq d\<lhd> L \<and> qr d\<lhd> L \<and> pr d\<lhd> L" using cd 
        alldp projective_plane_data.pcollinear_def [of _ _ dincid] by auto
      then have "L = Q" using pp projective_plane.p1 [of _ _ incid L Q]
        alldist pqr pqdef qrdef dLdef dm by auto
      then show False using qnot dm ldef by auto
    qed
  qed
  then show ?thesis using alldist alldp by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in projective_plane) non_containing_line:
  fixes P
  assumes "P \<in> Points"
  shows "\<exists>l. l \<in> Lines \<and> (\<not> P \<lhd> l)"
  using assms p1 p3 unfolding pcollinear_def by metis
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma dp_p4:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  fixes k U
  assumes ku_facts: "k \<in> dLines \<and> U = {P. (P \<in> dPoints \<and> P d\<lhd> k)}"
  shows "\<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
proof -
  obtain l where ldef: "l \<in> Lines \<and> (\<not> incid k l)" using ku_facts pp
    projective_plane.non_containing_line [of Points Lines] dLdef by auto
  obtain A B C where "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> incid A l \<and> incid B l \<and> incid C l \<and> distinct[A,B,C]" 
    using ldef pp projective_plane.p4 [of Points Lines incid l] by auto
  then obtain Q R S where "Q \<in> Lines \<and> R \<in> Lines \<and> S \<in> Lines \<and> incid k Q 
    \<and> incid A Q \<and> incid k R \<and> incid B R \<and> incid k S \<and> incid C S \<and> distinct[Q,R,S]" 
    using ku_facts ldef distinct_length_2_or_more distinct_singleton dLdef pp
    projective_plane.p1 [of Points Lines incid k]
    projective_plane.p1 [of Points Lines _ A B]
    projective_plane.p1 [of Points Lines _ A C]
    projective_plane.p1 [of Points Lines _ B C] by (metis (lifting))
  then show ?thesis using ku_facts dPdef dm by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
theorem dual_plane_is_projective:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  shows "projective_plane dPoints dLines dincid"
proof (unfold_locales)
  show "\<lbrakk>P \<noteq> Q; P \<in> dPoints; Q \<in> dPoints\<rbrakk> 
    \<Longrightarrow> (\<exists>!k. k \<in> dLines \<and> P d\<lhd> k \<and> Q d\<lhd> k)" for P Q 
    using assms dp_p1 [of Points Lines] by simp
  show "\<lbrakk>k \<in> dLines; n \<in> dLines\<rbrakk> 
    \<Longrightarrow> \<exists>P. (P \<in> dPoints \<and> P d\<lhd> k \<and> P d\<lhd> n)" for k n 
    using assms dp_p2 [of Points Lines] by simp
  show "\<exists>P Q R. P \<in> dPoints \<and> Q \<in> dPoints \<and> R \<in> dPoints 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R 
    \<and> \<not> (projective_plane_data.pcollinear dPoints dLines dincid P Q R)"
    using assms dp_p3 [of Points Lines] by simp
  show "\<lbrakk>k \<in> dLines; U = {P. (P \<in> dPoints \<and> P d\<lhd> k)}\<rbrakk> 
    \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]" for k U
    using assms dp_p4 [of Points Lines] by simp
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
definition dual_meet :: "('l set) \<Rightarrow> ('p set) \<Rightarrow> ('l \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'l" where
  "dual_meet dPoints dLines dincid n k = (if (n \<in> dLines \<and> k \<in> dLines \<and> n \<noteq> k) 
  then THE P. P \<in> dPoints \<and> dincid P n \<and> dincid P k else undefined)"
text\<open>\done\<close>

text \<open>\hadi\<close>
definition dual_join::"('l set) \<Rightarrow> ('p set) \<Rightarrow> ('l \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'p" where
  "dual_join dPoints dLines dincid P Q = (if (P \<in> dPoints \<and> Q \<in> dPoints \<and> P \<noteq> Q) 
  then THE k. k \<in> dLines \<and> dincid P k \<and> dincid Q k else undefined)"
text\<open>\done\<close>

text \<open>\hadi\<close>
lemma dual_meet_is_join:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool"
  assumes dm: \<open>dincid = mdualize incid\<close>
  fixes n k
  assumes "n \<in> dLines \<and> k \<in> dLines"
  shows "dual_meet dPoints dLines dincid n k 
    = projective_plane_data.join Points Lines incid n k"
  unfolding dm dLdef dPdef dual_meet_def projective_plane_data.join_def by auto
text\<open>\done\<close>

text \<open>\hadi\<close>
lemma dual_join_is_meet:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool"
  assumes dm: \<open>dincid = mdualize incid\<close>
  fixes P Q
  assumes "P \<in> dPoints \<and> Q \<in> dPoints"
  shows "dual_join dPoints dLines dincid P Q 
    = projective_plane_data.meet Points Lines incid P Q"
  unfolding dm dLdef dPdef dual_join_def projective_plane_data.meet_def by auto
text\<open>\done\<close>

definition (in projective_plane_data) meet2 where
  "meet2 n k = (if (n \<in> Lines \<and> k \<in> Lines \<and> n \<noteq> k) 
  then THE P. P \<in> Points \<and> incid P n \<and> incid P k else undefined)"

definition (in projective_plane_data) join2 where
  "join2 P Q = (if (P \<in> Points \<and> Q \<in> Points \<and> P \<noteq> Q) 
  then THE k. k \<in> Lines \<and> P \<lhd> k \<and> Q \<lhd> k else undefined)"

text \<open>\hadi\<close>
definition desarguesian :: "('p set) \<Rightarrow> ('l set) \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool" where
  "desarguesian Points Lines incid \<equiv> (projective_plane Points Lines incid) 
    \<and> (\<forall>M A B C A' B' C'. M \<in> Points \<and> A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
      \<and> A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points 
      \<and> projective_plane_data.pcollinear Points Lines incid M A A'
      \<and> projective_plane_data.pcollinear Points Lines incid M B B'
      \<and> projective_plane_data.pcollinear Points Lines incid M C C'
      \<and> (\<not> projective_plane_data.pcollinear Points Lines incid A B C) 
      \<and> (\<not> projective_plane_data.pcollinear Points Lines incid A' B' C')
      \<longrightarrow> projective_plane_data.pcollinear Points Lines incid 
        (projective_plane_data.meet2 Points Lines incid 
          (projective_plane_data.join2 Points Lines incid A B)
          (projective_plane_data.join2 Points Lines incid A' B'))
        (projective_plane_data.meet2 Points Lines incid 
          (projective_plane_data.join2 Points Lines incid B C)
          (projective_plane_data.join2 Points Lines incid B' C'))
        (projective_plane_data.meet2 Points Lines incid 
          (projective_plane_data.join2 Points Lines incid A C)
          (projective_plane_data.join2 Points Lines incid A' C')))"
text \<open>\done\<close>

lemma apply_desargues:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes "desarguesian Points Lines incid"
  fixes M A B C A' B' C'
  assumes "M \<in> Points \<and> A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points 
    \<and> projective_plane_data.pcollinear Points Lines incid M A A'
    \<and> projective_plane_data.pcollinear Points Lines incid M B B'
    \<and> projective_plane_data.pcollinear Points Lines incid M C C'
    \<and> (\<not> projective_plane_data.pcollinear Points Lines incid A B C) 
    \<and> (\<not> projective_plane_data.pcollinear Points Lines incid A' B' C')"
  shows "projective_plane_data.pcollinear Points Lines incid 
    (projective_plane_data.meet2 Points Lines incid 
      (projective_plane_data.join2 Points Lines incid A B)
      (projective_plane_data.join2 Points Lines incid A' B'))
    (projective_plane_data.meet2 Points Lines incid 
      (projective_plane_data.join2 Points Lines incid B C)
      (projective_plane_data.join2 Points Lines incid B' C'))
    (projective_plane_data.meet2 Points Lines incid 
      (projective_plane_data.join2 Points Lines incid A C)
      (projective_plane_data.join2 Points Lines incid A' C'))"
  using assms unfolding desarguesian_def by metis

text \<open>\hadi\<close>
theorem p5_implies_dual_p5:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes dsp: "desarguesian Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool"
  assumes dm: \<open>dincid = mdualize incid\<close>
  shows "desarguesian dPoints dLines dincid" unfolding desarguesian_def 
proof
  show dualp: "projective_plane dPoints dLines dincid" 
    using assms dual_plane_is_projective unfolding desarguesian_def by auto
  show "\<forall>M A B C A' B' C'. (M \<in> dPoints \<and> A \<in> dPoints \<and> B \<in> dPoints \<and> C \<in> dPoints 
    \<and> A' \<in> dPoints \<and> B' \<in> dPoints \<and> C' \<in> dPoints 
    \<and> projective_plane_data.pcollinear dPoints dLines dincid M A A'
    \<and> projective_plane_data.pcollinear dPoints dLines dincid M B B'
    \<and> projective_plane_data.pcollinear dPoints dLines dincid M C C'
    \<and> (\<not> projective_plane_data.pcollinear dPoints dLines dincid A B C) 
    \<and> (\<not> projective_plane_data.pcollinear dPoints dLines dincid A' B' C'))
    \<longrightarrow> projective_plane_data.pcollinear dPoints dLines dincid 
      (projective_plane_data.meet2 dPoints dLines dincid 
        (projective_plane_data.join2 dPoints dLines dincid A B)
        (projective_plane_data.join2 dPoints dLines dincid A' B'))
      (projective_plane_data.meet2 dPoints dLines dincid 
        (projective_plane_data.join2 dPoints dLines dincid B C)
        (projective_plane_data.join2 dPoints dLines dincid B' C'))
      (projective_plane_data.meet2 dPoints dLines dincid 
        (projective_plane_data.join2 dPoints dLines dincid A C)
        (projective_plane_data.join2 dPoints dLines dincid A' C'))"
  proof clarify
    fix M A B C A' B' C'
    assume m:"M \<in> dPoints" and a:"A \<in> dPoints" and b:"B \<in> dPoints" and c:"C \<in> dPoints"
    and a':"A' \<in> dPoints" and b':"B' \<in> dPoints" and c':"C' \<in> dPoints" 
    and maa': "projective_plane_data.pcollinear dPoints dLines dincid M A A'"
    and mbb': "projective_plane_data.pcollinear dPoints dLines dincid M B B'"
    and mcc': "projective_plane_data.pcollinear dPoints dLines dincid M C C'"
    and abc: "\<not> projective_plane_data.pcollinear dPoints dLines dincid A B C"
    and a'b'c': "\<not> projective_plane_data.pcollinear dPoints dLines dincid A' B' C'"
    let ?P = "(projective_plane_data.meet2 dPoints dLines dincid 
      (projective_plane_data.join2 dPoints dLines dincid A B)
      (projective_plane_data.join2 dPoints dLines dincid A' B'))"
    let ?Q = "(projective_plane_data.meet2 dPoints dLines dincid 
      (projective_plane_data.join2 dPoints dLines dincid A C)
      (projective_plane_data.join2 dPoints dLines dincid A' C'))"
    let ?R = "(projective_plane_data.meet2 dPoints dLines dincid 
      (projective_plane_data.join2 dPoints dLines dincid B C)
      (projective_plane_data.join2 dPoints dLines dincid B' C'))"
    have ppdef: "?P = (projective_plane_data.meet dPoints dLines dincid 
      (projective_plane_data.join dPoints dLines dincid A B)
      (projective_plane_data.join dPoints dLines dincid A' B'))" 
      using projective_plane_data.join2_def [of dPoints dLines dincid] 
        projective_plane_data.join_def [of dPoints dLines dincid]
        projective_plane_data.meet2_def [of dPoints dLines dincid] 
        projective_plane_data.meet_def [of dPoints dLines dincid] by auto
    have qqdef: "?Q = (projective_plane_data.meet dPoints dLines dincid 
      (projective_plane_data.join2 dPoints dLines dincid A C)
      (projective_plane_data.join2 dPoints dLines dincid A' C'))"
      using projective_plane_data.join2_def [of dPoints dLines dincid] 
        projective_plane_data.join_def [of dPoints dLines dincid]
        projective_plane_data.meet2_def [of dPoints dLines dincid] 
        projective_plane_data.meet_def [of dPoints dLines dincid] by auto
    have rrdef: "?R = (projective_plane_data.meet2 dPoints dLines dincid 
      (projective_plane_data.join2 dPoints dLines dincid B C)
      (projective_plane_data.join2 dPoints dLines dincid B' C'))"
      using projective_plane_data.join2_def [of dPoints dLines dincid] 
        projective_plane_data.join_def [of dPoints dLines dincid]
        projective_plane_data.meet2_def [of dPoints dLines dincid] 
        projective_plane_data.meet_def [of dPoints dLines dincid] by auto
    show "projective_plane_data.pcollinear dPoints dLines dincid ?P ?R ?Q"
    proof -
      obtain M0 where m0: "M0 \<in> Points \<and> incid M0 M \<and> incid M0 A \<and> incid M0 A'" 
        using m a a' maa' dLdef dm unfolding projective_plane_data.pcollinear_def by auto
      obtain A0 where a0: "A0 \<in> Points \<and> incid A0 M \<and> incid A0 B \<and> incid A0 B'" 
        using m b b' mbb' dLdef dm unfolding projective_plane_data.pcollinear_def by auto
      obtain A'0 where a'0: "A'0 \<in> Points \<and> incid A'0 M \<and> incid A'0 C \<and> incid A'0 C'" 
        using m c c' mcc' dLdef dm unfolding projective_plane_data.pcollinear_def by auto
      obtain B0 where b0: "B0 \<in> Points \<and> incid B0 A \<and> incid B0 B" 
        using a b dLdef dm dualp mdualize.elims(2) projective_plane.p3 
        projective_plane.p1 [of _ _ dincid] by metis
      obtain B'0 where b'0: "B'0 \<in> Points \<and> incid B'0 A \<and> incid B'0 C" 
        using a c dLdef dm dualp mdualize.elims(2) projective_plane.p3 
        projective_plane.p1 [of _ _ dincid] by metis
      obtain C0 where c0: "C0 \<in> Points \<and> incid C0 A' \<and> incid C0 B'" 
        using a' b' dLdef dm dualp mdualize.elims(2) projective_plane.p3 
        projective_plane.p1 [of _ _ dincid] by metis
      obtain C'0 where c'0: "C'0 \<in> Points \<and> incid C'0 A' \<and> incid C'0 C'" 
        using a' c' dLdef dm dualp mdualize.elims(2) projective_plane.p3 
        projective_plane.p1 [of _ _ dincid] by metis
      have allp: "M0 \<in> Points \<and> A0 \<in> Points \<and> B0 \<in> Points \<and> C0 \<in> Points \<and> A'0 \<in> Points 
        \<and> B'0 \<in> Points \<and> C'0 \<in> Points" using m0 a0 b0 c0 a'0 b'0 c'0 by simp
      have m0a0a'0: " projective_plane_data.pcollinear Points Lines incid M0 A0 A'0"
        using projective_plane_data.pcollinear_def [of _ _ incid] 
        m m0 a0 a'0 dPdef by auto
      have m0b0b'0: "projective_plane_data.pcollinear Points Lines incid M0 B0 B'0"
        using projective_plane_data.pcollinear_def [of _ _ incid] 
        a m0 b0 b'0 dPdef by auto
      have m0c0c'0: "projective_plane_data.pcollinear Points Lines incid M0 C0 C'0"
        using projective_plane_data.pcollinear_def [of _ _ incid] 
        a' m0 c0 c'0 dPdef by auto
      have a0b0c0: "\<not> projective_plane_data.pcollinear Points Lines incid A0 B0 C0"
      proof (rule ccontr)
        assume cd1: "\<not> (\<not> projective_plane_data.pcollinear Points Lines incid A0 B0 C0)"
        show False
        proof -
          have "projective_plane_data.pcollinear Points Lines incid A0 B0 C0" using cd1 by simp
          then obtain l1 where l1def: "l1 \<in> Lines \<and> incid A0 l1 \<and> incid B0 l1 \<and> incid C0 l1" 
            using a0 b0 c0 projective_plane_data.pcollinear_def [of _ _ incid] by auto
          then obtain l where "l \<in> dLines \<and> dincid A l \<and> dincid B l \<and> dincid C l" sorry
          then show False 
            using a b c abc projective_plane_data.pcollinear_def [of _ _ dincid] by auto
        qed
      qed
      have a'0b'0c'0: "\<not> projective_plane_data.pcollinear Points Lines incid A'0 B'0 C'0" sorry
      let ?P' = "(projective_plane_data.meet2 Points Lines incid 
        (projective_plane_data.join2 Points Lines incid A0 B0)
        (projective_plane_data.join2 Points Lines incid A'0 B'0))"
      let ?Q' = "(projective_plane_data.meet2 Points Lines incid 
        (projective_plane_data.join2 Points Lines incid A0 C0)
        (projective_plane_data.join2 Points Lines incid A'0 C'0))"
      let ?R' = "(projective_plane_data.meet2 Points Lines incid 
        (projective_plane_data.join2 Points Lines incid B0 C0)
        (projective_plane_data.join2 Points Lines incid B'0 C'0))"
      have p'q'r': "projective_plane_data.pcollinear Points Lines incid ?P' ?Q' ?R'"
        using apply_desargues [of Points Lines incid M0 A0 B0 C0 A'0 B'0 C'0] 
        dsp allp m0a0a'0 m0b0b'0 m0c0c'0 a0b0c0 a'0b'0c'0 unfolding
        desarguesian_def projective_plane_data.pcollinear_def by (smt (z3))
      have p0bc: "?P' = projective_plane_data.meet2 Points Lines incid B C" sorry
      have q0b'c': "?Q' = projective_plane_data.meet2 Points Lines incid B' C'" sorry
      have "?P' = projective_plane_data.join2 dPoints dLines dincid B C" sorry
      have "?Q' = projective_plane_data.join2 dPoints dLines dincid B' C'" sorry
      have p'q'isr': "projective_plane_data.meet2 dPoints dLines dincid ?P' ?Q' = ?R"  
      using
        \<open>projective_plane_data.meet2 Points Lines incid (projective_plane_data.join2 Points Lines incid A0 B0) (projective_plane_data.join2 Points Lines incid A'0 B'0) = projective_plane_data.join2 dPoints dLines dincid B C\<close>
        \<open>projective_plane_data.meet2 Points Lines incid (projective_plane_data.join2 Points Lines incid A0 C0) (projective_plane_data.join2 Points Lines incid A'0 C'0) = projective_plane_data.join2 dPoints dLines dincid B' C'\<close>
        by auto
      obtain S where "S \<in> Points \<and> incid S ?P \<and> incid S ?R \<and> incid S ?Q" sorry
      then have "S \<in> dLines \<and> dincid ?P S \<and> dincid ?R S \<and> dincid ?Q S" using dm dLdef by auto
      then have "projective_plane_data.pcollinear dPoints dLines dincid ?P ?R ?Q"
        sorry
      show ?thesis sorry
    qed
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
definition proj_statement :: "('p set) \<Rightarrow> ('l set) \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool" where
  "proj_statement Points Lines incid = projective_plane Points Lines incid"
text \<open>\done\<close>

text \<open>\hadi\<close>
lift_definition dual_statement :: "('l set) \<Rightarrow> ('p set) \<Rightarrow> ('l \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> bool"
  is "\<lambda>Points Lines incid. proj_statement Lines Points (mdualize incid)" .
text \<open>\done\<close>

text \<open>\hadi\<close>
theorem principle_of_duality:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes "proj_statement Points Lines incid"
  shows "dual_statement Points Lines incid" using assms dual_plane_is_projective 
    dual_statement.transfer proj_statement_def by metis
text \<open>\done\<close>

text \<open>\hadi\<close>
theorem double_dual_iso:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool"
  assumes dm: \<open>dincid = mdualize incid\<close>
  defines ddPdef: "ddPoints \<equiv> dLines"
  defines ddLdef: "ddLines \<equiv> dPoints"
  fixes ddincid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes ddm: \<open>ddincid = mdualize dincid\<close>
  shows "\<exists>(f::('p \<Rightarrow> 'p)). (bij_betw f Points ddPoints) 
    \<and> (\<forall>A B C. (projective_plane_data.pcollinear Points Lines incid A B C) 
    \<longrightarrow> (projective_plane_data.pcollinear ddPoints ddLines ddincid (f A) (f B) (f C)))" 
proof -
  obtain f::"'p \<Rightarrow> 'p" where fdef: "f P = P" for P by simp
  then have fbij: "bij_betw f Points ddPoints" using assms by (simp add: bij_betwI')
  have "\<forall>A B C. (projective_plane_data.pcollinear Points Lines incid A B C) 
    \<longrightarrow> (projective_plane_data.pcollinear ddPoints ddLines ddincid (f A) (f B) (f C))"
    using assms fdef projective_plane_data.pcollinear_def [of Points Lines] by auto
  then show ?thesis using fbij by auto
qed
text \<open>\done\<close>
end