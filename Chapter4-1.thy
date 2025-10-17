theory "Chapter4-1"
  imports Complex_Main "Chapter1-1"

begin
text \<open>Everything up to the Principle of Duality and the remarks after it. 
(You don't need to prove remark 2!)\<close>

fun mdualize :: "('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('l \<Rightarrow> 'p \<Rightarrow> bool)" 
  where "mdualize (incid) (l::'l) (P::'p) = incid P l"

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
    using pq_facts pp projective_plane.p2 unfolding dPdef by fastforce
  then have "\<lbrakk>S \<in> Points; incid S P; incid S Q\<rbrakk> \<Longrightarrow> R = S" for S 
    using pq_facts pp projective_plane.p1 unfolding dPdef by fastforce
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
    using kn_facts pp projective_plane_def dLdef by (metis (lifting))
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
    projective_plane_data.pcollinear_def by fastforce
  have qnot: "\<not> (incid Q pr)" using pqr prdef 
    projective_plane_data.pcollinear_def [of Points Lines] by auto
  have "\<not> (projective_plane_data.pcollinear dPoints dLines dincid pq qr pr)"
  proof (rule ccontr)
    assume cd: "\<not> (\<not> (projective_plane_data.pcollinear dPoints dLines dincid pq qr pr))"
    show False
    proof -
      obtain L where ldef: "L \<in> dLines \<and> pq d\<lhd> L \<and> qr d\<lhd> L \<and> pr d\<lhd> L" using cd 
        alldp projective_plane_data.pcollinear_def [of dPoints dLines] by auto
      then have "L = Q" using pp projective_plane.p1 [of Points Lines incid] 
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
  using assms p1 p1 [of P] p3 pcollinear_def by metis
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
    projective_plane.non_containing_line dLdef by metis
  obtain A B C where "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> incid A l \<and> incid B l \<and> incid C l \<and> distinct[A, B, C]" 
    using ldef pp projective_plane.p4 [of Points Lines incid l] by auto
  then obtain Q R S where "Q \<in> Lines \<and> R \<in> Lines \<and> S \<in> Lines \<and> incid k Q 
    \<and> incid A Q \<and> incid k R \<and> incid B R \<and> incid k S \<and> incid C S \<and> distinct[Q, R, S]" 
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

definition proj_statement :: "('p set) \<Rightarrow> ('l set) \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool" where
  "proj_statement Points Lines incid = projective_plane Points Lines incid"

lift_definition dual_statement :: "('l set) \<Rightarrow> ('p set) \<Rightarrow> ('l \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> bool"
  is "\<lambda>Points Lines incid. proj_statement Lines Points (mdualize incid)" .

text \<open>\hadi\<close>
theorem principle_of_duality:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes "proj_statement Points Lines incid"
  shows "dual_statement Points Lines incid"
  using assms dual_plane_is_projective dual_statement.transfer proj_statement_def by metis
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
  shows "Points = ddPoints \<and> Lines = ddLines \<and> incid = ddincid" 
  using assms by fastforce
text \<open>\done\<close>
end