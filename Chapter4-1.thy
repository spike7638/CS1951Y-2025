theory "Chapter4-1"
  imports Complex_Main "Chapter1-1"

begin
text \<open>Everything up to the Principle of Duality and the remarks after it. 
(You don't need to prove remark 2!)\<close>

fun mdualize :: "('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('l \<Rightarrow> ('l set \<times> 'p) \<Rightarrow> bool)" 
  where "mdualize (incid) (l::'l) (_, P) = incid P l"

text \<open>\hadi\<close>
lemma dp_p1:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane2 Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> {({n::'l . (n \<in> Lines) \<and> incid P n}, P) | P. (P \<in> Points)}"
  fixes dincid :: "'l \<Rightarrow> ('l set \<times> 'p) \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  fixes P Q
  assumes pq_facts: "P \<noteq> Q \<and> P \<in> dPoints \<and> Q \<in> dPoints"
  shows "\<exists>!k. k \<in> dLines \<and> P d\<lhd> k \<and> Q d\<lhd> k"
proof -
  obtain R where rdef: "R \<in> Points \<and> incid R P \<and> incid R Q" 
    using pq_facts pp projective_plane2.p2 unfolding dPdef by fastforce
  then have runique: "\<lbrakk>S \<in> Points; incid S P; incid S Q\<rbrakk> \<Longrightarrow> R = S" for S 
    using pq_facts pp projective_plane2.p1 unfolding dPdef by fastforce
  let ?k = "({n::'l . (n \<in> Lines) \<and> incid R n}, R)"
  have k_facts: "?k \<in> dLines \<and> P d\<lhd> ?k \<and> Q d\<lhd> ?k" using rdef dm dLdef by auto
  have "\<lbrakk>n \<in> dLines; P d\<lhd> n \<and> Q d\<lhd> n\<rbrakk> \<Longrightarrow> ?k = n" for n using dLdef dm runique by auto
  then show ?thesis using k_facts by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma dp_p2:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane2 Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> {({n::'l . (n \<in> Lines) \<and> incid P n}, P) | P. (P \<in> Points)}"
  fixes dincid :: "'l \<Rightarrow> ('l set \<times> 'p) \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  fixes k n
  assumes kn_facts: "k \<in> dLines \<and> n \<in> dLines"
  shows "\<exists>P. (P \<in> dPoints \<and> P d\<lhd> k \<and> P d\<lhd> n)"
proof (cases "k = n")
  case 1: True
  obtain R where rdef: "R \<in> Points \<and> k = ({l::'l . (l \<in> Lines) \<and> incid R l}, R)" 
    using dLdef kn_facts by auto
  then obtain m where "m \<in> Lines \<and> incid R m" 
    using pp projective_plane2_def by (metis (lifting))
  then show ?thesis using 1 rdef dm dPdef by auto
next
  case False
  then obtain P Q where pqdef: "P \<in> Points \<and> Q \<in> Points \<and> P \<noteq> Q 
    \<and> k = ({l::'l . (l \<in> Lines) \<and> incid P l}, P) 
    \<and> n = ({l::'l . (l \<in> Lines) \<and> incid Q l}, Q)" using dLdef kn_facts by auto
  obtain m where "m \<in> Lines \<and> incid P m \<and> incid Q m" 
    using pqdef pp projective_plane2.p1 by fastforce
  then show ?thesis using pqdef dm dPdef by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma dp_p3:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane2 Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> {({n::'l . (n \<in> Lines) \<and> incid P n}, P) | P. (P \<in> Points)}"
  fixes dincid :: "'l \<Rightarrow> ('l set \<times> 'p) \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  shows "\<exists>P Q R. P \<in> dPoints \<and> Q \<in> dPoints \<and> R \<in> dPoints \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R 
    \<and> \<not> (projective_plane_data2.pcollinear dPoints dLines dincid P Q R)"
proof -
  obtain P Q R where pqr: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R 
    \<and> Q \<noteq> R \<and> \<not> (projective_plane_data2.pcollinear Points Lines incid P Q R)" 
    using pp projective_plane2.p3 by blast
  then obtain pq where pqdef: "pq \<in> Lines \<and> incid P pq \<and> incid Q pq" 
    using pp projective_plane2.p1 [of Points Lines incid P Q] by auto
  obtain qr where qrdef: "qr \<in> Lines \<and> incid Q qr \<and> incid R qr" 
    using pqr pp projective_plane2.p1 [of Points Lines incid Q R] by auto
  obtain pr where prdef: "pr \<in> Lines \<and> incid P pr \<and> incid R pr" 
    using pqr pp projective_plane2.p1 [of Points Lines incid P R] by auto
  have alldp: "pq \<in> dPoints \<and> qr \<in> dPoints \<and> pr \<in> dPoints" 
    using pqdef qrdef prdef dPdef by auto
  have alldist: "pq \<noteq> qr \<and> pq \<noteq> pr \<and> qr \<noteq> pr" using pqr pqdef qrdef prdef 
    projective_plane_data2.pcollinear_def by fastforce
  have "\<not> (incid Q pr)" using pqr prdef 
    projective_plane_data2.pcollinear_def [of Points Lines] by auto
  then have prnot: "\<not> pr d\<lhd> ({m::'l. (m \<in> Lines) \<and> incid Q m}, Q)" using dm by auto
  have "\<not> (projective_plane_data2.pcollinear dPoints dLines dincid pq qr pr)"
  proof (rule ccontr)
    assume cd: "\<not> (\<not> (projective_plane_data2.pcollinear dPoints dLines dincid pq qr pr))"
    show False
    proof -
      obtain L where ldef: "L \<in> dLines \<and> pq d\<lhd> L \<and> qr d\<lhd> L \<and> pr d\<lhd> L" using cd 
        alldp projective_plane_data2.pcollinear_def [of dPoints dLines] by auto
      obtain G where gdef: "G \<in> Points \<and> L = ({m::'l. (m \<in> Lines) \<and> incid G m}, G)" 
        using dLdef ldef by auto
      then have "G = Q" using alldist pqr ldef pqdef qrdef dm mdualize.simps
        pp projective_plane2.p1 [of _ _ incid] by (metis (lifting))
      then show False using gdef ldef prnot by blast
    qed
  qed
  then show ?thesis using alldist alldp by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma (in projective_plane2) non_containing_line:
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
  assumes pp: "projective_plane2 Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> {({n::'l . (n \<in> Lines) \<and> incid P n}, P) | P. (P \<in> Points)}"
  fixes dincid :: "'l \<Rightarrow> ('l set \<times> 'p) \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  fixes k U
  assumes ku_facts: "k \<in> dLines \<and> U = {P. (P \<in> dPoints \<and> P d\<lhd> k)}"
  shows "\<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
proof -
  obtain P where sdef: "P \<in> Points \<and> k = ({n::'l. (n \<in> Lines) \<and> incid P n}, P)"
    using ku_facts dLdef by auto
  obtain l where ldef: "l \<in> Lines \<and> (\<not> incid P l)" using sdef pp
    projective_plane2.non_containing_line by metis
  obtain A B C where abcdef: "A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> incid A l \<and> incid B l \<and> incid C l \<and> distinct[A, B, C]" 
    using ldef pp projective_plane2.p4 [of Points Lines incid l] by auto
  then obtain Q R S where "Q \<in> Lines \<and> R \<in> Lines \<and> S \<in> Lines \<and> incid P Q 
    \<and> incid A Q \<and> incid P R \<and> incid B R \<and> incid P S \<and> incid C S \<and> distinct[Q, R, S]" 
    using sdef ldef distinct_length_2_or_more distinct_singleton pp
    projective_plane2.p1 [of Points Lines incid P]
    projective_plane2.p1 [of Points Lines _ A B]
    projective_plane2.p1 [of Points Lines _ A C]
    projective_plane2.p1 [of Points Lines _ B C] by (metis (lifting))
  then show ?thesis using sdef dm ku_facts dPdef by auto
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
theorem dual_plane_is_projective:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane2 Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> {({n::'l . (n \<in> Lines) \<and> incid P n}, P) | P. (P \<in> Points)}"
  fixes dincid :: "'l \<Rightarrow> ('l set \<times> 'p) \<Rightarrow> bool" (infix "d\<lhd>" 60)
  assumes dm: \<open>dincid = mdualize incid\<close>
  shows "projective_plane2 dPoints dLines dincid"
proof (unfold_locales)
  show "\<lbrakk>P \<noteq> Q; P \<in> dPoints; Q \<in> dPoints\<rbrakk> 
    \<Longrightarrow> (\<exists>!k. k \<in> dLines \<and> P d\<lhd> k \<and> Q d\<lhd> k)" for P Q 
    using assms dp_p1 [of Points Lines] by simp
  show "\<lbrakk>k \<in> dLines; n \<in> dLines\<rbrakk> 
    \<Longrightarrow> \<exists>P. (P \<in> dPoints \<and> P d\<lhd> k \<and> P d\<lhd> n)" for k n 
    using assms dp_p2 [of Points Lines] by simp
  show "\<exists>P Q R. P \<in> dPoints \<and> Q \<in> dPoints \<and> R \<in> dPoints 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R  
    \<and> \<not> (projective_plane_data2.pcollinear dPoints dLines dincid P Q R)"
    using assms dp_p3 [of Points Lines] by simp
  show "\<lbrakk>k \<in> dLines; U = {P. (P \<in> dPoints \<and> P d\<lhd> k)}\<rbrakk> 
    \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]" for k U
    using assms dp_p4 [of Points Lines] by simp
qed
text \<open>\done\<close>
end