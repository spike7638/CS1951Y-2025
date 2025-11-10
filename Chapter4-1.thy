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
lemma mmi_eq: "incid = (mdualize (mdualize incid))" by fastforce
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
  assumes dm: "dincid = mdualize incid"
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
  assumes dm: "dincid = mdualize incid"
  fixes k n
  assumes kn_facts: "k \<in> dLines \<and> n \<in> dLines"
  shows "\<exists>P. (P \<in> dPoints \<and> P d\<lhd> k \<and> P d\<lhd> n)"
proof -
  obtain m where "m \<in> Lines \<and> incid k m \<and> incid n m" 
    using kn_facts dLdef pp unfolding projective_plane_def by metis
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
  assumes dm: "dincid = mdualize incid"
  shows "\<exists>P Q R. P \<in> dPoints \<and> Q \<in> dPoints \<and> R \<in> dPoints \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R 
    \<and> \<not> (projective_plane_data.pcollinear dPoints dLines dincid P Q R)"
proof -
  obtain P Q R where pqr: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R 
    \<and> Q \<noteq> R \<and> \<not> (projective_plane_data.pcollinear Points Lines incid P Q R)" 
    using pp projective_plane.p3 [of Points Lines incid] by auto
  then obtain pq qr pr where pqdef: "pq \<in> Lines \<and> incid P pq \<and> incid Q pq" 
    and qrdef: "qr \<in> Lines \<and> incid Q qr \<and> incid R qr"
    and prdef: "pr \<in> Lines \<and> incid P pr \<and> incid R pr"
    using pp projective_plane.p1 [of _ _ incid] by meson
  then have alldp: "pq \<in> dPoints \<and> qr \<in> dPoints \<and> pr \<in> dPoints" using dPdef by auto
  have alldist: "pq \<noteq> qr \<and> pq \<noteq> pr \<and> qr \<noteq> pr" 
    and qnot: "\<not> (incid Q pr)" using pqr pqdef qrdef prdef 
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
  assumes dm: "dincid = mdualize incid"
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
  assumes dm: "dincid = mdualize incid"
  shows "projective_plane dPoints dLines dincid"
proof (unfold_locales)
  show "\<lbrakk>P \<noteq> Q; P \<in> dPoints; Q \<in> dPoints\<rbrakk> 
    \<Longrightarrow> (\<exists>!k. k \<in> dLines \<and> P d\<lhd> k \<and> Q d\<lhd> k)" for P Q
    using assms dp_p1 [of _ _ incid] by simp
  show "\<lbrakk>k \<in> dLines; n \<in> dLines\<rbrakk> 
    \<Longrightarrow> \<exists>P. (P \<in> dPoints \<and> P d\<lhd> k \<and> P d\<lhd> n)" for k n
    using assms dp_p2 [of _ _ incid] by simp
  show "\<exists>P Q R. P \<in> dPoints \<and> Q \<in> dPoints \<and> R \<in> dPoints 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R 
    \<and> \<not> (projective_plane_data.pcollinear dPoints dLines dincid P Q R)"
    using assms dp_p3 [of _ _ incid] by simp
  show "\<lbrakk>k \<in> dLines; U = {P. (P \<in> dPoints \<and> P d\<lhd> k)}\<rbrakk> 
    \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]" for k U
    using assms dp_p4 [of _ _ incid] by simp
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma dual_meet_is_join:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool"
  assumes dm: "dincid = mdualize incid"
  fixes n k
  shows "projective_plane_data.meet dPoints dLines dincid n k 
    = projective_plane_data.join Points Lines incid n k"
  using dm dLdef dPdef unfolding projective_plane_data.meet_def 
    projective_plane_data.join_def by auto
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma dual_join_is_meet:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool"
  assumes dm: "dincid = mdualize incid"
  fixes P Q
  shows "projective_plane_data.join dPoints dLines dincid P Q 
    = projective_plane_data.meet Points Lines incid P Q"
  using dm dLdef dPdef unfolding projective_plane_data.meet_def 
    projective_plane_data.join_def by auto
text \<open>\done\<close>

text \<open>\hadi\<close>
definition desarguesian :: "('p set) \<Rightarrow> ('l set) \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool" where
  "desarguesian Points Lines incid \<equiv> (projective_plane Points Lines incid) 
    \<and> (\<forall>M A B C A' B' C'. distinct[M,A,B,C,A',B',C'] \<and> M \<in> Points \<and> A \<in> Points 
      \<and> B \<in> Points \<and> C \<in> Points \<and> A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points 
      \<and> projective_plane_data.pcollinear Points Lines incid M A A'
      \<and> projective_plane_data.pcollinear Points Lines incid M B B'
      \<and> projective_plane_data.pcollinear Points Lines incid M C C'
      \<and> (\<not> projective_plane_data.pcollinear Points Lines incid A B C) 
      \<and> (\<not> projective_plane_data.pcollinear Points Lines incid A' B' C')
      \<and> (distinct[(projective_plane_data.join Points Lines incid A A'),
          (projective_plane_data.join Points Lines incid B B'),
          (projective_plane_data.join Points Lines incid C C')])
      \<longrightarrow> (projective_plane_data.pcollinear Points Lines incid 
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid A B)
          (projective_plane_data.join Points Lines incid A' B'))
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid A C)
          (projective_plane_data.join Points Lines incid A' C'))
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid B C)
          (projective_plane_data.join Points Lines incid B' C'))))"
text \<open>\done\<close>

text \<open>\hadi\<close>
theorem dual_plane_is_desarguesian:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes dsp: "desarguesian Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool"
  assumes dm: "dincid = mdualize incid"
  shows "desarguesian dPoints dLines dincid" unfolding desarguesian_def 
proof
  show dualp: "projective_plane dPoints dLines dincid" 
    using assms dual_plane_is_projective unfolding desarguesian_def by auto
  show "\<forall>M A B C A' B' C'. distinct[M,A,B,C,A',B',C'] \<and> M \<in> dPoints 
    \<and> A \<in> dPoints \<and> B \<in> dPoints \<and> C \<in> dPoints 
    \<and> A' \<in> dPoints \<and> B' \<in> dPoints \<and> C' \<in> dPoints 
    \<and> projective_plane_data.pcollinear dPoints dLines dincid M A A'
    \<and> projective_plane_data.pcollinear dPoints dLines dincid M B B'
    \<and> projective_plane_data.pcollinear dPoints dLines dincid M C C'
    \<and> (\<not> projective_plane_data.pcollinear dPoints dLines dincid A B C) 
    \<and> (\<not> projective_plane_data.pcollinear dPoints dLines dincid A' B' C')
    \<and> (distinct[(projective_plane_data.join dPoints dLines dincid A A'),
        (projective_plane_data.join dPoints dLines dincid B B'),
        (projective_plane_data.join dPoints dLines dincid C C')])
    \<longrightarrow> projective_plane_data.pcollinear dPoints dLines dincid 
      (projective_plane_data.meet dPoints dLines dincid 
        (projective_plane_data.join dPoints dLines dincid A B)
        (projective_plane_data.join dPoints dLines dincid A' B'))
      (projective_plane_data.meet dPoints dLines dincid 
        (projective_plane_data.join dPoints dLines dincid A C)
        (projective_plane_data.join dPoints dLines dincid A' C'))
      (projective_plane_data.meet dPoints dLines dincid 
        (projective_plane_data.join dPoints dLines dincid B C)
        (projective_plane_data.join dPoints dLines dincid B' C'))"
  proof (clarify)
    fix M A B C A' B' C'
    assume alldist: "distinct[M,A,B,C,A',B',C']"
    and m:"M \<in> dPoints" and a:"A \<in> dPoints" and b:"B \<in> dPoints" and c:"C \<in> dPoints"
    and a':"A' \<in> dPoints" and b':"B' \<in> dPoints" and c':"C' \<in> dPoints" 
    and maa': "projective_plane_data.pcollinear dPoints dLines dincid M A A'"
    and mbb': "projective_plane_data.pcollinear dPoints dLines dincid M B B'"
    and mcc': "projective_plane_data.pcollinear dPoints dLines dincid M C C'"
    and abc: "\<not> projective_plane_data.pcollinear dPoints dLines dincid A B C"
    and a'b'c': "\<not> projective_plane_data.pcollinear dPoints dLines dincid A' B' C'"
    and aa'bb'cc': "(distinct[(projective_plane_data.join dPoints dLines dincid A A'),
      (projective_plane_data.join dPoints dLines dincid B B'),
      (projective_plane_data.join dPoints dLines dincid C C')])"
    let ?P = "(projective_plane_data.meet dPoints dLines dincid 
      (projective_plane_data.join dPoints dLines dincid A B)
      (projective_plane_data.join dPoints dLines dincid A' B'))"
    let ?Q = "(projective_plane_data.meet dPoints dLines dincid 
      (projective_plane_data.join dPoints dLines dincid A C)
      (projective_plane_data.join dPoints dLines dincid A' C'))"
    let ?R = "(projective_plane_data.meet dPoints dLines dincid 
      (projective_plane_data.join dPoints dLines dincid B C)
      (projective_plane_data.join dPoints dLines dincid B' C'))"
    show "projective_plane_data.pcollinear dPoints dLines dincid ?P ?Q ?R"
    proof -
      have pdef: "?P \<in> dPoints" and qdef: "?Q \<in> dPoints" and rdef: "?R \<in> dPoints"
        using alldist a a' b b' c c' aa'bb'cc' dualp distinct_length_2_or_more
        projective_plane.join_properties1 [of dPoints dLines dincid]
        projective_plane.join_properties2 [of dPoints dLines dincid]
        projective_plane.meet_properties2 by metis+
      obtain M0 A0 A'0 where m0: "M0 \<in> Points \<and> incid M0 M \<and> incid M0 A \<and> incid M0 A'" 
        and a0: "A0 \<in> Points \<and> incid A0 M \<and> incid A0 B \<and> incid A0 B'"
        and a'0: "A'0 \<in> Points \<and> incid A'0 M \<and> incid A'0 C \<and> incid A'0 C'" 
        using m a b c a' b' c' maa' mbb' mcc' dLdef dm 
        unfolding projective_plane_data.pcollinear_def by auto
      obtain B0 B'0 where b0: "B0 \<in> Points \<and> incid B0 A \<and> incid B0 B" 
        and b'0: "B'0 \<in> Points \<and> incid B'0 A \<and> incid B'0 C" 
        using a b c dLdef dm dualp mdualize.elims(2) projective_plane.p3 
        projective_plane.p1 [of _ _ dincid] by (metis (full_types))
      obtain C0 C'0 where c0: "C0 \<in> Points \<and> incid C0 A' \<and> incid C0 B'" 
        and c'0: "C'0 \<in> Points \<and> incid C'0 A' \<and> incid C'0 C'" 
        using a' b' c' dLdef dm dualp mdualize.elims(2) projective_plane.p3
        projective_plane.p1 [of _ _ dincid] by (metis (full_types))
      have allp: "M0 \<in> Points \<and> A0 \<in> Points \<and> B0 \<in> Points \<and> C0 \<in> Points \<and> A'0 \<in> Points 
        \<and> B'0 \<in> Points \<and> C'0 \<in> Points" using m0 a0 b0 c0 a'0 b'0 c'0 by simp
      have alldist0: "distinct[M0,A0,B0,C0,A'0,B'0,C'0]"
      proof (rule ccontr)
        assume "\<not> distinct[M0,A0,B0,C0,A'0,B'0,C'0]"
        then consider
        "B0 = B'0" | "C0 = C'0" | "M0 = A0" | "M0 = B0" | "M0 = C0" | "M0 = A'0" 
        | "M0 = B'0" | "M0 = C'0" | "A0 = B0" | "A0 = C0" | "A0 = A'0" | "A0 = B'0" 
        | "A0 = C'0" | "B0 = C0" | "B0 = A'0" | "B0 = C'0" | "C0 = A'0" | "C0 = B'0" 
        | "A'0 = B'0" | "A'0 = C'0" | "B'0 = C'0" by fastforce
        then show False using alldist m a a' b b' c c' aa'bb'cc' m0 a0 b0 a'0 b'0 dm 
        dualp dLdef projective_plane.join_properties2 [of _ _ dincid] apply cases 
        apply auto+ using abc projective_plane_data.pcollinear_def apply fastforce
        using c0 c'0 a'b'c' projective_plane_data.pcollinear_def apply fastforce
        using a'b'c' c'0 c0 abc unfolding projective_plane_data.pcollinear_def by metis+
      qed
      have b0ab: "B0 = projective_plane_data.meet Points Lines incid A B"
        and b'0ac: "B'0 = projective_plane_data.meet Points Lines incid A C"
        using a b c b b'0 b0 abc dLdef dPdef dm dsp dual_join_is_meet mdualize.elims(3) 
        dualp projective_plane.join_properties2 [of dPoints _ _ A] desarguesian_def 
        [of _ _ incid] projective_plane_data.meet_def [of _ _ incid A]
        projective_plane_data.pcollinear_def [of _ _ dincid] by (metis (lifting))+
      have m0a0a'0: " projective_plane_data.pcollinear Points Lines incid M0 A0 A'0"
        and m0b0b'0: "projective_plane_data.pcollinear Points Lines incid M0 B0 B'0"
        and m0c0c'0: "projective_plane_data.pcollinear Points Lines incid M0 C0 C'0"
        using projective_plane_data.pcollinear_def [of _ _ incid] 
         m a a' m0 a0 a'0 b0 b'0 c0 c'0 dPdef by auto
      have a0b0b: "incid A0 B \<and> incid B0 B \<and> A0 \<noteq> B0" 
        and a0c0b': "incid A0 B' \<and> incid C0 B' \<and> A0 \<noteq> C0" 
        and a'0b'0c: "incid A'0 C \<and> incid B'0 C \<and> A'0 \<noteq> B'0"
        and a'0c'0c': "incid A'0 C' \<and> incid C'0 C' \<and> A'0 \<noteq> C'0" 
        using a0 b0 c0 a'0 b'0 c'0 alldist0 by auto
      then have bj2a0b0: "B = projective_plane_data.join Points Lines incid A0 B0" 
        and b'j2a0c0: "B' = projective_plane_data.join Points Lines incid A0 C0"
        and cj2a'0b'0: "C = projective_plane_data.join Points Lines incid A'0 B'0" 
        and c'j2a'0c'0: "C' = projective_plane_data.join Points Lines incid A'0 C'0"
        using allp b b' c c' dPdef projective_plane.join_properties2 dsp 
        unfolding desarguesian_def by auto
      have a0b0c0: "\<not> projective_plane_data.pcollinear Points Lines incid A0 B0 C0"
      proof (rule ccontr)
        assume "\<not> (\<not> projective_plane_data.pcollinear Points Lines incid A0 B0 C0)"
        then obtain l1 where l1def: "l1 \<in> Lines \<and> incid A0 l1 \<and> incid B0 l1 \<and> incid C0 l1" 
          using a0 b0 c0 projective_plane_data.pcollinear_def [of _ _ incid] by auto
        then have "B' = l1" using b' a0 c0 a0c0b' dLdef dPdef dm dualp 
          projective_plane.unique_meet [of _ _ dincid] by auto
        then have "B' = B" using l1def b a0 b0 a0b0b dLdef dPdef dm dualp
          projective_plane.unique_meet [of _ _ dincid] by auto
        then show False using alldist by simp
      qed
      have a'0b'0c'0: "\<not> projective_plane_data.pcollinear Points Lines incid A'0 B'0 C'0"
      proof (rule ccontr)
        assume "\<not> (\<not> projective_plane_data.pcollinear Points Lines incid A'0 B'0 C'0)"
        then obtain l2 where l2def: "l2 \<in> Lines \<and> incid A'0 l2 \<and> incid B'0 l2 \<and> incid C'0 l2" 
          using a'0 b'0 c'0 projective_plane_data.pcollinear_def [of _ _ incid] by auto
        then have "C = l2" using c a'0 b'0 a'0b'0c dLdef dPdef dm dualp 
          projective_plane.unique_meet [of _ _ dincid] by auto
        then have "C = C'" using l2def c' a'0 c'0 a'0c'0c' dLdef dPdef dm dualp
          projective_plane.unique_meet [of _ _ dincid] by auto
        then show False using alldist by simp
      qed
      have a0ma'0m: "incid A0 M \<and> incid A'0 M \<and> A0 \<noteq> A'0"
        and b0ab'0a: "incid B0 A \<and> incid B'0 A \<and> B0 \<noteq> B'0" 
        and "incid C0 A' \<and> incid C'0 A' \<and> C0 \<noteq> C'0"
        using a0 b0 c0 a'0 b'0 c'0 alldist0 by simp+
      then have "M = (projective_plane_data.join Points Lines incid A0 A'0)" 
        and "A = (projective_plane_data.join Points Lines incid B0 B'0)"
        and "A' = (projective_plane_data.join Points Lines incid C0 C'0)"
        using m a a' a0 b0 c0 a'0 b'0 c'0 dLdef dPdef dm dualp mmi_eq
        dual_plane_is_projective projective_plane.join_properties2 by metis+
      then have a0a'0b0b'0c0c'0: 
        "(distinct[(projective_plane_data.join Points Lines incid A0 A'0),
          (projective_plane_data.join Points Lines incid B0 B'0),
          (projective_plane_data.join Points Lines incid C0 C'0)])" 
        using alldist by auto
      let ?P' = "(projective_plane_data.meet Points Lines incid 
        (projective_plane_data.join Points Lines incid A0 B0)
        (projective_plane_data.join Points Lines incid A'0 B'0))"
      let ?Q' = "(projective_plane_data.meet Points Lines incid 
        (projective_plane_data.join Points Lines incid A0 C0)
        (projective_plane_data.join Points Lines incid A'0 C'0))"
      let ?R' = "(projective_plane_data.meet Points Lines incid 
        (projective_plane_data.join Points Lines incid B0 C0)
        (projective_plane_data.join Points Lines incid B'0 C'0))"
      have p'q'r': "projective_plane_data.pcollinear Points Lines incid ?P' ?Q' ?R'"
        using alldist0 dsp allp m0a0a'0 m0b0b'0 m0c0c'0 a0b0c0 a'0b'0c'0 a0a'0b0b'0c0c'0
        unfolding desarguesian_def projective_plane_data.pcollinear_def by blast
      have "?P' = projective_plane_data.meet Points Lines incid B C" 
        using bj2a0b0 cj2a'0b'0 by auto
      then have p'bc: "?P' = projective_plane_data.join dPoints dLines dincid B C"
        using dm dsp dPdef dLdef dual_join_is_meet [of _ _ incid _ B C] 
        unfolding desarguesian_def by auto
      have "?Q' = projective_plane_data.meet Points Lines incid B' C'" 
        using b'j2a0c0 c'j2a'0c'0 by auto
      then have q'b'c': "?Q' = projective_plane_data.join dPoints dLines dincid B' C'"
        using dm dsp dPdef dLdef dual_join_is_meet [of _ _ incid _ B' C'] 
        unfolding desarguesian_def by auto
      have "?R' = projective_plane_data.meet Points Lines incid ?P ?Q" 
        using alldist a a' b b' c c' b0 c0 b'0 c'0 dLdef dPdef dual_meet_is_join 
        [of _ _ incid _ B0 C0] dual_meet_is_join [of _ _ incid _ B'0 C'0]
        dm dsp dualp projective_plane.join_properties2 [of _ _ dincid] 
        unfolding desarguesian_def [of _ _ incid] by auto
      then have r'pq: "?R' = projective_plane_data.join dPoints dLines dincid ?P ?Q"
        using dm dsp dPdef dLdef dual_join_is_meet [of _ _ incid] 
        unfolding desarguesian_def by auto
      have p'def: "?P' \<in> Points" and q'def: "?Q' \<in> Points"
        using alldist projective_plane.join_properties1 [of _ _ dincid] 
        b c b' c' p'bc q'b'c' b'0ac b0ab b0ab'0a dLdef dualp by auto
      have r'def: "?R' \<in> Points" using b0 c0 b'0 c'0 a0a'0b0b'0c0c'0 alldist0 
        distinct_length_2_or_more dsp projective_plane.join_properties1 
        [of _ _ incid] projective_plane.join_properties2 [of Points _ incid] 
        projective_plane.meet_properties2 unfolding desarguesian_def by metis
      have p'nq': "?P' \<noteq> ?Q'" using b c b' c' a0 a'0 a0ma'0m p'bc q'b'c' 
        alldist distinct_length_2_or_more dLdef dm dualp mdualize.elims(3) 
        projective_plane.unique_meet [of _ _ dincid] 
        projective_plane.join_properties1 by metis
      have "?R = projective_plane_data.meet dPoints dLines dincid ?P' ?Q'"
        using p'bc q'b'c' by auto
      then have "?R = projective_plane_data.join Points Lines incid ?P' ?Q'"
        using dLdef dPdef dm unfolding projective_plane_data.join_def
        projective_plane_data.meet_def by simp
      obtain S where "S \<in> Lines \<and> incid ?P' S \<and> incid ?Q' S \<and> incid ?R' S"
        using p'q'r' p'def q'def r'def 
        unfolding projective_plane_data.pcollinear_def by auto
      then have p'q'r's: "S \<in> dPoints \<and> dincid S ?P' \<and> dincid S ?Q' \<and> dincid S ?R'"
        using dPdef dm by simp
      then have "S = ?R" using p'def q'def p'bc q'b'c' p'nq' dLdef dualp 
        projective_plane.meet_properties2 [of _ _ dincid] 
        projective_plane.unique_meet [of _ _ dincid] by simp
      then have rr': "dincid ?R ?R'" using p'q'r's by simp
      have "?P \<noteq> ?Q" using a b c a' b' c' alldist b0 c0 b'0 c'0 alldist0 dLdef dm
        projective_plane.join_properties2 [of dPoints dLines dincid A B] 
        projective_plane.join_properties2 [of dPoints dLines dincid A C] 
        projective_plane.join_properties2 [of dPoints dLines dincid A'] 
        projective_plane.meet_properties2 [of dPoints dLines dincid C0 B0] 
        projective_plane.meet_properties2 [of dPoints dLines dincid C'0 B'0] 
        dualp distinct_length_2_or_more mdualize.elims(3) by (metis (full_types))
      then have "dincid ?P ?R' \<and> dincid ?Q ?R'" using pdef qdef r'pq dualp 
        projective_plane.join_properties1 [of _ _ dincid] by simp
      then show ?thesis unfolding projective_plane_data.pcollinear_def
        using pdef qdef rdef rr' r'def dLdef by auto
    qed
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma principle_of_duality_example:
  fixes Points :: "'a set"
  fixes Lines :: "'a set"
  fixes incid :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  (* join_properties2: "\<forall>P Q k. P \<in> Points \<and> Q \<in> Points \<and> P \<noteq> Q 
    \<and> k \<in> Lines \<and> incid P k \<and> incid Q k 
    \<longrightarrow> k = projective_plane_data.join Points Lines incid P Q" *)
  shows "\<forall>P Q k. P \<in> Lines \<and> Q \<in> Lines \<and> P \<noteq> Q \<and> k \<in> Points 
    \<and> (mdualize incid) P k \<and> (mdualize incid) Q k 
    \<longrightarrow> k = projective_plane_data.join Lines Points (mdualize incid) P Q" 
  using pp projective_plane.join_properties2 [of _ _ "mdualize incid"] 
    dual_plane_is_projective [of _ _ incid] by simp
text \<open>\done\<close>

text \<open>\hadi\<close>
theorem double_dual_isomorphic:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes pp: "projective_plane Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool"
  assumes dm: "dincid = mdualize incid"
  defines ddPdef: "ddPoints \<equiv> dLines"
  defines ddLdef: "ddLines \<equiv> dPoints"
  fixes ddincid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes ddm: "ddincid = mdualize dincid"
  shows "\<exists>(f::('p \<Rightarrow> 'p)). (bij_betw f Points ddPoints) 
    \<and> (\<forall>A B C. (projective_plane_data.pcollinear Points Lines incid A B C) 
    \<longrightarrow> (projective_plane_data.pcollinear ddPoints ddLines ddincid (f A) (f B) (f C)))" 
proof -
  obtain f::"'p \<Rightarrow> 'p" where fdef: "f P = P" for P by simp
  then have fbij: "bij_betw f Points ddPoints" using dLdef ddPdef bij_betwI' [of _ f] by simp
  have "\<forall>A B C. (projective_plane_data.pcollinear Points Lines incid A B C) 
    \<longrightarrow> (projective_plane_data.pcollinear ddPoints ddLines ddincid (f A) (f B) (f C))"
    using assms fdef projective_plane_data.pcollinear_def [of Points Lines] by simp
  then show ?thesis using fbij by auto
qed
text \<open>\done\<close>

(*text \<open>\hadi\<close>
definition nonfano :: "('p set) \<Rightarrow> ('l set) \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool" where
  "nonfano Points Lines incid \<equiv> projective_plane Points Lines incid
    \<and> (\<forall>A B C D. distinct[A,B,C,D] 
    \<and> A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points
    \<and> \<not> projective_plane_data.pcollinear Points Lines incid A B C 
    \<and> \<not> projective_plane_data.pcollinear Points Lines incid A B D
    \<and> \<not> projective_plane_data.pcollinear Points Lines incid A C D
    \<and> \<not> projective_plane_data.pcollinear Points Lines incid B C D
    \<longrightarrow> (\<not> projective_plane_data.pcollinear Points Lines incid
      (projective_plane_data.meet Points Lines incid
        (projective_plane_data.join Points Lines incid A B)
        (projective_plane_data.join Points Lines incid C D))
      (projective_plane_data.meet Points Lines incid
        (projective_plane_data.join Points Lines incid A C)
        (projective_plane_data.join Points Lines incid B D))
      (projective_plane_data.meet Points Lines incid
        (projective_plane_data.join Points Lines incid A D)
        (projective_plane_data.join Points Lines incid B C))))"
text \<open>\done\<close>

text \<open>\hadi\<close>
theorem dual_plane_is_nonfano:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes proj_fano: "nonfano Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool"
  assumes dm: "dincid = mdualize incid"
  shows "nonfano dPoints dLines dincid" unfolding nonfano_def
proof
  show dualp: "projective_plane dPoints dLines dincid" 
    using assms dual_plane_is_projective unfolding nonfano_def by auto
  show "\<forall>A B C D. distinct[A,B,C,D] 
    \<and> A \<in> dPoints \<and> B \<in> dPoints \<and> C \<in> dPoints \<and> D \<in> dPoints
    \<and> \<not> projective_plane_data.pcollinear dPoints dLines dincid A B C 
    \<and> \<not> projective_plane_data.pcollinear dPoints dLines dincid A B D
    \<and> \<not> projective_plane_data.pcollinear dPoints dLines dincid A C D
    \<and> \<not> projective_plane_data.pcollinear dPoints dLines dincid B C D
    \<longrightarrow> (\<not> projective_plane_data.pcollinear dPoints dLines dincid
      (projective_plane_data.meet dPoints dLines dincid
        (projective_plane_data.join dPoints dLines dincid A B)
        (projective_plane_data.join dPoints dLines dincid C D))
      (projective_plane_data.meet dPoints dLines dincid
        (projective_plane_data.join dPoints dLines dincid A C)
        (projective_plane_data.join dPoints dLines dincid B D))
      (projective_plane_data.meet dPoints dLines dincid
        (projective_plane_data.join dPoints dLines dincid A D)
        (projective_plane_data.join dPoints dLines dincid B C)))"
  proof (clarify)
    fix A B C D
    assume alldist: "distinct[A,B,C,D]"
    and a:"A \<in> dPoints" and b:"B \<in> dPoints" and c:"C \<in> dPoints" and d:"D \<in> dPoints"
    and abc: "\<not> projective_plane_data.pcollinear dPoints dLines dincid A B C" 
    and abd: "\<not> projective_plane_data.pcollinear dPoints dLines dincid A B D"
    and acd: "\<not> projective_plane_data.pcollinear dPoints dLines dincid A C D"
    and bcd: "\<not> projective_plane_data.pcollinear dPoints dLines dincid B C D"
    let ?P = "projective_plane_data.meet dPoints dLines dincid
      (projective_plane_data.join dPoints dLines dincid A B)
      (projective_plane_data.join dPoints dLines dincid C D)"
    let ?Q = "projective_plane_data.meet dPoints dLines dincid
      (projective_plane_data.join dPoints dLines dincid A C)
      (projective_plane_data.join dPoints dLines dincid B D)"
    let ?R = "projective_plane_data.meet dPoints dLines dincid
      (projective_plane_data.join dPoints dLines dincid A D)
      (projective_plane_data.join dPoints dLines dincid B C)"
    show "projective_plane_data.pcollinear dPoints dLines dincid ?P ?Q ?R \<Longrightarrow> False"
    proof -
      assume pqr: "projective_plane_data.pcollinear dPoints dLines dincid ?P ?Q ?R"
      obtain A0 B0 C0 D0 where a0: "A0 \<in> Points \<and> incid A0 B \<and> incid A0 D"
        and b0: "B0 \<in> Points \<and> incid B0 C \<and> incid B0 D"
        and c0: "C0 \<in> Points \<and> incid C0 A \<and> incid C0 B"
        and d0: "D0 \<in> Points \<and> incid D0 A \<and> incid D0 C"
        using a b c d dm dualp dp_p2 [of _ _ dincid] mmi_eq dLdef by fastforce+
      have alldist0: "distinct[A0,B0,C0,D0]" using a b c d abc abd acd bcd a0 b0 c0 d0 
        dLdef dm projective_plane_data.pcollinear_def [of _ _ dincid] by fastforce
      have a0b0c0: "\<not> projective_plane_data.pcollinear Points Lines incid A0 B0 C0" 
        and a0b0d0: "\<not> projective_plane_data.pcollinear Points Lines incid A0 B0 D0" 
        and a0c0d0: "\<not> projective_plane_data.pcollinear Points Lines incid A0 C0 D0" 
        and b0c0d0: "\<not> projective_plane_data.pcollinear Points Lines incid B0 C0 D0" 
        using a b c d alldist a0 b0 c0 d0 alldist0 dPdef dLdef dm dualp mmi_eq
          dual_plane_is_projective distinct_length_2_or_more 
          projective_plane.unique_meet [of _ _ incid] unfolding 
          projective_plane_data.pcollinear_def by metis+
      let ?P0 = "projective_plane_data.meet Points Lines incid
        (projective_plane_data.join Points Lines incid A0 B0)
        (projective_plane_data.join Points Lines incid C0 D0)"
      let ?Q0 = "projective_plane_data.meet Points Lines incid
        (projective_plane_data.join Points Lines incid A0 C0)
        (projective_plane_data.join Points Lines incid B0 D0)"
      let ?R0 = "projective_plane_data.meet Points Lines incid
        (projective_plane_data.join Points Lines incid A0 D0)
        (projective_plane_data.join Points Lines incid B0 C0)"
      have p0q0r0: "\<not> projective_plane_data.pcollinear Points Lines incid ?P0 ?Q0 ?R0"
        using a0 b0 c0 d0 alldist0 a0b0c0 a0b0d0 a0c0d0 b0c0d0 proj_fano
        unfolding nonfano_def by simp
      have da0b0: "D = projective_plane_data.join Points Lines incid A0 B0" 
        and ac0d0: "A = projective_plane_data.join Points Lines incid C0 D0"
        and ba0c0: "B = projective_plane_data.join Points Lines incid A0 C0"
        and cb0d0: "C = projective_plane_data.join Points Lines incid B0 D0"
        using a b c d a0 b0 c0 d0 alldist0 dLdef dPdef dm dualp dual_plane_is_projective
          mmi_eq distinct_length_2_or_more projective_plane.join_properties2 by metis+
      
      have "projective_plane_data.pcollinear Points Lines incid ?P0 ?Q0 ?R0" sorry
      then show False using p0q0r0 by simp
    qed
  qed
qed
text \<open>\done\<close>*)
end