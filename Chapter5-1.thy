theory "Chapter5-1"
  imports "Chapter4-4"
begin

text \<open>\hadi\<close>
definition FTPL :: "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool" where
  "FTPL Points Lines incid \<equiv> (projective_plane Points Lines incid) 
    \<and> (\<forall>l \<in> Lines. (\<forall>A B C A' B' C'. 
      A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points 
    \<and> distinct3 A B C \<and> distinct3 A' B' C' 
    \<and> incid A l \<and> incid B l \<and> incid C l 
    \<and> incid A' l \<and> incid B' l \<and> incid C' l 
    \<longrightarrow> (\<exists>(f::('p \<Rightarrow> 'p)). \<exists>ps ls. 
      (f = projective_plane.projectivity Points Lines incid ps ls) 
      \<and> (hd ls = l) \<and> (last ls = l)
      \<and> (f A = A') \<and> (f B = B') \<and> (f C = C'))))"
text \<open>\done\<close>

text \<open>\hadi\<close>
definition P6 :: "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool" where
  "P6 Points Lines incid \<equiv> (projective_plane Points Lines incid) 
    \<and> (\<forall>l l' A B C A' B' C'. (l \<in> Lines \<and> l' \<in> Lines 
    \<and> A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points 
    \<and> distinct4 A B C (projective_plane_data.meet Points Lines incid l l') 
    \<and> distinct4 A' B' C' (projective_plane_data.meet Points Lines incid l l')
    \<and> incid A l \<and> incid B l \<and> incid C l 
    \<and> incid A' l' \<and> incid B' l' \<and> incid C' l')
    \<longrightarrow> (projective_plane_data.pcollinear Points Lines incid 
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid A B')
          (projective_plane_data.join Points Lines incid A' B))
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid A C')
          (projective_plane_data.join Points Lines incid A' C))
        (projective_plane_data.meet Points Lines incid 
          (projective_plane_data.join Points Lines incid B C')
          (projective_plane_data.join Points Lines incid B' C))))"
text \<open>\done\<close>

text \<open>\hadi\<close>
theorem dual_plane_is_p6:
  fixes Points :: "'p set"
  fixes Lines :: "'l set"
  fixes incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes p6p: "P6 Points Lines incid"
  defines dPdef: "dPoints \<equiv> Lines"
  defines dLdef: "dLines \<equiv> Points"
  fixes dincid :: "'l \<Rightarrow> 'p \<Rightarrow> bool"
  assumes dm: "dincid = mdualize incid"
  shows "P6 dPoints dLines dincid" unfolding P6_def
proof
  show dualp: "projective_plane dPoints dLines dincid" 
    using assms dual_plane_is_projective unfolding P6_def by auto
  show "\<forall>l l' A B C A' B' C'. (l \<in> dLines \<and> l' \<in> dLines 
    \<and> A \<in> dPoints \<and> B \<in> dPoints \<and> C \<in> dPoints 
    \<and> A' \<in> dPoints \<and> B' \<in> dPoints \<and> C' \<in> dPoints 
    \<and> distinct4 A B C (projective_plane_data.meet dPoints dLines dincid l l') 
    \<and> distinct4 A' B' C' (projective_plane_data.meet dPoints dLines dincid l l')
    \<and> dincid A l \<and> dincid B l \<and> dincid C l 
    \<and> dincid A' l' \<and> dincid B' l' \<and> dincid C' l')
    \<longrightarrow> (projective_plane_data.pcollinear dPoints dLines dincid 
        (projective_plane_data.meet dPoints dLines dincid 
          (projective_plane_data.join dPoints dLines dincid A B')
          (projective_plane_data.join dPoints dLines dincid A' B))
        (projective_plane_data.meet dPoints dLines dincid 
          (projective_plane_data.join dPoints dLines dincid A C')
          (projective_plane_data.join dPoints dLines dincid A' C))
        (projective_plane_data.meet dPoints dLines dincid 
          (projective_plane_data.join dPoints dLines dincid B C')
          (projective_plane_data.join dPoints dLines dincid B' C)))"
  proof (clarify)
    fix l l' A B C A' B' C'
    assume ll: "l \<in> dLines" and l'l: "l' \<in> dLines"
    assume a: "A \<in> dPoints" and b: "B \<in> dPoints" and c: "C \<in> dPoints" 
      and a': "A' \<in> dPoints" and b': "B' \<in> dPoints" and c': "C' \<in> dPoints"
      and abcxdist: "distinct4 A B C (projective_plane_data.meet dPoints dLines dincid l l')" 
      and a'b'c'xdist: "distinct4 A' B' C' (projective_plane_data.meet dPoints dLines dincid l l')"
      and aonl: "dincid A l" and bonl: "dincid B l" and conl: "dincid C l"
      and a'onl': "dincid A' l'" and b'onl': "dincid B' l'" and c'onl': "dincid C' l'"
    show "projective_plane_data.pcollinear dPoints dLines dincid 
      (projective_plane_data.meet dPoints dLines dincid 
        (projective_plane_data.join dPoints dLines dincid A B')
        (projective_plane_data.join dPoints dLines dincid A' B))
      (projective_plane_data.meet dPoints dLines dincid 
        (projective_plane_data.join dPoints dLines dincid A C')
        (projective_plane_data.join dPoints dLines dincid A' C))
      (projective_plane_data.meet dPoints dLines dincid 
        (projective_plane_data.join dPoints dLines dincid B C')
        (projective_plane_data.join dPoints dLines dincid B' C))"
    proof -
      show ?thesis sorry
    qed
  qed
qed
text \<open>\done\<close>

end