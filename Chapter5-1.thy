theory "Chapter5-1"
  imports "Chapter4-4jfh"
begin
text \<open>Everything up to and including Proposition 5.2\<close>

text \<open>\hadi\<close>
definition FTPL :: "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool" where
  "FTPL Points Lines incid \<equiv> (projective_plane Points Lines incid) 
    \<and> (\<forall>l \<in> Lines. (\<forall>A B C A' B' C'. 
      A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points 
    \<and> distinct3 A B C \<and> distinct3 A' B' C' 
    \<and> incid A l \<and> incid B l \<and> incid C l 
    \<and> incid A' l \<and> incid B' l \<and> incid C' l 
    \<longrightarrow> (\<exists>!(f::('p \<Rightarrow> 'p)). \<exists>! Or. \<exists>! ls. 
      (f = projective_plane.projectivity Points Lines incid ls) 
      \<and> (hd ls = (Or, l, l)) \<and> (last ls = (Or, l, l))
      \<and> (f A = A') \<and> (f B = B') \<and> (f C = C'))))"
text \<open>\done\<close>

text \<open>\hadi\<close>
definition P6 :: "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool" where
  "P6 Points Lines incid \<equiv> (projective_plane Points Lines incid) 
    \<and> (\<forall>l l' A B C A' B' C'. (l \<in> Lines \<and> l' \<in> Lines \<and> l \<noteq> l'
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
theorem dual_plane_is_P6:
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
  show "\<forall>l l' A B C A' B' C'. (l \<in> dLines \<and> l' \<in> dLines \<and> l \<noteq> l'
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
    assume ll: "l \<in> dLines" and l'l: "l' \<in> dLines" and lneql': "l \<noteq> l'"
    let ?X = "projective_plane_data.meet dPoints dLines dincid l l'"
    assume a: "A \<in> dPoints" and b: "B \<in> dPoints" and c: "C \<in> dPoints" 
      and a': "A' \<in> dPoints" and b': "B' \<in> dPoints" and c': "C' \<in> dPoints"
      and abcxdist: "distinct4 A B C ?X" and a'b'c'xdist: "distinct4 A' B' C' ?X"
      and aonl: "dincid A l" and bonl: "dincid B l" and conl: "dincid C l"
      and a'onl': "dincid A' l'" and b'onl': "dincid B' l'" and c'onl': "dincid C' l'"
    let ?P = "projective_plane_data.meet dPoints dLines dincid 
      (projective_plane_data.join dPoints dLines dincid A B')
      (projective_plane_data.join dPoints dLines dincid A' B)"
    let ?Q = "projective_plane_data.meet dPoints dLines dincid 
      (projective_plane_data.join dPoints dLines dincid A C')
      (projective_plane_data.join dPoints dLines dincid A' C)"
    let ?R = "projective_plane_data.meet dPoints dLines dincid 
      (projective_plane_data.join dPoints dLines dincid B C')
      (projective_plane_data.join dPoints dLines dincid B' C)"
    have lAC: "l = projective_plane_data.join dPoints dLines dincid A C"
      and l'A'C': "l' = projective_plane_data.join dPoints dLines dincid A' C'"
      using ll a c abcxdist aonl conl l'l a' c' a'b'c'xdist a'onl' c'onl' dualp
      projective_plane.join_properties2 unfolding distinct4_def by metis+
    have p: "?P \<in> dPoints" and q: "?Q \<in> dPoints" and r: "?R \<in> dPoints"
      using ll l'l lneql' a b c abcxdist aonl bonl conl a' b' c' a'b'c'xdist 
      a'onl' b'onl' c'onl' dualp projective_plane.meet_properties2
      projective_plane.join_properties1 projective_plane.join_properties2 
      unfolding distinct4_def by (smt (verit))+
    have bl: "B \<in> Lines" and b'l: "B' \<in> Lines" using b b' dPdef by simp+
    have bneqb': "B \<noteq> B'" using ll l'l lneql' b abcxdist bonl a'b'c'xdist b'onl'
      projective_plane.unique_meet projective_plane.meet_properties2
      dualp unfolding distinct4_def by fastforce
    let ?AO = "projective_plane_data.meet Points Lines incid B C'"
    let ?BO = l
    let ?CO = "projective_plane_data.meet Points Lines incid A' B"
    let ?A'O = "projective_plane_data.meet Points Lines incid A B'"
    let ?B'O = l'
    let ?C'O = "projective_plane_data.meet Points Lines incid B' C"
    have Opts: "?AO \<in> Points \<and> ?BO \<in> Points \<and> ?CO \<in> Points 
      \<and> ?A'O \<in> Points \<and> ?B'O \<in> Points \<and> ?C'O \<in> Points"
      using ll l'l lneql' a b c abcxdist a' b' c' a'b'c'xdist aonl bonl conl
      a'onl' b'onl' c'onl' projective_plane.join_properties2 dPdef dLdef dm
      projective_plane.meet_properties2 mdualize.simps dual_meet_is_join
      distinct4_def p6p unfolding P6_def by metis
    have aObOcOonB: "incid ?AO B \<and> incid ?BO B \<and> incid ?CO B" using bl a' c'
      bonl a'onl' c'onl' a'b'c'xdist lneql' projective_plane.meet_properties2
      dual_meet_is_join projective_plane.join_properties2 dPdef dLdef dm p6p
      mdualize.simps Opts unfolding distinct4_def P6_def by metis
    have a'Ob'Oc'OonB': "incid ?A'O B' \<and> incid ?B'O B' \<and> incid ?C'O B'" using b'l 
      a c b'onl' aonl conl a'b'c'xdist lneql' projective_plane.meet_properties2
      dual_meet_is_join projective_plane.join_properties2 dPdef dLdef dm p6p
      mdualize.simps Opts unfolding distinct4_def P6_def by metis
    let ?XO = "projective_plane_data.meet Points Lines incid B B'"
    have aObOcOxO: "distinct4 ?AO ?BO ?CO ?XO"
      using b abcxdist a' b' c' a'b'c'xdist lneql' bonl b'onl' l'A'C' Opts 
      projective_plane.join_properties1 projective_plane.meet_properties2
      projective_plane.unique_meet p6p dualp dPdef dLdef dm mdualize.simps 
      unfolding P6_def distinct4_def by (smt (z3))
    then have a'Ob'Oc'OxO: "distinct4 ?A'O ?B'O ?C'O ?XO"
      using a b c abcxdist b' bneqb' bonl lAC p6p dualp dPdef dLdef dm 
      projective_plane.join_properties2 projective_plane.meet_properties2 
      mdualize.simps unfolding P6_def distinct4_def by (smt (z3))
    let ?PO = "projective_plane_data.meet Points Lines incid 
      (projective_plane_data.join Points Lines incid ?AO ?B'O)
      (projective_plane_data.join Points Lines incid ?A'O ?BO)"
    let ?QO = "projective_plane_data.meet Points Lines incid 
      (projective_plane_data.join Points Lines incid ?AO ?C'O)
      (projective_plane_data.join Points Lines incid ?A'O ?CO)"
    let ?RO = "projective_plane_data.meet Points Lines incid 
      (projective_plane_data.join Points Lines incid ?BO ?C'O)
      (projective_plane_data.join Points Lines incid ?B'O ?CO)"
    have pO: "?PO \<in> Points" and qO: "?QO \<in> Points" and rO: "?RO \<in> Points"
      using a b c abcxdist a' b' c' a'b'c'xdist aonl conl c'onl' lneql' bneqb'
      Opts aObOcOonB a'Ob'Oc'OonB' p6p dPdef dLdef dm mdualize.elims(2)
      dual_meet_is_join projective_plane.join_properties1
      projective_plane.join_properties2 projective_plane.meet_properties2
      unfolding distinct4_def P6_def by (smt (z3))+
    have POAC': "?PO = projective_plane_data.join dPoints dLines dincid A C'"
      using a b c aObOcOxO aObOcOonB b' c' a'Ob'Oc'OonB' a'Ob'Oc'OxO aonl 
      conl c'onl' Opts p6p dual_join_is_meet projective_plane.meet_properties2
      projective_plane.join_properties2 dualp dPdef dLdef dm mdualize.simps
      unfolding P6_def distinct4_def by (smt (z3))
    have QOPR: "?QO = projective_plane_data.join dPoints dLines dincid ?P ?R"
      using p r p6p projective_plane.join_properties1 dual_join_is_meet 
      dual_meet_is_join projective_plane.join_properties2 dualp dPdef dLdef dm
      unfolding P6_def by (smt (verit, del_insts))
    have ROA'C: "?RO = projective_plane_data.join dPoints dLines dincid A' C"
      using a b c aObOcOxO aObOcOonB a' b' c' a'Ob'Oc'OxO a'Ob'Oc'OonB' a'onl'
      conl c'onl' Opts p6p dual_join_is_meet projective_plane.meet_properties2
      projective_plane.join_properties2 dualp dPdef dLdef dm mdualize.simps
      unfolding P6_def distinct4_def by (smt (z3))
    have "projective_plane_data.pcollinear Points Lines incid ?PO ?QO ?RO"
      using bl b'l bneqb' Opts aObOcOxO a'Ob'Oc'OxO aObOcOonB a'Ob'Oc'OonB' 
      p6p unfolding P6_def by auto
    then obtain k where kdef: "k \<in> Lines \<and> incid ?PO k \<and> incid ?QO k \<and> incid ?RO k"
      unfolding projective_plane_data.pcollinear_def 
      using pO qO rO p6p P6_def by auto
    then have "k = ?Q" using a b c abcxdist aObOcOxO a' c' a'b'c'xdist rO
      bonl POAC' ROA'C lAC l'A'C' dPdef dLdef dm mdualize.simps dualp mmi_eq 
      projective_plane.join_properties2 projective_plane.meet_properties2 p6p
      dual_join_is_meet unfolding P6_def distinct4_def by metis
    then show "projective_plane_data.pcollinear dPoints dLines dincid ?P ?Q ?R" 
      using kdef p q r QOPR dualp dm mdualize.simps
      projective_plane.pcollinear_commute projective_plane.pcollinear_degeneracy
      projective_plane.incid_join_collinear by metis
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma A2C_is_P6: "P6 A2C_Points A2C_Lines A2C_incid" unfolding P6_def
proof
  show pp: "projective_plane A2C_Points A2C_Lines A2C_incid" 
    using RP2C.projective_plane_axioms by simp
  show "(\<forall>l l' A B C A' B' C'. (l \<in> A2C_Lines \<and> l' \<in> A2C_Lines \<and> l \<noteq> l'
    \<and> A \<in> A2C_Points \<and> B \<in> A2C_Points \<and> C \<in> A2C_Points 
    \<and> A' \<in> A2C_Points \<and> B' \<in> A2C_Points \<and> C' \<in> A2C_Points 
    \<and> distinct4 A B C (RP2C.meet l l') 
    \<and> distinct4 A' B' C' (RP2C.meet l l')
    \<and> A2C_incid A l \<and> A2C_incid B l \<and> A2C_incid C l 
    \<and> A2C_incid A' l' \<and> A2C_incid B' l' \<and> A2C_incid C' l')
    \<longrightarrow> (RP2C.pcollinear (RP2C.meet (RP2C.join A B') (RP2C.join A' B))
      (RP2C.meet (RP2C.join A C') (RP2C.join A' C))
      (RP2C.meet (RP2C.join B C') (RP2C.join B' C))))"
  proof (clarify)
    fix l l' :: "(a2pt, a2ln) projLine"
    fix A B C A' B' C' :: "(a2pt, a2ln) projPoint"
    assume ll: "l \<in> A2C_Lines" and l'l: "l' \<in> A2C_Lines" and lneql': "l \<noteq> l'"
    let ?X = "RP2C.meet l l'"
    assume a: "A \<in> A2C_Points" and b: "B \<in> A2C_Points" and c: "C \<in> A2C_Points" 
      and a': "A' \<in> A2C_Points" and b': "B' \<in> A2C_Points" and c': "C' \<in> A2C_Points"
      and abcxdist: "distinct4 A B C ?X" and a'b'c'xdist: "distinct4 A' B' C' ?X"
      and aonl: "A2C_incid A l" and bonl: "A2C_incid B l" and conl: "A2C_incid C l"
      and a'onl': "A2C_incid A' l'" and b'onl': "A2C_incid B' l'" and c'onl': "A2C_incid C' l'"
    let ?P = "RP2C.meet (RP2C.join A B') (RP2C.join A' B)"
    let ?Q = "RP2C.meet (RP2C.join A C') (RP2C.join A' C)"
    let ?R = "RP2C.meet (RP2C.join B C') (RP2C.join B' C)"
    show "RP2C.pcollinear ?P ?Q ?R" sorry
  qed
qed

(*lemma RP2_is_P6: "P6 rp2_Points rp2_Lines rp2_incid" unfolding P6_def
proof
  show pp: "projective_plane rp2_Points rp2_Lines rp2_incid" 
    using RP2Q.projective_plane_axioms by simp
  show "(\<forall>l l' A B C A' B' C'. (l \<in> rp2_Lines \<and> l' \<in> rp2_Lines \<and> l \<noteq> l'
    \<and> A \<in> rp2_Points \<and> B \<in> rp2_Points \<and> C \<in> rp2_Points 
    \<and> A' \<in> rp2_Points \<and> B' \<in> rp2_Points \<and> C' \<in> rp2_Points 
    \<and> distinct4 A B C (RP2Q.meet l l') 
    \<and> distinct4 A' B' C' (RP2Q.meet l l')
    \<and> rp2_incid A l \<and> rp2_incid B l \<and> rp2_incid C l 
    \<and> rp2_incid A' l' \<and> rp2_incid B' l' \<and> rp2_incid C' l')
    \<longrightarrow> (RP2Q.pcollinear (RP2Q.meet (RP2Q.join A B') (RP2Q.join A' B))
      (RP2Q.meet (RP2Q.join A C') (RP2Q.join A' C))
      (RP2Q.meet (RP2Q.join B C') (RP2Q.join B' C))))"
  proof (clarify)
    fix l l' A B C A' B' C' :: rp2
    assume ll: "l \<in> rp2_Lines" and l'l: "l' \<in> rp2_Lines" and lneql': "l \<noteq> l'"
    let ?X = "RP2Q.meet l l'"
    assume a: "A \<in> rp2_Points" and b: "B \<in> rp2_Points" and c: "C \<in> rp2_Points" 
      and a': "A' \<in> rp2_Points" and b': "B' \<in> rp2_Points" and c': "C' \<in> rp2_Points"
      and abcxdist: "distinct4 A B C ?X" and a'b'c'xdist: "distinct4 A' B' C' ?X"
      and aonl: "rp2_incid A l" and bonl: "rp2_incid B l" and conl: "rp2_incid C l"
      and a'onl': "rp2_incid A' l'" and b'onl': "rp2_incid B' l'" and c'onl': "rp2_incid C' l'"
    let ?P = "RP2Q.meet (RP2Q.join A B') (RP2Q.join A' B)"
    let ?Q = "RP2Q.meet (RP2Q.join A C') (RP2Q.join A' C)"
    let ?R = "RP2Q.meet (RP2Q.join B C') (RP2Q.join B' C)"
    show "RP2Q.pcollinear ?P ?Q ?R" sorry
  qed
qed*)
text \<open>\done\<close>

end