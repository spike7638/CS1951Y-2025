theory "Chapter5-1"
  imports "Chapter4-4"
begin

text \<open>Everything up to and including Proposition 5.2\<close>

text \<open>\hadi\<close>
definition FTPL :: "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool" where
  "FTPL Points Lines incid \<equiv> (projective_plane Points Lines incid) 
    \<and> (\<forall>l A B C A' B' C'. (l \<in> Lines \<and> A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points \<and> distinct[A,B,C] 
    \<and> distinct[A',B',C'] \<and> incid A l \<and> incid B l \<and> incid C l 
    \<and> incid A' l \<and> incid B' l \<and> incid C' l)
    \<longrightarrow> (\<exists>!(f::('p \<Rightarrow> 'p)). \<exists>!Or. \<exists>!ls.
      (f = projective_plane.projectivity Points Lines incid ls) 
      \<and> (hd ls = (Or, l, l)) \<and> (last ls = (Or, l, l))
      \<and> (f A = A') \<and> (f B = B') \<and> (f C = C')))"

definition P6 :: "'p set \<Rightarrow> 'l set \<Rightarrow> ('p \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> bool" where
  "P6 Points Lines incid \<equiv> (projective_plane Points Lines incid) 
    \<and> (\<forall>l l' A B C A' B' C'. (l \<in> Lines \<and> l' \<in> Lines \<and> l \<noteq> l'
    \<and> A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
    \<and> A' \<in> Points \<and> B' \<in> Points \<and> C' \<in> Points 
    \<and> distinct[A,B,C,(projective_plane_data.meet Points Lines incid l l')] 
    \<and> distinct[A',B',C',(projective_plane_data.meet Points Lines incid l l')]
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
lemma (in projective_plane) opp_joins_neq:
  fixes l k
  assumes "l \<in> Lines" and "k \<in> Lines" and "l \<noteq> k"
  fixes A B C D
  assumes "A \<in> Points" and "B \<in> Points" and "C \<in> Points" and "D \<in> Points"
  assumes "distinct[A,B,(meet l k)]" and "distinct[C,D,(meet l k)]"
  assumes "A \<lhd> l" and "B \<lhd> l" and "C \<lhd> k" and "D \<lhd> k"
  shows "(join A C) \<noteq> (join B D)"
proof
  assume cd: "(join A C) = (join B D)"
  have "A \<noteq> C" and "B \<noteq> D" using assms meet_properties2 unique_meet by auto
  then have "A \<lhd> l \<and> A \<lhd> (join A C)" and "B \<lhd> l \<and> B \<lhd> (join B D)"
    using assms join_properties1 by auto
  then show False using assms cd join_properties1 unique_meet distinct3_def by metis
qed

lemma dist4to3: "distinct[A,B,C,X] 
  \<Longrightarrow> distinct[A,B,X] \<and> distinct[A,C,X] \<and> distinct[B,C,X]" by blast
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
  let ?dmeet = "projective_plane_data.meet dPoints dLines dincid"
  let ?djoin = "projective_plane_data.join dPoints dLines dincid"
  let ?meet = "projective_plane_data.meet Points Lines incid"
  let ?join = "projective_plane_data.join Points Lines incid"
  let ?dpcollinear = "projective_plane_data.pcollinear dPoints dLines dincid"
  let ?pcollinear = "projective_plane_data.pcollinear Points Lines incid"
  show "\<forall>l l' A B C A' B' C'. (l \<in> dLines \<and> l' \<in> dLines \<and> l \<noteq> l'
    \<and> A \<in> dPoints \<and> B \<in> dPoints \<and> C \<in> dPoints 
    \<and> A' \<in> dPoints \<and> B' \<in> dPoints \<and> C' \<in> dPoints 
    \<and> distinct[A,B,C,(?dmeet l l')] \<and> distinct[A',B',C',(?dmeet l l')]
    \<and> dincid A l \<and> dincid B l \<and> dincid C l 
    \<and> dincid A' l' \<and> dincid B' l' \<and> dincid C' l')
    \<longrightarrow> (?dpcollinear (?dmeet (?djoin A B') (?djoin A' B))
          (?dmeet (?djoin A C') (?djoin A' C))
          (?dmeet (?djoin B C') (?djoin B' C)))"
  proof (clarify)
    fix l l' A B C A' B' C'
    assume twolines: "l \<in> dLines" "l' \<in> dLines" "l \<noteq> l'"
    let ?X = "?dmeet l l'"
    assume allpts: "A \<in> dPoints" "B \<in> dPoints" "C \<in> dPoints" 
        "A' \<in> dPoints""B' \<in> dPoints" "C' \<in> dPoints" 
      and xdist: "A \<noteq> B \<and> A \<noteq> C \<and> A \<noteq> ?X \<and> B \<noteq> C \<and> B \<noteq> ?X \<and> C \<noteq> ?X" 
        "A' \<noteq> B' \<and> A' \<noteq> C' \<and> A' \<noteq> ?X \<and> B' \<noteq> C' \<and> B' \<noteq> ?X \<and> C' \<noteq> ?X" 
      and onll': "dincid A l" "dincid B l" "dincid C l" 
        "dincid A' l'" "dincid B' l'" "dincid C' l'"
    then have lAC: "l = ?djoin A C" and l'A'C': "l' = ?djoin A' C'"
      using twolines dualp projective_plane.join_properties2 by metis+
    let ?P = "?dmeet (?djoin A B') (?djoin A' B)"
    let ?Q = "?dmeet (?djoin A C') (?djoin A' C)"
    let ?R = "?dmeet (?djoin B C') (?djoin B' C)"
    (*have "(?djoin A B') \<noteq> (?djoin A' B)"
      using a b c a' b' c' ll l'l lneql' aonl bonl conl a'onl' b'onl' c'onl'
      abcxdist a'b'c'xdist dist4to3 
      projective_plane.opp_joins_neq [of dPoints dLines dincid l l' A B' A' B] 
      *)
    have pqr: "?P \<in> dPoints" "?Q \<in> dPoints" "?R \<in> dPoints"
      using twolines allpts xdist onll' dualp 
      projective_plane.meet_properties2 projective_plane.join_properties1 
      projective_plane.join_properties2 by (smt (verit))+
    have bl: "B \<in> Lines" and b'l: "B' \<in> Lines" using allpts dPdef by simp+
    have bneqb': "B \<noteq> B'" using twolines allpts xdist onll' dualp
      projective_plane.unique_meet projective_plane.meet_properties2 by fastforce
    let ?AO = "?meet B C'" let ?BO = l let ?CO = "?meet A' B"
    let ?A'O = "?meet A B'" let ?B'O = l' let ?C'O = "?meet B' C"
    have Opts: "?AO \<in> Points \<and> ?BO \<in> Points \<and> ?CO \<in> Points 
      \<and> ?A'O \<in> Points \<and> ?B'O \<in> Points \<and> ?C'O \<in> Points"
      using twolines allpts xdist onll' p6p dPdef dLdef dm
      projective_plane.join_properties2 projective_plane.meet_properties2 
      mdualize.simps dual_meet_is_join unfolding P6_def by metis
    then have OponB: "incid ?AO B \<and> incid ?BO B \<and> incid ?CO B" 
      and Op'onB': "incid ?A'O B' \<and> incid ?B'O B' \<and> incid ?C'O B'" using bl b'l 
      twolines allpts xdist onll' projective_plane.meet_properties2
      projective_plane.join_properties2 dual_meet_is_join dPdef dLdef dm
      mdualize.simps p6p unfolding P6_def by metis+
    let ?XO = "?meet B B'"
    have Oxdist: "distinct[?AO,?BO,?CO,?XO]" 
      and O'xdist: "distinct[?A'O,?B'O,?C'O,?XO]"
      using twolines allpts xdist onll' lAC l'A'C' Opts 
      projective_plane.join_properties1 projective_plane.meet_properties2
      projective_plane.unique_meet p6p dualp dPdef dLdef dm mdualize.simps 
      unfolding P6_def by (smt (z3))+
    let ?PO = "?meet (?join ?AO ?B'O) (?join ?A'O ?BO)"
    let ?QO = "?meet (?join ?AO ?C'O) (?join ?A'O ?CO)"
    let ?RO = "?meet (?join ?BO ?C'O) (?join ?B'O ?CO)"
    have Opqr: "?PO \<in> Points" "?QO \<in> Points" "?RO \<in> Points"
      using twolines allpts xdist onll' bneqb' Opts Oxdist
      O'xdist p6p dPdef dLdef dm mdualize.elims(2)  dual_meet_is_join 
      projective_plane.join_properties1 projective_plane.join_properties2 
      projective_plane.meet_properties2 unfolding P6_def by (smt (z3))+
    have POAC': "?PO = ?djoin A C'" and ROA'C: "?RO = ?djoin A' C"
      using allpts onll' Oxdist OponB O'xdist Op'onB' Opts p6p 
      dualp dPdef dLdef dm mdualize.simps dual_join_is_meet 
      projective_plane.meet_properties2 projective_plane.join_properties2 
      unfolding P6_def sorry
    have QOPR: "?QO = ?djoin ?P ?R" using pqr p6p projective_plane.join_properties1 
      dual_join_is_meet dual_meet_is_join projective_plane.join_properties2 dualp 
      dPdef dLdef dm unfolding P6_def by (smt (z3))
    have "?pcollinear ?PO ?QO ?RO" using bl b'l bneqb' Opts Oxdist O'xdist 
      OponB Op'onB' p6p unfolding P6_def by auto
    then obtain k where kdef: "k \<in> Lines \<and> incid ?PO k \<and> incid ?QO k \<and> incid ?RO k"
      using Opqr p6p P6_def unfolding projective_plane_data.pcollinear_def by auto
    then have "k = ?Q" using allpts xdist onll' Oxdist Opqr POAC' ROA'C lAC l'A'C'
      dPdef dLdef dm mdualize.simps dualp mmi_eq p6p dual_join_is_meet
      projective_plane.join_properties2 projective_plane.meet_properties2
      unfolding P6_def distinct4_def by metis
    then show "?dpcollinear ?P ?Q ?R" using kdef pqr QOPR dualp dm mdualize.simps
      projective_plane.pcollinear_commute projective_plane.pcollinear_degeneracy
      projective_plane.incid_join_collinear by metis
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma A2C_P6_helper:
  fixes l'::a2ln
  assumes "l' \<in> A2Lines"
  fixes m' b'::real
  assumes "l' = A2Ordinary m' b'"
  fixes A' B' C'::a2pt
  assumes "A' \<in> A2Points" and "B' \<in> A2Points" and "C' \<in> A2Points"
  assumes "a2incid A' l'" and "a2incid B' l'" and "a2incid C' l'"
  fixes A'x B'x C'x A'y B'y C'y::real
  assumes "A' = A2Point A'x A'y" and "B' = A2Point B'x B'y" and "C' = A2Point C'x C'y"
  fixes Am Bm Cm::real
  assumes "distinct[m',b'Am,Bm,Cm]"
  fixes A'B A'C B'A B'C C'A C'B::a2ln
  assumes "A'B = A2Ordinary Bm (A'y-(Bm*A'x))"
    and "A'C = A2Ordinary Cm (A'y-(Cm*A'x))"
    and "B'A = A2Ordinary Am (B'y-(Am*B'x))"
    and "B'C = A2Ordinary Cm (B'y-(Cm*B'x))"
    and "C'A = A2Ordinary Am (C'y-(Am*C'x))"
    and "C'B = A2Ordinary Bm (C'y-(Bm*C'x))"
  shows "A2.collinear (a2meet A'B B'A) (a2meet A'C C'A) (a2meet B'C C'B)"
  sorry

theorem A2C_is_P6: "P6 A2C_Points A2C_Lines A2C_incid" unfolding P6_def
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
    have p: "?P \<in> A2C_Points" and q: "?Q \<in> A2C_Points" and r: "?R \<in> A2C_Points"
      using ll l'l lneql' a b c abcxdist aonl bonl conl a' b' c' a'b'c'xdist 
      a'onl' b'onl' c'onl' pp projective_plane.meet_properties2
      projective_plane.join_properties1 projective_plane.join_properties2 
      unfolding distinct4_def by (smt (verit))+
    consider (linf) "l = Infty \<and> l' \<noteq> Infty" | (l'inf) "l \<noteq> Infty \<and> l' = Infty"
      | (ll'ord) "l \<noteq> Infty \<and> l' \<noteq> Infty" using lneql' by auto
    then show "RP2C.pcollinear ?P ?Q ?R"
    proof (cases)
      case linf
      then obtain l'0::a2ln where l'0def: "l' = OrdinaryL l'0" 
        using projLine.exhaust by metis
      let ?T' = "(Ideal (affine_plane_data.line_pencil A2Points A2Lines a2incid l'0))"
      have idl_l'0: "A2C_incid ?T' l" using linf by simp
      then show ?thesis sorry
    next
      case l'inf
      then obtain l0::a2ln where l0def: "l = OrdinaryL l0" 
        using projLine.exhaust by metis
      let ?T = "(Ideal (affine_plane_data.line_pencil A2Points A2Lines a2incid l0))"
      have idl_l0: "A2C_incid ?T l'" using l'inf by simp
      then show ?thesis sorry
    next
      case ll'ord
      then obtain l0 l'0::a2ln where l0def: "l = OrdinaryL l0" 
        and l'0def: "l' = OrdinaryL l'0" using projLine.exhaust by metis
      then consider (oo) "(\<exists>m b. l0 = A2Ordinary m b) \<and> (\<exists>m b. l'0 = A2Ordinary m b)"
        | (ov) "(\<exists>m b. l0 = A2Ordinary m b) \<and> (\<exists>x. l'0 = A2Vertical x)"
        | (vo) "(\<exists>x. l0 = A2Vertical x) \<and> (\<exists>m b. l'0 = A2Ordinary m b)"
        | (vv) "(\<exists>x. l0 = A2Vertical x) \<and> (\<exists>x. l'0 = A2Vertical x)"
        using a2ln.exhaust by metis
      then show ?thesis
      proof (cases)
        case oo
        then obtain m b m' b'::real where l0mb: "l0 = A2Ordinary m b"
          and l'0m'b': "l'0 = A2Ordinary m' b'" by auto
        then show ?thesis sorry
      next
        case ov
        then show ?thesis sorry
      next
        case vo
        then show ?thesis sorry
      next
        case vv
        then show ?thesis sorry
      qed
    qed
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
    have p: "?P \<in> rp2_Points" and q: "?Q \<in> rp2_Points" and r: "?R \<in> rp2_Points" 
      using a b c a' b' c' aonl a'onl' bonl b'onl' conl c'onl' abcxdist 
      a'b'c'xdist ll l'l lneql' RP2Q.join_properties1 RP2Q.meet_properties2
      RP2Q.unique_meet unfolding distinct4_def by metis+
    then obtain x1 x2 x3 y1 y2 y3 z1 z2 z3::real 
    where xdef: "(Rep_Proj ?P) = (vector[x1,x2,x3]::v3)"
    and ydef: "(Rep_Proj ?Q) = (vector[y1,y2,y3]::v3)"
    and zdef: "(Rep_Proj ?R) = (vector[z1,z2,z3]::v3)"
    using exists_rp2_coords by fastforce
    obtain v1 v2 v3::real where leqtn: "\<forall>V \<in> rp2_Points. rp2_incid V l
      \<longleftrightarrow> ((v1 * (Rep_Proj V)$1) + (v2 * (Rep_Proj V)$2) + (v3 * (Rep_Proj V)$3) = 0)" 
      using ll rp2_line_equation [of l] by auto
    obtain w1 w2 w3::real where l'eqtn: "\<forall>V \<in> rp2_Points. rp2_incid V l'
      \<longleftrightarrow> ((w1 * (Rep_Proj V)$1) + (w2 * (Rep_Proj V)$2) + (w3 * (Rep_Proj V)$3) = 0)" 
      using l'l rp2_line_equation [of l'] by auto
    show "RP2Q.pcollinear ?P ?Q ?R" sorry
  qed
qed*)
text \<open>\done\<close>

end