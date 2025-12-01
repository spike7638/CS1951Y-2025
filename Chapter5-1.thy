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
  have pp: "projective_plane Points Lines incid" using p6p P6_def by auto
  then show dualp: "projective_plane dPoints dLines dincid" 
    using assms dual_plane_is_projective by auto
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
      and xdist: "A \<noteq> B" "A \<noteq> C" "A \<noteq> ?X" "B \<noteq> C" "B \<noteq> ?X" "C \<noteq> ?X" 
        "A' \<noteq> B'" "A' \<noteq> C'" "A' \<noteq> ?X" "B' \<noteq> C'" "B' \<noteq> ?X" "C' \<noteq> ?X" 
      and onll': "dincid A l" "dincid B l" "dincid C l" 
        "dincid A' l'" "dincid B' l'" "dincid C' l'"
    then have ll'dj: "l = ?djoin A C" "l' = ?djoin A' C'"
      using twolines dualp projective_plane.join_properties2 by metis+
    let ?P = "?dmeet (?djoin A B') (?djoin A' B)"
    let ?Q = "?dmeet (?djoin A C') (?djoin A' C)"
    let ?R = "?dmeet (?djoin B C') (?djoin B' C)"
    have hneqs: "A \<noteq> B'" "A' \<noteq> B" "A \<noteq> C'" "A' \<noteq> C" "B \<noteq> C'" "B' \<noteq> C" 
      using twolines allpts xdist onll' projective_plane.meet_properties2
      projective_plane.join_properties2 [of _ _ _ _ _ l] dualp
      projective_plane.join_properties2 [of _ _ _ _ _ l'] by metis+
    then have jneqs: "(?djoin A B') \<noteq> (?djoin A' B)" "(?djoin A C') \<noteq> (?djoin A' C)"
      "(?djoin B C') \<noteq> (?djoin B' C)" using twolines allpts xdist onll' dualp
      projective_plane.join_properties1 [of _ _ dincid]
      projective_plane.unique_meet [of _ _ dincid] by metis+
    then have pqr: "?P \<in> dPoints" "?Q \<in> dPoints" "?R \<in> dPoints"
      using allpts hneqs dualp projective_plane.mjj_point [of _ _ dincid] by auto
    have bb'l: "B \<in> Lines \<and> B' \<in> Lines" using allpts dPdef by simp
    have bneqb': "B \<noteq> B'" using twolines allpts xdist onll' dualp
      projective_plane.unique_meet projective_plane.meet_properties2 by fastforce
    let ?AO = "?meet B C'" let ?BO = l let ?CO = "?meet A' B"
    let ?A'O = "?meet A B'" let ?B'O = l' let ?C'O = "?meet B' C"
    have Opts: "?AO \<in> Points \<and> ?BO \<in> Points \<and> ?CO \<in> Points 
      \<and> ?A'O \<in> Points \<and> ?B'O \<in> Points \<and> ?C'O \<in> Points"
      using twolines allpts xdist onll' p6p dPdef dLdef dm
      projective_plane.join_properties2 projective_plane.meet_properties2 
      mdualize.simps dual_meet_is_join unfolding P6_def by metis
    then have OonB: "incid ?AO B \<and> incid ?BO B \<and> incid ?CO B" 
      "incid ?A'O B' \<and> incid ?B'O B' \<and> incid ?C'O B'"
      using bb'l twolines allpts xdist onll' pp dPdef dLdef dm 
      projective_plane.meet_properties2 projective_plane.join_properties2 
      dual_meet_is_join mdualize.simps by metis+
    let ?XO = "?meet B B'"
    have Oxdist: "?AO \<noteq> ?BO \<and> ?AO \<noteq> ?CO \<and> ?AO \<noteq> ?XO \<and> ?BO \<noteq> ?CO \<and> ?BO \<noteq> ?XO \<and> ?CO \<noteq> ?XO"
      "?A'O \<noteq> ?B'O \<and> ?A'O \<noteq> ?C'O \<and> ?A'O \<noteq> ?XO \<and> ?B'O \<noteq> ?C'O \<and> ?B'O \<noteq> ?XO \<and> ?C'O \<noteq> ?XO"
      using Opts twolines allpts xdist onll' dPdef dm pp dualp mdualize.simps
      projective_plane.meet_properties2 [of dPoints dLines dincid]
      projective_plane.meet_properties2 [of Points Lines incid]
      projective_plane.unique_meet [of Points Lines incid] by (metis (full_types))+
    let ?PO = "?meet (?join ?AO ?B'O) (?join ?A'O ?BO)"
    let ?QO = "?meet (?join ?AO ?C'O) (?join ?A'O ?CO)"
    let ?RO = "?meet (?join ?BO ?C'O) (?join ?B'O ?CO)"
    have Ohneqs: "?AO \<noteq> ?B'O" "?A'O \<noteq> ?BO" "?AO \<noteq> ?C'O" "?A'O \<noteq> ?CO" "?BO \<noteq> ?C'O" 
      "?B'O \<noteq> ?CO" using bb'l bneqb' projective_plane.meet_properties2
      projective_plane.join_properties2 [of _ _ _ _ _ B] Opts Oxdist OonB pp
      projective_plane.join_properties2 [of _ _ _ _ _ B'] by metis+
    then have Ojneqs: "(?join ?AO ?B'O) \<noteq> (?join ?A'O ?BO)" 
      "(?join ?AO ?C'O) \<noteq> (?join ?A'O ?CO)" "(?join ?BO ?C'O) \<noteq> (?join ?B'O ?CO)" 
      using bb'l bneqb' pp projective_plane.join_properties1 [of _ _ incid]
      Opts Oxdist OonB projective_plane.unique_meet [of _ _ incid] by metis+
    then have Opqr: "?PO \<in> Points" "?QO \<in> Points" "?RO \<in> Points"
      using Opts Ohneqs pp projective_plane.mjj_point by auto
    have POROdj: "?PO = ?djoin A C'" "?RO = ?djoin A' C"
      using allpts onll' Opts Oxdist OonB pp mdualize.simps dPdef dLdef dm dualp
      dual_join_is_meet projective_plane.join_properties2 [of Points Lines incid ?AO]
      projective_plane.join_properties2 [of Points Lines incid ?A'O]
      projective_plane.join_properties2 [of dPoints dLines dincid A C' ?PO]
      projective_plane.join_properties2 [of Points Lines incid ?BO]
      projective_plane.join_properties2 [of Points Lines incid ?B'O]
      projective_plane.join_properties2 [of dPoints dLines dincid A' C ?RO]
      projective_plane.meet_properties2 [of Points Lines incid] by (smt (verit))+
    have QOPR: "?QO = ?djoin ?P ?R" using pqr pp dualp dPdef dLdef dm
      dual_join_is_meet dual_meet_is_join projective_plane.join_properties2 
      projective_plane.join_properties1 [of dPoints dLines dincid ?P ?R] by (smt (z3))
    have "?pcollinear ?PO ?QO ?RO" using bb'l bneqb' Opts Oxdist OonB p6p 
      unfolding P6_def by auto
    then obtain k where kdef: "k \<in> Lines \<and> incid ?PO k \<and> incid ?QO k \<and> incid ?RO k"
      using Opqr p6p P6_def unfolding projective_plane_data.pcollinear_def by auto
    then have "k = ?Q" using allpts xdist onll' Oxdist Opqr POROdj ll'dj
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
lemma A2C_P6_helper: (* Hartshorne's proof in Euclidean space *)
  fixes l::a2ln
  assumes "l \<in> A2Lines"
  fixes m b::real
  assumes "l = A2Ordinary m b"
  fixes A B C::a2pt
  assumes "A \<in> A2Points" and "B \<in> A2Points" and "C \<in> A2Points"
  assumes "a2incid A l" and "a2incid B l" and "a2incid C l"
  fixes Ax Ay Bx By Cx Cy::real
  assumes "A = A2Point Ax Ay" and "B = A2Point Bx By" and "C = A2Point Cx Cy"
  fixes D1 D2 D3::real
  assumes "distinct[m,b,D1,D2,D3]"
  fixes a1 b1 a2 c2 b3 c3::a2ln
  assumes "a1 = A2Ordinary D1 (Ay-(D1*Ax))"
    and "b1 = A2Ordinary D1 (By-(D1*Bx))"
    and "a2 = A2Ordinary D2 (Ay-(D2*Ax))"
    and "c2 = A2Ordinary D2 (Cy-(D2*Cx))"
    and "b3 = A2Ordinary D3 (By-(D3*Bx))"
    and "c3 = A2Ordinary D3 (Cy-(D3*Cx))"
  shows "A2.collinear (a2meet a2 b3) (a2meet a1 c3) (a2meet b1 c2)"
  sorry
text \<open>\done\<close>

(*theorem A2C_is_P6: "P6 A2C_Points A2C_Lines A2C_incid" unfolding P6_def
proof
  show pp: "projective_plane A2C_Points A2C_Lines A2C_incid" 
    using RP2C.projective_plane_axioms by simp
  show "(\<forall>l l' A B C A' B' C'. (l \<in> A2C_Lines \<and> l' \<in> A2C_Lines \<and> l \<noteq> l'
    \<and> A \<in> A2C_Points \<and> B \<in> A2C_Points \<and> C \<in> A2C_Points 
    \<and> A' \<in> A2C_Points \<and> B' \<in> A2C_Points \<and> C' \<in> A2C_Points 
    \<and> distinct[A,B,C,(RP2C.meet l l')]
    \<and> distinct[A',B',C',(RP2C.meet l l')]
    \<and> A2C_incid A l \<and> A2C_incid B l \<and> A2C_incid C l 
    \<and> A2C_incid A' l' \<and> A2C_incid B' l' \<and> A2C_incid C' l')
    \<longrightarrow> (RP2C.pcollinear (RP2C.meet (RP2C.join A B') (RP2C.join A' B))
      (RP2C.meet (RP2C.join A C') (RP2C.join A' C))
      (RP2C.meet (RP2C.join B C') (RP2C.join B' C))))"
  proof (clarify)
    fix l l' :: "(a2pt, a2ln) projLine"
    fix A B C A' B' C' :: "(a2pt, a2ln) projPoint"
    assume twolines: "l \<in> A2C_Lines" "l' \<in> A2C_Lines" "l \<noteq> l'"
    let ?X = "RP2C.meet l l'"
    assume allpts: "A \<in> A2C_Points" "B \<in> A2C_Points" "C \<in> A2C_Points" 
      "A' \<in> A2C_Points" "B' \<in> A2C_Points" "C' \<in> A2C_Points"
      and xdist: "A \<noteq> B" "A \<noteq> C" "A \<noteq> ?X" "B \<noteq> C" "B \<noteq> ?X" "C \<noteq> ?X" 
        "A' \<noteq> B'" "A' \<noteq> C'" "A' \<noteq> ?X" "B' \<noteq> C'" "B' \<noteq> ?X" "C' \<noteq> ?X" 
      and onll': "A2C_incid A l" "A2C_incid B l" "A2C_incid C l" 
        "A2C_incid A' l'" "A2C_incid B' l'" "A2C_incid C' l'"
    let ?P = "RP2C.meet (RP2C.join A B') (RP2C.join A' B)"
    let ?Q = "RP2C.meet (RP2C.join A C') (RP2C.join A' C)"
    let ?R = "RP2C.meet (RP2C.join B C') (RP2C.join B' C)"
    have hneqs: "A \<noteq> B'" "A' \<noteq> B" "A \<noteq> C'" "A' \<noteq> C" "B \<noteq> C'" "B' \<noteq> C" 
      using twolines allpts xdist onll' projective_plane.meet_properties2
      projective_plane.join_properties2 [of _ _ _ _ _ l] pp
      projective_plane.join_properties2 [of _ _ _ _ _ l'] by metis+
    then have jneqs: "(RP2C.join A B') \<noteq> (RP2C.join A' B)" 
      "(RP2C.join A C') \<noteq> (RP2C.join A' C)" "(RP2C.join B C') \<noteq> (RP2C.join B' C)" 
      using twolines allpts xdist onll' pp projective_plane.join_properties1 
      [of _ _ A2C_incid] projective_plane.unique_meet [of _ _ A2C_incid] by metis+
    then have pqr: "?P \<in> A2C_Points" "?Q \<in> A2C_Points" "?R \<in> A2C_Points"
      using allpts hneqs pp projective_plane.mjj_point [of _ _ A2C_incid] by auto
    consider (linf) "l = Infty \<and> l' \<noteq> Infty" | (l'inf) "l \<noteq> Infty \<and> l' = Infty"
      | (ll'ord) "l \<noteq> Infty \<and> l' \<noteq> Infty" using twolines by auto
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
text \<open>\done\<close>*)

(*text \<open>\hadi\<close>
fun a2collinear :: "a2pt \<Rightarrow> a2pt \<Rightarrow> a2pt \<Rightarrow> bool" where
  "a2collinear (A2Point x1 y1) (A2Point x2 y2) (A2Point x3 y3) 
    = Linear_Algebra.collinear {vector[x1,y1],vector[x2,y2],vector[x3,y3]::real^2}"

fun a2segmentLength :: "a2pt \<Rightarrow> a2pt \<Rightarrow> real" (infix "@@" 50) where
  "a2segmentLength (A2Point x1 y1) (A2Point x2 y2) = sqrt((x1 - y1)^2 + (x2 - y2)^2)"

theorem menelaus:
  fixes A B C D E F :: a2pt 
  assumes "{A,B,C} \<inter> {D,E,F} = {}"
  assumes "\<not> a2collinear A B C"
  fixes k :: "a2ln"
  assumes "a2incid D (a2join B C)" and "a2incid D k"
  assumes "a2incid E (a2join A C)" and "a2incid E k"
  assumes "a2incid F (a2join A B)" and "a2incid F k"
  shows "(((A @@ F)/(F @@ B))*((B @@ D)/(D @@ C))*((C @@ E)/(E @@ A))) = 1"
  sorry

definition segmentLength3 :: "real^3 \<Rightarrow> real^3 \<Rightarrow> real" where
  "segmentLength3 x y = sqrt((x$1 - y$1)^2 + (x$2 - y$2)^2 + (x$3 - y$3)^2)"

lift_definition SegmentLength :: "rp2 \<Rightarrow> rp2 \<Rightarrow> real" is "\<lambda>x y. segmentLength3 x y"
proof -
  fix v1 v2 v3 v4
  assume a1: "rp2rel v1 v2" and a2: "rp2rel v3 v4"
  show "(segmentLength3 v1 v3) = (segmentLength3 v2 v4)" 
  proof -
    obtain t1 t2 where tdefs: "t1 \<noteq> 0 \<and> v1 = t1 *\<^sub>R v2" "t2 \<noteq> 0 \<and> v3 = t2 *\<^sub>R v4" 
      using a1 a2 rp2rel_def by auto
    then have mcoords: "v1$1 = t1 * v2$1" "v1$2 = t1 * v2$2" "v1$3 = t1 * v2$3"
      "v3$1 = t2 * v4$1" "v3$2 = t2 * v4$2" "v3$3 = t2 * v4$3" by auto 
    have lengths: "(segmentLength3 v1 v3) = sqrt((v1$1 - v3$1)^2 + (v1$2 - v3$2)^2 + (v1$3 - v3$3)^2)"
      "(segmentLength3 v2 v4) = sqrt((v2$1 - v4$1)^2 + (v2$2 - v4$2)^2 + (v2$3 - v4$3)^2)"
      using segmentLength3_def by auto
    have "(v1$1 - v3$1) = ((t1 * v2$1) - (t2 * v4$1))" using mcoords by auto
    show ?thesis sorry
  qed
qed*)

theorem RP2_is_P6: "P6 rp2_Points rp2_Lines rp2_incid" unfolding P6_def
proof
  show pp: "projective_plane rp2_Points rp2_Lines rp2_incid" 
    using RP2Q.projective_plane_axioms by simp
  show "(\<forall>l l' A B C A' B' C'. (l \<in> rp2_Lines \<and> l' \<in> rp2_Lines \<and> l \<noteq> l'
    \<and> A \<in> rp2_Points \<and> B \<in> rp2_Points \<and> C \<in> rp2_Points 
    \<and> A' \<in> rp2_Points \<and> B' \<in> rp2_Points \<and> C' \<in> rp2_Points 
    \<and> distinct[A,B,C,(RP2Q.meet l l')]
    \<and> distinct[A',B',C',(RP2Q.meet l l')]
    \<and> rp2_incid A l \<and> rp2_incid B l \<and> rp2_incid C l 
    \<and> rp2_incid A' l' \<and> rp2_incid B' l' \<and> rp2_incid C' l')
    \<longrightarrow> (RP2Q.pcollinear (RP2Q.meet (RP2Q.join A B') (RP2Q.join A' B))
      (RP2Q.meet (RP2Q.join A C') (RP2Q.join A' C))
      (RP2Q.meet (RP2Q.join B C') (RP2Q.join B' C))))"
  proof (clarify)
    fix l l' A B C A' B' C' :: rp2
    assume twolines: "l \<in> rp2_Lines" "l' \<in> rp2_Lines" "l \<noteq> l'"
    let ?X = "RP2Q.meet l l'"
    assume allpts: "A \<in> rp2_Points" "B \<in> rp2_Points" "C \<in> rp2_Points" 
      "A' \<in> rp2_Points" "B' \<in> rp2_Points" "C' \<in> rp2_Points"
      and xdist: "A \<noteq> B" "A \<noteq> C" "A \<noteq> ?X" "B \<noteq> C" "B \<noteq> ?X" "C \<noteq> ?X" 
        "A' \<noteq> B'" "A' \<noteq> C'" "A' \<noteq> ?X" "B' \<noteq> C'" "B' \<noteq> ?X" "C' \<noteq> ?X" 
      and onll': "rp2_incid A l" "rp2_incid B l" "rp2_incid C l" 
        "rp2_incid A' l'" "rp2_incid B' l'" "rp2_incid C' l'"
    let ?P = "RP2Q.meet (RP2Q.join A B') (RP2Q.join A' B)"
    let ?Q = "RP2Q.meet (RP2Q.join A C') (RP2Q.join A' C)"
    let ?R = "RP2Q.meet (RP2Q.join B C') (RP2Q.join B' C)"
    have hneqs: "A \<noteq> B'" "A' \<noteq> B" "A \<noteq> C'" "A' \<noteq> C" "B \<noteq> C'" "B' \<noteq> C" 
      using twolines allpts xdist onll' projective_plane.meet_properties2
      projective_plane.join_properties2 [of _ _ _ _ _ l] pp
      projective_plane.join_properties2 [of _ _ _ _ _ l'] by metis+
    then have jneqs: "(RP2Q.join A B') \<noteq> (RP2Q.join A' B)" 
      "(RP2Q.join A C') \<noteq> (RP2Q.join A' C)" "(RP2Q.join B C') \<noteq> (RP2Q.join B' C)" 
      using twolines allpts xdist onll' pp projective_plane.join_properties1 
      [of _ _ rp2_incid] projective_plane.unique_meet [of _ _ rp2_incid] by metis+
    then have pqr: "?P \<in> rp2_Points" "?Q \<in> rp2_Points" "?R \<in> rp2_Points"
      using allpts hneqs pp projective_plane.mjj_point [of _ _ rp2_incid] by auto
    then obtain x1 x2 x3 y1 y2 y3 z1 z2 z3::real 
    where xdef: "(Rep_rp2 ?P) = (vector[x1,x2,x3]::v3)"
    and ydef: "(Rep_rp2 ?Q) = (vector[y1,y2,y3]::v3)"
    and zdef: "(Rep_rp2 ?R) = (vector[z1,z2,z3]::v3)"
    using exists_rp2_coords by fastforce
    obtain v1 v2 v3::real where leqtn: "\<forall>V \<in> rp2_Points. rp2_incid V l
      \<longleftrightarrow> ((v1 * (Rep_rp2 V)$1) + (v2 * (Rep_rp2 V)$2) + (v3 * (Rep_rp2 V)$3) = 0)" 
      using twolines rp2_line_equation [of l] by auto
    obtain w1 w2 w3::real where l'eqtn: "\<forall>V \<in> rp2_Points. rp2_incid V l'
      \<longleftrightarrow> ((w1 * (Rep_rp2 V)$1) + (w2 * (Rep_rp2 V)$2) + (w3 * (Rep_rp2 V)$3) = 0)" 
      using twolines rp2_line_equation [of l'] by auto
    show "RP2Q.pcollinear ?P ?Q ?R" sorry
  qed
qed
text \<open>\done\<close>

end