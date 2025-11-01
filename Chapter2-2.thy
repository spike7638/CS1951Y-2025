theory "Chapter2-2R"
  imports  "HOL-Library.Uprod" 
           "../COMPLETED-VERSIONS/ALTERNATIVE-VERSIONs/Chapter1-1R" 
           "../COMPLETED-VERSIONS/ALTERNATIVE-VERSIONs/Chapter1-2R" 
           "../COMPLETED-VERSIONS/ALTERNATIVE-VERSIONs/Chapter1-3R" 
           "Chapter2-1R"

begin
declare [[smt_timeout = 1500]]
declare [[smt_reconstruction_step_timeout = 1500]]

subsection \<open>Setup and proof of P4 for a free projective plane on four points.\<close>
text\<open>
Here's the idea of the proof. 

Start with the four points of the configuration, and from them form four Base points, which we'll
call the basic points; for each pair of these, we have a basic line; these six lines are all distinct.

lemma two_basic_lines: Suppose n and m are distinct basic lines that share the basic point X, 
and that n . k = m . k is some point P. Then P = X. 
Proof: both contain X; both contain P. By uniqueness of join, X = P, because n <> m. 

lemma P4_basic: 
Take the four basic points U
For any two of these, the line between them has at least 3 points. 

pf: say they're A, B; the others are then P Q.
Then X = PQ . AB is on the line AB
If X = A, then P Q A are collinear; similarly for B. Thus X, A, B are all distinct. 
Done.


take any line k in fpp that's NOT a basic line
show that k has at least 3 points. 

Lemma: every nonbasic line k, k has at least two points:
for each basic line n, consider the point n . k which lies on k. 

If all of these points are the same point X, 
then we have AB = XAB and AC = XAC are lines both containing 
A and X,hence are equal, so B is in AC; contradiction. 
Hence every line has at least two points. QED

lemma P4_non_basic:

For contradiction, suppose the non-basic line k has ONLY 2 points P and Q.

Each basic line intersects k in either P or Q. Let H and K be the sets of
basic lines intersecting P and Q respectively. Then their cardinalities sum to 6, 
hence at least one -- say H -- contains at least 3 basic lines. 

By Spike's lemma, there's a point, say A, on at least two of these basic lines. 
That means that the points A and P are on two distinct lines...which means A = P. 
So if the line k has only two points, then one of them is a basic point. And the set
of basic lines meeting k there consists of at least AB AC and AD. 

If, say, BC were in there too, then the lemma two_basic_lines, applied to AB and BC, would show B = P. 
But A = P and A <> B.  contradiction. 

Thus there are the three basic lines that do NOT contain P: BC, BD, CD. 

Each of these intersects k SOMEwhere, hence at Q. But that (from lemma two-basic-lines) says B = Q. 

Hence k must be the line AB, a contradiction (because k is non-basic)
\<close>

text \<open>To continue this discussion, we'll make a locale consisting of the necessary setup (four points,
no three collinear) of a configuration to ensure that the 'free projective plane' on that configuration 
is indeed a projective plane (Prop. 2.2); we'll then define a confined configuration, and prove proposition
2.3 still within the context of this locale, and finish up with the non-Desarguesian projective plane.\<close>

\<comment> \<open>Let's establish a locale for proving things about a finite projective plane over a configuration 
with at least four points, no three collinear; we'll call such a configuration "ample" in the sense
that it has enough `starting material' to make the resulting structure an actual projective plane. \<close>
locale ample_fpp_setup =
  fixes
    A B C D::"'p" and
    U :: "'p set" and
    CPoints:: "'p set" and
    CLines:: "'l set" and
    c :: "('p, 'l) plane_r" and
    incidx :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
   assumes
    a1: "distinct [A, B, C, D]" and
    a2: "U = {A, B, C, D}"  and
    a3: "c = \<lparr> Points=CPoints, Lines=CLines, incid=incidx \<rparr>" and
    a4: "U \<subseteq> Points c" and
    a5: "\<lbrakk>X\<in> U; Y \<in> U; Z \<in> U; distinct[X,Y,Z]\<rbrakk> \<Longrightarrow>  \<nexists> n . n \<in> (Lines c) \<and>  incid c X n \<and> incid c Y n \<and> incid c Z n"
begin

lemma U_size:   "card U = 4" using a1 a2 by auto
lemma u_finite: "finite U" using U_size card_eq_0_iff by fastforce

(* 
Start with the four points of the configuration, and from them form four Base points, which we'll
call the basic points; for each pair of these, we have a basic line; these six lines are all distinct.
*)
find_theorems "Base_point"

definition "ff \<equiv> (\<lambda> P . Base_point P )"

definition  basic_points::"('p, 'l) fpoint set" where
"basic_points = ff ` U "
 
definition  basic_lines::"('p, 'l) fline set" where
"basic_lines = {m  . \<exists> P Q . P \<in> basic_points \<and> Q \<in> basic_points \<and> P \<noteq> Q \<and> fppincid c P m \<and> fppincid c Q m}"

lemma injbp: "inj ff" 
  using inj_def ff_def  by (metis fpoint.inject(1))

lemma basep_size: "card basic_points = 4" using a1 a2 u_finite U_size injbp 
  by (metis UNIV_I basic_points_def card_image inj_on_def)

lemma kcollin: 
  fixes x X Y Z k XY
  assumes "XY \<in> Pi_lines c \<and> k \<in> Pi_lines c"
  assumes "fppincid c X XY \<and> fppincid c Y XY"
  assumes " \<nexists> h. h  \<in> Pi_lines c \<and> fppincid c  X h \<and>fppincid c  Y h \<and> fppincid c  Z h  "
  shows "\<not> (fppincid c Z XY \<and> fppincid c Z k)"
  using assms(1,2,3) by blast

lemma nonXY:
  fixes X Y k XY
  assumes "fppincid c X XY \<and> fppincid c Y XY"
  shows "\<lbrakk>X \<noteq> Y; (\<not>fppincid c X k) \<or>  (\<not>fppincid c X k)\<rbrakk> \<Longrightarrow> XY \<noteq> k" using assms by auto

theorem ample_free_planes1:
  shows "\<And>P Q. P \<noteq> Q \<Longrightarrow> P \<in> Pi_points c \<Longrightarrow> Q \<in> Pi_points c \<Longrightarrow>
    \<exists>!k. k \<in> Pi_lines c \<and> fppincid c P k \<and> fppincid c Q k" 
proof (unfold_locales)
  fix P Q
  show "P \<noteq> Q \<Longrightarrow> P \<in> Pi_points c \<Longrightarrow>
           Q \<in> Pi_points c \<Longrightarrow>
           \<exists>!k. k \<in> Pi_lines c \<and> fppincid c P k \<and> fppincid c Q k"  using free_planes_unique_join
    by (smt (verit) U_size a3 a4 linorder_linear select_convs(1))
qed

lemma ample_lines_two_points:
  shows "\<And>k. k \<in> Pi_lines c \<Longrightarrow>  \<exists>P Q. P \<noteq> Q \<and> fppincid c P k \<and> fppincid c Q k \<and>P \<in> Pi_points c \<and> Q \<in> Pi_points c " 
proof -
  fix k
  assume a: "k \<in> Pi_lines c"
  have u1: "\<lbrakk>c = \<lparr>Points = CPoints, Lines = CLines, incid = incidx\<rparr>; 
    k \<in> Pi_lines c;  l_level k = l_level k;   U \<subseteq> CPoints;  card U = 4;
    (\<And>P Q R. distinct [P, Q, R] \<and> {P, Q, R} \<subseteq> U  \<Longrightarrow>  \<not> projective_plane_data.pcollinear c P Q R) \<rbrakk> \<Longrightarrow>
    \<exists>P Q. P \<noteq> Q \<and> fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c" using  fpp_two_points [of c CPoints CLines incidx k "l_level k" U] by auto
  then have u2: "\<lbrakk>c = \<lparr>Points = CPoints, Lines = CLines, incid = incidx\<rparr>; 
    k \<in> Pi_lines c;  U \<subseteq> CPoints;  card U = 4;
    (\<And>P Q R. distinct [P, Q, R] \<and> {P, Q, R} \<subseteq> U  \<Longrightarrow>  \<not> projective_plane_data.pcollinear c P Q R) \<rbrakk> \<Longrightarrow>
    \<exists>P Q. P \<noteq> Q \<and> fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c" by auto
  then have u3: "\<lbrakk> k \<in> Pi_lines c;  
    (\<And>P Q R. distinct [P, Q, R] \<and> {P, Q, R} \<subseteq> U  \<Longrightarrow>  \<not> projective_plane_data.pcollinear c P Q R) \<rbrakk> \<Longrightarrow>
    \<exists>P Q. P \<noteq> Q \<and> fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c" using a2 a3 a4 U_size by auto
  then have u4: "\<lbrakk>(\<And>P Q R. distinct [P, Q, R] \<and> {P, Q, R} \<subseteq> U  \<Longrightarrow>  \<not> projective_plane_data.pcollinear c P Q R) \<rbrakk> \<Longrightarrow>
    \<exists>P Q. P \<noteq> Q \<and> fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c" using a by auto
  then show u5: "\<exists>P Q. P \<noteq> Q \<and> fppincid c P k \<and> fppincid c Q k \<and> P \<in> Pi_points c \<and> Q \<in> Pi_points c" 
    using a4 unfolding projective_plane_data.pcollinear_def
  by (smt (verit, best) a5 empty_iff insert_subset projective_plane_data.intro projective_plane_data.pcollinear_def
      subset_trans)
qed

theorem ample_free_planes2:
  shows "\<And>k n.  (k::('p, 'l) fline) \<in> Pi_lines c \<Longrightarrow>  n \<in> Pi_lines c \<Longrightarrow> \<exists>P.
    P \<in> Pi_points c \<and>
    fppincid c P k \<and>
    fppincid c P n" 
proof (unfold_locales)
    fix k n
    assume kdef: "(k::('p, 'l) fline) \<in> Pi_lines c" and ndef: "n \<in> Pi_lines c"
    show "\<exists>P.  P \<in> Pi_points c \<and> fppincid c P k \<and> fppincid c P n" 
    proof (cases "k = n")
      case True
      then show ?thesis using ample_lines_two_points kdef by blast 
    next
      case False
      then show ?thesis by (metis crossing_point kdef linorder_linear ndef)
    qed
  qed

lemma ample_free_planes3:
  shows "\<exists>P Q R.
       P \<in> Pi_points c \<and>
       Q \<in> Pi_points c \<and> R \<in> Pi_points c \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> 
      \<not> projective_plane_data.pcollinear \<lparr> Points = (Pi_points c), Lines = (Pi_lines c), incid = (fppincid c) \<rparr> P Q R"
proof -
  define cfpp where "cfpp = \<lparr> Points = (Pi_points c), Lines = (Pi_lines c), incid = (fppincid c) \<rparr>"
  obtain P Q R S where pqrs: "U = {P,Q,R,S}" using  a2 by auto
  have dd: "distinct [P,Q,R]" using pqrs 
    by (smt (verit) a1 a2 card.empty card_insert_disjoint distinct.simps(2) empty_set finite_insert insert_absorb insert_commute
        list.simps(15) nat.simps(1,3) u_finite)
  have ee: "{P,Q, R} \<subseteq> U" using pqrs by simp
  then have ef: "{P,Q,R} \<subseteq> CPoints" using a3 a4 by auto
  have eg: "card {P,Q,R} = 3" using dd by fastforce
  have e1: "((distinct [P,Q,R]) \<and> ({P, Q, R} \<subseteq> U))" using dd ee conjI by blast
  have e2: " \<not> (projective_plane_data.pcollinear c P Q R)" using a4 e1 
    by (smt (verit) a5 bot.extremum_unique insertI1 insert_commute insert_not_empty projective_plane_data.intro projective_plane_data.pcollinear_def
      subsetD)
    then have e21: " \<not> (if (P \<in> CPoints \<and> Q \<in> CPoints \<and> R \<in> CPoints)  
      then (\<exists> l. l \<in> CLines \<and> incidx P l \<and> incidx Q l  \<and> incidx R l) else undefined)" 
      using a3 a5 e1 ef by auto
    have e3: " \<not> (\<exists>k \<in> CLines . incidx P k \<and> incidx Q k \<and> incidx R k)" using e2 ef e21 by auto
    (* make P, Q, R into Base_points called S, T, V and ...*)
    then have e4: "
       (Base_point P) \<in> Pi_points c \<and>
        (Base_point Q) \<in> Pi_points c \<and>
        (Base_point R) \<in> Pi_points c"
      by (metis (mono_tags, lifting) a4 ee insert_absorb insert_subset mem_Collect_eq new_points.simps(1) pi_points_contents)

    have e5:
        "(Base_point P) \<noteq> (Base_point Q) \<and>
         (Base_point P) \<noteq> (Base_point R) \<and>
         (Base_point Q) \<noteq> (Base_point R)" using dd by auto 
    have "c = \<lparr>Points = CPoints, Lines = CLines, incid = incidx\<rparr> \<Longrightarrow>
         card {P, Q, R} = 3 \<Longrightarrow>
         {P, Q, R} \<subseteq> CPoints \<Longrightarrow>
         \<not> (\<exists>k\<in>CLines. incidx P k \<and> incidx Q k \<and> incidx R k) \<Longrightarrow>
         \<not> (\<exists>m\<in>Pi_lines c. fppincid c (Base_point P) m \<and> fppincid c (Base_point Q) m \<and> fppincid c (Base_point R) m)" using  non_collinear_persistence [of c CPoints CLines incidx P Q R] by blast
    then have "
         \<not> (\<exists>k\<in>CLines. incidx P k \<and> incidx Q k \<and> incidx R k) \<Longrightarrow>
         \<not> (\<exists>m\<in>Pi_lines c. fppincid c (Base_point P) m \<and> fppincid c (Base_point Q) m \<and> fppincid c (Base_point R) m)" using a3 ef eg by blast
    then have q0: "\<not> (\<exists>m\<in>Pi_lines c. fppincid c (Base_point P) m \<and> fppincid c (Base_point Q) m \<and> fppincid c (Base_point R) m)" using e3 by blast

    thm "Chapter1-1R.projective_plane_data.pcollinear_def"  [of cfpp "(Base_point P)"  "(Base_point Q)"  "(Base_point R)"] 

    have "(projective_plane_data.pcollinear cfpp  (Base_point P)  (Base_point Q)  (Base_point R)) = 
      (if Base_point P \<in> Points cfpp \<and> Base_point Q \<in> Points cfpp \<and> Base_point R \<in> Points cfpp
       then \<exists>l. l \<in> Lines cfpp \<and> Base_point P \<lhd>\<^bsub>cfpp\<^esub> l \<and> Base_point Q \<lhd>\<^bsub>cfpp\<^esub> l \<and> Base_point R \<lhd>\<^bsub>cfpp\<^esub> l else undefined)" 
      using cfpp_def "Chapter1-1R.projective_plane_data.pcollinear_def" [of cfpp "(Base_point P)"  "(Base_point Q)"  "(Base_point R)"] 
      e4 projective_plane_data_def by fastforce
    then have "(projective_plane_data.pcollinear cfpp  (Base_point P)  (Base_point Q)  (Base_point R)) = 
       (\<exists>l. l \<in> Lines cfpp \<and> Base_point P \<lhd>\<^bsub>cfpp\<^esub> l \<and> Base_point Q \<lhd>\<^bsub>cfpp\<^esub> l \<and> Base_point R \<lhd>\<^bsub>cfpp\<^esub> l)" using e4  cfpp_def by auto
    then have "(projective_plane_data.pcollinear cfpp  (Base_point P)  (Base_point Q)  (Base_point R)) = 
       (\<exists>l. l \<in> Lines cfpp \<and> fppincid c (Base_point P) l \<and> fppincid c (Base_point Q) l \<and> fppincid c (Base_point R)  l)" by (simp add: cfpp_def)

    then have e6: " \<not> projective_plane_data.pcollinear cfpp  (Base_point P)  (Base_point Q)  (Base_point R)" 
    using cfpp_def q0 by auto

    show " \<exists>P Q R.
      P \<in> Pi_points c \<and>  Q \<in> Pi_points c \<and> R \<in> Pi_points c \<and> 
      P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> 
      \<not> projective_plane_data.pcollinear cfpp  P Q R" 
      by (meson e4 e5 e6) 
  qed


lemma ample_free_planes4:  (* Shows axiom P4 of a projective plane holds for free projective plane *)
(*  assumes imp: "\<And> P Q R . ((distinct [P,Q,R]) \<and> ({P, Q, R} \<subseteq> U)) \<Longrightarrow>  \<not> (projective_plane_data.pcollinear c P Q R)" *)
  shows "k \<in> Pi_lines c \<Longrightarrow> W = {P \<in> Pi_points c. fppincid c P k} \<Longrightarrow> \<exists>Q R S. Q \<in> W \<and> R \<in> W \<and> S \<in> W \<and> distinct [Q, R, S]"
proof -
  assume "k \<in> Pi_lines c"
  assume aw: "W = {P \<in> Pi_points c. fppincid c P k} "
  show "\<exists>Q R S. Q \<in> W \<and> R \<in> W \<and> S \<in> W \<and> distinct [Q, R, S]"
  proof -
    let ?f = "(\<lambda> x .  Base_point x)"
    have finj: "inj ?f" using inj_def by auto

    let ?H = " {P \<in> CPoints. fppincid c (Base_point P) k}"
    let ?K = "?f ` ?H"
    let ?V = "?f ` U"
    have "?V \<subseteq> Pi_points c" 
      using image_subset_iff mem_Collect_eq new_points.simps pi_points_contents
        select_convs subset_eq by (smt (verit) a4)
    have "card ?V = card U" using card_image inj_on_subset subset_UNIV finj by metis
    let ?count = "card(U \<inter> ?H)"
    consider (lots) "?count \<ge> 3" | (few) "?count \<le> 2" by linarith
    then show ?thesis 
    proof cases
      case lots
      let ?f = "\<lambda> x . Base_point x"
      have "inj ?f" using injI fpoint.inject finj by blast
      have g1: "card (?f ` (U \<inter> ?H)) = card (U \<inter> ?H)"   by (simp add: card_image inj_on_def)
      have g2: "(?f ` (U \<inter> ?H)) = ((?f ` U) \<inter> (?f `?H))" by blast
      have g3: "card ((?f ` U) \<inter> (?f `?H)) \<ge> 3"  by (metis g1 g2 lots)
      have g4: "card (?V \<inter> ?K) \<ge> 3" using g3 by blast
      obtain A B C  where tt: "(A::('p, 'l) fpoint) \<in>(?V \<inter> ?K) \<and> B \<in> (?V \<inter> ?K)  \<and> C \<in> (?V \<inter> ?K) \<and> distinct [A, B, C]" using g4 three_elements 
        by (metis (mono_tags, lifting) One_nat_def Suc_1 less_eq_Suc_le numeral_3_eq_3)
      then show ?thesis using tt
          by (smt (verit, del_insts) IntE \<open>(\<lambda>x. Base_point x) ` U \<subseteq> Pi_points c\<close> aw imageE mem_Collect_eq
           subset_eq)
    next
      case few
      have twopts: "card (U - {P \<in> CPoints. fppincid c (Base_point P) k}) \<ge> 2" 
        by (metis (lifting) Nat.add_diff_assoc U_size card_Diff_subset_Int few finite_Int nat_le_iff_add numeral_Bit0 u_finite)

      obtain Ac Bc where uu: "Ac \<in> U - ?H \<and> Bc \<in> U - ?H \<and> Ac \<noteq> Bc" using twopts 
        by (smt (verit) One_nat_def Suc_1 card_le_Suc_iff insertI1 insert_commute)     
      define V where "V = U - {Ac, Bc}"
      have "card V = 2" using U_size using V_def card.insert uu by auto
      then obtain Cc Dc where vv: "V = {Cc, Dc} \<and> Cc \<noteq> Dc" by (meson card_2_iff)
      define A::"('p, 'l) fpoint" where "A = Base_point Ac"
      define B::"('p, 'l) fpoint" where "B = Base_point Bc"
      define C::"('p, 'l) fpoint" where "C = Base_point Cc"
      define D::"('p, 'l) fpoint" where "D = Base_point Dc"
      have abdiff: "A \<noteq> B" by (simp add: A_def B_def uu)
      have acddiff: "A \<noteq> C \<and> A \<noteq> D" using A_def C_def D_def vv V_def uu by blast
      have "\<not> fppincid c A k \<and> \<not> fppincid c B k" using A_def B_def a3 a4 uu by auto
      obtain AC where "fppincid c A AC \<and>  fppincid c C AC \<and> AC \<in> Pi_lines c" 
        by (metis (no_types, lifting) A_def C_def Diff_iff V_def \<open>Base_point ` U \<subseteq> Pi_points c\<close> acddiff ample_free_planes1 image_subset_iff
          insertI1 uu vv)
      obtain AD where "fppincid c A AD \<and>  fppincid c D AD \<and> AD \<in> Pi_lines c"
        by (metis (mono_tags, lifting) A_def D_def Diff_iff V_def \<open>Base_point ` U \<subseteq> Pi_points c\<close> acddiff ample_free_planes1 image_subset_iff
          insert_iff uu vv)
      obtain AB where "fppincid c A AB \<and>  fppincid c B AB \<and> AB \<in> Pi_lines c" 
        by (metis (mono_tags, lifting) A_def B_def Diff_iff \<open>Base_point ` U \<subseteq> Pi_points c\<close> abdiff ample_free_planes1 image_subset_iff
          uu)
      obtain H where hdef: "fppincid c H AC \<and> fppincid c H k \<and> H \<in> Pi_points c"
        by (metis \<open>\<not> fppincid c A k \<and> \<not> fppincid c B k\<close> \<open>fppincid c A AC \<and> fppincid c C AC \<and> AC \<in> Pi_lines c\<close> \<open>k \<in> Pi_lines c\<close>
          crossing_point linorder_linear)
      obtain Y where ydef: "fppincid c Y AD \<and> fppincid c Y k \<and> Y \<in> Pi_points c" 
        by (metis \<open>\<not> fppincid c A k \<and> \<not> fppincid c B k\<close> \<open>fppincid c A AD \<and> fppincid c D AD \<and> AD \<in> Pi_lines c\<close> \<open>k \<in> Pi_lines c\<close>
          crossing_point linorder_linear)
      obtain Z where zdef: "fppincid c Z AB \<and> fppincid c Z k \<and> Z \<in> Pi_points c" 
        by (metis \<open>\<not> fppincid c A k \<and> \<not> fppincid c B k\<close> \<open>fppincid c A AB \<and> fppincid c B AB \<and> AB \<in> Pi_lines c\<close> \<open>k \<in> Pi_lines c\<close>
          crossing_point linorder_linear)
      have ACdiff: "AC \<noteq> k" 
      using \<open>\<not> fppincid c A k \<and> \<not> fppincid c B k\<close> \<open>fppincid c A AC \<and> fppincid c C AC \<and> AC \<in> Pi_lines c\<close> by auto
      have ADdiff: "AD \<noteq> k" 
        using \<open>\<not> fppincid c A k \<and> \<not> fppincid c B k\<close> \<open>fppincid c A AD \<and> fppincid c D AD \<and> AD \<in> Pi_lines c\<close> by auto
      have "Z \<noteq> Y" (* if so then AB and AD both contain Y, i.e. AY contains both B and D, so ABD collinear *)
      proof (rule ccontr)
        assume "\<not> (Z \<noteq> Y)"
        then have "Z = Y" by blast
        then have r0:"fppincid c Z AD \<and> fppincid c A AD" by (simp add: \<open>fppincid c A AD \<and> fppincid c D AD \<and> AD \<in> Pi_lines c\<close> ydef)  
        have r1:"fppincid c Z AB \<and> fppincid c A AB" by (simp add: \<open>fppincid c A AB \<and> fppincid c B AB \<and> AB \<in> Pi_lines c\<close> zdef)
        have r2:"Z \<noteq> A" using \<open>\<not> Z \<noteq> Y\<close> \<open>\<not> fppincid c A k \<and> \<not> fppincid c B k\<close> ydef by auto
        have r3: "AB = AD" using  r0 r1 r2 
          by (metis (no_types, lifting) A_def \<open>Base_point ` U \<subseteq> Pi_points c\<close> \<open>\<not> Z \<noteq> Y\<close> \<open>fppincid c A AB \<and> fppincid c B AB \<and> AB \<in> Pi_lines c\<close>
            \<open>fppincid c A AD \<and> fppincid c D AD \<and> AD \<in> Pi_lines c\<close> ample_free_planes1 image_subset_iff mem_Collect_eq set_diff_eq uu
            ydef)
        have r4: "fppincid c A AB \<and> fppincid c B AB \<and> fppincid c D AB" 
          using \<open>fppincid c A AB \<and> fppincid c B AB \<and> AB \<in> Pi_lines c\<close> \<open>fppincid c A AD \<and> fppincid c D AD \<and> AD \<in> Pi_lines c\<close> r3 by auto
        have r5: "distinct [Ac, Bc, Dc]" using V_def uu vv by auto
        have r6: "Ac \<in> U \<and> Bc \<in> U \<or> Dc \<in> U" using uu by blast
        thm non_collinear_persistence [of c CPoints CLines incidx Ac Bc Dc]
        have r7: "\<not>( \<exists>m\<in>Pi_lines c.
           fppincid c (Base_point Ac) m \<and>
           fppincid c (Base_point Bc) m \<and>
           fppincid c (Base_point Dc) m)" using a5 r5 r6  non_collinear_persistence [of c CPoints CLines incidx Ac Bc Dc]
          by (smt (verit, del_insts) Diff_subset V_def a3 a4 card.empty card.insert card_gt_0_iff distinct.simps(2) finite.intros(1)
            insert_subset list.set(1,2) numeral_3_eq_3 select_convs(1,2,3) subset_iff uu vv zero_less_Suc)
        show False using r4 r7 
          using A_def B_def D_def \<open>fppincid c A AB \<and> fppincid c B AB \<and> AB \<in> Pi_lines c\<close> by blast
      qed

      have "Z \<noteq> H" (* if so then AC and CD both contain Z, i.e. CZ contains both A and D, so ACD collinear *)
      proof (rule ccontr)
        assume "\<not> (Z \<noteq> H)"
        then have "Z = H" by blast
        then have r0:"fppincid c Z AC \<and> fppincid c A AC"
        using \<open>fppincid c A AC \<and> fppincid c C AC \<and> AC \<in> Pi_lines c\<close> hdef by blast 
        have r1:"fppincid c Z AB \<and> fppincid c A AB"
        by (simp add: \<open>fppincid c A AB \<and> fppincid c B AB \<and> AB \<in> Pi_lines c\<close> zdef)
        have r2:"Z \<noteq> A" 
        using \<open>\<not> fppincid c A k \<and> \<not> fppincid c B k\<close> zdef by blast
        have r3: "AC = AB" using  r0 r1 r2 
        using A_def \<open>Base_point ` U \<subseteq> Pi_points c\<close> \<open>\<not> Z \<noteq> H\<close> \<open>fppincid c A AB \<and> fppincid c B AB \<and> AB \<in> Pi_lines c\<close>
          \<open>fppincid c A AC \<and> fppincid c C AC \<and> AC \<in> Pi_lines c\<close> ample_free_planes1 hdef uu by fastforce
        have r4: "fppincid c A AC \<and> fppincid c C AC \<and> fppincid c B AC" 
        using \<open>fppincid c A AB \<and> fppincid c B AB \<and> AB \<in> Pi_lines c\<close> \<open>fppincid c A AC \<and> fppincid c C AC \<and> AC \<in> Pi_lines c\<close> r3 by auto 
        have r5: "distinct [Ac, Bc, Cc]" using V_def uu vv by auto
        have r6: "Ac \<in> U \<and> Bc \<in> U \<or> Cc \<in> U" using uu by blast
        thm non_collinear_persistence [of c CPoints CLines incidx Ac Bc Cc]
        have r7: "\<not>( \<exists>m\<in>Pi_lines c.
           fppincid c (Base_point Ac) m \<and>
           fppincid c (Base_point Bc) m \<and>
           fppincid c (Base_point Cc) m)" using a5 r5 r6  non_collinear_persistence [of c CPoints CLines incidx Ac Bc Cc]
        by (smt (verit, del_insts) Diff_subset V_def a3 a4 card.empty card.insert card_gt_0_iff distinct.simps(2) finite.intros(1)
            insert_subset list.set(1,2) numeral_3_eq_3 select_convs(1,2,3) subset_iff uu vv zero_less_Suc)
        show False using r4 r7 
          using A_def C_def B_def \<open>fppincid c A AC \<and> fppincid c C AC \<and> AC \<in> Pi_lines c\<close> by blast
      qed

      have "H \<noteq> Y" (* if so then AC and AD both contain H, i.e. AH contains both A and C, so ACD collinear *)
      proof (rule ccontr)
        assume "\<not> (H \<noteq> Y)"
        then have "H = Y" by blast
        then have r0:"fppincid c H AC \<and> fppincid c A AC"
        using \<open>fppincid c A AC \<and> fppincid c C AC \<and> AC \<in> Pi_lines c\<close> hdef by blast
        have r1:"fppincid c H AD \<and> fppincid c A AD"
        using \<open>\<not> H \<noteq> Y\<close> \<open>fppincid c A AD \<and> fppincid c D AD \<and> AD \<in> Pi_lines c\<close> ydef by auto
        have r2:"H \<noteq> A" using \<open>\<not> fppincid c A k \<and> \<not> fppincid c B k\<close> hdef by blast 
        have r3: "AC = AD" using  r0 r1 r2 
        using A_def \<open>Base_point ` U \<subseteq> Pi_points c\<close> \<open>fppincid c A AC \<and> fppincid c C AC \<and> AC \<in> Pi_lines c\<close>
          \<open>fppincid c A AD \<and> fppincid c D AD \<and> AD \<in> Pi_lines c\<close> ample_free_planes1 hdef uu by fastforce
        then have r4: "fppincid c A AC \<and> fppincid c C AC \<and> fppincid c D AC"
        using \<open>fppincid c A AC \<and> fppincid c C AC \<and> AC \<in> Pi_lines c\<close> \<open>fppincid c A AD \<and> fppincid c D AD \<and> AD \<in> Pi_lines c\<close> by blast 
        have r5: "distinct [Ac, Cc, Dc]" using V_def uu vv by auto
        have r6: "Ac \<in> U \<and> Cc \<in> U \<or> Dc \<in> U" using uu  using V_def vv by blast
        thm non_collinear_persistence [of c CPoints CLines incidx Ac Cc Dc]
        have r7: "\<not>( \<exists>m\<in>Pi_lines c.
           fppincid c (Base_point Ac) m \<and>
           fppincid c (Base_point Cc) m \<and>
           fppincid c (Base_point Dc) m)" using a5 r5 r6  non_collinear_persistence [of c CPoints CLines incidx Ac Cc Dc] 
        by (smt (verit, del_insts) Diff_subset V_def a3 a4 card.empty card.insert distinct.simps(2) finite.intros(1) finite_insert
            insert_subset list.set(1,2) numeral_3_eq_3 select_convs(1,2,3) subset_iff uu vv)
        show False using r4 r7 
        using A_def C_def D_def \<open>fppincid c A AC \<and> fppincid c C AC \<and> AC \<in> Pi_lines c\<close> by blast
      qed

      have dd: "distinct [H, Y, Z]" using \<open>H \<noteq> Y\<close> \<open>Z \<noteq> H\<close> \<open>Z \<noteq> Y\<close> by auto
      then show ?thesis using hdef ydef zdef dd aw by blast 
    qed
  qed
qed


theorem ample_free_plane_is_projective_plane:
  assumes "cfpp = \<lparr> Points = (Pi_points c), Lines = (Pi_lines c), incid = (fppincid c) \<rparr>"
  shows "projective_plane cfpp"
proof (unfold_locales)
  show "Points cfpp \<noteq>  {}" using ample_free_planes3 assms by auto
next
  fix P Q
  show  "\<lbrakk>P \<noteq> Q ;P \<in> Points cfpp; Q \<in> Points cfpp\<rbrakk> \<Longrightarrow>
           \<exists>!k. k \<in> Lines cfpp \<and> P \<lhd>\<^bsub>cfpp\<^esub> k \<and> Q \<lhd>\<^bsub>cfpp\<^esub> k" using ample_free_planes1 by (simp add: assms)
next
  fix k n
  show "\<lbrakk>k \<in> Lines cfpp; n \<in> Lines cfpp \<rbrakk> \<Longrightarrow>
       \<exists>P. P \<in> Points cfpp \<and> P \<lhd>\<^bsub>cfpp\<^esub> k \<and> P \<lhd>\<^bsub>cfpp\<^esub> n"
    by (simp add: ample_free_planes2 assms)
next
  show "\<exists>P Q R.
       P \<in> Points cfpp \<and>
       Q \<in> Points cfpp \<and>
       R \<in> Points cfpp \<and>
       P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       \<not> projective_plane_data.pcollinear
           cfpp P Q R" using ample_free_planes3 by (simp add:assms)
next
  fix k X 
  show  "\<lbrakk>k \<in> Lines cfpp; X = {P \<in> Points cfpp. P \<lhd>\<^bsub>cfpp\<^esub> k}\<rbrakk> \<Longrightarrow>
           \<exists>Q R S. Q \<in> X \<and> R \<in> X \<and> S \<in> X \<and>
              distinct [Q, R, S]" using ample_free_planes4 assms by simp
qed

end

locale confined_configuration = 
  configuration S for S::"('p, 'l) plane_r" (structure) + 
 
  assumes C2: "U \<in> Points S \<Longrightarrow> \<exists> k l m  . k \<in> Lines S \<and> l \<in> Lines S \<and> m \<in> Lines S \<and> 
  incid S U k \<and> incid S U l \<and> incid S U m \<and> distinct [k, l,m]"
  assumes C3: "k \<in> Lines S \<Longrightarrow> \<exists> P Q R  . P \<in>Points S \<and> Q \<in> Points S \<and> R \<in> Points S \<and> 
  incid S P k \<and> incid S Q k \<and> incid S R k \<and> distinct [P, Q, R]"
begin
end

lemma desargues_is_cconfig:
  shows "confined_configuration \<lparr> Points=PointsD, Lines=LinesD, incid=incidD \<rparr>"
proof -
  have "?thesis \<equiv> (configuration     \<lparr>Points = PointsD, Lines = LinesD, incid = incidD\<rparr>) \<and>
    confined_configuration_axioms
     \<lparr>Points = PointsD, Lines = LinesD, incid = incidD\<rparr>" 
    by (simp add: confined_configuration_def)
  then have restate: "?thesis  \<equiv>  confined_configuration_axioms
     \<lparr>Points = PointsD, Lines = LinesD, incid = incidD\<rparr>" using desargues_is_config by force
  fix U k l m 
  have three_lines_per_point: "U \<in> PointsD \<longrightarrow> (\<exists> k l m  . k \<in> LinesD \<and> l \<in> LinesD \<and> m \<in> LinesD \<and> 
  incidD U k \<and> incidD U l \<and> incidD U m \<and> distinct [k, l,m])" for U using desargues_three_lines by blast
  then have three_points_per_line: "k \<in> LinesD  \<longrightarrow> (\<exists> P Q R  . P \<in>PointsD  \<and> Q \<in> PointsD  \<and> R \<in> PointsD  \<and> 
  incidD  P k \<and> incidD  Q k \<and> incidD  R k \<and> distinct [P, Q, R])" for k
  by (metis PointsD_def UNIV_I desargues_three_points incidD_def lessI numeral_eq_Suc pred_numeral_simps(3)
      three_elements)
  have cc: "confined_configuration_axioms
     \<lparr>Points = PointsD, Lines = LinesD, incid = incidD\<rparr>" using three_points_per_line three_lines_per_point
  by (smt (verit, del_insts) One_nat_def PointsD_def Suc_1 UNIV_I confined_configuration_axioms_def desargues_three_lines
      desargues_three_points incidD_def lessI numeral_3_eq_3 select_convs(1,2,3) three_elements)
  show ?thesis using cc restate by auto
qed

theorem confined_config_in_base: 
  fixes c PointsCC LinesCC 
  assumes "cfpp = \<lparr> Points = (Pi_points c), Lines = (Pi_lines c), incid = (fppincid c) \<rparr>"
  assumes "PointsCC \<subseteq> (Pi_points c)" and "LinesCC \<subseteq> (Pi_lines c)"
  assumes "cc =\<lparr>Points = PointsCC, Lines = LinesCC, incid = (fppincid c) \<rparr>"
  assumes "confined_configuration cc"
  assumes "finite PointsCC" and "finite LinesCC"
  defines "ptop \<equiv> Max {p_level p | p . p \<in> PointsCC}"
  defines "ltop \<equiv> Max {l_level k | k . k \<in> LinesCC}"
  shows "max ptop ltop  = 0"
  sorry

end
