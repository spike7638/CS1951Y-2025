theory "Chapter2-2"
  imports  "HOL-Library.Uprod" 
           "Chapter2-1"

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


locale ample_fpp_setup = configuration CPoints CLines incidx for
CPoints CLines incidx +
  fixes
    A B C D U
(*  and
  CPoints:: "'p set" and
    CLines:: "'l set" and
    incidx :: "'p \<Rightarrow> 'l \<Rightarrow> bool" *)
   assumes
    a1: "distinct[A, B, C, D]" and
    a2: "U = {A, B, C, D}"  and
    a4: "U \<subseteq> CPoints" and
    a5: "\<lbrakk>X\<in> U; Y \<in> U; Z \<in> U; distinct[X, Y, Z] \<rbrakk> \<Longrightarrow>  \<nexists> n . n \<in> (CLines) \<and>  incidx X n \<and> incidx  Y n \<and> incidx Z n"     
begin

lemma U_size:   "card U = 4" using a1 a2 unfolding distinct4_def by auto
lemma u_finite: "finite U" using a2 by blast

(* 
Start with the four points of the configuration, and from them form four Base points, which we'll
call the basic points; for each pair of these, we have a basic line; these six lines are all distinct.
*)
find_theorems "Base_point"

definition "ff \<equiv> (\<lambda> P . Base_point P )"

definition  basic_points where
"basic_points = ff ` U "
 
definition  basic_lines where
"basic_lines = {m  . \<exists> P Q . P \<in> basic_points \<and> Q \<in> basic_points \<and> P \<noteq> Q \<and> fppincid P m \<and> fppincid Q m}"

lemma injbp: "inj ff" 
  using inj_def ff_def  by (metis fpoint.inject(1))

lemma basep_size: "card basic_points = 4" using a1 a2 u_finite U_size injbp 
  by (metis UNIV_I basic_points_def card_image inj_on_def)

lemma kcollin: 
  fixes x X Y Z k XY
  assumes "XY \<in> Pi_lines  \<and> k \<in> Pi_lines "
  assumes "fppincid  X XY \<and> fppincid  Y XY"
  assumes " \<nexists> h. h  \<in> Pi_lines  \<and> fppincid   X h \<and>fppincid   Y h \<and> fppincid Z h  "
  shows "\<not> (fppincid Z XY \<and> fppincid Z k)"
  using assms(1,2,3) by blast

lemma nonXY:
  fixes X Y k XY
  assumes "fppincid X XY \<and> fppincid Y XY"
  shows "\<lbrakk>X \<noteq> Y; (\<not>fppincid X k) \<or>  (\<not>fppincid X k)\<rbrakk> \<Longrightarrow> XY \<noteq> k" using assms by auto

theorem ample_free_planes1:
  shows "\<And>P Q. P \<noteq> Q \<Longrightarrow> P \<in> Pi_points \<Longrightarrow> Q \<in> Pi_points \<Longrightarrow>
    \<exists>!k. k \<in> Pi_lines \<and> fppincid P k \<and> fppincid Q k" 
proof (unfold_locales)
  fix P Q
  show "P \<noteq> Q \<Longrightarrow> P \<in> Pi_points \<Longrightarrow>
           Q \<in> Pi_points \<Longrightarrow>
           \<exists>!k. k \<in> Pi_lines \<and> fppincid P k \<and> fppincid Q k"  using free_planes_unique_join
  using U_size a4 by auto
qed

lemma ample_lines_two_points:
  shows "\<And>k. k \<in> Pi_lines \<Longrightarrow>  \<exists>P Q. P \<noteq> Q \<and> fppincid P k \<and> fppincid Q k \<and>
     P \<in> Pi_points \<and> Q \<in> Pi_points " 
proof -
  fix k
  assume a: "k \<in> Pi_lines"
  have u1: "\<lbrakk>k \<in> Pi_lines;  l_level k = l_level k;   U \<subseteq> CPoints;  card U = 4;
    (\<And>P Q R. distinct[P, Q, R] \<and> {P, Q, R} \<subseteq> U  \<Longrightarrow>  \<not> projective_plane_data.pcollinear CPoints CLines incidx P Q R) \<rbrakk> \<Longrightarrow>
    \<exists>P Q. P \<noteq> Q \<and> fppincid P k \<and> fppincid Q k \<and> P \<in> Pi_points \<and> Q \<in> Pi_points" using  fpp_two_points [of k "l_level k" U] 
    by simp
  then have u2: "\<lbrakk>k \<in> Pi_lines;  U \<subseteq> CPoints;  card U = 4;
    (\<And>P Q R.  distinct[P, Q, R] \<and> {P, Q, R} \<subseteq> U  \<Longrightarrow>  \<not> projective_plane_data.pcollinear CPoints CLines incidx P Q R) \<rbrakk> \<Longrightarrow>
    \<exists>P Q. P \<noteq> Q \<and> fppincid P k \<and> fppincid Q k \<and> P \<in> Pi_points \<and> Q \<in> Pi_points" by auto
  then have u3: "\<lbrakk> k \<in> Pi_lines;  
    (\<And>P Q R.  distinct[P, Q, R] \<and> {P, Q, R} \<subseteq> U  \<Longrightarrow>  \<not> projective_plane_data.pcollinear CPoints CLines incidx P Q R) \<rbrakk> \<Longrightarrow>
    \<exists>P Q. P \<noteq> Q \<and> fppincid P k \<and> fppincid Q k \<and> P \<in> Pi_points \<and> Q \<in> Pi_points " using a2 a4 U_size unfolding distinct3_def by auto
  then have u4: "\<lbrakk>(\<And>P Q R.   distinct[P, Q, R] \<and> {P, Q, R} \<subseteq> U  \<Longrightarrow>  \<not> projective_plane_data.pcollinear CPoints CLines incidx P Q R) \<rbrakk> \<Longrightarrow>
    \<exists>P Q. P \<noteq> Q \<and> fppincid P k \<and> fppincid Q k \<and> P \<in> Pi_points \<and> Q \<in> Pi_points " using a unfolding distinct3_def by auto
  then show u5: "\<exists>P Q. P \<noteq> Q \<and> fppincid P k \<and> fppincid Q k \<and> P \<in> Pi_points \<and>
     Q \<in> Pi_points" 
    using a4 a5 unfolding projective_plane_data.pcollinear_def 
    unfolding distinct3_def 
  by (smt (verit, best) insert_subset pcollinear_def subset_trans)
qed

theorem ample_free_planes2:
  shows "\<And>k n.  k \<in> Pi_lines \<Longrightarrow>  n \<in> Pi_lines \<Longrightarrow> \<exists>P.
    P \<in> Pi_points \<and>
    fppincid P k \<and>
    fppincid P n" 
proof (unfold_locales)
    fix k n
    assume kdef: "k \<in> Pi_lines" and ndef: "n \<in> Pi_lines"
    show "\<exists>P.  P \<in> Pi_points \<and> fppincid P k \<and> fppincid P n" 
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
       P \<in> Pi_points \<and>
       Q \<in> Pi_points \<and> R \<in> Pi_points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> 
      \<not> projective_plane_data.pcollinear Pi_points Pi_lines fppincid P Q R"
proof -
  obtain P Q R S where pqrs: "U = {P,Q,R,S}" using  a2 by auto
  have dd: " distinct[P, Q, R] " unfolding distinct3_def  distinct4_def using pqrs 
    by (smt (verit, best) a1 a2 distinct4_def insert_iff singleton_iff)
  have ee: "{P,Q, R} \<subseteq> U" using pqrs by simp
  then have ef: "{P,Q,R} \<subseteq> CPoints" using a4 by auto
  have eg: "card {P,Q,R} = 3" using dd unfolding distinct3_def by fastforce
  have e1: "(( distinct[P, Q, R]) \<and> ({P, Q, R} \<subseteq> U))" using dd ee conjI unfolding distinct3_def by auto
  have e2: " \<not> (projective_plane_data.pcollinear CPoints CLines incidx P Q R)" 
    using a4 a5 dd ef e1 insert_subset pcollinear_def unfolding distinct3_def by metis
  then have e21: " \<not> (if (P \<in> CPoints \<and> Q \<in> CPoints \<and> R \<in> CPoints)  
      then (\<exists> l. l \<in> CLines \<and> incidx P l \<and> incidx Q l  \<and> incidx R l) else undefined)" 
    using  a5 e1 ef using pcollinear_def by force
  have e3: " \<not> (\<exists>k \<in> CLines . incidx P k \<and> incidx Q k \<and> incidx R k)" using e2 ef e21 by auto
      (* make P, Q, R into Base_points called S, T, V and ...*)
  then have e4: "
       (Base_point P) \<in> Pi_points \<and>
        (Base_point Q) \<in> Pi_points \<and>
        (Base_point R) \<in> Pi_points"
    by (metis (mono_tags, lifting) ef insert_subset mem_Collect_eq new_points.simps(1) point_containment)

  have e5:
    "(Base_point P) \<noteq> (Base_point Q) \<and>
         (Base_point P) \<noteq> (Base_point R) \<and>
         (Base_point Q) \<noteq> (Base_point R)" using dd unfolding distinct3_def by auto 
  have "card {P, Q, R} = 3 \<Longrightarrow>
         {P, Q, R} \<subseteq> CPoints \<Longrightarrow>
         \<not> (\<exists>k\<in>CLines. incidx P k \<and> incidx Q k \<and> incidx R k) \<Longrightarrow>
         \<not> (\<exists>m\<in>Pi_lines . fppincid (Base_point P) m \<and> fppincid (Base_point Q) m \<and> fppincid (Base_point R) m)" 
    using  non_collinear_persistence by auto
  then have "
         \<not> (\<exists>k\<in>CLines. incidx P k \<and> incidx Q k \<and> incidx R k) \<Longrightarrow>
         \<not> (\<exists>m\<in>Pi_lines . fppincid (Base_point P) m \<and> fppincid (Base_point Q) m \<and> fppincid (Base_point R) m)" using  ef eg by blast
  then have q0: "\<not> (\<exists>m\<in>Pi_lines . fppincid (Base_point P) m \<and> fppincid (Base_point Q) m \<and> fppincid (Base_point R) m)" using e3 by blast


  have "(projective_plane_data.pcollinear Pi_points Pi_lines fppincid  (Base_point P)  (Base_point Q)  (Base_point R)) = 
      (if Base_point P \<in> Pi_points  \<and> Base_point Q \<in>  Pi_points \<and> Base_point R \<in>  Pi_points
       then \<exists>l. l \<in>  Pi_lines \<and> fppincid (Base_point P)  l \<and>  fppincid (Base_point Q) l \<and>  fppincid (Base_point R) l else undefined)" 
    using "projective_plane_data.pcollinear_def" [of Pi_points Pi_lines fppincid "(Base_point P)"  "(Base_point Q)"  "(Base_point R)"] 
      e4  by fastforce

  then have "(projective_plane_data.pcollinear Pi_points Pi_lines fppincid  (Base_point P)  (Base_point Q)  (Base_point R)) =
       (\<exists>l. l \<in>  Pi_lines \<and> fppincid (Base_point P)  l \<and>  fppincid (Base_point Q) l \<and>  fppincid (Base_point R) l)" using e4  by auto
  then have "(projective_plane_data.pcollinear Pi_points Pi_lines fppincid  (Base_point P)  (Base_point Q)  (Base_point R)) =
       (\<exists>l. l \<in> Pi_lines \<and> fppincid (Base_point P) l \<and> fppincid (Base_point Q) l \<and> fppincid (Base_point R)  l)" by (simp )

  then have e6: " \<not> projective_plane_data.pcollinear  Pi_points Pi_lines fppincid   (Base_point P)  (Base_point Q)  (Base_point R)" 
    using  q0 by auto

  show " \<exists>P Q R.
      P \<in> Pi_points \<and>  Q \<in> Pi_points \<and> R \<in> Pi_points \<and> 
      P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> 
      \<not> projective_plane_data.pcollinear  Pi_points Pi_lines fppincid   P Q R" 
    by (meson e4 e5 e6) 
qed

(*
lemma three_members:
  fixes X
  assumes "card(X) \<ge> 3"
  obtains P Q R where "P \<in> X \<and> Q \<in> X \<and> R \<in> X \<and> distinct[P, Q, R]"
  unfolding distinct3_def by sledgehammer
*)


lemma ample_free_planes4:  
  shows "k \<in> Pi_lines \<Longrightarrow> W = {P \<in> Pi_points . fppincid P k} \<Longrightarrow> \<exists>Q R S. Q \<in> W \<and> R \<in> W \<and> S \<in> W \<and> distinct[Q, R, S]"
proof -
  assume "k \<in> Pi_lines "
  assume aw: "W = {P \<in> Pi_points . fppincid P k} "
  show "\<exists>Q R S. Q \<in> W \<and> R \<in> W \<and> S \<in> W \<and> distinct[Q, R, S]"
  proof -
    let ?f = "(\<lambda> x .  Base_point x)"
    have finj: "inj ?f" using inj_def by auto

    let ?H = " {P \<in> CPoints. fppincid (Base_point P) k}"
    let ?K = "?f ` ?H"
    let ?V = "?f ` U"
    have "?V \<subseteq> Pi_points " 
      using image_subset_iff mem_Collect_eq new_points.simps pi_points_contents
         subset_eq by (smt (verit) a4)
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
      obtain A B C  where tt: "(A::('a, 'b) fpoint) \<in>(?V \<inter> ?K) \<and> B \<in> (?V \<inter> ?K)  \<and> C \<in> (?V \<inter> ?K) \<and> distinct[A, B, C]" 
        unfolding distinct3_def distinct4_def using g4 three_elements card_le_Suc_iff insertCI numeral_3_eq_3 
      by (smt (verit, ccfv_SIG) card_insert_disjoint distinct_length_2_or_more less_Suc_eq_le numeral_2_eq_2)
      then show ?thesis using tt 
      by (smt (verit) Int_iff \<open>Base_point ` U \<subseteq> Pi_points\<close> aw imageE mem_Collect_eq subset_eq)
    next
      case few
      have twopts: "card (U - {P \<in> CPoints. fppincid (Base_point P) k}) \<ge> 2" 
        by (metis (lifting) Nat.add_diff_assoc U_size card_Diff_subset_Int few finite_Int nat_le_iff_add numeral_Bit0 u_finite)

      obtain Ac Bc where uu: "Ac \<in> U - ?H \<and> Bc \<in> U - ?H \<and> Ac \<noteq> Bc" using twopts 
        by (smt (verit) One_nat_def Suc_1 card_le_Suc_iff insertI1 insert_commute)     
      define V where "V = U - {Ac, Bc}"
      have "card V = 2" using U_size using V_def card.insert uu by auto
      then obtain Cc Dc where vv: "V = {Cc, Dc} \<and> Cc \<noteq> Dc" by (meson card_2_iff)
      define A::"('a, 'b) fpoint" where "A = Base_point Ac"
      define B::"('a, 'b) fpoint" where "B = Base_point Bc"
      define C::"('a, 'b) fpoint" where "C = Base_point Cc"
      define D::"('a, 'b) fpoint" where "D = Base_point Dc"
      have abdiff: "A \<noteq> B" by (simp add: A_def B_def uu)
      have acddiff: "A \<noteq> C \<and> A \<noteq> D" using A_def C_def D_def vv V_def uu by blast
      have "\<not> fppincid A k \<and> \<not> fppincid B k" using A_def B_def  a4 uu by auto
      obtain AC where "fppincid A AC \<and>  fppincid C AC \<and> AC \<in> Pi_lines"
        by (metis (no_types, lifting) A_def C_def Diff_iff V_def \<open>Base_point ` U \<subseteq> Pi_points\<close> acddiff ample_free_planes1 image_subset_iff
          insertI1 uu vv)
      obtain AD where "fppincid A AD \<and>  fppincid D AD \<and> AD \<in> Pi_lines"
        by (metis (mono_tags, lifting) A_def D_def Diff_iff V_def \<open>Base_point ` U \<subseteq> Pi_points\<close> acddiff ample_free_planes1 image_subset_iff
          insert_iff uu vv)
      obtain AB where "fppincid A AB \<and>  fppincid B AB \<and> AB \<in> Pi_lines" 
        by (metis (mono_tags, lifting) A_def B_def Diff_iff \<open>Base_point ` U \<subseteq> Pi_points\<close> abdiff ample_free_planes1 image_subset_iff
          uu)
      obtain H where hdef: "fppincid H AC \<and> fppincid H k \<and> H \<in> Pi_points"
        by (metis \<open>\<not> fppincid A k \<and> \<not> fppincid B k\<close> \<open>fppincid A AC \<and> fppincid C AC \<and> AC \<in> Pi_lines\<close> \<open>k \<in> Pi_lines\<close>
          crossing_point linorder_linear)
      obtain Y where ydef: "fppincid Y AD \<and> fppincid Y k \<and> Y \<in> Pi_points" 
        by (metis \<open>\<not> fppincid A k \<and> \<not> fppincid B k\<close> \<open>fppincid A AD \<and> fppincid D AD \<and> AD \<in> Pi_lines\<close> \<open>k \<in> Pi_lines\<close>
          crossing_point linorder_linear)
      obtain Z where zdef: "fppincid Z AB \<and> fppincid Z k \<and> Z \<in> Pi_points" 
        by (metis \<open>\<not> fppincid A k \<and> \<not> fppincid B k\<close> \<open>fppincid A AB \<and> fppincid B AB \<and> AB \<in> Pi_lines\<close> \<open>k \<in> Pi_lines\<close>
          crossing_point linorder_linear)
      have ACdiff: "AC \<noteq> k" 
      using \<open>\<not> fppincid A k \<and> \<not> fppincid B k\<close> \<open>fppincid A AC \<and> fppincid C AC \<and> AC \<in> Pi_lines\<close> by auto
      have ADdiff: "AD \<noteq> k" 
        using \<open>\<not> fppincid A k \<and> \<not> fppincid B k\<close> \<open>fppincid A AD \<and> fppincid D AD \<and> AD \<in> Pi_lines\<close> by auto
      have "Z \<noteq> Y" (* if so then AB and AD both contain Y, i.e. AY contains both B and D, so ABD collinear *)
      proof (rule ccontr)
        assume "\<not> (Z \<noteq> Y)"
        then have "Z = Y" by blast
        then have r0:"fppincid Z AD \<and> fppincid A AD" by (simp add: \<open>fppincid A AD \<and> fppincid D AD \<and> AD \<in> Pi_lines\<close> ydef)  
        have r1:"fppincid Z AB \<and> fppincid A AB" by (simp add: \<open>fppincid A AB \<and> fppincid B AB \<and> AB \<in> Pi_lines\<close> zdef)
        have r2:"Z \<noteq> A" using \<open>\<not> Z \<noteq> Y\<close> \<open>\<not> fppincid A k \<and> \<not> fppincid B k\<close> ydef by auto
        have r3: "AB = AD" using  r0 r1 r2 
          using A_def \<open>Base_point ` U \<subseteq> Pi_points\<close> \<open>\<not> Z \<noteq> Y\<close> \<open>fppincid A AB \<and> fppincid B AB \<and> AB \<in> Pi_lines\<close> \<open>fppincid A AD \<and> fppincid D AD \<and> AD \<in> Pi_lines\<close>
          ample_free_planes1 image_subset_iff uu ydef by blast
        have r4: "fppincid A AB \<and> fppincid B AB \<and> fppincid D AB" 
          using \<open>fppincid A AB \<and> fppincid B AB \<and> AB \<in> Pi_lines\<close> \<open>fppincid A AD \<and> fppincid D AD \<and> AD \<in> Pi_lines\<close> r3 by auto
        have r5: "distinct[Ac, Bc, Dc]" unfolding distinct3_def using V_def uu vv by auto
        have r6: "Ac \<in> U \<and> Bc \<in> U \<or> Dc \<in> U" using uu by blast
        have r7: "\<not>( \<exists>m\<in>Pi_lines .
           fppincid (Base_point Ac) m \<and>
           fppincid (Base_point Bc) m \<and>
           fppincid (Base_point Dc) m)" using a5 r5 r6  non_collinear_persistence [of Ac Bc Dc]
        by (metis (no_types, opaque_lifting) card_3_iff distinct3_def dual_order.refl empty_iff)
        show False using r4 r7 
          using A_def B_def D_def \<open>fppincid A AB \<and> fppincid B AB \<and> AB \<in> Pi_lines\<close> by blast
      qed

      have "Z \<noteq> H" (* if so then AC and CD both contain Z, i.e. CZ contains both A and D, so ACD collinear *)
      proof (rule ccontr)
        assume "\<not> (Z \<noteq> H)"
        then have "Z = H" by blast
        then have r0:"fppincid Z AC \<and> fppincid A AC"
        using \<open>fppincid A AC \<and> fppincid C AC \<and> AC \<in> Pi_lines\<close> hdef by blast 
        have r1:"fppincid Z AB \<and> fppincid A AB"
        by (simp add: \<open>fppincid A AB \<and> fppincid B AB \<and> AB \<in> Pi_lines\<close> zdef)
        have r2:"Z \<noteq> A" 
        using \<open>\<not> fppincid A k \<and> \<not> fppincid B k\<close> zdef by blast
        have r3: "AC = AB" using  r0 r1 r2 
        using A_def \<open>Base_point ` U \<subseteq> Pi_points\<close> \<open>\<not> Z \<noteq> H\<close> \<open>fppincid A AB \<and> fppincid B AB \<and> AB \<in> Pi_lines\<close>
          \<open>fppincid A AC \<and> fppincid C AC \<and> AC \<in> Pi_lines\<close> ample_free_planes1 hdef uu by fastforce
        have r4: "fppincid A AC \<and> fppincid C AC \<and> fppincid B AC" 
        using \<open>fppincid A AB \<and> fppincid B AB \<and> AB \<in> Pi_lines\<close> \<open>fppincid A AC \<and> fppincid C AC \<and> AC \<in> Pi_lines\<close> r3 by auto 
        have r5: "distinct[Ac, Bc, Cc]" unfolding distinct3_def using V_def uu vv  by auto
        have r6: "Ac \<in> U \<and> Bc \<in> U \<or> Cc \<in> U" using uu by blast
        have r7: "\<not>( \<exists>m\<in>Pi_lines .
           fppincid (Base_point Ac) m \<and>
           fppincid (Base_point Bc) m \<and>
           fppincid (Base_point Cc) m)" using a4 a5 r5 r6  non_collinear_persistence [of Ac Bc Cc] 
          by (metis card_3_iff distinct3_def dual_order.refl empty_iff)
        show False using r4 r7 
          using A_def C_def B_def \<open>fppincid A AC \<and> fppincid C AC \<and> AC \<in> Pi_lines\<close> by blast
      qed

      have "H \<noteq> Y" (* if so then AC and AD both contain H, i.e. AH contains both A and C, so ACD collinear *)
      proof (rule ccontr)
        assume "\<not> (H \<noteq> Y)"
        then have "H = Y" by blast
        then have r0:"fppincid H AC \<and> fppincid A AC"
        using \<open>fppincid A AC \<and> fppincid C AC \<and> AC \<in> Pi_lines\<close> hdef by blast
        have r1:"fppincid H AD \<and> fppincid A AD"
        using \<open>\<not> H \<noteq> Y\<close> \<open>fppincid A AD \<and> fppincid D AD \<and> AD \<in> Pi_lines\<close> ydef by auto
        have r2:"H \<noteq> A" using \<open>\<not> fppincid A k \<and> \<not> fppincid B k\<close> hdef by blast 
        have r3: "AC = AD" using  r0 r1 r2 
        using A_def \<open>Base_point ` U \<subseteq> Pi_points\<close> \<open>fppincid A AC \<and> fppincid C AC \<and> AC \<in> Pi_lines\<close>
          \<open>fppincid A AD \<and> fppincid D AD \<and> AD \<in> Pi_lines\<close> ample_free_planes1 hdef uu by fastforce
        then have r4: "fppincid A AC \<and> fppincid C AC \<and> fppincid D AC"
        using \<open>fppincid A AC \<and> fppincid C AC \<and> AC \<in> Pi_lines\<close> \<open>fppincid A AD \<and> fppincid D AD \<and> AD \<in> Pi_lines\<close> by blast 
        have r5: "distinct[Ac, Cc, Dc]" unfolding distinct3_def using V_def uu vv by auto
        have r6: "Ac \<in> U \<and> Cc \<in> U \<or> Dc \<in> U" using uu  using V_def vv by blast
        have r7: "\<not>( \<exists>m\<in>Pi_lines .
           fppincid (Base_point Ac) m \<and>
           fppincid (Base_point Cc) m \<and>
           fppincid (Base_point Dc) m)" using a5 r5 r6  non_collinear_persistence [of Ac Cc Dc] 
        by (metis card_3_iff distinct3_def dual_order.refl empty_iff)
        show False using r4 r7 
        using A_def C_def D_def \<open>fppincid A AC \<and> fppincid C AC \<and> AC \<in> Pi_lines\<close> by blast
      qed

      have dd: "distinct[H, Y, Z]" unfolding distinct3_def using \<open>H \<noteq> Y\<close> \<open>Z \<noteq> H\<close> \<open>Z \<noteq> Y\<close> by auto
      then show ?thesis using hdef ydef zdef dd aw by blast
    qed
  qed
qed


theorem ample_free_plane_is_projective_plane:
  shows "projective_plane Pi_points Pi_lines fppincid"
proof (unfold_locales)
  fix P Q
  show  "\<lbrakk>P \<noteq> Q ;P \<in> Pi_points; Q \<in> Pi_points\<rbrakk> \<Longrightarrow>
           \<exists>!k. k \<in> Pi_lines \<and> fppincid P k \<and> fppincid Q k" using ample_free_planes1 by presburger
next
  fix k n
  show "\<lbrakk>k \<in> Pi_lines; n \<in>  Pi_lines  \<rbrakk> \<Longrightarrow>
       \<exists>P. P \<in> Pi_points \<and> fppincid P  k \<and> fppincid P  n"
    by (simp add: ample_free_planes2)
next
  show "\<exists>P Q R.
       P \<in> Pi_points \<and>
       Q \<in> Pi_points \<and>
       R \<in> Pi_points \<and>
       P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       \<not> projective_plane_data.pcollinear Pi_points Pi_lines fppincid
            P Q R" using ample_free_planes3 by simp
next
  fix k X 
  show  "\<lbrakk>k \<in> Pi_lines ; X = {P \<in> Pi_points . fppincid P  k}\<rbrakk> \<Longrightarrow>
           \<exists>Q R S . Q \<in> X \<and> R \<in> X \<and> S \<in> X \<and>
              distinct[Q, R, S]" unfolding distinct3_def using distinct3_def ample_free_planes4 by metis
qed

end

(*
configuration CPoints CLines incidx for
CPoints CLines incidx +
  fixes
    A B C D U*)

locale confined_configuration = configuration Points Lines incid
  for Points Lines incid + 
  assumes C2: "U \<in> Points  \<Longrightarrow> \<exists> k l m  . k \<in> Lines \<and> l \<in> Lines \<and> m \<in> Lines \<and> 
  incid U k \<and> incid U l \<and> incid U m \<and> distinct[k, l, m]"
  assumes C3: "k \<in> Lines \<Longrightarrow> \<exists> P Q R  . P \<in>Points \<and> Q \<in> Points \<and> R \<in> Points \<and> 
  incid P k \<and> incid Q k \<and> incid R k \<and> distinct[P, Q, R]"
begin
end

lemma desargues_is_cconfig:
  shows "confined_configuration PointsD LinesD incidD"
proof (unfold_locales)
  fix U V k n
  show "U \<in> PointsD \<and> V \<in> PointsD \<and> k \<in> LinesD \<and> n \<in> LinesD \<and> 
    incidD U k \<and> incidD V k \<and> incidD U n \<and> incidD V n \<and> U \<noteq> V \<Longrightarrow> k = n" 
    using desargues_is_config configuration.C1 by metis
next
  fix U
  show "U \<in> PointsD \<Longrightarrow> \<exists>k l m. k \<in> LinesD \<and> l \<in> LinesD \<and> m \<in> LinesD \<and> 
        incidD U k \<and> incidD U l \<and> incidD U m \<and> distinct[k, l, m]" using desargues_is_config
  by (meson desargues_three_lines distinct3_def)
next
  fix k
  show "k \<in> LinesD \<Longrightarrow> \<exists>P Q R. P \<in> PointsD \<and> Q \<in> PointsD \<and> R \<in> PointsD \<and> 
        incidD P k \<and> incidD Q k \<and> incidD R k \<and> distinct[P, Q, R]"  
    using desargues_is_config desargues_three_points[of k] unfolding distinct3_def incidD_def
  by (metis PointsD_def UNIV_I card_3_iff insert_iff)
qed



(* To be proved, perhaps *)
(* 
theorem confined_config_in_base: 
  fixes PointsCC LinesCC 
  assumes "PointsCC \<subseteq> (Pi_points)" and "LinesCC \<subseteq> (Pi_lines)"
  assumes "confined_configuration PointsCC LinesCC fffincid"
  assumes "finite PointsCC" and "finite LinesCC"
  defines "ptop \<equiv> Max {p_level p | p . p \<in> PointsCC}"
  defines "ltop \<equiv> Max {l_level k | k . k \<in> LinesCC}"
  shows "max ptop ltop  = 0"
  sorry
*)

end
