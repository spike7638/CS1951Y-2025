theory "Chapter1-3" imports "Chapter1-2"
begin

text \<open>Hartshorne defines isomorphism, but it's nice to also just have maps sometimes.
But to be a map of projective planes, you must take collinear things to collinear things.\<close>

locale pp_morphism = 
  source: projective_plane "Points1" "Lines1" "incid1" + 
  target: projective_plane "Points2" "Lines2" "incid2" 
  for Points1 and Lines1 and incid1 and Points2 and Lines2 and incid2 + 
  fixes "f" 
  assumes
    m1: "\<lbrakk>P \<in> Points1\<rbrakk> \<Longrightarrow> (f P) \<in> Points2" and
    m2: "\<lbrakk>P \<in> Points1; Q \<in> Points1; R \<in> Points1; source.pcollinear P Q R\<rbrakk> 
      \<Longrightarrow> target.pcollinear (f P) (f Q) (f R)"
begin
end

text \<open>Now we can say that an isomorphism is a morphism that's a bijection. In Chapter 2, we'll 
need to talk about an automorphism, which is a bijection from a projective plane to itself.\<close>
locale pp_isomorphism = pp_morphism Points1 Lines1 incid1 Points2 Lines2 incid2 f
  for Points1 Lines1 incid1 Points2 Lines2 incid2 f +
  assumes
    m3: "bij_betw f Points1 Points2"
begin
end

locale pp_automorphism = pp_isomorphism Points1 Lines1 incid1 Points1 Lines1 incid1 f
  for Points1 Lines1 incid1 Points2 Lines2 incid2 f +
  assumes
    m4: "Points2 = Points1 \<and> Lines2 = Lines1 \<and> incid2 = incid1"
begin
end

text \<open>\hadi\<close>
definition A2C_Points :: "((a2pt, a2ln) projPoint) set" where
  "A2C_Points \<equiv> {OrdinaryP P | P. (P \<in> A2Points)} \<union> {Ideal t | k t. ((k \<in> A2Lines) 
    \<and> (t = affine_plane_data.line_pencil A2Points A2Lines a2incid k))}"

definition A2C_Lines :: "((a2pt, a2ln) projLine) set" where
 "A2C_Lines \<equiv> {OrdinaryL n | n. (n \<in>  A2Lines)} \<union> {Infty}"

definition A2C_incid :: 
  "((a2pt, a2ln) projPoint) \<Rightarrow> ((a2pt, a2ln) projLine) \<Rightarrow> bool" where 
  "A2C_incid \<equiv> mprojectivize a2incid"
text \<open>\done\<close>

text \<open>\hadi\<close>
fun rp2iso :: "rp2 \<Rightarrow> ((a2pt, a2ln) projPoint)" where
  "rp2iso V = (if ((Rep_Proj V)$3 \<noteq> 0) 
    then (OrdinaryP (A2Point 
      ((Rep_Proj V)$1/(Rep_Proj V)$3) 
      ((Rep_Proj V)$2/(Rep_Proj V)$3))) 
    else (if ((Rep_Proj V)$1 \<noteq> 0) 
    then (Ideal (affine_plane_data.line_pencil A2Points A2Lines a2incid 
      (A2Ordinary ((Rep_Proj V)$2/(Rep_Proj V)$1) 0))) 
    else (Ideal (affine_plane_data.line_pencil A2Points A2Lines a2incid 
      (A2Vertical 0)))))"

lemma rp2P_to_A2CP: "\<forall>P. P \<in> rp2_Points \<longrightarrow> rp2iso P \<in> A2C_Points"
  using A2Points_def A2Lines_def unfolding A2C_Points_def by auto
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma rp2iso_inj: "inj_on rp2iso rp2_Points"
proof
  fix P Q
  assume fpisfq: "rp2iso P = rp2iso Q"
  have "P \<in> rp2_Points" and "Q \<in> rp2_Points" using rp2_Points_def by simp+
  then obtain x1 x2 x3 y1 y2 y3::real 
    where xdef: "(Rep_Proj P) = (vector[x1,x2,x3]::v3)"
    and ydef: "(Rep_Proj Q) = (vector[y1,y2,y3]::v3)"
    using exists_rp2_coords by fastforce
  consider (ord) "x3 \<noteq> 0 \<and> y3 \<noteq> 0" | (idl) "x3 = 0 \<and> y3 = 0" using xdef ydef 
    fpisfq rp2iso.simps rp2iso.elims vector_3(3) projPoint.simps(4) by metis
  then show "P = Q"
  proof (cases)
    case ord
    then have "x1/x3 = y1/y3 \<and> x2/x3 = y2/y3" using xdef ydef fpisfq by auto
    then obtain t::real where "t \<noteq> 0 \<and> x1 = t * y1 \<and> x2 = t * y2 \<and> x3 = t * y3" 
      using ord mult.commute divide_eq_0_iff nonzero_mult_div_cancel_left 
      times_divide_eq_right times_divide_eq_left by metis
    then have "projrel (Rep_Proj P) (Rep_Proj Q)" using xdef ydef rep_P_nz cross3_def
      cross_nz [of "Rep_Proj P" "Rep_Proj Q"] unfolding zvec_def by fastforce
    then show ?thesis using Quotient3_rel_rep Quotient3_rp2 by fastforce
  next
    case idl
    show ?thesis 
    proof (cases "x1 = 0")
      case x1z: True
      then have x2nz: "x2 \<noteq> 0" using xdef idl rep_P_nz zvec_def by metis
      have "rp2iso P = (Ideal (affine_plane_data.line_pencil A2Points 
        A2Lines a2incid (A2Vertical 0)))" using xdef x1z idl by simp
      then have y1nz: "y1 = 0" 
        using fpisfq ydef idl ord_not_vert_pencils A2Lines_def by fastforce
      then have "projrel (Rep_Proj Q) (Rep_Proj P)" using idl xdef ydef x1z y1nz x2nz 
        rep_P_nz cross3_def cross_nz [of "Rep_Proj Q" "Rep_Proj P"] by fastforce
      then show ?thesis using Quotient3_rel_rep Quotient3_rp2 by fastforce
    next
      case x1nz: False
      let ?Ix2x1 = "affine_plane_data.line_pencil 
        A2Points A2Lines a2incid (A2Ordinary (x2/x1) 0)"
      have fPIx2x1: "rp2iso P = Ideal ?Ix2x1" using xdef x1nz idl by simp
      then have y1nz: "y1 \<noteq> 0"
        using fpisfq ydef idl ord_not_vert_pencils A2Lines_def by fastforce 
      let ?Iy2y1 = "affine_plane_data.line_pencil 
        A2Points A2Lines a2incid (A2Ordinary (y2/y1) 0)"
      have "?Ix2x1 = ?Iy2y1" using fpisfq fPIx2x1 y1nz ydef idl by simp
      then have "\<forall>l \<in> ?Iy2y1. (\<exists>b::real. l = A2Ordinary (x2/x1) b)"
        using ord_pencil_slopes A2Lines_def by blast
      then have "(x2/x1) = (y2/y1)" unfolding affine_plane_data.line_pencil_def
        affine_plane_data.parallel_def A2Lines_def by simp
      then obtain t::real where "t \<noteq> 0 \<and> x1 = t*y1 \<and> x2 = t*y2" 
        using x1nz y1nz eq_divide_eq divide_eq_0_iff mult.left_commute by metis
      then have "projrel (Rep_Proj P) (Rep_Proj Q)" using idl xdef ydef rep_P_nz 
        cross3_def cross_nz [of "Rep_Proj P" "Rep_Proj Q"] by fastforce
      then show ?thesis using Quotient3_rel_rep Quotient3_rp2 by fastforce
    qed
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma rp2iso_surj:
  fixes Q
  assumes "Q \<in> A2C_Points"
  shows "\<exists>P \<in> rp2_Points. Q = rp2iso P"
proof (cases Q)
  case QO: (OrdinaryP R)
  then obtain x y::real where xydef: "R = (A2Point x y)" 
    using a2pt.exhaust by auto
  let ?R = "vector[x,y,1]::v3" let ?P = "Abs_Proj ?R"
  have Ppt: "?P \<in> rp2_Points" using rp2_Points_def by simp
  have "projrel (Rep_Proj ?P) ?R"  using ra vector_3_eq_iff by auto
  then obtain t::real where "t \<noteq> 0 \<and> (Rep_Proj ?P) = t *\<^sub>R ?R"
    using projrel_def by auto
  then have "rp2iso ?P = Q" using xydef QO by simp
  then show ?thesis using Ppt by blast
next
  case QI: (Ideal T)
  then obtain k::a2ln where kdef: "k \<in> A2Lines 
    \<and> T = affine_plane_data.line_pencil A2Points A2Lines a2incid k" 
    using assms A2C_Points_def by blast
  show ?thesis
  proof (cases k)
    case (A2Ordinary m _)
    then have kpm0: "affine_plane_data.parallel A2Points A2Lines a2incid 
      k (A2Ordinary m 0)" using A2.a2b a2find_parallel.simps(1) UNIV_I
      add_diff_cancel_left' A2Lines_def A2Points_def by metis
    let ?R = "vector[1,m,0]::v3" let ?P = "Abs_Proj ?R"
    have Ppt: "?P \<in> rp2_Points" using rp2_Points_def by simp
    have "projrel (Rep_Proj ?P) ?R" using ra vector_3_eq_iff by auto
    then have "rp2iso ?P = (Ideal (affine_plane_data.line_pencil 
      A2Points A2Lines a2incid (A2Ordinary m 0)))" 
      using projrel_imp_smult by fastforce
    then show ?thesis using QI kdef kpm0 Ppt A2_affine same_pencils
      affine_plane_data.parallel_def by metis
  next
    case (A2Vertical _)
    then have kp0: "affine_plane_data.parallel A2Points A2Lines a2incid 
      k (A2Vertical 0)" using A2.a2b a2find_parallel.simps(2) 
      A2Points_def A2Lines_def UNIV_I by metis
    let ?R = "vector[0,1,0]::v3" let ?P = "Abs_Proj ?R"
    have Ppt: "?P \<in> rp2_Points" using rp2_Points_def by simp
    have "projrel (Rep_Proj ?P) ?R" using ra vector_3_eq_iff by auto
    then have "rp2iso ?P = (Ideal (affine_plane_data.line_pencil 
      A2Points A2Lines a2incid (A2Vertical 0)))" 
      using projrel_imp_smult by fastforce
    then show ?thesis using QI kdef kp0 Ppt A2_affine same_pencils
      affine_plane_data.parallel_def by metis
  qed 
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma not_both_ideal:
  fixes P Q::rp2
  assumes p: "P \<in> rp2_Points" and q: "Q \<in> rp2_Points"
  assumes pq_dist: "P \<noteq> Q"
  fixes l::rp2
  assumes ldef: "l \<in> rp2_Lines \<and> rp2_incid P l \<and> rp2_incid Q l"
  fixes a1 a2 a3::real
  assumes a1a2nz: "a1 \<noteq> 0 \<or> a2 \<noteq> 0"
  assumes l_equation: "\<forall>V \<in> rp2_Points. rp2_incid V l
    \<longleftrightarrow> ((a1 * (Rep_Proj V)$1) + (a2 * (Rep_Proj V)$2) + (a3 * (Rep_Proj V)$3) = 0)"
  defines ideals_def: "ideals \<equiv> {Ideal t | k t. ((k \<in> A2Lines) 
    \<and> (t = affine_plane_data.line_pencil A2Points A2Lines a2incid k))}"
  shows "\<not> ((rp2iso P) \<in> ideals \<and> (rp2iso Q) \<in> ideals)"
proof (rule ccontr)
  assume "\<not> (\<not> ((rp2iso P) \<in> ideals \<and> (rp2iso Q) \<in> ideals))"
  then have cd: "(rp2iso P) \<in> ideals \<and> (rp2iso Q) \<in> ideals" by simp
  have Ipq_dist: "(rp2iso P) \<noteq> (rp2iso Q)" 
    using p q pq_dist rp2iso_inj inj_on_eq_iff by metis
  obtain x1 x2 x3 y1 y2 y3::real 
    where xdef: "(Rep_Proj P) = (vector[x1,x2,x3]::v3)"
    and ydef: "(Rep_Proj Q) = (vector[y1,y2,y3]::v3)"
    using p q exists_rp2_coords by fastforce
  then have Pdl: "a1*x1 + a2*x2 + a3*x3 = 0" and Qdl: "a1*y1 + a2*y2 + a3*y3 = 0"
    using p q xdef ydef ldef l_equation by auto
  have x3y3z: "x3 = 0 \<and> y3 = 0" using assms cd xdef ydef by fastforce
  then consider 
    (ez) "(x1 = 0 \<and> y1 \<noteq> 0) \<or> (x1 \<noteq> 0 \<and> y1 = 0)" | (bnz) "x1 \<noteq> 0 \<and> y1 \<noteq> 0" 
    using xdef ydef Ipq_dist by fastforce
  then show False
  proof (cases)
    case ez
    then show ?thesis using a1a2nz xdef ydef x3y3z Pdl Qdl rep_P_nz zvec_def
      add.right_neutral add_0 mult_eq_0_iff by metis
  next
    case bnz
    have "(x2/x1) = (y2/y1)"
    proof (cases "a1 = 0")
      case True
      then show ?thesis using a1a2nz x3y3z Pdl Qdl by simp
    next
      case a1nz: False
      have "a1*x1 = (-a2)*x2 \<and> a1*y1 = (-a2)*y2" using x3y3z Pdl Qdl by simp
      then show ?thesis 
        using bnz a1nz frac_eq_eq mult.commute mult_eq_0_iff by metis
    qed
    then show ?thesis using bnz xdef ydef x3y3z pq_dist Ipq_dist
      Quotient_rel_rep Quotient_rp2 by fastforce
  qed
qed

lemma a2nz_ord_on_j:
  fixes a1 a2 a3 z1 z2 z3::real
  assumes eqn: "a1*z1 + a2*z2 + a3*z3 = 0"
  assumes zanz: "z3 \<noteq> 0 \<and> a2 \<noteq> 0"
  shows "a2incid (A2Point (z1/z3) (z2/z3)) (A2Ordinary ((-a1)/a2) ((-a3)/a2))"
proof -
  have "(a2*z2) = (-a1*z1) + (-a3*z3)" using eqn by simp
  then have "((a2*z2)/z3) = ((-a1*z1)/z3) + ((-a3*z3)/z3)" 
    using zanz add_divide_distrib by metis
  then have "a2*(z2/z3) = (-a1)*(z1/z3) + (-a3)" using zanz by simp
  then have "((a2*(z2/z3))/a2) = (((-a1)*(z1/z3))/a2) + ((-a3)/a2)" 
    using add_divide_distrib by metis
  then show ?thesis using zanz by simp
qed

lemma one_ideal_coll:
  fixes P Q R::rp2
  assumes p: "P \<in> rp2_Points" and q: "Q \<in> rp2_Points" and r: "R \<in> rp2_Points"
  assumes pqr_dist: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R"
  fixes l::rp2
  assumes ldef: "l \<in> rp2_Lines \<and> rp2_incid P l \<and> rp2_incid Q l \<and> rp2_incid R l"
  fixes a1 a2 a3::real
  assumes a1a2nz: "a1 \<noteq> 0 \<or> a2 \<noteq> 0"
  assumes l_equation: "\<forall>V \<in> rp2_Points. rp2_incid V l
    \<longleftrightarrow> ((a1 * (Rep_Proj V)$1) + (a2 * (Rep_Proj V)$2) + (a3 * (Rep_Proj V)$3) = 0)"
  defines ideals_def: "ideals \<equiv> {Ideal t | k t. ((k \<in> A2Lines) 
    \<and> (t = affine_plane_data.line_pencil A2Points A2Lines a2incid k))}"
  assumes PIQO: "(rp2iso P) \<in> ideals \<and> (rp2iso Q) \<notin> ideals"
  shows "projective_plane_data.pcollinear A2C_Points A2C_Lines A2C_incid
    (rp2iso P) (rp2iso Q) (rp2iso R)"
proof -
  obtain x1 x2 x3 y1 y2 y3 z1 z2 z3::real 
    where xdef: "(Rep_Proj P) = (vector[x1,x2,x3]::v3)"
    and ydef: "(Rep_Proj Q) = (vector[y1,y2,y3]::v3)"
    and zdef: "(Rep_Proj R) = (vector[z1,z2,z3]::v3)"
    using p q r exists_rp2_coords by fastforce
  then have Pdl: "a1 * x1 + a2 * x2 + a3 * x3 = 0" 
    and Qdl: "a1 * y1 + a2 * y2 + a3 * y3 = 0"
    and Rdl: "a1 * z1 + a2 * z2 + a3 * z3 = 0" 
    using p q r ldef l_equation by auto
  have Ipqr_dist: "(rp2iso P) \<noteq> (rp2iso Q) \<and> (rp2iso P) \<noteq> (rp2iso R)
    \<and> (rp2iso Q) \<noteq> (rp2iso R)" using p q r pqr_dist rp2iso_inj inj_on_eq_iff by metis
  then obtain k where kdef: "k \<in> A2C_Lines \<and> A2C_incid (rp2iso P) k \<and> A2C_incid (rp2iso Q) k"
    using xdef ydef RP2C.join_properties1 [of "rp2iso P" "rp2iso Q"] rp2P_to_A2CP 
    A2C_Points_def A2C_Lines_def unfolding rp2_Points_def A2C_incid_def by blast
  then obtain k0 where k0def: "k = OrdinaryL k0" using kdef projLine.exhaust 
    rp2iso.simps mprojectivize.simps(3) mem_Collect_eq UNIV_I PIQO
    A2Lines_def A2C_incid_def ideals_def by (metis (full_types, lifting))
  have x3z: "x3 = 0" using PIQO xdef ideals_def by fastforce
  have y3nz: "y3 \<noteq> 0" using PIQO ydef rp2iso.simps vector_3(3) mem_Collect_eq 
    A2Lines_def UNIV_I unfolding ideals_def by (metis (mono_tags, lifting))
  then obtain TP Q0 where TPQ0_facts: "Q0 \<in> A2Points \<and> rp2iso P = Ideal TP 
    \<and> rp2iso Q = OrdinaryP Q0" using xdef ydef x3z A2Points_def by fastforce
  then have k0TP: "k0 \<in> TP" 
    using kdef k0def mprojectivize.simps(2) A2C_incid_def by metis 
  then have Q0def: "Q0 = A2Point (y1/y3) (y2/y3)" 
    using xdef ydef y3nz TPQ0_facts by simp
  then have Q0k0: "a2incid Q0 k0" using kdef k0def TPQ0_facts 
    mprojectivize.simps(1) A2C_incid_def by metis
  have IRO: "rp2iso R \<notin> ideals" using PIQO p r ldef l_equation pqr_dist 
    a1a2nz not_both_ideal ideals_def by blast
  then obtain R0::a2pt where fRR0: "rp2iso R = OrdinaryP R0" using rp2iso.elims 
    A2Lines_def mem_Collect_eq UNIV_I ideals_def by (metis (mono_tags, lifting))
  then have z3nz: "z3 \<noteq> 0" 
    using zdef rp2iso.simps projPoint.simps(4) vector_3 by metis
  then have R0def: "R0 = A2Point (z1/z3) (z2/z3)" using fRR0 rp2iso.simps
    zdef projPoint.inject(1) vector_3 by metis
  have "A2C_incid (rp2iso R) k"
  proof (cases "x1 = 0")
    case x1z: True
    then have TPdef: "TP = affine_plane_data.line_pencil A2Points A2Lines
      a2incid (A2Vertical 0)" using TPQ0_facts xdef x3z by simp
    then have a2z: "a1 \<noteq> 0 \<and> a2 = 0" using xdef x1z x3z a1a2nz Pdl rep_P_nz
      zvec_def mult_eq_0_iff add_cancel_left_right by metis
    then have "a1*y1 = (-a3)*y3 \<and> a1*z1 = (-a3)*z3" using Qdl Rdl by simp
    then have "(y1/y3) = (z1/z3)" using a2z y3nz z3nz frac_eq_eq mult.commute by metis
    then have "k0 = A2Vertical (z1/z3)" using Q0def Q0k0 k0TP TPdef TPQ0_facts
      A2.a2d A2Lines_def affine_plane_data.line_pencil_def by fastforce
    then show ?thesis using k0def R0def fRR0 A2C_incid_def
      a2incid.simps(2) mprojectivize.simps(1) by metis
  next
    case x1nz: False
    then have a2nz: "a2 \<noteq> 0" and "(-a1) * x1 = a2 * x2" using a1a2nz x3z Pdl by auto
    then have "(x2/x1) = ((-a1)/a2)" using x1nz frac_eq_eq mult.commute by metis
    then have TPdef: "TP = affine_plane_data.line_pencil A2Points A2Lines
      a2incid (A2Ordinary ((-a1)/a2) 0)" using xdef x1nz x3z TPQ0_facts by simp  
    then obtain b where ordk0: "k0 = A2Ordinary ((-a1)/a2) b"
      using k0TP ord_pencil_slopes unfolding A2Lines_def by blast
    then have "b = (y2/y3) + (a1/a2)*(y1/y3)" using Q0def Q0k0 by simp
    then have "b*y3*a2 = -a3*y3" using Qdl a2nz y3nz 
      by (simp add: distrib_left mult.commute)
    then have "b = (-a3)/a2"
      using a2nz y3nz times_divide_eq_left nonzero_mult_div_cancel_right by metis
    then have "a2incid R0 k0" using a2nz z3nz ordk0 R0def Rdl a2nz_ord_on_j by simp
    then show ?thesis using k0def fRR0 mprojectivize.simps(1) A2C_incid_def by metis
  qed
  then show ?thesis using p q r kdef rp2P_to_A2CP 
    unfolding projective_plane_data.pcollinear_def by metis
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma rp2iso_coll_to_coll: 
  fixes P Q R::rp2
  assumes p: "P \<in> rp2_Points" and q: "Q \<in> rp2_Points" and r: "R \<in> rp2_Points" 
  assumes pqr_coll: "RP2Q.pcollinear P Q R" 
  assumes pqr_dist: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R"
  shows "projective_plane_data.pcollinear A2C_Points A2C_Lines A2C_incid
    (rp2iso P) (rp2iso Q) (rp2iso R)"
proof -
  obtain x1 x2 x3 y1 y2 y3 z1 z2 z3::real 
    where xdef: "(Rep_Proj P) = (vector[x1,x2,x3]::v3)"
    and ydef: "(Rep_Proj Q) = (vector[y1,y2,y3]::v3)"
    and zdef: "(Rep_Proj R) = (vector[z1,z2,z3]::v3)"
    using p q r exists_rp2_coords by fastforce
  obtain l where ldef: "l \<in> rp2_Lines \<and> rp2_incid P l \<and> rp2_incid Q l \<and> rp2_incid R l"
    using pqr_coll RP2Q.pcollinear_def rp2_Points_def by auto
  then obtain a1 a2 a3::real where l_equation: "\<forall>V \<in> rp2_Points. rp2_incid V l
    \<longleftrightarrow> ((a1 * (Rep_Proj V)$1) + (a2 * (Rep_Proj V)$2) + (a3 * (Rep_Proj V)$3) = 0)" 
    using rp2_line_equation [of l] by auto
  then have Pdl: "a1 * x1 + a2 * x2 + a3 * x3 = 0" and Qdl: "a1 * y1 + a2 * y2 + a3 * y3 = 0"
    and Rdl: "a1 * z1 + a2 * z2 + a3 * z3 = 0" using p q r xdef ydef zdef ldef by auto
  have Ipqr_dist: "(rp2iso P) \<noteq> (rp2iso Q) \<and> (rp2iso P) \<noteq> (rp2iso R)
    \<and> (rp2iso Q) \<noteq> (rp2iso R)" using p q r pqr_dist rp2iso_inj inj_on_eq_iff by metis
  then obtain k where kdef: "k \<in> A2C_Lines \<and> A2C_incid (rp2iso P) k \<and> A2C_incid (rp2iso Q) k"
    using xdef ydef RP2C.join_properties1 [of "rp2iso P" "rp2iso Q"] rp2P_to_A2CP 
    A2C_Points_def A2C_Lines_def unfolding rp2_Points_def A2C_incid_def by blast
  let ?ideals = "{Ideal t | k t. ((k \<in> A2Lines) 
    \<and> (t = affine_plane_data.line_pencil A2Points A2Lines a2incid k))}"
  let ?j = "(A2Ordinary ((-a1)/a2) ((-a3)/a2))"
show ?thesis
proof (cases "a1 \<noteq> 0 \<or> a2 \<noteq> 0")
  case a1a2nz: True
  then have pq_one_idl: "\<not> ((rp2iso P) \<in> ?ideals \<and> (rp2iso Q) \<in> ?ideals)" 
    using p q pqr_dist ldef l_equation not_both_ideal by blast
  then obtain k0 where k0def: "k = OrdinaryL k0" using kdef projLine.exhaust 
    rp2iso.simps mprojectivize.simps(3) mem_Collect_eq UNIV_I
    A2Lines_def A2C_incid_def by (metis (full_types, lifting))
  consider (PIQO) "rp2iso P \<in> ?ideals \<and> rp2iso Q \<notin> ?ideals" 
    | (POQI) "rp2iso P \<notin> ?ideals \<and> rp2iso Q \<in> ?ideals" 
    | (POQO) "rp2iso P \<notin> ?ideals \<and> rp2iso Q \<notin> ?ideals" using pq_one_idl by blast
  then show ?thesis
  proof (cases)
    case PIQO
    then show ?thesis using a1a2nz ldef l_equation pqr_dist rp2_Points_def
      one_ideal_coll [of P Q] by simp
  next
    case POQI
    then have "projective_plane_data.pcollinear A2C_Points A2C_Lines A2C_incid
      (rp2iso Q) (rp2iso P) (rp2iso R)" using a1a2nz ldef l_equation pqr_dist 
      rp2_Points_def one_ideal_coll [of Q P] by blast
    then show ?thesis using Ipqr_dist A2C_Points_def A2C_Lines_def A2C_incid_def 
      rp2P_to_A2CP projectivisation_of_A2 rp2_Points_def UNIV_I
      RP2C.pcollinear_commute [of "rp2iso Q" "rp2iso P" "rp2iso R"] by metis
  next
    case POQO
    then have x3y3nz: "x3 \<noteq> 0 \<and> y3 \<noteq> 0" using xdef ydef rp2iso.simps vector_3(3)
      A2Lines_def mem_Collect_eq UNIV_I by (metis (mono_tags, lifting))
    then obtain P0 Q0 where P0Q0_facts: "P0 \<in> A2Points \<and> Q0 \<in> A2Points 
      \<and> rp2iso P = OrdinaryP P0 \<and> rp2iso Q = OrdinaryP Q0" 
      using xdef ydef A2Points_def by simp
    then have P0def: "P0 = A2Point (x1/x3) (x2/x3)" 
      and Q0def: "Q0 = A2Point (y1/y3) (y2/y3)" using xdef ydef x3y3nz by simp+
    have k0join: "k0 = a2join P0 Q0" using kdef k0def P0Q0_facts Ipqr_dist A2_a1b
      mprojectivize.simps(1) A2C_incid_def by metis
    have xy1or2: "(x1/x3) \<noteq> (y1/y3) \<or> (x2/x3) \<noteq> (y2/y3)" 
      using P0def Q0def P0Q0_facts Ipqr_dist by auto
    then consider 
      (ordk0) "\<exists>m b. k0 = A2Ordinary m b" | (vertk0) "k0 = A2Vertical (x1/x3)"
      using k0join P0def Q0def a2join.simps by metis
    then have "A2C_incid (rp2iso R) k"
    proof (cases)
      case ordk0
      then have xny1: "(x1/x3) \<noteq> (y1/y3)" using xy1or2 P0def Q0def k0join by auto
      then have a2nz: "a2 \<noteq> 0" using a1a2nz x3y3nz Pdl Qdl add.right_neutral 
        add_eq_0_iff add_num_frac divide_divide_eq_right mult_1 mult_zero_left 
        nonzero_mult_div_cancel_left by metis
      show ?thesis
      proof (cases "rp2iso R")
        case RO: (OrdinaryP R0)
        then have z3nz: "z3 \<noteq> 0"
          using zdef rp2iso.simps vector_3(3) projPoint.distinct(1) by metis
        then have "R0 = A2Point (z1/z3) (z2/z3)" using RO zdef by simp
        then have "a2incid P0 ?j \<and> a2incid Q0 ?j \<and> a2incid R0 ?j" 
          using a2nz P0def Q0def Pdl Qdl Rdl x3y3nz z3nz a2nz_ord_on_j by simp
        then show ?thesis using RO k0def k0join P0Q0_facts Ipqr_dist A2_a1b 
          mprojectivize.simps(1) A2C_incid_def by metis
      next
        case RI: (Ideal T)
        then have z3z: "z3 = 0" 
          using zdef rp2iso.simps projPoint.simps(4) vector_3(3) by metis
        then have z1nz: "z1 \<noteq> 0" using a2nz Rdl add.right_neutral add_0 
          mult_eq_0_iff rep_P_nz zdef zvec_def by metis
        have "(-a1) * z1 = a2 * z2" using Rdl z3z by simp
        then have z2z1a1a2: "(z2/z1) = ((-a1)/a2)" using a1a2nz z1nz mult_eq_0_iff
          mult.commute minus_mult_commute add.inverse_inverse frac_eq_eq by metis
        then have Tdef: "T = (affine_plane_data.line_pencil A2Points A2Lines a2incid 
          (A2Ordinary ((-a1)/a2) 0))" using RI z1nz z3z zdef by simp
        have jT: "?j \<in> T" using Tdef ord_slopes_pencil A2Lines_def by auto
        have "a2incid P0 ?j \<and> a2incid Q0 ?j" 
          using a2nz x3y3nz P0def Q0def Pdl Qdl a2nz_ord_on_j by simp
        then have "k0 = ?j" using k0join A2.a1b P0Q0_facts Ipqr_dist by metis
        then show ?thesis using RI k0def jT unfolding A2C_incid_def by simp
      qed
    next
      case vertk0
      then have xeqy1: "(x1/x3) = (y1/y3)" 
        using k0join P0def Q0def a2join.simps a2ln.distinct(1) by metis
      then have xny2: "(x2/x3) \<noteq> (y2/y3)" using xy1or2 by simp
      then have a1nz: "a1 \<noteq> 0" using a1a2nz x3y3nz Pdl Qdl add.right_neutral 
        add_eq_0_iff add_num_frac divide_divide_eq_right mult_1 mult_zero_left 
        nonzero_mult_div_cancel_left by metis
      have a2z: "a2 = 0"
      proof (rule ccontr) 
        assume "a2 \<noteq> 0"
        then have "a2incid P0 ?j \<and> a2incid Q0 ?j" 
          using P0def Q0def Pdl Qdl x3y3nz a2nz_ord_on_j by simp
        then show False using vertk0 k0join P0Q0_facts Ipqr_dist A2.a1b by auto
      qed
      show ?thesis
      proof (cases "rp2iso R")
        case RO: (OrdinaryP R0)
        then have z3nz: "z3 \<noteq> 0" 
          using zdef rp2iso.simps vector_3(3) projPoint.distinct(1) by metis
        then have R0def: "R0 = A2Point (z1/z3) (z2/z3)" using RO zdef by simp
        have "a1*z1 + a3*z3 = 0 \<and> a1*x1 + a3*x3 = 0" using Pdl Rdl a2z by simp
        then have "(z1/z3) = (x1/x3)" using a1nz z3nz x3y3nz  
          add_num_frac div_0 divide_divide_eq_left' add_eq_0_iff
          nonzero_mult_divide_mult_cancel_left by metis
        then show ?thesis using RO vertk0 k0def R0def P0Q0_facts   
          a2incid.simps(2) mprojectivize.simps(1) A2C_incid_def by metis
      next
        case RI: (Ideal T)
        then have z3z: "z3 = 0" 
          using zdef rp2iso.simps projPoint.simps(4) vector_3(3) by metis
        then have z1z: "z1 = 0" using Rdl a1nz a2z by simp
        then have TVert: "T = affine_plane_data.line_pencil A2Points 
          A2Lines a2incid (A2Vertical 0)" using RI zdef z3z by simp
        then have "k0 \<in> T" using vertk0 TVert A2.a2b a2find_parallel.simps(2)
          affine_plane_data.line_pencil_def A2Lines_def A2Points_def 
          UNIV_I mem_Collect_eq by metis
        then show ?thesis using RI k0def unfolding A2C_incid_def by simp
      qed
    qed
    then show ?thesis using p q r kdef rp2P_to_A2CP 
      unfolding projective_plane_data.pcollinear_def by metis
    qed
  next
    case False
    then have a1a2z: "a1 = 0 \<and> a2 = 0" by simp
    then have liff: "\<forall>V \<in> rp2_Points. rp2_incid V l \<longleftrightarrow> ((Rep_Proj V)$3) = 0" 
      using ldef l_equation rp2_P3 mult_eq_0_iff add_0 by metis
    then have "\<exists>TP TQ. (rp2iso P) = Ideal TP \<and> (rp2iso Q) = Ideal TQ"
      using xdef ydef ldef rp2_Points_def by auto
    then have "k = Infty" using p q Ipqr_dist kdef A2_affine rp2P_to_A2CP 
      two_ideal_is_infinite [of "rp2iso P" _ "rp2iso Q" _ A2Points A2Lines 
      a2incid _ _ _ k] A2C_Points_def A2C_Lines_def A2C_incid_def by metis
    then have "A2C_incid (rp2iso R) k" using ldef liff rp2_Points_def 
      unfolding A2C_incid_def by simp
    then show ?thesis using p q r kdef rp2P_to_A2CP 
      unfolding projective_plane_data.pcollinear_def by metis
  qed
qed
text \<open>\done\<close>

text \<open>\hadi\<close>
lemma real_projective_planes_isomorphic:
  shows "pp_isomorphism rp2_Points rp2_Lines rp2_incid 
    A2C_Points A2C_Lines A2C_incid rp2iso"
proof (unfold_locales)
  show "\<lbrakk>P \<noteq> Q; P \<in> A2C_Points; Q \<in> A2C_Points\<rbrakk>
    \<Longrightarrow> \<exists>!k. k \<in> A2C_Lines \<and> A2C_incid P k \<and> A2C_incid Q k" for P Q
    using A2C_Lines_def A2C_Points_def A2C_incid_def RP2C.p1 by simp
  show "\<lbrakk>k \<in> A2C_Lines; n \<in> A2C_Lines\<rbrakk> 
    \<Longrightarrow>  \<exists>P. P \<in> A2C_Points \<and> A2C_incid P k \<and> A2C_incid P n" for k n
    using A2C_Lines_def A2C_Points_def A2C_incid_def RP2C.p2 by simp
  show "\<exists>P Q R. P \<in> A2C_Points \<and> Q \<in> A2C_Points \<and> R \<in> A2C_Points 
    \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R 
    \<and> \<not> (projective_plane_data.pcollinear A2C_Points A2C_Lines A2C_incid P Q R)"
    using A2C_Lines_def A2C_Points_def A2C_incid_def RP2C.p3 by simp
  show "\<lbrakk>k \<in> A2C_Lines; U = {P. (P \<in> A2C_Points \<and> A2C_incid P k)}\<rbrakk> 
    \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct[Q, R, S]" for k U 
    using A2C_Lines_def A2C_Points_def A2C_incid_def RP2C.p4 by simp
  show "P \<in> rp2_Points \<Longrightarrow> rp2iso P \<in> A2C_Points" for P using rp2P_to_A2CP by simp
  show "\<lbrakk>P \<in> rp2_Points; Q \<in> rp2_Points; R \<in> rp2_Points; RP2Q.pcollinear P Q R\<rbrakk> 
    \<Longrightarrow> projective_plane_data.pcollinear A2C_Points A2C_Lines A2C_incid
      (rp2iso P) (rp2iso Q) (rp2iso R)" for P Q R
  proof -
    fix P Q R
    assume p: "P \<in> rp2_Points" and q: "Q \<in> rp2_Points" and r: "R \<in> rp2_Points" 
    assume pqr_coll: "RP2Q.pcollinear P Q R"
    show "projective_plane_data.pcollinear A2C_Points A2C_Lines A2C_incid
      (rp2iso P) (rp2iso Q) (rp2iso R)"
    proof (cases "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R")
      case True
      then show ?thesis using p q r pqr_coll rp2iso_coll_to_coll by simp
    next
      case False 
      then show ?thesis using p q r rp2P_to_A2CP projective_plane.pcollinear_degeneracy 
        A2C_Points_def A2C_Lines_def A2C_incid_def projectivisation_of_A2 by metis
    qed
  qed
  show "bij_betw rp2iso rp2_Points A2C_Points" using rp2iso_inj rp2iso_surj 
    rp2P_to_A2CP unfolding bij_betw_def by blast
qed
text \<open>\done\<close>

end