theory "Chapter1-3"
imports "Chapter1-2"
begin

text\<open> Hartshorne defines isomorphism, but it's nice to also just have maps sometimes. But to be a map
of projective planes, you must take collinear things to collinear things. \<close>

locale  pp_morphism = 
  source: projective_plane "Points1" "Lines1" "incid1" + 
  target: projective_plane "Points2" "Lines2" "incid2" 
  for Points1 and Lines1 and incid1 and Points2 and Lines2 and incid2 + 
  fixes "f" 
  assumes
    m1: "\<lbrakk>P \<in> Points1\<rbrakk> \<Longrightarrow> (f P) \<in> Points2" and
    m2: "\<lbrakk>P \<in> Points1; Q \<in> Points1; R \<in> Points1; source.pcollinear P Q R\<rbrakk> \<Longrightarrow> target.pcollinear  (f P) (f Q) (f R)"
begin
end

text\<open> Now we can say that an isomorphism is a morphism that's a bijection. In Chapter 2, we'll 
need to talk about an automorphism, which is a bijection from a projective plane to itself. \<close>
locale  pp_isomorphism = pp_morphism  Points1 Lines1 incid1 Points2 Lines2 incid2 f
  for Points1 Lines1 incid1 Points2 Lines2 incid2 f +
  assumes
    m3: "bij_betw f Points1 Points2"
begin
end

locale  pp_automorphism = pp_isomorphism  Points1 Lines1 incid1 Points1 Lines1 incid1 f
  for Points1 Lines1 incid1 Points2 Lines2 incid2 f +
  assumes
    m4: "Points2 = Points1 \<and> Lines2 = Lines1 \<and> incid2=incid1"
begin
end

definition rp2iso:: "rp2 \<Rightarrow> ((a2pt, a2ln) projPoint)" where
"rp2iso P = (let s  = (Rep_Proj P) in (if (s$3 = 0) then 
 (if (s$1 = 0) then 
 (Ideal (affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0))) else 
 Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (s$2/s$1) 0))) else
 (OrdinaryP (A2Point (s$1/s$3) (s$2/s$3)))))"

lemma rp2iso_preserves_collinearity:
  fixes P Q R::rp2
  assumes "RP2Q.pcollinear P Q R"
  shows "projective_plane_data.pcollinear ({OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k})
        ({OrdinaryL n |n. n \<in> A2Lines} \<union> {Infty}) (mprojectivize a2incid) (rp2iso P) (rp2iso Q) (rp2iso R)"
proof -
  define P' where "P' = rp2iso P"
  define Q' where "Q' = rp2iso Q"
  define R' where "R' = rp2iso R"
  define incidC where "incidC = (mprojectivize a2incid)"

  from assms obtain k where kfact: " (rp2_incid k P) \<and> (rp2_incid k Q) \<and> (rp2_incid k R)" using RP2Q.pcollinear_def 
    using incid_commute rp2_Points_def by auto
  define p3 where "p3 \<equiv> Rep_Proj P"
  define q3 where "q3 \<equiv> Rep_Proj Q"
  define r3 where "r3 \<equiv> Rep_Proj R"
  define k3 where "k3 \<equiv> Rep_Proj k"
  from kfact have dots: " k3 \<bullet> p3 = 0 \<and> k3 \<bullet> q3 = 0 \<and> k3 \<bullet> r3 = 0" 
    by (simp add: k3_def p3_def q3_def r3_def rp2_incid.rep_eq)
  from k3_def have knz: "k3 \<noteq> zvec" by (metis Quotient_rel_rep Quotient_rp2 projrel_def)
  obtain a1 a2 a3 where kfact: "k3 = vector[a1, a2, a3]"  using forall_vector_3 by fastforce
  from knz have knz2: "a1 \<noteq> 0 \<or> a2 \<noteq> 0 \<or> a3 \<noteq> 0" by (metis kfact zvec_def)
  consider (Inf) "a1 = 0 \<and> a2 = 0 \<and> a3 \<noteq> 0"  | (Vert) "a1 \<noteq> 0 \<and> a2 = 0" | (Sloped) "a2 \<noteq> 0" using knz2 by blast
  then show ?thesis
  proof (cases)
    case Inf
    define n where "n::(a2pt, a2ln) projLine \<equiv> Infty"
    have u0: "vector[0,0,a3] \<bullet> p3 = 0 \<and> vector[0,0,a3] \<bullet> q3 = 0 \<and> vector[0,0,a3] \<bullet> r3 = 0" using dots kfact Inf by blast
    then have u1: "incidC P' n = incidC P' Infty \<and> incidC Q' n = incidC Q' Infty \<and> incidC R' n = incidC R' Infty" 
      using n_def by auto 
    have u2: "(incidC P' Infty \<longleftrightarrow> (\<exists>l . P' = Ideal l)) \<and>
              (incidC Q' Infty \<longleftrightarrow> (\<exists>l . Q' = Ideal l))\<and>
              (incidC R' Infty \<longleftrightarrow> (\<exists>l . R' = Ideal l))"  using incidC_def mprojectivize.elims(2) by fastforce
    from u0 Inf have u3: "(p3$3 = 0)\<and> (q3$3 = 0) \<and> (r3$3 = 0)" by (simp add: inner_vec_def sum_3)
    then have u5: "(\<exists>l . rp2iso (Abs_Proj p3) = Ideal l) \<and>
                   (\<exists>l . rp2iso (Abs_Proj q3) = Ideal l) \<and>
                   (\<exists>l . rp2iso (Abs_Proj r3) = Ideal l)" 
      using ar p3_def q3_def r3_def rp2iso_def  by (smt (verit, del_insts))
    then have h: "(incidC P' n) \<and> (incidC Q' n) \<and> (incidC R' n)" 
      using u0 u1 u2 u3 u5 P'_def Q'_def R'_def ar p3_def q3_def r3_def by auto 
    have "?thesis =
          projective_plane_data.pcollinear ({OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k})
        ({OrdinaryL n |n. n \<in> A2Lines} \<union> {Infty}) incidC P' Q' R'" using P'_def Q'_def R'_def incidC_def by force

    then show ?thesis using h P'_def Q'_def R'_def 
    by (smt (verit, del_insts) A2Lines_def A2Points_def RP2C.pcollinear_def UNIV_I Un_iff completed_lines_def completed_points_def incidC_def
        insert_iff mem_Collect_eq n_def rp2iso_def)
  next
    case Vert
    then show ?thesis sorry
  next
    case Sloped
    then show ?thesis sorry
  qed
qed
(*
fun mprojectivize :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (('a, 'b) projPoint \<Rightarrow> ('a, 'b) projLine \<Rightarrow> bool)" where
  "mprojectivize (incid) (OrdinaryP P) (OrdinaryL k) = incid P k"
| "mprojectivize (incid) (Ideal s) (OrdinaryL m) = (m \<in> s)"
| "mprojectivize (incid) (OrdinaryP P) Infty = False"
| "mprojectivize (incid) (Ideal s) Infty = True"
*)

lemma rp2iso_is_bijection:
  shows "bij_betw rp2iso rp2_Points ({OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k})"
  unfolding bij_betw_def
proof 
  show "inj_on rp2iso rp2_Points"
    unfolding inj_on_def 
  proof (clarify)
    fix x y::rp2
    assume "x \<in> rp2_Points"
    assume "y \<in> rp2_Points"
    assume equal_image: "rp2iso x = rp2iso y"
    show "x = y"
    proof -
      define rx where rxf: "rx = Rep_Proj x"
      define ry where ryf: "ry = Rep_Proj y"
      have rp2iso_v2: "s = Rep_Proj u \<Longrightarrow> rp2iso u = (if (s$3 = 0) then 
 (if (s$1 = 0) then 
 (Ideal (affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0))) else 
 Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (s$2/s$1) 0))) else
 (OrdinaryP (A2Point (s$1/s$3) (s$2/s$3)))) " for u s using rp2iso_def rxf by (smt (verit))

      have y1: "rp2iso y =  (if (ry$3 = 0) then 
 (if (ry$1 = 0) then 
 (Ideal (affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0))) else 
 Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (ry$2/ry$1) 0))) else
 (OrdinaryP (A2Point (ry$1/ry$3) (ry$2/ry$3))))" using rp2iso_v2 [of ry y] ryf by auto
      have x1: "rp2iso x =  (if (rx$3 = 0) then 
 (if (rx$1 = 0) then 
 (Ideal (affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0))) else 
 Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (rx$2/rx$1) 0))) else
 (OrdinaryP (A2Point (rx$1/rx$3) (rx$2/rx$3))))" using rp2iso_v2 [of rx x] rxf by auto

      consider (PQord) "rx$3 \<noteq> 0 \<and> ry$3 \<noteq> 0" | (Pord) "rx$3 \<noteq> 0 \<and> ry$3 = 0"
        | (Qord) "rx$3 = 0\<and> ry$3 \<noteq> 0" | 
          (bothInf00) "rx$3 = 0 \<and> rx$1 \<noteq> 0 \<and> ry$3 = 0 \<and> ry$1 \<noteq> 0" |
          (bothInfI0) "rx$3 = 0 \<and> rx$1 = 0 \<and> ry$3 = 0 \<and> ry$1 \<noteq> 0" |
          (bothInf0I) "rx$3 = 0 \<and> rx$1 \<noteq> 0 \<and> ry$3 = 0 \<and> ry$1 = 0" |
          (bothInfII) "rx$3 = 0 \<and> rx$1 = 0 \<and> ry$3 = 0 \<and> ry$1 = 0" by auto
  then show ?thesis
  proof (cases)
    case PQord
    have fx:"rp2iso x = OrdinaryP (A2Point (rx$1/rx$3) (rx$2/rx$3))" using x1 PQord by auto
    have fy:"rp2iso y = OrdinaryP (A2Point (ry$1/ry$3) (ry$2/ry$3))" using y1 PQord by auto
    have "OrdinaryP (A2Point (rx$1/rx$3) (rx$2/rx$3))=OrdinaryP (A2Point (ry$1/ry$3) (ry$2/ry$3))" using fx fy equal_image by auto
    then have "rx$1/rx$3 = ry$1/ry$3 \<and> rx$2/rx$3 =  ry$2/ry$3" by auto
    then have s: "rx$1 = (rx$3/ry$3)*ry$1 \<and> rx$2 = (rx$3/ry$3)*ry$2 \<and> rx$3 = (rx$3/ry$3)*ry$3" using PQord  by (simp add: nonzero_divide_eq_eq) 
    define t where tf: "t \<equiv> (rx$3/ry$3)"
    have "rx = t *\<^sub>R ry" using s tf by (smt (verit, best) exhaust_3 real_scaleR_def vec_eq_iff vector_scaleR_component)
    then have "projrel rx ry" using projrel_def using PQord zvec_alt by force
    then show ?thesis using rxf ryf  by (metis Quotient3_rel Quotient3_rp2 ar)
  next
    case Pord
    have fx:"rp2iso x = OrdinaryP (A2Point (rx$1/rx$3) (rx$2/rx$3))" using x1 Pord by auto
    have fy:"rp2iso y = (if (ry$1 = 0) then  
                (Ideal (affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0))) else 
                 Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (ry$2/ry$1) 0)))" using y1 Pord by auto 
    have False using fx fy equal_image rxf ryf by (metis projPoint.distinct(1))
    then show ?thesis by blast
  next
    case Qord
    have fy:"rp2iso y = OrdinaryP (A2Point (ry$1/ry$3) (ry$2/ry$3))" using y1 Qord by auto
    have fx:"rp2iso x = (if (rx$1 = 0) then  
                (Ideal (affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0))) else 
                 Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (rx$2/rx$1) 0)))" using x1 Qord by auto 
    have False using fx fy equal_image rxf rxf by (metis projPoint.distinct(1))
    then show ?thesis by blast
  next
    case bothInf00
    have fx:"rp2iso x = Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (rx$2/rx$1) 0))" using x1 bothInf00 by auto
    have fy:"rp2iso y = Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (ry$2/ry$1) 0))" using y1 bothInf00 by auto
    have p1:"affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (rx$2/rx$1) 0) =
             affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (ry$2/ry$1) 0)" using fx fy by (simp add: equal_image)
    then have "affine_plane_data.parallel A2Points A2Lines a2incid (A2Ordinary (rx$2/rx$1) 0) (A2Ordinary (ry$2/ry$1) 0)" using affine_plane_data.line_pencil_def
      by (metis A2.parallel_def A2Lines_def UNIV_I mem_Collect_eq)
    then have "(rx$2/rx$1) =  (ry$2/ry$1) " using affine_plane_data.parallel_def
      by (metis (no_types, lifting) A2Points_def UNIV_I a2incid.simps(1) a2ln.inject(1) mult_cancel_right2)
    then have "rx$2 =  (rx$1/ry$1) * ry$2 \<and> rx$1 =  (rx$1/ry$1) * ry$1 \<and> rx$3 =  (rx$1/ry$1) * ry$3" 
      using bothInf00  by (simp add: nonzero_divide_eq_eq)
    then have "rx = (rx$1/ry$1) *\<^sub>R ry" using vector_3 vector_3_eq_iff scaleR_class_def 
      by (smt (verit) exhaust_3 real_scaleR_def vec_eq_iff vector_scaleR_component)
    then have "projrel rx ry" using projrel_def[of rx ry] 
      by (metis bothInf00 divide_eq_0_iff zero_index zvec_alt)
    then show ?thesis by (metis Quotient3_rel Quotient3_rp2 ar rxf ryf)
  next
    case bothInfI0
    have fx:"rp2iso x = Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0))" using x1 bothInfI0 by auto
    have fy:"rp2iso y = Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (ry$2/ry$1) 0))" using y1 bothInfI0 by auto
    have p1: "affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0) = 
              affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (ry$2/ry$1) 0)" using fx fy equal_image by auto
    then have "A2.parallel (A2Vertical 0) (A2Ordinary (ry$2/ry$1) 0)" 
      using A2.line_pencil_def A2.parallel_reflexive A2Lines_def by auto
    then have "False" by (metis A2.parallel_def A2Points_def UNIV_I a2incid.simps(1,2) a2ln.simps(4))
    then show ?thesis by auto
  next
    case bothInf0I
    have fx:"rp2iso x = Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (rx$2/rx$1) 0))" using x1 bothInf0I by auto
    have fy:"rp2iso y = Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0))" using y1 bothInf0I by auto
    have p1: "affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0) = 
              affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Ordinary (rx$2/rx$1) 0)" using fx fy equal_image by auto
    then have "A2.parallel (A2Vertical 0) (A2Ordinary (rx$2/rx$1) 0)" 
      using A2.line_pencil_def A2.parallel_reflexive A2Lines_def by auto
    then have "False" by (metis A2.parallel_def A2Points_def UNIV_I a2incid.simps(1,2) a2ln.simps(4))
    then show ?thesis by auto
  next
    case bothInfII
    have fx:"rp2iso x = Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0))" using x1 bothInfII by auto
    have fy:"rp2iso y = Ideal(affine_plane_data.line_pencil A2Points A2Lines a2incid (A2Vertical 0))" using y1 bothInfII by auto
    have "rx$2 \<noteq> 0 \<and> ry$2 \<noteq> 0" using bothInfII 
      by (metis \<open>x \<in> rp2_Points\<close> \<open>y \<in> rp2_Points\<close> exhaust_3 rep_P_nz rxf ryf vec_eq_iff zero_index zvec_alt)
    then have "rx$2 =  (rx$2/ry$2) * ry$2 \<and> rx$1 =  (rx$2/ry$2) * ry$1 \<and> rx$3 =  (rx$2/ry$2) * ry$3" 
      using bothInfII by simp
    then have "rx = (rx$2/ry$2) *\<^sub>R ry" using vector_3 vector_3_eq_iff scaleR_class_def 
      by (smt (verit) exhaust_3 real_scaleR_def vec_eq_iff vector_scaleR_component)
    then have "projrel rx ry" using projrel_def[of rx ry] 
      by (metis \<open>x \<in> rp2_Points\<close> rep_P_nz rxf scaleR_eq_0_iff zvec_alt)
    then show ?thesis by (metis Quotient3_rel Quotient3_rp2 ar rxf ryf)
   qed
qed
qed
  show "rp2iso ` rp2_Points = {OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k} " sorry
qed

      
text\<open>\spike\<close>
lemma real_projective_planes_isomorphic:
  shows "pp_isomorphism rp2_Points rp2_Lines rp2_incid completed_points completed_lines (mprojectivize (a2incid))    rp2iso"
  unfolding completed_points_def completed_lines_def
proof 
  show "\<And>P Q. P \<noteq> Q \<Longrightarrow>
           P \<in> {OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k} \<Longrightarrow>
           Q \<in> {OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k} \<Longrightarrow>
           \<exists>!k. k \<in> {OrdinaryL n |n. n \<in> A2Lines} \<union> {Infty} \<and> mprojectivize a2incid P k \<and> mprojectivize a2incid Q k"
    using RP2C.p1 by (simp add: completed_lines_def completed_points_def)
  show "\<And>k n. k \<in> {OrdinaryL n |n. n \<in> A2Lines} \<union> {Infty} \<Longrightarrow> 
       n \<in> {OrdinaryL n |n. n \<in> A2Lines} \<union> {Infty} \<Longrightarrow>
       \<exists>P. P \<in> {OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k} \<and>
       mprojectivize a2incid P k \<and> mprojectivize a2incid P n" 
    using RP2C.p2  by (simp add: completed_lines_def completed_points_def)
  show "\<exists>P Q R.
       P \<in> {OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k} \<and>
       Q \<in> {OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k} \<and>
       R \<in> {OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k} \<and>
       P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       \<not> projective_plane_data.pcollinear ({OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k})
           ({OrdinaryL n |n. n \<in> A2Lines} \<union> {Infty}) (mprojectivize a2incid) P Q R" 
    using RP2C.p3  by (simp add: completed_lines_def completed_points_def)
  show "\<And>k U. k \<in> {OrdinaryL n |n. n \<in> A2Lines} \<union> {Infty} \<Longrightarrow>
           U = {P \<in> {OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k}. mprojectivize a2incid P k} \<Longrightarrow>
           \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]" 
    using RP2C.p4 by (simp add: completed_lines_def completed_points_def)

  fix P::rp2
  show "P \<in> rp2_Points \<Longrightarrow> rp2iso P \<in> {OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k}" 
    using rp2iso_def by (smt (verit) A2Lines_def A2Points_def UNIV_I UnCI mem_Collect_eq)
  show "\<And>P Q R.
       P \<in> rp2_Points \<Longrightarrow>
       Q \<in> rp2_Points \<Longrightarrow>
       R \<in> rp2_Points \<Longrightarrow>
       RP2Q.pcollinear P Q R \<Longrightarrow>
       projective_plane_data.pcollinear ({OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k})
        ({OrdinaryL n |n. n \<in> A2Lines} \<union> {Infty}) (mprojectivize a2incid) (rp2iso P) (rp2iso Q) (rp2iso R)" using rp2iso_preserves_collinearity by auto
  show "bij_betw rp2iso rp2_Points ({OrdinaryP P |P. P \<in> A2Points} \<union> {uu. \<exists>k t. uu = Ideal t \<and> k \<in> A2Lines \<and> t = A2.line_pencil k})" 
      using rp2iso_is_bijection by auto
qed  
text\<open>\done\<close>
end