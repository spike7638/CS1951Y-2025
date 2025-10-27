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
  for Points1 Lines1 incid1 Points2 Lines2 incid2 f
begin
end


(* PLACEHOLDER -- need to fill in Hartshorne's definition here *)
fun  rp2iso:: "((a2pt, a2ln) projPoint) \<Rightarrow> rp2" where
"rp2iso (Ideal t) = Abs_Proj(vector [0,0,1]::v3)" |  
"rp2iso (OrdinaryP P) = Abs_Proj(vector [0,0,1]::v3) " 

(* PLACEHOLDER -- and, of course, there's a proof to fill in here. 
You'll want to start with "unfolding completed_points_def completed_lines_def". *)

lemma real_projective_planes_isomorphic:
  shows "pp_isomorphism completed_points completed_lines (mprojectivize (a2incid)) rp2_Points rp2_Lines rp2_incid rp2iso"
  sorry

end