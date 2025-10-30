theory locale_example
  imports Main
begin
locale projective_plane_data =
  fixes Points :: "'p set" and Lines :: "'l set" and incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool" (infix "\<lhd>" 60)
begin

definition (in projective_plane_data) pcollinear :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  where "pcollinear A B C = (if (A \<in> Points \<and> B \<in> Points \<and> C \<in> Points)  
  then (\<exists> l. l \<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l \<and> C \<lhd> l) else undefined)"
end

locale projective_plane = projective_plane_data Points Lines incid
  for
    Points :: "'p set" and
    Lines :: "'l set" and
    incid :: "'p \<Rightarrow> 'l \<Rightarrow> bool"  (infix "\<lhd>" 60)  + 
  assumes
    p1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> (\<exists>!k. k \<in> Lines \<and> P \<lhd> k \<and> Q \<lhd> k)" and
    p2: "\<lbrakk>k \<in> Lines; n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists>P. (P \<in> Points \<and> P \<lhd> k \<and> P \<lhd> n)" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (pcollinear P Q R)" and
    p4: "\<lbrakk>k \<in> Lines; U = {P. (P \<in> Points \<and> P \<lhd> k)} \<rbrakk> \<Longrightarrow> \<exists>Q R S. Q \<in> U \<and> R \<in> U \<and> S \<in> U \<and> distinct [Q, R, S]"
begin
end

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

locale  pp_automorphism = pp_isomorphism  Points1 Lines1 incid1  Points1 Lines1 incid1 
  for Points1 Lines1 incid1
begin
end



end
