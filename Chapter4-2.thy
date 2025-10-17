theory "Chapter4-2"
  imports Complex_Main  "Chapter4-1"

begin
text\<open> start at definition of complete quadrangle; stop just before "Harmonic points"\<close>

definition (in projective_plane) cquadrangle :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  where "cquadrangle A B C D = (A \<in> Points \<and> B \<in> Points \<and> C \<in> Points \<and> D \<in> Points \<and> 
  \<not>pcollinear A B C \<and> \<not>pcollinear A B D \<and> \<not>pcollinear A C D \<and> \<not>pcollinear B C D)"

term affine_plane


(* Temporarily deleted: 
fun (in projective_plane) cquadrangle_sides :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'l set"
  where "cquadrangle_sides A B C D = (if (cquadrangle A B C D) 
  then({join A B})
  else undefined)"


fun (in projective_plane) cquadrangle_sides :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'l set"
  where "cquadrangle_sides A B C D = (if (cquadrangle A B C D) 
  then({join A B,
        THE l. l\<in> Lines \<and> A \<lhd> l \<and> C \<lhd> l, 
        THE l. l\<in> Lines \<and> B \<lhd> l \<and> C \<lhd> l,
        THE l. l\<in> Lines \<and> A \<lhd> l \<and> D \<lhd> l,
        THE l. l\<in> Lines \<and> B \<lhd> l \<and> D \<lhd> l,
        THE l. l\<in> Lines \<and> C \<lhd> l \<and> D \<lhd> l})
  else undefined)"

fun (in projective_plane) cquadrangle_points :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p set"
  where "cquadrangle_points A B C D = (if (cquadrangle A B C D)
  then {THE P. P \<in> Points \<and> P \<lhd> (THE l. l\<in> Lines \<and> A \<lhd> l \<and> B \<lhd> l)}
  else undefined)" termination by (relation "{}") simp

*)


end


