theory "Chapter4-2"
  imports Complex_Main  "Chapter4-1"

begin
text\<open> start at definition of complete quadrangle; stop just before "Harmonic points"\<close>

definition cquadrangle :: "('p set) \<Rightarrow> (('p set) \<Rightarrow> ('l set))"
  where "'p"

text\<open>
Our idea for defining the configuration cquadrangle:
- p_4p: a definition of points a x b x c x d
- cquadrangle: a definition of a set of p_4p's, where the a, b, c, d in every p_4p are noncolinear
- cquadrangle_fun: a function that takes in one p_4p's in cquadrangles => (point set, line set) 
\<close>

 datatype cquadrangle = A | B | C | D 
 definition "cquadranglePoints = {A, B, C, D}"
 definition "cqAB = {A, B}"
 definition "cqBC = {B, C}"
 definition "cqCD = {C, D}"
 definition "cqDA = {D, A}"
 definition "A4Lines = {A4PQ, A4PR, A4PS, A4QR, A4QS, A4RS}"


end


