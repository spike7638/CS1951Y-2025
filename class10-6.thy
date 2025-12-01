theory "class10-6"
imports Complex_Main
begin
declare [[show_types = true]]
text \<open>Creation of new types\<close>
type_synonym qq = nat \<comment> \<open>the most basic case -- purely syntactic renaming\<close>
lemma type_syn_example:
  shows "(2::qq) + 2 = (4::qq)"
  by auto

text\<open>A much more general tool, whose use for us is only a tiny portion of the 
full generality\<close>
datatype ssss = One int | Two "int * int"
datatype line_example = Vertical real | Sloped real real
find_theorems name: "ssss"

text\<open>Restriction types: consist of all items of some type that satisfy some predicate.\<close>
typedef pReal = "{x::real . x \<noteq> 0}" \<comment> \<open>Note that there's a proof obligation here!\<close>
proof -
  have "(1::real) \<noteq> (0::real)" using zero_neq_one by metis
  then show ?thesis by blast
qed

find_theorems name: "*_pReal"

text\<open>Let's try to build a new type that behaves like a mathematical set (has empty, element-of, 
union, etc.). 
\<close>

typedef 'a SET = "{ f :: 'a \<Rightarrow> bool. True}"  by auto

term "Rep_SET"
term "Abs_SET"

definition EMPTY :: "'a SET" where
"EMPTY = Abs_SET (\<lambda> _. False)"

definition ELEM :: "'a \<Rightarrow> 'a SET \<Rightarrow> bool" where
"ELEM x A = Rep_SET A x"

term "ELEM EMPTY EMPTY"
lemma
  shows "ELEM EMPTY EMPTY = False" 
proof -
  show ?thesis
    apply (simp add: ELEM_def)
    apply (simp add: EMPTY_def)
    apply (simp add: Abs_SET_inverse)
    done
qed
(*  by (simp add: Abs_SET_inverse ELEM_def EMPTY_def) *)

definition UNION :: "'a SET \<Rightarrow> 'a SET \<Rightarrow> 'a SET" where
"UNION A B = Abs_SET (\<lambda> x. Rep_SET A x \<or> Rep_SET B x)"


typedef 'a ty0 = "{ f :: 'a \<Rightarrow> bool . True}" sorry
typedef 'a ty1 = "{ f :: 'a \<Rightarrow> nat . True}" sorry
typedef 'a ty2 = "{ f :: 'a \<Rightarrow> nat . finite {x. f x > 0}}" sorry
typedef 'a ty3 = "{ f :: nat \<Rightarrow> 'a . True}" sorry
typedef 'a ty4 = "{ (n, f :: nat \<Rightarrow> 'a) . (\<forall> i. i < n \<or> f i = undefined) }" sorry

(*====Integers as (bool,nat) pairs; (True, 0) represents 0 ==========*)
typedef INTEGER = "{ bn. case bn of (b,n :: nat) \<Rightarrow> n = 0 \<longrightarrow> b}" by auto

find_theorems name: "*_INTEGER"

definition ZERO :: INTEGER where
  "ZERO = Abs_INTEGER (True, 0)"

fun add_integer :: "bool \<times> nat \<Rightarrow> bool \<times> nat \<Rightarrow> bool \<times> nat" where
  "add_integer (True,n) (True,m) = (True, n+m)"
| "add_integer (False,n) (False,m) = (False, n+m)"
| "add_integer (True,n) (False,m) = (if m \<le> n then (True, n - m) else (False, m - n))"
| "add_integer (False,n) (True,m) = (if n \<le> m then (True, m - n) else (False, n - m))"

definition ADD :: "INTEGER \<Rightarrow> INTEGER \<Rightarrow> INTEGER" where
  "ADD x y = Abs_INTEGER (add_integer (Rep_INTEGER x) (Rep_INTEGER y))"
find_theorems name: "Rep_INTEGER_inv"
find_theorems name: "Abs_INTEGER_inv"

(* Lemma for showing that ADD x ZERO = x *)
lemma h:
  fixes b n
  assumes "n \<noteq> 0 \<or> b = True"
  shows "add_integer (b, n) (True, 0::nat) = (b, n)" 
    using assms add_integer.simps 
    by (metis (full_types) diff_zero le_zero_eq nat_arith.rule0)

lemma "ADD x ZERO = x" 
proof -
  obtain b n where xfact: "Rep_INTEGER x = (b, n) \<and> (n \<noteq> 0 \<or> b = True)" using Rep_INTEGER by fastforce
  have "add_integer (b, n) (True, 0) = (b, n)" using xfact h by auto
  then have "Abs_INTEGER (add_integer (b, n) (True, 0)) = Abs_INTEGER (b, n)" by auto
  then have "ADD (Abs_INTEGER (b, n)) (Abs_INTEGER (True, 0)) = (Abs_INTEGER (b, n))"
    using ADD_def Abs_INTEGER_inverse xfact by auto
  then show ?thesis using  Rep_INTEGER_inverse [of x] ZERO_def xfact by auto

(* Another example of a 'subtype' construction: naturals modeled as non-neg integers.*)


typedef NAT = "{ n :: int. 0 \<le> n }" by auto
(* We'd like to add, multiply, etc. and have commutativity and distributive law, 
but ...we have to do the work ourselves *)


(* more general creation of new types: quotients *)
(* an example we've already seen *)
quotient_type int = "nat \<times> nat" / "(\<lambda>(x, y) (u, v). x + v = u + y)"

(* As before, there's an Abs_T and a Rep_T functions, called "morphisms" *)

(* In .../HOL.thy we have this, where WE choose names for the  morphisms.

quotient_type int = "nat \<times> nat" / "intrel"
  morphisms Rep_Integ Abs_Integ
proof (rule equivpI)
  show "reflp intrel" by (auto simp: reflp_def)
  show "symp intrel" by (auto simp: symp_def)
  show "transp intrel" by (auto simp: transp_def)
qed

*)

(* 
Lifting and Transfer: define types and lift some definitions 
to the new type; then, using "Transfer", automatically move a theorem
from the "Rep" domain to the "Abs" domain. 
*) 

(* 
"Lifting" workflow:
* define a type via some predicate P as before
* tell the lifting package about your new type
* lift some definitions on rep-type to abs-type
* whenever result of a function contains an abs-type, you have an obligation:
   show that the result satisfies the defining predicate P
* For inputs, one can ASSUME that they satisfy P. 

"Transfer" workflow: (?)
Given some property on the abstract type
Convert to property on representative type
one may assume each representative element satisfies P
*)

(* By example *)
(* already done above:
typedef INTEGER = "{ bn. case bn of (b,n :: nat) \<Rightarrow> n = 0 \<longrightarrow> b}" by auto
*)
setup_lifting type_definition_INTEGER
lift_definition Zero :: INTEGER is "(True,0)" sorry
(* show that (True,0) satisfies predicate *)

lift_definition Add :: "INTEGER \<Rightarrow> INTEGER \<Rightarrow> INTEGER" is add_integer sorry

(* show that add_integer bn1 bn2 satisfies predicate,
whenever bn1 and bn2 satisfy predicate *)

lemma "Add x Zero = x"
(* show that add_integer bn (True,0) = bn,
whenever bn satisfies predicate *)
  sorry