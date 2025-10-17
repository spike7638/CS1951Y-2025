theory "sch"
imports Complex_Main
begin

typedef pReal = "{x::real . x \<noteq> 0}" 
proof -
  have "(1::real) \<noteq> (0::real)" using zero_neq_one by metis
  then show ?thesis by blast
qed

(*====Integers as (bool,nat) pairs; (True, 0) represents 0 ==========*)
typedef INTEGER = "{ bn. case bn of (b,n :: nat) \<Rightarrow> n = 0 \<longrightarrow> b}" by auto

(* The pedestrian approach *)
definition ZERO :: INTEGER where
  "ZERO = Abs_INTEGER (True, 0)"

fun add :: "bool \<times> nat \<Rightarrow> bool \<times> nat \<Rightarrow> bool \<times> nat" where
  "add (True,n) (True,m) = (True, n+m)"
| "add (False,n) (False,m) = (False, n+m)"
| "add (True,n) (False,m) = (if m \<le> n then (True, n - m) else (False, m - n))"
| "add (False,n) (True,m) = (if n \<le> m then (True, m - n) else (False, n - m))"

definition ADD :: "INTEGER \<Rightarrow> INTEGER \<Rightarrow> INTEGER" where
  "ADD x y = Abs_INTEGER (add (Rep_INTEGER x) (Rep_INTEGER y))"

lemma h:
  fixes b n
  assumes "n \<noteq> 0 \<or> b = True"
  shows "add (b, n) (True, 0::nat) = (b, n)" using assms add.simps 
    by (metis (full_types) diff_zero le_zero_eq nat_arith.rule0)

lemma "ADD x ZERO = x" 
proof -
  obtain b n where xfact: "Rep_INTEGER x = (b, n) \<and> (n \<noteq> 0 \<or> b = True)" using Rep_INTEGER by fastforce
  have 1: "add (b, n) (True, 0::nat) = (b, n)" using h xfact by auto
  then have "add (Rep_INTEGER x) (True, 0::nat) = (Rep_INTEGER x)" 
    using xfact Rep_INTEGER ZERO_def by auto
  then have "add (Rep_INTEGER x) (Rep_INTEGER ZERO) = (Rep_INTEGER x)" 
    using  ZERO_def Abs_INTEGER_inverse [of "(True, 0)"] by auto
  then show "ADD x ZERO = x"  using ADD_def Rep_INTEGER_inverse by auto
qed

(* The more sophisticated approach, using Lifting/Transfer *)

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
use "transfer" to convert to property on representative type
one may assume each representative element satisfies P
*)

(* By example *)
(* Recall:
typedef INTEGER = "{ bn. case bn of (b,n :: nat) \<Rightarrow> n = 0 \<longrightarrow> b}" by auto
*)

setup_lifting type_definition_INTEGER
lift_definition Zero :: INTEGER is "(True,0)" by auto
(*obligation above:  show that (True,0) satisfies predicate *)

fun add_integer :: "bool \<times> nat \<Rightarrow> bool \<times> nat \<Rightarrow> bool \<times> nat" where 
  "add_integer (True,n) (True,m) = (True, n+m)"
| "add_integer (False,n) (False,m) = (False, n+m)"
| "add_integer (True,n) (False,m) = (if m \<le> n then (True, n - m) else (False, m - n))"
| "add_integer (False,n) (True,m) = (if n \<le> m then (True, m - n) else (False, n - m))"

lift_definition Add :: "INTEGER \<Rightarrow> INTEGER \<Rightarrow> INTEGER" is add_integer 
proof (transfer, goal_cases)
  case (1 prod1 prod2)
  obtain  bs ns where  sumf: "add_integer prod1 prod2 = (bs, ns)" using old.prod.exhaust by blast 
  have "ns =  0 \<longrightarrow> bs" 
    by (smt (verit) "1"(1,2) Pair_inject add_integer.simps(1,2,3,4) add_is_0 case_prodE diff_is_0_eq sumf)
  then show ?case   by (simp add: sumf)
qed 

lemma "Add x Zero = x"
(* show that add_integer bn (True,0) = bn,
whenever bn satisfies predicate *)

(* Note: 'lift_definition' and 'transfer' both often produce
new proof-obligations that are messy (using rep-types instead of 
abs-types); generates a lot of fix-assume-show stuff. 
The proof method "goal-cases" helps
produce one case for each subgoal
(case 1 x y z) starts first subgoal where x, y, z are user-chosen 
names for meta-quantified variables
The label '1' refers to all the assumptions.
"show ?case" is the current conclusion-to-be-shown
"next" separates cases. 
*)
proof (transfer, goal_cases)
  case (1 x)
  then show ?case using h 
    by (smt (z3) add.simps(4) add_integer.simps(1,4) case_prodE nat_arith.rule0)
qed 
