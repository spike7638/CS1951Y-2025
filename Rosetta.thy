theory Rosetta
  imports Complex_Main 
begin

text\<open>A collection of examples of tiny theorems that use a particular structure, and then that structure
implemented in Isabelle.\<close>

text\<open>Case-based proof. To show $a \le abs(a)$, consider the two cases where $a \ge 0$ and $a < 0$. In the first case,
$abs(a)$ is just $a$, so we need prove that $a \le a$, which is obvious. In the second, $abs(a) = -a$, 
and we need to show that $a \le -a$ ... which is true because $a < 0$, so $0 < -a$, hence $a < -a$. \<close>

definition abs:: "real \<Rightarrow> real" where
"abs x = (if (x \<ge> 0) then  x else -x)"

lemma case_example:
  fixes x
  shows "x \<le> (abs x)"
proof (cases "x \<ge> 0")
  case True
  then show ?thesis sorry
next
  case False
  then show ?thesis sorry
  oops

  text \<open>The format above is what Isar offers as an automatic completion once you put in "x \<ge> 0" as the argument
for 'cases'. In general, cases takes its argument and makes one case for each constructor; booleans have 
two constructors, True and False, and 'cases' uses these as the names for the two cases. Often that's not a 
great choice. You can rename them like this:\<close>

lemma case_example:
  fixes x
  shows "x \<le> (abs x)"
proof (cases "x \<ge> 0")
  case nonneg: True
  then show ?thesis using nonneg abs_def by simp 
next
  case negative: False
  then show ?thesis using negative abs_def by simp
qed

text\<open>and 'using nonneg' reads better than 'using True'. This approach to writing cases also works 
for lists, where the 
two constructors are Nil and Cons (for which "#" is an infix notation). This small example doesn't 
need to use the Case conditions, but if it did, you might write "show ?thesis using Nil by simp", for
example. Or, as before, you could assign new labels to the cases.  \<close>

lemma case_example2:
  fixes x::"real list"
  fixes b::"real"
  shows "(hd (b # x)) = b"
proof (cases "x")
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  then show ?thesis by simp
qed

text \<open>Goal-reduction in the form "it suffices to prove". "It suffices to prove" is often used to 
simplify or alter the goal of a proof before getting into the meat of it. Isabelle 
folks call this a 'backwards' proof, and it's not Isar's strong suit, but you
can do it. Here I'm showing an example of proving that A and B imply C. I claim that it suffices to 
show that A and B imply D. Normally at this point, you'd give a proof of that claim, but here I'd
added it as a hypothesis in the lemma, so I can just say "by a2". At this point, after the first 
'blast', the goal in the proof-state has changed to A /\ B ==> D, but we're still within the logical 
scope of the "presume ph: D". The "next" leaves that scope, and all we need to show 
is $A /\ B ==> D". Fortunately that, too, is easy to prove because I included it in the assumptions
as a way to provide a minimal proof. 
\<close>

lemma suffices_example:
  fixes A B C
  assumes a1: "A \<and> B \<Longrightarrow> D"
  assumes a2: "D \<Longrightarrow> C"
  shows "A \<and>  B \<Longrightarrow> C"
proof -
  presume ph: D 
  show ?thesis using ph a2  by blast
next
  show q: "A \<and> B \<Longrightarrow> D" using a1 by blast
qed

text \<open>Here's a concrete example of that kind of proof. In the middle it uses a sequence of
inequalities to show one large inequality, using "chaining", in which "..." means "the right hand
side of the previous inequality in the chain" and the "." at the end means "combine all these
inequalities into LHS \<le> RHS, where LHS is the left-hand side of the FIRST fact in the chain, 
and RHS is the right-hand side of the LAST fact in the chain." The statement itself is an exercise
in Spivak's "Calculus", and while it can be proved by noting that the expression is a quadratic form
with eigenvalues 1/2 and 3/2 that are both positive, I wanted to give an elementary proof.
\<close>

lemma quadratic: 
  fixes x::"real" and y
  shows "0 \<le> x^2 + x*y + y^2"
proof -
  presume p: "0 \<le> 4*x^2 + 4*x*y + 4*y^2" 
  show ?thesis using p by linarith
next
  have nneg_square: "0 \<le> (u::real)^2" for u by simp
  have py: "0 \<le> 3 * y^2" using nneg_square [of y] by simp
  have "(0::real) \<le> (2*x + y)^2" using nneg_square [of "2*x + y"] .
  also have "...\<le> 4*x^2 + 4*x*y + y^2"  by (simp add:power2_sum)
  also have "...\<le> 4*x^2 + 4*x*y +4* y^2" using py by simp
  finally show "0 \<le>  4*x^2 + 4*x*y +4* y^2" .
qed

text \<open>Induction. Isabelle has incredibly rich induction and co-induction stuff built into it, but
for basic induction over the natural numbers (or over lists, or any other datatype with just one 
or two constructors) things are relatively simple. From Peter Zeller via stackexchange, here are two
models for proving that $n + 0 = n$ for every natural number $n$. Note that "plus_nat.add_0" is 
the \emph{definition}, for naturals, of adding zero, and similarly add_Suc. In each proof, "Suc.IH"
is used as a fact. It's a new fact introduced by the "induction" proof method, asserting that
"n + 0 = n"; we're then aiming to prove that (Suc n) + 0 = Suc n. Using part of the definition 
of addition for natural numbers (plus_nat.add_Suc) we change the goal to proving that Suc (n+0) = Suc n.
We then use Suc.IH to replace the "n+0" on the left with $n$, and we're reduced to proving "Suc n = Suc n"; 
we do this with the rule "refl", which says that  for any $x$, we have $x = x$. 

The "by (subst Suc.SH) (rule refl)" uses a variant of "by" in which you can have two steps
following the "by"; details are on pages 148-150 of the isar reference manual. 
\<close>

theorem add_0: "n+0 = (n::nat)"
proof (induction n)
  case 0 \<comment> \<open>Focus on induction base subgoal here\<close>
  show "0 + 0 = (0::nat)" 
    by (rule plus_nat.add_0)
next
  case (Suc n) \<comment> \<open>Focus on induction step subgoal here\<close>
  show "Suc n + 0 = Suc n"
    thm Suc.IH
  proof (subst plus_nat.add_Suc)
    show "Suc (n + 0) = Suc n"
      by (subst Suc.IH)  (rule refl)
  qed
qed

theorem add_0_1: "n+0 = (n::nat)"  \<comment> \<open>version avoiding "by A B" \<close>
proof (induction n)
  case 0 \<comment> \<open>Focus on induction base subgoal here\<close>
  show "0 + 0 = (0::nat)" 
    by (rule plus_nat.add_0)
next
  case (Suc n) \<comment> \<open>Focus on induction step subgoal here\<close>
  show "Suc n + 0 = Suc n"
    thm Suc.IH
  proof (subst plus_nat.add_Suc)
    show "Suc (n + 0) = Suc n"
    proof (subst Suc.IH)
      show "Suc n = Suc n" by (rule refl)
    qed
  qed
qed

theorem add_0_2: "n+0 = (n::nat)"  \<comment> \<open>version avoiding "by A B", but using the "proof A qed B" form \<close>
proof (induction n)
  case 0 \<comment> \<open>Focus on induction base subgoal here\<close>
  show "0 + 0 = (0::nat)" 
    by (rule plus_nat.add_0)
next
  case (Suc n) \<comment> \<open>Focus on induction step subgoal here\<close>
  show "Suc n + 0 = Suc n"
    thm Suc.IH
  proof (subst plus_nat.add_Suc)
    show "Suc (n + 0) = Suc n"
    proof (subst Suc.IH)
    qed (rule refl)
  qed
qed


text\<open>
Or implicitly, without naming cases:\<close>

theorem add_0_3: "n+0 = (n::nat)"
proof (induction n)
  show "0 + 0 = (0::nat)" 
    by (rule plus_nat.add_0)
next
  fix n :: nat
  assume IH: "n + 0 = n"
  show "Suc n + 0 = Suc n"
  proof (subst plus_nat.add_Suc)
    show "Suc (n + 0) = Suc n"
      by (subst IH) (rule refl)
  qed
qed

text\<open>Contradiction. Isabelle calls this "classical contradiction", and the proof method is "rule 
ccontr". 

In the example shown here, I've taken the goal ("even n") and explicitly negated it. It's tempting 
to say "the opposite of even is odd!" and just use, as our contradiction hypothesis, "odd n", but
that requires that someone has previously proven somewhere that for all natural n, either "odd n"
or "even n", but not both. If you place your cursor just before the 'obtain', you'll see that
Isabelle has in fact replaced "not (even n)" with "odd n", but not every proof works out like this.
I ALWAYS write the exact negated goal as the contradiction hypothesis, particularly in the case 
where the original goal is itself a negation. So if the original goal is some expression \<not>P, my 
contradiction hypothesis is \<not>\<not>P.

The goal in a classical contradiction proof is to show "False" by arriving at a pair of mutually 
contradictory facts; in this example, those facts are "n^2 + 5 is even" and "n^2 + 5 is odd".
\<close>

lemma 
  fixes n::nat
  assumes "odd (n^2 + 5)"
  shows "even n"
proof (rule ccontr)
  assume ch: "\<not> (even n)"
  obtain k where q: "n = 2*k + 1" using ch oddE by blast
  have s1: "n^2 + 5 = 4*k^2 + 4*k + 6" using q  by (simp add: power2_eq_square)
  have s2: "even (n^2 + 5)" using s1 by simp
  show "False" using assms s2 by blast
qed


text\<open>Here's an attempt at a contradiction proof where I've miatakenly said that the 
negation of \<not>(P \<and> False) is (P \<and> False), but the proof fails when we attempt 
to show False, as you'll see if you place your cursor just after that "show" statement but
before the 'oops'. You might want to try changing the contradiction hypothesis to \<not>\<not>(P \<and> False) 
to see what happens, by swapping the line that's commented out. \<close>


lemma silly:
  fixes P::bool
  assumes P
  shows "\<not>(P \<and> False)"
proof (rule ccontr)
  assume ch: "P \<and> False"
(*  assume ch: "\<not>\<not>(P \<and> False)" *)
  show "False" oops

text\<open>Proof with alternative assumptions. Suppose you know "P \<or> Q", and want 
to show R. One way to do this is to show that P implies R, and then show
that Q implies R. Here's a very silly proof that if n is a natural number,
then n + 1 > 0, done by two cases: one where n is even, the other 
where n is odd. \<close>

lemma nat_pos:
  fixes n::nat
  shows "0 < (n+1)"
proof -
  have "even n \<or> odd n" by simp 
  then show ?thesis
  proof
    assume c1: "even n" 
    obtain k::nat where kfact1: "n = 2*k" using c1 by blast 
    show "0 < n + 1" using kfact1 by simp
  next
    assume c1: "odd n" 
    obtain k::nat where kfact2: "n = 2*k+1" using c1 oddE by blast 
    show "0 < n + 1" using kfact2 by simp
  qed
qed

text\<open>Note that above, the internal proof starts with "proof" rather than 
our usual "proof -"; leaving off the "-" makes isabelle apply 
whatever elimination rule it can to the current fact. In this case,
or-introduction says that to prove that P \<or> Q implies R, you can instead
prove that P implies R and then that Q implies R, so that just 
after the "proof" (with no hyphen after it), we have two distinct 
goals, and are set up to work on proving the first. When we're done, 
we move on to the second using "next".\<close>

text\<open>Logical Equivalence. Just as before, we can use 'proof' without the following
hyphen, and isabelle will apply an elimination rule to convert it to two 
separate goals to be proved. I'll show that n = 1 is equivalent to Suc n = 2 
using this approach. Fortunately, most facts about concrete small integers
can be easily proven by simp. For more complex goals, there would be 
multiple lines between the "assume" and "show" lines for each goal. \<close>

lemma add_one:
  fixes n::nat
  shows "(n = 1) \<longleftrightarrow> ((Suc n) = 2)"
proof -
  show ?thesis
  proof
    assume a: "n = 1"
    show "Suc n = 2" using a by simp 
  next
    assume a: "Suc n = 2"
    show "n = 1" using a by simp 
  qed
qed

text\<open>Forall formulas. The same approach --- the no-hyphen proof --- works 
when you want to prove something like \<forall>n . 0 \<le> n^2, or more generally, 
\<forall> k . P(k), where the 'dot' after the 'forall' is Isabelle's way of separating
the variables from the proposition to be proved. Here's a proof of the 
first of these:\<close>
(*
lemma nonnegative_squares:
  shows "\<forall> n::nat . 0 \<le> n^2" 
proof \<comment> \<open>At this point the 'forall' has become a meta-logic forall\<close>
  fix k::nat  \<comment> \<open>To prove it, we fix some arbitrary nat and prove 
                 the claim for that one. I could have used 'n' 
                 instead of k. but I personally find that confusing\<close>
  show "0 \<le> k^2" by simp
qed
*)

text \<open>Forall formulas, part 2. Because of Isabelle's structure, 'forall'
formulas are seldom the ideal thing to prove. Instead, something like
"0 \<le> (n::nat)^2" is more useful. Here's an essentially identical 
lemma expressed that way. The proof, in this case, is so simple that it 
has zero lines. \<close>


lemma nonnegative_squares_2:
  fixes n::nat
  shows "0 \<le> n^2" 
proof 
qed

text\<open>TO DO\<close>
text\<open>Existence formulas.\<close>
text\<open>Applying foralls\<close>
text\<open>Applying existence formulas\<close>
text\<open>Applying existence formulas with extra conditions\<close>
text\<open>Multi-choice disjunction.\<close>
text\<open>Set equality\<close>
text\<open>Subsets\<close>
