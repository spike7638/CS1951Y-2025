theory ration
imports Complex_Main
begin
hide_type rat

definition ratrel :: "(int \<times> int) \<Rightarrow> (int \<times> int) \<Rightarrow> bool"
  where "ratrel = (\<lambda>x y. snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x)"

lemma ratrel_iff [simp]: "ratrel x y \<longleftrightarrow> snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x"
  by (simp add: ratrel_def)

lemma exists_ratrel_refl: "\<exists>x. ratrel x x"
proof -
  have "ratrel (0, 1) (0, 1)"  by auto
  then show ?thesis by blast
qed
(*  by (auto intro!: one_neq_zero) *)

lemma symp_ratrel: "symp ratrel"
  by (simp add: ratrel_def symp_def)

lemma transp_ratrel: "transp ratrel"
proof (rule transpI, unfold split_paired_all)
  fix a b a' b' a'' b'' :: int
  assume *: "ratrel (a, b) (a', b')"
  assume **: "ratrel (a', b') (a'', b'')"
  have "b' * (a * b'') = b'' * (a * b')" by simp
  also from * have "a * b' = a' * b" by auto
  also have "b'' * (a' * b) = b * (a' * b'')" by simp
  also from ** have "a' * b'' = a'' * b'" by auto
  also have "b * (a'' * b') = b' * (a'' * b)" by simp
  finally have "b' * (a * b'') = b' * (a'' * b)" .
  moreover from ** have "b' \<noteq> 0" by auto
  ultimately have "a * b'' = a'' * b" by simp
  with * ** show "ratrel (a, b) (a'', b'')" by auto
qed

(*
definition part_equivp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "part_equivp R \<longleftrightarrow> (\<exists>x. R x x) \<and> (\<forall>x y. R x y \<longleftrightarrow> R x x \<and> R y y \<and> R x = R y)"
*)
lemma part_equivp_ratrel: "part_equivp ratrel"
  by (rule part_equivpI [OF exists_ratrel_refl symp_ratrel transp_ratrel])

quotient_type rat = "int \<times> int" / partial: "ratrel"
  morphisms Rep_Rat Abs_Rat
  by (rule part_equivp_ratrel)

lemma Domainp_cr_rat [transfer_domain_rule]: "Domainp pcr_rat = (\<lambda>x. snd x \<noteq> 0)"
  by (simp add: rat.domain_eq)


subsubsection \<open>Representation and basic operations\<close>

lift_definition Fract :: "int \<Rightarrow> int \<Rightarrow> rat"
  is "\<lambda>a b. if b = 0 then (0, 1) else (a, b)"
  by simp

lemma eq_rat:
  "\<And>a b c d. b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b = Fract c d \<longleftrightarrow> a * d = c * b"
  "\<And>a. Fract a 0 = Fract 0 1"
  "\<And>a c. Fract 0 a = Fract 0 c"
  by (transfer, simp)+

lemma Rat_cases [case_names Fract, cases type: rat]:
  assumes that: "\<And>a b. q = Fract a b \<Longrightarrow> b > 0 \<Longrightarrow> coprime a b \<Longrightarrow> C"
  shows C
proof -
  obtain a b :: int where q: "q = Fract a b" and b: "b \<noteq> 0"
    by transfer simp
  let ?a = "a div gcd a b"
  let ?b = "b div gcd a b"
  from b have "?b * gcd a b = b"
    by simp
  with b have "?b \<noteq> 0"
    by fastforce
  with q b have q2: "q = Fract ?a ?b"
    by (simp add: eq_rat dvd_div_mult mult.commute [of a])
  from b have coprime: "coprime ?a ?b"
    by (auto intro: div_gcd_coprime)
  show C
  proof (cases "b > 0")
    case True
    then have "?b > 0"
      by (simp add: nonneg1_imp_zdiv_pos_iff)
    from q2 this coprime show C by (rule that)
  next
    case False
    have "q = Fract (- ?a) (- ?b)"
      unfolding q2 by transfer simp
    moreover from False b have "- ?b > 0"
      by (simp add: pos_imp_zdiv_neg_iff)
    moreover from coprime have "coprime (- ?a) (- ?b)"
      by simp
    ultimately show C
      by (rule that)
  qed
qed

lemma Rat_induct [case_names Fract, induct type: rat]:
  assumes "\<And>a b. b > 0 \<Longrightarrow> coprime a b \<Longrightarrow> P (Fract a b)"
  shows "P q"
  using assms by (cases q) simp

instantiation rat :: field
begin

lift_definition zero_rat :: "rat" is "(0, 1)"
  by simp

lift_definition one_rat :: "rat" is "(1, 1)"
  by simp

lemma Zero_rat_def: "0 = Fract 0 1"
  by transfer simp

lemma One_rat_def: "1 = Fract 1 1"
  by transfer simp

lift_definition plus_rat :: "rat \<Rightarrow> rat \<Rightarrow> rat"
  is "\<lambda>x y. (fst x * snd y + fst y * snd x, snd x * snd y)"
  by (auto simp: distrib_right) (simp add: ac_simps)

lemma add_rat [simp]:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b + Fract c d = Fract (a * d + c * b) (b * d)"
  using assms by transfer simp

lift_definition uminus_rat :: "rat \<Rightarrow> rat" is "\<lambda>x. (- fst x, snd x)"
  by simp

lemma minus_rat [simp]: "- Fract a b = Fract (- a) b"
  by transfer simp

lemma minus_rat_cancel [simp]: "Fract (- a) (- b) = Fract a b"
  by (cases "b = 0") (simp_all add: eq_rat)

definition diff_rat_def: "q - r = q + - r" for q r :: rat

lemma diff_rat [simp]:
  "b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b - Fract c d = Fract (a * d - c * b) (b * d)"
  by (simp add: diff_rat_def)

lift_definition times_rat :: "rat \<Rightarrow> rat \<Rightarrow> rat"
  is "\<lambda>x y. (fst x * fst y, snd x * snd y)"
  by (simp add: ac_simps)

lemma mult_rat [simp]: "Fract a b * Fract c d = Fract (a * c) (b * d)"
  by transfer simp

lemma mult_rat_cancel: "c \<noteq> 0 \<Longrightarrow> Fract (c * a) (c * b) = Fract a b"
  by transfer simp

lift_definition inverse_rat :: "rat \<Rightarrow> rat"
  is "\<lambda>x. if fst x = 0 then (0, 1) else (snd x, fst x)"
  by (auto simp add: mult.commute)

lemma inverse_rat [simp]: "inverse (Fract a b) = Fract b a"
  by transfer simp

definition divide_rat_def: "q div r = q * inverse r" for q r :: rat

lemma divide_rat [simp]: "Fract a b div Fract c d = Fract (a * d) (b * c)"
  by (simp add: divide_rat_def)

instance
proof
  fix q r s :: rat
  show "(q * r) * s = q * (r * s)"
    by transfer simp
  show "q * r = r * q"
    by transfer simp
  show "1 * q = q"
    by transfer simp
  show "(q + r) + s = q + (r + s)"
    by transfer (simp add: algebra_simps)
  show "q + r = r + q"
    by transfer simp
  show "0 + q = q"
    by transfer simp
  show "- q + q = 0"
    by transfer simp
  show "q - r = q + - r"
    by (fact diff_rat_def)
  show "(q + r) * s = q * s + r * s"
    by transfer (simp add: algebra_simps)
  show "(0::rat) \<noteq> 1"
    by transfer simp
  show "inverse q * q = 1" if "q \<noteq> 0"
    using that by transfer simp
  show "q div r = q * inverse r"
    by (fact divide_rat_def)
  show "inverse 0 = (0::rat)"
    by transfer simp
qed

end
end
