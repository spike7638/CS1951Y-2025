theory THEexample
  imports Complex_Main
begin
(* see src/HOL/Transcendental.thy *)
lemma sin_total:
  assumes y: "-1 \<le> y" "y \<le> 1"
  shows "\<exists>!x. - (pi/2) \<le> x \<and> x \<le> pi/2 \<and> sin x = y"
  sorry

definition arcsin :: "real \<Rightarrow> real"
  where "arcsin y = (THE x. -(pi/2) \<le> x \<and> x \<le> pi/2 \<and> sin x = y)"

lemma arcsin: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> - (pi/2) \<le> arcsin y \<and> arcsin y \<le> pi/2 \<and> sin (arcsin y) = y"
  unfolding arcsin_def by (rule theI' [OF sin_total])

lemma arcsin_pi: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> - (pi/2) \<le> arcsin y \<and> arcsin y \<le> pi \<and> sin (arcsin y) = y"
  by (drule (1) arcsin) (force intro: order_trans)

lemma sin_arcsin [simp]: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> sin (arcsin y) = y"
  by (blast dest: arcsin)

lemma arcsin_bounded: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> - (pi/2) \<le> arcsin y \<and> arcsin y \<le> pi/2"
  by (blast dest: arcsin)

lemma arcsin_lbound: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> - (pi/2) \<le> arcsin y"
  by (blast dest: arcsin)

lemma arcsin_ubound: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> arcsin y \<le> pi/2"
  by (blast dest: arcsin)

lemma arcsin_lt_bounded:
  assumes "- 1 < y" "y < 1"
  shows  "- (pi/2) < arcsin y \<and> arcsin y < pi/2"
proof -
  have "arcsin y \<noteq> pi/2"
    by (metis arcsin assms not_less not_less_iff_gr_or_eq sin_pi_half)
  moreover have "arcsin y \<noteq> - pi/2"
    by (metis arcsin assms minus_divide_left not_less not_less_iff_gr_or_eq sin_minus sin_pi_half)
  ultimately show ?thesis
    using arcsin_bounded [of y] assms by auto
qed

lemma arcsin_sin: "- (pi/2) \<le> x \<Longrightarrow> x \<le> pi/2 \<Longrightarrow> arcsin (sin x) = x"
  unfolding arcsin_def
  using the1_equality [OF sin_total]  by simp

lemma arcsin_unique:
  assumes "-pi/2 \<le> x" and "x \<le> pi/2" and "sin x = y" shows "arcsin y = x"
  using arcsin_sin[of x] assms by force

lemma arcsin_0 [simp]: "arcsin 0 = 0"
  using arcsin_sin [of 0] by simp

end