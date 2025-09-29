(* Title:      Kolmogorov_Chentsov/Dyadic_Interval.thy
   Author:     Christian Pardillo Laursen, University of York
*)

section "Intervals of dyadic rationals"

theory Dyadic_Interval
  imports "HOL-Analysis.Analysis"
begin

text \<open> In this file we describe intervals of dyadic numbers ${S..T}$ for reals S T. We use the floor
  and ceiling functions to approximate the numbers with increasing accuracy. \<close>

lemma frac_floor: \<open>\<lfloor>x\<rfloor> = x - frac x\<close>
  by (simp add: frac_def)

lemma frac_ceil: \<open>\<lceil>x\<rceil> = x + frac (- x)\<close>
  apply (cases \<open>x = real_of_int \<lfloor>x\<rfloor>\<close>)
  unfolding ceiling_altdef apply simp
   apply (metis Ints_minus Ints_of_int)
  apply (simp add: frac_neg frac_floor)
  done

lemma floor_pow2_lim: \<open>(\<lambda>n. \<lfloor>2^n * T\<rfloor> / 2 ^ n) \<longlonglongrightarrow> T\<close>
proof (intro LIMSEQ_I)
  fix r :: \<open>real\<close> assume \<open>r > 0\<close>
  obtain k where k: \<open>1 / 2^k < r\<close>
    by (metis \<open>r > 0\<close> one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76))
  then have \<open>\<forall>n\<ge>k. norm (\<lfloor>2 ^ n * T\<rfloor> / 2 ^ n - T) < r\<close>
    apply (simp add: frac_floor field_simps)
    by (smt (verit, ccfv_SIG) \<open>0 < r\<close> frac_lt_1 mult_left_mono power_increasing)
  then show \<open>\<exists>no. \<forall>n\<ge>no. norm (real_of_int \<lfloor>2 ^ n * T\<rfloor> / 2 ^ n - T) < r\<close>
    by blast
qed

lemma floor_pow2_leq: \<open>\<lfloor>2^n * T\<rfloor> / 2 ^ n \<le> T\<close>
  by (simp add: frac_floor field_simps)

lemma ceil_pow2_lim: \<open>(\<lambda>n. \<lceil>2^n * T\<rceil> / 2 ^ n) \<longlonglongrightarrow> T\<close>
proof (intro LIMSEQ_I)
  fix r :: \<open>real\<close> assume \<open>r > 0\<close>
  obtain k where k: \<open>1 / 2^k < r\<close>
    by (metis \<open>r > 0\<close> one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76))
  then have \<open>\<forall>n\<ge>k. norm (\<lceil>2 ^ n * T\<rceil> / 2 ^ n - T) < r\<close>
    apply (simp add: frac_ceil field_simps)
    by (smt (verit) \<open>0 < r\<close> frac_lt_1 mult_left_mono power_increasing)
  then show \<open>\<exists>no. \<forall>n\<ge>no. norm (\<lceil>2 ^ n * T\<rceil> / 2 ^ n - T) < r\<close>
    by blast 
qed

lemma ceil_pow2_geq: \<open>\<lceil>2^n * T\<rceil> / 2 ^ n \<ge> T\<close>
  by (simp add: frac_ceil field_simps)

text \<open> \texttt{dyadic\_interval\_step} $n$ $S$ $T$ is the collection of dyadic numbers in $\{S..T\}$ with denominator $2^n$. As
 $n \to \infty$ this collection approximates $\{S..T\}$. Compare with @{thm dyadics_def}\<close>

definition dyadic_interval_step :: \<open>nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real set\<close>
  where \<open>dyadic_interval_step n S T \<equiv> (\<lambda>k. k / (2 ^ n)) ` {\<lceil>2^n * S\<rceil>..\<lfloor>2^n * T\<rfloor>}\<close>

definition dyadic_interval :: \<open>real \<Rightarrow> real \<Rightarrow> real set\<close>
  where \<open>dyadic_interval S T \<equiv> (\<Union>n. dyadic_interval_step n S T)\<close>

lemma dyadic_interval_step_empty[simp]: \<open>T < S \<Longrightarrow> dyadic_interval_step n S T = {}\<close>
  unfolding dyadic_interval_step_def apply simp
  by (smt (verit) ceil_pow2_geq floor_le_ceiling floor_mono floor_pow2_leq
      linordered_comm_semiring_strict_class.comm_mult_strict_left_mono zero_less_power)

lemma dyadic_interval_step_singleton[simp]: \<open>X \<in> \<int> \<Longrightarrow> dyadic_interval_step n X X = {X}\<close>
proof -
  assume \<open>X \<in> \<int>\<close>
  then have *: \<open>\<lfloor>2 ^ k * X\<rfloor> = 2 ^ k * X\<close> for k :: \<open>nat\<close>
    by simp
  then show \<open>?thesis\<close>
    unfolding dyadic_interval_step_def apply (simp add: ceiling_altdef)
    using * by presburger
qed

lemma dyadic_interval_step_zero [simp]: \<open>dyadic_interval_step 0 S T = real_of_int ` {\<lceil>S\<rceil> .. \<lfloor>T\<rfloor>}\<close>
  unfolding dyadic_interval_step_def by simp

lemma dyadic_interval_step_mem [intro]:
  assumes\<open>x \<ge> 0\<close> \<open>T \<ge> 0\<close> \<open>x \<le> T\<close> 
  shows \<open>\<lfloor>2^n * x\<rfloor> / 2 ^ n \<in> dyadic_interval_step n 0 T\<close>
  unfolding dyadic_interval_step_def by (simp add: assms image_iff floor_mono)

lemma dyadic_interval_step_iff: 
  \<open>x \<in> dyadic_interval_step n S T \<longleftrightarrow>
   (\<exists>k. k \<ge> \<lceil>2^n * S\<rceil> \<and> k \<le> \<lfloor>2^n * T\<rfloor> \<and> x = k/2^n)\<close>
  unfolding dyadic_interval_step_def by (auto simp add: image_iff)

lemma dyadic_interval_step_memI [intro]:
  assumes \<open>\<exists>k::int. x = k/2^n\<close> \<open>x \<ge> S\<close> \<open>x \<le> T\<close>
  shows \<open>x \<in> dyadic_interval_step n S T\<close>
proof -
  obtain k :: \<open>int\<close> where \<open>x = k/2^n\<close>
    using assms(1) by blast
  then have k: \<open>k = 2^n * x\<close>
    by simp
  then have \<open>k \<ge> \<lceil>2^n * S\<rceil>\<close>
    by (simp add: assms(2) ceiling_le)
  moreover from k have \<open>k \<le> \<lfloor>2^n * T\<rfloor>\<close>
    by (simp add: assms(3) le_floor_iff)
  ultimately show \<open>?thesis\<close>
    using dyadic_interval_step_iff \<open>x = k / 2 ^ n\<close> by blast
qed

lemma mem_dyadic_interval: \<open>x \<in> dyadic_interval S T \<longleftrightarrow> (\<exists>n. x \<in> dyadic_interval_step n S T)\<close>
  unfolding dyadic_interval_def by blast

lemma mem_dyadic_intervalI: \<open>\<exists>n. x \<in> dyadic_interval_step n S T \<Longrightarrow> x \<in> dyadic_interval S T\<close>
  using mem_dyadic_interval by fast

lemma dyadic_step_leq: \<open>x \<in> dyadic_interval_step n S T \<Longrightarrow> x \<le> T\<close>
  unfolding dyadic_interval_step_def apply clarsimp
  by (simp add: divide_le_eq le_floor_iff mult.commute)

lemma dyadics_leq: \<open>x \<in> dyadic_interval S T \<Longrightarrow> x \<le> T\<close>
  using dyadic_step_leq mem_dyadic_interval by blast

lemma dyadic_step_geq: \<open>x \<in> dyadic_interval_step n S T \<Longrightarrow> x \<ge> S\<close>
  unfolding dyadic_interval_step_def apply clarsimp
  by (simp add: ceiling_le_iff mult.commute pos_le_divide_eq)

lemma dyadics_geq: \<open>x \<in> dyadic_interval S T \<Longrightarrow> x \<ge> S\<close>
  using dyadic_step_geq mem_dyadic_interval by blast

corollary dyadic_interval_subset_interval [simp]: \<open>(dyadic_interval 0 T) \<subseteq> {0..T}\<close>
  using dyadics_geq dyadics_leq by force

lemma zero_in_dyadics: \<open>T \<ge> 0 \<Longrightarrow> 0 \<in> dyadic_interval_step n 0 T\<close>
  using dyadic_interval_step_def by force

text \<open> The following theorem is useful for reasoning with at\_within \<close>
lemma dyadic_interval_converging_sequence:
  assumes \<open>t \<in> {0..T}\<close> \<open>T \<noteq> 0\<close>
  shows \<open>\<exists>s. \<forall>n. s n \<in> dyadic_interval 0 T - {t} \<and> s \<longlonglongrightarrow> t\<close>
proof -
  from assms have \<open>T > 0\<close>
    by auto
  consider (eq_0) \<open>t = 0\<close> | (dyadic) \<open>t \<in> dyadic_interval 0 T - {0}\<close> | (real) \<open>t \<notin> dyadic_interval 0 T\<close>
    by blast
  then show \<open>?thesis\<close>
  proof cases
    case eq_0
    obtain n where \<open>1 \<le> 2 ^ n * T\<close>
    proof -
      assume *: \<open>\<And>n. 1 \<le> 2 ^ n * T \<Longrightarrow> thesis\<close>
      obtain n where \<open>2 ^ n > 1/T\<close>
        using real_arch_pow by fastforce
      then have \<open>2 ^ n * T \<ge> 1\<close>
        using \<open>T > 0\<close> by (simp add: field_simps)
      then show \<open>?thesis\<close>
        using * by blast
    qed
    define s :: \<open>nat \<Rightarrow> real\<close> where \<open>s = (\<lambda>m. 1/2^(m + n))\<close>
    have \<open>\<forall>m. s m \<in> dyadic_interval_step (m + n) 0 T - {0}\<close>
      unfolding s_def apply (simp add: dyadic_interval_step_iff)
      using  \<open>1 \<le> 2 ^ n * T\<close>
      by (smt (verit, best) \<open>0 < T\<close> le_add2 mult_right_mono power_increasing_iff)
    then have \<open>\<forall>m. s m \<in> dyadic_interval 0 T - {0}\<close>
      using mem_dyadic_interval by auto
    moreover {
      have \<open>(\<lambda>m. (1::real)/2^m) \<longlonglongrightarrow> 0\<close>
        by (simp add: divide_real_def LIMSEQ_inverse_realpow_zero)
      then have \<open>s \<longlonglongrightarrow> 0\<close>
        unfolding s_def using LIMSEQ_ignore_initial_segment by auto
    }
    ultimately show \<open>?thesis\<close>
      using eq_0 by blast
  next
    case dyadic
    then have \<open>t \<noteq> 0\<close>
      by blast
    from dyadic obtain n where n: \<open>t \<in> dyadic_interval_step n 0 T\<close>
      by (auto simp: mem_dyadic_interval)
    then obtain k :: \<open>int\<close> where k: \<open>t = k / 2^n\<close> \<open>k \<le> \<lfloor>2 ^ n * T\<rfloor>\<close>
      using dyadic_interval_step_iff by blast
    then have \<open>k > 0\<close>
      using \<open>t \<noteq> 0\<close> dyadic_interval_step_iff n by force
    define s :: \<open>nat \<Rightarrow> real\<close> where \<open>s \<equiv> \<lambda>m. (k * 2^(m+1) - 1) / 2 ^ (m + n + 1)\<close>
    have \<open>s m \<in> dyadic_interval_step (m + n + 1) 0 T\<close> for m
    proof -
      have \<open>k * (2 ^ (m+1)) - 1 \<le> \<lfloor>2 ^ n * T\<rfloor> * (2 ^ (m+1)) - 1\<close>
        by (smt (verit) k(2) mult_right_mono zero_le_power)
      also have \<open>... \<le> \<lfloor>2 ^ n * T\<rfloor> * \<lfloor>(2 ^ (m+1))\<rfloor>\<close>
        by (metis add.commute add_le_cancel_left diff_add_cancel diff_self floor_numeral_power
            zero_less_one_class.zero_le_one)
      also have \<open>\<lfloor>2 ^ n * T\<rfloor> * \<lfloor>(2 ^ (m+1))\<rfloor> \<le> \<lfloor>2 ^ n * T * (2 ^ (m+1))\<rfloor>\<close>
        by (smt (z3) \<open>0 < T\<close> floor_one floor_power le_mult_floor mult_nonneg_nonneg of_int_1
            of_int_add one_add_floor one_add_one zero_le_power)
      also have \<open>... = \<lfloor>(2 ^ (m+n+1)) * T\<rfloor>\<close>
        apply (rule arg_cong[where f=\<open>floor\<close>])
        by (simp add: power_add)
      finally show \<open>?thesis\<close>
        unfolding s_def apply (simp only: dyadic_interval_step_iff)
        apply (rule exI[where x=\<open>k * (2 ^ (m+1)) - 1\<close>])
        by (simp add: \<open>0 < k\<close>)
    qed
    then have \<open>s m \<in> dyadic_interval 0 T\<close> for m
      using mem_dyadic_interval by blast
    moreover have \<open>s m \<noteq> t\<close> for m
      unfolding s_def k(1) by (simp add: power_add field_simps)
    moreover have \<open>s \<longlonglongrightarrow> t\<close>
    proof
      fix e :: \<open>real\<close> assume \<open>0 < e\<close>
      then obtain m where \<open>1 / 2 ^ m < e\<close>
        by (metis one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76))
      { fix m' assume \<open>m' \<ge> m\<close>
        then have \<open>1 / 2 ^ m' < e\<close>
          using \<open>1/2^m < e\<close>
          by (smt (verit) frac_less2 le_eq_less_or_eq power_strict_increasing zero_less_power)
        then have \<open>1/ 2^(m'+n+1) < e\<close>
          by (smt (verit, ccfv_SIG) divide_less_eq_1_pos half_gt_zero_iff power_less_imp_less_exp 
              power_one_over power_strict_decreasing trans_less_add1)
        have \<open>s m' - t = (k * 2^(m'+1) - 1) / 2 ^ (m' + n + 1) - k / 2 ^ n\<close>
          by (simp add: s_def k(1))
        also have \<open>... = ((k * 2 ^ (m' + 1) - 1) - (k * 2 ^(m'+1))) / 2 ^ (m' + n + 1)\<close>
          by (simp add: field_simps power_add)
        also have \<open>... = -1/ 2^(m'+n+1)\<close>
          by (simp add: field_simps)
        finally have \<open>dist (s m') t < e\<close>
          unfolding s_def k(1)
          apply (simp add: dist_real_def)
          using \<open>1 / 2 ^ (m' + n + 1) < e\<close> by auto
      }
      then show \<open>\<forall>\<^sub>F x in sequentially. dist (s x) t < e\<close>
        apply (simp add: eventually_sequentially)
        apply (intro exI[where x=\<open>m\<close>])
        by simp
    qed
    ultimately show \<open>?thesis\<close>
      by blast
  next
    case real
    then obtain n where \<open>dyadic_interval_step n 0 T \<noteq> {}\<close>
      by (metis \<open>0 < T\<close> empty_iff less_eq_real_def zero_in_dyadics)
    define s :: \<open>nat \<Rightarrow> real\<close> where \<open>s \<equiv> \<lambda>m. \<lfloor>2^(m+n) * t\<rfloor> / 2 ^ (m+n)\<close>
    have \<open>s m \<in> dyadic_interval_step (m+n) 0 T\<close> for m
      unfolding s_def
      by (metis assms(1) atLeastAtMost_iff ceiling_zero dyadic_interval_step_iff floor_mono 
          mult.commute mult_eq_0_iff mult_right_mono zero_le_floor zero_le_numeral zero_le_power)
    then have \<open>s m \<in> dyadic_interval 0 T\<close> for m
      using mem_dyadic_interval by blast
    moreover have \<open>s \<longlonglongrightarrow> t\<close>
      unfolding s_def using LIMSEQ_ignore_initial_segment floor_pow2_lim by blast
    ultimately show \<open>?thesis\<close>
      using real by blast
  qed
qed

lemma dyadic_interval_dense: \<open>closure (dyadic_interval 0 T) = {0..T}\<close>
proof (rule subset_antisym)
  have \<open>(dyadic_interval 0 T) \<subseteq> {0..T}\<close>
    by (fact dyadic_interval_subset_interval)
  then show \<open>closure (dyadic_interval 0 T) \<subseteq> {0..T}\<close>
    by (auto simp: closure_minimal)
  have \<open>{0..T} \<subseteq> closure (dyadic_interval 0 T)\<close> if \<open>T \<ge> 0\<close>
    unfolding closure_def
  proof -
    {
      fix x assume x: \<open>0 \<le> x\<close> \<open>x \<le> T\<close> \<open>x \<notin> dyadic_interval 0 T\<close>
      then have \<open>x > 0\<close>
        unfolding dyadic_interval_def
        using zero_in_dyadics[OF that] order_le_less by blast
      have \<open>x islimpt (dyadic_interval 0 T)\<close>
        apply (simp add: islimpt_sequential)
        apply (rule exI [where x=\<open>\<lambda>n. \<lfloor>2^n * x\<rfloor> / 2^n\<close>])
        apply safe
        using dyadic_interval_step_mem mem_dyadic_interval x(1,2) apply auto[1]
         apply (smt (verit, ccfv_threshold) dyadic_interval_step_mem mem_dyadic_interval x)
        using floor_pow2_lim apply blast
        done
    }
    thus \<open>{0..T} \<subseteq> dyadic_interval 0 T \<union> {x. x islimpt dyadic_interval 0 T}\<close>
      by force
  qed
  then show \<open>{0..T} \<subseteq> closure (dyadic_interval 0 T)\<close>
    by (cases \<open>T \<ge> 0\<close>; simp)
qed

corollary dyadic_interval_islimpt:
  assumes \<open>T > 0\<close> \<open>t \<in> {0..T}\<close>
  shows \<open>t islimpt dyadic_interval 0 T\<close>
  using assms by (subst limpt_of_closure[symmetric], simp add: dyadic_interval_dense)

corollary at_within_dyadic_interval_nontrivial[simp]:
  assumes \<open>T > 0\<close> \<open>t \<in> {0..T}\<close>
  shows \<open>(at t within dyadic_interval 0 T) \<noteq> bot\<close>
  using assms dyadic_interval_islimpt trivial_limit_within by blast

lemma dyadic_interval_step_finite[simp]: \<open>finite (dyadic_interval_step n S T)\<close>
  unfolding dyadic_interval_step_def by simp

lemma dyadic_interval_countable[simp]: \<open>countable (dyadic_interval S T)\<close>
  by (simp add: dyadic_interval_def dyadic_interval_step_def)

lemma floor_pow2_add_leq:
  fixes T :: \<open>real\<close>
  shows \<open>\<lfloor>2^n * T\<rfloor> / 2 ^ n \<le> \<lfloor>2 ^ (n+k) * T\<rfloor> / 2 ^ (n+k)\<close>
proof (induction \<open>k\<close>)
  case 0
  then show \<open>?case\<close> by simp
next
  case (Suc k)
  let \<open>?f\<close> = \<open>frac (2 ^ (n + k) * T)\<close>
    and \<open>?f'\<close> = \<open>frac (2 ^ (n + (Suc k)) * T)\<close>
  show \<open>?case\<close>
  proof (cases \<open>?f < 1/2\<close>)
    case True
    then have \<open>?f + ?f < 1\<close>
      by auto
    then have \<open>frac ((2 ^ (n + k) * T) + (2 ^ (n + k) * T)) = ?f + ?f\<close>
      using frac_add by meson
    then have \<open>?f' = ?f + ?f\<close>
      by (simp add: field_simps)
    then have \<open>\<lfloor>2 ^ (n + Suc k) * T\<rfloor> / 2 ^ (n + Suc k) = \<lfloor>2^(n + k) * T\<rfloor> / 2 ^ (n + k)\<close>
      by (simp add: frac_def)
    then show \<open>?thesis\<close>
      using Suc by presburger
  next
    case False
    have \<open>?f' = frac (2 ^ (n + k) * T + 2 ^ (n + k) * T)\<close>
      by (simp add: field_simps)
    then have \<open>?f' = 2 * ?f - 1\<close>
      by (smt (verit, del_insts) frac_add False field_sum_of_halves)
    then have \<open>?f' < ?f\<close>
      using frac_lt_1 by auto
    then have \<open>(2 ^ (n + k) * T - ?f) / 2 ^ (n + k) < (2 ^ (n + (Suc k)) * T - ?f') / 2 ^ (n + Suc k)\<close>
      apply (simp add: field_simps)
      by (smt (verit, ccfv_threshold) frac_ge_0)
    then show \<open>?thesis\<close>
      by (smt (verit, ccfv_SIG) Suc frac_def)
  qed
qed

corollary floor_pow2_mono: \<open>mono (\<lambda>n. \<lfloor>2^n * (T :: real)\<rfloor> / 2 ^ n)\<close>
  apply (intro monoI)
  subgoal for x y
    using floor_pow2_add_leq[of \<open>x\<close> \<open>T\<close> \<open>y - x\<close>] by force
  done

lemma dyadic_interval_step_Max: \<open>T \<ge> 0 \<Longrightarrow> Max (dyadic_interval_step n 0 T) = \<lfloor>2^n * T\<rfloor> / 2^n\<close>
  apply (simp add: dyadic_interval_step_def)
  apply (subst mono_Max_commute[of \<open>\<lambda>x. real_of_int x / 2^n\<close>, symmetric])
  by (auto simp: mono_def field_simps Max_eq_iff)

lemma dyadic_interval_step_subset:
  \<open>n \<le> m \<Longrightarrow> dyadic_interval_step n 0 T \<subseteq> dyadic_interval_step m 0 T\<close>
proof (rule subsetI)
  fix x assume \<open>n \<le> m\<close> \<open>x \<in> dyadic_interval_step n 0 T\<close>
  then obtain k where k:  \<open>k \<ge> 0\<close> \<open>k \<le> \<lfloor>2^n * T\<rfloor>\<close> \<open>x = k / 2^n\<close>
    unfolding dyadic_interval_step_def by fastforce
  then have \<open>k * 2 ^ (m - n) \<in> {0 .. \<lfloor>2^m * T\<rfloor>}\<close>
  proof -
    have \<open>k / 2 ^ n \<le> \<lfloor>2^m * T\<rfloor> / 2 ^ m\<close>
      by (smt floor_pow2_mono[THEN monoD, OF \<open>n \<le> m\<close>] k(2) divide_right_mono of_int_le_iff zero_le_power)
    then have \<open>k / 2 ^ n * 2 ^ m \<le> \<lfloor>2^m * T\<rfloor>\<close>
      by (simp add: field_simps)
    moreover have \<open>k / 2 ^ n * 2 ^ m = k * 2 ^ (m - n)\<close>
      apply (simp add: field_simps)
      apply (metis \<open>n \<le> m\<close> add_diff_inverse_nat not_less power_add)
      done
    ultimately have \<open>k * 2 ^ (m - n) \<le> \<lfloor>2^m * T\<rfloor>\<close>
      by linarith
    then show \<open>k * 2 ^ (m - n) \<in> {0 .. \<lfloor>2^m * T\<rfloor>}\<close>
      using k(1) by simp
  qed
  then show \<open>x \<in> dyadic_interval_step m 0 T\<close>
    apply (subst dyadic_interval_step_iff)
    apply (rule exI[where x=\<open>k * 2 ^ (m - n)\<close>])
    apply simp
    apply (simp add: \<open>n \<le> m\<close> k(3) power_diff)
    done
qed

corollary dyadic_interval_step_mono: 
  assumes \<open>x \<in> dyadic_interval_step n 0 T\<close> \<open>n \<le> m\<close>
  shows \<open>x \<in> dyadic_interval_step m 0 T\<close>
  using assms dyadic_interval_step_subset by blast

lemma dyadic_as_natural:
  assumes \<open>x \<in> dyadic_interval_step n 0 T\<close>
  shows \<open>\<exists>!k. x = real k / 2 ^ n\<close>
  using assms
proof (induct \<open>n\<close>)
  case 0
  then show \<open>?case\<close>
    apply simp
    by (metis 0 ceiling_zero div_by_1 dyadic_interval_step_iff mult_not_zero of_nat_eq_iff of_nat_nat power.simps(1))
next
  case (Suc n)
  then show \<open>?case\<close>
    by (auto simp: dyadic_interval_step_iff, metis of_nat_nat)
qed

lemma dyadic_of_natural:
  assumes \<open>real k / 2 ^ n \<le> T\<close>
  shows \<open>real k / 2 ^ n  \<in> dyadic_interval_step n 0 T\<close>
  using assms apply (induct \<open>n\<close>)
   apply simp
   apply (metis atLeastAtMost_iff imageI le_floor_iff of_int_of_nat_eq of_nat_0_le_iff)
  apply (simp add: dyadic_interval_step_iff)
  by (smt (verit, ccfv_SIG) divide_le_eq le_floor_iff mult.commute of_int_of_nat_eq of_nat_0_le_iff zero_less_power)

lemma dyadic_interval_minus:
  assumes \<open>x \<in> dyadic_interval_step n 0 T\<close> \<open>y \<in> dyadic_interval_step n 0 T\<close> \<open>x \<le> y\<close>
  shows \<open>y - x \<in> dyadic_interval_step n 0 T\<close>
proof -
  obtain kx :: \<open>nat\<close> where \<open>x = real kx / 2 ^ n\<close>
    using dyadic_as_natural assms(1) by blast
  obtain ky :: \<open>nat\<close> where \<open>y = real ky / 2 ^ n\<close>
    using dyadic_as_natural assms(2) by blast
  then have \<open>y - x = (ky - kx) / 2^n\<close>
    by (smt (verit, ccfv_SIG) \<open>x = real kx / 2 ^ n\<close> add_diff_inverse_nat add_divide_distrib 
        assms(3) divide_strict_right_mono of_nat_add of_nat_less_iff zero_less_power)
  then show \<open>?thesis\<close>
    using dyadic_of_natural
    by (smt (verit, best) assms(1,2) dyadic_step_geq dyadic_step_leq)
qed

lemma dyadic_times_nat: \<open>x \<in> dyadic_interval_step n 0 T \<Longrightarrow> (x * 2 ^ n) \<in> \<nat>\<close>
  using dyadic_as_natural by fastforce

definition \<open>dyadic_expansion x n b k \<equiv> set b \<subseteq> {0,1}
  \<and> length b = n \<and> x = real_of_int k + (\<Sum>m\<in>{1..n}. real (b ! (m-1)) / 2 ^ m)\<close>

lemma dyadic_expansionI:
  assumes \<open>set b \<subseteq> {0,1}\<close> \<open>length b = n\<close> \<open>x = k + (\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m)\<close>
  shows \<open>dyadic_expansion x n b k\<close>
  unfolding dyadic_expansion_def using assms by blast

lemma dyadic_expansionD:
  assumes \<open>dyadic_expansion x n b k\<close>
  shows \<open>set b \<subseteq> {0,1}\<close>
    and \<open>length b = n\<close>
    and \<open>x = k + (\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m)\<close>
  using assms unfolding dyadic_expansion_def by simp_all

lemma dyadic_expansion_ex:
  assumes \<open>x \<in> dyadic_interval_step n 0 T\<close> 
  shows \<open>\<exists>b k. dyadic_expansion x n b k\<close>
  using assms
proof (induction \<open>n\<close> arbitrary: \<open>x\<close>)
  case 0
  then show \<open>?case\<close>
    unfolding dyadic_expansion_def by force
next
  case (Suc n)
  then obtain k where k: \<open>k \<in> {0..\<lfloor>2 ^ (Suc n) * T\<rfloor>}\<close> \<open>x = k / 2 ^ (Suc n)\<close>
    unfolding dyadic_interval_step_def by fastforce
  then have div2: \<open>k div 2 \<in> {0..\<lfloor>2 ^ n * T\<rfloor>}\<close>
    using k(1) apply simp
    by (metis divide_le_eq_numeral1(1) floor_divide_of_int_eq floor_mono le_floor_iff mult.assoc mult.commute of_int_numeral)
  then show \<open>?case\<close>
  proof (cases \<open>even k\<close>)
    case True
    then have \<open>x = k div 2 / 2 ^ n\<close>
      by (simp add: k(2) real_of_int_div)
    then have \<open>x \<in> dyadic_interval_step n 0 T\<close>
      using dyadic_interval_step_def div2 by force
    then obtain k' b where kb: \<open>dyadic_expansion x n b k'\<close>
      using Suc(1) by blast
    show \<open>?thesis\<close>
      apply (rule exI[where x=\<open>b @ [0]\<close>])
      apply (rule exI[where x=\<open>k'\<close>])
      unfolding dyadic_expansion_def apply safe
      using kb unfolding dyadic_expansion_def apply simp_all
       apply (auto intro!: sum.cong simp: nth_append)
      done
  next
    case False
    then have \<open>k = 2 * (k div 2) + 1\<close>
      by force
    then have \<open>x = k div 2 / 2 ^ n + 1 / 2 ^ (Suc n)\<close>
      by (simp add: k(2) field_simps)
    then have \<open>x - 1 / 2 ^ (Suc n) \<in> dyadic_interval_step n 0 T\<close>
      using div2 by (simp add: dyadic_interval_step_def)
    then obtain k' b where kb: \<open>dyadic_expansion (x-1/2^Suc n) n b k'\<close>
      using Suc(1)[of \<open>x - 1 / 2 ^ (Suc n)\<close>] by blast
    have x: \<open>x = real_of_int k' + (\<Sum>m = 1..n. b ! (m-1) / 2 ^ m) + 1/2^Suc n\<close>
      using dyadic_expansionD(3)[OF kb] by (simp add: field_simps)
    show \<open>?thesis\<close>
      apply (rule exI[where x=\<open>b @ [1]\<close>])
      apply (rule exI[where x=\<open>k'\<close>])
      unfolding dyadic_expansion_def apply safe
      using kb x unfolding dyadic_expansion_def apply simp_all
       apply (auto intro!: sum.cong simp: nth_append)
      done
  qed
qed

lemma dyadic_expansion_frac_le_1: 
  assumes \<open>dyadic_expansion x n b k\<close>
  shows \<open>(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) < 1\<close>
proof -
  have \<open>b ! (m - 1) \<in> {0,1}\<close> if \<open>m \<in> {1..n}\<close> for m
  proof -
    from assms have \<open>set b \<subseteq> {0,1}\<close> \<open>length b = n\<close>
      unfolding dyadic_expansion_def by blast+
    then have \<open>a < n \<Longrightarrow> b ! a \<in> {0,1}\<close> for a
      using nth_mem by blast
    moreover have \<open>m - 1 < n\<close>
      using that by force
    ultimately show \<open>?thesis\<close>
      by blast
  qed
  then have \<open>(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<le> (\<Sum>m\<in>{1..n}. 1 / 2 ^ m)\<close>
    apply (intro sum_mono)
    using assms by fastforce
  also have \<open>... = 1 - 1/2^n\<close>
    by (induct \<open>n\<close>, auto)
  finally show \<open>?thesis\<close>
    by (smt (verit, ccfv_SIG) add_divide_distrib divide_strict_right_mono zero_less_power)
qed

lemma dyadic_expansion_frac_range:
  assumes \<open>dyadic_expansion x n b k\<close> \<open>m \<in> {1..n}\<close>
  shows \<open>b ! (m-1) \<in> {0,1}\<close>
proof -
  have \<open>m - 1 < length b\<close>
    using dyadic_expansionD(2)[OF assms(1)] assms(2) by fastforce
  then show \<open>?thesis\<close>
    using nth_mem dyadic_expansionD(1)[OF assms(1)] by blast
qed

lemma dyadic_expansion_interval:
  assumes \<open>dyadic_expansion x n b k\<close> \<open>x \<in> {S..T}\<close>
  shows \<open>x \<in> dyadic_interval_step n S T\<close>
proof (subst dyadic_interval_step_iff, intro exI, safe)
  define k' where \<open>k' \<equiv> k * 2^n + (\<Sum>i = 1..n. b!(i-1) * 2^(n-i))\<close>
  show \<open>x = k' / 2^n\<close>
    apply (simp add: dyadic_expansionD(3)[OF assms(1)] k'_def add_divide_distrib sum_divide_distrib)
    apply (intro sum.cong, simp)
    apply (simp add: field_simps)
    by (metis add_diff_inverse_nat linorder_not_le power_add)
  then have \<open>k' = \<lfloor>2^n * x\<rfloor>\<close>
    by simp
  then show \<open>k' \<le> \<lfloor>2 ^ n * T\<rfloor>\<close>
    using assms(2) by (auto intro!: floor_mono mult_left_mono)
  from \<open>x = k'/2^n\<close> have \<open>k' = \<lceil>2^n * x\<rceil>\<close>
    by force
  then show \<open>\<lceil>2 ^ n * S\<rceil> \<le> k'\<close>
    using assms(2) by (auto intro!: ceiling_mono mult_left_mono)
qed

lemma dyadic_expansion_nth_geq:
  assumes \<open>dyadic_expansion x n b k\<close> \<open>m \<in> {1..n}\<close> \<open>b ! (m-1) = 1\<close>
  shows \<open>x \<ge> k + 1/2^m\<close>
proof -
  have \<open>(\<Sum> i = 1..n. f i) = f m + (\<Sum> i \<in> ({1..n} - {m}). f i)\<close> for f :: \<open>nat \<Rightarrow> real\<close>
    by (meson assms(2) finite_atLeastAtMost sum.remove)
  with dyadic_expansionD(3)[OF assms(1)] assms(2,3)
  have \<open>x = k + b!(m-1)/2^m + (\<Sum> i \<in> ({1..n} - {m}). b ! (i-1) / 2^i)\<close>
    by simp
  moreover have \<open>(\<Sum> i \<in> ({1..n} - {m}). b ! (i-1) / 2^i) \<ge> 0\<close>
    by (simp add: sum_nonneg)
  ultimately show \<open>?thesis\<close>
    using assms(3) by fastforce
qed

lemma dyadic_expansion_frac_geq_0:
  assumes \<open>dyadic_expansion x n b k\<close>
  shows \<open>(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<ge> 0\<close>
proof -
  have \<open>b ! (m - 1) \<in> {0,1}\<close> if \<open>m \<in> {1..n}\<close> for m
    using dyadic_expansion_frac_range[OF assms] that by blast
  then have \<open>(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<ge> (\<Sum>m\<in>{1..n}. 0)\<close>
    by (intro sum_mono, fastforce)
  then show \<open>?thesis\<close>
    by auto
qed

lemma dyadic_expansion_frac:
  assumes \<open>dyadic_expansion x n b k\<close>
  shows \<open>frac x = (\<Sum>m\<in>{1..n}. (b ! (m-1))/ 2 ^ m)\<close>
  apply (simp add: frac_unique_iff)
  apply safe
  using dyadic_expansionD(3)[OF assms] apply simp
  using dyadic_expansion_frac_geq_0[OF assms] apply simp
  using dyadic_expansion_frac_le_1[OF assms] apply simp
  done

lemma dyadic_expansion_floor:
  assumes \<open>dyadic_expansion x n b k\<close>
  shows \<open>k = \<lfloor>x\<rfloor>\<close>
proof -
  have \<open>x = k + (\<Sum>m\<in>{1..n}. (b ! (m-1))/ 2 ^ m)\<close>
    using assms by (rule dyadic_expansionD(3))
  then have \<open>x = k + frac x\<close>
    using dyadic_expansion_frac[OF assms] by linarith
  then have \<open>k = x - frac x\<close>
    by simp
  then show \<open>k = \<lfloor>x\<rfloor>\<close>
    by (metis floor_of_int frac_floor)
qed

lemma sum_interval_pow2_inv: \<open>(\<Sum>m\<in>{Suc l..n}. (1 :: real) / 2 ^ m) = 1 / 2^l - 1/2^n\<close> if \<open>l < n\<close>
  using that proof (induct \<open>l\<close>)
  case 0
  then show \<open>?case\<close>
    by (induct \<open>n\<close>; fastforce)
next
  case (Suc l)
  have \<open>(\<Sum>m\<in>{Suc l..n} - {Suc l}. (1::real) / 2 ^ m) = (\<Sum>m = Suc l..n. 1 / 2 ^ m) - 1 / 2 ^ Suc l\<close>
    using Suc by (auto simp add: Suc sum_diff1, linarith)
  moreover have \<open>{Suc l..n} - {Suc l} = {Suc (Suc l)..n}\<close> 
    by fastforce
  ultimately have \<open>(\<Sum>m = Suc (Suc l)..n. (1::real) / 2 ^ m) = (\<Sum>m = (Suc l)..n. 1 / 2 ^ m) - 1 / 2^(Suc l)\<close>
    by force
  also have \<open>... = 1 / 2 ^ l - 1 / 2 ^ n - 1 / 2^(Suc l)\<close>
    using Suc by linarith
  also have \<open>... = 1 / 2 ^ Suc l - 1 / 2 ^ n\<close>
    by (simp add: field_simps)
  finally show \<open>?case\<close>
    by blast
qed

lemma dyadic_expansion_unique:
  assumes \<open>dyadic_expansion x n b k\<close>
    and \<open>dyadic_expansion x n c j\<close>
  shows \<open>b = c \<and> (j = k)\<close>
proof (safe, rule ccontr)
  show \<open>j = k\<close>
    using assms dyadic_expansion_floor by blast
  assume \<open>b \<noteq> c\<close>
  have eq: \<open>(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) = (\<Sum>m\<in>{1..n}. (c ! (m-1)) / 2 ^ m)\<close>
  proof -
    have \<open>k + (\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) = j + (\<Sum>m\<in>{1..n}. (c ! (m-1)) / 2 ^ m)\<close>
      using assms dyadic_expansionD(3) by blast
    then show \<open>?thesis\<close>
      using \<open>j = k\<close> by linarith
  qed
  have ex: \<open>\<exists>l < n. b ! l \<noteq> c ! l\<close>
    by (metis list_eq_iff_nth_eq assms \<open>b \<noteq> c\<close> dyadic_expansionD(2))
  text \<open> l is the highest-value bit in the expansion that is not equal \<close>
  define l where \<open>l \<equiv> LEAST l. l < n \<and> b ! l \<noteq> c ! l\<close>
  then have l: \<open>l < n\<close> \<open>b ! l \<noteq> c ! l\<close>
    unfolding l_def using LeastI_ex[OF ex] by blast+
  have less_l: \<open>b ! k = c ! k\<close> if \<open>k < l\<close> for k
  proof -
    have \<open>k < n\<close>
      using that l by linarith
    then show \<open>b ! k = c ! k\<close>
      using that unfolding l_def using not_less_Least by blast
  qed
  then have \<open>l \<in> {0..n-1}\<close>
    using l by simp
  then have \<open>l < n\<close>
    apply (simp add: algebra_simps)
    using ex by fastforce
  then have \<open>b ! l \<in> {0,1}\<close> \<open>c ! l \<in> {0,1}\<close>
    by (metis assms insert_absorb insert_subset dyadic_expansionD(1,2) nth_mem)+
  {
    fix i j :: \<open>nat list\<close>
    fix m :: \<open>int\<close>
    assume i: \<open>i!l = 0\<close> and j: \<open>j!l = 1\<close>
      and dyadic: \<open>dyadic_expansion x n i m\<close>
    text \<open> If the bits do not coincide at l, the sums of bits below l are not equal \<close>
    have \<open>(\<Sum>m\<in>{l+1..n}. (i ! (m-1)) / 2 ^ m) \<noteq> (\<Sum>m\<in>{l+1..n}. (j ! (m-1)) / 2 ^ m)\<close>
    proof (cases \<open>l+1<n\<close>)
      case True
      have \<open>(\<Sum>m\<in>{l+1..n}. (j ! (m-1)) / 2 ^ m) = 
           (j ! ((l+1)-1)) / 2 ^ (l+1) + (\<Sum>m\<in>{Suc (l+1)..n}. (j ! (m-1)) / 2 ^ m)\<close>
        by (smt (verit, ccfv_SIG) Suc_eq_plus1 Suc_le_mono Suc_pred' \<open>l \<in> {0..n - 1}\<close>
            atLeastAtMost_iff bot_nat_0.not_eq_extremum ex order_less_trans sum.atLeast_Suc_atMost)
      also have \<open>... \<ge> 1 / 2 ^ (l+1)\<close>
        apply (simp add: i j)
        apply (rule sum_nonneg)
        using dyadic_expansion_frac_range[OF assms(2)] by simp
      finally have x_ge: \<open>(\<Sum>m\<in>{l+1..n}. (j ! (m-1)) / 2 ^ m) \<ge> 1/2^(l+1)\<close> .
      have \<open>(\<Sum>m\<in>{l+1..n}. (i ! (m-1)) / 2 ^ m) =
            (i ! ((l+1)-1)) / 2 ^ (l+1) + (\<Sum>m\<in>{Suc (l+1)..n}. (i ! (m-1)) / 2 ^ m)\<close>
        by (meson True nat_less_le sum.atLeast_Suc_atMost)
      also have \<open>... = (\<Sum>m\<in>{Suc (l+1)..n}. (i ! (m-1)) / 2 ^ m)\<close>
        using i by auto
      also have \<open>... \<le> (\<Sum>m\<in>{Suc (l+1)..n}. 1 / 2 ^ m)\<close>
        apply (rule sum_mono)
        using dyadic_expansion_frac_range[OF dyadic] apply (simp add: field_simps)
        by (metis Suc_le_D Suc_le_eq le0 zero_less_Suc)
      also have \<open>... < 1 / 2 ^ (l+1)\<close>
        using sum_interval_pow2_inv[OF \<open>l + 1 < n\<close>] by fastforce
      finally have \<open>(\<Sum>m\<in>{l+1..n}. (i ! (m-1)) / 2 ^ m) < 1 / 2 ^ (l+1)\<close> .
      with x_ge show \<open>?thesis\<close>
        by argo
    next
      case False
      then have \<open>l+1 = n\<close>
        using \<open>l < n\<close> by simp
      then show \<open>?thesis\<close>
        using i j by force
    qed
  } note sum_ge_l_noteq_wlog = this
  consider \<open>b!l = 0 \<and> c!l = 1\<close> | \<open>b!l = 1 \<and> c!l = 0\<close>
    using \<open>b ! l \<in> {0, 1}\<close> \<open>c ! l \<in> {0, 1}\<close> l(2) by fastforce
  then have sum_ge_l_noteq: 
    \<open>(\<Sum>m = l + 1..n. real (b ! (m - 1)) / 2 ^ m) \<noteq>
     (\<Sum>m = l + 1..n. real (c ! (m - 1)) / 2 ^ m)\<close>
    apply (cases)
     apply (rule sum_ge_l_noteq_wlog; simp)
    using assms(1) apply blast
    apply (rule sum_ge_l_noteq_wlog[symmetric])
    using assms apply simp_all
    done
  moreover have sum_upto_l_eq: \<open>(\<Sum>m\<in>{1..l}. (b ! (m-1)) / 2 ^ m) =
                                (\<Sum>m\<in>{1..l}. (c ! (m-1)) / 2 ^ m)\<close>
    apply (safe intro!: sum.cong)
    apply simp
    by (smt (verit, best) Suc_le_eq Suc_pred \<open>l < n\<close> l_def not_less_Least order_less_trans)
  ultimately have \<open>(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<noteq> (\<Sum>m\<in>{1..n}. (c ! (m-1)) / 2 ^ m)\<close>
  proof -
    have \<open>{1..n} = {1..l} \<union> {l<..n}\<close>
      using \<open>l < n\<close> by auto
    moreover have \<open>{1..l} \<inter> {l<..n} = {}\<close>
      using ivl_disj_int_two(8) by blast
    ultimately have split_sum: \<open>(\<Sum>m \<in>{1..n}. (h ! (m-1)) / 2 ^ m) =
                 (\<Sum>m =1..l. (h ! (m-1)) / 2 ^ m) + (\<Sum>m \<in> {l<..n}. (h ! (m-1)) / 2 ^ m)\<close>
      for h :: \<open>nat list\<close>
      by (simp add: sum_Un)
    then show \<open>?thesis\<close>
      apply simp
      by (metis (no_types, lifting)  sum_upto_l_eq sum_ge_l_noteq One_nat_def Suc_eq_plus1
          add_left_imp_eq atLeastSucAtMost_greaterThanAtMost sum.cong)
  qed
  then show \<open>False\<close>
    using eq by blast
qed

end
