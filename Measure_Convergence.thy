(* Title:      Kolmogorov_Chentsov/Measure_Convergence.thy
   Author:     Christian Pardillo Laursen, University of York
*)

section "Convergence in measure"

theory Measure_Convergence
  imports "HOL-Probability.Probability"
begin

text \<open> We use measure rather than emeasure because ennreal is not a metric space, which we need to
  reason about convergence. By intersecting with the set of finite measure A, we don't run into issues
  where infinity is collapsed to 0.

  For finite measures this definition is equal to the definition without set A -- see below. \<close>

definition tendsto_measure :: \<open>'b measure \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('c :: {second_countable_topology,metric_space}))
   \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a filter \<Rightarrow> bool\<close>
  where \<open>tendsto_measure M X l F \<equiv> (\<forall>n. X n \<in> borel_measurable M) \<and> l \<in> borel_measurable M \<and>
  (\<forall>\<epsilon> > 0. \<forall>A \<in> fmeasurable M.
  ((\<lambda>n. measure M ({\<omega> \<in> space M. dist (X n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A)) \<longlongrightarrow> 0) F)\<close>

abbreviation (in prob_space) tendsto_prob  (infixr \<open>\<longlongrightarrow>\<^sub>P\<close> 55) where
  \<open>(f \<longlongrightarrow>\<^sub>P l) F \<equiv> tendsto_measure M f l F\<close>

lemma tendsto_measure_measurable[measurable_dest]:
  \<open>tendsto_measure M X l F \<Longrightarrow> X n \<in> borel_measurable M\<close>
  unfolding tendsto_measure_def by meson

lemma tendsto_measure_measurable_lim[measurable_dest]:
  \<open>tendsto_measure M X l F \<Longrightarrow> l \<in> borel_measurable M\<close>
  unfolding tendsto_measure_def by meson

lemma tendsto_measure_mono: \<open>F \<le> F' \<Longrightarrow> tendsto_measure M f l F' \<Longrightarrow> tendsto_measure M f l F\<close>
  unfolding tendsto_measure_def by (simp add: tendsto_mono)

lemma tendsto_measureI:
  assumes [measurable]: \<open>\<And>n. X n \<in> borel_measurable M\<close> \<open>l \<in> borel_measurable M\<close>
    and \<open>\<And>\<epsilon> A. \<epsilon> > 0 \<Longrightarrow> A \<in> fmeasurable M \<Longrightarrow>
    ((\<lambda>n. measure M ({\<omega> \<in> space M. dist (X n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A)) \<longlongrightarrow> 0) F\<close>
  shows \<open>tendsto_measure M X l F\<close>
  unfolding tendsto_measure_def using assms by fast

lemma (in finite_measure) finite_tendsto_measureI:
  assumes [measurable]: \<open>\<And>n. f' n \<in> borel_measurable M\<close> \<open>f \<in> borel_measurable M\<close>
    and \<open>\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> ((\<lambda>n. measure M {\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) > \<epsilon>}) \<longlongrightarrow> 0) F\<close>
  shows \<open>tendsto_measure M f' f F\<close>
proof (intro tendsto_measureI)
  fix \<epsilon> :: \<open>real\<close> assume \<open>\<epsilon> > 0\<close>
  then have prob_conv: \<open>((\<lambda>n. measure M {\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)}) \<longlongrightarrow> 0) F\<close>
    using assms by simp
  fix A assume \<open>A \<in> fmeasurable M\<close>
  have \<open>\<And>n. measure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)}) \<ge> 
            measure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A)\<close>
    by (rule finite_measure_mono; measurable)
  then show \<open>((\<lambda>n. measure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A)) \<longlongrightarrow> 0) F\<close>
    by (simp add: tendsto_0_le[OF prob_conv, where K=\<open>1\<close>])
qed measurable

lemma (in finite_measure) finite_tendsto_measureD:
  assumes [measurable]: \<open>tendsto_measure M f' f F\<close>
  shows \<open>(\<forall>\<epsilon> > 0. ((\<lambda>n. measure M {\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) > \<epsilon>}) \<longlongrightarrow> 0) F)\<close>
proof -
  from assms have \<open>((\<lambda>n. measure M ({\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) > \<epsilon>} \<inter> space M)) \<longlongrightarrow> 0) F\<close>
    if \<open>\<epsilon> > 0\<close> for \<epsilon>
    unfolding tendsto_measure_def using that fmeasurable_eq_sets by blast
  then show \<open>?thesis\<close>
    by (simp add: sets.Int_space_eq2[symmetric, where M=\<open>M\<close>])
qed

lemma (in finite_measure) tendsto_measure_leq:
  assumes [measurable]: \<open>\<And>n. f' n \<in> borel_measurable M\<close> \<open>f \<in> borel_measurable M\<close>
  shows \<open>tendsto_measure M f' f F \<longleftrightarrow>
   (\<forall>\<epsilon> > 0. ((\<lambda>n. measure M {\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) \<ge> \<epsilon>}) \<longlongrightarrow> 0) F)\<close> (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof (rule iffI, goal_cases)
  case 1
  {
    fix \<epsilon> :: \<open>real\<close> assume \<open>\<epsilon> > 0\<close>
    then have \<open>((\<lambda>n. measure M {\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) > \<epsilon>/2}) \<longlongrightarrow> 0) F\<close>
      using finite_tendsto_measureD[OF 1] half_gt_zero by blast
    then have \<open>((\<lambda>n. measure M {\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) \<ge> \<epsilon>}) \<longlongrightarrow> 0) F\<close>
      apply (rule metric_tendsto_imp_tendsto)
      using \<open>\<epsilon> > 0\<close> by (auto intro!: eventuallyI finite_measure_mono)
  }
  then show \<open>?case\<close>
    by simp
next
  case 2
  {
    fix \<epsilon> :: \<open>real\<close> assume \<open>\<epsilon> > 0\<close>
    then have *: \<open>((\<lambda>n. \<P>(\<omega> in M. \<epsilon> \<le> dist (f' n \<omega>) (f \<omega>))) \<longlongrightarrow> 0) F\<close>
      using 2 by blast
    then have \<open>((\<lambda>n. \<P>(\<omega> in M. \<epsilon> < dist (f' n \<omega>) (f \<omega>))) \<longlongrightarrow> 0) F\<close>
      apply (rule metric_tendsto_imp_tendsto)
      using \<open>\<epsilon> > 0\<close> by (auto intro!: eventuallyI finite_measure_mono)
  }
  then show \<open>?case\<close>
    by (simp add: finite_tendsto_measureI[OF assms])
qed

abbreviation \<open>LIMSEQ_measure M f l \<equiv> tendsto_measure M f l sequentially\<close>

lemma LIMSEQ_measure_def: \<open>LIMSEQ_measure M f l \<longleftrightarrow>
  (\<forall>n. f n \<in> borel_measurable M) \<and> (l \<in> borel_measurable M) \<and>
   (\<forall>\<epsilon> > 0. \<forall>A \<in> fmeasurable M.
   (\<lambda>n. measure M ({\<omega> \<in> space M. dist (f n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A)) \<longlonglongrightarrow> 0)\<close>
  unfolding tendsto_measure_def ..

lemma LIMSEQ_measureD:
  assumes \<open>LIMSEQ_measure M f l\<close> \<open>\<epsilon> > 0\<close> \<open>A \<in> fmeasurable M\<close>
  shows \<open>(\<lambda>n. measure M ({\<omega> \<in> space M. dist (f n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A)) \<longlonglongrightarrow> 0\<close>
  using assms LIMSEQ_measure_def by blast

lemma fmeasurable_inter: \<open>\<lbrakk>A \<in> sets M; B \<in> fmeasurable M\<rbrakk> \<Longrightarrow> A \<inter> B \<in> fmeasurable M\<close>
proof (intro fmeasurableI, goal_cases measurable finite)
  case measurable
  then show \<open>?case\<close> by simp
next
  case finite
  then have \<open>emeasure M (A \<inter> B) \<le> emeasure M B\<close>
    by (simp add: emeasure_mono)
  also have \<open>emeasure M B < \<infinity>\<close>
    using finite(2)[THEN fmeasurableD2] by (simp add: top.not_eq_extremum)
  finally show \<open>?case\<close> .
qed

lemma LIMSEQ_measure_emeasure:
  assumes \<open>LIMSEQ_measure M f l\<close> \<open>\<epsilon> > 0\<close> \<open>A \<in> fmeasurable M\<close>
    and [measurable]: \<open>\<And>i. f i \<in> borel_measurable M\<close> \<open>l \<in> borel_measurable M\<close> 
  shows \<open>(\<lambda>n. emeasure M ({\<omega> \<in> space M. dist (f n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A)) \<longlonglongrightarrow> 0\<close>
proof -
  have fmeasurable: \<open>{\<omega> \<in> space M. dist (f n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A \<in> fmeasurable M\<close> for n
    by (rule fmeasurable_inter; simp add: assms(3))
  then show \<open>?thesis\<close>
    apply (simp add: emeasure_eq_measure2 ennreal_tendsto_0_iff)
    using LIMSEQ_measure_def assms by blast
qed

lemma measure_Lim_within_LIMSEQ:
  fixes a :: \<open>'a :: first_countable_topology\<close>
  assumes \<open>\<And>t. X t \<in> borel_measurable M\<close> \<open>L \<in> borel_measurable M\<close>
  assumes \<open>\<And>S. \<lbrakk>(\<forall>n. S n \<noteq> a \<and> S n \<in> T); S \<longlonglongrightarrow> a\<rbrakk> \<Longrightarrow> LIMSEQ_measure M (\<lambda>n. X (S n)) L\<close>
  shows \<open>tendsto_measure M X L (at a within T)\<close>
  apply (intro tendsto_measureI[OF assms(1,2)])
  unfolding tendsto_measure_def[where l=\<open>L\<close>] tendsto_def apply safe
  apply (rule sequentially_imp_eventually_within)
  using assms unfolding LIMSEQ_measure_def tendsto_def by presburger

definition tendsto_AE :: \<open>'b measure \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c :: topological_space) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a filter \<Rightarrow> bool\<close> where
  \<open>tendsto_AE M f' l F \<longleftrightarrow> (AE \<omega> in M. ((\<lambda>n. f' n \<omega>) \<longlongrightarrow> l \<omega>) F)\<close>

lemma LIMSEQ_ae_pointwise: \<open>(\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> l x) \<Longrightarrow> tendsto_AE M f l sequentially\<close>
  unfolding tendsto_AE_def by simp

lemma tendsto_AE_within_LIMSEQ:
  fixes a :: \<open>'a :: first_countable_topology\<close>
  assumes \<open>\<And>S. \<lbrakk>(\<forall>n. S n \<noteq> a \<and> S n \<in> T); S \<longlonglongrightarrow> a\<rbrakk> \<Longrightarrow> tendsto_AE M (\<lambda>n. X (S n)) L sequentially\<close>
  shows \<open>tendsto_AE M X L (at a within T)\<close>
  oops

lemma LIMSEQ_dominated_convergence:
  fixes X :: \<open>nat \<Rightarrow> real\<close>
  assumes \<open>X \<longlonglongrightarrow> L\<close> \<open>(\<And>n. Y n \<le> X n)\<close> \<open>(\<And>n. Y n \<ge> L)\<close>
  shows \<open>Y \<longlonglongrightarrow> L\<close>
proof (rule metric_LIMSEQ_I)
  have \<open>X n \<ge> L\<close> for n
    using assms(2,3)[of \<open>n\<close>] by linarith
  fix r :: \<open>real\<close> assume \<open>0 < r\<close>
  then obtain N where \<open>\<forall>n\<ge>N. dist (X n) L < r\<close>
    using metric_LIMSEQ_D[OF assms(1) \<open>0 < r\<close>]  by blast
  then have N: \<open>\<forall>n\<ge>N. X n - L < r\<close>
    using \<open>\<And>n. L \<le> X n\<close> by (auto simp: dist_real_def)
  have \<open>\<forall>n\<ge>N. Y n - L < r\<close>
  proof clarify
    fix n assume \<open>n \<ge> N\<close>
    then have \<open>X n - L < r\<close>
      using N by blast
    then show \<open>Y n - L < r\<close>
      using assms(2)[of \<open>n\<close>] by auto
  qed
  then show \<open>\<exists>no. \<forall>n\<ge>no. dist (Y n) L < r\<close>
    apply (intro exI[where x=\<open>N\<close>])
    using assms(3) dist_real_def by auto
qed

text \<open> Klenke remark 6.4 \<close>
lemma measure_conv_imp_AE_sequentially: 
  assumes [measurable]: \<open>\<And>n. f' n \<in> borel_measurable M\<close> \<open>f \<in> borel_measurable M\<close>
    and \<open>tendsto_AE M f' f sequentially\<close>
  shows \<open>LIMSEQ_measure M f' f\<close>
proof (unfold tendsto_measure_def, safe)
  fix \<epsilon> :: \<open>real\<close> assume \<open>0 < \<epsilon>\<close>
  fix A assume A[measurable]: \<open>A \<in> fmeasurable M\<close>
  text \<open> From AE convergence we know there's a null set where f' doesn't converge \<close>
  obtain N where N: \<open>N \<in> null_sets M\<close> \<open>{\<omega> \<in> space M. \<not> (\<lambda>n. f' n \<omega>) \<longlonglongrightarrow> f \<omega>} \<subseteq> N\<close>
    using assms unfolding tendsto_AE_def by (simp add: eventually_ae_filter, blast)
  then have measure_0: \<open>measure M {\<omega> \<in> space M. \<not> (\<lambda>n. f' n \<omega>) \<longlonglongrightarrow> f \<omega>} = 0\<close>
    by (meson measure_eq_0_null_sets measure_notin_sets null_sets_subset)
  text \<open> D is a sequence of sets that converges to N \<close>
  define D where \<open>D \<equiv> \<lambda>n. {\<omega> \<in> space M. \<exists>m \<ge> n. dist (f' m \<omega>) (f \<omega>) > \<epsilon>}\<close>
  have \<open>\<And>n. D n \<in> sets M\<close>
    unfolding D_def by measurable
  then have [measurable]: \<open>\<And>n. D n \<inter> A \<in> sets M\<close>
    by simp
  have \<open>(\<Inter>n. D n) \<in> sets M\<close>
    unfolding D_def by measurable
  then have measurable_D_A: \<open>(\<Inter>n. D n \<inter> A) \<in> sets M\<close>
    by simp
  have \<open>(\<Inter>n. D n) \<subseteq> {\<omega> \<in> space M. \<not> (\<lambda>n. (f' n \<omega>)) \<longlonglongrightarrow> f \<omega>}\<close>
  proof (intro subsetI)
    fix x assume \<open>x \<in> (\<Inter>n. D n)\<close>
    then have \<open>x \<in> space M\<close> \<open>\<And>n. \<exists>m \<ge> n. \<epsilon> < dist (f' m x) (f x)\<close>
      unfolding D_def by simp_all
    then have \<open>\<not> (\<lambda>n. f' n x) \<longlonglongrightarrow> f x\<close>
      by (simp add: LIMSEQ_def) (meson \<open>0 < \<epsilon>\<close> not_less_iff_gr_or_eq order_less_le)
    then show \<open>x \<in> {\<omega> \<in> space M. \<not> (\<lambda>n. f' n \<omega>) \<longlonglongrightarrow> f \<omega>}\<close>
      using \<open>x \<in> space M\<close> by blast
  qed
  then have \<open>measure M (\<Inter>n. D n) = 0\<close>
    by (metis (no_types, lifting) N \<open>\<Inter> (range D) \<in> sets M\<close> measure_eq_0_null_sets null_sets_subset subset_trans)
  then have \<open>measure M (\<Inter>n. D n \<inter> A) = 0\<close>
  proof -
    have \<open>emeasure M (\<Inter>n. D n \<inter> A) \<le> emeasure M (\<Inter>n. D n)\<close>
      apply (rule emeasure_mono)
       apply blast
      unfolding D_def apply measurable
      done
    then show \<open>?thesis\<close>
      by (smt (verit, del_insts) N Sigma_Algebra.measure_def \<open>measure M (\<Inter> (range D)) = 0\<close>
          \<open>\<Inter> (range D) \<in> sets M\<close> \<open>\<Inter> (range D) \<subseteq> {\<omega> \<in> space M. \<not> (\<lambda>n. f' n \<omega>) \<longlonglongrightarrow> f \<omega>}\<close> 
          dual_order.trans enn2real_mono ennreal_zero_less_top measure_nonneg null_setsD1 null_sets_subset)
  qed
  moreover have \<open>(\<lambda>n. measure M (D n \<inter> A)) \<longlonglongrightarrow> measure M (\<Inter>n. D n \<inter> A)\<close>
    apply (rule Lim_measure_decseq)
    using A(1) \<open>\<And>n. D n \<in> sets M\<close> apply blast
    subgoal 
      apply (intro monotoneI) 
      apply clarsimp
      apply (simp add: D_def) 
      by (meson order_trans)
    apply (simp add: A \<open>\<And>n. D n \<in> sets M\<close> fmeasurableD2 fmeasurable_inter)
    done
  ultimately have measure_D_0: \<open>(\<lambda>n. measure M (D n \<inter> A)) \<longlonglongrightarrow> 0\<close>
    by presburger
  have \<open>\<And>n. {\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A \<subseteq> (D n \<inter> A)\<close>
    unfolding D_def by blast
  then have \<open>\<And>n. emeasure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A) \<le> emeasure M (D n \<inter> A)\<close>
    by (rule emeasure_mono) measurable
  then have \<open>\<And>n. measure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A) \<le> measure M (D n \<inter> A)\<close>
    unfolding measure_def apply (rule enn2real_mono)
    by (meson A \<open>\<And>n. D n \<in> sets M\<close> fmeasurableD2 fmeasurable_inter top.not_eq_extremum)
  then show \<open>(\<lambda>n. measure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A)) \<longlonglongrightarrow> 0\<close>
    by (simp add: LIMSEQ_dominated_convergence[OF measure_D_0])
qed simp_all

corollary LIMSEQ_measure_pointwise:
  assumes \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> f' x\<close> \<open>\<And>n. f n \<in> borel_measurable M\<close> \<open>f' \<in> borel_measurable M\<close>
  shows \<open>LIMSEQ_measure M f f'\<close>
  by (simp add: LIMSEQ_ae_pointwise measure_conv_imp_AE_sequentially assms)

lemma Lim_measure_pointwise:
  fixes a :: \<open>'a :: first_countable_topology\<close>
  assumes \<open>\<And>x. ((\<lambda>n. f n x) \<longlongrightarrow> f' x)(at a within T)\<close> \<open>\<And>n. f n \<in> borel_measurable M\<close> \<open>f' \<in> borel_measurable M\<close>
  shows \<open>tendsto_measure M f f' (at a within T)\<close>
proof (intro measure_Lim_within_LIMSEQ)
  fix S assume \<open>\<forall>n. S n \<noteq> a \<and> S n \<in> T\<close> \<open>S \<longlonglongrightarrow> a\<close>
  then have \<open>(\<lambda>n. f (S n) x) \<longlonglongrightarrow> f' x\<close> for x
    using assms(1) by (simp add: tendsto_at_iff_sequentially o_def)
  then show \<open>LIMSEQ_measure M (\<lambda>n. f (S n)) f'\<close>
    by (simp add: LIMSEQ_measure_pointwise assms(2,3))
qed (simp_all add: assms)

corollary measure_conv_imp_AE_at_within:
  fixes x :: \<open>'a :: first_countable_topology\<close>
  assumes [measurable]: \<open>\<And>n. f' n \<in> borel_measurable M\<close> \<open>f \<in> borel_measurable M\<close>
    and \<open>tendsto_AE M f' f (at x within S)\<close>
  shows \<open>tendsto_measure M f' f (at x within S)\<close>
proof (rule measure_Lim_within_LIMSEQ[OF assms(1,2)])
  fix s assume *: \<open>\<forall>n. s n \<noteq> x \<and> s n \<in> S\<close> \<open>s \<longlonglongrightarrow> x\<close>
  have AE_seq: \<open>AE \<omega> in M. \<forall>X. (\<forall>i. X i \<in> S - {x}) \<longrightarrow> X \<longlonglongrightarrow> x \<longrightarrow> ((\<lambda>n. f' n \<omega>) \<circ> X) \<longlonglongrightarrow> f \<omega>\<close>
    using assms(3) by (simp add: tendsto_AE_def tendsto_at_iff_sequentially)
  then have \<open>AE \<omega> in M. (\<forall>i. s i \<in> S - {x}) \<longrightarrow> s \<longlonglongrightarrow> x \<longrightarrow> ((\<lambda>n. f' n \<omega>) \<circ> s) \<longlonglongrightarrow> f \<omega>\<close>
    by force
  then have \<open>AE \<omega> in M. ((\<lambda>n. f' n \<omega>) \<circ> s) \<longlonglongrightarrow> f \<omega>\<close>
    using * by force
  then have \<open>tendsto_AE M (\<lambda>n. f' (s n)) f sequentially\<close>
    unfolding tendsto_AE_def comp_def by blast
  then show \<open>LIMSEQ_measure M (\<lambda>n. f' (s n)) f\<close>
    by (rule measure_conv_imp_AE_sequentially[OF assms(1,2)])
qed

text \<open> Klenke remark 6.5 \<close>
lemma (in sigma_finite_measure) LIMSEQ_measure_unique_AE:
  fixes f :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology,metric_space}\<close>
  assumes [measurable]: \<open>\<And>n. f n \<in> borel_measurable M\<close> \<open>l \<in> borel_measurable M\<close> \<open>l' \<in> borel_measurable M\<close>
    and \<open>LIMSEQ_measure M f l\<close> \<open>LIMSEQ_measure M f l'\<close>
  shows \<open>AE x in M. l x = l' x\<close>
proof -
  obtain A :: \<open>nat \<Rightarrow> 'a set\<close> where A: \<open>\<And>i. A i \<in> fmeasurable M\<close> \<open>(\<Union>i. A i) = space M\<close>
    by (metis fmeasurableI infinity_ennreal_def rangeI sigma_finite subset_eq top.not_eq_extremum)
  have \<open>\<And>m \<epsilon>. {x \<in> space M. dist (l x) (l' x) > \<epsilon>} \<inter> A m \<in> fmeasurable M\<close>
    by (intro fmeasurable_inter; simp add: A)
  then have emeasure_leq: \<open>emeasure M ({x \<in> space M. dist (l x) (l' x) > \<epsilon>} \<inter> A m) \<le>
     emeasure M ({x \<in> space M. dist (l x) (f n x) > \<epsilon>/2} \<inter> A m) +
     emeasure M ({x \<in> space M. dist (f n x) (l' x) > \<epsilon>/2} \<inter> A m)\<close> if \<open>\<epsilon> > 0\<close> for n m \<epsilon>
  proof -
    have [measurable]:
      \<open>{x \<in> space M. \<epsilon> / 2 < dist (l x) (f n x)} \<inter> A m \<in> sets M\<close>
      \<open>{x \<in> space M. \<epsilon> / 2 < dist (f n x) (l' x)} \<inter> A m \<in> sets M\<close>
      using A by (measurable; auto)+
    have \<open>dist (l x) (l' x) \<le> dist (l x) (f n x) + dist (f n x) (l' x)\<close> for x
      by (simp add: dist_triangle)
    then have \<open>{x. dist (l x) (l' x) > \<epsilon>} \<subseteq> {x. dist (l x) (f n x) > \<epsilon>/2} \<union> {x. dist (f n x) (l' x) > \<epsilon>/2}\<close>
      by (safe, smt (verit, best) field_sum_of_halves)
    then have \<open>{x \<in> space M. dist (l x) (l' x) > \<epsilon>} \<inter> A m \<subseteq> 
    ({x \<in> space M. dist (l x) (f n x) > \<epsilon>/2} \<inter> A m) \<union> ({x \<in> space M. dist (f n x) (l' x) > \<epsilon>/2} \<inter> A m)\<close>
      by blast
    then have \<open>emeasure M ({x \<in> space M. dist (l x) (l' x) > \<epsilon>} \<inter> A m) \<le>
     emeasure M ({x \<in> space M. dist (l x) (f n x) > \<epsilon>/2} \<inter> A m \<union> {x \<in> space M. dist (f n x) (l' x) > \<epsilon>/2} \<inter> A m)\<close>
      apply (rule emeasure_mono)
      using A by measurable
    also have \<open>... \<le> emeasure M ({x \<in> space M. dist (l x) (f n x) > \<epsilon>/2} \<inter> A m) +
     emeasure M ({x \<in> space M. dist (f n x) (l' x) > \<epsilon>/2} \<inter> A m)\<close>
      apply (rule emeasure_subadditive)
      using A by measurable
    finally show \<open>?thesis\<close> .
  qed

  moreover have tendsto_zero: \<open>(\<lambda>n. emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l x)} \<inter> A m)
       + emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l' x)} \<inter> A m)) \<longlonglongrightarrow> 0\<close>
    if \<open>\<epsilon> > 0\<close> for \<epsilon> m
    apply (rule tendsto_add_zero)
     apply (rule LIMSEQ_measure_emeasure[OF assms(4)])
        prefer 5 apply (rule LIMSEQ_measure_emeasure[OF assms(5)])
    using that A apply simp_all
    done
  have dist_\<epsilon>_emeasure: \<open>emeasure M ({x \<in> space M. \<epsilon> < dist (l x) (l' x)} \<inter> A m) = 0\<close> 
    if \<open>\<epsilon> > 0\<close> for \<epsilon> m
  proof (rule ccontr)
    assume \<open>emeasure M ({x \<in> space M. \<epsilon> < dist (l x) (l' x)} \<inter> A m) \<noteq> 0\<close>
    then obtain e where e: \<open>e > 0\<close> \<open>emeasure M ({x \<in> space M. \<epsilon> < dist (l x) (l' x)} \<inter> A m) \<ge> e\<close>
      using not_gr_zero by blast
    have \<open>\<exists>no. \<forall>n\<ge>no. (emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l x)} \<inter> A m)
       + emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l' x)} \<inter> A m)) < e\<close>
    proof -
      have measure_tendsto_0: \<open>(\<lambda>n. measure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l x)} \<inter> A m)
       + measure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l' x)} \<inter> A m)) \<longlonglongrightarrow> 0\<close>
        apply (rule tendsto_add_zero)
        using A(1) LIMSEQ_measure_def assms(4,5) half_gt_zero that by blast+
      have \<open>enn2real e > 0\<close>
        by (metis (no_types, lifting) A(1) e(1) e(2) emeasure_neq_0_sets enn2real_eq_0_iff 
            enn2real_nonneg fmeasurableD2 fmeasurable_inter inf_right_idem linorder_not_less nless_le top.not_eq_extremum)
      then obtain no where \<open>\<forall>n\<ge>no. (measure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l x)} \<inter> A m)
       + measure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l' x)} \<inter> A m)) < enn2real e\<close>
        using LIMSEQ_D[OF measure_tendsto_0 \<open>enn2real e > 0\<close>] by (simp) blast
      then show \<open>?thesis\<close>
        apply (safe intro!: exI[where x=\<open>no\<close>])
        by (smt (verit, del_insts) A(1) Sigma_Algebra.measure_def add_eq_0_iff_both_eq_0 
            emeasure_eq_measure2 emeasure_neq_0_sets enn2real_mono enn2real_plus enn2real_top 
            ennreal_0 ennreal_zero_less_top fmeasurable_inter inf_sup_ord(2) le_iff_inf
            linorder_not_less top.not_eq_extremum zero_less_measure_iff)
    qed
    then obtain N where N: \<open>emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f N x) (l x)} \<inter> A m)
       + emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f N x) (l' x)} \<inter> A m) < e\<close>
      by auto
    then have \<open>emeasure M ({x \<in> space M. \<epsilon> < dist (l x) (l' x)} \<inter> A m) < e\<close>
      by (smt (verit, del_insts) emeasure_leq[OF that] Collect_cong dist_commute e(2) leD order_less_le_trans)
    then show \<open>False\<close>
      using e(2) by auto
  qed
  have \<open>emeasure M ({x \<in> space M. 0 < dist (l x) (l' x)} \<inter> A m) = 0\<close> for m
  proof -
    have sets: \<open>range (\<lambda>n. {x \<in> space M. 1/2^n < dist (l x) (l' x)} \<inter> A m) \<subseteq> sets M\<close>
      using A by force
    have \<open>(\<Union>n. {x \<in> space M. 1/2^n < dist (l x) (l' x)}) = {x \<in> space M. 0 < dist (l x) (l' x)}\<close>
      apply (intro subset_antisym subsetI)
       apply force
      apply simp
      by (metis one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76) zero_less_dist_iff)
    moreover have \<open>emeasure M ({x \<in> space M. 1/2^n < dist (l x) (l' x)} \<inter> A m) = 0\<close> for n
      using dist_\<epsilon>_emeasure by simp
    then have suminf_zero: \<open>(\<Sum>n. emeasure M ({x \<in> space M. 1/2^n < dist (l x) (l' x)} \<inter> A m)) = 0\<close>
      by auto
    then have \<open>emeasure M (\<Union>n. ({x \<in> space M. 1/2^n < dist (l x) (l' x)} \<inter> A m)) \<le> 0\<close>
      apply (subst suminf_zero[symmetric])
      apply (rule emeasure_subadditive_countably)
      by (simp add: emeasure_subadditive_countably sets)
    ultimately show \<open>?thesis\<close>
      by simp
  qed
  then have \<open>(\<Sum>m. emeasure M ({x \<in> space M. 0 < dist (l x) (l' x)} \<inter> A m)) = 0\<close>
    by simp
  then have \<open>emeasure M (\<Union>m. {x \<in> space M. 0 < dist (l x) (l' x)} \<inter> A m) = 0\<close>
  proof -
    let \<open>?S\<close> = \<open>\<lambda>m. {x \<in> space M. 0 < dist (l x) (l' x)} \<inter> A m\<close>
    have \<open>emeasure M (\<Union>m. ?S m) \<le> (\<Sum>m. emeasure M (?S m))\<close>
      apply (rule emeasure_subadditive_countably)
      using \<open>\<And>m \<epsilon>. {x \<in> space M. \<epsilon> < dist (l x) (l' x)} \<inter> A m \<in> fmeasurable M\<close> by blast
    then show \<open>?thesis\<close>
      using \<open>(\<Sum>m. emeasure M (?S m)) = 0\<close> by force
  qed
  then have \<open>emeasure M {x \<in> space M. 0 < dist (l x) (l' x)} = 0\<close>
    using A by simp
  then show \<open>?thesis\<close>
    by (auto simp add: AE_iff_null)
qed

corollary (in sigma_finite_measure) LIMSEQ_ae_unique_AE:
  fixes f :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology,metric_space}\<close>
  assumes \<open>\<And>n. f n \<in> borel_measurable M\<close> \<open>l \<in> borel_measurable M\<close> \<open>l' \<in> borel_measurable M\<close>
    and \<open>tendsto_AE M f l sequentially\<close> \<open>tendsto_AE M f l' sequentially\<close>
  shows \<open>AE x in M. l x = l' x\<close>
proof -
  have \<open>LIMSEQ_measure M f l\<close> \<open>LIMSEQ_measure M f l'\<close>
    using assms measure_conv_imp_AE_sequentially by blast+
  then show \<open>?thesis\<close>
    using assms(1-3) LIMSEQ_measure_unique_AE by blast
qed

lemma (in sigma_finite_measure) tendsto_measure_at_within_eq_AE:
  fixes f :: \<open>'b :: first_countable_topology \<Rightarrow> 'a \<Rightarrow> 'c :: {second_countable_topology,metric_space}\<close>
  assumes f_measurable: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<in> borel_measurable M\<close>
    and l_measurable: \<open>l \<in> borel_measurable M\<close> \<open>l' \<in> borel_measurable M\<close>
    and tendsto: \<open>tendsto_measure M f l (at t within S)\<close> \<open>tendsto_measure M f l' (at t within S)\<close>
    and not_bot: \<open>(at t within S) \<noteq> \<bottom>\<close>
  shows \<open>AE x in M. l x = l' x\<close>
proof -
  from not_bot have \<open>t islimpt S\<close>
    using trivial_limit_within by blast
  then obtain s :: \<open>nat \<Rightarrow> 'b\<close> where s: \<open>\<And>i. s i \<in> S - {t}\<close> \<open>s \<longlonglongrightarrow> t\<close>
    using islimpt_sequential by meson
  then have fs_measurable: \<open>\<And>n. f (s n) \<in> borel_measurable M\<close>
    using f_measurable by blast
  have *: \<open>LIMSEQ_measure M (\<lambda>n. f (s n)) l\<close>
    if \<open>l \<in> borel_measurable M\<close> \<open>tendsto_measure M f l (at t within S)\<close> for l
  proof (intro tendsto_measureI[OF fs_measurable that(1)], goal_cases)
    case (1 \<epsilon> A)
    then have \<open>((\<lambda>n. measure M ({\<omega> \<in> space M. \<epsilon> < dist (f n \<omega>) (l \<omega>)} \<inter> A)) \<longlongrightarrow> 0)(at t within S)\<close>
      using that(2) 1 tendsto_measure_def by blast
    then show \<open>?case\<close>
      apply (rule filterlim_compose[where f=\<open>s\<close>])
      by (smt (verit, del_insts) DiffD1 DiffD2 eventuallyI filterlim_at insertI1 s)
  qed
  show \<open>?thesis\<close>
    apply (rule LIMSEQ_measure_unique_AE[OF fs_measurable l_measurable])
    using * tendsto l_measurable by simp_all
qed
end
