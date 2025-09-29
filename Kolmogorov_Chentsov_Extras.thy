(* Title:      Kolmogorov_Chentsov/Kolmogorov_Chentsov_Extras.thy
   Author:     Christian Pardillo Laursen, University of York
*)

section "Supporting lemmas"

theory Kolmogorov_Chentsov_Extras
  imports "HOL-Probability.Probability"
begin

lemma atLeastAtMost_induct[consumes 1, case_names base Suc]:
  assumes \<open>x \<in> {n..m}\<close>
    and \<open>P n\<close>
    and \<open>\<And>k. \<lbrakk>k \<ge> n; k < m; P k\<rbrakk> \<Longrightarrow> P (Suc k)\<close>
  shows \<open>P x\<close>
  by (smt (verit, ccfv_threshold) assms Suc_le_eq atLeastAtMost_iff dec_induct le_trans)

lemma eventually_prodI':
  assumes \<open>eventually P F\<close> \<open>eventually Q G\<close> \<open>\<forall>x y. P x \<longrightarrow> Q y \<longrightarrow> R (x,y)\<close>
  shows \<open>eventually R (F \<times>\<^sub>F G)\<close>
  using assms eventually_prod_filter by blast

text \<open> Analogous to @{thm AE_E3}\<close>
lemma AE_I3:
  assumes \<open>\<And>x. x \<in> space M - N \<Longrightarrow> P x\<close> \<open>N \<in> null_sets M\<close>
  shows \<open>AE x in M. P x\<close>
  by (metis (no_types, lifting) assms DiffI eventually_ae_filter mem_Collect_eq subsetI)

text \<open>Extends @{thm tendsto_dist}\<close>
lemma tendsto_dist_prod:
  fixes l m :: \<open>'a :: metric_space\<close>
  assumes f: \<open>(f \<longlongrightarrow> l) F\<close>
    and g: \<open>(g \<longlongrightarrow> m) G\<close>
  shows \<open>((\<lambda>x. dist (f (fst x)) (g (snd x))) \<longlongrightarrow> dist l m) (F \<times>\<^sub>F G)\<close>
proof (rule tendstoI)
  fix e :: \<open>real\<close> assume \<open>0 < e\<close>
  then have e2: \<open>0 < e/2\<close> by simp
  show \<open>\<forall>\<^sub>F x in F \<times>\<^sub>F G. dist (dist (f (fst x)) (g (snd x))) (dist l m) < e\<close>
    using tendstoD [OF f e2] tendstoD [OF g e2] apply (rule eventually_prodI')
    apply simp
    by (smt (verit) dist_commute dist_norm dist_triangle real_norm_def)
qed

lemma borel_measurable_at_within_metric [measurable]:
  fixes f :: \<open>'a :: first_countable_topology \<Rightarrow> 'b \<Rightarrow> 'c :: metric_space\<close>
  assumes [measurable]: \<open>\<And>t. t \<in> S \<Longrightarrow> f t \<in> borel_measurable M\<close>
    and convergent: \<open>\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<exists>l. ((\<lambda>t. f t \<omega>) \<longlongrightarrow> l) (at x within S)\<close>
    and nontrivial: \<open>at x within S \<noteq> \<bottom>\<close>
  shows \<open>(\<lambda>\<omega>. Lim (at x within S) (\<lambda>t. f t \<omega>)) \<in> borel_measurable M\<close>
proof -
  obtain l where l: \<open>\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> ((\<lambda>t. f t \<omega>) \<longlongrightarrow> l \<omega>) (at x within S)\<close>
    using convergent by metis
  then have Lim_eq: \<open>Lim (at x within S) (\<lambda>t. f t \<omega>) = l \<omega>\<close>
    if \<open>\<omega> \<in> space M\<close> for \<omega>
    using tendsto_Lim[OF nontrivial] that by blast
  from nontrivial have 1: \<open>x islimpt S\<close>
    using trivial_limit_within by blast
  then obtain s :: \<open>nat \<Rightarrow> 'a\<close> where s: \<open>\<And>n. s n \<in> S - {x}\<close> \<open>s \<longlonglongrightarrow> x\<close>
    using islimpt_sequential by blast
  then have \<open>\<And>n. f (s n) \<in> borel_measurable M\<close>
    using s by simp
  moreover have \<open>(\<lambda>n. (f (s n) \<omega>)) \<longlonglongrightarrow> l \<omega>\<close> if \<open>\<omega> \<in> space M\<close> for \<omega>
    using s l[unfolded tendsto_at_iff_sequentially comp_def, OF that]
    by blast
  ultimately have \<open>l \<in> borel_measurable M\<close>
    by (rule borel_measurable_LIMSEQ_metric)
  then show \<open>?thesis\<close>
    using measurable_cong[OF Lim_eq] by fast
qed

lemma Max_finite_image_ex:
  assumes \<open>finite S\<close> \<open>S \<noteq> {}\<close> \<open>P (MAX k\<in>S. f k)\<close> 
  shows \<open>\<exists>k \<in> S. P (f k)\<close>
  using bexI[of \<open>P\<close> \<open>Max (f ` S)\<close> \<open>f ` S\<close>] by (simp add: assms)

lemma measure_leq_emeasure_ennreal: \<open>0 \<le> x \<Longrightarrow> emeasure M A \<le> ennreal x \<Longrightarrow> measure M A \<le> x\<close>
  apply (cases \<open>A \<in> M\<close>)
   apply (metis Sigma_Algebra.measure_def enn2real_leI)
  apply (auto simp: measure_notin_sets emeasure_notin_sets)
  done

lemma Union_add_subset: \<open>(m :: nat) \<le> n \<Longrightarrow> (\<Union>k. A (k + n)) \<subseteq> (\<Union>k. A (k + m))\<close>
  apply (subst subset_eq)
  apply simp
  apply (metis add.commute le_iff_add trans_le_add1)
  done

lemma floor_in_Nats [simp]: \<open>x \<ge> 0 \<Longrightarrow> \<lfloor>x\<rfloor> \<in> \<nat>\<close>
  by (metis nat_0_le of_nat_in_Nats zero_le_floor)

lemma triangle_ineq_list:
  fixes l :: \<open>('a :: metric_space) list\<close>
  assumes \<open>l \<noteq> []\<close>
  shows \<open>dist (hd l) (last l) \<le> (\<Sum> i=1..length l - 1. dist (l!i) (l!(i-1)))\<close>
  using assms proof (induct \<open>l\<close> rule: rev_nonempty_induct)
  case (single x)
  then show \<open>?case\<close> by force
next
  case (snoc x xs)
  define S :: \<open>'a list \<Rightarrow> real\<close> where
    \<open>S \<equiv> \<lambda>l. (\<Sum> i=1..length l - 1. dist (l!i) (l!(i-1)))\<close>
  have \<open>S (xs @ [x]) = dist x (last xs) + S xs\<close>
    unfolding S_def apply simp
    apply (subst sum.last_plus)
     apply (simp add: Suc_leI snoc.hyps(1))
    apply (rule arg_cong2[where f=\<open>(+)\<close>])
     apply (simp add: last_conv_nth nth_append snoc.hyps(1))
    apply (rule sum.cong)
     apply fastforce
    by (smt (verit) Suc_pred atLeastAtMost_iff diff_is_0_eq less_Suc_eq nat_less_le not_less nth_append)
  moreover have \<open>dist (hd xs) (last xs) \<le> S xs\<close>
    unfolding S_def using snoc by blast
  ultimately have \<open>dist (hd xs) x \<le> S (xs@[x])\<close>
    by (smt (verit) dist_triangle2)
  then show \<open>?case\<close>
    unfolding S_def using snoc by simp    
qed

lemma triangle_ineq_sum:
  fixes f :: \<open>nat \<Rightarrow> 'a :: metric_space\<close>
  assumes \<open>n \<le> m\<close>
  shows \<open>dist (f n) (f m) \<le> (\<Sum> i=Suc n..m. dist (f i) (f (i-1)))\<close>
proof (cases \<open>n=m\<close>)
  case True
  then show \<open>?thesis\<close> by simp
next
  case False
  then have \<open>n < m\<close>
    using assms by simp
  define l where \<open>l \<equiv> map (f o nat) [n..m]\<close>
  have [simp]: \<open>l \<noteq> []\<close>
    using \<open>n < m\<close> l_def by fastforce
  have [simp]: \<open>length l = m - n +1\<close>
    unfolding l_def apply simp
    using assms by linarith
  with l_def have \<open>hd l = f n\<close>
    by (simp add: assms upto.simps)
  moreover have \<open>last l = f m\<close>
    unfolding l_def apply (subst last_map)
    using assms apply force
    using \<open>n < m\<close> upto_rec2 by force
  ultimately have \<open>dist (f n) (f m) = dist (hd l) (last l)\<close>
    by simp
  also have \<open>... \<le>  (\<Sum> i=1..length l - 1. dist (l!i) (l!(i-1)))\<close>
    by (rule triangle_ineq_list[OF \<open>l \<noteq> []\<close>])
  also have \<open>... = (\<Sum> i=Suc n..m. dist (f i) (f (i-1)))\<close>
    apply (rule sum.reindex_cong[symmetric, where l=\<open>(+) n\<close>])
    using inj_on_add apply blast
     apply (simp add: assms)
    apply (rule arg_cong2[where f=\<open>dist\<close>])
     apply simp_all
    unfolding l_def apply (subst nth_map, fastforce)
     apply (subst nth_upto, linarith)
    subgoal by simp (insert nat_int_add, presburger)
    apply (subst nth_map, fastforce)
    apply (subst nth_upto, linarith)
    by (simp add: add_diff_eq nat_int_add nat_diff_distrib')
  finally show \<open>?thesis\<close>
    by blast
qed

lemma (in product_prob_space) indep_vars_PiM_coordinate:
  assumes \<open>I \<noteq> {}\<close>
  shows \<open>prob_space.indep_vars (\<Pi>\<^sub>M i\<in>I. M i) M (\<lambda>x f. f x) I\<close>
proof -
  have \<open>distr (Pi\<^sub>M I M) (Pi\<^sub>M I M) (\<lambda>x. restrict x I) = distr (Pi\<^sub>M I M) (Pi\<^sub>M I M) (\<lambda>x. x)\<close>
    by (rule distr_cong; simp add: space_PiM)
  also have \<open>... = PiM I M\<close>
    by simp
  also have \<open>... = Pi\<^sub>M I (\<lambda>i. distr (Pi\<^sub>M I M) (M i) (\<lambda>f. f i))\<close>
    using PiM_component by (intro PiM_cong, auto)
  finally have \<open>distr (Pi\<^sub>M I M) (Pi\<^sub>M I M) (\<lambda>x. restrict x I) = Pi\<^sub>M I (\<lambda>i. distr (Pi\<^sub>M I M) (M i) (\<lambda>f. f i))\<close>
    .
  then show \<open>?thesis\<close>
    using assms by (simp add: indep_vars_iff_distr_eq_PiM')
qed 

lemma (in prob_space) indep_sets_indep_set:
  assumes \<open>indep_sets F I\<close> \<open>i \<in> I\<close> \<open>j \<in> I\<close> \<open>i \<noteq> j\<close>
  shows \<open>indep_set (F i) (F j)\<close>
  unfolding indep_set_def
proof (rule indep_setsI)
  show \<open>(case x of True \<Rightarrow> F i | False \<Rightarrow> F j) \<subseteq> events\<close> for x
    using assms by (auto split: bool.split simp: indep_sets_def)
  fix A J assume *: \<open>J \<noteq> {}\<close> \<open>J \<subseteq> UNIV\<close> \<open>\<forall>ja\<in>J. A ja \<in> (case ja of True \<Rightarrow> F i | False \<Rightarrow> F j)\<close>
  {
    assume \<open>J = UNIV\<close>
    then have \<open>indep_sets F I\<close> \<open>{i,j} \<subseteq> I\<close> \<open>{i, j} \<noteq> {}\<close> \<open>finite {i,j}\<close> \<open>\<forall>x \<in> {i,j}. (\<lambda>x. if x = i then A True else A False) x \<in> F x\<close>
      using * assms apply simp_all
      by (simp add: bool.split_sel)
    then have \<open>prob (\<Inter>j\<in>{i, j}. if j = i then A True else A False) = (\<Prod>j\<in>{i, j}. prob (if j = i then A True else A False))\<close>
      by (rule indep_setsD)
    then have \<open>prob (A True \<inter> A False) = prob (A True) * prob (A False)\<close>
      using assms by (auto simp: ac_simps)
  } note X = this
  consider \<open>J = {True, False}\<close> | \<open>J = {False}\<close> | \<open>J = {True}\<close>
    using *(1,2) unfolding UNIV_bool by blast
  then show \<open>prob (\<Inter> (A ` J)) = (\<Prod>j\<in>J. prob (A j))\<close>
    using X by (cases; auto)
qed

lemma (in prob_space) indep_vars_indep_var:
  assumes \<open>indep_vars M' X I\<close> \<open>i \<in> I\<close> \<open>j \<in> I\<close> \<open>i \<noteq> j\<close>
  shows \<open>indep_var (M' i) (X i) (M' j) (X j)\<close>
  using assms unfolding indep_vars_def indep_var_eq
  by (meson indep_sets_indep_set)

end
