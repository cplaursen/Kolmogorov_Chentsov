(* Title:      Kolmogorov_Chentsov/Holder_Continuous.thy
   Author:     Christian Pardillo Laursen, University of York
*)

section "Hölder continuity"

theory Holder_Continuous
  imports "HOL-Analysis.Analysis"
begin

text \<open> H{\"o}lder continuity is a weaker version of Lipschitz continuity. \<close>

definition holder_at_within :: \<open>real \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ('a :: metric_space \<Rightarrow> 'b :: metric_space) \<Rightarrow> bool\<close> where
  \<open>holder_at_within \<gamma> D r \<phi> \<equiv> \<gamma> \<in> {0<..1} \<and> 
  (\<exists>\<epsilon> > 0. \<exists>C \<ge> 0. \<forall>s \<in> D. dist r s < \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>)\<close>

definition local_holder_on :: \<open>real \<Rightarrow> 'a :: metric_space set \<Rightarrow> ('a \<Rightarrow> 'b :: metric_space) \<Rightarrow> bool\<close> where
  \<open>local_holder_on \<gamma> D \<phi> \<equiv> \<gamma> \<in> {0<..1} \<and>
  (\<forall>t\<in>D. \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. (\<forall>r\<in>D. \<forall>s\<in>D. dist s t < \<epsilon> \<and> dist r t < \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))\<close>

definition holder_on :: \<open>real \<Rightarrow> 'a :: metric_space set \<Rightarrow> ('a \<Rightarrow> 'b :: metric_space) \<Rightarrow> bool\<close> (\<open>_-holder'_on\<close> 1000) where
  \<open>\<gamma>-holder_on D \<phi> \<longleftrightarrow> \<gamma> \<in> {0<..1} \<and> (\<exists>C \<ge> 0. (\<forall>r\<in>D. \<forall>s\<in>D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))\<close>

lemma holder_onI:
  assumes \<open>\<gamma> \<in> {0<..1}\<close> \<open>\<exists>C \<ge> 0. (\<forall>r\<in>D. \<forall>s\<in>D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>)\<close>
  shows \<open>\<gamma>-holder_on D \<phi>\<close>
  unfolding holder_on_def using assms by blast

text \<open> We prove various equivalent formulations of local holder continuity, using open and closed
  balls and inequalities. \<close>

lemma local_holder_on_cball:
  \<open>local_holder_on \<gamma> D \<phi> \<longleftrightarrow> \<gamma> \<in> {0<..1} \<and>
  (\<forall>t\<in>D. \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. (\<forall>r\<in>cball t \<epsilon> \<inter> D. \<forall>s\<in>cball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))\<close>
  (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof
  assume *: \<open>?L\<close>
  {
    fix t assume \<open>t \<in> D\<close>
    then obtain \<epsilon> C where \<open>\<epsilon> > 0\<close> \<open>C \<ge> 0\<close>
      \<open>\<forall>r\<in>ball t \<epsilon> \<inter> D. \<forall>s\<in>ball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>\<close>
      using * unfolding local_holder_on_def apply simp
      by (metis Int_iff dist_commute mem_ball)
    then have **: \<open>\<forall>r\<in>cball t (\<epsilon>/2) \<inter> D. \<forall>s\<in>cball t (\<epsilon>/2) \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>\<close>
      by auto
    have \<open>\<exists>\<epsilon> > 0. \<exists>C \<ge> 0. \<forall>r\<in>cball t \<epsilon> \<inter> D. \<forall>s\<in>cball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>\<close>
      apply (rule exI[where x = \<open>\<epsilon>/2\<close>])
      apply (simp add: \<open>\<epsilon> > 0\<close>)
      apply (rule exI[where x = \<open>C\<close>])
      using ** \<open>C \<ge> 0\<close> by blast
  }
  then show \<open>?R\<close>
    using * local_holder_on_def by blast
next
  assume *: \<open>?R\<close>
  {
    fix t assume \<open>t \<in> D\<close>
    then obtain \<epsilon> C where eC: \<open>\<epsilon> > 0\<close> \<open>C \<ge> 0\<close>
      \<open>\<forall>r\<in>cball t \<epsilon> \<inter> D. \<forall>s\<in>cball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>\<close>
      using * by blast
    then have \<open>\<forall>r \<in> D. \<forall>s \<in> D. dist r t < \<epsilon> \<and> dist s t < \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>\<close>
      unfolding cball_def by (simp add: dist_commute)
    then have \<open>\<exists>\<epsilon>>0. \<exists>C\<ge>0. \<forall>r \<in> D. \<forall>s \<in> D. dist r t < \<epsilon> \<and> dist s t < \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>\<close>
      using eC by blast
  }
  then show \<open>local_holder_on \<gamma> D \<phi>\<close>
    using * unfolding local_holder_on_def by metis
qed

corollary local_holder_on_leq_def: \<open>local_holder_on \<gamma> D \<phi> \<longleftrightarrow> \<gamma> \<in> {0<..1} \<and>
  (\<forall>t\<in>D. \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. (\<forall>r\<in>D. \<forall>s\<in>D. dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))\<close>
  unfolding local_holder_on_cball by (metis dist_commute Int_iff mem_cball)

corollary local_holder_on_ball: \<open>local_holder_on \<gamma> D \<phi> \<longleftrightarrow> \<gamma> \<in> {0<..1} \<and>
  (\<forall>t\<in>D. \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. (\<forall>r\<in>ball t \<epsilon> \<inter> D. \<forall>s\<in>ball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))\<close>
  unfolding local_holder_on_def by (metis dist_commute Int_iff mem_ball)

lemma local_holder_on_altdef:
  assumes \<open>D \<noteq> {}\<close>
  shows \<open>local_holder_on \<gamma> D \<phi> = (\<forall>t \<in> D. (\<exists>\<epsilon> > 0. (\<gamma>-holder_on ((cball t \<epsilon>) \<inter> D) \<phi>)))\<close>
  unfolding local_holder_on_cball holder_on_def using assms by blast

lemma local_holder_on_cong[cong]:
  assumes \<open>\<gamma> = \<epsilon>\<close> \<open>C = D\<close> \<open>\<And>x. x \<in> C \<Longrightarrow> \<phi> x = \<psi> x\<close>
  shows \<open>local_holder_on \<gamma> C \<phi> \<longleftrightarrow> local_holder_on \<epsilon> D \<psi>\<close>
  unfolding local_holder_on_def using assms by presburger

lemma local_holder_onI:
  assumes \<open>\<gamma> \<in> {0<..1}\<close> \<open>(\<forall>t\<in>D. \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. (\<forall>r\<in>D. \<forall>s\<in>D. dist s t < \<epsilon> \<and> dist r t < \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))\<close>
  shows \<open>local_holder_on \<gamma> D \<phi>\<close>
  using assms unfolding local_holder_on_def by blast

lemma local_holder_ballI:
  assumes \<open>\<gamma> \<in> {0<..1}\<close>
    and \<open>\<And>t. t \<in> D \<Longrightarrow> \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. \<forall>r\<in>ball t \<epsilon> \<inter> D. \<forall>s\<in>ball t \<epsilon> \<inter> D. 
                dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>\<close>
  shows \<open>local_holder_on \<gamma> D \<phi>\<close>
  using assms unfolding local_holder_on_ball by blast

lemma local_holder_onE:
  assumes local_holder: \<open>local_holder_on \<gamma> D \<phi>\<close>
    and gamma: \<open>\<gamma> \<in> {0<..1}\<close>
    and \<open>t \<in> D\<close>
  obtains \<epsilon> C where \<open>\<epsilon> > 0\<close> \<open>C \<ge> 0\<close> 
    \<open>\<And>r s. r \<in> ball t \<epsilon> \<inter> D \<Longrightarrow> s \<in> ball t \<epsilon> \<inter> D \<Longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>\<close>
  using assms unfolding local_holder_on_ball by auto

text \<open> Holder continuity matches up with the existing definitions in @{theory "HOL-Analysis.Lipschitz"}\<close>

lemma holder_1_eq_lipschitz: \<open>1-holder_on D \<phi> = (\<exists>C. lipschitz_on C D \<phi>)\<close>
  unfolding holder_on_def lipschitz_on_def by (auto simp: fun_eq_iff dist_commute)

lemma local_holder_1_eq_local_lipschitz: 
  assumes \<open>T \<noteq> {}\<close>
  shows \<open>local_holder_on 1 D \<phi> = local_lipschitz T D (\<lambda>_. \<phi>)\<close>
proof
  assume *: \<open>local_holder_on 1 D \<phi>\<close>
  {
    fix t assume \<open>t \<in> D\<close>
    then obtain \<epsilon> C where eC: \<open>\<epsilon> > 0\<close> \<open>C \<ge> 0\<close>
      \<open>(\<forall>r\<in>D. \<forall>s\<in>D. dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s)\<close>
      using * powr_to_1 unfolding local_holder_on_cball apply simp
      by (metis Int_iff dist_commute mem_cball)
    {
      fix r s assume rs: \<open>r \<in> D\<close> \<open>s \<in> D\<close> \<open>dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon>\<close>
      then have \<open>r \<in> cball t \<epsilon> \<inter> D\<close> \<open>s\<in>cball t \<epsilon> \<inter> D\<close> \<open>dist (\<phi> r) (\<phi> s) \<le> C * dist r s\<close>
        unfolding cball_def using rs eC by (auto simp: dist_commute)
    }
    then have \<open>\<forall>r\<in>cball t \<epsilon> \<inter> D. \<forall>s\<in>cball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s\<close>
      by (simp add: dist_commute)
    then have \<open>C-lipschitz_on ((cball t \<epsilon>) \<inter> D) \<phi>\<close>
      using eC lipschitz_on_def by blast
    then have \<open>\<exists>\<epsilon>>0. \<exists>C. C-lipschitz_on ((cball t \<epsilon>) \<inter> D) \<phi>\<close>
      using eC(1) by blast
  }
  then show \<open>local_lipschitz T D (\<lambda>_. \<phi>)\<close>
    unfolding local_lipschitz_def by blast
next
  assume *: \<open>local_lipschitz T D (\<lambda>_. \<phi>)\<close>
  {
    fix x assume x: \<open>x \<in> D\<close>
    fix t assume t: \<open>t \<in> T\<close>
    then obtain u L where uL: \<open>u > 0\<close> \<open>\<forall>t\<in>cball t u \<inter> T. L-lipschitz_on (cball x u \<inter> D) \<phi>\<close>
      using * x t unfolding local_lipschitz_def by blast
    then have \<open>L-lipschitz_on (cball x u \<inter> D) \<phi>\<close>
      using t by force
    then have \<open>1-holder_on (cball x u \<inter> D) \<phi>\<close>
      using holder_1_eq_lipschitz by blast
    then have \<open>\<exists>\<epsilon> > 0. (1-holder_on ((cball x \<epsilon>) \<inter> D) \<phi>)\<close>
      using uL by blast
  }
  then have \<open>x \<in> D \<Longrightarrow> \<exists>\<epsilon>>0. (1-holder_on (cball x \<epsilon> \<inter> D) \<phi>)\<close> for x
    using assms by blast
  then show \<open>local_holder_on 1 D \<phi>\<close>
    unfolding local_holder_on_cball holder_on_def by (auto simp: dist_commute)
qed

lemma local_holder_refine:
  assumes g: \<open>local_holder_on g D \<phi>\<close> \<open>g \<le> 1\<close> 
    and  h: \<open>h \<le> g\<close> \<open>h > 0\<close>
  shows \<open>local_holder_on h D \<phi>\<close>
proof -
  {
    fix t assume t: \<open>t \<in> D\<close>
    then have \<open>\<exists>\<epsilon>>0. \<exists>C\<ge>0. (\<forall>r\<in>D. \<forall>s\<in>D. dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr g)\<close>
      using g(1) unfolding local_holder_on_leq_def by blast 
    then obtain \<epsilon> C where eC: \<open>\<epsilon> > 0\<close> \<open>C \<ge> 0\<close> 
      \<open>(\<forall>s\<in>D. \<forall>r\<in>D. dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr g)\<close>
      by blast
    let \<open>?e\<close> = \<open>min \<epsilon> (1/2)\<close>
    {
      fix s r assume *: \<open>s \<in> D\<close> \<open>r \<in> D\<close> \<open>dist s t \<le> ?e\<close> \<open>dist r t \<le> ?e\<close>
      then have \<open>dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr g\<close>
        using eC by simp
      moreover have \<open>dist r s \<le> 1\<close>
        by (smt (verit) * dist_triangle2 half_bounded_equal)
      ultimately have \<open>dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr h\<close>
        by (metis dual_order.trans zero_le_dist powr_mono' assms(3) eC(2) mult_left_mono )
    }
    then have \<open>(\<forall>s\<in>D. \<forall>r\<in>D. dist s t \<le> ?e \<and> dist r t \<le> ?e \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr h)\<close>
      by blast
    moreover have \<open>?e > 0\<close> \<open>C \<ge> 0\<close>
      using eC by linarith+
    ultimately have \<open>\<exists>\<epsilon>>0. \<exists>C\<ge>0. (\<forall>r\<in>D. \<forall>s\<in>D. dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr h)\<close>
      by blast
  }
  then show \<open>?thesis\<close>
    unfolding local_holder_on_leq_def using assms by force
qed

lemma holder_uniform_continuous:
  assumes \<open>\<gamma>-holder_on X \<phi>\<close>
  shows \<open>uniformly_continuous_on X \<phi>\<close>
  unfolding uniformly_continuous_on_def
proof safe
  fix e::\<open>real\<close>
  assume \<open>0 < e\<close>
  from assms obtain C where C: \<open>C \<ge> 1\<close> \<open>(\<forall>r\<in>X. \<forall>s\<in>X. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>)\<close>
    unfolding holder_on_def
    by (smt (verit) dist_eq_0_iff mult_le_cancel_right1 powr_0 powr_gt_zero)
  {
    fix r s assume \<open>r \<in> X\<close> \<open>s \<in> X\<close>
    have dist_0: \<open>dist (\<phi> r) (\<phi> s) = 0 \<Longrightarrow> dist (\<phi> r) (\<phi> s) < e\<close>
      using \<open>0 < e\<close> by linarith
    then have holder_neq_0: \<open>dist (\<phi> r) (\<phi> s) < (C + 1) * dist r s powr \<gamma>\<close> if \<open>dist (\<phi> r) (\<phi> s) > 0\<close>
      using C(2) that
      by (smt (verit, ccfv_SIG) \<open>r \<in> X\<close> \<open>s \<in> X\<close> dist_eq_0_iff mult_le_cancel_right powr_gt_zero)
    have gamma: \<open>\<gamma> \<in> {0<..1}\<close>
      using assms holder_on_def by blast+
    assume \<open>dist r s < (e/C) powr (1 / \<gamma>)\<close>
    then have \<open>C * dist r s powr \<gamma> < C * ((e/C) powr (1 / \<gamma>)) powr \<gamma>\<close> if \<open>dist (\<phi> r) (\<phi> s) > 0\<close>
      using holder_neq_0 C(1) powr_less_mono2 gamma by fastforce
    also have \<open>... = e\<close>
      using C(1) gamma \<open>0 < e\<close> powr_powr by auto
    finally have \<open>dist (\<phi> r) (\<phi> s) < e\<close>
      using dist_0 holder_neq_0 C(2) \<open>r \<in> X\<close> \<open>s \<in> X\<close> by fastforce
  }
  then show \<open>\<exists>d>0. \<forall>x\<in>X. \<forall>x'\<in>X. dist x' x < d \<longrightarrow> dist (\<phi> x') (\<phi> x) < e\<close>
    by (metis C(1) \<open>0 < e\<close> divide_eq_0_iff linorder_not_le order_less_irrefl powr_gt_zero zero_less_one)
qed

corollary holder_on_continuous_on: \<open>\<gamma>-holder_on X \<phi> \<Longrightarrow> continuous_on X \<phi>\<close>
  using holder_uniform_continuous uniformly_continuous_imp_continuous by blast


lemma holder_implies_local_holder: \<open>\<gamma>-holder_on D \<phi> \<Longrightarrow> local_holder_on \<gamma> D \<phi>\<close>
  apply (cases \<open>D = {}\<close>)
   apply (simp add: holder_on_def local_holder_on_def)
  apply (simp add: local_holder_on_altdef holder_on_def)
  apply (metis IntD1 inf.commute)
  done

lemma local_holder_imp_continuous:
  assumes local_holder: \<open>local_holder_on \<gamma> X \<phi>\<close>
  shows \<open>continuous_on X \<phi>\<close>
  unfolding continuous_on_def
proof safe
  fix x assume \<open>x \<in> X\<close>
  {
    assume \<open>X \<noteq> {}\<close>
    from local_holder obtain \<epsilon> where \<open>0 < \<epsilon>\<close> and holder: \<open>\<gamma>-holder_on ((cball x \<epsilon>) \<inter> X) \<phi>\<close>
      unfolding local_holder_on_altdef[OF \<open>X \<noteq> {}\<close>] using \<open>x \<in> X\<close> by blast
    have \<open>x \<in> ball x \<epsilon>\<close> using \<open>0 < \<epsilon>\<close> by simp
    then have \<open>(\<phi> \<longlongrightarrow> \<phi> x) (at x within cball x \<epsilon> \<inter> X)\<close>
      using holder_on_continuous_on[OF holder] \<open>x \<in> X\<close> unfolding continuous_on_def by simp
    moreover have \<open>\<forall>\<^sub>F xa in at x. (xa \<in> cball x \<epsilon> \<inter> X) = (xa \<in> X)\<close>
      using eventually_at_ball[OF \<open>0 < \<epsilon>\<close>, of \<open>x\<close> \<open>UNIV\<close>]
      by eventually_elim auto
    ultimately have \<open>(\<phi> \<longlongrightarrow> \<phi> x) (at x within X)\<close>
      by (rule Lim_transform_within_set)
  }
  then show \<open>(\<phi> \<longlongrightarrow> \<phi> x) (at x within X)\<close>
    by fastforce
qed

lemma local_holder_compact_imp_holder:
  assumes \<open>compact I\<close> \<open>local_holder_on \<gamma> I \<phi>\<close>
  shows \<open>\<gamma>-holder_on I \<phi>\<close>
proof -
  have *: \<open>\<gamma> \<in> {0<..1}\<close> \<open>(\<forall>t\<in>I. \<exists>\<epsilon>. \<exists>C. \<epsilon> > 0 \<and> C \<ge> 0 \<and> 
    (\<forall>r \<in> ball t \<epsilon> \<inter> I. \<forall>s \<in> ball t \<epsilon> \<inter> I. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))\<close>
    using assms(2) unfolding local_holder_on_ball by simp_all
  obtain \<epsilon> C where eC: \<open>t \<in> I \<Longrightarrow> \<epsilon> t > 0 \<and> C t \<ge> 0 \<and> (\<forall>r \<in> ball t (\<epsilon> t) \<inter> I. \<forall>s \<in> ball t (\<epsilon> t) \<inter> I. dist (\<phi> r) (\<phi> s) \<le> C t * dist r s powr \<gamma>)\<close> for t
    by (metis *(2))
  have \<open>I \<subseteq> (\<Union>t \<in> I. ball t (\<epsilon> t))\<close>
    apply (simp add: subset_iff)
    using eC by force
  then obtain D where D: \<open>D \<subseteq> (\<lambda>t. ball t (\<epsilon> t)) ` I\<close> \<open>finite D\<close> \<open>I \<subseteq> \<Union> D\<close>
    using compact_eq_Heine_Borel[of \<open>I\<close>] apply (simp add: assms(1))
    by (smt (verit, ccfv_SIG) open_ball imageE mem_Collect_eq subset_iff)
  then obtain T where T: \<open>D = (\<lambda>t. ball t (\<epsilon> t)) ` T\<close> \<open>T \<subseteq> I\<close> \<open>finite T\<close>
    by (meson finite_subset_image subset_image_iff)
  text \<open> $\varrho$ is the Lebesgue number of the cover \<close>
  from D obtain \<rho> :: \<open>real\<close> where \<rho>: \<open>\<forall>t \<in> I. \<exists>U \<in> D. ball t \<rho> \<subseteq> U\<close> \<open>\<rho> > 0\<close>
    by (smt (verit, del_insts) Elementary_Metric_Spaces.open_ball Heine_Borel_lemma assms(1) imageE subset_image_iff)
  have \<open>bounded (\<phi> ` I)\<close>
    by (metis compact_continuous_image compact_imp_bounded assms local_holder_imp_continuous)
  then obtain l where l: \<open>\<forall>x \<in> I. \<forall>y \<in> I. dist (\<phi> x) (\<phi> y) \<le> l\<close>
    by (metis bounded_two_points image_eqI)
  text \<open> Simply need to construct C\_bar such that it is greater than any of these \<close>
  define C_bar where \<open>C_bar \<equiv> max ((\<Sum>t \<in> T. C t)) (l * \<rho> powr (- \<gamma>))\<close>
  have C_bar_le: \<open>C_bar \<ge> C t\<close> if \<open>t \<in> T\<close> for t
  proof -
    have ge_0: \<open>t \<in> T \<Longrightarrow> C t \<ge> 0\<close> for t
      using T(2) eC by blast
    then have \<open>\<Sum> (C ` (T - {t})) \<ge> 0\<close>
      by (metis (mono_tags, lifting) Diff_subset imageE subset_eq sum_nonneg)
    then have \<open>(\<Sum>t \<in> T. C t) \<ge> C t\<close>
      by (metis T(3) ge_0 sum_nonneg_leq_bound that)
    then have \<open>max ((\<Sum>t \<in> T. C t)) S \<ge> C t\<close> for S
      by argo
    then show \<open>C_bar \<ge> C t\<close>
      unfolding C_bar_def by blast
  qed
  {
    fix s r assume sr: \<open>s \<in> I\<close> \<open>r \<in> I\<close>
    {
      assume \<open>dist s r < \<rho>\<close>
      then obtain t where t: \<open>t \<in> T\<close> \<open>s \<in> ball t (\<epsilon> t)\<close> \<open>r \<in> ball t (\<epsilon> t)\<close>
        by (smt (verit) sr D T \<rho> ball_eq_empty centre_in_ball imageE mem_ball subset_iff)
      then have \<open>dist (\<phi> s) (\<phi> r) \<le> C t * dist s r powr \<gamma>\<close>
        using eC[of \<open>t\<close>] T(2) sr by blast
      then have \<open>dist (\<phi> s) (\<phi> r) \<le> C_bar * dist s r powr \<gamma>\<close>
        by (smt (verit, best) t C_bar_le mult_right_mono powr_non_neg)
    } note le_rho = this
    {
      assume \<open>dist s r \<ge> \<rho>\<close>
      then have \<open>dist (\<phi> s) (\<phi> r) \<le> l * (dist s r / \<rho>) powr \<gamma>\<close>
      proof -
        have \<open>(dist s r / \<rho>) \<ge> 1\<close>
          using \<open>dist s r \<ge> \<rho>\<close> \<open>\<rho> > 0\<close> by auto
        then have \<open>(dist s r / \<rho>) powr \<gamma> \<ge> 1\<close>
          using "*"(1) ge_one_powr_ge_zero by auto
        then show \<open>dist (\<phi> s) (\<phi> r) \<le> l * (dist s r / \<rho>) powr \<gamma>\<close>
          using l
          by (metis dist_self linordered_nonzero_semiring_class.zero_le_one mult.right_neutral mult_mono sr(1) sr(2))
      qed
      also have \<open>... \<le> C_bar * dist s r powr \<gamma>\<close>
      proof -
        have \<open>l * (dist s r / \<rho>) powr \<gamma> = l * \<rho> powr (- \<gamma>) * dist s r powr \<gamma> \<close>
          using \<rho>(2) divide_powr_uminus powr_divide by force
        also have \<open>... \<le> C_bar * dist s r powr \<gamma>\<close>
          unfolding C_bar_def by (simp add: mult_right_mono)
        finally show \<open>l * (dist s r / \<rho>) powr \<gamma> \<le> C_bar * dist s r powr \<gamma>\<close>
          .
      qed
      finally have \<open>dist (\<phi> s) (\<phi> r) \<le> C_bar * dist s r powr \<gamma>\<close>
        .
    }
    then have \<open>dist (\<phi> s) (\<phi> r) \<le> C_bar * dist s r powr \<gamma>\<close>
      using le_rho by argo
  }
  then have \<open>\<forall>r\<in>I. \<forall>s\<in>I. dist (\<phi> r) (\<phi> s) \<le> C_bar * dist r s powr \<gamma>\<close>
    by simp
  then show \<open>?thesis\<close>
    unfolding holder_on_def
    by (metis "*"(1) C_bar_def dist_self div_by_0 divide_nonneg_pos divide_powr_uminus 
        dual_order.trans l max.cobounded2 powr_0 powr_gt_zero)
qed

lemma holder_const: \<open>\<gamma>-holder_on C (\<lambda>_. c) \<longleftrightarrow> \<gamma> \<in> {0<..1}\<close>
  unfolding holder_on_def by auto

lemma local_holder_const: \<open>local_holder_on \<gamma> C (\<lambda>_. c) \<longleftrightarrow> \<gamma> \<in> {0<..1}\<close>
  using holder_const holder_implies_local_holder local_holder_on_def by blast

section \<open> For $0 < \gamma \leq 1$, \<^term>\<open>\<lambda>x. x powr \<gamma>\<close> satisfies \<^term>\<open>\<gamma>-holder_on {0..}\<close> \<close>

lemma concave_on_subset:
  assumes \<open>concave_on T f\<close> \<open>S \<subseteq> T\<close> \<open>convex S\<close>
  shows \<open>concave_on S f\<close>
proof -
  have \<open>convex_on T (\<lambda>x. - f x)\<close>
    using assms(1) unfolding concave_on_def .
  then have \<open>convex_on S (\<lambda>x. - f x)\<close>
    using assms(2,3) by (rule convex_on_subset)
  then show \<open>?thesis\<close>
    unfolding concave_on_def by blast
qed

lemma concave_subadditive:
  fixes f :: \<open>real \<Rightarrow> real\<close>
  assumes \<open>concave_on {0..} f\<close> \<open>0 \<le> f 0\<close> \<open>0 \<le> x\<close> \<open>0 \<le> y\<close>
  shows \<open>f (x + y) \<le> f x + f y\<close>
proof -
  have mult: \<open>t * f a \<le> f (t * a)\<close>
    if \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> \<open>a \<in> {0..}\<close> for t a
  proof -
    have \<open>t * f a \<le> (1-t) * f 0 + t * f a\<close>
      using assms(2) that(1,2) mult_left_le_one_le by simp
    also have \<open>... \<le> f ((1-t) * 0 + t * a)\<close>
      using assms(1)[THEN concave_onD, OF that(1,2)] that(3) by force
    also have \<open>... \<le> f (t * a)\<close>
      by auto
    finally show \<open>?thesis\<close>
      using add.commute by argo
  qed
  consider \<open>x + y = 0\<close> | \<open>x + y > 0\<close>
    using assms(3,4) by linarith
  then show \<open>?thesis\<close>
  proof cases
    case 1
    then have \<open>x = 0\<close> \<open>y = 0\<close>
      using assms(3,4) by argo+
    then show \<open>?thesis\<close>
      by (simp add: assms(2))
  next
    case 2
    then have \<open>f (x + y) = (x/(x+y)) * f (x + y) + (y / (x+y)) * f (x + y)\<close>
      by (simp add: add_divide_distrib[symmetric] 
                  vector_space_over_itself.scale_left_distrib[symmetric])
    also have \<open>... \<le> f (x / (x + y) * (x + y)) + f (y / (x + y) * (x + y))\<close>
      apply (intro add_mono mult)
      using assms(3,4) divide_nonneg_pos 2 by simp_all
    also have \<open>... = f x + f y\<close>
      using 2 by (auto cong: arg_cong2[where f=\<open>(+)\<close>] arg_cong[where f=\<open>f\<close>])
    finally show \<open>?thesis\<close>
      by blast
  qed
qed    

lemma powr_0_1_concave:
  assumes \<open>\<gamma> \<in> {0<..1}\<close>
  shows \<open>concave_on {0..} (\<lambda>x. x powr \<gamma>)\<close>
proof -
  have \<open>concave_on {0<..} (\<lambda>x. x powr \<gamma>)\<close>
    apply (rule f''_le0_imp_concave)
       apply simp
      apply (auto intro!: has_real_derivative_powr)[1]
    using assms apply (auto intro!: derivative_intros simp: field_simps)
    done
  {
    fix x y :: \<open>real\<close>
    assume \<open>x \<in> {0..}\<close> \<open>y \<in> {0..}\<close>
    then have *: \<open>\<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u * x powr \<gamma> + v * y powr \<gamma> \<le> (u *\<^sub>R x + v *\<^sub>R y) powr \<gamma>\<close>
      if \<open>x = 0 \<or> y = 0\<close>
      using that apply auto
       apply (metis add.commute assms greaterThanAtMost_iff landau_o.R_mult_right_mono
          le_add_same_cancel1 powr_ge_zero powr_mono' powr_mult powr_one_gt_zero_iff)+
      done
    consider \<open>x = 0 \<or> y = 0\<close> | \<open>x \<in> {0<..} \<and> y \<in> {0<..}\<close>
      using \<open>x \<in> {0..}\<close> \<open>y \<in> {0..}\<close> by fastforce
    then have \<open>\<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u * x powr \<gamma> + v * y powr \<gamma> \<le> (u *\<^sub>R x + v *\<^sub>R y) powr \<gamma>\<close>
      apply cases
       apply (fact *)
      using \<open>concave_on {0<..} (\<lambda>x. x powr \<gamma>)\<close>[simplified concave_on_iff] apply simp
      done
  }  then show \<open>?thesis\<close>
    by (simp add: concave_on_iff)
qed

corollary powr_0_1_concave_interval:
  assumes \<open>x \<ge> 0\<close> \<open>y \<ge> 0\<close> \<open>\<gamma> \<in> {0<..1}\<close>
  shows \<open>concave_on {x..y} (\<lambda>r. r powr \<gamma>)\<close>
  using assms by (auto intro: concave_on_subset[OF powr_0_1_concave])

lemma powr_0_1_subadditive:
  fixes x y \<gamma> :: \<open>real\<close>
  assumes \<open>\<gamma> \<in> {0<..1}\<close> \<open>x \<ge> 0\<close> \<open>y \<ge> 0\<close>
  shows \<open>x powr \<gamma> + y powr \<gamma> \<ge> (x + y) powr \<gamma>\<close>
  using concave_subadditive powr_0_1_concave[OF assms(1)] assms(2,3) by fastforce

theorem holder_powr:
  assumes \<open>\<gamma> \<in> {0<..1}\<close>
  shows \<open>\<gamma>-holder_on {0..} (\<lambda>x. x powr \<gamma>)\<close>
  apply (clarsimp simp: dist_real_def abs_real_def
                  intro!: holder_onI[OF assms] exI[where x=\<open>1\<close>])
  apply safe
     apply (smt (verit, best) powr_0_1_subadditive[OF assms])
    apply (meson assms greaterThanAtMost_iff powr_less_mono2)
   apply (metis assms greaterThanAtMost_iff linorder_not_less order_less_le powr_less_mono2)
  apply (smt (verit, best) powr_0_1_subadditive[OF assms])
  done

end
