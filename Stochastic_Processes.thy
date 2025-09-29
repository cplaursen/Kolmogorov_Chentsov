(* Title:      Kolmgorov_Chentsov/Stochastic_Processes.thy
   Author:     Christian Pardillo Laursen, University of York
*)

section "Stochastic processes"

theory Stochastic_Processes
  imports Kolmogorov_Chentsov_Extras Dyadic_Interval
begin

text \<open> A stochastic process is an indexed collection of random variables. For compatibility with 
  \texttt{product\_prob\_space} we don't enforce conditions on the index set $I$ in the assumptions. \<close>

locale stochastic_process = prob_space +
  fixes M' :: \<open>'b measure\<close>
    and I :: \<open>'t set\<close>
    and X :: \<open>'t \<Rightarrow> 'a \<Rightarrow> 'b\<close>
  assumes random_process[measurable]: \<open>\<And>i. random_variable M' (X i)\<close>

sublocale stochastic_process \<subseteq> product: product_prob_space \<open>(\<lambda>t. distr M M' (X t))\<close>
  using prob_space_distr random_process by (blast intro: product_prob_spaceI)

lemma (in prob_space) stochastic_processI:
  assumes \<open>\<And>i. random_variable M' (X i)\<close>
  shows \<open>stochastic_process M M' X\<close>
  by (simp add: assms prob_space_axioms stochastic_process_axioms.intro stochastic_process_def)

typedef ('t, 'a, 'b) stochastic_process =
  \<open>{(M :: 'a measure, M' :: 'b measure, I :: 't set, X :: 't \<Rightarrow> 'a \<Rightarrow> 'b).
   stochastic_process M M' X}\<close>
proof
  show \<open>(return (sigma UNIV {{}, UNIV}) x, sigma UNIV UNIV, UNIV, \<lambda>_ _. c) \<in>
       {(M, M', I, X). stochastic_process M M' X}\<close> for x :: \<open>'a\<close> and c :: \<open>'b\<close>
    by (simp add: prob_space_return prob_space.stochastic_processI)
qed

setup_lifting type_definition_stochastic_process

lift_definition proc_source :: \<open>('t,'a,'b) stochastic_process \<Rightarrow> 'a measure\<close>
  is \<open>fst\<close> .

interpretation proc_source: prob_space \<open>proc_source X\<close>
  by (induction, simp add: proc_source_def Abs_stochastic_process_inverse case_prod_beta' stochastic_process_def)

lift_definition proc_target :: \<open>('t,'a,'b) stochastic_process \<Rightarrow> 'b measure\<close>
  is \<open>fst \<circ> snd\<close> .

lift_definition proc_index :: \<open>('t,'a,'b) stochastic_process \<Rightarrow> 't set\<close>
  is \<open>fst \<circ> snd \<circ> snd\<close> .

lift_definition process :: \<open>('t,'a,'b) stochastic_process \<Rightarrow> 't \<Rightarrow> 'a \<Rightarrow> 'b\<close>
  is \<open>snd \<circ> snd \<circ> snd\<close> .

declare [[coercion \<open>process\<close>]]

lemma stochastic_process_construct [simp]: \<open>stochastic_process (proc_source X) (proc_target X) (process X)\<close>
  by (transfer, force)

interpretation stochastic_process \<open>proc_source X\<close> \<open>proc_target X\<close> \<open>proc_index X\<close> \<open>process X\<close>
  by simp

lemma stochastic_process_measurable [measurable]: \<open>process X t \<in> (proc_source X) \<rightarrow>\<^sub>M (proc_target X)\<close>
  by (meson random_process)
text \<open> Here we construct a process on a given index set. For this we need to produce measurable
  functions for indices outside the index set; we use the constant function, but it needs to point at
  an element of the target set to be measurable. \<close>

context prob_space
begin

lift_definition process_of :: \<open>'b measure \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('t,'a,'b) stochastic_process\<close>
  is \<open>\<lambda> M' I X \<omega>. if (\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M') \<and> \<omega> \<in> space M'
  then (M, M', I, (\<lambda>t. if t \<in> I then X t else (\<lambda>_. \<omega>)))
  else (return (sigma UNIV {{}, UNIV}) (SOME x. True), sigma UNIV UNIV, I, \<lambda>_ _. \<omega>)\<close>
  by (simp add: stochastic_processI prob_space_return prob_space.stochastic_processI)

lemma index_process_of[simp]: \<open>proc_index (process_of M' I X \<omega>) = I\<close>
  by (transfer, auto)

lemma
  assumes \<open>\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M'\<close> \<open>\<omega> \<in> space M'\<close>
  shows
    source_process_of[simp]: \<open>proc_source (process_of M' I X \<omega>) = M\<close> and
    target_process_of[simp]: \<open>proc_target (process_of M' I X \<omega>) = M'\<close> and
    process_process_of[simp]: \<open>process (process_of M' I X \<omega>) = (\<lambda>t. if t \<in> I then X t else (\<lambda>_. \<omega>))\<close>
  using assms by (transfer, auto)+

lemma process_of_apply:
  assumes \<open>\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M'\<close> \<open>\<omega> \<in> space M'\<close> \<open>t \<in> I\<close>
  shows \<open>process (process_of M' I X \<omega>) t = X t\<close>
  using assms by (meson process_process_of)
end

text \<open> We define the finite-dimensional distributions of our process. \<close>

lift_definition distributions :: \<open>('t, 'a, 'b) stochastic_process \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'b) measure\<close>
  is \<open>\<lambda>(M, M', _, X) T. (\<Pi>\<^sub>M t\<in>T. distr M M' (X t))\<close> .

lemma distributions_altdef: \<open>distributions X T = (\<Pi>\<^sub>M t\<in>T. distr (proc_source X) (proc_target X) (X t))\<close>
  by (transfer, auto)

lemma prob_space_distributions: \<open>prob_space (distributions X J)\<close>
  unfolding distributions_altdef
  by (simp add: prob_space_PiM proc_source.prob_space_distr random_process)

lemma sets_distributions: \<open>sets (distributions X J) = sets (PiM J (\<lambda>_. (proc_target X)))\<close>
  by (transfer, auto cong: sets_PiM_cong)

lemma space_distributions: \<open>space (distributions X J) = (\<Pi>\<^sub>E i\<in>J. space (proc_target X))\<close>
  by (transfer, auto simp add: space_PiM)

lemma emeasure_distributions:
  assumes \<open>finite J\<close> \<open>\<And>j. j\<in>J \<Longrightarrow> A j \<in> sets (proc_target X)\<close>
  shows \<open>emeasure (distributions X J) (Pi\<^sub>E J A) = (\<Prod>j\<in>J. emeasure (distr (proc_source X) (proc_target X) (X j)) (A j))\<close>
  by (simp add: assms(1) assms(2) distributions_altdef product.emeasure_PiM)

interpretation projective_family \<open>(proc_index X)\<close> \<open>distributions X\<close> \<open>(\<lambda>_. proc_target X)\<close>
proof (intro projective_family.intro)
  fix J and H
  let \<open>?I\<close> = \<open>proc_index X\<close>
    and \<open>?M\<close> = \<open>proc_source X\<close>
    and \<open>?M'\<close> = \<open>proc_target X\<close>
  assume *: \<open>J \<subseteq> H\<close> \<open>finite H\<close> \<open>H \<subseteq> ?I\<close>
  then have \<open>J \<subseteq> ?I\<close>
    by simp
  show \<open>distributions X J = distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J)\<close>
  proof (rule measure_eqI)
    show \<open>sets (distributions X J) = sets (distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J))\<close>
      by (simp add: sets_distributions)
    fix S assume \<open>S \<in> sets (distributions X J)\<close>
    then have in_sets: \<open>S \<in> sets (PiM J (\<lambda>_. ?M'))\<close>
      by (simp add: sets_distributions)
    have prod_emb_distr: \<open>(prod_emb H (\<lambda>_. ?M') J S) = (prod_emb H (\<lambda>t. distr ?M ?M' (X t)) J S)\<close>
      by (simp add: prod_emb_def)
    have \<open>emeasure (distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J)) S =
          emeasure (distributions X H) (prod_emb H (\<lambda>_. ?M') J S)\<close>
      apply (rule emeasure_distr_restrict)
      by (simp_all add: "*" sets_distributions in_sets)
    also have \<open>... = emeasure (distributions X J) S\<close>
      unfolding distributions_altdef
      using *(1,2) in_sets prod_emb_distr by force
    finally show \<open>emeasure (distributions X J) S 
                = emeasure (distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J)) S\<close>
      by argo
  qed
qed (rule prob_space_distributions)

locale polish_stochastic = stochastic_process \<open>M\<close> \<open>borel :: 'b::polish_space measure\<close> \<open>I\<close> \<open>X\<close>
  for M and I and X

(*
sublocale polish_stochastic \<subseteq> polish_projective I distributions
  by (simp add: polish_projective.intro projective_family_axioms) *)

lemma distributed_cong_random_variable:
  assumes \<open>M = K\<close> \<open>N = L\<close> \<open>AE x in M. X x = Y x\<close> \<open>X \<in> M \<rightarrow>\<^sub>M N\<close> \<open>Y \<in> K \<rightarrow>\<^sub>M L\<close> \<open>f \<in> borel_measurable N\<close>
  shows \<open>distributed M N X f \<longleftrightarrow> distributed K L Y f\<close>
  using assms by (auto simp add: distributed_def distr_cong_AE)

text \<open> For all sorted lists of indices, the increments specified by this list are independent \<close>

lift_definition indep_increments :: \<open>('t :: linorder, 'a, 'b :: minus) stochastic_process \<Rightarrow> bool\<close> is
  \<open>\<lambda>(M, M', I, X).
  (\<forall>l. set l \<subseteq> I \<and> sorted l \<and> length l \<ge> 2 \<longrightarrow>
     prob_space.indep_vars M (\<lambda>_. M') (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l})\<close> .

lemma indep_incrementsE:
  assumes \<open>indep_increments X\<close>
    and \<open>set l \<subseteq> proc_index X \<and> sorted l \<and> length l \<ge> 2\<close>
  shows \<open>prob_space.indep_vars (proc_source X) (\<lambda>_. proc_target X)
         (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l}\<close>
  using assms by (transfer, auto)

lemma indep_incrementsI:
  assumes \<open>\<And>l. set l \<subseteq> proc_index X \<Longrightarrow> sorted l \<Longrightarrow> length l \<ge> 2 \<Longrightarrow>
   prob_space.indep_vars (proc_source X) (\<lambda>_. proc_target X) (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l}\<close>
  shows \<open>indep_increments X\<close>
  using assms by (transfer, auto)

lemma indep_increments_indep_var:
  assumes \<open>indep_increments X\<close> \<open>h \<in> proc_index X\<close> \<open>j \<in> proc_index X\<close> \<open>k \<in> proc_index X\<close> \<open>h \<le> j\<close> \<open>j \<le> k\<close>
  shows \<open>prob_space.indep_var (proc_source X) (proc_target X) (\<lambda>v. X j v - X h v) (proc_target X) (\<lambda>v. X k v - X j v)\<close>
proof -
  let \<open>?l\<close> = \<open>[h,j,k]\<close>
  have \<open>set ?l \<subseteq> proc_index X \<and> sorted ?l \<and> 2 \<le> length ?l\<close>
    using assms by auto
  then have \<open>prob_space.indep_vars (proc_source X) (\<lambda>_. proc_target X) (\<lambda>k v. X (?l!k) v - X (?l!(k-1)) v) {1..<length ?l}\<close>
    by (rule indep_incrementsE[OF assms(1)])
  then show \<open>?thesis\<close>
    using proc_source.indep_vars_indep_var by fastforce
qed

definition \<open>stationary_increments X \<longleftrightarrow> (\<forall>t1 t2 k. t1 > 0 \<and> t2 > 0 \<and> k > 0 \<longrightarrow> 
     distr (proc_source X) (proc_target X) (\<lambda>v. X (t1 + k) v - X t1 v) =
     distr (proc_source X) (proc_target X) (\<lambda>v. X (t2 + k) v - X t2 v))\<close>

text \<open> Processes on the same source measure space, with the same index space, but not necessarily the same
  target measure since we only care about the measurable target space, not the measure \<close>

lift_definition compatible :: \<open>('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool\<close>
  is \<open>\<lambda>(Mx, M'x, Ix, X) (My, M'y, Iy, _). Mx = My \<and> sets M'x = sets M'y \<and> Ix = Iy\<close> .

lemma compatibleI:
  assumes \<open>proc_source X = proc_source Y\<close> \<open>sets (proc_target X) = sets (proc_target Y)\<close>
    \<open>proc_index X = proc_index Y\<close>
  shows \<open>compatible X Y\<close>
  using assms by (transfer, auto)

lemma
  assumes \<open>compatible X Y\<close>
  shows
    compatible_source [dest]: \<open>proc_source X = proc_source Y\<close> and
    compatible_target [dest]: \<open>sets (proc_target X) = sets (proc_target Y)\<close> and
    compatible_index [dest]: \<open>proc_index X = proc_index Y\<close>
  using assms by (transfer, auto)+

lemma compatible_refl [simp]: \<open>compatible X X\<close>
  by (transfer, auto)

lemma compatible_sym: \<open>compatible X Y \<Longrightarrow> compatible Y X\<close>
  by (transfer, auto)

lemma compatible_trans:
  assumes \<open>compatible X Y\<close> \<open>compatible Y Z\<close>
  shows \<open>compatible X Z\<close>
  using assms by (transfer, auto)

lemma (in prob_space) compatible_process_of:
  assumes measurable: \<open>\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M'\<close> \<open>\<forall>t \<in> I. Y t \<in> M \<rightarrow>\<^sub>M M'\<close> 
    and \<open>a \<in> space M'\<close> \<open>b \<in> space M'\<close>
  shows \<open>compatible (process_of M' I X a) (process_of M' I Y b)\<close>
  using assms by (transfer, auto)

definition modification :: \<open>('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool\<close> where
  \<open>modification X Y \<longleftrightarrow> compatible X Y \<and> (\<forall>t \<in> proc_index X. AE x in proc_source X. X t x = Y t x)\<close>

lemma modificationI [intro]:
  assumes \<open>compatible X Y\<close> \<open>\<And>t. t \<in> proc_index X \<Longrightarrow> AE x in proc_source X. X t x = Y t x\<close>
  shows \<open>modification X Y\<close>
  unfolding modification_def using assms by blast

lemma modificationD [dest]:
  assumes \<open>modification X Y\<close>
  shows \<open>compatible X Y\<close>
    and \<open>\<And>t. t \<in> proc_index X \<Longrightarrow> AE x in proc_source X. X t x = Y t x\<close>
  using assms unfolding modification_def by blast+

lemma modification_null_set:
  assumes \<open>modification X Y\<close> \<open>t \<in> proc_index X\<close>
  obtains N where \<open>{x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N\<close> \<open>N \<in> null_sets (proc_source X)\<close>
proof -
  from assms have \<open>AE x in proc_source X. X t x = Y t x\<close>
    by (rule modificationD(2))
  then have \<open>\<exists>N\<in>null_sets (proc_source X). {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N\<close>
    by (simp add: eventually_ae_filter)
  then show \<open>?thesis\<close>
    using that by blast
qed

lemma modification_refl [simp]: \<open>modification X X\<close>
  by (simp add: modificationI)

lemma modification_sym: \<open>modification X Y \<Longrightarrow> modification Y X\<close>
proof (rule modificationI)
  assume *: \<open>modification X Y\<close>
  then show compat: \<open>compatible Y X\<close>
    using compatible_sym modificationD(1) by blast
  fix t assume \<open>t \<in> proc_index Y\<close>
  then have \<open>t \<in> proc_index X\<close>
    using compatible_index[OF compat] by blast
  have \<open>AE x in proc_source Y. X t x = Y t x\<close>
    using modificationD(2)[OF * \<open>t \<in> proc_index X\<close>]
      compatible_source[OF compat] by argo
  then show \<open>AE x in proc_source Y. Y t x = X t x\<close>
    by force
qed

lemma modification_trans:
  assumes \<open>modification X Y\<close> \<open>modification Y Z\<close>
  shows \<open>modification X Z\<close>
proof (intro modificationI)
  show \<open>compatible X Z\<close>
    using compatible_trans modificationD(1) assms by blast
  fix t assume t: \<open>t \<in> proc_index X\<close>
  have XY: \<open>AE x in proc_source X. process X t x = process Y t x\<close>
    by (fact modificationD(2)[OF assms(1) t])
  have \<open>t \<in> proc_index Y\<close> \<open>proc_source X = proc_source Y\<close>
    using compatible_index compatible_source assms(1) modificationD(1) t by blast+
  then have \<open>AE x in proc_source X. process Y t x = process Z t x\<close>
    using modificationD(2)[OF assms(2)] by presburger
  then show \<open>AE x in proc_source X. process X t x = process Z t x\<close>
    using XY by fastforce
qed

lemma modification_imp_identical_distributions:
  assumes modification: \<open>modification X Y\<close>
    and index: \<open>T \<subseteq> proc_index X\<close>
  shows \<open>distributions X T = distributions Y T\<close>
proof -
  have \<open>proc_source X = proc_source Y\<close>
    using modification by blast
  moreover have \<open>sets (proc_target X) = sets (proc_target Y)\<close>
    using modification by blast
  ultimately have \<open>distr (proc_source X) (proc_target X) (X x) =
         distr (proc_source Y) (proc_target Y) (Y x)\<close>
    if \<open>x \<in> T\<close> for x
    apply (rule distr_cong_AE)
      apply (metis assms modificationD(2) subset_eq that)
     apply simp_all
    done
  then show \<open>?thesis\<close>
    by (auto simp: distributions_altdef cong: PiM_cong)
qed

definition indistinguishable :: \<open>('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool\<close> where
  \<open>indistinguishable X Y \<longleftrightarrow> compatible X Y \<and>
 (\<exists>N \<in> null_sets (proc_source X). \<forall>t \<in> proc_index X. {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N)\<close>

lemma indistinguishableI:
  assumes \<open>compatible X Y\<close> 
    and \<open>\<exists>N \<in> null_sets (proc_source X). (\<forall>t \<in> proc_index X. {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N)\<close>
  shows \<open>indistinguishable X Y\<close>
  unfolding indistinguishable_def using assms by blast

lemma indistinguishable_null_set:
  assumes \<open>indistinguishable X Y\<close>
  obtains N where 
    \<open>N \<in> null_sets (proc_source X)\<close>
    \<open>\<And>t. t \<in> proc_index X \<Longrightarrow> {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N\<close>
  using assms unfolding indistinguishable_def by force

lemma indistinguishableD:
  assumes \<open>indistinguishable X Y\<close>
  shows \<open>compatible X Y\<close>
    and \<open>\<exists>N \<in> null_sets (proc_source X). (\<forall>t \<in> proc_index X. {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N)\<close>
  using assms unfolding indistinguishable_def by blast+

lemma indistinguishable_eq_AE:
  assumes \<open>indistinguishable X Y\<close>
  shows \<open>AE x in proc_source X. \<forall>t \<in> proc_index X. X t x = Y t x\<close>
  using assms[THEN indistinguishableD(2)] by (auto simp add: eventually_ae_filter)

lemma indistinguishable_null_ex:
  assumes \<open>indistinguishable X Y\<close>
  shows \<open>\<exists>N \<in> null_sets (proc_source X). {x \<in> space (proc_source X).\<exists>t \<in> proc_index X. X t x \<noteq> Y t x} \<subseteq> N\<close>
  using indistinguishableD(2)[OF assms] by blast

lemma indistinguishable_refl [simp]: \<open>indistinguishable X X\<close>
  by (auto intro: indistinguishableI)

lemma indistinguishable_sym: \<open>indistinguishable X Y \<Longrightarrow> indistinguishable Y X\<close>
  unfolding indistinguishable_def apply (simp add: compatible_sym)
  by (smt (verit, ccfv_SIG) Collect_cong compatible_index compatible_source indistinguishable_def)

lemma indistinguishable_trans:
  assumes \<open>indistinguishable X Y\<close> \<open>indistinguishable Y Z\<close> 
  shows \<open>indistinguishable X Z\<close>
proof (intro indistinguishableI)
  show \<open>compatible X Z\<close>
    using assms indistinguishableD(1) compatible_trans by blast
  have eq: \<open>proc_index X = proc_index Y\<close> \<open>proc_source X = proc_source Y\<close>
    using compatible_index compatible_source indistinguishableD(1)[OF assms(1)] by blast+
  have \<open>AE x in proc_source X. \<forall>t \<in> proc_index X. X t x = Y t x\<close>
    by (fact indistinguishable_eq_AE[OF assms(1)])
  moreover have \<open>AE x in proc_source X. \<forall>t \<in> proc_index X. Y t x = Z t x\<close>
    apply (subst eq)+
    by (fact indistinguishable_eq_AE[OF assms(2)])
  ultimately have \<open>AE x in proc_source X. \<forall>t \<in> proc_index X. X t x = Z t x\<close>
    using assms by fastforce
  then obtain N where \<open>N \<in> null_sets (proc_source X)\<close> 
    \<open>{x \<in> space (proc_source X).\<exists>t\<in>proc_index X. process X t x \<noteq> process Z t x} \<subseteq> N\<close>
    using eventually_ae_filter by (smt (verit) Collect_cong eventually_ae_filter)
  then show \<open>\<exists>N\<in>null_sets (proc_source X). \<forall>t\<in>proc_index X. {x \<in> space (proc_source X). process X t x \<noteq> process Z t x} \<subseteq> N\<close>
    by blast
qed

lemma indistinguishable_modification: \<open>indistinguishable X Y \<Longrightarrow> modification X Y\<close>
  apply (intro modificationI)
   apply (erule indistinguishableD(1))
  apply (drule indistinguishableD(2))
  using eventually_ae_filter by blast

text \<open> Klenke 21.5(i) \<close>

lemma modification_countable:
  assumes \<open>modification X Y\<close> \<open>countable (proc_index X)\<close>
  shows \<open>indistinguishable X Y\<close>
proof (rule indistinguishableI)
  show \<open>compatible X Y\<close>
    using assms(1) modification_def by auto
  let \<open>?N\<close> = \<open>(\<lambda>t. {x \<in> space (proc_source X). X t x \<noteq> Y t x})\<close>
  from assms(1) have \<open>\<forall>t \<in> proc_index X. AE x in proc_source X. X t x = Y t x\<close>
    unfolding modification_def by argo
  then have \<open>\<And>t. t \<in> proc_index X \<Longrightarrow> \<exists>N \<in> null_sets (proc_source X). ?N t \<subseteq> N\<close>
    by (subst eventually_ae_filter[symmetric], blast)
  then have \<open>\<exists>N. \<forall>t \<in> proc_index X. N t \<in> null_sets (proc_source X) \<and> ?N t \<subseteq> N t\<close>
    by meson
  then obtain N where N: \<open>\<forall>t \<in> proc_index X. (N t) \<in> null_sets (proc_source X) \<and> ?N t \<subseteq> N t\<close>
    by blast
  then have null: \<open>(\<Union>t \<in> proc_index X. N t) \<in> null_sets (proc_source X)\<close>
    by (simp add: null_sets_UN' assms(2))
  moreover have \<open>\<forall>t\<in>proc_index X. ?N t \<subseteq> (\<Union>t \<in> proc_index X. N t)\<close>
    using N by blast 
  ultimately show \<open>\<exists>N\<in> null_sets (proc_source X). (\<forall>t\<in>proc_index X. ?N t \<subseteq> N)\<close>
    by blast
qed

text \<open> Klenke 21.5(ii). The textbook statement is more general - we reduce right continuity to regular continuity \<close>

lemma modification_continuous_indistinguishable:
  fixes X :: \<open>(real, 'a, 'b :: metric_space) stochastic_process\<close>
  assumes modification: \<open>modification X Y\<close>
    and interval: \<open>\<exists>T > 0. proc_index X = {0..T}\<close>
    and rc: \<open>AE \<omega> in proc_source X. continuous_on (proc_index X) (\<lambda>t. X t \<omega>)\<close>
    (is \<open>AE \<omega> in proc_source X. ?cont_X \<omega>\<close>)
    \<open>AE \<omega> in proc_source Y. continuous_on (proc_index Y) (\<lambda>t. Y t \<omega>)\<close>
    (is \<open>AE \<omega> in proc_source Y. ?cont_Y \<omega>\<close>)
  shows \<open>indistinguishable X Y\<close>
proof (rule indistinguishableI)
  show \<open>compatible X Y\<close>
    using modification modification_def by blast
  obtain T where T: \<open>proc_index X = {0..T}\<close> \<open>T > 0\<close>
    using interval by blast
  define N where \<open>N \<equiv> \<lambda>t. {x \<in> space (proc_source X). X t x \<noteq> Y t x}\<close>
  have 1: \<open>\<forall>t \<in> proc_index X. \<exists>S. N t \<subseteq> S \<and> S \<in> null_sets (proc_source X)\<close>
    using modificationD(2)[OF modification] by (auto simp add: N_def eventually_ae_filter)
  text \<open> $S$ is a null set such that $X_t(x) \neq Y_t(x) \Longrightarrow x \in S_t$ \<close>
  obtain S where S: \<open>\<forall>t \<in> proc_index X. N t \<subseteq> S t \<and> S t \<in> null_sets (proc_source X)\<close>
    using bchoice[OF 1] by blast
  have eq: \<open>proc_source X = proc_source Y\<close> \<open>proc_index X = proc_index Y\<close>
    using \<open>compatible X Y\<close> compatible_source compatible_index by blast+
  have \<open>AE p in proc_source X. ?cont_X p \<and> ?cont_Y p\<close>
    apply (rule AE_conjI)
    using eq rc by argo+
  text \<open> $R$ is a set of measure 1 such that if $x \in R$ then the paths at $x$ are continuous for $X$ and $Y$ \<close>
  then obtain R where R: \<open>R \<subseteq> {p \<in> space (proc_source X). ?cont_X p \<and> ?cont_Y p}\<close>
    \<open>R \<in> sets (proc_source X)\<close> \<open>measure (proc_source X) R = 1\<close>
    using proc_source.AE_E_prob by blast
  text \<open> We use an interval of dyadic rationals because we need to produce a countable dense set
  for $\{0..T\}$, which we have by @{thm dyadic_interval_dense}. \<close>
  let \<open>?I\<close> = \<open>dyadic_interval 0 T\<close>
  let \<open>?N'\<close> = \<open>\<Union>n \<in> ?I. N n\<close>
  have N_subset: \<open>\<And>t. t \<in> proc_index X \<Longrightarrow> N t \<inter> R \<subseteq> ?N'\<close>
  proof
    fix t assume \<open>t \<in> proc_index X\<close>
    fix p assume *: \<open>p \<in> N t \<inter> R\<close>
    then obtain \<epsilon> where \<epsilon>: \<open>0 < \<epsilon>\<close> \<open>\<epsilon> = dist (X t p) (Y t p)\<close>
      by (simp add: N_def)
    have cont_p: \<open>continuous_on {0..T} (\<lambda>t. Y t p)\<close> \<open>continuous_on {0..T} (\<lambda>t. X t p)\<close>
      using R *(1) T(1)[symmetric] eq(2) by auto
    then have continuous_dist: \<open>continuous_on {0..T} (\<lambda>t. dist (X t p) (Y t p))\<close>
      using continuous_on_dist by fast
    {
      assume \<open>\<forall>r\<in> ?I. X r p = Y r p\<close>
      then have dist_0: \<open>\<And>r. r \<in> ?I \<Longrightarrow> dist (X r p) (Y r p) = 0\<close>
        by auto
      have \<open>dist (X t p) (Y t p) = 0\<close>
      proof -
        have dist_tendsto_0: \<open>((\<lambda>t. dist (X t p) (Y t p)) \<longlongrightarrow> 0)(at t within ?I)\<close>
          using dist_0 continuous_dist
          by (smt (verit, best) Lim_transform_within \<epsilon> tendsto_const)
        have XY: \<open>((\<lambda>t. X t p) \<longlongrightarrow> X t p)(at t within ?I)\<close> \<open>((\<lambda>t. Y t p) \<longlongrightarrow> Y t p)(at t within ?I)\<close>
          by (metis cont_p T(1) \<open>t \<in> proc_index X\<close> continuous_on_def tendsto_within_subset dyadic_interval_subset_interval)+
        show \<open>?thesis\<close>
          apply (rule tendsto_unique[of \<open>at t within ?I\<close>])
            apply (simp add: trivial_limit_within)
            apply (metis T(1) T(2) \<open>t \<in> proc_index X\<close> dyadic_interval_dense islimpt_Icc limpt_of_closure)
          using tendsto_dist[OF XY] dist_tendsto_0 
          by simp_all
      qed
      then have \<open>False\<close>
        using \<epsilon> by force
    }
    then have \<open>\<exists>r\<in>dyadic_interval 0 T. p \<in> N r\<close>
      unfolding N_def using * R(2) sets.sets_into_space by auto
    then show \<open>p \<in> \<Union> (N ` ?I)\<close>
      by simp
  qed
  have null: \<open>(space (proc_source X) - R) \<union> (\<Union>r \<in> ?I. S r) \<in> null_sets (proc_source X)\<close>
    apply (rule null_sets.Un)
     apply (smt (verit) R(2,3) AE_iff_null_sets proc_source.prob_compl proc_source.prob_eq_0 sets.Diff sets.top)
    by (metis (no_types, lifting) S T(1) dyadic_interval_countable dyadic_interval_subset_interval in_mono null_sets_UN')
  have \<open>(\<Union>r \<in> proc_index X. N r) \<subseteq> (space (proc_source X) - R) \<union> (\<Union>r \<in> proc_index X. N r)\<close>
    by blast
  also have \<open>... \<subseteq> (space (proc_source X) - R) \<union> (\<Union>r \<in> ?I. N r)\<close>
    using N_subset N_def by blast
  also have \<open>... \<subseteq> (space (proc_source X) - R) \<union> (\<Union>r \<in> ?I. S r)\<close>
    by (smt (verit, ccfv_threshold)S T(1) UN_iff Un_iff dyadic_interval_subset_interval in_mono subsetI)
  finally show \<open>\<exists>N\<in>null_sets (proc_source X). \<forall>t\<in>proc_index X. {x \<in> space (proc_source X). process X t x \<noteq> process Y t x} \<subseteq> N\<close>
    by (smt (verit) N_def null S SUP_le_iff order_trans)
qed

lift_definition restrict_index :: \<open>('t, 'a, 'b) stochastic_process \<Rightarrow> 't set \<Rightarrow> ('t, 'a, 'b) stochastic_process\<close>
  is \<open>\<lambda>(M, M', I, X) T. (M, M', T, X)\<close> by fast

lemma
  shows
    restrict_index_source[simp]: \<open>proc_source (restrict_index X T) = proc_source X\<close> and
    restrict_index_target[simp]: \<open>proc_target (restrict_index X T) = proc_target X\<close> and
    restrict_index_index[simp]:  \<open>proc_index (restrict_index X T) = T\<close> and
    restrict_index_process[simp]: \<open>process (restrict_index X T) = process X\<close>
  by (transfer, force)+

lemma restrict_index_override[simp]: \<open>restrict_index (restrict_index X T) S = restrict_index X S\<close>
  by (transfer, auto)

lemma compatible_restrict_index:
  assumes \<open>compatible X Y\<close>
  shows \<open>compatible (restrict_index X S) (restrict_index Y S)\<close>
  using assms unfolding compatible_def by (transfer, auto)

lemma modification_restrict_index:
  assumes \<open>modification X Y\<close> \<open>S \<subseteq> proc_index X\<close>
  shows \<open>modification (restrict_index X S) (restrict_index Y S)\<close>
  using assms unfolding modification_def
  apply (simp add: compatible_restrict_index)
  apply (metis restrict_index_source subsetD)
  done

lemma indistinguishable_restrict_index:
  assumes \<open>indistinguishable X Y\<close> \<open>S \<subseteq> proc_index X\<close>
  shows \<open>indistinguishable (restrict_index X S) (restrict_index Y S)\<close>
  using assms unfolding indistinguishable_def by (auto simp: compatible_restrict_index)

lemma AE_eq_minus [intro]:
  fixes a :: \<open>'a \<Rightarrow> ('b :: real_normed_vector)\<close>
  assumes \<open>AE x in M. a x = b x\<close> \<open>AE x in M. c x = d x\<close>
  shows \<open>AE x in M. a x - c x = b x - d x\<close>
  using assms by fastforce

lemma modification_indep_increments:
  fixes X Y :: \<open>('a :: linorder, 'b, 'c :: {second_countable_topology, real_normed_vector}) stochastic_process\<close>
  assumes \<open>modification X Y\<close> \<open>sets (proc_target Y) = sets borel\<close>
  shows \<open>indep_increments X \<Longrightarrow> indep_increments Y\<close>
proof (intro indep_incrementsI, subst proc_source.indep_vars_iff_distr_eq_PiM, goal_cases)
  case (1 l)
  then show \<open>?case\<close> by simp
next
  case (2 l i)
  then show \<open>?case\<close>
    using assms apply measurable
    using modificationD(1)[OF assms(1), THEN compatible_source] assms(2)
    by (metis measurable_cong_sets random_process)+
next
  case (3 l)
  have target_X [measurable]: \<open>sets (proc_target X) = sets borel\<close>
    using assms by auto
  then have measurable_target: \<open>f \<in> M \<rightarrow>\<^sub>M proc_target X = (f \<in> borel_measurable M)\<close> for f and M :: \<open>'b measure\<close>
    using measurable_cong_sets by blast
  have \<open>AE \<omega> in proc_source X. X (l ! i) \<omega> = Y (l ! i) \<omega>\<close>
    if \<open>i \<in> {0..<length l}\<close> for i
    apply (rule assms(1)[THEN modificationD(2)])
    by (metis 3(2) that assms(1) atLeastLessThan_iff basic_trans_rules(31) 
        compatible_index modificationD(1) nth_mem)
  then have AE_eq: \<open>AE \<omega> in proc_source X. X (l!i) \<omega> - X (l!(i-1)) \<omega> = Y (l!i) \<omega> - Y (l!(i-1)) \<omega>\<close>
    if \<open>i \<in> {1..<length l}\<close> for i
    using AE_eq_minus that by auto
  have AE_eq': \<open>AE x in proc_source X. (\<lambda>i\<in>{1..<length l}. X (l ! i) x - X (l ! (i - 1)) x) = 
        (\<lambda>i\<in>{1..<length l}. Y (l ! i) x - Y (l ! (i - 1)) x)\<close>
  proof (rule AE_mp)
    show \<open>AE \<omega> in proc_source X. \<forall>i \<in>{1..<length l}. X (l!i) \<omega> - X (l!(i-1)) \<omega> = Y (l!i) \<omega> - Y (l!(i-1)) \<omega>\<close>
    proof -
      {
        fix i assume *: \<open>i \<in> {1..<length l}\<close>
        obtain N where 
          \<open>{\<omega> \<in> space (proc_source X). X (l!i) \<omega> - X (l!(i-1)) \<omega> \<noteq> Y (l!i) \<omega> - Y (l!(i-1)) \<omega>} \<subseteq> N\<close>
          \<open>N \<in> proc_source X\<close> \<open>emeasure (proc_source X) N = 0\<close>
          using AE_eq[OF *, THEN AE_E] .
        then have \<open>\<exists>N \<in> null_sets (proc_source X).
         {\<omega> \<in> space (proc_source X). X (l!i) \<omega> - X (l!(i-1)) \<omega> \<noteq> Y (l!i) \<omega> - Y (l!(i-1)) \<omega>} \<subseteq> N\<close>
          by blast
      } then obtain N where N: \<open>N i \<in> null_sets (proc_source X)\<close>
        \<open>{\<omega> \<in> space (proc_source X). X (l!i) \<omega> - X (l!(i-1)) \<omega> \<noteq> Y (l!i) \<omega> - Y (l!(i-1)) \<omega>} \<subseteq> N i\<close>
      if \<open>i \<in> {1..< length l}\<close> for i
        by (metis (lifting) ext)
      have \<open>{\<omega> \<in> space (proc_source X). \<not> (\<forall>i\<in>{1..<length l}. X (l ! i) \<omega> - X (l ! (i - 1)) \<omega> = Y (l ! i) \<omega> - Y (l ! (i - 1)) \<omega>)} \<subseteq> (\<Union> i \<in> {1..< length l}. N i)\<close>
        using N by blast
      moreover have \<open>(\<Union>i \<in> {1..< length l}. N i) \<in> null_sets (proc_source X)\<close>
        apply (rule null_sets.finite_UN)
        using 3 N by simp_all
      ultimately show \<open>?thesis\<close>
        by (blast intro: AE_I)
    qed
    show \<open>AE x in proc_source
             X. (\<forall>i\<in>{1..<length l}. process X (l ! i) x - process X (l ! (i - 1)) x = process Y (l ! i) x - process Y (l ! (i - 1)) x) \<longrightarrow>
                (\<lambda>i\<in>{1..<length l}. process X (l ! i) x - process X (l ! (i - 1)) x) = (\<lambda>i\<in>{1..<length l}. process Y (l ! i) x - process Y (l ! (i - 1)) x)\<close>
      by (rule AE_I2, auto)
  qed                                            
  have \<open>distr (proc_source Y) (Pi\<^sub>M {1..<length l} (\<lambda>i. proc_target Y))
                (\<lambda>x. \<lambda>i\<in>{1..<length l}. Y (l ! i) x - Y (l ! (i - 1)) x) =
            distr (proc_source X) (Pi\<^sub>M {1..<length l} (\<lambda>i. proc_target X))
              (\<lambda>x. \<lambda>i\<in>{1..<length l}. X (l ! i) x - X (l ! (i - 1)) x)\<close>
    apply (rule sym)
    apply (rule distr_cong_AE)
    using assms(1) apply blast
       apply (metis assms(2) sets_PiM_cong target_X)
      apply (fact AE_eq')
     apply simp
     apply (rule measurable_restrict)
     apply (simp add: measurable_target)
    subgoal by measurable (meson measurable_target random_process)+
    apply (rule measurable_restrict)
    by (metis (full_types) assms(2) borel_measurable_diff measurable_cong_sets stochastic_process_measurable)
  also have \<open>... = Pi\<^sub>M {1..<length l} (\<lambda>i. distr (proc_source X) (proc_target X) (\<lambda>v. X (l ! i) v - X (l ! (i - 1)) v))\<close>
    apply (subst proc_source.indep_vars_iff_distr_eq_PiM[symmetric])
    subgoal using 3 by simp
     apply simp
     apply (metis (full_types) borel_measurable_diff measurable_cong_sets stochastic_process_measurable target_X)
    apply (rule indep_incrementsE)
     apply (fact 3(1))
    using 3(2-) assms(1) by blast
  also have \<open>... = Pi\<^sub>M {1..<length l} (\<lambda>i. distr (proc_source Y) (proc_target Y) (\<lambda>v. Y (l ! i) v - Y (l ! (i - 1)) v))\<close>
    apply (safe intro!: PiM_cong)
    apply (rule distr_cong_AE)
    subgoal using assms(1) by blast
    subgoal using assms(1) by blast
    subgoal using AE_eq by presburger
    subgoal by (metis (mono_tags) borel_measurable_diff measurable_target random_process)
    by (metis (full_types) assms(2) borel_measurable_diff measurable_cong_sets random_process)
  finally show \<open>?case\<close> .
qed

end
