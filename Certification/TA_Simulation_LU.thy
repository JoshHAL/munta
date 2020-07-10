theory TA_Simulation_LU
  imports TA_Simulation
begin

text\<open>Shouldn't we also assume L(v' 0) = \<infinity>\<close>
locale TA_LU2 =
  Regions_TA where A = A +
  TA_LU where A = A and L = L and U = U
  for A  :: "('a, 'c, real, 'l) ta" and L :: "'l \<Rightarrow> 'c \<Rightarrow> nat" and U :: "'l \<Rightarrow> 'c \<Rightarrow> nat" +
  assumes X_is_clk_set: "X = clk_set A"
begin

abbreviation zone_of ("\<lbrakk>_\<rbrakk>") where "zone_of M \<equiv> [M]\<^bsub>v,n\<^esub>"

term "dbm_nonneg"

definition lu_apx where
  "lu_apx l M = extra_lu M (\<lambda>x. real (L l (v' x))) (\<lambda>x. real (U l (v' x))) n"


text\<open>
This is Lemma 8 from @{cite "BehrmannBLP06"}.
Probably we need to specify that i,j <= n
Maybe we should use v' which gives us a clock for the dbm entry but would it actually matter?
Steps
General we now lb = 0
case 1: v x = 0 \<longrightarrow> ub = 0 --> ?
case 2: v x > 0
  --> ub = l (v x) und 
norm_lower (norm_upper (M (v x) 0) ub) lb = \infty
--> norm_upper (M (v x) 0) ub < lb, denn upper wird nur infty wenn bereits infty
\<close>


definition lt_as_bound:: "'t::time DBMEntry \<Rightarrow> 't::time \<Rightarrow> bool" where
  "lt_as_bound x a \<equiv> x \<prec> Le a \<and> x \<prec> Lt a"


lemma lt_is_enough: 
  assumes "x \<prec> Lt a"
  shows "lt_as_bound x a"
    unfolding lt_as_bound_def
    using assms aux_3 by blast

lemma norm_lower_pres_ninf:
  assumes "norm_lower e t = DBM.INF"
  shows "e = DBM.INF"
  using assms by(cases "e \<prec> Lt t"; auto)

lemma norm_upper_infinty:
  assumes "norm_upper e t = DBM.INF"
  shows "Le t \<prec> e"
  using assms by(cases "Le t \<prec> e"; auto)

lemma Lemma8_j_bigger_zero:
  assumes bounded:"vabstr' Z M"
  and j_n: "j \<le> n \<and> j > 0"
  and l_inf:"M j 0 < DBM.INF"
  and eq_inf:"(lu_apx l M) j 0 = DBM.INF"
shows "\<not> (lt_as_bound (M j 0) (L l (v' j))) "
proof -
  let ?x = "v' j"
  and ?M_lu = "(lu_apx l M)"
  have not_inf:"(M j 0) \<noteq> DBM.INF" using l_inf by simp
  have j_le_n: "j \<le> n" using j_n by simp
  have j_not_0:"j \<noteq> 0" using j_n by simp
  hence n_not_0: "0 < n" using j_n by simp
  have "?M_lu j 0 = norm_lower (norm_upper (M j 0) (real (L l ?x))) 0"
    unfolding lu_apx_def extra_lu_def Let_def
    by (simp add: n_not_0 j_le_n j_not_0)  
  hence "DBM.INF = norm_lower (norm_upper (M j 0) (real (L l ?x))) 0"
    using eq_inf by simp
  hence "norm_upper (M j 0) (real (L l ?x)) = DBM.INF" 
    using norm_lower_pres_ninf[of "(norm_upper (M j 0) (real (L l ?x)))" "0"]
    by simp
  hence le:"Le (L l ?x) \<prec> M j 0"
    using norm_upper_infinty[of "(M j 0)" "(real (L l ?x))"] by fast
  hence lt:"Lt (L l ?x) \<prec> (M j 0)"
    using linordered_monoid.dual_order.strict_trans by blast
  hence "\<not> lt_as_bound (M j 0) (L l ?x)" using le
    using Le_Lt_dbm_lt_D not_inf
  proof (cases "M j 0")
    case (Le x1)
    then show ?thesis unfolding lt_as_bound_def 
      using le lt by auto
  next
    case (Lt x2)
    then show ?thesis unfolding lt_as_bound_def 
      using le lt by auto
  next
    case INF
    then show ?thesis 
    using not_inf by blast
qed
  thus  ?thesis by auto
qed


text\<open>Not sure whether this is what we want, maybe we should say: 
         M 0 i < Le u \<and> M 0 i < Lt u
      Analog in Lemma8\<close>
lemma Lemma9:
  assumes Hyp: "vabstr' Z M"
  and zero_i_n:"i \<le> n \<and> 0 < i"
  and "M 0 i \<noteq> (lu_apx l M) 0 i"
shows "lt_as_bound (M 0 i) (- U l (v' i))"
(*       "M_lu 0 i = Lt (- U l (v' i))" *)
proof -
  let ?x = "v' i"
  have i_le_n: "i \<le> n" using zero_i_n by simp
  have i_not_0:"i \<noteq> 0" using zero_i_n by simp
  hence n_not_0: "0 < n" using zero_i_n by simp
  hence base:"(lu_apx l M) 0 i = norm_lower (norm_upper (M 0 i) 0) 
                               (- (real  (U l ?x)))"
    unfolding lu_apx_def extra_lu_def Let_def
    using i_le_n i_not_0 n_not_0
    by simp
  have \<bullet>:"lt_as_bound (M 0 i) (- U l (v' i))" 
  proof (cases "(lu_apx l M) 0 i")
    case (Le x1)
    hence upper:
      "Le x1 = norm_lower (norm_upper (M 0 i) 0) 
                          (- (real  (U l ?x)))"
       using base
       by simp
     hence "Le x1 = norm_upper (M 0 i) 0"
       by fastforce
     hence extra_eq_bf:"Le x1 = M 0 i"
       by fastforce
     hence "M 0 i \<prec> Lt (- (real  (U l ?x)))"
       using upper
       using Le assms(3) by auto
    then show ?thesis
      using Le extra_eq_bf assms(3) by auto
  next
    case (Lt x2)
    hence \<star>:"Lt x2 = norm_lower (norm_upper (M 0 i) 0) 
                               (- (real  (U l ?x)))"
      using base by simp
    hence
      \<box>:"(x2 = (- (real  (U l ?x))) \<and> M 0 i \<prec> Lt x2 ) \<or> 
       Lt x2 = M 0 i"
      by auto
    consider 
     (up) "x2 = (- (real  (U l ?x)))\<and> M 0 i \<prec> Lt x2" 
   | (eq) "Lt x2 = M 0 i"
      using \<box> \<star>
      by force
    then show ?thesis
    proof cases
      case up
      hence "M 0 i \<prec> Lt (- (real  (U l ?x)))" 
        by blast
      thus ?thesis using lt_is_enough
        by auto
    next
      case eq
      then show ?thesis
        using Lt assms(3) by auto
    qed
  next
    case INF
    hence \<star>:"M 0 i = DBM.INF \<or> Le 0 \<prec> M 0 i"
      using base norm_lower_pres_ninf norm_upper_infinty 
      by auto
    consider (inf) "M 0 i = DBM.INF" |
             (lt) "Le 0 \<prec> M 0 i"
      using \<star>
      by blast
    then show ?thesis
    proof cases
      case inf
      then show ?thesis
        using INF assms(3) by auto
    next
      case lt
      have "dbm_nonneg n M" using assms(1)
        unfolding canonical_dbm_def
        by simp
      hence "dbm_le (M 0 i) (Le 0)" 
        unfolding dbm_nonneg_def
        using zero_i_n
        by (simp add: DBM.less_eq neutral)
      hence "M 0 i = Le 0" using lt by simp
      then show  ?thesis
        using lt by auto
    qed
  qed
  thus ?thesis by simp
qed

text\<open>Should also be possible without 0 < i\<close>
lemma helper_10i:
  assumes "u \<in> \<lbrakk>lu_apx l D\<rbrakk>"
  and "\<not> Le (L l (v' i)) \<prec> (D i 0)"
  and "i \<le> n"
  and "0 < i"
  and "vabstr' Z D"
shows "(lu_apx l D) i 0 = D i 0"
proof(cases "D i 0 \<prec> Lt 0")
  case True
  hence *:"(lu_apx l D) i 0 = norm_lower (D i 0) 0"
    unfolding lu_apx_def extra_lu_def Let_def
    using assms True
    by auto
  then show ?thesis
  proof(cases "D i 0 \<prec> Lt 0")
    case True
    have **:"D 0 i \<le> 0" using assms
      unfolding canonical_dbm_def dbm_nonneg_def
      by blast
    have "D i 0 \<prec> Le 0" 
      using True linordered_monoid.dual_order.strict_trans
      by blast
    hence "D i 0 < 0"
      by (simp add: less neutral)
    hence ***:"D 0 i + D i 0 < 0"
      using ** add_nonpos_neg less neutral by blast
    have "canonical D n" using assms 
      unfolding canonical_dbm_def
      by simp
    hence "D 0 0 < 0" using  assms(1-3) ***
      by force
    hence "D 0 0 \<prec> Le 0"
      by (simp add: less neutral)
    hence "(lu_apx l D) 0 0 = Lt 0" 
        unfolding lu_apx_def extra_lu_def Let_def 
                  norm_diag_def
        by simp
    hence "\<lbrakk>lu_apx l D\<rbrakk> = {}"
      unfolding DBM_zone_repr_def DBM_val_bounded_def dbm_le_def
      by (force; blast)
    then show ?thesis using assms by simp
  next
    case False
    then show ?thesis using * by simp
qed
next
  case False
  then show ?thesis 
    unfolding lu_apx_def extra_lu_def Let_def
    using assms
    by simp
qed



lemma Lemma10_i:
  assumes "u \<in> \<lbrakk>lu_apx l D\<rbrakk>"
  and "i \<le> n"
  and "i > 0"
  and "u (v' i) \<le> min (U l (v' i)) (L l (v' i))"
  and "vabstr' Z D"
shows "Le (u (v' i)) \<le> (D i 0)"
proof -
let ?x = "v' i"
  let ?L = "(L l ?x)"
  have clock_num:"v ?x = i"
    using assms(2) assms(3) clock_numbering(2) v_v' by auto
  hence x_i_less_n: "v ?x \<le> n" using assms by argo
  consider (gt) "D i 0 > Le ?L" | (le) "D i 0 \<le> Le ?L"
    by fastforce
  then show ?thesis
    proof cases
      case gt
      hence "Le (u ?x) < D i 0" using assms
        by (cases "D i 0"; simp)
    then show ?thesis by simp
    next
      case le
      hence "\<not> Le ?L \<prec> D i 0"
      using le less not_le
      by metis
    hence "(lu_apx l D) i 0 = D i 0" using assms helper_10i
      by blast
    hence "dbm_entry_val u (Some ?x) None (D i 0)"
      using assms(1) unfolding DBM_zone_repr_def DBM_val_bounded_def
      using x_i_less_n clock_num
      by fastforce
    hence "Le (u ?x) \<le> D i 0" using clock_num
      by (cases "D i 0"; force+)
    then show ?thesis using le
      by fastforce
    qed
qed


lemma Lemma10_ii:
  assumes "u \<in> \<lbrakk>lu_apx l D\<rbrakk>"
  and "u (v' i) \<le> min (U l (v' i)) (L l (v' i))"
shows "(Le (- u (v' i))) \<prec> (D 0 i)"
  sorry

lemma Theorem_Bouyer: assumes Hyp:"vabstr' Z M"
  assumes "M_lu = lu_apx l M"
  shows 
    "\<lbrakk>M_lu\<rbrakk> \<subseteq> local.abs l Z"
proof
  fix u
  assume "u \<in> \<lbrakk>M_lu\<rbrakk>"
  hence "u \<turnstile>\<^bsub>v,n\<^esub> M_lu" using assms unfolding Zones.DBM_zone_repr_def by simp
 (*  hence "x \<turnstile>\<^bsub>v,n\<^esub> M" *)
  hence "\<exists>u' \<in> Z. sim (l,u) (l,u')" sorry
  thus "u \<in> abs l Z" unfolding abs_def by simp
qed

interpretation extra: TA_Extrapolation where
  A = A and
  extra = "lu_apx" and
  sim = sim
  apply standard
  subgoal \<comment> \<open>Only non-negative clock valuations are simulated\<close>
    unfolding V_def unfolding X_is_clk_set by (auto simp: img_fst sim_nonneg)
  subgoal for Z M l \<comment> \<open>@{term extra_lu} extrapolates\<close>
    using clock_numbering(1) unfolding lu_apx_def by (auto intro: extra_lu_mono)
  subgoal for Z M l \<comment> \<open>The key property\<close>
    using Theorem_Bouyer by simp
  subgoal \<comment> \<open>Finite Extrapolation\<close>
    using extra_lu_finite \<comment> \<open>XXX: Does not quite fit yet\<close>
    sorry
  subgoal \<comment> \<open>Extrapolation keeps DBMs integral\<close>
    unfolding lu_apx_def by (intro extra_lu_preservation) auto
  \<comment> \<open>Properties of the starting state. Don't care for now, not instantiated.\<close>
  sorry

end

end