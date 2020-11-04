theory TA_Simulation_LU
  imports TA_Simulation
begin


locale TA_LU2 =
  Regions_TA where A = A +
  TA_LU where A = A and L = L and U = U
  for A  :: "('a, 'c, real, 'l) ta" and L :: "'l \<Rightarrow> 'c \<Rightarrow> nat" and U :: "'l \<Rightarrow> 'c \<Rightarrow> nat" +
  assumes X_is_clk_set: "X = clk_set A"
begin

abbreviation zone_of ("\<lbrakk>_\<rbrakk>") where "zone_of M \<equiv> [M]\<^bsub>v,n\<^esub>"

lemma clock_numbering_alt:
  "\<forall>c. v c \<le> n \<longrightarrow> 0 < v c"
  using clock_numbering(1) by blast

definition lu_apx where
  "lu_apx l M = extra_lu M (\<lambda>x. real (L l (v' x))) (\<lambda>x. real (U l (v' x))) n"

lemma norm_lower_pres_ninf:
  assumes "norm_lower e t = DBM.INF"
  shows "e = DBM.INF"
  using assms
  by(cases "e \<prec> Lt t"; auto) 

lemma norm_upper_infinity:
  assumes "norm_upper e t = DBM.INF"
  shows "Le t \<prec> e"
  using assms by(cases "Le t \<prec> e"; auto)

text\<open>Overall Procedure:

We prove the Lemmata 9 - 10 from @{cite "BehrmannBLP06"}
Afterwards we Construct a DBM u_dbm D out of some
u \<in> \<lbrakk>lu_apx l D\<rbrakk>
such that its zone representation
is u \<in> abs l Z, if \<lbrakk>u_dbm D\<rbrakk> \<noteq> \<emptyset>.
For this we do several things:
1. We open a context to fix u and ease the construction of P
2. In this context we first show that \<lbrakk>u_dbm D\<rbrakk> \<subseteq> abs l Z

3. Finally we show that \<lbrakk>u_dbm D\<rbrakk> cannot be empty and therefore \<lbrakk>lu_apx l M\<rbrakk> \<subseteq> local.abs l Z
  - This was more complicated than in the Paper
  - We needed to proof that u_dbm D 0 i + u_dbm D i 0 \<ge> Le 0
  - From this and under the assumption that \<lbrakk>u_dbm D\<rbrakk> = \<emptyset> we can prove that 
    \<exists> i \<noteq> j \<in> {1..n}. u_dbm D 0 i + D i j + u_dbm D j 0 < 0
    which results in a contradiction thus \<lbrakk>u_dbm D\<rbrakk> \<noteq> \<emptyset>.
\<close>


lemma case_zone_repr_empty:
  assumes "vabstr' {} M"
  shows "\<lbrakk>lu_apx l M\<rbrakk> = {}"
proof(rule ccontr)
  assume contr_assms:"\<lbrakk>lu_apx l M\<rbrakk> \<noteq> {}"
  have M_canonical:
    "canonical M n" 
    using assms
    unfolding canonical_dbm_def 
    by blast
  have neg_diag:"\<exists>i \<le> n. M i i < 0" 
    using clock_numbering(2) clock_numbering_alt assms
        M_canonical
        X_is_clk_set
        canonical_empty_zone[of n v M]
    by blast
  obtain i where i_le_n:"i\<le> n" and D_ii_neg:"M i i < 0"
    using neg_diag by blast
  have "lu_apx l M i i = norm_diag (M i i)"
    unfolding lu_apx_def extra_lu_def
    using i_le_n
    by presburger
  hence "lu_apx l M i i = Lt 0"
    unfolding norm_diag_def
    using D_ii_neg less
    by (simp add: less neutral)
  hence "lu_apx l M i i < 0"
    by (simp add: neutral)
  hence "\<exists> i \<le> n. lu_apx l M i i < 0"
    using i_le_n
    by blast
  hence "\<lbrakk>lu_apx l M\<rbrakk> = {}"
    using negative_diag_empty[of "lu_apx l M"]
    by argo
  thus "False"  using contr_assms
    by blast
qed

text\<open>Context for u_dbm D\<close>
context
  fixes l::'l
  fixes u::"('c,real) cval"
  fixes D::"real DBM"
  fixes Z
  assumes vabs:"vabstr' Z D"
  and D_zone_repr_non_empty: "Z \<noteq> {}"
  and u_apx:"u \<in> \<lbrakk>lu_apx l D\<rbrakk>"
begin

section Setup

lemma D_zone_repr_non_empty_alt:
  "\<lbrakk>D\<rbrakk> \<noteq> {}"
  using vabs D_zone_repr_non_empty
  by blast

lemma u_dbm_entry_val:
  assumes "j \<le> n" and "0 < j"
  shows "dbm_entry_val u None (Some (v' j)) (lu_apx l D 0 j)"
        "dbm_entry_val u (Some (v' j)) None (lu_apx l D j 0)"
  subgoal
  proof -
  have id_v_v':"v (v' j) = j" using clock_numbering assms v_v'
    by auto
  hence "v (v' j) \<le> n" using assms
    by argo
  hence "dbm_entry_val u None (Some (v' j)) (lu_apx l D 0 (v (v' j)))"
    using u_apx unfolding DBM_zone_repr_def DBM_val_bounded_def
    by fast
  thus ?thesis using id_v_v'
    by argo
qed
proof -
  have id_v_v':"v (v' j) = j" using clock_numbering assms v_v'
    by auto
  hence "v (v' j) \<le> n" using assms
    by argo
  hence "dbm_entry_val u (Some (v' j)) None (lu_apx l D (v (v' j)) 0)"
    using u_apx unfolding DBM_zone_repr_def DBM_val_bounded_def
    by fast
  thus "dbm_entry_val u (Some (v' j)) None (lu_apx l D j 0)" using id_v_v'
    by argo
qed

lemma u_dbm_entry_val_3:
  assumes "i \<in> {1..n} \<and> j \<in> {1..n}"
  shows "dbm_entry_val u (Some (v' i)) (Some (v' j)) (lu_apx l D i j)"
proof -
  have v_id:"v (v' i) = i \<and> v (v' j) = j"
    using assms
    using clock_numbering(2) v_v' by auto
  have "i \<le> n \<and> j \<le> n" using assms
    by auto
  hence "v (v' i) \<le> n \<and> v (v' j) \<le> n" 
    using v_id assms
    by argo
  hence "dbm_entry_val u (Some (v' i)) (Some (v' j)) (lu_apx l D (v (v' i)) (v (v' j)))"
    using u_apx unfolding DBM_zone_repr_def DBM_val_bounded_def
    by blast
  thus ?thesis using v_id
    by argo
qed


lemma D_canonical_dbm:
   "canonical_dbm D" 
  using vabs
  by blast

lemma D_nonneg:
  "dbm_nonneg n D"
  using D_canonical_dbm unfolding canonical_dbm_def
  by argo

lemma D_canonical: "canonical D n"
  using D_canonical_dbm unfolding canonical_dbm_def
  by argo

lemma D_cycle_free:
  "cycle_free D n"
  using D_zone_repr_non_empty_alt clock_numbering(2) non_empty_cycle_free
  by fast

lemma D_cyc_free:
  "cyc_free D n"
  using D_cycle_free cycle_free_diag_equiv
  by blast

lemma path_ge_zero:
  assumes "j \<le> n"
  and "0 < j"
  shows "0 \<le> D 0 j + D j 0"
proof -
  have lt_D00:"D 0 0 \<le> D 0 j + D j 0" using D_canonical assms
    by blast
  have "0 \<le> D 0 0" 
    using D_canonical_dbm D_zone_repr_non_empty_alt 
          D_cycle_free cycle_free_0_0 
    by blast
  thus ?thesis using lt_D00 by simp
qed

lemma D_zero_clock_ge_zero:
  "D 0 0 \<ge> 0"
  using D_cycle_free cycle_free_0_0 by blast

lemma D_through_zero:
  assumes "j \<le> n"
  shows "D 0 j + D j 0 \<ge> 0"
  using assms D_canonical D_zero_clock_ge_zero
  by force

text\<open>Wrappers for valuation u and the Lower and Upperbounds\<close>

definition u_i
  where "u_i i \<equiv> u (v' i)"

definition L'
  where "L' i \<equiv> real (L l (v' i))"

definition U'
  where "U' i \<equiv> real (U l (v' i))"

lemma bound_ge_zero:
  assumes "j \<le> n"
  and "0 < j"
  shows "u_i j \<ge> 0"
proof -
  have bound:"dbm_entry_val u None (Some (v' j)) (lu_apx l D 0 j)"
    using u_dbm_entry_val[of j] assms
    by fast
  have "dbm_nonneg n D" 
    using D_canonical_dbm
    unfolding canonical_dbm_def
    by blast
  hence le_zero:"lu_apx l D 0 j \<le> 0" 
    unfolding lu_apx_def
    dbm_nonneg_def
    using D_canonical extra_lu_lower_bounds[of n D "\<lambda>x. real (U l (v' x))" "\<lambda>x. real (L l (v' x))"]
    by (simp add: assms(1) assms(2))
  hence bound_le_zero:"dbm_entry_bound (lu_apx l D 0 j) \<le> 0"
    by(cases "lu_apx l D 0 j";auto;(simp add: neutral)+)
  have not_infinity:"lu_apx l D 0 j \<noteq> DBM.INF"
    using le_zero
    by (metis dbm_less_simps(2) neutral not_le)
    have "- u (v' j) \<le> dbm_entry_bound (lu_apx l D 0 j)"
    using bound not_infinity
    by(cases "lu_apx l D 0 j"; auto simp: bound)
  hence "u (v' j) \<ge> 0" 
    using bound_le_zero
    by linarith
  thus ?thesis unfolding u_i_def by argo
qed

section \<open>Lemmata 9 - 10\<close>

text\<open> Lemma 9 from the Paper\<close>
lemma Lemma9:
  assumes i_le_n:"i \<le> n"
  and i_gt_zero: "0 < i"
  and "D 0 i \<noteq> (lu_apx l D) 0 i"
shows "(D 0 i) \<prec> Lt (- U' i) 
    \<and> lu_apx l D 0 i = Lt (- U' i)"
proof -
  let ?x = "v' i"
  have base:"(lu_apx l D) 0 i = norm_lower (norm_upper (D 0 i) 0) 
                               (- (U l ?x))"
    unfolding lu_apx_def extra_lu_def Let_def
    using i_le_n i_gt_zero
    by force
  show ?thesis
  proof (cases "(lu_apx l D) 0 i")
    case (Le x1)
     have "Le x1 = norm_upper (D 0 i) 0"
       using base Le
       by fastforce
     hence "Le x1 = D 0 i"
       by fastforce
     thus ?thesis
      using Le assms by fastforce
  next
    case (Lt x2)
    hence \<star>:"Lt x2 = norm_lower (norm_upper (D 0 i) 0) 
                               (- (U l ?x))"
      using base by simp
    hence
      \<box>:"x2 = (- (U l ?x)) \<and> D 0 i \<prec> Lt x2 
         \<or> Lt x2 = D 0 i"
      by auto
    consider 
     (up) "x2 = (- (U l ?x)) \<and> D 0 i \<prec> Lt x2" 
   | (eq) "Lt x2 = D 0 i"
      using \<box> \<star>
      by force
    then show ?thesis
    proof cases
      case up
      hence *:"D 0 i \<prec> Lt (- (U l ?x))" 
        by blast
      have "Lt x2 = Lt (- (U l (v' i)))"
        using up
        by blast
      thus ?thesis 
        using Lt * 
        unfolding U'_def
        by auto
    next
      case eq
      then show ?thesis
        using Lt assms by auto
    qed
  next
    case INF
    hence \<star>:"D 0 i = DBM.INF \<or> Le 0 \<prec> D 0 i"
      using base norm_lower_pres_ninf norm_upper_infinity 
      by auto
    consider (inf) "D 0 i = DBM.INF" |
             (lt) "Le 0 \<prec> D 0 i"
      using \<star>
      by blast
    then show ?thesis
    proof cases
      case inf
      then show ?thesis
        using INF assms by auto
    next
      case lt
      hence "dbm_le (D 0 i) (Le 0)"
        using D_nonneg
        unfolding dbm_nonneg_def
        using i_le_n i_gt_zero       
        by (simp add: DBM.less_eq neutral)
      hence "D 0 i = Le 0" using lt by simp
      then show  ?thesis
        using lt by auto
    qed
  qed
qed

lemma helper_10i:
  assumes "\<not> Le (L' i) \<prec> (D i 0)"
  and "i \<le> n"
  and "0 < i"
shows "(lu_apx l D) i 0 = D i 0"
proof -
  have *:"(lu_apx l D) i 0 = norm_lower (D i 0) 0"
    unfolding lu_apx_def extra_lu_def
    using assms L'_def assms(1) 
    by auto
  show ?thesis
  proof(cases "D i 0 \<prec> Lt 0")
    case True
    have **:"D 0 i \<le> 0" using assms D_nonneg
      unfolding canonical_dbm_def dbm_nonneg_def
      by blast
    have "D i 0 \<prec> Le 0"
      using True linordered_monoid.dual_order.strict_trans
      by blast
    hence "D i 0 < 0"
      by (simp add: less neutral)
    hence ***:"D 0 i + D i 0 < 0"
      using ** add_nonpos_neg less neutral by blast
    have "D 0 i + D i 0 \<ge> 0"
      using path_ge_zero[of i] using assms(2-3)
      by simp
    then show ?thesis using *** by simp
  next
    case False
    then show ?thesis using * by simp
  qed
qed


text\<open>Lemmata 10 i) and ii) from the Paper vital in Proving the DBM that will be constructed is 
    subset of the zone abstraction later on\<close>

lemma Lemma10_i:
  assumes "i \<le> n"
  and "i > 0"
  and "u (v' i) \<le> min (U' i) (L' i)"
shows "dbm_le (Le (u_i i)) (D i 0)"
proof -
  let ?x = "v' i"
  let ?L = "(L l ?x)"
  have clock_num:"v ?x = i"
    using assms(1-2) clock_numbering(2) v_v' by auto
  hence x_i_less_n: "v ?x \<le> n" using assms by argo
  consider (gt) "D i 0 > Le ?L" | (le) "D i 0 \<le> Le ?L"
    by fastforce
    then show ?thesis
  proof cases
    case gt
    hence "Le (u ?x) < D i 0" 
      using assms
      unfolding L'_def U'_def
      by (cases "D i 0"; auto)
    then show ?thesis
      unfolding L'_def U'_def u_i_def
      by (auto simp: less)
    next
    case le
    hence "\<not> Le ?L \<prec> D i 0"
      using le less not_le
      by metis
    hence "(lu_apx l D) i 0 = D i 0" 
      using assms helper_10i[of i]
      unfolding L'_def
      by blast   
    hence "dbm_entry_val u (Some ?x) None (D i 0)"
      using u_dbm_entry_val(2)[of i] assms(1-2)
      by fastforce
    hence "Le (u ?x) \<le> D i 0" using clock_num
      by (cases "D i 0"; force+)
    then show ?thesis
      unfolding u_i_def
      by (simp add: less_eq)
    qed
qed


lemma Lemma10_ii:
  assumes "u (v' i) \<le> min (U' i) (L' i)"
  and "i \<le> n"
  and "i > 0"
shows "dbm_le (Le (- (u_i i))) (D 0 i)"
proof -
  let ?x = "v' i"
  let ?U = "U' i"
  have clock_num:"v ?x = i"
    using assms clock_numbering(2) v_v' by auto
  hence x_i_less_n: "v ?x \<le> n" using assms by argo
  have \<star>:"dbm_entry_val u None (Some ?x) (lu_apx l D 0 i)"
      using assms(2-3) u_dbm_entry_val(1)[of i]
      by fastforce
  have lu_start:"lu_apx l D 0 i = norm_lower (norm_upper (D 0 i) 0) (- ?U)"
      unfolding lu_apx_def extra_lu_def Let_def U'_def
      using assms
      by auto
  consider (lt) "D 0 i < Lt (- ?U)" | (ge) "D 0 i \<ge> Lt (- ?U)"
    by fastforce
  then show ?thesis
  proof cases
    case lt
    have notinf:"D 0 i \<noteq> DBM.INF" using lt by fastforce
    have \<box>:"Le (- u ?x) \<le> lu_apx l D 0 i"
      using notinf \<star>
      by(cases "lu_apx l D 0 i"; fastforce+)
    have "u ?x > ?U"
    proof(cases "Le 0 \<prec> D 0 i")
      case True
      have "dbm_nonneg n D" using D_nonneg
        by simp
      hence "D 0 i \<le> 0"
        unfolding dbm_nonneg_def
        using assms(2-3)
        by blast
      hence "D 0 i \<prec> Le 0 \<or> D 0 i = Le 0"
        using less_eq neutral
          by (simp add: less_eq neutral; fastforce)
      hence "False" using True by fastforce
      then show ?thesis by simp
    next
      case False
      hence "lu_apx l D 0 i = norm_lower (D 0 i) (- ?U)"
        using lu_start
        by fastforce
      hence "lu_apx l D 0 i = Lt (- ?U)" using lt
        by (simp add: less)
      hence "Le (- u ?x) \<le> Lt (- ?U)" using \<box>
        by presburger
      hence "u ?x > ?U"
        by fastforce
      then show ?thesis by simp
    qed
    hence "False" using assms by linarith
    then show ?thesis by simp
  next
    case ge
    hence not_lt:"\<not> (D 0 i) \<prec> Lt (- ?U)"
      by (simp add: less_eq)
    then show ?thesis
    proof(cases "Le 0 \<prec> D 0 i")
      case True
      have "dbm_nonneg n D" using D_nonneg
        by simp
      hence "D 0 i \<le> 0"
        unfolding dbm_nonneg_def
        using assms(2-3)
        by blast
      hence "D 0 i \<prec> Le 0 \<or> D 0 i = Le 0"
        using less_eq neutral
          by (simp add: less_eq neutral; fastforce)
      hence "False" using True by fastforce
      then show ?thesis by simp
    next
      case False
      hence "lu_apx l D 0 i = norm_lower (D 0 i) (- ?U)"
        using False lu_start
        by fastforce
      hence "lu_apx l D 0 i = D 0 i" using not_lt lu_start
        by force
      hence "dbm_entry_val u None (Some ?x) (D 0 i)"
        using \<star> 
        by argo
      hence "Le (- u ?x) \<le> D 0 i"
        by (cases "D 0 i"; force+)
      then show ?thesis
        unfolding u_i_def
        by (simp add: DBM.less_eq)
    qed
  qed
qed

definition u_dbm_row :: "nat \<Rightarrow> real DBMEntry \<Rightarrow> real DBMEntry"
  where
    "u_dbm_row i e \<equiv>
      let b = Le (u_i i) in 
      if u_i i \<le> min (L' i)  (U' i) then b
      else if L' i < u_i i \<and> u_i i \<le> U' i then dmin b e
      else e"

definition u_dbm_col :: "nat \<Rightarrow> real DBMEntry \<Rightarrow> real DBMEntry"
  where
    "u_dbm_col i e \<equiv>
      let ub = Le (-u_i i) in
      if u_i i \<le> min (L' i)  (U' i) then ub
      else if U' i < u_i i \<and> u_i i \<le> L' i then dmin ub e
      else dmin e (Lt (-L' i))"

definition u_dbm :: "real DBM \<Rightarrow> real DBM"
  where
    "u_dbm M \<equiv> \<lambda>i j.
      if i = 0 \<and> j = 0 then M i j
      else if j = 0 \<and> i \<le> n then u_dbm_row i (M i j)
      else if i = 0 \<and> j \<le> n then u_dbm_col j (M i j)
      else M i j"

abbreviation P_u
  where
    "P_u \<equiv> {u' \<in> \<lbrakk>D\<rbrakk>. sim (l,u) (l,u')}"

section \<open>\<lbrakk>u_dbm D\<rbrakk> \<subseteq> P_u\<close>

lemma zero_invar:
  assumes "DBM_val_bounded v x (u_dbm D) n"
  shows "dbm_le (Le 0) (D 0 0)"
proof -
  have "dbm_le (Le 0) (u_dbm D 0 0)" 
    using assms unfolding DBM_val_bounded_def by blast
  thus ?thesis unfolding u_dbm_def by simp
qed

lemma helper1:
  assumes "j \<le> n"
  and "0 < j"
  and "u_i j \<le> min (U' j) (L' j)"
  shows "dbm_le (u_dbm D 0 j) (D 0 j)"
proof -
  have u_dbm:"u_dbm D 0 j  = Le (- u_i j)"
    unfolding u_dbm_def u_dbm_col_def using assms
    by auto
  have **:"u (v' j) \<le> min (L' j) (U' j)" using assms u_i_def
      by auto
  have "dbm_le (Le (- u_i j)) (D 0 j)" 
      using u_apx ** assms(2)  assms(1) vabs Lemma10_ii L'_def U'_def 
      by auto
   thus ?thesis using u_dbm
     by presburger
  qed

lemma helper2:
  assumes "i \<le> n"
  and "0 < i"
  and "u_i i \<le> min (U' i) (L' i)"
  shows "dbm_le (u_dbm D i 0) (D i 0)"
proof -
  have u_dbm:"u_dbm D i 0 = Le (u_i i)"
    unfolding u_dbm_def u_dbm_row_def using assms
    by auto
  have **:"u (v' i) \<le> min (L' i) (U' i)" using assms u_i_def
      by auto
  have "dbm_le (Le (u_i i)) (D i 0)" 
      using u_apx ** assms(2)  assms(1) vabs Lemma10_i L'_def U'_def
      by fastforce
   thus ?thesis using u_dbm
     by presburger
  qed

lemma u_dbm_mono:
  assumes "i \<le> n"
  and "j \<le> n"
  shows "dbm_le (u_dbm D i j) (D i j)"
proof -
  consider
    (both_zero) "i = 0 \<and> j = 0" |
    (c1_zero) "i = 0 \<and> j  \<noteq> 0" |
    (c2_zero) "j = 0 \<and> i \<noteq> 0" |
    (neq_zero) "i \<noteq> 0 \<and> j \<noteq> 0"
    by fast
  then show ?thesis
  proof(cases)
    case both_zero
    hence "u_dbm D i j = D i j"
      unfolding u_dbm_def
      by simp
    then show ?thesis
      by fastforce
  next
    case c1_zero
    hence abs:"u_dbm D i j = u_dbm_col j (D 0 j)"
      unfolding u_dbm_def using assms(2)
      by presburger
    consider 
    (before) "u_i j \<le> min (L' j)  (U' j)" |
    (middle) "U' j < u_i j \<and> u_i j \<le> L' j" |
    (bigger_than_L) "L' j < u_i j"
    by linarith
  then show ?thesis
  proof(cases)
    case before
    hence "dbm_le (u_dbm D 0 j) (D 0 j)"
      using c1_zero assms helper1
      by simp
    then show ?thesis using c1_zero
      by argo
  next
    case middle
    hence "u_dbm D i j = dmin (Le (- u_i j)) (D 0 j)"
      using abs unfolding u_dbm_col_def
      by simp
    then show ?thesis using c1_zero
      by fastforce
  next
    case bigger_than_L
    hence "u_dbm D i j =  dmin (D 0 j) (Lt (- L' j))"
      using abs unfolding u_dbm_col_def
      by auto
    then show ?thesis using c1_zero
      by fastforce
  qed
  next
    case c2_zero
    have *:"u_dbm D i j = u_dbm_row i (D i 0)"
      unfolding u_dbm_def using c2_zero assms(1)
      by auto
    consider 
    (before) "u_i i \<le> min (L' i)  (U' i)" |
    (middle) "L' i < u_i i \<and> u_i i \<le> U' i" |
    (bigger_than_U) "U' i < u_i i"
    by linarith
  then show ?thesis
  proof(cases)
    case before
    hence "dbm_le (u_dbm D i 0) (D i 0)"
      using c2_zero assms(1) helper2
      by force
    then show ?thesis using c2_zero
      by argo
  next
    case middle
    hence "u_dbm D i j =  dmin (Le (u_i i)) (D i 0)"
      using *
      unfolding u_dbm_row_def
      by auto
    then show ?thesis using c2_zero
      by auto
  next
    case bigger_than_U
    hence "u_dbm D i j =  (D i 0)"
      using * unfolding u_dbm_row_def
      by simp
    then show ?thesis using c2_zero
      by fastforce
  qed
  next
    case neq_zero
    hence "u_dbm D i j = D i j"
      unfolding u_dbm_def
      by simp
    then show ?thesis by fastforce
  qed
qed

lemma cor:
  assumes "v c \<le> n"
  shows "dbm_le (u_dbm D (v c) 0) (D (v c) 0)"
        "dbm_le (u_dbm D 0 (v c)) (D 0 (v c))"
proof -
  show "dbm_le (u_dbm D (v c) 0) (D (v c) 0)"
    using assms u_dbm_mono
    by blast
next
  show "dbm_le (u_dbm D 0 (v c)) (D 0 (v c))"
  using assms u_dbm_mono
  by blast
qed

lemma bounded1:
assumes "DBM_val_bounded v x (u_dbm D) n"
  and "v c \<le> n"
shows "dbm_entry_val x None (Some c) (D 0 (v c))"
      "dbm_entry_val x (Some c) None (D (v c) 0)"
proof -
  have *:"dbm_entry_val x None (Some c) (u_dbm D 0 (v c))"
    using assms unfolding DBM_val_bounded_def by blast
  have "dbm_le (u_dbm D 0 (v c)) (D 0 (v c))"
    using cor assms(2)
    by blast
  thus "dbm_entry_val x None (Some c) (D 0 (v c))"  using * dbm_entry_val_mono(2)
    by fastforce
next
  have *:"dbm_entry_val x (Some c) None (u_dbm D (v c) 0)"
    using assms unfolding DBM_val_bounded_def by blast
  have "dbm_le (u_dbm D (v c) 0) (D (v c) 0)"
    using cor assms(2)
    by blast
  thus "dbm_entry_val x (Some c) None (D (v c) 0)" using * dbm_entry_val_mono(3)
    by fastforce
qed


lemma bounded2:
  assumes "DBM_val_bounded v x (u_dbm D) n"
  and "v c1 \<le> n"
  and "v c2 \<le> n"
shows "dbm_entry_val x (Some c1) (Some c2) (D (v c1) (v c2))"
proof -
  have "dbm_le (u_dbm D (v c1) (v c2)) (D (v c1) (v c2))"
    using u_dbm_mono assms
    by blast
  hence is_min:"min (u_dbm D (v c1) (v c2)) (D (v c1) (v c2)) = (u_dbm D (v c1) (v c2))"
    by (simp add: DBM.less_eq)
  have "dbm_entry_val x (Some c1) (Some c2) (u_dbm D (v c1) (v c2))"
    using assms unfolding DBM_val_bounded_def
    by blast
  thus ?thesis 
    using is_min dbm_entry_dbm_min[of "x" "c1" "c2" "u_dbm D (v c1) (v c2)" "D (v c1) (v c2)"]
    by argo
qed

lemma u_dbm_pres_bounded:
  assumes "DBM_val_bounded v x (u_dbm D) n"
  shows "DBM_val_bounded v x D n"
proof -
  have b1:"\<forall>c. v c \<le> n \<longrightarrow> 
            (dbm_entry_val x None (Some c) (D 0 (v c)) \<and> dbm_entry_val x (Some c) None (D (v c) 0))"
    using assms bounded1
    by fast
  have b2:"\<forall> c1 c2. v c1 \<le> n \<and> v c2 \<le> n \<longrightarrow> 
            dbm_entry_val x (Some c1) (Some c2) (D (v c1) (v c2))"
    using assms bounded2
    by blast
  thus ?thesis 
    unfolding DBM_val_bounded_def 
    using assms zero_invar b1 b2
    by blast
qed


lemma u_dbm_subset_input:
  "\<lbrakk>u_dbm D\<rbrakk> \<subseteq> \<lbrakk>D\<rbrakk>"
proof
  fix "x"
  assume "x \<in> \<lbrakk>u_dbm D\<rbrakk>"
  hence "DBM_val_bounded v x (u_dbm D) n" unfolding DBM_zone_repr_def by fast
  hence "DBM_val_bounded v x D n" using u_dbm_pres_bounded
    by blast
  thus "x \<in> \<lbrakk>D\<rbrakk>" unfolding DBM_zone_repr_def by fast
qed
  

lemma fst_sim:
  assumes "u' \<in> \<lbrakk>u_dbm D\<rbrakk>"
  and "x \<in> X"
  and "u' x < u x"
shows "real (L l x) < u' x"
proof -
  have \<box>:"v x > 0"
    using clock_numbering(1) by blast
  have a:"v x \<le> n"
    using assms(2) clock_numbering(3) by blast
  hence bound:"dbm_entry_val u' None (Some x) (u_dbm D 0 (v x))"
    using assms(1) unfolding DBM_zone_repr_def DBM_val_bounded_def 
    by blast
  have \<star>:"u_dbm D 0 (v x) = u_dbm_col (v x) (D 0 (v x))"
    unfolding u_dbm_def using a \<box>
    by presburger
  consider 
    (before) "u_i (v x) \<le> min (L' (v x))  (U' (v x))" |
    (middle) "U' (v x) < u_i (v x) \<and> u_i (v x) \<le> L' (v x)" |
    (bigger_than_L) "L' (v x) < u_i (v x)"
    by linarith
  then show ?thesis
  proof(cases)
    case before
    hence "u_dbm D 0 (v x) = Le (- u_i (v x))"
      using \<star>
      unfolding u_dbm_col_def
      using before
      by presburger
    hence "dbm_entry_val u' None (Some x) (Le (- u_i (v x)))"
      using bound
      by argo
    then show ?thesis
      using assms(2) assms(3) u_i_def v_v' 
      by auto
  next
    case middle
    hence "u_dbm D 0 (v x) = dmin (Le (- u_i (v x))) (D 0 (v x)) "
      using \<star>
      unfolding u_dbm_col_def
      using middle
      by auto
    hence "dbm_le (u_dbm D 0 (v x)) (Le (- u_i (v x)))"
      using dbm_le_def by auto
    hence "dbm_entry_val u' None (Some x) (Le (- u_i (v x)))"
      using bound  dbm_entry_val_mono(2) 
      by fast
    then show ?thesis
      using assms(2) assms(3) u_i_def v_v' 
      by auto
  next
    case bigger_than_L
    hence "u_dbm D 0 (v x) = dmin  (D 0 (v x)) (Lt (- L' (v x)))"
      using \<star>
      unfolding u_dbm_col_def
      using bigger_than_L
      by fastforce
    hence "dbm_le (u_dbm D 0 (v x)) (Lt (- L' (v x)))"
      using dbm_le_def by auto
    hence "dbm_entry_val u' None (Some x) (Lt (- L' (v x)))"
      using bound  dbm_entry_val_mono(2) 
      by fast
    then show ?thesis
      using \<box> L'_def assms(2) v_v' by auto
  qed
qed


lemma fst_sim_ball:
  assumes "u' \<in> \<lbrakk>u_dbm D\<rbrakk>"
  shows "\<forall>x \<in> X. u' x < u x \<longrightarrow> real (L l x) < u' x"
  using assms fst_sim by blast


lemma snd_sim:
  assumes "u' \<in> \<lbrakk>u_dbm D\<rbrakk>"
  and "x \<in> X"
  and "u' x > u x"
shows "real (U l x) < u x"
proof -
   have \<box>:"v x > 0"
    using clock_numbering(1) by blast
  have a:"v x \<le> n"
    using assms(2) clock_numbering(3) by blast
  hence bound:"dbm_entry_val u' (Some x) None (u_dbm D (v x) 0)"
    using assms(1) unfolding DBM_zone_repr_def DBM_val_bounded_def 
    by blast
  have \<star>:"u_dbm D (v x) 0 = u_dbm_row (v x) (D (v x) 0)"
    unfolding u_dbm_def using a \<box>
    by presburger
  consider 
    (before) "u_i (v x) \<le> min (L' (v x))  (U' (v x))" |
    (middle) "L' (v x) < u_i (v x) \<and> u_i (v x) \<le> U' (v x)" |
    (bigger_than_U) "U' (v x) < u_i (v x)"
    by linarith
  then show ?thesis
  proof(cases)
    case before
    hence "u_dbm D (v x) 0 = Le (u_i (v x))"
      using \<star>
      unfolding u_dbm_row_def
      using before
      using assms(2) assms(3) bound u_i_def v_v' by auto
    hence "dbm_entry_val u' (Some x) None (Le (u_i (v x)))"
      using bound
      by argo
    hence "u' x \<le> u_i (v x)"
      by blast
    hence "u' x \<le> u x" using assms(2) assms(3) bound u_i_def v_v'
      by auto
    then show ?thesis using assms
      by linarith
  next
    case middle
    hence "u_dbm D (v x) 0 = dmin (Le (u_i (v x))) (D (v x) 0) "
      using \<star>
      unfolding u_dbm_row_def
      using middle
      by auto
    hence "dbm_le (u_dbm D (v x) 0) (Le (u_i (v x)))"
      using dbm_le_def by auto
    hence "dbm_entry_val u' (Some x) None (Le (u_i (v x)))"
      using bound dbm_entry_val_mono_3 by fastforce
    hence "u' x \<le> u_i (v x)"
      by blast
    then show ?thesis
      using assms(2) assms(3) u_i_def v_v' by auto
  next
    case bigger_than_U
    then show ?thesis
      using \<box> U'_def assms(2) u_i_def v_v' by auto
  qed
qed


lemma snd_sim_ball:
  assumes "u' \<in> \<lbrakk>u_dbm D\<rbrakk>"
  shows "\<forall>x \<in> X. u' x > u x \<longrightarrow> u x > real (U l x)"
  using assms snd_sim by blast


lemma sim_ball:
  assumes "u' \<in> \<lbrakk>u_dbm D\<rbrakk>"
  shows "\<forall>x \<in> X. (u' x < u x \<longrightarrow> real (L l x) < u' x) \<and> 
                 (u' x > u x \<longrightarrow> u x > real (U l x))"
  using assms fst_sim snd_sim
  by blast


lemma u_dbm_sim:
  assumes "u' \<in> \<lbrakk>u_dbm D\<rbrakk>"
  shows "sim (l, u) (l, u')"
  unfolding sim_def
  using assms sim_ball X_is_clk_set
  by blast


lemma u_dbm_repr_P_u:
  "\<lbrakk>u_dbm D\<rbrakk> \<subseteq> P_u"
  using u_dbm_subset_input u_dbm_sim
  by fast

section \<open>\<lbrakk>u_dbm D\<rbrakk> \<noteq> \<emptyset>\<close>

lemma u_dbm_not_cyc_free:
  assumes "\<lbrakk>u_dbm D\<rbrakk> = {}"
  shows "\<not> cyc_free (u_dbm D) n"
  using assms clock_numbering_alt empty_not_cyc_free
  by blast

lemma u_dbm_nearly_cyc_free:
"set ys \<subseteq> {1..n} \<and> i \<in> {1..n} \<and> j \<in> {1..n}\<longrightarrow> 
      len (u_dbm D) i j ys = len D i j ys"
proof(induction ys arbitrary: i j)
  case Nil
  have "set [] \<subseteq> {1..n} \<and> i \<in> {1..n} \<and> j \<in> {1..n}  \<longrightarrow> 
      len (u_dbm D) i j [] = len D i j []"
  proof
    assume "set [] \<subseteq> {1..n} \<and> i \<in> {1..n} \<and> j \<in> {1..n}"
    hence \<box>:"0 < i \<and> i \<le> n \<and> 0 < j \<and> j \<le> n"
      by auto
    have "len (u_dbm D) i j [] = u_dbm D i j"
      by simp
    hence "len (u_dbm D) i j [] = D i j"
      unfolding u_dbm_def using \<box>
      by simp
    thus "len (u_dbm D) i j [] = len D i j []"
      by fastforce
    qed
  then show ?case
    by fast
next
  case (Cons a xs)
  have "set (a#xs) \<subseteq> {1..n} \<and> i \<in> {1..n} \<and> j \<in> {1..n} \<longrightarrow> 
        len (u_dbm D) i j (a#xs) = len D i j (a#xs)"
  proof
    assume \<star>:"set (a#xs) \<subseteq> {1..n} \<and> i \<in> {1..n} \<and> j \<in> {1..n}"
    hence \<box>:"set xs \<subseteq> {1..n} \<and> a \<in> {1..n}"
      by auto
    have for_head:"u_dbm D i a = D i a"
      using \<box> \<star> unfolding u_dbm_def
      by force
    have "len (u_dbm D) i j (a#xs) = u_dbm D i a + len (u_dbm D) a j xs"
      by fastforce
    hence "len (u_dbm D) i j (a#xs) = D i a + len (u_dbm D) a j xs"
      using for_head
      by argo
    hence "len (u_dbm D) i j (a#xs) = D i a + len D a j xs"
      using \<box> \<star> Cons[of a j]
      by presburger
    thus "len (u_dbm D) i j (a#xs) = len D i j (a#xs)"
      by simp
    qed
    then show ?case by blast
qed

lemma u_dbm_len_ge_entry:
  assumes "set ys \<subseteq> {1..n} \<and> i \<in> {1..n} \<and> j \<in> {1..n}" 
  shows "len (u_dbm D) i j ys \<ge> D i j"
proof -
  have id:"len (u_dbm D) i j ys = len D i j ys" 
    using u_dbm_nearly_cyc_free[of ys i j] assms 
    by blast
  have can_subs:"canonical_subs n {0..n} D"
    using D_canonical canonical_alt_def by blast
  have "j \<le> n \<and> i \<le> n" using assms
    by simp
  hence "len D i j ys \<ge> D i j" 
    using assms can_subs
          canonical_subs_len[of n "{0..n}" D i j ys]
    by fastforce
  thus ?thesis using id
    by argo
qed

lemma zero_gt_neg_u_i_Di0:
  assumes "i \<le> n"
  and "0 < i"
  and "u_i i \<le> (L' i)"
  and "Le (- u_i i) + D i 0 < 0"
shows "u_i i < U' i"
proof -
  have dj0_lt_u_i:"D i 0 < Le (u_i i)" using assms
    by(cases "D i 0"; auto simp: add dbm_lt.simps neutral)+
  hence not_lt_Dj0:"\<not> Le (u_i i) \<le> D i 0"
    by auto
  have u_le_L:"Le (u_i i) \<le>  Le (L' i)" using assms(3)
    by auto
  hence dj0_lt_L:"D i 0 < Le (L' i)" using dj0_lt_u_i 
    by (smt antisym_conv min.bounded_iff min_simps(2) not_le_imp_less)      
  have u_not_bound_Dj0:"\<not> (dbm_entry_val u (Some (v' i)) None (D i 0))"
  proof(rule notI)
    assume bounded:"dbm_entry_val u (Some (v' i)) None (D i 0)"
    show "False"
    proof(cases "D i 0")
      case (Le x1)
      hence "u (v' i) \<le> x1" using bounded
        by fastforce
      hence "u_i i \<le> x1" unfolding u_i_def by argo
      hence "Le (u_i i) \<le> D i 0" using Le
        by auto
      then show ?thesis using not_lt_Dj0
        by argo
    next
      case (Lt x2)
      hence "u (v' i) < x2" using bounded
        by fastforce
      hence "u_i i < x2" unfolding u_i_def by argo
      hence "Le (u_i i) \<le> D i 0" using Lt
        by auto
      then show ?thesis using not_lt_Dj0
        by argo
    next
      case INF
      then show ?thesis
        using not_lt_Dj0 by auto
    qed
  qed
  have "\<not> (lu_apx l D i 0 \<le> D i 0)"
  proof(rule notI)
    assume "lu_apx l D i 0 \<le> D i 0"
    hence "dbm_le (lu_apx l D i 0) (D i 0)" by (simp add: less_eq)
    hence "dbm_entry_val u (Some (v' i)) None (D i 0)"
      using dbm_entry_val_mono_3 u_dbm_entry_val(2)[of i] assms(1-2)
      by fast
    thus "False" using u_not_bound_Dj0
      by argo
  qed
  hence lu_gt_id:"lu_apx l D i 0 > D i 0"
    by simp
  have upper_eq_Dj0:"norm_upper (D i 0) (L' i) = D i 0"
    using dj0_lt_L
    by (metis less linordered_monoid.less_imp_not_less norm_upper.simps)
  have base:"lu_apx l D i 0 = norm_lower (norm_upper (D i 0) (L' i)) 0" 
    unfolding lu_apx_def extra_lu_def L'_def
    using assms
    by auto
  hence "lu_apx l D i 0 = norm_lower (D i 0) 0"
    using upper_eq_Dj0 by argo
  hence "lu_apx l D i 0 = Lt 0"
    using lu_gt_id
    by fastforce
  hence "u (v' i) < 0" using u_dbm_entry_val[of i] assms
    by force
  hence u_lt_0:"u_i i < 0" unfolding u_i_def
    by argo
  have "U' i \<ge> 0" unfolding U'_def
    by simp
  hence "u_i i < U' i" 
    using assms(3) u_lt_0 by linarith
  thus ?thesis.
qed

lemma zero_gt_u_dbm_L:
  assumes "j \<le> n"
  and "0 < j"
  and "L' j < u_i j"
  and lt_0:"Lt (-L' j) + D j 0 < 0"
shows "False"
proof -
  have *:"D 0 j + D j 0 \<ge> 0"
    using path_ge_zero[of j] assms(1-2) by argo
  have "D 0 j \<le> Le 0" 
     using D_canonical_dbm neutral assms
     unfolding canonical_dbm_def dbm_nonneg_def
     by metis
  hence dj0_gt_zero:"D j 0 \<ge> 0"
    using *
    by (metis add_nonpos_neg linorder_not_less neutral)
  have dj0_le_L:"dbm_entry_bound (D j 0) \<le> L' j" 
  proof(cases "D j 0")
    case (Le x1)
    hence "Lt (- L' j) + D j 0 = Lt (x1 - L' j)" 
      by (simp add: add)
    hence "Lt (x1 - L' j) < Le 0" 
      using lt_0 neutral
      by metis
    hence "x1 - L' j \<le> 0"
      by force
    hence "x1 \<le> L' j"
      by simp
    then show ?thesis using Le
      by fastforce
  next
    case (Lt x2)
    hence "Lt (- L' j) + D j 0 = Lt (x2 - L' j)" 
      by (simp add: add)
    hence "Lt (x2 - L' j) < Le 0" 
      using lt_0 neutral
      by metis
    hence "x2 - L' j \<le> 0"
      by force
    hence "x2 \<le> L' j"
      by simp
    then show ?thesis using Lt
      by force
  next
    case INF
    then show ?thesis using lt_0
      by fastforce
  qed
  hence upper_id: "norm_upper (D j 0) (L' j) = D j 0"
    by(cases "D j 0"; auto)
  have "Le 0 > Lt 0"
    by simp
  hence "D j 0 > Lt 0"
    using dj0_gt_zero neutral
    by (smt DBM.less_eq dbm_le_def less linordered_monoid.dual_order.strict_trans)
  hence "\<not> D j 0 \<prec> Lt 0"
    by (simp add: less)
  hence lower_id:"norm_lower (D j 0) 0 = D j 0"
    by auto
  hence lower_upper_id: "norm_lower (norm_upper (D j 0) (L' j)) 0 = D j 0"
    using upper_id
    by argo
  have "lu_apx l D j 0 = norm_lower (norm_upper (D j 0) (L' j)) 0"
    unfolding lu_apx_def extra_lu_def L'_def
    using assms
    by fastforce
  hence "lu_apx l D j 0 = D j 0" 
    using lower_upper_id
    by argo
  hence "dbm_entry_val u (Some (v' j)) None (D j 0)"
    using u_dbm_entry_val assms
    by fastforce
  hence "u (v' j) \<le> dbm_entry_bound (D j 0)"
    using lt_0
    by(cases "D j 0";auto)
  hence "u (v' j) \<le> L' j" using dj0_le_L
    by linarith
  thus "False" using assms(3) unfolding u_i_def
    by auto
qed

lemma u_dbm_same_clock_impl_u_bigger_ceil_min:
assumes "j \<le> n"
  and "0 \<noteq> j"
  and  "u_dbm D 0 j + u_dbm D j 0 < 0"
shows "u_i j > min (L' j) (U' j)"
proof(rule ccontr)
  assume "\<not>(u_i j >  min (L' j)  (U' j))"
  hence A: "u_i j \<le> min (L' j)  (U' j)"
    by linarith
  have \<box>:"u_dbm D j 0 = Le (u_i j)"
        unfolding u_dbm_def using assms
        unfolding u_dbm_row_def
        using A
        by presburger
  have "u_dbm D 0 j = Le (- u_i j)"
        unfolding u_dbm_def using assms
        unfolding u_dbm_col_def
        using A
        by presburger
  hence "u_dbm D 0 j + u_dbm D j 0 = 0"
        using \<box>
        by (simp add: neutral ab_semigroup_add_class.add.commute)
  thus "False" using assms
    by auto
qed


lemma reuse_Dj0_U_lt_0:
  assumes "0 < j \<and> j \<le> n"
  and "D 0 j + Le (u_i j) < 0"
  and "u_i j \<le> U' j"
shows "False"
proof -
  have bounded:"dbm_entry_val u None (Some (v' j)) (lu_apx l D 0 j)"
    using u_apx 
    unfolding DBM_zone_repr_def DBM_val_bounded_def u_i_def
    using assms
    using clock_numbering(2) v_v' by auto
  have "D 0 j \<noteq> lu_apx l D 0 j"
  proof(rule notI)
    assume eq_lu:"D 0 j = lu_apx l D 0 j"
    hence lu_not_inf:"lu_apx l D 0 j \<noteq> DBM.INF"
      using assms
      by auto
    hence "Le (- u_i j) \<le> D 0 j"
    proof(cases "D 0 j")
      case (Le x1)
      hence "- u_i j \<le> x1"
        unfolding u_i_def 
        using bounded eq_lu
        by auto
      then show ?thesis
        by (simp add: Le)
    next
      case (Lt x2)
      hence "- u_i j < x2"
        unfolding u_i_def 
        using bounded eq_lu
        by auto
      then show ?thesis
        by (simp add: Lt)
    next
      case INF
      then show ?thesis using lu_not_inf eq_lu
      by argo
    qed
    hence "0 \<le> D 0 j + Le (u_i j)"
         by (smt Le_cancel_1 add_mono_thms_linordered_semiring(1) neutral order_mono_setup.refl)
    thus "False" using assms
      by fastforce
  qed
  hence "lu_apx l D 0 j = Lt (- U l (v' j))"
    using Lemma9[of j] vabs assms
    unfolding U'_def
    by auto
  hence "dbm_entry_val u None (Some (v' j)) (Lt (- U l (v' j)))"
    using bounded
    by argo
  hence "- u (v' j) < - U l (v' j)" 
    by fast
  hence "- u (v' j) < - U' j"
    using U'_def by auto
  hence "u_i j > U' j"
    unfolding u_i_def
    by auto
  then show ?thesis using assms(3)
    by linarith
qed

text\<open>Vital in showing that:
      \<lbrakk>u_dbm D\<rbrakk> = {} implies
      \<exists>i \<noteq> j \<in> {1..n}. u_dbm D 0 i + D i j + D j 0 < 0\<close>
lemma u_dbm_same_clock:
  assumes "j \<le> n"
  and "0 < j"
shows "u_dbm D 0 j + u_dbm D j 0 \<ge> 0"
proof(rule ccontr)
  assume "\<not>(u_dbm D 0 j + u_dbm D j 0 \<ge> 0)"
  hence assm_c:"u_dbm D 0 j + u_dbm D j 0 < 0"
    by auto
  have not_min:"u_i j >  min (L' j)  (U' j)"
    using assms assm_c u_dbm_same_clock_impl_u_bigger_ceil_min
    by blast
  consider
    (middle) "L' j < u_i j \<and> u_i j \<le> U' j" |
    (bigger_U) "u_i j > U' j"
    using not_min assms
    by linarith
  thus "False"
  proof(cases)
    case middle
    hence L_lt_u:"L' j < u_i j"
      by simp
    have b1:"u_dbm D j 0 = dmin (Le (u_i j)) (D j 0)"
        unfolding u_dbm_def
        using assms
        unfolding u_dbm_row_def
        using middle by auto
    hence b2:"u_dbm D 0 j = dmin (D 0 j) (Lt (- L' j))"
        unfolding u_dbm_def
        using assms
        unfolding u_dbm_col_def
        using L_lt_u
        by fastforce
   have not_both_bigger_D:
        "\<not>(Lt (- L' j) \<ge> D 0 j \<and> Le (u_i j) \<ge> D j 0)"
   proof(rule notI)
     assume "Lt (- L' j) \<ge> D 0 j \<and> Le (u_i j) \<ge> D j 0"
     hence "u_dbm D 0 j + u_dbm D j 0 = D 0 j + D j 0"
       using b1 b2
       by (metis DBM.less_eq dbm_le_def less linorder_not_less)
     hence "0 \<le> u_dbm D 0 j + u_dbm D j 0"
       using D_through_zero assms(1)
       by simp
     thus "False" using assm_c by auto
   qed
   have zero_le_u_L:"0 \<le> Le (u_i j) + Lt (- L' j)"
     by (smt L_lt_u Le_cancel_1 Le_le_LtI add_left_mono neutral)
   have not_both_smaller_D:
     "\<not>(Lt (- L' j) \<le>  D 0 j \<and> Le (u_i j) \<le> D j 0)"
   proof(rule notI)
     assume "Lt (- L' j) \<le>  D 0 j \<and> Le (u_i j) \<le> D j 0"
     hence "u_dbm D 0 j + u_dbm D j 0 = Lt (- L' j) + Le (u_i j)"
       using b1 b2
       by (metis DBM.less_eq dbm_le_def less linorder_not_less)
     hence "u_dbm D 0 j + u_dbm D j 0 \<ge> 0"
       using zero_le_u_L
       by (simp add: ab_semigroup_add_class.add.commute)
     thus "False" using assm_c
       by auto
   qed
   consider
     (1) "Lt (- L' j) \<ge> D 0 j \<and> Le (u_i j) \<le> D j 0" |
     (2) "Lt (- L' j) \<le> D 0 j \<and> Le (u_i j) \<ge> D j 0"
     using not_both_bigger_D  not_both_smaller_D by fastforce
    then show ?thesis
    proof(cases)
      case 1
      hence A:"u_dbm D j 0 = Le (u_i j) \<and> u_dbm D 0 j = D 0 j"
        using b1 b2 less_eq
        by (metis dbm_le_def)
      then show ?thesis 
        using assm_c middle reuse_Dj0_U_lt_0[of j] assms
        by argo
   next
     case 2
     hence A:"u_dbm D j 0 = D j 0 \<and> u_dbm D 0 j = Lt (- L' j)"
       using b1 b2 less_eq
       by (metis dbm_le_def not_both_bigger_D not_both_smaller_D)    
     have lt_zero:"D j 0 + Lt (- L' j) < 0"
       by (metis ab_semigroup_add_class.add.commute assm_c A)
     hence neq_inf:"D j 0 \<noteq> DBM.INF"
       by force
     hence "D j 0 \<le> Le (L' j)" using lt_zero
       by(cases "D j 0";auto simp: add neutral)
     hence "\<not> Le (L l (v' j)) \<prec> (D j 0)"
       unfolding L'_def using assms(2)
       by (simp add: DBM.less_eq)
     hence is_lu:"lu_apx l D j 0 = D j 0" 
       using assms vabs u_apx  
       using helper_10i[of j]
       unfolding L'_def
       by fast
     hence bounded:"dbm_entry_val u (Some (v' j)) None (D j 0)"
       using u_apx is_lu
       unfolding DBM_zone_repr_def DBM_val_bounded_def u_i_def
       using assms
       using clock_numbering(2) v_v'
       by fastforce
     show ?thesis
     proof(cases "D j 0")
       case (Le x1)
       hence  "u (v' j) \<le> x1" using Le bounded
         by fastforce
       hence "u_i j \<le> x1" unfolding u_i_def
         by blast
       hence " Le (u_i j) \<le> D j 0" using Le
         by simp
       hence is_u:"Le (u_i j) = D j 0" using 2
         by fastforce
       have "u_i j - L' j > 0"
         by (simp add: L_lt_u)
       hence "Lt (u_i j - L' j) > 0"
         using "2" \<open>Le (u_i j) \<le> D j 0\<close> not_both_smaller_D by blast
       have "D j 0 + Lt (- L' j) > 0" 
         using is_u "2" not_both_smaller_D by auto
       then show ?thesis using lt_zero
         by force
     next
       case (Lt x2)
       hence  "u (v' j) < x2" using Lt bounded
         by fastforce
       hence "u_i j < x2" unfolding u_i_def
         by blast
       hence " Le (u_i j) <  D j 0" using Lt
         by simp
       then show ?thesis using 2
         by fastforce
     next
       case INF
       then show ?thesis using lt_zero by force
     qed
   qed
 next
   case bigger_U
   hence rhs: "u_dbm D j 0 = D j 0"
     unfolding u_dbm_def u_dbm_row_def by auto
   have lhs_not_id: "u_dbm D 0 j \<noteq> D 0 j"
   proof(rule ccontr)
     assume "\<not>(u_dbm D 0 j \<noteq> D 0 j)"
     hence "D 0 j + D j 0 < 0" 
       using assm_c rhs
       by argo
     thus "False" using path_ge_zero[of j] assms
       by force
   qed
   consider (between) "(U' j < u_i j \<and> u_i j \<le> L' j)" |
             (bigger) "(U' j < u_i j \<and> u_i j > L' j)" 
     using not_min bigger_U by linarith
   then show ?thesis
   proof(cases)
     case between
     hence "u_dbm D 0 j = dmin (Le (- u_i j)) (D 0 j)"
       unfolding u_dbm_def u_dbm_col_def using assms 
       by auto
     hence lhs:"u_dbm D 0 j = Le (- u_i j)"
       using lhs_not_id
       by argo
     hence "Le (- u_i j) + D j 0 < 0" 
       using rhs assm_c
       by argo
     hence "u_i j < U' j" 
       using assms zero_gt_neg_u_i_Di0[of j] between
       by fast
     thus ?thesis using between
       by linarith
    next
      case bigger
      hence "u_dbm D 0 j = Lt (- L' j)"
        using u_dbm_col_def u_dbm_def lhs_not_id by auto
      hence lt_0:"Lt (- L' j) + D j 0  < 0" 
        using rhs assm_c
        by (simp add: ab_semigroup_add_class.add.commute)
      then show ?thesis using zero_gt_u_dbm_L[of j] bigger assms 
        by argo
    qed
  qed
qed

lemma cons_eq_some_append:
  "ys = [] \<or> (\<exists>a as. ys = as @ [a])"
  by(induction ys arbitrary: a as; auto)


lemma negative_len_shortest_alt:
  assumes "len m i i xs < 0"
  shows "\<exists> j ys. distinct (j # ys) \<and> len m j j ys < 0 
              \<and> j \<in> set (i # xs) \<and> set ys \<subseteq> set xs"
  using negative_len_shortest[of xs "length xs"] assms by blast

lemma disjE_reuse_fst:
  assumes "(P \<or> Q)"
  and "P \<Longrightarrow> R"
  and "Q \<Longrightarrow> P \<or> R"
shows "R"
  using assms by argo

lemma cycle_u_dbm_weak:
  assumes "\<lbrakk>u_dbm D\<rbrakk> = {}"
  shows "\<exists> i j. i \<in> {1..n} \<and> j \<in> {1..n} \<and> u_dbm D 0 i + D i j + u_dbm D j 0 < 0"
proof -
  text \<open>First we obtain a distinct shortest path which is less than 0\<close>
  obtain i xs where
    *:"set xs \<subseteq> {0..n}"
    "i \<le> n"
    "len (u_dbm D) i i xs < 0"
    using assms u_dbm_not_cyc_free
    by force
    hence "\<exists> j ys. distinct (j # ys) \<and> len (u_dbm D) j j ys < 0 \<and> j \<in> set (i # xs) \<and> set ys \<subseteq> set xs"
      using negative_len_shortest_alt[of "u_dbm D" i xs]
      by blast
    from this obtain j ys where 
      j_ys:"distinct (j # ys)"
      "len (u_dbm D) j j ys < 0"
      "j \<in> set (i#xs)"
      "set ys \<subseteq> set xs"
      by blast
    have len_u_dbm_lt_zero: "len (u_dbm D) j j ys < 0"
      using j_ys
      by argo
    have ys_le_n: "set ys \<subseteq> {0..n}" using j_ys(4) *(1)
      by fast
    text\<open>The path must contain at least two points between j
        We first show it must contain atleast one point:\<close>
    have ys_non_empty:"\<exists> k ks. ys = k#ks"
    proof(rule ccontr)
      assume "\<not> (\<exists> k ks. ys = k#ks)"
      hence "ys = []"
        using list_encode.elims by blast
      hence "u_dbm D j j < 0" 
          using j_ys
          by force
      hence **:"D j j < 0"
          unfolding u_dbm_def using j_ys
          by presburger
      have "j \<le> n" using j_ys *
      by force
      hence "D j j \<ge> 0" 
        by (simp add: D_cyc_free clock_numbering_alt cyc_free_not_empty dbm_non_empty_diag)
      thus "False" using **
          by simp
      qed
    obtain k ks where
      k_ks:"ys = k#ks" using ys_non_empty
      by blast
    hence ks_len: "len (u_dbm D) j j ys = u_dbm D j k + len (u_dbm D) k j ks"
      by simp
    have zero_in_path:"j = 0 \<or> 0 \<in> set ys"
    proof(rule ccontr)
      assume "\<not>(j = 0 \<or> 0 \<in> set ys )"
      hence "j > 0 \<and> 0 \<notin> set ys"
        by fast
      hence \<box>:"j \<in> {1..n} \<and> 0 \<notin> set ys"
        using * j_ys by auto
      hence "j \<in> {1..n} \<and> set ys \<subseteq> {1..n}"
        using "*"(1) j_ys(4) nat_geq_1_eq_neqz by fastforce
      hence "len (u_dbm D) j j ys = len D j j ys"
        using u_dbm_nearly_cyc_free[of ys j j]
        by blast
      hence "len (u_dbm D) j j ys \<ge> 0"
        using D_cyc_free
        using "*"(1) \<box> j_ys(4) by auto
      thus "False" using j_ys
        by auto
    qed
    hence "(j = 0 \<and> set ys \<subseteq> {1..n}) \<or> (0 \<noteq> j \<and> 0 \<in> set ys)"
      using j_ys(1) distinct.simps using nat_not_ge_1D
    proof(cases "j = 0")
      case True
      hence "0 \<notin> set ys" using distinct.simps j_ys(1)
        by fast
      hence "\<forall>x \<in> set ys. x > 0" using ys_le_n
        by blast
      then show ?thesis using True ys_le_n
        by force    
    next
      case False
      then show ?thesis using zero_in_path
        by argo
    qed
    then consider 
      (j_zero) "j = 0 \<and> set ys \<subseteq> {1..n}" |
      (ys_zero) "j \<noteq> 0 \<and> 0 \<in> set ys"
      by argo
    thus ?thesis
    proof(cases)
      case j_zero
      hence "len (u_dbm D) 0 0 ys < 0" using j_ys(2)
        by blast
      hence \<box>:"u_dbm D 0 k + len (u_dbm D) k 0 ks < 0"
        using k_ks
        by fastforce
      then show ?thesis
      proof(cases ks)
        text \<open>The Nil Case proofs that ys contains at least two points\<close>
        case Nil
        hence contr:"u_dbm D 0 k + u_dbm D k 0 < 0"
          using \<box>
          by force
        have "u_dbm D 0 k + u_dbm D k 0 \<ge> 0" 
          using k_ks j_zero u_dbm_same_clock[of k]
          by fastforce
        then show ?thesis using contr
          by auto
      next
        case (Cons a as)
        hence "\<exists> q qs. ks = qs @ [q]" using cons_eq_some_append
          by blast
        from this obtain q qs where
          q_qs:"ks = qs @ [q]"
          by blast
        hence len_ge:"len (u_dbm D) k q qs \<ge> D k q" 
          using j_zero k_ks u_dbm_len_ge_entry[of qs k q]
          by force
        have len_ys:"len (u_dbm D) 0 0 ys = u_dbm D 0 k + len (u_dbm D) k 0 ks"
          using ks_len j_zero
          by fastforce
        have "len (u_dbm D) k 0 ks = len (u_dbm D) k q qs + u_dbm D q 0"
          using q_qs len_comp[of "u_dbm D" k 0 qs q Nil]
          by fastforce
        hence "len (u_dbm D) 0 0 ys = u_dbm D 0 k + len (u_dbm D) k q qs + u_dbm D q 0"
          using len_ys
          by (simp add: add.assoc)
        hence "len (u_dbm D) 0 0 ys \<ge> u_dbm D 0 k + D k q + u_dbm D q 0"
          using len_ge
          by (simp add: add_left_mono add_right_mono)
        then show ?thesis 
          using j_ys(2) j_zero k_ks q_qs by fastforce
      qed
    next
      case ys_zero
      hence "\<exists>as bs. ys = as @ 0#bs"
        by (meson in_set_list_format)
      from this obtain "as" "bs" 
        where as_bs:"ys = as @0#bs"
              "(\<forall>x \<in> set as. x > 0) \<and> (\<forall>x \<in> set bs. x > 0)"
              "set as \<subseteq> set ys \<and> set bs \<subseteq> set ys"
        using j_ys(1) k_ks
        by fastforce
      hence set_as_bs:"set as \<subseteq> {1..n} \<and> set bs \<subseteq> {1..n}" 
        using ys_le_n
        by force
      hence "len (u_dbm D) j j ys = len (u_dbm D) j 0 as + len (u_dbm D) 0 j bs"
        using len_comp as_bs(1)
        by fast
      hence len_ys: "len (u_dbm D) j j ys = len (u_dbm D) 0 j bs + len (u_dbm D) j 0 as"
        by (simp add: add.commute add.assoc)
      text\<open> either as or bs need to be non empty\<close>
      have j_le_n: "j \<le> n"
        using "*"(1) "*"(2) j_ys(3) ys_zero by auto
      hence j_in_1_n:"j \<in> {1..n}" using ys_zero
        by force
      have "\<not> (as = [] \<and> bs = [])"
      proof(rule notI)
        assume "as = [] \<and> bs = []"
        hence contr:" u_dbm D 0 j + u_dbm D j 0 < 0"
          using len_ys j_ys(2)
          by force
        have "u_dbm D 0 j + u_dbm D j 0 \<ge> 0"
          using j_le_n ys_zero
              u_dbm_same_clock[of j]
          by fast
        thus "False" using contr
          by fastforce
      qed
      hence "(\<exists>l ls . as = ls@[l]) \<or> (\<exists>m ms. bs = m#ms) "
        using cons_eq_some_append[of as]
        by (meson list_encode.elims)
    then show ?thesis
    proof(rule disjE_reuse_fst[of "\<exists>l ls . as = ls@[l]" "\<exists>m ms. bs = m#ms"])    
      assume "\<exists>l ls . as = ls@[l]"
      from this obtain l ls where
        lhs: "as = ls @ [l]"
        by blast
      hence l_ls_le_n:"l \<in> {1..n} \<and> set ls \<subseteq> {1..n}"
        using set_as_bs
        by simp
      have "len (u_dbm D) j 0 as = len (u_dbm D) j l ls + u_dbm D l 0"
        using lhs len_comp[ of "u_dbm D" j 0 ls l Nil]
        by auto
      hence len_as:"len (u_dbm D) j 0 as \<ge> D j l + u_dbm D l 0"
        using j_in_1_n l_ls_le_n u_dbm_len_ge_entry[of ls j l]
          add_mono_left
        by auto
      show ?thesis
      proof(cases bs)
        case Nil
        hence "len (u_dbm D) 0 j bs = u_dbm D 0 j"
          by auto
        hence "len (u_dbm D) j j ys \<ge> u_dbm D 0 j + D j l + u_dbm D l 0 "
          using len_as len_ys
          by (simp add: add_mono_right add.assoc)
        hence "u_dbm D 0 j + D j l + u_dbm D l 0 < 0" using j_ys(2)
          by force
        then show ?thesis using j_in_1_n l_ls_le_n
          by blast
      next
        case (Cons m ms)
        hence m_ms_le_n:"m \<in> {1..n} \<and> set ms \<subseteq> {1..n}" using set_as_bs
          by simp
        hence ms_len:"len (u_dbm D) m j ms \<ge> D m j" 
          using u_dbm_len_ge_entry[of ms m j] j_in_1_n
          by argo
        have sp:"D m j + D j l \<ge> D m l" using D_canonical m_ms_le_n l_ls_le_n
          j_le_n
          by auto
        have "len (u_dbm D) 0 j bs = u_dbm D 0 m + len (u_dbm D) m j ms"
          using Cons by force
        hence "len (u_dbm D) 0 j bs \<ge> u_dbm D 0 m + D m j"
          using ms_len add_mono_right
          by auto
        hence "len (u_dbm D) j j ys \<ge> u_dbm D 0 m + D m j + D j l + u_dbm D l 0"
          using len_as 
                add_mono[of "u_dbm D 0 m + D m j" "len (u_dbm D) 0 j bs"
                            "D j l + u_dbm D l 0" "len (u_dbm D) j 0 as"
                        ]
              len_ys
          by (simp add: add.assoc)
        hence "len (u_dbm D) j j ys \<ge> u_dbm D 0 m + D m l + u_dbm D l 0"
          using sp
          by (smt DBM.less_eq ab_semigroup_add_class.add.commute add.assoc add_left_mono linordered_monoid.dual_order.trans)
        hence "u_dbm D 0 m + D m l + u_dbm D l 0 < 0" using j_ys(2)
          by auto
        then show ?thesis using j_in_1_n m_ms_le_n l_ls_le_n by blast
      qed
    next
      let ?thesis = 
        "(\<exists>l ls. as = ls @ [l]) \<or> 
         (\<exists>i j. i \<in> {1..n} \<and> j \<in> {1..n} 
            \<and> u_dbm D 0 i + D i j + u_dbm D j 0 < 0)"
      assume "\<exists>m ms. bs = m#ms"
      from this obtain m ms where
        rhs:"bs = m#ms"
        by blast
      hence m_ms_le_n:"m \<in> {1..n} \<and> set ms \<subseteq> {1..n}" using set_as_bs
        by force
      have ms_len:"len (u_dbm D) m j ms \<ge> D m j"
        using u_dbm_len_ge_entry[of ms m j] j_in_1_n m_ms_le_n
        by fast
      have "len (u_dbm D) 0 j bs = u_dbm D 0 m + len (u_dbm D) m j ms"
        using rhs
        by force
      hence len_bs:"len (u_dbm D) 0 j bs  \<ge> u_dbm D 0 m + D m j"
        using ms_len add_mono_right
        by auto
      show ?thesis
      proof(cases as)
        case Nil
        hence "len (u_dbm D) j 0 as = u_dbm D j 0"
          by simp
        hence "len (u_dbm D) j j ys \<ge> u_dbm D 0 m + D m j + u_dbm D j 0"
          using len_bs len_ys
          by (simp add: add_right_mono)
        hence "u_dbm D 0 m + D m j + u_dbm D j 0 < 0" 
          using j_ys(2)
          by simp
        then show ?thesis using m_ms_le_n j_in_1_n
          by blast
      next
        case (Cons a list)
        hence "\<exists>ls l. as = ls @ [l]" 
          using cons_eq_some_append[of as]
          by fast
        then show ?thesis
          by blast
      qed
    qed
  qed
qed

lemma cycle_u_dbm:
  assumes "\<lbrakk>u_dbm D\<rbrakk> = {}"
  shows "\<exists> i j. i \<in> {1..n} \<and> j \<in> {1..n} \<and> i \<noteq> j \<and> u_dbm D 0 i + D i j + u_dbm D j 0 < 0"
proof -
  have "\<exists> i j. i \<in> {1..n} \<and> j \<in> {1..n}  \<and> u_dbm D 0 i + D i j + u_dbm D j 0 < 0"
    using cycle_u_dbm_weak assms
    by blast
  from this obtain i j where
    i_j:"i \<in> {1..n} \<and> j \<in> {1..n}"
    "u_dbm D 0 i + D i j + u_dbm D j 0 < 0"
    by blast
  have "i \<noteq> j"
  proof(rule notI)
    assume "i = j"
    hence C:"u_dbm D 0 i + D i i + u_dbm D i 0 < 0"
      using i_j(2)
      by presburger
    have *:"D i i \<ge> 0"
      using D_zone_repr_non_empty_alt dbm_non_empty_diag i_j(1) by auto
    have "u_dbm D 0 i + u_dbm D i 0 \<ge> 0"
      using u_dbm_same_clock i_j(1) by auto
    hence "u_dbm D 0 i + D i i + u_dbm D i 0 \<ge> 0"
      using *
      by (smt Le_cancel_1 ab_semigroup_add_class.add.commute add.assoc add_mono neutral)
    thus "False" using C
      by simp
  qed
  thus ?thesis using i_j
    by blast
qed


lemma u_dbm_dj0_rule:
  assumes "j \<in> {1..n}"
  and "u_i  j \<le> min (L' j)  (U' j) \<Longrightarrow> P (Le (u_i j))" (is "?case1 \<Longrightarrow> ?base")
  and "L' j < u_i j \<and> u_i j \<le> U' j \<Longrightarrow> P (min (Le (u_i j)) (D j 0))"
  and "U' j < u_i j \<Longrightarrow> P (D j 0)"
shows "P (u_dbm D j 0)"
proof -
  have is_u_dbm_row:"u_dbm D j 0 = u_dbm_row j (D j 0)" 
    unfolding u_dbm_def using assms
    by force
  consider 
    (before) "u_i  j \<le> min (L' j)  (U' j)" |
    (middle) "L' j < u_i j \<and> u_i j \<le> U' j" |
    (bigger_than_U) "U' j < u_i j"
  by linarith
  then show ?thesis
  proof(cases)
    case before
    have "u_dbm D j 0 = Le (u_i j)"
      using is_u_dbm_row 
      unfolding u_dbm_row_def 
      using before
      by presburger
    then show ?thesis using assms(2)
      using before by auto
  next
    case middle
    hence "u_dbm D j 0 = min (Le (u_i j)) (D j 0)"
      using is_u_dbm_row unfolding u_dbm_row_def
      by (smt DBM.less_eq less linordered_monoid.leI min.absorb2 min_simps(1))
    then show ?thesis using middle assms(3)
      by presburger
  next
    case bigger_than_U
    hence "u_dbm D j 0 = D j 0"
      using is_u_dbm_row unfolding u_dbm_row_def
      by auto
    then show ?thesis using bigger_than_U assms(4)
      by argo
  qed 
qed

lemma u_dbm_0j_rule:
assumes "j \<in> {1..n}"
  and "u_i  j \<le> min (L' j)  (U' j) \<Longrightarrow> P (Le (- u_i j))"
  and "U' j < u_i j \<and> u_i j \<le> L' j \<Longrightarrow> P (min (Le (- u_i j)) (D 0 j))"
  and "L' j < u_i j \<Longrightarrow> P (min (D 0 j) (Lt (- L' j)))"
shows "P (u_dbm D 0 j)"
proof -
  have is_u_dbm_col: "u_dbm D 0 j = u_dbm_col j (D 0 j)"
    unfolding u_dbm_def using assms
    by simp
  consider 
    (before) "u_i  j \<le> min (L' j)  (U' j)" |
    (middle) "U' j < u_i j \<and> u_i j \<le> L' j" |
    (bigger_than_U) "L' j < u_i j" by linarith
  then show ?thesis
  proof(cases)
    case before
    hence "u_dbm D 0 j = Le (- u_i j)" 
      using is_u_dbm_col unfolding u_dbm_col_def using before
      by presburger
    then show ?thesis using assms(2) before
      by presburger
  next
    case middle
    hence "u_dbm D 0 j = min (Le (- u_i j)) (D 0 j)"
      using is_u_dbm_col unfolding u_dbm_col_def using middle
      by (smt less min.absorb2 min_simps(1) not_le_imp_less)
    then show ?thesis using middle assms(3)
      by presburger
  next
    case bigger_than_U
    hence "u_dbm D 0 j = min (D 0 j) (Lt (- (L' j)))"
      using is_u_dbm_col unfolding u_dbm_col_def using bigger_than_U
      by (simp add: DBM.less_eq less min.absorb2)
    then show ?thesis using bigger_than_U assms(4)
      by argo
  qed
qed

lemma u_dbm_0j_rule_alt:
assumes "j \<in> {1..n}"
  and "P (D 0 j)"
  and "u_i j \<le> L' j \<Longrightarrow> P (Le (- u_i j))"
  and "L' j < u_i j \<Longrightarrow> P (Lt (- L' j))"
shows "P (u_dbm D 0 j)"
proof(rule u_dbm_0j_rule[of j])
  show "j \<in>{1..n}" using assms
    by argo
next
  assume "u_i j \<le> min (L' j) (U' j)"
  hence "u_i j \<le> L' j"
    by force
  thus "P (Le (- u_i j))" using assms(3)
    by blast
next
  assume A:"U' j < u_i j \<and> u_i j \<le> L' j"
  show "P (min (Le (- u_i j)) (D 0 j))"
  proof(cases "min (Le (- u_i j)) (D 0 j) = D 0 j")
    case True
    then show ?thesis using assms(2)
      by argo
  next
    case False
    hence "min (Le (- u_i j)) (D 0 j) = Le (- u_i j)"
      by fastforce
    then show ?thesis using assms(3) A 
      by presburger
  qed
next
  assume A:"L' j < u_i j"
  show "P (min (D 0 j) (Lt (- L' j)))"
  proof(cases "min (D 0 j)(Lt (- L' j)) = D 0 j")
    case True
    then show ?thesis using assms(2)
      by argo
  next
    case False
    hence "min (D 0 j) (Lt (- L' j))  = Lt (- L' j)"
      by fastforce
    then show ?thesis using assms(4) A 
      by argo
  qed
qed


lemma u_dbm_j0:
  assumes "j \<in> {1..n}"
  shows "u_dbm D j 0 = D j 0 \<or> (u_dbm D j 0 = Le ( u_i j) \<and> u_i j \<le> U' j)" 
  using assms
  by(rule u_dbm_dj0_rule[of j]; auto)

lemma u_dbm_E_1:
assumes "j \<in> {1..n}"
  and "u_i  j \<le> min (L' j)  (U' j)"
shows "u_dbm D 0 j = (Le (- u_i j))" 
  using assms u_dbm_0j_rule[of j]
  by (simp add: u_dbm_col_def u_dbm_def)

lemma u_dbm_zone_non_empty:
  assumes "\<lbrakk>u_dbm D\<rbrakk> = {}"
  shows "False"
proof -
  obtain i j where
    i_j: "i \<in> {1..n} \<and> j \<in> {1..n}"
    "u_dbm D 0 i + D i j + u_dbm D j 0 < 0"
    "i \<noteq> j"
    using cycle_u_dbm assms
    by blast
  hence i_j_le_n: "i \<le> n \<and> j \<le> n"
    by auto
  have zero_lt_i:"0 < i" using i_j(1)
    by auto
  text \<open>Cases for u_dbm D j 0\<close>
  consider (id) "u_dbm D j 0 = D j 0" |
           (is_u) "u_dbm D j 0 = Le (u_i j) \<and> u_i j \<le> U' j"
    using i_j u_dbm_j0[of j]
    by fast
  hence "\<not>(u_dbm D 0 i + D i j + u_dbm D j 0 < 0)"
  proof(cases)
    case id
    hence Di0_lt:"D i 0 \<le> D i j + u_dbm D j 0"
      using id D_canonical i_j
      by auto
    hence D0i_lt_0:"u_dbm D 0 i + D i 0 < 0" 
      using i_j add_mono_right[of "D i 0" "D i j + u_dbm D j 0" "u_dbm D 0 i"]
      by (simp add: add.assoc)
    show ?thesis
    proof(rule u_dbm_0j_rule[of i])
      show "i \<in> {1..n}" using i_j(1)
        by simp
    next
      assume min_cond:"u_i i \<le> min (L' i) (U' i)"
      hence "dbm_le (Le (u(v' i))) (D i 0)" 
        using u_apx i_j_le_n i_j(1)
        unfolding u_i_def L'_def U'_def
          using Lemma10_i vabs
          by auto
      hence "Le (u(v' i)) \<le> D i 0" 
        by (simp add: less_eq)
      hence *:"Le (u_i i) \<le> D i 0" unfolding u_i_def
        by presburger
      show "\<not> (Le (- u_i i) + D i j + u_dbm D j 0 < 0)"
      proof(rule notI)
        assume "Le (- u_i i) + D i j + u_dbm D j 0 < 0"
        hence "Le (- u_i i) + D i 0 < 0" 
          using Di0_lt add_mono_right
          using D0i_lt_0 min_cond u_dbm_E_1 i_j(1) by auto
        hence "D i 0 < Le (u_i i)"
          using Le_cancel_1[of "u_i i"] add_left_mono neutral
          by (metis Le_cancel_2 linorder_not_less)
        thus "False" using * by fastforce
      qed
    next
      assume between:"U' i < u_i i \<and> u_i i \<le> L' i"
      show "\<not> (min (Le (- u_i i)) (D 0 i) + D i j + u_dbm D j 0 < 0)"
      proof(rule notI)
        assume assm:"min (Le (- u_i i)) (D 0 i) + D i j + u_dbm D j 0 < 0"
        hence min_lt_z:"min (Le (- u_i i)) (D 0 i) + D i 0 < 0" 
          using Di0_lt 
            add_left_mono[of "D i 0" "D i j + u_dbm D j 0" "min (Le (- u_i i)) (D 0 i)"]
          by (simp add: add.assoc)
        hence "min (Le (- u_i i)) (D 0 i) = Le (- u_i i)"
          using D_through_zero[of i] i_j_le_n not_less by fastforce
        hence "Le (- u_i i) + D i 0 < 0"
          using min_lt_z by argo     
        hence "u_i i < U' i" 
          using between i_j(1) zero_gt_neg_u_i_Di0[of i] by fastforce
        thus "False" using between by linarith
      qed
    next
      assume A:"L' i < u_i i"
      show "\<not> (min (D 0 i) (Lt (- L' i)) + D i j + u_dbm D j 0 < 0)"
      proof(rule notI)
        assume assm: "min (D 0 i) (Lt (- L' i)) + D i j + u_dbm D j 0 < 0"
        hence min_lt:"min (D 0 i) (Lt (- L' i)) + D i 0 < 0"
          using Di0_lt 
            add_left_mono[of "D i 0" "D i j + u_dbm D j 0" "min (D 0 i) (Lt (- L' i))"]
          by (simp add: add.assoc)
        hence "min (D 0 i) (Lt (- L' i)) = Lt (- L' i)"
          using D_through_zero[of i] i_j_le_n not_less by fastforce
        hence "Lt (- L' i) + D i 0 < 0" using min_lt by argo
        thus "False" using i_j_le_n zero_lt_i  A zero_gt_u_dbm_L[of i]
          by blast
      qed
    qed
  next
    case is_u
    show ?thesis
    proof(rule u_dbm_0j_rule_alt[of i])
      show "i \<in> {1..n}" using i_j(1) by blast
    next
      show "\<not> D 0 i + D i j + u_dbm D j 0 < 0"
      proof(rule notI)
        assume A:"D 0 i + D i j + u_dbm D j 0 < 0"
        have "D 0 i + D i j \<ge> D 0 j" using i_j(1) D_canonical by auto
        hence "D 0 j + u_dbm D j 0 < 0" 
          using add_mono_left[of "D 0 j" "D 0 i + D i j" "u_dbm D j 0"]
          using A by auto
        hence "D 0 j + Le (u_i j) < 0" using is_u by argo
        thus "False" using reuse_Dj0_U_lt_0[of j] is_u i_j(1) by force
      qed
    next
      assume u_le_LU:"u_i i \<le> (L' i)"
      show "\<not> Le (- u_i i) + D i j + u_dbm D j 0 < 0"
      proof(rule notI)
        assume "Le (- u_i i) + D i j + u_dbm D j 0 < 0"
        hence assm:"Le (- u_i i) + D i j + Le (u_i j) < 0" 
          using is_u
          by argo
        hence "D i j + Le (u_i j) < Le (u_i i)" 
          using neutral Le_cancel_1[of "u_i i"]
          add_mono_left
          by (smt ab_semigroup_add_class.add.commute add.assoc linorder_not_less)
        have "Le (- u_i i) + Le (u_i j) + D i j < 0"
          using assm
          by (metis ab_semigroup_add_class.add.commute add.assoc)
        hence "Le (- u_i i + u_i j) + D i j < 0"
          by (simp add: add)
        hence "Le (u_i j - u_i i) + D i j < 0"
          by argo
        hence lt_u:"D i j < Le (u_i i - u_i j)"
          using neutral
          by (smt Le_cancel_1 add_left_mono linorder_not_less)
        hence entry_ninfty:"D i j \<noteq> DBM.INF"
          by fastforce
        hence "dbm_entry_val u (Some (v' i)) (Some (v' j)) (lu_apx l D i j)"
          using u_dbm_entry_val_3[of i j] using i_j(1)
          by argo
        hence bounded:"Le (u (v' i) - u(v' j)) \<le> lu_apx l D i j"
          by (cases "lu_apx l D i j"; auto)
        hence entry_lt_lu:"D i j < lu_apx l D i j"
          using lt_u
          unfolding u_i_def
          by auto
        have i_neq_j:"i \<noteq> j" using i_j(3) by simp
        have my_cases:"L' i < dbm_entry_bound (D i j)"
        proof(rule ccontr)
          assume "\<not> (L' i < dbm_entry_bound (D i j))"
          hence "L' i \<ge> dbm_entry_bound (D i j)"
            by linarith
          hence upper:"norm_upper (D i j) (L' i) = D i j"
            by(cases "D i j";auto)
          have "lu_apx l D i j = 
            norm_lower (norm_upper (D i j) (L' i) ) (- U' j)"
            unfolding lu_apx_def extra_lu_def L'_def U'_def
            using i_j(1) i_neq_j
            by auto
          hence "lu_apx l D i j = norm_lower (D i j) (- U' j)"
            using upper
            by argo
          hence "lu_apx l D i j = Lt(- U' j)" 
            using entry_lt_lu
            by fastforce
          hence "u (v' i) - u(v' j) < - U' j"
            using bounded
            by force
          hence "u (v' j) > u(v' i) + U' j"
            by argo
          hence *:"u_i j > u_i i + U' j"
            unfolding u_i_def
            by blast
          have "u_i i \<ge> 0"
            using i_j(1) bound_ge_zero[of i]
            by auto
          hence "u_i j > U' j" using *
            by linarith
          thus "False" using is_u
            by linarith
        qed
        hence "dbm_entry_bound (D i j) > u_i i"
            using u_le_LU
            by force
        hence "u_i j < 0"
            using lt_u
            by(cases "D i j"; auto)
          thus "False" using i_j(1) bound_ge_zero[of j]
            by auto
        qed
    next
      assume L_lt_u_i:"L' i < u_i i"
      hence **:"Lt (- L' i) > Lt (- u_i i)"
        by fastforce
      have "L' i \<ge> 0" 
        unfolding L'_def
        by fastforce
      hence **:"u_i i > 0" using L_lt_u_i
        by linarith
      show "\<not>  Lt (- L' i) + D i j + u_dbm D j 0 < 0"
      proof(rule notI)
        assume " Lt (- L' i) + D i j + u_dbm D j 0 < 0"
        hence *:"Lt (- L' i) + D i j + Le (u_i j) < 0"
          using is_u by argo
        hence "Lt (- L' i) + D i j < 0"
          using bound_ge_zero[of j] neutral
          by (metis add_nonneg_nonneg atLeastAtMost_iff dbm_less_eq_simps(1) gr_zeroI i_j(1) less_numeral_extra(1) linorder_not_less)
        
        hence "D i j \<le> Le (L' i)"
          by(cases "D i j";auto simp: neutral add *)
        hence "\<not> Le (L' i) \<prec> D i j"
          by (simp add: less less_eq)
        hence upper:"norm_upper (D i j) (L' i) = D i j"
          by fastforce
        hence "Lt (- U' j) < Le (- u_i j)"
          using is_u
          by fastforce
        have "lu_apx l D i j = norm_lower (norm_upper (D i j) (L' i)) (- U' j)"
          unfolding lu_apx_def 
          extra_lu_def L'_def U'_def
          using i_j(1) i_j(3)
          by simp
        hence "lu_apx l D i j = norm_lower (D i j) (- U' j)"
          using upper
          by argo
        
        hence lu:"lu_apx l D i j = D i j \<or>
               lu_apx l D i j = Lt (- U' j)"
          by auto
        
        have bound:"dbm_entry_val u (Some (v' i)) (Some (v' j)) (lu_apx l D  i j)"
          using u_dbm_entry_val_3[of i j] i_j(1) by argo
        have "lu_apx l D i j \<noteq> Lt (- U' j)"
        proof(rule notI)
          assume "lu_apx l D i j = Lt (- U' j)"
          hence "u (v' i) - u (v' j) < - U' j"
            using bound
            by auto
          hence "u (v' i) < 0" 
            using is_u 
            unfolding u_i_def
            by linarith
          thus "False" 
            using bound_ge_zero[of i] i_j(1)
            using u_i_def by auto
        qed
        hence lu_id:"lu_apx l D i j = D i j"
          using lu
          by blast
        text\<open>Have a look at lu_apx l D i j\<close>
        show "False"
        proof(cases "D i j")
          case (Le x1)
          hence "u_i i - u_i j \<le> x1" 
            using bound lu_id unfolding u_i_def
            by auto
          hence "- u_i i + x1 + u_i j \<ge> 0"
            by argo
          hence b:"Lt (- u_i i + x1 + u_i j) \<ge> Lt 0"
            by blast
          have c:"Lt (- L' i) + D i j + Le (u_i j) = Lt (- L' i + x1 + u_i j)"
            using Le
            by (simp add: add)
          hence "Lt (- L' i) + D i j + Le (u_i j) > Lt (- u_i i + x1 + u_i j)"
            using L_lt_u_i
            by fastforce
          hence "Lt (- L' i) + D i j + Le (u_i j) > Lt 0"
            using b 
            by (smt DBM.less_eq dbm_le_def linorder_not_less linordered_monoid.dual_order.strict_trans)
          hence "Lt (- L' i) + D i j + Le (u_i j) \<ge> 0"
            using neutral
            by (simp add: neutral Lt_Lt_dbm_lt_D c)
          then show ?thesis 
            using *
            by fastforce
        next
          case (Lt x2)
          hence "u_i i - u_i j < x2" 
            using bound lu_id unfolding u_i_def
            by auto
          hence "- u_i i + x2 + u_i j > 0"
            by linarith
          hence "- L' i + x2 + u_i j > 0" 
            using L_lt_u_i
            by linarith
          hence "Lt ( x2 - L' i + u_i j) \<ge> Le 0"

            by simp
          hence "Lt (- L' i) + D i j + Le (u_i j) \<ge> 0"
            using Lt by(simp add: add neutral)
          then show ?thesis using *
            by fastforce
        next
          case INF
          then show ?thesis using *
            by force
        qed
      qed
    qed
  qed
  thus "False" using i_j(2) by blast
qed

section \<open>Final result\<close>

lemma P_u_non_empty:
  assumes "Z \<noteq> {}"
  shows "P_u \<noteq> {}"
  using u_dbm_repr_P_u u_dbm_zone_non_empty
  by blast
end


lemma Theorem_Bouyer: 
  assumes "vabstr' Z M"
  and "Z \<noteq> {}"
  shows 
    "\<lbrakk>lu_apx l M\<rbrakk> \<subseteq> local.abs l Z"
proof
  fix u
  assume *:"u \<in> \<lbrakk>lu_apx l M\<rbrakk>"
  hence "P_u l u M \<noteq> {}" 
    using assms P_u_non_empty by blast
  hence "\<exists>u' \<in> Z. sim (l, u) (l, u')" 
    using * assms by auto
  thus "u \<in> abs l Z" unfolding abs_def
    by blast
qed

lemma lu_apx_\<alpha>:
  assumes "vabstr' Z M"
  shows "\<lbrakk>lu_apx l M\<rbrakk> \<subseteq> local.abs l Z"
proof(cases "Z = {}")
  case True
  then show ?thesis using assms case_zone_repr_empty by blast
next
  case False
  then show ?thesis using assms Theorem_Bouyer by blast
qed

interpretation extra: TA_Extrapolation where
  A = A and
  extra = "lu_apx" and
  sim = sim
  apply standard
  subgoal \<comment> \<open>Only non-negative clock valuations are simulated\<close>
    unfolding V_def unfolding X_is_clk_set by (auto simp: img_fst sim_nonneg)
  subgoal for Z M l \<comment> \<open>@{ extra_lu} extrapolates\<close>
    using clock_numbering(1) unfolding lu_apx_def by (auto intro: extra_lu_mono)
  subgoal for Z M l \<comment> \<open>The key property\<close>
    using lu_apx_\<alpha> by simp
  subgoal \<comment> \<open>Finite Extrapolation\<close>
    using extra_lu_finite \<comment> \<open>XXX: Does not quite fit yet\<close>
    sorry
  subgoal \<comment> \<open>Extrapolation keeps DBMs integral\<close>
    unfolding lu_apx_def by (intro extra_lu_preservation) auto
  \<comment> \<open>Properties of the starting state. Don't care for now, not instantiated.\<close>
  sorry

end

end