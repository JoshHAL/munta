theory TA_Simulation_LU
  imports TA_Simulation
begin

text\<open>Shouldn't we also assume L(v' 0) = 0\<close>


locale TA_LU2 =
  Regions_TA where A = A +
  TA_LU where A = A and L = L and U = U
  for A  :: "('a, 'c, real, 'l) ta" and L :: "'l \<Rightarrow> 'c \<Rightarrow> nat" and U :: "'l \<Rightarrow> 'c \<Rightarrow> nat" +
  assumes X_is_clk_set: "X = clk_set A"
begin

abbreviation zone_of ("\<lbrakk>_\<rbrakk>") where "zone_of M \<equiv> [M]\<^bsub>v,n\<^esub>"

definition lu_apx where
  "lu_apx l M = extra_lu M (\<lambda>x. real (L l (v' x))) (\<lambda>x. real (U l (v' x))) n"





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

lemma norm_upper_infinity:
  assumes "norm_upper e t = DBM.INF"
  shows "Le t \<prec> e"
  using assms by(cases "Le t \<prec> e"; auto)

text\<open>
This is Lemma 8 from @{cite "BehrmannBLP06"}.\<close>

lemma Lemma8:
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
    using norm_upper_infinity[of "(M j 0)" "(real (L l ?x))"] by fast
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


text\<open> Lemma 9 from the Paper\<close>
lemma Lemma9:
  assumes Hyp: "vabstr' Z M"
  and zero_i_n:"i \<le> n \<and> 0 < i"
  and "M 0 i \<noteq> (lu_apx l M) 0 i"
shows "lt_as_bound (M 0 i) (- U l (v' i))"
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
      using base norm_lower_pres_ninf norm_upper_infinity 
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

text\<open>Lemmata 10 i) and ii) from the Paper vital in Proving the DBM that will be constructed is 
    subset of the zone abstraction later on\<close>

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
  and "i \<le> n"
  and "i > 0"
  and "vabstr' Z D"
shows "(Le (- u (v' i))) \<le> (D 0 i)"
proof -
let ?x = "v' i"
  let ?U = "(U l ?x)"
  have clock_num:"v ?x = i"
    using assms clock_numbering(2) v_v' by auto
  hence x_i_less_n: "v ?x \<le> n" using assms by argo
  have \<star>:"dbm_entry_val u None (Some ?x) (lu_apx l D 0 i)"
      using assms(1) 
      unfolding DBM_zone_repr_def DBM_val_bounded_def
      using x_i_less_n clock_num
      by fastforce
  have lu_start:"lu_apx l D 0 i = norm_lower (norm_upper (D 0 i) 0) (- ?U)"
      unfolding lu_apx_def extra_lu_def Let_def
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
      have "dbm_nonneg n D" using assms
        unfolding canonical_dbm_def
        by simp
      hence "D 0 i \<le> 0"
        unfolding dbm_nonneg_def
        using assms(3-4)
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
    hence **:"\<not> (D 0 i) \<prec> Lt (- ?U)"
      by (simp add: less_eq)
    then show ?thesis
    proof(cases "Le 0 \<prec> D 0 i")
      case True
      have "dbm_nonneg n D" using assms
        unfolding canonical_dbm_def
        by simp
      hence "D 0 i \<le> 0"
        unfolding dbm_nonneg_def
        using assms(3-4)
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
      hence "lu_apx l D 0 i = D 0 i" using ** lu_start
        by force
      hence "dbm_entry_val u None (Some ?x) (D 0 i)"
        using \<star> 
        by argo
      hence "Le (- u ?x) \<le> D 0 i"
        by (cases "D 0 i"; force+)
      then show ?thesis by simp
    qed
  qed
qed


text\<open>Building for each v \<in> [| lu_apx D |] an DBM M s.t. 
    P_v := {v' \<in> [|D|] | sim (l,v) (l, v')} \<supseteq> [|M|]
    TODO:Next step show  [|M|]  \<noteq> \<emptyset>, by showing M doesnot contain zero cycles.
    Thus P_v \<noteq> \<emptyset> and thereby \<lbrakk>lu_apx l M\<rbrakk> \<subseteq> abs l Z\<close>

context
  fixes l::'l
  fixes u::"('c,real) cval"
  fixes D::"real DBM"
  fixes Z
  assumes vabs:"vabstr' Z D"
  and u_apx:"u \<in> \<lbrakk>lu_apx l D\<rbrakk>"
begin

definition u_i
  where "u_i i \<equiv> u (v' i)"


definition L'
  where "L' i \<equiv> if i = 0 then 0 else real (L l (v' i))"

definition U'
  where "U' i \<equiv> if i = 0 then 0 else real (U l (v' i))"

definition abs_row :: "nat \<Rightarrow> real DBMEntry \<Rightarrow> real DBMEntry"
  where
    "abs_row i e \<equiv>
      let b = Le (u_i i) in 
      if u_i i \<le> min (L' i)  (U' i) then b
      else if L' i < u_i i \<and> u_i i \<le> U' i then dmin b e
      else e"

definition abs_col :: "nat \<Rightarrow> real DBMEntry \<Rightarrow> real DBMEntry"
  where
    "abs_col i e \<equiv>
      let ub = Le (-u_i i) in
      if u_i i \<le> min (L' i)  (U' i) then ub
      else if U' i < u_i i \<and> u_i i \<le> L' i then dmin ub e
      else dmin e (Lt (-L' i))"

definition abs_dbm :: "real DBM \<Rightarrow> real DBM"
  where
    "abs_dbm M \<equiv> \<lambda>i j.
      if i = 0 \<and> j = 0 then M i j
      else if j = 0 \<and> i \<le> n then abs_row i (M i j)
      else if i = 0 \<and> j \<le> n then abs_col j (M i j)
      else M i j"


abbreviation P_u
  where
    "P_u \<equiv> {u' \<in> \<lbrakk>D\<rbrakk>. sim (l,u) (l,u')}"


lemma zero_invar:
  assumes "DBM_val_bounded v x (abs_dbm D) n"
  shows "dbm_le (Le 0) (D 0 0)"
proof -
  have "dbm_le (Le 0) (abs_dbm D 0 0)" 
    using assms unfolding DBM_val_bounded_def by blast
  thus ?thesis unfolding abs_dbm_def by simp
qed

lemma helper1:
  assumes "j \<le> n"
  and "0 < j"
  and "u_i j \<le> min (U' j) (L' j)"
  shows "dbm_le (abs_dbm D 0 j) (D 0 j)"
proof -
  have abs:"abs_dbm D 0 j  = Le (- u_i j)"
    unfolding abs_dbm_def abs_col_def using assms
    by auto
  have **:"u (v' j) \<le> min (L' j) (U' j)" using assms u_i_def
      by auto
  have "(Le (- u (v' j))) \<le> (D 0 j)" 
      using u_apx ** assms(2)  assms(1) vabs Lemma10_ii[of "u" "l" "D" "j" "Z"] L'_def U'_def 
      by auto
  hence "dbm_le (abs_dbm D 0 j) (D 0 j)"
      using abs u_i_def
      by (simp add: DBM.less_eq)
   thus ?thesis.
  qed

lemma helper2:
  assumes "i \<le> n"
  and "0 < i"
  and "u_i i \<le> min (U' i) (L' i)"
  shows "dbm_le (abs_dbm D i 0) (D i 0)"
proof -
  have abs:"abs_dbm D i 0 = Le (u_i i)"
    unfolding abs_dbm_def abs_row_def using assms
    by auto
  have **:"u (v' i) \<le> min (L' i) (U' i)" using assms u_i_def
      by auto
  have "(Le (u (v' i))) \<le> (D i 0)" 
      using u_apx ** assms(2)  assms(1) vabs Lemma10_i[of "u" "l" "D" "i" "Z"] L'_def U'_def
      by fastforce
  hence "dbm_le (abs_dbm D i 0) (D i 0)"
      using abs u_i_def
      by (simp add: DBM.less_eq)
   thus ?thesis.
  qed

lemma abs_dbm_mono:
  assumes "i \<le> n"
  and "j \<le> n"
  shows "dbm_le (abs_dbm D i j) (D i j)"
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
    hence "abs_dbm D i j = D i j"
      unfolding abs_dbm_def
      by simp
    then show ?thesis
      by fastforce
  next
    case c1_zero
    hence abs:"abs_dbm D i j = abs_col j (D 0 j)"
      unfolding abs_dbm_def using assms(2)
      by presburger
    consider 
    (before) "u_i j \<le> min (L' j)  (U' j)" |
    (middle) "U' j < u_i j \<and> u_i j \<le> L' j" |
    (bigger_than_L) "L' j < u_i j"
    by linarith
  then show ?thesis
  proof(cases)
    case before
    hence "dbm_le (abs_dbm D 0 j) (D 0 j)"
      using c1_zero assms helper1
      by simp
    then show ?thesis using c1_zero
      by argo
  next
    case middle
    hence "abs_dbm D i j = dmin (Le (- u_i j)) (D 0 j)"
      using abs unfolding abs_col_def
      by simp
    then show ?thesis using c1_zero
      by fastforce
  next
    case bigger_than_L
    hence "abs_dbm D i j =  dmin (D 0 j) (Lt (- L' j))"
      using abs unfolding abs_col_def
      by auto
    then show ?thesis using c1_zero
      by fastforce
  qed
  next
    case c2_zero
    have *:"abs_dbm D i j = abs_row i (D i 0)"
      unfolding abs_dbm_def using c2_zero assms(1)
      by auto
    consider 
    (before) "u_i i \<le> min (L' i)  (U' i)" |
    (middle) "L' i < u_i i \<and> u_i i \<le> U' i" |
    (bigger_than_U) "U' i < u_i i"
    by linarith
  then show ?thesis
  proof(cases)
    case before
    hence "dbm_le (abs_dbm D i 0) (D i 0)"
      using c2_zero assms(1) helper2
      by force
    then show ?thesis using c2_zero
      by argo
  next
    case middle
    hence "abs_dbm D i j =  dmin (Le (u_i i)) (D i 0)"
      using *
      unfolding abs_row_def
      by auto
    then show ?thesis using c2_zero
      by auto
  next
    case bigger_than_U
    hence "abs_dbm D i j =  (D i 0)"
      using * unfolding abs_row_def
      by simp
    then show ?thesis using c2_zero
      by fastforce
  qed
  next
    case neq_zero
    hence "abs_dbm D i j = D i j"
      unfolding abs_dbm_def
      by simp
    then show ?thesis by fastforce
  qed
qed

lemma cor1:
  assumes "v c \<le> n"
  shows "dbm_le (abs_dbm D (v c) 0) (D (v c) 0)"
  using assms abs_dbm_mono
  by blast

lemma cor2:
  assumes "v c \<le> n"
  shows "dbm_le (abs_dbm D 0 (v c)) (D 0 (v c))"
  using assms abs_dbm_mono
  by blast

lemma bounded1_i:
assumes "DBM_val_bounded v x (abs_dbm D) n"
  and "v c \<le> n"
shows "dbm_entry_val x None (Some c) (D 0 (v c))"
proof -
  have *:"dbm_entry_val x None (Some c) (abs_dbm D 0 (v c))"
    using assms unfolding DBM_val_bounded_def by blast
  have "dbm_le (abs_dbm D 0 (v c)) (D 0 (v c))"
    using cor2 assms(2)
    by blast
  thus ?thesis using * dbm_entry_val_mono(2)
    by fastforce
qed

lemma bounded1_ii:
 assumes "DBM_val_bounded v x (abs_dbm D) n"
  and "v c \<le> n"
shows "dbm_entry_val x (Some c) None (D (v c) 0)"
proof -
  have *:"dbm_entry_val x (Some c) None (abs_dbm D (v c) 0)"
    using assms unfolding DBM_val_bounded_def by blast
  have "dbm_le (abs_dbm D (v c) 0) (D (v c) 0)"
    using cor1 assms(2)
    by blast
  thus ?thesis using * dbm_entry_val_mono(3)
    by fastforce
qed

lemma abs_dbm_pres_bounded1_i:
  assumes "DBM_val_bounded v x (abs_dbm D) n"
  shows "\<forall>c. v c \<le> n \<longrightarrow> dbm_entry_val x None (Some c) (D 0 (v c))"
  using assms bounded1_i by blast

lemma abs_dbm_pres_bounded1_ii:
  assumes "DBM_val_bounded v x (abs_dbm D) n"
  shows "\<forall>c. v c \<le> n \<longrightarrow> dbm_entry_val x (Some c) None (D (v c) 0)"
  using assms bounded1_ii by blast

lemma abs_dbm_pres_bounded1:
  assumes "DBM_val_bounded v x (abs_dbm D) n"
  shows "\<forall>c. v c \<le> n \<longrightarrow> 
             dbm_entry_val x None (Some c) (D 0 (v c)) \<and> dbm_entry_val x (Some c) None (D (v c) 0)"
  using assms abs_dbm_pres_bounded1_i abs_dbm_pres_bounded1_ii
  by presburger

lemma abs_dbm_pres_bounded2':
  assumes "DBM_val_bounded v x (abs_dbm D) n"
  and "v c1 \<le> n"
  and "v c2 \<le> n"
shows "dbm_entry_val x (Some c1) (Some c2) (D (v c1) (v c2))"
proof -
  have "dbm_le (abs_dbm D (v c1) (v c2)) (D (v c1) (v c2))"
    using abs_dbm_mono assms
    by blast
  hence is_min:"min (abs_dbm D (v c1) (v c2)) (D (v c1) (v c2)) = (abs_dbm D (v c1) (v c2))"
    by (simp add: DBM.less_eq)
  have "dbm_entry_val x (Some c1) (Some c2) (abs_dbm D (v c1) (v c2))"
    using assms unfolding DBM_val_bounded_def
    by blast
  thus ?thesis 
    using is_min dbm_entry_dbm_min[of "x" "c1" "c2" "abs_dbm D (v c1) (v c2)" "D (v c1) (v c2)"]
    by argo
qed

lemma abs_dbm_pres_bounded2:
  assumes "DBM_val_bounded v x (abs_dbm D) n"
  shows "\<forall> c1 c2. v c1 \<le> n \<and> v c2 \<le> n \<longrightarrow> dbm_entry_val x (Some c1) (Some c2) (D (v c1) (v c2))"
  using assms abs_dbm_pres_bounded2' by simp

lemma abs_dbm_pres_bounded:
  assumes "DBM_val_bounded v x (abs_dbm D) n"
  shows "DBM_val_bounded v x D n"
proof -
  have b1:"\<forall>c. v c \<le> n \<longrightarrow> 
            (dbm_entry_val x None (Some c) (D 0 (v c)) \<and> dbm_entry_val x (Some c) None (D (v c) 0))"
    using assms abs_dbm_pres_bounded1
    by fast
  have b2:"\<forall> c1 c2. v c1 \<le> n \<and> v c2 \<le> n \<longrightarrow> 
            dbm_entry_val x (Some c1) (Some c2) (D (v c1) (v c2))"
    using assms abs_dbm_pres_bounded2
    by blast
  have zero:
    "dbm_le (Le 0) (D 0 0)"
    using assms zero_invar
    by blast
  show ?thesis unfolding DBM_val_bounded_def using zero b1 b2
    by blast
qed

lemma abs_subset_input:
  "\<lbrakk>abs_dbm D\<rbrakk> \<subseteq> \<lbrakk>D\<rbrakk>"
proof
  fix "x"
  assume "x \<in> \<lbrakk>abs_dbm D\<rbrakk>"
  hence "DBM_val_bounded v x (abs_dbm D) n" unfolding DBM_zone_repr_def by fast
  hence "DBM_val_bounded v x D n" using abs_dbm_pres_bounded try0
    by blast
  thus "x \<in> \<lbrakk>D\<rbrakk>" unfolding DBM_zone_repr_def by fast
qed

lemma D_sset:"\<lbrakk>D\<rbrakk> \<subseteq> \<lbrakk>lu_apx l D\<rbrakk>"
  by (simp add: clock_numbering(1) extra_lu_mono lu_apx_def subsetI)

text\<open>How about proof by contradiction\<close>
lemma TODO:
  assumes "u' \<in> \<lbrakk>abs_dbm D\<rbrakk>"
  and "x \<in> X"
  and "u' x < u x"
shows "u' x > L l x"
proof -
  obtain j where id_j:"v' j = x"
    using assms(2) v_v' by blast
  have "u' (v' j) < u_i j"
    using assms unfolding u_i_def using id_j 
    by blast
  have "u' \<in> \<lbrakk>D\<rbrakk>" using assms(1) abs_subset_input
    by blast
  hence "u' \<in> \<lbrakk>lu_apx l D\<rbrakk>" using D_sset by blast
  show ?thesis sorry
qed

lemma abs_dbm_repr_P_u:
  "\<lbrakk>abs_dbm D\<rbrakk> \<subseteq> P_u"
  proof
    fix u'
    assume a:"u' \<in> \<lbrakk>abs_dbm D\<rbrakk>"
    hence "DBM_val_bounded v u' (abs_dbm D) n" unfolding DBM_zone_repr_def by fast
    have sset: "u' \<in> \<lbrakk>D\<rbrakk>" using abs_subset_input a
      by blast
    have "u' \<in> \<lbrakk>D\<rbrakk> \<and> sim (l, u) (l, u')" sorry
    then show "u' \<in> P_u"
      by fast
  qed

lemma abs_dbm_repr_non_empty:
  "\<lbrakk>abs_dbm D\<rbrakk> \<noteq> {}"
  sorry

lemma P_u_non_empty:
  "P_u \<noteq> {}"
  using abs_dbm_repr_P_u abs_dbm_repr_non_empty
  by blast
end



lemma Theorem_Bouyer: 
  assumes "vabstr' Z M"
  shows 
    "\<lbrakk>lu_apx l M\<rbrakk> \<subseteq> local.abs l Z"
proof
  fix u
  assume *:"u \<in> \<lbrakk>lu_apx l M\<rbrakk>"
  hence "P_u l u M \<noteq> {}" 
    using assms P_u_non_empty by blast
  hence "\<exists>u' \<in> Z. sim (l, u) (l, u')" 
    using * assms by auto
  thus "u \<in> abs l Z" using abs_def by blast
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