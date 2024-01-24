theory SpreadsSAT
imports Main "HOL-Library.Code_Target_Int" "HOL-Library.Code_Target_Nat"
begin

type_synonym point = nat
type_synonym line = "point list"

definition lines :: "line list" where
"lines = [[0, 1, 2],
          [0, 3, 4],
         [0, 5, 6],
         [0, 7, 8],
         [0, 10, 9],
         [0, 11, 12],
         [0, 13, 14],
         [1, 4, 6],
         [1, 8, 10],
         [1, 12, 14],
         [1, 7, 9],
         [1, 13, 11],
         [1, 3, 5],
         [2, 7, 10],
         [2, 11, 14],
         [2, 3, 6],
         [2, 12, 13],
         [2, 4, 5],
         [2, 8, 9],
         [3, 10, 14],
         [3, 8, 12],
         [3, 9, 13],
         [3, 7, 11],
         [4, 9, 14],
         [4, 8, 11],
         [4, 10, 13],
         [4, 7, 12],
         [5, 8, 14],
         [5, 7, 13],
         [5, 9, 11],
         [5, 10, 12],
         [6, 7, 14],
         [6, 8, 13],
         [6, 9, 12],
         [6, 10, 11]]"

lemma distinct_lines:
  shows "distinct (map set lines)"
  by eval
  
definition all_points where
  "all_points = remdups (sort (concat lines))"

lemma all_points:
  shows "all_points = [0..<15]"
  by eval

type_synonym line_index = nat

text\<open>Indices of lines that contain the given point\<close>
definition point_lines :: "point \<Rightarrow> line list \<Rightarrow> line_index list" where
   "point_lines p ls = map fst (filter (\<lambda> (i, l). p \<in> set l) (zip [0..<length ls] ls))"

lemma distinct_point_lines:
  shows "distinct (point_lines p lines)"
  unfolding point_lines_def
  by (simp add: distinct_map_filter)

lemma set_point_lines:
  shows "set (point_lines p ls) = {i. i < length ls \<and> p \<in> set (ls ! i)}"
proof safe
  fix x
  assume "x \<in> set (point_lines p ls)"
  then show "x < length ls" "p \<in> set (ls ! x)"
    unfolding point_lines_def
    by (auto simp add: set_zip)
next
  fix x
  assume "x < length ls" "p \<in> set (ls ! x)"
  then have "(\<lambda> (i, l). p \<in> set l) (x, ls ! x)" "(x, ls ! x) \<in> set (zip [0..<length ls] ls)"
    by (force simp add: in_set_zip)+
  then have "(x, ls ! x) \<in> set (filter (\<lambda>(i, l). p \<in> set l) (zip [0..<length ls] ls))"
    by (subst set_filter, simp)
  then show "x \<in> set (point_lines p ls)"
    unfolding point_lines_def
    by (metis in_set_zipE zip_map_fst_snd)
qed

definition all_pairs where
  "all_pairs xs =
    (let n = length xs
      in concat (map (\<lambda> i. map (\<lambda> j. (xs ! i, xs ! j)) [i+1..<n]) [0..<n]))"

lemma set_all_pairs:
  "set (all_pairs vs) = {(vs ! i,  vs ! j) | i j. i < j \<and> j < length vs}"
proof safe
  fix a b
  assume "(a, b) \<in> set (all_pairs vs)"
  then have "\<exists>i\<in>{0..<length vs}. (a, b) \<in> (\<lambda>j. (vs ! i, vs ! j)) ` {i+1..<length vs}"
    unfolding all_pairs_def Let_def
    by simp
  then obtain i j where "i\<in>{0..<length vs}" "j \<in> {i+1..<length vs}" "(a, b) = (vs ! i, vs ! j)"
    by blast
  then show "\<exists>i j. (a, b) = (vs ! i, vs ! j) \<and> i < j \<and> j < length vs"
  by (metis Suc_eq_plus1 Suc_le_lessD atLeastLessThan_iff)
next
  fix  i j
  assume "i < j" "j < length vs"
  then have "i \<in> {0..<length vs}" "j \<in> {i+1..<length vs}"
    by auto
  then have "(vs ! i, vs ! j) \<in> (\<lambda>j. (vs ! i, vs ! j)) ` {i+1..<length vs}"
    by blast
  then show "(vs ! i, vs ! j) \<in> set (all_pairs vs)"
    unfolding all_pairs_def Let_def
    by force
qed

definition satisfies_lit :: "(nat \<Rightarrow> bool) \<Rightarrow> int \<Rightarrow> bool" where
  "satisfies_lit val lit \<longleftrightarrow> (if lit > 0 then val (nat lit) else \<not> val (nat (-lit)))"
definition satisfies_clause :: "(nat \<Rightarrow> bool) \<Rightarrow> int list \<Rightarrow> bool" where
  "satisfies_clause val cl \<longleftrightarrow> (\<exists> lit \<in> set cl. satisfies_lit val lit)"
definition satisfies_formula :: "(nat \<Rightarrow> bool) \<Rightarrow> int list list \<Rightarrow> bool" where
   "satisfies_formula val fml \<longleftrightarrow> (\<forall> cl \<in> set fml. satisfies_clause val cl)"

definition exactly1 :: "nat list \<Rightarrow> int list list" where
  "exactly1 ls =  (map int ls) # 
                   map (\<lambda> (i, j). [-(int i), - (int j)]) (all_pairs ls)"

definition exactly1_val where
 "exactly1_val val vs \<longleftrightarrow> 
  (\<exists> v \<in> set vs. val v = True \<and> (\<forall> v' \<in> set vs. v' \<noteq> v \<longrightarrow> val v' = False))"

lemma exactly1:
  assumes "0 \<notin> set vs" "distinct vs"
  shows "(\<forall> clause \<in> set (exactly1 vs). satisfies_clause val clause) \<longleftrightarrow>
         exactly1_val val vs" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have "satisfies_clause val (map int vs)" and 
    *: "(\<forall> (i, j) \<in>set (all_pairs vs). satisfies_clause val [- int i, - int j])"
    unfolding exactly1_def
    by auto
  obtain v where "v \<in> set vs" "val v"
    using \<open>satisfies_clause val (map int vs)\<close> assms
    unfolding satisfies_clause_def satisfies_lit_def
    by (auto split: if_split_asm)
  moreover
  have "\<forall>v'\<in>set vs. v' \<noteq> v \<longrightarrow> val v' = False"
  proof safe
    fix v'
    assume "v' \<in> set vs" "v' \<noteq> v" "val v'"
    then obtain i j where ij: "i < length vs" "j < length vs" "i \<noteq> j" "v = vs ! i" "v' = vs ! j"
      using \<open>v \<in> set vs\<close>
      by (metis in_set_conv_nth)
    then have "\<not> satisfies_clause val [- (int (vs ! i)), - (int (vs ! j))]"
              "\<not> satisfies_clause val [- (int (vs ! j)), - (int (vs ! i))]"
      using \<open>val v\<close> \<open>val v'\<close>
      unfolding satisfies_clause_def satisfies_lit_def
      by auto
    moreover
    have "(vs ! i, vs ! j) \<in> set (all_pairs vs) \<or> (vs ! j, vs ! i) \<in> set (all_pairs vs)"
      using ij
      unfolding set_all_pairs
      by (cases "i < j", auto)
    ultimately show False
      using *
      by auto
  qed
  ultimately
  show ?rhs
    unfolding exactly1_val_def
    by auto
next
  assume ?rhs
  then obtain v where v: "v\<in>set vs" "val v" "\<forall>v'\<in>set vs. v' \<noteq> v \<longrightarrow> val v' = False"
    unfolding exactly1_val_def
    by auto
  show ?lhs
  proof
    fix clause
    assume "clause \<in> set (exactly1 vs)"
    then have "clause = map int vs \<or>
               clause \<in> (\<lambda>(i, j). [- int i, - int j]) ` set (all_pairs vs)"
      unfolding exactly1_def
      by simp
    then show "satisfies_clause val clause"
    proof
      assume "clause = map int vs"
      then show "satisfies_clause val clause"
        using v assms
        by (auto simp add: satisfies_clause_def satisfies_lit_def)
    next
      assume "clause \<in> (\<lambda>(i, j). [- int i, - int j]) ` set (all_pairs vs)"
      then obtain i j where "i < j" "j < length vs" "clause = [- int (vs ! i), - int (vs ! j)]"
        unfolding set_all_pairs
        by auto
      then show "satisfies_clause val clause"
        using v \<open>distinct vs\<close>
        unfolding satisfies_clause_def satisfies_lit_def
        by (smt (verit, ccfv_SIG) distinct_conv_nth insert_iff list.set(2) nat_int nat_neq_iff nth_mem of_nat_less_0_iff order_less_trans)
    qed
  qed
qed

definition L :: "line_index \<Rightarrow> nat" where 
  "L l = l + 1"

definition spreadsSAT where
 "spreadsSAT = concat (map (\<lambda> p. exactly1 (map L (point_lines p lines))) all_points)"

lemma spreadsSAT_nonzero:
  shows "\<forall> clause \<in> set spreadsSAT. 0 \<notin> set clause"
  unfolding spreadsSAT_def
  by (auto simp add: exactly1_def set_all_pairs L_def)

lemma spreadsSAT_distinct:
  shows "\<forall> clause \<in> set spreadsSAT. distinct clause"
  using distinct_point_lines
  unfolding spreadsSAT_def
  by (auto simp add: exactly1_def set_all_pairs L_def distinct_map inj_on_def nth_eq_iff_index_eq )
 
lemma satisfies_formula:
  "satisfies_formula val spreadsSAT \<longleftrightarrow> 
  (\<forall> p \<in> set (all_points). exactly1_val val (map L (point_lines p lines)))"
proof-
  have "\<forall> p \<in> set all_points. distinct (map L (point_lines p lines))"
    using distinct_point_lines
    by (simp add: L_def distinct_conv_nth)
  moreover
  have "\<forall> p \<in> set all_points. 0 \<notin> set (map L (point_lines p lines))"
    by (metis L_def Suc_eq_plus1 ex_map_conv nat.distinct(1))
  ultimately
  show ?thesis
    using exactly1
    unfolding satisfies_formula_def spreadsSAT_def
    by auto
qed

definition is_partition :: "(point set) list \<Rightarrow> bool" where
  "is_partition s \<longleftrightarrow> 
    (\<forall> p \<in> set (all_points). (\<exists> i. i < length s \<and> p \<in> s ! i)) \<and>
    (\<forall> l1 \<in> set s. \<forall> l2 \<in> set s. l1 \<noteq> l2 \<longrightarrow> l1 \<inter> l2 = {})"

lemma is_partition:
  assumes "distinct s" "\<Union> (set s) \<subseteq> set all_points"
  shows "is_partition s \<longleftrightarrow> (\<forall> p \<in> set (all_points). \<exists>! i. i < length s \<and> p \<in> s ! i)"
proof
  assume "is_partition s"
  then show "(\<forall> p \<in> set (all_points). \<exists>! i. i < length s \<and> p \<in> s ! i)"
    using \<open>distinct s\<close>
    by (metis IntI  empty_iff is_partition_def nth_eq_iff_index_eq nth_mem)
next
  assume *: "(\<forall> p \<in> set (all_points). \<exists>! i. i < length s \<and> p \<in> s ! i)"
  show "is_partition s"
    unfolding is_partition_def
  proof
    show "\<forall>p\<in>set all_points. \<exists>i<length s. p \<in> s ! i"
    proof
      fix p
      assume "p \<in> set all_points"
      then obtain i where "i < length s" "p \<in> s ! i" and i': "\<forall> i'. i' < length s \<and> p \<in> s ! i' \<longrightarrow> i' = i"
        using *
        unfolding Ex1_def
        by auto
      then show "\<exists> i < length s. p \<in> s ! i"
        by auto
    qed
  next
    show "\<forall>l1\<in>set s. \<forall>l2\<in>set s. l1 \<noteq> l2 \<longrightarrow> l1 \<inter> l2 = {}"
    proof (rule ballI, rule ballI, rule impI)
      fix l1 l2
      assume "l1 \<in> set s" "l2 \<in> set s" "l1 \<noteq> l2"
      show "l1 \<inter> l2 = {}"
      proof (rule ccontr)
        assume "l1 \<inter> l2 \<noteq> {}"
        then obtain p where "p \<in> l1" "p \<in> l2"
          by auto
        then have "p \<in> set all_points"
          using \<open>l1 \<in> set s\<close> \<open>\<Union> (set s) \<subseteq> set all_points\<close>
          by auto
        then have "\<exists>! i. i < length s \<and> p \<in> s ! i"
          using *
          by simp
        then show False
          using \<open>l1 \<in> set s\<close> \<open>l2 \<in> set s\<close> \<open>p \<in> l1\<close> \<open>p \<in> l2\<close> \<open>l1 \<noteq> l2\<close> \<open>distinct s\<close>
          by (metis distinct_Ex1)
      qed
    qed
  qed
qed

definition is_spread where
  "is_spread s \<longleftrightarrow> 
    set s \<subseteq> {0..<length lines} \<and> sorted s \<and> distinct s \<and> is_partition (map (\<lambda> i. set (lines ! i)) s)"

lemma inj_set_lines:
  assumes "set s \<subseteq> {0..<length lines}"
  shows "inj_on (\<lambda> i. set (lines ! i)) (set s)"
  unfolding inj_on_def
proof safe
  fix x y
  assume "x \<in> set s" "y \<in> set s" and xy: "set (lines ! x) = set (lines ! y)"
  then have "x < length lines" "y < length lines"
    using assms
    by auto
  then show "x = y"
    using distinct_lines xy
    using nth_eq_iff_index_eq 
    by fastforce
qed
 

lemma is_spread:
  shows "is_spread s \<longleftrightarrow> 
     set s \<subseteq> {0..<length lines} \<and> sorted s \<and> distinct s \<and> 
     (\<forall> p \<in> set (all_points). \<exists>! i. i < length s \<and> p \<in> set (lines ! (s ! i)))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have "\<Union> (set (map (\<lambda>i. set (lines ! i)) s)) \<subseteq> \<Union> (set (map (\<lambda> i. set (lines ! i)) [0..<length lines]))"
    by (simp add: SUP_subset_mono is_spread_def)
  also have "... = \<Union> (set (map set lines))"
    by (smt (verit, ccfv_SIG) add.left_neutral diff_zero length_map map_upt_eqI nth_map)
  finally have *: "\<Union> (set (map (\<lambda>i. set (lines ! i)) s)) \<subseteq> set all_points"
    unfolding all_points_def
    by simp

  have **: "distinct (map (\<lambda>i. set (lines ! i)) s)"
    using \<open>is_spread s\<close> distinct_map inj_set_lines is_spread_def
    by blast
  show ?rhs
    using is_partition[OF ** *] \<open>is_spread s\<close>
    unfolding is_spread_def
    by (metis length_map nth_map)
next
  assume R: ?rhs

  then have "\<Union> (set (map (\<lambda>i. set (lines ! i)) s)) \<subseteq> \<Union> (set (map (\<lambda> i. set (lines ! i)) [0..<length lines]))"
    by (simp add: SUP_subset_mono is_spread_def)
  also have "... = \<Union> (set (map set lines))"
    by (smt (verit, ccfv_SIG) add.left_neutral diff_zero length_map map_upt_eqI nth_map)
  finally have *: "\<Union> (set (map (\<lambda>i. set (lines ! i)) s)) \<subseteq> set all_points"
    unfolding all_points_def
    by simp

  have **: "distinct (map (\<lambda>i. set (lines ! i)) s)"
    using R
    by (simp add: distinct_map inj_set_lines)

  show ?lhs
    using is_partition[OF ** *] R
    unfolding is_spread_def
    by (metis length_map nth_map)
qed

definition spread_to_val where
  "spread_to_val s = (\<lambda> v. \<exists> l \<in> set s. L l = v)"

definition val_to_spread where
  "val_to_spread val = filter (\<lambda> i. val (L i)) [0..<length lines]"

lemma distinct_val_to_spread [simp]:
  shows "distinct (val_to_spread val)"
  unfolding val_to_spread_def
  by simp

lemma sorted_val_to_spread [simp]:
  shows "sorted (val_to_spread val)"
  unfolding val_to_spread_def
  using sorted_upt sorted_wrt_filter
  by blast

lemma set_val_to_spread:
  shows "set (val_to_spread val) = {i. i < length lines \<and> val (L i)}"
  unfolding val_to_spread_def
  by auto

lemma set_val_to_spread_subset [simp]:
  shows "set (val_to_spread val) \<subseteq> {0..<length lines}"
  unfolding val_to_spread_def
  by auto

lemma val_to_spread_spread_to_val:
  assumes "distinct s" "sorted s" "set s \<subseteq> {0..<length lines}"
  shows "val_to_spread (spread_to_val s) = s"
proof (rule sorted_distinct_set_unique)
  show "sorted (val_to_spread (spread_to_val s))"
    by simp
next
  show "distinct (val_to_spread (spread_to_val s))"
    by simp
next
  show "sorted s" "distinct s"
    by fact+
next
  show "set (val_to_spread (spread_to_val s)) = set s"
    using assms subst set_val_to_spread
    by (auto simp add: spread_to_val_def L_def)
qed
  
lemma exactly1_val:
  assumes "p \<in> set all_points"
  shows "exactly1_val val (map L (point_lines p lines)) \<longleftrightarrow> 
         (\<exists>! i. i < length (val_to_spread val) \<and> p \<in> set (lines ! ((val_to_spread val) ! i)))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  let ?s = "val_to_spread val"
  assume ?lhs
  then obtain v where 
    "v \<in> set (map L (point_lines p lines))"
    "val v = True" and 
    v': "\<forall>v'\<in>set (map L (point_lines p lines)). v' \<noteq> v \<longrightarrow> val v' = False"
    unfolding exactly1_val_def
    by auto
  then obtain l where
    "l \<in> set (point_lines p lines)" "v = L l"
    by auto
  then have "l \<in> set ?s"
    using \<open>val v = True\<close>
    unfolding set_val_to_spread
    by (simp add: set_point_lines)
  then obtain i where "i < length ?s" "?s ! i = l"
    by (meson in_set_conv_nth)
  show ?rhs
  proof
    show "i < length ?s \<and> p \<in> set (lines ! (?s ! i))"
      using \<open>i < length ?s\<close> \<open>l \<in> set (point_lines p lines)\<close> \<open>?s ! i = l\<close> 
      by (auto simp add: set_point_lines)
  next
    fix i'
    assume i': "i' < length (val_to_spread val) \<and> p \<in> set (lines ! (val_to_spread val ! i'))"
    define l' where l': "l' = ?s ! i'"
    have "l' \<in> set ?s" "p \<in> set (lines ! l')"
      using l' i'
      by auto
    then have "val (L l') = True"
      by (simp add: set_val_to_spread)
    moreover have "l' \<in> set (point_lines p lines)"
      using \<open>l' \<in> set ?s\<close> \<open>p \<in> set (lines ! l')\<close> set_point_lines set_val_to_spread
      by auto
    ultimately have "L l' = L l"
      using v' \<open>v = L l\<close>
      by auto
    then have "l = l'"
      unfolding L_def
      by auto
    then show "i' = i"
      using \<open>?s ! i = l\<close> l' \<open>i < length ?s\<close> i'
      by (simp add: nth_eq_iff_index_eq)
  qed
next
  let ?s = "val_to_spread val"
  assume ?rhs
  then obtain i where "i < length ?s" "p \<in> set (lines ! (?s ! i))" and 
       i': "\<forall>i'. i' < length ?s \<and> p \<in> set (lines ! (?s ! i')) \<longrightarrow> i' = i"
    unfolding Ex1_def
    by auto
  show ?lhs
    unfolding exactly1_val_def
  proof
    show "L (?s ! i) \<in> set (map L (point_lines p lines))"
      using \<open>i < length ?s\<close> \<open>p \<in> set (lines ! (?s ! i))\<close>
      by (metis (mono_tags, lifting) image_eqI list.set_map mem_Collect_eq nth_mem set_point_lines set_val_to_spread)
  next
    show "val (L (?s ! i)) = True \<and>
          (\<forall> v' \<in> set (map L (point_lines p lines)). 
          v' \<noteq> L (?s ! i) \<longrightarrow> val v' = False)"
    proof safe
      show "val (L (?s ! i))"
        using \<open>i < length ?s\<close> nth_mem set_val_to_spread
        by auto
    next
      fix v'
      assume "v' \<in> set (map L (point_lines p lines))"  "v' \<noteq> L (?s ! i)" "val v'"
      then obtain l' where "l' \<in> set (point_lines p lines)" "v' = L l'"
        by auto
      then have "l' \<in> set ?s"
        using \<open>val v'\<close> set_point_lines set_val_to_spread 
        by auto
      then obtain i' where "i' < length ?s" "?s ! i' = l'"
        by (meson in_set_conv_nth)
      then have "i = i'"
        using i'
        using \<open>l' \<in> set (point_lines p lines)\<close> set_point_lines by auto
      then show False
        using \<open>v' = L l'\<close> \<open>v' \<noteq> L (?s ! i)\<close> \<open>?s ! i' = l'\<close> 
        by blast
    qed
  qed
qed

lemma models_spread:
  assumes "satisfies_formula val spreadsSAT"
  shows "is_spread (val_to_spread val)"
  using assms exactly1_val
  unfolding is_spread satisfies_formula
  by auto

lemma spread_model:
  assumes "is_spread s"
  shows "satisfies_formula (spread_to_val s) spreadsSAT"
  unfolding satisfies_formula
proof
  fix p
  assume p: "p \<in> set all_points"
  show "exactly1_val (spread_to_val s) (map L (point_lines p lines))"
    unfolding exactly1_val[OF p]
    using assms p
    unfolding is_spread
    by (simp add: val_to_spread_spread_to_val)
qed

definition spreads :: "nat list list" where
"spreads = [[0, 19, 24, 28, 33],
           [0, 19, 26, 29, 32],
           [0, 20, 23, 28, 34],
           [0, 20, 25, 29, 31],
           [0, 21, 24, 30, 31],
           [0, 21, 26, 27, 34],
           [0, 22, 23, 30, 32],
           [0, 22, 25, 27, 33],
           [1, 8, 14, 28, 33],
           [1, 8, 16, 29, 31],
           [1, 9, 13, 29, 32],
           [1, 9, 18, 28, 34],
           [1, 10, 14, 30, 32],
           [1, 10, 16, 27, 34],
           [1, 11, 13, 27, 33],
           [1, 11, 18, 30, 31],
           [2, 8, 14, 21, 26],
           [2, 8, 16, 22, 23],
           [2, 9, 13, 21, 24],
           [2, 9, 18, 22, 25],
           [2, 10, 14, 20, 25],
           [2, 10, 16, 19, 24],
           [2, 11, 13, 20, 23],
           [2, 11, 18, 19, 26],
           [3, 7, 14, 21, 30],
           [3, 7, 16, 19, 29],
           [3, 9, 15, 25, 29],
           [3, 9, 17, 21, 34],
           [3, 11, 15, 23, 30],
           [3, 11, 17, 19, 33],
           [3, 12, 14, 25, 33],
           [3, 12, 16, 23, 34],
           [4, 7, 14, 20, 28],
           [4, 7, 16, 22, 27],
           [4, 9, 15, 24, 28],
           [4, 9, 17, 22, 32],
           [4, 11, 15, 26, 27],
           [4, 11, 17, 20, 31],
           [4, 12, 14, 26, 32],
           [4, 12, 16, 24, 31],
           [5, 7, 13, 21, 27],
           [5, 7, 18, 19, 28],
           [5, 8, 15, 23, 28],
           [5, 8, 17, 21, 31],
           [5, 10, 15, 25, 27],
           [5, 10, 17, 19, 32],
           [5, 12, 13, 23, 32],
           [5, 12, 18, 25, 31],
           [6, 7, 13, 20, 29],
           [6, 7, 18, 22, 30],
           [6, 8, 15, 26, 29],
           [6, 8, 17, 22, 33],
           [6, 10, 15, 24, 30],
           [6, 10, 17, 20, 34],
           [6, 12, 13, 24, 33],
           [6, 12, 18, 26, 34]]"

lemma spreads_is_spread:
  "\<forall> s \<in> set spreads. is_spread s"
  unfolding is_spread_def
  by eval

definition not_in_spreadsSAT where
  "not_in_spreadsSAT = 
     map (\<lambda> s. map (\<lambda> l. if l \<in> set s then - int (L l) else int (L l)) [0..<length lines]) spreads"

lemma not_in_spreadsSAT:
  assumes "\<not> satisfies_formula val not_in_spreadsSAT"
  shows "val_to_spread val \<in> set spreads"
proof-
  from assms obtain clause where
     "\<not> satisfies_clause val clause" "clause \<in> set not_in_spreadsSAT"
    unfolding satisfies_formula_def
    by auto
  then obtain s where
    "s \<in> set spreads" "clause = map (\<lambda> l. if l \<in> set s then - int (L l) else int (L l)) [0..<length lines]" 
    unfolding not_in_spreadsSAT_def
    by auto
  then have "\<forall> l < length lines. \<not> satisfies_lit val (if l \<in> set s then - int (L l) else int (L l))"
    using \<open>\<not> satisfies_clause val clause\<close>
    unfolding satisfies_clause_def 
    by auto
  then have *: "\<forall> l < length lines. if l \<in> set s then val (L l) else \<not> val (L l)"
    unfolding satisfies_lit_def
    by (smt (verit, best) L_def Suc_eq_plus1 less_Suc_eq_0_disj nat_int zero_less_nat_eq)
  have "s = val_to_spread val"
  proof (rule sorted_distinct_set_unique)
    show "sorted s" "distinct s"
      using \<open>s \<in> set spreads\<close> spreads_is_spread
      by (auto simp add: is_spread_def)
  next
    show "sorted (val_to_spread val)" "distinct (val_to_spread val)"
      by simp_all
  next
    have "set s \<subseteq> {0..<length lines}"
      using \<open>s \<in> set spreads\<close> spreads_is_spread
      unfolding is_spread_def
      by auto
    then show "set s = set (val_to_spread val)"
      using *
      unfolding set_val_to_spread
      by (auto split: if_split_asm)
  qed
  then show ?thesis
    using \<open>s \<in> set spreads\<close>
    by simp
qed

lemma not_in_spreadsSAT':
  assumes "is_spread s" "s \<notin> set spreads"
  shows "satisfies_formula (spread_to_val s) not_in_spreadsSAT"
  using assms
  by (metis is_spread_def not_in_spreadsSAT val_to_spread_spread_to_val)
  
lemma no_other_spreads_formula:
  assumes "is_spread s" "s \<notin> set spreads"
  shows "satisfies_formula (spread_to_val s) (spreadsSAT @ not_in_spreadsSAT)"
  using assms(1) assms(2) not_in_spreadsSAT' satisfies_formula_def spread_model 
  by auto

lemma no_other_spreads:
  shows "\<not> (\<exists> s. is_spread s \<and> s \<notin> set spreads)"
proof-
  have "\<not> (\<exists> val. satisfies_formula val (spreadsSAT @ not_in_spreadsSAT))"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain val where "satisfies_formula val (spreadsSAT @ not_in_spreadsSAT)"
      by auto
    then show False
      by normalization sat
  qed
  then show ?thesis
    using no_other_spreads_formula
    by blast
qed

theorem spreads:
  "is_spread s \<longleftrightarrow> s \<in> set spreads"
  using no_other_spreads spreads_is_spread 
  by blast

end