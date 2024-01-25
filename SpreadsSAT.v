Require Import Arith.
Require Import List.
Import ListNotations.

Require Import ZArith.

From SMTCoq Require Import SMTCoq.

Definition point := nat.
Definition line  := list point.
                        
Definition lines : list line :=
         [[0; 1; 2];
         [0; 3; 4];
         [0; 5; 6];
         [0; 7; 8];
         [0; 10; 9];
         [0; 11; 12];
         [0; 13; 14];
         [1; 4; 6];
         [1; 8; 10];
         [1; 12; 14];
         [1; 7; 9];
         [1; 13; 11];
         [1; 3; 5];
         [2; 7; 10];
         [2; 11; 14];
         [2; 3; 6];
         [2; 12; 13];
         [2; 4; 5];
         [2; 8; 9];
         [3; 10; 14];
         [3; 8; 12];
         [3; 9; 13];
         [3; 7; 11];
         [4; 9; 14];
         [4; 8; 11];
         [4; 10; 13];
         [4; 7; 12];
         [5; 8; 14];
         [5; 7; 13];
         [5; 9; 11];
         [5; 10; 12];
         [6; 7; 14];
         [6; 8; 13];
         [6; 9; 12];
         [6; 10; 11]].

Definition nat_eq := Nat.eqb.
Definition nat_le := Nat.leb.

Fixpoint listnat_eq l1 l2 :=
  match (l1,l2) with
    ([],[]) => true
  | ([], _::_) => false
  | (_::_,[]) => false
  | (x::xs, y::ys) => (Nat.eqb x y && listnat_eq xs ys)%bool
  end.

(* assuming both lists have the same size *)
Fixpoint listnat_le l1 l2 :=
  match (l1,l2) with
    ([],[]) => true
  | ([], _::_) => true
  | (_::_,[]) => false
  | (x::xs, y::ys) => (Nat.leb x y && listnat_le xs ys)%bool
  end.

Fixpoint belongs {A:Set} (eqb:A->A->bool) (p:A) (l:list A) :=
  match l with
    [] => false
  | x::xs => ((eqb p x) || (belongs eqb p xs))%bool
  end.

Definition incl {A:Set} eqb (l1:list A) (l2:list A) := forallb (fun x=> belongs eqb x l2) l1.

Definition belongs_nat := belongs nat_eq.
Definition belongs_listnat := belongs listnat_eq.

Fixpoint distinct {A:Set} (eqb:A->A->bool) l :=
  match l with
    [] => true
  | x::xs => if (belongs eqb x xs) then false else distinct eqb xs end.


Lemma distinct_lines: distinct listnat_eq lines.
Proof.
  reflexivity.
Qed.

Fixpoint insert {A:Set} (leb:A->A->bool) t s :=
  match s with
  | [] => [t]
  | x::xs => if leb t x then t::(x::xs) else x::(insert leb t xs)
  end.
(*
Functional Scheme insert_ind := Induction for insert Sort Prop.*)

Fixpoint sort {A:Set} (leb:A->A->bool) s :=
  match s with
  | [] => []
  | x::xs => insert leb x (sort leb xs)
  end.

Fixpoint remdups {A:Set}(dec:forall x y : A, {x = y} + {x <> y}) l :=
  match l with
    [] => []
  | x::xs => if (@in_dec A dec x xs) then remdups dec xs else x::remdups dec xs
  end.

Definition all_points := remdups eq_nat_dec (sort nat_le (concat lines)).
Eval compute in all_points.

Fixpoint upto (n:nat) :=
  match n with
    O => []
  | S p => (upto p)++[p]
  end.

Fixpoint upto2 (s n:nat) :=
  match n with
    O => []
  | S p => if (lt_dec s n) then (upto2 s p)++[p] else []
  end.

Lemma all_points_equiv : all_points = (upto 15).
Proof.
  unfold upto, all_points, lines; reflexivity.
Qed.

Definition line_index := nat.

(* Indices of lines that contain the given point *)
Definition point_lines (p: point) (ls:list line) : list line_index := 
   map fst (filter (fun  x  => match x with (i, l) => belongs nat_eq p l end) (combine (upto (length ls)) ls)).

Eval compute in point_lines 0 lines.
Eval compute in distinct nat_eq (point_lines 0 lines).

Lemma distinct_point_lines : forall p, belongs nat_eq p all_points = true -> distinct nat_eq (point_lines p lines)=true.
Proof.
  intros p.
  unfold all_points; simpl.
  repeat rewrite Bool.orb_true_iff; repeat rewrite Nat.eqb_eq; intuition; subst.
  par:(unfold all_points, point_lines, lines; reflexivity).
Qed.

(*Lemma set_points_lines : forall p, (point_lines p ls) = {i. i < length ls \<and> p \<in> set (ls ! i)
                                                                                     Proof.*)

                                                   (*
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
*)

Definition inth (l:list nat) (n:nat) : nat := List.nth n l 0. 

Definition all_pairs xs := 
    let n := length xs
      in concat (map (fun i =>  map (fun j => (inth xs i, inth xs j)) (upto2 (i+1) n)) (upto n)).

Eval compute in all_pairs [1;2;3;4].
(*
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
 *)


Definition satisfies_lit (val: nat -> bool) (lit:Z) : bool :=
  (if Z_gt_le_dec lit 0 then val (Z.to_nat lit) else negb (val (Z.to_nat (-lit)%Z))).

Definition satisfies_clause (val : nat -> bool) (cl:list Z) : bool :=
  existsb (fun lit => satisfies_lit val lit) cl.

Definition satisfies_formula (val : nat -> bool) (fmt: list (list Z)) : bool :=
  forallb (fun cl => satisfies_clause val cl) fmt.

Definition exactly1 (ls: list nat) : list (list Z) := 
  (map Z.of_nat ls) :: map (fun x => match x with (i,j) => [-(Z.of_nat i); -(Z.of_nat j)] end)%Z (all_pairs ls).
Eval compute in (exactly1 [1;2;3;4]).

Definition eqb (x y:bool) := match (x,y) with (true, true) | (false, false) => true | _ => false end.

Definition exactly1_val val vs :=
existsb (fun v => (eqb (val v) true) && (forallb (fun v' => negb (eqb v' v) && (eqb (val v') false)) vs))%bool vs.

(*
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
 *)

Definition L (l:line_index) : nat := 1 + l.
Fixpoint map1 {A B:Set} (f:A->B) (l:list A) : list B :=
  match l with
    [] => []
  | x::xs => (f x)::map1 f xs
  end.

Definition spreadsSAT := concat (map1 (fun p => exactly1 (map L (point_lines p lines))) all_points).

Eval compute in spreadsSAT.

(*Lemma spreadsSAT_nonzero: forall clause, In clause spreadsSAT, 
  shows "\<forall> clause \<in> set spreadsSAT. 0 \<notin> set clause"
  unfolding spreadsSAT_def
  by (auto simp add: exactly1_def set_all_pairs L_def)
 *)

(*
lemma spreadsSAT_distinct:
  shows "\<forall> clause \<in> set spreadsSAT. distinct clause"
  using distinct_point_lines
  unfolding spreadsSAT_def
  by (auto simp add: exactly1_def set_all_pairs L_def distinct_map inj_on_def nth_eq_iff_index_eq )
 *)

(*lemma satisfies_formula:
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
 *)

Fixpoint intersect {A:Set} (eqb:A -> A -> bool) (l1 l2:list A) :=
  match l1 with
    [] => []
  | x::xs => if (belongs eqb x l2) then x::intersect eqb xs l2 else intersect eqb xs l2 
  end.

Definition is_empty {A:Set} (l:list A ) : bool := match l with [] => true | _ => false end.

Definition is_partition (s : list (list point)) : bool := 
  ((forallb (fun p => (existsb (fun q => belongs nat_eq p q) s)) all_points) &&
  forallb (fun l1 => forallb (fun l2 => (implb (negb (listnat_eq l1 l2)) (is_empty (intersect nat_eq l1 l2)))) s) s)%bool. 

Eval compute in is_partition ([[0;1;2;3;4];[6;7;8;9;10];[11];[12;13;5;14]]).

(*Definition is_partition :: "(point set) list -> bool" where
  "is_partition s \<longleftrightarrow> 
    (\<forall> p \<in> set (all_points). (\<exists> i. i < length s \<and> p \<in> s ! i)) \<and>
    (\<forall> l1 \<in> set s. \<forall> l2 \<in> set s. l1 \<noteq> l2 \<longrightarrow> l1 \<inter> l2 = {})"
*)
(*lemma is_partition:
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
*)

Fixpoint sorted {A:Set} (leb:A->A->bool) s :=
  match s with
  | [] => true
  | x::[] => true
  | x::(y::xs) as z => (leb x y && (sorted leb z))%bool
  end.
Check is_partition.
Check point_lines.

Eval compute in point_lines 1 lines.

Definition inth_l {A:Set} (l:list (list A)) i := nth i l [].
Open Scope bool_scope.
Definition is_spread s :=  
  ((forallb (fun t => belongs nat_eq t (upto (length lines))) s) 
             && sorted nat_le s
             && distinct nat_eq s
             && is_partition (map (fun i => (inth_l lines i)) s)).

Eval compute in is_spread [0; 19; 24; 28; 33].
(*
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
*)
Definition spread_to_val s := 
  fun v => existsb (fun l => belongs nat_eq l s && nat_eq (L l) v)%bool s.

Definition val_to_spread val := filter (fun i => val (L i)) (upto (length lines)).


Lemma distinct_cons : forall (A:Set) (l:list A) eq a, distinct eq (a::l) -> distinct eq l. 
Proof.
Admitted.

Lemma distinct_filter : forall (A:Set) (l:list A) eq f , distinct eq l -> distinct eq (filter f l).
Proof.
Admitted.  
  
Lemma distinct_val_to_spread : forall val, distinct nat_eq (val_to_spread val).
Proof.
  intros.
  unfold val_to_spread. simpl upto.
  apply distinct_filter.
  reflexivity.
Qed.

Lemma sorted_inv : forall {A:Set} le a (l:list A), sorted le (a::l) -> sorted le l.
Proof.
Admitted.

Lemma sorted_filter : forall (A:Set) (l:list A) le f , sorted le l -> sorted le (filter f l).
Proof.
(*  induction l.
  intros; trivial.
  intros.
  simpl.
  assert (sorted le l).
  eapply sorted_inv; eassumption.
  case_eq (f a); intros.
  

  admit.
  apply IHl.
  assumption.*)
Admitted.

Lemma sorted_val_to_spread : forall val, sorted nat_le (val_to_spread val).
Proof.
  unfold val_to_spread.
  intros; apply sorted_filter; reflexivity.
Qed.
(*
Lemma set_val_to_spread: 
  shows "set (val_to_spread val) = {i. i < length lines \<and> val (L i)}"
  unfolding val_to_spread_def
  by auto

lemma set_val_to_spread_subset [simp]:
  shows "set (val_to_spread val) \<subseteq> {0..<length lines}"
  unfolding val_to_spread_def
  by auto
*)
Lemma val_to_spread_spread_to_val: forall eq le s, distinct eq s -> sorted le s -> incl eq s (upto (length lines)) -> val_to_spread (spread_to_val s) = s.
Proof.
  intros.
  assert (Hs:sorted nat_le (val_to_spread (spread_to_val s))).
  apply sorted_val_to_spread. 
  assert (Hd : distinct nat_eq (val_to_spread (spread_to_val s))).
  apply distinct_val_to_spread. 
Admitted.

(*proof (rule sorted_distinct_set_unique)
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
*)
Lemma spread_model: forall s, is_spread s -> satisfies_formula (spread_to_val s) spreadsSAT.
Proof.
  unfold satisfies_formula.
  intros.

Admitted.
(*proof
  fix p
  assume p: "p \<in> set all_points"
  show "exactly1_val (spread_to_val s) (map L (point_lines p lines))"
    unfolding exactly1_val[OF p]
    using assms p
    unfolding is_spread
    by (simp add: val_to_spread_spread_to_val)
qed
*)
Definition spreads : list (list nat) := 
 ([[0; 19; 24; 28; 33];
           [0; 19; 26; 29; 32];
           [0; 20; 23; 28; 34];
           [0; 20; 25; 29; 31];
           [0; 21; 24; 30; 31];
           [0; 21; 26; 27; 34];
           [0; 22; 23; 30; 32];
           [0; 22; 25; 27; 33];
           [1; 8; 14; 28; 33];
           [1; 8; 16; 29; 31];
           [1; 9; 13; 29; 32];
           [1; 9; 18; 28; 34];
           [1; 10; 14; 30; 32];
           [1; 10; 16; 27; 34];
           [1; 11; 13; 27; 33];
           [1; 11; 18; 30; 31];
           [2; 8; 14; 21; 26];
           [2; 8; 16; 22; 23];
           [2; 9; 13; 21; 24];
           [2; 9; 18; 22; 25];
           [2; 10; 14; 20; 25];
           [2; 10; 16; 19; 24];
           [2; 11; 13; 20; 23];
           [2; 11; 18; 19; 26];
           [3; 7; 14; 21; 30];
           [3; 7; 16; 19; 29];
           [3; 9; 15; 25; 29];
           [3; 9; 17; 21; 34];
           [3; 11; 15; 23; 30];
           [3; 11; 17; 19; 33];
           [3; 12; 14; 25; 33];
           [3; 12; 16; 23; 34];
           [4; 7; 14; 20; 28];
           [4; 7; 16; 22; 27];
           [4; 9; 15; 24; 28];
           [4; 9; 17; 22; 32];
           [4; 11; 15; 26; 27];
           [4; 11; 17; 20; 31];
           [4; 12; 14; 26; 32];
           [4; 12; 16; 24; 31];
           [5; 7; 13; 21; 27];
           [5; 7; 18; 19; 28];
           [5; 8; 15; 23; 28];
           [5; 8; 17; 21; 31];
           [5; 10; 15; 25; 27];
           [5; 10; 17; 19; 32];
           [5; 12; 13; 23; 32];
           [5; 12; 18; 25; 31];
           [6; 7; 13; 20; 29];
           [6; 7; 18; 22; 30];
           [6; 8; 15; 26; 29];
           [6; 8; 17; 22; 33];
           [6; 10; 15; 24; 30];
           [6; 10; 17; 20; 34];
           [6; 12; 13; 24; 33];
           [6; 12; 18; 26; 34]])%nat.

Lemma spreads_is_spread:
  forall s, In s spreads -> is_spread s.
Proof.
  unfold spreads.
  intros s HIn_S.
  repeat (destruct HIn_S as [HeqL | HIn_S]; subst; try solve [reflexivity |  elim  (in_nil HIn_S)]).
Qed.

Definition not_in_spreadsSAT := 
     map (fun  s => map (fun l => - Z.of_nat (L l)) s)%Z spreads.

Eval compute in not_in_spreadsSAT.

Lemma not_in_spreadsSAT_characterization :
  forall val, ~ satisfies_formula val not_in_spreadsSAT -> In (val_to_spread val) spreads.
Proof.
Admitted.
(*proof-
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
    by (smt (verit;best) L_def Suc_eq_plus1 less_Suc_eq_0_disj nat_int zero_less_nat_eq)
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
 *)

Lemma foo : forall  A B : Prop, (A -> B) -> (~B->~A).
Proof.
solve [intuition].
Qed.

Lemma andb_istrue : forall a b, is_true (andb a b) <-> (is_true a/\ is_true b).
Proof.
  intros; destruct a; destruct b; split; zchaff.
Qed.

Lemma bool_not_not : forall b:bool, ~~b<->b.
Proof.
  zchaff.
Qed.

Lemma not_in_spreadsSAT': forall s, is_spread s -> ~In s spreads -> satisfies_formula (spread_to_val s) not_in_spreadsSAT.
Proof.
  unfold is_spread.
  intros.
  repeat rewrite andb_istrue in H; destruct H as [[[Hf Hs] Hd] Hp].
  
  simpl upto in Hf.
  rewrite <- val_to_spread_spread_to_val with (eq:=nat_eq) (le:=nat_le) (s:=s) in H0.

  generalize (foo _ _ (not_in_spreadsSAT_characterization (spread_to_val s)) H0).
  apply bool_not_not.
  assumption.
  assumption.
  simpl.
  assumption.
Qed.

Lemma satisfies_formula_app :
  forall val l1 l2, satisfies_formula val (l1++l2) = (satisfies_formula val l1 && satisfies_formula val l2)%bool.
Proof.
induction l1.
reflexivity.  
intros; simpl; rewrite IHl1.
intuition.
Qed.

Lemma no_other_spreads_formula:
  forall s, is_spread s -> ~In s spreads -> satisfies_formula (spread_to_val s) (spreadsSAT ++ not_in_spreadsSAT).
  intros.
  rewrite satisfies_formula_app.
  apply andb_true_intro; split.
  apply spread_model.
  assumption.
  apply not_in_spreadsSAT'; assumption.
Qed.

Fixpoint all_true (l:list bool) :=
  match l with
    [] => true | x::xs => (x && all_true xs)%bool
  end.

Lemma satisfies_formula_concat :
  forall val m, satisfies_formula val
                  (concat m) = all_true (map (fun t => satisfies_formula val t) m).
Proof.  
induction m.
reflexivity.
simpl.
rewrite <- IHm.
apply satisfies_formula_app.
Qed.

Lemma main_theorem_zchaff : forall val, negb (satisfies_formula val (spreadsSAT ++ not_in_spreadsSAT))=true.
Proof.
  unfold spreadsSAT, not_in_spreadsSAT, spreads, all_points, exactly1, lines.
  intros; rewrite satisfies_formula_app.
  rewrite satisfies_formula_concat.
  unfold point_lines, belongs.
  simpl sort. simpl remdups. simpl length. simpl upto. simpl combine. 
  (*simpl map1.*)
 simpl. unfold satisfies_lit. simpl.
  zchaff_no_check.
Qed.

Lemma negb_lemma : forall x, x=negb x -> False.
Proof.
destruct x; simpl; intuition.
Qed.  

Lemma no_other_spreads: ~(exists s, is_spread s=true /\ ~In s spreads).
Proof.
  assert (~ (exists val, satisfies_formula val (spreadsSAT ++ not_in_spreadsSAT))).
  intro.
  destruct H.
  assert (negb (satisfies_formula x (spreadsSAT ++ not_in_spreadsSAT)) = satisfies_formula x (spreadsSAT ++ not_in_spreadsSAT)).
  rewrite main_theorem_zchaff.
  rewrite <- H.
  reflexivity.
  eapply Bool.no_fixpoint_negb; eassumption.

  intro.
  apply H.
  destruct H0.
  exists (spread_to_val x).
  apply no_other_spreads_formula; solve [intuition].
Qed.

Lemma classical_foo : forall P :list nat -> Prop, ~(exists s : list nat, P s) <-> forall s:list nat, ~ P s.
Proof.
intros; firstorder.
Qed.

Lemma in_dec_not_not : forall {A:Set} (x:A) (eq_dec:forall x y:A, {x=y}+{~x=y}) (l:list A), ~~ In x l -> In x l.
Proof.
  intros; apply Decidable.not_not.
  destruct (in_dec eq_dec x l).
  left; trivial.
  right; trivial.
  assumption.
Qed.

Theorem spreads_characterization : forall s,
  is_spread s <-> In s spreads.
Proof.
  split.
  intros.
  generalize no_other_spreads; intros no.
  rewrite classical_foo in no.
  generalize (no s); intros.
  assert (dec:Decidable.decidable (is_spread s = true)).
  destruct (is_spread s); solve [left;reflexivity | right; intro Hf; inversion Hf].
  destruct (Decidable.not_and (is_spread s = true) (~ In s spreads) dec H0).
  solve [intuition]. 
  apply in_dec_not_not; solve [assumption | apply list_eq_dec; apply eq_nat_dec].

  intros; apply spreads_is_spread; assumption.
Qed.


