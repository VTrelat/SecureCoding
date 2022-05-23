section \<open>Rank Annotated Tree\<close>

theory RankAnnotatedTree
imports Main

begin

subsection \<open>Type definition and operations\<close>

datatype 'a rtree = Leaf ("\<langle>/ \<rangle>")| Node "'a rtree" nat 'a "'a rtree" ("(1\<langle> _,/ _,/ _,/ _ \<rangle>)")

fun num_nodes :: "'a rtree \<Rightarrow> nat" where
"num_nodes \<langle>\<rangle> = 0" |
"num_nodes \<langle>l, _, _, r\<rangle> = 1 + num_nodes l + num_nodes r"

value  "num_nodes \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>"

fun set_rtree :: "'a rtree \<Rightarrow> 'a set" where
  "set_rtree \<langle>\<rangle> = {}"
| "set_rtree \<langle>l,n,x,r\<rangle> = set_rtree l \<union> set_rtree r \<union> {x}"

fun rbst :: "('a::linorder) rtree \<Rightarrow> bool" where
"rbst \<langle>\<rangle> = True" |
"rbst \<langle>l, n, x, r\<rangle> = ((\<forall>a \<in> set_rtree l. a < x) \<and> (\<forall>a \<in> set_rtree r. x < a) \<and> rbst l \<and> rbst r \<and> n = num_nodes l)"

value "rbst \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>"
value "rbst \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 2, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>"

lemma set_rtree_rbst: "rbst \<langle>l, n, x, r\<rangle> \<Longrightarrow> a \<in> set_rtree \<langle>l, n, x, r\<rangle> \<Longrightarrow> a < x \<Longrightarrow> a \<in> set_rtree l"
  by force

fun rins :: "'a::linorder \<Rightarrow> 'a rtree \<Rightarrow> 'a rtree" where
"rins a \<langle>\<rangle> = \<langle>\<langle>\<rangle>, 0, a, \<langle>\<rangle>\<rangle>" |
"rins a \<langle>l, n, x, r\<rangle> = (if a \<in> set_rtree \<langle>l, n, x, r\<rangle> then \<langle>l, n, x, r\<rangle>
                      else if a < x then \<langle>rins a l, n + 1, x, r\<rangle>
                      else \<langle>l, n, x, rins a r\<rangle>)"

value "rins 9 \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<rangle>\<rangle>\<rangle>"

lemma rins_set[simp]: "set_rtree (rins x t) = insert x (set_rtree t)"
  by (induction t arbitrary: x rule: set_rtree.induct) auto

lemma num_nodes_rins_notin[simp]: "x \<notin> set_rtree t \<Longrightarrow> rbst t \<Longrightarrow> num_nodes (rins x t) = 1 + num_nodes t"
  by (induction t rule: rbst.induct) simp+

lemma num_nodes_rins_in[simp]: "x \<in> set_rtree t \<Longrightarrow> rbst t \<Longrightarrow> num_nodes (rins x t) = num_nodes t"
  by (induction t rule: rbst.induct) auto

lemma rins_invar[simp]: "x \<notin> set_rtree t \<Longrightarrow> rbst t \<Longrightarrow> rbst (rins x t)"
proof (induction t rule: rbst.induct)
  case 1
  then show ?case by simp
next
  case (2 l n a r)
  then show ?case
    by auto
qed

lemma rins_invar_in[simp]: "x \<in> set_rtree t \<Longrightarrow> rbst t \<Longrightarrow> rbst (rins x t)"
  using rbst.elims(2) by force


subsection \<open>Inorder traversal and getting rank\<close>

fun inorder:: "'a rtree \<Rightarrow> 'a list" where
"inorder \<langle>\<rangle> = []" |
"inorder \<langle>l, _, x, r\<rangle> = inorder l  @ (x # inorder r)"

value  "inorder \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>"

fun rank:: "'a::linorder \<Rightarrow> 'a rtree \<Rightarrow> nat" where
"rank a \<langle>\<rangle> = 0" |
"rank a \<langle>l, n, x, r\<rangle> = (if a = x then n
                       else if a > x then 1 + n + rank a r
                       else rank a l)"

value  "rank 9 \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>"

definition "at_index i l x \<equiv> i < length l \<and> l!i=x"

lemma num_nodes_inorder[simp]: "num_nodes t = length (inorder t)"
  by (induction t) simp+

lemma set_rtree_inorder_in[simp]:"x \<in> set_rtree t \<longleftrightarrow> x \<in> set(inorder t)"
  by (induction t) auto

lemma inorder_index: "rbst t \<Longrightarrow> a \<in> set_rtree t \<Longrightarrow> at_index (rank a t) (inorder t) a"
proof (induction t)
  case Leaf
  then show ?case by simp
next
  case (Node l n x r)
  then show ?case
  proof (cases "a = x")
    case True
    hence "rank a \<langle>l, n, x, r\<rangle> = n"
      by simp
    have "n = num_nodes l"
      using Node.prems(1) rbst.simps(2) by blast
    then have "... = length (inorder l)"
      by simp
    then show ?thesis using True by (auto split: if_splits simp add: \<open>n = num_nodes l\<close> at_index_def)
  next
    case False
    then show ?thesis
    proof (cases "a > x")
      case True
      hence "rank a \<langle>l, n, x, r\<rangle> = 1 + n + rank a r"
        using Node.prems(2) by auto
      from True have "a \<in> set_rtree r"
        using Node.prems(1) Node.prems(2) order_less_imp_not_less by fastforce
      then show ?thesis using True
        apply (auto split: if_splits simp add: at_index_def)
         apply (metis Node.IH(2) Node.prems(1) \<open>a \<in> set_rtree r\<close> at_index_def nat_add_left_cancel_less num_nodes_inorder rbst.simps(2))
        by (metis (no_types, lifting) Node.IH(2) Node.prems(1) \<open>a \<in> RankAnnotatedTree.set_rtree r\<close> add_Suc_right add_diff_cancel_left' at_index_def not_add_less1 nth_Cons_Suc nth_append num_nodes_inorder rbst.simps(2))
    next
      case False
      hence "rank a \<langle>l, n, x, r\<rangle> = rank a l" using \<open>a \<noteq> x\<close>
        using Node.prems(2) by auto
      from False \<open>a \<noteq>x\<close> have "a \<in> set_rtree l"
        by (meson Node.prems(1) Node.prems(2) antisym_conv3 set_rtree_rbst)
      then show ?thesis using False \<open>a \<noteq> x\<close>
        apply (auto split: if_splits simp add: at_index_def)
         apply (metis Node.IH(1) Node.prems(1) \<open>a \<in> RankAnnotatedTree.set_rtree l\<close> at_index_def less_Suc_eq rbst.simps(2) trans_less_add1)
        by (metis Node.IH(1) Node.prems(1) \<open>a \<in> RankAnnotatedTree.set_rtree l\<close> at_index_def nth_append rbst.simps(2))
    qed
  qed

qed

subsection \<open>Selection in a rank annotated tree\<close>

fun sel:: "nat \<Rightarrow> 'a::linorder rtree \<Rightarrow>'a" where
"sel _ \<langle>\<rangle> = undefined" |
"sel i \<langle>l, n, x, r\<rangle> = (if i = n then x
                      else if i < n then sel i l
                      else sel (i - n - 1) r)"

value  "sel 5 \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>" 


lemma sel_in_set_rtree:"\<And> i. sel i t = a \<Longrightarrow> a \<noteq> undefined \<Longrightarrow> a \<in> set_rtree t"
proof(induction t)
  case Leaf
  then show ?case
    by simp
next
  case (Node l n x r)
  then show ?case
  proof (cases "i = n")
    case True
    then show ?thesis
      using Node.prems(1) by auto
  next
    case False
    then show ?thesis
    proof (cases "i<n")
      case True
      hence "sel i \<langle>l, n, x, r\<rangle> = sel i l"
        by simp
      then show ?thesis using Node.IH
        using Node.prems(1) Node.prems(2) by auto
    next
      case False
      hence "sel i \<langle>l, n, x, r\<rangle> = sel (i-n-1) r" using \<open>i\<noteq>n\<close>
        by simp
      then show ?thesis using \<open>i\<noteq>n\<close>
        using Node.IH(2) Node.prems(1) Node.prems(2) by auto
    qed
  qed
qed

lemma select_correct: "rbst t \<Longrightarrow> i < length (inorder t) \<Longrightarrow> sel i t = inorder t!i"
proof (induction t arbitrary: i)
  case Leaf
  then show ?case
    by simp
next
  case (Node l n x r)
  then show ?case
  proof (cases "i = n")
    case True
    then show ?thesis
      using Node.prems(1) by auto
  next
    case False
    then show ?thesis
    proof (cases "i < n")
      case True
      then show ?thesis
        by (metis False Node.IH(1) Node.prems(1) inorder.simps(2) nth_append num_nodes_inorder rbst.simps(2) sel.simps(2))
    next
      case False
      then have "sel i \<langle>l, n, x, r\<rangle> = sel (i - n - 1) r" using \<open>i \<noteq> n\<close>
        by simp
      moreover have "i - n - 1 < length (inorder r)" using False \<open>i \<noteq> n\<close>
        using Node.prems(1) Node.prems(2) by force
      moreover have "sel (i - n - 1) r = inorder r ! (i - n - 1)" using False \<open>i \<noteq> n\<close> Node.IH
        using Node.prems(1) calculation(2) rbst.simps(2) by blast
      then show ?thesis using False \<open>i \<noteq> n\<close>
        by (metis Node.prems(1) antisym_conv3 calculation(1) inorder.simps(2) nth_Cons_pos nth_append num_nodes_inorder rbst.simps(2) zero_less_diff)
    qed
  qed
qed

lemma rank_sel_id: "rbst t \<Longrightarrow> i < length (inorder t) \<Longrightarrow> rank (sel i t) t = i"
proof (induction t arbitrary: i)
  case Leaf
  then show ?case by simp
next
  case (Node l n x r)
  then show ?case using select_correct
    apply auto
       apply (simp add: order_less_not_sym select_correct)
    by fastforce+
qed

fun rfold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a rtree \<Rightarrow> 'b \<Rightarrow> 'b" where
"rfold f \<langle>\<rangle> acc = acc" |
"rfold f \<langle>l, _, a, r\<rangle> acc = rfold f r (f a (rfold f l acc))"

fun to_list :: "'a rtree \<Rightarrow> 'a list" where
"to_list \<langle>\<rangle> = []" |
"to_list \<langle>l, _, a, r\<rangle> = a # to_list l @ to_list r"

definition rmerge :: "'a::linorder rtree \<Rightarrow> 'a rtree \<Rightarrow> 'a rtree" where
"rmerge t u = fold rins (to_list u) t"

lemma rmerge_rbst: "rbst u \<Longrightarrow> rbst t \<Longrightarrow> rbst (rmerge t u)"
  unfolding rmerge_def proof (induction u arbitrary: t)
  case Leaf
  then show ?case by simp
next
  case (Node u1 x2 x3 u2)
  then show ?case apply auto
    by (meson rins_invar rins_invar_in)
qed


lemma to_list_set: "set_rtree t = set (to_list t)"
proof (induction t)
  case Leaf
  then show ?case by simp
next
  case (Node t1 x2 x3 t2)
  then show ?case by auto
qed

lemma rmerge_set: "rbst u \<Longrightarrow> rbst t \<Longrightarrow> set_rtree (rmerge t u) = set_rtree t \<union> set_rtree u"
  unfolding rmerge_def proof (induction u arbitrary: t)
  case Leaf
  then show ?case by simp
next
  case (Node l n a r)
  have "set_rtree (fold rins (to_list \<langle>l, n, a, r\<rangle>) t) = set_rtree (rins a (fold rins (to_list l @ to_list r) t))" apply auto sledgehammer 
  then show ?case using set_rtree_inorder_in rins_set to_list_set Node.IH apply auto sledgehammer
qed

fun rdel :: "'a::linorder \<Rightarrow> 'a rtree \<Rightarrow> 'a rtree" where
"rdel x \<langle>\<rangle> = \<langle>\<rangle>" |
"rdel x \<langle>l, n, a, r\<rangle> = (if x = a then rmerge r l
  else (if x < a then (if x \<in> set_rtree l then \<langle>rdel x l, n-1, a, r\<rangle> else \<langle>l, n, a, r\<rangle>)
    else \<langle>l, n, a, rdel x r\<rangle>))"

lemma rdel_rbst: "rbst t \<Longrightarrow> rbst (rdel x t)"
proof (induction t arbitrary: x)
  case Leaf
  then show ?case by simp
next
  case (Node l n a r)
  then show ?case using Node.IH rmerge_rbst apply (auto simp: rmerge_rbst split: if_splits) sledgehammer
qed


end