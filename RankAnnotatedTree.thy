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

lemma set_rtree_set_inorder_eq[simp]: "rbst t \<Longrightarrow> set_rtree t = set(inorder t)"
  by auto

lemma card_set_rtree[simp]: "rbst t \<Longrightarrow> num_nodes t = card (set_rtree t)"
proof (induction t rule:rtree.induct)
  case Leaf
  then show ?case by simp
next
  case (Node l n a r)
  have a_not_in:"a \<notin> set_rtree l \<and> a \<notin> set_rtree r"
    by (metis Node.prems not_less_iff_gr_or_eq rbst.simps(2))
  then show ?case using card_def Node.IH a_not_in apply auto
    using Node.prems card_Un_disjoint by fastforce
qed



fun rmerge :: "'a::linorder rtree \<Rightarrow> 'a rtree \<Rightarrow> 'a rtree" where
"rmerge t \<langle>\<rangle> = t" |
"rmerge t \<langle>l, _, a, r\<rangle> = rins a (rmerge (rmerge t r) l)"

lemma rmerge_inv[simp]: "rbst u \<Longrightarrow> rbst t \<Longrightarrow> rbst (rmerge t u)"
  proof (induction u arbitrary: t rule: rmerge.induct)
    case (1 t)
    then show ?case by simp
  next
    case (2 t l n a r)
    then show ?case using 2 apply auto
      by (meson rins_invar rins_invar_in) 
  qed

lemma rmerge_set[simp]: "rbst u \<Longrightarrow> rbst t \<Longrightarrow> set_rtree (rmerge t u) = set_rtree t \<union> set_rtree u"
  by (induction u arbitrary: t rule: rmerge.induct) auto

lemma card_rmerge[simp]: 
  assumes "rbst t" and "rbst u"
  shows "card (set_rtree (rmerge t u)) = card (set_rtree t \<union> set_rtree u)"
using assms proof (induction u arbitrary: t rule:rtree.induct)
  case Leaf
  then show ?case by simp
next
  case (Node l n x r)
  then show ?case
    by (cases "x \<in> set_rtree t")(metis Node.prems(1) Node.prems(2) rmerge_set)+
qed

fun rdel :: "'a::linorder \<Rightarrow> 'a rtree \<Rightarrow> 'a rtree" where
"rdel x \<langle>\<rangle> = \<langle>\<rangle>" |
"rdel x \<langle>l, n, a, r\<rangle> = (if x \<in> set_rtree \<langle>l, n, a, r\<rangle> then
  (if x < a then \<langle>rdel x l, n-1, a, r\<rangle> else
    (if x > a then \<langle>l, n, a, rdel x r\<rangle> else
      rmerge l r))
  else \<langle>l, n, a, r\<rangle>)"

value  "rdel 5 \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>" 
value  "rdel 6 \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>" 
value  "rdel 10 \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>
  = \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>" 


lemma rdel_set[simp]:"rbst t \<Longrightarrow> set_rtree (rdel x t) = (set_rtree t) - {x}"
proof (induction t arbitrary: x rule:rtree.induct)
  case Leaf
  then show ?case by simp
next
  case (Node l n a r)
  then show ?case apply auto
    apply fastforce
    apply fastforce
       apply (metis Un_iff rmerge_set  set_rtree_inorder_in)
    apply (metis Un_iff not_less_iff_gr_or_eq rmerge_set set_rtree_inorder_in)
    apply (metis Un_iff rmerge_set set_rtree_inorder_in)
    by (metis Un_iff rmerge_set set_rtree_inorder_in)
qed


lemma rdel_inv: "rbst t \<Longrightarrow> rbst (rdel x t)"
proof (induct t rule: rtree.induct)
  case Leaf
  then show ?case by simp
next
  case ind:(Node l n a r)
  then show ?case
  proof (cases "x \<in> set_rtree \<langle>l, n, a, r\<rangle>")
    case in_tree:True
    then show ?thesis
    proof (cases "x = a")
      case True
      then show ?thesis using ind rmerge_inv by auto
    next
      case x_neq_a:False
      then show ?thesis
      proof (cases "x < a")
        case True
        have "rbst (rdel x l)" using ind by simp
        moreover have "set_rtree (rdel x l) = set_rtree l - {x}"
          by (meson ind.prems rbst.simps(2) rdel_set)
        moreover have x_in_l: "x \<in> set_rtree l" using in_tree x_neq_a ind.prems True set_rtree_rbst
          by blast
        moreover have "card (set_rtree l - {x}) = n - 1"
          by (metis card_Diff_singleton card_set_rtree ind.prems rbst.simps(2) x_in_l)
        moreover have "length (inorder (rdel x l)) = n - 1" using ind rbst.simps x_in_l apply auto
          by (metis One_nat_def calculation(4) card_set_rtree num_nodes_inorder rdel_set)
        then show ?thesis using ind apply auto 
            apply (metis Diff_iff rdel_set set_rtree_set_inorder_eq)
          using order.asym apply blast
          using True by blast
      next
        case x_geq_a: False
        have x_in_r: "x \<in> set_rtree r" using ind in_tree x_neq_a x_geq_a by auto
        then show ?thesis using ind in_tree x_in_r x_geq_a x_neq_a rbst.simps apply auto
          by (metis Diff_iff rdel_set set_rtree_set_inorder_eq)
      qed
    qed
  next
    case False
    then show ?thesis using ind by auto
  qed
qed


end