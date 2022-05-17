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

fun rins :: "'a::linorder \<Rightarrow> 'a rtree \<Rightarrow> 'a rtree" where
"rins a \<langle>\<rangle> = \<langle>\<langle>\<rangle>, 0, a, \<langle>\<rangle>\<rangle>" |
"rins a \<langle>l, n, x, r\<rangle> = (if a < x then \<langle>rins a l, n + 1, x, r\<rangle>
                      else if a = x then \<langle>l, n, x, r\<rangle>
                      else \<langle>l, n, x, rins a r\<rangle>)"

value "rins 9 \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<rangle>\<rangle>\<rangle>"

lemma rins_set[simp]: "set_rtree (rins x t) = insert x (set_rtree t)"
  by (induction t arbitrary: x rule: set_rtree.induct) auto

lemma num_nodes_rins[simp]: "x \<notin> set_rtree t \<Longrightarrow> rbst t \<Longrightarrow> num_nodes (rins x t) = 1 + num_nodes t"
proof (induction t rule: rbst.induct)
  case 1
  then show ?case by simp
next
  case (2 l n x r)
  then show ?case
    by auto
qed

lemma rins_invar[simp]: "x \<notin> set_rtree t \<Longrightarrow> rbst t \<Longrightarrow> rbst (rins x t)"
proof (induction t rule: rbst.induct)
  case 1
  then show ?case by simp
next
  case (2 l n a r)
  then show ?case
    by auto
qed

subsection \<open>Inorder traversal and getting rank\<close>

fun inorder:: "'a rtree \<Rightarrow> 'a list" where
"inorder \<langle>\<rangle> = []" |
"inorder \<langle>l, _, x, r\<rangle> acc = inorder l  @ (x # inorder r)"

value  "inorder \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle> []"

fun rank:: "'a::linorder \<Rightarrow> 'a rtree \<Rightarrow> nat" where
"rank a \<langle>\<rangle> = 0" |
"rank a \<langle>l, n, x, r\<rangle> = (if a > x then 1 + num_nodes l + rank a r
                       else rank a l)"
value  "rank 6 \<langle>\<langle>\<langle>\<langle>\<rangle>, 0, 3, \<langle>\<rangle>\<rangle> , 1, 4, \<langle>\<langle>\<rangle>, 0, 5, \<langle>\<rangle>\<rangle>\<rangle>, 3, 6::nat, \<langle>\<langle>\<langle>\<rangle>, 0, 7,\<langle>\<rangle>\<rangle>, 1, 8, \<langle>\<langle>\<rangle>, 0, 9,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>"


definition "at_index i l x \<equiv> i < length l \<and> l!i=x"

lemma inorder_index: "rbst t \<Longrightarrow> x \<in> set_rtree t \<Longrightarrow> at_index (rank x t) (inorder t) x"
  sorry

end