theory RankAnnotatedTree
imports Main

begin

datatype 'a rtree = Leaf | Node "'a rtree" nat 'a "'a rtree"


end