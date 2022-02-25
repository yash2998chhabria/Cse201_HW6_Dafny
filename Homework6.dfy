datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)


function flatten<T>(tree:Tree<T>):List<T>
ensures tree == Leaf ==> flatten(tree) == Nil
{
    match tree
        case Leaf => Nil
        case Node(t1, t2, t) => append(Cons(t, flatten(t1)), flatten(t2))
}


function append<T>(xs:List<T>, ys:List<T>):List<T>
{
	
}

function treeContains<T>(tree:Tree<T>, element:T):bool
{
	
}

function listContains<T>(xs:List<T>, element:T):bool
{
	
}


lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{
	
}