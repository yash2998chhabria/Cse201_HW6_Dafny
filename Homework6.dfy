datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)


function flatten<T>(tree:Tree<T>):List<T>
ensures tree == Leaf ==> flatten(tree) == Nil
decreases tree
{
    match tree
        case Leaf => Nil
        case Node(l, r, t) => append(Cons(t, flatten(l)), flatten(r))
}


function append<T>(xs:List<T>, ys:List<T>):List<T>
ensures xs == Nil ==> append(xs,ys) == ys
ensures ys == Nil ==> append(xs,ys) == xs
decreases xs
{
	match xs
        case Nil => ys
        case Cons(x,xs_1) => Cons(x, append(xs_1,ys))
}

function treeContains<T>(tree:Tree<T>, element:T):bool
ensures tree == Leaf ==> treeContains(tree, element) == false
decreases tree
{
	match tree
        case Leaf => false
        case Node(l, r, t) => t == element || treeContains(l, element) || treeContains(r, element)
}

function listContains<T>(xs:List<T>, element:T):bool
ensures xs == Nil ==> listContains(xs, element) == false
decreases xs
{
	match xs
    case Nil => false
    case Cons(x, xs_1) => (x == element) || listContains(xs_1, element)
}



lemma member_to_list<T>(x:T,ys:List<T>,zs:List<T>)
decreases ys
decreases zs
ensures listContains(append(ys,zs), x) == (listContains(ys, x) || listContains(zs, x))
{
    match ys
    case Nil => {}
    case Cons(y,ys_1) => {
        member_to_list(x,ys_1,zs);
        assert listContains(append(ys_1,zs),x) == (listContains(ys_1,x) || listContains(zs,x));
        assert listContains(append(ys,zs),x)
            == listContains(append(Cons(y,ys_1),zs),x)
            == listContains(Cons(y,append(ys_1,zs)),x)
            == (x==y || listContains((append(ys_1,zs)),x))
            == (x==y || listContains(ys_1,x) || listContains(zs,x))
            == (listContains(Cons(y,ys_1),x) || listContains(zs,x))
            == (listContains(ys,x)          || listContains(zs,x))
            ;
    }
}

lemma sameElements<T>(tree:Tree<T>, element:T)
decreases tree
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{ 
    match tree
    case Leaf => {}
    case Node(l, r, t) => {
        sameElements(l, element);
        sameElements(r, element);
        member_to_list(element,flatten(l),flatten(r));
        assert treeContains(Node(l, r, t), element)
            == (treeContains(l, element) || treeContains(r, element) || t == element)
            == (listContains(flatten(l), element) || listContains(flatten(r), element) || t == element)
            == (listContains(append(flatten(l),flatten(r)), element) || t == element)
            == listContains (Cons(t, append(flatten(l),flatten(r))), element)
            == listContains(flatten(Node(l, r, t)), element)
            ;
    }
}
