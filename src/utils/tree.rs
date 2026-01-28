/// This is a plain tree whose only purpose is to be converted into a flat vector by depth-first traversal.
pub enum Tree<T> {
    Empty,
    Leaf(T),
    VecLeaf(Vec<T>),
    Node(Vec<Tree<T>>),
}

impl<T> From<T> for Tree<T> {
    fn from(x: T) -> Self {
        Tree::Leaf(x)
    }
}

impl<T> From<Vec<T>> for Tree<T> {
    fn from(vec: Vec<T>) -> Self {
        Tree::VecLeaf(vec)
    }
}

impl<T> From<Vec<Tree<T>>> for Tree<T> {
    fn from(trees: Vec<Tree<T>>) -> Self {
        if trees.is_empty() {
            Tree::Empty
        } else {
            Tree::Node(trees)
        }
    }
}

impl<T> Tree<T> {
    pub fn flatten(self) -> Vec<T> {
        #[inline]
        fn flatten_node<T>(node: Tree<T>, flat: &mut Vec<T>) {
            match node {
                Tree::Empty => {}
                Tree::Leaf(x) => {
                    flat.push(x);
                }
                Tree::VecLeaf(vec) => {
                    flat.extend(vec);
                }
                Tree::Node(children) => {
                    flatten_vec(children, flat);
                }
            }
        }

        fn flatten_vec<T>(nodes: Vec<Tree<T>>, flat: &mut Vec<T>) {
            for node in nodes {
                flatten_node(node, flat);
            }
        }

        let mut flat = Vec::new();
        flatten_node(self, &mut flat);
        flat
    }
}
