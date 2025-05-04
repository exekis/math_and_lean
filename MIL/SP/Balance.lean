inductive AvlTree1 (α : Type) where
  -- | leaf : AvlTree1 α
  -- | node (value : α) (height : Nat) (left : AvlTree1 α) (right : AvlTree1 α) : AvlTree1 α
  | empty : AvlTree1 α
  | node (value : α) (height : Nat) (left : AvlTree1 α) (right : AvlTree1 α) : AvlTree1 α

def AvlTree1.height {α : Type} : AvlTree1 α → Nat
  | AvlTree1.empty => 0
  | AvlTree1.node _ height _ _ => height

def AvlTree1.balanceFactor {α : Type} : AvlTree1 α → Int
  | AvlTree1.empty => 0
  | AvlTree1.node _ _ left right => left.height - right.height

def AvlTree1.isAvl {α : Type} : AvlTree1 α → Bool
  -- match every possible case of AvlTree1 and check if it is AVL using balance factor
  | AvlTree1.empty => true
  | AvlTree1.node _ _ left right => left.isAvl && right.isAvl && Int.ofNat left.height - Int.ofNat right.height <= 1 && Int.ofNat left.height - Int.ofNat right.height >= -1
