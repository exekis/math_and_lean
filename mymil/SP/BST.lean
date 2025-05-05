import MIL.Common
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


inductive Tree1 (α : Type) where
  | empty : Tree1 α
  | node : Tree1 α → α → Tree1 α → Tree1 α
  deriving Repr

namespace BST

def BinarySearchTree1 (α : Type) [Ord α] := Tree1 α

def isEmpty {α : Type} : Tree1 α → Bool
  | .empty => true
  | .node _ _ _ => false

def insert {α : Type} [Ord α] (x : α) : Tree1 α → Tree1 α
  | .empty => .node .empty x .empty
  | .node left root right =>
    match compare x root with
    | .lt => .node (insert x left) root right
    | .eq => .node left root right
    | .gt => .node left root (insert x right)

def contains {α : Type} [Ord α] (x : α) : Tree1 α → Bool
  | .empty => false
  | .node left root right =>
    match compare x root with
    | .lt => contains x left
    | .eq => true
    | .gt => contains x right

def findMin {α : Type} : Tree1 α → Option α
  | .empty => none
  | .node .empty root _ => some root
  | .node left _ _ => findMin left

def findMax {α : Type} : Tree1 α → Option α
  | .empty => none
  | .node _ root .empty => some root
  | .node _ _ right => findMax right

def remove {α : Type} [Ord α] (x : α) : Tree1 α → Tree1 α
  | .empty => .empty
  | .node left root right =>
    match compare x root with
    | .lt => .node (remove x left) root right
    | .gt => .node left root (remove x right)
    | .eq =>
      match left, right with
      | .empty, .empty => .empty
      | .empty, r => r
      | l, .empty => l
      | l, r =>
        match findMin r with
        | none => .empty  -- this should never happen btw!
        | some minRight =>
          .node l minRight (remove minRight r)

-- (for demonstration, not a full proof)
def isBST {α : Type} [Ord α] : Tree1 α → Bool
  | .empty => true
  | .node left root right =>
    (match findMax left with
    | none => true
    | some maxLeft => compare maxLeft root == .lt) &&
    (match findMin right with
    | none => true
    | some minRight => compare root minRight == .lt) &&
    isBST left && isBST right

def empty {α : Type} : Tree1 α := Tree1.empty

end BST

-- tests

def exampleTree : Tree1 Nat :=
  BST.insert 5 (BST.insert 3 (BST.insert 7 (BST.insert 10 (BST.insert 4 BST.empty))))

#check exampleTree
#eval exampleTree
#eval BST.contains 5 exampleTree
#eval BST.contains 10 exampleTree
#eval BST.findMin exampleTree
#eval BST.findMax exampleTree
