import Mathlib.Tactic.NormNum

inductive AVLTree1 (α : Type) : Option Nat → Option Nat → Nat → Type where
  | leaf : AVLTree1 α none none 0
  | node (key : Nat) (value : α) {lo hi : Option Nat} {l r : Nat}
    (left : AVLTree1 α lo (some key) l) (right : AVLTree1 α (some key) hi r)
    (bal : l ≤ r + 1 ∧ r ≤ l + 1) : AVLTree1 α lo hi (max l r + 1)

@[simp] def height {α : Type} {lo hi : Option Nat} {h : Nat} (_ : AVLTree1 α lo hi h) : Nat := h

def balanceFactor {α : Type} {lo hi : Option Nat} {h : Nat} (t : AVLTree1 α lo hi h) : Int :=
  match t with
  | .leaf => 0
  | .node _ _ left right _ =>
      Int.ofNat (height left) - Int.ofNat (height right)

def leftChild {α : Type} {lo hi : Option Nat} {h : Nat} :
  AVLTree1 α lo hi h → Option (Σ lo' hi' h', AVLTree1 α lo' hi' h')
  | .leaf => none
  | .node _ _ left _ _ => some ⟨_, _, _, left⟩

def rightChild {α : Type} {lo hi : Option Nat} {h : Nat} :
  AVLTree1 α lo hi h → Option (Σ lo' hi' h', AVLTree1 α lo' hi' h')
  | .leaf => none
  | .node _ _ _ right _ => some ⟨_, _, _, right⟩

def key {α : Type} {lo hi : Option Nat} {h : Nat} :
  AVLTree1 α lo hi h → Option Nat
  | .leaf => none
  | .node k _ _ _ _ => some k

def value {α : Type} {lo hi : Option Nat} {h : Nat} :
  AVLTree1 α lo hi h → Option α
  | .leaf => none
  | .node _ v _ _ _ => some v

theorem leaf_height {α : Type} :
  height (AVLTree1.leaf : AVLTree1 α none none 0) = 0 :=
  rfl

theorem node_balance {α : Type} {lo hi : Option Nat} {l r : Nat}
  (k : Nat) (v : α)
  (left : AVLTree1 α lo (some k) l)
  (right : AVLTree1 α (some k) hi r)
  (h : l ≤ r + 1 ∧ r ≤ l + 1) :
  balanceFactor (.node k v left right h) = Int.ofNat l - Int.ofNat r := by
  simp [balanceFactor]


-- Create a simple function to construct a leaf
def mkLeaf {α : Type} : AVLTree1 α none none 0 :=
  AVLTree1.leaf

-- Basic helper to get height
def getHeight {α : Type} {lo hi : Option Nat} {h : Nat} (t : AVLTree1 α lo hi h) : Nat :=
  height t


def mkBalanceProof (l r : Nat) (h : l ≤ r + 1 ∧ r ≤ l + 1) : l ≤ r + 1 ∧ r ≤ l + 1 := h
