import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic

open List

/-! ### 1. QuickCheck-style “length of append” -/
/--
for any lists `l₁ l₂` the length of their concatenation equals
`length l₁ + length l₂` (haskell quickCheck demo property)
-/
theorem length_append_eq {α : Type} (l₁ l₂ : List α) :
  (l₁ ++ l₂).length = l₁.length + l₂.length := by
  simp [List.length_append]

/-! ### 2. ScalaCheck-style “double reverse is identity” -/
/--
reversing a list twice gives the original list
(ScalaCheck tutorial property)
-/
theorem reverse_reverse_id {α : Type} (l : List α) :
  l.reverse.reverse = l := by
  simp [List.reverse_reverse]

/-! ### 3. test.check-style “sort is idempotent” -/
/--
sorting a list of natural numbers twice with ≤ yields the same list
(idempotence of `sort` in Clojure test.check docs).
gotta use `mergeSort` the implementation behind `List.sort`.
-/
-- def lt : Nat → Nat → Bool := fun x y => decide (x ≤ y)

-- theorem mergeSort_idempotent (l : List Nat) :
--   List.mergeSort lt l = List.mergeSort lt (List.mergeSort lt l) := by
--   apply Eq.symm
--   apply List.mergeSort_eq_self
--   apply List.sorted_mergeSort
