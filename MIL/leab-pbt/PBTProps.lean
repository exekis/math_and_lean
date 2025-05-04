/-
PBTProps.lean – formal proofs of three standard
property-based-testing “equations” in Lean 4.

Requires: mathlib4 (tested with a reasonably recent version)
-/

import Mathlib.Data.List.Basic     -- length, reverse, append
import Mathlib.Data.List.Sort      -- mergeSort & lemmas
import Mathlib.Tactic              -- `simp`, `rw`, `exact`, etc.

open List

/-! ### 1. QuickCheck-style “length of append” -/

/-- For any lists `l₁ l₂`, the length of their concatenation equals
    `length l₁ + length l₂` (Haskell QuickCheck demo property). -/
theorem length_append_eq {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).length = l₁.length + l₂.length := by
  -- Use `simp` with the specific lemma from the library.
  simp [List.length_append]


/-! ### 2. ScalaCheck-style “double reverse is identity” -/

/-- Reversing a list twice gives the original list
    (canonical ScalaCheck tutorial property). -/
theorem reverse_reverse_id {α : Type} (l : List α) :
    l.reverse.reverse = l := by
  -- Use `simp` with the specific lemma from the library.
  simp [List.reverse_reverse]


/-! ### 3. test.check-style “sort is idempotent” -/

/--
Sorting a list of natural numbers twice with ≤ yields the same list
(idempotence of `sort`; showcased in Clojure test.check docs).
We use `mergeSort`, the implementation behind `List.sort`.

`≤` is a total, transitive and antisymmetric relation on `ℕ`, so the
library lemmas we need (`IsTotal`, `IsTrans`, `IsAntisymm` instances for `Nat.le`)
are already available and inferred automatically by the tactics.
-/
theorem mergeSort_idempotent (l : List Nat) :
    -- Goal: sort l = sort (sort l)
    List.mergeSort (· ≤ ·) l =
      List.mergeSort (· ≤ ·) (List.mergeSort (· ≤ ·) l) := by
  -- Let `sl` be the sorted version of `l`.
  let sl := List.mergeSort (· ≤ ·) l
  -- Show that `sl` is sorted using the standard library lemma `sorted_mergeSort'`.
  -- `sorted_mergeSort'` needs `IsTrans` and `IsTotal` for `(· ≤ ·)`, which are available for `Nat.le`.
  have hsorted : List.Sorted (· ≤ ·) sl := by
    exact List.sorted_mergeSort' (· ≤ ·) l
  -- Show that sorting an already sorted list (`sl`) yields the list itself.
  -- `mergeSort_eq_self` needs `IsTrans` and `IsAntisymm` for `(· ≤ ·)`, which are available for `Nat.le`.
  have h_idem_rhs : List.mergeSort (· ≤ ·) sl = sl := by
    -- We use `.symm` because `mergeSort_eq_self` proves `List.mergeSort r l = l` given `Sorted r l`.
    -- Our goal here is `List.mergeSort (· ≤ ·) sl = sl`, and we have `hsorted : List.Sorted (· ≤ ·) sl`.
    exact (List.mergeSort_eq_self (· ≤ ·) hsorted).symm
  -- The theorem statement is `sl = List.mergeSort (· ≤ ·) sl` after substituting `sl`.
  -- We have derived `h_idem_rhs : List.mergeSort (· ≤ ·) sl = sl`.
  -- Applying symmetry to `h_idem_rhs` gives exactly the goal.
  exact h_idem_rhs.symm
