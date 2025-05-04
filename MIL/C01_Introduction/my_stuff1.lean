import MIL.Common

open Nat

-- #check 2 + 2

-- def f (x : ℕ) :=
--   x + 2

-- #check f

-- def FermatLastTheorem :=
--   ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

-- #check FermatLastTheorem

theorem Even_mul : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say `m` and `n` are natural numbers, and assume `n = 2 * k`.
  rintro m n ⟨k, hk⟩
  -- We need to prove `m * n` is twice a natural number. Let's show it's twice `m * k`.
  use m * k
  -- Substitute for `n`,
  rw [hk]
  -- and now it's obvious.
  ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]


  example (a b c : ℝ) : a * b * c = b * (a * c) := by
    rw [mul_comm a b]
    rw [mul_assoc b a c]


    -- 1 goal
    -- x y : ℕ,
    -- h₁ : Prime x,
    -- h₂ : ¬Even x,
    -- h₃ : y > x
    -- ⊢ y ≥ 4

example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc] -- b * (a * c) == b * c * a
  rw [mul_comm] -- a * (b * c) == b * (a * c)

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_comm]
  rw [mul_assoc]
  rw [h]
  rw [mul_comm]
  ring

example (a b c d : ℝ) (h₁ : c = b * a - d) (h₂ : d = a * b) : c = 0 := by
  rw [h₁]
  rw [mul_comm]
  rw [h₂]
  ring

section
variable (a b c d e f g : ℝ)


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

-- example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
--   calc
--     (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
--       sorry
--     _ = a * a + (b * a + a * b) + b * b := by
--       sorry
--     _ = a * a + 2 * (a * b) + b * b := by
--       sorry


example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  calc
   (a + b) * (c + d) = a * (c + d) + b * (c + d) := by
      rw [mul_comm]
      rw [mul_add]
      ring
   _ = a * c + a * d + b * c + b * d := by
      rw [mul_add]
      ring

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [add_mul, mul_sub, mul_sub, mul_comm]
  ring
