import tactic
import data.nat.basic
import data.nat.prime


namespace lecture7

open nat

example : ∀ n, ¬ prime (2 * n * n + 11 * n + 15) := 
begin
  intro n,
  let m := (2 * n + 5) * (n + 3),
  have factored : (2 * n * n + 11 * n + 15 = m) := by linarith,
  rw factored,
  refine not_prime_mul _ _,
  linarith,
  linarith,
end

example (a b c : ℕ) : (∀ x, a ∣ (b * x + c)) -> a ∣ b + c := 
begin
  intro h,
  specialize h 1,
  rw mul_one at h, 
  exact h,
end

example (x : ℤ) : (x^2 + 4 * x + 7 > 0) :=
begin
  have factored : (x^2 + 4 * x + 7 = (x + 2)^2 + 3) := by linarith,
  rw factored,
  have h : (x + 2)^2 ≥ 0 := begin
    rw pow_two,
    exact mul_self_nonneg (x + 2),
  end,
  refine lt_add_of_nonneg_of_lt h _,
  linarith,
end

end lecture7