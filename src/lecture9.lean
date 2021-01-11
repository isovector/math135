import tactic
import data.nat.basic
import data.nat.prime
import data.real.sqrt


namespace lecture9

open nat

example {x : ℤ} : x^3 - 5 * x^2 + 3 * x ≠ 15 -> x ≠ 5 :=
begin
  contrapose,
  intro x_eq_5,
  simp at x_eq_5,
  simp,
  rw x_eq_5,
  linarith,
end

end lecture9