import tactic
import data.nat.basic
import data.nat.prime


namespace lecture7

open nat

example : ¬ (∀ a b c : ℕ, a ∣ (b * c) -> a ∣ b ∨ a ∣ c) :=
begin
  intros hx,
  specialize hx 6 2 3,
  have not_dvd_2 : ¬ (6 ∣ 2) := of_to_bool_ff rfl,
  have not_dvd_3 : ¬ (6 ∣ 3) := of_to_bool_ff rfl,
  cases hx (dvd_refl 6),
  exact not_dvd_2 h,
  exact not_dvd_3 h,
end

end lecture7