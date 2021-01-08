import data.int.basic
import data.nat.parity
import data.nat.prime
import tactic
import tactic.linarith

namespace lecture4

open nat

theorem div_14_div_7 : ∀ N, 14 ∣ N → 7 ∣ N :=
begin
  intros N h,
  cases h with divisor h,
  refine dvd.intro _ _,
  let divisor' := 2 * divisor,
  use divisor',
  simp,
  linarith,
end

theorem prime_and_prime_succ : ∀ p, prime p → prime (p + 1) → p = 2 :=
begin
  intros p hprime hprimesucc,
  cases even_or_odd p,
  {
    cases h with n hn,
    let hprime2 := hprime,
    cases hprime,
    specialize hprime_right n,
    have n_div_p : n ∣ p,
    {
      exact dvd.intro_left 2 (eq.symm hn)
    },

    cases hprime_right n_div_p,
    {
      linarith,
    },

    have p_zero : p = 0,
    {
      rw h at hn,
      linarith,
    },

    by_contradiction h',
    apply not_prime_zero,
    rw p_zero at hprime2,
    exact hprime2,
  },

  let h2 := h,
  cases h with n hn,
  cases hprimesucc,

  have n_div_succ_p : 2 ∣ succ p,
  {
    refine even_iff_two_dvd.mp _,
    refine even_succ.mpr _,
    exact odd_iff_not_even.mp h2,
  },

  specialize hprimesucc_right 2,
  cases hprimesucc_right n_div_succ_p,
  {
    by_contradiction h',
    linarith,
  },

  have n_zero : n = 0,
  {
    linarith,
  },

  rw n_zero at hn,
  by_contradiction,
  refine not_prime_one _,
  have p_one : p = 1,
  {
    linarith,
  },
  rw ←p_one,
  exact hprime,
end


lemma only_even_prime_is_2 : ∀ {n}, prime n -> even n -> n = 2 :=
begin
  intros n hp he,
  cases hp,
  cases he,
  specialize hp_right 2,
  cases hp_right (dvd.intro he_w (eq.symm he_h) : 2 ∣ n),
  {
    finish,
  },
  linarith,
end

theorem prime_and_prime_succ2
      {p} (hprime : prime p) (hprimesucc : prime (p + 1)) : p = 2 :=
begin
  cases even_or_odd p,
  {
    exact only_even_prime_is_2 hprime h,
  },
  exfalso,
  have p_succ_even : even (p + 1) := begin
    refine even_succ.mpr _,
    exact odd_iff_not_even.mp h,
  end,
  have p_succ_is_two : (p + 1) = 2 := only_even_prime_is_2 hprimesucc p_succ_even,
  have p_is_one : p = 1 := by linarith,
  refine not_prime_one _,
  rw p_is_one at hprime,
  exact hprime,
end

end lecture4
