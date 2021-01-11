import tactic
import data.nat.basic
import data.nat.prime
import data.real.basic
import data.nat.gcd
import data.real.sqrt
import data.nat.parity
import tactic.slim_check

namespace lecture10

open nat

def irrational (r : ℝ) := ∀ (n d : ℕ), (d ≠ 0) -> coprime n d -> ¬ coe n / coe d = r

lemma not_coprime_if_even {a b : ℕ} (even_a : even a) (even_b : even b) : ¬ (coprime a b) := 
begin
  intro h_coprime,
  rw [coprime] at h_coprime,
  have two_div_coprime : 2 ∣ gcd a b := dvd_gcd even_a even_b,
  rw h_coprime at two_div_coprime,
  finish,
end

lemma even_iff_even_square {a : ℕ} : even a ↔ even (a ^ 2) :=
begin
  fconstructor,
  {
    intro h,
    refine even_iff_two_dvd.mpr _,
    cases h with k hk,
    rw hk,
    rw pow_two,
    refine dvd_mul_of_dvd_left _ (2 * k),
    exact dvd.intro k rfl,
  },
  {
    intro h,
    refine even_iff_two_dvd.mpr _,
    rw pow_two at h,
    rw even_mul at h,
    finish,
  },
end

lemma irrational_sqrt_2 : irrational (real.sqrt 2) := 
begin
  rw irrational,
  intros n d d_neq_zero h,
  by_contra,

  have h' : n^2 = 2 * d^2 := 
  begin
    have x' : (coe n)^2 = (real.sqrt 2)^2 * (coe d)^2 := 
    begin
      refine tactic.ring_exp.pow_pp_pf_prod _ rfl rfl,
      refine (div_eq_iff _).mp h,
      exact cast_ne_zero.mpr d_neq_zero,
    end,
    rw real.sqr_sqrt at x',
    assumption_mod_cast,
    norm_num,
  end,

  have even_pow_n_2 : even (n^2) := begin
    refine even_iff_two_dvd.mpr _,
    finish,
  end,

  have even_n  : even n := even_iff_even_square.mpr even_pow_n_2,
  have even_n' : even n := even_n,

  cases even_n with k hk,
  have yo :=
    calc 
      2 * d^2 = n^2            : h'.symm
          ... = (2 * k)^2      : by rw hk
          ... = 2^2 * k^2      : by linarith
          ... = 4 * k^2        : by linarith
          ... = 2 * (2 * k^2)  : by linarith,
  replace h := (mul_right_inj' (by norm_num)).1 yo,
  have even_pow_d_2 : even (d^2) := 
  begin
     refine even_iff_two_dvd.mpr _,
     finish,
  end,
  have even_d : even d := even_iff_even_square.mpr even_pow_d_2,

  have not_coprime : ¬ coprime n d := not_coprime_if_even even_n' even_d,
  contradiction,
end

end lecture10