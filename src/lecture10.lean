import tactic
import data.nat.basic
import data.nat.prime
import data.real.basic
import data.nat.gcd
import data.real.sqrt

namespace lecture10

open nat

def irrational (r : ℝ) := ∀ (n d : ℕ), coprime n d -> ¬ coe n / coe d = r

lemma not_coprime_if_even {a b : ℕ} (even_a : even a) (even_b : even b) : ¬ (coprime a b) := 
begin
  cases even_a with i hi,
  cases even_b with j hj,
  have two_div_a : 2 ∣ a := by sorry,
  have two_div_b : 2 ∣ b := by sorry,
  intro h_coprime,
  simp [coprime] at h_coprime,
  have h : a.gcd b ≥ 2 := begin
    rw hi,
    rw hj,
    simp,
    sorry,
  end,
  rw h_coprime at h,
  linarith,
end

lemma even_iff_even_square {a : ℕ} : even a ↔ even (a ^ 2) :=
begin
  sorry
end

lemma irrational_sqrt_2 : irrational (real.sqrt 2) := 
begin
  rw irrational,
  intros n d h,
  by_contra,

  have h' : n^2 = 2 * d^2 := 
  begin
    have x : coe n = real.sqrt 2 * coe d := by sorry,
    have x' : (coe n)^2 = (real.sqrt 2)^2 * (coe d)^2 := 
      tactic.ring_exp.pow_pp_pf_prod x rfl rfl,
    rw real.sqr_sqrt at x',
    {
      
    },

  end,
    

  
  have even_pow_n_2 : even (n^2) := begin
    refine even_iff_two_dvd.mpr _,
    sorry,
  end,
  have even_n : even n := even_iff_even_square.mpr even_pow_n_2,
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
     sorry,
  end,
  have even_d : even d := even_iff_even_square.mpr even_pow_d_2,

  have not_coprime : ¬ coprime n d := not_coprime_if_even even_n' even_d,
  sorry,
end

end lecture10