import tactic
import data.nat.parity
import data.set
import data.set.basic

namespace lecture6

open set

example : {n | 4 ∣ n + 1} ⊆ {k | odd k} := 
begin
  rw set.subset_def,
  intros x hx,
  simp at hx,
  simp,
  cases nat.even_or_odd x,
  {
    refine nat.even_succ.symm.mpr _,
    refine even_iff_two_dvd.mpr _,
    refine dvd_of_mul_left_dvd _,
    use 2,
    exact hx,
  },
  exact nat.odd_iff_not_even.mp h,
end

lemma eq_intersect_union_one_contains_other 
    {α} 
    {s t : set α} 
    (union_eq_inter : s ∪ t = s ∩ t)
    : s ⊆ t := 
begin
  rw set.subset_def,
  intros x x_in_s,
  have s_in_union : s ⊆ s ∪ t := subset_union_left s t,
  have intersect_in_t : s ∩ t ⊆ t := inter_subset_right s t,
  refine mem_of_subset_of_mem intersect_in_t _,
  rw ← union_eq_inter,
  refine mem_of_subset_of_mem s_in_union _,
  exact x_in_s,
end

example : Π {α : Type} (s t : set α), s = t ↔ s ∪ t = s ∩ t :=
begin
  intros a s t,
  split,
  {
    intro s_eq_t,
    refine ext _,
    intro x,
    split,
    {
      intro x_in_union,
      rw s_eq_t at *,
      rw union_self at x_in_union,
      rw inter_self,
      exact x_in_union,
    },
    intro x_in_inter,
    rw s_eq_t at *,
    rw union_self,
    rw inter_self at x_in_inter,
    exact x_in_inter,
  },
  intro union_eq_intersect,
  
  have s_in_t : s ⊆ t := eq_intersect_union_one_contains_other union_eq_intersect,
  have t_in_s : t ⊆ s := 
  begin
    refine eq_intersect_union_one_contains_other _,
    rw union_comm,
    rw inter_comm,
    exact union_eq_intersect,
  end,

  exact le_antisymm s_in_t t_in_s,
end


end lecture6
