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
    apply nat.even_succ.symm.mpr,
    refine dvd_of_mul_left_dvd _,
    use 2,
    exact hx,
  },
  exact nat.odd_iff_not_even.mp h,
end


example : Π {α : Type} (s t : set α), s = t ↔ s ∪ t = s ∩ t :=
begin
  intros a s t,
  split,
  {
    intro s_eq_t,
    rw [s_eq_t, union_self, inter_self],
  },
  intro union_eq_intersect,
  apply le_antisymm,
  {
    calc s ⊆ s ∪ t : subset_union_left s t
    ...    = s ∩ t  : union_eq_intersect
    ...    ⊆ t     : inter_subset_right s t,
  },
  calc t ⊆ s ∪ t : subset_union_right s t
  ...    = s ∩ t  : union_eq_intersect
  ...    ⊆ s     : inter_subset_left s t,
end


end lecture6
