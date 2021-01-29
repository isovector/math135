import data.nat.basic
import tactic
import data.fin
import tactic.slim_check
import data.multiset.sort


def apply_le {α : Type} (f : α -> ℕ) (a b : α) : Prop := f a ≤ f b

instance decidable_apply_le {α : Type} (f : α -> ℕ) : decidable_rel (apply_le f) := 
begin
  intros a b,
  by_cases f a ≤ f b,
  {
    apply is_true,
    assumption,
  },
  apply is_false,
  assumption,
end

instance trans_apply_le {α : Type} (f : α -> ℕ) : is_trans α (apply_le f) := 
begin
  constructor,
  unfold apply_le,
  intros a b c a_lt_b b_lt_c,
  exact le_trans a_lt_b b_lt_c,
end

instance total_apply_le {α : Type} (f : α -> ℕ) : is_total α (apply_le f) := 
begin
  constructor,
  unfold apply_le,
  intros a b,
  by_cases f a ≤ f b,
  {
      left,
      assumption,
  },
  rw not_le at h,
  right,
  exact le_of_lt h,
end

instance antisymm_apply_le {α : Type} (f : α -> ℕ) (inj : function.injective f) : is_antisymm α (apply_le f) := 
begin
  constructor,
  unfold apply_le,
  intros a b a_lt_b b_lt_a,
  have h : f a = f b,
  {
    exact le_antisymm a_lt_b b_lt_a,
  },
  finish,
end

def sort_func_result {α : Type} [fintype α] (f : α → ℕ) (inj : function.injective f) : list α := 
  @multiset.sort α (apply_le f) _ _ (antisymm_apply_le f inj) _ (fintype.elems α).val

def vickrey_auction {α : Type} [inhabited α] [fintype α] (bids : α → ℕ) (inj : function.injective bids) := 
begin
  have sorted := list.reverse (sort_func_result bids inj),
  -- have sorted_not_nil : sorted ≠ list.nil := by sorry,
  exact (list.head sorted, bids (list.head (list.tail sorted))),
end

#check vickrey_auction
