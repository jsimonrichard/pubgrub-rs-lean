class StrictPartialOrder (α : Type) where
  lt : α → α → Prop
  lt_irrefl : ∀ a : α, ¬lt a a
  lt_trans : ∀ a b c : α, lt a b → lt b c → lt a c
