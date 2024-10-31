import Mathlib.Tactic

variable {α : Type}

-- instead of `parent(x,y)` we write `P x y`
-- instead of `x > y` we write `D P x y` where `D P` is a relation based on `P` as follows
private inductive D (P : α → α → Prop) : α → α → Prop
  -- if `parent(x,y)` then `x > y`
  | direct (x y : α) (hxy : P x y) : D P x y
  -- if `parent(x,z)` and `z > y` then `x > y`
  | distant (x z y : α) (hxz : P x z) (hzy : D P z y) : D P x y

example {H M : α → Prop} (HxorM : ∀ a : α, H a ∧ ¬ M a ∨ M a ∧ ¬ H a)
  {x y : α} (monkey : M x) (human : H y) {P : α → α → Prop} (hXY : D P x y) :
  ∃ z₁ z₂ : α, P z₁ z₂ ∧ M z₁ ∧ H z₂ :=
by
  sorry -- TODO homework 4.2
