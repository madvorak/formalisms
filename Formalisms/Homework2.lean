import Formalisms.Class2

theorem fixpointKnasterTarski {A : Type} {F : A → A} [CompleteLattic A] (hF : Monoton F) :
  -- the least upper bound of all prefixpoints is the (unique) great fixpoint
  (GreatFixpoint F).ContainsOnly (⊔ Prefixpoint F) ∧
  -- the great lower bound of all posfixpoints is the (unique) least fixpoint
  (LeastFixpoint F).ContainsOnly (⊓ Posfixpoint F) :=
by
  have hy := supre_is_UpperBound (Prefixpoint F) -- `⊔`
  have hb := infim_is_LowerBound (Posfixpoint F) -- `⊓`
  have hy' := supre_is_Least (Prefixpoint F) -- `⊔`
  have hb' := infim_is_Great (Posfixpoint F) -- `⊓`
  set y := ⊔ Prefixpoint F -- `⊔`
  set b := ⊓ Posfixpoint F -- `⊓`
  sorry -- homework #2
