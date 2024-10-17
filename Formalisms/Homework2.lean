import Formalisms.Class2

theorem fixpointKnasterTarski {A : Type} {F : A → A} [CompleteLattic A] (hF : Monoton F) :
  -- the least upper bound of all prefixpoints is a great fixpoint
  GreatFixpoint F (⊔ Prefixpoint F) ∧
  -- the great lower bound of all posfixpoints is a least fixpoint
  LeastFixpoint F (⊓ Posfixpoint F) :=
by
  have hyF := supre_is_upper (Prefixpoint F) -- `⊔`
  have hbF := infim_is_lower (Posfixpoint F) -- `⊓`
  have hy' := supre_is_least (Prefixpoint F) -- `⊔`
  have hb' := infim_is_great (Posfixpoint F) -- `⊓`
  set y := ⊔ Prefixpoint F -- `⊔`
  set b := ⊓ Posfixpoint F -- `⊓`
  sorry -- homework #2


theorem fixpointKnasterTarski_full {A : Type} {F : A → A} [CompleteLattic A] (hF : Monoton F) :
  -- the least upper bound of all prefixpoints is the unique great fixpoint
  (GreatFixpoint F).ContainsOnly (⊔ Prefixpoint F) ∧
  -- the great lower bound of all posfixpoints is the unique least fixpoint
  (LeastFixpoint F).ContainsOnly (⊓ Posfixpoint F) :=
by
  have hyF := supre_is_upper (Prefixpoint F) -- `⊔`
  have hbF := infim_is_lower (Posfixpoint F) -- `⊓`
  have hy' := supre_is_least (Prefixpoint F) -- `⊔`
  have hb' := infim_is_great (Posfixpoint F) -- `⊓`
  set y := ⊔ Prefixpoint F -- `⊔`
  set b := ⊓ Posfixpoint F -- `⊓`
  sorry
