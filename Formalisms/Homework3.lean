import Formalisms.Class3


variable {A : Type} [CompleteLattic A]

/- Kleene fixpoint theorem -/

theorem JoinContinuous.constructLeastFixpoint {F : A → A} (hF : JoinContinuous F) :
  LeastFixpoint F (⊔ { F^[i] ⊥ | i : ℕ }) :=
by
  sorry

theorem MeetContinuous.constructGreatFixpoint {F : A → A} (hF : MeetContinuous F) :
  GreatFixpoint F (⊓ { F^[i] ⊤ | i : ℕ }) :=
by
  sorry
