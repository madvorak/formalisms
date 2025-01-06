import Formalisms.Class3


variable {A : Type} [CompleteLattic A]

/- Kleene fixpoint theorem -/

theorem JoinContinuous.constructLeastFixpoint {F : A → A} (hF : JoinContinuous F) :
  LeastFixpoint F (⊔ { F^[i] ⊥ | i : ℕ }) :=
by
  have important : ∀ n : ℕ, F^[n] ⊥ ⊑ F^[n.succ] ⊥
  · intro n
    induction n with
    | zero =>
      apply bot_under
    | succ _ ih =>
      convert hF.monoton _ _ ih using 1 <;>
      · apply Function.iterate_succ_apply'
  constructor
  · set u := ⊔ { F^[i] ⊥ | i : ℕ }
    show F u = u
    rw [hF _ important]
    apply Poset.antis
    constructor
    · apply supre_is_least
      intro y ⟨i, hiy⟩
      apply supre_is_upper
      use i.succ
      rwa [Function.iterate_succ', Function.comp_apply]
    · apply supre_is_least
      intro y ⟨i, hiy⟩
      apply Poset.trans y (F y)
      constructor
      · rw [←hiy]
        convert important i using 1
        symm
        apply Function.iterate_succ_apply'
      · apply supre_is_upper
        use i
        rw [hiy]
  · intro y hy
    have under : ∀ i : ℕ, F^[i] ⊥ ⊑ y
    · intro i
      induction i with
      | zero =>
        apply bot_under
      | succ n ih =>
        rw [hy.symm, Function.iterate_succ_apply']
        apply hF.monoton
        exact ih
    apply supre_is_least _ y
    intro z ⟨i, hiz⟩
    specialize under i
    rwa [hiz] at under

theorem MeetContinuous.constructGreatFixpoint {F : A → A} (hF : MeetContinuous F) :
  GreatFixpoint F (⊓ { F^[i] ⊤ | i : ℕ }) :=
by
  have important : ∀ n : ℕ, F^[n.succ] ⊤ ⊑ F^[n] ⊤
  · intro n
    induction n with
    | zero =>
      apply top_above
    | succ _ ih =>
      convert hF.monoton _ _ ih using 1 <;>
      · apply Function.iterate_succ_apply'
  constructor
  · set l := ⊓ { F^[i] ⊤ | i : ℕ }
    show F l = l
    rw [hF _ important]
    apply Poset.antis
    constructor
    · apply infim_is_great
      intro y ⟨i, hiy⟩
      apply Poset.trans _ (F y)
      constructor
      · apply infim_is_lower
        use i
        rw [hiy]
      · rw [←hiy]
        convert important i using 1
        symm
        apply Function.iterate_succ_apply'
    · apply infim_is_great
      intro y ⟨i, hiy⟩
      apply infim_is_lower
      use i.succ
      rwa [Function.iterate_succ', Function.comp_apply]
  · intro y hy
    have above : ∀ i : ℕ, y ⊑ F^[i] ⊤
    · intro i
      induction i with
      | zero =>
        apply top_above
      | succ n ih =>
        rw [hy.symm, Function.iterate_succ_apply']
        apply hF.monoton
        exact ih
    apply infim_is_great _ y
    intro z ⟨i, hiz⟩
    specialize above i
    rwa [hiz] at above
