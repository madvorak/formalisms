import Formalisms.Class2

variable {A : Type}

def Monoton [Relation A] (F : A → A) : Prop :=
  ∀ x y : A, x ⊑ y → F x ⊑ F y

/-
The recent changes to `Class2.lean` don't influence the homework in any way.
Use which whichever version of the files `Class2.lean` and `Homework2.lean` you want to use,
just make sure your copy of the repository isn't older than the second class, i.e.,
be on the revision c4c781cea73d5eb46ce97b1e36c8f189af34e603 or newer.
-/
theorem fixpointKnasterTarski {F : A → A} [CompleteLattic A] (hF : Monoton F) :
  -- the least upper bound of all prefixpoints is a great fixpoint
  GreatFixpoint F (⊔ Prefixpoint F) ∧
  -- the great lower bound of all posfixpoints is a least fixpoint
  LeastFixpoint F (⊓ Posfixpoint F) :=
by
  have hyF := supre_is_upper (Prefixpoint F) -- `⊔`
  have hbF := infim_is_lower (Posfixpoint F) -- `⊓`
  have hy' := supre_is_least (Prefixpoint F) -- `⊔`
  have hb' := infim_is_great (Posfixpoint F) -- `⊓`
  set y := ⊔ Prefixpoint F
  set b := ⊓ Posfixpoint F
  constructor
  · have hyFy : y ⊑ F y
    · have hFxFy : ∀ x, Prefixpoint F x → F x ⊑ F y
      · intro x hx
        apply hF
        apply hyF
        exact hx
      have hxFy : ∀ x, Prefixpoint F x → x ⊑ F y
      · intro x hx
        apply Poset.trans
        constructor
        · exact hx
        · apply hFxFy
          exact hx
      apply hy'
      exact hxFy
    constructor
    · apply Poset.antis
      constructor
      · apply hyF
        apply hF
        exact hyFy
      · exact hyFy
    · intro a ha
      apply hyF
      apply prefixpoint_of_fixpoint
      exact ha
  · have hFbb : F b ⊑ b
    · have hFbFx : ∀ x, Posfixpoint F x → F b ⊑ F x
      · intro x hx
        apply hF
        apply hbF
        exact hx
      have hFbx : ∀ x, Posfixpoint F x → F b ⊑ x
      · intro x hx
        apply Poset.trans
        constructor
        · apply hFbFx
          exact hx
        · exact hx
      apply hb'
      exact hFbx
    constructor
    · apply Poset.antis
      constructor
      · exact hFbb
      · apply hbF
        apply hF
        exact hFbb
    · intro a ha
      apply hbF
      apply posfixpoint_of_fixpoint
      exact ha
