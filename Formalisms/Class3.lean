import Formalisms.Homework2
import Mathlib.Data.Stream.Init


section induction_on_natural_numbers

theorem pow_two_lt_two_pow {n : ℕ} (at_least_five : n ≥ 5) : n^2 < 2^n := by
  sorry

end induction_on_natural_numbers


section continuous_functions

variable {A : Type} [CompleteLattic A]

def SupreContinuous (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, s n ⊑ s n.succ) →
    F (⊔ { s n | n : ℕ }) = ⊔ { F (s n) | n : ℕ }

def InfimContinuous (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, s n.succ ⊑ s n) →
    F (⊓ { s n | n : ℕ }) = ⊓ { F (s n) | n : ℕ }

lemma under_iff_supre_pair (a b : A) :
  a ⊑ b ↔ ⊔ {a, b} = b :=
by
  sorry

lemma under_iff_infim_pair (a b : A) :
  a ⊑ b ↔ ⊓ {a, b} = a :=
by
  sorry

lemma SupreContinuous.monoton {F : A → A} (suprec : SupreContinuous F) :
  Monoton F :=
by
  sorry

lemma InfimContinuous.monoton {F : A → A} (infimc : InfimContinuous F) :
  Monoton F :=
by
  sorry

noncomputable instance : Bot A where
  bot := ⊔ Set.univ

noncomputable instance : Top A where
  top := ⊓ Set.univ

theorem leastFixpoint_of_supreContinuous {F : A → A} (hF : SupreContinuous F) :
  LeastFixpoint F (⊔ { F^[i] ⊥ | i : ℕ }) :=
by
  sorry

theorem greatFixpoint_of_infimContinuous {F : A → A} (hF : InfimContinuous F) :
  GreatFixpoint F (⊓ { F^[i] ⊤ | i : ℕ }) :=
by
  sorry

end continuous_functions


section infinite_words

private abbrev IW := Stream' (Fin 2)

-- Let `S` be the largest subset of `{0,1}^ω` such that `X ⊆ 01X ∪ 10X`.

private def S : Set IW :=
  fun w : IW =>
    ∃ X : Set IW, -- Alex Keizer's union-of-all-prefixpoints trick!
      w ∈ X ∧
      X ⊆ (Stream'.cons 0 '' (Stream'.cons 1 '' X))
        ∪ (Stream'.cons 1 '' (Stream'.cons 0 '' X))

-- Prove `∀ x : {0,1}^ω` we have `x ∈ S` ↔ every finite prefix of `x` of even length has #`0` = #`1`.

example : ∀ x : IW, x ∈ S ↔ ∀ n : ℕ, (x.take (2*n)).count 0 = (x.take (2*n)).count 1 := by
  intro x
  constructor
  · sorry
  · intro hx
    -- Mario Carneiro's co-induction trick!
    use { w : IW | ∀ n : ℕ, (w.take (2*n)).count 0 = (w.take (2*n)).count 1 }
    constructor
    · exact hx
    · sorry

end infinite_words
