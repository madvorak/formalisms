import Mathlib.Tactic


def rectanglec (a b : Float) : Float :=
  2 * (a + b)

#eval rectanglec 2.5 1

def fact : ℕ → ℕ
| 0     => 1
| (n+1) => (n+1) * fact n

#eval fact 7

def fibo : ℕ → ℕ
| 0     => 0
| 1     => 1
| (n+2) => fibo n + fibo (n+1)

#eval fibo 10


def Bound (f : ℝ → ℝ) (b : ℝ) : Prop := ∀ x : ℝ, f x ≤ b

def Bounded (f : ℝ → ℝ) : Prop := ∃ b : ℝ, Bound f b

theorem bounded_add_bounded (f g : ℝ → ℝ) : Bounded f ∧ Bounded g → Bounded (f+g) := by
  intro ⟨hf, hg⟩
  unfold Bounded Bound at *
  obtain ⟨a, hfa⟩ := hf
  obtain ⟨b, hgb⟩ := hg
  use a + b
  intro x
  show f x + g x ≤ a + b
  specialize hfa x
  specialize hgb x
  exact add_le_add hfa hgb


theorem almostCantor (T : Type) : ¬ (∃ f : T → Set T, f.Surjective) := by
  intro ⟨f, hf⟩
  unfold Function.Surjective at hf
  specialize hf { x | x ∉ f x }
  obtain ⟨a, ha⟩ := hf
  have impossible : a ∈ f a ↔ a ∉ f a
  · exact Eq.to_iff (congr_fun ha a)
  obtain ⟨yesin, notin⟩ := impossible
  if hyp : a ∈ f a then
  · apply yesin <;>
    · exact hyp
  else
  · apply yesin <;>
    · apply notin
      exact hyp



-- for next four: `exact`, `constructor`, `left`, `right`, `intro`, `use`, `cases`, `obtain`

theorem and_swap (P Q : Prop) : P ∧ Q → Q ∧ P := by
  tauto

theorem or_swap (P Q : Prop) : P ∨ Q → Q ∨ P := by
  tauto

theorem and_distrib_or (P Q R : Prop) : P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R := by
  tauto

theorem deMorgan_all {T : Type} {R : T → Prop} : (∀ a : T, ¬ R a) ↔ ¬ (∃ a : T, R a) := by
  tauto


-- prove manually:
theorem rationals_dense (x z : ℚ) : x < z → ∃ y : ℚ, x < y ∧ y < z :=
  exists_between
