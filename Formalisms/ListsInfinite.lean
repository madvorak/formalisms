import Mathlib.Tactic
import Mathlib.Data.Stream.Init


private abbrev IW := Stream' (Fin 2)

-- Let `E` be the largest `X : {0,1}^ω` such that `X ⊆ 01X ∪ 10X`.

private def E : Set IW :=
  fun w : IW =>
    ∃ X : Set IW, -- Alex Keizer's union-of-all-prefixpoints trick!
      w ∈ X ∧
      X ⊆ (Stream'.cons 0 '' (Stream'.cons 1 '' X))
        ∪ (Stream'.cons 1 '' (Stream'.cons 0 '' X))

-- Prove `∀ x : {0,1}^ω` we have `x ∈ S` ↔ every finite prefix of `x` of even length has #`0` = #`1`.

example : ∀ x : IW, x ∈ E ↔ ∀ n : ℕ, (x.take (2*n)).count 0 = (x.take (2*n)).count 1 := by
  intro x
  constructor
  · sorry -- TODO homework 4.3
  · intro hx
    -- Mario Carneiro's co-induction trick!
    use { w : IW | ∀ n : ℕ, (w.take (2*n)).count 0 = (w.take (2*n)).count 1 }
    sorry
