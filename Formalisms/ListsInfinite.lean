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

-- FYI there is no homework 4.3 because we solved it in the class.

example : ∀ x : IW, x ∈ E ↔ ∀ n : ℕ, (x.take (2*n)).count 0 = (x.take (2*n)).count 1 := by
  intro x
  constructor
  · intro ⟨X, hxX, hXX⟩ n
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
      cases' hXX hxX with xin xin <;>
      · simp at xin
        obtain ⟨x', hx', hxx'⟩ := xin
        rw [←hxx', show 2 * (n+1) = 2*n + 1 + 1 by ring]
        simp
        apply ih
        exact hx'
  · intro hx
    -- Mario Carneiro's co-induction trick!
    use { w : IW | ∀ n : ℕ, (w.take (2*n)).count 0 = (w.take (2*n)).count 1 }, hx
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image, exists_exists_and_eq_and]
    match hwh : w.head with
    | 0 =>
      left
      have hwth : w.tail.head = 1
      · specialize hw 1
        rw [mul_one] at hw
        rw [show w.take 2 = [w.head, w.tail.head] by rfl] at hw
        rw [hwh] at hw
        have almost : [w.tail.head].count 0 + 1 = [w.tail.head].count 1
        · convert hw using 1
          simp
        match wthval : w.tail.head with
        | 0 =>
          exfalso
          rw [wthval] at almost
          simp at almost
        | 1 => rfl
      use w.tail.tail
      constructor
      · intro n
        have hwn2 := hw n.succ
        have hw2 := hw 1
        have detach : w.take (2 * n.succ) = w.take 2 ++ w.tail.tail.take (2 * n)
        · rfl
        rw [detach] at hwn2
        rw [mul_one] at hw2
        rw [List.count_append, List.count_append] at hwn2
        clear * - hwn2 hw2
        linarith
      · convert_to (w.tail.tail.cons 1).cons 0 = w.tail.cons w.head
        · exact w.eta.symm
        rw [hwh]
        apply congr_arg
        convert_to w.tail.tail.cons 1 = w.tail.tail.cons w.tail.head
        · exact w.tail.eta.symm
        rw [hwth]
    | 1 =>
      right
      have hwth : w.tail.head = 0
      · specialize hw 1
        rw [mul_one] at hw
        rw [show w.take 2 = [w.head, w.tail.head] by rfl] at hw
        rw [hwh] at hw
        have almost : [w.tail.head].count 0 = [w.tail.head].count 1 + 1
        · convert hw using 1
          simp
        match wthval : w.tail.head with
        | 1 =>
          exfalso
          rw [wthval] at almost
          simp at almost
        | 0 => rfl
      use w.tail.tail
      constructor
      · intro n
        have hwn2 := hw n.succ
        have hw2 := hw 1
        rw [show w.take (2 * n.succ) = w.take 2 ++ w.tail.tail.take (2 * n) by rfl] at hwn2
        rw [mul_one] at hw2
        rw [List.count_append, List.count_append] at hwn2
        clear * - hwn2 hw2
        linarith
      · convert_to (w.tail.tail.cons 0).cons 1 = w.tail.cons w.head
        · exact w.eta.symm
        rw [hwh]
        apply congr_arg
        convert_to w.tail.tail.cons 0 = w.tail.tail.cons w.tail.head
        · exact w.tail.eta.symm
        rw [hwth]
