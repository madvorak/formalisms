import Mathlib.Tactic
import Mathlib.Data.List.Basic

variable {α : Type}


-- ### Concatenating lists

def cat : List α → List α → List α
| [ ]   , y => y
| a :: x, y => a :: cat x y

infix:66 " ;; " => cat
-- Outside of this exercise, we will write `++` for `List.append` which comes with many lemmas.

theorem cat_assoc (x y z : List α) :
  (x ;; y) ;; z = x ;; (y ;; z) :=
by
  induction x with
  | nil => rfl
  | cons a s ih => exact congr_arg (a :: ·) ih

theorem cat_nil (x : List α) :
  x ;; [] = x :=
by
  induction x with
  | nil => rfl
  | cons a s ih => exact congr_arg (a :: ·) ih


-- ### Reversing lists

def rev : List α → List α
| [ ]    => [ ]
| a :: x => rev x ;; [a]

private def r : List α → List α → List α
| [ ]   , y => y
| a :: x, y => r x (a :: y)

def rev' (x : List α) : List α :=
  r x []

private lemma rev_eq_r (x : List α) :
  rev x = r x [] :=
by
  -- starting by `induction x` would get us into a blind alley
  have generalized : ∀ x y : List α, rev x ;; y = r x y
  · clear x
    intro x
    -- here `intro y` would get us into another blind alley
    induction x with
    | nil =>
      intro y
      rfl
    | cons a u ih =>
      intro y
      unfold rev r
      rewrite [←ih (a :: y), cat_assoc]
      rfl
  specialize generalized x []
  rw [cat_nil] at generalized
  exact generalized

theorem rev_eq_rev' : @rev α = rev' :=
by
  ext1
  apply rev_eq_r


-- ### Sorting lists

/-- Creates a list made of every other element of given list, starting with its head.  -/
private def eo : List α → List α
| [ ]         => [ ]
| [ a ]       => [ a ]
| a :: _ :: s => a :: eo s

private lemma length_eo_cons (a : α) (s : List α) :
  (eo s).length ≤ (eo (a :: s)).length ∧
  (eo (a :: s)).length ≤ (eo s).length.succ :=
by
  induction s with
  | nil => simp [eo]
  | cons d l ih =>
    cases l with
    | nil => simp [eo, ih]
    | cons d' l' =>
      simp [eo] at ih ⊢
      constructor
      · exact ih.right
      · exact ih.left

private lemma length_eo2_lt (a b : α) (s : List α) :
  (eo (a :: b :: s)).length < s.length.succ.succ :=
by
  induction s with
  | nil => simp [eo]
  | cons d l ih =>
    cases l with
    | nil => simp [eo, ih]
    | cons d' l' =>
      simp [eo] at ih ⊢
      have not_longer := (length_eo_cons d' l').left
      linarith

private lemma length_eo1_lt (a : α) (s : List α) :
  (eo (a :: s)).length < s.length.succ.succ :=
by
  cases s with
  | nil => simp [eo]
  | cons d l =>
    apply (length_eo2_lt a d l).trans_le
    apply Nat.succ_le_succ
    apply Nat.succ_le_succ
    exact Nat.le_succ l.length

variable [LinearOrder α]

def merge : List α → List α → List α
| [ ]   , y      => y
| x     , [ ]    => x
| a :: x, b :: y => if a ≤ b
                    then a :: merge x (b :: y)
                    else b :: merge (a :: x) y
termination_by
  x y => x.length + y.length

def mergesort : List α → List α
| [ ]         => [ ]
| [ a ]       => [ a ]
| a :: b :: s => merge (mergesort (eo (a :: b :: s))) (mergesort (eo (b :: s)))
-- the compiler needs the following hints
termination_by l => l.length
decreasing_by
  simp_wf
  · apply length_eo2_lt
  · apply length_eo1_lt


private def testList : List ℕ := [3, 5, 7, 1, 9, 5, 0, 2, 4, 6, 8]
#eval mergesort testList  -- 0..9 with 5 twice
#eval mergesort (rev' testList) -- dtto
#eval rev' (mergesort testList) -- dtto backwards


def IsSorted : List α → Prop
| [ ]         => True
| [ _ ]       => True
| a :: b :: s => a ≤ b ∧ IsSorted (b :: s)


/- ### Lists "contain the same elements"

Mathlib (imported here) defines list permutations as follows.
If `s` and `t` are lists of the same type, then `s ~ t` denotes that `s` is a permutation of `t`
where `~` is a binary relation defined by the following four rules:
• empty list is a permutation of empty list: `[] ~ []`
• if `a` is an element and `x` and `y` are lists such that `x ~ y` then we have: `a :: x ~ a :: y`
• if `a` and `b` are elements and `x` is a list then we have: `b :: a :: x ~ a :: b :: x`
• if `x`, `y`, `z` are lists such that `x ~ y` and `y ~ z` then we have: `x ~ z`
-/
open scoped List

theorem mergesort_works : ∀ x : List α, IsSorted (mergesort x) ∧ (mergesort x) ~ x :=
by
  sorry -- TODO homework 4.1
