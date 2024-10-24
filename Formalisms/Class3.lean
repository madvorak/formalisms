import Formalisms.Homework2


section induction_on_natural_numbers

theorem pow_two_lt_two_pow {n : ℕ} (at_least_five : n ≥ 5) : n^2 < 2^n := by
  sorry

end induction_on_natural_numbers


section continuous_functions

variable {A : Type} [CompleteLattic A]

def JoinContinuous (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, s n ⊑ s n.succ) →
    F (⊔ { s n | n : ℕ }) = ⊔ { F (s n) | n : ℕ }

def MeetContinuous (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, s n.succ ⊑ s n) →
    F (⊓ { s n | n : ℕ }) = ⊓ { F (s n) | n : ℕ }

lemma under_iff_supre_pair (a b : A) :
  a ⊑ b ↔ ⊔ {a, b} = b :=
by
  constructor <;> intro hab
  rw [←Set.LeastUpperBound.eq_supre]
  · constructor
    · intro x hx
      cases hx with
      | inl ha =>
        rw [ha]
        exact hab
      | inr hb =>
        rw [hb]
        apply Poset.refle
    · intro x hx
      apply hx
      apply Set.mem_insert_of_mem
      rfl
  · rw [←hab]
    apply supre_is_upper
    apply Set.mem_insert

lemma under_iff_infim_pair (a b : A) :
  a ⊑ b ↔ ⊓ {a, b} = a :=
by
  sorry

lemma JoinContinuous.monoton {F : A → A} (hF : JoinContinuous F) :
  Monoton F :=
by
  intro x y hxy
  have hFxy : F (⊔ {x, y}) = ⊔ {F x, F y} := by
    convert hF (fun i : ℕ => if i = 0 then x else y) (by
        intro
        have := Poset.refle y
        aesop
      ) using 1 <;>
    · congr
      apply Set.Subset.antisymm <;> intro z hz
      · cases hz with
        | inl hzx =>
          use 0
          exact hzx.symm
        | inr hzy =>
          use 1
          exact hzy.symm
      · obtain ⟨n, hn⟩ := hz
        cases n <;> simp_all
  rw [under_iff_supre_pair] at hxy ⊢
  rw [hxy] at hFxy
  exact hFxy.symm

lemma MeetContinuous.monoton {F : A → A} (hF : MeetContinuous F) :
  Monoton F :=
by
  sorry

-- TODO monotonicity implies one "direction" of continuity.

noncomputable instance : Bot A where
  bot := ⊔ Set.univ

noncomputable instance : Top A where
  top := ⊓ Set.univ

/- Kleene fixpoint theorem -/

theorem JoinContinuous.leastFixpoint {F : A → A} (hF : JoinContinuous F) :
  LeastFixpoint F (⊔ { F^[i] ⊥ | i : ℕ }) :=
by
  sorry -- homework

theorem MeetContinuous.greatFixpoint {F : A → A} (hF : MeetContinuous F) :
  GreatFixpoint F (⊓ { F^[i] ⊤ | i : ℕ }) :=
by
  sorry -- homework

end continuous_functions
