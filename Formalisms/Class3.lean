import Formalisms.Homework2


section induction_on_natural_numbers

lemma pow_two_lt_two_pow_aux_add_five (n : ℕ) : (n+5) ^ 2 < 2 ^ (n+5) := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    convert_to (n + 1 + 5) ^ 2 < 2 ^ (n+5) + 2 ^ (n+5)
    · ring
    convert_to (n+5) ^ 2 + (n+5) * 2 + 1 < 2 ^ (n+5) + 2 ^ (n+5)
    · ring
    nlinarith

theorem pow_two_lt_two_pow {n : ℕ} (at_least_five : n ≥ 5) : n^2 < 2^n := by
  convert pow_two_lt_two_pow_aux_add_five (n-5) <;> omega

end induction_on_natural_numbers


section continuous_functions

variable {A : Type} [CompleteLattic A]

example {F : A → A} (hF : Monoton F) {s : ℕ → A} :
  ⊔ { F (s n) | n : ℕ } ⊑ F (⊔ { s n | n : ℕ }) :=
by
  apply supre_is_least
  simp [Set.UpperBound]
  intro i
  apply hF
  apply supre_is_upper
  use i

example {F : A → A} (hF : Monoton F) {s : ℕ → A} :
  F (⊓ { s n | n : ℕ }) ⊑ ⊓ { F (s n) | n : ℕ } :=
by
  apply infim_is_great
  simp [Set.LowerBound]
  intro i
  apply hF
  apply infim_is_lower
  use i

def JoinContinuous (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, s n ⊑ s n.succ) →
    F (⊔ { s n | n : ℕ }) = ⊔ { F (s n) | n : ℕ }

def MeetContinuous (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, s n.succ ⊑ s n) →
    F (⊓ { s n | n : ℕ }) = ⊓ { F (s n) | n : ℕ }

lemma above_iff_supre_pair (a b : A) :
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
  constructor <;> intro hab
  rw [←Set.GreatLowerBound.eq_infim]
  · constructor
    · intro x hx
      cases hx with
      | inl ha =>
        rw [ha]
        apply Poset.refle
      | inr hb =>
        rw [hb]
        exact hab
    · intro x hx
      apply hx
      apply Set.mem_insert
  · rw [←hab]
    apply infim_is_lower
    apply Set.mem_insert_of_mem
    rfl

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
  rw [above_iff_supre_pair] at hxy ⊢
  rw [hxy] at hFxy
  exact hFxy.symm

lemma MeetContinuous.monoton {F : A → A} (hF : MeetContinuous F) :
  Monoton F :=
by
  intro x y hxy
  have hFxy : F (⊓ {x, y}) = ⊓ {F x, F y} := by
    convert hF (fun i : ℕ => if i = 0 then y else x) (by
        intro
        have := Poset.refle x
        aesop
      ) using 1 <;>
    · congr
      apply Set.Subset.antisymm <;> intro z hz
      · cases hz with
        | inl hzx =>
          use 1
          exact hzx.symm
        | inr hzy =>
          use 0
          exact hzy.symm
      · obtain ⟨n, hn⟩ := hz
        cases n <;> simp_all
  rw [under_iff_infim_pair] at hxy ⊢
  rw [hxy] at hFxy
  exact hFxy.symm

noncomputable instance : Bot A where
  bot := ⊓ Set.univ

noncomputable instance : Top A where
  top := ⊔ Set.univ

lemma bot_under (x : A) : ⊥ ⊑ x := by
  apply infim_is_lower
  trivial

lemma top_above (x : A) : x ⊑ ⊤ := by
  apply supre_is_upper
  trivial

end continuous_functions
