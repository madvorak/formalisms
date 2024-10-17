import Mathlib.Tactic


section relations

class Relation (A : Type) where
  rel : A → A → Prop

infix:51 " ⊑ " => Relation.rel

def Reflexiv (A : Type) [Relation A] : Prop := ∀ x : A, x ⊑ x

def Antisym (A : Type) [Relation A] : Prop := ∀ x y : A, x ⊑ y ∧ y ⊑ x → x = y

def Transitiv (A : Type) [Relation A] : Prop := ∀ x y z : A, x ⊑ y ∧ y ⊑ z → x ⊑ z

class Poset (A : Type) extends Relation A where
  refle : Reflexiv A
  antis : Antisym A
  trans : Transitiv A

theorem triangleless {A : Type} [Poset A] (a b c : A) :
  (a ⊑ b ∧ b ⊑ c ∧ c ⊑ a) → a = b :=
by
  intro ⟨hab, hbc, hca⟩
  /-
  have hba : b ⊑ a
  · apply Poset.trans
    constructor
    · exact hbc
    · exact hca
  apply Poset.antis
  constructor
  · exact hab
  · exact hba
  -/
  apply Poset.antis
  constructor
  · exact hab
  · apply Poset.trans
    constructor
    · exact hbc
    · exact hca

end relations


variable {A : Type}

section bounds

variable [Poset A]

/-- mnemonics: `a b x y z` -/

def Set.LowerBound (S : Set A) (a : A) : Prop :=
  ∀ x ∈ S, a ⊑ x

def Set.UpperBound (S : Set A) (z : A) : Prop :=
  ∀ x ∈ S, x ⊑ z

def Set.LeastUpperBound (S : Set A) (y : A) : Prop :=
  S.UpperBound y ∧ ∀ z : A, S.UpperBound z → y ⊑ z

def Set.GreatLowerBound (S : Set A) (b : A) : Prop :=
  S.LowerBound b ∧ ∀ a : A, S.LowerBound a → a ⊑ b

lemma glb_is_unique {S : Set A} {x₁ x₂ : A}
  (hx₁ : S.GreatLowerBound x₁) (hx₂ : S.GreatLowerBound x₂) :
  x₁ = x₂ :=
by
  apply Poset.antis
  constructor
  · apply hx₂.right
    exact hx₁.left
  · apply hx₁.right
    exact hx₂.left

lemma lub_is_unique {S : Set A} {x₁ x₂ : A}
  (hx₁ : S.LeastUpperBound x₁) (hx₂ : S.LeastUpperBound x₂) :
  x₁ = x₂ :=
by
  apply Poset.antis
  constructor
  · apply hx₁.right
    exact hx₂.left
  · apply hx₂.right
    exact hx₁.left

class CompleteLattic (A : Type) extends Poset A where
  hasInfim : ∀ S : Set A, ∃ b : A, S.GreatLowerBound b
  hasSupre : ∀ S : Set A, ∃ y : A, S.LeastUpperBound y

end bounds


section extrema

variable [CompleteLattic A]

noncomputable def infim (S : Set A) : A :=
  (CompleteLattic.hasInfim S).choose

noncomputable def supre (S : Set A) : A :=
  (CompleteLattic.hasSupre S).choose

prefix:999 "⊓ " => infim
prefix:999 "⊔ " => supre

lemma infim_is_lower (S : Set A) : S.LowerBound (⊓S) :=
  (CompleteLattic.hasInfim S).choose_spec.left

lemma supre_is_upper (S : Set A) : S.UpperBound (⊔S) :=
  (CompleteLattic.hasSupre S).choose_spec.left

lemma infim_is_great (S : Set A) (a : A) (ha : S.LowerBound a) : a ⊑ ⊓S :=
  (CompleteLattic.hasInfim S).choose_spec.right a ha

lemma supre_is_least (S : Set A) (z : A) (hz : S.UpperBound z) : ⊔S ⊑ z :=
  (CompleteLattic.hasSupre S).choose_spec.right z hz

lemma glb_is_supre {S : Set A} {x : A} (hx : S.GreatLowerBound x) :
  x = ⊓S :=
by
  apply glb_is_unique
  · exact hx
  · constructor
    · exact infim_is_lower S
    · exact infim_is_great S

lemma lub_is_infim {S : Set A} {x : A} (hx : S.LeastUpperBound x) :
  x = ⊔S :=
by
  apply lub_is_unique
  · exact hx
  · constructor
    · exact supre_is_upper S
    · exact supre_is_least S

end extrema


section fixpoints

def Fixpoint (F : A → A) (x : A) : Prop :=
  F x = x

def Prefixpoint [Relation A] (F : A → A) (x : A) : Prop :=
  x ⊑ F x

def Posfixpoint [Relation A] (F : A → A) (x : A) : Prop :=
  F x ⊑ x

lemma prefixpoint_of_fixpoint [Poset A] {F : A → A} {x : A} (hx : Fixpoint F x) :
  Prefixpoint F x :=
by
  unfold Prefixpoint
  rw [hx]
  apply Poset.refle

lemma posfixpoint_of_fixpoint [Poset A] {F : A → A} {x : A} (hx : Fixpoint F x) :
  Posfixpoint F x :=
by
  unfold Posfixpoint
  rw [hx]
  apply Poset.refle

lemma fixpoint_of_pre_pos [Poset A] {F : A → A} {x : A} :
  Posfixpoint F x ∧ Prefixpoint F x → Fixpoint F x :=
by
  apply Poset.antis

def GreatFixpoint [Poset A] (F : A → A) : Set A :=
  Fixpoint F ∩ (setOf (Fixpoint F)).UpperBound

def LeastFixpoint [Poset A] (F : A → A) : Set A :=
  Fixpoint F ∩ (setOf (Fixpoint F)).LowerBound

end fixpoints
