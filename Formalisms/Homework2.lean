import Mathlib.Tactic


class Relation (A : Type) where
  rel : A → A → Prop

infix:51 " ⊑ " => Relation.rel


def Reflexiv (A : Type) [Relation A] : Prop := ∀ x : A, x ⊑ x

def Antisym (A : Type) [Relation A] : Prop := ∀ x y : A, x ⊑ y → y ⊑ x → x = y

def Transitiv (A : Type) [Relation A] : Prop := ∀ x y z : A, x ⊑ y → y ⊑ z → x ⊑ z

class Poset (A : Type) extends Relation A where
  refle : Reflexiv A
  antis : Antisym A
  trans : Transitiv A


section posets

variable {A : Type} [Poset A]

theorem triangleless (a b c : A) :
  (a ⊑ b ∧ b ⊑ c ∧ c ⊑ a) → a = b :=
by
  sorry


def Set.LowerBound (S : Set A) (a : A) : Prop :=
  ∀ x ∈ S, a ⊑ x

def Set.UpperBound (S : Set A) (z : A) : Prop :=
  ∀ x ∈ S, x ⊑ z

def Set.LeastUpperBound (S : Set A) (y : A) : Prop :=
  S.UpperBound y ∧ ∀ z : A, S.UpperBound z → y ⊑ z

def Set.GreatLowerBound (S : Set A) (b : A) : Prop :=
  S.LowerBound b ∧ ∀ a : A, S.LowerBound a → a ⊑ b

class CompleteLattic (A : Type) extends Poset A where
  hasInfim : ∀ S : Set A, ∃ b : A, S.GreatLowerBound b
  hasSupre : ∀ S : Set A, ∃ y : A, S.LeastUpperBound y

end posets


section lattices

variable {A : Type} [CompleteLattic A]

noncomputable def infim (S : Set A) : A :=
  (CompleteLattic.hasInfim S).choose

noncomputable def supre (S : Set A) : A :=
  (CompleteLattic.hasSupre S).choose

prefix:70 " ⊓ " => infim
prefix:70 " ⊔ " => supre

lemma infim_is_LowerBound (S : Set A) : S.LowerBound (⊓S) :=
  (CompleteLattic.hasInfim S).choose_spec.left

lemma supre_is_UpperBound (S : Set A) : S.UpperBound (⊔S) :=
  (CompleteLattic.hasSupre S).choose_spec.left

lemma infim_is_Great (S : Set A) (a : A) (ha : S.LowerBound a) : a ⊑ ⊓S :=
  (CompleteLattic.hasInfim S).choose_spec.right a ha

lemma supre_is_Least (S : Set A) (z : A) (hz : S.UpperBound z) : ⊔S ⊑ z :=
  (CompleteLattic.hasSupre S).choose_spec.right z hz

end lattices


section fixpoints

def Monoton {A : Type} [Relation A] (F : A → A) : Prop :=
  ∀ x y : A, x ⊑ y → F x ⊑ F y

def UniqueMember {A : Type} (S : Set A) (a : A) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, b = a

def Fixpoint {A : Type} (F : A → A) (x : A) : Prop :=
  F x = x

def Prefixpoint {A : Type} [Relation A] (F : A → A) (x : A) : Prop :=
  x ⊑ F x

def Posfixpoint {A : Type} [Relation A] (F : A → A) (x : A) : Prop :=
  F x ⊑ x

lemma prefixpoint_of_fixpoint {A : Type} (P : Poset A) {F : A → A} {x : A} (fpx : Fixpoint F x) :
  Prefixpoint F x :=
by
  unfold Prefixpoint
  unfold Fixpoint at fpx
  rw [fpx]
  apply P.refle

lemma posfixpoint_of_fixpoint {A : Type} (P : Poset A) {F : A → A} {x : A} (fpx : Fixpoint F x) :
  Posfixpoint F x :=
by
  unfold Posfixpoint
  unfold Fixpoint at fpx
  rw [fpx]
  apply P.refle _

lemma fixpoint_of_pre_pos {A : Type} (P : Poset A) {F : A → A} {x : A} :
  Posfixpoint F x → Prefixpoint F x → Fixpoint F x :=
P.antis (F x) x

def GreatFixpoint {A : Type} [Poset A] (F : A → A) : Set A :=
  Fixpoint F ∩ (Set.UpperBound (Fixpoint F))

def LeastFixpoint {A : Type} [Poset A] (F : A → A) : Set A :=
  Fixpoint F ∩ (Set.LowerBound (Fixpoint F))

theorem fixpointKnasterTarski {A : Type} {P : Poset A} {F : A → A}
  [CompleteLattic A] (hF : Monoton F) :
  -- the least upper bound of all prefixpoints (ŷ) is the (unique) great fixpoint
  UniqueMember (GreatFixpoint F) (⊔ Prefixpoint F) ∧
  -- the great lower bound of all posfixpoints (ẑ) is the (unique) least fixpoint
  UniqueMember (LeastFixpoint F) (⊓ Posfixpoint F) :=
by
  sorry -- homework #2

end fixpoints
