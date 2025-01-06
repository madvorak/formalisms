import Mathlib.Tactic


/-- Function `f` is "injective". -/
def OneToOne {A B : Type} (f : A → B) : Prop := ∀ x y : A, x ≠ y → f x ≠ f y

theorem OneToOne.comp {A B C : Type} {f : A → B} {g : B → C}
  (hf : OneToOne f) (hg : OneToOne g) :
  OneToOne (g ∘ f) :=
by
  intro x y hxy
  show g (f x) ≠ g (f y)
  apply hg
  apply hf
  exact hxy

/-- Function `f` is "surjective". -/
def Onto {A B : Type} (f : A → B) : Prop := ∀ z : B, ∃ x : A, f x = z

theorem Onto.comp {A B C : Type} {f : A → B} {g : B → C}
  (hf : Onto f) (hg : Onto g) :
  Onto (g ∘ f) :=
by
  intro z
  obtain ⟨y, hyz⟩ := hg z
  obtain ⟨x, hxy⟩ := hf y
  use x
  rewrite [← hyz, ← hxy]
  rfl

/-- `A` and `B` have "the same size" iff there is `f : A → B` that is both "injective" and "surjective". -/
def Equipollent (A B : Type) : Prop := ∃ f : A → B, OneToOne f ∧ Onto f


/-- Inductive definition of the ancestor count when finite and acyclic:
    `Generation f g a n` means that the element `a : A` has exactly `n : ℕ` ancestors
    with respect to chaining `f : A → B` and `g : B → A` alternately
    (if `n` is not zero, then `g` was applied last). -/
inductive Generation : {A B : Type} → (A → B) → (B → A) → A → ℕ → Prop
| zer {A B : Type} {f : A → B} {g : B → A} {a : A} (orphan : ¬ ∃ b : B, g b = a) :
    Generation f g a 0
| nex {A B : Type} {f : A → B} {g : B → A} {a : A} (p : B) (parent : g p = a) {n : ℕ}
    (their : Generation g f p n) : Generation f g a n.succ

variable {A B : Type} -- Do not move any higher!

/-- Definition of both `Aₑ` and `Bₑ` (depending on arguments). -/
def EvenGeneration (f : A → B) (g : B → A) (a : A) : Prop :=
  ∃ n : ℕ, Generation f g a (2*n)

/-- Definition of both `Aₒ` and `Bₒ` (depending on arguments). -/
def OddGeneration (f : A → B) (g : B → A) (a : A) : Prop :=
  ∃ n : ℕ, Generation f g a (2*n + 1)

/-- Every element of `Aₒ` has a parent. -/
lemma OddGeneration.exists_parent {f : A → B} {g : B → A} {a : A}
  (oddGen : OddGeneration f g a) :
  ∃ p : B, g p = a ∧ EvenGeneration g f p :=
by
  have ⟨n, hn⟩ := oddGen
  cases hn with
  | nex p hp hpg =>
    use p
    constructor
    · exact hp
    · use n

/-- If `a` is in `Aₒ`, then `f a` is in `Bₑ`. -/
lemma OddGeneration.nextEvenGeneration {f : A → B} {g : B → A} {a : A}
  (oddGen : OddGeneration f g a) :
  EvenGeneration g f (f a) :=
by
  have ⟨n, hn⟩ := oddGen
  use n+1
  right
  · rfl
  exact hn

/-- If `a` is in `Aₑ`, then `f a` is in `Bₒ`. -/
lemma EvenGeneration.nextOddGeneration {f : A → B} {g : B → A} {a : A}
  (evenGen : EvenGeneration f g a) :
  OddGeneration g f (f a) :=
by
  have ⟨n, hn⟩ := evenGen
  use n
  right
  · rfl
  exact hn

/-- If `f a` is in `Bₑ`, then `a` is in `Aₒ`. -/
lemma EvenGeneration.prevOddGeneration {f : A → B} {g : B → A} {a : A}
  (evenGen : EvenGeneration g f (f a)) (hf : OneToOne f) :
  OddGeneration f g a :=
by
  have ⟨n, hn⟩ := evenGen
  cases n with
  | zero =>
    cases hn with
    | zer orph =>
      exfalso
      apply orph
      use a
  | succ k =>
    use k
    cases hn with
    | nex p hfpa hp =>
      have hpa : p = a
      · by_contra kdyby
        exact hf p a kdyby hfpa
      rw [hpa] at hp
      exact hp

/-- This function is called `g⁻¹` in the textbook. For simplicity, we define it only as
    a function `Aₒ → B` (which is sufficient for proving the Schröder-Bernstein theorem). -/
noncomputable def funOdd {f : A → B} {g : B → A} {a : A} (oddGen : OddGeneration f g a) : B :=
  oddGen.exists_parent.choose

/-- We have `g (g⁻¹ a) = a` for all `a` from `Aₒ`. -/
lemma OddGeneration.g_funOdd {f : A → B} {g : B → A} {a : A} (oddGen : OddGeneration f g a) :
  g (funOdd oddGen) = a :=
oddGen.exists_parent.choose_spec.left

/-- If `a` is from `Aₒ`, then we know that `g⁻¹ a` is from `Bₑ`. -/
lemma OddGeneration.evenGen_funOdd {f : A → B} {g : B → A} {a : A} (oddGen : OddGeneration f g a) :
  EvenGeneration g f (funOdd oddGen) :=
oddGen.exists_parent.choose_spec.right

/-- The function `g⁻¹` behaves on its domain like a one-to-one function. -/
lemma funOdd_likeOneToOne {f : A → B} {g : B → A} {x y : A} (hxy : x ≠ y)
  (hxₒ : OddGeneration f g x) (hyₒ : OddGeneration f g y) :
  funOdd hxₒ ≠ funOdd hyₒ :=
by
  sorry

/-- Finally, the Schröder-Bernstein theorem! -/
theorem equipollentSchroderBernstein :
  (∃ f : A → B, OneToOne f) ∧ (∃ g : B → A, OneToOne g) → Equipollent A B :=
by
  rintro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  classical
  let F : A → B := fun a => if haₒ : OddGeneration f g a then funOdd haₒ else f a
  use F
  constructor
  · intro x y hxy
    if hx : OddGeneration f g x
    then
      if hy : OddGeneration f g y
      then
        convert_to funOdd hx ≠ funOdd hy
        · exact dif_pos hx
        · exact dif_pos hy
        apply funOdd_likeOneToOne
        exact hxy
      else
        convert_to funOdd hx ≠ f y
        · exact dif_pos hx
        · exact dif_neg hy
        have yeseven : EvenGeneration g f (funOdd hx)
        · exact hx.evenGen_funOdd
        have noteven : ¬ EvenGeneration g f (f y)
        · intro ifeven
          apply hy
          apply ifeven.prevOddGeneration
          exact hf
        intro hhx
        rw [hhx] at yeseven
        exact noteven yeseven
    else
      if hy : OddGeneration f g y
      then
        convert_to f x ≠ funOdd hy
        · exact dif_neg hx
        · exact dif_pos hy
        have yeseven : EvenGeneration g f (funOdd hy)
        · exact hy.evenGen_funOdd
        have noteven : ¬ EvenGeneration g f (f x)
        · intro ifeven
          apply hx
          apply ifeven.prevOddGeneration
          exact hf
        intro hhy
        rw [hhy] at noteven
        exact noteven yeseven
      else
        convert_to f x ≠ f y
        · exact dif_neg hx
        · exact dif_neg hy
        apply hf
        exact hxy
  · intro z
    if hz : EvenGeneration g f z
    then
      use g z
      have hgz : OddGeneration f g (g z)
      · exact hz.nextOddGeneration
      convert_to funOdd hgz = z
      · exact dif_pos hgz
      by_contra contr
      exact hg (funOdd hgz) z contr hgz.g_funOdd
    else
      by_contra outer_contra
      apply hz
      use 0
      constructor
      intro inner_contra
      apply outer_contra
      obtain ⟨a, ha⟩ := inner_contra
      use a
      rw [←ha]
      have notodd : ¬ OddGeneration f g a
      · intro hlga
        apply hz
        rw [←ha]
        exact hlga.nextEvenGeneration
      exact dif_neg notodd
