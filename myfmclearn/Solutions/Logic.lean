section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro hP
  intro hnP
  apply hnP
  exact hP

theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro hnnP
  by_cases hP : P
  -- case P
  exact hP
  -- case ¬P
  exfalso
  exact hnnP hP

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor
  -- ⇒
  intro hnnP
  by_cases hP : P
  -- case P
  exact hP
  -- case ¬P
  exfalso
  exact hnnP hP
  -- ⇐
  intro hP
  intro hnP
  apply hnP
  exact hP



------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro hor
  rcases hor with (hP | hQ)
  right
  exact hP
  left
  exact hQ

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro hand
  rcases hand with ⟨hP, hQ⟩
  constructor
  exact hQ
  exact hP


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro hnPorQ
  intro hP
  rcases hnPorQ with (hnP | hQ)
  exfalso
  apply hnP hP
  exact hQ



theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro poq
  intro hnp
  rcases poq with (hp | hq)
  exfalso
  apply hnp hp
  exact hq


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro piq
  intro hnq
  intro hp
  have hq : Q := piq hp
  exact hnq hq

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro nqinp
  intro hp
  by_cases hq: Q
  exact hq
  exfalso
  have hnp : ¬P := nqinp hq
  exact hnp hp


theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  intro piq
  intro hnq
  intro hp
  have hq : Q := piq hp
  exact hnq hq
  intro nqinp
  intro hp
  by_cases hq: Q
  exact hq
  exfalso
  have hnp : ¬P := nqinp hq
  exact hnp hp


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro nponp
  apply nponp
  right
  intro hp
  apply nponp
  left
  exact hp


------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro piqip
  intro hnp
  apply hnp
  apply piqip
  intro hp
  contradiction

------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases hp : P
  right
  intro hq
  exact hp
  left
  intro hp2
  contradiction

------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro porq
  intro npandnq
  rcases npandnq with ⟨hnp, hnq⟩
  rcases porq with (hp | hq)
  apply hnp hp
  apply hnq hq

theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro pandq
  intro npornq
  rcases pandq with ⟨hp, hq⟩
  rcases npornq with (hnp | hnq)
  contradiction
  contradiction


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro nporq
  constructor
  intro hp
  apply nporq
  left
  exact hp
  intro hq
  apply nporq
  right
  exact hq

theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro npandnq
  intro nporq
  rcases npandnq with ⟨hnp, hnq⟩
  rcases nporq with (hp | hq)
  exact hnp hp
  exact hnq hq

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro nhporq
  by_cases hp : P
  left
  intro hq
  apply nhporq
  constructor
  exact hp
  exact hq
  right
  exact hp

theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro hnqornp
  intro hpandq
  rcases hpandq with ⟨hp, hq⟩
  rcases hnqornp with (hnq | hnp)
  contradiction
  contradiction

theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  constructor
  intro nhpandq
  by_cases hp : P
  left
  intro hq
  apply nhpandq
  constructor
  exact hp
  exact hq
  right
  exact hp
  intro nqandnp
  intro pandq
  rcases pandq with ⟨hp, hq⟩
  rcases nqandnp with (hnq | hnp)
  contradiction
  contradiction



theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor
  intro nhporq
  constructor
  intro hp
  apply nhporq
  left
  exact hp
  intro hq
  apply nhporq
  right
  exact hq
  intro hnpandnq
  intro hporq
  rcases hnpandnq with ⟨hnp, hnq⟩
  rcases hporq with (hp | hq)
  contradiction
  contradiction


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro pandqorr
  rcases pandqorr with ⟨hp, qorr⟩
  rcases qorr with (hq | hr)
  left
  constructor
  exact hp
  exact hq
  right
  constructor
  exact hp
  exact hr

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro pandqorpandr
  constructor
  rcases pandqorpandr with (pandq | pandr)
  rcases pandq with ⟨hp, hq⟩
  exact hp
  rcases pandr with ⟨hp, hr⟩
  exact hp
  rcases pandqorpandr with (pandq | pandr)
  rcases pandq with ⟨hp, hq⟩
  left
  exact hq
  rcases pandr with ⟨hp, hr⟩
  right
  exact hr

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro porqandr
  constructor
  rcases porqandr with (hp | qandr)
  left
  exact hp
  rcases qandr with ⟨hq, hr⟩
  right
  exact hq
  rcases porqandr with (hp | qandr)
  left
  exact hp
  rcases qandr with ⟨hq, hr⟩
  right
  exact hr

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  intro porqandporr
  rcases porqandporr with ⟨porq, porr⟩
  rcases porq with (hp | hq)
  left
  exact hp
  rcases porr with (hp | hr)
  left
  exact hp
  right
  constructor
  exact hq
  exact hr

------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro pandqir
  intro hp
  intro hq
  have hpandhq : P ∧ Q := And.intro hp hq
  exact pandqir hpandhq

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro piqir
  intro pandq
  rcases pandq with ⟨hp, hq⟩
  have qir : Q → R := piqir hp
  apply qir hq

------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro hp
  exact hp


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro hp
  left
  exact hp

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro hq
  right
  exact hq

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro pandq
  rcases pandq with ⟨hp, hq⟩
  exact hp

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro pandq
  rcases pandq with ⟨hp, hq⟩
  exact hq

------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor
  intro porp
  rcases porp with (hp | hp)
  exact hp
  exact hp
  intro hp
  left
  exact hp

theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor
  intro pandp
  rcases pandp with ⟨hp1, hp2⟩
  exact hp1
  intro hp
  constructor
  exact hp
  exact hp

------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  exact False.elim

theorem true_top :
  P → True  := by
  intro hp
  exact True.intro

end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Type)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
