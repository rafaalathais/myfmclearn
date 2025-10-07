section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro hp
  intro hnnp
  contradiction


theorem doubleneg_elim :
  ¬ ¬ P → P  := by
intro hnnp
by_cases hp: P
assumption
contradiction


theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor
  intro hnnp
  by_cases hp: P
  assumption
  contradiction
  intro qp
  intro qnnp
  contradiction


------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro h
  rcases h with (hp | hq)
  right
  assumption
  left
  assumption


theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro h
  rcases h with ⟨hp , hq⟩
  constructor
  assumption
  assumption


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro h
  intro hp
  rcases h with (hnp | hq)
  contradiction
  exact hq

theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro h
  intro hnp
  rcases h with (hp | hq)
  contradiction
  exact hq


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro h hnq hp
  have hq: Q := h hp
  contradiction

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro h
  intro hp
  by_cases hq: Q
  assumption
  have hnp: ¬ P := h hq
  contradiction


theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  intro hpq hnq hp
  have hq: Q := hpq hp
  contradiction
  intro hnpnq
  intro hp
  by_cases hq: Q
  assumption
  have hnp: ¬ P := hnpnq hq
  contradiction


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro h
  have hpnp: P ∨ ¬ P := by
    right
    intro hp
    apply h
    left
    assumption
  contradiction



------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro h hnp
  have hpq: P → Q := by
    intro hp
    contradiction
  have hp: P := h hpq
  contradiction


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases hqnq: Q
  left
  intro hp
  assumption
  right
  intro hq
  contradiction

------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro hpq hnpnq
  rcases hnpnq with ⟨hnp , hnq⟩
  rcases hpq with (hp | hq)
  contradiction
  contradiction

theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro hpq hnpnq
  rcases hpq with ⟨hp , hq⟩
  rcases hnpnq with (hnp | hnq)
  contradiction
  contradiction


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro hnpq
  constructor
  by_cases hpnp: P
  intro hp
  have hpq: P ∨ Q := by
    left
    assumption
  contradiction
  assumption
  by_cases hqnq: Q
  have hpq: P ∨ Q := by
    right
    assumption
  contradiction
  assumption


theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro hnpnq hpq
  rcases hnpnq
  rcases hpq
  contradiction
  contradiction

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro h
  by_cases hq: Q
  right
  intro hp
  have hpq: P ∧ Q := by
    constructor
    assumption
    assumption
  contradiction
  left
  assumption


theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro h hpq
  rcases hpq
  rcases h
  contradiction
  contradiction


theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  constructor
  intro hnpq
  by_cases hq: Q
  right
  intro hp
  have hpq: P ∧ Q := by
    constructor
    assumption
    assumption
  contradiction
  left
  assumption
  intro hnpnq hpq
  rcases hpq
  rcases hnpnq
  contradiction
  contradiction


theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor
  intro hnpq
  constructor
  by_cases hpnp: P
  intro hp
  have hpq: P ∨ Q := by
    left
    assumption
  contradiction
  assumption
  by_cases hqnq: Q
  have hpq: P ∨ Q := by
    right
    assumption
  contradiction
  assumption
  intro hnpnq hpq
  rcases hnpnq
  rcases hpq
  contradiction
  contradiction


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro h
  rcases h with ⟨hp , hqr⟩
  rcases hqr
  left
  constructor
  assumption
  assumption
  right
  constructor
  assumption
  assumption

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro h
  rcases h with (hpq|hpr)
  rcases hpq
  constructor
  assumption
  left
  assumption
  rcases hpr
  constructor
  assumption
  right
  assumption

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro h
  rcases h with (hp | hqr)
  constructor
  left
  assumption
  left
  assumption
  rcases hqr
  constructor
  right
  assumption
  right
  assumption

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  intro h
  rcases h with ⟨hpq , hpr⟩
  rcases hpq with (hp|hq)
  left
  assumption
  rcases hpr with (hp| hr)
  left
  assumption
  right
  constructor
  assumption
  assumption

------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro hpqr
  intro hp
  intro hq
  apply hpqr
  constructor
  assumption
  assumption


theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro hpqr hpq
  rcases hpq
  apply hpqr
  assumption
  assumption

------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro h
  exact h

------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro hp
  left
  assumption

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro hq
  right
  assumption

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro h
  rcases h
  assumption

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro h
  rcases h
  assumption

------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor
  intro hpp
  rcases hpp
  assumption
  assumption
  intro hp
  left
  assumption

theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor
  intro hpp
  rcases hpp
  assumption
  intro hp
  constructor
  assumption
  assumption

------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro h
  exfalso
  exact h

theorem true_top :
  P → True  := by
  intro h
  trivial


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
