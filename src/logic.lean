
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hd,
  intro hd,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro d1,
  by_contradiction hboom,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P,
  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h1,
  cases h1 with hp hq,
  
  right,
  exact hp,

  left,
  exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro d1,
  cases d1 with dp dq,
  split,
  exact dq,
  exact dp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro d1,
  cases d1 with dnp dq,
  
  intro d2,
  
  contradiction,
  intro d2,
  exact dq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro d1,
  cases d1 with dp dq,
  intro d2,
  contradiction,
  intro d2,
  exact dq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro d1,
  intro d2,
  intro d3,
  have dq : Q := d1 d3,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro left,
  intro p,
  by_contradiction hboom,
  have np : ¬P := left hboom,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  
  intro left,
  intro nq,
  intro np,
  have q : Q := left np,
  contradiction, 

  intro left,
  intro p,
  by_contradiction hboom,
  have np : ¬P := left hboom,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro hl,
  have g: (P∨¬P),
  right,
  intro p,
  have ll: (P∨¬P),
  left,
  exact p,
  contradiction,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro hl,
  intro np,
  have g: (P → Q),
  intro p,
  contradiction,
  have p : P := hl g,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro hl,
  intro npenq,
  cases npenq with np nq,
  cases hl with p q,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro peq,
  intro npounq,
  cases peq with p q,
  cases npounq with np nq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npouq,
  split,
  intro p,
  have pouq: (P∨Q),
  left,
  exact p,
  contradiction,
  intro q,
  have pouq: (P∨Q),
  right,
  exact q,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro npenq,
  intro peq,
  cases npenq with np nq,
  cases peq with p q,
  contradiction,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro npeq,
  by_cases vq: Q, --- lem sobre Q
  right,
  intro p,
  have peq: (P∧Q),
  split,
  exact p,
  exact vq,
  contradiction,
  left,
  exact vq,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nqounp,
  intro peq,
  cases nqounp with nq np,
  cases peq with p q,
  contradiction,
  cases peq with p q,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  exact demorgan_conj P Q,
  exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro peqour,
  cases peqour with p qour,
  cases qour with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact r, 
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro hl,
  cases hl with peq per,
  cases peq with p q,
  split,
  exact p,
  left,
  exact q,
  cases per with p r,
  split,
  exact p,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro hl,
  cases hl with p qer,
  split,
  left,
  exact p,
  left,
  exact p,
  cases qer with q r,
  split,
  right,
  exact q,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro hl,
  cases hl with pouq pour,
  cases pouq with p q,
  left,
  exact p,
  cases pour with p r,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro hl,
  intro p,
  intro q,
  have peq: (P∧Q),
  split,
  exact p,
  exact q,
  have r: R := hl peq,
  exact r,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro left,
  intro peq,
  cases peq with p q,
  have qtor: Q→R := left p,
  have r: R := qtor q,
  exact r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left, 
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro peq,
  cases peq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro peq,
  cases peq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pep,
  cases pep with pl pr,
  exact pl,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro poup,
  cases poup with pl pr,
  exact pl,
  exact pr,
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro hl,
  intro x,
  intro pdex,
  apply hl,
  existsi x,
  exact pdex,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro hl,
  intro d2,
  cases d2 with x pdex,
  exact hl x pdex,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro hl,
  by_contradiction hc,
  apply hl,
  intro u,
  by_contradiction hc',
  apply hc,
  existsi u,
  exact hc',
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro hl,
  intro hp,
  cases hl with h ha,
  have pdeh : P h := hp h, --- proposicao universal 
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  apply demorgan_forall,
  apply demorgan_forall_converse,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  apply demorgan_exists,
  apply demorgan_exists_converse,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro hl,
  intro hq,
  cases hl with h ha,
  have npdeh : ¬P h := hq h,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro hl,
  intro he,
  cases he with a ha,
  have pdex : P a := hl a,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro hl,
  intro e,
  by_contradiction,
  apply hl,
  existsi e,
  exact h,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro hl,
  by_contradiction he,
  apply hl,
  intro a,
  intro ha,
  apply he,
  existsi a,
  exact ha,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  apply forall_as_neg_exists,
  apply forall_as_neg_exists_converse,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  apply exists_as_neg_forall,
  apply exists_as_neg_forall_converse,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro hl,
  split,
  cases hl with u hu,
  cases hu with hup huq,
  existsi u,
  exact hup,
  cases hl with u hu,
  cases hu with hup huq,
  existsi u,
  exact huq,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro hl,
  cases hl with u hu,
  cases hu,
  left,
  existsi u,
  exact hu,
  right,
  existsi u,
  exact hu,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro hl,
  cases hl,
  cases hl with u hu,
  existsi u,
  left,
  exact hu,
  cases hl with u hu,
  existsi u,
  right,
  exact hu,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro hl,
  split,
  intro u,
  have pxeqx : P u ∧ Q u := hl u,
  cases pxeqx with pu qu,
  exact pu,
  intro u,
  have pxeqx : P u ∧ Q u := hl u,
  cases pxeqx with pu qu,
  exact qu,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro hl,
  intro u,
  split,
  cases hl,
  have pu : P u := hl_left u,
  exact pu,
  cases hl,
  have qu : Q u := hl_right u,
  exact qu,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro hl,
  intro u,
  cases hl,
  have pu : P u := hl u,
  left,
  exact pu,
  have qu : Q u := hl u,
  right,
  exact qu,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
