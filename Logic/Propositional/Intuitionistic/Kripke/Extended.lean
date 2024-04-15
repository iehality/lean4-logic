import Logic.Vorspiel.BinaryRelations
import Logic.Propositional.Intuitionistic.Kripke.Semantics

namespace LO.Propositional.Intuitionistic

variable {α β}

@[simp]
def Formula.ExtendedKripkeSatisfies (P : Kripke.Frame α → Prop) (M : Kripke.Model α β) (w : α) (p : Formula β) : Prop := (P M.frame) → (p.KripkeSatisfies M w)
notation w " ⊩ⁱ[" P "," M "] " p => Formula.ExtendedKripkeSatisfies P M w p

@[simp] lemma Formula.ExtendedKripkeSatisfies.iff_int {p : Formula β} : (w ⊩ⁱ[λ _ => True, M] p) ↔ (w ⊩ⁱ[M] p) := by simp;


@[simp]
def Theory.ExtendedKripkeSatisfies (P : Kripke.Frame α → Prop) (M : Kripke.Model α β) (w : α) (Γ : Theory β) := ∀ p ∈ Γ, (w ⊩ⁱ[P, M] p)
notation w " ⊩ⁱ[" P "," M "] " Γ => Theory.ExtendedKripkeSatisfies P M w Γ

lemma Theory.ExtendedKripkeSatisfies.iff_int {Γ : Theory β} : (w ⊩ⁱ[λ _ => True, M] Γ) ↔ (w ⊩ⁱ[M] Γ) := by simp; rfl;


@[simp]
def Formula.ExtendedKripkeModels (P : Kripke.Frame α → Prop) (M : Kripke.Model α β) (p : Formula β) : Prop := ∀ w, (w ⊩ⁱ[P, M] p)
notation M " ⊧[" P "] " p => Formula.ExtendedKripkeModels P M p

@[simp] lemma Formula.ExtendedKripkeModels.iff_int {p : Formula β} : (M ⊧[λ _ => True] p) ↔ (M ⊧ⁱ p) := by simp; rfl;


@[simp]
def Formula.ExtendedKripkeValid (P : ∀ {α : Type}, Kripke.Frame α → Prop) (p : Formula β) : Prop := ∀ {α}, ∀ (M : Kripke.Model α β), (M ⊧[P] p)
notation "⊧[" P "] " p => Formula.ExtendedKripkeValid P p

@[simp] lemma Formula.ExtendedKripkeValid.iff_int {p : Formula β} : (⊧[λ _ => True] p) ↔ (⊧ⁱ p) := by simp; rfl;


@[simp]
def Formula.ExtendedKripkeConsequence (P : ∀ {α : Type}, Kripke.Frame α → Prop) (Γ : Theory β) (p : Formula β) : Prop := ∀ {α : Type}, ∀ (M : Kripke.Model α β) w, (w ⊩ⁱ[(@P α), M] Γ) → (w ⊩ⁱ[(@P α), M] p)
notation:50 Γ " ⊨ⁱ[" P "] " p => Formula.ExtendedKripkeConsequence P Γ p

@[simp] lemma Formula.ExtendedKripkeConsequence.iff_int : (Formula.ExtendedKripkeConsequence (λ _ => True) Γ p) ↔ (Formula.KripkeConsequence Γ p) := by simp; rfl;


section LEM

def _root_.Full (rel : α → α → Prop) := ∀ ⦃x y : α⦄, rel x y ↔ x = y

lemma _root_.full_of_refl_antisymm_eucl {rel : α → α → Prop} (hRefl : Reflexive rel) (hAntisymm : AntiSymmetric rel) (hEucl : Euclidean rel) : Full rel := by
  intro x y;
  constructor;
  . intro hxy;
    have hxx := hRefl x;
    have hyx := hEucl hxy hxx;
    exact hAntisymm hxy hyx;
  . intro exy; simp_all; apply hRefl;

example : ⊧[Full] (p ⋎ ~p) := by
  intro _ M w hf;
  by_cases h : w ⊩ⁱ[M] p;
  case pos => left; assumption;
  case neg =>
    right;
    simp [NegDefinition.neg];
    intro w' hw';
    have := hf.mp hw';
    simp_all;

end LEM

end LO.Propositional.Intuitionistic
