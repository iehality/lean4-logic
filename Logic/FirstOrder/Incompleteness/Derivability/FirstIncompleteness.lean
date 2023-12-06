import Logic.Logic.HilbertStyle
import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Incompleteness.Derivability.Conditions

open LO.System LO.System.Intuitionistic

namespace LO.FirstOrder.Arith.Incompleteness

open FirstOrder.Theory HasProvablePred

variable (T₀ T : Theory ℒₒᵣ) [Subtheory T₀ T]
variable [Diagonizable T₀ Π 1]
variable
  [hPred : HasProvablePred T]
  [hPredDef : HasProvablePred.Definable.Sigma T 1]
  [hD1 : Derivability1 T₀ T]

variable (hG : IsGoedelSentence T₀ T G)

open HasProvablePred.Derivability1

lemma GoedelSentenceUnprovablility [hConsis : Theory.Consistent T] : T ⊬! G := by
  by_contra hP; simp at hP;
  have h₁ : T ⊢! (Pr[T] ⸢G⸣) := hD1.D1' hP;
  have h₂ : T ⊢! (Pr[T] ⸢G⸣) ⟶ ~G := by simpa using weakening $ iff_mpr $ iff_contra hG;
  have hR : T ⊢! ~G := weakening (h₂ ⨀ h₁);
  exact hConsis.consistent.false (no_contradiction hP hR).some;

lemma GoedelSentenceUnrefutability [hSound : SigmaOneSound T] : T ⊬! ~G := by
  by_contra hR; simp at hR;
  have h₁ : T ⊢! ~G ⟶ Pr[T] ⸢G⸣ := by simpa [Subformula.neg_neg'] using weakening $ iff_mp $ iff_contra hG;
  have h₂ : T ⊢! Pr[T] ⸢G⸣ := h₁ ⨀ hR; simp at h₂;
  have h₃ : ℕ ⊧ (Pr[T] ⸢G⸣) := hSound.sound (Hierarchy.rew _ hPredDef.definable) h₂;
  have hP : T ⊢! G := hPred.spec.mp h₃;
  exact (Consistent_of_SigmaOneSound T).consistent.false (no_contradiction hP hR).some;

theorem FirstIncompleteness [hSound : SigmaOneSound T] : Theory.Incomplete T := by
  have ⟨G, ⟨hG, _⟩⟩ := @existsGoedelSentence T₀ T _ _ 1 _ _;
  have := Consistent_of_SigmaOneSound T;
  by_contra hCC; simp at hCC;
  cases (hCC.some.complete G) with
  | inl h => simpa using (GoedelSentenceUnprovablility T₀ T hG);
  | inr h => simpa using (GoedelSentenceUnrefutability T₀ T hG);

end LO.FirstOrder.Arith.Incompleteness
