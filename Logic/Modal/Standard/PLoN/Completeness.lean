import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.PLoN.Soundness

namespace LO.Modal.Standard

namespace PLoN

variable {α : Type*} [DecidableEq α]

open Formula
open Theory
open MaximalConsistentTheory

abbrev CanonicalFrame (Λ : DeductionParameter α) [Inhabited (Λ)-MCT] : PLoN.Frame (Λ)-MCT α where
  Rel :=  λ p Ω₁ Ω₂ => ~(□p) ∈ Ω₁.theory ∧ ~p ∈ Ω₂.theory

abbrev CanonicalModel (Λ : DeductionParameter α) [Inhabited (Λ)-MCT] : PLoN.Model (Λ)-MCT α where
  Frame := CanonicalFrame Λ
  Valuation Ω a := (atom a) ∈ Ω.theory

variable {Λ : DeductionParameter α} [Inhabited (Λ)-MCT] [Λ.HasNec]
         {p : Formula α}

lemma truthlemma : ∀ {Ω : (CanonicalModel Λ).World}, Ω ⊧ p ↔ (p ∈ Ω.theory) := by
  induction p using Formula.rec' with
  | hbox p ih =>
    intro Ω;
    constructor;
    . intro h;
      by_contra hC;
      suffices ¬Ω ⊧ □p by contradiction; done;
      simp [plon_satisfies];
      constructor;
      . assumption;
      . obtain ⟨Ω', hΩ'⟩ := lindenbaum (𝓓 := Λ) (T := {~p}) (not_singleton_consistent Ω.consistent (iff_mem_neg.mpr hC));
        use Ω';
        constructor;
        . apply iff_mem_neg.mp;
          simp_all;
        . apply ih.not.mpr;
          apply iff_mem_neg.mp;
          simp_all;
    . intro h;
      by_contra hC;
      simp [plon_satisfies] at hC;
      simp_all only [plon_satisfies.iff_models];
  | _ => simp_all [plon_satisfies];

lemma complete_of_mem_canonicalFrame {𝔽 : FrameClass α} (hFC : ⟨(Λ)-MCT, CanonicalFrame Λ⟩ ∈ 𝔽) : 𝔽 ⊧ p → Λ ⊢! p:= by
  simp [valid_on_PLoNFrameClass, valid_on_PLoNFrame, valid_on_PLoNModel];
  contrapose; push_neg;
  intro h;
  use (Λ)-MCT, (CanonicalFrame Λ);
  constructor;
  . exact hFC;
  . use (CanonicalModel Λ).Valuation;
    obtain ⟨Ω, hΩ⟩ := lindenbaum (𝓓 := Λ) (T := {~p}) (by
      apply unprovable_iff_singleton_neg_Consistent.mp;
      exact h;
    );
    use Ω;
    apply truthlemma.not.mpr;
    apply iff_mem_neg.mp;
    simp_all;

lemma instComplete_of_mem_canonicalFrame {𝔽 : FrameClass α} (hFC : ⟨(Λ)-MCT, CanonicalFrame Λ⟩ ∈ 𝔽) : Complete Λ 𝔽 := ⟨complete_of_mem_canonicalFrame hFC⟩

instance : Complete 𝐍 (AllFrameClass α) := instComplete_of_mem_canonicalFrame trivial

end PLoN

end LO.Modal.Standard