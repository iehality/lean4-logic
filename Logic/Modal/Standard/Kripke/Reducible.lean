import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

open DeductionParameter Normal

namespace Kripke

open Formula

variable {α : Type*} {Ax₁ Ax₂ : AxiomSet α} (𝔽₁ 𝔽₂ : FrameClass)
  [sound₁ : Sound 𝝂Ax₁ 𝔽₁#] [sound₂ : Sound 𝝂Ax₂ 𝔽₂#]
  [complete₁ : Complete 𝝂Ax₁ 𝔽₁#] [complete₂ : Complete 𝝂Ax₂ 𝔽₂#]

lemma reducible_of_subset_FrameClass (h𝔽 : 𝔽₂ ⊆ 𝔽₁) : 𝝂Ax₁ ≤ₛ 𝝂Ax₂ := by
  apply System.reducible_iff.mpr;
  intro p hp;
  apply complete₂.complete;
  intro F hF;
  exact sound₁.sound hp $ h𝔽 hF;

/-
lemma strictreducible_of_ssubset_FrameClass (hne : Ax₂.Nonempty) (h𝔽 : 𝔽₂ ⊂ 𝔽₁) : Ax₁ᴺ <ₛ Ax₂ᴺ := by
  rw [Set.ssubset_def] at h𝔽;
  constructor;
  . apply reducible_of_subset_FrameClass sound₁ complete₂; exact h𝔽.1;
  . apply System.not_reducible_iff.mpr;
    obtain ⟨p, hp⟩ := hne;
    use p;
    constructor;
    . exact ⟨Deduction.maxm (by simp_all)⟩;
    . apply (not_imp_not.mpr $ sound₁.sound);
      simp [Kripke.ValidOnFrameClass];
      obtain ⟨F, hF₁, hF₂⟩ := by simpa [Set.not_subset] using h𝔽.2;
      use F;
      constructor;
      . exact hF₁;
      . sorry;
-/

lemma equiv_of_eq_FrameClass (h𝔽 : 𝔽₁ = 𝔽₂) : 𝝂Ax₁ =ₛ 𝝂Ax₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_subset_FrameClass 𝔽₁ 𝔽₂;
    subst_vars; rfl;
  . apply reducible_of_subset_FrameClass 𝔽₂ 𝔽₁;
    subst_vars; rfl;

end LO.Modal.Standard.Kripke
