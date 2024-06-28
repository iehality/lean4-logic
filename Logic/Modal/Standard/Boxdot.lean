import Logic.Modal.Standard.Deduction2
import Logic.Modal.Standard.HilbertStyle

namespace LO.Modal.Standard

open DeductionSystem

variable [DecidableEq α]

def Formula.BoxdotTranslation : Formula α → Formula α
  | atom p => .atom p
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⟶ q => (BoxdotTranslation p) ⟶ (BoxdotTranslation q)
  | p ⋏ q => (BoxdotTranslation p) ⋏ (BoxdotTranslation q)
  | p ⋎ q => (BoxdotTranslation p) ⋎ (BoxdotTranslation q)
  | box p => ⊡(BoxdotTranslation p)
postfix:75 "ᵇ" => Formula.BoxdotTranslation

open System
open Formula
open StandardModalLogicalConnective (boxdot)

variable {p : Formula α}


lemma boxdotTranslatedK4_of_S4 (h : 𝐒𝟒 ⊢! p) : 𝐊𝟒 ⊢! pᵇ := by
  have : System.S4 (𝐒𝟒 : Rules (Formula α)) := inferInstance
  induction h using Deduction.inducition! with
  | rule r hr hant ih =>
    rcases hr with ((((hPL | hK) | hNec) | hT) | h4);
    . sorry;
    . obtain ⟨_, ⟨p, q, _⟩, _⟩ := hK; subst_vars;
      simp only [DeductionSystem.Axioms.K, Formula.BoxdotTranslation, boxdot_axiomK!];
    . obtain ⟨q, ⟨_, _, _⟩, _⟩ := hNec;
      simp only [BoxdotTranslation];
      apply boxdot_nec!;
      exact ih (by simp);
    . obtain ⟨_, ⟨p, _, _⟩, _⟩ := hT; subst_vars;
      simp only [DeductionSystem.Axioms.T, Formula.BoxdotTranslation, boxdot_axiomT!];
    . obtain ⟨_, ⟨p, _, _⟩, _⟩ := h4;
      subst_vars;
      sorry; -- simp only [DeductionSystem.Axioms.Four, Formula.BoxdotTranslation, boxdot_axiomFour!];


lemma iff_boxdotTranslation_S4 : 𝐒𝟒 ⊢! p ⟷ pᵇ := by
  induction p using Formula.rec' with
  | hand p q ihp ihq => dsimp [BoxdotTranslation]; exact and_replace_iff! ihp ihq;
  | hor p q ihp ihq => dsimp [BoxdotTranslation]; exact or_replace_iff! ihp ihq;
  | himp p q ihp ihq => dsimp [BoxdotTranslation]; exact imp_replace_iff! ihp ihq;
  | hbox p ihp =>
    dsimp [BoxdotTranslation];
    exact iff_trans''! (box_iff! ihp) iff_box_boxdot!;
  | _ => dsimp [BoxdotTranslation]; exact iff_id!;

lemma S4_of_boxdotTranslatedK4 (h : 𝐊𝟒 ⊢! pᵇ) : 𝐒𝟒 ⊢! p := by
  exact (and₂'! iff_boxdotTranslation_S4) ⨀ (reducible_iff.mp $ reducible_K4_S4) h

theorem iff_S4_boxdotTranslatedK4 : 𝐒𝟒 ⊢! p ↔ 𝐊𝟒 ⊢! pᵇ := by
  constructor;
  . apply boxdotTranslatedK4_of_S4;
  . apply S4_of_boxdotTranslatedK4;

end LO.Modal.Standard
