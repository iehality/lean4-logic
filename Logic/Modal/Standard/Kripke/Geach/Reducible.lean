import Logic.Modal.Standard.Kripke.Reducible
import Logic.Modal.Standard.Kripke.Geach.Definability
import Logic.Modal.Standard.Kripke.Geach.Completeness

namespace LO.Modal.Standard

open System (not_reducible_iff)
open Formula
open Kripke
open AxiomSet

variable {α : Type u} [DecidableEq α] [Inhabited α]

section

variable {L₁ L₂ : DeductionParameter α} [geach₁ : L₁.IsGeach] [geach₂ : L₂.IsGeach]

lemma reducible_of_geach_defnability
  (hs : ∀ {F : Frame.{u}}, MultiGeachConfluent geach₂.taples F → MultiGeachConfluent geach₁.taples F)
  : (L₁ ≤ₛ L₂) := reducible_of_definability (α := α) (definability₁ := instGeachDefinability) (definability₂ := instGeachDefinability) hs


lemma equiv_of_geach_defnability
  (hs : ∀ {F : Frame.{u}}, MultiGeachConfluent geach₁.taples F ↔ MultiGeachConfluent geach₂.taples F)
  : (L₁ =ₛ L₂) := equiv_of_iff_definability (definability₁ := instGeachDefinability) (definability₂ := instGeachDefinability) hs

end

theorem reducible_KD_KT : (𝐊𝐃 : DeductionParameter α) ≤ₛ 𝐊𝐓 := by apply reducible_of_geach_defnability; simp_all [serial_of_refl];

variable {W : Type u} [Inhabited W]

lemma unprovable_of_exists_frame {𝓓 : DeductionParameter α} [𝓓.HasNecOnly] {p : Formula α} (h : ∃ (F : Frame' α), F ∈ 𝔽(Ax(𝓓)) ∧ ¬F ⊧ p) : 𝓓 ⊬! p := by
  apply not_imp_not.mpr $ sound!_on_frameclass;
  simpa;


theorem strict_reducible_KD_KT [atleast : AtLeast 2 W] : (𝐊𝐃 : DeductionParameter α) <ₛ 𝐊𝐓 := by
  constructor;
  . apply reducible_KD_KT;
  . apply not_reducible_iff.mpr;
    obtain ⟨f, finv, fInj⟩ := atleast.mapping;
    use (□(atom default) ⟶ (atom default));
    constructor;
    . exact ⟨Deduction.maxm (by simp)⟩
    . apply unprovable_of_exists_frame;
      use { World := W, Rel := λ _ y => y = f 1 };
      constructor;
      . apply iff_definability_memAxiomSetFrameClass (by simpa using instGeachDefinability (L := 𝐊𝐃)) |>.mpr;
        simp [Serial];
      . simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel, Formula.Kripke.Satisfies];
        use λ w _ => w = f 1;
        constructor;
        . rfl;
        . use (f 0);
          exact fInj.injective.ne (by simp)

theorem  strict_reducible_K4_S4 [atleast : AtLeast 2 W] : (𝐊𝟒 : DeductionParameter α) <ₛ 𝐒𝟒 := by
  constructor;
  . apply reducible_K4_S4;
  . apply not_reducible_iff.mpr;
    obtain ⟨f, finv, fInj⟩ := atleast.mapping;
    use (□(atom default) ⟶ (atom default));
    constructor;
    . simp;
    . apply unprovable_of_exists_frame;
      use { World := W, Rel := λ _ y => y = f 1 };
      constructor;
      . apply iff_definability_memAxiomSetFrameClass (by simpa using instGeachDefinability (L := 𝐊𝟒)) |>.mpr;
        simp [Transitive];
      . simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel, Formula.Kripke.Satisfies];
        use λ w _ => w = f 1;
        constructor;
        . rfl;
        . use (f 0);
          exact fInj.injective.ne (by simp);

theorem reducible_S4_S5 : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟓 := by apply reducible_of_geach_defnability; simp_all [trans_of_refl_eucl];


theorem strict_reducible_S4_S5 [atleast : AtLeast 3 W] : (𝐒𝟒 : DeductionParameter α) <ₛ 𝐒𝟓 := by
  constructor;
  . apply reducible_S4_S5;
  . apply not_reducible_iff.mpr;
    obtain ⟨f, finv, fInj⟩ := atleast.mapping;
    existsi (◇(Formula.atom default) ⟶ □◇(Formula.atom default));
    constructor;
    . sorry;
    . apply unprovable_of_exists_frame;
      use { World := W, Rel := λ x y => (x = y) ∨ (x = (f 0) ∧ y = (f 1)) ∨ (x = (f 0) ∧ y = (f 2))};
      constructor;
      . apply iff_definability_memAxiomSetFrameClass (by simpa using instGeachDefinability (L := 𝐒𝟒)) |>.mpr;
        simp [Reflexive, Transitive];
        aesop;
      . simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel, Formula.Kripke.Satisfies];
        use λ w _ => w = f 2, f 0;
        constructor;
        . use f 2;
          constructor;
          . right; simp;
          . rfl;
        . use f 2;
          constructor;
          . aesop;
          . intro x hx;
            sorry;
            -- exact fInj.injective.ne (by simp);

theorem equiv_S5_KT4B : (𝐒𝟓 : DeductionParameter α) =ₛ 𝐊𝐓𝟒𝐁 := by apply equiv_of_geach_defnability; intros; constructor <;> simp_all [symm_of_refl_eucl, trans_of_refl_eucl, eucl_of_symm_trans];

end LO.Modal.Standard
