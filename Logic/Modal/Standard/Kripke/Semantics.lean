import Logic.Logic.Kripke.Basic
import Logic.Logic.System
import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.Deduction

universe u v

namespace LO.Modal.Standard

open System
open Kripke

namespace Formula.Kripke

def Satisfies (M : Kripke.Model α) (x : M.World) : Formula α → Prop
  | atom a  => M.Valuation x a
  | verum   => True
  | falsum  => False
  | and p q => (Satisfies M x p) ∧ (Satisfies M x q)
  | or p q  => (Satisfies M x p) ∨ (Satisfies M x q)
  | imp p q => (Satisfies M x p) → (Satisfies M x q)
  | neg p   => ¬(Satisfies M x p)
  | □p   => ∀ {y}, x ≺ y → (Satisfies M y p)

namespace Satisfies

protected instance semantics {M : Kripke.Model α} : Semantics (Formula α) (M.World) := ⟨fun x ↦ Formula.Kripke.Satisfies M x⟩

variable {M : Kripke.Model α} {x : M.World} {p q : Formula α}

@[simp] protected lemma iff_models : x ⊧ p ↔ Kripke.Satisfies M x p := iff_of_eq rfl

lemma and_def : x ⊧ p ⋏ q ↔ x ⊧ p ∧ x ⊧ q := by
  constructor;
  . intro ⟨hp, hq⟩; exact ⟨hp, hq⟩;
  . intro h; exact ⟨h.1, h.2⟩;

lemma or_def : x ⊧ p ⋎ q ↔ x ⊧ p ∨ x ⊧ q := by
  constructor;
  . intro h; exact h.elim (λ hp => Or.inl hp) (λ hq => Or.inr hq);
  . intro h; exact h.elim (λ hp => Or.inl hp) (λ hq => Or.inr hq);

lemma not_def : x ⊧ ~p ↔ ¬(x ⊧ p) := by
  constructor;
  . intro h; exact h;
  . intro h; exact h;

lemma imp_def : x ⊧ p ⟶ q ↔ (x ⊧ p) → (x ⊧ q) := by
  constructor;
  . intro h; exact h;
  . intro h; exact h;

protected instance tarski : Semantics.Tarski (M.World) where
  realize_top := by intro; trivial;
  realize_bot := by aesop;
  realize_not := not_def;
  realize_and := and_def;
  realize_or  := or_def;
  realize_imp := imp_def;


lemma dia_def : x ⊧ ◇p ↔ ∃ y, x ≺ y ∧ y ⊧ p := by simp [Kripke.Satisfies];

lemma multibox_def : x ⊧ □^[n]p ↔ ∀ {y}, x ≺^[n] y → y ⊧ p := by
  induction n generalizing x with
  | zero => aesop;
  | succ n ih =>
    constructor;
    . intro h y Rxy;
      simp [Kripke.Satisfies] at h;
      obtain ⟨u, Rxu, Ruy⟩ := Rxy;
      exact (ih.mp $ h Rxu) Ruy;
    . simp;
      intro h y Rxy;
      apply ih.mpr;
      intro u Ryu;
      exact h _ Rxy Ryu;

lemma multidia_def : x ⊧ ◇^[n]p ↔ ∃ y, x ≺^[n] y ∧ y ⊧ p := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h;
      replace h : x ⊧ (◇◇^[n]p) := by simpa using h;
      obtain ⟨v, hwv, hv⟩ := dia_def.mp h;
      obtain ⟨x, hvx, hx⟩ := ih.mp hv;
      use x;
      constructor;
      . use v;
      . assumption;
    . intro h;
      obtain ⟨y, Rxy, hy⟩ := h;
      obtain ⟨u, Rxu, Ruy⟩ := Rxy;
      simp;
      apply dia_def.mpr;
      use u;
      constructor;
      . exact Rxu;
      . apply ih.mpr;
        use y;

end Satisfies


def ValidOnModel (M : Kripke.Model α) (p : Formula α) := ∀ x : M.World, x ⊧ p

namespace ValidOnModel

instance semantics : Semantics (Formula α) (Kripke.Model α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

@[simp] protected lemma iff_models {M : Kripke.Model α} : M ⊧ f ↔ Kripke.ValidOnModel M f := iff_of_eq rfl

instance : Semantics.Bot (Kripke.Model α) where
  realize_bot M := by simp [Kripke.ValidOnModel, Kripke.Satisfies];

end ValidOnModel


def ValidOnFrame (F : Frame) (p : Formula α) := ∀ V, (⟨F, V⟩ : Kripke.Model α) ⊧ p

namespace ValidOnFrame

instance semantics : Semantics (Formula α) (Frame.Dep α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Frame.Dep α}

@[simp] protected lemma models_iff : F ⊧ p ↔ Kripke.ValidOnFrame F p := iff_of_eq rfl


instance : Semantics.Bot (Frame.Dep α) where
  realize_bot _ := by simp [Kripke.ValidOnFrame];


protected lemma axiomK : F ⊧* 𝗞 := by
  simp [Kripke.ValidOnFrame, Kripke.ValidOnModel, Axioms.K];
  intro _ p q e V x; subst e;
  intro h₁ h₂ y Rxy;
  exact h₁ Rxy $ h₂ Rxy;

protected lemma nec (h : F ⊧ p) : F ⊧ □p := by
  intro V x y _;
  exact h V y;

protected lemma mdp (hpq : F ⊧ p ⟶ q) (hp : F ⊧ p) : F ⊧ q := by
  intro V x;
  exact (hpq V x) (hp V x);

end ValidOnFrame


@[simp] def ValidOnFrameClass (𝔽 : FrameClass) (p : Formula α) := ∀ {F : Frame}, F ∈ 𝔽 → F#α ⊧ p

namespace ValidOnFrameClass

instance semantics :Semantics (Formula α) (FrameClass.Dep α) := ⟨fun 𝔽 ↦ ValidOnFrameClass 𝔽⟩

variable {𝔽 : FrameClass.Dep α}

@[simp] protected lemma models_iff : 𝔽 ⊧ p ↔ Formula.Kripke.ValidOnFrameClass 𝔽 p := iff_of_eq rfl

protected lemma axiomK : 𝔽 ⊧* 𝗞 := by
  simp only [Semantics.RealizeSet.setOf_iff];
  rintro f ⟨p, q, _⟩ F _;
  apply (Semantics.RealizeSet.setOf_iff.mp $ Kripke.ValidOnFrame.axiomK) f;
  use p, q;

protected lemma nec (h : 𝔽 ⊧ p) : 𝔽 ⊧ □p := by
  intro _ hF;
  apply Kripke.ValidOnFrame.nec;
  exact h hF;

protected lemma mdp (hpq : 𝔽 ⊧ p ⟶ q) (hp : 𝔽 ⊧ p) : 𝔽 ⊧ q := by
  intro _ hF;
  exact Kripke.ValidOnFrame.mdp (hpq hF) (hp hF)

end ValidOnFrameClass

end Formula.Kripke


namespace Kripke

open Formula.Kripke (ValidOnFrame ValidOnModel Satisfies)

variable {𝔽 : Kripke.FrameClass} {F : Kripke.Frame}
         {p q : Formula α}

lemma iff_not_validOnFrameClass : ¬(𝔽#α ⊧ p) ↔ ∃ F ∈ 𝔽, ∃ V x, ¬Satisfies ⟨F, V⟩ x p := by
  simp [ValidOnFrame, ValidOnModel, Satisfies];

lemma iff_not_set_validOnFrameClass : ¬(𝔽#α ⊧* T) ↔ ∃ p ∈ T, ∃ F ∈ 𝔽, ∃ V x, ¬Satisfies ⟨F, V⟩ x p  := by
  simp [Semantics.realizeSet_iff, ValidOnFrame, ValidOnModel, Satisfies];

lemma iff_not_validOnFrame : ¬(F#α ⊧* T) ↔ ∃ p ∈ T, ∃ V x, ¬Satisfies ⟨F, V⟩ x p := by
  simp [Semantics.realizeSet_iff, ValidOnFrame, ValidOnModel, Satisfies];


abbrev FrameClassOfSystem (α : Type u) {S : Type v} [System (Formula α) S] (𝓢 : S) : FrameClass.Dep α := { (F : Frame.Dep α) | F ⊧* System.theory 𝓢 }
notation "𝔽(" 𝓢 " of " α ")" => FrameClassOfSystem α 𝓢

def characterizable_of_valid_axiomset {Ax : Set (Formula α)} {𝔽 : FrameClass} (nonempty : 𝔽.Nonempty) (h : 𝔽#α ⊧* Ax)
  : FrameClass.Characteraizable { (F : Frame.Dep α) | F ⊧* (System.theory 𝝂(Ax)) } 𝔽 where
  characterize := by
    simp only [System.theory, Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, Set.mem_setOf_eq];
    intro F hF p hp;
    induction hp using Deduction.inducition_with_necOnly! with
    | hMaxm h =>
      simp at h;
      rcases h with (⟨_, _, rfl⟩ | hR);
      . simp_all [ValidOnFrame, ValidOnModel, Satisfies];
      . exact h.RealizeSet hR hF;
    | hOrElim =>
      simp_all [ValidOnFrame, ValidOnModel, Satisfies];
      intros; rename_i hpr hqr hpq;
      cases hpq with
      | inl hp => exact hpr hp;
      | inr hq => exact hqr hq;
    | _ => simp_all [ValidOnFrame, ValidOnModel, Satisfies];
  nonempty := nonempty


section Sound

variable {α : Type u} [System (Formula α) S] {𝓢 : S} {p : Formula α}

lemma sound : 𝓢 ⊢! p → 𝔽(𝓢 of α) ⊧ p := by
  intro hp F hF;
  simp [System.theory] at hF;
  exact hF p hp;

instance : Sound 𝓢 𝔽(𝓢 of α) := ⟨sound⟩

lemma unprovable_bot (hc : 𝔽(𝓢 of α).Nonempty) : 𝓢 ⊬! ⊥ := by
  apply (not_imp_not.mpr (sound (α := α)));
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hc;
  use F;
  constructor;
  . exact hF;
  . exact Semantics.Bot.realize_bot (F := Formula α) (M := Frame.Dep α) F;

instance (hc : 𝔽(𝓢 of α).Nonempty) : System.Consistent 𝓢 := System.Consistent.of_unprovable $ unprovable_bot hc

lemma sound_of_characterizability [characterizability : 𝔽(𝓢 of α).Characteraizable 𝔽₂] : 𝓢 ⊢! p → 𝔽₂#α ⊧ p := by
  intro h F hF;
  apply sound h;
  apply characterizability.characterize hF;

instance instSoundOfCharacterizability [𝔽(𝓢 of α).Characteraizable 𝔽₂] : Sound 𝓢 (𝔽₂#α) := ⟨sound_of_characterizability⟩

lemma unprovable_bot_of_characterizability [characterizability : 𝔽(𝓢 of α).Characteraizable 𝔽₂] : 𝓢 ⊬! ⊥ := by
  apply unprovable_bot;
  obtain ⟨F, hF⟩ := characterizability.nonempty;
  use F;
  apply characterizability.characterize hF;

instance instConsistentOfCharacterizability [FrameClass.Characteraizable.{u} 𝔽(𝓢 of α) 𝔽₂] : System.Consistent 𝓢
  := System.Consistent.of_unprovable $ unprovable_bot_of_characterizability

end Sound


private instance K_characterizable' : FrameClass.Characteraizable { (F : Frame.Dep α) | F ⊧* (System.theory 𝝂(∅)) } AllFrameClass := characterizable_of_valid_axiomset
  ⟨⟨PUnit,  λ _ _ => True⟩, trivial⟩
  (by aesop)

instance K_characterizable : 𝔽(𝐊 of α).Characteraizable AllFrameClass := by
  convert K_characterizable';
  exact DeductionParameter.K_is_empty_normal;

instance K_sound : Sound 𝐊 (AllFrameClass#α) := inferInstance

instance K_consistent : System.Consistent (𝐊 : DeductionParameter α) := inferInstance


section FiniteSound

variable {𝔽 : FrameClass} {p : Formula α}

lemma restrict_finite : 𝔽#α ⊧ p → 𝔽ꟳ#α ⊧ p := by
  intro h F hF;
  obtain ⟨fF, hfF, e⟩ := hF; subst e;
  exact h hfF;

instance instFiniteSound {Λ : DeductionParameter α} [sound : Sound Λ (𝔽#α)] : Sound Λ (𝔽ꟳ#α) := ⟨by
  intro p h;
  exact restrict_finite $ sound.sound h;
⟩

instance K_fin_sound : Sound 𝐊 (AllFrameClassꟳ#α) := inferInstance

end FiniteSound

end Kripke


section StrictlyWeakerThan

variable [Inhabited α] [DecidableEq α]

open System (weakerThan_iff)
open Kripke
open Formula (atom)
open Formula.Kripke

theorem K_strictlyWeakerThan_KD : (𝐊 : DeductionParameter α) <ₛ 𝐊𝐃 := by
  constructor;
  . apply reducible_K_KD;
  . simp [weakerThan_iff];
    use (□(atom default) ⟶ ◇(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [ValidOnFrame, ValidOnModel];
      use { World := Fin 1, Rel := λ _ _ => False }, (λ w _ => w = 0), 0;
      simp [Satisfies];

-- MEMO: 𝐊𝐃 <ₛ 𝐊𝐓, so 𝐊 <ₛ 𝐊𝐓,

theorem K_strictlyWeakerThan_K4 : (𝐊 : DeductionParameter α) <ₛ 𝐊𝟒 := by
  constructor;
  . apply reducible_K_K4;
  . simp [weakerThan_iff];
    use (□(atom default) ⟶ □□(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [ValidOnFrame, ValidOnModel];
      use { World := Fin 2, Rel := λ x y => x ≠ y }, (λ w _ => w = 1), 0;
      simp [Satisfies];
      constructor;
      . intro y;
        match y with
        | 0 => simp [Frame.Rel]; aesop;
        | 1 => simp;
      . use 1;
        constructor;
        . simp [Frame.Rel]; aesop;
        . use 0; simp [Frame.Rel]; aesop;

theorem K_strictlyWeakerThan_KB : (𝐊 : DeductionParameter α) <ₛ 𝐊𝐁 := by
  constructor;
  . apply reducible_K_KB;
  . simp [weakerThan_iff];
    use ((atom default) ⟶ □◇(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [ValidOnFrame, ValidOnModel];
      use { World := Fin 2, Rel := λ x y => x = 0 ∧ y = 1 }, (λ w _ => w = 0), 0;
      simp [Satisfies];
      use 1;

theorem K_strictlyWeakerThan_K5 : (𝐊 : DeductionParameter α) <ₛ 𝐊𝟓 := by
  constructor;
  . apply reducible_K_K5;
  . simp [weakerThan_iff];
    use (◇(atom default) ⟶ □◇(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [ValidOnFrame, ValidOnModel];
      use { World := Fin 2, Rel := λ x _ => x = 0 }, (λ w _ => w = 0), 0;
      simp [Satisfies];
      use 1;
      simp;

end StrictlyWeakerThan

end LO.Modal.Standard
