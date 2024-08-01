import Logic.Logic.Semantics
import Logic.Logic.System
import Logic.Vorspiel.BinaryRelations

universe u v
-- set_option autoImplicit false

namespace LO.Kripke

structure Frame where
  World : Type u
  Rel : Rel World World
  [World_nonempty : Nonempty World]

instance : CoeSort Frame (Type u) := ⟨Frame.World⟩
instance : CoeFun Frame (λ F => F.World → F.World → Prop) := ⟨Frame.Rel⟩

instance {F : Frame} : Nonempty F.World := F.World_nonempty

abbrev Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y
scoped infix:45 " ≺ " => Frame.Rel'

noncomputable abbrev Frame.default {F : Frame} : F.World := Classical.choice F.World_nonempty
notation "﹫" => Frame.default


set_option linter.unusedVariables false in
abbrev Frame.Dep (α : Type*) := Frame

abbrev Frame.alt (F : Frame) (α) : Frame.Dep α := F
notation F:max "#" α:max => Frame.alt F α


structure FiniteFrame extends Frame where
  [World_finite : Finite World]

instance {F : FiniteFrame} : Finite (F.World) := F.World_finite
instance : Coe (FiniteFrame) (Frame) := ⟨λ F ↦ F.toFrame⟩


open Relation (ReflTransGen TransGen)


protected abbrev Frame.RelReflTransGen {F : Frame} : _root_.Rel F.World F.World:= ReflTransGen (· ≺ ·)
scoped infix:45 " ≺^* " => Frame.RelReflTransGen

namespace Frame.RelReflTransGen

variable {F : Frame}

@[simp] lemma single {x y : F.World} (hxy : x ≺ y) : x ≺^* y := ReflTransGen.single hxy

@[simp] lemma reflexive : Reflexive F.RelReflTransGen := Relation.reflexive_reflTransGen

@[simp] lemma refl {x : F.World} : x ≺^* x := reflexive x

@[simp] lemma transitive : Transitive F.RelReflTransGen := Relation.transitive_reflTransGen

@[simp] lemma symmetric : Symmetric F.Rel → Symmetric F.RelReflTransGen := ReflTransGen.symmetric

end Frame.RelReflTransGen


abbrev Frame.TransitiveReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^* ·)
postfix:max "^*" => Frame.TransitiveReflexiveClosure

namespace Frame.TransitiveReflexiveClosure

variable {F : Frame}

lemma single {x y : F.World} (hxy : x ≺ y) : F^*.Rel x y := ReflTransGen.single hxy

lemma rel_reflexive : Reflexive F^*.Rel := by intro x; exact ReflTransGen.refl;

lemma rel_transitive : Transitive F^*.Rel := by simp;

lemma rel_symmetric : Symmetric F.Rel → Symmetric F^* := ReflTransGen.symmetric

end Frame.TransitiveReflexiveClosure



protected abbrev Frame.RelTransGen {F : Frame} : _root_.Rel F.World F.World := TransGen (· ≺ ·)
scoped infix:45 " ≺^+ " => Frame.RelTransGen

namespace Frame.RelTransGen

variable {F : Frame}

@[simp] lemma single {x y : F.World} (hxy : x ≺ y) : x ≺^+ y := TransGen.single hxy

@[simp]
lemma transitive : Transitive F.RelTransGen := λ _ _ _ => TransGen.trans

@[simp]
lemma symmetric (hSymm : Symmetric F.Rel) : Symmetric F.RelTransGen := by
  intro x y rxy;
  induction rxy with
  | single h => exact TransGen.single $ hSymm h;
  | tail _ hyz ih => exact TransGen.trans (TransGen.single $ hSymm hyz) ih

end Frame.RelTransGen


abbrev Frame.TransitiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^+ ·)
scoped postfix:max "^+" => Frame.TransitiveClosure

namespace Frame.TransitiveClosure

variable {F : Frame}

lemma single {x y : F.World} (hxy : x ≺ y) : F^+ x y := TransGen.single hxy

lemma rel_transitive : Transitive F^+ := by simp;

lemma rel_symmetric (hSymm : Symmetric F.Rel) : Symmetric F.TransitiveClosure := by simp_all

end Frame.TransitiveClosure


abbrev FrameProperty := Frame → Prop


abbrev FrameClass := Set (Frame)

set_option linter.unusedVariables false in
abbrev FrameClass.Dep (α : Type*) := FrameClass

abbrev FrameClass.alt (𝔽 : FrameClass) (α) : FrameClass.Dep α := 𝔽
notation 𝔽:max "#" α:max => FrameClass.alt 𝔽 α

/-
abbrev FiniteFrameClass := Set (FiniteFrame)

@[simp] def FiniteFrameClass.toFrameClass (𝔽 : FiniteFrameClass) : FrameClass := { F | ∃ F', F' ∈ 𝔽 ∧ F'.toFrame = F }
instance : Coe (FiniteFrameClass) (FrameClass) := ⟨FiniteFrameClass.toFrameClass⟩

@[simp] def FrameClass.toFiniteFrameClass (𝔽 : FrameClass) : FiniteFrameClass := { F | F.toFrame ∈ 𝔽 }
instance : Coe (FrameClass) (FiniteFrameClass) := ⟨FrameClass.toFiniteFrameClass⟩

@[simp] abbrev FrameClass.restrictFinite (𝔽 : FrameClass) : FrameClass := FiniteFrameClass.toFrameClass ↑𝔽
postfix:max "ꟳ" => FrameClass.restrictFinite

lemma FrameClass.iff_mem_restrictFinite {𝔽 : FrameClass} {F : Frame} (h : F ∈ 𝔽) (F_finite : Finite F.World) : F ∈ 𝔽ꟳ := by
  simp;
  use { toFrame := F, World_finite := F_finite };
-/

-- set_option pp.universes true in
abbrev FrameClassOfSystem {F : Type u} [System F S] (𝓢 : S) (α : Type u) [Semantics F (Frame.Dep α)] : FrameClass.Dep α := { F | F ⊧* System.theory 𝓢 }
notation "𝔽(" 𝓢 " of " α ")" => FrameClassOfSystem 𝓢 α

abbrev FrameClassOfFrameProperty (P : FrameProperty) : FrameClass := { F | P F }
notation "𝔽(" P ")" => FrameClassOfFrameProperty P


section

/-- FrameClass for `𝐈𝐧𝐭` or `𝐒𝟒` -/
abbrev TransitiveReflexiveFrameClass := 𝔽((λ F => Transitive F ∧ Reflexive F))

/-- FrameClass for `𝐂𝐥` -/
abbrev TransitiveReflexiveExtensiveFrameClass := 𝔽((λ F => Transitive F ∧ Reflexive F ∧ Extensive F))

end


class FrameClass.Characteraizable (𝔽 : FrameClass) (P : FrameProperty) where
  characterize : ∀ {F}, P F → F ∈ 𝔽
  nonempty : ∃ F, P F


section Soundness

variable
  {F : Type u} {S} {α : Type u}
  [System F S] [Semantics F (Frame.Dep α)]
  {𝓢 : S} {p : F} {P : FrameProperty}

lemma sound : 𝓢 ⊢! p → 𝔽(𝓢 of α) ⊧ p := by
  intro hp F hF;
  simp [System.theory] at hF;
  exact hF p hp;

instance : Sound 𝓢 𝔽(𝓢 of α) := ⟨sound⟩


lemma sound_of_characterizability (characterizability : 𝔽(𝓢 of α).Characteraizable P) : 𝓢 ⊢! p → 𝔽(P) ⊧ p := by
  intro h F hF;
  apply sound h;
  apply characterizability.characterize hF;

instance instSoundOfCharacterizability (characterizability : 𝔽(𝓢 of α).Characteraizable P) : Sound 𝓢 𝔽(P) := ⟨sound_of_characterizability characterizability⟩


variable [LogicalConnective F] [Semantics.Bot (Frame.Dep α)]

lemma unprovable_bot (hc : 𝔽(𝓢 of α).Nonempty) : 𝓢 ⊬! ⊥ := by
  apply (not_imp_not.mpr (sound (α := α)));
  simp [Semantics.Realize];
  exact hc;

  -- exact Semantics.Bot.realize_bot 𝔽(𝓢 of α);

lemma unprovable_bot_of_characterizability (characterizability : 𝔽(𝓢 of α).Characteraizable P) : 𝓢 ⊬! ⊥ := by
  apply not_imp_not.mpr $ sound_of_characterizability (characterizability := characterizability);
  simp [Semantics.Realize];
  exact characterizability.nonempty;

/-
instance
  [characterizability : 𝔽(𝓢 of α).Characteraizable P]
  : System.Consistent 𝓢 := System.Consistent.of_unprovable $ unprovable_bot_of_characterizability (α := α) (characterizability := characterizability)
-/

end Soundness


abbrev Valuation (F : Frame) (α : Type*) := F.World → α → Prop

abbrev Valuation.atomic_hereditary (V : Valuation F α) : Prop := ∀ {w₁ w₂ : F.World}, (w₁ ≺ w₂) → ∀ {a}, (V w₁ a) → (V w₂ a)


structure Model (α) where
  Frame : Frame
  Valuation : Valuation Frame α

abbrev Model.World (M : Model α) := M.Frame.World
instance : CoeSort (Model α) (Type u) := ⟨Model.World⟩



end LO.Kripke