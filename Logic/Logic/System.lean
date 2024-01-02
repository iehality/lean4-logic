import Logic.Logic.Semantics

/-!
# Basic definitions and properties of proof-related notions

This file defines a characterization of the proof/provability/calculus of formulas.
Also defines soundness and completeness.

## Main Definitions
* `LO.System`: Proof system of logic.
* `LO.Sound`: Soundness of the proof system.
* `LO.Complete`: Completeness of the proof system.

-/

namespace LO

variable {F : Type u} [LogicSymbol F]

/- Deduction System of F -/

class System (F : Type u) [LogicSymbol F] where
  Bew : Set F → F → Type u
  axm : ∀ {f}, f ∈ T → Bew T f
  weakening' : ∀ {T U f}, T ⊆ U → Bew T f → Bew U f

namespace System
variable [𝓑 : System F]

instance : HasTurnstile F (Type u) := ⟨𝓑.Bew⟩

def BewTheory (T U : Set F) : Type u := {f : F} → f ∈ U → T ⊢ f

infix:45 " ⊢* " => System.BewTheory

abbrev Provable (T : Set F) (f : F) : Prop := Nonempty (T ⊢ f)

infix:45 " ⊢! " => System.Provable

noncomputable def Provable.toProof {T : Set F} {f : F} (h : T ⊢! f) : T ⊢ f := Classical.choice h

abbrev Unprovable (T : Set F) (f : F) : Prop := IsEmpty (T ⊢ f)

infix:45 " ⊬ " => System.Unprovable

-- TODO: 互換性のために残している
infix:45 " ⊬! " => System.Unprovable

lemma unprovable_iff_not_provable {T : Set F} {f : F} : T ⊬ f ↔ ¬T ⊢! f := by simp[System.Unprovable]

def BewTheoryEmpty (T : Set F) : T ⊢* ∅ := fun h => by contradiction

def BewTheory.ofSubset {T U : Set F} (h : U ⊆ T) : T ⊢* U := fun hf => axm (h hf)

def BewTheory.refl (T : Set F) : T ⊢* T := axm

def Consistent (T : Set F) : Prop := IsEmpty (T ⊢ ⊥)

def weakening {T U : Set F} {f : F} (b : T ⊢ f) (ss : T ⊆ U) : U ⊢ f := weakening' ss b

lemma Consistent.of_subset {T U : Set F} (h : Consistent U) (ss : T ⊆ U) : Consistent T := ⟨fun b => h.false (weakening b ss)⟩

lemma inconsistent_of_proof {T : Set F} (b : T ⊢ ⊥) : ¬Consistent T := by simp[Consistent]; exact ⟨b⟩

lemma consistemt_iff_unprovable {T : Set F} : Consistent T ↔ T ⊬ ⊥ := by rfl

protected def Complete (T : Set F) : Prop := ∀ f, (T ⊢! f) ∨ (T ⊢! ~f)

def Independent (T : Set F) (f : F) : Prop := T ⊬ f ∧ T ⊬ ~f

lemma incomplete_iff_exists_independent {T : Set F} :
    ¬System.Complete T ↔ ∃ f, Independent T f := by simp[System.Complete, not_or, Independent]

def theory (T : Set F) : Set F := {p | T ⊢! p}

class Subtheory (T U : Set F) where
  sub : {f : F} → T ⊢ f → U ⊢ f

class Equivalent (T U : Set F) where
  ofLeft : {f : F} → T ⊢ f → U ⊢ f
  ofRight : {f : F} → U ⊢ f → T ⊢ f

namespace Subtheory

variable (T U T₁ T₂ T₃ : Set F)

@[refl] instance : Subtheory T T := ⟨id⟩

@[trans] protected def trans [Subtheory T₁ T₂] [Subtheory T₂ T₃] : Subtheory T₁ T₃ :=
  ⟨fun {f} b => sub (sub b : T₂ ⊢ f)⟩

def ofSubset (h : T ⊆ U) : Subtheory T U := ⟨fun b => weakening b h⟩

end Subtheory

namespace Equivalent

variable (T U T₁ T₂ T₃ : Set F)

@[refl] instance : Equivalent T T := ⟨id, id⟩

@[symm] instance [Equivalent T U] : Equivalent U T := ⟨ofRight, ofLeft⟩

@[trans] protected def trans [Equivalent T₁ T₂] [Equivalent T₂ T₃] : Equivalent T₁ T₃ :=
  ⟨fun {f} b => ofLeft (ofLeft b : T₂ ⊢ f), fun {f} b => ofRight (ofRight b : T₂ ⊢ f)⟩

end Equivalent

end System

def System.hom [System F] {G : Type u} [LogicSymbol G] (F : G →L F) : System G where
  Bew := fun T g => F '' T ⊢ F g
  axm := fun h => System.axm (Set.mem_image_of_mem F h)
  weakening' := fun h => by simp; exact System.weakening' (Set.image_subset F h)

variable (F)
variable [LogicSymbol F] [𝓑 : System F] {α: Type*} [𝓢 : Semantics F α]

class Sound where
  sound : ∀ {T : Set F} {p : F}, T ⊢ p → T ⊨ p

class SoundOn (M : Type w) (a : α) (H : Set F) where
  sound : ∀ {T : Set F} {p : F}, p ∈ H → T ⊢ p → a ⊧ p

class Complete extends Sound F where
  complete : ∀ {T : Set F} {p : F}, T ⊨ p → T ⊢ p

variable {F}

namespace Sound

variable [Sound F]
variable {a : α}

lemma sound' {T : Set F} {f : F} : T ⊢! f → T ⊨ f := by rintro ⟨b⟩; exact sound b

lemma not_provable_of_countermodel {T : Set F} {p : F}
  (hT : a ⊧* T) (hp : ¬a ⊧ p) : IsEmpty (T ⊢ p) :=
  ⟨fun b => by have : a ⊧ p := Sound.sound b hT; contradiction⟩

lemma consistent_of_model {T : Set F}
  (hT : a ⊧* T) : System.Consistent T :=
  not_provable_of_countermodel (p := ⊥) hT (by simp)

lemma consistent_of_satisfiable {T : Set F} : Semantics.SatisfiableTheory T → System.Consistent T := by
  rintro ⟨_, h⟩; exact consistent_of_model h

lemma models_of_proof {T : Set F} {f} (h : a ⊧* T) (b : T ⊢ f) : a ⊧ f :=
  Sound.sound b h

lemma modelsTheory_of_proofTheory {T U : Set F} (h : s ⊧* T) (b : T ⊢* U) : s ⊧* U :=
  fun _ hf => models_of_proof h (b hf)

end Sound

namespace Complete

variable [Complete F]

lemma satisfiableTheory_iff_consistent {T : Set F} : Semantics.SatisfiableTheory T ↔ System.Consistent T :=
  ⟨Sound.consistent_of_satisfiable,
   by contrapose; intro h
      have : T ⊨ ⊥
      { intro a hM; have : Semantics.SatisfiableTheory T := ⟨a, hM⟩; contradiction }
      have : T ⊢ ⊥ := complete this
      exact System.inconsistent_of_proof this⟩

lemma not_satisfiable_iff_inconsistent {T : Set F} : ¬Semantics.SatisfiableTheory T ↔ T ⊢! ⊥ := by
  simp[satisfiableTheory_iff_consistent, System.Consistent]

lemma consequence_iff_provable {T : Set F} {f : F} : T ⊨ f ↔ T ⊢! f :=
⟨fun h => ⟨complete h⟩, by rintro ⟨b⟩; exact Sound.sound b⟩

end Complete

namespace System

variable [LO.Complete F]

def ofSemanticsSubtheory {T₁ T₂ : Set F} (h : Semantics.Subtheory T₁ T₂) : System.Subtheory T₁ T₂ :=
  ⟨fun hf => Complete.complete (h (Sound.sound hf))⟩

end System

namespace Semantics

variable [LO.Complete F]

lemma ofSystemSubtheory (T₁ T₂ : Set F) [System.Subtheory T₁ T₂] : Semantics.Subtheory T₁ T₂ :=
  fun hf => (Sound.sound $ System.Subtheory.sub $ Complete.complete hf)

end Semantics

end LO
