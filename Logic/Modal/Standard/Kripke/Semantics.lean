import Logic.Logic.System
import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.Deduction

class Set.IsNonempty (s : Set α) where
  nonempty : s.Nonempty

universe u v

namespace LO.Modal.Standard

def RelItr (R : α → α → Prop) : ℕ → α → α → Prop
  | 0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, R x z ∧ RelItr R n z y

@[simp]
lemma relItr_zero {R : α → α → Prop} {x y : α} : RelItr R 0 x y ↔ x = y := iff_of_eq rfl

@[simp]
lemma relItr_succ {R : α → α → Prop} {x y : α} : RelItr R (n + 1) x y ↔ ∃ z, R x z ∧ RelItr R n z y := iff_of_eq rfl

namespace Kripke


structure Frame (α : Type*) where
  World : Type*
  [World_nonempty : Nonempty World]
  Rel : World → World → Prop

structure FiniteFrame (α) extends Frame α where
  [World_finite : Finite World]

instance (F : Frame α) : Nonempty F.World := F.World_nonempty

instance : CoeSort (Frame α) (Type*) := ⟨Frame.World⟩

instance : Coe (FiniteFrame α) (Frame α) := ⟨λ F ↦ F.toFrame⟩

abbrev Frame.Rel' {F : Frame α} (w w' : F.World) := F.Rel w w'
scoped infix:45 " ≺ " => Frame.Rel'

protected abbrev Frame.RelItr (n : ℕ) {F : Frame α} (w w' : F.World) : Prop := RelItr (· ≺ ·) n w w'
scoped notation w:45 " ≺^[" n "] " w':46 => Frame.RelItr n w w'

/-- Frame with single world and identiy relation -/
abbrev TerminalFrame (α) : FiniteFrame α := { World := PUnit, Rel := (· = ·) }

@[simp]
lemma TerminalFrame.iff_rel : Frame.Rel' (F := (TerminalFrame α).toFrame) x y ↔ x = y := by aesop;

@[simp]
lemma TerminalFrame.iff_relItr : Frame.RelItr n (F := (TerminalFrame α).toFrame) x y ↔ x = y := by
  induction n with
  | zero => simp only [relItr_zero];
  | succ n ih => simp_all only [relItr_succ, exists_eq_left', iff_true];

abbrev FrameClass (α) := Set (Frame α)

/-
class FrameClass.IsNonempty (𝔽 : FrameClass α) where
  [nonempty : 𝔽.Nonempty]
-/


abbrev FiniteFrameClass (α) := Set (FiniteFrame α)

/-
class FiniteFrameClass.IsNonempty (𝔽 : FiniteFrameClass α) where
  [nonempty : 𝔽.Nonempty]
-/

def FrameClass.toFinite (𝔽 : FrameClass α) : FiniteFrameClass α := { F | ↑F ∈ 𝔽 }
postfix:max "ꟳ" => FrameClass.toFinite

instance : Coe (FrameClass α) (FiniteFrameClass α) := ⟨λ 𝔽 ↦ 𝔽ꟳ⟩


abbrev FrameCondition (α) := Frame α → Prop

abbrev FiniteFrameCondition (α) := FiniteFrame α → Prop


-- MEMO: 型を上手く合わせられず両方とも`u`に属しているが別にする必要があるだろう
abbrev Valuation (W : Type u) (α : Type u) := W → α → Prop

structure Model (α) where
  Frame : Frame α
  Valuation : Valuation Frame.World α

abbrev Model.World (M : Model α) := M.Frame.World
instance : CoeSort (Model α) (Type _) where coe := Model.World

end Kripke


variable {α : Type*}

open Standard.Kripke

def Formula.kripke_satisfies (M : Kripke.Model α) (w : M.World) : Formula α → Prop
  | atom a  => M.Valuation w a
  | verum   => True
  | falsum  => False
  | and p q => (kripke_satisfies M w p) ∧ (kripke_satisfies M w q)
  | or p q  => (kripke_satisfies M w p) ∨ (kripke_satisfies M w q)
  | imp p q => (kripke_satisfies M w p) → (kripke_satisfies M w q)
  | box p   => ∀ {w'}, w ≺ w' → (kripke_satisfies M w' p)

namespace Formula.kripke_satisfies

protected instance semantics (M : Model α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.kripke_satisfies M w⟩

variable {M : Model α} {w : M.World} {p q : Formula α}

@[simp] protected lemma iff_models : w ⊧ f ↔ kripke_satisfies M w f := iff_of_eq rfl

local infix:45 " ⊩ " => Formula.kripke_satisfies M

@[simp] lemma atom_def : w ⊧ atom a ↔ M.Valuation w a := by simp [kripke_satisfies];
@[simp] lemma top_def  : w ⊩ ⊤ ↔ True := by simp [kripke_satisfies];
@[simp] lemma bot_def  : w ⊩ ⊥ ↔ False := by simp [kripke_satisfies];
@[simp] lemma and_def  : w ⊩ p ⋏ q ↔ w ⊩ p ∧ w ⊩ q := by simp [kripke_satisfies];
@[simp] lemma or_def   : w ⊩ p ⋎ q ↔ w ⊩ p ∨ w ⊩ q := by simp [kripke_satisfies];
@[simp] lemma imp_def  : w ⊩ p ⟶ q ↔ w ⊩ p → w ⊩ q := by simp [kripke_satisfies, imp_iff_not_or];
@[simp] lemma not_def  : w ⊩ ~p ↔ ¬w ⊩ p := by simp [kripke_satisfies];
@[simp] lemma box_def  : w ⊩ □p ↔ ∀ w', w ≺ w' → w' ⊩ p := by simp [kripke_satisfies];
@[simp] lemma dia_def  : w ⊩ ◇p ↔ ∃ w', w ≺ w' ∧ w' ⊩ p := by simp [kripke_satisfies];

@[simp]
lemma multibox_def : w ⊩ □^[n]p ↔ ∀ v, w ≺^[n] v → v ⊩ p := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h w' hww';
      simp at h;
      obtain ⟨v, hwv, hvw'⟩ := hww';
      exact (ih.mp $ h _ hwv) w' hvw';
    . simp;
      intro h w' hww';
      apply ih.mpr;
      intro v hwv;
      exact h v w' hww' hwv;

@[simp]
lemma multidia_def : w ⊩ ◇^[n]p ↔ ∃ v, w ≺^[n] v ∧ v ⊩ p := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h;
      obtain ⟨v, hwv, hv⟩ := by simpa using h;
      obtain ⟨x, hvx, hx⟩ := ih.mp hv;
      existsi x;
      constructor;
      . existsi v; simp_all;
      . simpa;
    . simp;
      intro x y hwy hyx hx;
      existsi y;
      constructor;
      . simpa;
      . apply ih.mpr;
        existsi x;
        simp_all;

instance : Semantics.Tarski M.World where
  realize_top := by simp [top_def];
  realize_bot := by simp [bot_def];
  realize_not := by simp [not_def];
  realize_and := by simp [and_def];
  realize_or  := by simp [or_def];
  realize_imp := by simp [imp_def];

lemma mdp (hpq : w ⊧ p ⟶ q) (hp : w ⊧ p) : w ⊧ q := imp_def.mp hpq hp

end Formula.kripke_satisfies


def Formula.valid_on_KripkeModel (M : Model α) (f : Formula α) := ∀ w : M.World, w ⊧ f

namespace Formula.valid_on_KripkeModel

protected instance : Semantics (Formula α) (Model α) := ⟨fun M ↦ Formula.valid_on_KripkeModel M⟩

@[simp] protected lemma iff_models {M : Model α} : M ⊧ f ↔ valid_on_KripkeModel M f := iff_of_eq rfl

instance : Semantics.Bot (Model α) where
  realize_bot _ := by simp [valid_on_KripkeModel];

end Formula.valid_on_KripkeModel


def Formula.valid_on_KripkeFrame (F : Frame α) (f : Formula α) := ∀ V, (Model.mk F V) ⊧ f

namespace Formula.valid_on_KripkeFrame

protected instance semantics : Semantics (Formula α) (Frame α) := ⟨fun F ↦ Formula.valid_on_KripkeFrame F⟩

@[simp] protected lemma models_iff {F : Frame α} : F ⊧ f ↔ valid_on_KripkeFrame F f := iff_of_eq rfl

instance : Semantics.Bot (Frame α) where
  realize_bot _ := by simp [valid_on_KripkeFrame];

protected lemma axiomK {F : Frame α} : F ⊧* 𝗞 := by
  simp [valid_on_KripkeFrame, valid_on_KripkeModel, System.Axioms.K];
  intro f p q ef V x; subst ef;
  intro h₁ h₂ y rxy;
  exact h₁ rxy (h₂ rxy);

protected lemma nec {F : Frame α} (h : F ⊧ p) : F ⊧ □p := by
  intro V x y _;
  exact h V y;

protected lemma mdp {F : Frame α} (hpq : F ⊧ p ⟶ q) (hp : F ⊧ p) : F ⊧ q := by
  intro V x;
  exact (hpq V x) (hp V x);

end Formula.valid_on_KripkeFrame


@[simp] def Formula.valid_on_FiniteKripkeFrame (F : FiniteFrame α) (f : Formula α) := (F.toFrame) ⊧ f
namespace Formula.valid_on_FiniteKripkeFrame

protected instance semantics : Semantics (Formula α) (FiniteFrame α) := ⟨fun F ↦ Formula.valid_on_FiniteKripkeFrame F⟩

@[simp] protected lemma models_iff {F : FiniteFrame α} : F ⊧ f ↔ valid_on_FiniteKripkeFrame F f := iff_of_eq rfl

end Formula.valid_on_FiniteKripkeFrame


@[simp] def Formula.valid_on_KripkeFrameClass (𝔽 : FrameClass α) (p : Formula α) := ∀ F ∈ 𝔽, F ⊧ p

namespace Formula.valid_on_KripkeFrameClass

protected instance semantics : Semantics (Formula α) (FrameClass α) := ⟨fun 𝔽 ↦ Formula.valid_on_KripkeFrameClass 𝔽⟩

variable {𝔽 : FrameClass α}

@[simp] protected lemma models_iff : 𝔽 ⊧ f ↔ Formula.valid_on_KripkeFrameClass 𝔽 f := iff_of_eq rfl

protected lemma axiomK : 𝔽 ⊧* 𝗞 := by
  simp only [Semantics.RealizeSet.setOf_iff];
  rintro f ⟨p, q, _⟩ F _;
  apply (Semantics.RealizeSet.setOf_iff.mp $ valid_on_KripkeFrame.axiomK) f;
  use p, q;

protected lemma nec (h : 𝔽 ⊧ p) : 𝔽 ⊧ □p := by
  intro F hF;
  apply valid_on_KripkeFrame.nec;
  exact h F hF;

protected lemma mdp (hpq : 𝔽 ⊧ p ⟶ q) (hp : 𝔽 ⊧ p) : 𝔽 ⊧ q := by
  intro F hF;
  exact valid_on_KripkeFrame.mdp (hpq F hF) (hp F hF)

end Formula.valid_on_KripkeFrameClass


@[simp] def Formula.valid_on_FiniteKripkeFrameClass (𝔽 : FiniteFrameClass α) (p : Formula α) := ∀ F ∈ 𝔽, F ⊧ p

namespace Formula.valid_on_FiniteKripkeFrameClass

protected instance : Semantics (Formula α) (FiniteFrameClass α) := ⟨fun 𝔽 ↦ Formula.valid_on_FiniteKripkeFrameClass 𝔽⟩

@[simp] protected lemma models_iff {𝔽 : FiniteFrameClass α} : 𝔽 ⊧ f ↔ Formula.valid_on_FiniteKripkeFrameClass 𝔽 f := iff_of_eq rfl

end Formula.valid_on_FiniteKripkeFrameClass

/-
def AxiomSet.KripkeFrameClass (Ax : AxiomSet α) : FrameClass α := { F | F ⊧* System.theory (DeductionParameter.Normal Ax) }
notation "𝔽₂(" Ax ")" => AxiomSet.KripkeFrameClass Ax

def AxiomSet.FiniteKripkeFrameClass (Ax : AxiomSet α) : FiniteFrameClass α := { F | F ⊧* System.theory (DeductionParameter.Normal Ax)  }
notation "𝔽₂ꟳ(" Ax ")" => AxiomSet.FiniteKripkeFrameClass Ax


def DeductionParamter.KripkeFrameClass (𝓓 : DeductionParameter α) [𝓓.IsNormal] : FrameClass α := { F | F ⊧* System.theory 𝓓 }
notation "𝔽(" 𝓓 ")" => DeductionParamter.KripkeFrameClass 𝓓

def DeductionParamter.FiniteKripkeFrameClass (𝓓 : DeductionParameter α) [𝓓.IsNormal] : FiniteFrameClass α := { F | F ⊧* System.theory 𝓓 }
notation "𝔽ꟳ(" 𝓓 ")" => DeductionParamter.FiniteKripkeFrameClass 𝓓


def Kripke.AxiomSetFrameClass (Ax : AxiomSet α) : FrameClass α := { (F : Frame α) | F ⊧* Ax }
notation "𝔽(" Ax ")" => Kripke.AxiomSetFrameClass Ax

def Kripke.AxiomSetFiniteFrameClass (Ax : AxiomSet α) : FiniteFrameClass α := { (F : FiniteFrame α) | F.toFrame ⊧* Ax }
notation "𝔽ꟳ(" Ax ")" => Kripke.AxiomSetFiniteFrameClass Ax
-/


class AxiomSet.DefinesKripkeFrameClass (Ax : AxiomSet α) (𝔽 : FrameClass α) where
  defines : ∀ {F : Frame α}, F ⊧* Ax ↔ F ∈ 𝔽

instance AxiomSet.DefinesKripkeFrameClass.union
  {Ax₁ Ax₂ : AxiomSet α}
  (definability₁ : Ax₁.DefinesKripkeFrameClass 𝔽₁) (definability₂ : Ax₂.DefinesKripkeFrameClass 𝔽₂)
  : (Ax₁ ∪ Ax₂).DefinesKripkeFrameClass (𝔽₁ ∩ 𝔽₂) where
  defines := by
    intro F;
    simp only [Semantics.RealizeSet.union_iff];
    constructor;
    . intro ⟨h₁, h₂⟩;
      constructor;
      . exact definability₁.defines.mp h₁;
      . exact definability₂.defines.mp h₂;
    . intro ⟨h₁, h₂⟩;
      constructor;
      . apply definability₁.defines.mpr h₁;
      . apply definability₂.defines.mpr h₂;

open Formula

namespace Kripke

def ConditionalFrameClass (P : FrameCondition α) : FrameClass α := { F | P F }
notation "𝔽(" P ")" => ConditionalFrameClass P

def ConditionalFiniteFrameClass (P : FiniteFrameCondition α) : FiniteFrameClass α := { F | P F }
notation "𝔽ꟳ(" P ")" => ConditionalFiniteFrameClass P


abbrev AllFrameClass (α) : FrameClass α := Set.univ

instance : (AllFrameClass α).IsNonempty where
  nonempty := by use TerminalFrame α; trivial;


abbrev TransitiveFrameClass (α) : FrameClass α := 𝔽(λ F => Transitive F.Rel)

instance : 𝗞.DefinesKripkeFrameClass (AllFrameClass α) where
  defines := by simp only [Set.mem_univ, iff_true]; apply valid_on_KripkeFrame.axiomK;

end Kripke

/-
lemma validOnAxiomSetFrameClass_axiom (h : p ∈ Ax) : 𝔽(Ax) ⊧ p := by intro F hF; exact hF.realize h;

/-- Every frame that valid all axioms in `Ax` satisfy frame property `P` -/
class Definability (Ax : AxiomSet α) (P : FrameCondition α) where
  defines : ∀ (F : Frame α), F ⊧* Ax ↔ P F

instance Definability.union (definability₁ : Definability Ax₁ P₁) (definability₂ : Definability Ax₂ P₂) : Definability (Ax₁ ∪ Ax₂) (λ F => P₁ F ∧ P₂ F) where
  defines F := by
    constructor;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at h;
      constructor;
      . exact Definability.defines F |>.mp h.1;
      . exact Definability.defines F |>.mp h.2;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply Definability.defines F |>.mpr h.1;
      . apply Definability.defines F |>.mpr h.2;

lemma iff_definability_memAxiomSetFrameClass (definability : Definability Ax P) : ∀ {F : Frame α}, F ∈ 𝔽(Ax) ↔ P F := by
  apply definability.defines;


/-- Every **finite** frame that valid all axioms in `Ax` satisfy **finite** frame property `P` -/
class FiniteDefinability (Ax : AxiomSet α) (P : FiniteFrameCondition α) where
  fin_defines : ∀ (F : FiniteFrame α), F.toFrame ⊧* Ax ↔ P F

instance FiniteDefinability.union (definability₁ : FiniteDefinability Ax₁ P₁) (definability₂ : FiniteDefinability Ax₂ P₂) : FiniteDefinability (Ax₁ ∪ Ax₂) (λ F => P₁ F ∧ P₂ F) where
  fin_defines F := by
    constructor;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at h;
      constructor;
      . exact FiniteDefinability.fin_defines F |>.mp h.1;
      . exact FiniteDefinability.fin_defines F |>.mp h.2;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply FiniteDefinability.fin_defines F |>.mpr h.1;
      . apply FiniteDefinability.fin_defines F |>.mpr h.2;

lemma iff_finiteDefinability_memFiniteFrameClass (definability : FiniteDefinability Ax P) : ∀ {F : FiniteFrame α}, 𝔽ꟳ(Ax) F ↔ P F := by
  apply definability.fin_defines;

instance [definability : Definability Ax P] : FiniteDefinability Ax (λ F => P F.toFrame) where
  fin_defines F := by
    constructor;
    . exact iff_definability_memAxiomSetFrameClass definability |>.mp;
    . exact iff_definability_memAxiomSetFrameClass definability |>.mpr;

instance [ne : 𝔽ꟳ.IsNonempty] : 𝔽.IsNonempty where
  nonempty := by obtain ⟨F, hF⟩ := ne.nonempty; existsi F; exact hF;

instance [ne : 𝔽ꟳ(Ax).IsNonempty ] : 𝔽(Ax).IsNonempty where
  nonempty := by obtain ⟨F, hF⟩ := ne.nonempty; existsi F; exact hF;

end Kripke

section K

instance AxiomSet.K.definability : Definability (α := α) 𝗞 (λ _ => True) where
  defines := by
    simp [valid_on_KripkeFrame, valid_on_KripkeModel, System.Axioms.K];
    intros; subst_vars;
    simp_all;

instance AxiomSet.K.finiteDefinability : FiniteDefinability (α := α) 𝗞 (λ _ => True) where
  fin_defines := by
    simp [valid_on_KripkeFrame, valid_on_KripkeModel, System.Axioms.K];
    intros; subst_vars;
    simp_all;

instance [definability : Definability Ax P] : Definability (𝗞 ∪ Ax) P := by simpa using Definability.union AxiomSet.K.definability definability;

instance [definability : FiniteDefinability Ax P] : FiniteDefinability (𝗞 ∪ Ax) P := by simpa using FiniteDefinability.union AxiomSet.K.finiteDefinability definability;

instance : (𝔽ꟳ(𝗞) : FiniteFrameClass α).IsNonempty where
  nonempty := by
    existsi TerminalFrame α;
    apply iff_finiteDefinability_memFiniteFrameClass AxiomSet.K.finiteDefinability |>.mpr;
    trivial;

instance : (𝔽(𝗞) : FrameClass α).IsNonempty  := inferInstance

end K
-/

end LO.Modal.Standard
