import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard

namespace PLoN

structure Frame (α) where
  World : Type*
  [World_inhabited : Inhabited World]
  Rel : Formula α → World → World → Prop

abbrev Frame.default {F : PLoN.Frame α} : F.World := F.World_inhabited.default
scoped notation "﹫" => Frame.default


instance : CoeFun (PLoN.Frame α) (λ F => Formula α → F.World → F.World → Prop) := ⟨Frame.Rel⟩

abbrev Frame.Rel' {F : PLoN.Frame α} (p : Formula α) (x y : F.World) := F.Rel p x y
scoped notation:45 x:90 " ≺[" p "] " y:90 => Frame.Rel' p x y


structure FiniteFrame (α) extends Frame α where
  [World_finite : Finite World]

instance : Coe (FiniteFrame α) (Frame α) := ⟨λ F ↦ F.toFrame⟩


abbrev terminalFrame (α) : FiniteFrame α where
  World := Unit
  Rel := λ _ _ _ => True


abbrev FrameClass (α : Type*) := Set (PLoN.Frame α)


abbrev Valuation (F : PLoN.Frame α) (α : Type*) := F.World → α → Prop

structure Model (α) where
  Frame : PLoN.Frame α
  Valuation : PLoN.Valuation Frame α

abbrev Model.World (M : PLoN.Model α) := M.Frame.World
instance : CoeSort (PLoN.Model α) (Type _) := ⟨Model.World⟩



end PLoN

variable {α : Type*}

open Standard.PLoN

def Formula.PLoN.Satisfies (M : PLoN.Model α) (w : M.World) : Formula α → Prop
  | atom a  => M.Valuation w a
  | verum   => True
  | falsum  => False
  | and p q => (PLoN.Satisfies M w p) ∧ (PLoN.Satisfies M w q)
  | or p q  => (PLoN.Satisfies M w p) ∨ (PLoN.Satisfies M w q)
  | imp p q => (PLoN.Satisfies M w p) → (PLoN.Satisfies M w q)
  | box p   => ∀ {w'}, w ≺[p] w' → (PLoN.Satisfies M w' p)


namespace Formula.PLoN.Satisfies

protected instance semantics (M : PLoN.Model α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.PLoN.Satisfies M w⟩

variable {M : PLoN.Model α} {w : M.World} {p q : Formula α}

@[simp] protected lemma iff_models : w ⊧ p ↔ PLoN.Satisfies M w p := by rfl

instance : Semantics.Tarski M.World where
  realize_top := by simp [PLoN.Satisfies];
  realize_bot := by simp [PLoN.Satisfies];
  realize_not := by simp [PLoN.Satisfies];
  realize_and := by simp [PLoN.Satisfies];
  realize_or  := by simp [PLoN.Satisfies];
  realize_imp := by simp [PLoN.Satisfies];

end Formula.PLoN.Satisfies


def Formula.PLoN.ValidOnModel (M : PLoN.Model α) (p : Formula α) : Prop := ∀ w : M.World, w ⊧ p

namespace Formula.PLoN.ValidOnModel

instance : Semantics (Formula α) (PLoN.Model α) := ⟨fun M ↦ Formula.PLoN.ValidOnModel M⟩

@[simp]
protected lemma iff_models {M : PLoN.Model α} {p : Formula α}
: M ⊧ p ↔ Formula.PLoN.ValidOnModel M p := by rfl

instance : Semantics.Bot (PLoN.Model α) where
  realize_bot _ := by
    simp [Formula.PLoN.ValidOnModel];
    use ﹫;

end Formula.PLoN.ValidOnModel


def Formula.PLoN.ValidOnFrame (F : PLoN.Frame α) (p : Formula α) := ∀ V, (Model.mk F V) ⊧ p

namespace Formula.PLoN.ValidOnFrame

instance : Semantics (Formula α) (PLoN.Frame α) := ⟨fun F ↦ Formula.PLoN.ValidOnFrame F⟩

@[simp]
protected lemma iff_models {F : PLoN.Frame α} {p : Formula α}
: F ⊧ p ↔ Formula.PLoN.ValidOnFrame F p := by rfl

variable {F : Frame α}

instance : Semantics.Bot (PLoN.Frame α) where
  realize_bot _ := by simp [Formula.PLoN.ValidOnFrame];

protected lemma nec (h : F ⊧ p) : F ⊧ □p := by
  intro V x y _;
  exact h V y;

protected lemma mdp (hpq : F ⊧ p ⟶ q) (hp : F ⊧ p) : F ⊧ q := by
  intro V x;
  exact (hpq V x) (hp V x);

protected lemma disj₃ : F ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r := by
  intro V x hpr hqr hpq;
  cases hpq with
  | inl hp => exact hpr hp;
  | inr hq => exact hqr hq;

end Formula.PLoN.ValidOnFrame


def Formula.PLoN.ValidOnFrameClass (𝔽 : PLoN.FrameClass α) (p : Formula α) := ∀ {F}, F ∈ 𝔽 → F ⊧ p

namespace Formula.PLoN.ValidOnFrameClass

instance : Semantics (Formula α) (PLoN.FrameClass α) := ⟨fun 𝔽 ↦ Formula.PLoN.ValidOnFrameClass 𝔽⟩

variable {𝔽 : FrameClass α}

@[simp]
protected lemma iff_models {𝔽 : PLoN.FrameClass α} {p : Formula α} : 𝔽 ⊧ p ↔ Formula.PLoN.ValidOnFrameClass 𝔽 p := by rfl

protected lemma nec (h : 𝔽 ⊧ p) : 𝔽 ⊧ □p := by
  intro _ hF;
  apply PLoN.ValidOnFrame.nec;
  exact h hF;

protected lemma mdp (hpq : 𝔽 ⊧ p ⟶ q) (hp : 𝔽 ⊧ p) : 𝔽 ⊧ q := by
  intro _ hF;
  exact PLoN.ValidOnFrame.mdp (hpq hF) (hp hF)

protected lemma disj₃ : 𝔽 ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r := by
  intro _ _;
  exact PLoN.ValidOnFrame.disj₃;

end Formula.PLoN.ValidOnFrameClass


def DeductionParameter.CharacterizedByPLoNFrameClass (𝓓 : DeductionParameter α) (𝔽 : PLoN.FrameClass α) := ∀ {F : Frame α}, F ∈ 𝔽 → F ⊧* 𝓓.theory

-- MEMO: `←`方向は成り立たない可能性がある
def DeductionParameter.DefinesPLoNFrameClass (𝓓 : DeductionParameter α) (𝔽 : PLoN.FrameClass α) := ∀ {F : Frame α}, F ⊧* 𝓓.theory ↔ F ∈ 𝔽

namespace PLoN

open Formula.PLoN

abbrev AllFrameClass (α) : FrameClass α := Set.univ

lemma AllFrameClass.nonempty : (AllFrameClass.{_, 0} α).Nonempty := by
  use terminalFrame α
  trivial;

open Formula

lemma N_characterized : 𝐍.CharacterizedByPLoNFrameClass (AllFrameClass α) := by
  intro F;
  simp [DeductionParameter.theory, System.theory, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  intro p hp;
  induction hp using Deduction.inducition_with_necOnly! with
  | hMaxm h => simp at h;
  | hMdp ihpq ihp => exact PLoN.ValidOnFrame.mdp ihpq ihp;
  | hNec ihp => exact PLoN.ValidOnFrame.nec ihp;
  | hOrElim => exact PLoN.ValidOnFrame.disj₃;
  | _ => simp_all [PLoN.Satisfies];


namespace Frame

variable (F : Frame α)

def SerialOnFormula (p : Formula α) : Prop := Serial (F.Rel' p)

def SerialOnTheory (T : Theory α) : Prop := ∀ p ∈ T, F.SerialOnFormula p

protected def Serial : Prop := ∀ p, F.SerialOnFormula p


def TransitiveOnFormula (p : Formula α) : Prop := ∀ {x y z : F.World}, x ≺[□p] y → y ≺[p] z → x ≺[p] z

def TransitiveOnTheory (T : Theory α) : Prop := ∀ p ∈ T, F.SerialOnFormula p

protected def Transitive (F : Frame α) := ∀ p, F.TransitiveOnFormula p

end Frame


open System

lemma validRosserRule_of_serial {p : Formula α} {F : PLoN.Frame α} (hSerial : F.SerialOnFormula p) (h : F ⊧ ~p) : F ⊧ ~(□p) := by
  intro V x;
  obtain ⟨y, hy⟩ := hSerial x;
  simp [Formula.PLoN.Satisfies];
  use y, hy;
  exact h V y;

lemma validAxiomFour_of_transitive {p : Formula α} {F : PLoN.Frame α} (hTrans : F.TransitiveOnFormula p) : F ⊧ Axioms.Four p := by
  dsimp [Axioms.Four];
  intro V x h y rxy z ryz;
  exact h (hTrans rxy ryz);


abbrev TransitiveFrameClass (α) : PLoN.FrameClass α := { F | Frame.Transitive F }

lemma TransitiveFrameClass.nonempty : (TransitiveFrameClass.{_, 0} α).Nonempty := by
  use terminalFrame α;
  simp [Frame.Transitive, Frame.TransitiveOnFormula];


abbrev SerialFrameClass (α) : PLoN.FrameClass α := { F | Frame.Serial F }

lemma SerialFrameClass.nonempty : (SerialFrameClass.{_, 0} α).Nonempty := by
  use terminalFrame α;
  intro p x; use x;


abbrev TransitiveSerialFrameClass (α) : PLoN.FrameClass α := { F | F.Transitive ∧ F.Serial }

lemma TransitiveSerialFrameClass.nonempty : (TransitiveSerialFrameClass.{_, 0} α).Nonempty := by
  use terminalFrame α;
  simp [Frame.Transitive, Frame.Serial, Frame.TransitiveOnFormula, Frame.SerialOnFormula];
  intro p x; use x;


lemma N4_characterized : 𝐍𝟒.CharacterizedByPLoNFrameClass (TransitiveFrameClass α) := by
  intro F;
  simp [DeductionParameter.theory, System.theory, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  intro hTrans p hp;
  induction hp using Deduction.inducition_with_necOnly! with
  | hMaxm h =>
    obtain ⟨p, e⟩ := h; subst e;
    exact validAxiomFour_of_transitive (hTrans p);
  | hMdp ihpq ihp => exact PLoN.ValidOnFrame.mdp ihpq ihp;
  | hNec ihp => exact PLoN.ValidOnFrame.nec ihp;
  | hOrElim => exact PLoN.ValidOnFrame.disj₃;
  | _ => simp_all [PLoN.Satisfies];

lemma NRosser_characterized : 𝐍(𝐑).CharacterizedByPLoNFrameClass (SerialFrameClass α) := by
  intro F;
  simp [DeductionParameter.theory, System.theory, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  intro hSerial p hp;
  induction hp using Deduction.inducition! with
  | hMaxm h => simp at h;
  | hMdp ihpq ihp => exact PLoN.ValidOnFrame.mdp ihpq ihp;
  | hRules rl hrl hant ih =>
    rcases hrl with (hNec | hRosser)
    . obtain ⟨p, e⟩ := hNec; subst e; simp_all;
      exact PLoN.ValidOnFrame.nec ih;
    . obtain ⟨p, e⟩ := hRosser; subst e; simp_all;
      exact validRosserRule_of_serial (hSerial _) ih;
  | hOrElim => exact PLoN.ValidOnFrame.disj₃;
  | _ => simp_all [PLoN.Satisfies];

-- TODO: `theory 𝐍𝟒 ∪ theory 𝐍(𝐑) = theory 𝐍𝟒(𝐑)`という事実を示せば共通部分だけで簡単に特徴づけられる気がする
lemma N4Rosser_characterized : 𝐍𝟒(𝐑).CharacterizedByPLoNFrameClass (TransitiveSerialFrameClass α) := by
  intro F;
  simp [DeductionParameter.theory, System.theory, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  intro hTrans hSerial p hp;
  induction hp using Deduction.inducition! with
  | hMaxm h =>
    obtain ⟨p, e⟩ := h; subst e;
    exact validAxiomFour_of_transitive (hTrans p);
  | hMdp ihpq ihp => exact PLoN.ValidOnFrame.mdp ihpq ihp;
  | hRules rl hrl hant ih =>
    rcases hrl with (hNec | hRosser)
    . obtain ⟨p, e⟩ := hNec; subst e; simp_all;
      exact PLoN.ValidOnFrame.nec ih;
    . obtain ⟨p, e⟩ := hRosser; subst e; simp_all;
      exact validRosserRule_of_serial (hSerial _) ih;
  | hOrElim => exact PLoN.ValidOnFrame.disj₃;
  | _ => simp_all [PLoN.Satisfies];

end PLoN

end LO.Modal.Standard
