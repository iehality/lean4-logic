import Logic.Logic.System
import Logic.Modal.LogicSymbol
import Logic.Logic.HilbertStyle.Basic

namespace LO

namespace System

namespace Axioms

variable {F : Type*} [LogicalConnective F] [StandardModalLogicalConnective F]
variable (p q r : F)

protected abbrev K := □(p ⟶ q) ⟶ □p ⟶ □q
abbrev K.set : Set F := { Axioms.K p q | (p) (q) }
notation "⟮K⟯" => K.set

protected abbrev T := □p ⟶ p
abbrev T.set : Set F := { Axioms.T p | (p) }
notation "⟮T⟯" => T.set

protected abbrev B := p ⟶ □◇p
abbrev B.set : Set F := { Axioms.B p | (p) }
notation "⟮B⟯" => B.set

protected abbrev D := □p ⟶ ◇p
abbrev D.set : Set F := { Axioms.D p | (p) }
notation "⟮D⟯" => D.set

protected abbrev Four := □p ⟶ □□p
abbrev Four.set : Set F := { Axioms.Four p | (p) }
notation "⟮4⟯" => Four.set

protected abbrev Five := ◇p ⟶ □◇p
abbrev Five.set : Set F := { Axioms.Five p | (p) }
notation "⟮5⟯" => Five.set

protected abbrev Dot2 := ◇□p ⟶ □◇p

protected abbrev C4 := □□p ⟶ □p

protected abbrev CD := ◇p ⟶ □p

protected abbrev Tc := p ⟶ □p
abbrev Tc.set : Set F := { Axioms.Tc p | (p) }
notation "⟮Tc⟯" => Tc.set

protected abbrev Ver := □p
abbrev Ver.set : Set F := { Axioms.Ver p | (p) }
notation "⟮Ver⟯" => Ver.set

protected abbrev Dot3 := □(□p ⟶ q) ⋎ □(□q ⟶ p)

protected abbrev Grz := □(□(p ⟶ □p) ⟶ p) ⟶ p

protected abbrev M := (□◇p ⟶ ◇□p)

protected abbrev L := □(□p ⟶ p) ⟶ □p
abbrev L.set : Set F := { Axioms.L p | (p) }
notation "⟮L⟯" => L.set

protected abbrev H := □(□p ⟷ p) ⟶ □p
abbrev H.set : Set F := { Axioms.H p | (p) }
notation "⟮H⟯" => H.set

end Axioms


section Systems

variable {S F : Type*} [LogicalConnective F] [StandardModalLogicalConnective F] [System F S]
variable (𝓢 : S)

class Necessitation where
  nec {p : F} : 𝓢 ⊢ p → 𝓢 ⊢ □p

class LoebRule where
  loeb {p : F} : 𝓢 ⊢ □p ⟶ p → 𝓢 ⊢ p

class HenkinRule where
  henkin {p : F} : 𝓢 ⊢ □p ⟷ p → 𝓢 ⊢ p

class HasAxiomK where
  K (p q : F) : 𝓢 ⊢ Axioms.K p q

class HasAxiomT where
  T (p : F) : 𝓢 ⊢ Axioms.T p

class HasAxiomD where
  D (p : F) : 𝓢 ⊢ Axioms.D p

class HasAxiomB where
  B (p : F) : 𝓢 ⊢ Axioms.B p

class HasAxiomFour where
  Four (p : F) : 𝓢 ⊢ Axioms.Four p

class HasAxiomFive where
  Five (p : F) : 𝓢 ⊢ Axioms.Five p

class HasAxiomL where
  L (p : F) : 𝓢 ⊢ Axioms.L p

class HasAxiomDot2 where
  Dot2 (p : F) : 𝓢 ⊢ Axioms.Dot2 p

class HasAxiomDot3 where
  Dot3 (p q : F) : 𝓢 ⊢ Axioms.Dot3 p q

class HasAxiomGrz where
  Grz (p : F) : 𝓢 ⊢ Axioms.Grz p

class HasAxiomTc where
  Tc (p : F) : 𝓢 ⊢ Axioms.Tc p

class HasAxiomVer where
  Ver (p : F) : 𝓢 ⊢ Axioms.Ver p

class HasAxiomH where
  H (p : F) : 𝓢 ⊢ Axioms.H p


protected class K extends System.Classical 𝓢, Necessitation 𝓢, HasAxiomK 𝓢

protected class KT extends System.K 𝓢, HasAxiomT 𝓢

protected class KD extends System.K 𝓢, HasAxiomD 𝓢

protected class K4 extends System.K 𝓢, HasAxiomFour 𝓢

protected class S4 extends System.K 𝓢, HasAxiomT 𝓢, HasAxiomFour 𝓢

protected class S5 extends System.K 𝓢, HasAxiomT 𝓢, HasAxiomFive 𝓢

protected class S4Dot2 extends System.S4 𝓢, HasAxiomDot2 𝓢

protected class S4Dot3 extends System.S4 𝓢, HasAxiomDot3 𝓢

protected class S4Grz extends System.S4 𝓢, HasAxiomGrz 𝓢

protected class GL extends System.K 𝓢, HasAxiomL 𝓢

protected class Triv extends System.K 𝓢, HasAxiomT 𝓢, HasAxiomTc 𝓢

protected class Ver extends System.K 𝓢, HasAxiomVer 𝓢

protected class K4H extends System.K4 𝓢, HasAxiomH 𝓢

protected class K4Loeb extends System.K4 𝓢, LoebRule 𝓢

protected class K4Henkin extends System.K4 𝓢, HenkinRule 𝓢

end Systems


end System


namespace DeductionSystem

open System.Axioms

variable {S F : Type*} [LogicalConnective F] [StandardModalLogicalConnective F] [System F S]

structure Rule (F) where
  antecedents : List F
  consequence  : F

abbrev Rules (F) := Set (Rule F)

inductive Deduction (𝓡 : Rules F) : F → Type _
  | rule {rl}     : rl ∈ 𝓡 → (∀ {p}, p ∈ rl.antecedents → Deduction 𝓡 p) → Deduction 𝓡 rl.consequence

instance : System F (Rules F) := ⟨Deduction⟩

namespace Deduction

variable {𝓡 𝓡₁ 𝓡₂ : Rules F}

noncomputable def inducition!
  {motive : (p : F) → 𝓡 ⊢! p → Sort*}
  (rule   : (r : Rule F) → (hr : r ∈ 𝓡) →
            (hant : ∀ {p}, p ∈ r.antecedents → 𝓡 ⊢! p) →
            (ih : ∀ {p}, (hp : p ∈ r.antecedents) →
            motive p (hant hp)) → motive r.consequence ⟨rule hr (λ hp => (hant hp).some)⟩)
  : ∀ {p}, (d : 𝓡 ⊢! p) → motive p d := by
  intro p d;
  induction d.some with
  | rule hr h ih => apply rule _ hr; intro p hp; exact ih hp ⟨h hp⟩;

lemma reducible (h : 𝓡₁ ⊆ 𝓡₂ := by aesop) : 𝓡₁ ≤ₛ 𝓡₂ := by
  intro p hp; simp_all [System.theory];
  induction hp using inducition! with
  | rule _ hr _ ih => exact ⟨rule (h hr) (λ hp => (ih hp).some)⟩;

end Deduction

namespace Axioms

variable (p q r : F)

section Propositional

protected abbrev Verum : F := ⊤
abbrev Verum.set : Set F := { Axioms.Verum }
notation:max "⟮⊤⟯" => Verum.set

protected abbrev Imply₁ := p ⟶ q ⟶ p
abbrev Imply₁.set : Set F := { Axioms.Imply₁ p q | (p) (q) }
notation:max "⟮⟶₁⟯" => Imply₁.set

protected abbrev Imply₂ := (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
abbrev Imply₂.set : Set F := { Axioms.Imply₂ p q r | (p) (q) (r) }
notation:max "⟮⟶₂⟯" => Imply₂.set

protected abbrev AndElim₁ := p ⋏ q ⟶ p
abbrev AndElim₁.set : Set F := { Axioms.AndElim₁ p q | (p) (q) }
notation:max "⟮⋏E₁⟯" => AndElim₁.set

protected abbrev AndElim₂ := p ⋏ q ⟶ q
abbrev AndElim₂.set : Set F := { Axioms.AndElim₂ p q | (p) (q) }
notation:max "⟮⋏E₂⟯" => AndElim₂.set

-- abbrev AndElim.set : Set F := ⟮⋏E₁⟯ ∪ ⟮⋏E₂⟯
-- notation:max "⟮⋏E⟯" => AndElim.set

protected abbrev AndInst := p ⟶ q ⟶ p ⋏ q
abbrev AndInst.set : Set F := { Axioms.AndInst p q | (p) (q) }
notation:max "⟮⋏I⟯" => AndInst.set

protected abbrev OrInst₁ := p ⟶ p ⋎ q
abbrev OrInst₁.set : Set F := { Axioms.OrInst₁ p q | (p) (q) }
notation:max "⟮⋎I₁⟯" => OrInst₁.set

protected abbrev OrInst₂ := q ⟶ p ⋎ q
abbrev OrInst₂.set : Set F := { Axioms.OrInst₂ p q | (p) (q) }
notation:max "⟮⋎I₂⟯" => OrInst₂.set

-- abbrev OrInst.set : Set F := ⟮⋎I₁⟯ ∪ ⟮⋎I₂⟯
-- notation:max "⟮⋎I⟯" => OrInst.set

protected abbrev OrElim := (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)
abbrev OrElim.set : Set F := { Axioms.OrElim p q r | (p) (q) (r) }
notation:max "⟮⋎E⟯" => OrElim.set

protected abbrev NegEquiv := ~p ⟷ p ⟶ ⊥
abbrev NegEquiv.set : Set F := { Axioms.NegEquiv p | (p) }
notation:max "⟮~⟯" => NegEquiv.set

protected abbrev EFQ := ⊥ ⟶ p
abbrev EFQ.set : Set F := { Axioms.EFQ p | (p) }
notation:max "⟮EFQ⟯" => EFQ.set

protected abbrev LEM := p ⋎ ~p
abbrev LEM.set : Set F := { Axioms.LEM p | (p) }
notation:max "⟮LEM⟯" => LEM.set

protected abbrev WeakLEM := ~p ⋎ ~~p
abbrev WeakLEM.set : Set F := { Axioms.WeakLEM p | (p) }
notation:max "⟮WEM⟯" => WeakLEM.set

protected abbrev GD := (p ⟶ q) ⋎ (q ⟶ p)
abbrev GD.set : Set F := { Axioms.GD p q | (p) (q) }

protected abbrev DNE := ~~p ⟶ p
abbrev DNE.set : Set F := { Axioms.DNE p | (p) }
notation:max "⟮DNE⟯" => DNE.set

protected abbrev Peirce := ((p ⟶ q) ⟶ p) ⟶ p
abbrev Peirce.set : Set F := { Axioms.Peirce p q | (p) (q) }

end Propositional


section Modal

end Modal

end Axioms


namespace InferenceRules

abbrev Init (Ax : Set F) : Rules F := { ⟨[], p⟩ | (p ∈ Ax) }
postfix:max "ⁱ" => Init

abbrev ModusPonens : Rules F := { ⟨[p, p ⟶ q], q⟩ | (p) (q) }
notation:max "⟮MP⟯" => ModusPonens

abbrev Necessitation : Rules F := { ⟨[p], □p⟩ | (p) }
notation:max "⟮Nec⟯" => Necessitation

abbrev LoebRule : Rules F := { ⟨[□p ⟶ p], p⟩ | (p) }
notation:max "⟮Loeb⟯" => LoebRule

abbrev HenkinRule : Rules F := { ⟨[□p ⟷ p], p⟩ | (p) }
notation:max "⟮Henkin⟯" => HenkinRule

end InferenceRules

variable {𝓡 : Rules F}

open InferenceRules (Init)

abbrev MinimalPropositional : Rules F := ⟮⊤⟯ⁱ ∪ ⟮⟶₁⟯ⁱ ∪ ⟮⟶₂⟯ⁱ ∪ ⟮⋏E₁⟯ⁱ ∪ ⟮⋏E₂⟯ⁱ ∪ ⟮⋏I⟯ⁱ ∪ ⟮⋎E⟯ⁱ ∪ ⟮⋎I₁⟯ⁱ ∪ ⟮⋎I₂⟯ⁱ ∪ ⟮~⟯ⁱ ∪ ⟮MP⟯
notation:max "𝐦𝐏𝐋" => MinimalPropositional

instance instModusPonens (h : ⟮MP⟯ ⊆ 𝓡) : System.ModusPonens 𝓡 where
  mdp := by
    intro p q hpq hp;
    have h : ⟨[p, p ⟶ q], q⟩ ∈ 𝓡 := by apply h; simp;
    exact Deduction.rule h (by
      rintro r hr; simp at hr;
      sorry;
    );

instance instHasVerum (h : ⟮⊤⟯ⁱ ⊆ 𝓡) : System.HasVerum 𝓡 where
  verum := by exact Deduction.rule (show ⟨[], Axioms.Verum⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasImply₁ (h : ⟮⟶₁⟯ⁱ ⊆ 𝓡) : System.HasImply₁ 𝓡 where
  imply₁ := by intro p q; exact Deduction.rule (show ⟨[], Axioms.Imply₁ p q⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasImply₂ (h : ⟮⟶₂⟯ⁱ ⊆ 𝓡) : System.HasImply₂ 𝓡 where
  imply₂ := by intro p q r; exact Deduction.rule (show ⟨[], Axioms.Imply₂ p q r⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasAnd₁ (h : ⟮⋏E₁⟯ⁱ ⊆ 𝓡) : System.HasAnd₁ 𝓡 where
  and₁ := by intro p q; exact Deduction.rule (show ⟨[], Axioms.AndElim₁ p q⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasAnd₂ (h : ⟮⋏E₂⟯ⁱ ⊆ 𝓡) : System.HasAnd₂ 𝓡 where
  and₂ := by intro p q; exact Deduction.rule (show ⟨[], Axioms.AndElim₂ p q⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasAnd₃ (h : ⟮⋏I⟯ⁱ ⊆ 𝓡) : System.HasAnd₃ 𝓡 where
  and₃ := by intro p q; exact Deduction.rule (show ⟨[], Axioms.AndInst p q⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasOr₁ (h : ⟮⋎I₁⟯ⁱ ⊆ 𝓡) : System.HasOr₁ 𝓡 where
  or₁ := by intro p q; exact Deduction.rule (show ⟨[], Axioms.OrInst₁ p q⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasOr₂ (h : ⟮⋎I₂⟯ⁱ ⊆ 𝓡) : System.HasOr₂ 𝓡 where
  or₂ := by intro p q; exact Deduction.rule (show ⟨[], Axioms.OrInst₂ p q⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasOr₃ (h : ⟮⋎E⟯ⁱ ⊆ 𝓡) : System.HasOr₃ 𝓡 where
  or₃ := by intro p q r; exact Deduction.rule (show ⟨[], Axioms.OrElim p q r⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasEFQ (h : ⟮EFQ⟯ⁱ ⊆ 𝓡) : System.HasEFQ 𝓡 where
  efq := by intro p; exact Deduction.rule (show ⟨[], Axioms.EFQ p⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasDNE (h : ⟮DNE⟯ⁱ ⊆ 𝓡) : System.HasDNE 𝓡 where
  dne := by intro p; exact Deduction.rule (show ⟨[], Axioms.DNE p⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instMinimal (h : 𝐦𝐏𝐋 ⊆ 𝓡) : System.Minimal 𝓡 where
  mdp    := instModusPonens (by simp_all) |>.mdp;
  verum  := instHasVerum    (by simp_all) |>.verum;
  imply₁ := instHasImply₁   (by simp_all) |>.imply₁;
  imply₂ := instHasImply₂   (by simp_all) |>.imply₂;
  and₁   := instHasAnd₁     (by simp_all) |>.and₁;
  and₂   := instHasAnd₂     (by simp_all) |>.and₂;
  and₃   := instHasAnd₃     (by simp_all) |>.and₃;
  or₁    := instHasOr₁      (by simp_all) |>.or₁;
  or₂    := instHasOr₂      (by simp_all) |>.or₂;
  or₃    := instHasOr₃      (by simp_all) |>.or₃;

instance : System.Minimal (𝐦𝐏𝐋 : Rules F) := instMinimal (by rfl)


abbrev IntuitionisticPropositional : Rules F := 𝐦𝐏𝐋 ∪ ⟮EFQ⟯ⁱ
notation:max "𝐢𝐏𝐋" => IntuitionisticPropositional

instance instIntuitionistic (h : 𝐢𝐏𝐋 ⊆ 𝓡) : System.Intuitionistic 𝓡 := by
  have : System.Minimal 𝓡 := instMinimal (by aesop);
  have : System.HasEFQ 𝓡 := instHasEFQ (by aesop);
  exact ⟨⟩;

instance : System.Intuitionistic (𝐢𝐏𝐋 : Rules F) := instIntuitionistic (by rfl)


abbrev ClassicalPropositional : Rules F := 𝐦𝐏𝐋 ∪ ⟮DNE⟯ⁱ
notation:max "𝐏𝐋" => ClassicalPropositional

instance instClassical (h : 𝐏𝐋 ⊆ 𝓡) : System.Classical 𝓡 := by
  have : System.Minimal 𝓡 := instMinimal (by aesop);
  have : System.HasDNE 𝓡 := instHasDNE (by aesop);
  exact ⟨⟩;

instance : System.Classical (𝐏𝐋 : Rules F) := instClassical (by rfl)


instance instNecessitation (h : ⟮Nec⟯ ⊆ 𝓡) : System.Necessitation 𝓡 where
  nec := by
    intro p hp;
    have h : ⟨[p], □p⟩ ∈ 𝓡 := by aesop;
    exact Deduction.rule h (by intro q hq; simp at hq; subst hq; assumption);

instance instLoebRule (h : ⟮Loeb⟯ ⊆ 𝓡) : System.LoebRule 𝓡 where
  loeb := by
    intro p hp;
    have h : ⟨[□p ⟶ p], p⟩ ∈ 𝓡 := by aesop;
    exact Deduction.rule h (by intro q hq; simp at hq; subst hq; assumption);

instance instHenkinRule (h : ⟮Henkin⟯ ⊆ 𝓡) : System.HenkinRule 𝓡 where
  henkin := by
    intro p hp;
    have h : ⟨[□p ⟷ p], p⟩ ∈ 𝓡 := by aesop;
    exact Deduction.rule h (by intro q hq; simp at hq; subst hq; assumption);

instance instHasAxiomK (h : ⟮K⟯ⁱ ⊆ 𝓡) : System.HasAxiomK 𝓡 where
  K := by intro p q; exact Deduction.rule (show ⟨[], Axioms.K p q⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasAxiomFour (h : ⟮4⟯ⁱ ⊆ 𝓡) : System.HasAxiomFour 𝓡 where
  Four := by intro p; exact Deduction.rule (show ⟨[], Axioms.Four p⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasAxiomFive (h : ⟮5⟯ⁱ ⊆ 𝓡) : System.HasAxiomFive 𝓡 where
  Five := by intro p; exact Deduction.rule (show ⟨[], Axioms.Five p⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasAxiomL (h : ⟮L⟯ⁱ ⊆ 𝓡) : System.HasAxiomL 𝓡 where
  L := by intro p; exact Deduction.rule (show ⟨[], Axioms.L p⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasAxiomH (h : ⟮H⟯ⁱ ⊆ 𝓡) : System.HasAxiomH 𝓡 where
  H := by intro p; exact Deduction.rule (show ⟨[], Axioms.H p⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasAxiomT (h : ⟮T⟯ⁱ ⊆ 𝓡) : System.HasAxiomT 𝓡 where
  T := by intro p; exact Deduction.rule (show ⟨[], Axioms.T p⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasAxiomVer (h : ⟮Ver⟯ⁱ ⊆ 𝓡) : System.HasAxiomVer 𝓡 where
  Ver := by intro p; exact Deduction.rule (show ⟨[], Axioms.Ver p⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

instance instHasAxiomTc (h : ⟮Tc⟯ⁱ ⊆ 𝓡) : System.HasAxiomTc 𝓡 where
  Tc := by intro p; exact Deduction.rule (show ⟨[], Axioms.Tc p⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

abbrev ModalK : Rules F := 𝐏𝐋 ∪ ⟮K⟯ⁱ ∪ ⟮Nec⟯
notation:max "𝐊" => ModalK

instance instK (h : 𝐊 ⊆ 𝓡) : System.K 𝓡 := by
  have : System.Classical 𝓡 := instClassical (by aesop);
  have : System.Necessitation 𝓡 := instNecessitation (by aesop);
  have : System.HasAxiomK 𝓡 := instHasAxiomK (by aesop);
  exact ⟨⟩;

instance : System.K (𝐊 : Rules F) := instK (by rfl)


abbrev ModalKT : Rules F := 𝐊 ∪ ⟮T⟯ⁱ
notation:max "𝐊𝐓" => ModalKT

instance instKT (h : 𝐊𝐓 ⊆ 𝓡) : System.KT 𝓡 := by
  have : System.K 𝓡 := instK (by aesop);
  have : System.HasAxiomT 𝓡 := instHasAxiomT (by aesop);
  exact ⟨⟩;

instance : System.KT (𝐊𝐓 : Rules F) := instKT (by rfl)


abbrev ModalK4 : Rules F := 𝐊 ∪ ⟮4⟯ⁱ
notation:max "𝐊𝟒" => ModalK4

instance instK4 (h : 𝐊𝟒 ⊆ 𝓡) : System.K4 𝓡 := by
  have : System.K 𝓡 := instK (by aesop);
  have : System.HasAxiomFour 𝓡 := instHasAxiomFour (by aesop);
  exact ⟨⟩;

instance : System.K4 (𝐊𝟒 : Rules F) := instK4 (by rfl)


abbrev ModalS4 : Rules F := 𝐊 ∪ ⟮T⟯ⁱ ∪ ⟮4⟯ⁱ
notation:max "𝐒𝟒" => ModalS4

instance instS4 (h : 𝐒𝟒 ⊆ 𝓡) : System.S4 𝓡 := by
  have : System.KT 𝓡 := instKT (by aesop);
  have : System.HasAxiomFour 𝓡 := instHasAxiomFour (by aesop);
  exact ⟨⟩;

instance : System.S4 (𝐒𝟒 : Rules F) := instS4 (by rfl)


abbrev ModalS5 : Rules F := 𝐊 ∪ ⟮T⟯ⁱ ∪ ⟮5⟯ⁱ
notation:max "𝐒𝟓" => ModalS5

instance instS5 (h : 𝐒𝟓 ⊆ 𝓡) : System.S5 𝓡 := by
  have : System.KT 𝓡 := instKT (by aesop);
  have : System.HasAxiomFive 𝓡 := instHasAxiomFive (by aesop);
  exact ⟨⟩;

instance : System.S5 (𝐒𝟓 : Rules F) := instS5 (by rfl)


abbrev Triv : Rules F := 𝐊 ∪ ⟮T⟯ⁱ ∪ ⟮Tc⟯ⁱ
notation:max "𝐓𝐫𝐢𝐯" => Triv

instance instTriv (h : 𝐓𝐫𝐢𝐯 ⊆ 𝓡) : System.Triv 𝓡 := by
  have : System.KT 𝓡 := instKT (by aesop);
  have : System.HasAxiomTc 𝓡 := instHasAxiomTc (by aesop);
  exact ⟨⟩;


abbrev Ver : Rules F := 𝐊 ∪ ⟮Ver⟯ⁱ
notation:max "𝐕𝐞𝐫" => Ver

instance instVer (h : 𝐕𝐞𝐫 ⊆ 𝓡) : System.Ver 𝓡 := by
  have : System.K 𝓡 := instK (by aesop);
  have : System.HasAxiomVer 𝓡 := instHasAxiomVer (by aesop);
  exact ⟨⟩;

instance : System.Ver (𝐕𝐞𝐫 : Rules F) := instVer (by rfl)


abbrev GL : Rules F := 𝐊 ∪ ⟮L⟯ⁱ
notation:max "𝐆𝐋" => GL

instance instGL (h : 𝐆𝐋 ⊆ 𝓡) : System.GL 𝓡 := by
  have : System.K 𝓡 := instK (by aesop);
  have : System.HasAxiomL 𝓡 := instHasAxiomL (by aesop);
  exact ⟨⟩;

instance : System.GL (𝐆𝐋 : Rules F) := instGL (by rfl)


abbrev K4H : Rules F := 𝐊 ∪ ⟮4⟯ⁱ ∪ ⟮H⟯ⁱ
notation:max "𝐊𝟒𝐇" => K4H

instance instK4H (h : 𝐊𝟒𝐇 ⊆ 𝓡) : System.K4H 𝓡 := by
  have : System.K4 𝓡 := instK4 (by aesop);
  have : System.HasAxiomH 𝓡 := instHasAxiomH (by aesop);
  exact ⟨⟩;

instance : System.K4H (𝐊𝟒𝐇 : Rules F) := instK4H (by rfl)


abbrev K4Loeb : Rules F := 𝐊 ∪ ⟮4⟯ⁱ ∪ ⟮Loeb⟯
notation:max "𝐊𝟒(𝐋)" => K4Loeb

instance instK4Loeb (h : 𝐊𝟒(𝐋) ⊆ 𝓡) : System.K4Loeb 𝓡 := by
  have : System.K4 𝓡 := instK4 (by aesop);
  have : System.LoebRule 𝓡 := instLoebRule (by aesop);
  exact ⟨⟩;

instance : System.K4Loeb (𝐊𝟒(𝐋) : Rules F) := instK4Loeb (by rfl)

abbrev K4Henkin : Rules F := 𝐊 ∪ ⟮4⟯ⁱ ∪ ⟮Henkin⟯
notation:max "𝐊𝟒(𝐇)" => K4Henkin

instance instK4Henkin (h : 𝐊𝟒(𝐇) ⊆ 𝓡) : System.K4Henkin 𝓡 := by
  have : System.K4 𝓡 := instK4 (by aesop);
  have : System.HenkinRule 𝓡 := instHenkinRule (by aesop);
  exact ⟨⟩;

instance : System.K4Henkin (𝐊𝟒(𝐇) : Rules F) := instK4Henkin (by rfl)


section Reducible

open System


lemma reducible_K4_S4 : (𝐊𝟒 : Rules F) ≤ₛ 𝐒𝟒 := Deduction.reducible

end Reducible

end DeductionSystem

/-
namespace Modal.Standard

open DeductionSystem

open System

lemma reducible_K4_S4 : (𝐊𝟒 : Rules (Formula α)) ≤ₛ 𝐒𝟒 := Deduction.reducible

lemma reducible_GL_K4Loeb : (𝐆𝐋 : Rules (Formula α)) ≤ₛ 𝐊𝟒(𝐋) := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | rule r hr hant ih =>
    rcases hr with ((hPL | hL) | hNec) | hL;
    . sorry;
    . obtain ⟨_, ⟨q, _, _⟩, e⟩ := hL; subst_vars; simp;
    . obtain ⟨p, e⟩ := hNec; subst_vars;
      exact nec! $ ih (by simp);
    . obtain ⟨_, ⟨q, _, _⟩, e⟩ := hL; subst_vars;
      simp; sorry;

end Modal.Standard
-/

/-
namespace Modal.Standard

variable {α} [DecidableEq α]

structure Rule (α) where
  antecedents : List (Formula α)
  consequence  : Formula α

abbrev Rules (α) := Set (Rule α)

inductive Deduction (𝓡 : Rules α) : (Formula α) → Type _
  | rule {r}     : r ∈ 𝓡 → (∀ {p}, p ∈ r.antecedents → Deduction 𝓡 p) → Deduction 𝓡 r.consequence
  | mdp {p q}    : Deduction 𝓡 (p ⟶ q) → Deduction 𝓡 p → Deduction 𝓡 q
  | verum        : Deduction 𝓡 ⊤
  | imply₁ p q   : Deduction 𝓡 (p ⟶ q ⟶ p)
  | imply₂ p q r : Deduction 𝓡 ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | and₁ p q     : Deduction 𝓡 (p ⋏ q ⟶ p)
  | and₂ p q     : Deduction 𝓡 (p ⋏ q ⟶ q)
  | and₃ p q     : Deduction 𝓡 (p ⟶ q ⟶ p ⋏ q)
  | or₁ p q      : Deduction 𝓡 (p ⟶ p ⋎ q)
  | or₂ p q      : Deduction 𝓡 (q ⟶ p ⋎ q)
  | or₃ p q r    : Deduction 𝓡 ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | dne p        : Deduction 𝓡 (~~p ⟶ p)



namespace Deduction

instance : System (Formula α) (Rules α) := ⟨Deduction⟩

variable {𝓡 𝓡₁ 𝓡₂: Rules α}

instance : System.Classical 𝓡 where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  and₁ := and₁
  and₂ := and₂
  and₃ := and₃
  or₁ := or₁
  or₂ := or₂
  or₃ := or₃
  dne := dne

noncomputable def inducition!
  {motive : (p : Formula α) → 𝓡 ⊢! p → Sort*}
  (rule   : {r : Rule α} → (hr : r ∈ 𝓡) → (hant : ∀ {p}, p ∈ r.antecedents → 𝓡 ⊢! p)
             → (ih : ∀ {p}, (hp : p ∈ r.antecedents) → motive p (hant hp)) → motive r.consequence ⟨rule hr (λ hp => (hant hp).some)⟩)
  (mdp    : ∀ {p q}, {hpq : 𝓡 ⊢! p ⟶ q} → {hp : 𝓡 ⊢! p} → (ihpq : motive (p ⟶ q) hpq) → (ihq : motive p hp) → motive q ⟨mdp hpq.some hp.some⟩)
  (verum  : motive ⊤ ⟨verum⟩)
  (imply₁ : ∀ {p q}, motive (p ⟶ q ⟶ p) $ ⟨imply₁ p q⟩)
  (imply₂ : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ ⟨imply₂ p q r⟩)
  (and₁   : ∀ {p q}, motive (p ⋏ q ⟶ p) $ ⟨and₁ p q⟩)
  (and₂   : ∀ {p q}, motive (p ⋏ q ⟶ q) $ ⟨and₂ p q⟩)
  (and₃   : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ ⟨and₃ p q⟩)
  (or₁    : ∀ {p q}, motive (p ⟶ p ⋎ q) $ ⟨or₁ p q⟩)
  (or₂    : ∀ {p q}, motive (q ⟶ p ⋎ q) $ ⟨or₂ p q⟩)
  (or₃    : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ ⟨or₃ p q r⟩)
  (dne    : ∀ {p}, motive (~~p ⟶ p) $ ⟨dne p⟩)
  : ∀ {p}, (d : 𝓡 ⊢! p) → motive p d := by
  intro p d;
  induction d.some with
  | rule hr h ih => apply rule hr; intro p hp; exact ih hp ⟨h hp⟩;
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | _ => aesop

open System

lemma reducible (h : 𝓡₁ ⊆ 𝓡₂ := by aesop) : 𝓡₁ ≤ₛ 𝓡₂ := by
  intro p hp; simp_all [System.theory];
  induction hp using Deduction.inducition! with
  | rule hr _ ih => exact ⟨rule (h hr) (λ hp => (ih hp).some)⟩;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | verum => exact verum!;
  | imply₁ => exact imply₁!;
  | imply₂ => exact imply₂!;
  | and₁ => exact and₁!;
  | and₂ => exact and₂!;
  | and₃ => exact and₃!;
  | or₁ => exact or₁!;
  | or₂ => exact or₂!;
  | or₃ => exact or₃!;
  | dne => exact dne!


abbrev NecRule {α} : Rules α := { ⟨[p], □p⟩ | (p : Formula α) }
notation:max "⟮Nec⟯" => NecRule

class SubsetNec (𝓡 : Rules α) where
  nec : ⟮Nec⟯ ⊆ 𝓡 := by aesop

instance [h : SubsetNec 𝓡] : System.Necessitation 𝓡 where
  nec := by intro p hp; exact rule (show ⟨[p], □p⟩ ∈ 𝓡 by apply h.nec; simp_all) (by intros; simp_all; apply hp);


abbrev LoebRule {α} : Rules α := { ⟨[□p ⟶ p], p⟩ | (p : Formula α) }
notation:max "⟮Loeb⟯" => LoebRule

class SubsetLoeb (𝓡 : Rules α) where
  loeb : ⟮Loeb⟯ ⊆ 𝓡 := by aesop

instance [h : SubsetLoeb 𝓡] : System.LoebRule 𝓡 where
  loeb := by intro p hp; exact rule (show ⟨[□p ⟶ p], p⟩ ∈ 𝓡 by apply h.loeb; simp_all) (by intros; simp_all; apply hp);


abbrev HenkinRule {α} : Rules α := { ⟨[□p ⟷ p], p⟩ | (p : Formula α) }
notation:max "⟮Henkin⟯" => HenkinRule

class SubsetHenkin (𝓡 : Rules α) where
  henkin : ⟮Henkin⟯ ⊆ 𝓡 := by aesop

instance [h : SubsetHenkin 𝓡] : System.HenkinRule 𝓡 where
  henkin := by intro p hp; exact rule (show ⟨[□p ⟷ p], p⟩ ∈ 𝓡 by apply h.henkin; simp_all) (by intros; simp_all; apply hp);



abbrev AxiomRule (Ax : AxiomSet α) : Rules α := { ⟨_, p⟩ | (p : Formula α) ∈ Ax }
notation:max "⟮" Ax "⟯" => AxiomRule Ax

class SubsetAxiomK (𝓡 : Rules α) where
  axiomK : ⟮𝗞⟯ ⊆ 𝓡 := by aesop

instance [h : SubsetAxiomK 𝓡] : System.HasAxiomK 𝓡 where
  K := by intro p q; exact rule (show ⟨[], Axioms.K p q⟩ ∈ 𝓡 by apply h.axiomK; simp_all) (by intros; simp_all);


/-


class SubsetAxiomT (𝓡 : Rules α) where
  axiomT : ⟮𝗧⟯ ⊆ 𝓡 := by aesop

instance [h : SubsetAxiomT 𝓡] : System.HasAxiomT 𝓡 where
  T := by intro p; exact rule (show ⟨[], Axioms.T p⟩ ∈ 𝓡 by apply h.axiomT; simp_all) (by intros; simp_all);


class SubsetAxiomFour (𝓡 : Rules α) where
  axiomFour : ⟮𝟒⟯ ⊆ 𝓡 := by aesop

instance [h : SubsetAxiomFour 𝓡] : System.HasAxiomFour 𝓡 where
  Four := by intro p; exact rule (show ⟨[], Axioms.Four p⟩ ∈ 𝓡 by apply h.axiomFour; simp_all) (by intros; simp_all);


class SubsetAxiomL (𝓡 : Rules α) where
  axiomL : ⟮𝗟⟯ ⊆ 𝓡 := by aesop

instance [h : SubsetAxiomL 𝓡] : System.HasAxiomL 𝓡 where
  L := by intro p; exact rule (show ⟨[], Axioms.L p⟩ ∈ 𝓡 by apply h.axiomL; simp_all) (by intros; simp_all);


class SubsetAxiomH (𝓡 : Rules α) where
  axiomH : ⟮𝗛⟯ ⊆ 𝓡 := by aesop

instance [h : SubsetAxiomH 𝓡] : System.HasAxiomH 𝓡 where
  H := by intro p; exact rule (show ⟨[], Axioms.H p⟩ ∈ 𝓡 by apply h.axiomH; simp_all) (by intros; simp_all);
-/

end Deduction

open Deduction

protected abbrev K : Rules α := ⟮𝗞⟯ ∪ ⟮Nec⟯
notation:max "𝐊" => Standard.K
instance : SubsetNec (α := α) 𝐊 where


def mkNormal (Ax : AxiomSet α) : Rules α := ⟮𝗞 ∪ Ax⟯ ∪ ⟮Nec⟯
prefix:max "𝝂" => mkNormal

instance {Ax : AxiomSet α} : SubsetNec 𝝂(Ax) where
  nec := by simp [mkNormal];

instance {Ax : AxiomSet α} : SubsetAxiomK 𝝂(Ax) where
  axiomK := by
    apply Set.subset_union_left;
    apply Set.subset_union_left;
    intro r hR; obtain ⟨p, q, e⟩ := hR;





protected abbrev KT : Rules α := 𝝂(𝗧)
notation:max "𝐊𝐓" => Standard.KT
instance : SubsetNec (α := α) 𝐊𝐓 where


protected abbrev KD : Rules α := 𝝂(𝗗)
notation:max "𝐊𝐃" => Standard.KD
instance : SubsetNec (α := α) 𝐊𝐃 where


protected abbrev K4 : Rules α := 𝝂(𝟒)
notation:max "𝐊𝟒" => Standard.K4
instance : SubsetAxiomK (α := α) 𝐊𝟒 where
instance : SubsetAxiomFour (α := α) 𝐊𝟒 where
instance : SubsetNec (α := α) 𝐊𝟒 where


protected abbrev K5 : Rules α := 𝝂(𝟱)
notation:max "𝐊𝟓" => Standard.K5
instance : SubsetAxiomK (α := α) 𝐊𝟓 where
instance : SubsetNec (α := α) 𝐊𝟓 where


protected abbrev S4 : Rules α := 𝝂(𝗧 ∪ 𝟒)
notation:max "𝐒𝟒" => Standard.S4
instance : SubsetAxiomK (α := α) 𝐒𝟒 where
instance : SubsetAxiomFour (α := α) 𝐒𝟒 where
instance : SubsetNec (α := α) 𝐒𝟒 where


protected abbrev S5 : Rules α :=  𝝂(𝗧 ∪ 𝟱)
notation:max "𝐒𝟓" => Standard.S5
instance : SubsetNec (α := α) 𝐒𝟓 where
instance : SubsetAxiomK (α := α) 𝐒𝟓 where


protected abbrev GL : Rules α := 𝝂(𝗟)
notation:max "𝐆𝐋" => Standard.GL
instance : SubsetAxiomK (α := α) 𝐆𝐋 where
instance : SubsetAxiomL (α := α) 𝐆𝐋 where
instance : SubsetNec (α := α) 𝐆𝐋 where
instance : System.GL (𝐆𝐋 : Rules α) where


protected abbrev K4H : Rules α := 𝝂(𝟒 ∪ 𝗛)
notation:max "𝐊𝟒𝐇" => Standard.K4H
instance : SubsetAxiomK (α := α) 𝐊𝟒𝐇 where
instance : SubsetAxiomFour (α := α) 𝐊𝟒𝐇 where
instance : SubsetAxiomH (α := α) 𝐊𝟒𝐇 where
instance : SubsetNec (α := α) 𝐊𝟒𝐇 where
instance : System.K4H (𝐊𝟒𝐇 : Rules α) where


protected abbrev K4Loeb : Rules α := ⟮𝗞 ∪ 𝟒⟯ ∪ ⟮Nec⟯ ∪ ⟮Loeb⟯
notation:max "𝐊𝟒(𝐋)" => Standard.K4Loeb
instance : SubsetAxiomK (α := α) 𝐊𝟒(𝐋) where
instance : SubsetAxiomFour (α := α) 𝐊𝟒(𝐋) where
instance : SubsetNec (α := α) 𝐊𝟒(𝐋) where
instance : SubsetLoeb (α := α) 𝐊𝟒(𝐋) where
instance : System.K4Loeb (𝐊𝟒(𝐋) : Rules α) where


protected abbrev K4Henkin : Rules α := ⟮𝗞 ∪ 𝟒⟯ ∪ ⟮Nec⟯ ∪ ⟮Henkin⟯
notation:max "𝐊𝟒(𝐇)" => Standard.K4Henkin
instance : SubsetNec (α := α) 𝐊𝟒(𝐇) where
instance : SubsetHenkin (α := α) 𝐊𝟒(𝐇) where
instance : SubsetAxiomK (α := α) 𝐊𝟒(𝐇) where
instance : SubsetAxiomFour (α := α) 𝐊𝟒(𝐇) where
instance : System.K4Henkin (𝐊𝟒(𝐇) : Rules α) where

macro_rules | `(tactic| trivial) => `(tactic| apply System.verum!)
macro_rules | `(tactic| trivial) => `(tactic| apply System.imply₁!)
macro_rules | `(tactic| trivial) => `(tactic| apply System.imply₂!)
macro_rules | `(tactic| trivial) => `(tactic| apply System.and₁!)
macro_rules | `(tactic| trivial) => `(tactic| apply System.and₂!)
macro_rules | `(tactic| trivial) => `(tactic| apply System.and₃!)
macro_rules | `(tactic| trivial) => `(tactic| apply System.or₁!)
macro_rules | `(tactic| trivial) => `(tactic| apply System.or₂!)
macro_rules | `(tactic| trivial) => `(tactic| apply System.or₃!)
macro_rules | `(tactic| trivial) => `(tactic| apply System.dne!)

section Reducible

lemma reducible_K_KT : (𝐊 : Rules α) ≤ₛ 𝐊𝐓 := reducible

lemma reducible_K_KD : (𝐊 : Rules α) ≤ₛ 𝐊𝐃 := reducible

lemma reducible_K_K4 : (𝐊 : Rules α) ≤ₛ 𝐊𝟒 := reducible

lemma reducible_K_K5 : (𝐊 : Rules α) ≤ₛ 𝐊𝟓 := reducible

lemma reducible_KT_S4 : (𝐊𝐓 : Rules α) ≤ₛ 𝐒𝟒 := reducible

lemma reducible_KT_S5 : (𝐊𝐓 : Rules α) ≤ₛ 𝐒𝟓 := reducible

open System

-- Macintyre & Simmons (1973)
-- 𝐆𝐋 =ₛ 𝐊𝟒(𝐋) =ₛ 𝐊𝟒(𝐇) =ₛ 𝐊𝟒𝐇
section GL

lemma reducible_GL_K4Loeb : (𝐆𝐋 : Rules α) ≤ₛ 𝐊𝟒(𝐋) := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | rule hr hant ih =>
    rcases hr with (hK | hL) | hNec;
    . obtain ⟨_, _, e⟩ := hK; rw [←e]; exact axiomK!;
    . obtain ⟨_, e⟩ := hL; rw [←e]; exact axiomL!;
    . obtain ⟨p, e⟩ := hNec; subst e; exact nec! $ ih (by tauto);
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | _ => trivial;

lemma reducible_K4Loeb_K4Henkin : (𝐊𝟒(𝐋) : Rules α) ≤ₛ 𝐊𝟒(𝐇) := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | rule hr hant ih =>
    rcases hr with ((hK | h4) | hNec) | hLoeb;
    . obtain ⟨_, _, e⟩ := hK; rw [←e]; exact axiomK!;
    . obtain ⟨_, e⟩ := h4; rw [←e]; exact axiomFour!;
    . obtain ⟨_, e⟩ := hNec; subst e; exact nec! $ ih (by tauto);
    . obtain ⟨p, e⟩ := hLoeb; subst e; exact loeb! $ ih (by tauto);
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | _ => trivial;

lemma reducible_K4Henkin_K4H : (𝐊𝟒(𝐇) : Rules α) ≤ₛ 𝐊𝟒𝐇 := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | rule hr hant ih =>
    rcases hr with ((hK | h4) | hNec) | hHenkin;
    . obtain ⟨_, _, e⟩ := hK; rw [←e]; exact axiomK!;
    . obtain ⟨_, e⟩ := h4; rw [←e]; exact axiomFour!;
    . obtain ⟨_, e⟩ := hNec; subst e; exact nec! $ ih (by tauto);
    . obtain ⟨_, e⟩ := hHenkin; subst e; exact henkin! $ ih (by tauto);
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | _ => trivial;

lemma reducible_K4H_GL : (𝐊𝟒𝐇 : Rules α) ≤ₛ 𝐆𝐋 := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | rule hr hant ih =>
    rcases hr with (hK | h4 | hH) | hNec;
    . obtain ⟨_, _, e⟩ := hK; rw [←e]; exact axiomK!;
    . obtain ⟨_, e⟩ := h4; rw [←e]; exact axiomFour!;
    . obtain ⟨_, e⟩ := hH; rw [←e]; exact axiomH!;
    . obtain ⟨_, e⟩ := hNec; subst e; exact nec! $ ih (by tauto);
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | _ => trivial;

end GL

end Reducible


end Modal.Standard

end LO
-/
