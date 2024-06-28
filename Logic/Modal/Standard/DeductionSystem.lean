import Logic.Logic.Deduction
import Logic.Modal.Standard.System

namespace LO.DeductionSystem

variable {F : Type*} [LogicalConnective F] [StandardModalLogicalConnective F]

namespace InferenceRules

abbrev Necessitation : Rules F := { ⟨[p], □p⟩ | (p) }
notation:max "⟮Nec⟯" => Necessitation

abbrev LoebRule : Rules F := { ⟨[□p ⟶ p], p⟩ | (p) }
notation:max "⟮Loeb⟯" => LoebRule

abbrev HenkinRule : Rules F := { ⟨[□p ⟷ p], p⟩ | (p) }
notation:max "⟮Henkin⟯" => HenkinRule

end InferenceRules

variable {𝓡 : Rules F}

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

abbrev ModalK : Rules F := 𝐜𝐏𝐋 ∪ ⟮K⟯ⁱ ∪ ⟮Nec⟯
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

end LO.DeductionSystem
